//! A crate which introduces a type for sharing a mutable reference
//! and mutating the value behind it. 

use std::cell::Cell;
use std::{mem, ops, fmt, cmp};

/// A type which allows to share a mutable refernce and mutate the value behind it.
#[repr(transparent)]
pub struct SharedMutRef<'r, T: ?Sized + 'r>(Cell<Option<&'r mut T>>);

impl<'r, T: ?Sized + 'r> SharedMutRef<'r, T> {
    /// Creates a new [`SharedMutRef`] containing the given mutable reference.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// ```
    pub fn new(value_ref: &'r mut T) -> Self {
        Self(Cell::new(Some(value_ref)))
    }

    /// Unwraps the underlying mutable reference and consumes the [`SharedMutRef`].
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// let value_ref = shared_mut_ref.into_inner();
    /// ```
    pub fn into_inner(self) -> &'r mut T {
        self.0.take().unwrap()
    }

    /// Returns a [`TempMutRef`] to the borrowed value if it wasn't already taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// let mut temp_mut_ref = shared_mut_ref.get_temp().unwrap();
    /// temp_mut_ref[0] = 4;
    /// 
    /// assert_eq!(*temp_mut_ref, vec![4, 2, 3]);
    /// ```
    pub fn get_temp(&self) -> Option<TempMutRef<'_, 'r, T>> {
        self.0.take().map(|value_ref| TempMutRef {
            shared: self,
            value_ref: Some(value_ref),
        })
    }

    /// Modifies the borrowed value if [`TempMutRef`] wasn't taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// shared_mut_ref.modify(|value_ref| value_ref.reverse());
    /// assert_eq!(shared_mut_ref.get(), Some(vec![3, 2, 1]));
    /// ```
    pub fn modify<U, F>(&self, f: F) -> Option<U>
    where
        F: FnOnce(&mut T) -> U,
    {
        self.get_temp()
            .map(|mut temp_mut_ref| f(&mut *temp_mut_ref))
    }
}

impl<'r, T: 'r> SharedMutRef<'r, T> {
    /// Sets the borrowed value if [`TempMutRef`] wasn't taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// shared_mut_ref.set(vec![4, 5, 6]);
    /// assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
    /// ```
    pub fn set(&self, value: T) -> Result<(), T> {
        let Some(value_ref) = self.0.take() else {
            return Err(value);
        };
        *value_ref = value;
        self.0.set(Some(value_ref));

        Ok(())
    }

    /// Replaces the borrowed value with `new_value` and returns
    /// the old borrowed value if [`TempMutRef`] wasn't taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// assert_eq!(shared_mut_ref.replace(vec![4, 5, 6]), Ok(vec![1, 2, 3]));
    /// assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
    /// ```
    pub fn replace(&self, new_value: T) -> Result<T, T> {
        let Some(value_ref) = self.0.take() else {
            return Err(new_value);
        };
        let old_value = mem::replace(value_ref, new_value);
        self.0.set(Some(value_ref));

        Ok(old_value)
    }
}

impl<'r, T: Default + 'r> SharedMutRef<'r, T> {
    /// Takes the borrowed value and leaves a default value in its place
    /// if [`TempMutRef`] wasn't taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// assert_eq!(shared_mut_ref.take(), Some(vec![1, 2, 3]));
    /// assert_eq!(shared_mut_ref.get(), Some(vec![]));
    /// ```
    pub fn take(&self) -> Option<T> {
        let Some(value_ref) = self.0.take() else {
            return None;
        };
        let value = mem::take(value_ref);
        self.0.set(Some(value_ref));

        Some(value)
    }
}

impl<'r, T: Clone + 'r> SharedMutRef<'r, T> {
    /// Clones the borrowed value and returns it if [`TempMutRef`] wasn't taken.
    /// 
    /// # Example
    /// 
    /// ```
    /// use shared_mut_ref::SharedMutRef;
    /// 
    /// let mut value = vec![1, 2, 3];
    /// let shared_mut_ref = SharedMutRef::new(&mut value);
    /// 
    /// assert_eq!(shared_mut_ref.get(), Some(vec![1, 2, 3]));
    /// ```
    pub fn get(&self) -> Option<T> {
        let Some(value_ref) = self.0.take() else {
            return None;
        };
        let value = value_ref.clone();
        self.0.set(Some(value_ref));

        Some(value)
    }
}

impl<T: fmt::Debug> fmt::Debug for SharedMutRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(value_ref) = self.0.take() else {
            return f.write_fmt(format_args!("SharedMutRef(<temporary_borrowed>)"));
        };
        let ret = f.write_fmt(format_args!("SharedMutRef({:?})", *value_ref));
        self.0.set(Some(value_ref));

        ret
    }
}

impl<'r, T: ?Sized + 'r> From<&'r mut T> for SharedMutRef<'r, T> {
    fn from(value: &'r mut T) -> Self {
        Self::new(value)
    }
}

/// A wrapper around a mutable reference which gives a temporary unique access to borrowed value.
/// 
/// The [`TempMutRef`] is returned by [`SharedMutRef::get_temp`].
/// 
/// [`SharedMutRef::get_temp`]: crate::SharedMutRef::get_temp
pub struct TempMutRef<'s, 'r, T: ?Sized + 'r> {
    shared: &'s SharedMutRef<'r, T>,
    value_ref: Option<&'r mut T>,
}

impl<T: ?Sized> ops::Deref for TempMutRef<'_, '_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &**self
            .value_ref
            .as_ref()
            .expect("TempMutRef doesn't point to any value")
    }
}

impl<T: ?Sized> ops::DerefMut for TempMutRef<'_, '_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut **self
            .value_ref
            .as_mut()
            .expect("TempMutRef doesn't point to any value")
    }
}

impl<T: fmt::Debug> fmt::Debug for TempMutRef<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("TempMutRef({:?})", **self))
    }
}

impl<T: fmt::Display> fmt::Display for TempMutRef<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> ops::Drop for TempMutRef<'_, '_, T> {
    fn drop(&mut self) {
        self.shared.0.set(self.value_ref.take());
    }
}

impl<T: cmp::PartialEq> cmp::PartialEq for TempMutRef<'_, '_, T> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: cmp::Eq> cmp::Eq for TempMutRef<'_, '_, T> {}

impl<T: cmp::PartialOrd> cmp::PartialOrd for TempMutRef<'_, '_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: cmp::Ord> cmp::Ord for TempMutRef<'_, '_, T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(&**other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_mut_ref_get() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        assert_eq!(shared_mut_ref.get(), Some(vec![1, 2, 3]));

        let _temp = shared_mut_ref.get_temp();
        assert!(shared_mut_ref.get().is_none())
    }

    #[test]
    fn test_shared_mut_ref_set() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        {
            assert!(shared_mut_ref.set(vec![4, 5, 6]).is_ok());
            assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
        }

        {
            let _temp = shared_mut_ref.get_temp();
            assert_eq!(shared_mut_ref.set(vec![7, 8, 9]), Err(vec![7, 8, 9]));
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
    }

    #[test]
    fn test_shared_mut_ref_replace() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        {
            assert_eq!(shared_mut_ref.replace(vec![4, 5, 6]), Ok(vec![1, 2, 3]));
            assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
        }

        {
            let _temp = shared_mut_ref.get_temp();
            assert_eq!(shared_mut_ref.replace(vec![7, 8, 9]), Err(vec![7, 8, 9]));
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));
    }

    #[test]
    fn test_shared_mut_ref_take() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        {
            assert_eq!(shared_mut_ref.take(), Some(vec![1, 2, 3]));
            assert_eq!(shared_mut_ref.get(), Some(vec![]));
        }

        {
            let _temp = shared_mut_ref.get_temp();
            assert!(shared_mut_ref.take().is_none());
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![]));
    }

    #[test]
    fn test_shared_mut_ref_modify() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        {
            shared_mut_ref.modify(|value_ref| value_ref.reverse());
            assert_eq!(shared_mut_ref.get(), Some(vec![3, 2, 1]));
        }

        {
            let _temp = shared_mut_ref.get_temp();
            shared_mut_ref.modify(|value_ref| value_ref.reverse());
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![3, 2, 1]));
    }

    #[test]
    fn test_shared_mut_ref_get_temp() {
        let mut vec = vec![1, 2, 3];
        let shared_mut_ref = SharedMutRef::new(&mut vec);

        {
            let temp = shared_mut_ref.get_temp().unwrap();
            assert_eq!(*temp, vec![1, 2, 3]);
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![1, 2, 3]));

        {
            let mut temp = shared_mut_ref.get_temp().unwrap();
            *temp = vec![4, 5, 6];
            assert_eq!(*temp, vec![4, 5, 6]);
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![4, 5, 6]));

        {
            let mut temp1 = shared_mut_ref.get_temp().unwrap();

            let temp2 = shared_mut_ref.get_temp();
            assert!(temp2.is_none());

            *temp1 = vec![1, 2, 3];
            assert_eq!(*temp1, vec![1, 2, 3]);
        }

        assert_eq!(shared_mut_ref.get(), Some(vec![1, 2, 3]));
    }
}
