#![no_std]
#![feature(step_trait)]
//! Iterator utility for counting the number of iterations with an arbitrary
//! type that implements the [`Step`] trait.

use core::iter::Step;

/// Consumes the iterator, counting the number of iterations.
/// This uses the [`Step`] trait to keep track of the count of iterations.
/// The count starts from the default value provided by the [`Default`] trait.
///
/// _Note_: This function takes any implementation of [`IntoIterator`],
/// which includes iterators themselves.
///
/// # Panics
///
/// Panics if the count exceeds the capacity of the count type (`T`).
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use step_count::step_count;
/// let arr = [1, 2, 3];
/// let count: usize = step_count(arr);
/// assert_eq!(count, 3);
/// ```
///
/// Overflow:
///
/// ```should_panic
/// # use step_count::step_count;
/// let arr = [(); u8::MAX as usize + 1];
/// step_count::<u8>(arr);
/// ```
#[inline]
pub fn step_count<T: Step + Default>(iter: impl IntoIterator) -> T {
    step_count_from(iter, T::default())
}

/// Consumes the iterator, counting the number of iterations,
/// starting from a given value.
/// This uses the [`Step`] trait to keep track of the count of iterations.
///
/// _Note_: This function takes any implementation of [`IntoIterator`],
/// which includes iterators themselves.
///
/// # Panics
///
/// Panics if the count exceeds the capacity of the count type (`T`).
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use step_count::step_count_from;
/// let arr = [1, 2, 3];
/// let count: u16 = step_count_from(arr, 2);
/// assert_eq!(count, 5);
/// ```
///
/// Overflow:
///
/// ```should_panic
/// # use step_count::step_count_from;
/// let arr = [(); u8::MAX as usize - 1];
/// step_count_from::<u8>(arr, 2);
/// ```
#[inline]
pub fn step_count_from<T: Step>(iter: impl IntoIterator, start: T) -> T {
    let iter = iter.into_iter();
    iter.fold(start, |count, _| T::forward(count, 1))
}

/// Consumes the iterator, counting the number of iterations.
/// This uses the [`Step`] trait to keep track of the count of iterations.
/// The count starts from the default value provided by the [`Default`] trait.
/// Returns [`None`] if the count exceeded the capcity of the count type (`T`).
///
/// This function always fully consumes the iterator, even if [`None`] is returned.
///
/// _Note_: This function takes any implementation of [`IntoIterator`],
/// which includes iterators themselves.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use step_count::step_count_checked;
/// let arr = [1, 2, 3];
/// let count: Option<u16> = step_count_checked(arr);
/// assert_eq!(count, Some(3));
/// ```
///
/// Overflow:
///
/// ```
/// # use step_count::step_count_checked;
/// let arr = [(); u8::MAX as usize + 1];
/// let count: Option<u8> = step_count_checked(arr);
/// assert_eq!(count, None);
/// ```
///
/// Consumption:
///
/// ```
/// # use step_count::step_count_checked;
/// let mut range = -1..u8::MAX as isize;
/// let count: Option<u8> = step_count_checked(&mut range);
/// assert!(range.is_empty());
/// ```
#[inline]
pub fn step_count_checked<T: Step + Default>(iter: impl IntoIterator) -> Option<T> {
    step_count_from_checked(iter, T::default())
}

/// Consumes the iterator, counting the number of iterations,
/// starting from a given value.
/// This uses the [`Step`] trait to keep track of the count of iterations.
/// Returns [`None`] if the count exceeded the capcity of the count type (`T`).
///
/// This function always fully consumes the iterator, even if [`None`] is returned.
///
/// _Note_: This function takes any implementation of [`IntoIterator`],
/// which includes iterators themselves.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use step_count::step_count_from_checked;
/// let arr = [1, 2, 3];
/// let count: Option<u16> = step_count_from_checked(arr, 2);
/// assert_eq!(count, Some(5));
/// ```
///
/// Overflow:
///
/// ```
/// # use step_count::step_count_from_checked;
/// let arr = [(); u8::MAX as usize - 1];
/// let count: Option<u8> = step_count_from_checked(arr, 2);
/// assert_eq!(count, None);
/// ```
///
/// Consumption:
///
/// ```
/// # use step_count::step_count_from_checked;
/// let mut range = -2..=i8::MAX as isize;
/// let count: Option<i8> = step_count_from_checked(&mut range, -1);
/// assert!(range.is_empty());
/// ```
#[inline]
pub fn step_count_from_checked<T: Step>(iter: impl IntoIterator, start: T) -> Option<T> {
    let mut iter = iter.into_iter();
    let result = iter.try_fold(start, |count, _| T::forward_checked(count, 1));
    iter.last();
    result
}

/// Convenience trait to allow using `step_count*` functions as methods.
/// This trait is implemented for every [`Iterator`].
pub trait StepCount: Iterator {
    /// Consumes the iterator, counting the number of iterations.
    /// This uses the [`Step`] trait to keep track of the count of iterations.
    /// The count starts from the default value provided by the [`Default`] trait.
    ///
    /// # Panics
    ///
    /// Panics if the count exceeds the capacity of the count type (`T`).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let arr = [1, 2, 3];
    /// let count: usize = arr.into_iter().step_count();
    /// assert_eq!(count, 3);
    /// ```
    ///
    /// Overflow:
    ///
    /// ```should_panic
    /// # use step_count::StepCount;
    /// let range = 0..u8::MAX as usize + 1;
    /// range.step_count::<u8>();
    /// ```
    #[inline]
    fn step_count<T: Step + Default>(self) -> T
    where
        Self: Sized,
    {
        step_count(self)
    }
    /// Consumes the iterator, counting the number of iterations,
    /// starting from a given value.
    /// This uses the [`Step`] trait to keep track of the count of iterations.
    ///
    /// # Panics
    ///
    /// Panics if the count exceeds the capacity of the count type (`T`).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let arr = [1, 2, 3];
    /// let count: u16 = arr.into_iter().step_count_from(2);
    /// assert_eq!(count, 5);
    /// ```
    ///
    /// Overflow:
    ///
    /// ```should_panic
    /// # use step_count::StepCount;
    /// let range = 0..u8::MAX as usize - 1;
    /// range.step_count_from::<u8>(2);
    /// ```
    #[inline]
    fn step_count_from<T: Step>(self, start: T) -> T
    where
        Self: Sized,
    {
        step_count_from(self, start)
    }
    /// Consumes the iterator, counting the number of iterations.
    /// This uses the [`Step`] trait to keep track of the count of iterations.
    /// The count starts from the default value provided by the [`Default`] trait.
    /// Returns [`None`] if the count exceeded the capcity of the count type (`T`).
    ///
    /// This function always fully consumes the iterator, even if [`None`] is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let arr = [1, 2, 3];
    /// let count: Option<u16> = arr.into_iter().step_count_checked();
    /// assert_eq!(count, Some(3));
    /// ```
    ///
    /// Overflow:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let range = 0..u8::MAX as usize + 1;
    /// let count: Option<u8> = range.step_count_checked();
    /// assert_eq!(count, None);
    /// ```
    ///
    /// Consumption:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let mut range = -1..u8::MAX as isize;
    /// let count: Option<u8> = range.by_ref().step_count_checked();
    /// assert!(range.is_empty());
    /// ```
    #[inline]
    fn step_count_checked<T: Step + Default>(self) -> Option<T>
    where
        Self: Sized,
    {
        step_count_checked(self)
    }
    /// Consumes the iterator, counting the number of iterations,
    /// starting from a given value.
    /// This uses the [`Step`] trait to keep track of the count of iterations.
    /// Returns [`None`] if the count exceeded the capcity of the count type (`T`).
    ///
    /// This function always fully consumes the iterator, even if [`None`] is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let arr = [1, 2, 3];
    /// let count: Option<u16> = arr.into_iter().step_count_from_checked(2);
    /// assert_eq!(count, Some(5));
    /// ```
    ///
    /// Overflow:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let range = 0..u8::MAX as usize - 1;
    /// let count: Option<u8> = range.step_count_from_checked(2);
    /// assert_eq!(count, None);
    /// ```
    ///
    /// Consumption:
    ///
    /// ```
    /// # use step_count::StepCount;
    /// let mut range = -2..i8::MAX as isize;
    /// let count: Option<i8> = range.by_ref().step_count_from_checked(-1);
    /// assert!(range.is_empty());
    /// ```
    #[inline]
    fn step_count_from_checked<T: Step>(self, start: T) -> Option<T>
    where
        Self: Sized,
    {
        step_count_from_checked(self, start)
    }
}

impl<T: Iterator> StepCount for T {}
