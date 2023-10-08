use std::sync::atomic::Ordering;

use crossbeam::queue::SegQueue;
use pi_null::Null;
use pi_share::ShareU32;

// So our macros can refer to these.
#[doc(hidden)]
pub mod __impl {
    pub use core::convert::From;
    pub use core::result::Result;
    #[cfg(feature = "serde")]
    pub use serde::{Deserialize, Deserializer, Serialize, Serializer};
}

/// The actual data stored in a [`Key`].
///
/// This implements [`Ord`](std::cmp::Ord) so keys can be stored in e.g.
/// [`BTreeMap`](std::collections::BTreeMap), but the order of keys is
/// unspecified.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyData {
    idx: u32,
    version: u32,
}

impl KeyData {
    fn new(idx: u32, version: u32) -> Self {
        Self { idx, version }
    }

    pub fn index(&self) -> u32 {
        self.idx
    }
    pub fn version(&self) -> u32 {
        self.version
    }
    /// Returns the key data as a 64-bit integer. No guarantees about its value
    /// are made other than that passing it to [`from_ffi`](Self::from_ffi)
    /// will return a key equal to the original.
    ///
    /// This is not a substitute for proper serialization, use [`serde`] for
    /// that. If you are not doing FFI, you almost surely do not need this
    /// function.
    ///
    /// [`serde`]: crate#serialization-through-serde-no_std-support-and-unstable-features
    pub fn as_ffi(self) -> u64 {
        (u64::from(self.version) << 32) | u64::from(self.idx)
    }

    /// Iff `value` is a value received from `k.as_ffi()`, returns a key equal
    /// to `k`. Otherwise the behavior is safe but unspecified.
    pub fn from_ffi(value: u64) -> Self {
        let idx = value & 0xffff_ffff;
        let version = value >> 32; // Ensure version is odd.
        Self::new(idx as u32, version as u32)
    }
}

impl core::fmt::Debug for KeyData {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}v{}", self.idx, self.version)
    }
}

impl Default for KeyData {
    fn default() -> Self {
        Self::null()
    }
}
impl Null for KeyData {
    fn null() -> Self {
        Self::new(u32::null(), 0)
    }

    fn is_null(&self) -> bool {
        self.idx.is_null()
    }
}
/// it is suggested to have a unique key type for each slot
/// map. You can create new key types using [`new_key_type!`], which makes a
/// new type identical to [`DefaultKey`], just with a different name.
///
/// This trait is intended to be a thin wrapper around [`KeyData`], and all
/// methods must behave exactly as if we're operating on a [`KeyData`] directly.
/// The internal unsafe code relies on this, therefore this trait is `unsafe` to
/// implement. It is strongly suggested to simply use [`new_key_type!`] instead
/// of implementing this trait yourself.
pub unsafe trait Key:
    From<KeyData>
    + Copy
    + Clone
    + Default
    + Eq
    + PartialEq
    + Ord
    + PartialOrd
    + core::hash::Hash
    + core::fmt::Debug
    + pi_null::Null
{
    /// Gets the [`KeyData`] stored in this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_key_alloter::*;
    /// new_key_type! { struct MyKey; }
    /// let dk = DefaultKey::null();
    /// let mk = MyKey::null();
    /// assert_eq!(dk.data(), mk.data());
    /// ```
    fn data(&self) -> KeyData;
}

/// Returns if a is an older version than b, taking into account wrapping of
/// versions.
pub fn is_older_version(a: u32, b: u32) -> bool {
    if b == std::u32::MAX {
        return false;
    }
    let diff = a.wrapping_sub(b);
    diff >= (1 << 31)
}

/// A helper macro to create new key types. If you use a new key type for each
/// slot map you create you can entirely prevent using the wrong key on the
/// wrong slot map.
///
/// The type constructed by this macro is defined exactly as [`DefaultKey`],
/// but is a distinct type for the type checker and does not implicitly convert.
///
/// # Examples
///
/// ```
/// # use pi_key_alloter::*;
/// new_key_type! {
///     // A private key type.
///     struct RocketKey;
///
///     // A public key type with a doc comment.
///     /// Key for the user.
///     pub struct UserKey;
/// }
///
/// fn main() {
///     let users = KeyAlloter::new(0);
///     let rockets = KeyAlloter::new(0);
///     let bob: UserKey = users.alloc(1).into();
///     let apollo: RocketKey = rockets.alloc(1).into();
///     println!("users: {:?} rocket: {:?}", bob, apollo);
/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! new_key_type {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default,
                 Eq, PartialEq, Ord, PartialOrd,
                 Hash, Debug)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);


        impl $crate::__impl::From<$crate::KeyData> for $name {
            fn from(k: $crate::KeyData) -> Self {
                $name(k)
            }
        }
        impl pi_null::Null for $name {
            fn null() -> Self {
                $crate::KeyData::null().into()
            }

            fn is_null(&self) -> bool {
                self.0.is_null()
            }
        }
        unsafe impl $crate::Key for $name {
            fn data(&self) -> $crate::KeyData {
                self.0
            }
        }

        $crate::__serialize_key!($name);

        $crate::new_key_type!($($rest)*);
    };

    () => {}
}

#[cfg(feature = "serde")]
#[doc(hidden)]
#[macro_export]
macro_rules! __serialize_key {
    ( $name:ty ) => {
        impl $crate::__impl::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> $crate::__impl::Result<S::Ok, S::Error>
            where
                S: $crate::__impl::Serializer,
            {
                $crate::Key::data(self).serialize(serializer)
            }
        }

        impl<'de> $crate::__impl::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> $crate::__impl::Result<Self, D::Error>
            where
                D: $crate::__impl::Deserializer<'de>,
            {
                let key_data: $crate::KeyData =
                    $crate::__impl::Deserialize::deserialize(deserializer)?;
                Ok(key_data.into())
            }
        }
    };
}

#[cfg(not(feature = "serde"))]
#[doc(hidden)]
#[macro_export]
macro_rules! __serialize_key {
    ( $name:ty ) => {};
}

new_key_type! {
    /// The default key type.
    pub struct DefaultKey;
}

// Serialization with serde.
#[cfg(feature = "serde")]
mod serialize {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use super::*;

    #[derive(Serialize, Deserialize)]
    pub struct SerKey {
        idx: u32,
        version: u32,
    }

    impl Serialize for KeyData {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let ser_key = SerKey {
                idx: self.idx,
                version: self.version,
            };
            ser_key.serialize(serializer)
        }
    }

    impl<'de> Deserialize<'de> for KeyData {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            let ser_key: SerKey = Deserialize::deserialize(deserializer)?;
            Ok(Self::new(ser_key.idx, ser_key.version))
        }
    }
}

#[cfg(not(feature = "rc"))]
pub type Queue = SegQueue<KeyData>;
#[cfg(feature = "rc")]
#[derive(Debug, Default)]
pub struct Queue(std::cell::RefCell<Vec<KeyData>>);

#[cfg(feature = "rc")]
impl Queue {
    fn pop(&self) -> Option<KeyData> {
        self.0.borrow_mut().pop()
    }
    fn push(&self, key: KeyData) {
        self.0.borrow_mut().push(key)
    }
    fn len(&self) -> usize {
        self.0.borrow().len()
    }
}
/// `KeyAlloter` 结构体用于线程安全地分配和回收Key。
/// 结构体包含两个字段，`max`表示已分配Key的最大值，`recycled`用于存储曾经分配出去，后又被回收的Key
/// 分配Key时， 如果recycled长度大于0，将从recycled中弹出一个Key，否则，分配的Key值为`max`,并且`max`会自增1
#[derive(Debug, Default)]
pub struct KeyAlloter {
    max: ShareU32,
    recycled: Queue,
}

impl KeyAlloter {
    /// 构造方法
    pub fn new(start_index: u32) -> Self {
        KeyAlloter {
            max: ShareU32::new(start_index),
            recycled: Default::default(),
        }
    }
    /// 已分配的Key个数
    pub fn len(&self) -> usize {
        self.max.load(Ordering::Acquire) as usize - self.recycled.len()
    }
    /// 分配一个Key，如果recycled中存在回收Key，将从recycled中弹出一个Key，并且版本增加指定的值。
    /// 否则，分配的Key值为`max`,并且`max`会自增1，版本初始值为指定的版本增加值
    pub fn alloc(&self, version_incr: u32) -> KeyData {
        match self.recycled.pop() {
            Some(r) => KeyData::new(r.idx, r.version + version_incr),
            None => KeyData::new(self.max.fetch_add(1, Ordering::AcqRel), version_incr),
        }
    }
    
    /// 回收一个Key
    pub fn recycle(&self, key: KeyData) {
        self.recycled.push(key);
    }
    /// 是否没有回收的key
    pub fn is_recycle_empty(&self) -> bool {
        self.recycled.is_empty()
    }
    /// 已回收的Key个数
    pub fn recycle_len(&self) -> usize {
        self.recycled.len()
    }

    /// 当前已分配Key的最大值
    pub fn max(&self) -> u32 {
        self.max.load(Ordering::Acquire)
    }
    /// 外部必须保证没有其他线程分配Key，整理，返回整理迭代器，迭代器返回(当前最大值, 空位)，外部可利用该信息进行数据交换，让分配的Key和Value连续
    pub fn collect(&self, version_incr: u32) -> Drain {
        let max = self.max.load(Ordering::Acquire);
        Drain {
            max,
            index: max,
            version_incr,
            alloter: &self,
        }
    }
}

#[derive(Debug)]
pub struct Drain<'a> {
    max: u32,
    index: u32,
    version_incr: u32,
    alloter: &'a KeyAlloter,
}
impl<'a> Iterator for Drain<'a> {
    type Item = (u32, KeyData);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(r) = self.alloter.recycled.pop() {
            self.index -= 1;
            if self.index != r.idx {
                return Some((self.index, KeyData::new(r.idx, r.version + self.version_incr)))
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.alloter.recycled.len();
        (len, Some(len))
    }
}
impl<'a> Drop for Drain<'a> {
    fn drop(&mut self) {
        let _ = self
            .alloter
            .max
            .compare_exchange(self.max, self.index, Ordering::Relaxed, Ordering::Relaxed)
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    // Intentionally no `use super::*;` because we want to test macro expansion
    // in the *users* scope, which might not have that.
    #[test]
    fn macro_expansion() {
        #![allow(dead_code)]
        use super::new_key_type;

        // Clobber namespace with clashing names - should still work.
        trait Serialize {}
        trait Deserialize {}
        trait Serializer {}
        trait Deserializer {}
        trait Key {}
        trait From {}
        struct Result;
        struct KeyData;

        new_key_type! {
            struct A;
            pub(crate) struct B;
            pub struct C;
        }
    }

    #[test]
    fn check_is_older_version() {
        use crate::is_older_version;

        let is_older = |a, b| is_older_version(a, b);
        assert!(!is_older(42, 42));
        assert!(is_older(0, 1));
        assert!(is_older(0, 1 << 31));
        assert!(!is_older(0, (1 << 31) + 1));
        assert!(is_older(u32::MAX, 0));
    }
    #[test]
    fn test_new_key_type() {
        use crate::*;
        new_key_type! {
            // A private key type.
            struct RocketKey;

            // A public key type with a doc comment.
            /// Key for the user.
            pub struct UserKey;
        }
        let users = KeyAlloter::new(0);
        let rockets = KeyAlloter::new(0);
        let bob: UserKey = users.alloc(1).into();
        let apollo: RocketKey = rockets.alloc(1).into();
        println!("users: {:?} rocket: {:?}", bob, apollo);
    }
    #[test]
    fn test_key() {
        use crate::*;

        let alloter = KeyAlloter::new(0);
        let k = alloter.alloc(1);
        assert_eq!(0, k.index());
        assert_eq!(1, k.version());
        alloter.recycle(k);
        let k = alloter.alloc(1);
        assert_eq!(0, k.index());
        assert_eq!(2, k.version());
        let k = alloter.alloc(1);
        assert_eq!(1, k.index());
        assert_eq!(1, k.version());
    }

    #[test]
    fn test() {
        use crate::*;
        let alloter = Arc::new(KeyAlloter::new(0));

        // spawn 6 threads that append to the arr
        let threads = (0..6)
            .map(|_i| {
                let alloter = alloter.clone();

                std::thread::spawn(move || {
                    let _ = alloter.alloc(1);
                })
            })
            .collect::<Vec<_>>();

        // wait for the threads to finish
        for thread in threads {
            thread.join().unwrap();
        }
        let k = alloter.alloc(1);
        assert_eq!(6, k.index());
        assert_eq!(1, k.version());
    }
}
