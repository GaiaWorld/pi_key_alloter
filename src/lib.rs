use pi_null::Null;

// So our macros can refer to these.
#[doc(hidden)]
pub mod __impl {
    pub use core::convert::From;
    pub use core::result::Result;
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
    #[inline(always)]
    fn new(idx: u32, version: u32) -> Self {
        Self {
            idx,
            version: Self::version_mask(version),
        }
    }

    #[inline(always)]
    pub fn index(&self) -> u32 {
        self.idx
    }
    #[inline(always)]
    pub fn version(&self) -> u32 {
        self.version
    }
    /// Returns the key data as a 64-bit integer. No guarantees about its value
    /// are made other than that passing it to [`from_ffi`](Self::from_ffi)
    /// will return a key equal to the original.
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
    #[cfg(not(feature = "bits21_version"))]
    #[inline(always)]
    fn version_mask(ver: u32) -> u32 {
        ver
    }

    #[cfg(feature = "bits21_version")]
    #[inline(always)]
    fn version_mask(ver: u32) -> u32 {
        const VERSION_MASK: u32 = (1 << 21) - 1;
        ver & VERSION_MASK
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
    #[inline(always)]
    fn null() -> Self {
        Self::new(u32::null(), 0)
    }

    #[inline(always)]
    fn is_null(&self) -> bool {
        self.idx.is_null()
    }
}

#[inline(always)]
pub unsafe fn key_data(idx: u32, version: u32) -> KeyData {
    KeyData::new(idx, version)
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
pub trait Key:
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
    + 'static
{
    /// Gets the [`KeyData`] stored in this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_key::*;
    /// new_key_type! { struct MyKey; }
    /// let dk = DefaultKey::null();
    /// let mk = MyKey::null();
    /// assert_eq!(dk.data(), mk.data());
    /// ```
    fn with(idx: usize) -> Self;
    fn data(&self) -> KeyData;
    fn index(&self) -> usize;
}
impl From<KeyData> for usize {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.idx as usize
    }
}
impl Key for usize {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self
    }
}
impl From<KeyData> for i64 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.as_ffi() as i64
    }
}
impl Key for i64 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i64
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::from_ffi(*self as u64)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for u64 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.as_ffi()
    }
}
impl Key for u64 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u64
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::from_ffi(*self)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for i32 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.idx as i32
    }
}
impl Key for i32 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i32
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for u32 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.idx
    }
}
impl Key for u32 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u32
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for i16 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.idx as i16
    }
}
impl Key for i16 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i16
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for u16 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        k.idx as u16
    }
}
impl Key for u16 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u16
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for i8 {
    fn from(k: KeyData) -> Self {
        k.idx as i8
    }
}
impl Key for i8 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i8
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl From<KeyData> for u8 {
    fn from(k: KeyData) -> Self {
        k.idx as u8
    }
}
impl Key for u8 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u8
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        KeyData::new(*self as u32, 0)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

/// Returns if a is an older version than b, taking into account wrapping of
/// versions.
pub fn is_older_version(a: u32, b: u32) -> bool {
    if b == u32::MAX {
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
/// # use pi_key::*;
/// new_key_type! {
///     // A private key type.
///     struct RocketKey;
///
///     // A public key type with a doc comment.
///     /// Key for the user.
///     pub struct UserKey;
/// }
///
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
            #[inline(always)]
            fn from(k: $crate::KeyData) -> Self {
                $name(k)
            }
        }
        impl pi_null::Null for $name {
            #[inline(always)]
            fn null() -> Self {
                $crate::KeyData::null().into()
            }

            #[inline(always)]
            fn is_null(&self) -> bool {
                self.0.is_null()
            }
        }
        impl $crate::Key for $name {
            #[inline(always)]
            fn with(idx: usize) -> Self {
                $name(unsafe {$crate::key_data(idx as u32, 0)})
            }
            #[inline(always)]
            fn data(&self) -> $crate::KeyData {
                self.0
            }
            #[inline(always)]
            fn index(&self) -> usize {
                self.0.index() as usize
            }
        }

        $crate::__serialize_key!($name);

        $crate::new_key_type!($($rest)*);
    };

    () => {}
}

#[doc(hidden)]
#[macro_export]
macro_rules! __serialize_key {
    ( $name:ty ) => {};
}

new_key_type! {
    /// The default key type.
    pub struct DefaultKey;
}
