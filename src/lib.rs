//! 统一的索引键接口、带版本的键数据和类型安全的自定义键宏。
//!
//! 索引型整数键有意忽略版本；u64、i64 和宏生成的键保留版本。
//! 版本始终使用完整的 32 位。
//! 本库不负责槽位分配、回收，也不自动验证键是否仍然有效。

use pi_null::Null;

// 宏通过 $crate 访问这些重导出，不依赖调用方的导入或传递依赖路径。
#[doc(hidden)]
pub mod __impl {
    pub use core::convert::From;
    pub use core::result::Result;
    #[cfg(feature = "fory")]
    pub use fory;
    pub use pi_null::Null;
    #[cfg(feature = "serde")]
    pub use serde;
}

/// [`Key`] 的底层数据：一个 `u32` 索引和完整的 `u32` 版本。
///
/// 索引 `u32::MAX` 表示空，与版本无关；规范空数据的版本为零。
/// 版本零本身有效，不表示空或跳过版本校验。
///
/// 实现 [`Ord`] 以支持 [`BTreeMap`](std::collections::BTreeMap)
/// 等有序容器；该排序不是版本的时间先后，回绕比较应使用 [`is_older_version`]。
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "fory", derive(fory::ForyStruct))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyData {
    idx: u32,
    version: u32,
}

impl KeyData {
    /// 从原始索引和版本构造数据，完整保留版本，不检查容器有效性。
    ///
    /// `idx == u32::MAX` 表示空，但这里保留传入的版本，不强制规范化为零。
    #[inline(always)]
    pub fn new(idx: u32, version: u32) -> Self {
        Self { idx, version }
    }

    /// 返回原始索引；`u32::MAX` 表示空，不能用于访问容器。
    #[inline(always)]
    pub fn index(&self) -> u32 {
        self.idx
    }
    /// 返回完整版本；零也是有效版本。
    #[inline(always)]
    pub fn version(&self) -> u32 {
        self.version
    }
    /// 打包为 `u64`：高 32 位为版本，低 32 位为索引。
    ///
    /// 经 [`from_ffi`](Self::from_ffi) 可以无损还原，包括非规范空数据的版本。
    /// 此原始编码不同于空 `u64` 键的整数哨兵；键转换应使用 `From<KeyData>`。
    /// 外部存储应使用此编码，而不是直接存储 `i64` 键的整数表示。
    pub fn as_ffi(self) -> u64 {
        (u64::from(self.version) << 32) | u64::from(self.idx)
    }

    /// 将低 32 位解码为索引，高 32 位解码为完整版本。
    ///
    /// 任意输入均可解码，但不保证键在消费者容器中有效，也不规范化空版本。
    /// `i64` 键可能使用转义编码，
    /// 必须先经 [`Key::data`] 转为数据，不能直接将其整数值传入此方法。
    pub fn from_ffi(value: u64) -> Self {
        let idx = value & 0xffff_ffff;
        let version = value >> 32;
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
    #[inline(always)]
    fn null() -> Self {
        Self::new(u32::null(), 0)
    }

    #[inline(always)]
    fn is_null(&self) -> bool {
        self.idx.is_null()
    }
}

/// 从原始索引和版本构造数据，完整保留版本，不检查容器有效性。
///
/// `idx == u32::MAX` 表示空，但这里保留传入的版本，不强制规范化为零。
///
/// # Safety
///
/// 保留既有 `unsafe` 签名；本函数本身没有额外的内存安全前提。
/// 业务有效性仍由消费者检查。若下游使用未经检查的索引执行不安全访问，
/// 其内存安全前提由下游负责，本库不提供该保证。
#[inline(always)]
pub unsafe fn key_data(idx: u32, version: u32) -> KeyData {
    KeyData::new(idx, version)
}
/// 统一的索引键接口；它是安全 trait，不是对容器访问安全性的担保。
///
/// 建议用 [`new_key_type!`] 为不同用途声明独立类型，避免混用。宏生成的键
/// 与 [`DefaultKey`] 保存全部 [`KeyData`]，包括非规范空数据的版本。
/// `u64`、`i64` 保存有效非空键的索引和版本。
/// `i64` 将非空原始编码 `0x8000000000000000`
/// 转义为 `0x00000000ffffffff`，避免与空哨兵 `i64::MIN` 冲突。
///
/// `usize/u32/i32/u16/i16/u8/i8` 有意只保存索引：`From<KeyData>`
/// 丢弃版本，[`data`](Key::data) 返回版本零。这不表示免除版本校验；
/// 索引键不能区分同一槽位的不同代，是否适用及容器语义由消费者决定。
///
/// 整数转换保持空性：空数据转为对应整数的 `pi_null::Null` 哨兵，
/// 空整数的 `data()` 返回规范空数据，原空版本不保留。
/// 有效非空键满足 `key.index() == key.data().index() as usize`。
///
/// # 索引范围
///
/// `with` 和非空 `From<KeyData>` 输入必须可表示且不与空值冲突。
/// 所有索引均小于 `u32::MAX`，`usize` 在 64 位平台也受此上限约束。
/// 有符号索引型整数还要求索引不超过该类型的 `MAX`；无符号索引型整数
/// 还要求索引小于该类型的 `MAX`（保留为空）。例如 `i8` 为 `0..=127`，
/// `u8` 为 `0..=254`。空数据的 `From<KeyData>` 不受这些范围限制。
///
/// 越界不检查、不新增 panic，仍使用 Rust 的 `as` 转换，可能截断、
/// 变为负数或与空值冲突；这些输入不属于有效键契约。空键索引不得用于访问。
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
    /// 从上述有效范围内的索引创建版本零的键，不进行范围检查。
    ///
    /// # 示例
    ///
    /// ```
    /// # use pi_key::*;
    /// # use pi_null::Null;
    /// new_key_type! { struct MyKey; }
    /// let dk = DefaultKey::with(7);
    /// let mk = MyKey::with(7);
    /// assert_eq!(dk.data(), mk.data());
    /// assert_eq!(mk.data().version(), 0);
    /// assert!(MyKey::default().is_null());
    /// ```
    fn with(idx: usize) -> Self;
    /// 返回底层数据；索引型整数使用版本零，空整数返回规范空数据。
    /// 宏生成的键保留全部原始数据，`i64` 在此逆转特殊编码。
    fn data(&self) -> KeyData;
    /// 返回访问索引；仅有效非空键可用于访问，调用者必须先检查空性及容器有效性。
    fn index(&self) -> usize;
}
impl From<KeyData> for usize {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as usize
        }
    }
}
impl Key for usize {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self
    }
}
impl From<KeyData> for i64 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            let packed = k.as_ffi() as i64;
            // 将与空值哨兵冲突的有效编码转义到保留的空索引编码。
            if packed == i64::null() {
                u32::MAX as i64
            } else {
                packed
            }
        }
    }
}
impl Key for i64 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i64
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else if *self == u32::MAX as i64 {
            // 逆转空索引编码的转义，还原索引 0、完整版本 0x80000000。
            KeyData::from_ffi(i64::MIN as u64)
        } else {
            KeyData::from_ffi(*self as u64)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        self.data().index() as usize
    }
}
impl From<KeyData> for u64 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.as_ffi()
        }
    }
}
impl Key for u64 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u64
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::from_ffi(*self)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        self.data().index() as usize
    }
}
impl From<KeyData> for i32 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as i32
        }
    }
}
impl Key for i32 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i32
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for u32 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx
        }
    }
}
impl Key for u32 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u32
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for i16 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as i16
        }
    }
}
impl Key for i16 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i16
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for u16 {
    #[inline(always)]
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as u16
        }
    }
}
impl Key for u16 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u16
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}
impl From<KeyData> for i8 {
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as i8
        }
    }
}
impl Key for i8 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as i8
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

impl From<KeyData> for u8 {
    fn from(k: KeyData) -> Self {
        if k.is_null() {
            Self::null()
        } else {
            k.idx as u8
        }
    }
}
impl Key for u8 {
    #[inline(always)]
    fn with(idx: usize) -> Self {
        idx as u8
    }
    #[inline(always)]
    fn data(&self) -> KeyData {
        if self.is_null() {
            KeyData::null()
        } else {
            KeyData::new(*self as u32, 0)
        }
    }
    #[inline(always)]
    fn index(&self) -> usize {
        *self as usize
    }
}

/// 判断版本 `a` 是否比 `b` 旧，支持完整 32 位版本的回绕。
///
/// 使用模差 `(a - b) mod 2^32 > 2^31` 判断。
/// 相等或恰好相隔半周期时，两个方向都返回 `false`。只有实际时间间隔
/// 小于半周期时才能据此判断先后，长跨度无法判定；`u32::MAX` 无特殊哨兵语义。
pub fn is_older_version(a: u32, b: u32) -> bool {
    a.wrapping_sub(b) > (1u32 << 31)
}

/// 声明与 [`DefaultKey`] 行为相同、类型独立的键，保存全部 [`KeyData`]。
///
/// 为不同容器用途声明独立类型可减少混用，但类型不验证实例归属或槽位有效性。
/// 支持多个声明、可见性和属性；生成的类型之间不会隐式转换。
/// 宏通过 `$crate::__impl` 和完全限定的 `Null` 调用展开，声明时无需
/// 直接依赖或导入 `pi_null`。调用 `null()` / `is_null()` 则需直接依赖
/// `pi_null` 并导入其 `Null` trait；`default()` 无此要求。
/// 也可用 `Key::data().index() == u32::MAX` 检查空性。
///
/// # 示例
///
/// ```
/// # use pi_key::*;
/// new_key_type! {
///     // 私有键类型。
///     struct RocketKey;
///
///     // 带文档的公开键类型。
///     /// 用户键。
///     pub struct UserKey;
/// }
/// assert_eq!(UserKey::default().data().index(), u32::MAX);
///
/// ```
#[macro_export(local_inner_macros)]
macro_rules! new_key_type {
    ( $(#[$outer:meta])* $vis:vis struct $name:ident; $($rest:tt)* ) => {
        $crate::__define_key! { $(#[$outer])* $vis struct $name; }


        impl $crate::__impl::From<$crate::KeyData> for $name {
            #[inline(always)]
            fn from(k: $crate::KeyData) -> Self {
                $name(k)
            }
        }
        impl $crate::__impl::Null for $name {
            #[inline(always)]
            fn null() -> Self {
                <$crate::KeyData as $crate::__impl::Null>::null().into()
            }

            #[inline(always)]
            fn is_null(&self) -> bool {
                <$crate::KeyData as $crate::__impl::Null>::is_null(&self.0)
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

        $crate::new_key_type!($($rest)*);
    };

    () => {}
}

#[doc(hidden)]
#[macro_export]
#[cfg(all(feature = "serde", feature = "fory"))]
macro_rules! __define_key {
    ($(#[$outer:meta])* $vis:vis struct $name:ident;) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug,
                 $crate::__impl::serde::Serialize, $crate::__impl::serde::Deserialize)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);
        $crate::__serialize_key!($name);
    };
}

#[doc(hidden)]
#[macro_export]
#[cfg(all(feature = "serde", not(feature = "fory")))]
macro_rules! __define_key {
    ($(#[$outer:meta])* $vis:vis struct $name:ident;) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug,
                 $crate::__impl::serde::Serialize, $crate::__impl::serde::Deserialize)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);
    };
}

#[doc(hidden)]
#[macro_export]
#[cfg(all(not(feature = "serde"), feature = "fory"))]
macro_rules! __define_key {
    ($(#[$outer:meta])* $vis:vis struct $name:ident;) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);
        $crate::__serialize_key!($name);
    };
}

#[doc(hidden)]
#[macro_export]
#[cfg(not(any(feature = "serde", feature = "fory")))]
macro_rules! __define_key {
    ($(#[$outer:meta])* $vis:vis struct $name:ident;) => {
        $(#[$outer])*
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        #[repr(transparent)]
        $vis struct $name($crate::KeyData);
    };
}

#[doc(hidden)]
#[macro_export]
#[cfg(feature = "fory")]
macro_rules! __serialize_key {
    ($name:ident) => {
        impl $crate::__impl::fory::Serializer for $name {
            type Target = Self;

            fn write_data(
                value: &Self,
                context: &mut $crate::__impl::fory::WriteContext<'_>,
            ) -> $crate::__impl::Result<(), $crate::__impl::fory::Error> {
                context.writer.write_u64(value.0.as_ffi());
                Ok(())
            }

            fn read_data(
                context: &mut $crate::__impl::fory::ReadContext<'_>,
            ) -> $crate::__impl::Result<Self, $crate::__impl::fory::Error> {
                Ok(Self($crate::KeyData::from_ffi(context.reader.read_u64()?)))
            }
        }
    };
}

new_key_type! {
    /// 默认的类型安全键，保存全部 [`KeyData`]；默认值为规范空键。
    pub struct DefaultKey;
}
