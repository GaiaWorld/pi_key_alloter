# pi_key

统一的索引键接口、带版本的 `KeyData` 和类型安全键宏。本 crate 不是槽位分配器：不分配或回收槽位，不管理容器，也不自动验证键的归属、边界或存活状态。

## 数据与版本

`KeyData` 包含 `u32` 索引和完整的 `u32` 版本。索引 `u32::MAX` 表示空，与版本无关；规范空数据为 `(u32::MAX, 0)`。版本零本身有效，不代表空，也不代表免版本校验。`Default` 返回规范空数据。

`KeyData::new(idx, version)` 完整保留版本，包括空索引的非零版本，不检查容器有效性。`KeyData::as_ffi()` 的原始 `u64` 编码为高 32 位版本、低 32 位索引。`from_ffi()` 可无损还原，不规范化空版本。`Ord` 用于有序容器，不表示版本的时间先后。

```rust
use pi_key::KeyData;

let data = KeyData::new(12, 7);
assert_eq!(data.index(), 12);
assert_eq!(data.version(), 7);
assert_eq!(KeyData::from_ffi(data.as_ffi()), data);
```

## 可选序列化

`serde` 和 `fory` 均默认关闭；不开启对应 feature 时不会引入该依赖。可按需启用：

```toml
pi_key = { version = "0.3", features = ["serde", "fory"] }
```

两种 feature 都支持 `KeyData`、`DefaultKey` 和 `new_key_type!` 生成的键。Fory 中注册 `KeyData` 使用 `register::<KeyData>(id)`；注册宏生成的键使用 `register_serializer::<MyKey>(id)`，避免跨 crate 派生索引冲突。Fory 1.7.7 在 32 位 x86 Windows 上编译失败，启用此 feature 时需要支持的目标平台。

## 键类型

| 类型 | 保存内容 | `data()` 与空值行为 |
| --- | --- | --- |
| `DefaultKey`、`new_key_type!` 生成的类型 | 全部 `KeyData` | 保留原数据，包括非规范空版本 |
| `u64`、`i64` | 有效非空键的索引和版本 | 空整数返回规范空数据；`i64` 逆转特殊编码 |
| `usize/u32/i32/u16/i16/u8/i8` | 仅索引 | `From<KeyData>` 丢弃版本，`data()` 版本为零；空整数返回规范空数据 |

索引型整数是有意设计的索引表示，不能区分同一槽位的不同代。选择此类型不表示可以跳过版本校验：消费者必须自行决定是否适合其容器语义，以及如何处理删除、复用和过期键。

```rust
use pi_key::{DefaultKey, Key, KeyData};

let data = KeyData::from_ffi((3_u64 << 32) | 9);
let full = DefaultKey::from(data);
let index_only = u16::from(data);
assert_eq!(full.data(), data);
assert_eq!(index_only.data().index(), 9);
assert_eq!(index_only.data().version(), 0);
```

## 有效索引范围

以下范围适用于 `Key::with(usize)` 和非空 `From<KeyData>`，均为闭区间。所有索引必须小于 `u32::MAX`；有符号索引型整数还必须不超过该类型 `MAX`，无符号索引型整数还必须小于该类型 `MAX`，因为其最大值保留为空。

| 键类型 | 有效非空索引 |
| --- | --- |
| `DefaultKey`、宏生成类型、`u64`、`i64` | `0..=u32::MAX - 1` |
| `usize`、`u32` | `0..=u32::MAX - 1`（`usize` 在 64 位平台也不扩展范围） |
| `i32` | `0..=i32::MAX` |
| `u16` | `0..=65534` |
| `i16` | `0..=32767` |
| `u8` | `0..=254` |
| `i8` | `0..=127` |

有效非空键满足 `key.index() == key.data().index() as usize`。越界输入不检查、不新增 panic，保留现有 Rust `as` 转换，可能截断、变为负数或与空值冲突，不属于有效键契约。空 `KeyData` 的 `From` 转换豁免以上范围限制；空键的 `index()` 不得用于访问。

## 空值与 i64 转义

空值依赖 `pi_null::Null`：无符号整数使用该类型 `MAX`，有符号整数使用该类型 `MIN`。空 `KeyData` 转为整数时返回对应哨兵，原空版本不保留；空整数经 `data()` 返回规范空数据。`KeyData::as_ffi()` 仍保留原始字段编码，若要转成 `u64` 空键，应使用 `u64::from(data)`；反向应使用 `u64` 的 `Key::data()`。宏生成的键则保存原空数据。

索引 `0`、版本 `0x80000000` 的原始 FFI 编码为 `0x8000000000000000`，按 `i64` 解释恰好是空哨兵 `i64::MIN`。为保持有效非空键，`From<KeyData> for i64` 将它转义为 `u32::MAX as i64`，即 `0x00000000ffffffff`；`i64::data()` 逆转此编码。

因此 `i64` 键的整数表示不总等于原始 FFI 编码，不能直接将其整数值交给 `KeyData::from_ffi()`。外部存储应使用 `key.data().as_ffi()`，读取时走 `KeyData::from_ffi()` 再转换为键。任意手写整数值不保证符合有效键契约。

## 自定义键宏

宏支持多个类型、可见性和属性，生成独立类型并保存全部数据。为不同用途建立不同类型能减少混用，但不能验证某个键是否属于某个容器实例。

```rust
use pi_key::{new_key_type, Key};

new_key_type! {
    struct RocketKey;
    /// 用户键，与 RocketKey 是不同类型。
    pub struct UserKey;
}

let key = UserKey::with(12);
assert_eq!(key.data().index(), 12);
assert_eq!(key.data().version(), 0);
assert_eq!(RocketKey::default().data().index(), u32::MAX);
```

宏通过 `$crate::__impl` 重导出与完全限定的 `Null` 调用展开。仅声明类型无需直接依赖或导入 `pi_null`；`default()` 也无需它。可以用 `Key::data().index() == u32::MAX` 检查空性。

若调用 `null()` / `is_null()`，调用方需直接添加 `pi_null = "0.2.2"` 依赖并导入 trait：

```rust
use pi_key::{DefaultKey, Key};
use pi_null::Null;

let key = DefaultKey::null();
assert!(key.is_null());
assert_eq!(key.data().version(), 0);
```

## 版本回绕比较

`is_older_version(a, b)` 用模差 `(a - b) mod 2^32 > 2^31` 判断 `a` 是否更旧，支持最大版本回绕到零。相等或恰好相隔半周期时，两个方向都返回 `false`。只有实际时间间隔小于半周期时，结果才可用于判断先后；长跨度无法判定。`u32::MAX` 没有特殊哨兵语义。

完整 32 位版本的示例：

```rust
use pi_key::is_older_version;

let max = u32::MAX;
let half = 1u32 << 31;
assert!(is_older_version(max, 0));
assert!(!is_older_version(0, max));
assert!(!is_older_version(7, 7));
assert!(!is_older_version(0, half));
assert!(!is_older_version(half, 0));
```

## 消费者责任

`Key` 是安全 trait，并非 `unsafe trait`，不能把其实现视为不安全索引访问的证明。消费者负责检查空性、范围、容器归属和槽位版本，决定分配、回收、复用以及过期键处理方式。本库既不保证业务有效性，也不替下游承担 `unsafe` 访问的内存安全前提。

`key_data(idx, version)` 保留原有 `unsafe` API 签名；函数本身没有额外的内存安全前提，只构造数据，不检查容器有效性。新代码可使用安全的 `KeyData::new(idx, version)`。

## 验证

```sh
cargo fmt --check
cargo test
cargo test --features serde
cargo +nightly-x86_64-pc-windows-msvc test --all-features
cargo doc --no-deps
```
