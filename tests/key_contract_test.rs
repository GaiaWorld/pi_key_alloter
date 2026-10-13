// @test: public Key and KeyData contracts agreed in this change.
use pi_key::{is_older_version, Key, KeyData};
use pi_null::Null;

mod macro_without_null_import {
    pi_key::new_key_type! { pub struct CustomKey; }
}

fn data(index: u32, version: u32) -> KeyData {
    KeyData::from_ffi((u64::from(version) << 32) | u64::from(index))
}

macro_rules! index_only_tests {
    ($($name:ident: $ty:ty => $max:expr),* $(,)?) => {
        $(mod $name {
            use super::*;

            #[test]
            fn discards_version_but_preserves_index() {
                let key = <$ty>::from(data(7, 42));
                assert_eq!(key.index(), 7);
                assert_eq!(key.data(), data(7, 0));
                assert_eq!(key, <$ty>::from(data(7, 43)));
            }

            #[test]
            fn accepts_largest_valid_index() {
                let index: u32 = $max;
                let key = <$ty as Key>::with(index as usize);
                assert!(!key.is_null());
                assert_eq!(key.index(), index as usize);
                assert_eq!(key.data(), data(index, 0));
                assert_eq!(<$ty>::from(data(index, 9)), key);
            }
        })*
    };
}

index_only_tests! {
    usize_key: usize => u32::MAX - 1,
    u32_key: u32 => u32::MAX - 1,
    i32_key: i32 => i32::MAX as u32,
    u16_key: u16 => u16::MAX as u32 - 1,
    i16_key: i16 => i16::MAX as u32,
    u8_key: u8 => u8::MAX as u32 - 1,
    i8_key: i8 => i8::MAX as u32,
}

#[test]
fn integer_conversions_preserve_nullness() {
    macro_rules! check {
        ($($ty:ty),*) => {
            $(assert!(<$ty>::from(KeyData::null()).is_null());
              assert!(<$ty>::from(data(u32::MAX, 42)).is_null());
              assert_eq!(<$ty>::null().data(), KeyData::null());
              assert!(!<$ty>::from(data(0, 0)).is_null());)*
        };
    }
    check!(usize, u64, i64, u32, i32, u16, i16, u8, i8);
}

#[test]
fn packed_integers_preserve_version_and_extract_index() {
    for index in [0, 7, u32::MAX - 1] {
        for version in [0, 42, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
            let original = data(index, version);
            let unsigned = u64::from(original);
            let signed = i64::from(original);
            assert!(!unsigned.is_null());
            assert!(!signed.is_null());
            assert_eq!(unsigned.data(), original);
            assert_eq!(signed.data(), original);
            assert_eq!(unsigned.index(), index as usize);
            assert_eq!(signed.index(), index as usize);
        }
    }
}

#[test]
fn out_of_range_indices_keep_rust_cast_behavior() {
    for index in [128u32, 255, 256, 257] {
        assert_eq!(<u8 as Key>::with(index as usize), index as u8);
        assert_eq!(<i8 as Key>::with(index as usize), index as i8);
        assert_eq!(u8::from(data(index, 42)), index as u8);
        assert_eq!(i8::from(data(index, 42)), index as i8);
    }
}

#[test]
fn macro_key_preserves_data_without_null_trait_import() {
    use macro_without_null_import::CustomKey;
    let original = data(7, 42);
    assert_eq!(CustomKey::from(original).data(), original);
    assert!(CustomKey::null().is_null());
}

#[cfg(feature = "bits21_version")]
const VERSION_BITS: u32 = 21;
#[cfg(not(feature = "bits21_version"))]
const VERSION_BITS: u32 = 32;

#[test]
fn compares_versions_across_wrap() {
    let last = u32::MAX >> (32 - VERSION_BITS);
    let wrapped = data(0, last.wrapping_add(1)).version();
    assert_eq!(wrapped, 0);
    assert!(is_older_version(last, wrapped));
    assert!(!is_older_version(wrapped, last));
    assert!(is_older_version(last - 1, last));
    assert!(!is_older_version(last, last - 1));
}

#[test]
fn equal_and_half_cycle_versions_are_not_ordered() {
    let half = 1u32 << (VERSION_BITS - 1);
    assert!(!is_older_version(7, 7));
    assert!(!is_older_version(0, half));
    assert!(!is_older_version(half, 0));
    assert!(is_older_version(0, 1));
    assert!(!is_older_version(1, 0));
}

#[test]
fn version_comparison_masks_inputs_to_configured_width() {
    assert_eq!(
        is_older_version(u32::MAX, 0),
        is_older_version(data(0, u32::MAX).version(), 0)
    );
}
