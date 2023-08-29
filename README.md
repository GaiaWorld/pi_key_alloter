# pi_key_alloter

[![Crate](https://img.shields.io/crates/v/pi_key_alloter?style=for-the-badge)](https://crates.io/crates/pi_key_alloter)
[![Github](https://img.shields.io/badge/github-pi_key_alloter-success?style=for-the-badge)](https://github.com/GaiaWorld/pi_key_alloter)
[![Docs](https://img.shields.io/badge/docs.rs-0.2.2-4d76ae?style=for-the-badge)](https://docs.rs/pi_key_alloter)

lock-free Key(idx:u32, version:u32) alloter.

# Examples

alloc key:

```rust
let alloter = pi_key_alloter::KeyAlloter::new(0);
let k = alloter.alloc();
assert_eq!(0, k.index());
assert_eq!(1, k.version());
alloter.recycle(k);
let k = alloter.alloc();
assert_eq!(0, k.index());
assert_eq!(2, k.version());
let k = alloter.alloc();
assert_eq!(1, k.index());
assert_eq!(1, k.version());
```

The alloter can be shared across threads with an `Arc`:

```rust
use std::sync::Arc;

fn main() {
    let alloter = Arc::new(pi_key_alloter::KeyAlloter::new());

    // spawn 6 threads that append to the arr
    let threads = (0..6)
        .map(|i| {
            let alloter = alloter.clone();

            std::thread::spawn(move || {
                let _ = alloter.alloc();
            })
        })
        .collect::<Vec<_>>();

    // wait for the threads to finish
    for thread in threads {
        thread.join().unwrap();
    }
    let k = alloter.alloc();
    assert_eq!(6, k.index());
    assert_eq!(1, k.version());
    
}
```

