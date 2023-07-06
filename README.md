# type-safe-id

A type-safe, K-sortable, globally unique identifier.

Typed implementation of <https://github.com/jetpack-io/typeid> in Rust.

# Examples

## StaticType prefixes

This is the intended happy path. Using a StaticType implementation, you ensure
that the ID being parsed is of the intended type.

```rust
use type_safe_id::{StaticType, TypeSafeId};

#[derive(Default)]
struct User;

impl StaticType for User {
    // must be lowercase ascii [a-z] only
    const TYPE: &'static str = "user";
}

// type alias for your custom typed id
type UserId = TypeSafeId<User>;

let user_id1 = UserId::new();
# std::thread::sleep(std::time::Duration::from_millis(10));
let user_id2 = UserId::new();

let uid1 = user_id1.to_string();
let uid2 = user_id2.to_string();
dbg!(&uid1, &uid2);
assert!(uid2 > uid1, "type safe IDs are ordered");

let user_id3: UserId = uid1.parse().expect("invalid user id");
let user_id4: UserId = uid2.parse().expect("invalid user id");

assert_eq!(user_id1.uuid(), user_id3.uuid(), "round trip works");
assert_eq!(user_id2.uuid(), user_id4.uuid(), "round trip works");
```

## DynamicType prefixes

If you can't know what the prefix will be, you can use the DynamicType prefix.

```rust
use type_safe_id::{DynamicType, TypeSafeId};

let id: TypeSafeId<DynamicType> = "prefix_01h2xcejqtf2nbrexx3vqjhp41".parse().unwrap();

assert_eq!(id.type_prefix(), "prefix");
assert_eq!(id.uuid(), uuid::uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881"));
```

# Help

```rust
error[E0080]: evaluation of `<Index as type_safe_id::StaticType>::__TYPE_PREFIX_IS_VALID` failed
  --> /Users/conrad/Documents/code/type-safe-id/src/lib.rs:76:13
   |
76 |             assert!(Self::TYPE.as_bytes()[i].is_ascii_lowercase());
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the evaluated program panicked at 'assertion failed: Self::TYPE.as_bytes()[i].is_ascii_lowercase()', /Users/conrad/Documents/code/type-safe-id/src/lib.rs:76:13
```

This compiler error suggests that your static type prefix is not valid because it contains non ascii-lowercase values.

```rust
error[E0080]: evaluation of `<Index as type_safe_id::StaticType>::__TYPE_PREFIX_IS_VALID` failed
  --> /Users/conrad/Documents/code/type-safe-id/src/lib.rs:73:9
   |
73 |         assert!(Self::TYPE.len() < 64);
   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the evaluated program panicked at 'assertion failed: Self::TYPE.len() < 64', /Users/conrad/Documents/code/type-safe-id/src/lib.rs:73:9
   |
```

This compiler error suggests that your static type prefix is not valid because it contains more than 63 characters.
