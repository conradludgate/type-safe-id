#![no_main]

use libfuzzer_sys::fuzz_target;
use type_safe_id::{TypeSafeId, StaticType};

fuzz_target!(|id: TypeSafeId<Type>| {
    let id2 = id.to_string().parse().unwrap();
    assert_eq!(id, id2);
});

#[derive(Default, Debug, PartialEq)]
struct Type;
impl StaticType for Type {
    const TYPE: &'static str = "type";
}
