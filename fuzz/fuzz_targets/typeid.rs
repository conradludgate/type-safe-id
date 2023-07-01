#![no_main]

use libfuzzer_sys::fuzz_target;
use type_safe_id::{TypeSafeId, DynamicType};

fuzz_target!(|id: TypeSafeId<DynamicType>| {
    let id2 = id.to_string().parse().unwrap();
    assert_eq!(id, id2);
});
