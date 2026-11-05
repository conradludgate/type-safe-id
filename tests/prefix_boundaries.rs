use type_safe_id::{DynamicType, Type};

#[test]
fn overlong_unicode_prefixes_return_errors_without_splitting_characters() {
    for prefix in [
        "é".repeat(32),
        format!("{}é", "a".repeat(62)),
        format!("{}🦀", "a".repeat(60)),
    ] {
        let expected = DynamicType::try_from_type_prefix(&prefix).unwrap_err();
        assert!(expected.len() <= 63);
        assert!(prefix.starts_with(expected.as_ref()));
    }
}

#[test]
fn overlong_ascii_prefix_keeps_its_existing_hint() {
    let prefix = "a".repeat(64);
    assert_eq!(
        DynamicType::try_from_type_prefix(&prefix).unwrap_err(),
        "a".repeat(63)
    );
}
