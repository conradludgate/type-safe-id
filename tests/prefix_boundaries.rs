use type_safe_id::{DynamicType, StaticType, Type, TypeSafeId};

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

#[derive(Default)]
struct Empty;

impl StaticType for Empty {
    const TYPE: &'static str = "";
}

#[test]
fn empty_prefix_length_matches_the_encoding() {
    let id = TypeSafeId::<Empty>::from_uuid(uuid::Uuid::nil());
    assert_eq!(id.to_string().len(), 26);
    assert_eq!(id.len(), id.to_string().len());
    assert_eq!(TypeSafeId::<Empty>::static_len(), id.len());

    let dynamic = TypeSafeId::from_type_and_uuid(DynamicType::new("").unwrap(), uuid::Uuid::nil());
    assert_eq!(dynamic.len(), dynamic.to_string().len());
}

#[test]
fn nonempty_prefix_length_includes_one_separator() {
    let dynamic =
        TypeSafeId::from_type_and_uuid(DynamicType::new("user").unwrap(), uuid::Uuid::nil());
    assert_eq!(dynamic.len(), dynamic.to_string().len());
    assert_eq!(dynamic.len(), 31);
}
