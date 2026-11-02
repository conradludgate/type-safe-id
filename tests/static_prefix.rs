use type_safe_id::{StaticType, Type};

macro_rules! prefix {
    ($name:ident, $value:literal) => {
        #[derive(Default)]
        struct $name;
        impl StaticType for $name {
            const TYPE: &'static str = $value;
        }
        const _: () = assert!($name::TYPE_PREFIX_IS_VALID);
    };
}

prefix!(Empty, "");
prefix!(Underscores, "a__b");
prefix!(
    MaximumLength,
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
);

#[test]
fn const_validation_accepts_prefix_boundaries() {
    assert_eq!(Empty.to_type_prefix(), "");
    assert_eq!(Underscores.to_type_prefix(), "a__b");
    assert_eq!(MaximumLength.to_type_prefix().len(), 63);
}
