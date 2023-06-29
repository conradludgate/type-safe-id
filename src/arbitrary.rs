use arbitrary::{Arbitrary, Result, Unstructured};

use crate::{encode_unix_timestamp_millis, DynamicType, StaticType, TypeSafeId};

#[cfg_attr(docsrs, doc(cfg(feature = "arbitrary")))]
impl<'a, T: StaticType> Arbitrary<'a> for TypeSafeId<T> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let millis = u.arbitrary::<u64>()? & 0xFFFF_FFFF_FFFF; // 48 bits
        let data: [u8; 10] = u.arbitrary()?;

        Self::from_type_and_uuid(T::default(), encode_unix_timestamp_millis(millis, &data))
            .map_err(|_| arbitrary::Error::IncorrectFormat)
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "arbitrary")))]
impl<'a> Arbitrary<'a> for DynamicType {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        u.arbitrary().map(DynamicType)
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "arbitrary")))]
impl<'a> Arbitrary<'a> for TypeSafeId<DynamicType> {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let tag: DynamicType = u.arbitrary()?;
        let millis = u.arbitrary::<u64>()? & 0xFFFF_FFFF_FFFF; // 48 bits
        let data: [u8; 10] = u.arbitrary()?;

        Self::from_type_and_uuid(tag, encode_unix_timestamp_millis(millis, &data))
            .map_err(|_| arbitrary::Error::IncorrectFormat)
    }
}
