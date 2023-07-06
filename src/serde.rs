use std::fmt;

use serde::{Deserialize, Serialize};

use crate::{DynamicType, StaticType, Type, TypeSafeId};

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<T: Type> Serialize for TypeSafeId<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&super::to_array_string(self.type_prefix(), self.data))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de, T: StaticType> Deserialize<'de> for TypeSafeId<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct FromStrVisitor<T>(std::marker::PhantomData<T>);
        impl<'de, T: StaticType> serde::de::Visitor<'de> for FromStrVisitor<T> {
            type Value = TypeSafeId<T>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(
                    formatter,
                    "a string containing a type-id with {:?} type prefix",
                    T::TYPE
                )
            }
            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                v.parse().map_err(E::custom)
            }
        }
        deserializer.deserialize_str(FromStrVisitor(std::marker::PhantomData))
    }
}

#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> Deserialize<'de> for TypeSafeId<DynamicType> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct FromStrVisitor;
        impl<'de> serde::de::Visitor<'de> for FromStrVisitor {
            type Value = TypeSafeId<DynamicType>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "a string containing a type-id")
            }
            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                v.parse().map_err(E::custom)
            }
        }
        deserializer.deserialize_str(FromStrVisitor)
    }
}
