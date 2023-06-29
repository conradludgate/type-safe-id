//! A type-safe, K-sortable, globally unique identifier
//!
//! ```
//! use type_safe_id::{StaticType, TypeSafeId};
//!
//! #[derive(Default)]
//! struct User;
//!
//! impl StaticType for User {
//!     // must be lowercase ascii [a-z] only
//!     const TYPE: &'static str = "user";
//! }
//!
//! // type alias for your custom typed id
//! type UserId = TypeSafeId<User>;
//!
//! let user_id1 = UserId::new().expect("type should be lowercase ascii");
//! # std::thread::sleep(std::time::Duration::from_millis(10));
//! let user_id2 = UserId::new().expect("type should be lowercase ascii");
//!
//! let uid1 = user_id1.to_string();
//! let uid2 = user_id2.to_string();
//! dbg!(&uid1, &uid2);
//! assert!(uid2 > uid1, "type safe IDs are ordered");
//!
//! let user_id3: UserId = uid1.parse().expect("invalid user id");
//! let user_id4: UserId = uid2.parse().expect("invalid user id");
//!
//! assert_eq!(user_id1.uuid(), user_id3.uuid(), "round trip works");
//! assert_eq!(user_id2.uuid(), user_id4.uuid(), "round trip works");
//! ```
#![cfg_attr(docsrs, feature(doc_cfg))]

use std::{
    fmt::{self, Write},
    str::FromStr,
};

use uuid::{NoContext, Uuid};

#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The ID type was not valid
    #[error("id type is invalid")]
    InvalidType,
    /// The ID type did not match the expected type
    #[error("id type {actual:?} does not match expected {expected:?}")]
    IncorrectType {
        actual: smol_str::SmolStr,
        expected: &'static str,
    },
    /// The ID data was not valid
    #[error("id data is invalid")]
    InvalidData,
    /// The string was not formed as a type-id
    #[error("string is not a type-id")]
    NotATypeId,
}

/// A static type prefix
pub trait StaticType: Default {
    /// must be lowercase ascii [a-z] only
    const TYPE: &'static str;
}

/// Represents a type that can serialize to and be parsed from a tag
pub trait Type: Sized {
    /// Try convert the prefix into the well known type.
    /// If the prefix is incorrect, return the expected prefix.
    fn try_from_type_prefix(tag: &str) -> Result<Self, &'static str>;

    /// Get the prefix from this type
    fn to_type_prefix(&self) -> &str;
}

impl<T: StaticType> Type for T {
    fn try_from_type_prefix(tag: &str) -> Result<Self, &'static str> {
        if tag != Self::TYPE {
            Err(Self::TYPE)
        } else {
            Ok(T::default())
        }
    }

    fn to_type_prefix(&self) -> &str {
        Self::TYPE
    }
}

/// A dynamic type prefix
///
/// ```
/// use type_safe_id::{DynamicType, TypeSafeId};
///
/// let id: TypeSafeId<DynamicType> = "prefix_01h2xcejqtf2nbrexx3vqjhp41".parse().unwrap();
///
/// assert_eq!(id.type_prefix(), "prefix");
/// assert_eq!(id.uuid(), uuid::uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881"));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DynamicType(smol_str::SmolStr);

impl DynamicType {
    /// Create a new type prefix from a dynamic str
    ///
    /// ```
    /// use type_safe_id::{DynamicType, TypeSafeId};
    ///
    /// let dynamic_type = DynamicType::new("prefix");
    ///
    /// let data = uuid::uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881");
    /// let id = TypeSafeId::from_type_and_uuid(dynamic_type, data).unwrap();
    ///
    /// assert_eq!(id.to_string(), "prefix_01h2xcejqtf2nbrexx3vqjhp41");
    /// ```
    pub fn new(s: &str) -> Self {
        Self(s.into())
    }
}

impl Type for DynamicType {
    fn try_from_type_prefix(tag: &str) -> Result<Self, &'static str> {
        Ok(Self(tag.into()))
    }

    fn to_type_prefix(&self) -> &str {
        &self.0
    }
}

/// A typed UUID.
///
/// ```
/// use type_safe_id::{StaticType, TypeSafeId};
///
/// #[derive(Default)]
/// struct User;
///
/// impl StaticType for User {
///     // must be lowercase ascii [a-z] only
///     const TYPE: &'static str = "user";
/// }
///
/// // type alias for your custom typed id
/// type UserId = TypeSafeId<User>;
///
/// let user_id1 = UserId::new().expect("type should be lowercase ascii");
/// # std::thread::sleep(std::time::Duration::from_millis(10));
/// let user_id2 = UserId::new().expect("type should be lowercase ascii");
///
/// let uid1 = user_id1.to_string();
/// let uid2 = user_id2.to_string();
/// dbg!(&uid1, &uid2);
/// assert!(uid2 > uid1, "type safe IDs are ordered");
///
/// let user_id3: UserId = uid1.parse().expect("invalid user id");
/// let user_id4: UserId = uid2.parse().expect("invalid user id");
///
/// assert_eq!(user_id1.uuid(), user_id3.uuid(), "round trip works");
/// assert_eq!(user_id2.uuid(), user_id4.uuid(), "round trip works");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeSafeId<T> {
    tag: T,
    data: Uuid,
}

impl<T: StaticType> TypeSafeId<T> {
    /// Create a new type-id
    pub fn new() -> Result<Self, Error> {
        Self::new_with_ts_rng(
            T::default(),
            uuid::Timestamp::now(NoContext),
            &mut rand::thread_rng(),
        )
    }

    /// Create a new type-id from the given uuid data
    pub fn from_uuid(data: Uuid) -> Result<Self, Error> {
        Self::from_type_and_uuid(T::default(), data)
    }
}

impl<T: Type> TypeSafeId<T> {
    /// Create a new type-id with the given type prefix
    pub fn new_with_type(type_prefix: T) -> Result<Self, Error> {
        Self::new_with_ts_rng(
            type_prefix,
            uuid::Timestamp::now(NoContext),
            &mut rand::thread_rng(),
        )
    }

    fn new_with_ts_rng(
        type_prefix: T,
        ts: uuid::Timestamp,
        rng: &mut impl rand::Rng,
    ) -> Result<Self, Error> {
        Self::from_type_and_uuid(type_prefix, encode_unix_timestamp_millis(ts, &rng.gen()))
    }

    /// Create a new type-id with the given type prefix and uuid data
    pub fn from_type_and_uuid(type_prefix: T, data: Uuid) -> Result<Self, Error> {
        let t = type_prefix.to_type_prefix();
        if t.len() > 63 || t.bytes().any(|b| !b.is_ascii_lowercase()) {
            return Err(Error::InvalidType);
        }

        Ok(Self {
            tag: type_prefix,
            data,
        })
    }

    pub fn type_prefix(&self) -> &str {
        self.tag.to_type_prefix()
    }
    pub fn uuid(&self) -> Uuid {
        self.data
    }
}

impl<T: Type> FromStr for TypeSafeId<T> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.split_once('_') {
            Some((tag, id)) => {
                let tag =
                    T::try_from_type_prefix(tag).map_err(|expected| Error::IncorrectType {
                        actual: tag.into(),
                        expected,
                    })?;

                let mut id: [u8; 26] = id.as_bytes().try_into().map_err(|_| Error::InvalidData)?;
                let mut max = 0;
                for b in &mut id {
                    *b = CROCKFORD_INV[*b as usize];
                    max = u8::max(max, *b);
                }
                if max > 32 {
                    return Err(Error::InvalidData);
                }

                let mut out = 0u128;
                for b in id {
                    out <<= 5;
                    out |= b as u128;
                }

                Ok(Self {
                    tag,
                    data: Uuid::from_bytes(out.to_be_bytes()),
                })
            }
            None => Err(Error::NotATypeId),
        }
    }
}

impl<T: Type> fmt::Display for TypeSafeId<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0; 26];
        let mut x = u128::from_be_bytes(*self.data.as_bytes());
        for b in buf.iter_mut().rev() {
            *b = CROCKFORD[((x as u8) & 0x1f) as usize];
            x >>= 5;
        }
        let s = std::str::from_utf8(&buf).map_err(|_| fmt::Error)?;
        f.write_str(self.tag.to_type_prefix())?;
        f.write_char('_')?;
        f.write_str(s)
    }
}

// basically just ripped from the uuid crate. they have it as unstable, but we can use it fine.
#[inline]
const fn encode_unix_timestamp_millis(ts: uuid::Timestamp, random_bytes: &[u8; 10]) -> Uuid {
    let (secs, nanos) = ts.to_unix();
    let millis = (secs * 1000).saturating_add(nanos as u64 / 1_000_000);
    let millis_high = ((millis >> 16) & 0xFFFF_FFFF) as u32;
    let millis_low = (millis & 0xFFFF) as u16;

    let random_and_version =
        (random_bytes[0] as u16 | ((random_bytes[1] as u16) << 8) & 0x0FFF) | (0x7 << 12);

    let mut d4 = [0; 8];

    d4[0] = (random_bytes[2] & 0x3F) | 0x80;
    d4[1] = random_bytes[3];
    d4[2] = random_bytes[4];
    d4[3] = random_bytes[5];
    d4[4] = random_bytes[6];
    d4[5] = random_bytes[7];
    d4[6] = random_bytes[8];
    d4[7] = random_bytes[9];

    Uuid::from_fields(millis_high, millis_low, random_and_version, &d4)
}

const CROCKFORD: &[u8; 32] = b"0123456789abcdefghjkmnpqrstvwxyz";
const CROCKFORD_INV: &[u8; 256] = &{
    let mut output = [255; 256];

    let mut i = 0;
    while i < 32 {
        output[CROCKFORD[i as usize] as usize] = i;
        i += 1;
    }

    // uppercases
    let mut i = 10;
    while i < 32 {
        output[(CROCKFORD[i as usize] - b'a' + b'A') as usize] = i;
        i += 1;
    }

    // confusables
    output[b'O' as usize] = 0;
    output[b'o' as usize] = 0;

    output[b'I' as usize] = 1;
    output[b'i' as usize] = 1;
    output[b'L' as usize] = 1;
    output[b'l' as usize] = 1;

    output
};

#[cfg(feature = "serde")]
mod serde_impl {
    use std::fmt;

    use serde::{Deserialize, Serialize};

    use crate::{DynamicType, StaticType, Type, TypeSafeId};

    #[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
    impl<T: Type> Serialize for TypeSafeId<T> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.collect_str(self)
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
                    write!(formatter, "a type-id with {:?} type prefix", T::TYPE)
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
                    write!(formatter, "a type-id")
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
}

#[cfg(test)]
mod tests {

    use crate::{StaticType, TypeSafeId};

    #[derive(Default)]
    struct Prefix;

    impl StaticType for Prefix {
        const TYPE: &'static str = "prefix";
    }

    type PrefixId = TypeSafeId<Prefix>;

    #[test]
    fn works() {
        let str = "prefix_01h2xcejqtf2nbrexx3vqjhp41";
        let uuid = uuid::uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881");

        let uid: PrefixId = str.parse().unwrap();

        assert_eq!(uid.uuid(), uuid);
        assert_eq!(uid.to_string(), str);
    }
}