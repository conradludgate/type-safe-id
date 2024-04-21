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
//! let user_id1 = UserId::new();
//! # std::thread::sleep(std::time::Duration::from_millis(10));
//! let user_id2 = UserId::new();
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
#![forbid(unsafe_code)]

#[cfg(feature = "arbitrary")]
mod arbitrary;

#[cfg(feature = "serde")]
mod serde;

use std::{borrow::Cow, fmt, str::FromStr};

use arrayvec::ArrayString;
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
        actual: String,
        expected: Cow<'static, str>,
    },
    /// The ID suffix was not valid
    #[error("id suffix is invalid")]
    InvalidData,
    /// The string was not formed as a type-id
    #[error("string is not a type-id")]
    NotATypeId,
}

/// A static type prefix
pub trait StaticType: Default {
    /// must be lowercase ascii [a-z_] only, under 64 characters.
    /// first character cannot be an underscore
    const TYPE: &'static str;

    #[doc(hidden)]
    const __TYPE_PREFIX_IS_VALID: bool = {
        assert!(Self::TYPE.len() < 64);
        let mut i = 0;
        while i < Self::TYPE.len() {
            let b = Self::TYPE.as_bytes()[i];
            assert!(
                matches!(b, b'a'..=b'z' | b'_'),
                "type prefix must contain only lowercase ascii, or underscores"
            );
            i += 1;
        }
        if !Self::TYPE.is_empty() {
            assert!(
                Self::TYPE.as_bytes()[0] != b'_',
                "type prefix must not start with an underscore"
            );
            assert!(
                Self::TYPE.as_bytes()[i - 1] != b'_',
                "type prefix must not end with an underscore"
            );
        }
        true
    };
}

/// Represents a type that can serialize to and be parsed from a tag
pub trait Type: Sized {
    /// Try convert the prefix into the well known type.
    /// If the prefix is incorrect, return the expected prefix.
    fn try_from_type_prefix(tag: &str) -> Result<Self, Cow<'static, str>>;

    /// Get the prefix from this type
    fn to_type_prefix(&self) -> &str;
}

impl<T: StaticType> Type for T {
    fn try_from_type_prefix(tag: &str) -> Result<Self, Cow<'static, str>> {
        assert!(Self::__TYPE_PREFIX_IS_VALID);
        if tag != Self::TYPE {
            Err(Self::TYPE.into())
        } else {
            Ok(T::default())
        }
    }

    fn to_type_prefix(&self) -> &str {
        assert!(Self::__TYPE_PREFIX_IS_VALID);
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
pub struct DynamicType(ArrayString<63>);

impl DynamicType {
    /// Create a new type prefix from a dynamic str
    ///
    /// ```
    /// use type_safe_id::{DynamicType, TypeSafeId};
    ///
    /// let dynamic_type = DynamicType::new("prefix").unwrap();
    ///
    /// let data = uuid::uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881");
    /// let id = TypeSafeId::from_type_and_uuid(dynamic_type, data);
    ///
    /// assert_eq!(id.to_string(), "prefix_01h2xcejqtf2nbrexx3vqjhp41");
    /// ```
    pub fn new(s: &str) -> Result<Self, Error> {
        let tag: ArrayString<63> = s.try_into().map_err(|_| Error::InvalidType)?;

        if tag.bytes().any(|b| !matches!(b, b'a'..=b'z' | b'_')) {
            return Err(Error::InvalidType);
        }
        if !tag.is_empty() && (tag.as_bytes()[0] == b'_' || tag.as_bytes()[tag.len() - 1] == b'_') {
            return Err(Error::InvalidType);
        }
        Ok(Self(tag))
    }
}

impl Type for DynamicType {
    fn try_from_type_prefix(tag: &str) -> Result<Self, Cow<'static, str>> {
        let tag: ArrayString<63> = tag.try_into().map_err(|_| tag[..63].to_owned())?;
        if tag.bytes().any(|b| !matches!(b, b'a'..=b'z' | b'_')) {
            return Err(tag.to_lowercase().into());
        }
        if !tag.is_empty() && (tag.as_bytes()[0] == b'_' || tag.as_bytes()[tag.len() - 1] == b'_') {
            return Err(tag.to_lowercase().into());
        }
        Ok(Self(tag))
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
/// let user_id1 = UserId::new();
/// # std::thread::sleep(std::time::Duration::from_millis(10));
/// let user_id2 = UserId::new();
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
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeSafeId<T> {
    tag: T,
    data: Uuid,
}

impl<T: Type> fmt::Debug for TypeSafeId<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TypeSafeId")
            .field("tag", &self.tag.to_type_prefix())
            .field("data", &self.data)
            .finish()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Uuid128(u128);

impl From<Uuid> for Uuid128 {
    fn from(value: Uuid) -> Self {
        Self(u128::from_be_bytes(value.into_bytes()))
    }
}
impl From<Uuid128> for Uuid {
    fn from(value: Uuid128) -> Self {
        Uuid::from_bytes(value.0.to_be_bytes())
    }
}

impl<T: StaticType> TypeSafeId<T> {
    /// Create a new type-id
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self::new_with_ts_rng(
            T::default(),
            uuid::Timestamp::now(NoContext),
            &mut rand::thread_rng(),
        )
    }

    /// Create a new type-id from the given uuid data
    pub fn from_uuid(data: Uuid) -> Self {
        Self::from_type_and_uuid(T::default(), data)
    }
}

impl<T: Type> TypeSafeId<T> {
    /// Create a new type-id with the given type prefix
    pub fn new_with_type(type_prefix: T) -> Self {
        Self::new_with_ts_rng(
            type_prefix,
            uuid::Timestamp::now(NoContext),
            &mut rand::thread_rng(),
        )
    }

    fn new_with_ts_rng(type_prefix: T, ts: uuid::Timestamp, rng: &mut impl rand::Rng) -> Self {
        let (secs, nanos) = ts.to_unix();
        let millis = (secs * 1000).saturating_add(nanos as u64 / 1_000_000);
        Self::from_type_and_uuid(
            type_prefix,
            encode_unix_timestamp_millis(millis, &rng.gen()),
        )
    }

    /// Create a new type-id with the given type prefix and uuid data
    pub fn from_type_and_uuid(type_prefix: T, data: Uuid) -> Self {
        Self {
            tag: type_prefix,
            data,
        }
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

    fn from_str(id: &str) -> Result<Self, Self::Err> {
        let (tag, id) = match id.rsplit_once('_') {
            Some(("", _)) => return Err(Error::InvalidType),
            Some((tag, id)) => (tag, id),
            None => ("", id),
        };

        let tag = T::try_from_type_prefix(tag).map_err(|expected| Error::IncorrectType {
            actual: tag.into(),
            expected,
        })?;

        Ok(Self {
            tag,
            data: parse_base32_uuid7(id)?.into(),
        })
    }
}

fn parse_base32_uuid7(id: &str) -> Result<Uuid128, Error> {
    let mut id: [u8; 26] = id.as_bytes().try_into().map_err(|_| Error::InvalidData)?;
    let mut max = 0;
    for b in &mut id {
        *b = CROCKFORD_INV[*b as usize];
        max |= *b;
    }
    if max > 32 || id[0] > 7 {
        return Err(Error::InvalidData);
    }

    let mut out = 0u128;
    for b in id {
        out <<= 5;
        out |= b as u128;
    }

    Ok(Uuid128(out))
}

impl<T: Type> fmt::Display for TypeSafeId<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&to_array_string(self.type_prefix(), self.data.into()))
    }
}

fn to_array_string(prefix: &str, data: Uuid128) -> ArrayString<90> {
    let mut out = ArrayString::new();

    if !prefix.is_empty() {
        out.push_str(prefix);
        out.push_str("_");
    }

    let mut buf = [0; 26];
    let mut data = data.0;
    for b in buf.iter_mut().rev() {
        *b = CROCKFORD[((data as u8) & 0x1f) as usize];
        debug_assert!(b.is_ascii());
        data >>= 5;
    }

    let s = std::str::from_utf8(&buf).expect("only ascii bytes should be in the buffer");

    out.push_str(s);
    out
}

// basically just ripped from the uuid crate. they have it as unstable, but we can use it fine.
const fn encode_unix_timestamp_millis(millis: u64, random_bytes: &[u8; 10]) -> Uuid {
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

    output
};
