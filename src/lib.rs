mod read;
mod write;

pub use read::Reader;
pub use write::Writer;

use num_bigint::{BigInt, BigUint};
use num_derive::FromPrimitive;
use ordered_float::OrderedFloat;
use std::collections::BTreeMap;

pub type Size = u32;

#[repr(u8)]
#[derive(Debug, Clone, Copy, Hash, FromPrimitive)]
pub enum ValueKind {
    Nil = 0,
    Bytes = 1,
    Bool = 2,
    U8 = 3,
    U16 = 4,
    U32 = 5,
    U64 = 6,
    U128 = 7,
    BigU = 8,
    I8 = 9,
    I16 = 10,
    I32 = 11,
    I64 = 12,
    I128 = 13,
    BigI = 14,
    F32 = 15,
    F64 = 16,
    Str = 17,
    Array = 18,
    Dict = 19,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytes {
    pub kind: Size,
    pub data: Vec<u8>,
}

impl Bytes {
    pub fn new(kind: Size, data: Vec<u8>) -> Self {
        Self { kind, data }
    }
}

pub type Array<T> = Vec<T>;

pub type Dict<K, V> = BTreeMap<K, V>;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    Nil,
    Bytes(Bytes),
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    BigU(BigUint),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    BigI(BigInt),
    F32(OrderedFloat<f32>),
    F64(OrderedFloat<f64>),
    Str(String),
    Array(Array<Self>),
    Dict(Dict<Self, Self>),
}

impl Value {
    pub fn is_nil(&self) -> bool {
        match self {
            Self::Nil => true,
            _ => false,
        }
    }

    pub fn is_bytes(&self) -> bool {
        match self {
            Self::Bytes(_) => true,
            _ => false,
        }
    }

    pub fn as_bytes(&self) -> Option<&Bytes> {
        match self {
            Self::Bytes(bytes) => Some(bytes),
            _ => None,
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            _ => false,
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match *self {
            Self::Bool(b) => Some(b),
            _ => None,
        }
    }

    pub fn is_biguint(&self) -> bool {
        match self {
            Self::BigU(_) => true,
            _ => false,
        }
    }

    pub fn as_biguint(&self) -> Option<&BigUint> {
        match self {
            Self::BigU(i) => Some(i),
            _ => None,
        }
    }

    pub fn is_bigint(&self) -> bool {
        match self {
            Self::BigI(_) => true,
            _ => false,
        }
    }

    pub fn as_bigint(&self) -> Option<&BigInt> {
        match self {
            Self::BigI(i) => Some(i),
            _ => None,
        }
    }

    pub fn is_f32(&self) -> bool {
        match self {
            Self::F32(_) => true,
            _ => false,
        }
    }

    pub fn as_f32(&self) -> Option<f32> {
        match self {
            Self::F32(i) => Some(i.into_inner()),
            _ => None,
        }
    }

    pub fn is_f64(&self) -> bool {
        match self {
            Self::F64(_) => true,
            _ => false,
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Self::F64(i) => Some(i.into_inner()),
            _ => None,
        }
    }

    pub fn is_str(&self) -> bool {
        match self {
            Self::Str(_) => true,
            _ => false,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_array(&self) -> bool {
        match self {
            Self::Array(_) => true,
            _ => false,
        }
    }

    pub fn as_array(&self) -> Option<&[Value]> {
        match self {
            Self::Array(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_dict(&self) -> bool {
        match self {
            Self::Dict(_) => true,
            _ => false,
        }
    }

    pub fn as_dict(&self) -> Option<&Dict<Self, Self>> {
        match self {
            Self::Dict(s) => Some(s),
            _ => None,
        }
    }
}

macro_rules! impl_as {
    ($is:ident, $as:ident, $enum:ident, $ty:ty) => {
        impl Value {
            pub fn $is(&self) -> bool {
                match self {
                    Self::$enum(_) => true,
                    _ => false,
                }
            }

            pub fn $as(&self) -> Option<$ty> {
                match *self {
                    Self::$enum(i) => Some(i),
                    _ => None,
                }
            }
        }
    };
}

impl_as!(is_u8, as_u8, U8, u8);
impl_as!(is_u16, as_u16, U16, u16);
impl_as!(is_u32, as_u32, U32, u32);
impl_as!(is_u64, as_u64, U64, u64);
impl_as!(is_u128, as_u128, U128, u128);
impl_as!(is_i8, as_i8, I8, i8);
impl_as!(is_i16, as_i16, I16, i16);
impl_as!(is_i32, as_i32, I32, i32);
impl_as!(is_i64, as_i64, I64, i64);
impl_as!(is_i128, as_i128, I128, i128);

macro_rules! impl_from {
    ($int:ty, $enum:ident) => {
        impl From<$int> for Value {
            fn from(data: $int) -> Self {
                Self::$enum(data)
            }
        }
    };
}

impl_from!(Bytes, Bytes);
impl_from!(bool, Bool);
impl_from!(u8, U8);
impl_from!(u16, U16);
impl_from!(u32, U32);
impl_from!(u64, U64);
impl_from!(u128, U128);
impl_from!(BigUint, BigU);
impl_from!(i8, I8);
impl_from!(i16, I16);
impl_from!(i32, I32);
impl_from!(i64, I64);
impl_from!(i128, I128);
impl_from!(BigInt, BigI);
impl_from!(String, Str);

impl From<f32> for Value {
    fn from(data: f32) -> Self {
        Self::F32(OrderedFloat::from(data))
    }
}

impl From<f64> for Value {
    fn from(data: f64) -> Self {
        Self::F64(OrderedFloat::from(data))
    }
}

impl<T> From<Array<T>> for Value
where
    T: Into<Self>,
{
    fn from(data: Array<T>) -> Self {
        Self::Array(data.into_iter().map(|v| v.into()).collect())
    }
}

impl<K, V> From<Dict<K, V>> for Value
where
    K: Into<Self>,
    V: Into<Self>,
{
    fn from(data: Dict<K, V>) -> Self {
        Self::Dict(
            data.into_iter()
                .map(|(k, v)| (k.into(), v.into()))
                .collect(),
        )
    }
}
