use crate::{Array, Bytes, Dict, Value, ValueKind};
use byteorder::{NetworkEndian, ReadBytesExt};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::FromPrimitive;
use ordered_float::OrderedFloat;
use std::io;
use std::string::FromUtf8Error;

pub struct Reader<R>
where
    R: io::Read,
{
    reader: R,
}

impl<R> Reader<R>
where
    R: io::Read,
{
    pub fn new(reader: R) -> Self {
        Self { reader }
    }

    pub fn read(&mut self) -> Result<Value, Error> {
        let kind = self.reader.read_u8()?;
        if let Some(kind) = ValueKind::from_u8(kind) {
            match kind {
                ValueKind::Nil => Ok(Value::Nil),
                ValueKind::Bytes => {
                    let bytes_kind = self.reader.read_u32::<NetworkEndian>()?;
                    let bytes_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut bytes_buf = vec![0; bytes_len as usize];
                    self.reader.read_exact(&mut bytes_buf)?;
                    Ok(Value::Bytes(Bytes {
                        kind: bytes_kind,
                        data: bytes_buf,
                    }))
                }
                ValueKind::Bool => {
                    let value = self.reader.read_u8()?;
                    Ok(Value::Bool(if value == 1 {
                        true
                    } else if value == 0 {
                        false
                    } else {
                        return Err(Error::OutOfBoundBool(value));
                    }))
                }
                ValueKind::U8 => Ok(Value::U8(self.reader.read_u8()?)),
                ValueKind::U16 => Ok(Value::U16(self.reader.read_u16::<NetworkEndian>()?)),
                ValueKind::U32 => Ok(Value::U32(self.reader.read_u32::<NetworkEndian>()?)),
                ValueKind::U64 => Ok(Value::U64(self.reader.read_u64::<NetworkEndian>()?)),
                ValueKind::U128 => Ok(Value::U128(self.reader.read_u128::<NetworkEndian>()?)),
                ValueKind::BigU => {
                    let bytes_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut bytes_buf = vec![0; bytes_len as usize];
                    self.reader.read_exact(&mut bytes_buf)?;
                    Ok(Value::BigU(BigUint::from_bytes_be(&bytes_buf)))
                }
                ValueKind::I8 => Ok(Value::I8(self.reader.read_i8()?)),
                ValueKind::I16 => Ok(Value::I16(self.reader.read_i16::<NetworkEndian>()?)),
                ValueKind::I32 => Ok(Value::I32(self.reader.read_i32::<NetworkEndian>()?)),
                ValueKind::I64 => Ok(Value::I64(self.reader.read_i64::<NetworkEndian>()?)),
                ValueKind::I128 => Ok(Value::I128(self.reader.read_i128::<NetworkEndian>()?)),
                ValueKind::BigI => {
                    let sign = match self.reader.read_u8()? {
                        0 => Sign::Minus,
                        1 => Sign::NoSign,
                        2 => Sign::Plus,
                        s => return Err(Error::OutOfBoundSign(s)),
                    };
                    let bytes_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut bytes_buf = vec![0; bytes_len as usize];
                    self.reader.read_exact(&mut bytes_buf)?;
                    Ok(Value::BigI(BigInt::from_bytes_be(sign, &bytes_buf)))
                }
                ValueKind::F32 => Ok(Value::F32(OrderedFloat::from(
                    self.reader.read_f32::<NetworkEndian>()?,
                ))),
                ValueKind::F64 => Ok(Value::F64(OrderedFloat::from(
                    self.reader.read_f64::<NetworkEndian>()?,
                ))),
                ValueKind::Str => {
                    let str_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut str_buf = vec![0; str_len as usize];
                    self.reader.read_exact(&mut str_buf)?;
                    Ok(Value::Str(String::from_utf8(str_buf)?))
                }
                ValueKind::Array => {
                    let data_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut data_buf = Array::with_capacity(data_len as usize);
                    for _ in 0..data_len {
                        data_buf.push(self.read()?)
                    }
                    Ok(Value::Array(data_buf))
                }
                ValueKind::Dict => {
                    let data_len = self.reader.read_u32::<NetworkEndian>()?;
                    let mut data_buf = Dict::new();
                    for _ in 0..data_len {
                        let key = self.read()?;
                        let value = self.read()?;
                        data_buf.insert(key, value);
                    }
                    Ok(Value::Dict(data_buf))
                }
            }
        } else {
            Err(Error::OutOfBoundKind(kind))
        }
    }
}

#[derive(Debug)]
pub enum Error {
    IOError(io::Error),
    OutOfBoundKind(u8),
    OutOfBoundBool(u8),
    OutOfBoundSign(u8),
    Utf8Error(FromUtf8Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IOError(e) => write!(f, "{}", e),
            Self::OutOfBoundKind(k) => write!(f, "Value kind is out of bound: {}", k),
            Self::OutOfBoundBool(b) => write!(f, "Expected bool value to be either 0 or 1: {}", b),
            Self::OutOfBoundSign(s) => {
                write!(f, "Expected sign value to be either 0, 1 or 2: {}", s)
            }
            Self::Utf8Error(e) => write!(f, "{}", e),
        }
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::IOError(error)
    }
}

impl From<FromUtf8Error> for Error {
    fn from(error: FromUtf8Error) -> Self {
        Self::Utf8Error(error)
    }
}

impl std::error::Error for Error {}
