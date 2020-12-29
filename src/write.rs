use crate::{Size, Value, ValueKind};
use byteorder::{NetworkEndian, WriteBytesExt};
use num_bigint::Sign;
use std::io;

macro_rules! int_arm {
    ($self:ident, $data:ident, $enum:ident, $write_fn:ident) => {{
        $self.writer.write_u8(ValueKind::$enum as u8)?;
        $self.writer.$write_fn::<NetworkEndian>(*$data)
    }};
}

pub struct Writer<W>
where
    W: io::Write,
{
    writer: W,
}

impl<W> Writer<W>
where
    W: io::Write,
{
    pub fn new(writer: W) -> Self {
        Self { writer }
    }

    pub fn write(&mut self, value: &Value) -> io::Result<()> {
        match value {
            Value::Nil => self.writer.write_u8(ValueKind::Nil as u8),
            Value::Bytes(data) => {
                self.writer.write_u8(ValueKind::Bytes as u8)?;
                self.writer.write_u32::<NetworkEndian>(data.kind)?;
                self.writer
                    .write_u32::<NetworkEndian>(data.data.len() as Size)?;
                self.writer.write_all(&data.data)
            }
            Value::Bool(data) => {
                self.writer.write_u8(ValueKind::Bool as u8)?;
                self.writer.write_u8(if *data { 1 } else { 0 })
            }
            Value::U8(data) => {
                self.writer.write_u8(ValueKind::U8 as u8)?;
                self.writer.write_u8(*data)
            }
            Value::U16(data) => int_arm!(self, data, U16, write_u16),
            Value::U32(data) => int_arm!(self, data, U32, write_u32),
            Value::U64(data) => int_arm!(self, data, U64, write_u64),
            Value::U128(data) => int_arm!(self, data, U128, write_u128),
            Value::BigU(data) => {
                self.writer.write_u8(ValueKind::BigU as u8)?;
                let bytes = data.to_bytes_be();
                self.writer
                    .write_u32::<NetworkEndian>(bytes.len() as Size)?;
                self.writer.write_all(&bytes)
            }
            Value::I8(data) => {
                self.writer.write_u8(ValueKind::I8 as u8)?;
                self.writer.write_i8(*data)
            }
            Value::I16(data) => int_arm!(self, data, I16, write_i16),
            Value::I32(data) => int_arm!(self, data, I32, write_i32),
            Value::I64(data) => int_arm!(self, data, I64, write_i64),
            Value::I128(data) => int_arm!(self, data, I128, write_i128),
            Value::BigI(data) => {
                self.writer.write_u8(ValueKind::BigI as u8)?;
                let (sign, bytes) = data.to_bytes_be();
                self.writer.write_u8(match sign {
                    Sign::Minus => 0,
                    Sign::NoSign => 1,
                    Sign::Plus => 2,
                })?;
                self.writer
                    .write_u32::<NetworkEndian>(bytes.len() as Size)?;
                self.writer.write_all(&bytes)
            }
            Value::F32(data) => {
                self.writer.write_u8(ValueKind::F32 as u8)?;
                self.writer.write_f32::<NetworkEndian>(data.into_inner())
            }
            Value::F64(data) => {
                self.writer.write_u8(ValueKind::F64 as u8)?;
                self.writer.write_f64::<NetworkEndian>(data.into_inner())
            }
            Value::Str(data) => {
                self.writer.write_u8(ValueKind::Str as u8)?;
                let data = data.as_bytes();
                self.writer.write_u32::<NetworkEndian>(data.len() as Size)?;
                self.writer.write_all(data)
            }
            Value::Array(data) => {
                self.writer.write_u8(ValueKind::Array as u8)?;
                self.writer.write_u32::<NetworkEndian>(data.len() as Size)?;
                for entry in data {
                    self.write(entry)?;
                }
                Ok(())
            }
            Value::Dict(data) => {
                self.writer.write_u8(ValueKind::Dict as u8)?;
                self.writer.write_u32::<NetworkEndian>(data.len() as Size)?;
                for (key, value) in data {
                    self.write(key)?;
                    self.write(value)?;
                }
                Ok(())
            }
        }
    }
}
