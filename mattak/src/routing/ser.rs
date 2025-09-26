use std::{
    collections::{hash_map, HashMap},
    fmt::Display,
    rc::Rc,
    sync::LazyLock,
};

use serde::{
    ser::{
        self, SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
        SerializeTupleStruct, SerializeTupleVariant,
    },
    Serialize,
};

use crate::routing::{parser::VarSpec, FillPolicy, Parsed, VarMod};

use super::parser;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("custom error: {0}")]
    CustomError(String),
    #[error("fewer parameters provided ({0}) than fields in template {1}")]
    MissingPositionalFields(usize, usize),
    #[error("more parameters provided ({0}) than fields in template {1}")]
    ExtraPositionalFields(usize, usize),
    #[error("one or more parameters provided than there are fields in template")]
    OverrunPositionalField, // when this happens, we don't have sizing contexts
    #[error("no value provided for variable: {0}")]
    MissingNamedVariable(String),
    #[error("bindings provided don't match expression - this is a Mattak error")]
    BindingsDontMatchExpression,
    #[error("cannot serialize a {0} as a key")]
    InvalidKeyType(String),
    #[error("serde provided value before key")]
    SerializationStateError,
    #[error("unexpected field: {0}")]
    ExtraNamedField(String),
    #[error("couldn't serialize non-utf8 bytes: {0}")]
    NotUTF8(std::str::Utf8Error),
}

impl ser::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: Display,
    {
        Error::CustomError(msg.to_string())
    }
}

macro_rules! demark {
    ($name:ident,$mark:literal) => {
        const $name: LazyLock<Rc<str>> = LazyLock::new(|| Rc::from($mark));
    };
}
demark!(EMPTY, "");
demark!(OPEN_BRACE, "{");
demark!(CLOSE_BRACE, "}");
demark!(COMMA, ",");
demark!(EQUALS, "=");
demark!(DOT, ".");
demark!(SEMI, ";");
demark!(AND, "&");
demark!(QMARK, "?");
demark!(SLASH, "/");
demark!(OCTOTHORPE, "#");

/// This allows us to make use of Serializer implemented on Formatter
/// since we can't (in stable Rust) construct a Formatter ourselves
/// For future consideration: we may want to produce more restricted Serializers,
/// since we use this for e.g. key names and prefixed variables (which have to be simple values)
/// and this allows serialization of numbers and lists and everything.
struct Fmt<T: Serialize>(T);

impl<T: Serialize> Display for Fmt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.serialize(f)
    }
}

struct VarBinding {
    vmod: VarMod,
    op: parser::Op,
    val: Option<Vec<Rc<str>>>,
}

impl VarSpec {
    fn to_str(&self) -> Rc<str> {
        use VarMod::*;
        match self.modifier {
            Prefix(n) => Rc::from(format!("{}:{n}", self.varname)),
            Explode => Rc::from(format!("{}*", self.varname)),
            None => Rc::from(self.varname.clone()),
        }
    }
}

fn mapvars(
    template: Parsed,
    policy: FillPolicy,
    bindings: HashMap<Rc<str>, VarBinding>,
) -> Result<Vec<Rc<str>>, Error> {
    template
        .parts_iter()
        .map(|part| {
            use crate::routing::Part::*;
            match part {
                Lit(s) => Ok(vec![Rc::<str>::from(s.clone())]),
                Expression(expression) => mapexpvars(expression, policy, &bindings),
                SegVar(expression)
                | SegPathVar(expression)
                | SegRest(expression)
                | SegPathRest(expression) => {
                    mapexpvars(expression, policy, &bindings).map(|mut vec| {
                        vec.insert(0, "/".into()); // XXX perf O(n)!
                        vec
                    })
                }
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(vec![])
}

fn mapexpvars(
    expression: &parser::Expression,
    policy: FillPolicy,
    bindings: &HashMap<Rc<str>, VarBinding>,
) -> Result<Vec<Rc<str>>, Error> {
    // The process here is that we need to break an Expression
    // into "stripes": literal parts where it's resolved
    // and new "unbound" expressions where it isn't.
    // If the FillPolicy forbids missing variables,
    // we can return an error as soon as we hit one, though
    let mut resolved = vec![];

    let mut joiner: Rc<str>;
    let mut specs = expression.varspecs.iter().peekable();
    while specs.peek().is_some() {
        joiner = Rc::from(expression.operator.prefix());
        while let Some(varspec) = specs.peek() {
            let vb = bindings
                .get(&Rc::from(varspec.varname.clone()))
                .ok_or(Error::BindingsDontMatchExpression)?;
            if let Some(ref val) = vb.val {
                specs.next();
                resolved.push(joiner);
                resolved.extend(val.clone()); // XXX prefix
                joiner = Rc::from(expression.operator.separator());
            } else {
                use FillPolicy::*;
                match policy {
                    NoMissing | Strict => {
                        return Err(Error::MissingNamedVariable(varspec.varname.clone()))
                    }
                    NoExtra | Relaxed => break,
                }
            }
        }

        if specs.peek().is_some() {
            use parser::Op::*;
            match expression.operator {
                Query if resolved.len() == 0 => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(QMARK.clone());
                }
                Fragment if resolved.len() == 0 => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(OCTOTHORPE.clone());
                }
                Simple | Reserved | Fragment => {
                    resolved.push(COMMA.clone());
                    resolved.push(OPEN_BRACE.clone());
                }
                Label => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(DOT.clone());
                }
                Path => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(SLASH.clone());
                }
                PathParam => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(SEMI.clone());
                }
                Query | QueryCont => {
                    resolved.push(OPEN_BRACE.clone());
                    resolved.push(AND.clone());
                }
            }
            joiner = EMPTY.clone();
        }

        while let Some(varspec) = specs.peek() {
            let vb = bindings
                .get(&Rc::from(varspec.varname.clone()))
                .ok_or(Error::BindingsDontMatchExpression)?;
            if vb.val.is_none() {
                resolved.push(joiner);
                resolved.push(varspec.to_str());
                specs.next();
                joiner = COMMA.clone();
            } else {
                resolved.push(CLOSE_BRACE.clone());
                break;
            }
        }
    }
    Ok(resolved)
}
pub(super) fn fill_template(parsed: Parsed, context: impl Serialize) -> Result<String, Error> {
    let mut serializer = Serializer {
        template: parsed.clone(),
        policy: FillPolicy::Strict,
    };
    context.serialize(&mut serializer)
}

struct Serializer {
    template: Parsed,
    policy: FillPolicy,
}

macro_rules! render_single_value {
    ($trait_fn:ident, $ty:ty) => {
        fn $trait_fn(self, v: $ty) -> Result<Self::Ok, Self::Error> {
            let mut seq = self.serialize_tuple(1)?;
            SerializeSeq::serialize_element(&mut seq, &v)?;
            SerializeSeq::end(seq)
        }
    };
}

impl<'a> serde::Serializer for &'a mut Serializer {
    type Ok = String;

    type Error = Error;

    type SerializeSeq = PositionSerializer;

    type SerializeTuple = PositionSerializer;

    type SerializeTupleStruct = PositionSerializer;

    type SerializeTupleVariant = PositionSerializer;

    type SerializeMap = NamedSerializer;

    type SerializeStruct = NamedSerializer;

    type SerializeStructVariant = NamedSerializer;

    render_single_value!(serialize_bool, bool);

    render_single_value!(serialize_i8, i8);
    render_single_value!(serialize_i16, i16);
    render_single_value!(serialize_i32, i32);
    render_single_value!(serialize_i64, i64);
    render_single_value!(serialize_u8, u8);
    render_single_value!(serialize_u16, u16);
    render_single_value!(serialize_u32, u32);
    render_single_value!(serialize_u64, u64);
    render_single_value!(serialize_f32, f32);
    render_single_value!(serialize_f64, f64);
    render_single_value!(serialize_char, char);
    render_single_value!(serialize_str, &str);
    render_single_value!(serialize_bytes, &[u8]);

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let mut seq = self.serialize_tuple(1)?;
        SerializeSeq::serialize_element(&mut seq, value)?;
        SerializeSeq::end(seq)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        let seq = self.serialize_tuple(0)?;
        SerializeSeq::end(seq)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let mut seq = self.serialize_tuple(1)?;
        SerializeSeq::serialize_element(&mut seq, &value)?;
        SerializeSeq::end(seq)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let mut seq = self.serialize_tuple(1)?;
        SerializeSeq::serialize_element(&mut seq, &value)?;
        SerializeSeq::end(seq)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        PositionSerializer::build(self.policy, len, self.template.clone())
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        PositionSerializer::build(self.policy, Some(len), self.template.clone())
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        PositionSerializer::build(self.policy, Some(len), self.template.clone())
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        PositionSerializer::build(self.policy, Some(len), self.template.clone())
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        NamedSerializer::build(self.policy, len, self.template.clone())
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        NamedSerializer::build(self.policy, Some(len), self.template.clone())
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        NamedSerializer::build(self.policy, Some(len), self.template.clone())
    }
}

// serialize the template based on variable first-appearance position
struct PositionSerializer {
    template: Parsed, //XXX needed?
    policy: FillPolicy,
    pos: Vec<Rc<str>>,
    vals: HashMap<Rc<str>, VarBinding>,
}

impl PositionSerializer {
    fn build(policy: FillPolicy, len: Option<usize>, template: Parsed) -> Result<Self, Error> {
        let mut pos = match len {
            None => vec![],
            Some(size) => Vec::with_capacity(size),
        };
        let mut vals = match len {
            None => HashMap::new(),
            Some(size) => HashMap::with_capacity(size),
        };

        template.parts_iter().for_each(|part| {
            if let Some(exp) = part.expression() {
                for vs in &exp.varspecs {
                    let name = Rc::<str>::from(vs.varname.clone());
                    match vals.entry(name.clone()) {
                        hash_map::Entry::Occupied(_) => (),
                        hash_map::Entry::Vacant(vacant_entry) => {
                            pos.push(name);
                            vacant_entry.insert(VarBinding {
                                vmod: vs.modifier,
                                op: exp.operator,
                                val: None,
                            });
                        }
                    }
                }
            }
        });

        if let Some(l) = len {
            use FillPolicy::*;
            match policy {
                Relaxed => (),
                NoMissing | Strict if l < pos.len() => {
                    return Err(Error::MissingPositionalFields(l, pos.len()))
                }
                NoExtra | Strict if l > pos.len() => {
                    return Err(Error::ExtraPositionalFields(l, pos.len()))
                }
                _ => (),
            }
        }

        Ok(Self {
            template,
            policy,
            pos,
            vals,
        })
    }
}

macro_rules! pos_impl {
    ($trait:ident, $item_fn:ident) => {
        impl<'a> $trait for PositionSerializer {
            type Ok = String;

            type Error = Error;

            fn $item_fn<T>(&mut self, value: &T) -> Result<(), Self::Error>
            where
                T: ?Sized + Serialize,
            {
                use parser::Op::*;
                let name = if let Some(n) = self.pos.pop() {
                    n
                } else {
                    use FillPolicy::*;
                    return match self.policy {
                        Relaxed | NoMissing => Ok(()),
                        NoExtra | Strict => Err(Error::OverrunPositionalField),
                    };
                };

                let binding = self
                    .vals
                    .get_mut(&name)
                    .expect("positional names to index into variable hash");
                let vstr = match binding.vmod {
                    VarMod::Explode => value.serialize(ExplodeSerializer {
                        name: name.clone(),
                        op: binding.op,
                    })?, // XXX
                    VarMod::Prefix(_) => value.serialize(ScalarSerializer {
                        name: match binding.op {
                            PathParam | Query | QueryCont => Some(name),
                            _ => None,
                        },
                    })?,
                    VarMod::None => value.serialize(ScalarSerializer {
                        name: match binding.op {
                            PathParam | Query | QueryCont => Some(name),
                            _ => None,
                        },
                    })?,
                };
                binding.val = Some(vstr);
                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                mapvars(self.template, self.policy, self.vals)
                    .map(|v| v.iter().map(|rc| rc.as_ref()).collect())
            }
        }
    };
}

pos_impl!(SerializeSeq, serialize_element);
pos_impl!(SerializeTuple, serialize_element);
pos_impl!(SerializeTupleStruct, serialize_field);
pos_impl!(SerializeTupleVariant, serialize_field);

struct NamedSerializer {
    template: Parsed,
    policy: FillPolicy,
    key: Option<Rc<str>>,
    vals: HashMap<Rc<str>, VarBinding>,
}

impl NamedSerializer {
    fn build(policy: FillPolicy, len: Option<usize>, template: Parsed) -> Result<Self, Error> {
        let mut vals = match len {
            None => HashMap::new(),
            Some(size) => HashMap::with_capacity(size),
        };

        let mut field_count = 0; // saves allocating the vector...

        template.parts_iter().for_each(|part| {
            if let Some(exp) = part.expression() {
                for vs in &exp.varspecs {
                    let name = Rc::<str>::from(vs.varname.clone());
                    match vals.entry(name) {
                        hash_map::Entry::Occupied(_) => (),
                        hash_map::Entry::Vacant(vacant_entry) => {
                            field_count += 1;
                            vacant_entry.insert(VarBinding {
                                vmod: vs.modifier,
                                op: exp.operator,
                                val: None,
                            });
                        }
                    }
                }
            }
        });

        if let Some(l) = len {
            use FillPolicy::*;
            match policy {
                Relaxed => (),
                NoMissing | Strict if l < field_count => {
                    return Err(Error::MissingPositionalFields(l, field_count))
                }
                NoExtra | Strict if l > field_count => {
                    return Err(Error::ExtraPositionalFields(l, field_count))
                }
                _ => (),
            }
        }

        Ok(Self {
            key: None,
            template,
            policy,
            vals,
        })
    }

    fn insert_value<T: ?Sized + Serialize>(
        &mut self,
        name: Rc<str>,
        value: &T,
    ) -> Result<(), Error> {
        use parser::Op::*;
        use FillPolicy::*;
        let binding = match self.vals.get_mut(&name) {
            Some(b) => b,
            None => match self.policy {
                Relaxed | NoMissing => return Ok(()),
                NoExtra | Strict => return Err(Error::ExtraNamedField(name.as_ref().into())),
            },
        };
        let vstr = match binding.vmod {
            VarMod::Explode => value.serialize(ExplodeSerializer {
                name: name.clone(),
                op: binding.op,
            })?,
            VarMod::Prefix(_) => value.serialize(ScalarSerializer {
                name: match binding.op {
                    PathParam | Query | QueryCont => Some(name),
                    _ => None,
                },
            })?,
            VarMod::None => value.serialize(ScalarSerializer {
                name: match binding.op {
                    PathParam | Query | QueryCont => Some(name),
                    _ => None,
                },
            })?,
        };
        binding.val = Some(vstr);
        Ok(())
    }
}

impl<'a> SerializeMap for NamedSerializer {
    type Ok = String;

    type Error = Error;

    fn serialize_entry<K, V>(&mut self, key: &K, value: &V) -> Result<(), Self::Error>
    where
        K: ?Sized + Serialize,
        V: ?Sized + Serialize,
    {
        let name = Rc::<str>::from(format!("{}", Fmt(key)));
        self.insert_value(name, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        mapvars(self.template, self.policy, self.vals)
            .map(|v| v.iter().map(|rc| rc.as_ref()).collect())
    }

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let _ = self.key.insert(Rc::<str>::from(format!("{}", Fmt(key))));
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let name = if let Some(n) = self.key.take() {
            n
        } else {
            return Err(Error::SerializationStateError);
        };
        self.insert_value(name, value)
    }
}

impl<'a> SerializeStruct for NamedSerializer {
    type Ok = String;

    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let name = Rc::<str>::from(key);
        self.insert_value(name, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        mapvars(self.template, self.policy, self.vals)
            .map(|v| v.iter().map(|rc| rc.as_ref()).collect())
    }

    fn skip_field(&mut self, key: &'static str) -> Result<(), Self::Error> {
        let _ = key;
        Ok(())
    }
}

impl<'a> SerializeStructVariant for NamedSerializer {
    type Ok = String;

    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let name = Rc::<str>::from(key);
        self.insert_value(name, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        mapvars(self.template, self.policy, self.vals)
            .map(|v| v.iter().map(|rc| rc.as_ref()).collect())
    }

    fn skip_field(&mut self, key: &'static str) -> Result<(), Self::Error> {
        let _ = key;
        Ok(())
    }
}

struct ScalarSerializer {
    name: Option<Rc<str>>,
}

macro_rules! render_single_value {
    ($trait_fn:ident, $ty:ty) => {
        fn $trait_fn(self, v: $ty) -> Result<Self::Ok, Self::Error> {
            if let Some(n) = self.name {
                Ok(vec![n.clone(), EQUALS.clone(), Rc::from(format!("{v}"))])
            } else {
                Ok(vec![Rc::from(format!("{v}"))])
            }
        }
    };
}

macro_rules! serializer_base_types {
    () => {
        type Ok = Vec<Rc<str>>;

        type Error = Error;
    };
}

macro_rules! serializer_types {
    ($seq:ident,$map:ident) => {
        serializer_base_types!();

        type SerializeSeq = $seq;

        type SerializeTuple = $seq;

        type SerializeTupleStruct = $seq;

        type SerializeTupleVariant = $seq;

        type SerializeMap = $map;

        type SerializeStruct = $map;

        type SerializeStructVariant = $map;
    };
}

impl serde::Serializer for ScalarSerializer {
    serializer_types!(ListScalarSerializer, ListScalarSerializer);

    render_single_value!(serialize_bool, bool);
    render_single_value!(serialize_i8, i8);
    render_single_value!(serialize_i16, i16);
    render_single_value!(serialize_i32, i32);
    render_single_value!(serialize_i64, i64);
    render_single_value!(serialize_u8, u8);
    render_single_value!(serialize_u16, u16);
    render_single_value!(serialize_u32, u32);
    render_single_value!(serialize_u64, u64);
    render_single_value!(serialize_f32, f32);
    render_single_value!(serialize_f64, f64);
    render_single_value!(serialize_char, char);

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(vec![Rc::from(v)])
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(vec![Rc::from(
            str::from_utf8(v).map_err(|e| Error::NotUTF8(e))?,
        )])
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(vec![Rc::from("")])
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(ListScalarSerializer::new(len))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(ListScalarSerializer::new(Some(len)))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(ListScalarSerializer::new(Some(len)))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(ListScalarSerializer::new(Some(len)))
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(ListScalarSerializer::new(len))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(ListScalarSerializer::new(Some(len)))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(ListScalarSerializer::new(Some(len)))
    }
}

struct ListScalarSerializer {
    output: Vec<Rc<str>>,
}

macro_rules! val_item {
    ($trait_fn:ident) => {
        fn $trait_fn<T>(&mut self, value: &T) -> Result<(), Self::Error>
        where
            T: ?Sized + Serialize,
        {
            if self.output.len() > 0 {
                self.output.push(COMMA.clone())
            }
            self.output.push(Rc::from(format!("{}", Fmt(value))));
            Ok(())
        }
    };
}

macro_rules! val_pair {
    ($trait_fn:ident) => {
        fn $trait_fn<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
        where
            T: ?Sized + Serialize,
        {
            if self.output.len() > 0 {
                self.output.push(COMMA.clone())
            }
            self.output.push(Rc::from(key));
            self.output.push(COMMA.clone());
            self.output.push(Rc::from(format!("{}", Fmt(value))));
            Ok(())
        }
    };
}
macro_rules! val_end {
    () => {
        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(self.output)
        }
    };
}

impl ListScalarSerializer {
    fn new(size: Option<usize>) -> Self {
        if let Some(s) = size {
            Self {
                output: Vec::with_capacity(s),
            }
        } else {
            Self { output: Vec::new() }
        }
    }
}

impl SerializeSeq for ListScalarSerializer {
    serializer_base_types!();
    val_item!(serialize_element);
    val_end!();
}
impl SerializeTuple for ListScalarSerializer {
    serializer_base_types!();
    val_item!(serialize_element);
    val_end!();
}
impl SerializeTupleStruct for ListScalarSerializer {
    serializer_base_types!();
    val_item!(serialize_field);
    val_end!();
}
impl SerializeTupleVariant for ListScalarSerializer {
    serializer_base_types!();
    val_item!(serialize_field);
    val_end!();
}
impl SerializeMap for ListScalarSerializer {
    serializer_base_types!();
    val_item!(serialize_key);
    val_item!(serialize_value);
    val_end!();
}
impl SerializeStruct for ListScalarSerializer {
    serializer_base_types!();
    val_pair!(serialize_field);
    val_end!();
}
impl SerializeStructVariant for ListScalarSerializer {
    serializer_base_types!();
    val_pair!(serialize_field);
    val_end!();
}

struct ExplodeSerializer {
    op: parser::Op,
    name: Rc<str>,
}

macro_rules! explode_single_value {
    ($trait_fn:ident, $ty:ty) => {
        fn $trait_fn(self, v: $ty) -> Result<Self::Ok, Self::Error> {
            use parser::Op::*;
            match self.op {
                PathParam | Query | QueryCont => {
                    Ok(vec![self.name, EQUALS.clone(), Rc::from(format!("{v}"))])
                }
                _ => Ok(vec![Rc::from(format!("{v}"))]),
            }
        }
    };
}

impl serde::Serializer for ExplodeSerializer {
    serializer_types!(ListExplodeSerializer, AssocExplodeSerializer);

    explode_single_value!(serialize_bool, bool);
    explode_single_value!(serialize_i8, i8);
    explode_single_value!(serialize_i16, i16);
    explode_single_value!(serialize_i32, i32);
    explode_single_value!(serialize_i64, i64);
    explode_single_value!(serialize_u8, u8);
    explode_single_value!(serialize_u16, u16);
    explode_single_value!(serialize_u32, u32);
    explode_single_value!(serialize_u64, u64);
    explode_single_value!(serialize_f32, f32);
    explode_single_value!(serialize_f64, f64);
    explode_single_value!(serialize_char, char);

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(vec![Rc::from(v)])
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(vec![Rc::from(
            str::from_utf8(v).map_err(|e| Error::NotUTF8(e))?,
        )])
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(vec![EMPTY.clone()])
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(ListExplodeSerializer::new(self.op, self.name, len))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(ListExplodeSerializer::new(self.op, self.name, Some(len)))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(ListExplodeSerializer::new(self.op, self.name, Some(len)))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(ListExplodeSerializer::new(self.op, self.name, Some(len)))
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(AssocExplodeSerializer::new(self.op, len))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Ok(AssocExplodeSerializer::new(self.op, Some(len)))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(AssocExplodeSerializer::new(self.op, Some(len)))
    }
}

macro_rules! explode_item {
    ($trait_fn:ident) => {
        fn $trait_fn<T>(&mut self, value: &T) -> Result<(), Self::Error>
        where
            T: ?Sized + Serialize,
        {
            if self.output.len() > 0 {
                self.add_separator()
            }
            self.output.push(self.name.clone());
            self.output.push(EQUALS.clone());
            self.output.push(Rc::from(format!("{}", Fmt(value))));
            Ok(())
        }
    };
}

struct ListExplodeSerializer {
    op: parser::Op,
    name: Rc<str>,
    output: Vec<Rc<str>>,
}

impl ListExplodeSerializer {
    fn new(op: parser::Op, name: Rc<str>, size: Option<usize>) -> Self {
        Self {
            op,
            name,
            output: match size {
                Some(s) => Vec::with_capacity(s),
                None => todo!(),
            },
        }
    }

    fn add_separator(&mut self) {
        use parser::Op::*;
        self.output.push(match self.op {
            Simple | Reserved | Fragment => COMMA.clone(),
            Label => DOT.clone(),
            Path => SLASH.clone(),
            PathParam => SEMI.clone(),
            Query | QueryCont => AND.clone(),
        })
    }
}

impl SerializeSeq for ListExplodeSerializer {
    serializer_base_types!();

    explode_item!(serialize_element);

    val_end!();
}
impl SerializeTuple for ListExplodeSerializer {
    serializer_base_types!();

    explode_item!(serialize_element);
    val_end!();
}
impl SerializeTupleStruct for ListExplodeSerializer {
    serializer_base_types!();
    explode_item!(serialize_field);
    val_end!();
}
impl SerializeTupleVariant for ListExplodeSerializer {
    serializer_base_types!();
    explode_item!(serialize_field);
    val_end!();
}

struct AssocExplodeSerializer {
    op: parser::Op,
    output: Vec<Rc<str>>,
}

impl AssocExplodeSerializer {
    fn new(op: parser::Op, size: Option<usize>) -> Self {
        Self {
            op,
            output: match size {
                Some(s) => Vec::with_capacity(s), // *4?
                None => todo!(),
            },
        }
    }

    fn add_separator(&mut self) {
        use parser::Op::*;
        self.output.push(match self.op {
            Simple | Reserved | Fragment => COMMA.clone(),
            Label => DOT.clone(),
            Path => SLASH.clone(),
            PathParam => SEMI.clone(),
            Query | QueryCont => AND.clone(),
        })
    }
}

impl SerializeMap for AssocExplodeSerializer {
    serializer_base_types!();

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        if self.output.len() > 0 {
            self.add_separator()
        }
        self.output.push(Rc::<str>::from(format!("{}", Fmt(key))));
        self.output.push(EQUALS.clone());
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.output.push(Rc::<str>::from(format!("{}", Fmt(value))));
        Ok(())
    }

    val_end!();
}
impl SerializeStruct for AssocExplodeSerializer {
    serializer_base_types!();

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        if self.output.len() > 0 {
            self.add_separator()
        }
        self.output.push(Rc::<str>::from(format!("{}", Fmt(key))));
        self.output.push(EQUALS.clone());
        self.output.push(Rc::<str>::from(format!("{}", Fmt(value))));
        Ok(())
    }

    val_end!();
}
impl SerializeStructVariant for AssocExplodeSerializer {
    serializer_base_types!();

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        if self.output.len() > 0 {
            self.add_separator()
        }
        self.output.push(Rc::<str>::from(format!("{}", Fmt(key))));
        self.output.push(EQUALS.clone());
        self.output.push(Rc::<str>::from(format!("{}", Fmt(value))));
        Ok(())
    }

    val_end!();
}
