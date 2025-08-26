use hyper::Uri;
use regex::Regex;
use serde::{
    de::{self, DeserializeSeed, EnumAccess, Error, MapAccess, SeqAccess, VariantAccess, Visitor},
    forward_to_deserialize_any, Deserializer,
};
use std::{
    any::type_name,
    collections::{hash_map, HashMap, HashSet, VecDeque},
    fmt,
    rc::Rc,
};

use crate::{
    error,
    routing::{render::var_re_name, Parsed, Part, VarMod},
};

// *** Time being, this is cribbed wholesale from Axum

// *** Pulled in from uses in Axum

// this wrapper type is used as the deserializer error to hide the `serde::de::Error` impl which
// would otherwise be public if we used `ErrorKind` as the error directly
#[derive(Debug)]
pub struct UriDeserializationError {
    pub(super) kind: ErrorKind,
}

impl UriDeserializationError {
    pub(super) fn new(kind: ErrorKind) -> Self {
        Self { kind }
    }

    pub(super) fn wrong_number_of_parameters(got: usize, expected: usize) -> Self {
        Self {
            kind: ErrorKind::WrongNumberOfParameters { got, expected },
        }
    }

    #[track_caller]
    pub(super) fn unsupported_type(name: &'static str) -> Self {
        Self::new(ErrorKind::UnsupportedType { name })
    }
}

impl Error for UriDeserializationError {
    #[inline]
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Self {
            kind: ErrorKind::Message(msg.to_string()),
        }
    }
}

impl fmt::Display for UriDeserializationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::error::Error for UriDeserializationError {}

#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The URI contained the wrong number of parameters.
    WrongNumberOfParameters {
        /// The number of actual parameters in the URI.
        got: usize,
        /// The number of expected parameters.
        expected: usize,
    },

    /// Failed to parse the value at a specific key into the expected type.
    ///
    /// This variant is used when deserializing into types that have named fields, such as structs.
    ParseErrorAtKey {
        /// The key at which the value was located.
        key: String,
        /// The value from the URI.
        value: String,
        /// The expected type of the value.
        expected_type: &'static str,
    },

    /// Failed to parse the value at a specific index into the expected type.
    ///
    /// This variant is used when deserializing into sequence types, such as tuples.
    ParseErrorAtIndex {
        /// The index at which the value was located.
        index: usize,
        /// The value from the URI.
        value: String,
        /// The expected type of the value.
        expected_type: &'static str,
    },

    /// Failed to parse a value into the expected type.
    ///
    /// This variant is used when deserializing into a primitive type (such as `String` and `u32`).
    ParseError {
        /// The value from the URI.
        value: String,
        /// The expected type of the value.
        expected_type: &'static str,
    },

    /// Tried to serialize into an unsupported type such as nested maps.
    ///
    /// This error kind is caused by programmer errors and thus gets converted into a `500 Internal
    /// Server Error` response.
    UnsupportedType {
        /// The name of the unsupported type.
        name: &'static str,
    },

    MismatchedValue {
        expected_type: &'static str,
    },

    /// Catch-all variant for errors that don't fit any other variant.
    Message(String),
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::Message(error) => error.fmt(f),
            ErrorKind::WrongNumberOfParameters { got, expected } => {
                write!(
                    f,
                    "Wrong number of path arguments for `Path`. Expected {expected} but got {got}"
                )?;

                if *expected == 1 {
                    write!(f, ". Note that multiple parameters must be extracted with a tuple `Path<(_, _)>` or a struct `Path<YourParams>`")?;
                }

                Ok(())
            }
            ErrorKind::UnsupportedType { name } => write!(f, "Unsupported type `{name}`"),
            ErrorKind::MismatchedValue { expected_type } => {
                write!(f, "value not suitable for type `{expected_type}`")
            }
            ErrorKind::ParseErrorAtKey {
                key,
                value,
                expected_type,
            } => write!(
                f,
                "Cannot parse `{key}` with value `{value:?}` to a `{expected_type}`"
            ),
            ErrorKind::ParseError {
                value,
                expected_type,
            } => write!(f, "Cannot parse `{value:?}` to a `{expected_type}`"),
            ErrorKind::ParseErrorAtIndex {
                index,
                value,
                expected_type,
            } => write!(
                f,
                "Cannot parse value at index {index} with value `{value:?}` to a `{expected_type}`"
            ),
        }
    }
}

// *** end of inlining types

macro_rules! unsupported_type {
    ($trait_fn:ident) => {
        fn $trait_fn<V>(self, _: V) -> Result<V::Value, Self::Error>
        where
            V: Visitor<'de>,
        {
            Err(UriDeserializationError::unsupported_type(type_name::<
                V::Value,
            >()))
        }
    };
}

macro_rules! parse_single_value {
    ($trait_fn:ident, $visit_fn:ident, $ty:literal) => {
        fn $trait_fn<V>(self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: Visitor<'de>,
        {
            if self.varlist.len() == 1 {
                let value = match &self.varlist[0] {
                    (_, VarBinding::Scalar(scalar)) => scalar.parse().map_err(|_| {
                        UriDeserializationError::new(ErrorKind::ParseError {
                            value: scalar.to_string(),
                            expected_type: $ty,
                        })
                    })?,
                    (_, VarBinding::PathExplode(_, string)) => string.parse().map_err(|_| {
                        UriDeserializationError::new(ErrorKind::ParseError {
                            value: string.to_string(),
                            expected_type: $ty,
                        })
                    })?,
                    (_, VarBinding::QueryExplode(_)) => {
                        return Err(UriDeserializationError::new(ErrorKind::MismatchedValue {
                            expected_type: $ty,
                        }))
                    }
                    (_, VarBinding::Empty) => {
                        return Err(UriDeserializationError::new(ErrorKind::ParseError {
                            value: "<empty>".to_string(),
                            expected_type: $ty,
                        }))
                    }
                };
                visitor.$visit_fn(value)
            } else {
                return Err(UriDeserializationError::wrong_number_of_parameters(
                    self.varlist.len(),
                    1,
                ));
            }
        }
    };
}

pub(crate) struct UriDeserializer {
    varlist: Vec<(Rc<str>, VarBinding)>,
    query_assocs: HashMap<Rc<str>, Rc<str>>,
}

impl UriDeserializer {
    #[inline]
    pub(crate) fn new(
        varlist: Vec<(Rc<str>, VarBinding)>,
        query_assocs: HashMap<Rc<str>, Rc<str>>,
    ) -> Self {
        UriDeserializer {
            varlist,
            query_assocs,
        }
    }
}

#[derive(Clone)]
enum VarBinding {
    Scalar(Rc<str>),
    PathExplode(Rc<str>, Rc<str>), // sep, string value
    QueryExplode(Vec<Rc<str>>),
    Empty,
}

impl VarBinding {
    fn to_str(&self) -> Result<Rc<str>, UriDeserializationError> {
        match self {
            VarBinding::Scalar(v) => Ok(v.clone()),
            VarBinding::PathExplode(_, joined) => Ok(joined.clone()),
            VarBinding::QueryExplode(items) => Ok(items.join(",").into()),
            VarBinding::Empty => Err(UriDeserializationError::wrong_number_of_parameters(0, 1)),
        }
    }
}

fn parsed_template_vars(parsed: &Parsed) -> Vec<Rc<str>> {
    parsed
        .parts_iter()
        .filter_map(|part| match part {
            Part::Lit(_) => None,
            Part::Expression(expression)
            | Part::SegVar(expression)
            | Part::SegPathVar(expression)
            | Part::SegRest(expression)
            | Part::SegPathRest(expression) => Some(
                expression
                    .varspecs
                    .iter()
                    .map(|vs| Rc::<str>::from(vs.varname.clone())) // XXX consider Rc<str> in VarSpec
                    .collect::<Vec<_>>(),
            ),
        })
        .flatten()
        .collect::<Vec<_>>()
}

//   * Parser Path Scalar names
//   Need to emit (capture,varname) - usually (x,x) but sometimes (x,x_p3)
fn path_scalar_names(parsed: &Parsed) -> HashMap<Rc<str>, Rc<str>> {
    let mut result = HashMap::new();
    use Part::*;
    for part in parsed.nonquery_parts_iter() {
        match part {
            // PATH
            SegRest(exp) | SegPathRest(exp) | SegVar(exp) | SegPathVar(exp) => {
                for v in &exp.varspecs {
                    match v.modifier {
                        VarMod::None => {
                            let name: Rc<str> = v.varname.clone().into();
                            result.insert(name.clone(), name); // SCALAR
                        }
                        VarMod::Prefix(_) => {
                            // XXX edge case: should be the longest prefix
                            result.insert(v.varname.clone().into(), var_re_name(&v).into());
                        }
                        VarMod::Explode => (),
                    }
                }
            }
            _ => (),
        }
    }
    result
}
//   * Parser Query Scalar names
fn query_scalar_names(parsed: &Parsed) -> HashSet<&str> {
    use Part::*;
    parsed
        .query_parts_iter()
        .filter_map(|part| match part {
            // QUERY
            SegRest(exp) | SegPathRest(exp) | SegVar(exp) | SegPathVar(exp) => {
                Some(
                    exp.varspecs
                        .iter()
                        .filter_map(|v| match v.modifier {
                            VarMod::None | VarMod::Prefix(_) => Some(v.varname.as_str()), // SCALAR
                            _ => None,
                        })
                        .collect::<Vec<&str>>(),
                )
            }
            _ => None,
        })
        .flatten()
        .collect()
}
//   * Parser Path Explode names - might need the joiner in order to split them
fn path_explode_names(parsed: &Parsed) -> Vec<(&str, &str)> {
    use Part::*;
    parsed
        .nonquery_parts_iter()
        .filter_map(|part| match part {
            // PATH
            SegRest(exp) | SegPathRest(exp) | SegVar(exp) | SegPathVar(exp) => {
                Some(
                    exp.varspecs
                        .iter()
                        .filter_map(|v| match v.modifier {
                            VarMod::Explode => Some((exp.operator.separator(), v.varname.as_str())), // EXPLODE
                            _ => None,
                        })
                        .collect::<Vec<(&str, &str)>>(),
                )
            }
            _ => None,
        })
        .flatten()
        .collect()
}
//   * Parser Query Explode names
fn query_explode_names(parsed: &Parsed) -> HashSet<&str> {
    use Part::*;
    parsed
        .query_parts_iter()
        .filter_map(|part| match part {
            // QUERY
            SegRest(exp) | SegPathRest(exp) | SegVar(exp) | SegPathVar(exp) => {
                Some(
                    exp.varspecs
                        .iter()
                        .filter_map(|v| match v.modifier {
                            VarMod::Explode => Some(v.varname.as_str()), // EXPLODE
                            _ => None,
                        })
                        .collect::<Vec<&str>>(),
                )
            }
            _ => None,
        })
        .flatten()
        .collect()
}
impl UriDeserializer {
    // XXX &Uri?
    // The deserializer will need:
    // * KV of scalars
    // * KV of (joiner, list) or (scalar, split list) from path explodes
    // * KV of Option<lists> from query explodes
    // Path lists need their joiner provided
    // Note: queries can provide keys not in the template,
    // because {?assoc*} (only that case)
    //
    // During URI parsing,
    // * same key with different values: Error
    // * path lists in preference to query lists
    //
    // Deserialization: exactly one map/struct can consume
    // {?assoc*} fields. Rule is:
    //
    // Field is named in template: it gets the value provided
    // One field (map/struct) not named in template: all the unnamed scalars
    // A second complex field not named in template: Error
    //
    // Explicitly ignoring order of visit, e.g. with Default rules
    // (derive(Route) should be able to compare template to fields and (possibly) panic)
    // Note: template doesn't know field types,
    // so multiple explode _could_ all (or all but one) be lists.
    // The URI presented also doesn't make it clear: multiple missing explodes... might just be empty lists
    //
    // path list with scalar field: gets the value as provided
    //  with seq field, split with joiner
    //
    // query list with scalar field: error
    //
    // scalar with seq field: split on ,
    // scalar with map field: split on , into pairs
    //
    //
    // Inputs here:
    //   * Parser Path Scalar names
    //   * Parser Path Explode names
    //   * Parser Query Scalar names
    //   * Parser Query Explode names
    //   * Regex Path captures
    //   * Form query pairs
    //
    //
    // Part of the logic here:
    //
    //                     DeserializeTarget
    //                         scalar       seq
    // Template
    // --------------------+------------+-------------
    // Mod::None           |   idem     |   split(",")
    // Path, Mod::Explode  | "/seg/seg" | split(joiner)
    // Query, Mod::Explode |  Error     |
    //
    // How should we handle prefix catpures in regex (e.g. foo_p5)?
    // How should we handle prefixes in queries?
    //
    // IMO {?var:3} is a _mistake_ not an error
    // 6570 doesn't have a way to rename that field, so e.g.
    // {?var:3,var} would -> ?var=val&var=value
    // Feels, atm, like an edge case. Let's: scalar value conflict error
    //
    // That said, I can see wanting to parse limited size values, so let's
    // ensure that the longest templated prefex is captured as the value
    // In the paths, we can (probably) collect the prefix forms and choose the longest
    // In queries, authors should note (and ideally get a good error) that
    // scalar values can't use different prefix counts
    //
    // Query prefix should be checked by derive(Route) and here.
    //
    // More logic: if the template provides
    //
    //            query_var
    //
    // path var     nomod       prefix[n]     prefix[M]
    //
    // nomod        must equal  path wins
    //                          must prefix?
    // prefix[n]    query wins  must equal    must prefix,
    //                                        largest wins
    //
    //  use _values_ to check prefixing and length
    //  IOW: if a variable repeats, new value must be a prefix of old
    //  or v/v. Longest is new value. Not a prefix? Error.
    //  For same length, devolves to equality, and we don't have to record
    //  anything about what the template said.
    //
    //  XXX It's an error to reuse a capture group name in Regex
    //
    //  XXX As is, a varname can be both a scalar and complex, which seems like a weird edge case
    //      That's true both within path/query, and between (i.e. scalar path, list query)
    //      However!! that's a problem with template, which should be validated separately
    //      (and before it goes into the main MAP
    //
    //  Key realization: template issues should already have been validated
    //  * TODO: template validation post-parse
    //  * Template errors here can panic
    //  * URI errors (e.g. same variable, different values) should raise errors
    /// Creates a UriDeserializer for a Uri, a Parsed route template and the compiled regex for
    /// the Parsed.
    ///
    /// # Panics
    ///
    /// Panics if the template has invalid overlaps between scalar and complex variables.
    ///
    /// # Errors
    ///
    /// This function will return an error if
    pub(crate) fn for_uri(
        uri: &Uri,
        parsed: &Parsed,
        regex: &Regex,
    ) -> Result<UriDeserializer, error::Error> {
        let mut scalars: HashMap<Rc<str>, Rc<str>> = HashMap::new();
        let mut path_explodes: HashMap<Rc<str>, (Rc<str>, Rc<str>)> = HashMap::new();
        let mut query_explodes: HashMap<Rc<str>, Vec<Rc<str>>> = HashMap::new();
        let mut query_assocs: HashMap<Rc<str>, Rc<str>> = HashMap::new();
        // definitely considering a secondary Nom parser instead of RE here.
        let path = uri.path();
        let url = match (uri.scheme_str(), uri.authority().map(|a| a.as_str())) {
            (Some(scheme), Some(auth)) => &format!("{scheme}://{auth}{path}"),
            (None, Some(auth)) => &format!("//{auth}{path}"),
            (Some(scheme), None) => &format!("{scheme}://{path}"),
            (None, None) => path,
        };

        let caps = regex
            .captures(url)
            .ok_or_else(|| error::Error::NoMatch(url.to_string()))?;

        let query_parse = match (parsed.query.is_some(), uri.query()) {
            (false, None) |
            (false, Some(_)) | // XXX Error? (if you want to accept abitrary queries, {?ignored*}
            (true,  None) => form_urlencoded::parse(&[]),
            (true, Some(q)) => form_urlencoded::parse(q.as_bytes()),
        };

        let mut new_scalar = |var_name: Rc<str>, m: Rc<str>| -> Result<(), error::Error> {
            if let Some(new_val) = percent_decode(m) {
                if let Some(val) = scalars.get(&var_name) {
                    if val.len() > new_val.len() {
                        if !val.starts_with(&*new_val) {
                            return Err(error::Error::MismatchedValues(
                                var_name.to_string(),
                                val.to_string(),
                                new_val.to_string(),
                            ));
                        } // else we already have the longest value
                    } else if new_val.starts_with(val.as_ref()) {
                        scalars.insert(var_name, new_val);
                    } else {
                        return Err(error::Error::MismatchedValues(
                            var_name.to_string(),
                            val.to_string(),
                            new_val.to_string(),
                        ));
                    }
                } else {
                    scalars.insert(var_name, new_val);
                }
            };
            Ok(())
        };

        let query_scalar_names = query_scalar_names(parsed);
        let query_explode_names = query_explode_names(parsed);
        for (cow_var_name, cow_value) in query_parse {
            let var_name: Rc<str> = cow_var_name.into_owned().into();
            let value: Rc<str> = cow_value.into_owned().into();

            if query_scalar_names.contains(var_name.as_ref()) {
                new_scalar(var_name, value)?
            } else if query_explode_names.contains(var_name.as_ref()) {
                query_explodes
                    .entry(var_name)
                    .and_modify(|exes| exes.push(value.clone()))
                    .or_insert_with(|| vec![value.clone()]);
            } else {
                match query_assocs.entry(var_name.as_ref().into()) {
                    hash_map::Entry::Occupied(entry) => {
                        let old_val = entry.get();
                        if &value != old_val {
                            return Err(error::Error::MismatchedValues(
                                var_name.to_string(),
                                old_val.to_string(),
                                value.to_string(),
                            ));
                        }
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(value);
                    }
                }
            }
        }
        for x_name in query_explode_names {
            query_explodes.entry(x_name.into()).or_default();
        }

        let names = path_scalar_names(parsed);
        for (var_name, re_name) in names {
            if let Some(m) = caps.name(&re_name) {
                new_scalar(var_name, m.as_str().into())?
            }
        }
        for (sep, var_name) in path_explode_names(parsed) {
            if let Some(m) = caps.name(&var_name) {
                if let Some(dec) = percent_decode(m.as_str()) {
                    path_explodes.insert(var_name.into(), (sep.into(), dec));
                }
            }
        }

        let varlist = parsed_template_vars(parsed)
            .iter()
            .map(move |vname| {
                match (
                    scalars.get(vname),
                    path_explodes.get(vname),
                    query_explodes.get(vname),
                ) {
                    (Some(scalar), None, None) => {
                        Ok((vname.clone(), VarBinding::Scalar(scalar.clone())))
                    }
                    (None, Some((sep, string)), None) => Ok((
                        vname.clone(),
                        VarBinding::PathExplode(sep.clone(), string.clone()),
                    )),
                    (None, None, Some(query)) => {
                        if query.len() > 0 {
                            Ok((vname.clone(), VarBinding::QueryExplode(query.clone())))
                        } else {
                            Ok((vname.clone(), VarBinding::Empty))
                        }
                    }
                    (None, Some((sep, string)), Some(query)) => {
                        let path_vec = string
                            .split(sep.as_ref())
                            .map(|part| part.into())
                            .collect::<Vec<Rc<str>>>();
                        if query.len() > 0 {
                            if path_vec == *query {
                                Ok((
                                    vname.clone(),
                                    VarBinding::PathExplode(sep.clone(), string.clone()),
                                ))
                            } else {
                                Err(error::Error::MismatchedValues(
                                    vname.to_string(),
                                    string.to_string(),
                                    query.join(sep),
                                ))
                            }
                        } else {
                            Err(error::Error::MismatchedValues(
                                vname.to_string(),
                                string.to_string(),
                                "".to_string(),
                            ))
                        }
                    }
                    (None, None, None) => Ok((vname.clone(), VarBinding::Empty)),
                    (Some(_), Some(_), _) => {
                        panic!("scalar and path explode should be caught in template parse")
                    }
                    (Some(_), _, Some(_)) => {
                        panic!("scalar and query explode should be caught in template parse")
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(UriDeserializer {
            varlist,
            query_assocs,
        })
    }
}

fn percent_decode<S: AsRef<str>>(s: S) -> Option<Rc<str>> {
    percent_encoding::percent_decode(s.as_ref().as_bytes())
        .decode_utf8()
        .ok() //consider: Result?
        .map(|decoded| decoded.as_ref().into())
}

impl<'de> Deserializer<'de> for UriDeserializer {
    type Error = UriDeserializationError;

    unsupported_type!(deserialize_bytes);
    unsupported_type!(deserialize_option);
    unsupported_type!(deserialize_identifier);
    unsupported_type!(deserialize_ignored_any);

    parse_single_value!(deserialize_bool, visit_bool, "bool");
    parse_single_value!(deserialize_i8, visit_i8, "i8");
    parse_single_value!(deserialize_i16, visit_i16, "i16");
    parse_single_value!(deserialize_i32, visit_i32, "i32");
    parse_single_value!(deserialize_i64, visit_i64, "i64");
    parse_single_value!(deserialize_i128, visit_i128, "i128");
    parse_single_value!(deserialize_u8, visit_u8, "u8");
    parse_single_value!(deserialize_u16, visit_u16, "u16");
    parse_single_value!(deserialize_u32, visit_u32, "u32");
    parse_single_value!(deserialize_u64, visit_u64, "u64");
    parse_single_value!(deserialize_u128, visit_u128, "u128");
    parse_single_value!(deserialize_f32, visit_f32, "f32");
    parse_single_value!(deserialize_f64, visit_f64, "f64");
    parse_single_value!(deserialize_string, visit_string, "String");
    parse_single_value!(deserialize_byte_buf, visit_string, "String");
    parse_single_value!(deserialize_char, visit_char, "char");

    fn deserialize_any<V>(self, v: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(v)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if let [(_, binding)] = self.varlist.as_slice() {
            visitor.visit_str(&binding.to_str()?)
        } else {
            return Err(UriDeserializationError::wrong_number_of_parameters(
                self.varlist.len(),
                1,
            ));
        }
        //visitor.visit_borrowed_str(&self.url_params[0].1)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let params = self.varlist.into();
        visitor.visit_seq(SeqDeserializer { params, idx: 0 })
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.varlist.len() < len {
            return Err(UriDeserializationError::wrong_number_of_parameters(
                self.varlist.len(),
                len,
            ));
        }
        let params = self.varlist.into();
        visitor.visit_seq(SeqDeserializer {
            params: params,
            idx: 0,
        })
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.varlist.len() < len {
            return Err(UriDeserializationError::wrong_number_of_parameters(
                self.varlist.len(),
                len,
            ));
        }
        let params = self.varlist.into();
        visitor.visit_seq(SeqDeserializer { params, idx: 0 })
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_map(MapDeserializer {
            params: self.varlist.into(),
            value: None,
            key: None,
        })
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.varlist.len() != 1 {
            return Err(UriDeserializationError::wrong_number_of_parameters(
                self.varlist.len(),
                1,
            ));
        }

        visitor.visit_enum(EnumDeserializer {
            value: self.varlist[0].0.clone(),
        })
    }
}

struct MapDeserializer {
    params: VecDeque<(Rc<str>, VarBinding)>,
    key: Option<KeyOrIdx>,
    value: Option<Rc<str>>,
}

impl<'de> MapAccess<'de> for MapDeserializer {
    type Error = UriDeserializationError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: DeserializeSeed<'de>,
    {
        match self.params.pop_front() {
            Some((key, value)) => {
                self.key = Some(KeyOrIdx::Key(key.clone()));
                self.value = Some(value.to_str()?);
                seed.deserialize(KeyDeserializer { key }).map(Some)
            }
            None => Ok(None),
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        match self.value.take() {
            Some(value) => seed.deserialize(ValueDeserializer {
                key: self.key.take(),
                value,
            }),
            None => Err(UriDeserializationError::custom("value is missing")),
        }
    }
}

struct KeyDeserializer {
    key: Rc<str>,
}

macro_rules! parse_key {
    ($trait_fn:ident) => {
        fn $trait_fn<V>(self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: Visitor<'de>,
        {
            visitor.visit_str(&self.key)
        }
    };
}

impl<'de> Deserializer<'de> for KeyDeserializer {
    type Error = UriDeserializationError;

    parse_key!(deserialize_identifier);
    parse_key!(deserialize_str);
    parse_key!(deserialize_string);

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::custom("Unexpected key type"))
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char bytes
        byte_buf option unit unit_struct seq tuple
        tuple_struct map newtype_struct struct enum ignored_any
    }
}

macro_rules! parse_value {
    ($trait_fn:ident, $visit_fn:ident, $ty:literal) => {
        fn $trait_fn<V>(mut self, visitor: V) -> Result<V::Value, Self::Error>
        where
            V: Visitor<'de>,
        {
            let v = self.value.parse().map_err(|_| {
                if let Some(key) = self.key.take() {
                    let kind = match key {
                        KeyOrIdx::Key(key) => ErrorKind::ParseErrorAtKey {
                            key: key.to_string(),
                            value: self.value.to_string(),
                            expected_type: $ty,
                        },
                        KeyOrIdx::Idx { idx: index, key: _ } => ErrorKind::ParseErrorAtIndex {
                            index,
                            value: self.value.to_string(),
                            expected_type: $ty,
                        },
                    };
                    UriDeserializationError::new(kind)
                } else {
                    UriDeserializationError::new(ErrorKind::ParseError {
                        value: self.value.to_string(),
                        expected_type: $ty,
                    })
                }
            })?;
            visitor.$visit_fn(v)
        }
    };
}

#[derive(Debug)]
struct ValueDeserializer {
    key: Option<KeyOrIdx>,
    value: Rc<str>,
}

impl<'de> Deserializer<'de> for ValueDeserializer {
    type Error = UriDeserializationError;

    unsupported_type!(deserialize_map);
    unsupported_type!(deserialize_identifier);

    parse_value!(deserialize_bool, visit_bool, "bool");
    parse_value!(deserialize_i8, visit_i8, "i8");
    parse_value!(deserialize_i16, visit_i16, "i16");
    parse_value!(deserialize_i32, visit_i32, "i32");
    parse_value!(deserialize_i64, visit_i64, "i64");
    parse_value!(deserialize_i128, visit_i128, "i128");
    parse_value!(deserialize_u8, visit_u8, "u8");
    parse_value!(deserialize_u16, visit_u16, "u16");
    parse_value!(deserialize_u32, visit_u32, "u32");
    parse_value!(deserialize_u64, visit_u64, "u64");
    parse_value!(deserialize_u128, visit_u128, "u128");
    parse_value!(deserialize_f32, visit_f32, "f32");
    parse_value!(deserialize_f64, visit_f64, "f64");
    parse_value!(deserialize_string, visit_string, "String");
    parse_value!(deserialize_byte_buf, visit_string, "String");
    parse_value!(deserialize_char, visit_char, "char");

    fn deserialize_any<V>(self, v: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(v)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_str(&self.value)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_bytes(self.value.as_bytes())
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_some(self)
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        struct PairDeserializer {
            key: Option<KeyOrIdx>,
            value: Option<Rc<str>>,
        }

        impl<'de> SeqAccess<'de> for PairDeserializer {
            type Error = UriDeserializationError;

            fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
            where
                T: DeserializeSeed<'de>,
            {
                match self.key.take() {
                    Some(KeyOrIdx::Idx { idx: _, key }) => {
                        return seed.deserialize(KeyDeserializer { key }).map(Some);
                    }
                    // `KeyOrIdx::Key` is only used when deserializing maps so `deserialize_seq`
                    // wouldn't be called for that
                    Some(KeyOrIdx::Key(_)) => unreachable!(),
                    None => {}
                };

                self.value
                    .take()
                    .map(|value| seed.deserialize(ValueDeserializer { key: None, value }))
                    .transpose()
            }
        }

        if len == 2 {
            match self.key {
                Some(key) => visitor.visit_seq(PairDeserializer {
                    key: Some(key),
                    value: Some(self.value),
                }),
                // `self.key` is only `None` when deserializing maps so `deserialize_seq`
                // wouldn't be called for that
                None => unreachable!(),
            }
        } else {
            Err(UriDeserializationError::unsupported_type(type_name::<
                V::Value,
            >()))
        }
    }

    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::unsupported_type(type_name::<
            V::Value,
        >()))
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::unsupported_type(type_name::<
            V::Value,
        >()))
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::unsupported_type(type_name::<
            V::Value,
        >()))
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_enum(EnumDeserializer { value: self.value })
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }
}

struct EnumDeserializer {
    value: Rc<str>,
}

impl<'de> EnumAccess<'de> for EnumDeserializer {
    type Error = UriDeserializationError;
    type Variant = UnitVariant;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        Ok((
            seed.deserialize(KeyDeserializer { key: self.value })?,
            UnitVariant,
        ))
    }
}

struct UnitVariant;

impl<'de> VariantAccess<'de> for UnitVariant {
    type Error = UriDeserializationError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, _seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        Err(UriDeserializationError::unsupported_type(
            "newtype enum variant",
        ))
    }

    fn tuple_variant<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::unsupported_type(
            "tuple enum variant",
        ))
    }

    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(UriDeserializationError::unsupported_type(
            "struct enum variant",
        ))
    }
}

struct SeqDeserializer {
    params: VecDeque<(Rc<str>, VarBinding)>,
    idx: usize,
}

impl<'de> SeqAccess<'de> for SeqDeserializer {
    type Error = UriDeserializationError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        match self.params.pop_front() {
            Some((key, value)) => {
                let idx = self.idx;
                self.idx += 1;
                Ok(Some(seed.deserialize(ValueDeserializer {
                    key: Some(KeyOrIdx::Idx { idx, key }),
                    value: value.to_str()?,
                })?))
            }
            None => Ok(None),
        }
    }
}

#[derive(Debug, Clone)]
enum KeyOrIdx {
    Key(Rc<str>),
    Idx { idx: usize, key: Rc<str> },
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::collections::HashMap;

    #[derive(Debug, Deserialize, Eq, PartialEq)]
    enum MyEnum {
        A,
        B,
        #[serde(rename = "c")]
        C,
    }

    #[derive(Debug, Deserialize, Eq, PartialEq)]
    struct Struct {
        c: String,
        b: bool,
        a: i32,
    }

    fn create_url_params<I, K, V>(values: I) -> Vec<(Rc<str>, VarBinding)>
    where
        I: IntoIterator<Item = (K, V)>,
        K: AsRef<str>,
        V: AsRef<str>,
    {
        values
            .into_iter()
            .map(|(k, v)| {
                (
                    Rc::from(k.as_ref()),
                    VarBinding::Scalar(Rc::from(v.as_ref())),
                )
            })
            .collect()
    }

    macro_rules! check_single_value {
        ($ty:ty, $value_str:literal, $value:expr) => {
            #[allow(clippy::bool_assert_comparison)]
            {
                let url_params = create_url_params(vec![("value", $value_str)]);
                let deserializer = UriDeserializer::new(url_params, HashMap::new());
                assert_eq!(<$ty>::deserialize(deserializer).unwrap(), $value);
            }
        };
    }

    #[test]
    fn test_parse_single_value() {
        check_single_value!(bool, "true", true);
        check_single_value!(bool, "false", false);
        check_single_value!(i8, "-123", -123);
        check_single_value!(i16, "-123", -123);
        check_single_value!(i32, "-123", -123);
        check_single_value!(i64, "-123", -123);
        check_single_value!(i128, "123", 123);
        check_single_value!(u8, "123", 123);
        check_single_value!(u16, "123", 123);
        check_single_value!(u32, "123", 123);
        check_single_value!(u64, "123", 123);
        check_single_value!(u128, "123", 123);
        check_single_value!(f32, "123", 123.0);
        check_single_value!(f64, "123", 123.0);
        check_single_value!(String, "abc", "abc");
        // check_single_value!(String, "one%20two", "one two"); // percent decoding happens in routing/mod.rs
        check_single_value!(&str, "abc", "abc");
        // check_single_value!(&str, "one%20two", "one two");
        check_single_value!(char, "a", 'a');

        let url_params = create_url_params(vec![("a", "B")]);
        assert_eq!(
            MyEnum::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            MyEnum::B
        );

        let url_params = create_url_params(vec![("a", "1"), ("b", "2")]);
        let error_kind = i32::deserialize(UriDeserializer::new(url_params, HashMap::new()))
            .unwrap_err()
            .kind;
        assert!(matches!(
            error_kind,
            ErrorKind::WrongNumberOfParameters {
                expected: 1,
                got: 2
            }
        ));
    }

    #[test]
    fn test_parse_seq() {
        let url_params = create_url_params(vec![("a", "1"), ("b", "true"), ("c", "abc")]);
        assert_eq!(
            <(i32, bool, String)>::deserialize(UriDeserializer::new(
                url_params.clone(),
                HashMap::new()
            ))
            .unwrap(),
            (1, true, "abc".to_owned())
        );

        #[derive(Debug, Deserialize, Eq, PartialEq)]
        struct TupleStruct(i32, bool, String);
        assert_eq!(
            TupleStruct::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            TupleStruct(1, true, "abc".to_owned())
        );

        let url_params = create_url_params(vec![("a", "1"), ("b", "2"), ("c", "3")]);
        assert_eq!(
            <Vec<i32>>::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            vec![1, 2, 3]
        );

        let url_params = create_url_params(vec![("a", "c"), ("a", "B")]);
        assert_eq!(
            <Vec<MyEnum>>::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            vec![MyEnum::C, MyEnum::B]
        );
    }

    #[test]
    fn test_parse_seq_tuple_string_string() {
        let url_params = create_url_params(vec![("a", "foo"), ("b", "bar")]);
        assert_eq!(
            <Vec<(String, String)>>::deserialize(UriDeserializer::new(url_params, HashMap::new()))
                .unwrap(),
            vec![
                ("a".to_owned(), "foo".to_owned()),
                ("b".to_owned(), "bar".to_owned())
            ]
        );
    }

    #[test]
    fn test_parse_seq_tuple_string_parse() {
        let url_params = create_url_params(vec![("a", "1"), ("b", "2")]);
        assert_eq!(
            <Vec<(String, u32)>>::deserialize(UriDeserializer::new(url_params, HashMap::new()))
                .unwrap(),
            vec![("a".to_owned(), 1), ("b".to_owned(), 2)]
        );
    }

    #[test]
    fn test_parse_struct() {
        let url_params = create_url_params(vec![("a", "1"), ("b", "true"), ("c", "abc")]);
        assert_eq!(
            Struct::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            Struct {
                c: "abc".to_owned(),
                b: true,
                a: 1,
            }
        );
    }

    #[test]
    fn test_parse_struct_ignoring_additional_fields() {
        let url_params = create_url_params(vec![
            ("a", "1"),
            ("b", "true"),
            ("c", "abc"),
            ("d", "false"),
        ]);
        assert_eq!(
            Struct::deserialize(UriDeserializer::new(url_params, HashMap::new())).unwrap(),
            Struct {
                c: "abc".to_owned(),
                b: true,
                a: 1,
            }
        );
    }

    #[test]
    fn test_parse_tuple_ignoring_additional_fields() {
        let url_params = create_url_params(vec![
            ("a", "abc"),
            ("b", "true"),
            ("c", "1"),
            ("d", "false"),
        ]);
        assert_eq!(
            <(&str, bool, u32)>::deserialize(UriDeserializer::new(url_params, HashMap::new()))
                .unwrap(),
            ("abc", true, 1)
        );
    }

    #[test]
    fn test_parse_map() {
        let url_params = create_url_params(vec![("a", "1"), ("b", "true"), ("c", "abc")]);
        assert_eq!(
            <HashMap<String, String>>::deserialize(UriDeserializer::new(
                url_params,
                HashMap::new()
            ))
            .unwrap(),
            [("a", "1"), ("b", "true"), ("c", "abc")]
                .iter()
                .map(|(key, value)| ((*key).to_owned(), (*value).to_owned()))
                .collect()
        );
    }

    macro_rules! test_parse_error {
        (
            $params:expr,
            $ty:ty,
            $expected_error_kind:expr $(,)?
        ) => {
            let url_params = create_url_params($params);
            let actual_error_kind =
                <$ty>::deserialize(UriDeserializer::new(url_params, HashMap::new()))
                    .unwrap_err()
                    .kind;
            assert_eq!(actual_error_kind, $expected_error_kind);
        };
    }

    #[test]
    fn test_wrong_number_of_parameters_error() {
        test_parse_error!(
            vec![("a", "1")],
            (u32, u32),
            ErrorKind::WrongNumberOfParameters {
                got: 1,
                expected: 2,
            }
        );
    }

    #[test]
    fn test_parse_error_at_key_error() {
        #[derive(Debug, Deserialize)]
        #[allow(dead_code)]
        struct Params {
            a: u32,
        }
        test_parse_error!(
            vec![("a", "false")],
            Params,
            ErrorKind::ParseErrorAtKey {
                key: "a".to_owned(),
                value: "false".to_owned(),
                expected_type: "u32",
            }
        );
    }

    #[test]
    fn test_parse_error_at_key_error_multiple() {
        #[derive(Debug, Deserialize)]
        #[allow(dead_code)]
        struct Params {
            a: u32,
            b: u32,
        }
        test_parse_error!(
            vec![("a", "false")],
            Params,
            ErrorKind::ParseErrorAtKey {
                key: "a".to_owned(),
                value: "false".to_owned(),
                expected_type: "u32",
            }
        );
    }

    #[test]
    fn test_parse_error_at_index_error() {
        test_parse_error!(
            vec![("a", "false"), ("b", "true")],
            (bool, u32),
            ErrorKind::ParseErrorAtIndex {
                index: 1,
                value: "true".to_owned(),
                expected_type: "u32",
            }
        );
    }

    #[test]
    fn test_parse_error_error() {
        test_parse_error!(
            vec![("a", "false")],
            u32,
            ErrorKind::ParseError {
                value: "false".to_owned(),
                expected_type: "u32",
            }
        );
    }

    #[test]
    fn test_unsupported_type_error_nested_data_structure() {
        test_parse_error!(
            vec![("a", "false")],
            Vec<Vec<u32>>,
            ErrorKind::UnsupportedType {
                name: "alloc::vec::Vec<u32>",
            }
        );
    }

    #[test]
    fn test_parse_seq_tuple_unsupported_key_type() {
        test_parse_error!(
            vec![("a", "false")],
            Vec<(u32, String)>,
            ErrorKind::Message("Unexpected key type".to_owned())
        );
    }

    #[test]
    fn test_parse_seq_wrong_tuple_length() {
        test_parse_error!(
            vec![("a", "false")],
            Vec<(String, String, String)>,
            ErrorKind::UnsupportedType {
                name: "(alloc::string::String, alloc::string::String, alloc::string::String)",
            }
        );
    }

    #[test]
    fn test_parse_seq_seq() {
        test_parse_error!(
            vec![("a", "false")],
            Vec<Vec<String>>,
            ErrorKind::UnsupportedType {
                name: "alloc::vec::Vec<alloc::string::String>",
            }
        );
    }
}
