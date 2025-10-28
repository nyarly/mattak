use mattak::routing::template_vars;
use proc_macro::TokenStream as StdTokenStream;
use proc_macro2::{Delimiter, Ident, TokenStream, TokenTree};
use quote::quote;

/*
* Given
#[derive(Route)]
#[template(/event_games/{event_id}/user/{user_id})]
pub(crate) enum MyRoute {
  event_id: u16,
  user_id: String,
}

* Produce
impl RouteTemplate for MyRoute {
    fn route_template() -> RouteTemplateString {
        RouteTemplateString("/event_games/{event_id}/user/{user_id}".to_string())
    }
}
*/

#[proc_macro]
pub fn id_type(input: StdTokenStream) -> StdTokenStream {
    #[cfg(debug_output)]
    eprintln!("INPUT: {:?}\n\n", input);

    let proc2_item = TokenStream::from(input);

    let mut tok_iter = proc2_item.into_iter().peekable();

    // INPUT: TokenStream [Ident { ident: "TwoId", span: #0 bytes(3192..3197) }, Group { delimiter: Parenthesis, stream: TokenStream [Ident { ident: "i64", span:
    // #0 bytes(3198..3201) }], span: #0 bytes(3197..3202) }, Punct { ch: ',', spacing: Alone, span: #0 bytes(3202..3203) }, Ident { ident: "IdForTwo", span: #0
    // bytes(3204..3212) }]

    let name = if let Some(ident) = tok_iter.next() {
        ident
    } else {
        panic!("first id_type token must be an ident");
    };

    let wraps = if let Some(TokenTree::Group(group)) = tok_iter.next() {
        let mut group_iter = group.stream().into_iter();
        if let Some(ident) = group_iter.next() {
            ident
        } else {
            panic!("id_type wrapping group must not be empty");
        }
    } else {
        panic!("id_type ended early");
    };

    let mut expanded = quote! {
        #[derive(::std::cmp::PartialEq, ::std::cmp::Eq, ::std::hash::Hash, ::std::fmt::Debug, ::std::clone::Clone, ::std::marker::Copy, ::sqlx::Type, ::serde::Deserialize, ::serde::Serialize)]
        #[sqlx(transparent)]
        #[serde(transparent)]
        pub struct #name(#wraps);

        impl ::std::convert::From<#wraps> for #name {
            fn from(n: #wraps) -> Self {
                Self(n)
            }
        }

        impl ::std::convert::From<#name> for #wraps {
            fn from(val: #name) -> Self {
                val.0
            }
        }

        impl ::std::fmt::Display for #name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> Result<(), ::std::fmt::Error> {
                write!(f, "#name{}", self.0)
            }
        }
    };

    if let Some(_) = tok_iter.next() {
        if let Some(marker) = tok_iter.next() {
            let extra = quote! {
                pub(crate) trait #marker {}
                impl #marker for #name {}
                impl #marker for ::mattak::querymapping::NoId {}
            };
            expanded.extend(extra);
        }
    }
    #[cfg(debug_output)]
    eprintln!("OUTPUT: {:?}\n\n", expanded);
    expanded.into()
}

#[proc_macro_derive(Route, attributes(template, assoc))]
pub fn route_derive(annotated_item: StdTokenStream) -> StdTokenStream {
    let (struct_name, template, vars, _var_types, assoc_vars) = parse_route(annotated_item);

    validate_route(template.clone(), vars.clone());

    let expanded = quote! {
        impl ::mattak::routing::Route for #struct_name {
            fn route_template() -> ::mattak::routing::RouteTemplateString {
                ::mattak::routing::RouteTemplateString(#template.to_string(), vec![#(stringify!(#assoc_vars).to_string()),*])
            }
        }

        impl ::mattak::routing::Listable for #struct_name {
            fn list_vars(&self) -> Vec<String> {
                vec![#(stringify!(#vars).to_string()),*]
            }
        }
    };

    // to enable debug_output:
    // cargo test --config "build.rustflags = '--cfg=debug_output'"
    #[cfg(debug_output)]
    eprintln!("{}", expanded);
    expanded.into()
}

fn validate_route(template: TokenStream, vars: Vec<Ident>) {
    let mut tmpl_iter = template.into_iter();
    let tmpl_string = match tmpl_iter.next() {
        Some(TokenTree::Literal(t)) => t.to_string(),
        _ => panic!("#[template(...)] argument must be a string!"),
    };
    let tmpl_string = tmpl_string.trim_matches('"');
    #[cfg(debug_output)]
    eprintln!("TEMPLATE {tmpl_string:?}");

    let mut expected = template_vars(tmpl_string);
    expected.sort();
    expected.dedup();
    let mut actual = vars.iter().map(|v| v.to_string()).collect::<Vec<_>>();
    actual.sort();

    #[cfg(debug_output)]
    eprintln!("EXPECTED {expected:?}");
    #[cfg(debug_output)]
    eprintln!("ACTUAL   {actual:?}");

    if expected != actual {
        panic!("fields of a Route have to match their #[template(...)] vars!");
    }
}

/*
* Given
#[derive(RouteTemplate)]
#[template(/event_games/{event_id}/user/{user_id})]
pub(crate) enum MyRoute {
  event_id: u16,
  user_id: String,
}

* Produce
impl RouteTemplate for MyRoute {
    fn route_template(&self) -> String {
        "/event_games/{event_id}/user/{user_id}".to_string()
    }
*/

#[proc_macro_derive(RouteTemplate, attributes(template))]
pub fn route_template_derive(annotated_item: StdTokenStream) -> StdTokenStream {
    let (struct_name, template) = parse_route_template(annotated_item);

    let expanded = quote! {
        impl ::mattak::routing::RouteTemplate for #struct_name {
            fn route_template(&self) -> String {
                #template.to_string()
            }
        }
    };

    // to enable debug_output:
    // cargo test --config "build.rustflags = '--cfg=debug_output'"
    #[cfg(debug_output)]
    eprintln!("{}", expanded);
    expanded.into()
}

/*
Given:
#[derive(Listable)]
struct MyLocationType {
    event_id: u16,
    user_id: String
}

we want to produce:

impl crate::routing::Listable for MyLocationType {
    fn list_vars(&self) -> Vec<String> {
        vec!["event_id".to_string(), "user_id".to_string()]
    }
}

XXX consider helper attrs to customize inclusion etc
*/

#[proc_macro_derive(Listable)]
pub fn listable_derive(annotated_item: StdTokenStream) -> StdTokenStream {
    let (struct_name, vars, _) = parse(annotated_item);

    let expanded = quote! {
        impl ::mattak::routing::Listable for #struct_name {
            fn list_vars(&self) -> Vec<String> {
                vec![#(stringify!(#vars).to_string()),*]
            }
        }
    };

    // to enable debug_output:
    // cargo test --config "build.rustflags = '--cfg=debug_output'"
    #[cfg(debug_output)]
    eprintln!("{}", expanded);
    expanded.into()
}

/*
Given:
#[derive(Context)]
struct MyLocationType {
    event_id: u16,
    user_id: String
}

Then:
impl ::iri_string::template::context::Context for MyLocationType {
    fn visit<V: iri_string::template::context::Visitor>(&self, visitor: V) -> V::Result {
        match visitor.var_name().as_str() {
            "event_id" => visitor.visit_string(self.event_id),
            "user_id" => visitor.visit_string(self.user_id),
            _ => visitor.visit_undefined()
        }
    }
}

XXX consider helper attrs to customize visit type
*/

#[proc_macro_derive(Context)]
pub fn context_derive(item: StdTokenStream) -> StdTokenStream {
    let (struct_name, vars, _) = parse(item);

    let expanded = quote! {
        impl ::mattak::routing::context::Context for #struct_name {
            fn visit<V: ::mattak::routing::context::Visitor>(&self, visitor: V) -> V::Result {
                match visitor.var_name().as_str() {
                    #( stringify!(#vars) => visitor.visit_string(self.#vars.clone()), )*
                    _ => visitor.visit_undefined()
                }
            }
        }
    };

    #[cfg(debug_output)]
    eprintln!("{}", expanded);
    expanded.into()
}

#[proc_macro_derive(Extract)]
pub fn extract_derive(item: StdTokenStream) -> StdTokenStream {
    let (struct_name, vars, var_types) = parse(item);

    let expanded = quote! {
        impl<'de> ::serde::Deserialize<'de> for #struct_name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where D: ::serde::Deserializer<'de> {
                let ( #( #vars ),* ) = <( #( #var_types ),* ) as ::serde::Deserialize>::deserialize(deserializer)?;
                Ok(Self{ #( #vars ),* })
            }
        }
    };

    #[cfg(debug_output)]
    eprintln!("{}", expanded);
    expanded.into()
}

fn parse(input: StdTokenStream) -> (Ident, Vec<Ident>, Vec<TokenTree>) {
    let proc2_item = TokenStream::from(input);
    #[cfg(debug_output)]
    eprintln!("INPUT: {:?}\n\n", proc2_item);
    let mut tok_iter = proc2_item.into_iter().peekable();

    loop {
        match tok_iter.next() {
            Some(TokenTree::Ident(s)) if s == "struct" => break,
            None => panic!("cannot derive Listable without a struct"),
            _ => (),
        }
    }

    let struct_name = match tok_iter.next() {
        Some(TokenTree::Ident(s)) => s,
        _ => panic!("don't know what to do with a non-ident in this position"),
    };
    let body = match tok_iter.next() {
        Some(TokenTree::Group(g)) => g,
        _ => panic!("now I'm expecting a group"),
    };
    let mut body_iter = body.stream().into_iter().peekable();
    let mut fields = vec![];
    let mut field_types = vec![];
    while let Some(tok) = body_iter.next() {
        match (tok, body_iter.peek()) {
            (TokenTree::Ident(var), Some(TokenTree::Punct(punct))) if punct.as_char() == ':' => {
                fields.push(var);
                body_iter.next(); // consume the ':'
                field_types.push(body_iter.next().expect("a single ident type after :"))
                // naive assumption
            }
            _ => (),
        }
    }

    #[cfg(debug_output)]
    eprintln!("STRUCT: {:?}", struct_name);
    #[cfg(debug_output)]
    eprintln!("VARS: {:?}", fields);

    (struct_name, fields, field_types)
}

fn parse_route_template(input: StdTokenStream) -> (Ident, TokenStream) {
    let proc2_item = TokenStream::from(input);
    #[cfg(debug_output)]
    eprintln!("INPUT: {:?}\n\n", proc2_item);
    let mut tok_iter = proc2_item.into_iter().peekable();

    let mut attr_iter: std::iter::Peekable<proc_macro2::token_stream::IntoIter>;
    loop {
        loop {
            match tok_iter.next() {
                Some(TokenTree::Punct(p)) if p.as_char() == '#' => break,
                None => panic!("Route template requires #[template(\"...\")]"),
                _ => (),
            }
        }

        let attr = match tok_iter.next() {
            Some(TokenTree::Group(br)) if br.delimiter() == Delimiter::Bracket => br.stream(),
            _ => panic!("#[template(...)] required by RouteTemplate"),
        };

        attr_iter = attr.into_iter().peekable();
        match attr_iter.next() {
            Some(TokenTree::Ident(n)) if n == "template" => break,
            Some(TokenTree::Ident(_)) => (),
            _ => panic!("expecting an attribute name inside #[...]"),
        };
    }

    let template = match attr_iter.next() {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis => g.stream(),
        _ => panic!("#[template] must have (\"<template>\")"),
    };

    loop {
        match tok_iter.next() {
            Some(TokenTree::Ident(s)) if s == "struct" => break,
            None => panic!("RouteTemplate can only be derived on a struct"),
            _ => (),
        }
    }

    let struct_name = match tok_iter.next() {
        Some(TokenTree::Ident(s)) => s,
        _ => panic!("don't know what to do with a non-ident after `struct`"),
    };

    #[cfg(debug_output)]
    eprintln!("STRUCT: {:?}", struct_name);
    #[cfg(debug_output)]
    eprintln!("TEMPLATE: {:?}", template);

    (struct_name, template)
}

fn parse_route(
    input: StdTokenStream,
) -> (Ident, TokenStream, Vec<Ident>, Vec<TokenTree>, Vec<Ident>) {
    let proc2_item = TokenStream::from(input);
    #[cfg(debug_output)]
    eprintln!("INPUT: {:?}\n\n", proc2_item);
    let mut tok_iter = proc2_item.into_iter().peekable();

    let mut attr_iter: std::iter::Peekable<proc_macro2::token_stream::IntoIter>;
    loop {
        loop {
            match tok_iter.next() {
                Some(TokenTree::Punct(p)) if p.as_char() == '#' => break,
                None => panic!("Route template requires #[template(\"...\")]"),
                _ => (),
            }
        }

        let attr = match tok_iter.next() {
            Some(TokenTree::Group(br)) if br.delimiter() == Delimiter::Bracket => br.stream(),
            _ => panic!("#[template(...)] required by RouteTemplate"),
        };

        attr_iter = attr.into_iter().peekable();
        match attr_iter.next() {
            Some(TokenTree::Ident(n)) if n == "template" => break,
            Some(TokenTree::Ident(_)) => (),
            _ => panic!("expecting an attribute name inside #[...]"),
        };
    }

    let template = match attr_iter.next() {
        Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis => g.stream(),
        _ => panic!("#[template] must have (\"<template>\")"),
    };

    loop {
        match tok_iter.next() {
            Some(TokenTree::Ident(s)) if s == "struct" => break,
            None => panic!("Route can only be derived on a struct"),
            _ => (),
        }
    }

    let struct_name = match tok_iter.next() {
        Some(TokenTree::Ident(s)) => s,
        _ => panic!("don't know what to do with a non-ident after `struct`"),
    };

    let body = match tok_iter.next() {
        Some(TokenTree::Group(g)) => g,
        _ => panic!("now I'm expecting a group"),
    };
    let mut body_iter = body.stream().into_iter().peekable();
    let mut fields = vec![];
    let mut assocs = vec![];
    let mut field_types = vec![];
    let mut next_is_assoc = false;
    while let Some(tok) = body_iter.next() {
        match (tok, body_iter.peek()) {
            (TokenTree::Punct(p), _) if p.as_char() == '#' => {
                let attr = match body_iter.next() {
                    Some(TokenTree::Group(br)) if br.delimiter() == Delimiter::Bracket => {
                        br.stream()
                    }
                    _ => panic!("expecting #[...]"),
                };
                attr_iter = attr.into_iter().peekable();
                match attr_iter.next() {
                    Some(TokenTree::Ident(n)) if n == "assoc" => {
                        next_is_assoc = true;
                    }
                    _ => panic!("expecting #[assoc]"),
                };
            }
            (TokenTree::Ident(var), Some(TokenTree::Punct(punct))) if punct.as_char() == ':' => {
                if next_is_assoc {
                    assocs.push(var.clone());
                    next_is_assoc = false;
                }
                fields.push(var);

                body_iter.next(); // consume the ':'
                field_types.push(body_iter.next().expect("a single ident type after :"))
                // naive assumption
            }
            _ => (),
        }
    }

    #[cfg(debug_output)]
    eprintln!("STRUCT: {:?}", struct_name);
    #[cfg(debug_output)]
    eprintln!("TEMPLATE: {:?}", template);
    #[cfg(debug_output)]
    eprintln!("FIELDS: {:?}", fields);

    (struct_name, template, fields, field_types, assocs)
}
