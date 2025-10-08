use ::core::{future::Future, pin::Pin};

use axum::{
    extract::{rejection::NestedPathRejection, FromRef, FromRequestParts, NestedPath},
    http::request::Parts,
    response::IntoResponse,
};
use hyper::Uri;
use serde::de::DeserializeOwned;

use crate::{
    error,
    routing::{route_config, Entry, Route, RouteTemplate as _},
};

pub struct NestedRoute<R: Route> {
    pub nested_path: NestedPath,
    pub nick: R,
}

impl<R: Route> NestedRoute<R> {
    pub fn entry(&self) -> Entry {
        R::route_template().prefixed(self.nested_path.as_str())
    }
}

impl<R, S> FromRequestParts<S> for NestedRoute<R>
where
    R: Route + DeserializeOwned,
    S: Send + Sync,
{
    /// If the extractor fails it'll use this "rejection" type. A rejection is
    /// a kind of error that can be converted into a response.
    type Rejection = Rejection;

    ///  Perform the extraction.
    #[allow(clippy::type_complexity, clippy::type_repetition_in_bounds)]
    fn from_request_parts<'life0, 'life1, 'async_trait>(
        parts: &'life0 mut Parts,
        state: &'life1 S,
    ) -> Pin<
        Box<
            dyn Future<Output = Result<Self, Self::Rejection>>
                + ::core::marker::Send
                + 'async_trait,
        >,
    >
    where
        'life0: 'async_trait,
        'life1: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(extract_nested(parts, state))
    }
}

pub async fn extract_nested<R, S>(parts: &mut Parts, state: &S) -> Result<NestedRoute<R>, Rejection>
where
    R: Route + DeserializeOwned,
    S: Send + Sync,
{
    let nested_path = NestedPath::from_request_parts(parts, state).await?;

    let rt = R::route_template();
    let cfg = route_config(rt);
    let route = cfg.from_uri(parts.uri.clone())?;

    Ok(NestedRoute {
        nested_path,
        nick: route,
    })
}

pub struct CanonicalUri(Uri);

pub struct CanonRoute<R: Route> {
    pub uri: Uri,
    pub nested_path: NestedPath,
    pub nick: R,
}

impl<R: Route> CanonRoute<R> {
    pub fn entry(&self) -> Entry {
        R::route_template().prefixed(self.nested_path.as_str())
    }
}

impl<R, S> FromRequestParts<S> for CanonRoute<R>
where
    R: Route + DeserializeOwned,
    CanonicalUri: FromRef<S>,
    S: Send + Sync,
{
    /// If the extractor fails it'll use this "rejection" type. A rejection is
    /// a kind of error that can be converted into a response.
    type Rejection = Rejection;

    /// Perform the extraction.
    #[allow(clippy::type_complexity, clippy::type_repetition_in_bounds)]
    fn from_request_parts<'life0, 'life1, 'async_trait>(
        parts: &'life0 mut Parts,
        state: &'life1 S,
    ) -> ::core::pin::Pin<
        Box<
            dyn ::core::future::Future<Output = Result<Self, Self::Rejection>>
                + ::core::marker::Send
                + 'async_trait,
        >,
    >
    where
        'life0: 'async_trait,
        'life1: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(extract_canon(parts, state))
    }
}

pub async fn extract_canon<R, S>(parts: &mut Parts, state: &S) -> Result<CanonRoute<R>, Rejection>
where
    R: Route + DeserializeOwned,
    S: Send + Sync,
    CanonicalUri: FromRef<S>,
{
    let uri = CanonicalUri::from_ref(&state).0;

    let nested_path = NestedPath::from_request_parts(parts, state).await?;

    let rt = R::route_template();
    let cfg = route_config(rt);
    let route = cfg.from_uri(parts.uri.clone())?;

    Ok(CanonRoute {
        uri,
        nested_path,
        nick: route,
    })
}

#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum Rejection {
    #[error("couldn't get nested path {0:?}")]
    NestedPath(#[from] NestedPathRejection),
    #[error("top-level error {0:?}")]
    TopLevel(#[from] error::Error), // XXX barf
}

impl IntoResponse for Rejection {
    fn into_response(self) -> axum::response::Response {
        match self {
            Rejection::NestedPath(npr) => npr.into_response(),
            Rejection::TopLevel(error) => error.into_response(),
        }
    }
}
