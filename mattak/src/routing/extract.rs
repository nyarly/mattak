use ::core::{future::Future, pin::Pin};

use axum::{
    extract::{rejection::NestedPathRejection, FromRequestParts, NestedPath},
    http::request::Parts,
    response::IntoResponse,
};
use serde::de::DeserializeOwned;

use crate::{
    error,
    routing::{route_config, Route},
};

pub struct Extract<R: Route> {
    pub nested_path: String,
    pub route: R,
}

impl<R: Route + DeserializeOwned, S: Send + Sync> FromRequestParts<S> for Extract<R> {
    #[doc = " If the extractor fails it'll use this \"rejection\" type. A rejection is"]
    #[doc = " a kind of error that can be converted into a response."]
    type Rejection = Rejection;

    #[doc = " Perform the extraction."]
    #[allow(
        elided_named_lifetimes,
        clippy::type_complexity,
        clippy::type_repetition_in_bounds
    )]
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
        Box::pin(extract(parts, state))
    }
}

async fn extract<R: Route + DeserializeOwned, S: Send + Sync>(
    parts: &mut Parts,
    state: &S,
) -> Result<Extract<R>, Rejection> {
    let nested_path = NestedPath::from_request_parts(parts, state)
        .await
        .map_err(Rejection::from)?
        .as_str()
        .to_string();

    let rt = R::route_template();
    let cfg = route_config(rt);
    let route = cfg.from_uri(parts.uri.clone())?;

    Ok(Extract { nested_path, route })
}

#[derive(thiserror::Error, Debug)]
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
