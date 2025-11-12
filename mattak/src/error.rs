use axum::{http, response::IntoResponse};
use tracing::debug;

use crate::{biscuits, condreq, hypermedia, querymapping, routing};

#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("unknown error: {0}")]
    Unknown(String),
    #[error("database error: {0}")]
    Querymapping(#[from] querymapping::Error),
    #[error("authentication: {0}")]
    Biscuits(#[from] biscuits::Error),
    // #[error("cachecontrol: {0:?}")]
    // Cachecontrol(#[from] cachecontrol::Error),
    #[error("condreq: {0:?}")]
    Condreq(#[from] condreq::Error),
    #[error("hypermedia: {0:?}")]
    Hypermedia(#[from] hypermedia::Error),
    // #[error("ratelimiting: {0:?}")]
    // Ratelimiting(#[from] ratelimiting::Error),
    #[error("routing: {0:?}")]
    Routing(#[from] routing::Error),
}

impl IntoResponse for Error {
    fn into_response(self) -> axum::response::Response {
        debug!("Returning error: {:?}", &self);
        match self {
            Error::Biscuits(e) => e.into_response(),
            Error::Querymapping(e) => e.into_response(),
            Error::Condreq(e) => e.into_response(),
            Error::Hypermedia(e) => e.into_response(),
            Error::Routing(e) => e.into_response(),
            Error::Unknown(_) => {
                (http::StatusCode::INTERNAL_SERVER_ERROR, self.to_string()).into_response()
            }
        }
    }
}
