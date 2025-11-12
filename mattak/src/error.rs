use axum::{http, response::IntoResponse};
use tracing::debug;

#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("unknown error: {0}")]
    Unknown(String),
    #[error("database error: {0}")]
    #[cfg(feature = "querymapping")]
    Querymapping(#[from] crate::querymapping::Error),
    #[error("authentication: {0}")]
    #[cfg(feature = "biscuits")]
    Biscuits(#[from] crate::biscuits::Error),
    // #[error("cachecontrol: {0:?}")]
    // Cachecontrol(#[from] cachecontrol::Error),
    #[error("condreq: {0:?}")]
    #[cfg(feature = "condreq")]
    Condreq(#[from] crate::condreq::Error),
    #[error("hypermedia: {0:?}")]
    #[cfg(feature = "hypermedia")]
    Hypermedia(#[from] crate::hypermedia::Error),
    // #[error("ratelimiting: {0:?}")]
    // Ratelimiting(#[from] ratelimiting::Error),
    #[error("routing: {0:?}")]
    #[cfg(feature = "routing")]
    Routing(#[from] crate::routing::Error),
}

impl IntoResponse for Error {
    fn into_response(self) -> axum::response::Response {
        debug!("Returning error: {:?}", &self);
        match self {
            #[cfg(feature = "biscuits")]
            Error::Biscuits(e) => e.into_response(),
            #[cfg(feature = "querymapping")]
            Error::Querymapping(e) => e.into_response(),
            #[cfg(feature = "condreq")]
            Error::Condreq(e) => e.into_response(),
            #[cfg(feature = "hypermedia")]
            Error::Hypermedia(e) => e.into_response(),
            #[cfg(feature = "routing")]
            Error::Routing(e) => e.into_response(),
            Error::Unknown(_) => {
                (http::StatusCode::INTERNAL_SERVER_ERROR, self.to_string()).into_response()
            }
        }
    }
}
