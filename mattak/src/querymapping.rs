use std::convert::Infallible;

use axum::{http, response::IntoResponse};

#[derive(PartialEq, Eq, Clone, Copy, Default, Debug, serde::Serialize)]
pub struct NoId;

impl From<NoId> for Infallible {
    fn from(_val: NoId) -> Self {
        unreachable!("it's not an id")
    }
}

/// Use as a generic type to skip fields that might sometimes be included
#[derive(sqlx::FromRow, Debug, Default, Clone, Copy, serde::Serialize)]
#[allow(dead_code)] // Have to match DB
pub struct Omit {}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("sqlx: ${0:?}")]
    Sqlx(#[from] sqlx::Error),
}

impl IntoResponse for Error {
    fn into_response(self) -> axum::response::Response {
        use http::status::StatusCode;
        match self {
            Error::Sqlx(ref e) => match e {
                sqlx::Error::TypeNotFound { .. } | sqlx::Error::ColumnNotFound(_) => {
                    (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()).into_response()
                }

                sqlx::Error::Configuration(_)
                | sqlx::Error::Migrate(_)
                | sqlx::Error::Database(_)
                | sqlx::Error::Tls(_)
                | sqlx::Error::AnyDriverError(_) => StatusCode::BAD_GATEWAY.into_response(),

                sqlx::Error::Io(_)
                | sqlx::Error::Protocol(_)
                | sqlx::Error::PoolTimedOut
                | sqlx::Error::PoolClosed
                | sqlx::Error::WorkerCrashed => StatusCode::GATEWAY_TIMEOUT.into_response(),

                sqlx::Error::RowNotFound => StatusCode::NOT_FOUND.into_response(),

                sqlx::Error::ColumnIndexOutOfBounds { .. }
                | sqlx::Error::ColumnDecode { .. }
                | sqlx::Error::Encode(_)
                | sqlx::Error::Decode(_) => StatusCode::BAD_REQUEST.into_response(),

                _ => StatusCode::INTERNAL_SERVER_ERROR.into_response(),
            },
        }
    }
}
