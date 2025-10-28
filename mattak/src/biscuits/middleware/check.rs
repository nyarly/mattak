use axum::{
    extract::Request,
    response::{IntoResponse as _, Response},
};
use biscuit_auth::{format::schema::AuthorizerSnapshot, Authorizer, AuthorizerBuilder};
use futures::future::ok;
use futures_util::future::BoxFuture;
use std::task::{Context, Poll};
use tower::{Layer, Service};

use super::{AuthContext, Error};

pub trait IntoPolicySnapshot {
    fn into_snapshot(self) -> AuthorizerSnapshot;
}

impl IntoPolicySnapshot for String {
    fn into_snapshot(self) -> AuthorizerSnapshot {
        AuthorizerBuilder::new()
            .code(self)
            .expect("policy must parse")
            .snapshot()
            .expect("authorizor to snapshot from string")
    }
}

impl IntoPolicySnapshot for Authorizer {
    fn into_snapshot(self) -> AuthorizerSnapshot {
        self.snapshot().expect("authorizor to snapshot")
    }
}

impl IntoPolicySnapshot for AuthorizerSnapshot {
    fn into_snapshot(self) -> AuthorizerSnapshot {
        self
    }
}

#[derive(Clone)]
pub struct AuthenticationCheck {
    pub policy: AuthorizerSnapshot,
}

impl AuthenticationCheck {
    pub fn new<P: IntoPolicySnapshot>(policy: P) -> Self {
        Self {
            policy: policy.into_snapshot(),
        }
    }
}

impl<S> Layer<S> for AuthenticationCheck {
    type Service = CheckMiddleware<S>;

    fn layer(&self, inner: S) -> Self::Service {
        CheckMiddleware {
            inner,
            policy: self.policy.clone(),
        }
    }
}

fn check_authentication(
    policy_snapshot: AuthorizerSnapshot,
    request: Request,
) -> Result<Request, Error> {
    let ctx = request
        .extensions()
        .get::<AuthContext>()
        .ok_or(Error::MissingContext)?
        .clone();
    let policy = AuthorizerBuilder::from_snapshot(policy_snapshot)?;

    ctx.check(policy).map(|_| request)
}

#[derive(Clone)]
pub struct CheckMiddleware<S> {
    pub(crate) inner: S,
    pub(crate) policy: AuthorizerSnapshot,
}

impl<S> Service<Request> for CheckMiddleware<S>
where
    S: Service<Request, Response = Response> + Send + Clone + 'static,
    S::Future: Send + 'static,
    S::Error: Send,
{
    type Response = S::Response;
    type Error = S::Error;
    // `BoxFuture` is a type alias for `Pin<Box<dyn Future + Send + 'a>>`
    type Future = BoxFuture<'static, Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, request: Request) -> Self::Future {
        match check_authentication(self.policy.clone(), request) {
            Ok(req) => {
                let future = self.inner.call(req);
                Box::pin(async move {
                    let response: Response = future.await?;
                    Ok(response)
                })
            }
            Err(e) => {
                let future = ok(e.into_response());
                Box::pin(async move {
                    let response: Response = future.await?;
                    Ok(response)
                })
            }
        }
    }
}
