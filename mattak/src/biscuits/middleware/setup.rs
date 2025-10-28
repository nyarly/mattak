use super::{AuthContext, Authentication, Error};
use axum::{
    extract::{self, Request},
    response::{IntoResponse as _, Response},
    RequestExt,
};
use axum_extra::extract as extra_extract;
use biscuit_auth::{
    macros::{authorizer, fact},
    Biscuit, PublicKey, RootKeyProvider,
};
use futures::{ready, FutureExt as _, TryFutureExt as _};
use futures_util::future::BoxFuture;
use pin_project_lite::pin_project;
use std::{
    collections::HashMap,
    future::{self, Future},
    net::SocketAddr,
    pin::Pin,
    task::{Context, Poll},
};
use tower::{Layer, Service};

async fn find_facts(
    header: String,
    root: impl RootKeyProvider,
    mut request: Request,
) -> Result<Request, Error> {
    let token = request
        .headers()
        .get(header.clone())
        .map(|val| Biscuit::from_base64(val.as_bytes(), root))
        .transpose()?;

    let version = request.version();
    let version_str = format!("{:?}", version);

    let method = request.method().clone();
    let method_str = method.as_str();

    let uri = request.uri().clone();
    let uri_path = uri.path();

    let maybe_uri_scheme = uri.scheme_str();
    let maybe_uri_port = uri.port_u16();
    let maybe_path_and_query = uri.path_and_query();

    let extract::Host(host) = request.extract_parts().await?;

    let matched_path = request.extract_parts::<extract::MatchedPath>().await?;
    let full_route = matched_path.as_str();

    let nested_path = request.extract_parts::<extract::NestedPath>().await?;
    let nested_at = nested_path.as_str();

    let maybe_route = full_route.strip_prefix(nested_at);

    let mut auth_builder = authorizer!(
        r#"
        version({version_str});
        host({host});
        method({method_str});
        full_route({full_route});
        nested_at({nested_at});
        path({uri_path});
        "#
    );

    if let Some(route) = maybe_route {
        auth_builder = auth_builder.fact(fact!("route({route})"))?;
    }

    if let Some(uri_scheme) = maybe_uri_scheme {
        auth_builder = auth_builder.fact(fact!("uri_scheme({uri_scheme})"))?;
    }

    if let Some(uri_port) = maybe_uri_port {
        let uri_port = uri_port as i64;
        auth_builder = auth_builder.fact(fact!("uri_port({uri_port})"))?;
    }

    if let Some(path_and_query) = maybe_path_and_query {
        let full_path_str = path_and_query.as_str();
        auth_builder = auth_builder.fact(fact!("full_path({full_path_str})"))?;
    }

    let maybe_connection_info = request
        .extract_parts::<Option<extract::ConnectInfo<SocketAddr>>>()
        .await
        .expect("infallible to mean infallible");
    if let Some(extract::ConnectInfo(addr)) = maybe_connection_info {
        let ip = addr.ip().to_string();
        auth_builder = auth_builder.fact(fact!("client_ip({ip})"))?;
    }

    let path_params = request.extract_parts::<extract::RawPathParams>().await?;
    for (key, value) in &path_params {
        auth_builder = auth_builder.fact(fact!("path_param({key}, {value})"))?;
    }

    let extra_extract::Query(query_params): extra_extract::Query<HashMap<String, String>> =
        request.extract_parts().await?;
    for (key, value) in query_params {
        auth_builder = auth_builder.fact(fact!("query_param({key}, {value})"))?;
    }

    let ctx = AuthContext {
        authority: token,
        authorizer: auth_builder,
        revoked_ids: vec![],
    };
    request.extensions_mut().insert(ctx);
    Ok(request)
}

pub trait GetPublic {
    type PublicKey: RootKeyProvider + Send + 'static;
    fn get_public(&self, req: &Request) -> Result<Self::PublicKey, Error>;
}

pub trait GetPublicSource {
    type Public: GetPublic;

    fn make_get_public(&self) -> Self::Public;
}

impl GetPublic for Authentication {
    type PublicKey = PublicKey;
    fn get_public(&self, _: &Request) -> Result<Self::PublicKey, Error> {
        Ok(self.private_key.public())
    }
}

impl GetPublicSource for Authentication {
    type Public = Self;
    fn make_get_public(&self) -> Self {
        self.clone()
    }
}

#[derive(Clone)]
pub struct AuthenticationSetup<A: GetPublicSource> {
    pub root: A,
    pub header: String,
}

impl<A: GetPublicSource> AuthenticationSetup<A> {
    pub fn new<S: Into<String>>(root: A, header: S) -> Self {
        Self {
            root,
            header: header.into(),
        }
    }
}

impl<A: GetPublicSource, S> Layer<S> for AuthenticationSetup<A> {
    type Service = SetupMiddleware<A::Public, S>;

    fn layer(&self, inner: S) -> Self::Service {
        SetupMiddleware {
            inner,
            public: self.root.make_get_public(),
            header: self.header.clone(),
        }
    }
}

#[derive(Clone)]
pub struct SetupMiddleware<G, S> {
    pub(crate) inner: S,
    pub(crate) public: G,
    pub(crate) header: String,
}

impl<G, S> Service<Request> for SetupMiddleware<G, S>
where
    G: GetPublic,
    S: Service<Request, Response = Response> + Send + Clone + 'static,
    S::Future: Send + 'static,
    S::Error: Send,
{
    type Response = S::Response;
    type Error = S::Error;
    // `BoxFuture` is a type alias for `Pin<Box<dyn Future + Send + 'a>>`
    type Future = SetupFuture<BoxFuture<'static, Result<Request, Error>>, S>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }

    fn call(&mut self, request: Request) -> Self::Future {
        let pkr = self.public.get_public(&request);
        let h = self.header.clone();
        let future = future::ready(pkr).and_then(|pubkey| find_facts(h, pubkey, request));

        SetupFuture::new(future.boxed(), self.inner.clone())
    }
}

pin_project! {
    #[derive(Debug)]
    pub struct SetupFuture<F, S>
    where
        F: Future,
        S: Service<Request>,
    {
        #[pin]
        state: State<F, S::Future>,

        // Inner service
        service: S,
    }
}

pin_project! {
    #[project = StateProj]
    #[derive(Debug)]
    enum State<F, G> {
        /// Waiting for the find future
        Extracting {
            #[pin]
            extraction: F
        },
        /// Waiting for the response future
        WaitResponse {
            #[pin]
            response: G
        },
    }
}

impl<F, S> SetupFuture<F, S>
where
    F: Future,
    S: Service<Request>,
{
    pub(crate) fn new(extraction: F, service: S) -> Self {
        Self {
            state: State::Extracting { extraction },
            service,
        }
    }
}

impl<F, S> Future for SetupFuture<F, S>
where
    F: Future<Output = Result<Request, Error>>,
    S: Service<Request, Response = Response> + Send + 'static,
{
    type Output = Result<Response, S::Error>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        loop {
            match this.state.as_mut().project() {
                StateProj::Extracting { mut extraction } => {
                    match ready!(extraction.as_mut().poll(cx)) {
                        Ok(request) => {
                            let response = this.service.call(request);
                            this.state.set(State::WaitResponse { response });
                        }
                        Err(e) => return Poll::Ready(Ok(e.into_response())),
                    }
                }
                StateProj::WaitResponse { response } => {
                    return response.poll(cx).map_err(Into::into);
                }
            }
        }
    }
}
