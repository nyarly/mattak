use axum::{
    extract::{self, FromRef},
    response::IntoResponse,
};
use axum_extra::extract as extra_extract;
use base64ct::{Base64, Encoding as _};
use biscuit_auth::{
    error,
    macros::{biscuit, fact},
    Algorithm, Authorizer, AuthorizerBuilder, AuthorizerLimits, Biscuit, KeyPair, PrivateKey,
};
use hyper::StatusCode;
use std::{
    fs::File,
    io::{self, Read, Write},
    net::SocketAddr,
    path::Path,
    time::{Duration, SystemTime},
};
use tracing::{debug, trace};

pub mod keysets;
pub mod middleware;
pub mod resources;

#[derive(thiserror::Error, Debug)]
#[non_exhaustive]
pub enum Error {
    #[error("issue building token: {0:?}")]
    Token(#[from] biscuit_auth::error::Token),
    #[error("no authentication context found")]
    MissingContext,
    #[error("no authentication credential token found")]
    NoToken,
    #[error("provided token has been revoked")]
    RevokedToken,
    #[error("authorization failed")]
    AuthorizationFailed,
    #[error("fetching keyset: {0}")]
    KeysetFetch(#[from] reqwest::Error),
    #[error("extracting host")]
    Host(#[from] extract::rejection::HostRejection),
    #[error("routing match error")]
    MatchedPath(#[from] extract::rejection::MatchedPathRejection),
    #[error("nested path error")]
    NestedPath(#[from] extract::rejection::NestedPathRejection),
    #[error("extension error")]
    Extension(#[from] extract::rejection::ExtensionRejection),
    #[error("extracting path params")]
    PathParams(#[from] extract::rejection::RawPathParamsRejection),
    #[error("extracting query params")]
    Query(#[from] extra_extract::QueryRejection),
    #[error("deserializing WebKeys: {0}")]
    KeysetDeserialize(#[from] serde_json::Error),
    #[error("URI authority (domain:port) required for authentication")]
    URIAuthorityMissing,
    #[error("URI authority ({0}) not configured with an upstream authentication authority")]
    NoKeysetForAuthority(String),
    #[error("conditional request error: {0:?}")]
    CondReq(#[from] mattak_condreq::Error),
}

impl IntoResponse for Error {
    fn into_response(self) -> axum::response::Response {
        match self {
            Error::CondReq(e) => e.into_response(),
            Error::MatchedPath(e) => e.into_response(),
            Error::NestedPath(e) => e.into_response(),
            Error::Extension(e) => e.into_response(),
            Error::PathParams(e) => e.into_response(),
            Error::Host(e) => e.into_response(),
            Error::Query(e) => e.into_response(),
            Error::NoToken => (StatusCode::UNAUTHORIZED, "/api/authentication").into_response(),
            Error::RevokedToken => {
                (StatusCode::UNAUTHORIZED, "/api/authentication").into_response()
            }
            Error::AuthorizationFailed => {
                (StatusCode::FORBIDDEN, "insufficient access").into_response()
            }
            Error::MissingContext => {
                (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()).into_response()
            }
            Error::Token(err) => match err {
                biscuit_auth::error::Token::ConversionError(_) => {
                    (StatusCode::BAD_REQUEST, "couldn't convert token").into_response()
                }
                biscuit_auth::error::Token::Base64(_) => {
                    (StatusCode::BAD_REQUEST, "invalid token encoding").into_response()
                }
                biscuit_auth::error::Token::Format(_) => {
                    (StatusCode::BAD_REQUEST, "invalid token format").into_response()
                }
                _ => (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "internal authentication error",
                )
                    .into_response(),
            },
            Error::URIAuthorityMissing | Error::NoKeysetForAuthority(_) => (
                StatusCode::BAD_REQUEST,
                format!("request cannot be authenticated: {:?}", self),
            )
                .into_response(),
            Error::KeysetDeserialize(_) | Error::KeysetFetch(_) => {
                debug!("internal authentication issue");
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "internal authentication error",
                )
                    .into_response()
            }
        }
    }
}

fn show_matching_policy(idx: usize, az: Authorizer) -> Result<String, Error> {
    match az.save()?.policies.get(idx) {
        Some(pol) => Ok(format!("{}", pol)),
        None => Ok("<cannot find policy!>".to_string()),
    }
}

fn show_checks(checks: Vec<error::FailedCheck>) -> String {
    checks
        .into_iter()
        .map(|check| match check {
            error::FailedCheck::Block(c) => format!("block {} :{}", c.block_id, c.rule),
            error::FailedCheck::Authorizer(c) => format!("autherizer: {}", c.rule),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_rejection(az: Authorizer, token: error::Token) -> Result<String, Error> {
    match token {
        error::Token::FailedLogic(error::Logic::Unauthorized { policy, checks }) => match policy {
            error::MatchedPolicy::Deny(idx) => Ok(format!(
                "refused by policy: {} - failed checks: {}",
                show_matching_policy(idx, az)?,
                show_checks(checks)
            )),
            error::MatchedPolicy::Allow(_) => Ok(format!("failed checks: {}", show_checks(checks))),
        },
        error::Token::FailedLogic(error::Logic::NoMatchingPolicy { checks }) => Ok(format!(
            "no matching policy; failed checks: {}",
            show_checks(checks)
        )),
        _ => Ok(format!("{:?}", token)),
    }
}

#[derive(Clone)]
pub struct AuthContext {
    authority: Option<Biscuit>,
    revoked_ids: Vec<String>,
    authorizer: AuthorizerBuilder,
}

impl AuthContext {
    pub fn revocation_ids(&self) -> Option<Vec<String>> {
        self.authority.as_ref().map(|token| {
            token
                .revocation_identifiers()
                .into_iter()
                .map(|rev| Base64::encode_string(&rev))
                .collect()
        })
    }

    pub fn with_revoked_ids(&self, newrids: Vec<String>) -> AuthContext {
        let mut other = self.clone();
        let mut newrids = newrids.clone();
        other.revoked_ids.append(&mut newrids);
        other
    }

    pub fn check(&self, policy: AuthorizerBuilder) -> Result<(), Error> {
        let token = match &self.authority {
            Some(token) => token,
            None => {
                debug!("No token included in request for controlled resource");
                return Err(Error::NoToken);
            }
        };
        for raw_token_rvk in token.revocation_identifiers() {
            let token_rvk = Base64::encode_string(&raw_token_rvk);
            for ctx_rvk in &self.revoked_ids {
                trace!("compare: {:?} / {:?}", token_rvk, ctx_rvk);
                if token_rvk == *ctx_rvk {
                    debug!("token revoked: {:?}", token_rvk);
                    return Err(Error::RevokedToken);
                }
            }
        }
        let mut az = self
            .authorizer
            .clone()
            .merge(policy)
            .time()
            .set_limits(AuthorizerLimits {
                max_time: Duration::from_millis(20),
                ..Default::default()
            })
            .build(token)?;
        debug!("Authorizing against: \n{}", az.dump_code());
        match az.authorize() {
            Ok(idx) => {
                // XXX conditional compile?
                debug!(
                    "Authorized by: \n{}",
                    match az.save()?.policies.get(idx) {
                        Some(pol) => format!("{}", pol),
                        None => "<cannot find authorizing policy!>".to_string(),
                    }
                );
                Ok(())
            }
            Err(err) => {
                debug!("Authorization rejected: {}", format_rejection(az, err)?);
                Err(Error::AuthorizationFailed)
            }
        }
    }
}

pub struct TokenBundle {
    pub token: String,
    pub revocation_ids: Vec<String>,
}

impl TokenBundle {
    fn build(biscuit: Biscuit) -> Result<Self, Error> {
        let token = biscuit.to_base64()?;
        let revocation_ids = biscuit
            .revocation_identifiers()
            .into_iter()
            .map(|rev| {
                trace!(
                    "biscuit revocation ID b64: {:?}",
                    Base64::encode_string(&rev)
                );
                Base64::encode_string(&rev)
            })
            .collect();
        Ok(Self {
            token,
            revocation_ids,
        })
    }
}

#[derive(Clone, FromRef)]
pub struct Authentication {
    private_key: PrivateKey,
    key_id: u32,
}

impl Authentication {
    pub fn new<P: AsRef<Path> + Clone>(
        persist_path: P,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let private_key = match File::open(persist_path.clone()) {
            Ok(mut f) => {
                let mut k = String::new();
                f.read_to_string(&mut k)?;
                PrivateKey::from_bytes_hex(&k, Algorithm::Ed25519)?
            }
            Err(err) if err.kind() == io::ErrorKind::NotFound => {
                let kp = KeyPair::new();
                let data = kp.private().to_bytes_hex();
                let mut f = File::create_new(persist_path)?;
                f.write_all(data.as_bytes())?;
                kp.private()
            }
            Err(e) => Err(e)?,
        };
        Ok(Self {
            private_key,
            key_id: 1, // :(
        })
    }

    fn keypair(&self) -> KeyPair {
        KeyPair::from(&(self.private_key))
    }

    pub fn reset_password(&self, userid: &str, expires: SystemTime) -> Result<TokenBundle, Error> {
        let now = SystemTime::now();
        let builder = biscuit!(
            r#"
        reset_password({userid});
        issued_at({now});
        check if issued_at($issued), time($time), $issued <= $time;
        check if time($time), $time < {expires};
        "#
        );
        TokenBundle::build(builder.build(&self.keypair())?)
    }

    /// A convenience method for building a authentication token
    /// The result is (biscuit_auth::Biscuit.to_base64(), Biscuit.revocation_identifiers().to_base64())
    /// The caller is responsible for storing the revocation ids!
    /// Likewise, you are responsible for providing revoked IDs in the AuthContext
    pub fn authority(
        &self,
        userid: &str,
        expires: SystemTime,
        maybe_addr: Option<SocketAddr>,
    ) -> Result<TokenBundle, Error> {
        let now = SystemTime::now();
        let mut builder = biscuit!(
            r#"
        user({userid});
        issued_at({now});
        check if issued_at($issued), time($time), $issued <= $time;
        check if time($time), $time < {expires};
        "#
        );
        if let Some(addr) = maybe_addr {
            let addr_str = addr.ip().to_string();
            builder = builder.fact(fact!("client_ip({addr_str})"))?;
        }
        TokenBundle::build(builder.build(&self.keypair())?)
    }
}
