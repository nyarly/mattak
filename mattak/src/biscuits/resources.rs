use axum::{extract::State, response::IntoResponse};
use biscuit_auth::BiscuitWebKey;
use chrono::{TimeDelta, Utc};
use serde::Serialize;

use crate::{
    biscuits::Authentication,
    condreq,
    routing::{Route, RouteTemplateString},
    Error,
};

pub struct WellKnownKeySet();

impl Route for WellKnownKeySet {
    fn route_template() -> RouteTemplateString {
        RouteTemplateString("/.well-known/biscuit-web-keys".to_string(), vec![])
    }
}

#[derive(Serialize, Clone)]
pub struct KeySetResponse(Vec<BiscuitWebKey>);

const ONE_WEEK: i64 = 60 * 60 * 24 * 7;

impl From<Authentication> for KeySetResponse {
    fn from(auth: Authentication) -> Self {
        Self(vec![BiscuitWebKey {
            public_key: auth.private_key.public(),
            key_id: auth.key_id,
            issuer: None,
            expires_at: Some((Utc::now() + TimeDelta::seconds(ONE_WEEK)).into()),
        }])
    }
}

pub async fn get_well_known_key_set<KS: Into<KeySetResponse>>(
    if_none_match: condreq::CondRetreiveHeader,
    State(keys): State<KS>,
) -> Result<impl IntoResponse, Error> {
    Ok(if_none_match.respond(keys.into())?)
}
