use axum::{extract::Request, http::uri::Authority};
use biscuit_auth::{BiscuitWebKey, RootKeyProvider};
use bounded_join_set::JoinSet;
use hyper::{header, HeaderMap};
use reqwest::Client;
use serde::Deserialize;
use tracing::{debug, trace};

use crate::middleware::setup::{GetPublic, GetPublicSource};

use super::Error;

#[derive(Clone, Debug, Deserialize)]
pub struct AuthorityMapping {
    pub url: String,
    pub keyset: String,
}
impl<U: Into<String>, K: Into<String>> From<(U, K)> for AuthorityMapping {
    fn from((u, k): (U, K)) -> Self {
        Self {
            url: u.into(),
            keyset: k.into(),
        }
    }
}

#[derive(Debug)]
pub struct AuthorityMap(Vec<AuthorityMapping>);

impl<LM, M> From<LM> for AuthorityMap
where
    LM: IntoIterator<Item = M>,
    AuthorityMapping: From<M>,
{
    fn from(pairs: LM) -> Self {
        AuthorityMap(
            pairs
                .into_iter()
                .map(|m| AuthorityMapping::from(m))
                .collect(),
        )
    }
}

const CONCURRENT_KEY_REQUESTS: usize = 10;
impl AuthorityMap {
    pub async fn fetch_keys(&self, client: Client) -> Result<KeyMap, Error> {
        // each authmap,
        let mut fetchwait = JoinSet::new(CONCURRENT_KEY_REQUESTS);
        for pair in &self.0 {
            fetchwait.spawn(pair.clone().fetch_key(client.clone()));
        }

        let mut webkeys = vec![];
        while let Some(kmr) = fetchwait.join_next().await {
            webkeys.push(kmr.expect("no JoinError")?)
        }

        Ok(KeyMap(webkeys))
    }
}

impl AuthorityMapping {
    async fn fetch_key(self, client: Client) -> Result<KeyMapping, Error> {
        let url = format!("https://{}/.well-known/biscuit-web-keys", self.keyset);

        let rz = client.get(&url).send().await?;
        match rz.error_for_status() {
            Ok(rz) => {
                let keys = serde_json::from_str(&(rz.text().await?))?;
                Ok(KeyMapping {
                    url: self.url.clone(),
                    keys,
                })
            }
            Err(e) => return Err(Error::KeysetFetch(e)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct KeyMapping {
    pub url: String,
    pub keys: Vec<BiscuitWebKey>,
}
#[derive(Clone, Debug)]
pub struct KeyMap(Vec<KeyMapping>);

impl GetPublicSource for KeyMap {
    type Public = KeyMap;

    fn make_get_public(&self) -> Self::Public {
        self.clone()
    }
}

const X_FORWARDED_HOST_HEADER_KEY: &str = "X-Forwarded-Host";
fn uri_authority(req: &Request) -> Option<String> {
    if let Some(host) = parse_forwarded(&req.headers()) {
        return Some(host.to_owned());
    }

    if let Some(host) = req
        .headers()
        .get(X_FORWARDED_HOST_HEADER_KEY)
        .and_then(|host| host.to_str().ok())
    {
        return Some(host.to_owned());
    }

    if let Some(host) = req
        .headers()
        .get(header::HOST)
        .and_then(|host| host.to_str().ok())
    {
        return Some(host.to_owned());
    }

    if let Some(authority) = req.uri().authority() {
        return Some(parse_authority(authority).to_owned());
    }

    None
}

fn parse_forwarded(headers: &HeaderMap) -> Option<&str> {
    // if there are multiple `Forwarded` `HeaderMap::get` will return the first one
    let forwarded_values = headers.get(header::FORWARDED)?.to_str().ok()?;

    // get the first set of values
    let first_value = forwarded_values.split(',').nth(0)?;

    // find the value of the `host` field
    first_value.split(';').find_map(|pair| {
        let (key, value) = pair.split_once('=')?;
        key.trim()
            .eq_ignore_ascii_case("host")
            .then(|| value.trim().trim_matches('"'))
    })
}

fn parse_authority(auth: &Authority) -> &str {
    auth.as_str()
        .rsplit('@')
        .next()
        .expect("split always has at least 1 item")
}

impl GetPublic for KeyMap {
    type PublicKey = WebKeyProvider;

    fn get_public(&self, req: &Request) -> Result<Self::PublicKey, Error> {
        let uri_auth = uri_authority(req).ok_or(Error::URIAuthorityMissing)?;
        debug!("Getting PublicKey for URI: {uri_auth:?}");
        match self.0.iter().find(|km| km.url == uri_auth) {
            Some(km) => Ok(WebKeyProvider(km.keys.clone())),
            None => Err(Error::NoKeysetForAuthority(uri_auth)),
        }
    }
}

pub struct WebKeyProvider(Vec<BiscuitWebKey>);

impl RootKeyProvider for WebKeyProvider {
    fn choose(
        &self,
        key_id: Option<u32>,
    ) -> Result<biscuit_auth::PublicKey, biscuit_auth::error::Format> {
        trace!("Getting pubkey {key_id:?}");
        match self.0.get(key_id.unwrap_or(0) as usize) {
            Some(bwk) => Ok(bwk.public_key),
            None => Err(biscuit_auth::error::Format::UnknownPublicKey),
        }
    }
}
