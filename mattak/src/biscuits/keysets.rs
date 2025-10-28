use biscuit_auth::{BiscuitWebKey, RootKeyProvider};
use bounded_join_set::JoinSet;
use reqwest::Client;

use crate::biscuits::middleware::setup::{GetPublic, GetPublicSource};

use super::Error;

#[derive(Clone)]
pub struct AuthorityMapping {
    pub url: String,
    pub keyset: String,
}
pub struct AuthorityMap(Vec<AuthorityMapping>);

#[derive(Clone)]
pub struct KeyMapping {
    pub url: String,
    pub keys: Vec<BiscuitWebKey>,
}
pub struct KeyMap(Vec<KeyMapping>);

impl GetPublicSource for KeyMap {
    type Public = KeyMap;

    fn make_get_public(&self) -> Self::Public {
        KeyMap(self.0.clone())
    }
}

impl GetPublic for KeyMap {
    type PublicKey = WebKeyProvider;

    fn get_public(&self, req: &axum::extract::Request) -> Result<Self::PublicKey, Error> {
        let uri_auth = if let Some(auth) = req.uri().authority() {
            auth.to_string()
        } else {
            return Err(Error::URIAuthorityMissing);
        };
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
        match self.0.get(key_id.unwrap_or(0) as usize) {
            Some(bwk) => Ok(bwk.public_key),
            None => Err(biscuit_auth::error::Format::UnknownPublicKey),
        }
    }
}

const CONCURRENT_KEY_REQUESTS: usize = 10;

impl AuthorityMap {
    pub async fn fetch_keys(&self) -> Result<KeyMap, Error> {
        let client = Client::builder().use_rustls_tls().build()?;
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
