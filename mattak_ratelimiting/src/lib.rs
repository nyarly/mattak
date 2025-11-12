/// This module provides a little convenience glue on tower_governor.
///
/// First, it provides a configurable KeyExtractor, so that the same binary
/// can be deployed behind a proxy or not with a little configuration.
///
/// Secondly, it provides a rate limiting setup function that automatically
/// spawns a thread to reap governor data.
///
/// Use this like:
/// ```ignore
/// use mattak::ratelimiting::{self, IpExtractor, GovernorConfigBuilder};
///
/// fn main() -> () {
///    let app = Router::new()
///        .route(&path("/"), get(sitemap))
///        .layer(ratelimiting::layer("api-root", extractor, GovernorConfigBuilder::default()
///            .per_millisecond(20)
///            .burst_size(60)
///        ));
/// }
/// ```
use std::{net::IpAddr, sync::Arc, time::Duration};

use governor::{clock::QuantaInstant, middleware::RateLimitingMiddleware};
use tower_governor::{
    key_extractor::{KeyExtractor, PeerIpKeyExtractor, SmartIpKeyExtractor},
    GovernorLayer,
};

pub use tower_governor::governor::GovernorConfigBuilder;

#[derive(Clone, Copy, Debug)]
pub enum IpExtractor {
    PeerIp(PeerIpKeyExtractor),
    RevProxy(SmartIpKeyExtractor),
}

impl IpExtractor {
    pub fn trust(yes: bool) -> Self {
        if yes {
            IpExtractor::RevProxy(SmartIpKeyExtractor {})
        } else {
            IpExtractor::PeerIp(PeerIpKeyExtractor {})
        }
    }
}

impl KeyExtractor for IpExtractor {
    type Key = IpAddr;

    fn name(&self) -> &'static str {
        match self {
            IpExtractor::PeerIp(ex) => ex.name(),
            IpExtractor::RevProxy(ex) => ex.name(),
        }
    }

    fn extract<T>(
        &self,
        req: &axum::http::Request<T>,
    ) -> Result<Self::Key, tower_governor::GovernorError> {
        match self {
            IpExtractor::PeerIp(ex) => ex.extract(req),
            IpExtractor::RevProxy(ex) => ex.extract(req),
        }
    }
}

pub fn layer<K, M>(
    name: &str,
    extractor: IpExtractor,
    cfg_builder: &mut GovernorConfigBuilder<K, M>,
) -> GovernorLayer<IpExtractor, M>
where
    K: KeyExtractor + Sync + std::fmt::Debug,
    M: RateLimitingMiddleware<QuantaInstant> + Send + Sync + 'static,
    <K as KeyExtractor>::Key: Send + Sync + 'static,
{
    let governor_conf = Arc::new(cfg_builder.key_extractor(extractor).finish().unwrap());

    tracing::debug!("{name} governor created: {governor_conf:?}");

    let governor_limiter = governor_conf.limiter().clone();
    let interval = Duration::from_secs(60);
    // a separate background task to clean up
    std::thread::spawn(move || loop {
        std::thread::sleep(interval);
        tracing::debug!("rate limiting storage size: {}", governor_limiter.len());
        governor_limiter.retain_recent();
    });

    GovernorLayer {
        config: governor_conf,
    }
}
