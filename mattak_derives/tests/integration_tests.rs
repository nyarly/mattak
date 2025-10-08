use std::collections::HashMap;

use iri_string::{spec::IriSpec, template::UriTemplateStr};
use mattak_derives::{Context, Listable, Route, RouteTemplate};

use ::mattak::routing::Route;

#[allow(dead_code)] // I just want to check that it lists the field names
#[derive(Default, Listable, PartialEq, Eq, Hash)]
struct AListable {
    event_id: u16,
    user_id: String,
}

#[allow(dead_code)] // I just want to check that it lists the field names
#[derive(Clone, RouteTemplate, Default, PartialEq, Eq, Hash)]
#[template("/event_games/{event_id}/user/{user_id}")]
struct ARouteTemplate {}

#[derive(Context)]
struct AContext {
    event_id: u16,
    user_id: String,
}

#[derive(Context)]
struct EmptyContext {}

#[derive(Route, Clone, PartialEq, Eq)]
#[template("/event_games/{event_id}/user/{user_id}{?query*}")]
struct ARoute {
    event_id: u16,
    user_id: String,
    #[assoc]
    query: HashMap<String, String>,
}

#[test]
fn smoke_route() {
    use ::mattak::routing::Listable;
    use ::mattak::routing::RouteTemplate;

    let route = ARoute {
        event_id: 17,
        user_id: "mikey".to_string(),
        query: HashMap::new(),
    };
    assert_eq!(
        ARoute::route_template().route_template(),
        "/event_games/{event_id}/user/{user_id}{?query*}"
    );
    assert_eq!(ARoute::route_template().assoc_fields(), vec!["query"]);
    assert_eq!(
        route.list_vars(),
        vec![
            "event_id".to_string(),
            "user_id".to_string(),
            "query".to_string()
        ]
    );
}
#[test]
fn smoke_route_template() {
    use ::mattak::routing::RouteTemplate;

    let rt = ARouteTemplate::default();
    assert_eq!(
        rt.route_template(),
        "/event_games/{event_id}/user/{user_id}"
    );
}

#[test]
fn smoke_listable() {
    use ::mattak::routing::Listable;

    let alist = AListable::default();
    assert_eq!(
        alist.list_vars(),
        vec!["event_id".to_string(), "user_id".to_string()]
    );
}

#[test]
fn smoke_context() {
    let ctx = AContext {
        event_id: 17,
        user_id: "mikey".to_string(),
    };
    let template = UriTemplateStr::new("{event_id}xxx-{user_id}").expect("new");
    assert_eq!(
        template
            .expand::<IriSpec, _>(&ctx)
            .expect("expand")
            .to_string(),
        "17xxx-mikey".to_string()
    );

    let empty = EmptyContext {};
    let template = UriTemplateStr::new("xxx-").expect("new");
    assert_eq!(
        template
            .expand::<IriSpec, _>(&empty)
            .expect("expand")
            .to_string(),
        "xxx-".to_string()
    );
}
