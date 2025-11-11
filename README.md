# Mattak

This is a suite of tools meant to compliment Axum
and support a semantic approach to web application development.

## What's in a name

Apps written using Mattak can be referred to
as "Axum-Mattak" applications.
The thinking is that semantic web applications
are "axiomatically" more correct
(whatever that means.)

## What's in the box

Mattak provides:

### hypermedia

A module to describe API affordances,
which encapsulate not only the resource locator,
either as a simple URI or a URITemplate,
but also the HTTP method to use,
and an RDF type to hint about the meaning of the affordance.

### biscuits

A wrapper around the biscuit-auth crate
to provide a Layer to allow easy use of biscuits
for authentication
in Axum.

### cachecontrol

A layer to add cache control headers to responses;
you provide the TTL, and it works out the rest.

### condreq

Etags and conditional requests,
which can greatly optimize HTTP responses -
there's no response faster than no response.

### ratelimiting

A thin wrapper over the tower-governor crate,
that makes it easy to set up rate limits.

### routing

Bidirectional routing with URITemplates.
Define routes with parameters and a template,
and easily add them to Axum routes,
as well as render them in responses as full affordances
or mere URIs.

## The mattak_derives crate

You'll find derive macros for RouteTemplates and Locators here,
which will let you define one struct per route,
and get all the `routing` goodness with a `#[derive(...)]` attribute.

## License

The
[license](./LICENSE)
for this project is
the MPL-2.0 license.
In addition,
please **let me know** that you're using it.
The long and the short of it
is that I just want to know if what I've been doing
is useful to someone else.
