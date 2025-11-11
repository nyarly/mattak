pub mod check;
pub mod setup;

use super::{AuthContext, Authentication, Error};

pub fn setup<A: setup::GetPublicSource, S: Into<String>>(
    root: A,
    header: S,
) -> setup::AuthenticationSetup<A> {
    setup::AuthenticationSetup::new(root, header)
}

pub fn check<P: check::IntoPolicySnapshot>(policy: P) -> check::AuthenticationCheck {
    check::AuthenticationCheck::new(policy)
}
