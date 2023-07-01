use std::str::FromStr;

use libtest_mimic::{Arguments, Trial};
use serde::Deserialize;
use type_safe_id::{DynamicType, TypeSafeId};
use uuid::Uuid;

#[derive(Deserialize)]
struct Valid {
    name: String,
    typeid: String,
    prefix: String,
    uuid: Uuid,
}

#[derive(Deserialize)]
struct Invalid {
    name: String,
    typeid: String,
    description: String,
}

type Id = TypeSafeId<DynamicType>;

fn main() {
    let mut tests = vec![];

    let valid: Vec<Valid> = serde_yaml::from_str(include_str!("spec/valid.yml")).unwrap();
    let invalid: Vec<Invalid> = serde_yaml::from_str(include_str!("spec/invalid.yml")).unwrap();

    for test in valid {
        tests.push(Trial::test(format!("valid::{}", test.name), move || {
            let id = match Id::from_str(&test.typeid) {
                Ok(id) => id,
                Err(e) => return Err(e.to_string().into()),
            };
            if id.uuid() != test.uuid {
                return Err(format!("expected {:?}, got {:?}", test.uuid, id.uuid()).into());
            }
            if id.type_prefix() != test.prefix {
                return Err(
                    format!("expected {:?}, got {:?}", test.prefix, id.type_prefix()).into(),
                );
            }

            if id.to_string() == test.typeid {
                Ok(())
            } else {
                Err(format!("expected {:?}, got {:?}", test.typeid, id.to_string()).into())
            }
        }))
    }

    for test in invalid {
        tests.push(Trial::test(
            format!("invalid::{}", test.name),
            move || match Id::from_str(&test.typeid) {
                Ok(_) => Err(test.description.into()),
                Err(_) => Ok(()),
            },
        ))
    }

    let args = Arguments::from_args();
    libtest_mimic::run(&args, tests).exit_if_failed();
}
