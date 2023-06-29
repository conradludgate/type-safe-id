use libtest_mimic::{Arguments, Failed};
use type_safe_id::Error;

fn main() {
    let mut tests = vec![];
    invalid_prefix::tests(&mut tests);
    invalid_suffix::tests(&mut tests);
    special_values::tests(&mut tests);

    let args = Arguments::from_args();
    libtest_mimic::run(&args, tests).exit_if_failed();
}

fn expect_err(x: Result<(), Error>) -> Result<(), Failed> {
    match x {
        Ok(()) => Err("expected a failure".into()),
        Err(_) => Ok(()),
    }
}

mod invalid_prefix {
    use libtest_mimic::Trial;
    use type_safe_id::{DynamicType, Error, TypeSafeId};

    use crate::expect_err;

    pub fn tests(t: &mut Vec<Trial>) {
        add_test(t, "caps", "PREFIX");
        add_test(t, "numeric", "12323");
        add_test(t, "symbols", "pre.fix");
        add_test(t, "spaces", "  ");
        add_test(
            t,
            "long",
            "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz",
        );
    }

    fn add_test(t: &mut Vec<Trial>, name: &'static str, input: &'static str) {
        t.push(Trial::test(
            "invalid_prefix.".to_owned() + name,
            move || expect_err(test(input)),
        ))
    }

    fn test(input: &str) -> Result<(), Error> {
        TypeSafeId::new_with_type(DynamicType::new(input))?;
        Ok(())
    }
}
mod invalid_suffix {
    use std::str::FromStr;

    use libtest_mimic::Trial;
    use type_safe_id::{DynamicType, Error, TypeSafeId};

    use crate::expect_err;

    pub fn tests(t: &mut Vec<Trial>) {
        add_test(t, "spaces", "  ");
        add_test(t, "short", "01234");
        add_test(
            t,
            "long",
            "012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789",
        );
        // we implement the parsing of capitcal letters
        // add_test(t, "caps", "00041061050R3GG28A1C60T3GF");

        add_test(t, "hyphens", "00041061050-3gg28a1-60t3gf");

        // we implement the parsing of ambiguous characters
        // add_test(t, "crockford_ambiguous", "ooo41o61o5or3gg28a1c6ot3gi");

        add_test(t, "symbols", "00041061050.3gg28a1_60t3gf");
        add_test(t, "wrong_alphabet", "ooooooiiiiiiuuuuuuulllllll");
    }

    fn add_test(t: &mut Vec<Trial>, name: &'static str, input: &'static str) {
        t.push(Trial::test(
            "invalid_suffix.".to_owned() + name,
            move || expect_err(test(input)),
        ))
    }

    fn test(input: &str) -> Result<(), Error> {
        let id = format!("prefix_{input}");
        TypeSafeId::<DynamicType>::from_str(&id)?;
        Ok(())
    }
}

mod special_values {
    use libtest_mimic::Trial;
    use type_safe_id::{DynamicType, Error, TypeSafeId};
    use uuid::{uuid, Uuid};

    pub fn tests(t: &mut Vec<Trial>) {
        add_test(
            t,
            "nil",
            "00000000000000000000000000",
            uuid!("00000000-0000-0000-0000-000000000000"),
        );
        add_test(
            t,
            "one",
            "00000000000000000000000001",
            uuid!("00000000-0000-0000-0000-000000000001"),
        );
        add_test(
            t,
            "ten",
            "0000000000000000000000000a",
            uuid!("00000000-0000-0000-0000-00000000000a"),
        );
        add_test(
            t,
            "sixteen",
            "0000000000000000000000000g",
            uuid!("00000000-0000-0000-0000-000000000010"),
        );
        add_test(
            t,
            "thirty-two",
            "00000000000000000000000010",
            uuid!("00000000-0000-0000-0000-000000000020"),
        );
    }

    fn add_test(t: &mut Vec<Trial>, name: &'static str, id: &'static str, uuid: Uuid) {
        t.push(Trial::test(
            "special_values.".to_owned() + name,
            move || test(id, uuid).map_err(|e| e.to_string().into()),
        ))
    }

    fn test(id: &str, uuid: Uuid) -> Result<(), Error> {
        let id = format!("prefix_{id}");
        let tid: TypeSafeId<DynamicType> = id.parse()?;
        assert_eq!(tid.uuid(), uuid);

        let tid = TypeSafeId::from_type_and_uuid(DynamicType::new("prefix"), uuid)?;
        assert_eq!(tid.to_string(), id);

        Ok(())
    }
}
