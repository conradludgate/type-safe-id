use std::{io::Write, str::FromStr};

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use type_safe_id::{StaticType, TypeSafeId};
use uuid::{uuid, Uuid};

#[derive(Default)]
struct Index;

impl StaticType for Index {
    const TYPE: &'static str = "index";
}

type IndexId = TypeSafeId<Index>;

const UUID: Uuid = uuid!("0188bac7-4afa-78aa-bc3b-bd1eef28d881");

fn format() -> [u8; 32] {
    let id = IndexId::from_uuid(black_box(UUID)).unwrap();

    let mut out = [0u8; 32];
    write!(out.as_mut(), "{}", id).unwrap();
    out
}

fn parse() -> IndexId {
    IndexId::from_str(black_box("index_01h2xcejqtf2nbrexx3vqjhp41")).unwrap()
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("format", |b| b.iter(format));
    c.bench_function("parse", |b| b.iter(parse));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
