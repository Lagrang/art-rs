use art::keys::ByteString;
use art::Art;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::SliceRandom;
use rand::{thread_rng, Rng};
use std::collections::HashSet;
use std::time::Instant;

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("modification");
    group.bench_function("insert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.insert(ByteString::from(key), key);
            key += 1;
        })
    });

    group.bench_function("upsert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.upsert(ByteString::from(key), key);
            key += 1;
        })
    });

    group.bench_function("remove", |b| {
        let mut tree = Art::new();
        b.iter_custom(|iters| {
            for i in 0..iters {
                tree.insert(ByteString::from(i), i);
            }
            let start = Instant::now();
            for i in 0..iters {
                tree.remove(&ByteString::from(i));
            }
            start.elapsed()
        })
    });
    group.finish();

    let mut group = c.benchmark_group("access");
    group.bench_function("get", |b| {
        let mut tree = Art::new();
        b.iter_custom(|iters| {
            for i in 0..iters {
                tree.insert(ByteString::from(i), i);
            }
            let start = Instant::now();
            for i in 0..iters {
                tree.get(&ByteString::from(i));
            }
            start.elapsed()
        })
    });

    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("iter_u64", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(ByteString::from(i), i);
            }
            b.iter(|| {
                tree.iter().count();
            })
        });
    }

    group.bench_function("iter_small_sized_str", |b| {
        let mut tree = Art::new();
        for i in gen_keys(2, 2, 2) {
            tree.insert(ByteString::new(i.as_bytes()), i);
        }
        b.iter(|| {
            tree.iter().count();
        })
    });

    group.bench_function("iter_mid_sized_str", |b| {
        let mut tree = Art::new();
        for i in gen_keys(4, 4, 3) {
            tree.insert(ByteString::new(i.as_bytes()), i);
        }
        b.iter(|| {
            tree.iter().count();
        })
    });

    group.bench_function("iter_large_sized_str", |b| {
        let mut tree = Art::new();
        for i in gen_keys(8, 6, 6) {
            tree.insert(ByteString::new(i.as_bytes()), i);
        }
        b.iter(|| {
            tree.iter().count();
        })
    });
    group.finish();
}

fn gen_keys(l1_prefix: usize, l2_prefix: usize, suffix: usize) -> Vec<String> {
    let mut keys = HashSet::new();
    let chars: Vec<char> = ('a'..='z').collect();
    for i in 0..chars.len() {
        let level1_prefix = chars[i].to_string().repeat(l1_prefix);
        for i in 0..chars.len() {
            let level2_prefix = chars[i].to_string().repeat(l2_prefix);
            let key_prefix = level1_prefix.clone() + &level2_prefix;
            for _ in 0..=u8::MAX {
                let suffix: String = (0..suffix)
                    .map(|_| chars[thread_rng().gen_range(0..chars.len())])
                    .collect();
                let string = key_prefix.clone() + &suffix;
                keys.insert(string.clone());
            }
        }
    }

    let mut res: Vec<String> = keys.drain().collect();
    res.shuffle(&mut thread_rng());
    res
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
