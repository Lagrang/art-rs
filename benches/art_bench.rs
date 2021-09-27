use art_tree::Art;
use art_tree::ByteString;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::prelude::SliceRandom;
use rand::{thread_rng, Rng};
use std::collections::HashSet;
use std::time::Instant;

pub fn modifications(c: &mut Criterion) {
    let mut group = c.benchmark_group("modification");
    group.throughput(Throughput::Elements(1));
    group.bench_function("seq_insert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.insert(ByteString::from(key), key);
            key += 1;
        })
    });

    group.bench_function("rand_insert", |b| {
        let mut tree = Art::new();
        let mut rng = thread_rng();
        let keys = gen_keys(3, 2, 3);
        b.iter(|| {
            let key = &keys[rng.gen_range(0..keys.len())];
            tree.insert(ByteString::new(key.as_bytes()), key.clone());
        })
    });

    group.bench_function("seq_upsert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.upsert(ByteString::from(key), key);
            key += 1;
        })
    });

    group.bench_function("rand_upsert", |b| {
        let mut tree = Art::new();
        let mut rng = thread_rng();
        let keys = gen_keys(3, 2, 3);
        b.iter(|| {
            let key = &keys[rng.gen_range(0..keys.len())];
            tree.upsert(ByteString::new(key.as_bytes()), key.clone());
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
}

pub fn access(c: &mut Criterion) {
    let mut group = c.benchmark_group("access");
    group.throughput(Throughput::Elements(1));
    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("rand_get", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(ByteString::from(i), i);
            }
            let mut rng = thread_rng();
            b.iter(|| {
                let key = rng.gen_range(0..*size);
                tree.get(&ByteString::from(key));
            })
        });
    }

    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("seq_get", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(ByteString::from(i), i);
            }
            let mut key = 0u64;
            b.iter(|| {
                tree.get(&ByteString::from(key));
                key += 1;
            })
        });
    }
    group.finish();
}

pub fn iter(c: &mut Criterion) {
    let mut group = c.benchmark_group("iteration");
    group.throughput(Throughput::Elements(1));
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

criterion_group!(mods, modifications);
criterion_group!(gets, access);
criterion_group!(iters, iter);
criterion_main!(mods, gets, iters);
