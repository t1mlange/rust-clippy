#![allow(dead_code)]

fn unnecessary_fold_my() {
    let mut set = std::collections::HashSet::new();

    let mut vec = vec![1, 2, 3];
    let changed = vec
        .split_off(1)
        .iter()
        .map(|e| set.insert(e))
        .fold(false, |acc, x| acc || x);
}

fn main() {}
