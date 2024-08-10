use sweep_bptree::argument::SearchArgument;
use sweep_bptree::{argument::Argument, BPlusTreeMap};

/// An argumentation that counts even numbers
#[derive(Default, Clone, Debug)]
struct EvenCount(usize);

fn value_is_even(v: i64) -> bool {
    v % 2 == 0
}

impl Argument<i64> for EvenCount {
    fn from_leaf(keys: &[i64]) -> Self {
        // For leafs, we count all keys that are even
        Self(keys.iter().filter(|i| value_is_even(**i)).count())
    }

    fn from_inner(_keys: &[i64], arguments: &[Self]) -> Self {
        // For inner nodes, we aggregate all the EvenCount
        Self(arguments.iter().map(|a| a.0).sum::<usize>())
    }
}

/// This implementation enables get key by 'nth' even number. This effectively makes
/// `EvenCount` a secondary index
impl SearchArgument<i64> for EvenCount {
    /// offset of even number
    type Query = usize;

    fn locate_in_leaf(mut offset: usize, keys: &[i64]) -> Option<usize> {
        for (idx, key) in keys.iter().enumerate() {
            if value_is_even(*key) {
                if offset == 0 {
                    return Some(idx);
                }

                offset -= 1;
            }
        }

        None
    }

    fn locate_in_inner(offset: usize, _keys: &[i64], arguments: &[Self]) -> Option<(usize, usize)> {
        let mut relative_offset = offset;
        for (child_idx, argument) in arguments.iter().enumerate() {
            if argument.0 > relative_offset {
                return Some((child_idx, relative_offset));
            } else {
                relative_offset -= argument.0
            }
        }

        // not found
        None
    }
}

fn main() {
    // create a tree with the argument
    let mut tree = BPlusTreeMap::<i64, i64, EvenCount>::new();

    // insert 100000 numbers
    for i in 0..100000 {
        tree.insert(i, i);
    }

    // check we get the correct count
    assert_eq!(dbg!(tree.root_argument()).0, 50000);

    // then remove some keys
    for i in 0..100 {
        tree.remove(&(i * 2));
    }
    assert_eq!(dbg!(tree.root_argument()).0, 49900);

    // remove odd numbers should not affect the even count
    for i in 0..100 {
        tree.remove(&(i * 2 + 1));
    }
    assert_eq!(dbg!(tree.root_argument()).0, 49900);

    // able to get nth even value easily
    for i in 0..tree.root_argument().0 {
        let Some((k, _)) = tree.get_by_argument::<usize>(i) else {
            panic!("should got a value");
        };
        assert_eq!(k % 2, 0);
    }

    // offset = length - 1, get(length) should be None
    assert!(tree
        .get_by_argument::<usize>(tree.root_argument().0)
        .is_none());
}