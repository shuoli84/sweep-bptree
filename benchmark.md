# Intro

Migrated Benchmark data into this doc.

## Benchmark

Data collected on macbook pro m1. The Key type is `Point { x: f64, y: f64}`

```bash
# try it
cargo bench

# generate the table
critcmp > benchmark_data 
python3 render_table.py

```

### Advantages

* bptree ordered_get is way faster than random_get, also way faster(1.2ms vs 4.7ms) than btree's ordered_get.
* bptree iter's faster than btree(86us vs 220us).
* bptree bulk_insert is the most fast way to build a tree(938µs vs normal bptree insert 2ms vs btree insert 8ms).
* For unsorted data, sort then bulk_load is the fastest(9ms vs normal bptree 18.ms vs normal btree insert 13.9ms).

### Disadvantages

* bptree random_get is slower(13ms vs 9ms) than btree.
* random_remove(17ms vs 12ms).

### Point benchmark data

Point is a struct with 2 f64 fields, with very cheap clone and cmp cost.

| name | size | btree | bptree | speed factor |
| - | - | - | - | - |
| clone | 1000 | 12.3±0.08µs | 5.6±0.21µs | 2.20 |
| clone | 10000 | 133.2±1.60µs | 60.3±0.53µs | 2.21 |
| clone | 100000 | 2.5±0.03ms | 1073.9±93.60µs | 2.33 |
| cursor | 1000 | - | 4.6±0.03µs | - |
| cursor | 10000 | - | 46.8±0.18µs | - |
| cursor | 100000 | - | 470.0±2.39µs | - |
| drop | 1000 | 7.9±0.10µs | 1093.1±17.60ns | 7.23 |
| drop | 10000 | 84.7±1.08µs | 12.1±0.32µs | 7.00 |
| drop | 100000 | 1799.9±23.56µs | 295.2±11.19µs | 6.10 |
| into_iter | 1000 | 8.1±0.58µs | 1134.7±13.43ns | 7.14 |
| into_iter | 10000 | 84.9±0.71µs | 12.1±0.10µs | 7.02 |
| into_iter | 100000 | 1825.7±79.25µs | 254.9±7.95µs | 7.16 |
| iter | 1000 | 844.2±8.44ns | 416.8±5.02ns | 2.03 |
| iter | 10000 | 11.9±0.29µs | 4.7±0.03µs | 2.53 |
| iter | 100000 | 216.5±0.80µs | 54.8±0.13µs | 3.95 |
| ordered_get | 1000 | 26.8±1.08µs | 10.0±0.10µs | 2.68 |
| ordered_get | 10000 | 418.7±2.83µs | 107.5±0.53µs | 3.89 |
| ordered_get | 100000 | 4.7±0.01ms | 1126.8±4.21µs | 4.17 |
| ordered_remove | 1000 | 32.5±0.84µs | 84.1±0.80µs | 0.39 |
| ordered_remove | 10000 | 344.9±3.55µs | 873.5±0.72µs | 0.39 |
| ordered_remove | 100000 | 4.5±0.47ms | 9.6±0.20ms | 0.47 |
| random_get | 1000 | 25.1±1.45µs | 18.6±1.77µs | 1.35 |
| random_get | 10000 | 664.3±50.24µs | 956.8±6.58µs | 0.69 |
| random_get | 100000 | 9.3±0.01ms | 13.4±0.02ms | 0.69 |
| random_remove | 1000 | 61.6±4.01µs | 89.6±1.39µs | 0.69 |
| random_remove | 10000 | 912.4±0.84µs | 1411.6±2.83µs | 0.65 |
| random_remove | 100000 | 12.8±0.90ms | 18.7±0.04ms | 0.68 |

#### Point benchmark data with bulk_load

| name | size | type | time |
| - | - | - | - |
| ordered_insert | 1000 | bptree | 26.9±0.23µs
|  |  | bptree_bulk | 6.1±0.08µs
|  |  | btree | 50.8±1.80µs
| ordered_insert | 10000 | bptree | 358.3±10.02µs
|  |  | bptree_bulk | 66.0±0.61µs
|  |  | btree | 778.5±13.34µs
| ordered_insert | 100000 | bptree | 4.7±0.02ms
|  |  | bptree_bulk | 916.1±20.79µs
|  |  | btree | 8.8±0.04ms
| random_insert | 1000 | bptree | 81.3±1.15µs
|  |  | bptree_sort_load | 43.2±0.29µs
|  |  | btree | 55.5±1.36µs
| random_insert | 10000 | bptree | 1381.6±16.30µs
|  |  | bptree_sort_load | 698.6±7.84µs
|  |  | btree | 962.6±9.49µs
| random_insert | 100000 | bptree | 18.3±0.06ms
|  |  | bptree_sort_load | 9.5±0.01ms
|  |  | btree | 14.0±0.08ms

### String benchmark data

String type is relative heavy for clone, cmp and drop.

For clone and drop, bptree actually needs to do more work, but still faster.
For random_get and random_remove, bptree still slower, but the margin is smaller.

| name | size | btree | bptree | speed factor |
| - | - | - | - | - |
| clone | 1000 | 34.4±0.41µs | 27.6±0.55µs | 1.25 |
| clone | 10000 | 431.6±10.88µs | 307.0±8.21µs | 1.41 |
| clone | 100000 | 7.2±0.07ms | 5.2±0.02ms | 1.38 |
| cursor | 1000 | - | 30.2±0.16µs | - |
| cursor | 10000 | - | 306.2±0.89µs | - |
| cursor | 100000 | - | 3.5±0.64ms | - |
| drop | 1000 | 21.5±1.03µs | 14.7±0.06µs | 1.46 |
| drop | 10000 | 234.5±2.83µs | 146.6±2.22µs | 1.60 |
| drop | 100000 | 4.5±0.06ms | 2.3±0.02ms | 1.96 |
| into_iter | 1000 | 20.5±0.19µs | 13.2±0.82µs | 1.55 |
| into_iter | 10000 | 235.2±7.75µs | 147.2±1.07µs | 1.60 |
| into_iter | 100000 | 4.4±0.07ms | 2.3±0.02ms | 1.91 |
| iter | 1000 | 848.8±6.17ns | 405.1±5.59ns | 2.10 |
| iter | 10000 | 18.3±0.42µs | 5.1±0.03µs | 3.59 |
| iter | 100000 | 235.7±6.59µs | 55.1±0.40µs | 4.28 |
| ordered_get | 1000 | 221.5±2.02µs | 213.1±1.81µs | 1.04 |
| ordered_get | 10000 | 2.4±0.00ms | 2.1±0.02ms | 1.14 |
| ordered_get | 100000 | 25.8±0.07ms | 22.2±0.02ms | 1.16 |
| ordered_remove | 1000 | 231.5±2.46µs | 311.2±4.56µs | 0.74 |
| ordered_remove | 10000 | 2.4±0.00ms | 3.2±0.02ms | 0.75 |
| ordered_remove | 100000 | 26.2±0.67ms | 34.5±0.92ms | 0.76 |
| random_get | 1000 | 63.8±0.84µs | 71.2±1.82µs | 0.90 |
| random_get | 10000 | 1156.2±5.75µs | 1464.0±11.94µs | 0.79 |
| random_get | 100000 | 23.0±0.68ms | 26.0±0.32ms | 0.88 |
| random_remove | 1000 | 126.1±0.93µs | 152.2±2.01µs | 0.83 |
| random_remove | 10000 | 1764.6±30.54µs | 2.2±0.00ms | 0.80 |
| random_remove | 100000 | 30.7±0.11ms | 37.2±0.19ms | 0.83 |

#### String benchmark data with bulk_load

| name | size | type | time |
| - | - | - | - |
| ordered_insert | 1000 | bptree | 220.3±2.30µs
|  |  | bptree_bulk | 173.1±2.14µs
|  |  | btree | 268.3±11.22µs
| ordered_insert | 10000 | bptree | 2.4±0.07ms
|  |  | bptree_bulk | 1736.9±16.15µs
|  |  | btree | 3.0±0.00ms
| ordered_insert | 100000 | bptree | 25.5±0.11ms
|  |  | bptree_bulk | 17.8±0.13ms
|  |  | btree | 33.0±0.11ms
| random_insert | 1000 | bptree | 135.6±1.39µs
|  |  | bptree_sort_load | 75.4±1.55µs
|  |  | btree | 122.8±1.82µs
| random_insert | 10000 | bptree | 2.2±0.00ms
|  |  | bptree_sort_load | 1449.7±14.30µs
|  |  | btree | 1807.4±18.02µs
| random_insert | 100000 | bptree | 36.5±0.53ms
|  |  | bptree_sort_load | 20.8±0.46ms
|  |  | btree | 30.9±0.82ms
