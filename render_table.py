from collections import defaultdict


def parse_and_render():
    with open("benchmark_data") as f:
        lines = f.readlines()

    # key_type, name, size
    benchmarks_point = {}
    benchmarks_string = {}

    for line in lines[2:]:
        components = line.split()
        name = components[0]
        time = components[2]

        name_components = name.split("/")
        if len(name_components) != 4:
            continue

        bench_name = name_components[0]
        bench_key_type = name_components[1]
        tree_type = name_components[2]
        bench_size = int(name_components[3])

        time_components = time.split("±")

        if "µs" in time:
            base = 1000
        elif "ns" in time:
            base = 1
        elif "ms" in time:
            base = 1000 * 1000
        elif "ps" in time:
            base = 1 / 1000
        elif "s" in time:
            base = 1000 * 1000 * 1000
        else:
            print(f"unknown time unit {time}")
            continue

        time_ns = float(time_components[0]) * base

        time_obj = {
            "time_ns": time_ns,
            "time_disp": time,
        }

        if bench_key_type == "Point":
            cur_benchmarks = benchmarks_point
        elif bench_key_type == "String":
            cur_benchmarks = benchmarks_string
        else:
            continue

        if bench_name not in cur_benchmarks:
            cur_benchmarks[bench_name] = {bench_size: {tree_type: time_obj}}
        elif bench_size not in cur_benchmarks[bench_name]:
            cur_benchmarks[bench_name][bench_size] = {tree_type: time_obj}
        else:
            cur_benchmarks[bench_name][bench_size][tree_type] = time_obj

    print("## Point benchmark")
    print_benchmark(benchmarks_point)

    print("## String benchmark")
    print_benchmark(benchmarks_string)


def print_benchmark(benchmarks):
    # render benchmarks as markdown table
    print("| name | size | btree | bptree | speed factor |")
    print("| - | - | - | - | - |")

    benchmarks_with_bulk = defaultdict(defaultdict)

    for bench_name in benchmarks:
        for bench_size in benchmarks[bench_name]:
            if len(benchmarks[bench_name][bench_size]) == 3:
                # print in a new table
                benchmarks_with_bulk[bench_name][bench_size] = benchmarks[bench_name][
                    bench_size
                ]
                continue

            if "btree" not in benchmarks[bench_name][bench_size]:
                bptree_time = benchmarks[bench_name][bench_size]["bptree"]["time_ns"]
                bptree_time_disp = benchmarks[bench_name][bench_size]["bptree"][
                    "time_disp"
                ]

                print(f"| {bench_name} | {bench_size} | - | {bptree_time_disp} | - |")
            else:
                btree_time = benchmarks[bench_name][bench_size]["btree"]["time_ns"]
                btree_time_disp = benchmarks[bench_name][bench_size]["btree"][
                    "time_disp"
                ]

                bptree_time = benchmarks[bench_name][bench_size]["bptree"]["time_ns"]
                bptree_time_disp = benchmarks[bench_name][bench_size]["bptree"][
                    "time_disp"
                ]

                speed_factor = btree_time / bptree_time

                print(
                    f"| {bench_name} | {bench_size} | {btree_time_disp} | {bptree_time_disp} | {speed_factor:.2f} |"
                )

    print("| name | size | type | time |")
    print("| - | - | - | - |")
    last_bench_name = None
    for bench_name in benchmarks_with_bulk:
        for bench_size in benchmarks_with_bulk[bench_name]:
            benchmarks = list(benchmarks_with_bulk[bench_name][bench_size].items())
            benchmarks.sort()

            for bench_type, time in benchmarks:
                name = None
                if (bench_name, bench_size) == last_bench_name:
                    name = ""
                    size = ""
                else:
                    last_bench_name = (bench_name, bench_size)
                    name = bench_name
                    size = bench_size

                print(f"| {name} | {size} | {bench_type} | {time['time_disp']}")


if __name__ == "__main__":
    parse_and_render()
