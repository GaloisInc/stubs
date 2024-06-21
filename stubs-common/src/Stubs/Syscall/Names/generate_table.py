#!/usr/bin/env python3
import argparse

parser = argparse.ArgumentParser(
                    prog="generate_table.py",
                    description="Generate a map of syscall names from a .tbl file")
parser.add_argument("filename",
                    help="The input .tbl file")
parser.add_argument("--exclude-abi",
                    help="Exclude syscalls that require the supplied ABI name",
                    default=[],
                    action="append")

args = parser.parse_args()

with open(args.filename, "r") as f:
    data = f.readlines()

failed = []

for line in data:
    dat = line.strip()
    if dat.startswith("#") or len(dat) == 0:
        continue
    try:
        parts = dat.split("\t")
        code = int(parts[0].strip())
        # Filter out syscalls that are in the list of excluded ABIs
        abi = parts[1].strip()
        if abi in args.exclude_abi:
            continue
        syscall = parts[2].strip()
        print(f"    ({code}, \"{syscall}\"),")
    except:
        failed += ["-- failed: " + dat]

for fail in failed:
    print(fail)
