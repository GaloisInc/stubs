#!/usr/bin/env python3
import sys

if len(sys.argv) == 1 or sys.argv[1] == "--help" or sys.argv[1] == "-h":
    print("Usage: generate_table.py <input .tbl file>")
    exit(1)

inpfile = sys.argv[1]

with open(inpfile, "r") as f:
    data = f.readlines()

failed = []

for line in data:
    dat = line.strip()
    if dat.startswith("#") or len(dat) == 0:
        continue
    try:
        parts = dat.split("\t")
        code = int(parts[0].strip())
        # Special case: filter out syscalls that use the x32 abi
        abi = parts[1].strip()
        if abi == "x32":
            continue
        syscall = parts[2].strip()
        print(f"    ({code}, \"{syscall}\"),")
    except:
        failed += ["-- failed: " + dat]

for fail in failed:
    print(fail)
