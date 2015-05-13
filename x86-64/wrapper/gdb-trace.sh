#!/bin/bash
python input.py | gdb a.out | sed 's/^(gdb).*//g' | gzip > gdb-trace.txt.gz
