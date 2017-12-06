#!/bin/sh

set -eu

( cd "$(dirname "$0")"

  ( cd ocaml
    make
  )

  ( cd cakeml
    make
  )

  ( cd sml
    make
  )

  python benchmark.py
)
