#!/bin/bash -e
#
# Purpose: measures and sorts all compilation times
# 

## Usage:
## 
## 
## author: rab
## date: Mon May 4 12:19:14 EDT 2026


NUM_ARGS=0


if [[ "$#" -ne "$NUM_ARGS" ]]; then 
    >&2 echo "Usage: $0"
    exit 1
fi

BUILD_DIR=".."
TIMING_DIR="$BUILD_DIR/timing-experiments"

make -C "$BUILD_DIR" clean
make -C "$BUILD_DIR" TIMING=1

find "$BUILD_DIR" -name "*.v.timing" -exec "$TIMING_DIR/sum-times.sh" {} \; | sort -k2 -n
