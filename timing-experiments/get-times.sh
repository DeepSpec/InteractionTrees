#!/bin/bash -e
#
# Purpose: Prints the sum total time of all measured commands in a .v.timing file.
# 

## Usage: ./get-times.sh <file.v.timing>. 
## 
## 
## author: rab
## date: Mon May 4 12:03:49 EDT 2026


NUM_ARGS=1


if [[ "$#" -ne "$NUM_ARGS" ]]; then 
    >&2 echo "Usage: $0 .v.timing file"
    exit 1
fi

grep -oe ".\.[0-9]* secs" "$1" | awk '{ sum += $1 } END { print sum }' 