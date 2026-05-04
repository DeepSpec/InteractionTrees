#!/bin/bash -e
#
# Purpose:
# 

## Usage:
## 
## 
## author: rab
## date: Mon May 4 11:50:06 EDT 2026


NUM_ARGS=1


if [[ "$#" -ne "$NUM_ARGS" ]]; then 
    >&2 echo "Usage: $0 times-file"
    exit 1
fi

awk '{ sum += $1 } END { print sum }' "$1" 