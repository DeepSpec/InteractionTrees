#!/bin/bash -e
#
# Purpose: Checks that files in _CoqProject actually exist
# 

## Usage: validate-coqproject <_CoqProject-filename>
## 
## 
## author: rab
## date: Wed Apr 8 15:24:03 EDT 2026


NUM_ARGS=1


if [[ "$#" -ne "$NUM_ARGS" ]]; then 
    >&2 echo "Usage: $0 <_CoqProject-filename>"
    exit 1
fi

tail -n +3 "$1" | while IFS= read -r f; do [[ -z "$f" ]] || [[ -e "$f" ]] || echo "$f"; done
