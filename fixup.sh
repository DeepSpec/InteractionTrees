#!/bin/sh
awk '/\(theories/ { sub(/^/,";") } ; {print}' extra/dune > tmp && mv tmp extra/dune
