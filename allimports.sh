#!/usr/bin/env bash
set -Eeo pipefail

git ls-files '*agda' -z | while read -rd $'' file; do
    echo "Processing: $file"
    ../imports.sh -r "$file"
done
