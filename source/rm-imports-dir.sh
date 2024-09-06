#!/usr/bin/env bash
set -Eeuo pipefail

# This script will *remove* unused imports from all files in directory
#
# Example usage
## Run from TypeTopology/source
## ./rm-imports-dir.sh UF/

# WARNING: This script will break your file in case of duplicate imports.
# This is not great, but at least it detects such duplicates as a side-effect :)
# I think manually fixing those is the easiest way to handle this (for now).

# WARNING: This script does *not* recurse in multi-level directories (yet),
# e.g. if you want to remove unused imports in TWA/Thesis/Chapter6/ you have to
# run ./rm-imports-dir.sh TWA/Thesis/Chapter6/

DIR=$1

for i in ${DIR}*.lagda
do
    echo $i
    ./rm-imports.sh $i
    echo "Done with $(basename ${i})"
done
