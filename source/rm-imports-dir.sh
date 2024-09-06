# This script will *remove* unused imports from all files in directory
#
# Example usage
## Run from TypeTopology/source
## ./rm-imports-dir.sh UF/

# WARNING: This script will break your file in case of duplicate imports.
# This is not great, but at least it detects such duplicates as a side-effect :)
# I think manually fixing those is the easiest way to handle this (for now).

# WARNING: This script does *not* work with multi-level directories (yet),
# e.g. TWA/ and DomainTheory/

DIR=$1

for i in $(ls $DIR);
do
    ./rm-imports.sh "${DIR}${i}"
    echo "Done with ${i}"
done
