# This script will *remove* unused imports
#
# Example usage
## Run from TypeTopology/source
## ./rm-imports.sh UF/Embeddings.lagda
## ./rm-imports.sh DomainTheory/Lifting/LiftingDcpo.lagda

# NB: This script will break your file in case of duplicate imports.
# This is not great, but at least it detects such duplicates as a side-effect :)
# I think manually fixing those is the easiest way to handle this (for now).

FILE=$1

# Get all line numbers that have 'open import ...'
IMPORTS=$(grep -n "open import" $FILE | cut -d ':' -f1)

# Get the cluster, e.g. 'UF' or 'DomainTheory/Lifting'
CLUSTER=$(dirname $FILE)

# And with '.' instead of '/'
CLUSTERMOD=$(echo $CLUSTER | sed 's/\//./')

# Get the (relative) module name
MODNAME=$(basename $FILE | sed 's/.lagda$//')

# Set up a temporary file for testing
TEMP="UnusedImportTesting"
FULLTEMP="${CLUSTER}/${TEMP}.lagda"

UNUSED=()

for i in $IMPORTS;
do
    sed "$i s/^/-- /" $FILE > $FULLTEMP # Comment out an import

    # Replace module name to match the temporary file
    OLDMOD="module ${CLUSTERMOD}.${MODNAME}"
    NEWMOD="module ${CLUSTERMOD}.${TEMP}"
    sed -i "s/${OLDMOD}/${NEWMOD}/" $FULLTEMP

    # Try to compile and save line numbers of unused imports
    agda $FULLTEMP > /dev/null &&
	{
	    UNUSED+=( $i )
	}
done
rm $FULLTEMP

# Remove unused imports from the file
sed -i "${UNUSED[*]/%/d;}" $FILE
