# This script will list unused imports
#
# Example usage
## Run from TypeTopology/source
## ./imports.sh UF/Embeddings.lagda
## ./imports.sh DomainTheory/Lifting/LiftingDcpo.lagda

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

for i in $IMPORTS;
do
    sed "$i s/^/-- /" $FILE > $FULLTEMP # Comment out an import

    # Replace module name to match the temporary file
    OLDMOD="module ${CLUSTERMOD}.${MODNAME}"
    NEWMOD="module ${CLUSTERMOD}.${TEMP}"
    sed -i "s/${OLDMOD}/${NEWMOD}/" $FULLTEMP

    # Try to compile and report back
    agda $FULLTEMP > /dev/null &&
	{
	    IMPORT=$(sed -n "${i}p" $FILE | cut -d ' ' -f3)
	    echo "Importing $IMPORT was not necessary"
	}
done
rm $FULLTEMP
