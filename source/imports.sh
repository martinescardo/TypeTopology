#!/usr/bin/env bash
set -Eeuo pipefail

# This script will list unused imports
#
# Example usage
## Run from TypeTopology/source
## ./imports.sh UF/Embeddings.lagda
## ./imports.sh DomainTheory/Lifting/LiftingDcpo.lagda

# See https://stackoverflow.com/questions/4247068/sed-command-with-i-option-failing-on-mac-but-works-on-linux
if [[ "$OSTYPE" == "darwin"* ]]; then
  # Require gnu-sed.
  if ! [ -x "$(command -v gsed)" ]; then
    echo "Error: 'gsed' is not istalled." >&2
    echo "If you are using Homebrew, install with 'brew install gnu-sed'." >&2
    exit 1
  fi
  SED_CMD=gsed
else
  SED_CMD=sed
fi

FILE=$1

# Get all line numbers that have 'open import ...'
IMPORTS=$(grep -n "open import" $FILE | cut -d ':' -f1)

# Get the cluster, e.g. 'UF' or 'DomainTheory/Lifting'
CLUSTER=$(dirname $FILE)

# And with '.' instead of '/'
CLUSTERMOD=$(echo $CLUSTER | ${SED_CMD} 's/\//./')

# Get the (relative) module name
MODNAME=$(basename $FILE | ${SED_CMD} 's/.lagda$//')

# Set up a temporary file for testing
TEMP="UnusedImportTesting"
FULLTEMP="${CLUSTER}/${TEMP}.lagda"

for i in $IMPORTS;
do
    ${SED_CMD} "$i s/^/-- /" $FILE > $FULLTEMP # Comment out an import

    # Replace module name to match the temporary file
    OLDMOD="module ${CLUSTERMOD}.${MODNAME}"
    NEWMOD="module ${CLUSTERMOD}.${TEMP}"
    ${SED_CMD} -i "s/${OLDMOD}/${NEWMOD}/" $FULLTEMP

    # Try to compile and report back
    agda $FULLTEMP > /dev/null &&
	{
	    IMPORT=$(${SED_CMD} -n "${i}p" $FILE | cut -d ' ' -f3)
	    echo "Importing $IMPORT was not necessary"
	}
done
rm $FULLTEMP
