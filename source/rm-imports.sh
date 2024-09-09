#!/usr/bin/env bash
set -Eeuo pipefail

# This script will *remove* unused imports
#
# Example usage
## Run from TypeTopology/source
## ./rm-imports.sh UF/Embeddings.lagda
## ./rm-imports.sh DomainTheory/Lifting/LiftingDcpo.lagda

# NB: This script will break your file in case of duplicate imports.
# This is not great, but at least it detects such duplicates as a side-effect :)
# I think manually fixing those is the easiest way to handle this (for now).

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

# "catch exit status 1" grep wrapper
# https://stackoverflow.com/questions/6550484/prevent-grep-returning-an-error-when-input-doesnt-match/49627999#49627999
c1grep() { grep "$@" || test $? = 1; }

# Get all line numbers that have 'open import ...'
IMPORTS=$(c1grep -n "open import" $FILE | cut -d ':' -f1)

# Get the cluster, e.g. 'UF' or 'DomainTheory/Lifting'
CLUSTER=$(dirname $FILE)

# And with '.' instead of '/'
CLUSTERMOD=$(echo $CLUSTER | ${SED_CMD} 's/\//./g')

# Get the (relative) module name
MODNAME=$(basename $FILE | ${SED_CMD} 's/.lagda$//')

# Set up a temporary file for testing
TEMP="UnusedImportTesting"
FULLTEMP="${CLUSTER}/${TEMP}.lagda"

UNUSED=()

for i in $IMPORTS;
do
    ${SED_CMD} "$i s/^/-- /" $FILE > $FULLTEMP # Comment out an import

    # Replace module name to match the temporary file
    OLDMOD="module ${CLUSTERMOD}.${MODNAME}"
    NEWMOD="module ${CLUSTERMOD}.${TEMP}"
    ${SED_CMD} -i "s/${OLDMOD}/${NEWMOD}/" $FULLTEMP

    # Try to compile and save line numbers of unused imports
    agda $FULLTEMP > /dev/null &&
	{
	    UNUSED+=( $i )
	}

    rm $FULLTEMP
done

# Remove unused imports from the file
${SED_CMD} -i "${UNUSED[*]/%/d;}" $FILE
