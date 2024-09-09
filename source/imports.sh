#!/usr/bin/env bash
set -Eeo pipefail

# Created by Tom de Jong in September 2024.


# Ensure we have GNU-style sed
# See https://stackoverflow.com/questions/4247068/sed-command-with-i-option-failing-on-mac-but-works-on-linux
if [[ "$OSTYPE" == "darwin"* ]]; then
  # Require gnu-sed.
  if ! [ -x "$(command -v gsed)" ]; then
    echo "Error: 'gsed' is not istalled." >&2
    echo "If you are using Homebrew, install with 'brew install gnu-sed'." >&2
    exit 1
  fi
  sed_cmd=gsed
else
  sed_cmd=sed
fi


# "catch exit status 1" grep wrapper
# https://stackoverflow.com/questions/6550484/prevent-grep-returning-an-error-when-input-doesnt-match/49627999#49627999
c1grep() { grep "$@" || test $? = 1; }


# This script will list unused imports
#
# Example usage
## Run from TypeTopology/source
## ./imports.sh UF/Embeddings.lagda
## ./imports.sh DomainTheory/Lifting/LiftingDcpo.lagda

print_usage() {
  printf "From TypeTopology/source, run this script as
  ./imports.sh UF/Embeddings.lagda
to report redundant imports in UF/Embeddings.lagda.

Alternatively, use the -d (directory) flag to report redundant
imports in all .lagda files in the UF/ directory, e.g.
  ./imports.sh -d UF/
NB: The forward slash at the end of the directory is important.

Use the -r flag to remove redundant imports (without reporting them), e.g.
  ./imports.sh -d -r UF/
  ./imports.sh -r UF/Embeddings.lagda

Wrong flags, or the -h (help) flag, displays this message.
"
}


# Implement option flags
# https://stackoverflow.com/questions/7069682/how-to-get-arguments-with-flags-in-bash
dir_flag=false
rem_flag=false

OPTIND=1
while getopts 'drh' flag; do
  case "${flag}" in
    d) dir_flag=true ;;
    r) rem_flag=true ;;
    h) print_usage
       exit 0 ;;
    *) print_usage
       exit 1 ;;
  esac
done


# Discard options so we can get the file/directory name next
shift "$((OPTIND-1))"
if [ $# -ge 1 ] && [ -n "$1" ]; then
  input=$1
else
  print_usage
  exit 1
fi


check_imports() {
  unused=()
  local file=$1

  # Get all line numbers that have 'open import ...'
  imports=$(c1grep -n "open import" $file | cut -d ':' -f1)

  # Get the cluster, e.g. 'UF' or 'DomainTheory/Lifting'
  cluster=$(dirname $file)

  # And with '.' instead of '/'
  clustermod=$(echo $cluster | ${sed_cmd} 's/\//./')

  # Get the (relative) module name
  modname=$(basename $file | ${sed_cmd} 's/.lagda$//')

  # Set up a temporary file for testing
  temp="UnusedImportTesting"
  fulltemp="${cluster}/${temp}.lagda"

  local i
  for i in $imports;
  do
    ${sed_cmd} "$i s/^/-- /" $file > $fulltemp # Comment out an import

    # Replace module name to match the temporary file
    oldmod="module ${clustermod}.${modname}"
    newmod="module ${clustermod}.${temp}"
    ${sed_cmd} -i "s/${oldmod}/${newmod}/" $fulltemp

    # Try to scope-check and save (line numbers of) any redundant imports
    agda --only-scope-checking $fulltemp > /dev/null &&
      {
        unused+=( $i )
      }

    rm $fulltemp
  done

  if $rem_flag; then
      ${sed_cmd} -i "${unused[*]/%/d;}" $file # Remove redundant imports
  else # Report redundant imports
      for i in $unused;
      do
	import=$(${sed_cmd} -n "${i}p" $file | cut -d ' ' -f3)
	echo "Importing $import was not necessary"
      done
  fi
}


if $dir_flag; then # Check all *.lagda files in given directory
  for i in ${input}*.lagda
  do
    check_imports $i
    echo "Done with $(basename $i)"
  done
else
  check_imports $input # Check a single file
fi