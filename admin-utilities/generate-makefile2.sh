#!/bin/bash

# Run from TypeTopology
#
# $ admin-utilities/generate-makefile2
#
# $ time gmake -j10

set -Eeo pipefail

agda -j --dependency-graph="admin-utilities/dependency_graph.dot" source/AllModulesIndex.lagda +RTS -A16M -qb0 && echo "Successfully generated dependency_graph.dot."

ghc -O3 admin-utilities/GenerateMakefile2.hs -o GenerateMakefile2

echo "Now generating Makefile..."

./GenerateMakefile2 > Makefile
