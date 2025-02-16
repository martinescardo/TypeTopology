#!/bin/bash

agda --dependency-graph="admin-utilities/dependency_graph.dot" source/AllModulesIndex.lagda && echo "Successfully generated `dependency_graph.dot`."

ghc -O3 admin-utilities/GenerateMakefile.hs -o GenerateMakefile

echo "Now generating Makefile..."

./GenerateMakefile > Makefile
