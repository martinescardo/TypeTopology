#!/usr/bin/env bash

# # This script generates a dependency graph of (subfolders of)
# # TypeTopology, in the format recognized by the unix command tsort.

# # Convention here: double hashes are explanations. Single hashes are
# # code you may wish to include in future experiments.

# # This script creates a file in the format required by unix `tsort`.
# #
# # But also this file can be used for other statistics.
# # It is particularly easy to read e.g. from a Haskell program or
# # indeed a program in any programming language.
# #
# # The format is (as for tsort), a list of lines
# #
# #  dependecy -> thing that depends on the dependency.

# #
# # Run e.g. as
# #
# #   $ TypeTopology/source> ../topologicalsort | tsort | wc
# #     9831   19662  464509
# #
# # But you can also run it as e.g.
# #
# #   $ cd TypeTopology
# #   $ TypeTopology/source/TypeTopology> ../../topologicalsort.sh | wc
# #     406     812   16483
# #
# # In other words, you will get the dependency graph for the folder you at.

set -Eeo pipefail

# # Optionally remove unsafe modules. If this is desired,
# # insert the following, after CubicalBinarySystem below:

  # grep -v Cubical \
  # | grep -v Unsafe \
  # | grep -v InfinitePigeon \
  # | grep -v Primitive \
  # | grep -v "Games/Main" \
  # | grep -v "Chapter6/Main" \
  # | grep -v index \
  # | grep -v AllModulesIndex \

# # NB. CubicalBinarySystem no longer works.

# # What we do here:
# #
# # 1.  We get all lines that contain "import" and "open import" in Agda files
# #     under git control, taking care of whitespaces,
# # 2.  remove the extensions .(l)agda,
# # 3.  remove all spaces at the beginning of lines,
# # 4.  collapse multiple spaces to single spaces,
# # 5.  remove "(open) import" from line beginnings,
# # 6.  remove all spaces that appear immediately after a colon
# #     (where the colon is produced by grep), without removing the colon,
# # 7.  remove everything after a whitespace (this will be module parameters),
# # 8.  swap what is before the colon with what is after the colon
# #     (to get the right dependency order),
# # 9.  replace "/" by "." globally,
# # 10. replace ":" by ":" globally
# #     (at the stage we have a file that tsort can work with,
# #      but we may as well cleanup),
# # 11. remove duplicate lines.

grep -E "^[[:space:]]*(open[[:space:]]+)?import " `git ls-files '*agda'` \
  | grep -v CubicalBinarySystem \
  | sed 's/\.lagda//' \
  | sed 's/\.agda//' \
  | sed 's/^[[:space:]]*//' \
  | sed 's/  */ /g' \
  | sed 's/open import //' \
  | sed 's/import //' \
  | sed 's/:\([[:space:]]*\)/:/g' \
  | sed 's/ .*//' \
  | sed 's/^\([^:]*\):\(.*\)$/\2:\1/' \
  | sed 's|/|.|g' \
  | sed 's|:| |g' \
  | uniq \

# # Optionally continue as follows to produce a safe Agda file,
# # but then the above filter has to be applied.

#  | tsort \
#  | sed 's/^/import /' \
#  | awk 'BEGIN {print "{-# OPTIONS --safe --without-K #-}"; \
#                print "module listOfAlmostAllFiles where"} {print}' \
#        > listOfAlmostAllFiles.agda

# agda listOfAlmostAllFiles.agda -j +RTS -A16M -qb0
# agda ../AllModulesIndex.lagda

# # However, this is not very useful other than as a sanity check
# # during the development of this script.


# # TODO. Someone brave people please make a more general version of
# # this script, including the above single-hash comments as options.
