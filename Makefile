# Makefile for type-checking the whole TypeTopology development.
#
# Every checking target type-checks source/AllModulesIndex.lagda, which
# hereditarily imports every module in the library.
#
# Targets:
#
#   make              Same as `make latest`.
#
#   make latest       Type-check everything sequentially with the latest
#   make l            released Agda (2.8.0; also works on 2.9.0). `l` is a shorthand.
#
#   make development  Type-check everything sequentially with the development
#   make d            version of Agda (>= 2.9.0). Same as `latest` but adds the
#                     warning flag described below. `d` is a shorthand.
#
#   make j            Like `development`/`d`, but in parallel: also passes
#                     `agda -j` (all available cores).
#
# Override the Agda executable with e.g.  make latest AGDA=agda-2.8.0

AGDA ?= agda

.DEFAULT_GOAL := latest

.PHONY: help latest l development d j

help:
	@echo "TypeTopology type-checking. Available targets:"
	@echo
	@echo "  make              Same as 'make latest' (the default)."
	@echo "  make latest       Type-check with the latest released Agda (2.8.0+)."
	@echo "  make l            Shorthand for 'make latest'."
	@echo "  make development  Type-check sequentially (development Agda >= 2.9.0)."
	@echo "  make d            Shorthand for 'make development'."
	@echo "  make j            Like 'd' but in parallel (uses '-j', all cores)."
	@echo "  make help         Print this message."
	@echo
	@echo "Note: the parallel target is 'make j'. Beware that 'make -j' is GNU"
	@echo "make's own jobs flag, not this target, and does not do what you want."
	@echo
	@echo "Override the Agda executable with e.g. make l AGDA=agda-2.8.0".
	@echo "                                   or  make d AGDA=agda-2.9.0".


latest l:
	cd source && $(AGDA) AllModulesIndex.lagda

development d:
	cd source && $(AGDA) AllModulesIndex.lagda

j:
	cd source && $(AGDA) -j AllModulesIndex.lagda

# Friendly error for an unrecognised target: report it and show the help.
# The empty rule for Makefile stops this catch-all from trying to "remake"
# the Makefile itself.

Makefile: ;
%:
	@echo "make: unknown target '$@'." >&2
	@$(MAKE) --no-print-directory help >&2
	@exit 2
