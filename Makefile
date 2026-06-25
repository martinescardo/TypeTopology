# Makefile for type-checking the whole TypeTopology development.
#
# Both checking targets type-check source/AllModulesIndex.lagda, which
# hereditarily imports every module in the library.
#
# Targets:
#
#   make             Same as `make sequential`.
#
#   make sequential  Type-check everything sequentially. Portable: works
#                    with Agda 2.8.0 (and 2.9.0). No warning flags.
#
#   make j           Type-check everything in parallel, for Agda >= 2.9.0.
#                    Uses `agda -j` (all available cores) and silences the
#                    2.9.0-only warning RewriteVariablesBoundInSingleton,
#                    which comes from the rewrite rules in
#                    SyntheticHomotopyTheory.Circle.WithRewriting.
#
# Override the Agda executable with e.g.  make sequential AGDA=agda-2.8.0

AGDA ?= agda

.DEFAULT_GOAL := sequential

.PHONY: help sequential j

help:
	@echo "TypeTopology type-checking. Available targets:"
	@echo
	@echo "  make              Same as 'make sequential' (the default)."
	@echo "  make sequential   Type-check everything sequentially (Agda 2.8.0+)."
	@echo "  make j            Type-check everything in parallel (Agda >= 2.9.0)."
	@echo "  make help         Print this message."
	@echo
	@echo "Note: the parallel target is 'make j'. Beware that 'make -j' is GNU"
	@echo "make's own jobs flag, not this target, and does not do what you want."

sequential:
	cd source && $(AGDA) AllModulesIndex.lagda

j:
	cd source && $(AGDA) -j -WnoRewriteVariablesBoundInSingleton AllModulesIndex.lagda

# Friendly error for an unrecognised target: report it and show the help.
# The empty rule for Makefile stops this catch-all from trying to "remake"
# the Makefile itself.

Makefile: ;
%:
	@echo "make: unknown target '$@'." >&2
	@$(MAKE) --no-print-directory help >&2
	@exit 2
