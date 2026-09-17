# Common README.md rule for cakeml-tree Holmakefiles.
#
# Each leaf Holmakefile sinclude's this snippet to get a `README.md`
# target wired up the same way everywhere.  The default file list
# covers the usual *Script.sml / *Lib.sml / *Syntax.sml triad; a
# Holmakefile that needs more (or fewer) sources sets README_SOURCES
# *before* the sinclude line.
#
# Usage:
#   sinclude $(CAKEMLDIR)/developers/readme.mk
#
# Or, with extras:
#   README_SOURCES = $(wildcard *Script.sml) $(wildcard *Lib.sml) \
#                    $(wildcard *Syntax.sml) $(wildcard *.lem)
#   sinclude $(CAKEMLDIR)/developers/readme.mk

ifndef README_SOURCES
README_SOURCES = $(wildcard *Script.sml) $(wildcard *Lib.sml) $(wildcard *Syntax.sml)
endif

all: README.md
.PHONY: all

README.md: $(CAKEMLDIR)/developers/readme_gen readmePrefix \
           $(wildcard */readmePrefix) $(README_SOURCES)
	$(protect $(CAKEMLDIR)/developers/readme_gen) $(README_SOURCES)
