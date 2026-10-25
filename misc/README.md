Auxiliary files providing glue between a standard HOL installation
and what we want to use for CakeML development.

[basicComputeLib.sml](basicComputeLib.sml):
Build a basic compset for evaluation in the logic.

[buildInfoLib.sml](buildInfoLib.sml):
Build information (CakeML and HOL4 commits and tags, and whether their
worktrees have uncommitted or untracked changes) for embedding in
programs, e.g. in the output of cake --version. It is read from
build_info.txt, which update_build_info.sh keeps up to date whenever
Holmake reads the Holmakefile in this directory. Anything that cannot be
determined is shown as unknown, with a warning.

[induct_tweakLib.sml](induct_tweakLib.sml):
Code for adjusting and improving induction theorems.

[miscScript.sml](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[packLib.sml](packLib.sml):
A library for packing theorems, terms, and types as theorems (which can
thereby be saved in theories).

[preamble.sml](preamble.sml):
Proof tools (e.g. tactics) used throughout the development.

[update_build_info.sh](update_build_info.sh):
Records the CakeML and HOL4 commits, their tags (if a tag points at the
commit), their commit dates in UTC, and whether their worktrees have
uncommitted or untracked changes in build_info.txt, which buildInfoLib
reads. The file is only replaced when its contents change, so that Holmake
rebuilds dependents of buildInfoLib only when this information changes.
Setting CML_FREEZE_BUILD_INFO to a non-empty value keeps an existing
build_info.txt unchanged, so that commits and edits cause no rebuilds (the
build info then goes stale). Called from the Holmakefile with HOLDIR as
its argument; prints the name of the file it maintains.
