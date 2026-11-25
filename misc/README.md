Auxiliary files providing glue between a standard HOL installation
and what we want to use for CakeML development.

[basicComputeLib.sml](basicComputeLib.sml):
Build a basic compset for evaluation in the logic.

[buildInfoLib.sml](buildInfoLib.sml):
Provides build information for embedding in programs,
e.g. in the output of cake --version.

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
Generates build_info.txt, which records version information for CakeML
and HOL4.
It only updates build_info.txt if necessary; updates can be disabled by
setting the environment variable CML_FREEZE_BUILD_INFO.
