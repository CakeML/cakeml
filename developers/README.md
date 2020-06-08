This directory contains scripts for automating routine tasks, e.g., for
generating README.md files.

[rebuild-excludes](rebuild-excludes):
A list of glob patterns that should be omitted when packaging up a (partially)
built working directory for examination/rebuilding elsewhere (using HOL's
relocbuild facility).

[artefacts](artefacts):
A list of paths to files that are considered to be the (non-theory) outputs of
a successful build. As with rebuild-excludes and build-sequence, these are
paths relative to the root directory.

[bin](bin):
This directory represents a stage in the build sequence where the latest
available cake binary is downloaded to perform testing and bootstrapping.

[build-sequence](build-sequence):
The regression test runs through this list of directories.

[fix_scripts.sml](fix_scripts.sml):
This is a script that can automation adding a legacy mode line to
broken HOL4 scripts following changes to HOL4. Update the new_str
declaration below and run this with poly --script fix_scripts.sml in
the dir that needs fixing; it will recurse into INCLUDES dirs.

[readme_gen.sml](readme_gen.sml):
This SML program generates a `README.md` summary for the files
given as command-line arguments to this script. The contents of the
summaries are read from a specific style of comment that needs to
appear at the top of each file.

[wc.sh](wc.sh):
A script that counts non-blank lines.
