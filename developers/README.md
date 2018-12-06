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

[readme_gen.sml](readme_gen.sml):
This SML program generates a `README.md` summary for the files
given as command-line arguments to this script. The contents of the
summaries are read from a specific style of comment that needs to
appear at the top of each file.

[wc.sh](wc.sh):
A script that counts non-blank lines.
