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
