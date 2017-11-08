This directory contains scripts for automating routine tasks, e.g. for
running regression tests.

[build-email.sh](build-email.sh):
This script produces a report on whether a regression test
succeeded, timed out or failed.

[build-sequence](build-sequence):
The regression test runs through this list of directories.

[build-travis.sh](build-travis.sh):
A Travis selftest script. This file is probably obsolete, since
Travis is no longer supported.

[cached-deps.sh](cached-deps.sh):
A script for downloading cached state for Travis. This file is
probably obsolete, since Travis is no longer supported.

[install-deps.sh](install-deps.sh):
Builds various things for Travis. This file is probably obsolete,
since Travis is no longer supported.

[misc.sh](misc.sh):
Functions for displaying time and memory usage.

[readme_gen.sml](readme_gen.sml):
This SML program generates a `README.md` summary for the files
given as command-line arguments to this script. The contents of the
summaries are read from a specific style of comment that needs to
appear at the top of each given file.

[regression](regression):
Automated regression test infrastructure for CakeML.

[regression-test.sh](regression-test.sh):
A script that runs the regression test.

[wc.sh](wc.sh):
A script that counts non-blank lines.
