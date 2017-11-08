This directory contains scripts for automating routine tasks, e.g., for
generating README.md files.

[build-email.sh](build-email.sh):
This script produces a report on whether a regression test
succeeded, timed out or failed.

[build-sequence](build-sequence):
The regression test runs through this list of directories.

[misc.sh](misc.sh):
Functions for displaying time and memory usage.

[readme_gen.sml](readme_gen.sml):
This SML program generates a `README.md` summary for the files
given as command-line arguments to this script. The contents of the
summaries are read from a specific style of comment that needs to
appear at the top of each given file.

[regression-test.sh](regression-test.sh):
A script that runs the regression test.

[wc.sh](wc.sh):
A script that counts non-blank lines.
