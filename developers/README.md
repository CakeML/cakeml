This directory contains scripts for automating routine tasks, e.g., for
generating README.md files.

[build-sequence](build-sequence):
The regression test runs through this list of directories.

[readme_gen.sml](readme_gen.sml):
This SML program generates a `README.md` summary for the files
given as command-line arguments to this script. The contents of the
summaries are read from a specific style of comment that needs to
appear at the top of each given file.

[wc.sh](wc.sh):
A script that counts non-blank lines.
