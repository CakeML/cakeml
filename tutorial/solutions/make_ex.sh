#!/bin/bash

# An answer block starts with a single commented line of the form
# "(*ex ... *)" and is ended by a single line of the form (* ex*)

sed 's/(\*ex \(.*\) \*)/\1\n (\*ex/g' "$1" \
    | sed '/(\*ex/,/ex\*)/d'


