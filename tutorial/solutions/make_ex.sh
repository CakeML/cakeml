#!/bin/bash

# An answer block starts with a single commented line of the form
# "(*ex ... *)" and is ended by a single line of the form (* ex*)
for file in "$@"
do
    sed 's/(\*ex \(.*\) \*)/\1\n (\*ex/g' "$file" \
        | sed '/(\*ex/,/ex\*)/d' > "../$file"
done

