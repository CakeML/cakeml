#!/bin/sh
# Run from this directory with a freshly bootstrapped, Eval-enabled compiler.
# Keep the full transcript; compare every marker and diagnostic in order.
set -eu

./cake --repl < test-repl-opens.cml > test-repl-opens.out 2> test-repl-opens.err
if test -s test-repl-opens.err; then
    cat test-repl-opens.err >&2
    exit 1
fi
awk '
    /^DOPEN-REPL:/ { print; next }
    /ERROR:/ {
        diagnostic = substr($0, index($0, "ERROR:"))
        if (diagnostic ~ /^ERROR: Undefined module: Missing at /)
            print "ERROR: undefined-module"
        else if (diagnostic ~ /^ERROR: Type mismatch/)
            print "ERROR: type-mismatch"
        else if (diagnostic ~ /^ERROR: Value restriction violated at /)
            print "ERROR: value-restriction"
        else if (diagnostic ~ /^ERROR: Undefined variable: N[.]y at /)
            print "ERROR: undefined-variable"
        else
            print diagnostic
        next
    }
    /EXCEPTION:/ { print substr($0, index($0, "EXCEPTION:")); next }
    /Parsing failed|<failure:|Compilation interrupted/ { print }
' test-repl-opens.out > test-repl-opens.events
diff -u test-repl-opens.expected test-repl-opens.events
