#!/bin/sh
find . -name '*Script.sml' -o -name '*Lib.sml' |
egrep -v 'hol-light|whole-prog|sem-reason|lem_lib|okasaki|other-examples|simulator|hardware|tests|testing|unverified|print_ast|word_prelude|_demo|validate_printer' |
xargs cat |
sed '/(\*/{: a ; /\*)/b b ; N ; b a ; : b ; d}' | # delete comments
sed '/^\s*$/d' | # delete blank lines
wc -l

# semantics   3942
# metatheory  8420
# parsing     5064
# inference   5484
# bytecode    1637
# compiler   22086
# repl        3021
# bootstrap   1568
# x86-64     14747
# translator  5116
# misc        1348
