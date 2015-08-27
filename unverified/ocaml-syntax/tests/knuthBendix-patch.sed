# Eta-expansions

s/val length =$/fun length xs =/
s/in j 0/\0 xs/

s/val rev =$/fun rev xs =/
s/in f \[\]/\0 xs/

s/val check_rules =$/fun check_rules xs =/
s/ 0;/ 0 xs;/

s/val pretty_rules = app pretty_rule;$/fun pretty_rules xs = app pretty_rule xs;/

0,/val doit =/s/val doit =/PLACEHOLDER/
s/val doit =/val doit = fn i =>/
s/PLACEHOLDER/val doit =/
s/in loop/in loop i/
