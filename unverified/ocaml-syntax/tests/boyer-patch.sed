# Some definitions don't typecheck because of a monomorphism restriction.
# CakeML has no type annotations, so I see no better way to fix these.

s/\(val lemmas = \).*/\1ref (List.tl [MkHead ("", ref [])]);/
s/\(val r = \).*/\1ref (List.tl [(Var 0, Var 0)]);/
