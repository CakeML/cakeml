# The definition of `lemmas` doesn't typecheck because of the value
# restriction.
# CakeML has no type annotations, so I see no better way to fix this.

s/\(val lemmas = \)Pervasives.oc_ref \[\];/\1ref (List.tl [MkHead ("", ref [])]);/
