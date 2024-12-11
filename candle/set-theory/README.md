A specification of (roughly) Zermelo's set theory.

[jrhSetScript.sml](jrhSetScript.sml):
A HOL4 port of Model/modelset.ml from the HOL Light distribution.
Now unused, but was once the set theory behind our semantics.

[setModelScript.sml](setModelScript.sml):
An example universe satisfying is_set_theory and (assuming the
existence of an infinite set) is_model.

[setSpecScript.sml](setSpecScript.sml):
Specification of (roughly) Zermelo's set theory.
Two main definitions:
  is_set_theory (mem : 'U -> 'U -> bool), and
  is_model (mem, indset, ch)

[zfc](zfc):
An old formalisation of set theory
