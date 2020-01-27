The CakeML pattern matching expressions compiler

[pattern_commonScript.sml](pattern_commonScript.sml):
Types common to some different parts of the pattern match compiler.

[pattern_compScript.sml](pattern_compScript.sml):
A simple pattern compiler that moves constant patterns upwards,
checks for exhaustiveness, and then converts the pattern rows into
an if-then-else decision tree.

[pattern_semanticsScript.sml](pattern_semanticsScript.sml):
The syntax and semantics of the input and output to the
pattern-match compiler.
