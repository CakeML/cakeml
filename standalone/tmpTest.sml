open standaloneLib;

val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val th = EVAL ``prog_to_bytecode_string ^x``;

