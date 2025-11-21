(*
  Various definitions that are used by multiple files, but don't quite fit in
  any of them.
*)
Theory dafny_misc
Libs
  preamble

Theorem OPT_MMAP_LENGTH:
  ∀xs ys. OPT_MMAP f xs = SOME ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct \\ simp []
  \\ gen_tac \\ Cases \\ simp []
QED

Theorem MEM_MAP_FST:
  ∀xs. MEM (x,y) xs ⇒ MEM x (MAP FST xs)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac \\ gvs []
QED
