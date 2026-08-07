(*
  This compiler phase removes all Skip instructions (generated from
  Tick in stackLang).
*)
Theory lab_filter
Ancestors
  labLang
Libs
  preamble

Definition not_skip_def:
  not_skip l = case l of Asm (Asmi (Inst Skip)) _ _ => F | _ => T
End

Definition filter_skip_def:
  (filter_skip [] = []) /\
  (filter_skip (Section n xs md :: rest) =
     Section n (FILTER not_skip xs) md :: filter_skip rest)
End

Theorem filter_skip_MAP:
   ∀ls. filter_skip ls = MAP (λx. case x of Section n xs md => Section n (FILTER not_skip xs) md) ls
Proof
  Induct \\ simp[filter_skip_def] \\ Cases \\ simp[filter_skip_def]
QED

