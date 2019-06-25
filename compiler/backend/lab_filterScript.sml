(*
  This compiler phase removes all Skip instructions (generated from
  Tick in stackLang).
*)
open preamble labLangTheory;

val _ = new_theory "lab_filter";

val not_skip_def = Define `
  not_skip l = case l of Asm (Asmi (Inst Skip)) _ _ => F | _ => T`;

val filter_skip_def = Define `
  (filter_skip [] = []) /\
  (filter_skip (Section n xs :: rest) =
     Section n (FILTER not_skip xs) :: filter_skip rest)`;

Theorem filter_skip_MAP:
   ∀ls. filter_skip ls = MAP (λx. case x of Section n xs => Section n (FILTER not_skip xs)) ls
Proof
  Induct \\ simp[filter_skip_def] \\ Cases \\ simp[filter_skip_def]
QED

val _ = export_theory();
