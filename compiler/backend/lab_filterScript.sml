open preamble labLangTheory;

val _ = new_theory "lab_filter";

(* This pass removes all Skip instructions (generated from Tick in stackLang) *)

val not_skip_def = Define `
  not_skip l = case l of Asm (Inst Skip) _ _ => F | _ => T`;

val filter_skip_def = Define `
  (filter_skip [] = []) /\
  (filter_skip (Section n xs :: rest) =
     Section n (FILTER not_skip xs) :: filter_skip rest)`;

val _ = export_theory();
