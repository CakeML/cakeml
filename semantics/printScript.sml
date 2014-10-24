open preamble
open terminationTheory initialProgramTheory
val _ = new_theory"print"

val type_to_string_def = tDefine "type_to_string" `
(type_to_string (Tvar tvn) ⇔ tvn) ∧
(type_to_string (Tvar_db n) ⇔ num_to_dec_string n) ∧
(type_to_string (Tapp [t1;t2] TC_fn) ⇔
  "(" ++ type_to_string t1 ++ "->" ++ type_to_string t2 ++ ")") ∧
(type_to_string (Tapp ts TC_fn) ⇔ "<bad function type>") ∧
(type_to_string (Tapp ts TC_tup) ⇔
  "(" ++ types_to_string ts ++ ")") ∧
(type_to_string (Tapp [] tc) ⇔ tc_to_string tc) ∧
(type_to_string (Tapp ts tc) ⇔
  "(" ++ types_to_string ts ++ ") " ++ tc_to_string tc) ∧
(types_to_string [] ⇔ "") ∧
(types_to_string [t] ⇔ type_to_string t) ∧
(types_to_string (t::ts) ⇔ type_to_string t ++ ", " ++ types_to_string ts)`
(wf_rel_tac `measure (\x. case x of INL x => t_size x | INR x => t1_size x)`);

val print_envM_def = Define `
print_envM envM = CONCAT (MAP (λ(x,m). "module " ++ x ++ " = <structure>\n") envM)`;

val print_lit_def = Define `
(print_lit (IntLit i) = int_to_string i) ∧
(print_lit (Char c) = "#"++(string_to_string [c])) ∧
(print_lit (StrLit s) = string_to_string s) ∧
(print_lit (Word8 w) = "0wx"++(word_to_hex_string w)) ∧
(print_lit (Bool T) = "true") ∧
(print_lit (Bool F) = "false") ∧
(print_lit Unit = "()")`;

val print_v_def = Define `
(print_v (Litv l) = print_lit l) ∧
(print_v (Conv _ _) = "<constructor>") ∧
(print_v (Vectorv _) = "<vector>") ∧
(print_v (Closure _ _ _) = "<fn>") ∧
(print_v (Recclosure _ _ _) = "<fn>") ∧
(print_v (Loc _) = "<ref>")`;

val print_envE_def = Define `
(print_envE [] [] = "") ∧
(print_envE ((x', (n,t))::types) ((x,v)::envE) =
  "val " ++ x ++ ":" ++ type_to_string t ++ " = " ++ print_v v ++ "\n" ++ print_envE types envE)`;

val print_result_def = Define `
(print_result types (Tdec _) (Rval (envM,envE)) = print_envE types envE) ∧
(print_result _ (Tmod mn _ _) (Rval _) = "structure "++mn++" = <structure>\n") ∧
(print_result _ _ (Rerr Rtimeout_error) = "<timeout error>\n") ∧
(print_result _ _ (Rerr Rtype_error) = "<type error>\n") ∧
(print_result _ _ (Rerr (Rraise e)) = "raise " ++ print_v e ++ "\n")`;

val print_prog_result_def = Define`
  (print_prog_result types (Rval (envM,envE)) =
   case ALOOKUP envE "it" of
     SOME v => print_v v ++ "\n"
   | NONE => "") ∧
  (print_prog_result _ (Rerr Rtimeout_error) = "<timeout error>\n") ∧
  (print_prog_result _ (Rerr Rtype_error) = "<type error>\n") ∧
  (print_prog_result _ (Rerr (Rraise e)) = "raise " ++ print_v e ++ "\n")`

val _ = export_theory()
