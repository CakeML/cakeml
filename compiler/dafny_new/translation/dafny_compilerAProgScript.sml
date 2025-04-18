(*
  TEST TEST TEST
*)

open preamble
open ml_translatorLib
open dafny_to_cakemlProgTheory
open dafny_compilerTheory
open cfTacticsLib  (* process_topdecs *)
open dafny_transformProgTheory
open fromSexpTheory  (* listsexp *)
open stringTheory
open numposrepTheory
open simpleSexpTheory
open ml_translatorTheory
open simpleSexpParseTheory

val _ = new_theory "dafny_compilerAProg";

val _ = translation_extends "dafny_transformProg";

val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val r = translate stringTheory.isPrint_def
val _ = ml_translatorLib.use_string_type false;

val _ = add_preferred_thy "-";

val _ = ml_translatorLib.use_string_type true;

Theorem strip_dot_alt =
  simpleSexpParseTheory.strip_dot_def |> PURE_ONCE_REWRITE_RULE [CONS_APPEND];
val _ = translate strip_dot_alt

val _ = translate simpleSexpParseTheory.print_space_separated_def;

val _ = use_string_type false;
val _ = translate simpleSexpParseTheory.escape_string_def;
val _ = use_string_type true;

Theorem num_to_dec_string_v_thm:
  (NUM --> HOL_STRING_TYPE) toString ^(IntProgTheory.tostring_v_thm |> concl |> rand)
Proof
  assume_tac IntProgTheory.tostring_v_thm >>
  fs[NUM_def,Arrow_def,HOL_STRING_TYPE_def,INT_def,AppReturns_def,
     GSYM mlintTheory.num_to_str_thm,mlintTheory.num_to_str_def]
QED

val _ = add_user_proved_v_thm num_to_dec_string_v_thm;

(* TODO: translator failed for some reason if I just prove these as equations on print_sexp *)
Definition print_sexp_alt_def:
  (print_sexp_alt (SX_SYM s) = s) ∧
  (print_sexp_alt (SX_NUM n) = toString n) ∧
  (print_sexp_alt (SX_STR s) = "\"" ++ IMPLODE(escape_string s) ++ "\"") ∧
  (print_sexp_alt s =
   let (ls,n) = strip_dot s in
   case n of
   | NONE =>
     if LENGTH ls = 2 ∧ HD ls = SX_SYM "quote"
     then "'" ++ print_sexp_alt (EL 1 ls)
     else "(" ++ print_space_separated (MAP print_sexp_alt ls) ++ ")"
   | SOME lst =>
       "(" ++ print_space_separated (MAP print_sexp_alt ls) ++ " . " ++ print_sexp_alt lst ++ ")")
Termination
  WF_REL_TAC`measure sexp_size` >> rw[] >> simp[simpleSexpTheory.sexp_size_def] >>
   fs[Once simpleSexpParseTheory.strip_dot_def] >>
   pairarg_tac \\ fs[] \\ rw[simpleSexpTheory.sexp_size_def] \\ fs[]
   \\ imp_res_tac simpleSexpParseTheory.strip_dot_MEM_sizelt
   \\ imp_res_tac simpleSexpParseTheory.strip_dot_last_sizeleq
   \\ fsrw_tac[boolSimps.DNF_ss][] \\ simp[]
   \\ fs[LENGTH_EQ_NUM_compute] \\ rw[] \\ fs[]
   \\ res_tac \\ simp[]
End

Theorem strip_dot_EQ_NILSOME:
  strip_dot s = ([], SOME x) ⇒ s = x
Proof
  Cases_on ‘s’ >> simp[AllCaseEqs()] >> pairarg_tac >> simp[]
QED

Theorem print_sexp_alt_thm:
  print_sexp s = print_sexp_alt s
Proof
  `?n. n = sexp_size s` by rw[] >>
  pop_assum mp_tac >>
  qid_spec_tac `s` >> qid_spec_tac `n` >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >> Cases_on `s` >>
  fs[simpleSexpParseTheory.print_sexp_def,print_sexp_alt_def,IMPLODE_EXPLODE_I,
     sexp_size_def, PULL_FORALL] >>
  pairarg_tac >> fs[] >> every_case_tac >>
  gvs[STRCAT_11, LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  pairarg_tac >> gvs[]
  >- (first_x_assum irule >> dxrule strip_dot_MEM_sizelt >> simp[])
  >- (drule strip_dot_last_sizelt >> dxrule strip_dot_MEM_sizelt >> simp[])
  >- (dxrule strip_dot_MEM_sizelt >>
      disch_then (C (resolve_then Any assume_tac)
                  (DECIDE “x < y ⇒ x < a + (y + 1n)”)) >>
      pop_assum (first_assum o resolve_then Any assume_tac) >>
      simp[Cong MAP_CONG] >> simp[SF ETA_ss])
  >- (drule strip_dot_last_sizelt >> drule strip_dot_MEM_sizelt >> simp[] >>
      rename [‘strip_dot s0 = (els, SOME _)’] >>
      Cases_on ‘NULL els’ >> gs[] >>
      disch_then (C (resolve_then Any assume_tac)
                  (DECIDE “x < y ⇒ x < a + (y + 1n)”)) >>
      pop_assum (first_assum o resolve_then Any assume_tac) >>
      simp[Cong MAP_CONG] >> simp[SF ETA_ss] >>
      Cases_on ‘els’ >> gs[] >>
      dxrule strip_dot_EQ_NILSOME >> simp[])
QED

val r = translate EL;

val el_side = Q.prove(
  `!n xs. el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "el_side_def"]
  THEN fs[])
                |> update_precondition;

val _ = translate print_sexp_alt_def;

val _ = translate print_sexp_alt_thm;

val _ = export_theory ();
