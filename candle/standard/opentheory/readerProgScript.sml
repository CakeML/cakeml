open preamble
     ml_monad_translatorLib
     readerTheory
     (*ml_hol_kernelProgTheory*)

val _ = new_theory "readerProg"

val _ = translation_extends "ml_hol_kernelProg"

(* Initial state for the reader.

   TODO: Move to readerScript
*)
val init_state_def = Define `
  init_state =
    <| stack := []
     ; dict  := LN
     ; thms  := [] |>`;

(* --- Translate the OpenTheory reader --- *)

val _ = translate init_state_def
val _ = translate object_case_def
val _ = translate list_case_def
val _ = translate pair_case_def
val _ = translate K_DEF
val _ = translate EVEN
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def

(* Monadic translations: failing *)
val r = m_translate getNum_def
val r = m_translate getName_def
val r = m_translate getList_def
val r = m_translate getTypeOp_def
val r = m_translate getType_def
val r = m_translate getConst_def
val r = m_translate getVar_def
val r = m_translate getTerm_def
val r = m_translate getThm_def
val r = m_translate pop_def
val r = m_translate peek_def
val r = m_translate find_axiom_def
val r = m_translate getList_def
val r = m_translate getTys_def
val r = m_translate getTms_def
val r = m_translate getNvs_def
val r = m_translate getCns_def
val r = m_translate readLine_def

