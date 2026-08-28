(*
  Adds file-level parsing and formula construction to ccnf_arrayProg
*)
Theory ccnf_parseProg
Ancestors
  ccnf ccnf_list ccnf_arrayProg mlint syntax_helper
Libs
  preamble basis

val _ = hide_environments true;

val _ = translation_extends"ccnf_arrayProg";

(* Reported by the file-level entry points *)
Definition format_dimacs_failure_def:
  format_dimacs_failure (lno:num) s =
  «c DIMACS parse failed at line: » ^ toString lno ^ «. Reason: » ^ s ^ «\n»
End

val res = translate format_dimacs_failure_def;

Definition notfound_string_def:
  notfound_string f =
  concat[«c Input file: »; f; « no such file or directory\n»]
End

val res = translate notfound_string_def;

(* Parsing helpers *)

(* TODO: Mostly copied from mlintTheory *)
val result = translate (fromChar_unsafe_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = n - 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub str m) * mul)
Termination
  WF_REL_TAC`measure (λ(b,n,_). n)`>>
  rw[]
End

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l (n+l) s mul acc =
  (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct
  >-
    rw[Once fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]>>
  rw[]>>
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;

val fromchars_range_unsafe_tail_side_def = theorem"fromchars_range_unsafe_tail_side_def";

Theorem fromchars_range_unsafe_tail_side_def[allow_rebind]:
  ∀a1 a0 a2 a3 a4.
  fromchars_range_unsafe_tail_side a0 a1 a2 a3 a4 ⇔
   ¬(a1 ≤ a0) ⇒
   (T ∧ a1 < 1 + strlen a2 ∧ 0 < strlen a2) ∧
   fromchars_range_unsafe_tail_side a0 (a1 − 1) a2 (a3 * 10)
     (a4 + fromChar_unsafe (strsub a2 (a1 − 1)) * a3)
Proof
  Induct>>
  rw[Once fromchars_range_unsafe_tail_side_def]>>
  simp[]>>eq_tac>>rw[ADD1]>>
  gvs[]
QED

val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

Theorem fromChars_unsafe_ind[local]:
  fromchars_unsafe_ind
Proof
  rewrite_tac [fetch "-" "fromchars_unsafe_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ fs [padLen_DEC_eq,ADD1]
QED

val _ = fromChars_unsafe_ind |> update_precondition;

val result = translate fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_side_def = fetch "-" "fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm[local]:
   ∀n s. n ≤ strlen s ⇒ fromchars_unsafe_side n s
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def,fromchars_range_unsafe_tail_side_def]
QED

Theorem fromString_unsafe_side[local]:
  ∀x. fromstring_unsafe_side x = T
Proof
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]
QED

val _ = update_precondition fromString_unsafe_side;

val res = translate blanks_def;
val res = translate tokenize_def;

val res = translate mk_lit_def;

val res = translate parse_until_zero_aux_def;
val res = translate parse_until_zero_def;

val res = translate parse_until_zero_nn_aux_def;
val res = translate parse_until_zero_nn_def;

val res = translate is_int_def;
val res = translate tokenize_fast_def;

val res = translate starts_with_def;

Theorem EqualityType_CNF_LIT_TYPE:
  EqualityType (CNF_LIT_TYPE NUM)
Proof
  metis_tac(eq_lemmas())
QED

(*** Building the initial formula array ***)

Quote add_cakeml:
  fun fill_cfml_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_cfml_arr (insert_clause_arr arr i v) (i+1) vs
End

Theorem fill_cfml_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE vcclause_TYPE ls lsv ∧
  LIST_REL vcclause_TYPE arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_cfml_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    &LIST_REL vcclause_TYPE
      (FOLDL (λacc (i,v). update_resize acc vcc_none v i)
        arrls (enumerate i ls)) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_cfml_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  xlet_autop>>
  xlet`POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    &LIST_REL vcclause_TYPE (insert_vcc_list arrls i h) arrlsv'`
  >- (xapp>>xsimpl)>>
  gvs[insert_vcc_list_def]>>
  xapp>>xsimpl
QED

Quote add_cakeml:
  fun build_cfml_arr n k ls =
    fill_cfml_arr (Array.array n vcc_none) k ls
End

Theorem build_cfml_arr_spec:
  NUM n nv ∧
  NUM k kv ∧
  LIST_TYPE vcclause_TYPE ls lsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"build_cfml_arr"(get_ml_prog_state()))
  [nv; kv; lsv]
  emp
  (POSTv resv.
    SEP_EXISTS arrlsv. ARRAY resv arrlsv *
    &LIST_REL vcclause_TYPE (build_cfml_list k ls n) arrlsv)
Proof
  rw[]>>
  xcf "build_cfml_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME array_alloc_spec)>>
  xapp>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  qexistsl_tac [`k`,`REPLICATE n vcc_none`]>>
  simp[build_cfml_list_def,build_fml_list_def,LIST_REL_REPLICATE_same,
    vcc_none_v_thm]
QED
