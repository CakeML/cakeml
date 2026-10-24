(*
  Adds file-level parsing and formula construction to ccnf_arrayProg
*)
Theory ccnf_parseProg
Ancestors
  cnf ccnf ccnf_list ccnf_arith ccnf_arrayProg mlint syntax_helper
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
Theorem fromChar_unsafe_small:
  fromChar_unsafe c =
  if smallnum_le 48 (ORD c) then smallnum_sub (ORD c) 48 else 0
Proof
  rw[fromChar_unsafe_def,smallnum_le_def,smallnum_sub_def]
QED

val result = translate fromChar_unsafe_small;

Theorem fromchar_unsafe_side[local]:
  fromchar_unsafe_side c ⇔ T
Proof
  rw[fetch "-" "fromchar_unsafe_side_def",smallnum_le_def,smallnum_sub_def]>>
  assume_tac (Q.SPEC `c` ORD_BOUND)>>
  simp[]
QED

val _ = fromchar_unsafe_side |> update_precondition;

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = n - 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub_unsafe str m) * mul)
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
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def,
       mlstringTheory.strsub_unsafe_eq_strsub]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

Theorem fromChars_range_unsafe_tail_small:
  fromChars_range_unsafe_tail b n str mul acc =
  if smallnum_le_str n b str then acc
  else
    let m = smallnum_sub_str n 1 str in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub_unsafe str m) * mul)
Proof
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [fromChars_range_unsafe_tail_def]))>>
  simp[smallnum_le_str_def,smallnum_sub_str_def]
QED

val result = translate_no_ind fromChars_range_unsafe_tail_small;

Theorem fromchars_range_unsafe_tail_ind[local]:
  fromchars_range_unsafe_tail_ind
Proof
  once_rewrite_tac [fetch "-" "fromchars_range_unsafe_tail_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac fromChars_range_unsafe_tail_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[smallnum_le_str_def,smallnum_sub_str_def]
QED

val _ = fromchars_range_unsafe_tail_ind |> update_precondition;

Theorem fromchars_range_unsafe_tail_side[local]:
  ∀b n s mul acc.
  n ≤ strlen s ∧ b ≤ strlen s ⇒
  fromchars_range_unsafe_tail_side b n s mul acc
Proof
  ho_match_mp_tac fromChars_range_unsafe_tail_ind>>
  rw[]>>
  rw[Once (fetch "-" "fromchars_range_unsafe_tail_side_def")]>>
  gvs[smallnum_le_str_def,smallnum_sub_str_def]
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
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def]
  \\ irule fromchars_range_unsafe_tail_side
  \\ fs[padLen_DEC_eq]
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

val res = translate var_lit_def;
val res = translate keep_line_def;

val res = translate parse_header_line_def;

Theorem parse_header_line_side_thm[local]:
  ∀x. parse_header_line_side x ⇔ T
Proof
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC
QED

val _ = parse_header_line_side_thm |> update_precondition;

(*** Printing back out in the DIMACS-style surface syntax ***)

val res = translate print_lit_def;
val res = translate print_lits_def;
val res = translate max_list_def;
val res = translate print_header_line_def;

(* Reading a tokenized line from an instream, specialized to the
  blanks/tokenize pair the DIMACS readers use *)
Theorem inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [theorem"blanks_v_thm",theorem"tokenize_v_thm",blanks_def];

(* Closing a proof file discards how far it had been read *)
Theorem fastForwardFD_ADELKEY_same[simp]:
  forwardFD fs fd n with infds updated_by ADELKEY fd =
  fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem SEP_IMP_REFL_gc:
  p ==>> p * GC
Proof
  xsimpl
QED

(* Binary proof records are terminated by a zero byte *)
Definition nulc_def:
  nulc = CHR 0
End

val res = translate nulc_def;

(* The buffer size for reading proofs. TextIO's openInSetBufferSize and
  openStdInSetBufferSize allocate min 65535 (max (bsize + 4) 1028) bytes,
  so this is the largest buffer they give. *)
Definition proof_buffer_size_def:
  proof_buffer_size = 65531n
End

val res = translate proof_buffer_size_def;

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
      let val arr' = insert_clause_arr arr i v in
        fill_cfml_arr arr' (Unsafe.Arith.addWitness i 1 arr') vs
      end
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
  xlet`POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    &LIST_REL vcclause_TYPE (insert_vcc_list arrls i h) arrlsv'`
  >- (xapp>>xsimpl)>>
  `i < LENGTH arrlsv'` by (
    imp_res_tac LIST_REL_LENGTH>>
    gvs[insert_vcc_list_def,update_resize_def]>>
    qpat_x_assum`LENGTH (if _ then _ else _) = _` mp_tac>>
    rw[])>>
  xlet_auto_spec (SOME num_add_arr_spec)
  >- xsimpl>>
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
