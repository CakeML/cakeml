(**
  Support lemmas for CF proofs in the end-to-end correctness theorems
**)
Theory cfSupport
Ancestors
  basis_ffi cfHeapsBase source_to_source2 CakeMLtoFloVer
  CakeMLtoFloVerProofs
Libs
  basis cfTacticsLib ml_translatorLib preamble

val _ = translation_extends "basisProg";

Theorem IMP_SPLIT:
  (P ⇒ (Q1 ∧ Q2)) ⇔ ((P ⇒ Q1) ∧ (P ⇒ Q2))
Proof
  EQ_TAC \\ rpt strip_tac \\ fs[]
QED

Definition getDeclLetParts_def:
  getDeclLetParts [Dlet loc (Pvar fname) e] =
  let (vars, body) = stripFuns e in
  (fname, vars, body)
End

Definition real_spec_prog_def:
  real_spec_prog body env fvars vs =
    case
      evaluate
       (empty_state with fp_state := empty_state.fp_state with <| canOpt := FPScope NoOpt; real_sem := T|>)
       (env with v :=
         toRspace (extend_env_with_vars (REVERSE fvars) (REVERSE vs) env.v))
       [realify body] of
    | (st, Rval [Real r]) => r
End

(* These definitions replace several deeply nested stacks of List.hd
 * applications in the readerN functions. Why? Because xlet_auto seems to be
 * quadratic (or worse?) in the size of the cf term, which caused obscene
 * running times for proofs in this theory.
 *)

Definition list2tup2_def[simp]:
  list2tup2 (a::b::t) = (a,b)
End

Definition list2tup3_def[simp]:
  list2tup3 (a::b::c::t) = (a,b,c)
End

Definition list2tup4_def[simp]:
  list2tup4 (a::b::c::d::t) = (a,b,c,d)
End

Definition list2tup6_def[simp]:
  list2tup6 (a::b::c::d::e::f::t) = (a,b,c,d,e,f)
End

Definition list2tup8_def[simp]:
  list2tup8 (a::b::c::d::e::f::g::h::t) = (a,b,c,d,e,f,g,h)
End

Definition list2tup9_def[simp]:
  list2tup9 (a::b::c::d::e::f::g::h::i::t) = (a,b,c,d,e,f,g,h,i)
End

Overload PAIR3_TYPE = ``\t. PAIR_TYPE t (PAIR_TYPE t t)``
Overload PAIR4_TYPE = ``\t. PAIR_TYPE t (PAIR3_TYPE t)``
Overload PAIR5_TYPE = ``\t. PAIR_TYPE t (PAIR4_TYPE t)``
Overload PAIR6_TYPE = ``\t. PAIR_TYPE t (PAIR5_TYPE t)``
Overload PAIR7_TYPE = ``\t. PAIR_TYPE t (PAIR6_TYPE t)``
Overload PAIR8_TYPE = ``\t. PAIR_TYPE t (PAIR7_TYPE t)``
Overload PAIR9_TYPE = ``\t. PAIR_TYPE t (PAIR8_TYPE t)``

val r = translate list2tup2_def;
val r = translate list2tup3_def;
val r = translate list2tup4_def;
val r = translate list2tup6_def;
val r = translate list2tup8_def;
val r = translate list2tup9_def;

val tm = process_topdecs `
  fun reader1 u =
    let val cl = CommandLine.arguments ();
    in List.hd cl end;
`;
val _ = append_prog tm;
Definition reader1_def: reader1 = ^tm
End;

val tm = process_topdecs `
  fun reader2 u =
    let val cl = CommandLine.arguments ();
    in list2tup2 cl end;
`;
val _ = append_prog tm;
Definition reader2_def: reader2 = ^tm
End

val tm = process_topdecs `
  fun reader3 u =
    let val cl = CommandLine.arguments ();
    in list2tup3 cl end;
`;
val _ = append_prog tm;
Definition reader3_def: reader3 = ^tm
End

val tm = process_topdecs `
  fun reader4 u =
    let val cl = CommandLine.arguments ();
    in list2tup4 cl end;
`;
val _ = append_prog tm;
Definition reader4_def: reader4 = ^tm
End

val tm = process_topdecs `
  fun reader6 u =
    let val cl = CommandLine.arguments ();
    in list2tup6 cl end;
`;
val _ = append_prog tm;
Definition reader6_def: reader6 = ^tm
End

val tm = process_topdecs `
  fun reader8 u =
    let val cl = CommandLine.arguments ();
    in list2tup8 cl end;
`;
val _ = append_prog tm;
Definition reader8_def: reader8 = ^tm
End

val tm = process_topdecs `
  fun reader9 u =
    let val cl = CommandLine.arguments ();
    in list2tup9 cl end;
`;
val _ = append_prog tm;
Definition reader9_def: reader9 = ^tm
End

val tm = process_topdecs `
  fun printer x =
    let val z = Word64.toInt x
        val y = Int.toString z
    in TextIO.print y end;
`;
val _ = append_prog tm;
Definition printer_def: printer = ^tm
End

Definition intToFP_def:
  intToFP =
  [Dlet unknown_loc (Pvar "intToFP")
    (Fun "s"
     (Let (SOME "io")
      (App Opapp [Var (Long "Int" (Short "fromString")); Var (Short "s")])
      (Let (SOME "i")
       (App Opapp [Var (Long "Option" (Short "valOf")); Var (Short ("io"))])
       (Let (SOME "w")
        (App Opapp [Var (Long "Word64" (Short "fromInt")); Var (Short "i")])
        (App FpFromWord [Var (Short "w")])))))]
End

val _ = append_prog (intToFP_def |> concl |> rhs);

val st = get_ml_prog_state();

Definition DOUBLE_def:
  DOUBLE (d:fp_word_val) =
  λ v. v = FP_WordTree d
End

Definition DOUBLE_RES_def:
  DOUBLE_RES (d:fp_word_val option) =
  λ v. case d of | NONE => F | SOME fp => v = FP_WordTree fp
End

Definition is_float_string_def:
  is_float_string s w =
  ∃ i. fromString s = SOME i ∧
    0 ≤ i ∧
   w = ((n2w (Num i)):word64)
End

Definition toString_def:
  toString (w:word64) = (mlint$toString:int->mlstring (&((w2n w):num)))
End

Definition CakeML_evaluates_and_prints_def:
  CakeML_evaluates_and_prints (cl,fs,prog) str =
    ∃io_events.
      semantics_prog (init_state (basis_ffi cl fs)) init_env prog
        (Terminate Success io_events) ∧
      extract_fs fs io_events = SOME (add_stdout fs str)
End

Definition init_ok_def:
  init_ok (cl,fs) ⇔ wfcl cl ∧ wfFS fs ∧ STD_streams fs
End

Theorem cf_fpfromword:
  ∀ env.
  cf_fpfromword (Lit (Word64 w)) env (STDIO fs)
  (POSTv v. &DOUBLE (Fp_const w) v * STDIO fs)
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘cf_fpfromword _ _ _ Post’
  \\ fs[cf_fpfromword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
         cfTheory.app_fpfromword_def]
  \\ rpt strip_tac
  \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
  \\ qexists_tac ‘Post’ \\ rpt conj_tac \\ unabbrev_all_tac \\ xsimpl
  \\ simp [DOUBLE_def, set_sepTheory.SEP_CLAUSES]
QED

Theorem cf_fpfromword_var:
  ∀ env.
  nsLookup env.v x = SOME (Litv (Word64 w)) ⇒
  cf_fpfromword (Var x) env (STDIO fs)
  (POSTv v. &DOUBLE (Fp_const w) v * STDIO fs)
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘cf_fpfromword _ _ _ Post’
  \\ fs[cf_fpfromword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
         cfTheory.app_fpfromword_def]
  \\ rpt strip_tac
  \\ qexists_tac ‘STDIO fs’ \\ qexists_tac ‘emp’
  \\ qexists_tac ‘Post’ \\ rpt conj_tac \\ unabbrev_all_tac \\ xsimpl
  \\ simp [DOUBLE_def, set_sepTheory.SEP_CLAUSES]
QED

Theorem fromstring_spec:
  STRING_TYPE s vs ⇒
  app p ^(fetch_v "Int.fromString" st) [vs]
  (emp) (POSTv uv. &(OPTION_TYPE INT (fromString s) uv))
Proof
  fs[app_def] \\ rpt strip_tac
  \\ assume_tac IntProgTheory.fromstring_v_thm
  \\ assume_tac (GEN_ALL (INST_TYPE [“:'a” |-> “:mlstring”,“:'b”|->“:int option”, “:'ffi” |-> “:'a”] Arrow_IMP_app_basic))
  \\ first_x_assum (qspecl_then [‘IntProg$fromstring_v’, ‘p’, ‘fromString’, ‘OPTION_TYPE INT’, ‘STRING_TYPE’] mp_tac)
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ res_tac
QED

Theorem valof_spec:
  OPTION_TYPE INT io ov ∧
  io = SOME i ⇒
  app p ^(fetch_v "Option.valOf" st) [ov]
  (emp) (POSTv uv. &(INT i uv))
Proof
  fs[app_def] \\ rpt strip_tac
  \\ qspecl_then [‘io’, ‘INT’] assume_tac (GEN_ALL OptionProgTheory.the_v_thm)
  \\ rfs[PRECONDITION_def, optionTheory.IS_SOME_DEF, Eq_def]
  \\ assume_tac (GEN_ALL (INST_TYPE [“:'a” |-> “:int option”,“:'b”|->“:int”, “:'ffi” |-> “:'a”] Arrow_IMP_app_basic))
  \\ first_x_assum (qspecl_then [‘the_v’, ‘p’, ‘THE’, ‘INT’] mp_tac)
  \\ disch_then drule
  \\ disch_then (qspecl_then [‘io’, ‘ov’] mp_tac)
  \\ impl_tac \\ fs[]
QED

Theorem word64_fromint_spec:
  INT i iv ∧ 0 ≤ i ⇒
  app p ^(fetch_v "Word64.fromInt" st) [iv]
  (emp) (POSTv uv. &(WORD ((n2w (Num i)):word64) uv))
Proof
  fs[app_def] \\ rpt strip_tac
  \\ assume_tac Word64ProgTheory.word64_fromint_v_thm
  \\ assume_tac (GEN_ALL (INST_TYPE [“:'a” |-> “:num”,“:'b”|->“:word64”, “:'ffi” |-> “:'a”] Arrow_IMP_app_basic))
  \\ first_x_assum (qspecl_then [‘word64_fromint_v’, ‘p’, ‘n2w’, ‘WORD’, ‘NUM’] mp_tac)
  \\ impl_tac \\ fs[]
  \\ disch_then (qspecl_then [‘Num i’, ‘iv’] mp_tac)
  \\ impl_tac \\ fs[NUM_def, INT_def]
  \\ qspec_then ‘i’ (simp o single o snd o EQ_IMP_RULE) integerTheory.INT_OF_NUM
QED

Theorem intToFP_spec:
  STRING_TYPE s sv ∧
  fromString s = SOME i ∧
  0 ≤ i ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "intToFP" st)
  [sv]
  (STDIO fs)
  (POSTv uv. &DOUBLE (Fp_const ((n2w (Num i)):word64)) uv * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "intToFP" st
  \\ xlet_auto_spec (SOME fromstring_spec) >- xsimpl
  \\ xlet_auto_spec (SOME valof_spec) >- xsimpl
  \\ xlet_auto_spec (SOME word64_fromint_spec) >- xsimpl
  \\ qmatch_goalsub_abbrev_tac ‘cf_fpfromword _ _ _ Post’
  \\ fs[cf_fpfromword_def, cfHeapsTheory.local_def, cfNormaliseTheory.exp2v_def,
         cfTheory.app_fpfromword_def]
  \\ rpt strip_tac
  \\ fs[set_sepTheory.STAR_def, PULL_EXISTS, set_sepTheory.cond_def]
  \\ qexists_tac ‘&WORD ((n2w (Num i)):word64) uv'’
  \\ qexists_tac ‘STDIO fs’
  \\ qexists_tac ‘POSTv uv. &(DOUBLE (Fp_const ((n2w (Num i)):word64)) uv)’
  \\ rpt conj_tac \\ unabbrev_all_tac \\ xsimpl
  \\ qexists_tac ‘EMPTY’ \\ qexists_tac ‘u’
  \\ fs[WORD_def, set_sepTheory.cond_def, SPLIT_def, set_sepTheory.STAR_def]
  \\ rpt conj_tac \\ rveq \\ unabbrev_all_tac \\ xsimpl
  \\ simp [DOUBLE_def, set_sepTheory.SEP_CLAUSES, set_sepTheory.SEP_IMP_def]
  \\ rpt strip_tac \\ qexists_tac ‘s'’ \\ qexists_tac ‘EMPTY’ \\ fs[GC_def]
  \\ fs[set_sepTheory.SEP_EXISTS] \\ qexists_tac ‘emp’ \\ fs[emp_def]
QED

Theorem reader1_spec:
  2 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader1" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(STRING_TYPE (HD (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader1" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` ListProgTheory.hd_v_thm))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute] \\ xsimpl
QED

Theorem reader2_spec:
  3 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader2" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv.
    &(PAIR_TYPE STRING_TYPE STRING_TYPE (list2tup2 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader2" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup2_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup2_side_def"]
  \\ xsimpl
QED

Theorem reader3_spec:
  4 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader3" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR3_TYPE STRING_TYPE (list2tup3 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader3" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup3_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup3_side_def"]
  \\ xsimpl
QED

Theorem reader4_spec:
  5 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader4" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR4_TYPE STRING_TYPE (list2tup4 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader4" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup4_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup4_side_def"]
  \\ xsimpl
QED

Theorem reader6_spec:
  7 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader6" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR6_TYPE STRING_TYPE (list2tup6 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader6" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup6_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup6_side_def"]
  \\ xsimpl
QED

Theorem reader8_spec:
  9 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader8" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR8_TYPE STRING_TYPE (list2tup8 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader8" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup8_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup8_side_def"]
  \\ xsimpl
QED

Theorem reader9_spec:
  10 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app (p: 'ffi ffi_proj) ^(fetch_v "reader9" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR9_TYPE STRING_TYPE (list2tup9 (TL cl)) uv) * STDIO fs)
Proof
  rpt strip_tac
  \\ xcf "reader9" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp_spec (Q.ISPEC `STRING_TYPE` (Q.GEN `a` (fetch "-" "list2tup9_v_thm")))
  \\ first_assum (irule_at Any)
  \\ gvs [LENGTH_EQ_NUM_compute, fetch "-" "list2tup9_side_def"]
  \\ xsimpl
QED

Theorem printer_spec:
  WORD (w:word64) v ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "printer" st)
    [v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (mlint$toString (&w2n w))))
Proof
  rpt strip_tac
  \\ xcf "printer" st
  \\ xlet_auto
  >- (xsimpl)
  \\ xlet_auto
  >- (xsimpl)
  \\ xapp \\ xsimpl
QED

