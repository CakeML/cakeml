(**
  Support lemmas for CF reasoning
**)
open basis_ffiTheory cfHeapsBaseTheory basis;
open cfTacticsLib ml_translatorLib;
open source_to_sourceTheory CakeMLtoFloVerTheory CakeMLtoFloVerProofsTheory;
open preamble;

val _ = new_theory "cfSupport";

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
       (empty_state with fp_state := empty_state.fp_state with real_sem := T)
       (env with v :=
         toRspace (extend_env_with_vars (REVERSE fvars) (REVERSE vs) env.v))
       [realify body] of
    | (st, Rval [Real r]) => r
End

(**
   fun reader3 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   in (cst1, (cst2, cst3)) end;
**)
Definition reader3_def:
  reader3 =
  [Dletrec
   (Locs <|row := 2; col := 4; offset := 0|>
    <|row := 8; col := 30; offset := 0|>)
   [("reader3","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (Con NONE
                  [Var (Short "cst2");
                   Var (Short "cst3")])
                 (Con NONE
                  [Var (Short "cst1"); Var (Short "e")]))))))))))]]
End

val _ = append_prog (reader3_def |> concl |> rhs);

(**
   fun reader4 u =
   let
   val cl = CommandLine.arguments ();
   val cst1 = List.hd cl;
   val cst2 = List.hd (List.tl cl);
   val cst3 = List.hd (List.tl (List.tl cl));
   val cst4 = List.hd (List.tl (List.tl (List.tl cl)));
   in (cst1, (cst2, (cst3, cst4))) end;
**)
Definition reader4_def:
  reader4 =
  [Dletrec
   (Locs <|row := 2; col := 4; offset := 0|>
    <|row := 9; col := 38; offset := 0|>)
   [("reader4","u",
     Let (SOME "a") (Con NONE [])
         (Let (SOME "cl")
          (App Opapp
           [Var (Long "CommandLine" (Short "arguments"));
            Var (Short "a")])
          (Let (SOME "cst1")
           (App Opapp
            [Var (Long "List" (Short "hd")); Var (Short "cl")])
           (Let (SOME "b")
            (App Opapp
             [Var (Long "List" (Short "tl")); Var (Short "cl")])
            (Let (SOME "cst2")
             (App Opapp
              [Var (Long "List" (Short "hd")); Var (Short "b")])
             (Let (SOME "c")
              (App Opapp
               [Var (Long "List" (Short "tl"));
                Var (Short "cl")])
              (Let (SOME "d")
               (App Opapp
                [Var (Long "List" (Short "tl"));
                 Var (Short "c")])
               (Let (SOME "cst3")
                (App Opapp
                 [Var (Long "List" (Short "hd"));
                  Var (Short "d")])
                (Let (SOME "e")
                 (App Opapp
                  [Var (Long "List" (Short "tl"));
                   Var (Short "cl")])
                 (Let (SOME "f")
                  (App Opapp
                   [Var (Long "List" (Short "tl"));
                    Var (Short "e")])
                  (Let (SOME "g")
                   (App Opapp
                    [Var (Long "List" (Short "tl"));
                     Var (Short "f")])
                   (Let (SOME "cst4")
                    (App Opapp
                     [Var
                      (Long "List" (Short "hd"));
                      Var (Short "g")])
                    (Let (SOME "h")
                     (Con NONE
                      [Var (Short "cst3");
                       Var (Short "cst4")])
                     (Let (SOME "i")
                      (Con NONE
                       [Var (Short "cst2");
                        Var (Short "h")])
                      (Con NONE
                       [Var (Short "cst1");
                        Var (Short "i")])))))))))))))))]]
End

val _ = append_prog (reader4_def |> concl |> rhs);

Definition printer_def:
  printer =
  [Dlet unknown_loc (Pvar "printer")
    (Fun "x"
     (Let (SOME "z")
      (App Opapp [
         Var (Long "Word64" (Short "toInt"));
         Var (Short "x")])
      (Let (SOME "y")
       (App Opapp [
          Var (Long "Int" (Short "toString"));
          Var (Short "z")])
       (App Opapp [
          Var (Long "TextIO" (Short "print"));
          Var (Short "y")]))))]
End

val _ = append_prog (printer_def |> concl |> rhs);

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

Theorem hd_spec:
  LIST_TYPE STRING_TYPE xs vs ∧
  xs ≠ [] ⇒
  app p ^(fetch_v "List.hd" st) [vs]
  (emp) (POSTv uv. &STRING_TYPE (HD xs) uv)
Proof
  fs[app_def] \\ rpt strip_tac
  \\ assume_tac (GEN_ALL (Q.ISPEC ‘STRING_TYPE’ (Q.GEN ‘a’ ListProgTheory.hd_v_thm)))
  \\ first_x_assum (qspec_then ‘xs’ assume_tac) \\ fs[PRECONDITION_def]
  \\ res_tac
  \\ fs[Eq_def]
  \\ assume_tac
     (GEN_ALL
      (INST_TYPE [“:'a” |-> “:mlstring list”,“:'b”|->“:mlstring”, “:'ffi” |-> “:'a”]
       Arrow_IMP_app_basic))
  \\ first_x_assum (qspecl_then [‘hd_v’, ‘p’, ‘HD’, ‘STRING_TYPE’] assume_tac)
  \\ res_tac
  \\ first_x_assum (qspecl_then [‘xs’, ‘vs’] irule)
  \\ fs[]
QED

Theorem tl_spec:
  LIST_TYPE STRING_TYPE xs vs ∧
  xs ≠ [] ⇒
  app p ^(fetch_v "List.tl" st) [vs]
  (emp) (POSTv uv. &LIST_TYPE STRING_TYPE (TL xs) uv)
Proof
  fs[app_def] \\ rpt strip_tac
  \\ assume_tac (GEN_ALL (Q.ISPEC ‘STRING_TYPE’ (Q.GEN ‘a’ ListProgTheory.tl_v_thm)))
  \\ assume_tac (GEN_ALL (INST_TYPE [“:'a” |-> “:mlstring list”,“:'b”|->“:mlstring list”, “:'ffi” |-> “:'a”] Arrow_IMP_app_basic))
  \\ first_x_assum (qspecl_then [‘tl_v’, ‘p’, ‘TL’, ‘LIST_TYPE STRING_TYPE’] assume_tac)
  \\ res_tac
QED

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
   >- (
    simp[set_sepTheory.STAR_def] \\ qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’
    \\ fs[SPLIT_def, emp_def])
   \\ fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
   \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
   \\ unabbrev_all_tac \\ fs[SPLIT_def]
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
   >- (
    simp[set_sepTheory.STAR_def] \\ qexists_tac ‘h’ \\ qexists_tac ‘EMPTY’
    \\ fs[SPLIT_def, emp_def])
   \\ fs[DOUBLE_def, set_sepTheory.SEP_IMP_def]
   \\ rpt strip_tac \\ fs[set_sepTheory.cond_def, set_sepTheory.STAR_def]
   \\ unabbrev_all_tac \\ fs[SPLIT_def]
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
  app p ^(fetch_v "intToFP" st)
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
  >- fs[DOUBLE_def]
  \\ rpt strip_tac \\ fs[set_sepTheory.SEP_IMP_def]
  \\ rpt strip_tac \\ fs[]
  \\ qexists_tac ‘s'’ \\ qexists_tac ‘EMPTY’ \\ fs[GC_def]
  \\ fs[set_sepTheory.SEP_EXISTS] \\ qexists_tac ‘emp’ \\ fs[emp_def]
QED

Theorem reader3_spec:
  4 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app p ^(fetch_v "reader3" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv. &(PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE STRING_TYPE) (HD(TL cl), (HD (TL (TL cl)), HD (TL (TL (TL cl))))) uv) * STDIO fs)
Proof
  xcf "reader3" st
  \\ reverse (Cases_on`STD_streams fs`) >-(fs[STDIO_def] \\ xpull)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ ‘~ NULL cl’ by fs[wfcl_def,NULL_EQ]
  \\ xlet_auto >- xsimpl
  \\ ‘cl ≠ []’ by (Cases_on ‘cl’ \\ fs[])
  \\ ‘TL cl ≠ []’ by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec)
  >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ ‘TL (TL cl) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ xlet_auto_spec (SOME tl_spec) >- (xsimpl)
  \\ ‘TL (TL (TL cl)) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- (xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ fs[PAIR_TYPE_def]
QED

Theorem reader4_spec:
  5 = LENGTH cl ∧
  UNIT_TYPE () uv ⇒
  app p ^(fetch_v "reader4" st)
  [uv]
  (STDIO fs * COMMANDLINE cl)
  (POSTv uv.
    &(PAIR_TYPE STRING_TYPE
      (PAIR_TYPE STRING_TYPE
       (PAIR_TYPE STRING_TYPE STRING_TYPE))
       (HD(TL cl), (HD (TL (TL cl)), HD (TL (TL (TL cl))), HD (TL (TL (TL (TL cl))))))
       uv) * STDIO fs)
Proof
  xcf "reader4" st
  \\ reverse (Cases_on`STD_streams fs`) >-(fs[STDIO_def] \\ xpull)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)
  \\ ‘~ NULL cl’ by fs[wfcl_def,NULL_EQ]
  \\ xlet_auto >- xsimpl
  \\ ‘cl ≠ []’ by (Cases_on ‘cl’ \\ fs[])
  \\ ‘TL cl ≠ []’ by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec)
  >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ ‘TL (TL cl) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ ‘TL (TL (TL cl)) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[] \\ Cases_on ‘t’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ xlet_auto_spec (SOME tl_spec) >- xsimpl
  \\ ‘TL (TL (TL (TL cl))) ≠ []’
     by (Cases_on ‘cl’ \\ fs[] \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[]
         \\ Cases_on ‘t’ \\ fs[] \\ Cases_on ‘t'’ \\ fs[])
  \\ xlet_auto_spec (SOME hd_spec) >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xcon \\ xsimpl
  \\ fs[PAIR_TYPE_def]
QED

Theorem printer_spec:
  WORD (w:word64) v ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "printer" st)
    [v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (mlint$toString (&w2n w))))
Proof
  xcf "printer" st
  \\ xlet_auto
  >- (xsimpl)
  \\ xlet_auto
  >- (xsimpl)
  \\ xapp \\ xsimpl
QED

val _ = export_theory();
