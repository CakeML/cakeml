(*
  Correctness proof for the Dafny to CakeML compiler.
*)
Theory dafny_to_cakemlProof
Ancestors
  ast semanticPrimitives evaluate evaluateProps ffi
  dafny_misc  (* OPT_MMAP_LENGTH *)
  dafnyProps dafny_semanticPrimitives dafny_evaluate dafny_evaluateProps
  namespace namespaceProps mlstring integer mlint result_monad
  dafny_freshenProof dafny_to_cakeml dafny_ast
Libs
  preamble

(* TODO Remove unused definition / trivialities *)

Type dfy_state[pp] = “:dafny_semanticPrimitives$state”
Type dfy_env[pp] = “:dafny_semanticPrimitives$sem_env”
Type dfy_exp[pp] = “:dafny_ast$exp”
Type dfy_exp_res[pp] = “:'a dafny_semanticPrimitives$exp_result”

Type cml_state[pp] = “:'ffi semanticPrimitives$state”
Type cml_env[pp] = “:v semanticPrimitives$sem_env”
Type cml_envc[pp] = “:(mlstring, mlstring, num # stamp) namespace”
Type cml_exp[pp] = “:ast$exp”
Type cml_res[pp] = “:(v list, v) semanticPrimitives$result”
Type cml_ns[pp] = “:(mlstring, mlstring, v) namespace”

(* Some general simps *)

(* TODO Better way of writing this? Perhaps using state_fupdcanon? *)
Theorem with_same_refs_ffi[local,simp]:
  (t: 'ffi cml_state) with <| refs := t.refs; ffi := t.ffi |> = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem with_same_ffi[local,simp]:
  (t: 'ffi cml_state) with <| clock := c; refs := r; ffi := t.ffi |> =
  t with <| clock := c; refs := r |>
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem with_same_ffi1[local,simp]:
  (t: 'ffi cml_state) with <| refs := r; ffi := t.ffi |> =
  t with <| refs := r |>
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem with_same_clock[local,simp]:
  (t: 'ffi cml_state) with clock := t.clock = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Theorem with_same_refs[local,simp]:
  s with refs := s.refs = s
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

(* TODO Check if needed; add to namespaceTheory? *)
Theorem nsAppend_empty[local,simp]:
  nsAppend (Bind [] []) b = b
Proof
  Cases_on ‘b’ \\ gvs [nsAppend_def]
QED

Theorem value_has_type_bool[local,simp]:
  value_has_type BoolT v ⇔ ∃b. v = BoolV b
Proof
  Cases_on ‘v’ \\ simp []
QED

Theorem value_has_type_str[local,simp]:
  value_has_type StrT v ⇔ ∃s. v = StrV s
Proof
  Cases_on ‘v’ \\ simp []
QED

Theorem value_has_type_int[local,simp]:
  value_has_type IntT v ⇔ ∃i. v = IntV i
Proof
  Cases_on ‘v’ \\ simp []
QED

(* Proving our to_string functions correct *)

Definition cml_dec_to_string_clos_def:
  cml_dec_to_string_clos env =
    Closure env cml_dec_to_string_param cml_dec_to_string_body
End

Definition dec_to_string_def:
  dec_to_string n = str (CHR (48 + n))
End

Definition has_list_cons_def:
  has_list_cons env ⇔
    nsLookup env.c (Short «[]») = SOME (0, TypeStamp «[]» list_type_num) ∧
    nsLookup env.c (Short «::») = SOME (2, TypeStamp «::» list_type_num)
End

Theorem cml_dec_to_string_correct:
  ∀s env e clos_env s₁ n.
    evaluate s env [e] = (s₁, Rval [Litv (IntLit &n)]) ∧ n < 10 ∧
    nsLookup env.v (Short cml_dec_to_string_name) =
      SOME (cml_dec_to_string_clos clos_env) ∧ has_list_cons clos_env ⇒
    ∃ck.
      evaluate (s with clock := s.clock + ck) env
               [App Opapp [Var (Short cml_dec_to_string_name); e]] =
      (s₁, Rval [Litv (StrLit (dec_to_string n))])
Proof
  simp [has_list_cons_def] \\ rpt strip_tac
  \\ qexists ‘1’
  \\ drule evaluate_add_to_clock
  \\ disch_then $ qspec_then ‘1’ assume_tac \\ gvs []
  \\ simp [evaluate_def, cml_dec_to_string_clos_def, do_opapp_def,
           evaluateTheory.dec_clock_def]
  \\ simp [cml_dec_to_string_body_def, cml_list_def, evaluate_def, do_conversion_def,
           do_con_check_def, build_conv_def, do_app_def, do_arith_def, check_type_def]
  \\ ‘¬((48: int) + &n < 0 ∨ (48: int) + &n > 255)’ by (intLib.COOPER_TAC)
  \\ simp [v_to_char_list_def]
  \\ gvs [dec_to_string_def, str_def]
  \\ AP_TERM_TAC \\ AP_THM_TAC \\ ntac 2 AP_TERM_TAC
  \\ intLib.COOPER_TAC
QED

Definition cml_nat_to_string_clos_def:
  cml_nat_to_string_clos env =
    Recclosure env
     [(cml_nat_to_string_name, cml_nat_to_string_param, cml_nat_to_string_body)]
     cml_nat_to_string_name
End

Definition nat_to_string_def:
  nat_to_string n =
  if n < 10 then dec_to_string n
  else nat_to_string (n DIV 10) ^ dec_to_string (n MOD 10)
End

Theorem evaluate_Strcat[local]:
  evaluate s env [re] = (s₁, Rval [Litv (StrLit rs)]) ∧
  evaluate s₁ env [le] = (s₂, Rval [Litv (StrLit ls)]) ∧
  has_list_cons env
  ⇒
  evaluate s env [App Strcat [cml_list [le; re]]] =
    (s₂, Rval [Litv (StrLit (ls ^ rs))])
Proof
  simp [has_list_cons_def] \\ rpt strip_tac
  \\ simp [evaluate_def, cml_list_def, do_con_check_def,
           build_conv_def, do_app_def, v_to_list_def, vs_to_string_def]
QED

Theorem cml_nat_to_string_correct:
  ∀n s env e s₁ clos_env₀ clos_env₁.
    evaluate s env [e] = (s₁, Rval [Litv (IntLit &n)]) ∧
    nsLookup env.v (Short cml_nat_to_string_name) =
      SOME (cml_nat_to_string_clos clos_env₀) ∧
    has_list_cons clos_env₀ ∧
    nsLookup clos_env₀.v (Short cml_dec_to_string_name) =
      SOME (cml_dec_to_string_clos clos_env₁) ∧
    has_list_cons clos_env₁
    ⇒
    ∃ck.
      evaluate (s with clock := s.clock + ck) env
        [App Opapp [Var (Short cml_nat_to_string_name); e]] =
      (s₁, Rval [Litv (StrLit (nat_to_string n))])
Proof
  recInduct nat_to_string_ind
  \\ rpt strip_tac
  \\ qpat_x_assum ‘has_list_cons clos_env₀’ mp_tac
  \\ rewrite_tac [has_list_cons_def] \\ strip_tac
  \\ simp [evaluate_def, do_opapp_def]
  \\ dxrule_then assume_tac evaluate_add_to_clock \\ gvs []
  \\ simp [cml_nat_to_string_clos_def, Once find_recfun_def, build_rec_env_def]
  \\ qrefine ‘ck + 1’ \\ simp [evaluateTheory.dec_clock_def]
  \\ simp [evaluate_def, do_app_def, do_if_def, do_test_def,
           cml_nat_to_string_body_def]
  \\ IF_CASES_TAC \\ gvs []
  >- (* n < 10 *)
   (qmatch_goalsub_abbrev_tac ‘evaluate _ call_env [_ _ [_; arg]]’
    \\ qspecl_then [‘s₁’, ‘call_env’, ‘arg’, ‘clos_env₁’, ‘s₁’, ‘n’] mp_tac
         cml_dec_to_string_correct
    \\ impl_tac >-
     (unabbrev_all_tac \\ simp [evaluate_def])
    \\ simp [Once nat_to_string_def])
  (* ¬(n < 10) *)
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env’
  \\ qmatch_goalsub_abbrev_tac
       ‘cml_list [_ _ [_; arg_div_10]; _ _ [_; arg_mod_10]]’
  \\ qspecl_then [‘s₁’, ‘call_env’, ‘arg_mod_10’, ‘clos_env₁’, ‘s₁’, ‘n MOD 10’]
        mp_tac cml_dec_to_string_correct
  \\ impl_tac >-
   (unabbrev_all_tac
    \\ simp [evaluate_def, do_app_def, do_arith_def, check_type_def])
  \\ disch_then $ qx_choose_then ‘ck’ assume_tac
  \\ last_x_assum $
       qspecl_then
         [‘s₁’, ‘call_env’, ‘arg_div_10’, ‘s₁’, ‘clos_env₀’, ‘clos_env₁’] mp_tac
  \\ impl_tac >-
   (unabbrev_all_tac
    \\ simp [cml_nat_to_string_clos_def, cml_nat_to_string_body_def]
    \\ simp [has_list_cons_def]
    \\ simp [evaluate_def, do_app_def, do_arith_def, check_type_def])
  \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac
  \\ rev_drule evaluate_add_to_clock
  \\ disch_then $ qspec_then ‘ck₁’ assume_tac \\ gvs []
  \\ qexists ‘ck + ck₁’
  \\ simp [Once nat_to_string_def]
  \\ irule evaluate_Strcat \\ simp []
  \\ unabbrev_all_tac \\ simp [has_list_cons_def]
QED

Definition cml_int_to_string_clos_def:
  cml_int_to_string_clos env =
    Closure env cml_int_to_string_param cml_int_to_string_body
End

Definition int_to_string_def:
  int_to_string (i: int) =
    if i < 0 then («-» ^ nat_to_string (Num (-i))) else nat_to_string (Num i)
End

Definition int_to_string_env_def:
  int_to_string_env clos_env ⇔
    ∃clos_env₁ clos_env₂.
      has_list_cons clos_env ∧
      nsLookup clos_env.v (Short cml_nat_to_string_name) =
        SOME (cml_nat_to_string_clos clos_env₁) ∧
      has_list_cons clos_env₁ ∧
      nsLookup clos_env₁.v (Short cml_dec_to_string_name) =
        SOME (cml_dec_to_string_clos clos_env₂) ∧
      has_list_cons clos_env₂
End

Theorem cml_int_to_string_correct:
  ∀s env e s₁ i clos_env₀ clos_env₁ clos_env₂.
    evaluate s env [e] = (s₁, Rval [Litv (IntLit i)]) ∧
    nsLookup env.v (Short cml_int_to_string_name) =
      SOME (cml_int_to_string_clos clos_env₀) ∧
    int_to_string_env clos_env₀
    ⇒
    ∃ck.
      evaluate (s with clock := s.clock + ck) env
               [App Opapp [Var (Short cml_int_to_string_name); e]] =
      (s₁, Rval [Litv (StrLit (int_to_string i))])
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘int_to_string_env _’ mp_tac
  \\ simp [int_to_string_env_def, PULL_EXISTS]
  \\ qx_genl_tac [‘clos_env₁’, ‘clos_env₂’]
  \\ strip_tac
  \\ qrefine ‘ck + 1’
  \\ drule evaluate_add_to_clock \\ simp []
  \\ disch_then $ qspec_then ‘1’ assume_tac
  \\ dxrule_then assume_tac evaluate_add_to_clock \\ gvs []
  \\ simp [evaluate_def, cml_int_to_string_clos_def, do_opapp_def,
           evaluateTheory.dec_clock_def]
  \\ simp [cml_int_to_string_body_def, evaluate_def, do_app_def, do_if_def,
           do_test_def]
  \\ simp [int_to_string_def]
  \\ reverse IF_CASES_TAC \\ gvs []
  >-
   (qmatch_goalsub_abbrev_tac ‘evaluate _ call_env [_ _ [_; arg]]’
    \\ qspecl_then
         [‘Num i’, ‘s₁’, ‘call_env’, ‘arg’, ‘s₁’, ‘clos_env₁’, ‘clos_env₂’] mp_tac
         cml_nat_to_string_correct
    \\ impl_tac >-
     (unabbrev_all_tac \\ simp [evaluate_def] \\ intLib.COOPER_TAC)
    \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env’
  \\ qmatch_goalsub_abbrev_tac ‘App Opapp [_; arg]’
  \\ qspecl_then
     [‘Num (-i)’, ‘s₁’, ‘call_env’, ‘arg’, ‘s₁’, ‘clos_env₁’, ‘clos_env₂’] mp_tac
       cml_nat_to_string_correct
  \\ impl_tac >-
   (unabbrev_all_tac \\ simp [evaluate_def, do_app_def, do_arith_def, check_type_def])
  \\ disch_then $ qx_choose_then ‘ck’ assume_tac
  \\ qexists ‘ck’
  \\ irule evaluate_Strcat \\ gvs []
  \\ gvs [Abbr ‘call_env’, has_list_cons_def]
  \\ simp [evaluate_def]
QED

Theorem Stuple_Tuple[local]:
  LENGTH xs ≠ 1 ⇒ Stuple xs = Tuple xs
Proof
  namedCases_on ‘xs’ ["", "x xs'"]
  \\ gvs [Stuple_def]
  \\ namedCases_on ‘xs'’ ["", "x' xs''"]
  \\ gvs [Stuple_def]
QED

Theorem Pstuple_Tuple[local]:
  LENGTH xs ≠ 1 ⇒ Pstuple xs = Pcon NONE xs
Proof
  namedCases_on ‘xs’ ["", "x xs'"]
  \\ gvs [Pstuple_def]
  \\ namedCases_on ‘xs'’ ["", "x' xs''"]
  \\ gvs [Pstuple_def]
QED

Theorem is_fresh_neq[local,simp]:
  is_fresh n ∧ ¬is_fresh n' ⇒ n ≠ n'
Proof
  rpt strip_tac \\ gvs [is_fresh_def]
QED

(* TODO Upstream these? Most likely will break things. *)
Theorem nsOptBind_some_simp[local,simp]:
  nsOptBind (SOME n) x env = nsBind n x env
Proof
  gvs [nsOptBind_def]
QED

Theorem nsOptBind_none_simp[local,simp]:
  nsOptBind NONE x env = env
Proof
  gvs [nsOptBind_def]
QED

Theorem no_shadow_evaluate_exp[local]:
  no_shadow (set (MAP FST s.locals)) stmt ∧
  evaluate_exp s env stmt' = (s', r) ⇒
  no_shadow (set (MAP FST s'.locals)) stmt
Proof
  rpt strip_tac
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

Theorem no_shadow_evaluate_stmt[local]:
  no_shadow (set (MAP FST s.locals)) stmt ∧
  evaluate_stmt s env stmt' = (s', r) ⇒
  no_shadow (set (MAP FST s'.locals)) stmt
Proof
  rpt strip_tac \\ drule evaluate_stmt_locals \\ gvs []
QED

Definition ret_stamp_def:
  ret_stamp = ExnStamp 4
End

Definition is_ret_exn_def[simp]:
  is_ret_exn val ⇔ val = Conv (SOME ret_stamp) []
End

Definition has_cons_def:
  has_cons (envc: cml_envc) ⇔
    nsLookup envc (Short «True») = SOME (0, TypeStamp «True» 0) ∧
    nsLookup envc (Short «False») = SOME (0, TypeStamp «False» 0) ∧
    nsLookup envc (Short «Return») = SOME (0, ret_stamp)
End

(* TODO Move to dafny_ast? *)
Definition dest_program_def:
  dest_program (Program members) = members
End


(* assert-statements should be ignored by the compiler *)
Definition no_assert_stmt_def:
  (no_assert_stmt (Assert _) ⇔ F) ∧
  (no_assert_stmt (Then stmt₁ stmt₂) ⇔
     no_assert_stmt stmt₁ ∧ no_assert_stmt stmt₂) ∧
  (no_assert_stmt (If _ stmt₁ stmt₂) ⇔
     no_assert_stmt stmt₁ ∧ no_assert_stmt stmt₂) ∧
  (no_assert_stmt (Dec _ body) ⇔ no_assert_stmt body) ∧
  (no_assert_stmt (While _ _ _ _ body) ⇔ no_assert_stmt body) ∧
  (no_assert_stmt _ ⇔ T)
End

Definition no_assert_member_def:
  (no_assert_member (Method _ _ _ _ _ _ _ _ stmt) = no_assert_stmt stmt) ∧
  (no_assert_member _ = T)
End

Inductive callable_rel:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_cons env.c ∧
  nsLookup env.v (Short cml_int_to_string_name) =
    SOME (cml_int_to_string_clos clos_env) ∧
  int_to_string_env clos_env
  ⇒
  callable_rel prog name (Recclosure env cml_funs («dfy_» ^ name))
End

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    has_cons env_cml.c ∧
    (∃clos_env.
       nsLookup env_cml.v (Short cml_int_to_string_name) =
         SOME (cml_int_to_string_clos clos_env) ∧
       int_to_string_env clos_env) ∧
    ∀name member.
      get_member name env_dfy.prog = SOME member ⇒
      is_fresh_member member ∧
      no_shadow_method member ∧
      no_assert_member member ∧
      ∃reclos.
        nsLookup env_cml.v (Short («dfy_» ^ name)) = SOME reclos ∧
        callable_rel env_dfy.prog name reclos
End

Inductive val_rel:
[~bool:]
  val_rel m (BoolV b) (Boolv b)
[~int:]
  val_rel m (IntV i) (Litv (IntLit i))
[~str:]
  val_rel m (StrV s) (Litv (StrLit s))
[~arr:]
  FLOOKUP m loc = SOME loc' ⇒
  val_rel m (ArrV len loc ty) (Conv NONE [Litv (IntLit (&len)); Loc T loc'])
End

Theorem val_rel_simp[simp] = LIST_CONJ $
  map (SCONV [val_rel_cases]) [“val_rel m (BoolV b) v”,
                               “val_rel m (IntV i) v”,
                               “val_rel m (StrV s) v”,
                               “val_rel m (ArrV len loc ty) v”];

Definition array_rel_def:
  array_rel m s_heap c_store ⇔
    INJ (λx. m ' x) (FDOM m) 𝕌(:num) ∧
    (∀i. i ∈ FDOM m ⇒ i < LENGTH s_heap) ∧
    (∀i. i ∈ FRANGE m ⇒
         i < LENGTH c_store ∧
         ∃vs. store_lookup i c_store = SOME (Varray vs)) ∧
    ∀loc vs ty.
      LLOOKUP s_heap loc = SOME (HArr vs ty) ⇒
      ∃loc' vs'.
        FLOOKUP m loc = SOME loc' ∧
        store_lookup loc' c_store = SOME (Varray vs') ∧
        LIST_REL (val_rel m) vs vs'
End

Definition locals_rel_def:
  locals_rel m (l: mlstring |-> num) s_locals t_refs (env_v: cml_ns) ⇔
    INJ (λx. l ' x) (FDOM l) 𝕌(:num) ∧
    (∀i. i ∈ FRANGE l ⇒ i < LENGTH t_refs) ∧
    ∀var dfy_ov.
      (* dfy_v may be uninitialized *)
      ALOOKUP s_locals var = SOME dfy_ov ∧
      is_fresh var ⇒
      ∃loc cml_v.
        FLOOKUP l var = SOME loc ∧
        (* locals map to references in CakeML *)
        store_lookup loc t_refs = SOME (Refv cml_v) ∧
        nsLookup env_v (Short var) = SOME (Loc T loc) ∧
        (∀dfy_v. dfy_ov = SOME dfy_v ⇒ val_rel m dfy_v cml_v)
End

Definition state_rel_def:
  state_rel m l s (t: 'ffi cml_state) cml_env ⇔
    s.clock = t.clock ∧
    array_rel m s.heap t.refs ∧
    locals_rel m l s.locals t.refs cml_env.v
End

(* TODO (?) Instead of mentioning what is preserved, it may have made more
 * sense to make the correctness lemmas mention what is changed, e.g.,
   ∃refs ck.
     ... = (t with <| refs := refs; clock := ck |>
   Changing this at this point sounds a bit tedious, so I will leave this for a
   future larger refactor (TM). *)
Definition cml_state_preserved_def:
  cml_state_preserved t t' ⇔
    t'.ffi = t.ffi ∧ t'.next_type_stamp = t.next_type_stamp ∧
    t'.next_exn_stamp = t.next_exn_stamp ∧ t'.eval_state = t.eval_state
End

Theorem cml_state_preserved_refl[local,simp]:
  cml_state_preserved t t
Proof
  simp [cml_state_preserved_def]
QED

Definition exp_res_rel_def[simp]:
  (exp_res_rel m (Rval dfy_v) (Rval [cml_v]) ⇔ val_rel m dfy_v cml_v) ∧
  (exp_res_rel m (Rerr Rtimeout) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_res_rel _ _ _ ⇔ F)
End

Theorem exp_res_rel_rval[local,simp]:
  exp_res_rel m (Rval dfy_v) r_cml ⇔
    ∃cml_v. r_cml = Rval [cml_v] ∧ val_rel m dfy_v cml_v
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘vs’ ["", "v rest"] \\ gvs []
  \\ Cases_on ‘rest’ \\ gvs []
QED

Theorem exp_res_rel_rerr[local,simp]:
  exp_res_rel m (Rerr dfy_err) r_cml ⇔
  dfy_err = Rtimeout ∧ r_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Definition exp_ress_rel_def[simp]:
  (exp_ress_rel m (Rval dfy_vs) (Rval cml_vs) ⇔
     LIST_REL (val_rel m) dfy_vs cml_vs) ∧
  (exp_ress_rel m (Rerr Rtimeout) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_ress_rel _ _ _ ⇔ F)
End

Theorem exp_ress_rel_rerr[local,simp]:
  exp_ress_rel m (Rerr dfy_err) rs_cml ⇔
  dfy_err = Rtimeout ∧ rs_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Theorem exp_ress_rel_rval[local,simp]:
  exp_ress_rel m (Rval dfy_vs) rs_cml ⇔
  ∃cml_vs. rs_cml = Rval cml_vs ∧ LIST_REL (val_rel m) dfy_vs cml_vs
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
QED

Definition stmt_res_rel_def[simp]:
  (stmt_res_rel Rcont (Rval _) ⇔ T) ∧
  (stmt_res_rel (Rstop Sret) (Rerr (Rraise val)) ⇔ is_ret_exn val) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout))
     (Rerr (Rabort Rtimeout_error)) ⇔ T) ∧
  (stmt_res_rel _ _ ⇔ F)
End

Theorem stmt_res_rel_simp[local,simp]:
  (stmt_res_rel Rcont r_cml ⇔
     ∃vs. r_cml = Rval vs) ∧
  (stmt_res_rel (Rstop Sret) r_cml ⇔
     ∃v. r_cml = Rerr (Rraise v) ∧ is_ret_exn v) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout)) r_cml ⇔
     r_cml = (Rerr (Rabort Rtimeout_error)))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["exn", "abrt"] \\ gvs []
  \\ Cases_on ‘abrt’ \\ gvs []
QED

Theorem read_local_some_imp[local]:
  read_local s.locals name = SOME dfy_v ∧
  state_rel m l s (t: 'ffi cml_state) env ∧
  is_fresh name ⇒
  ∃loc cml_v.
    FLOOKUP l name = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    val_rel m dfy_v cml_v ∧
    nsLookup env.v (Short name) = SOME (Loc T loc)
Proof
  gvs [state_rel_def, read_local_def, locals_rel_def, CaseEq "option"]
  \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rpt strip_tac
  \\ gvs []
QED

(* TODO Is there a better way to write these nsLookup lemmas? Maybe in a more
     general form? *)

(* TODO Upstream? *)
Theorem nslookup_nsbind[local,simp]:
  nsLookup (nsBind n v env) (Short n) = SOME v
Proof
  Cases_on ‘env’ \\ gvs [nsBind_def, nsLookup_def]
QED

(* TODO Upstream? *)
Theorem neq_nslookup_nsbind[local]:
  n ≠ n' ⇒
  nsLookup (nsBind n' v env) (Short n) = nsLookup env (Short n)
Proof
  Cases_on ‘env’ \\ gvs [nsBind_def, nsLookup_def]
QED

Theorem state_rel_env_push_not_fresh[local]:
  state_rel m l s (t: 'ffi cml_state) env ∧ ¬(is_fresh n) ⇒
  state_rel m l s t (env with v := (nsBind n v env.v))
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Theorem state_rel_env_pop_not_fresh[local]:
  ¬(is_fresh n) ∧
  state_rel m l s (t: 'ffi cml_state)
            (env with v := (nsBind n v env.v)) ⇒
  state_rel m l s t env
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Theorem is_fresh_not_dfy_pfx[local]:
  is_fresh n ⇒ n ≠ («dfy_» ^ sfx)
Proof
  Cases_on ‘n’ \\ simp [is_fresh_def, isprefix_thm]
QED

Theorem every_is_fresh_not_dfy[local]:
  EVERY (λn. is_fresh n) ns ⇒
  ∀sfx. EVERY (λn. n ≠ «dfy_» ^ sfx) ns
Proof
  simp [EVERY_MEM, MEM_MAP]
  \\ rpt strip_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ fs [is_fresh_def, isprefix_thm]
QED

Theorem every_is_fresh_not_int_to_string[local]:
  EVERY (λn. is_fresh n) ns ⇒
  EVERY (λn. n ≠ cml_int_to_string_name) ns
Proof
  simp [EVERY_MEM, MEM_MAP]
  \\ rpt strip_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ fs [is_fresh_def, isprefix_thm]
QED

Theorem locals_rel_env_change[local]:
  (∀n. is_fresh n ⇒
       nsLookup env_v (Short n) =
       nsLookup env_v' (Short n)) ∧
  locals_rel m l s_locals t_refs env_v ⇒
  locals_rel m l s_locals t_refs env_v'
Proof
  gvs [locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rpt (first_assum $ irule_at Any)
  \\ last_x_assum $ drule_then assume_tac
  \\ gvs []
QED

Theorem state_rel_env_change[local]:
  (∀n. is_fresh n ⇒
       nsLookup env.v (Short n) =
       nsLookup env'.v (Short n)) ∧
  state_rel m l s t env ⇒
  state_rel m l s t env'
Proof
  rpt strip_tac \\ gvs [state_rel_def]
  \\ irule locals_rel_env_change
  \\ last_assum $ irule_at Any \\ gvs []
QED

Theorem env_rel_env_change[local]:
  (∀n. isPrefix «dfy_» n ⇒
       nsLookup env_cml.v (Short n) = nsLookup env_cml'.v (Short n)) ∧
  (∃clos_env.
     nsLookup env_cml'.v (Short «int_to_string») =
     SOME (cml_int_to_string_clos clos_env) ∧ int_to_string_env clos_env) ∧
  has_cons env_cml'.c ∧
  env_rel env_dfy env_cml ⇒
  env_rel env_dfy env_cml'
Proof
  simp [env_rel_def, isprefix_strcat]
  \\ rpt strip_tac
  \\ first_x_assum drule \\ gvs []
QED

Theorem state_rel_llookup[local]:
  state_rel m l s t env ∧
  LLOOKUP s.heap dfy_loc = SOME (HArr dfy_arr ty) ∧
  FLOOKUP m dfy_loc = SOME cml_loc ⇒
  ∃cml_arr.
    store_lookup cml_loc t.refs = SOME (Varray cml_arr) ∧
    LIST_REL (val_rel m) dfy_arr cml_arr
Proof
  rpt strip_tac
  \\ gvs [state_rel_def, array_rel_def]
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
QED

Theorem find_recfun_some_aux[local]:
  ∀name members member cml_funs.
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    ∃cml_param cml_body.
      from_member_decl member =
        INR («dfy_» ^ name, cml_param, cml_body) ∧
      find_recfun («dfy_» ^ name) cml_funs =
        SOME (cml_param, cml_body)
Proof
  Induct_on ‘members’ \\ gvs [get_member_aux_def]
  \\ qx_genl_tac [‘member’, ‘name’] \\ rpt strip_tac
  \\ namedCases_on ‘member’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = name’ \\ gvs []
  \\ gvs [result_mmap_def, from_member_decl_def,
          set_up_cml_fun_def, oneline bind_def, CaseEq "sum"]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ simp [Once find_recfun_def]
QED

Theorem find_recfun_some[local]:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ⇒
  ∃cml_param cml_body.
    from_member_decl member =
      INR («dfy_» ^ name, cml_param, cml_body) ∧
    find_recfun («dfy_» ^ name) cml_funs =
      SOME (cml_param, cml_body)
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all find_recfun_some_aux \\ gvs []
QED

Theorem callable_rel_inversion[local]:
  callable_rel prog name reclos ⇒
  ∃clos_env env cml_funs member.
    reclos = (Recclosure env cml_funs («dfy_» ^ name)) ∧
    get_member name prog = SOME member ∧
    result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
    ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
    has_cons env.c ∧
    nsLookup env.v (Short cml_int_to_string_name) =
      SOME (cml_int_to_string_clos clos_env) ∧
    int_to_string_env clos_env
Proof
  rpt strip_tac \\ gvs [callable_rel_cases, SF SFY_ss]
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Theorem nsLookup_nsBind[local]:
  nsLookup (nsBind k x b) (Short k) = SOME x
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Theorem nsLookup_nsBind_neq[local]:
  k' ≠ k ⇒ nsLookup (nsBind k' x b) (Short k) = nsLookup b (Short k)
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Theorem nslookup_build_rec_env_reclos_aux[local]:
  ∀name members member cml_funs' cml_funs env (env₂_v: cml_ns).
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    nsLookup
      (FOLDR (λ(f,x,e) env₁. nsBind f (Recclosure env cml_funs' f) env₁)
             env₂_v cml_funs)
      (Short («dfy_» ^ name)) =
    SOME (Recclosure env cml_funs' («dfy_» ^ name))
Proof
  Induct_on ‘members’ \\ gvs [get_member_aux_def]
  \\ qx_genl_tac [‘member'’, ‘name’] \\ rpt strip_tac
  \\ namedCases_on ‘member'’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = name’ \\ gvs []
  \\ gvs [result_mmap_def, from_member_decl_def, set_up_cml_fun_def,
          oneline bind_def, CaseEq "sum"]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [build_rec_env_def, nsLookup_nsBind, nsLookup_nsBind_neq]
QED

Theorem nslookup_build_rec_env_reclos[local]:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_cons env.c ∧
  nsLookup env.v (Short «int_to_string») =
    SOME (cml_int_to_string_clos clos_env) ∧
  int_to_string_env clos_env ⇒
  ∃reclos.
    nsLookup
      (build_rec_env cml_funs env env'_v)
      (Short («dfy_» ^ name)) = SOME reclos ∧
    callable_rel prog name reclos ∧
    reclos = Recclosure env cml_funs («dfy_» ^ name)
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [build_rec_env_def]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all nslookup_build_rec_env_reclos_aux
  \\ disch_then $ qspecl_then [‘cml_funs’, ‘env’, ‘env'_v’] mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ gvs [callable_rel_cases]
  \\ qexistsl [‘clos_env’, ‘member’]
  \\ gvs [get_member_def, dest_program_def]
QED

Definition store_preserve_def:
  store_preserve m base t_refs t'_refs ⇔
    LENGTH t_refs ≤ LENGTH t'_refs ∧
    (* Everything below base and not part of m(odifies) is unchanged. *)
    ∀i v.
      i < base ∧ i ∉ m ∧ store_lookup i t_refs = SOME v ⇒
      store_lookup i t'_refs = SOME v
End

Definition store_preserve_all_def:
  store_preserve_all xs ys ⇔ store_preserve ∅ (LENGTH xs) xs ys
End

Theorem store_preserve_length[local]:
  store_preserve m base xs ys ⇒ LENGTH xs ≤ LENGTH ys
Proof
  simp [store_preserve_def]
QED

Theorem store_preserve_weaken_base[local]:
  store_preserve m base' xs ys ∧ base ≤ base' ⇒
  store_preserve m base xs ys
Proof
  simp [store_preserve_def]
QED

Theorem store_preserve_all_length[local]:
  store_preserve_all xs ys ⇒ LENGTH xs ≤ LENGTH ys
Proof
  simp [store_preserve_all_def] \\ strip_tac
  \\ drule store_preserve_length \\ simp []
QED

Theorem store_preserve_same[local,simp]:
  store_preserve m base xs xs
Proof
  gvs [store_preserve_def]
QED

Theorem store_preserve_all_same[local,simp]:
  store_preserve_all xs xs
Proof
  gvs [store_preserve_all_def]
QED

Theorem store_preserve_decat[local]:
  store_preserve m base (xs ++ ys) zs ⇒ store_preserve m base xs zs
Proof
  gvs [store_preserve_def, store_lookup_def, EL_APPEND]
QED

Theorem store_preserve_all_trans[local]:
  store_preserve_all xs ys ∧ store_preserve_all ys zs ⇒
  store_preserve_all xs zs
Proof
  gvs [store_preserve_all_def, store_preserve_def]
QED

Theorem store_preserve_all_concat[local]:
  store_preserve_all xs ys ⇒ store_preserve_all xs (ys ++ zs)
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def, EL_APPEND]
QED

Theorem store_preserve_all_decat[local]:
  store_preserve_all (xs ++ ys) zs ⇒ store_preserve_all xs zs
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def, EL_APPEND]
QED

Theorem store_preserve_all_locals_rel[local]:
  locals_rel m l s.locals (t: 'ffi cml_state).refs env ∧
  store_preserve_all t.refs (t': 'ffi cml_state).refs ⇒
  locals_rel m l s.locals t'.refs env
Proof
  gvs [locals_rel_def, store_preserve_all_def, store_preserve_def]
  \\ rpt strip_tac >- (last_x_assum drule \\ gvs [])
  \\ qpat_x_assum ‘∀_ _. ALOOKUP _ _ = _ ∧ _ ⇒ _’ $ drule_all
  \\ disch_then $ qx_choosel_then [‘loc’, ‘cml_v’] assume_tac \\ gvs []
  \\ qexists ‘cml_v’ \\ gvs []
  \\ gvs [store_lookup_def]
QED

Theorem store_preserve_all_weaken[local]:
  store_preserve_all xs ys ⇒ store_preserve m base xs ys
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def]
QED

Theorem state_rel_restore_caller[local]:
  state_rel m l s (t: 'ffi cml_state) env ∧
  state_rel m l s' (t': 'ffi cml_state) env' ∧
  store_preserve_all t.refs t'.refs ⇒
  state_rel m l (restore_caller s' s) t' env
Proof
  rpt strip_tac
  \\ gvs [restore_caller_def, state_rel_def]
  \\ irule store_preserve_all_locals_rel
  \\ last_x_assum $ irule_at Any \\ gvs []
QED

Theorem gen_arg_names_len[local,simp]:
  LENGTH (gen_arg_names xs) = LENGTH xs
Proof
  gvs [gen_arg_names_def]
QED

Theorem env_rel_nsLookup[local]:
  env_rel env_dfy env_cml ∧
  get_member name env_dfy.prog = SOME member ⇒
  is_fresh_member member ∧ no_shadow_method member ∧ no_assert_member member ∧
  ∃reclos.
    nsLookup env_cml.v (Short («dfy_» ^ name)) = SOME reclos ∧
    callable_rel env_dfy.prog name reclos
Proof
  rpt strip_tac \\ gvs [env_rel_def] \\ res_tac
QED

Theorem map_from_exp_empty[local,simp]:
  map_from_exp [] = INR []
Proof
  gvs [from_exp_def]
QED

Theorem cml_apps_apps[local]:
  ∀xs id. xs ≠ [] ⇒ cml_apps id xs = Apps id xs
Proof
  Cases_on ‘xs’ \\ gvs [cml_apps_def]
QED

Definition member_get_ins_def[simp]:
  member_get_ins (Method _ ins _ _ _ _ _ _ _) = ins ∧
  member_get_ins (Function _ ins _ _ _ _ _) = ins
End

Theorem map_from_exp_len[local]:
  ∀es cml_es. map_from_exp es = INR cml_es ⇒ LENGTH cml_es = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
QED

(* TODO Move to evaluateProps *)
Theorem evaluate_exps_length[local]:
  ∀s env es s' vs.
    evaluate_exps s env es = (s', Rval vs) ⇒ LENGTH vs = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, AllCaseEqs()]
  \\ res_tac
QED

Definition enumerate_from_def:
  enumerate_from offset ns = MAPi (λi n. (n, offset + i)) ns
End

Theorem enumerate_from_cons[local]:
  enumerate_from offset (n::ns) =
  (n, offset)::(enumerate_from (offset + 1) ns)
Proof
  gvs [enumerate_from_def] \\ irule MAPi_CONG \\ gvs [ADD1]
QED

Theorem enumerate_from_append[local]:
  ∀offset xs ys.
    enumerate_from offset (xs ++ ys) =
    (enumerate_from offset xs) ++ (enumerate_from (offset + LENGTH xs) ys)
Proof
  Induct_on ‘xs’ >- gvs [enumerate_from_def]
  \\ rpt strip_tac
  \\ gvs [enumerate_from_cons, ADD1]
QED

Definition add_refs_to_env_def:
  add_refs_to_env (env_v: (mlstring, mlstring, v) namespace) ns offset =
    nsAppend
      (alist_to_ns
         (REVERSE (MAP (λ(n, i). (n, Loc T i)) (enumerate_from offset ns))))
      env_v
End

Definition mk_locals_map_def:
  mk_locals_map (ns: mlstring list) offset =
    FEMPTY |++ (enumerate_from offset ns)
End

Theorem mk_locals_map_append[local]:
  mk_locals_map (xs ++ ys) offset =
  (mk_locals_map xs offset) |++ (enumerate_from (offset + LENGTH xs) ys)
Proof
  gvs [mk_locals_map_def] \\ gvs [enumerate_from_append, FUPDATE_LIST_APPEND]
QED

Theorem inj_mk_locals_map[local]:
  INJ
    (λn. mk_locals_map ns offset ' n) (FDOM (mk_locals_map ns offset)) 𝕌(:num)
Proof
  gvs [INJ_DEF]
  \\ rpt strip_tac
  \\ gvs [mk_locals_map_def, TO_FLOOKUP, flookup_fupdate_list, CaseEq "option",
          GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS, enumerate_from_def]
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [MEM_EL, enumerate_from_def]
QED

Theorem FST_enumerate_from[local,simp]:
  ∀offset. MAP FST (enumerate_from offset vars) = vars
Proof
  Induct_on ‘vars’
  >- gvs [enumerate_from_def]
  \\ gvs [enumerate_from_cons]
QED

Theorem lambda_SUC[local,simp]:
  (λi n. (n, i + x)) ∘ SUC = (λi n. (n, i + (x + 1)))
Proof
  gvs [FUN_EQ_THM]
QED

Theorem ALOOKUP_enumerate_from[local]:
  ∀i vars offset.
    i < LENGTH vars ∧ ALL_DISTINCT vars⇒
    ALOOKUP (enumerate_from offset vars) (EL i vars) = SOME (i + offset)
Proof
  Induct_on ‘vars’
  \\ gvs [enumerate_from_def]
  \\ rpt strip_tac
  \\ IF_CASES_TAC
  \\ gvs [EL_CONS_IF]
  \\ Cases_on ‘i = 0’ \\ gvs []
  \\ ‘PRE i < LENGTH vars’ by gvs []
  \\ gvs [EL_MEM]
QED

Theorem FRANGE_mk_locals_map[local]:
  ∀vars offset.
    i ∈ FRANGE (mk_locals_map vars offset) ∧ ALL_DISTINCT vars ⇒
    offset ≤ i ∧ i < LENGTH vars + offset
Proof
  gvs [mk_locals_map_def, TO_FLOOKUP, flookup_update_list_some]
  \\ ntac 3 strip_tac
  \\ rename [‘ALOOKUP _ k’]
  \\ qspecl_then [‘enumerate_from offset vars’, ‘k’] assume_tac
                 alookup_distinct_reverse
  \\ fs[] \\ pop_assum kall_tac
  \\ drule_then assume_tac ALOOKUP_find_index_SOME \\ gvs []
  \\ gvs [find_index_ALL_DISTINCT_EL_eq]
  \\ imp_res_tac ALOOKUP_enumerate_from \\ gvs []
QED

(* TODO Is this useful to be in namespaceTheory? *)
Theorem nsappend_alist_to_ns_nsbind[local]:
  LENGTH vs = LENGTH ns ⇒
  nsAppend (alist_to_ns (ZIP (ns, vs))) (nsBind n v env) =
  nsAppend (alist_to_ns (ZIP (SNOC n ns, SNOC v vs))) env
Proof
  strip_tac
  \\ Cases_on ‘env’
  \\ simp [alist_to_ns_def, nsBind_def, nsAppend_def]
  \\ DEP_REWRITE_TAC [GSYM ZIP_APPEND]
  \\ simp []
QED

Theorem nsappend_alist_to_ns_reverse_cons[local]:
  nsAppend (alist_to_ns (REVERSE xs ++ [(n,v)])) env_v =
  nsAppend (alist_to_ns (REVERSE xs)) (nsBind n v env_v)
Proof
  Cases_on ‘env_v’
  \\ gvs [alist_to_ns_def, nsAppend_def, nsBind_def]
QED

Theorem add_refs_to_env_cons[local]:
  add_refs_to_env env_v (n::ns) offset =
  (add_refs_to_env (nsBind n (Loc T offset) env_v) ns (offset + 1))
Proof
  gvs [add_refs_to_env_def, enumerate_from_cons,
       nsappend_alist_to_ns_reverse_cons]
QED

Theorem evaluate_set_up_in_refs[local]:
  ∀params vs s env body.
    LIST_REL (λn v. nsLookup env.v (Short n) = SOME v) params vs ∧
    ALL_DISTINCT params ⇒
    evaluate (s: 'ffi cml_state) env [set_up_in_refs params body] =
    evaluate
      (s with refs := s.refs ++ (MAP Refv vs))
      (env with v := add_refs_to_env env.v params (LENGTH s.refs))
      [body]
Proof
  Induct_on ‘params’
  \\ rpt strip_tac
  >- (gvs [set_up_in_refs_def, add_refs_to_env_def, enumerate_from_def])
  \\ gvs [set_up_in_refs_def]
  \\ gvs [evaluate_def]
  \\ gvs [do_app_def, store_alloc_def]
  \\ irule EQ_TRANS
  \\ last_x_assum $ irule_at (Pos hd) \\ gvs []
  \\ gvs [add_refs_to_env_cons]
  \\ rename [‘nsLookup _ (Short h) = SOME v’, ‘LIST_REL _ _ vs'’]
  \\ qexists ‘vs'’ \\ gvs []
  \\ strip_tac
  >- (gvs [LIST_REL_EL_EQN]
      \\ rpt strip_tac
      \\ ‘EL n params ≠ h’ by (strip_tac \\ gvs [EL_MEM])
      \\ gvs [])
  \\ ‘s.refs ++ [Refv v] ++ MAP Refv vs' =
        s.refs ++ Refv v::MAP Refv vs'’ by gvs []
  \\ simp [] \\ pop_assum kall_tac
QED

Theorem not_mem_nslookup_nsappend_alist[local]:
  ¬MEM x (MAP FST ys) ⇒
  nsLookup (nsAppend (alist_to_ns ys) ns) (Short x) = nsLookup ns (Short x)
Proof
  strip_tac
  \\ Cases_on ‘nsLookup ns (Short x)’ \\ simp []
  >- (simp [nsLookup_nsAppend_none, nsLookup_alist_to_ns_none, ALOOKUP_NONE])
  \\ simp [nsLookup_nsAppend_some]
  \\ disj2_tac
  \\ simp [nsLookup_alist_to_ns_none, ALOOKUP_NONE, id_to_mods_def]
QED

Theorem FST_o_n_Loc[local,simp]:
  FST ∘ (λ(n,i). (n, Loc T i)) = FST
Proof
  gvs [FUN_EQ_THM] \\ Cases \\ gvs []
QED

Theorem not_mem_nslookup_add_refs_to_env[local]:
  ¬MEM x ns ⇒
  nsLookup (add_refs_to_env env_v ns offset) (Short x) =
  nsLookup env_v (Short x)
Proof
  strip_tac
  \\ simp [add_refs_to_env_def]
  \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
  \\ simp [MAP_REVERSE, MAP_MAP_o]
QED

Theorem store_lookup_append[local]:
  store_lookup l st = SOME v ⇒ store_lookup l (st ++ st') = SOME v
Proof
  rpt strip_tac \\ gvs [store_lookup_def, rich_listTheory.EL_APPEND1]
QED

Theorem array_rel_append[local]:
  array_rel m s_heap t_heap ⇒
  array_rel m s_heap (t_heap ++ xs)
Proof
  gvs [array_rel_def]
  \\ rpt strip_tac
  \\ res_tac
  >- (intLib.COOPER_TAC)
  >- (drule store_lookup_append \\ simp [])
  >- (drule store_lookup_append \\ simp [])
QED

Theorem read_local_reverse_eq[local]:
  ALL_DISTINCT (MAP FST l) ⇒ read_local (REVERSE l) var = read_local l var
Proof
  rpt strip_tac
  \\ drule alookup_distinct_reverse
  \\ disch_then $ qspec_then ‘var’ assume_tac
  \\ gvs [read_local_def]
QED

Theorem ALOOKUP_ZIP_SOME_EL[local]:
  ∀(ns: mlstring list) (vs: value list) var val.
    ALOOKUP (ZIP (ns, MAP SOME vs)) var = SOME (SOME val) ∧
    ALL_DISTINCT ns ∧ LENGTH vs = LENGTH ns ⇒
    ∃i. var = EL i ns ∧ val = EL i vs ∧ i < LENGTH ns
Proof
  rpt strip_tac
  \\ drule ALOOKUP_find_index_SOME \\ rpt strip_tac
  \\ qexists ‘i’
  \\ gvs [EL_ZIP, find_index_ALL_DISTINCT_EL_eq, EL_MAP, MAP_ZIP]
QED

Theorem nsLookup_add_refs_to_env[local]:
  ALL_DISTINCT ns ∧
  i < LENGTH ns ⇒
  nsLookup
    (add_refs_to_env env_v ns offset)
    (Short (EL i ns)) =
  SOME (Loc T (i + offset))
Proof
  rpt strip_tac
  \\ gvs [add_refs_to_env_def]
  \\ gvs [nsLookup_nsAppend_some]
  \\ disj1_tac
  \\ gvs [nsLookup_alist_to_ns_some]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
  \\ strip_tac >- (gvs [MAP_MAP_o])
  \\ gvs [ALOOKUP_MAP, ALOOKUP_enumerate_from]
QED

Theorem LIST_REL_store_lookup[local]:
  LIST_REL (val_rel m) in_vs cml_vs ∧
  i < LENGTH cml_vs ⇒
  store_lookup (i + LENGTH s.refs) (s.refs ++ MAP Refv cml_vs) =
  SOME (Refv (EL i cml_vs)) ∧ val_rel m (EL i in_vs) (EL i cml_vs)
Proof
  strip_tac
  \\ simp [store_lookup_def]
  \\ simp [EL_APPEND, EL_MAP]
  \\ fs [LIST_REL_EL_EQN]
QED

Theorem ALOOKUP_ZIP_MAP_SOME_SOME[local]:
  ALOOKUP (ZIP (ns, MAP SOME vs)) var = SOME ov ∧
  LENGTH ns = LENGTH vs ⇒
  ∃v. ov = SOME v
Proof
  rpt strip_tac
  \\ drule ALOOKUP_MEM \\ rpt strip_tac
  \\ gvs [MEM_ZIP, EL_MAP]
QED

Theorem FLOOKUP_mk_locals_map[local]:
  i < LENGTH ns ∧ ALL_DISTINCT ns ⇒
  FLOOKUP (mk_locals_map ns offset) (EL i ns) = SOME (i + offset)
Proof
  strip_tac
  \\ imp_res_tac ALOOKUP_enumerate_from
  \\ simp [mk_locals_map_def, flookup_fupdate_list, CaseEq "option"]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse] \\ simp []
QED

(* TODO Is this a good way to write this?/Upstream to HOL *)
Theorem SNOC_HD_REVERSE_TL[local]:
  xs ≠ [] ⇒ SNOC (HD xs) (REVERSE (TL xs)) = REVERSE xs
Proof
  rpt strip_tac
  \\ ‘(HD xs)::(TL xs) = xs’ by gvs []
  \\ asm_rewrite_tac [GSYM (cj 2 REVERSE_SNOC_DEF)]
QED

Theorem INJ_FLOOKUP_IMP[local]:
  INJ (λx: num. m ' x) (FDOM m) 𝕌(:num) ∧
  FLOOKUP m x = SOME v ∧ FLOOKUP m y = SOME w ⇒
  (v = w ⇔ x = y)
Proof
  simp [INJ_DEF, FLOOKUP_DEF] \\ metis_tac []
QED

Theorem state_rel_array_loc_INJ[local]:
  state_rel m l s (t: 'ffi cml_state) env_cml ⇒
  INJ (λx. m ' x) (FDOM m) 𝕌(:num)
Proof
  gvs [state_rel_def, array_rel_def]
QED

(* TODO Upstream? *)
Theorem LIST_REL_nsLookup_nsAppend[local]:
  ∀names vals (ns: (mlstring, mlstring, v) namespace).
    ALL_DISTINCT names ∧
    LENGTH names = LENGTH vals ⇒
    LIST_REL
      (λn v.
         nsLookup
           (nsAppend (alist_to_ns (ZIP (names, vals))) ns)
           (Short n) = SOME v) names vals
Proof
  Induct \\ simp []
  \\ namedCases_on ‘vals’ ["", "val vals'"] \\ simp []
  \\ qx_gen_tac ‘name’ \\ rpt strip_tac \\ simp []
  \\ fs [LIST_REL_EL_EQN]
  \\ rpt strip_tac
  \\ ‘EL n names ≠ name’ by (strip_tac \\ gvs [EL_MEM])
  \\ simp []
QED

(* TODO better way to write this? *)
Theorem LIST_REL_nsLookup_nsAppend_REVERSE[local]:
  ∀names vals (ns: (mlstring, mlstring, v) namespace).
    ALL_DISTINCT names ∧
    LENGTH names = LENGTH vals ⇒
    LIST_REL
      (λn v.
         nsLookup
         (nsAppend (alist_to_ns (ZIP (REVERSE names, vals))) ns)
         (Short n) = SOME v) names (REVERSE vals)
Proof
  rpt strip_tac
  \\ qspecl_then [‘REVERSE names’, ‘vals’, ‘ns’] mp_tac
       LIST_REL_nsLookup_nsAppend
  \\ strip_tac \\ gvs []
  \\ drule_all EVERY2_REVERSE
  \\ pure_rewrite_tac [REVERSE_REVERSE]
  \\ gvs []
QED

(* TODO better way to write this? *)
Theorem LIST_REL_nsLookup_nsAppend_REVERSE1[local]:
  ∀names vals (ns: (mlstring, mlstring, v) namespace).
    ALL_DISTINCT names ∧
    LENGTH names = LENGTH vals ⇒
    LIST_REL
      (λn v.
         nsLookup
         (nsAppend (alist_to_ns (ZIP (names, REVERSE vals))) ns)
         (Short n) = SOME v) names (REVERSE vals)
Proof
  rpt strip_tac
  \\ qspecl_then [‘names’, ‘REVERSE vals’, ‘ns’] mp_tac
       LIST_REL_nsLookup_nsAppend
  \\ strip_tac \\ gvs []
  \\ drule_all EVERY2_REVERSE
QED

Theorem alookup_nslookup_store_lookup[local]:
  ∀(s: 'ffi cml_state) env ins in_vs var dfy_v m cml_vs.
    ALOOKUP (ZIP (MAP FST ins, MAP SOME in_vs)) var = SOME (SOME dfy_v) ∧
    LIST_REL (val_rel m) in_vs cml_vs ∧
    ALL_DISTINCT (MAP FST ins) ∧
    LENGTH in_vs = LENGTH ins ⇒
    ∃loc cml_v.
      nsLookup
        (add_refs_to_env env.v (MAP FST ins)
           (LENGTH s.refs))
        (Short var) = SOME (Loc T loc) ∧
      FLOOKUP (mk_locals_map (MAP FST ins) (LENGTH s.refs)) var = SOME loc ∧
      store_lookup loc (s.refs ++ MAP Refv cml_vs) = SOME (Refv cml_v) ∧
      val_rel m dfy_v cml_v
Proof
  rpt strip_tac
  \\ drule_then assume_tac ALOOKUP_ZIP_SOME_EL \\ gvs []
  \\ qexistsl [‘LENGTH s.refs + i’, ‘EL i cml_vs’]
  \\ gvs [GSYM MAP_MAP_o]
  \\ irule_at Any nsLookup_add_refs_to_env \\ gvs []
  \\ irule_at Any FLOOKUP_mk_locals_map \\ gvs []
  \\ irule LIST_REL_store_lookup \\ gvs []
  \\ imp_res_tac LIST_REL_LENGTH \\ simp []
QED

Theorem NOT_MEM_TL[local]:
  ¬MEM x xs ⇒ ¬MEM x (TL xs)
Proof
  rpt strip_tac \\ drule MEM_TL \\ simp []
QED

Theorem cml_fun_MEM_var[local]:
  cml_fun params body = (param, cml_body) ∧ params ≠ [] ⇒
  MEM param params
Proof
  Cases_on ‘params’ \\ simp [cml_fun_def]
QED

Theorem nslookup_build_rec_env_int_to_string_aux[local]:
  ∀members cml_funs' cml_funs (env_v: cml_ns) clos_env.
    result_mmap from_member_decl members = INR cml_funs ∧
    nsLookup env_v (Short «int_to_string») =
      SOME (cml_int_to_string_clos clos_env) ∧
    int_to_string_env clos_env
    ⇒
    nsLookup
      (FOLDR (λ(f,x,e) env₁. nsBind f (Recclosure env cml_funs' f) env₁)
             env_v cml_funs)
      (Short cml_int_to_string_name) =
      SOME (cml_int_to_string_clos clos_env) ∧
    int_to_string_env clos_env
Proof
  Induct_on ‘members’ \\ gvs [get_member_aux_def]
  \\ qx_genl_tac [‘member'’, ‘name’] \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ gvs [from_member_decl_def, oneline bind_def, set_up_cml_fun_def,
          AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [strcat_def, concat_def]
QED

Theorem nslookup_build_rec_env_int_to_string[local]:
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  nsLookup env.v (Short «int_to_string») =
    SOME (cml_int_to_string_clos clos_env) ∧
  int_to_string_env clos_env
  ⇒
  nsLookup (build_rec_env cml_funs env env.v) (Short cml_int_to_string_name) =
    SOME (cml_int_to_string_clos clos_env) ∧
  int_to_string_env clos_env
Proof
  strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [build_rec_env_def]
  \\ gvs [dest_program_def]
  \\ drule_all nslookup_build_rec_env_int_to_string_aux
  \\ simp []
QED

(* TODO split up cases into separate trivialities like other compiler proofs *)
Theorem correct_from_exp:
  (∀s env_dfy e_dfy s' r_dfy (t: 'ffi cml_state) env_cml e_cml m l.
     evaluate_exp s env_dfy e_dfy = (s', r_dfy) ∧
     from_exp e_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ is_fresh_exp e_dfy ∧
     r_dfy ≠ Rerr Rfail
     ⇒ ∃ck (t': 'ffi cml_state) r_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
           (t', r_cml) ∧
         store_preserve_all t.refs t'.refs ∧
         state_rel m l s' t' env_cml ∧
         cml_state_preserved t t' ∧
         exp_res_rel m r_dfy r_cml) ∧
  (∀s env_dfy es_dfy s' rs_dfy (t: 'ffi cml_state) env_cml es_cml m l.
     evaluate_exps s env_dfy es_dfy = (s', rs_dfy) ∧
     map_from_exp es_dfy = INR es_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ EVERY (λe. is_fresh_exp e) es_dfy ∧
     rs_dfy ≠ Rerr Rfail
     ⇒ ∃ck (t': 'ffi cml_state) rs_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml es_cml =
           (t', rs_cml) ∧
         store_preserve_all t.refs t'.refs ∧
         state_rel m l s' t' env_cml ∧
         cml_state_preserved t t' ∧
         exp_ress_rel m rs_dfy rs_cml)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘FunCall name args’] >-
   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘get_member name env_dfy.prog’ ["", "member"] \\ gvs []
    \\ Cases_on ‘member’ \\ gvs []
    \\ rename [‘Function name ins res_t _ _ _ body’]
    \\ drule get_member_some_fun_name \\ rpt strip_tac \\ gvs []
    \\ drule_all env_rel_nsLookup \\ rpt strip_tac
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ qabbrev_tac ‘fname = «dfy_» ^ name’ \\ gvs []
    \\ drule map_from_exp_len \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁,_)’]
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (* Evaluating arguments failed *)
     (qexists ‘ck’
      \\ Cases_on ‘cml_args = []’ \\ gvs []
      \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
      \\ drule_all evaluate_Apps_Rerr
      \\ disch_then $ qspec_then ‘Var (Short fname)’ assume_tac \\ gvs [])
    \\ drule evaluate_exps_length \\ rpt strip_tac \\ gvs []
    \\ namedCases_on
         ‘set_up_call s₁ (MAP FST ins) in_vs []’ ["", "r"] \\ gvs []
    \\ gvs [set_up_call_def, safe_zip_def]
    \\ Cases_on ‘LENGTH ins ≠ LENGTH in_vs’ \\ gvs []
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (* Dafny semantics ran out of ticks *)
     (qexists ‘ck’ \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
      >- (gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
               do_opapp_def, callable_rel_cases]
          \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
          \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def] \\ gvs []
          \\ gvs [restore_caller_def, state_rel_def])
      \\ Cases_on ‘cml_args = []’ \\ gvs []
      \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
      (* Preparing ns for evaluate_Apps *)
      \\ qabbrev_tac ‘params = MAP FST ins’
      \\ ‘LENGTH (REVERSE params) = LENGTH ins’ by (unabbrev_all_tac \\ gvs [])
      \\ ‘SUC (LENGTH (TL (REVERSE params))) = LENGTH ins’ by
        (Cases_on ‘REVERSE params’ \\ gvs [])
      (* Preparing clos_v for evaluate_Apps *)
      \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
      (* Preparing env1 for evaluate_Apps *)
      \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
      \\ qabbrev_tac
         ‘call_env =
            env with v :=
              nsBind cml_param (LAST cml_vs) (build_rec_env cml_funs env env.v)’
      (* Preparing e for evaluate_Apps *)
      \\ gvs [from_member_decl_def, set_up_cml_fun_def, oneline bind_def,
              CaseEq "sum"]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ qabbrev_tac ‘call_body = set_up_in_refs params cml_body'’
      (* Instantiating evaluate_Apps *)
      \\ drule evaluate_Apps
      \\ disch_then $ qspec_then ‘TL (REVERSE params)’ mp_tac \\ gvs []
      \\ disch_then $ drule
      \\ disch_then $ qspecl_then [‘call_env’, ‘call_body’] mp_tac
      \\ impl_tac >- gvs [do_opapp_def, cml_fun_def, MAP_MAP_o, AllCaseEqs()]
      \\ rpt strip_tac \\ gvs []
      \\ pop_assum $ kall_tac
      (* Finished instantiating evaluate_Apps *)
      \\ ‘t₁.clock = s₁.clock’ by gvs [state_rel_def] \\ gvs []
      \\ gvs [restore_caller_def, state_rel_def, cml_state_preserved_def])
    \\ qabbrev_tac ‘dfy_locals = REVERSE (ZIP (MAP FST ins, MAP SOME in_vs))’
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp call_t’
    \\ namedCases_on ‘evaluate_exp call_t env_dfy body’ ["s₂ r"]
    \\ gvs [Abbr ‘call_t’]
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    (* Show how compiling the function body succeeds *)
    \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
    \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ gvs [from_member_decl_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs []
    >-
     (gvs [evaluate_exp_def]
      \\ ‘ck = 0’ by gvs [state_rel_def] \\ gvs []
      \\ ‘t.clock ≠ 0’ by gvs [state_rel_def] \\ gvs []
      \\ last_x_assum $
           qspecl_then
             [‘dec_clock t’,
              ‘env with v :=
                 nsBind «» (Conv NONE []) (build_rec_env cml_funs env env.v)’,
              ‘m’, ‘l’]
             mp_tac
      \\ impl_tac
      >-
       (unabbrev_all_tac
        \\ gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def,
                locals_rel_def, read_local_def, env_rel_def]
        \\ rpt strip_tac
        >- (drule_all nslookup_build_rec_env_int_to_string \\ simp []
            \\ strip_tac \\ qexists ‘clos_env’ \\ simp [])
        >- res_tac
        >- res_tac
        >- res_tac
        >- (drule_all nslookup_build_rec_env_reclos \\ gvs [strcat_def, concat_def]))
      \\ rpt strip_tac
      \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = _’]
      \\ qexists ‘ck'’
      \\ gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
              do_opapp_def]
      \\ gvs [set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def]
      \\ gvs [evaluate_def, do_con_check_def, build_conv_def,
              evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r’ \\ gvs []
      \\ drule_all state_rel_restore_caller \\ gvs []
      \\ gvs [cml_state_preserved_def])
    (* Evaluating (non-empty) args succeeded *)
    \\ Cases_on ‘cml_args = []’ \\ gvs []
    \\ Cases_on ‘cml_vs = []’ \\ gvs []
    \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
    (* TODO Maybe we should case distinction on args earlier? *)
    (* Preparing ns for evaluate_Apps *)
    \\ qabbrev_tac ‘params = (MAP FST ins)’
    \\ ‘ALL_DISTINCT params’ by
      (simp [Abbr ‘params’, GSYM MAP_MAP_o, ALL_DISTINCT_MAP_explode])
    \\ ‘LENGTH (REVERSE params) = LENGTH ins’ by (unabbrev_all_tac \\ gvs [])
    \\ ‘SUC (LENGTH (TL (REVERSE params))) = LENGTH ins’ by
      (Cases_on ‘REVERSE params’ \\ gvs [])
    \\ ‘LENGTH cml_vs = LENGTH cml_args’ by
      (drule (cj 1 evaluate_length) \\ gvs [])
    \\ ‘LENGTH (REVERSE (TL (REVERSE params))) = LENGTH (FRONT cml_vs)’ by
      (Cases_on ‘cml_vs = []’ \\ gvs [FRONT_LENGTH])
    (* Preparing clos_v for evaluate_Apps *)
    \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
    (* Preparing env1 for evaluate_Apps *)
    \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ qabbrev_tac
       ‘call_env =
          env with v :=
            nsBind cml_param (LAST cml_vs) (build_rec_env cml_funs env env.v)’
    (* Preparing e for evaluate_Apps *)
    \\ gvs [from_member_decl_def, set_up_cml_fun_def, oneline bind_def,
            CaseEq "sum"]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ qabbrev_tac ‘call_body = set_up_in_refs params cml_body'’
    (* Instantiating IH *)
    \\ qabbrev_tac
         ‘call_env₁ =
            call_env with v :=
              nsAppend
                (alist_to_ns (ZIP (REVERSE (TL (REVERSE params)), FRONT cml_vs)))
                call_env.v’
    \\ qabbrev_tac
         ‘call_env₂ =
            call_env₁ with v :=
              add_refs_to_env call_env₁.v params (LENGTH t₁.refs)’
    \\ last_x_assum $
         qspecl_then
           [‘dec_clock (t₁ with refs := t₁.refs ++ MAP Refv cml_vs)’,
            ‘call_env₂’,
            ‘m’,
            ‘mk_locals_map (MAP FST ins) (LENGTH t₁.refs)’]
           mp_tac
    \\ impl_tac
    >- (rpt strip_tac
        >- (gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def]
            \\ irule_at Any array_rel_append \\ gvs []
            \\ gvs [locals_rel_def]
            \\ rpt strip_tac
            >- irule_at Any inj_mk_locals_map
            >- (drule FRANGE_mk_locals_map \\ gvs [])
            \\ gvs [Abbr ‘dfy_locals’]
            \\ ‘ALL_DISTINCT (MAP FST (ZIP (MAP FST ins, MAP SOME in_vs)))’
              by gvs [MAP_ZIP]
            \\ drule read_local_reverse_eq
            \\ disch_then $ qspec_then ‘var’ assume_tac
            \\ gvs []
            (* Delete rewriting assumptions we just made *)
            \\ ntac 2 (pop_assum $ kall_tac)
            \\ ‘ALL_DISTINCT (MAP FST (ZIP (MAP FST ins, MAP SOME in_vs)))’
              by gvs [MAP_ZIP]
            \\ gvs [alookup_distinct_reverse]
            \\ drule ALOOKUP_ZIP_MAP_SOME_SOME \\ rpt strip_tac \\ gvs []
            \\ gvs [Abbr ‘params’] \\ drule alookup_nslookup_store_lookup
            \\ disch_then drule \\ gvs []
            \\ disch_then $ qspecl_then [‘t₁’, ‘call_env₁’] mp_tac
            \\ rpt strip_tac \\ gvs [Abbr ‘call_env₂’])
        \\ gvs [env_rel_def] \\ rpt strip_tac
        >- (unabbrev_all_tac \\ gvs [has_cons_def])
        >-
         (‘EVERY (λn. n ≠ cml_int_to_string_name) (REVERSE params)’ by
            (drule every_is_fresh_not_int_to_string
             \\ simp [Abbr ‘params’, MAP_MAP_o])
          \\ gvs [Abbr ‘call_env₂’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env]
          \\ gvs [EVERY_MEM, Abbr ‘call_env₁’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
          \\ gvs [MAP_ZIP]
          \\ conj_tac >-
           (Cases_on ‘REVERSE params = []’ \\ gvs []
            \\ irule NOT_MEM_TL \\ simp [])
          \\ gvs [Abbr ‘call_env’]
          \\ DEP_REWRITE_TAC [nsLookup_nsBind_neq]
          \\ strip_tac >-
           (‘REVERSE params ≠ []’ by (spose_not_then assume_tac \\ gvs [])
            \\ drule_all cml_fun_MEM_var \\ strip_tac
            \\ spose_not_then assume_tac \\ gvs [])
          \\ drule_all nslookup_build_rec_env_int_to_string
          \\ strip_tac \\ fs []
          \\ first_assum $ irule_at (Pos last) \\ simp [])
        >- res_tac
        >- res_tac
        >- res_tac
        \\ rename [‘get_member name' _ = SOME _’]
        \\ ‘EVERY (λn. n ≠ «dfy_» ^ name') (REVERSE params)’ by
          (drule every_is_fresh_not_dfy
           \\ disch_then $ qspec_then ‘name'’ assume_tac
           \\ gvs [Abbr ‘params’, MAP_MAP_o])
        \\ gvs [Abbr ‘call_env₂’]
        \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env]
        \\ gvs [EVERY_MEM, Abbr ‘call_env₁’]
        \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
        \\ gvs [MAP_ZIP]
        \\ strip_tac >-
         (Cases_on ‘REVERSE params = []’ \\ gvs []
          \\ irule NOT_MEM_TL \\ simp [])
        \\ gvs [Abbr ‘call_env’]
        \\ DEP_REWRITE_TAC [nsLookup_nsBind_neq]
        \\ strip_tac >-
         (‘REVERSE params ≠ []’ by (spose_not_then assume_tac \\ gvs [])
          \\ drule_all cml_fun_MEM_var \\ strip_tac
          \\ spose_not_then assume_tac \\ gvs [])
        \\ drule_all nslookup_build_rec_env_reclos \\ gvs [])
    \\ rpt strip_tac
    (* Fixing clocks *)
    \\ ‘t₁.clock ≠ 0’ by gvs [state_rel_def]
    \\ qexists ‘ck + ck' + LENGTH ins - 1’
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck' + LENGTH ins - 1’ assume_tac
    \\ gvs []
    (* Instantiating evaluate_Apps *)
    \\ drule evaluate_Apps
    \\ disch_then $ qspec_then ‘TL (REVERSE params)’ mp_tac \\ gvs []
    \\ disch_then $ drule
    \\ disch_then $ qspecl_then [‘call_env’, ‘call_body’] mp_tac
    \\ impl_tac >- gvs [do_opapp_def, cml_fun_def, MAP_MAP_o, AllCaseEqs()]
    \\ rpt strip_tac \\ gvs []
    \\ pop_assum $ kall_tac
    (* Finished instantiating evaluate_Apps *)
    \\ ‘cml_param = HD (REVERSE params)’ by
      (Cases_on ‘REVERSE params’ \\ gvs [cml_fun_def])
    \\ gvs [evaluateTheory.dec_clock_def]
    \\ gvs [Abbr ‘call_body’]
    \\ ‘LIST_REL (λn v. nsLookup call_env₁.v (Short n) = SOME v) params cml_vs’
      by (gvs [Abbr ‘call_env₁’, Abbr ‘call_env’]
          \\ DEP_REWRITE_TAC [nsappend_alist_to_ns_nsbind]
          \\ Cases_on ‘params = []’ \\ gvs []
          \\ gvs [SNOC_LAST_FRONT, REVERSE_TL, SNOC_HD_REVERSE_TL]
          \\ irule LIST_REL_nsLookup_nsAppend
          \\ gvs [Abbr ‘params’, GSYM MAP_MAP_o])
    \\ drule_all evaluate_set_up_in_refs
    \\ disch_then $
         qspecl_then
           [‘t₁ with clock := ck' + t₁.clock - 1’, ‘cml_body'’] assume_tac
    \\ gvs []
    \\ rename [‘evaluate (t₁ with clock := _) _ _ = (t₂, _)’]
    \\ irule_at Any store_preserve_all_trans
    \\ qexists ‘t₁.refs’ \\ gvs []
    (* We will need this again later *)
    \\ ‘store_preserve_all t₁.refs t₂.refs’ by
      (irule_at Any store_preserve_all_decat
       \\ last_assum $ irule_at Any \\ gvs [])
    \\ gvs []
    \\ namedCases_on ‘r’ ["", "v err"] \\ gvs []
    \\ gvs [state_rel_def, restore_caller_def, cml_state_preserved_def]
    \\ irule store_preserve_all_locals_rel
    \\ last_assum $ irule_at (Pos hd) \\ gvs [])
  >~ [‘Lit l’] >-
   (qexistsl [‘0’, ‘t’]
    \\ Cases_on ‘l’
    \\ gvs [evaluate_exp_def, from_lit_def, from_exp_def, evaluate_def]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’
    \\ gvs [evaluate_def, do_con_check_def, env_rel_def, has_cons_def,
            build_conv_def, Boolv_def, bool_type_num_def])
  >~ [‘Var name’] >-
   (qexists ‘0’
    \\ gvs [evaluate_exp_def, CaseEq "option"]
    \\ drule_all read_local_some_imp \\ rpt strip_tac
    \\ gvs [from_exp_def, cml_read_var_def]
    \\ gvs [evaluate_def, do_app_def, state_rel_def])
  >~ [‘If grd thn els’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy grd’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["grd_v", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [])
    \\ namedCases_on ‘do_cond grd_v thn els’ ["", "branch"] \\ gvs []
    \\ gvs [oneline do_cond_def, CaseEq "value"]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ gvs [do_if_def, cml_state_preserved_def]
    \\ irule store_preserve_all_trans \\ gvs [SF SFY_ss])
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ qexists ‘ck’
    \\ Cases_on ‘uop’ \\ gvs [from_un_op_def, evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ gvs [do_uop_def, CaseEqs ["value", "option"], do_app_def,check_type_def]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs [do_arith_def])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e₀’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _ = (t₁, _)’]
    \\ gvs [evaluate_def]
    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >- (qexists ‘ck’ \\ gvs [])
    \\ rename [‘val_rel _ dfy_v₀ cml_v₀’]
    \\ Cases_on ‘do_sc bop dfy_v₀’ \\ gvs []
    >- (* Short-circuiting *)
     (qexists ‘ck’
      \\ gvs [oneline do_sc_def, val_rel_cases, evaluate_def, from_bin_op_def,
              do_log_def, Boolv_def, do_if_def, do_con_check_def, env_rel_def,
              build_conv_def, bool_type_num_def, env_rel_def,
              has_cons_def, AllCaseEqs()])
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy e₁’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ ‘¬is_fresh « l»’ by gvs [is_fresh_def, isprefix_thm]
    \\ drule_all state_rel_env_push_not_fresh
    \\ disch_then $ qspec_then ‘cml_v₀’ assume_tac
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_cons_def] \\ rpt strip_tac \\ res_tac
      \\ first_assum $ irule_at (Pos last) \\ simp [strcat_def, concat_def])
    \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ ‘store_preserve_all t.refs t₂.refs’ by
      (irule store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ drule state_rel_env_pop_not_fresh \\ gvs []
    \\ disch_then $ drule \\ rpt strip_tac \\ gvs []
    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >-
     (Cases_on ‘bop’
      \\ gvs [oneline do_sc_def, val_rel_cases, from_bin_op_def,
              evaluate_def, do_log_def, do_if_def, cml_state_preserved_def,
              AllCaseEqs()])
    \\ rename [‘val_rel _ dfy_v₁ cml_v₁’]
    \\ Cases_on ‘do_bop bop dfy_v₀ dfy_v₁’ \\ gvs []
    \\ Cases_on ‘bop = Div’ \\ gvs [] >-
     (gvs [do_bop_def, AllCaseEqs()]
      \\ gvs [from_bin_op_def, EDIV_DEF]
      \\ gvs [evaluate_def, do_app_def, do_if_def, do_test_def]
      \\ Cases_on ‘0 < i₁’
      \\ gvs [evaluate_def, do_app_def, do_arith_def, check_type_def, Boolv_def]
      \\ gvs [cml_state_preserved_def, state_rel_def])
    \\ Cases_on ‘bop = Mod’ \\ gvs [] >-
     (gvs [do_bop_def, CaseEq "value"]
      \\ gvs [from_bin_op_def, EMOD_DEF]
      \\ gvs [evaluate_def, do_app_def, do_if_def, do_test_def]
      \\ Cases_on ‘i₁ < 0’
      \\ gvs [evaluate_def, do_app_def, do_arith_def, check_type_def, INT_ABS]
      \\ gvs [cml_state_preserved_def])
    \\ Cases_on ‘bop = Eq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on ‘dfy_v₀’ ["i", "b", "str", "len dfy_loc ty"] \\ gvs []
      \\ namedCases_on ‘dfy_v₁’ ["i'", "b'", "str'", "len' dfy_loc' ty'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [do_eq_def, lit_same_type_def, Boolv_def, ctor_same_type_def,
                same_type_def]
        \\ gvs [cml_state_preserved_def])
      >~ [‘do_eq (Conv _ _) (Conv _ _)’] >-
       (drule_all state_rel_array_loc_INJ \\ rpt strip_tac
        \\ drule INJ_FLOOKUP_IMP
        \\ disch_then $ qspecl_then [‘dfy_loc’, ‘dfy_loc'’] mp_tac
        \\ disch_then drule_all
        \\ gvs [do_eq_def, lit_same_type_def]
        \\ Cases_on ‘len = len'’ \\ gvs []
        \\ Cases_on ‘dfy_loc = dfy_loc'’
        \\ gvs [cml_state_preserved_def, state_rel_def])
      \\ gvs [do_eq_def, lit_same_type_def]
      \\ gvs [cml_state_preserved_def])
    \\ Cases_on ‘bop = Neq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on
           ‘dfy_v₀’ ["i", "b", "dfy_str", "len dfy_loc ty"] \\ gvs []
      \\ namedCases_on
           ‘dfy_v₁’ ["i'", "b'", "dfy_str'", "len' dfy_loc' ty'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [evaluate_def, do_eq_def, lit_same_type_def, Boolv_def,
                ctor_same_type_def, same_type_def, do_if_def, do_con_check_def,
                build_conv_def, env_rel_def, has_cons_def,
                bool_type_num_def]
        \\ gvs [cml_state_preserved_def])
      >~ [‘do_eq (Conv _ _) (Conv _ _)’] >-
       (drule_all state_rel_array_loc_INJ \\ rpt strip_tac
        \\ drule INJ_FLOOKUP_IMP
        \\ disch_then $ qspecl_then [‘dfy_loc’, ‘dfy_loc'’] mp_tac
        \\ disch_then drule_all
        \\ gvs [do_eq_def, lit_same_type_def]
        \\ Cases_on ‘len = len'’ \\ gvs []
        \\ Cases_on ‘dfy_loc = dfy_loc'’
        \\ gvs [do_if_def, evaluate_def, do_con_check_def, env_rel_def,
                build_conv_def, Boolv_def, bool_type_num_def,
                has_cons_def]
        \\ gvs [cml_state_preserved_def])
      >~ [‘do_eq (Litv (IntLit _)) (Litv (IntLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘i' = i’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_cons_def]
        \\ gvs [cml_state_preserved_def])
      >~ [‘do_eq (Litv (StrLit _)) (Litv (StrLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘dfy_str = dfy_str'’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_cons_def]
        \\ gvs [cml_state_preserved_def]))
    \\ gvs [oneline do_bop_def, do_sc_def, AllCaseEqs()]
    \\ gvs [from_bin_op_def]
    \\ gvs [evaluate_def, do_app_def, do_test_def, do_arith_def, check_type_def,
              do_log_def, do_if_def]
    \\ gvs [cml_state_preserved_def])
  >~ [‘ArrLen arr’] >-
   (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ last_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ qexists ‘ck’
    \\ gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def]
    \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs []
    \\ namedCases_on ‘get_array_len arr_v’ ["", "len"] \\ gvs []
    \\ gvs [oneline get_array_len_def, AllCaseEqs()]
    \\ gvs [can_pmatch_all_def, pmatch_def, pat_bindings_def,
            cml_tup_vname_def, num_to_str_11]
    \\ Cases_on ‘env_cml.v’
    \\ gvs [alist_to_ns_def, nsAppend_def, nsLookup_def, num_to_str_11])
  >~ [‘ArrSel arr idx’] >-
   (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
    \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [evaluate_def])
    \\ gvs [evaluate_def]
    \\ rename [‘val_rel _ dfy_arr cml_arr’]
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ ‘¬is_fresh « arr»’ by gvs [is_fresh_def, isprefix_thm]
    \\ drule_all state_rel_env_push_not_fresh \\ gvs []
    \\ disch_then $ qspec_then ‘cml_arr’ assume_tac \\ gvs []
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_cons_def] \\ rpt strip_tac \\ res_tac
      \\ first_assum $ irule_at (Pos last) \\ simp [strcat_def, concat_def])
    \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ drule state_rel_env_pop_not_fresh \\ gvs []
    \\ disch_then $ drule
    \\ rpt strip_tac \\ gvs []
    \\ ‘store_preserve_all t.refs t₂.refs’ by
      (irule store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ reverse $ namedCases_on ‘r’ ["idx_v",  "err"] \\ gvs []
    \\ namedCases_on ‘index_array s₂ dfy_arr idx_v’ ["", "elem"] \\ gvs []
    \\ gvs [oneline index_array_def, oneline val_to_num_def, CaseEq "value",
            CaseEq "option", CaseEq "heap_value"]
    \\ gvs [can_pmatch_all_def, pmatch_def, cml_tup_vname_def,
            pat_bindings_def, num_to_str_11]
    \\ gvs [do_app_def]
    \\ gvs [cml_state_preserved_def]
    \\ drule_all state_rel_llookup \\ rpt strip_tac \\ gvs []
    \\ gvs [INT_ABS]
    \\ drule LIST_REL_LENGTH \\ rpt strip_tac
    \\ gvs [LLOOKUP_EQ_EL, LIST_REL_EL_EQN]
    \\ gvs [state_rel_def])
  >~ [‘map_from_exp []’] >-
   (qexists ‘0’ \\ gvs [from_exp_def, evaluate_exp_def, evaluate_def])
  >~ [‘map_from_exp (e::es)’] >-
   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ reverse $ namedCases_on ‘r’ ["cml_e",  "err"] \\ gvs []
    >- (qexists ‘ck’
        \\ rename [‘_::cml_es’]
        \\ Cases_on ‘cml_es’ \\ gvs [evaluate_def])
    \\ namedCases_on ‘es’ ["", "e' es"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [evaluate_exp_def, from_exp_def])
    \\ namedCases_on ‘evaluate_exps s₁ env_dfy (e'::es')’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rfail’ \\ gvs []
    \\ gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ ‘store_preserve_all t.refs t₂.refs’ by
      (irule store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ reverse $ Cases_on ‘r’ \\ gvs [evaluate_def]
    \\ gvs [cml_state_preserved_def])
  \\ gvs [from_exp_def]  (* These expression do not get compiled *)
QED

Theorem array_rel_submap[local]:
  array_rel m s.heap t.refs ⇒ m ⊑ m |+ (LENGTH s.heap, LENGTH t.refs)
Proof
  gvs [array_rel_def]
  \\ rpt strip_tac
  \\ disj1_tac
  \\ spose_not_then assume_tac
  \\ qpat_assum ‘∀_. _ ∈ FDOM _ ⇒ _ < _’ drule
  \\ rpt strip_tac \\ gvs []
QED

Theorem submap_val_rel[local]:
  val_rel m dfy_v cml_v ∧ m ⊑ m' ⇒ val_rel m' dfy_v cml_v
Proof
  rpt strip_tac \\ gvs [val_rel_cases, SUBMAP_FLOOKUP_EQN]
QED

(* TODO Upstream? *)
Theorem IMP_LIST_REL_REPLICATE[local]:
  P x y ⇒ LIST_REL P (REPLICATE n x) (REPLICATE n y)
Proof
  Cases_on ‘n’ >- simp []
  \\ rewrite_tac [LIST_REL_EL_EQN]
  \\ rpt strip_tac >- simp []
  \\ DEP_REWRITE_TAC [EL_REPLICATE]
  \\ fs []
QED

Theorem array_rel_add[local]:
  array_rel m s.heap (t: 'ffi cml_state).refs ∧
  val_rel m init_v init_cml_v ⇒
  array_rel
    (m |+ (LENGTH s.heap, LENGTH t.refs))
    (SNOC (HArr (REPLICATE (Num i) init_v) ty) s.heap)
    (t.refs ++ [Varray (REPLICATE (Num i) init_cml_v)])
Proof
  rpt strip_tac
  \\ drule submap_val_rel
  \\ disch_then $ qspec_then ‘(m |+ (LENGTH s.heap, LENGTH t.refs))’ mp_tac
  \\ impl_tac >- (irule array_rel_submap \\ gvs [])
  \\ gvs [array_rel_def]
  \\ rpt strip_tac \\ gvs []
  >- (simp [INJ_DEF, TO_FLOOKUP, FAPPLY_FUPDATE_THM]
      \\ qx_genl_tac [‘x’, ‘x'’]
      \\ rpt IF_CASES_TAC
      >- simp []
      >- (rpt strip_tac \\ gvs []
          \\ reverse $ qsuff_tac ‘m ' x' ∈ FRANGE m’
          >- (gvs [TO_FLOOKUP, FLOOKUP_SIMP, GSYM IS_SOME_EQ_NOT_NONE,
                  IS_SOME_EXISTS] \\ first_assum $ irule_at Any)
          \\ rpt strip_tac \\ last_x_assum drule \\ gvs [])
      >- (rpt strip_tac \\ gvs []
          \\ reverse $ qsuff_tac ‘m ' x ∈ FRANGE m’
          >- (gvs [TO_FLOOKUP, FLOOKUP_SIMP, GSYM IS_SOME_EQ_NOT_NONE,
                  IS_SOME_EXISTS] \\ first_assum $ irule_at Any)
          \\ rpt strip_tac \\ last_x_assum drule \\ gvs [])
      \\ rpt strip_tac \\ gvs []
      \\ gvs [TO_FLOOKUP, GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
      \\ drule INJ_FLOOKUP_IMP
      \\ disch_then $ qspecl_then [‘x’, ‘x'’] mp_tac
      \\ disch_then $ drule_all \\ simp [])
  >- (qpat_assum ‘∀_. _ ∈ FDOM _ ⇒ _’ $ drule_then assume_tac
      \\ intLib.COOPER_TAC)
  >- (simp [store_lookup_def, EL_APPEND])
  >- (drule (SRULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET) \\ rpt strip_tac
      \\ qpat_x_assum ‘∀_. _ ∈ FRANGE _ ⇒ _’ $ drule_then assume_tac
      \\ gvs [])
  >- (drule_then assume_tac (SRULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET)
      \\ qpat_x_assum ‘∀_. _ ∈ FRANGE _ ⇒ _’ $ drule_then assume_tac
      \\ fs []
      \\ drule store_lookup_append \\ simp [])
  \\ gvs [LLOOKUP_EQ_EL]
  \\ rename [‘loc < SUC _’]
  \\ Cases_on ‘loc = LENGTH s.heap’ \\ gvs []
  >- (qexistsl [‘LENGTH t.refs’, ‘REPLICATE (Num i) init_cml_v’]
      \\ gvs [EL_LENGTH_SNOC, FLOOKUP_SIMP, EL_LENGTH_APPEND_0,
              store_lookup_def]
      \\ irule IMP_LIST_REL_REPLICATE \\ simp [])
  \\ gvs [FLOOKUP_SIMP, EL_SNOC]
  \\ ‘loc < LENGTH s.heap’ by gvs [] \\ gvs []
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
  \\ gvs [store_lookup_def]
  \\ simp [EL_APPEND]
  \\ irule LIST_REL_mono
  \\ first_assum $ irule_at Any
  \\ rpt strip_tac
  \\ irule submap_val_rel
  \\ first_assum $ irule_at Any
  \\ simp []
  \\ disj1_tac
  \\ strip_tac
  \\ last_x_assum drule
  \\ simp []
QED

Theorem locals_rel_add_array[local]:
  locals_rel m l s.locals t.refs env_cml ∧ m ⊑ m' ⇒
  locals_rel m' l s.locals (t.refs ++ xs) env_cml
Proof
  gvs [locals_rel_def]
  \\ rpt strip_tac
  >- (last_x_assum drule \\ gvs [])
  \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
  \\ gvs [store_lookup_def, EL_APPEND]
  \\ rpt strip_tac
  \\ irule submap_val_rel \\ gvs [SF SFY_ss]
QED

Definition is_extension_def:
  is_extension t_refs m m' ⇔
    (∀cml_loc.
       cml_loc ∈ FRANGE m' ⇒ cml_loc ∈ FRANGE m ∨ (LENGTH t_refs) ≤ cml_loc)
End

Theorem is_extension_same[local,simp]:
  is_extension xs m m
Proof
  simp [is_extension_def]
QED

Theorem is_extension_fupdate[local]:
  LENGTH t_refs ≤ cml_loc ⇒
  is_extension t_refs m (m |+ (dfy_loc, cml_loc))
Proof
  simp [is_extension_def]
  \\ metis_tac [SUBSET_THM, FRANGE_DOMSUB_SUBSET]
QED

Theorem is_extension_decat[local]:
  is_extension (xs ++ ys) m m₁ ⇒
  is_extension xs m m₁
Proof
  simp [is_extension_def]
  \\ rpt strip_tac
  \\ res_tac \\ gvs []
QED

Theorem is_extension_weaken[local]:
  is_extension (xs: v store_v list) m m₁ ∧ LENGTH xs' ≤ LENGTH xs
  ⇒
  is_extension (xs': v store_v list) m m₁
Proof
  simp [is_extension_def]
  \\ rpt strip_tac
  \\ res_tac \\ gvs []
QED

Theorem is_extension_trans[local]:
  is_extension xs m m₁ ∧
  is_extension (ys: v store_v list) (m₁: num |-> num) m₂ ∧
  LENGTH xs ≤ LENGTH ys
  ⇒
  is_extension xs m m₂
Proof
  simp [is_extension_def]
  \\ rpt strip_tac
  \\ res_tac \\ gvs []
QED

Theorem correct_from_rhs_exp:
  ∀s env_dfy rhs_dfy s' r_dfy (t: 'ffi cml_state) env_cml e_cml m l.
    evaluate_rhs_exp s env_dfy rhs_dfy = (s', r_dfy) ∧
    from_rhs_exp rhs_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
    env_rel env_dfy env_cml ∧ is_fresh_rhs_exp rhs_dfy ∧
    r_dfy ≠ Rerr Rfail ⇒
    ∃ck (t': 'ffi cml_state) m' r_cml.
      evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
      (t', r_cml) ∧ store_preserve_all t.refs t'.refs ∧
      state_rel m' l s' t' env_cml ∧ cml_state_preserved t t' ∧
      exp_res_rel m' r_dfy r_cml ∧
      m ⊑ m' ∧ is_extension t.refs m m'
Proof
  Cases_on ‘rhs_dfy’ \\ rpt strip_tac
  >~ [‘ExpRhs e’] >-
   (gvs [evaluate_rhs_exp_def, from_rhs_exp_def]
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t'’, ‘r_cml’] assume_tac
    \\ qexistsl [‘ck’, ‘t'’, ‘m’, ‘r_cml’] \\ gvs [])
  >~ [‘ArrAlloc len init ty’] >-
   (gvs [evaluate_rhs_exp_def]
    \\ gvs [from_rhs_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy len’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["len_v", "err"] \\ gvs []
    >- (qexistsl [‘ck’, ‘t₁’, ‘m’]
        \\ gvs [cml_alloc_arr_def, evaluate_def])
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy init’ ["s₂ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule (cj 1 correct_from_exp)
    \\ disch_then drule
    \\ disch_then $
         qspecl_then
           [‘t₁’,
            ‘env_cml with v := nsBind « len» cml_v env_cml.v’ ,
            ‘m’, ‘l’]
           mp_tac
    \\ ‘¬is_fresh « len»’ by gvs [is_fresh_def, isprefix_thm]
    \\ impl_tac \\ gvs []
    >- (drule_all state_rel_env_push_not_fresh \\ gvs []
        \\ strip_tac
        \\ irule env_rel_env_change
        \\ rpt conj_tac
        >- (fs [env_rel_def] \\ first_assum $ irule_at (Pos last) \\ simp [])
        >- (gvs [env_rel_def, has_cons_def])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt gen_tac \\ disch_tac
        \\ ‘n ≠ « len»’ by (gvs [isprefix_strcat, strcat_def, concat_def])
        \\ simp [])
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ qexists ‘ck' + ck’
    \\ gvs [cml_alloc_arr_def, evaluate_def, do_con_check_def]
    \\ reverse $ namedCases_on ‘r’ ["init_v", "err"] \\ gvs []
    >- (qexists ‘m’
        \\ drule state_rel_env_pop_not_fresh \\ gvs []
        \\ disch_then drule \\ rpt strip_tac \\ gvs []
        \\ gvs [cml_state_preserved_def]
        \\ irule_at Any store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ rename [‘do_app _ _ [len_cml_v; init_cml_v]’]
    \\ namedCases_on ‘alloc_array s₂ len_v init_v ty’ ["", "r"] \\ gvs []
    \\ gvs [alloc_array_def, oneline val_to_num_def,
            CaseEqs ["option", "value"]]
    \\ gvs [do_app_def, store_alloc_def, build_conv_def, INT_ABS]
    \\ qexists ‘m |+ (LENGTH s₂.heap, LENGTH t₂.refs)’
    \\ rpt strip_tac
    >- (irule_at Any store_preserve_all_concat \\ gvs []
        \\ irule_at Any store_preserve_all_trans \\ gvs [SF SFY_ss])
    >- (gvs [state_rel_def]
        \\ irule_at Any array_rel_add \\ gvs []
        \\ irule locals_rel_add_array
        \\ qexists ‘m’
        \\ irule_at Any array_rel_submap \\ gvs []
        \\ irule locals_rel_env_change
        \\ first_assum $ irule_at (Pos last)
        \\ rpt gen_tac \\ disch_tac
        \\ ‘n ≠ « len»’ by (gvs [is_fresh_def, strcat_def, concat_def])
        \\ simp [])
    >- gvs [cml_state_preserved_def]
    >- intLib.COOPER_TAC
    >- gvs [FLOOKUP_SIMP]
    >- (irule array_rel_submap \\ gvs [state_rel_def])
    >- (irule is_extension_fupdate
        \\ imp_res_tac store_preserve_all_length \\ simp []))
QED

Theorem correct_map_from_rhs_exp:
  ∀s env_dfy rhss_dfy s' r_dfy (t: 'ffi cml_state) env_cml es_cml m l.
    evaluate_rhs_exps s env_dfy rhss_dfy = (s', r_dfy) ∧
    result_mmap from_rhs_exp rhss_dfy = INR es_cml ∧
    state_rel m l s t env_cml ∧ env_rel env_dfy env_cml ∧
    EVERY (λrhs. is_fresh_rhs_exp rhs) rhss_dfy ∧
    r_dfy ≠ Rerr Rfail ⇒
    ∃ck (t': 'ffi cml_state) m' r_cml.
      evaluate$evaluate (t with clock := t.clock + ck) env_cml es_cml =
      (t', r_cml) ∧ store_preserve_all t.refs t'.refs ∧
      state_rel m' l s' t' env_cml ∧ cml_state_preserved t t' ∧
      exp_ress_rel m' r_dfy r_cml ∧
      m ⊑ m' ∧ is_extension t.refs m m'
Proof
  Induct_on ‘rhss_dfy’ \\ rpt strip_tac
  >- (gvs [evaluate_rhs_exps_def, result_mmap_def]
      \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  \\ rename [‘rhs_dfy::rhss_dfy’]
  \\ gvs [evaluate_rhs_exps_def]
  \\ namedCases_on ‘evaluate_rhs_exp s env_dfy rhs_dfy’ ["s₁ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ drule_all correct_from_rhs_exp
  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m₁’] mp_tac
  \\ rpt strip_tac
  \\ reverse $ namedCases_on ‘r’ ["rhs_v", "err"] \\ gvs []
  >- (qexists ‘ck’ \\ simp [Once evaluate_cons] \\ gvs [SF SFY_ss])
  \\ namedCases_on ‘evaluate_rhs_exps s₁ env_dfy rhss_dfy’ ["s₂ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
  \\ last_x_assum drule_all
  \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₂’] mp_tac
  \\ rpt strip_tac
  \\ rev_drule evaluate_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck'’ assume_tac
  \\ qexists ‘ck + ck'’ \\ gvs []
  \\ simp [Once evaluate_cons]
  \\ reverse $ namedCases_on ‘r’ ["rhss_v", "err"] \\ gvs []
  \\ qexists ‘m₂’
  \\ ‘store_preserve_all t.refs t₂.refs’ by
    (irule store_preserve_all_trans
     \\ first_assum $ irule_at (Pos hd)\\ simp [])
  \\ ‘is_extension t.refs m m₂’ by
    (irule is_extension_trans
     \\ first_assum $ irule_at (Pos last)
     \\ imp_res_tac store_preserve_all_length
     \\ simp [])
  \\ ‘m ⊑ m₂’ by
    (irule_at Any SUBMAP_TRANS
     \\ first_assum $ irule_at Any \\ simp [])
  \\ simp []
  \\ gvs [cml_state_preserved_def]
  \\ irule submap_val_rel \\ gvs [SF SFY_ss]
QED

(* The base can be at most at our lowest locals or the current length of
   t_refs. *)
Definition base_at_most_def:
  base_at_most base t_refs (l: mlstring |-> num) ⇔
    (base ≤ LENGTH t_refs ∧ ∀i. i ∈ FRANGE l ⇒ base ≤ i)
End

Theorem base_at_most_lupdate[local,simp]:
  base_at_most base (LUPDATE store_v loc xs) l = base_at_most base xs l
Proof
  gvs [base_at_most_def]
QED

Theorem store_preserve_base_at_most[local]:
  store_preserve m base t.refs t'.refs ∧ base_at_most base t.refs l ⇒
  base_at_most base t'.refs l
Proof
  gvs [base_at_most_def, store_preserve_def]
QED

Theorem locals_above_extend[local]:
  base_at_most base t_refs l ⇒
  base_at_most base (t_refs ++ xs) (l |+ (n, LENGTH t_refs))
Proof
  gvs [base_at_most_def] \\ rpt strip_tac \\ gvs []
  \\ drule_then assume_tac (SRULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET)
  \\ gvs []
QED

(* TODO Upstream? *)
Theorem pmatch_list_MAP_Pvar[local]:
  ∀xs vs env refs acc.
    LENGTH xs = LENGTH vs ⇒
    pmatch_list env refs (MAP Pvar xs) vs acc =
    Match (ZIP (REVERSE xs, REVERSE vs) ++ acc)
Proof
  Induct \\ Cases_on ‘vs’ \\ gvs [pmatch_def]
  \\ rewrite_tac [GSYM SNOC_APPEND]
  \\ rpt strip_tac
  \\ DEP_REWRITE_TAC [ZIP_SNOC]
  \\ gvs []
QED

Theorem store_preserve_lupdate_local[local]:
  FLOOKUP l var = SOME loc ∧
  base_at_most base t.refs l ∧
  store_preserve m base (LUPDATE store_v loc t.refs) t'.refs ⇒
  store_preserve m base t.refs t'.refs
Proof
  gvs [store_preserve_def]
  \\ rpt strip_tac
  \\ last_x_assum drule \\ simp []
  \\ rename [‘store_lookup i _ = SOME v’]
  \\ disch_then $ qspec_then ‘v’ mp_tac
  \\ impl_tac \\ gvs []
  \\ gvs [store_lookup_def, base_at_most_def, EL_LUPDATE]
  \\ qsuff_tac ‘i ≠ loc’ \\ gvs []
  \\ drule_then assume_tac (cj 1 FINITE_MAP_LOOKUP_RANGE)
  \\ last_assum $ drule_then assume_tac
  \\ decide_tac
QED

Theorem store_preserve_lupdate_array[local]:
  store_preserve m base (LUPDATE store_v loc t.refs) t'.refs ∧ loc ∈ m ⇒
  store_preserve m base t.refs t'.refs
Proof
  gvs [store_preserve_def]
  \\ rpt strip_tac
  \\ gvs [store_lookup_def, EL_LUPDATE]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem update_array_some_eqs[local]:
  update_array s (ArrV len loc ty) (IntV idx) val = SOME s' ⇒
  s'.clock = s.clock ∧ s'.locals = s.locals ∧
  LENGTH s'.heap = LENGTH s.heap ∧
  ∀loc'. loc' ≠ loc ⇒ LLOOKUP s'.heap loc' = LLOOKUP s.heap loc'
Proof
  rpt strip_tac \\ gvs [update_array_def, LLOOKUP_LUPDATE, AllCaseEqs()]
QED

(* TODO Rename? *)
Theorem update_array_some_llookup[local]:
  update_array s arr_v idx_v rhs_v = SOME s' ⇒
  ∃len loc ty idx arr ty'.
    arr_v = ArrV len loc ty ∧ idx_v = IntV idx ∧ 0 ≤ idx ∧
    LLOOKUP s.heap loc = SOME (HArr arr ty') ∧
    Num idx < LENGTH arr ∧
    LLOOKUP s'.heap loc = SOME (HArr (LUPDATE rhs_v (Num idx) arr) ty')
Proof
  rpt strip_tac
  \\ gvs [update_array_def, oneline val_to_num_def, LLOOKUP_LUPDATE,
          AllCaseEqs()]
  \\ gvs [LLOOKUP_EQ_EL]  (* Needs to come after LLOOKUP_LUPDATE rewrite *)
  \\ intLib.COOPER_TAC
QED

Theorem update_array_state_rel[local]:
  update_array s (ArrV arr_len loc ty) (IntV idx) v = SOME s' ∧
  FLOOKUP m loc = SOME loc_cml ∧
  store_lookup loc_cml t.refs = SOME (Varray varr) ∧
  LLOOKUP s'.heap loc = SOME (HArr (LUPDATE v (Num idx) harr) ty') ∧
  LIST_REL (val_rel m) harr varr ∧
  val_rel m v v_cml ∧
  state_rel m l s t env_cml ⇒
  state_rel
    m l s'
    (t with refs :=
       LUPDATE (Varray (LUPDATE v_cml (Num idx) varr)) loc_cml t.refs)
    env_cml
Proof
  rpt strip_tac
  \\ gvs [state_rel_def]
  \\ drule update_array_some_eqs \\ gvs []
  \\ rpt strip_tac
  >- (* array_rel *)
   (gvs [array_rel_def]
    \\ conj_tac >-
     (rpt strip_tac
      \\ qpat_x_assum ‘∀_. _ ∈ FRANGE _ ⇒ _’ $ drule_then assume_tac
      \\ gvs [store_lookup_def, EL_LUPDATE]
      \\ IF_CASES_TAC \\ gvs [])
    \\ qx_gen_tac ‘loc'’ \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘loc' = loc’ \\ gvs []
    >- (gvs [store_lookup_def, EL_LUPDATE]
        \\ irule EVERY2_LUPDATE_same \\ gvs [])
    \\ first_x_assum drule \\ rpt strip_tac \\ gvs []
    \\ first_x_assum drule \\ rpt strip_tac \\ gvs []
    \\ gvs [store_lookup_def, EL_LUPDATE]
    \\ IF_CASES_TAC \\ gvs [INJ_DEF, FLOOKUP_DEF])
  (* local_rel *)
  \\ gvs [locals_rel_def] \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
  \\ gvs [store_lookup_def, EL_LUPDATE]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem update_local_aux_some[local]:
  ∀s_locals var val new_locals.
    update_local_aux s_locals var val = SOME new_locals ⇒
    ALOOKUP new_locals var = SOME (SOME val) ∧
    (∃ov. ALOOKUP s_locals var = SOME ov) ∧
    (∀var'. var' ≠ var ⇒ ALOOKUP new_locals var' = ALOOKUP s_locals var')
Proof
  Induct_on ‘s_locals’
  \\ gvs [update_local_aux_def]
  \\ qx_genl_tac [‘h’, ‘var’, ‘val’, ‘new_locals’]
  \\ namedCases_on ‘h’ ["x w"] \\ gvs []
  \\ rpt strip_tac
  \\ Cases_on ‘x = var’
  \\ gvs [update_local_aux_def, CaseEq "option"]
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
QED

Theorem lookup_locals_some[local]:
  state_rel m l s t env_cml ∧
  ALOOKUP s.locals var = SOME ov ∧ is_fresh var ⇒
  ∃loc cml_v.
    FLOOKUP l var = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    nsLookup env_cml.v (Short var) = SOME (Loc T loc)
Proof
  rpt strip_tac
  \\ gvs [state_rel_def, locals_rel_def]
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
QED

Theorem update_local_some_eqs[local]:
  update_local s var val = SOME s' ⇒
  s'.clock = s.clock ∧ s'.heap = s.heap
Proof
  rpt strip_tac \\ gvs [update_local_def, CaseEq "option"]
QED

Theorem update_local_some_alookup[local]:
  update_local s var val = SOME s' ⇒
  ALOOKUP s'.locals var = SOME (SOME val) ∧
  (∃ov. ALOOKUP s.locals var = SOME ov) ∧
  ∀var'. var' ≠ var ⇒ ALOOKUP s'.locals var' = ALOOKUP s.locals var'
Proof
  strip_tac
  \\ irule update_local_aux_some
  \\ gvs [update_local_def, CaseEq "option"]
QED

Theorem update_local_state_rel[local]:
  update_local s var new_v_dfy = SOME s' ∧
  is_fresh var ∧
  state_rel m l s t env_cml ∧
  FLOOKUP l var = SOME loc ∧
  store_lookup loc t.refs = SOME (Refv old_v_cml) ∧
  nsLookup env_cml.v (Short var) = SOME (Loc T loc) ∧
  val_rel m new_v_dfy new_v_cml
  ⇒
  state_rel m l s'
  (t with refs := LUPDATE (Refv new_v_cml) loc t.refs) env_cml
Proof
  rpt strip_tac
  \\ drule update_local_some_alookup \\ rpt strip_tac \\ gvs []
  \\ gvs [state_rel_def]
  \\ drule update_local_some_eqs \\ gvs []
  \\ disch_then kall_tac \\ rpt strip_tac
  >~ [‘array_rel _ _ _’] >-
   (gvs [array_rel_def] \\ rpt strip_tac
    \\ first_x_assum drule \\ rpt strip_tac
    \\ gvs [store_lookup_def, EL_LUPDATE]
    \\ IF_CASES_TAC \\ gvs [])
  \\ gvs [locals_rel_def]
  \\ qx_genl_tac [‘var'’] \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘var' ≠ var’ \\ gvs []
  >- (first_x_assum drule \\ rpt strip_tac \\ gvs []
      \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
      \\ gvs [store_lookup_def, EL_LUPDATE]
      \\ IF_CASES_TAC >- (gvs [INJ_DEF, FLOOKUP_DEF])
      \\ gvs [])
  \\ gvs [store_lookup_def, EL_LUPDATE]
QED

(* TODO Remove record accesses *)
Theorem store_preserve_trans[local]:
  store_preserve (FRANGE m) base t_refs t₁_refs ∧
  store_preserve (FRANGE m₁) base
    (t₁_refs: v store_v list) (t₂_refs: v store_v list) ∧
  is_extension t_refs (m: num |-> num) (m₁: num |-> num)
  ⇒
  store_preserve (FRANGE m) base t_refs t₂_refs
Proof
  simp [store_preserve_def, is_extension_def]
  \\ rpt strip_tac
  \\ last_x_assum $ drule_all_then assume_tac
  \\ Cases_on ‘i ∈ FRANGE m₁’ \\ gvs []
  \\ first_x_assum drule \\ strip_tac
  \\ gvs [store_lookup_def]
QED

Theorem evaluate_assign_values[local]:
  ∀s env_dfy lhss rhs_vs s' r_dfy names asss_cml cml_vs m l (t: 'ffi cml_state)
     env_cml base.
    assign_values s env_dfy lhss rhs_vs = (s', r_dfy) ∧
    result_mmap2 assign_single lhss (MAP (Var ∘ Short) names) = INR asss_cml ∧
    state_rel m l s t env_cml ∧
    env_rel env_dfy env_cml ∧
    LIST_REL (val_rel m) rhs_vs cml_vs ∧
    LIST_REL (λn v. nsLookup env_cml.v (Short n) = SOME v) names cml_vs ∧
    EVERY (λlhs. is_fresh_lhs_exp lhs) lhss ∧
    EVERY (λn. « arr» ≠ n) names ∧
    base_at_most base t.refs l ∧
    r_dfy ≠ Rstop (Serr Rfail) ⇒
    ∃ck t' r_cml.
      evaluate (t with clock := t.clock + ck) env_cml [Seqs asss_cml] =
      (t', r_cml) ∧
      store_preserve (FRANGE m) base t.refs t'.refs ∧
      state_rel m l s' t' env_cml ∧ cml_state_preserved t t' ∧
      stmt_res_rel r_dfy r_cml
Proof
  Induct_on ‘lhss’ \\ Cases_on ‘rhs_vs’ \\ gvs [assign_values_def]
  \\ rpt strip_tac
  >- (gvs [result_mmap2_def, Seqs_def, evaluate_def, do_con_check_def,
           build_conv_def] \\ qexists ‘0’ \\ gvs [])
  \\ gvs [result_mmap2_def, oneline bind_def, CaseEq "sum"]
  \\ rename [‘assign_value _ _ lhs rhs_v’,
             ‘result_mmap2 _ _ _ = INR ass_rest_cml'’]
  \\ gvs [Seqs_def, evaluate_def]
  \\ namedCases_on ‘lhs’ ["var", "arr idx"]
  \\ gvs [assign_single_def, assign_value_def, oneline bind_def, CaseEq "sum"]
  \\ rename [‘state_rel _ _ _ t _’, ‘assign_values _ _ _ rhs_vs_rest’]
  >- (* Variable assignment *)
   (namedCases_on ‘update_local s var rhs_v’ ["", "s₁"] \\ gvs []
    \\ drule update_local_some_alookup \\ rpt strip_tac \\ gvs []
    \\ drule_all lookup_locals_some
    \\ disch_then $ qx_choosel_then [‘loc_cml’, ‘old_v_cml’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def, do_app_def, store_assign_def, store_lookup_def,
            store_v_same_type_def]
    \\ last_x_assum drule
    \\ disch_then $ drule_at (Pos hd)
    \\ ntac 2 (disch_then $ drule_at (Pos $ el 2)) \\ gvs []
    \\ rename [‘LUPDATE (Refv rhs_v_cml)’]
    \\ disch_then $
         qspecl_then
           [‘l’,
            ‘t with refs := LUPDATE (Refv rhs_v_cml) loc_cml t.refs’,
            ‘base’]
           mp_tac
    \\ impl_tac >-
     (irule_at Any update_local_state_rel
      \\ gvs [base_at_most_def, store_lookup_def]
      \\ rpt (first_assum $ irule_at Any))
    \\ gvs []
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t'’] mp_tac \\ rpt strip_tac
    \\ qexists ‘ck’ \\ gvs []
    \\ gvs [cml_state_preserved_def]
    \\ irule store_preserve_lupdate_local
    \\ rpt (last_assum $ irule_at Any))
  (* Array update *)
  \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
  \\ drule_all (cj 1 correct_from_exp)
  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac \\ rpt strip_tac \\ gvs []
  \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
  >- (qexists ‘ck’
      \\ gvs [evaluate_def, store_preserve_all_def, store_preserve_def,
              store_lookup_def])
  \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
  \\ drule (cj 1 correct_from_exp)
  \\ disch_then drule
  \\ disch_then $
       qspecl_then
         [‘t₁’,
          ‘env_cml with v := nsBind « arr» cml_v env_cml.v’ ,
          ‘m’, ‘l’]
       mp_tac
  \\ ‘¬is_fresh « arr»’ by gvs [is_fresh_def, isprefix_thm]
  \\ impl_tac \\ gvs []
  >- (drule_all state_rel_env_push_not_fresh \\ gvs []
      \\ strip_tac
      \\ irule env_rel_env_change
      \\ rpt conj_tac
      >- (fs [env_rel_def] \\ first_assum $ irule_at (Pos last) \\ simp [])
      >- (gvs [env_rel_def, has_cons_def])
      \\ first_assum $ irule_at (Pos last)
      \\ rpt gen_tac \\ disch_tac
      \\ rename [‘isPrefix «dfy_» n’]
      \\ ‘n ≠ « arr»’ by (gvs [isprefix_strcat, strcat_def, concat_def])
      \\ simp [])
  \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’] mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ reverse $ namedCases_on ‘r’ ["idx_v", "err"] \\ gvs []
  >- (* Evaluation of index failed *)
   (qexists ‘ck₁ + ck’ \\ gvs []
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck₁’ assume_tac \\ gvs []
    \\ gvs [evaluate_def]
    \\ irule_at Any state_rel_env_pop_not_fresh
    \\ rpt (first_assum $ irule_at Any \\ gvs [])
    \\ gvs [cml_state_preserved_def]
    \\ irule store_preserve_all_weaken
    \\ irule store_preserve_all_trans
    \\ gvs [SF SFY_ss])
  (* Performing the array update *)
  \\ namedCases_on ‘update_array s₂ arr_v idx_v rhs_v’ ["", "s₃"] \\ gvs []
  \\ drule update_array_some_llookup
  \\ disch_then $
       qx_choosel_then
         [‘arr_len’, ‘arr_loc’, ‘arr_ty’, ‘idx_int’, ‘harr’, ‘harr_ty’]
         assume_tac
  \\ gvs []
  \\ rename [‘val_rel _ _ rhs_v_cml’, ‘Loc T loc_cml’]
  \\ drule_all state_rel_llookup
  \\ disch_then $ qx_choose_then ‘varr’ assume_tac \\ gvs []
  \\ last_x_assum drule
  \\ disch_then drule
  \\ ntac 4 (disch_then $ drule_at (Pos $ el 2)) \\ gvs []
  \\ disch_then $
       qspecl_then
         [‘l’,
          ‘t₂ with refs :=
             LUPDATE (Varray (LUPDATE rhs_v_cml (Num idx_int) varr))
                     loc_cml t₂.refs’,
          ‘base’] mp_tac
  \\ impl_tac \\ gvs [] >-
   (irule_at Any update_array_state_rel \\ gvs []
    \\ rpt (last_assum $ irule_at Any)
    \\ irule_at Any state_rel_env_pop_not_fresh
    \\ rpt (last_assum $ irule_at Any \\ gvs [])
    \\ gvs [base_at_most_def, store_preserve_all_def, store_preserve_def])
  \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’] mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ qexists ‘ck₂ + ck₁ + ck’
  \\ rev_dxrule evaluate_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck₂ + ck₁’ assume_tac \\ gvs []
  \\ rev_dxrule evaluate_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac \\ gvs []
  \\ gvs [evaluate_def]
  \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
  \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
  \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, pat_bindings_def,
          cml_tup_vname_def, num_to_str_11, do_app_def]
  \\ ‘¬(idx_int < 0)’ by intLib.COOPER_TAC \\ gvs [INT_ABS]
  \\ ‘Num idx_int < LENGTH varr’ by (drule LIST_REL_LENGTH \\ gvs []) \\ gvs []
  \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
  \\ gvs [cml_state_preserved_def]
  \\ irule store_preserve_trans
  \\ qexists ‘m’ \\ simp []
  \\ irule_at (Pos hd) store_preserve_all_weaken
  \\ last_assum $ irule_at (Pos hd)
  \\ irule store_preserve_trans
  \\ qexists ‘m’ \\ simp []
  \\ irule_at (Pos hd) store_preserve_all_weaken
  \\ last_assum $ irule_at (Pos hd)
  \\ irule store_preserve_lupdate_array
  \\ gvs [store_lookup_def]
  \\ rpt (last_assum $ irule_at Any)
  \\ imp_res_tac FINITE_MAP_LOOKUP_RANGE
QED

(* TODO Why does this work *)
Theorem cml_tup_vname_neq_arr[local]:
  cml_tup_vname n ≠ « arr»
Proof
  simp [cml_tup_vname_def]
  \\ Cases_on ‘toString n’
  \\ imp_res_tac num_to_str_imp_cons
  \\ simp [strcat_def, concat_def]
  \\ strip_tac \\ fs []
QED

Theorem all_distinct_genlist_cml_tup_vname[local]:
  ALL_DISTINCT (GENLIST (λn. cml_tup_vname n) len)
Proof
  simp [ALL_DISTINCT_GENLIST, cml_tup_vname_def, num_to_str_11]
QED

Theorem ALL_DISTINCT_pats_bindings[local]:
  ∀xs ys.
    ALL_DISTINCT (xs ++ ys) ⇒
    ALL_DISTINCT (pats_bindings (MAP Pvar xs) ys)
Proof
  Induct_on ‘xs’ \\ gvs [pat_bindings_def]
  \\ rpt strip_tac \\ gvs [ALL_DISTINCT_APPEND]
QED

Theorem state_rel_pop_env_while[local]:
  state_rel m l s t
    (env with v := nsBind «» v₀ (nsBind (loop_name lvl) v₁ env.v)) ⇒
  state_rel m l s t env
Proof
  rpt strip_tac
  \\ irule state_rel_env_pop_not_fresh
  \\ ‘¬is_fresh (loop_name lvl)’ by
    gvs [loop_name_def, is_fresh_def, isprefix_thm]
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ irule_at (Pos hd) state_rel_env_pop_not_fresh
  \\ ‘¬is_fresh «»’ by gvs [is_fresh_def, isprefix_thm]
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ first_assum $ irule_at Any
QED

Theorem evaluate_cml_new_refs[local]:
  ∀s env ns e.
    evaluate s env [cml_new_refs ns e] =
    evaluate
      (s with refs := s.refs ++ REPLICATE (LENGTH ns) (Refv (Litv (IntLit 0))))
      (env with v := add_refs_to_env env.v ns (LENGTH s.refs))
      [e]
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  >- (gvs [cml_new_refs_def, add_refs_to_env_def, enumerate_from_def,
           semanticPrimitivesTheory.state_component_equality])
  \\ gvs [cml_new_refs_def, evaluate_def, do_app_def, store_alloc_def]
  \\ gvs [add_refs_to_env_cons, APPEND_ASSOC_CONS]
QED

(* TODO Upstream? *)
Theorem NOT_MEM_FLOOKUP_UPDATE_LIST[local]:
  ¬MEM x (MAP FST l) ⇒ FLOOKUP (m |++ l) x = FLOOKUP m x
Proof
  rpt strip_tac
  \\ gvs [flookup_fupdate_list, CaseEq "option"]
  \\ disj1_tac
  \\ gvs [ALOOKUP_NONE, MAP_REVERSE]
QED

Theorem locals_rel_decl_uninit_vars[local]:
  locals_rel m l s_locals t_refs env_v ∧
  ALL_DISTINCT vars ∧
  (∀v. MEM v vars ⇒ ¬MEM v (MAP FST s_locals)) ⇒
  locals_rel m (l |++ enumerate_from (LENGTH t_refs) vars)
    ((REVERSE (ZIP (vars, REPLICATE (LENGTH vars) NONE))) ++ s_locals)
    (t_refs ++ REPLICATE (LENGTH vars) (Refv init))
    (add_refs_to_env env_v vars (LENGTH t_refs))
Proof
  gvs [locals_rel_def, ALL_DISTINCT_APPEND]
  \\ rpt strip_tac
  >- (* INJ (l |++ enumerate_from ...) *)
   (simp [INJ_DEF, TO_FLOOKUP]
    \\ rpt strip_tac
    \\ gvs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
    \\ gvs [flookup_update_list_some]
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [MEM_EL, enumerate_from_def]
    >- (rename [‘FLOOKUP _ _ = SOME (i + _)’]
        \\ ‘i + LENGTH t_refs ∈ FRANGE l’ by
          (simp [TO_FLOOKUP] \\ first_assum $ irule_at Any)
        \\ last_x_assum drule \\ gvs [])
    >- (rename [‘FLOOKUP _ _ = SOME (i + _)’]
        \\ ‘i + LENGTH t_refs ∈ FRANGE l’ by
          (simp [TO_FLOOKUP] \\ first_assum $ irule_at Any)
        \\ last_x_assum drule \\ gvs [])
    \\ gvs [INJ_DEF, TO_FLOOKUP])
  >- (* FRANGE < LENGTH vars + LENGTH t_refs *)
   (pop_assum mp_tac
    \\ simp [TO_FLOOKUP, flookup_update_list_some]
    \\ rpt strip_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ gvs [MEM_EL, enumerate_from_def]
    \\ rename [‘FLOOKUP _ _ = SOME i’]
    \\ ‘i ∈ FRANGE l’ by
      (simp [TO_FLOOKUP] \\ first_assum $ irule_at Any)
    \\ last_x_assum drule \\ simp [])
  \\ qmatch_asmsub_abbrev_tac ‘ZIP (vars, nones)’
  \\ ‘LENGTH nones = LENGTH vars’ by gvs [Abbr ‘nones’]
  \\ ‘ALL_DISTINCT (MAP FST (ZIP (vars, nones)))’ by
    gvs [REVERSE_ZIP, MAP_ZIP]
  \\ gvs [ALOOKUP_APPEND, CaseEq "option"]
  >- (* already existing variable *)
   (first_x_assum drule_all
    \\ rpt strip_tac \\ gvs []
    \\ rename [‘FLOOKUP _ var = _’]
    (* TODO There must be a cleaner way to do this: *)
    (*    ALOOKUP xs x = SOME v ⇒ MEM x (MAP FST xs) *)
    \\ ‘MEM var (MAP FST s_locals)’ by
      (spose_not_then assume_tac \\ gvs [iffRL ALOOKUP_NONE])
    \\ DEP_REWRITE_TAC [NOT_MEM_FLOOKUP_UPDATE_LIST] \\ gvs []
    \\ strip_tac >- (spose_not_then assume_tac \\ gvs [])
    \\ gvs [store_lookup_def, EL_APPEND]
    \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env] \\ gvs []
    \\ rpt strip_tac \\ gvs [])
  (* in the added variables *)
  \\ drule alookup_distinct_reverse \\ rpt strip_tac \\ gvs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule ALOOKUP_find_index_SOME
  \\ disch_then $ qx_choose_then ‘i’ assume_tac \\ gvs []
  \\ gvs [MAP_ZIP, find_index_ALL_DISTINCT_EL_eq,
          flookup_update_list_some]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse, ALOOKUP_enumerate_from]
  \\ gvs [store_lookup_def, EL_APPEND, EL_REPLICATE, EL_ZIP, Abbr ‘nones’,
          nsLookup_add_refs_to_env]
QED

Theorem locals_rel_decl_uninit_var[local]:
  locals_rel m l s.locals t.refs env_v ∧
  ¬MEM n (MAP FST s.locals) ⇒
  locals_rel m (l |+ (n,LENGTH t.refs)) ((n,NONE)::s.locals)
    (t.refs ++ [Refv (Litv (IntLit 0))])
    (nsBind n (Loc T (LENGTH t.refs)) env_v)
Proof
  rpt strip_tac
  \\ drule locals_rel_decl_uninit_vars
  \\ disch_then $ qspecl_then [‘[n]’, ‘Litv (IntLit 0)’] mp_tac
  \\ gvs [enumerate_from_def, add_refs_to_env_def,
          FUPDATE_EQ_FUPDATE_LIST]
  \\ pure_rewrite_tac [ONE, REPLICATE] \\ gvs []
QED

Theorem locals_rel_mk_locals_map_outs[local]:
  ALL_DISTINCT (MAP FST outs) ⇒
  locals_rel m (mk_locals_map (MAP FST outs) (LENGTH t_refs))
    (REVERSE (ZIP (MAP FST outs, REPLICATE (LENGTH outs) NONE)))
    (t_refs ++ REPLICATE (LENGTH outs) (Refv (Litv (IntLit 0))))
    (add_refs_to_env env_v (MAP FST outs) (LENGTH t_refs))
Proof
  gvs [mk_locals_map_def]
  \\ ‘locals_rel m FEMPTY [] t_refs env_v’ by gvs [locals_rel_def]
  \\ drule locals_rel_decl_uninit_vars \\ gvs []
  \\ disch_then $ qspecl_then [‘MAP FST outs’, ‘Litv (IntLit 0)’] mp_tac
  \\ gvs [MAP_MAP_o]
QED

Theorem locals_rel_mk_locals_map_ins[local]:
  ALL_DISTINCT (MAP FST ins) ∧
  LIST_REL (val_rel m) in_vs in_vs_cml ∧
  LENGTH in_vs = LENGTH ins ⇒
  locals_rel m (mk_locals_map (MAP FST ins) (LENGTH t_refs))
    (REVERSE (ZIP (MAP FST ins, MAP SOME in_vs)))
    (t_refs ++ MAP Refv in_vs_cml)
    (add_refs_to_env env_v (MAP FST ins) (LENGTH t_refs))
Proof
  (* The only time where we add a variable and initialize it at the same
     is when initializing the in-parameters when setting up a call. Thus,
     we don't need to write a more general theorem like
     locals_rel_decl_uninit_vars. *)
  gvs [locals_rel_def]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  >- (irule inj_mk_locals_map)
  >- (imp_res_tac FRANGE_mk_locals_map \\ gvs [])
  \\ qpat_x_assum ‘ALOOKUP _ _ = _’ mp_tac
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse] \\ gvs [MAP_ZIP]
  \\ rpt strip_tac
  \\ drule ALOOKUP_find_index_SOME
  \\ disch_then $ qx_choose_then ‘i’ assume_tac \\ gvs []
  \\ gvs [MAP_ZIP, find_index_ALL_DISTINCT_EL_eq,
          flookup_update_list_some]
  \\ DEP_REWRITE_TAC [FLOOKUP_mk_locals_map] \\ gvs []
  \\ gvs [store_lookup_def, EL_APPEND, EL_MAP, EL_ZIP]
  \\ drule nsLookup_add_refs_to_env \\ gvs []
  \\ disch_then drule \\ gvs [EL_MAP, MAP_MAP_o]
  \\ disch_then kall_tac
  \\ gvs [LIST_REL_EL_EQN]
QED

Theorem locals_mk_locals_map_ins_outs[local]:
  ALL_DISTINCT (MAP FST ins ++ MAP FST outs) ∧
  LIST_REL (val_rel m) in_vs cml_vs ∧
  LENGTH in_vs = LENGTH ins ⇒
  locals_rel m (mk_locals_map (MAP FST ins ++ MAP FST outs) (LENGTH t.refs))
    (REVERSE
       (ZIP (MAP FST ins, MAP SOME in_vs) ++
        ZIP (MAP FST outs, REPLICATE (LENGTH outs) NONE)))
    (t.refs ++ MAP Refv cml_vs ++
       REPLICATE (LENGTH outs) (Refv (Litv (IntLit 0))))
    (add_refs_to_env
       (add_refs_to_env env.v (MAP FST ins) (LENGTH t.refs))
       (MAP FST outs)
       (LENGTH t.refs + LENGTH cml_vs))
Proof
  rpt strip_tac
  \\ gvs [ALL_DISTINCT_APPEND]
  (* mk_locals_map (MAP FST ins) *)
  \\ rev_drule_all locals_rel_mk_locals_map_ins \\ gvs []
  \\ disch_then $ qspecl_then [‘t.refs’, ‘env.v’] assume_tac
  (* Add uninitialized outs to locals *)
  \\ drule locals_rel_decl_uninit_vars \\ gvs [REVERSE_ZIP, MAP_ZIP]
  \\ disch_then drule \\ gvs []
  \\ disch_then $ qspec_then ‘Litv (IntLit 0)’ mp_tac \\ gvs []
  \\ ‘LENGTH cml_vs = LENGTH in_vs’ by
    (imp_res_tac LIST_REL_LENGTH \\ gvs []) \\ gvs []
  \\ gvs [mk_locals_map_append]
  \\ gvs [MAP_MAP_o, REVERSE_APPEND, REVERSE_ZIP]
  \\ impl_tac >- metis_tac [] \\ gvs []
QED

Theorem locals_rel_submap[local]:
  locals_rel m l s.locals t.refs env_cml ∧ m ⊑ m' ⇒
  locals_rel m' l s.locals t.refs env_cml
Proof
  gvs [locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
  \\ rpt strip_tac
  \\ irule submap_val_rel
  \\ last_assum $ irule_at (Pos hd)
  \\ gvs []
QED

Theorem evaluate_cml_read_var[local]:
  read_local s.locals var = SOME val ∧
  state_rel m l s (t: 'ffi cml_state) env ∧
  is_fresh var ⇒
  ∃val_cml.
    evaluate t env [cml_read_var var] =
    (t, Rval [val_cml]) ∧ val_rel m val val_cml
Proof
  rpt strip_tac
  \\ drule_all read_local_some_imp
  \\ rpt strip_tac
  \\ gvs [evaluate_def, cml_read_var_def, do_app_def]
QED

Theorem evaluate_map_cml_read_var[local]:
  ∀s vars vals m l t env.
    OPT_MMAP (read_local s.locals) vars = SOME vals ∧
    state_rel m l s (t: 'ffi cml_state) env ∧
    EVERY (λv. is_fresh v) vars ⇒
    ∃val_cmls.
      evaluate t env (REVERSE (MAP cml_read_var vars)) =
      (t, Rval val_cmls) ∧ LIST_REL (val_rel m) vals (REVERSE val_cmls)
Proof
  Induct_on ‘vars’ \\ gvs []
  \\ rpt strip_tac
  \\ drule_all read_local_some_imp \\ rpt strip_tac
  \\ last_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
  \\ gvs [evaluate_append, cml_read_var_def, evaluate_def, do_app_def]
QED

Theorem locals_rel_array_rel_store_preserve_imp[local]:
  locals_rel m l s₁.locals (t: 'ffi cml_state).refs env_cml.v ∧
  array_rel m xs t.refs ∧
  store_preserve (FRANGE m) (LENGTH t.refs) t.refs (t₂: 'ffi cml_state).refs
  ⇒
  locals_rel m l s₁.locals t₂.refs env_cml.v
Proof
  rpt strip_tac
  \\ drule_then assume_tac store_preserve_length
  \\ gvs [locals_rel_def, array_rel_def, store_preserve_def]
  \\ rpt strip_tac \\ gvs []
  >-
   (qpat_x_assum ‘∀_. _ ∈ FRANGE _ ⇒ _’ $ drule_then assume_tac \\ gvs [])
  \\ last_x_assum $ drule_all_then assume_tac \\ gvs []
  \\ rename [‘store_lookup loc’]
  \\ ‘loc ∉ FRANGE m’ by
    (spose_not_then assume_tac \\ gvs []
     \\ qpat_x_assum ‘∀_. _ ∈ FRANGE m ⇒ _’ $ drule_then assume_tac
     \\ gvs [])
  \\ gvs [store_lookup_def]
QED

Theorem state_rel_restore_caller1[local]:
  state_rel m l s (t: 'ffi cml_state) env ∧
  state_rel m' l' s' (t': 'ffi cml_state) env' ∧
  store_preserve (FRANGE m) (LENGTH t.refs) t.refs t'.refs ∧ m ⊑ m' ⇒
  state_rel m' l (restore_caller s' s) t' env
Proof
  rpt strip_tac
  \\ gvs [restore_caller_def, state_rel_def]
  \\ irule locals_rel_submap
  \\ first_assum $ irule_at (Pos hd)
  \\ irule locals_rel_array_rel_store_preserve_imp
  \\ first_assum $ irule_at (Pos hd)
  \\ simp []
QED

Theorem GENLIST_lambda_MAP[local]:
  GENLIST (λx. f (g x)) len = MAP f (GENLIST (λx. g x) len)
Proof
  gvs [MAP_GENLIST, o_DEF]
QED

Theorem GENLIST_MAP_Pvar[local]:
  GENLIST (λn. Pvar (cml_tup_vname n)) len =
  MAP Pvar (GENLIST (λn. cml_tup_vname n) len)
Proof
  gvs [GENLIST_lambda_MAP]
QED

Theorem evaluate_map_var_short[local]:
  ∀env vars vals t.
    LIST_REL (λn v. nsLookup env.v (Short n) = SOME v) vars vals ⇒
    evaluate (t: 'ffi cml_state) env (MAP (Var ∘ Short) vars) = (t, Rval vals)
Proof
  Induct_on ‘vars’ \\ Cases_on ‘vals’ \\ gvs []
  \\ rpt strip_tac
  \\ last_x_assum drule \\ gvs []
  \\ simp [Once evaluate_cons]
  \\ gvs [evaluate_def]
QED

Theorem evaluate_Apps_with_clock[local]:
  ∀xs (st:'ffi cml_state) env s1 s2 vs ck.
    evaluate st env xs = (s1,Rval vs) ∧
    LENGTH xs = SUC (LENGTH ns) ∧
    nsLookup env.v n = SOME clos_v ∧
    do_opapp [clos_v; LAST vs] = SOME (env1,Funs ns e) ⇒
    evaluate (st with clock := st.clock + ck) env [Apps (Var n) (REVERSE xs)] =
    if (s1.clock + ck) < LENGTH xs then
      (s1 with clock := 0,Rerr (Rabort Rtimeout_error))
    else
      evaluate
        (s1 with clock := s1.clock + ck - LENGTH xs)
        (env1 with v := nsAppend (alist_to_ns (ZIP (REVERSE ns,BUTLAST vs))) env1.v) [e]
Proof
  rpt strip_tac
  \\ drule evaluate_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck’ assume_tac
  \\ drule_all evaluate_Apps \\ gvs []
QED

Theorem nsappend_alist_to_ns_concat[local]:
  ∀xs ys ns.
    nsAppend (alist_to_ns (xs ++ ys)) ns =
    nsAppend (alist_to_ns xs) (nsAppend (alist_to_ns ys) ns)
Proof
  gvs []
QED

Theorem is_fresh_cml_tup_vname_neq[local]:
  is_fresh n ⇒ n ≠ cml_tup_vname i
Proof
  rpt strip_tac \\ gvs [is_fresh_def, isprefix_thm, cml_tup_vname_def]
QED

Theorem dfy_pfx_cml_tup_vname_neq[local]:
  isPrefix «dfy_» n ⇒ n ≠ cml_tup_vname i
Proof
  rpt strip_tac \\ gvs [cml_tup_vname_def, isprefix_thm]
QED

Theorem is_fresh_neq_cml_tup_vname[local]:
  is_fresh n ⇒ n ≠ cml_tup_vname i
Proof
  simp [cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Theorem is_fresh_not_mem_genlist[local]:
  ∀n. is_fresh n ⇒ ¬MEM n (GENLIST (λn. cml_tup_vname n) len)
Proof
  rpt strip_tac
  \\ gvs [MEM_GENLIST, cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Theorem dfy_pfx_not_mem_genlist[local]:
  ∀n. isPrefix «dfy_» n ⇒ ¬MEM n (GENLIST (λn. cml_tup_vname n) len)
Proof
  rpt strip_tac
  \\ gvs [MEM_GENLIST, cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Theorem int_to_string_not_mem_genlist[local]:
  ∀len. ¬MEM cml_int_to_string_name (GENLIST (λn. cml_tup_vname n) len)
Proof
  gvs [MEM_GENLIST, cml_tup_vname_def, strcat_def, concat_def]
QED

Theorem MEM_LAST[local]:
  xs ≠ [] ⇒ MEM (LAST xs) xs
Proof
  Induct_on ‘xs’ using SNOC_INDUCT \\ gvs []
QED

Theorem store_preserve_append[local]:
  store_preserve m base xs ys ⇒
  store_preserve m base xs (ys ++ zs)
Proof
  simp [store_preserve_def]
  \\ rpt strip_tac
  \\ irule store_lookup_append \\ simp []
QED

Theorem state_rel_refs_append[local]:
  state_rel m l s t env ⇒
  state_rel m l s (t with refs := t.refs ++ xs) env
Proof
  simp [state_rel_def]
  \\ rpt strip_tac
  >- (drule_all array_rel_append \\ simp [])
  (* locals_rel *)
  \\ gvs [locals_rel_def]
  \\ rpt strip_tac
  >- (first_x_assum $ drule_then assume_tac \\ simp [])
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ simp []
  \\ rename [‘store_lookup _ _ = SOME (Refv cml_v)’]
  \\ qexists ‘cml_v’ \\ simp []
  \\ irule store_lookup_append \\ simp []
QED

Theorem is_fresh_not_int_to_string[local]:
  is_fresh n ⇒ n ≠ cml_int_to_string_name
Proof
  simp [is_fresh_def, isprefix_thm]
  \\ CASE_TAC \\ gvs []
QED

Theorem store_preserve_is_extension[local]:
  store_preserve (FRANGE m₁) base t.refs t₁.refs ∧
  is_extension t.refs m m₁ ∧ m ⊑ m₁
  ⇒
  store_preserve (FRANGE m) base t.refs t₁.refs
Proof
  simp [is_extension_def, store_preserve_def]
  \\ rpt strip_tac
  \\ Cases_on ‘i ∈ FRANGE m₁’ \\ gvs []
  \\ first_x_assum $ drule_then assume_tac \\ gvs []
  \\ gvs [store_lookup_def]
QED

Theorem isPrefix_dfy_v_neq[local]:
  isPrefix «dfy_» n₁ ∧ isPrefix «v» n₂ ⇒ n₁ ≠ n₂
Proof
  rpt strip_tac \\ gvs [isprefix_strcat, strcat_def, concat_def]
QED

(* TODO split up cases into separate trivialities like other compiler proofs *)
Theorem correct_from_stmt:
  ∀s env_dfy stmt_dfy s' r_dfy lvl (t: 'ffi cml_state) env_cml e_cml m l base.
    evaluate_stmt s env_dfy stmt_dfy = (s', r_dfy) ∧
    from_stmt stmt_dfy lvl = INR e_cml ∧ state_rel m l s t env_cml ∧
    base_at_most base t.refs l ∧
    env_rel env_dfy env_cml ∧ is_fresh_stmt stmt_dfy ∧
    no_shadow (set (MAP FST s.locals)) stmt_dfy ∧
    no_assert_stmt stmt_dfy ∧
    r_dfy ≠ Rstop (Serr Rfail)
    ⇒ ∃ck (t': 'ffi cml_state) m' r_cml.
        evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
        (t', r_cml) ∧
        store_preserve (FRANGE m) base t.refs t'.refs ∧
        state_rel m' l s' t' env_cml ∧
        cml_state_preserved t t' ∧
        m ⊑ m' ∧ is_extension t.refs m m' ∧
        stmt_res_rel r_dfy r_cml
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt strip_tac \\ fs [no_assert_stmt_def]
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, evaluate_def, do_con_check_def,
         build_conv_def]
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_stmt s env_dfy stmt₁’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rstop (Serr Rfail)’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
    \\ first_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs []
        \\ namedCases_on ‘stp’ ["", "err"] \\ gvs [SF SFY_ss]
        \\ Cases_on ‘err’ \\ gvs [SF SFY_ss])
    \\ rev_drule_at (Pos hd) no_shadow_evaluate_stmt
    \\ disch_then drule
    \\ drule_at (Pos hd) no_shadow_evaluate_stmt
    \\ disch_then drule \\ rpt strip_tac \\ gvs []
    \\ drule_all_then assume_tac store_preserve_base_at_most
    \\ last_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₂’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ qexists ‘ck' + ck’ \\ gvs []
    \\ qexists ‘m₂’ \\ simp []
    \\ rpt conj_tac
    >- (drule_all store_preserve_trans \\ simp [])
    >- gvs [cml_state_preserved_def]
    >- (drule_all SUBMAP_TRANS \\ simp [])
    >- (irule is_extension_trans
        \\ first_assum $ irule_at (Pos last)
        \\ imp_res_tac store_preserve_length
        \\ simp []))
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy tst’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    >- (qrefinel [‘ck’, ‘_’, ‘m’] \\ simp []
        \\ irule store_preserve_all_weaken \\ simp [])
    \\ namedCases_on ‘do_cond tst_v thn els’ ["", "branch"] \\ gvs []
    \\ gvs [oneline do_cond_def, CaseEq "value"]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ rev_drule_at (Pos hd) no_shadow_evaluate_exp
    \\ disch_then drule
    \\ drule_at (Pos hd) no_shadow_evaluate_exp
    \\ disch_then drule \\ rpt strip_tac \\ gvs []
    \\ ‘base_at_most base t₁.refs l’ by
      (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def])
    \\ last_x_assum drule_all
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ qexists ‘ck' + ck’ \\ gvs []
    \\ gvs [do_if_def]
    \\ qexists ‘m₁’ \\ simp []
    \\ ‘is_extension t.refs m m₁’ by
      (irule is_extension_weaken
       \\ first_assum $ irule_at (Pos last)
       \\ imp_res_tac store_preserve_all_length)
    \\ ‘store_preserve (FRANGE m) base t.refs t₂.refs’ by
      (irule store_preserve_trans
      \\ first_assum $ irule_at (Pos last) \\ simp []
       \\ irule store_preserve_all_weaken \\ simp [])
    \\ gvs [cml_state_preserved_def])
  >~ [‘Return’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, mk_id_def, evaluate_def,
         do_con_check_def, env_rel_def, has_cons_def, build_conv_def]
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Dec local scope’] >-
   (namedCases_on ‘local’ ["n ty"] \\ gvs []
    \\ gvs [evaluate_stmt_def] \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ rename [‘evaluate_stmt _ _ _ = (s₂, r)’]
    \\ ‘r_dfy = r’ by gvs [AllCaseEqs()] \\ gvs []
    \\ drule_then assume_tac evaluate_stmt_locals
    \\ gvs [declare_local_def]
    \\ gvs [pop_locals_def, safe_drop_def]
    \\ namedCases_on ‘s₂.locals’ ["", "hd tl"] \\ gvs []
    \\ namedCases_on ‘hd’ ["n nv"] \\ gvs []
    \\ last_x_assum drule
    \\ disch_then $
         qspecl_then
           [‘t with refs := t.refs ++ [Refv (Litv (IntLit 0))]’,
            ‘env_cml with v :=
               nsBind n (Loc T (LENGTH t.refs)) env_cml.v’,
            ‘m’,
            ‘l |+ (n, (LENGTH t.refs))’,
            ‘base’]
           mp_tac
    \\ impl_tac
    >- (gvs [state_rel_def]
        \\ irule_at Any array_rel_append \\ gvs []
        \\ irule_at Any locals_rel_decl_uninit_var \\ gvs []
        \\ irule_at Any locals_above_extend \\ gvs []
        \\ irule env_rel_env_change
        \\ rpt conj_tac
        >- (drule is_fresh_not_int_to_string \\ strip_tac \\ fs []
            \\ fs [env_rel_def]
            \\ first_assum $ irule_at (Pos last) \\ simp [])
        >- (gvs [env_rel_def, has_cons_def])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt strip_tac
        \\ rename [‘isPrefix «dfy_» n'’]
        \\ ‘n' ≠ n’ by (gvs [is_fresh_def] \\ imp_res_tac isPrefix_dfy_v_neq)
        \\ simp [])
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qexists ‘ck’
    \\ gvs [cml_new_refs_def]
    \\ gvs [evaluate_def, do_app_def, store_alloc_def]
    \\ drule_then assume_tac store_preserve_decat
    \\ drule_then assume_tac is_extension_decat
    \\ qexists ‘m₁’ \\ gvs []
    \\ gvs [cml_state_preserved_def]
    (* state_rel *)
    \\ gvs [state_rel_def]
    \\ gvs [locals_rel_def]
    \\ rpt strip_tac
    >- (first_x_assum drule \\ gvs [store_preserve_def])
    \\ rename [‘is_fresh var’]
    \\ ‘n ≠ var’ by
      (‘¬MEM n (MAP FST tl)’ by gvs []
       \\ spose_not_then assume_tac
       \\ fs [GSYM ALOOKUP_NONE])
    \\ first_x_assum $ qspec_then ‘var’ mp_tac \\ gvs []
    \\ rpt strip_tac \\ gvs [FLOOKUP_SIMP])
  >~ [‘Assign ass’] >-
   (gvs [evaluate_stmt_def]
    \\ qabbrev_tac ‘rhss = MAP SND ass’
    \\ qabbrev_tac ‘lhss = MAP FST ass’
    \\ namedCases_on ‘evaluate_rhs_exps s env_dfy rhss’ ["s₁ r"] \\ gvs []
    \\ gvs [from_stmt_def, par_assign_def, oneline bind_def, CaseEq "sum"]
    \\ ‘LENGTH ass = LENGTH cml_rhss’ by
      (unabbrev_all_tac \\ imp_res_tac result_mmap_len \\ gvs [])
    \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule_all correct_map_from_rhs_exp
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m₁’] mp_tac \\ rpt strip_tac
    \\ gvs [evaluate_def]
    \\ Cases_on ‘LENGTH rhss = 1’ \\ gvs []
    >- (* Simple assignment *)
     (drule_then assume_tac result_mmap_len \\ gvs [LENGTH_EQ_1]
      \\ unabbrev_all_tac
      \\ rename [‘result_mmap _ [SND h] = INR [rhs_cml]’]
      \\ namedCases_on ‘h’ ["lhs rhs"] \\ gvs []
      \\ gvs [evaluate_def, Stuple_def, Pstuple_def]
      \\ reverse $ namedCases_on ‘r’ ["rhs_vs", "err"] \\ gvs []
      >- (qexistsl [‘ck’, ‘t₁’, ‘m₁’]
          \\ gvs [store_preserve_all_def, store_preserve_def, base_at_most_def])
      \\ gvs [can_pmatch_all_def, pmatch_def, pat_bindings_def]
      \\ drule_then assume_tac evaluate_rhs_exps_len_eq \\ gvs [LENGTH_EQ_1]
      \\ rename [‘val_rel _ rhs_v rhs_v_cml’]
      \\ ‘¬is_fresh (cml_tup_vname 0)’ by
        gvs [is_fresh_def, cml_tup_vname_def, isprefix_thm]
      \\ drule_all state_rel_env_push_not_fresh \\ gvs []
      \\ disch_then $ qspec_then ‘rhs_v_cml’ assume_tac
      \\ drule evaluate_assign_values \\ gvs []
      \\ disch_then $ drule_at $ Pos (el 2) \\ gvs []
      \\ disch_then $ qspec_then ‘[cml_tup_vname 0]’ mp_tac \\ gvs []
      \\ disch_then $ qspec_then ‘base’ mp_tac \\ gvs []
      \\ ‘cml_tup_vname 0 ≠ « arr»’ by (gvs [cml_tup_vname_neq_arr]) \\ gvs []
      \\ impl_tac >-
       (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]
        \\ irule env_rel_env_change
        \\ rpt conj_tac
        >- (simp [cml_tup_vname_def]
            \\ fs [env_rel_def]
            \\ first_assum $ irule_at (Pos last) \\ simp [strcat_def, concat_def])
        >- (gvs [env_rel_def, has_cons_def])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt strip_tac
        \\ gvs [dfy_pfx_cml_tup_vname_neq])
      \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’] mp_tac \\ rpt strip_tac
      \\ qexists ‘ck₁ + ck’
      \\ rev_dxrule evaluate_add_to_clock \\ gvs []
      \\ disch_then $ qspec_then ‘ck₁’ assume_tac \\ gvs []
      \\ gvs []
      \\ irule_at (Pos hd) store_preserve_trans
      \\ irule_at (Pos hd) store_preserve_all_weaken
      \\ ntac 2 (first_assum $ irule_at (Pos hd))
      \\ irule_at Any state_rel_env_pop_not_fresh
      \\ last_assum $ irule_at (Pos hd)
      \\ gvs []
      \\ last_assum $ irule_at (Pos hd) \\ gvs []
      \\ gvs [cml_state_preserved_def])
    \\ imp_res_tac result_mmap_len
    \\ gvs [Stuple_Tuple, evaluate_def, do_con_check_def, build_conv_def]
    \\ reverse $ namedCases_on ‘r’ ["rhs_vs", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs [store_preserve_all_def, store_preserve_def, base_at_most_def])
    \\ qmatch_asmsub_abbrev_tac ‘MAP (Var ∘ Short) names’
    \\ ‘EVERY (λn. « arr» ≠ n) names’ by
      gvs [Abbr ‘names’, EVERY_GENLIST, cml_tup_vname_neq_arr]
    \\ ‘LENGTH names = LENGTH cml_vs’ by
      (imp_res_tac evaluate_length \\ simp [Abbr ‘names’])
    \\ ‘EVERY (λn. ¬(isPrefix «dfy_» n)) names’ by
      (simp [Abbr ‘names’, EVERY_GENLIST, cml_tup_vname_def, isprefix_thm])
    \\ ‘∀n. is_fresh n ⇒ ¬MEM n names’ by
      (simp [Abbr ‘names’, MAP_ZIP, is_fresh_not_mem_genlist])
    \\ ‘¬MEM cml_int_to_string_name names’ by
      (simp [Abbr ‘names’, int_to_string_not_mem_genlist])
    \\ qabbrev_tac
       ‘env₁ =
          env_cml with v :=
            nsAppend (alist_to_ns (ZIP (names,cml_vs))) env_cml.v’
    \\ ‘env_rel env_dfy env₁’ by
      (simp [Abbr ‘env₁’]
       \\ irule env_rel_env_change
       \\ rpt conj_tac
       >- (simp []
           \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
           \\ simp [MAP_ZIP] \\ fs []
           \\ fs [env_rel_def]
           \\ first_assum $ irule_at (Pos last) \\ simp [])
       >- (gvs [env_rel_def, has_cons_def])
       \\ first_assum $ irule_at (Pos last)
       \\ rpt strip_tac \\ simp []
       \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
       \\ rpt strip_tac
       \\ gvs [MAP_ZIP, EVERY_MEM])
    \\ ‘state_rel m₁ l s₁ t₁ env₁’ by
      (irule state_rel_env_change
       \\ first_assum $ irule_at Any
       \\ simp [Abbr ‘env₁’]
       \\ rpt strip_tac
       \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
       \\ simp [MAP_ZIP])
    \\ ‘base_at_most base t₁.refs l’ by
      (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def])
    \\ ‘LENGTH rhss = LENGTH cml_vs’ by
      (imp_res_tac evaluate_rhs_exps_len_eq
       \\ imp_res_tac LIST_REL_LENGTH \\ gvs [])
    \\ drule evaluate_assign_values
    \\ rpt (disch_then drule)
    \\ gvs []
    \\ disch_then $ qspec_then ‘base’ mp_tac
    \\ impl_tac \\ gvs [] >-
     (gvs [Abbr ‘env₁’]
      \\ irule LIST_REL_nsLookup_nsAppend
      \\ gvs [Abbr ‘names’]
      \\ gvs [all_distinct_genlist_cml_tup_vname])
    \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’] mp_tac \\ rpt strip_tac
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ reverse $ IF_CASES_TAC
    >- (gvs [can_pmatch_all_def, pmatch_def]
        \\ pop_assum mp_tac
        \\ DEP_REWRITE_TAC [Pstuple_Tuple]
        \\ imp_res_tac evaluate_length
        \\ fs [pmatch_def, pmatch_list_MAP_Pvar, Abbr ‘names’])
    \\ pop_assum kall_tac
    \\ reverse $ IF_CASES_TAC >-
     (‘LENGTH (MAP Pvar (REVERSE names)) ≠ 1’ by gvs [Abbr ‘names’]
      \\ drule Pstuple_Tuple \\ rpt strip_tac \\ gvs []
      \\ gvs [pat_bindings_def]
      \\ qsuff_tac ‘ALL_DISTINCT (REVERSE names ++ [])’
      >- (strip_tac \\ drule ALL_DISTINCT_pats_bindings \\ gvs [])
      \\ gvs [Abbr ‘names’, all_distinct_genlist_cml_tup_vname])
    \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
    \\ gvs [pmatch_def]
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC [pmatch_list_MAP_Pvar]
    \\ gvs []
    (* store_preserve + + cml_state_preserved + is_extension *)
    \\ irule_at Any store_preserve_trans \\ gvs []
    \\ irule_at (Pos hd) store_preserve_all_weaken
    \\ first_x_assum $ irule_at (Pos hd) \\ gvs []
    \\ first_x_assum $ irule_at (Pos hd) \\ simp []
    \\ first_x_assum $ irule_at (Pos last) \\ simp []
    \\ gvs [cml_state_preserved_def]
    (* state_rel *)
    \\ irule state_rel_env_change
    \\ first_x_assum $ irule_at Any
    \\ rpt strip_tac
    \\ gvs [Abbr ‘env₁’]
    \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
    \\ simp [MAP_ZIP])
  >~ [‘While grd _ _ _ body’] >-
   (gvs [evaluate_stmt_def]
    \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ ‘t.clock = s.clock’ by gvs [state_rel_def] \\ gvs []
    \\ Cases_on ‘s.clock = 0’ \\ gvs []
    >- (qexists ‘0’ \\ gvs []
        \\ gvs [evaluate_def, build_rec_env_def, cml_fapp_def, cml_apps_def,
                Apps_def, do_con_check_def, build_conv_def, loop_name_def,
                mk_id_def, do_opapp_def]
        \\ gvs [find_recfun_def, state_rel_def]
        \\ rpt (last_assum $ irule_at Any) \\ gvs []
        \\ gvs [cml_state_preserved_def])
    \\ namedCases_on ‘evaluate_exp (dec_clock s) env_dfy grd’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs [])
    (* TODO Better way to do this than writing this big block? *)
    \\ qabbrev_tac
       ‘env_cml₁ =
          env_cml with v :=
            nsBind «» (Conv NONE [])
              (nsBind (loop_name lvl)
                 (Recclosure env_cml
                    [(loop_name lvl,«»,
                      If cml_grd
                        (Let NONE cml_body
                           (App Opapp
                              [Var (Short (loop_name lvl)); Unit]))
                        Unit)] (loop_name lvl)) env_cml.v)’
    \\ ‘env_rel env_dfy env_cml₁’ by
      (irule env_rel_env_change
       \\ rpt conj_tac
       >- (gvs [Abbr‘env_cml₁’, env_rel_def, loop_name_def]
           \\ first_assum $ irule_at (Pos last)
           \\ simp [strcat_def, concat_def])
       >- (gvs [env_rel_def, has_cons_def, Abbr ‘env_cml₁’])
       \\ first_x_assum $ irule_at (Pos last)
       \\ rpt strip_tac
       \\ simp [Abbr ‘env_cml₁’]
       \\ DEP_REWRITE_TAC [neq_nslookup_nsbind]
       \\ rpt strip_tac
       \\ gvs [loop_name_def, isprefix_thm])
    \\ drule (cj 1 correct_from_exp) \\ gvs []
    \\ disch_then $ qspecl_then [‘dec_clock t’, ‘env_cml₁’, ‘m’, ‘l’] mp_tac
    \\ ‘∀n. is_fresh n ⇒ n ≠ «»’ by
      (rpt strip_tac \\ gvs [is_fresh_def, isprefix_thm])
    \\ ‘∀n lvl. is_fresh n ⇒ n ≠ loop_name lvl’ by
      (ntac 2 (strip_tac)
       \\ gvs [is_fresh_def, isprefix_thm, loop_name_def])
    \\ impl_tac >-
     (gvs [state_rel_def, evaluateTheory.dec_clock_def, dec_clock_def]
      \\ irule locals_rel_env_change
      \\ first_assum $ irule_at Any
      \\ rpt strip_tac
      \\ gvs [Abbr ‘env_cml₁’]
      \\ simp [])
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ gvs [evaluate_def, cml_fapp_def, cml_apps_def, mk_id_def, Apps_def,
            do_con_check_def, build_conv_def, build_rec_env_def, do_opapp_def]
    \\ gvs [find_recfun_def, evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["grd_v", "err"] \\ gvs []
    >- (qexists ‘ck’
        \\ gvs [evaluateTheory.dec_clock_def]
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ gvs [Abbr ‘env_cml₁’]
        \\ irule_at (Pos hd) state_rel_pop_env_while
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ gvs [cml_state_preserved_def])
    \\ Cases_on ‘grd_v = BoolV F’ \\ gvs []
    >- (qexists ‘ck’
        \\ gvs [evaluateTheory.dec_clock_def]
        \\ gvs [do_if_def, evaluate_def, do_con_check_def, build_conv_def]
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ gvs [Abbr ‘env_cml₁’]
        \\ irule_at (Pos hd) state_rel_pop_env_while
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ gvs [cml_state_preserved_def])
    \\ Cases_on ‘grd_v = BoolV T’ \\ gvs []
    \\ namedCases_on ‘evaluate_stmt s₁ env_dfy body’ ["s₂ r"] \\ gvs []
    \\ ‘r ≠ Rstop (Serr Rfail)’ by (spose_not_then assume_tac \\ gvs [])
    \\ ‘no_shadow (set (MAP FST s₁.locals)) body’ by
      (irule no_shadow_evaluate_exp
       \\ first_assum $ irule_at (Pos hd)
       \\ gvs [dec_clock_def])
    \\ first_x_assum drule \\ gvs []
    \\ disch_then $ drule \\ gvs []
    \\ disch_then $ qspec_then ‘base’ mp_tac
    \\ impl_tac
    >- gvs [base_at_most_def, store_preserve_all_def, store_preserve_def,
            evaluateTheory.dec_clock_def]
    \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    >- (reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
        (* Definitely not simulating a TRY using rpt here *)
        \\ rpt $ Cases_on ‘err’ \\ gvs []
        \\ qexists ‘ck₁ + ck’ \\ gvs []
        \\ rev_drule evaluate_add_to_clock
        \\ disch_then $ qspec_then ‘ck₁’ assume_tac \\ gvs []
        \\ gvs [evaluateTheory.dec_clock_def, do_if_def, evaluate_def]
        \\ irule_at (Pos hd) store_preserve_trans
        \\ irule_at (Pos hd) store_preserve_all_weaken
        \\ ntac 2 (first_assum $ irule_at (Pos hd))
        \\ gvs [Abbr ‘env_cml₁’]
        \\ irule_at (Pos hd) state_rel_pop_env_while
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ gvs [cml_state_preserved_def]
        (* is_extension *)
        \\ drule is_extension_weaken
        \\ disch_then irule
        \\ imp_res_tac store_preserve_all_length)
    \\ gvs [STOP_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ last_x_assum $ qspecl_then [‘lvl’, ‘t₂’, ‘env_cml’] mp_tac
    \\ gvs []
    \\ disch_then $ qspecl_then [‘m₁’, ‘l’, ‘base’] mp_tac \\ gvs []
    \\ impl_tac
    >- (gvs [dec_clock_def, evaluateTheory.dec_clock_def, state_rel_def,
             base_at_most_def, store_preserve_all_def, store_preserve_def,
             no_assert_stmt_def]
        \\ irule_at (Pos last) no_shadow_evaluate_stmt
        \\ last_assum $ irule_at (Pos $ el 2) \\ gvs []
        \\ irule locals_rel_env_change
        \\ first_assum $ irule_at Any
        \\ rpt strip_tac
        \\ simp [Abbr ‘env_cml₁’])
    \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’, ‘m₂’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qexists ‘ck₂ + ck₁ + ck’ \\ simp []
    \\ rev_dxrule evaluate_add_to_clock \\ simp []
    \\ disch_then $ qspec_then ‘ck₂ + ck₁’ mp_tac \\ simp []
    \\ simp [evaluateTheory.dec_clock_def]
    \\ disch_then $ kall_tac
    \\ simp [do_if_def, Once evaluate_def]
    \\ rev_dxrule evaluate_add_to_clock \\ simp []
    \\ disch_then $ qspec_then ‘ck₂’ mp_tac \\ simp []
    \\ disch_then $ kall_tac
    \\ simp []
    \\ qhdtm_x_assum ‘evaluate’ mp_tac
    \\ simp [Once evaluate_def]
    \\ simp [build_rec_env_def, cml_fapp_def, cml_apps_def, Apps_def, mk_id_def]
    \\ simp [evaluate_def, do_con_check_def, build_conv_def, Abbr ‘env_cml₁’,
             loop_name_def]
    \\ simp [strcat_def, concat_def]
    \\ disch_then kall_tac
    \\ irule_at (Pos hd) store_preserve_trans
    \\ irule_at (Pos hd) store_preserve_all_weaken
    \\ fs [evaluateTheory.dec_clock_def]
    \\ last_assum $ irule_at (Pos hd)
    \\ irule_at (Pos hd) store_preserve_trans
    \\ gvs [cml_state_preserved_def]
    (* Get rid of store_preserve in the goal *)
    \\ ntac 2 (last_assum $ irule_at (Pos hd))
    \\ simp []
    (* state_rel *)
    \\ first_assum $ irule_at (Pos hd)
    \\ irule_at (Pos hd) SUBMAP_TRANS
    \\ last_assum $ irule_at (Pos hd) \\ simp []
    (* is_extension *)
    \\ irule is_extension_trans
    \\ first_assum $ irule_at (Pos last)
    \\ imp_res_tac store_preserve_all_length
    \\ imp_res_tac store_preserve_length
    \\ simp []
    \\ irule is_extension_weaken
    \\ first_assum $ irule_at (Pos last)
    \\ simp [])
  >~ [‘Print e t’] >-
   (gvs [evaluate_stmt_def]
    \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (Cases_on ‘r’ \\ gvs [])
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choose_then ‘ck’ mp_tac \\ strip_tac
    \\ simp [Once evaluate_def]
    \\ Cases_on ‘t’ \\ gvs [to_string_def]
    >- (* BoolT *)
     (qexists ‘ck’
      \\ simp [Once evaluate_def]
      \\ reverse $ Cases_on ‘r’ \\ gvs []
      >-
       (irule_at (Pos hd) store_preserve_all_weaken \\ simp []
        \\ first_assum $ irule_at (Pos hd) \\ simp [])
      \\ rename [‘val_rel _ dfy_v _’]
      \\ Cases_on ‘¬value_has_type BoolT dfy_v’ \\ gvs []
      \\ simp [do_if_def]
      \\ IF_CASES_TAC \\ gvs []
      \\ simp [Once evaluate_def]
      \\ simp [evaluate_def, do_app_def, store_alloc_def, store_lookup_def,
               EL_LENGTH_APPEND_0, call_FFI_def, store_assign_def,
               store_v_same_type_def]
      \\ gvs [cml_state_preserved_def]
      \\ irule_at Any store_preserve_append
      \\ irule_at Any state_rel_refs_append
      \\ irule_at Any store_preserve_all_weaken \\ simp []
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    >- (* IntT *)
     (reverse $ Cases_on ‘r’ \\ gvs []
      \\ simp [cml_fapp_def, cml_apps_def, mk_id_def, Apps_def]
      >- (* Timeout evaluating expression *)
       (qexists ‘ck’
        \\ simp [evaluate_def]
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ simp []
        \\ first_assum $ irule_at (Pos hd) \\ simp [])
      \\ rename [‘val_rel _ dfy_v _’]
      \\ Cases_on ‘∀i. dfy_v ≠ IntV i’ \\ gvs []
      \\ drule cml_int_to_string_correct
      \\ fs [env_rel_def]
      \\ disch_then $ qspec_then ‘clos_env’ mp_tac \\ simp []
      \\ disch_then $ qx_choose_then ‘ck₁’ assume_tac \\ simp []
      \\ qexists ‘ck₁ + ck’ \\ simp []
      \\ simp [evaluate_def, do_app_def, store_alloc_def, store_lookup_def,
               EL_LENGTH_APPEND_0, call_FFI_def, store_assign_def,
               store_v_same_type_def]
      \\ gvs [cml_state_preserved_def]
      \\ irule_at Any store_preserve_append
      \\ irule_at Any state_rel_refs_append
      \\ irule_at Any store_preserve_all_weaken \\ simp []
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    (* StrT *)
    \\ qexists ‘ck’
    \\ simp [Once evaluate_def]
    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >-
     (irule_at (Pos hd) store_preserve_all_weaken \\ simp []
      \\ first_assum $ irule_at (Pos hd) \\ simp [])
    \\ rename [‘val_rel _ dfy_v _’]
    \\ Cases_on ‘∀s. dfy_v ≠ StrV s’ \\ gvs []
    \\ simp [evaluate_def, do_app_def, store_alloc_def, store_lookup_def,
             EL_LENGTH_APPEND_0, call_FFI_def, store_assign_def,
             store_v_same_type_def]
    \\ gvs [cml_state_preserved_def]
    \\ irule_at Any store_preserve_append
    \\ irule_at Any state_rel_refs_append
    \\ irule_at Any store_preserve_all_weaken \\ simp []
    \\ first_assum $ irule_at (Pos hd) \\ simp [])
  >~ [‘MetCall lhss name args’] >-
   (* TODO Can we minimize the proof by avoiding the case distinction on args?
      Perhaps we can write a more general version of evaluate_Apps, that
      applies to cml_Apps (i.e. also considers empty list?) *)
   (gvs [evaluate_stmt_def]
    (* Get member *)
    \\ namedCases_on ‘get_member name env_dfy.prog’ ["", "member"] \\ gvs []
    \\ Cases_on ‘member’ \\ gvs []
    \\ rename [‘Method name ins _ _ _ _ outs _ body’]
    \\ drule get_member_some_met_name \\ rpt strip_tac \\ gvs []
    \\ drule_all env_rel_nsLookup \\ rpt strip_tac \\ gvs []
    \\ qabbrev_tac ‘mname = «dfy_» ^ name’ \\ gvs []
    (* "Simulate" evaluating arguments *)
    \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ rename [‘map_from_exp _ = INR cml_args’]
    \\ imp_res_tac map_from_exp_len \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rfail’ by (spose_not_then assume_tac \\ gvs []) \\ gvs []
    \\ drule_all (cj 2 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qrefine ‘ck₁ + ck’
    \\ reverse $ namedCases_on ‘r’ ["in_vs", "err"] \\ gvs []
    >- (* Evaluating arguments failed *)
     (qexists ‘0’
      \\ Cases_on ‘cml_args’ \\ gvs []
      \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
      \\ drule_all evaluate_Apps_Rerr
      \\ disch_then $ qspec_then ‘Var (Short mname)’ assume_tac
      \\ gvs [cml_tup_case_def, evaluate_def]
      \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
      \\ last_assum $ irule_at (Pos hd) \\ gvs [])
    (* Evaluating arguments succeeded *)
    \\ imp_res_tac evaluate_exps_length \\ gvs []
    \\ namedCases_on
         ‘set_up_call s₁ (MAP FST ins) in_vs (MAP FST outs)’ ["", "r"] \\ gvs []
    \\ gvs [set_up_call_def, safe_zip_def]
    \\ ‘LENGTH ins = LENGTH args’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs [cml_tup_case_def, evaluate_def]
    \\ ‘∀n. isPrefix «dfy_» n ⇒ ¬MEM n (MAP FST outs)’ by
      (rpt strip_tac
       \\ ‘isPrefix «v» n’ by fs [EVERY_MEM, is_fresh_def]
       \\ drule_all isPrefix_dfy_v_neq \\ simp [])
    \\ ‘¬MEM cml_int_to_string_name (MAP FST outs)’ by
      (drule every_is_fresh_not_int_to_string \\ simp [EVERY_MEM, MAP_MAP_o])
    \\‘∀n. isPrefix «dfy_» n ⇒ ¬MEM n (MAP FST ins)’ by
      (rpt strip_tac
       \\ ‘isPrefix «v» n’ by fs [EVERY_MEM, is_fresh_def]
       \\ drule_all isPrefix_dfy_v_neq \\ simp [])
    \\ namedCases_on ‘args’ ["", "arg args'"] \\ gvs [] >-
     (* No arguments passed *)
     (drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
      \\ drule_all find_recfun_some \\ rpt strip_tac \\ gvs []
      \\ gvs [cml_apps_def, evaluate_def, do_con_check_def,
              build_conv_def, do_opapp_def]
      \\ Cases_on ‘s₁.clock = 0’ \\ gvs [] >-
       (* Failing to do the call, since we don't have any ticks left *)
       (qexists ‘0’ \\ gvs []
        \\ ‘ck = 0 ∧ t.clock = 0’ by gvs [state_rel_def] \\ gvs []
        \\ gvs [restore_caller_def, state_rel_def]
        \\ last_assum $ irule_at (Pos hd) \\ gvs [])
      (* Go through with the call *)
      \\ ‘¬(ck = 0 ∧ t.clock = 0)’ by gvs [state_rel_def] \\ gvs []
      \\ gvs [from_member_decl_def, oneline bind_def, CaseEq "sum",
              set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def]
      \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env’
      \\ gvs [evaluate_cml_new_refs]
      \\ gvs [evaluate_def, evaluateTheory.dec_clock_def]
      \\ qabbrev_tac
           ‘call_t = t with
              <| clock := ck + t.clock − 1;
                 refs := t.refs ++
                         REPLICATE (LENGTH outs) (Refv (Litv (IntLit 0)))|>’
      \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env₁’
      \\ qmatch_asmsub_abbrev_tac
           ‘evaluate_stmt (_ (_ with locals := dfy_locals))’
      \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt call_s’
      \\ namedCases_on ‘evaluate_stmt call_s env_dfy body’ ["s₂ r"]
      \\ gvs [Abbr ‘call_s’]
      \\ ‘r ≠ Rstop (Serr Rfail)’ by (spose_not_then assume_tac \\ gvs [])
      \\ gvs []
      \\ last_x_assum drule
      \\ disch_then $ qspecl_then
           [‘call_t’,
            ‘call_env₁’,
            ‘m’,
            ‘mk_locals_map (MAP FST outs) (LENGTH t.refs)’,
            ‘LENGTH t.refs’]
           mp_tac
      \\ impl_tac >-
       (rpt strip_tac
        >- (* state_rel *)
         (gvs [state_rel_def, dec_clock_def, Abbr ‘call_t’,
               Abbr ‘dfy_locals’, Abbr ‘call_env’, Abbr ‘call_env₁’]
          \\ irule_at (Pos hd) array_rel_append \\ gvs []
          \\ irule locals_rel_mk_locals_map_outs \\ gvs [])
        >- (* base_at_most *)
         (gvs [Abbr ‘call_t’, base_at_most_def]
          \\ rpt strip_tac
          \\ drule (cj 1 FRANGE_mk_locals_map) \\ gvs [])
        >- (* env_rel *)
         (gvs [env_rel_def]
          \\ rpt conj_tac
          >- (gvs [has_cons_def, Abbr ‘call_env₁’, Abbr ‘call_env’])
          >- (simp [Abbr ‘call_env₁’]
              \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env] \\ simp []
              \\ simp [Abbr ‘call_env’]
              \\ drule_all nslookup_build_rec_env_int_to_string
              \\ simp []
              \\ strip_tac
              \\ first_assum $ irule_at (Pos last) \\ simp [])
          \\ ntac 3 strip_tac
          \\ first_x_assum drule
          \\ strip_tac
          \\ simp [Abbr ‘call_env₁’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env]
          \\ conj_tac >- (first_assum $ irule_at (Pos hd) \\ simp [isprefix_thm])
          \\ simp [Abbr ‘call_env’]
          \\ drule_all nslookup_build_rec_env_reclos
          \\ disch_then $ qspec_then ‘env.v’ mp_tac
          \\ rpt strip_tac
          \\ first_assum $ irule_at (Pos last) \\ gvs [strcat_def,concat_def])
        >- (gvs [dec_clock_def, Abbr ‘dfy_locals’, REVERSE_ZIP, MAP_ZIP])
        >- fs [no_assert_member_def])
      \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’, ‘m₁’] mp_tac
      \\ rpt strip_tac \\ gvs []
      \\ gvs [Abbr ‘call_t’]
      (* Will be useful for finishing up proofs *)
      \\ drule_then assume_tac store_preserve_decat
      \\ ‘store_preserve (FRANGE m) base t.refs t₂.refs’ by
        (irule store_preserve_weaken_base
         \\ first_assum $ irule_at (Pos last)
         \\ fs [base_at_most_def])
      \\ qrefine ‘ck₂ + ck₁’
      \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
      \\ reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
      >-
       (qexists ‘0’
        \\ Cases_on ‘err’ \\ gvs []
        \\ gvs [cml_state_preserved_def]
        (* Timed out *)
        \\ gvs [state_rel_def, restore_caller_def]
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ drule_then assume_tac is_extension_decat \\ simp []
        \\ irule locals_rel_submap
        \\ first_assum $ irule_at (Pos hd)
        \\ drule_all locals_rel_array_rel_store_preserve_imp
        \\ simp [])
      (* Read outs *)
      \\ namedCases_on
           ‘OPT_MMAP (read_local s₂.locals) (MAP FST outs)’
           ["", "out_vs"]
      \\ gvs []
      \\ Cases_on ‘LENGTH lhss ≠ LENGTH out_vs’ \\ gvs []
      \\ Cases_on ‘LENGTH outs = 0’ \\ gvs []
      (* Rewrite works without having to instantiate the clock, nice. *)
      \\ rev_drule evaluate_add_to_clock \\ gvs []
      \\ disch_then kall_tac
      \\ gvs [can_pmatch_all_def, pmatch_def, mk_id_def, Abbr ‘call_env’,
              has_cons_def, same_type_def, same_ctor_def, ret_stamp_def,
              pat_bindings_def]
      >- (* Nothing to assign *)
       (qexists ‘0’
        (* Return exception was raised *)
        \\ gvs [par_assign_def, oneline bind_def, result_mmap2_def,
                CaseEq "sum"]
        \\ gvs [assign_values_def]
        \\ gvs [Stuple_def, Pstuple_def, Seqs_def, evaluate_def,
                do_con_check_def, build_conv_def, can_pmatch_all_def,
                pmatch_def, pat_bindings_def]
        (* TODO Same as the timeout case - refactor? *)
        \\ gvs [state_rel_def, restore_caller_def]
        \\ gvs [cml_state_preserved_def]
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ irule locals_rel_submap
        \\ first_assum $ irule_at (Pos hd)
        \\ drule_all locals_rel_array_rel_store_preserve_imp
        \\ simp [])
      \\ Cases_on ‘LENGTH outs = 1’ \\ gvs []
      >- (* Assigning a single value (no tuple used) *)
       (gvs [LENGTH_EQ_1, Stuple_def, Pstuple_def]
        \\ gvs [par_assign_def, oneline bind_def, CaseEq "sum"]
        \\ rename [‘read_local _ (FST out)’]
        \\ namedCases_on ‘out’ ["out_n out_v"] \\ gvs []
        \\ drule_all evaluate_cml_read_var \\ rpt strip_tac \\ gvs []
        \\ rename [‘val_rel _ out_v out_v_cml’]
        \\ drule evaluate_add_to_clock \\ gvs []
        \\ disch_then kall_tac
        \\ gvs [pmatch_def, pat_bindings_def, Stuple_def, Pstuple_def,
                evaluate_def, can_pmatch_all_def]
        \\ qpat_assum ‘_ ⊑ _’ $ irule_at Any
        \\ drule evaluate_assign_values \\ gvs []
        \\ disch_then $ qspec_then ‘[cml_tup_vname 0]’ mp_tac \\ gvs []
        \\ disch_then $
             qspecl_then
             [‘[out_v_cml]’, ‘m₁’, ‘l’, ‘t₂’,
              ‘(env_cml with
                  v :=
                    nsBind (cml_tup_vname 0) out_v_cml
                      (nsBind (cml_tup_vname 0) out_v_cml env_cml.v))’,
              ‘base’] mp_tac
        \\ gvs []
        \\ impl_tac >-
         (rpt strip_tac
          >- (* state_rel *)
           (irule state_rel_restore_caller1 \\ gvs [PULL_EXISTS]
            \\ first_assum $ irule_at (Pos hd) \\ gvs []
            \\ qexists ‘t with clock := ck + t.clock’ \\ gvs []
            \\ first_assum $ irule_at (Pos last) \\ gvs []
            \\ irule state_rel_env_change
            \\ first_assum $ irule_at (Pos last)
            \\ rpt strip_tac
            \\ drule is_fresh_cml_tup_vname_neq \\ simp [])
          >- (* env_rel *)
           (irule env_rel_env_change
            \\ rpt conj_tac
            >- (simp [cml_tup_vname_def] \\ fs [env_rel_def]
                \\ last_assum $ irule_at (Pos last)
                \\ simp [strcat_def, concat_def])
            >- (gvs [env_rel_def, has_cons_def, cml_tup_vname_def])
            \\ first_assum $ irule_at (Pos last)
            \\ rpt strip_tac
            \\ drule dfy_pfx_cml_tup_vname_neq \\ simp [])
          >- (gvs [cml_tup_vname_neq_arr])
          >- (* base_at_most *)
           (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]))
        \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’] mp_tac
        \\ rpt strip_tac \\ gvs []
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ gvs [cml_state_preserved_def]
        \\ irule_at (Pos hd) store_preserve_trans
        \\ ntac 2 (first_assum $ irule_at (Pos hd))
        \\ drule_then assume_tac is_extension_decat \\ simp []
        \\ gvs [state_rel_def]
        \\ irule locals_rel_env_change
        \\ first_assum $ irule_at (Pos last)
        \\ rpt strip_tac
        \\ drule is_fresh_cml_tup_vname_neq \\ simp [])
      (* Assigning multiple values (uses a tuple) *)
      \\ DEP_REWRITE_TAC [Stuple_Tuple] \\ gvs []
      \\ gvs [evaluate_def, do_con_check_def]
      \\ drule_all evaluate_map_cml_read_var \\ rpt strip_tac \\ gvs [MAP_MAP_o]
      \\ drule evaluate_add_to_clock \\ gvs []
      \\ disch_then kall_tac
      \\ gvs [build_conv_def]
      \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
      \\ imp_res_tac OPT_MMAP_LENGTH \\ gvs []
      \\ gvs [pmatch_def]
      \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
      \\ gvs [GENLIST_MAP_Pvar]
      \\ DEP_REWRITE_TAC [pmatch_list_MAP_Pvar] \\ gvs []
      \\ gvs [pat_bindings_def]
      \\ DEP_REWRITE_TAC [ALL_DISTINCT_pats_bindings] \\ gvs []
      \\ gvs [all_distinct_genlist_cml_tup_vname]
      \\ gvs [par_assign_def, oneline bind_def, CaseEq "sum"]
      \\ qmatch_goalsub_abbrev_tac ‘evaluate _ ass_env’
      \\ DEP_REWRITE_TAC [Stuple_Tuple, Pstuple_Tuple] \\ gvs []
      \\ gvs [evaluate_def, do_con_check_def]
      \\ simp [Ntimes GENLIST_lambda_MAP 2, MAP_MAP_o]
      \\ qspecl_then
           [‘ass_env’,
            ‘GENLIST (λn. cml_tup_vname n) (LENGTH outs)’,
            ‘REVERSE val_cmls’]
           mp_tac
           evaluate_map_var_short
      \\ impl_tac >-
       (gvs [Abbr ‘ass_env’]
        \\ irule LIST_REL_nsLookup_nsAppend_REVERSE
        \\ gvs [all_distinct_genlist_cml_tup_vname])
      \\ gvs [] \\ disch_then kall_tac
      \\ gvs [build_conv_def, can_pmatch_all_def, pmatch_def]
      \\ DEP_REWRITE_TAC [pmatch_list_MAP_Pvar] \\ gvs []
      \\ gvs [pat_bindings_def]
      \\ DEP_REWRITE_TAC [ALL_DISTINCT_pats_bindings] \\ gvs []
      \\ gvs [all_distinct_genlist_cml_tup_vname]
      \\ qmatch_goalsub_abbrev_tac ‘evaluate _ ass_env₁’
      \\ drule evaluate_assign_values \\ gvs []
      \\ disch_then drule \\ gvs []
      \\ disch_then $ drule_at (Pos $ el 3) \\ gvs []
      \\ disch_then $ qspecl_then [‘l’, ‘t₂’, ‘ass_env₁’, ‘base’] mp_tac \\ gvs []
      \\ impl_tac >-
       (rpt strip_tac
        >- (* state_rel *)
         (irule state_rel_restore_caller1 \\ gvs []
          \\ first_assum $ irule_at (Pos hd) \\ gvs []
          \\ qexists ‘t with clock := ck + t.clock’ \\ gvs []
          \\ first_assum $ irule_at (Pos last) \\ gvs []
          \\ gvs [state_rel_def]
          \\ irule locals_rel_env_change
          \\ first_assum $ irule_at (Pos last)
          \\ simp [Abbr ‘ass_env₁’, Abbr ‘ass_env’]
          \\ rpt strip_tac
          \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
          \\ simp [MAP_ZIP, is_fresh_not_mem_genlist])
        >- (* env_rel *)
         (irule env_rel_env_change
          \\ rpt conj_tac
          >- (simp [Abbr ‘ass_env₁’, Abbr ‘ass_env’]
              \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
              \\ simp [MAP_ZIP]
              \\ qspec_then ‘LENGTH outs’ mp_tac int_to_string_not_mem_genlist
              \\ simp []
              \\ disch_then kall_tac
              \\ fs [env_rel_def]
              \\ last_assum $ irule_at (Pos last) \\ simp [])
          >- (gvs [Abbr ‘ass_env₁’, Abbr ‘ass_env’, env_rel_def,
                   has_cons_def])
          \\ first_assum $ irule_at (Pos last)
          \\ rpt strip_tac
          \\ simp [Abbr ‘ass_env₁’, Abbr ‘ass_env’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
          \\ simp [MAP_ZIP, dfy_pfx_not_mem_genlist])
        >- (* LIST_REL nsLookup *)
         (gvs [Abbr ‘ass_env₁’]
          \\ irule LIST_REL_nsLookup_nsAppend_REVERSE1
          \\ gvs [all_distinct_genlist_cml_tup_vname])
        >- (gvs [EVERY_GENLIST, cml_tup_vname_neq_arr])
        >- (* base_at_most *)
         (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]))
      \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’] mp_tac
      \\ rpt strip_tac \\ gvs []
      \\ qexists ‘ck₂’ \\ gvs []
      \\ qexists ‘m₁’ \\ simp []
      \\ gvs [cml_state_preserved_def]
      \\ drule_then assume_tac is_extension_decat \\ simp []
      \\ irule_at (Pos hd) store_preserve_trans
      \\ ntac 2 (first_assum $ irule_at (Pos hd))
      \\ simp []
      \\ gvs [state_rel_def]
      \\ irule locals_rel_env_change
      \\ first_assum $ irule_at (Pos last)
      \\ simp [Abbr ‘ass_env₁’, Abbr ‘ass_env’]
      \\ rpt strip_tac
      \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
      \\ simp [MAP_ZIP, is_fresh_not_mem_genlist])
    (* Non-empty argument list *)
    \\ ‘cml_args ≠ []’ by (spose_not_then assume_tac \\ gvs []) \\ gvs []
    \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
    (* Preparing ns for evaluate_Apps *)
    \\ qabbrev_tac ‘params = MAP FST ins’
    \\ ‘ALL_DISTINCT params’ by
      (simp [Abbr ‘params’, GSYM MAP_MAP_o, ALL_DISTINCT_MAP_explode]
       \\ gvs [ALL_DISTINCT_APPEND])
    \\ ‘LENGTH (REVERSE params) = LENGTH ins’ by (unabbrev_all_tac \\ gvs [])
    \\ ‘SUC (LENGTH (TL (REVERSE params))) = LENGTH ins’ by
      (Cases_on ‘REVERSE params’ \\ gvs [])
    (* Preparing clos_v for evaluate_Apps *)
    \\ drule callable_rel_inversion \\ rpt strip_tac \\ gvs []
    (* Preparing env1 for evaluate_Apps *)
    \\ drule find_recfun_some \\ rpt strip_tac \\ gvs []
    \\ qabbrev_tac
       ‘call_env =
          env with v :=
            nsBind cml_param (LAST cml_vs) (build_rec_env cml_funs env env.v)’
    (* Preparing e for evaluate_Apps *)
    \\ gvs [from_member_decl_def, set_up_cml_fun_def, oneline bind_def,
            CaseEq "sum"]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ qmatch_asmsub_abbrev_tac ‘cml_fun _ call_body’
    (* Instantiate evaluate_Apps with clock *)
    \\ drule evaluate_Apps_with_clock
    \\ disch_then $ qspec_then ‘TL (REVERSE params)’ mp_tac \\ gvs []
    \\ disch_then $ drule
    \\ disch_then $ qspecl_then [‘call_env’, ‘call_body’] mp_tac
    \\ impl_tac >- (gvs [do_opapp_def, cml_fun_def, AllCaseEqs()]) \\ gvs []
    \\ disch_then kall_tac
    \\ qrefine ‘LENGTH ins - 1 + ck'’
    (* Dafny ran out of ticks *)
    \\ ‘t₁.clock = s₁.clock’ by gvs [state_rel_def]
    \\ Cases_on ‘s₁.clock = 0’ \\ gvs []
    >- (qexists ‘0’ \\ gvs []
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ qexists ‘m’ \\ gvs [restore_caller_def, state_rel_def]
        \\ gvs [cml_state_preserved_def])
    (* Dafny ran the call *)
    \\ ‘cml_param = HD (REVERSE params)’ by
      (Cases_on ‘REVERSE params’ \\ gvs [cml_fun_def])
    (* Start chipping away at the compilation of a method *)
    \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env₁’
    \\ ‘nsLookup call_env₁.c (mk_id [] «Return») = SOME (0, ret_stamp)’
      by gvs [Abbr ‘call_env₁’, Abbr ‘call_env’, mk_id_def, has_cons_def]
    \\ ‘LIST_REL (λn v. nsLookup call_env₁.v (Short n) = SOME v) params cml_vs’ by
      (gvs [Abbr ‘call_env₁’, Abbr ‘call_env’]
       \\ DEP_REWRITE_TAC [nsappend_alist_to_ns_nsbind]
       \\ ‘params ≠ []’ by (spose_not_then assume_tac \\ gvs []) \\ gvs []
       \\ ‘cml_vs ≠ []’ by (spose_not_then assume_tac \\ gvs []) \\ gvs []
       \\ imp_res_tac LIST_REL_LENGTH \\ simp [LENGTH_FRONT]
       \\ gvs [SNOC_LAST_FRONT, REVERSE_TL, SNOC_HD_REVERSE_TL]
       \\ irule LIST_REL_nsLookup_nsAppend
       \\ imp_res_tac evaluate_length \\ gvs []
       \\ gvs [Abbr ‘params’, GSYM MAP_MAP_o, ALL_DISTINCT_APPEND])
    \\ gvs [Abbr ‘call_body’]
    \\ drule_all evaluate_set_up_in_refs \\ gvs []
    \\ disch_then kall_tac
    \\ gvs [evaluate_cml_new_refs]
    \\ gvs [evaluate_def]
    (* Dafny: Call method *)
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt (_ (_ with locals := dfy_locals))’
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt call_s₁’
    \\ namedCases_on ‘evaluate_stmt call_s₁ env_dfy body’ ["s₂ r"]
    \\ gvs [Abbr ‘call_s₁’]
    \\ ‘r ≠ Rstop (Serr Rfail)’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs []
    (* Apply induction hypothesis *)
    \\ qmatch_goalsub_abbrev_tac
         ‘evaluate (_ with <| clock := _; refs := call_refs |>) call_env₂’
    \\ last_x_assum drule
    \\ disch_then $
         qspecl_then
           [‘dec_clock (t₁ with refs := call_refs)’,
            ‘call_env₂’,
            ‘m’,
            ‘mk_locals_map (MAP FST ins ++ MAP FST outs) (LENGTH t₁.refs)’,
            ‘LENGTH t₁.refs’]
           mp_tac
    \\ impl_tac >-
     (gvs [Abbr ‘dfy_locals’, dec_clock_def, evaluateTheory.dec_clock_def,
           state_rel_def, MAP_REVERSE, MAP_ZIP]
      \\ ‘LENGTH (FRONT cml_vs) = LENGTH args'’ by
        (imp_res_tac evaluate_length
         \\ ‘cml_vs ≠ []’ by (spose_not_then assume_tac \\ gvs [])
         \\ imp_res_tac LIST_REL_LENGTH
         \\ gvs [LENGTH_FRONT])
      \\ ‘MEM (HD (REVERSE params)) params’ by
        (Cases_on ‘(REVERSE params) = []’ \\ gvs []
         \\ DEP_REWRITE_TAC [HD_REVERSE, MEM_LAST] \\ simp [])
      \\ rpt strip_tac
      >- (* array_rel *)
       (gvs [Abbr ‘call_refs’] \\ ntac 2 (irule array_rel_append) \\ gvs [])
      >- (* locals_rel *)
       (gvs [Abbr ‘params’, Abbr ‘call_refs’, Abbr ‘call_env₂’]
        \\ irule locals_mk_locals_map_ins_outs \\ gvs [])
      >- (* base_at_most *)
       (gvs [base_at_most_def, Abbr ‘call_refs’] \\ rpt strip_tac
        \\ drule (cj 1 FRANGE_mk_locals_map) \\ gvs [])
      (* env_rel and no_assert_stmt *)
      \\ gvs [env_rel_def, no_assert_member_def]
      \\ rpt conj_tac
      >- (gvs [Abbr ‘call_env₂’, Abbr ‘call_env₁’, Abbr ‘call_env’,
               has_cons_def])
      >- (simp [Abbr ‘call_env₂’, Abbr ‘call_env₁’, Abbr ‘call_env’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env,
                              not_mem_nslookup_nsappend_alist]
          \\ simp [MAP_ZIP]
          \\ DEP_REWRITE_TAC [NOT_MEM_TL] \\ simp []
          \\ DEP_REWRITE_TAC [neq_nslookup_nsbind] \\ simp []
          \\ ‘EVERY (λn. n ≠ cml_int_to_string_name) params’ by
            (rev_drule every_is_fresh_not_int_to_string
             \\ simp [Abbr ‘params’, MAP_MAP_o])
          \\ conj_tac >-
           (pop_assum mp_tac
            \\ rewrite_tac [EVERY_MEM]
            \\ disch_then drule \\ simp [])
          \\ fs [EVERY_MEM]
          \\ drule_all nslookup_build_rec_env_int_to_string \\ simp []
          \\ disch_then kall_tac
          \\ first_assum $ irule_at (Pos last) \\ simp [])
      \\ ntac 3 strip_tac
      \\ first_x_assum drule
      \\ strip_tac
      \\ drule_all nslookup_build_rec_env_reclos
      \\ disch_then $ qspec_then ‘env.v’ mp_tac
      \\ strip_tac
      \\ first_assum $ irule_at (Pos last)
      \\ simp [Abbr ‘call_env₂’, Abbr ‘call_env₁’, Abbr ‘call_env’]
      \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env,
                          not_mem_nslookup_nsappend_alist]
      \\ simp [MAP_ZIP]
      \\ DEP_REWRITE_TAC [NOT_MEM_TL] \\ simp []
      \\ DEP_REWRITE_TAC [neq_nslookup_nsbind] \\ simp []
      \\ strip_tac
      >- (‘is_fresh (HD (REVERSE params))’ by fs [EVERY_MEM]
          \\ drule is_fresh_not_dfy_pfx \\ simp [])
      \\ gvs [isprefix_thm])
    \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qrefine ‘ck₁ + ck₂’ \\ gvs []
    \\ gvs [evaluateTheory.dec_clock_def, ADD1]
    \\ ‘is_extension t₁.refs m m₁’ by
      (simp [Abbr‘call_refs’]
       \\ drule_then assume_tac is_extension_decat
       \\ drule_then assume_tac is_extension_decat
       \\ simp [])
    \\ ‘is_extension t.refs m m₁’ by
      (irule is_extension_weaken
       \\ first_assum $ irule_at (Pos last)
       \\ imp_res_tac store_preserve_all_length)
    \\ ‘store_preserve (FRANGE m) (LENGTH t₁.refs) t₁.refs t₂.refs’ by
      (simp [Abbr ‘call_refs’]
       \\ drule_then assume_tac store_preserve_decat
       \\ drule_then assume_tac store_preserve_decat
       \\ simp [])
    \\ ‘store_preserve (FRANGE m) base t.refs t₂.refs’ by
      (irule store_preserve_trans
       \\ qexists ‘m’ \\ simp []
       \\ irule_at (Pos hd) store_preserve_all_weaken
       \\ last_assum $ irule_at (Pos hd)
       \\ irule store_preserve_weaken_base
       \\ first_assum $ irule_at (Pos last)
       \\ imp_res_tac store_preserve_all_length
       \\ fs [base_at_most_def])
    \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    \\ reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
    >-
     (Cases_on ‘err’ \\ gvs []
      (* Evaluating the body timed out *)
      \\ qexists ‘0’ \\ gvs []
      \\ gvs [Abbr ‘call_refs’]
      \\ qexists ‘m₁’ \\ simp []
      \\ gvs [cml_state_preserved_def]
      \\ irule state_rel_restore_caller1
      \\ last_assum $ irule_at (Pos hd) \\ gvs []
      \\ last_assum $ irule_at (Pos last) \\ gvs []
      \\ last_assum $ irule_at (Pos last) \\ gvs [])
    (* Dafny: read_locals *)
    \\ namedCases_on ‘OPT_MMAP (read_local s₂.locals) (MAP FST outs)’
         ["", "out_vs"]
    \\ gvs []
    \\ ‘LENGTH lhss = LENGTH out_vs’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs []
    \\ gvs [par_assign_def, oneline bind_def, CaseEq "sum"]
    \\ drule evaluate_add_to_clock \\ gvs []
    \\ disch_then kall_tac
    \\ gvs [can_pmatch_all_def, pmatch_def, ret_stamp_def, same_type_def,
            same_ctor_def, pat_bindings_def]
    \\ Cases_on ‘LENGTH outs = 1’ \\ gvs []
    >- (* Method returns value directly, instead of a tuple *)
     (gvs [LENGTH_EQ_1]
      \\ rename [‘read_local _ (FST out)’]
      \\ gvs [Stuple_def, Pstuple_def]
      \\ drule_all evaluate_cml_read_var \\ rpt strip_tac \\ gvs []
      \\ rename [‘val_rel _ out_v out_v_cml’]
      \\ drule evaluate_add_to_clock \\ gvs []
      \\ disch_then kall_tac
      \\ gvs [pmatch_def, pat_bindings_def]
      \\ gvs [evaluate_def, can_pmatch_all_def, pmatch_def, pat_bindings_def]
      \\ drule evaluate_assign_values \\ gvs []
      (* TODO Copy pasted from other case *)
      \\ disch_then $ qspec_then ‘[cml_tup_vname 0]’ mp_tac \\ gvs []
      \\ disch_then $
           qspecl_then
             [‘[out_v_cml]’, ‘m₁’, ‘l’, ‘t₂’,
              ‘(env_cml with
                  v :=
                    nsBind (cml_tup_vname 0) out_v_cml
                      (nsBind (cml_tup_vname 0) out_v_cml env_cml.v))’,
              ‘base’] mp_tac
      \\ gvs []
      \\ impl_tac >-
       (rpt strip_tac
          >- (* state_rel *)
           (irule state_rel_restore_caller1 \\ gvs []
            \\ first_assum $ irule_at (Pos hd) \\ gvs []
            \\ qexists ‘t₁’ \\ simp []
            \\ first_assum $ irule_at (Pos last) \\ gvs []
            \\ irule state_rel_env_change
            \\ first_assum $ irule_at (Pos last)
            \\ rpt strip_tac
            \\ simp [is_fresh_neq_cml_tup_vname])
          >- (* env_rel *)
           (irule env_rel_env_change
            \\ rpt conj_tac
            >- (simp [cml_tup_vname_def]
                \\ fs [env_rel_def]
                \\ last_assum $ irule_at (Pos last)
                \\ simp [strcat_def, concat_def])
            >- (gvs [env_rel_def, has_cons_def, cml_tup_vname_def])
            \\ first_assum $ irule_at (Pos last)
            \\ rpt gen_tac \\ disch_tac
            \\ simp [dfy_pfx_cml_tup_vname_neq])
          >- gvs [cml_tup_vname_neq_arr]
          >- (* base_at_most *)
           (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def,
                 Abbr ‘call_refs’]))
      \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’] mp_tac
      \\ rpt strip_tac \\ gvs []
      \\ first_assum $ irule_at (Pos hd) \\ gvs []
      \\ gvs [cml_state_preserved_def]
      \\ irule_at (Pos hd) store_preserve_trans
      \\ first_assum $ irule_at (Pos hd)
      \\ first_assum $ irule_at (Pos hd) \\ simp []
      \\ qexists ‘m₁’ \\ simp []
      \\ gvs [state_rel_def]
      \\ irule locals_rel_env_change
      \\ first_assum $ irule_at (Pos last)
      \\ rpt gen_tac \\ disch_tac
      \\ simp [is_fresh_neq_cml_tup_vname])
    \\ DEP_REWRITE_TAC [Stuple_Tuple] \\ gvs []
    \\ imp_res_tac OPT_MMAP_LENGTH \\ gvs []
    \\ drule_all evaluate_map_cml_read_var \\ rpt strip_tac \\ gvs [MAP_MAP_o]
    \\ drule evaluate_add_to_clock \\ gvs [evaluate_def]
    \\ disch_then kall_tac
    \\ gvs [do_con_check_def, build_conv_def]
    \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
    \\ gvs [pmatch_def]
    \\ drule (cj 1 evaluate_length) \\ gvs []
    \\ disch_then assume_tac
    \\ simp [GENLIST_lambda_MAP]
    \\ DEP_REWRITE_TAC [pmatch_list_MAP_Pvar] \\ gvs []
    \\ gvs [pat_bindings_def]
    \\ DEP_REWRITE_TAC [ALL_DISTINCT_pats_bindings] \\ gvs []
    \\ gvs [GSYM GENLIST_lambda_MAP, all_distinct_genlist_cml_tup_vname]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate _ ass_env’
    \\ simp [Ntimes GENLIST_lambda_MAP 2, MAP_MAP_o]
    \\ qspecl_then
       [‘ass_env’,
        ‘GENLIST (λn. cml_tup_vname n) (LENGTH outs)’,
        ‘REVERSE val_cmls’]
       mp_tac
       evaluate_map_var_short
    \\ impl_tac >-
     (gvs [Abbr ‘ass_env’]
      \\ irule LIST_REL_nsLookup_nsAppend_REVERSE
      \\ gvs [all_distinct_genlist_cml_tup_vname])
    \\ gvs []
    \\ disch_then kall_tac
    \\ gvs [can_pmatch_all_def, pmatch_def]
    \\ DEP_REWRITE_TAC [pmatch_list_MAP_Pvar] \\ gvs []
    \\ qmatch_goalsub_abbrev_tac ‘evaluate _ ass_env₁’
    \\ drule evaluate_assign_values \\ gvs []
    \\ qpat_x_assum ‘result_mmap2 _ _ _ = _’ mp_tac
    \\ simp [Ntimes GENLIST_lambda_MAP 2, MAP_MAP_o]
    \\ disch_then assume_tac
    \\ disch_then drule \\ gvs []
    \\ disch_then $ drule_at (Pos $ el 3) \\ gvs []
    \\ disch_then $ qspecl_then [‘l’, ‘t₂’, ‘ass_env₁’, ‘base’] mp_tac \\ gvs []
    \\ impl_tac >-
     (rpt strip_tac
      >- (* state_rel *)
       (irule state_rel_restore_caller1 \\ gvs []
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ qexists ‘t₁’ \\ gvs []
        \\ first_assum $ irule_at (Pos last) \\ gvs []
        \\ gvs [state_rel_def]
        \\ irule locals_rel_env_change
        \\ first_assum $ irule_at (Pos last)
        \\ rpt gen_tac \\ disch_tac
        \\ simp [Abbr ‘ass_env₁’]
        \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
        \\ simp [MAP_ZIP, is_fresh_not_mem_genlist])
      >- (* env_rel *)
       (irule env_rel_env_change
        \\ rpt conj_tac
        >- (simp [Abbr ‘ass_env₁’]
            \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
            \\ simp [MAP_ZIP]
            \\ qspec_then ‘LENGTH outs’ mp_tac int_to_string_not_mem_genlist
            \\ simp []
            \\ disch_then kall_tac
            \\ fs [env_rel_def]
            \\ last_assum $ irule_at (Pos last) \\ simp [])
        >- (fs [env_rel_def, has_cons_def, Abbr ‘ass_env₁’])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt gen_tac \\ strip_tac
        \\ simp [Abbr ‘ass_env₁’]
        \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
        \\ simp [MAP_ZIP, dfy_pfx_not_mem_genlist])
      >- (* LIST_REL nsLookup *)
       (gvs [Abbr ‘ass_env₁’]
        \\ pure_rewrite_tac [nsappend_alist_to_ns_concat]
        \\ irule LIST_REL_nsLookup_nsAppend_REVERSE1
        \\ gvs [all_distinct_genlist_cml_tup_vname])
      >- (gvs [EVERY_GENLIST, cml_tup_vname_neq_arr])
      >- (* base_at_most *)
       (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]))
    \\ disch_then $ qx_choosel_then [‘ck₂’, ‘t₃’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qexists ‘ck₂’ \\ gvs []
    \\ gvs [cml_state_preserved_def]
    \\ irule_at (Pos hd) store_preserve_trans
    \\ first_assum $ irule_at (Pos hd)
    \\ first_assum $ irule_at (Pos hd)
    \\ simp []
    \\ qexists ‘m₁’
    \\ gvs [state_rel_def]
    \\ irule locals_rel_env_change
    \\ first_assum $ irule_at (Pos last)
    \\ rpt gen_tac \\ disch_tac
    \\ simp [Abbr ‘ass_env₁’]
    \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
    \\ simp [MAP_ZIP, is_fresh_not_mem_genlist])
QED

Theorem from_member_decl_name[local]:
  from_member_decl member = INR cml_f ⇒
  (λ(x,y,z). x) $ cml_f = «dfy_» ^ member_name member
Proof
  rpt strip_tac
  \\ gvs [from_member_decl_def, oneline bind_def, set_up_cml_fun_def,
          AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem map_from_member_decl_name[local]:
  ∀members cml_fs.
    result_mmap from_member_decl members = INR cml_fs ⇒
    MAP (λ(x,y,z). x) cml_fs =
    MAP (strcat «dfy_» ∘ member_name) members
Proof
  Induct \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ imp_res_tac from_member_decl_name \\ gvs []
QED

Theorem MEM_dfy_MAP[local]:
  ∀xs x. MEM («dfy_» ^ x) (MAP (λx. «dfy_» ^ x) xs) = MEM x xs
Proof
  Induct \\ gvs []
QED

Theorem ALL_DISTINCT_member_name[local]:
  ∀members cml_fs.
    ALL_DISTINCT (MAP member_name members) ∧
    result_mmap from_member_decl members = INR cml_fs ⇒
    ALL_DISTINCT (MAP (λ(x,y,z). x) cml_fs)
Proof
  Induct \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ imp_res_tac from_member_decl_name
  \\ imp_res_tac map_from_member_decl_name
  \\ gvs []
  \\ rename [‘from_member_decl member’]
  \\ qspecl_then
       [‘MAP member_name members’, ‘member_name member’]
       assume_tac MEM_dfy_MAP
  \\ gvs [MAP_MAP_o, o_DEF]
  \\ simp [GSYM o_DEF, GSYM MAP_MAP_o]
QED

(* Proving that a generated CakeML expression e satisfies
   every_exp (one_con_check env_c) e *)

Theorem Apps_one_con_check[local]:
  ∀xs env_c f.
    every_exp (one_con_check env_c) f ∧
    EVERY (every_exp (one_con_check env_c)) xs ⇒
    every_exp (one_con_check env_c) (Apps f xs)
Proof
  Induct \\ gvs [Apps_def]
QED

Theorem Funs_one_con_check[local]:
  ∀xs env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (Funs xs body)
Proof
  Induct \\ gvs [Funs_def]
QED

Theorem from_exp_one_con_check[local]:
  (∀body cml_body envc.
     from_exp body = INR cml_body ∧
     has_cons envc ⇒
     every_exp (one_con_check envc) cml_body) ∧
  (∀bodys cml_bodys envc.
     map_from_exp bodys = INR cml_bodys ∧
     has_cons envc ⇒
     EVERY (every_exp (one_con_check envc)) cml_bodys)
Proof
  Induct \\ rpt gen_tac
  >~ [‘FunCall name args’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ namedCases_on ‘REVERSE cml_args’ ["", "cml_arg cml_args'"]
    \\ gvs [cml_apps_def, do_con_check_def]
    \\ DEP_REWRITE_TAC [Apps_one_con_check] \\ simp []
    \\ last_x_assum $ drule_then assume_tac
    \\ pop_assum mp_tac
    \\ rewrite_tac [Once $ GSYM EVERY_REVERSE]
    \\ disch_tac
    \\ rev_full_simp_tac std_ss [EVERY_DEF])
  >~ [‘Lit l’] >-
   (simp [from_exp_def] \\ disch_tac
    \\ gvs [oneline from_lit_def, do_con_check_def, has_cons_def,
            AllCaseEqs()])
  >~ [‘Var name’] >-
   (simp [from_exp_def] \\ disch_tac \\ gvs [cml_read_var_def])
  >~ [‘If grd thn els’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac \\ res_tac \\ gvs [])
  >~ [‘UnOp uop e’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac
    \\ gvs [oneline from_un_op_def, do_con_check_def, has_cons_def])
  >~ [‘BinOp bop e₀ e₁’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘bop’
    \\ gvs [from_bin_op_def, do_con_check_def, has_cons_def])
  >~ [‘ArrLen arr’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac
    \\ gvs [cml_get_arr_dim_def, cml_tup_select_def, cml_tup_case_def])
  >~ [‘ArrSel arr idx’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac
    \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def])
  >~ [‘map_from_exp []’] >-
   (simp [from_exp_def])
  >~ [‘map_from_exp (e::es)’] >-
   (simp [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ rpt strip_tac \\ gvs [])
  (* Uncompiled expressions *)
  \\ simp [from_exp_def]
QED

Theorem cml_new_refs_one_con_check[local]:
  ∀names env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (cml_new_refs names body)
Proof
  Induct \\ gvs [cml_new_refs_def]
QED

Theorem from_rhs_exp_one_con_check[local]:
  ∀rhs cml_rhs envc.
    from_rhs_exp rhs = INR cml_rhs ∧
    has_cons envc ⇒
    every_exp (one_con_check envc) cml_rhs
Proof
  Induct \\ rpt gen_tac
  >~ [‘ExpRhs e’] >-
   (simp [from_rhs_exp_def] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check) \\ gvs [])
  >~ [‘ArrAlloc len init’] >-
   (simp [from_rhs_exp_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check)
    \\ gvs [cml_alloc_arr_def, do_con_check_def])
QED

Theorem map_from_rhs_exp_one_con_check[local]:
  ∀rhss cml_rhss envc.
    result_mmap from_rhs_exp rhss = INR cml_rhss ∧
    has_cons envc ⇒
    EVERY (λe. every_exp (one_con_check envc) e) cml_rhss
Proof
  Induct
  \\ simp [result_mmap_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac from_rhs_exp_one_con_check \\ gvs []
QED

Theorem Seqs_one_con_check[local]:
  ∀es env.
    EVERY (λe. every_exp (one_con_check envc) e) es ⇒
    every_exp (one_con_check envc) (Seqs es)
Proof
  Induct \\ gvs [Seqs_def, do_con_check_def]
QED

Theorem assign_single_one_con_check[local]:
  assign_single lhs (Var (Short n)) = INR ass ∧
  has_cons envc ⇒
  every_exp (one_con_check envc) ass
Proof
  Cases_on ‘lhs’
  \\ simp [assign_single_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac (cj 1 from_exp_one_con_check)
  \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
QED

Theorem map_assign_single_one_con_check[local]:
  ∀lhss ns ass envc.
    result_mmap2 assign_single lhss (MAP (Var ∘ Short) ns) = INR ass ∧
    has_cons envc ⇒
    EVERY (λe. every_exp (one_con_check envc) e) ass
Proof
  Induct \\ Cases_on ‘ns’
  \\ simp [result_mmap2_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac assign_single_one_con_check
  \\ res_tac \\ gvs []
QED

Theorem Stuple_one_con_check[local]:
  EVERY (λe. every_exp (one_con_check env_c) e) es ⇒
  every_exp (one_con_check env_c) (Stuple es)
Proof
  Cases_on ‘LENGTH es = 1’
  >- (gvs [LENGTH_EQ_1, Stuple_def])
  \\ DEP_REWRITE_TAC [Stuple_Tuple]
  \\ simp [do_con_check_def]
QED

Theorem par_assign_one_con_check[local]:
  par_assign lhss cml_rhss = INR cml_body ∧
  EVERY (λe. every_exp (one_con_check envc) e) cml_rhss ∧
  has_cons envc ⇒
  every_exp (one_con_check envc) cml_body
Proof
  simp [par_assign_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ Cases_on ‘LENGTH lhss = LENGTH cml_rhss’ \\ gvs []
  \\ DEP_REWRITE_TAC [Seqs_one_con_check, Stuple_one_con_check]
  \\ imp_res_tac map_assign_single_one_con_check \\ gvs []
QED

Theorem to_string_one_con_check[local]:
  to_string cml_e t = INR cml_str ∧
  every_exp (one_con_check env_c) cml_e ⇒
  every_exp (one_con_check env_c) cml_str
Proof
  Cases_on ‘t’ \\ simp [to_string_def] \\ rpt strip_tac
  \\ gvs [cml_fapp_def, cml_apps_def, Apps_def]
QED

Theorem from_stmt_one_con_check[local]:
  ∀body lvl cml_body envc.
    from_stmt body lvl = INR cml_body ∧
    has_cons envc ⇒
    every_exp (one_con_check envc) cml_body
Proof
  Induct \\ rpt gen_tac
  >~ [‘Skip’] >-
   (simp [from_stmt_def, do_con_check_def])
  >~ [‘Assert e’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check) \\ simp [do_con_check_def])
  >~ [‘Then stmt₁ stmt₂’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ res_tac \\ gvs [])
  >~ [‘If tst thn els’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check) \\ res_tac \\ gvs [])
  >~ [‘Return’] >-
   (simp [from_stmt_def, mk_id_def, do_con_check_def, has_cons_def])
  >~ [‘Dec local scope’] >-
   (Cases_on ‘local’
    \\ simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ res_tac \\ drule_then assume_tac cml_new_refs_one_con_check \\ gvs [])
  >~ [‘Assign ass’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac map_from_rhs_exp_one_con_check
    \\ imp_res_tac par_assign_one_con_check)
  >~ [‘While grd _ _ _ body’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check) \\ res_tac
    \\ gvs [cml_fapp_def, cml_apps_def, mk_id_def, Apps_def, do_con_check_def])
  >~ [‘Print e t’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
    \\ imp_res_tac (cj 1 from_exp_one_con_check)
    \\ imp_res_tac to_string_one_con_check
    \\ gvs [cml_fapp_def, cml_apps_def, mk_id_def, Apps_def])
  >~ [‘MetCall lhss name args’] >-
   (simp [from_stmt_def, oneline bind_def, CaseEq "sum", cml_tup_case_def,
          cml_fapp_def]
    \\ rpt strip_tac
    \\ drule par_assign_one_con_check
    \\ disch_then $ drule_at (Pos last)
    \\ impl_tac >- (simp [EVERY_GENLIST])
    \\ rename [‘map_from_exp _ = INR cml_args’] \\ gvs []
    \\ Cases_on ‘REVERSE cml_args = []’
    >- (gvs [cml_apps_def, do_con_check_def])
    \\ DEP_REWRITE_TAC [cml_apps_apps, Apps_one_con_check] \\ simp []
    \\ imp_res_tac (cj 2 from_exp_one_con_check))
QED

Theorem set_up_in_refs_one_con_check[local]:
  ∀names env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (set_up_in_refs names body)
Proof
  Induct \\ gvs [set_up_in_refs_def]
QED

Theorem set_up_cml_fun_one_con_check[local]:
  every_exp (one_con_check env_c) body ⇒
  (λ(f,n,e). every_exp (one_con_check env_c) e)
    (set_up_cml_fun n ins body)
Proof
  disch_tac
  \\ simp [set_up_cml_fun_def, cml_fun_def]
  \\ drule_then assume_tac set_up_in_refs_one_con_check
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ DEP_REWRITE_TAC [Funs_one_con_check] \\ simp []
QED

Theorem MAP_cml_read_var_one_con_check[local]:
  ∀ns env_c e.
    EVERY (λe. every_exp (one_con_check env_c) e) (MAP cml_read_var ns)
Proof
  Induct \\ gvs [one_con_check_def, cml_read_var_def]
QED

Theorem from_member_decl_one_con_check[local]:
  from_member_decl member = INR cml_f ∧
  has_cons envc ⇒
  (λ(f,n,e). every_exp (one_con_check envc) e) cml_f
Proof
  rpt strip_tac
  \\ gvs [from_member_decl_def, oneline bind_def, AllCaseEqs()]
  >- (* Method *)
   (DEP_REWRITE_TAC [set_up_cml_fun_one_con_check, cml_new_refs_one_con_check]
    \\ simp []
    \\ DEP_REWRITE_TAC [Stuple_one_con_check] \\ simp []
    \\ gvs [MAP_cml_read_var_one_con_check]
    \\ imp_res_tac from_stmt_one_con_check \\ simp [])
  (* Function *)
  \\ DEP_REWRITE_TAC [set_up_cml_fun_one_con_check, cj 1 from_exp_one_con_check]
  \\ last_assum $ irule_at (Pos hd) \\ simp []
QED

Theorem map_from_member_decl_one_con_check[local]:
  ∀members cml_fs envc.
    result_mmap from_member_decl members = INR cml_fs ∧
    has_cons envc ⇒
    EVERY (λ(f,n,e). every_exp (one_con_check envc) e) cml_fs
Proof
  Induct
  \\ simp [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ rpt strip_tac
  \\ imp_res_tac from_member_decl_one_con_check
  \\ res_tac \\ gvs []
QED

Definition valid_prog_def:
  valid_prog (Program members) ⇔
    has_main (Program members) ∧
    EVERY is_fresh_member members ∧
    EVERY no_shadow_method members ∧
    EVERY no_assert_member members
End

Theorem find_recfun_main[local]:
  ∀members reqs ens rds decrs mod body cml_funs.
    get_member_aux «Main» members =
      SOME (Method «Main» [] reqs ens rds decrs [] mod body) ∧
    result_mmap from_member_decl members = INR cml_funs ∧
    EVERY is_fresh_member members ∧
    EVERY no_shadow_method members ∧
    EVERY no_assert_member members ⇒
    ∃cml_param cml_body.
      from_stmt body 0 = INR cml_body ∧
      is_fresh_stmt body ∧
      no_shadow ∅ body ∧
      no_assert_stmt body ∧
      ¬(isPrefix «dfy» cml_param) ∧
      cml_param ≠ cml_int_to_string_name ∧
      find_recfun «dfy_Main» cml_funs =
        SOME (cml_param,
              Handle cml_body [(Pcon (SOME (Short «Return»)) [], Unit)])
Proof
  Induct
  \\ simp [get_member_aux_def]
  \\ rpt gen_tac
  \\ reverse CASE_TAC
  \\ rename [‘m = «Main»’]
  >- (* Function *)
   (IF_CASES_TAC \\ simp []
    \\ ‘m ≠ «Main»’ by (spose_not_then assume_tac \\ fs [])
    \\ disch_tac
    \\ gvs [result_mmap_def, oneline bind_def, from_member_decl_def,
            CaseEq "sum"]
    \\ simp [Once find_recfun_def, set_up_cml_fun_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ simp [strcat_def, concat_def, CaseEq "mlstring"])
  (* Method *)
  \\ IF_CASES_TAC
  \\ disch_tac
  \\ gvs [result_mmap_def, from_member_decl_def, oneline bind_def,
          CaseEq "sum"]
  >- (* found main at head *)
   (fs [set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def, cml_new_refs_def,
        mk_id_def, Stuple_def, Once find_recfun_def, no_assert_member_def,
        strcat_def, concat_def, isprefix_thm])
  (* main is in tail *)
  \\ ‘m ≠ «Main»’ by (spose_not_then assume_tac \\ fs [])
  \\ simp [set_up_cml_fun_def, Once find_recfun_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ simp [strcat_def, concat_def, CaseEq "mlstring"]
QED

Theorem valid_main_nslookup[local]:
  get_member «Main» (Program members) =
    SOME (Method «Main» [] reqs ens rds decrs [] mod body) ∧
  result_mmap from_member_decl members = INR cml_funs ∧
  EVERY is_fresh_member members ∧
  EVERY no_shadow_method members ∧
  EVERY no_assert_member members ⇒
  ∃cml_param cml_body.
    from_stmt body 0 = INR cml_body ∧
    is_fresh_stmt body ∧
    no_shadow ∅ body ∧
    no_assert_stmt body ∧
    ¬(isPrefix «dfy» cml_param) ∧
    cml_param ≠ cml_int_to_string_name ∧
    find_recfun «dfy_Main» cml_funs =
      SOME (cml_param,
            Handle cml_body [(Pcon (SOME (Short «Return»)) [], Unit)]) ∧
    nsLookup (nsAppend (build_rec_env cml_funs cl_env env) env₁v)
      (Short «dfy_Main») =
    SOME (Recclosure cl_env cml_funs «dfy_Main»)
Proof
  rpt strip_tac
  \\ fs [get_member_def]
  \\ drule_all find_recfun_main
  \\ rpt strip_tac \\ gvs []
  \\ simp [nsLookup_nsAppend_some]
  \\ disj1_tac
  \\ simp [build_rec_env_def]
  \\ drule_all nslookup_build_rec_env_reclos_aux
  \\ simp [strcat_def, concat_def]
QED

Theorem get_member_MEM_aux[local]:
  ∀members. get_member_aux name members = SOME member ⇒ MEM member members
Proof
  Induct
  \\ simp [get_member_aux_def]
  \\ gen_tac
  \\ CASE_TAC
  \\ IF_CASES_TAC \\ simp []
QED

Theorem get_member_MEM[local]:
  get_member name (Program members) = SOME member ⇒ MEM member members
Proof
  simp [get_member_def] \\ disch_tac \\ imp_res_tac get_member_MEM_aux
QED

Definition has_basic_cons_def:
  has_basic_cons env ⇔
    nsLookup env.c (Short «True») = SOME (0, TypeStamp «True» 0) ∧
    nsLookup env.c (Short «False») = SOME (0, TypeStamp «False» 0) ∧
    nsLookup env.c (Short «[]») = SOME (0, TypeStamp «[]» list_type_num) ∧
    nsLookup env.c (Short «::») = SOME (2, TypeStamp «::» list_type_num)
End

Theorem correct_from_program:
  ∀dfy_ck prog s' r_dfy cml_decs env_cml (t: 'ffi cml_state).
    evaluate_program dfy_ck prog = (s', r_dfy) ∧
    from_program prog = INR cml_decs ∧
    valid_prog prog ∧ has_basic_cons env_cml ∧
    t.clock = dfy_ck ∧ ExnStamp t.next_exn_stamp = ret_stamp ∧
    r_dfy ≠ Rstop (Serr Rfail) ⇒
    ∃ck t' m' r_cml.
      evaluate_decs (t with clock := t.clock + ck) env_cml cml_decs =
        (t', r_cml) ∧
      state_rel m' FEMPTY s' t' env_cml ∧ stmt_res_rel r_dfy r_cml
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [evaluate_program_def]
  \\ Cases_on ‘¬ALL_DISTINCT (MAP member_name members)’ \\ gvs []
  \\ gvs [evaluate_stmt_def, mk_env_def]
  \\ namedCases_on ‘get_member «Main» (Program members)’ ["", "member"] \\ gvs []
  \\ namedCases_on ‘member’
       ["n ins reqs ens rds decrs outs mod body", "_ _ _ _ _ _ _"] \\ gvs []
  \\ imp_res_tac get_member_some_met_name \\ gvs []
  \\ gvs [evaluate_exp_def, valid_prog_def, has_main_def,
          set_up_call_def, safe_zip_def, init_state_def]
  \\ qmatch_asmsub_abbrev_tac ‘evaluate_stmt s env’
  \\ namedCases_on ‘evaluate_stmt s env body’ ["s r"] \\ gvs []
  \\ gvs [from_program_def, oneline bind_def, CaseEq "sum"]
  (* return exception*)
  \\ fs [has_basic_cons_def]
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  (* dec_to_string *)
  \\ simp [cml_dec_to_string_dlet_def, cml_dec_to_string_body_def]
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  \\ simp [cml_list_def, do_con_check_def, pat_bindings_def]
  \\ simp [evaluate_def, pmatch_def]
  \\ qmatch_goalsub_abbrev_tac ‘nsBind «dec_to_string» dts_clos’
  (* nat_to_string *)
  \\ simp [cml_nat_to_string_dletrec_def, cml_nat_to_string_body_def]
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  \\ simp [cml_list_def, do_con_check_def, build_rec_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘nsBind «nat_to_string» nts_clos’
  (* int_to_string *)
  \\ simp [cml_int_to_string_dlet_def, cml_int_to_string_body_def]
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  \\ simp [cml_list_def, do_con_check_def, pat_bindings_def]
  \\ simp [evaluate_def, pmatch_def]
  \\ qmatch_goalsub_abbrev_tac
       ‘nsBind «int_to_string» (Closure its_clos_env _ _)’
  \\ qmatch_goalsub_abbrev_tac
       ‘nsBind «int_to_string» its_clos’
  (* compiled function *)
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  \\ drule_all_then assume_tac ALL_DISTINCT_member_name \\ simp []
  \\ DEP_REWRITE_TAC [map_from_member_decl_one_con_check] \\ simp []
  \\ last_assum $ irule_at (Pos hd)
  \\ simp [has_cons_def]
  (* call to main *)
  \\ simp [Ntimes evaluate_decs_def 2, extend_dec_env_def]
  \\ simp [pat_bindings_def, cml_fapp_def, cml_apps_def, Apps_def, evaluate_def,
           do_con_check_def, build_conv_def, mk_id_def, extend_dec_env_def]
  \\ qmatch_goalsub_abbrev_tac ‘nsAppend (build_rec_env _ cl_env _) env_cml₁v’
  \\ drule_all valid_main_nslookup
  \\ disch_then $ qspecl_then [‘env_cml₁v’, ‘nsEmpty’, ‘cl_env’] mp_tac
  \\ rpt strip_tac
  \\ simp [do_opapp_def, evaluate_def]
  \\ Cases_on ‘t.clock = 0’ \\ gvs []
  >-
   (qrefinel [‘_’, ‘FEMPTY’,‘0’]
    \\ simp [combine_dec_result_def, restore_caller_def, state_rel_def,
             array_rel_def, locals_rel_def]
    \\ simp [oEL_def])
  \\ drule correct_from_stmt
  \\ disch_then drule
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env_cml₂’
  \\ disch_then $
       qspecl_then
         [‘dec_clock (t with next_exn_stamp := t.next_exn_stamp + 1)’,
          ‘env_cml₂’, ‘FEMPTY’, ‘FEMPTY’, ‘LENGTH t.refs’]
         mp_tac
  \\ impl_tac >-
   (rpt conj_tac
    \\ gvs [dec_clock_def, evaluateTheory.dec_clock_def]
    >- (* state_rel *)
     (gvs [Abbr ‘s’, state_rel_def, array_rel_def, LLOOKUP_def, locals_rel_def])
    >- (* base_at_most *)
     (gvs [base_at_most_def])
    >- (* env_rel *)
     (gvs [env_rel_def, has_cons_def, Abbr ‘env_cml₂’, Abbr ‘env_cml₁v’,
           Abbr ‘cl_env’, Abbr ‘env’]
      \\ conj_tac
      >-
       (qmatch_goalsub_abbrev_tac ‘build_rec_env _ env_cml₁ env_cml₂’
        \\ simp [build_rec_env_def]
        \\ drule nslookup_build_rec_env_int_to_string_aux
        \\ disch_then $
             qspecl_then [‘env_cml₁’, ‘cml_funs’, ‘env_cml₂’, ‘its_clos_env’] mp_tac
        \\ impl_tac >-
         (simp [Abbr ‘env_cml₂’, Abbr ‘its_clos’]
          \\ simp [cml_int_to_string_clos_def, cml_int_to_string_body_def,
                   cml_list_def]
          \\ simp [int_to_string_env_def, Abbr ‘its_clos_env’]
          \\ simp [has_list_cons_def]
          \\ simp [Abbr ‘nts_clos’, cml_nat_to_string_clos_def,
                   cml_nat_to_string_body_def, cml_list_def]
          \\ simp [Abbr ‘dts_clos’, cml_dec_to_string_clos_def,
                   cml_dec_to_string_body_def, cml_list_def])
        \\ simp []
        \\ rpt strip_tac
        \\ first_assum $ irule_at (Pos last) \\ simp [])
      \\ rpt gen_tac \\ disch_tac
      \\ drule get_member_MEM
      \\ gvs [EVERY_MEM]
      \\ disch_then kall_tac
      \\ ‘∀n. cml_param ≠ «dfy_» ^ n’ by (rpt strip_tac \\ fs [isprefix_thm])
      \\ gvs []
      \\ qmatch_goalsub_abbrev_tac ‘build_rec_env _ env_cml₁ env_cml₂’
      \\ drule nslookup_build_rec_env_reclos
      \\ simp [dest_program_def, has_cons_def]
      \\ disch_then $
           qspecl_then [‘env_cml₂’, ‘env_cml₁’, ‘its_clos_env’] mp_tac
      \\ impl_tac >-
       (simp [Abbr ‘env_cml₁’, Abbr ‘env_cml₂’, Abbr ‘its_clos’]
        \\ simp [cml_int_to_string_clos_def, cml_int_to_string_body_def,
                 cml_list_def]
        \\ unabbrev_all_tac
        \\ simp [int_to_string_env_def, has_list_cons_def,
                 cml_nat_to_string_clos_def,
                 cml_dec_to_string_clos_def,
                 cml_nat_to_string_body_def,
                 cml_dec_to_string_body_def,
                 cml_list_def])
      \\ simp [])
    >- (simp [Abbr ‘s’])
    \\ gvs [AllCaseEqs()])
  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m’, ‘r_cml’] mp_tac
  \\ rpt strip_tac
  \\ gvs [evaluateTheory.dec_clock_def]
  \\ qrefinel [‘_’, ‘_’, ‘m’, ‘ck’] \\ simp []
  \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
  \\ reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
  >- (Cases_on ‘err’
      \\ gvs [combine_dec_result_def, restore_caller_def, state_rel_def,
              locals_rel_def])
  \\ simp [Abbr ‘cl_env’]
  \\ gvs [assign_values_def, can_pmatch_all_def, pmatch_def, same_type_def,
          ret_stamp_def, same_ctor_def, combine_dec_result_def, state_rel_def,
          restore_caller_def, locals_rel_def, pat_bindings_def,
          do_con_check_def, build_conv_def]
QED
