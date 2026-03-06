(*
  Proving that the basis program only produces v_ok values.
 *)
Theory candle_basis_evaluate
Ancestors
  candle_prover_inv ast_extras evaluate namespaceProps
  perms[qualified] semanticPrimitivesProps misc[qualified]
  semanticPrimitives evaluateProps sptree candle_kernelProg
  candle_prover_evaluate
Libs
  preamble helperLib ml_progLib[qualified]


val _ = temp_send_to_back_overload "If"  {Name="If", Thy="compute_syntax"};
val _ = temp_send_to_back_overload "App" {Name="App",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "Var" {Name="Var",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "Let" {Name="Let",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "If"  {Name="If", Thy="compute_exec"};
val _ = temp_send_to_back_overload "App" {Name="App",Thy="compute_exec"};
val _ = temp_send_to_back_overload "Var" {Name="Var",Thy="compute_exec"};
val _ = temp_send_to_back_overload "Let" {Name="Let",Thy="compute_exec"};

Definition simple_exp_def:
  simple_exp = every_exp $ λx.
    case x of
      App op xs => (case op of
        VfromList => T
      | Aw8alloc => T
      | Test _ _ => T
      | Arith _ _ => T
      | FromTo _ _ => T
      | _ => F)
    | Lit lit => T
    | Var v => T
    | Con opt xs => T
    | _ => F
End

Theorem simple_exp_simps[simp] =
   [“simple_exp (Raise e)”,
    “simple_exp (Handle e pes)”,
    “simple_exp (Lit lit)”,
    “simple_exp (Con opt xs)”,
    “simple_exp (Var n)”,
    “simple_exp (Fun n x)”,
    “simple_exp (App op xs)”,
    “simple_exp (Log lop x y)”,
    “simple_exp (If x y z)”,
    “simple_exp (Mat e pes)”,
    “simple_exp (Let opt x y)”,
    “simple_exp (Letrec f x)”,
    “simple_exp (Tannot e t)”,
    “simple_exp (Lannot e l)”]
  |> map (SIMP_CONV (srw_ss()) [simple_exp_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM simple_exp_def, SF ETA_ss])
  |> LIST_CONJ;

Definition simple_pat_def[simp]:
  simple_pat (Pvar p) = T ∧
  simple_pat Pany = T ∧
  simple_pat _ = F
End

Definition simple_dec_def:
  simple_dec = every_dec $ λd.
      case d of
        Dlet l p (Fun n x) => simple_pat p
      | Dlet l p x => simple_exp x ∧ simple_pat p
      | Dletrec l f => T
      | _ => T
End

Theorem simple_dec_Dlet[simp]:
  simple_dec (Dlet l p x) ⇔
    ((∃n e. x = Fun n e) ∨ simple_exp x) ∧ simple_pat p
Proof
  rw [simple_dec_def]
  \\ CASE_TAC \\ gs []
QED

Theorem simple_dec_simps[simp] =
  [“simple_dec (Dletrec l f)”,
   “simple_dec (Dtype l tds)”,
   “simple_dec (Dtabbrev l ns n t)”,
   “simple_dec (Dexn l n ts)”,
   “simple_dec (Dmod mn ds)”,
   “simple_dec (Dlocal ds1 ds2)”,
   “simple_dec (Denv n)”]
  |> map (ONCE_REWRITE_CONV [simple_dec_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM simple_dec_def, SF ETA_ss])
  |> LIST_CONJ;

Definition post_state_ok_def:
  post_state_ok s ⇔
    (∀n. n ∈ kernel_types ⇒ s.next_type_stamp ≤ n) ∧
    (∀loc. loc ∈ kernel_locs ⇒ LENGTH s.refs ≤ loc)
End

Theorem evaluate_post_state_mono:
  evaluate s env xs = (s', res) ∧
  post_state_ok s' ⇒
    post_state_ok s
Proof
  simp [post_state_ok_def]
  \\ strip_tac
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ drule_then strip_assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ rw [] \\ first_x_assum (drule_all_then assume_tac) \\ gs []
QED

Theorem evaluate_decs_post_state_mono:
  ∀s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    post_state_ok s' ⇒
      post_state_ok s
Proof
  ho_match_mp_tac evaluate_decs_ind
  \\ rw [evaluate_decs_def] \\ gs []
  \\ gvs [CaseEqs ["semanticPrimitives$result", "dec", "prod", "option"]]
  >- (
    drule_all_then assume_tac evaluate_post_state_mono \\ gs [])
  >- (
    drule_all_then assume_tac evaluate_post_state_mono \\ gs [])
  \\ gs [post_state_ok_def] \\ rw []
  \\ first_x_assum (drule_all_then assume_tac) \\ gs []
QED

local
  val ind_thm =
    full_evaluate_ind
    |> Q.SPECL [
      ‘λs env xs. ∀res s' ctxt.
        evaluate s env xs = (s', res) ∧
        post_state_ok s' ∧
        (∀id len tag tn.
           nsLookup env.c id = SOME (len, TypeStamp tag tn) ⇒
             tn ∉ kernel_types) ∧
        env_ok ctxt env ∧
        EVERY simple_exp xs ⇒
          case res of
            Rval vs => EVERY (v_ok ctxt) vs
          | Rerr (Rraise v) => v_ok ctxt v
          | _ => T’,
      ‘λs env v ps errv. T’,
      ‘λs env ds. ∀res s' ctxt.
        evaluate_decs s env ds = (s', res) ∧
        post_state_ok s' ∧
        (∀id len tag tn.
           nsLookup env.c id = SOME (len, TypeStamp tag tn) ⇒
             tn ∉ kernel_types) ∧
        env_ok ctxt env ∧
        EVERY simple_dec ds ∧
        EVERY safe_dec ds ⇒
            case res of
              Rval env1 =>
                env_ok ctxt (extend_dec_env env1 env) ∧
                (∀id len tag tn.
                   nsLookup (extend_dec_env env1 env).c id =
                   SOME (len, TypeStamp tag tn) ⇒
                     tn ∉ kernel_types)
            | Rerr (Rraise v) => v_ok ctxt v
            | _ => T’]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun evaluate_basis_v_ok () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem evaluate_basis_v_ok_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_basis_v_ok_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "semanticPrimitives$result"], SF SFY_ss]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac evaluate_post_state_mono \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ simp [v_ok_Lit]
QED

Theorem evaluate_basis_v_ok_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"], EVERY_MAP,
          SF SFY_ss]
  \\ drule_all_then assume_tac evaluate_post_state_mono
  \\ gvs [build_conv_def, CaseEqs ["option", "prod"]]
  \\ irule v_ok_Conv \\ gs [] \\ rw []
  \\ strip_tac \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_Var:
  ^(get_goal "ast$Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_App:
  ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ Cases_on ‘getOpClass op’
  \\ gvs [CaseEqs ["bool", "option", "prod", "semanticPrimitives$result"], SF SFY_ss]
  >- (Cases_on ‘op’ \\ gs[])
  >- (Cases_on ‘op’ \\ gs[])
  >- (Cases_on ‘op’ \\ gs[])
  >- (Cases_on ‘op’ \\ gs[])
  >- (Cases_on ‘op’ \\ gvs [])
  >- (
    gvs [do_app_cases, Boolv_def]
    \\ rw [v_ok_def]
    >~ [`do_arith a ty`]
    >- (
      gvs[oneline do_arith_def, v_ok_def, AllCaseEqs()]
      \\ rw [Boolv_def] \\ rw [v_ok_def])
    >~ [`do_conversion _ ty1 ty2`]
    >- (gvs[oneline do_conversion_def, v_ok_def, AllCaseEqs()])
    >- (
      gvs [store_alloc_def, post_state_ok_def]
      \\ strip_tac
      \\ first_x_assum (drule_all_then assume_tac) \\ gs []
    )
    >- (
      irule v_ok_v_to_list
      \\ first_assum (irule_at Any)
      \\ first_x_assum irule \\ gs []
      \\ gs [post_state_ok_def]))
QED

Theorem evaluate_basis_v_ok_decs_Nil:
  ^(get_goal "[]:dec list")
Proof
  rw [evaluate_decs_def, extend_dec_env_def]
QED

Theorem evaluate_basis_v_ok_decs_Cons:
  ^(get_goal "_::_::_:dec list")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"], SF SFY_ss]
  \\ drule_all_then assume_tac evaluate_decs_post_state_mono
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ gs [combine_dec_result_def]
  \\ CASE_TAC \\ gs []
  \\ gs [extend_dec_env_def, env_ok_def, SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  rw [evaluate_decs_def] \\ gvs [evaluate_def]
  >- (
    CASE_TAC \\ gs []
    \\ Cases_on ‘p’ \\ gvs [pmatch_def]
    \\ gs [extend_dec_env_def, env_ok_def, nsLookup_nsAppend_some,
           nsLookup_alist_to_ns_some, SF SFY_ss]
    \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
    \\ rw [] \\ gs [v_ok_def, env_ok_def, SF SFY_ss])
  \\ gvs [evaluate_decs_def, CaseEqs ["prod", "semanticPrimitives$result"],
          SF SFY_ss]
  \\ CASE_TAC \\ gs []
  \\ Cases_on ‘p’ \\ gvs [pmatch_def]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dletrec:
  ^(get_goal "Dletrec")
Proof
  rw [evaluate_decs_def] \\ gs []
  \\ gs [extend_dec_env_def, build_rec_env_merge, env_ok_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP, EXISTS_PROD]
  \\ simp [v_ok_def, DISJ_EQ_IMP]
  \\ rw [] \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  rw [evaluate_decs_def] \\ gs []
  \\ gs [post_state_ok_def, env_ok_def, extend_dec_env_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ ‘∀m tds n l t k.
        nsLookup (build_tdefs m tds) n = SOME (l, TypeStamp t k) ⇒
          m ≤ k ∧
          k < m + LENGTH tds’
    by (ho_match_mp_tac build_tdefs_ind
        \\ simp [build_tdefs_def, nsLookup_nsAppend_some,
                 nsLookup_alist_to_ns_some, SF SFY_ss]
        \\ rw [] \\ gs [SF SFY_ss]
        >- (
          first_x_assum drule
          \\ gs [])
        >- (
          first_x_assum drule
          \\ gs [])
        \\ drule_then assume_tac ALOOKUP_MEM
        \\ gs [build_constrs_def, MEM_MAP, EXISTS_PROD])
  >~ [‘id_to_n id ∈ kernel_ctors’] >- (
    first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac) \\ gs [])
  \\ strip_tac
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_x_assum (drule_all_then assume_tac) \\ gs []
QED

Theorem evaluate_basis_v_ok_decs_Dtabbrev:
  ^(get_goal "Dtabbrev")
Proof
  rw [evaluate_decs_def]
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Denv:
  ^(get_goal "Denv")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"]]
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ gvs [declare_env_def, CaseEqs ["option", "eval_state", "prod"]]
  \\ fs [eval_state_ok_def,SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [v_ok_def, env_ok_def, nat_to_v_def, SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dexn:
  ^(get_goal "Dexn")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"], state_ok_def]
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ conj_tac
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dmod:
  ^(get_goal "Dmod")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"], SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ rpt conj_tac
  \\ Cases \\ gs [ml_progTheory.nsLookup_nsBind_compute,
                  nsLookup_nsAppend_some,
                  nsLookup_nsLift]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok_decs_Dlocal:
  ^(get_goal "Dlocal")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"], SF SFY_ss]
  \\ drule_all_then assume_tac evaluate_decs_post_state_mono
  \\ first_x_assum (drule_all_then assume_tac) \\ gs []
  \\ first_x_assum (drule_all_then assume_tac)
  \\ CASE_TAC \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ rpt conj_tac
  \\ Cases \\ gs [ml_progTheory.nsLookup_nsBind_compute,
                nsLookup_nsAppend_some]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_basis_v_ok:
  ^(evaluate_basis_v_ok ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac \\ rpt gen_tac
  \\ TRY (simp [] \\ NO_TAC)
  \\ rewrite_tac [evaluate_basis_v_ok_Nil, evaluate_basis_v_ok_Cons,
                  evaluate_basis_v_ok_Lit, evaluate_basis_v_ok_Con,
                  evaluate_basis_v_ok_Var, evaluate_basis_v_ok_App,
                  evaluate_basis_v_ok_decs_Nil,
                  evaluate_basis_v_ok_decs_Cons,
                  evaluate_basis_v_ok_decs_Dlet,
                  evaluate_basis_v_ok_decs_Dletrec,
                  evaluate_basis_v_ok_decs_Dtype,
                  evaluate_basis_v_ok_decs_Dtabbrev,
                  evaluate_basis_v_ok_decs_Denv,
                  evaluate_basis_v_ok_decs_Dexn,
                  evaluate_basis_v_ok_decs_Dmod,
                  evaluate_basis_v_ok_decs_Dlocal]
QED

Theorem evaluate_basis_v_ok_decs = el 3 (CONJUNCTS evaluate_basis_v_ok);

Theorem post_state_ok_with_clock[simp]:
  post_state_ok (s with clock := ck) = post_state_ok s
Proof
  rw [post_state_ok_def]
QED
