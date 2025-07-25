(*
  Correctness proof for the Dafny to CakeML compiler.
*)

open preamble
open astTheory
open semanticPrimitivesTheory
open evaluateTheory
open evaluatePropsTheory
open dafny_astTheory
open dafny_semanticPrimitivesTheory
open dafny_evaluateTheory
open dafny_evaluatePropsTheory
open namespaceTheory
open namespacePropsTheory
open mlstringTheory
open integerTheory
open mlintTheory
open result_monadTheory
open dafny_freshenProofTheory
open dafny_to_cakemlTheory

val _ = new_theory "dafny_to_cakemlProof";
val _ = set_grammar_ancestry
          ["ast", "semanticPrimitives", "evaluate", "evaluateProps",
           "dafny_semanticPrimitives", "dafny_evaluate", "dafny_evaluateProps",
           "namespace", "namespaceProps", "mlstring", "integer", "mlint",
           "result_monad", "dafny_freshenProof", "dafny_to_cakeml"];

(* TODO Remove unused definition / trivialities *)

Type dfy_state[pp] = “:dafny_semanticPrimitives$state”
Type dfy_env[pp] = “:dafny_semanticPrimitives$sem_env”
Type dfy_exp[pp] = “:dafny_ast$exp”
Type dfy_exp_res[pp] = “:'a dafny_semanticPrimitives$exp_result”

Type cml_state[pp] = “:'ffi semanticPrimitives$state”
Type cml_env[pp] = “:v semanticPrimitives$sem_env”
Type cml_exp[pp] = “:ast$exp”
Type cml_res[pp] = “:(v list, v) semanticPrimitives$result”
Type cml_ns[pp] = “:(string, string, v) namespace”

Triviality Stuple_Tuple:
  LENGTH xs ≠ 1 ⇒ Stuple xs = Tuple xs
Proof
  namedCases_on ‘xs’ ["", "x xs'"]
  \\ gvs [Stuple_def]
  \\ namedCases_on ‘xs'’ ["", "x' xs''"]
  \\ gvs [Stuple_def]
QED

Triviality Pstuple_Tuple:
  LENGTH xs ≠ 1 ⇒ Pstuple xs = Pcon NONE xs
Proof
  namedCases_on ‘xs’ ["", "x xs'"]
  \\ gvs [Pstuple_def]
  \\ namedCases_on ‘xs'’ ["", "x' xs''"]
  \\ gvs [Pstuple_def]
QED

Triviality is_fresh_neq[simp]:
  is_fresh n ∧ ¬is_fresh n' ⇒ n ≠ n'
Proof
  rpt strip_tac \\ gvs [is_fresh_def]
QED

(* TODO Upstream these? Most likely will break things. *)
Triviality nsOptBind_some_simp[simp]:
  nsOptBind (SOME n) x env = nsBind n x env
Proof
  gvs [nsOptBind_def]
QED

Triviality nsOptBind_none_simp[simp]:
  nsOptBind NONE x env = env
Proof
  gvs [nsOptBind_def]
QED

Triviality no_shadow_evaluate_exp:
  no_shadow (set (MAP FST s.locals)) stmt ∧
  evaluate_exp s env stmt' = (s', r) ⇒
  no_shadow (set (MAP FST s'.locals)) stmt
Proof
  rpt strip_tac
  \\ imp_res_tac evaluate_exp_with_clock \\ gvs []
QED

Triviality no_shadow_evaluate_stmt:
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
  has_cons env ⇔
    nsLookup env.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env.c (Short "False") = SOME (0, TypeStamp "False" 0) ∧
    nsLookup env.c (Short "Return") = SOME (0, ret_stamp)
End

(* TODO Move to dafny_ast? *)
Definition dest_program_def:
  dest_program (Program members) = members
End

Inductive callable_rel:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_cons env ⇒
  callable_rel prog name (Recclosure env cml_funs ("dfy_" ++ (explode name)))
End

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    env_dfy.is_running ∧
    has_cons env_cml ∧
    ∀name member.
      get_member name env_dfy.prog = SOME member ⇒
      is_fresh_member member ∧
      no_shadow_method member ∧
      ∃reclos.
        nsLookup env_cml.v (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
        callable_rel env_dfy.prog name reclos
End

Inductive val_rel:
[~bool:]
  val_rel m (BoolV b) (Boolv b)
[~int:]
  val_rel m (IntV i) (Litv (IntLit i))
[~str:]
  val_rel m (StrV s) (Litv (StrLit (explode s)))
[~arr:]
  len' = &len ∧ FLOOKUP m loc = SOME loc' ⇒
  val_rel m (ArrV len loc) (Conv NONE [Litv (IntLit (len')); Loc T loc'])
End

Theorem val_rel_simp[simp] = LIST_CONJ $
  map (SCONV [val_rel_cases]) [“val_rel m (BoolV b) v”,
                               “val_rel m (IntV i) v”,
                               “val_rel m (StrV s) v”,
                               “val_rel m (ArrV len loc) v”];

Definition array_rel_def:
  array_rel m s_heap c_store ⇔
    INJ (λx. m ' x) (FDOM m) 𝕌(:num) ∧
    (∀i. i ∈ FDOM m ⇒ i < LENGTH s_heap) ∧
    (∀i. i ∈ FRANGE m ⇒ i < LENGTH c_store) ∧
    ∀loc vs.
      LLOOKUP s_heap loc = SOME (HArr vs) ⇒
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
        nsLookup env_v (Short (explode var)) = SOME (Loc T loc) ∧
        (∀dfy_v. dfy_ov = SOME dfy_v ⇒ val_rel m dfy_v cml_v)
End

(* TODO *)
Definition print_rel_def:
  print_rel _ _ = ARB
End

Definition state_rel_def:
  state_rel m l s (t: 'ffi cml_state) cml_env ⇔
    s.clock = t.clock ∧
    array_rel m s.heap t.refs ∧
    locals_rel m l s.locals t.refs cml_env.v ∧
    print_rel s.output t.ffi.io_events
End

Definition exp_res_rel_def[simp]:
  (exp_res_rel m (Rval dfy_v) (Rval [cml_v]) ⇔ val_rel m dfy_v cml_v) ∧
  (exp_res_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_res_rel _ _ _ ⇔ F)
End

Triviality exp_res_rel_rval[simp]:
  exp_res_rel m (Rval dfy_v) r_cml ⇔
    ∃cml_v. r_cml = Rval [cml_v] ∧ val_rel m dfy_v cml_v
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘vs’ ["", "v rest"] \\ gvs []
  \\ Cases_on ‘rest’ \\ gvs []
QED

Triviality exp_res_rel_rerr[simp]:
  exp_res_rel m (Rerr dfy_err) r_cml ⇔
  dfy_err = Rtimeout_error ∧ r_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Definition exp_ress_rel_def[simp]:
  (exp_ress_rel m (Rval dfy_vs) (Rval cml_vs) ⇔
     LIST_REL (val_rel m) dfy_vs cml_vs) ∧
  (exp_ress_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_ress_rel _ _ _ ⇔ F)
End

Triviality exp_ress_rel_rerr[simp]:
  exp_ress_rel m (Rerr dfy_err) rs_cml ⇔
  dfy_err = Rtimeout_error ∧ rs_cml = (Rerr (Rabort Rtimeout_error))
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["raise", "abort"] \\ gvs []
  \\ Cases_on ‘abort’ \\ gvs []
  \\ Cases_on ‘dfy_err’ \\ gvs []
QED

Triviality exp_ress_rel_rval[simp]:
  exp_ress_rel m (Rval dfy_vs) rs_cml ⇔
  ∃cml_vs. rs_cml = Rval cml_vs ∧ LIST_REL (val_rel m) dfy_vs cml_vs
Proof
  namedCases_on ‘rs_cml’ ["vs", "err"] \\ gvs []
QED

Definition stmt_res_rel_def[simp]:
  (stmt_res_rel Rcont (Rval _) ⇔ T) ∧
  (stmt_res_rel (Rstop Sret) (Rerr (Rraise val)) ⇔ is_ret_exn val) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout_error))
     (Rerr (Rabort Rtimeout_error)) ⇔ T) ∧
  (stmt_res_rel _ _ ⇔ F)
End

Triviality stmt_res_rel_simp[simp]:
  (stmt_res_rel Rcont r_cml ⇔
     ∃vs. r_cml = Rval vs) ∧
  (stmt_res_rel (Rstop Sret) r_cml ⇔
     ∃v. r_cml = Rerr (Rraise v) ∧ is_ret_exn v) ∧
  (stmt_res_rel (Rstop (Serr Rtimeout_error)) r_cml ⇔
     r_cml = (Rerr (Rabort Rtimeout_error)))
Proof
  namedCases_on ‘r_cml’ ["vs", "err"] \\ gvs []
  \\ namedCases_on ‘err’ ["exn", "abrt"] \\ gvs []
  \\ Cases_on ‘abrt’ \\ gvs []
QED

Triviality read_local_some_imp:
  read_local s.locals name = SOME dfy_v ∧
  state_rel m l s (t: 'ffi cml_state) env ∧
  is_fresh name ⇒
  ∃loc cml_v.
    FLOOKUP l name = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    val_rel m dfy_v cml_v ∧
    nsLookup env.v (Short (explode name)) = SOME (Loc T loc)
Proof
  gvs [state_rel_def, read_local_def, locals_rel_def, CaseEq "option"]
  \\ rpt strip_tac
  \\ first_x_assum drule_all \\ rpt strip_tac
  \\ gvs []
QED

(* TODO Is there a better way to write these nsLookup lemmas? Maybe in a more
     general form? *)

(* TODO Upstream? *)
Triviality nslookup_nsbind[simp]:
  nsLookup (nsBind n v env) (Short n) = SOME v
Proof
  Cases_on ‘env’ \\ gvs [nsBind_def, nsLookup_def]
QED

(* TODO Upstream? *)
Triviality neq_nslookup_nsbind:
  n ≠ n' ⇒
  nsLookup (nsBind n' v env) (Short n) = nsLookup env (Short n)
Proof
  Cases_on ‘env’ \\ gvs [nsBind_def, nsLookup_def]
QED

Triviality state_rel_env_push_not_fresh:
  state_rel m l s (t: 'ffi cml_state) env ∧ ¬(is_fresh n) ⇒
  state_rel m l s t (env with v := (nsBind (explode n) v env.v))
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Triviality state_rel_env_pop_not_fresh:
  ¬(is_fresh n) ∧
  state_rel m l s (t: 'ffi cml_state)
            (env with v := (nsBind (explode n) v env.v)) ⇒
  state_rel m l s t env
Proof
  gvs [state_rel_def, locals_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule_all
  \\ rpt strip_tac
  \\ rename [‘store_lookup loc _ = SOME (Refv cml_v)’]
  \\ qexistsl [‘loc’, ‘cml_v’] \\ gvs []
QED

Triviality is_fresh_not_dfy_pfx:
  is_fresh (implode n) ⇒ n ≠ ("dfy_" ++ explode sfx)
Proof
  Cases_on ‘n’ \\ simp [is_fresh_def, isprefix_thm]
QED

Triviality every_is_fresh_not_dfy:
  EVERY (λn. is_fresh n) ns ⇒
  ∀sfx. EVERY (λn. n ≠ "dfy_" ++ (explode sfx)) (MAP explode ns)
Proof
  simp [EVERY_MEM, MEM_MAP]
  \\ rpt strip_tac
  \\ last_x_assum $ drule_then assume_tac
  \\ Cases_on ‘explode y’
  \\ fs [is_fresh_def, isprefix_thm]
QED

Triviality locals_rel_env_change:
  (∀n. is_fresh n ⇒
       nsLookup env_v (Short (explode n)) =
       nsLookup env_v' (Short (explode n))) ∧
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

Triviality state_rel_env_change:
  (∀n. is_fresh n ⇒
       nsLookup env.v (Short (explode n)) =
       nsLookup env'.v (Short (explode n))) ∧
  state_rel m l s t env ⇒
  state_rel m l s t env'
Proof
  rpt strip_tac \\ gvs [state_rel_def]
  \\ irule locals_rel_env_change
  \\ last_assum $ irule_at Any \\ gvs []
QED

Triviality env_rel_env_change:
  (∀n. "dfy_" ≼ n ⇒
       nsLookup env_cml.v (Short n) = nsLookup env_cml'.v (Short n)) ∧
  has_cons env_cml' ∧
  env_rel env_dfy env_cml ⇒
  env_rel env_dfy env_cml'
Proof
  simp [env_rel_def]
  \\ rpt strip_tac
  \\ first_x_assum drule \\ gvs []
QED

(* TODO Better way of writing this? Perhaps using state_fupdcanon? *)
Triviality with_same_refs_ffi[simp]:
  (t: 'ffi cml_state) with <| refs := t.refs; ffi := t.ffi |> = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality with_same_ffi[simp]:
  (t: 'ffi cml_state) with <| clock := c; refs := r; ffi := t.ffi |> =
  t with <| clock := c; refs := r |>
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality with_same_ffi1[simp]:
  (t: 'ffi cml_state) with <| refs := r; ffi := t.ffi |> =
  t with <| refs := r |>
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality state_rel_llookup:
  state_rel m l s t env ∧
  LLOOKUP s.heap dfy_loc = SOME (HArr dfy_arr) ∧
  FLOOKUP m dfy_loc = SOME cml_loc ⇒
  ∃cml_arr.
    store_lookup cml_loc t.refs = SOME (Varray cml_arr) ∧
    LIST_REL (val_rel m) dfy_arr cml_arr
Proof
  rpt strip_tac
  \\ gvs [state_rel_def, array_rel_def]
  \\ last_x_assum drule \\ rpt strip_tac \\ gvs []
QED

Triviality get_member_some_fun_name:
  get_member n p = SOME (Function n' ins res_t reqs rds decrs body) ⇒
  n' = n
Proof
  namedCases_on ‘p’ ["members"] \\ Induct_on ‘members’
  \\ gvs [get_member_def, get_member_aux_def]
  \\ qx_gen_tac ‘member’ \\ rpt strip_tac
  \\ namedCases_on ‘member’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = n’ \\ gvs []
QED

Triviality find_recfun_some_aux:
  ∀name members member cml_funs.
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    ∃cml_param cml_body.
      from_member_decl member =
        INR ("dfy_" ++ explode name, cml_param, cml_body) ∧
      find_recfun ("dfy_" ++ explode name) cml_funs =
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

Triviality find_recfun_some:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ⇒
  ∃cml_param cml_body.
    from_member_decl member =
      INR ("dfy_" ++ explode name, cml_param, cml_body) ∧
    find_recfun ("dfy_" ++ explode name) cml_funs =
      SOME (cml_param, cml_body)
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all find_recfun_some_aux \\ gvs []
QED

Triviality callable_rel_inversion:
  callable_rel prog name reclos ⇒
  ∃env cml_funs member.
    reclos = (Recclosure env cml_funs ("dfy_" ++ (explode name))) ∧
    get_member name prog = SOME member ∧
    result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
    ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
    has_cons env
Proof
   rpt strip_tac \\ gvs [callable_rel_cases, SF SFY_ss]
QED

Triviality nsLookup_nsBind:
  nsLookup (nsBind k x b) (Short k) = SOME x
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Triviality nsLookup_nsBind_neq:
  k' ≠ k ⇒ nsLookup (nsBind k' x b) (Short k) = nsLookup b (Short k)
Proof
  Cases_on ‘b’ \\ gvs [nsLookup_def, nsBind_def]
QED

Triviality nslookup_build_rec_env_reclos_aux:
  ∀name members member cml_funs' cml_funs env (env₂_v: cml_ns).
    get_member_aux name members = SOME member ∧
    result_mmap from_member_decl members = INR cml_funs ⇒
    nsLookup
      (FOLDR (λ(f,x,e) env₁. nsBind f (Recclosure env cml_funs' f) env₁)
             env₂_v cml_funs)
      (Short ("dfy_" ++ (explode name))) =
    SOME (Recclosure env cml_funs' ("dfy_" ++ (explode name)))
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

Triviality nslookup_build_rec_env_reclos:
  get_member name prog = SOME member ∧
  result_mmap from_member_decl (dest_program prog) = INR cml_funs ∧
  ALL_DISTINCT (MAP (λ(f,x,e). f) cml_funs) ∧
  has_cons env ⇒
  ∃reclos.
    nsLookup
      (build_rec_env cml_funs env env'_v)
      (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
    callable_rel prog name reclos ∧
    reclos = Recclosure env cml_funs ("dfy_" ++ (explode name))
Proof
  rpt strip_tac
  \\ namedCases_on ‘prog’ ["members"]
  \\ gvs [build_rec_env_def]
  \\ gvs [get_member_def, dest_program_def]
  \\ drule_all nslookup_build_rec_env_reclos_aux
  \\ disch_then $ qspecl_then [‘cml_funs’, ‘env’, ‘env'_v’] mp_tac
  \\ rpt strip_tac \\ gvs []
  \\ gvs [callable_rel_cases]
  \\ qexists ‘member’ \\ gvs [get_member_def, dest_program_def]
QED

Definition store_preserve_def:
  store_preserve base t_refs t'_refs ⇔
    LENGTH t_refs ≤ LENGTH t'_refs ∧
    (* All references below base are unchanged *)
    ∀i v.
      i < base ∧ store_lookup i t_refs = SOME (Refv v) ⇒
      store_lookup i t'_refs = SOME (Refv v)
End

Definition store_preserve_all_def:
  store_preserve_all xs ys ⇔ store_preserve (LENGTH xs) xs ys
End

Triviality store_preserve_same[simp]:
  store_preserve base xs xs
Proof
  gvs [store_preserve_def]
QED

Triviality store_preserve_all_same[simp]:
  store_preserve_all xs xs
Proof
  gvs [store_preserve_all_def]
QED

Triviality store_preserve_decat:
  store_preserve base (xs ++ ys) zs ⇒ store_preserve base xs zs
Proof
  gvs [store_preserve_def, store_lookup_def, EL_APPEND]
QED

Triviality store_preserve_trans:
  store_preserve base xs ys ∧ store_preserve base ys zs ⇒
  store_preserve base xs zs
Proof
  gvs [store_preserve_def]
QED

Triviality store_preserve_all_trans:
  store_preserve_all xs ys ∧ store_preserve_all ys zs ⇒
  store_preserve_all xs zs
Proof
  gvs [store_preserve_all_def, store_preserve_def]
QED

Triviality store_preserve_all_concat:
  store_preserve_all xs ys ⇒ store_preserve_all xs (ys ++ zs)
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def, EL_APPEND]
QED

Triviality store_preserve_all_decat:
  store_preserve_all (xs ++ ys) zs ⇒ store_preserve_all xs zs
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def, EL_APPEND]
QED

Triviality store_preserve_all_locals_rel:
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

Triviality store_preserve_all_weaken:
  store_preserve_all xs ys ⇒ store_preserve base xs ys
Proof
  gvs [store_preserve_all_def, store_preserve_def, store_lookup_def]
QED

Triviality state_rel_restore_caller:
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

Triviality gen_arg_names_len[simp]:
  LENGTH (gen_arg_names xs) = LENGTH xs
Proof
  gvs [gen_arg_names_def]
QED

(* TODO Check if needed; add to namespaceTheory? *)
Triviality nsAppend_empty[simp]:
  nsAppend (Bind [] []) b = b
Proof
  Cases_on ‘b’ \\ gvs [nsAppend_def]
QED

Triviality with_same_clock[simp]:
  (t: 'ffi cml_state) with clock := t.clock = t
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality env_rel_nsLookup:
  env_rel env_dfy env_cml ∧
  get_member name env_dfy.prog = SOME member ⇒
  is_fresh_member member ∧ no_shadow_method member ∧
  ∃reclos.
    nsLookup env_cml.v (Short ("dfy_" ++ (explode name))) = SOME reclos ∧
    callable_rel env_dfy.prog name reclos
Proof
  rpt strip_tac \\ gvs [env_rel_def] \\ res_tac
QED

Triviality map_from_exp_empty[simp]:
  map_from_exp [] = INR []
Proof
  gvs [from_exp_def]
QED

Triviality cml_apps_apps:
  ∀xs id. xs ≠ [] ⇒ cml_apps id xs = Apps id xs
Proof
  Cases_on ‘xs’ \\ gvs [cml_apps_def]
QED

Definition member_get_ins_def[simp]:
  member_get_ins (Method _ ins _ _ _ _ _ _ _) = ins ∧
  member_get_ins (Function _ ins _ _ _ _ _) = ins
End

Triviality map_from_exp_len:
  ∀es cml_es. map_from_exp es = INR cml_es ⇒ LENGTH cml_es = LENGTH es
Proof
  Induct_on ‘es’ \\ rpt strip_tac
  \\ gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
QED

(* TODO Move to evaluateProps *)
Triviality evaluate_exps_length:
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

Triviality enumerate_from_cons:
  enumerate_from offset (n::ns) =
  (n, offset)::(enumerate_from (offset + 1) ns)
Proof
  gvs [enumerate_from_def] \\ irule MAPi_CONG \\ gvs [ADD1]
QED

Triviality enumerate_from_append:
  ∀offset xs ys.
    enumerate_from offset (xs ++ ys) =
    (enumerate_from offset xs) ++ (enumerate_from (offset + LENGTH xs) ys)
Proof
  Induct_on ‘xs’ >- gvs [enumerate_from_def]
  \\ rpt strip_tac
  \\ gvs [enumerate_from_cons, ADD1]
QED

Definition add_refs_to_env_def:
  add_refs_to_env (env_v: (string, string, v) namespace) ns offset =
    nsAppend
      (alist_to_ns
         (REVERSE (MAP (λ(n, i). (n, Loc T i)) (enumerate_from offset ns))))
      env_v
End

Definition mk_locals_map_def:
  mk_locals_map (ns: mlstring list) offset =
    FEMPTY |++ (enumerate_from offset ns)
End

Triviality mk_locals_map_append:
  mk_locals_map (xs ++ ys) offset =
  (mk_locals_map xs offset) |++ (enumerate_from (offset + LENGTH xs) ys)
Proof
  gvs [mk_locals_map_def] \\ gvs [enumerate_from_append, FUPDATE_LIST_APPEND]
QED

Triviality inj_mk_locals_map:
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

Triviality FST_enumerate_from[simp]:
  ∀offset. MAP FST (enumerate_from offset vars) = vars
Proof
  Induct_on ‘vars’
  >- gvs [enumerate_from_def]
  \\ gvs [enumerate_from_cons]
QED

Triviality with_same_refs[simp]:
  s with refs := s.refs = s
Proof
  gvs [semanticPrimitivesTheory.state_component_equality]
QED

Triviality lambda_SUC[simp]:
  (λi n. (n, i + x)) ∘ SUC = (λi n. (n, i + (x + 1)))
Proof
  gvs [FUN_EQ_THM]
QED

Triviality ALOOKUP_enumerate_from:
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

Triviality FRANGE_mk_locals_map:
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
Triviality nsappend_alist_to_ns_nsbind:
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

Triviality nsappend_alist_to_ns_reverse_cons:
  nsAppend (alist_to_ns (REVERSE xs ++ [(n,v)])) env_v =
  nsAppend (alist_to_ns (REVERSE xs)) (nsBind n v env_v)
Proof
  Cases_on ‘env_v’
  \\ gvs [alist_to_ns_def, nsAppend_def, nsBind_def]
QED

Triviality add_refs_to_env_cons:
  add_refs_to_env env_v (n::ns) offset =
  (add_refs_to_env (nsBind n (Loc T offset) env_v) ns (offset + 1))
Proof
  gvs [add_refs_to_env_def, enumerate_from_cons,
       nsappend_alist_to_ns_reverse_cons]
QED

Triviality evaluate_set_up_in_refs:
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

Triviality not_mem_nslookup_nsappend_alist:
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

Triviality FST_o_n_Loc[simp]:
  FST ∘ (λ(n,i). (n, Loc T i)) = FST
Proof
  gvs [FUN_EQ_THM] \\ Cases \\ gvs []
QED

Triviality not_mem_nslookup_add_refs_to_env:
  ¬MEM x ns ⇒
  nsLookup (add_refs_to_env env_v ns offset) (Short x) =
  nsLookup env_v (Short x)
Proof
  strip_tac
  \\ simp [add_refs_to_env_def]
  \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
  \\ simp [MAP_REVERSE, MAP_MAP_o]
QED

Triviality store_lookup_append:
  store_lookup l st = SOME v ⇒ store_lookup l (st ++ st') = SOME v
Proof
  rpt strip_tac \\ gvs [store_lookup_def, rich_listTheory.EL_APPEND1]
QED

Triviality array_rel_append:
  array_rel m s_heap t_heap ⇒
  array_rel m s_heap (t_heap ++ xs)
Proof
  gvs [array_rel_def]
  \\ rpt strip_tac
  >- (qpat_assum ‘∀_. _ ∈ FRANGE _ ⇒ _ < _’ $ drule_then assume_tac
      \\ intLib.COOPER_TAC)
  \\ last_x_assum drule \\ rpt strip_tac
  \\ drule store_lookup_append
  \\ disch_then $ qspec_then ‘xs’ assume_tac
  \\ gvs []
QED

Triviality read_local_reverse_eq:
  ALL_DISTINCT (MAP FST l) ⇒ read_local (REVERSE l) var = read_local l var
Proof
  rpt strip_tac
  \\ drule alookup_distinct_reverse
  \\ disch_then $ qspec_then ‘var’ assume_tac
  \\ gvs [read_local_def]
QED

Triviality ALOOKUP_ZIP_SOME_EL:
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

Triviality nsLookup_add_refs_to_env:
  ALL_DISTINCT ns ∧
  i < LENGTH ns ⇒
  nsLookup
    (add_refs_to_env env_v (MAP explode ns) offset)
    (Short (explode (EL i ns))) =
  SOME (Loc T (i + offset))
Proof
  rpt strip_tac
  \\ gvs [add_refs_to_env_def]
  \\ gvs [nsLookup_nsAppend_some]
  \\ disj1_tac
  \\ gvs [nsLookup_alist_to_ns_some]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse]
  \\ strip_tac >- (gvs [MAP_MAP_o])
  \\ gvs [ALOOKUP_MAP]
  \\ ‘explode (EL i ns) = EL i (MAP explode ns)’ by gvs [EL_MAP]
  \\ simp [ALOOKUP_enumerate_from]
QED

Triviality LIST_REL_store_lookup:
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

Triviality ALOOKUP_ZIP_MAP_SOME_SOME:
  ALOOKUP (ZIP (ns, MAP SOME vs)) var = SOME ov ∧
  LENGTH ns = LENGTH vs ⇒
  ∃v. ov = SOME v
Proof
  rpt strip_tac
  \\ drule ALOOKUP_MEM \\ rpt strip_tac
  \\ gvs [MEM_ZIP, EL_MAP]
QED

Triviality FLOOKUP_mk_locals_map:
  i < LENGTH ns ∧ ALL_DISTINCT ns ⇒
  FLOOKUP (mk_locals_map ns offset) (EL i ns) = SOME (i + offset)
Proof
  strip_tac
  \\ imp_res_tac ALOOKUP_enumerate_from
  \\ simp [mk_locals_map_def, flookup_fupdate_list, CaseEq "option"]
  \\ DEP_REWRITE_TAC [alookup_distinct_reverse] \\ simp []
QED

(* TODO Is this a good way to write this?/Upstream to HOL *)
Triviality SNOC_HD_REVERSE_TL:
  xs ≠ [] ⇒ SNOC (HD xs) (REVERSE (TL xs)) = REVERSE xs
Proof
  rpt strip_tac
  \\ ‘(HD xs)::(TL xs) = xs’ by gvs []
  \\ asm_rewrite_tac [GSYM (cj 2 REVERSE_SNOC_DEF)]
QED

Triviality INJ_FLOOKUP_IMP:
  INJ (λx: num. m ' x) (FDOM m) 𝕌(:num) ∧
  FLOOKUP m x = SOME v ∧ FLOOKUP m y = SOME w ⇒
  (v = w ⇔ x = y)
Proof
  simp [INJ_DEF, FLOOKUP_DEF] \\ metis_tac []
QED

Triviality state_rel_array_loc_INJ:
  state_rel m l s (t: 'ffi cml_state) env_cml ⇒
  INJ (λx. m ' x) (FDOM m) 𝕌(:num)
Proof
  gvs [state_rel_def, array_rel_def]
QED

(* TODO Upstream? *)
Triviality LIST_REL_nsLookup_nsAppend:
  ∀names vals (ns: (string, string, v) namespace).
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
Triviality LIST_REL_nsLookup_nsAppend_REVERSE:
  ∀names vals (ns: (string, string, v) namespace).
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
Triviality LIST_REL_nsLookup_nsAppend_REVERSE1:
  ∀names vals (ns: (string, string, v) namespace).
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

Triviality alookup_nslookup_store_lookup:
  ∀(s: 'ffi cml_state) env ins in_vs var dfy_v m cml_vs.
    ALOOKUP (ZIP (MAP FST ins, MAP SOME in_vs)) var = SOME (SOME dfy_v) ∧
    LIST_REL (val_rel m) in_vs cml_vs ∧
    ALL_DISTINCT (MAP FST ins) ∧
    LENGTH in_vs = LENGTH ins ⇒
    ∃loc cml_v.
      nsLookup
        (add_refs_to_env env.v ((MAP (explode ∘ FST) ins))
           (LENGTH s.refs))
        (Short (explode var)) = SOME (Loc T loc) ∧
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

Triviality NOT_MEM_TL:
  ¬MEM x xs ⇒ ¬MEM x (TL xs)
Proof
  rpt strip_tac \\ drule MEM_TL \\ simp []
QED

Triviality cml_fun_MEM_var:
  cml_fun params body = (param, cml_body) ∧ params ≠ [] ⇒
  MEM param params
Proof
  Cases_on ‘params’ \\ simp [cml_fun_def]
QED

Theorem correct_from_exp:
  (∀s env_dfy e_dfy s' r_dfy (t: 'ffi cml_state) env_cml e_cml m l.
     evaluate_exp s env_dfy e_dfy = (s', r_dfy) ∧
     from_exp e_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ is_fresh_exp e_dfy ∧
     r_dfy ≠ Rerr Rtype_error
     ⇒ ∃ck (t': 'ffi cml_state) r_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
           (t', r_cml) ∧
         store_preserve_all t.refs t'.refs ∧
         state_rel m l s' t' env_cml ∧
         exp_res_rel m r_dfy r_cml) ∧
  (∀s env_dfy es_dfy s' rs_dfy (t: 'ffi cml_state) env_cml es_cml m l.
     evaluate_exps s env_dfy es_dfy = (s', rs_dfy) ∧
     map_from_exp es_dfy = INR es_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ EVERY (λe. is_fresh_exp e) es_dfy ∧
     rs_dfy ≠ Rerr Rtype_error
     ⇒ ∃ck (t': 'ffi cml_state) rs_cml.
         evaluate$evaluate (t with clock := t.clock + ck) env_cml es_cml =
           (t', rs_cml) ∧
         store_preserve_all t.refs t'.refs ∧
         state_rel m l s' t' env_cml ∧
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
    \\ qabbrev_tac ‘fname = "dfy_" ++ (explode name)’ \\ gvs []
    \\ drule map_from_exp_len \\ rpt strip_tac \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
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
      \\ qabbrev_tac ‘params = MAP (explode ∘ FST) ins’
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
      \\ gvs [restore_caller_def, state_rel_def])
    \\ qabbrev_tac ‘dfy_locals = REVERSE (ZIP (MAP FST ins, MAP SOME in_vs))’
    \\ qmatch_asmsub_abbrev_tac ‘evaluate_exp call_t’
    \\ namedCases_on ‘evaluate_exp call_t env_dfy body’ ["s₂ r"]
    \\ gvs [Abbr ‘call_t’]
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
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
                 nsBind "" (Conv NONE []) (build_rec_env cml_funs env env.v)’,
              ‘m’, ‘l’]
             mp_tac
      \\ impl_tac
      >-
       (unabbrev_all_tac
        \\ gvs [state_rel_def, dec_clock_def, evaluateTheory.dec_clock_def,
                locals_rel_def, read_local_def, env_rel_def]
        \\ rpt strip_tac
        >- gvs [has_cons_def]
        >- res_tac
        >- res_tac
        >- (drule_all nslookup_build_rec_env_reclos \\ gvs []))
      \\ rpt strip_tac
      \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = _’]
      \\ qexists ‘ck'’
      \\ gvs [cml_apps_def, evaluate_def, do_con_check_def, build_conv_def,
              do_opapp_def]
      \\ gvs [set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def]
      \\ gvs [evaluate_def, do_con_check_def, build_conv_def,
              evaluateTheory.dec_clock_def]
      \\ Cases_on ‘r’ \\ gvs []
      \\ drule_all state_rel_restore_caller \\ gvs [])
    (* Evaluating (non-empty) args succeeded *)
    \\ Cases_on ‘cml_args = []’ \\ gvs []
    \\ Cases_on ‘cml_vs = []’ \\ gvs []
    \\ DEP_REWRITE_TAC [cml_apps_apps] \\ gvs []
    (* TODO Maybe we should case distinction on args earlier? *)
    (* Preparing ns for evaluate_Apps *)
    \\ qabbrev_tac ‘params = (MAP (explode ∘ FST) ins)’
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
            \\ drule alookup_nslookup_store_lookup
            \\ disch_then drule \\ gvs []
            \\ disch_then $ qspecl_then [‘t₁’, ‘call_env₁’] mp_tac
            \\ rpt strip_tac \\ gvs [Abbr ‘call_env₂’, Abbr ‘params’])
        \\ gvs [env_rel_def] \\ rpt strip_tac
        >- (unabbrev_all_tac \\ gvs [has_cons_def])
        >- res_tac
        >- res_tac
        \\ rename [‘get_member name' _ = SOME _’]
        \\ ‘EVERY (λn. n ≠ STRCAT "dfy_" (explode name')) (REVERSE params)’ by
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
    \\ gvs [state_rel_def, restore_caller_def]
    \\ irule store_preserve_all_locals_rel
    \\ last_assum $ irule_at (Pos hd) \\ gvs [])
  >~ [‘Lit l’] >-
   (qexists ‘0’
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
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
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
    \\ gvs [do_if_def]
    \\ irule store_preserve_all_trans \\ gvs [SF SFY_ss])
  >~ [‘UnOp uop e’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ qexists ‘ck’
    \\ Cases_on ‘uop’ \\ gvs [from_un_op_def, evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["v", "err"] \\ gvs []
    \\ gvs [do_uop_def, CaseEqs ["value", "option"]]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’ \\ gvs []
    \\ gvs [do_if_def, evaluate_def, do_con_check_def, build_conv_def,
            env_rel_def, has_cons_def, Boolv_def, bool_type_num_def])
  >~ [‘BinOp bop e₀ e₁’] >-
   (gvs [evaluate_exp_def, from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy e₀’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
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
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ ‘¬is_fresh « l»’ by gvs [is_fresh_def, isprefix_thm]
    \\ drule_all state_rel_env_push_not_fresh
    \\ disch_then $ qspec_then ‘cml_v₀’ assume_tac
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_cons_def] \\ rpt strip_tac \\ res_tac)
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
    >- (Cases_on ‘bop’
        \\ gvs [oneline do_sc_def, val_rel_cases, from_bin_op_def,
                evaluate_def, do_log_def, do_if_def, AllCaseEqs()])
    \\ rename [‘val_rel _ dfy_v₁ cml_v₁’]
    \\ Cases_on ‘do_bop bop dfy_v₀ dfy_v₁’ \\ gvs []
    \\ Cases_on ‘bop = Div’ \\ gvs [] >-
     (gvs [do_bop_def, AllCaseEqs()]
      \\ gvs [from_bin_op_def, EDIV_DEF]
      \\ gvs [evaluate_def, do_app_def, do_if_def, opb_lookup_def]
      \\ Cases_on ‘0 < i₁’
      \\ gvs [evaluate_def, do_app_def, opn_lookup_def, Boolv_def])
    \\ Cases_on ‘bop = Eq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on ‘dfy_v₀’ ["i", "b", "str", "len dfy_loc"] \\ gvs []
      \\ namedCases_on ‘dfy_v₁’ ["i'", "b'", "str'", "len' dfy_loc'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [do_eq_def, lit_same_type_def, Boolv_def, ctor_same_type_def,
                same_type_def])
      >~ [‘do_eq (Conv _ _) (Conv _ _)’] >-
       (drule_all state_rel_array_loc_INJ \\ rpt strip_tac
        \\ drule INJ_FLOOKUP_IMP
        \\ disch_then $ qspecl_then [‘dfy_loc’, ‘dfy_loc'’] mp_tac
        \\ disch_then drule_all
        \\ gvs [do_eq_def, lit_same_type_def]
        \\ Cases_on ‘len = len'’ \\ gvs []
        \\ Cases_on ‘dfy_loc = dfy_loc'’ \\ gvs [])
      \\ gvs [do_eq_def, lit_same_type_def])
    \\ Cases_on ‘bop = Neq’ \\ gvs [] >-
     (gvs [do_bop_def]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def]
      \\ namedCases_on
           ‘dfy_v₀’ ["i", "b", "dfy_str", "len dfy_loc"] \\ gvs []
      \\ namedCases_on
           ‘dfy_v₁’ ["i'", "b'", "dfy_str'", "len' dfy_loc'"] \\ gvs []
      >~ [‘do_eq (Boolv _) (Boolv _)’] >-
       (Cases_on ‘b’ \\ Cases_on ‘b'’
        \\ gvs [evaluate_def, do_eq_def, lit_same_type_def, Boolv_def,
                ctor_same_type_def, same_type_def, do_if_def, do_con_check_def,
                build_conv_def, env_rel_def, has_cons_def,
                bool_type_num_def])
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
                has_cons_def])
      >~ [‘do_eq (Litv (IntLit _)) (Litv (IntLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘i' = i’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_cons_def])
      >~ [‘do_eq (Litv (StrLit _)) (Litv (StrLit _))’] >-
       (gvs [do_eq_def, lit_same_type_def, do_if_def]
        \\ Cases_on ‘dfy_str = dfy_str'’
        \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
                Boolv_def, bool_type_num_def, has_cons_def]))
      \\ gvs [oneline do_bop_def, do_sc_def, AllCaseEqs()]
      \\ gvs [from_bin_op_def]
      \\ gvs [evaluate_def, do_app_def, opb_lookup_def, opn_lookup_def,
              do_log_def, do_if_def])
  >~ [‘ArrLen arr’] >-
   (gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
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
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
    \\ DEP_REWRITE_TAC [Pstuple_Tuple] \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["arr_v",  "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [evaluate_def])
    \\ gvs [evaluate_def]
    \\ rename [‘val_rel _ dfy_arr cml_arr’]
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ ‘¬is_fresh « arr»’ by gvs [is_fresh_def, isprefix_thm]
    \\ drule_all state_rel_env_push_not_fresh \\ gvs []
    \\ disch_then $ qspec_then ‘cml_arr’ assume_tac \\ gvs []
    \\ last_x_assum drule
    \\ impl_tac >-
     (gvs [env_rel_def, has_cons_def] \\ rpt strip_tac \\ res_tac)
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
    \\ drule_all state_rel_llookup \\ rpt strip_tac \\ gvs []
    \\ gvs [INT_ABS]
    \\ drule LIST_REL_LENGTH \\ rpt strip_tac
    \\ gvs [LLOOKUP_EQ_EL, LIST_REL_EL_EQN])
  >~ [‘map_from_exp []’] >-
   (qexists ‘0’ \\ gvs [from_exp_def, evaluate_exp_def, evaluate_def])
  >~ [‘map_from_exp (e::es)’] >-
   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy e’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck + _) _ _’]
    \\ reverse $ namedCases_on ‘r’ ["cml_e",  "err"] \\ gvs []
    >- (qexists ‘ck’
        \\ rename [‘_::cml_es’]
        \\ Cases_on ‘cml_es’ \\ gvs [evaluate_def])
    \\ namedCases_on ‘es’ ["", "e' es"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [evaluate_exp_def, from_exp_def])
    \\ namedCases_on ‘evaluate_exps s₁ env_dfy (e'::es')’ ["s₂ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ gvs [from_exp_def, oneline bind_def, CaseEq "sum"]
    \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ rename [‘evaluate (_ with clock := ck' + _) _ _ = (t₂, _)’]
    \\ qexists ‘ck' + ck’
    \\ rev_drule evaluate_add_to_clock
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ gvs []
    \\ ‘store_preserve_all t.refs t₂.refs’ by
      (irule store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ reverse $ Cases_on ‘r’ \\ gvs [evaluate_def])
  (* These expression do not get compiled *)
  \\ gvs [from_exp_def]
QED

Triviality array_rel_submap:
  array_rel m s.heap t.refs ⇒ m ⊑ m |+ (LENGTH s.heap, LENGTH t.refs)
Proof
  gvs [array_rel_def]
  \\ rpt strip_tac
  \\ disj1_tac
  \\ spose_not_then assume_tac
  \\ qpat_assum ‘∀_. _ ∈ FDOM _ ⇒ _ < _’ drule
  \\ rpt strip_tac \\ gvs []
QED

Triviality submap_val_rel:
  val_rel m dfy_v cml_v ∧ m ⊑ m' ⇒ val_rel m' dfy_v cml_v
Proof
  rpt strip_tac \\ gvs [val_rel_cases, SUBMAP_FLOOKUP_EQN]
QED

(* TODO Upstream? *)
Triviality IMP_LIST_REL_REPLICATE:
  P x y ⇒ LIST_REL P (REPLICATE n x) (REPLICATE n y)
Proof
  Cases_on ‘n’ >- simp []
  \\ rewrite_tac [LIST_REL_EL_EQN]
  \\ rpt strip_tac >- simp []
  \\ DEP_REWRITE_TAC [EL_REPLICATE]
  \\ fs []
QED

Triviality array_rel_add:
  array_rel m s.heap (t: 'ffi cml_state).refs ∧
  val_rel m init_v init_cml_v ⇒
  array_rel
    (m |+ (LENGTH s.heap, LENGTH t.refs))
    (SNOC (HArr (REPLICATE (Num i) init_v)) s.heap)
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
  >- (drule (SRULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET) \\ rpt strip_tac
      \\ qpat_assum ‘∀_. _ ∈ FRANGE _ ⇒ _’ $ drule_then assume_tac
      \\ intLib.COOPER_TAC)
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

Triviality locals_rel_add_array:
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

Theorem correct_from_rhs_exp:
  ∀s env_dfy rhs_dfy s' r_dfy (t: 'ffi cml_state) env_cml e_cml m l.
    evaluate_rhs_exp s env_dfy rhs_dfy = (s', r_dfy) ∧
    from_rhs_exp rhs_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
    env_rel env_dfy env_cml ∧ is_fresh_rhs_exp rhs_dfy ∧
    r_dfy ≠ Rerr Rtype_error ⇒
    ∃ck (t': 'ffi cml_state) m' r_cml.
      evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
      (t', r_cml) ∧ store_preserve_all t.refs t'.refs ∧
      state_rel m' l s' t' env_cml ∧ exp_res_rel m' r_dfy r_cml ∧ m ⊑ m'
Proof
  Cases_on ‘rhs_dfy’ \\ rpt strip_tac
  >~ [‘ExpRhs e’] >-
   (gvs [evaluate_rhs_exp_def, from_rhs_exp_def]
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t'’, ‘r_cml’] assume_tac
    \\ qexistsl [‘ck’, ‘t'’, ‘m’, ‘r_cml’] \\ gvs [])
  >~ [‘ArrAlloc len init’] >-
   (gvs [evaluate_rhs_exp_def]
    \\ gvs [from_rhs_exp_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy len’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ reverse $ namedCases_on ‘r’ ["len_v", "err"] \\ gvs []
    >- (qexistsl [‘ck’, ‘t₁’, ‘m’]
        \\ gvs [cml_alloc_arr_def, evaluate_def])
    \\ namedCases_on ‘evaluate_exp s₁ env_dfy init’ ["s₂ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
    \\ drule (cj 1 correct_from_exp)
    \\ disch_then drule
    \\ disch_then $
         qspecl_then
           [‘t₁’,
            ‘env_cml with v := nsBind " len" cml_v env_cml.v’ ,
            ‘m’, ‘l’]
           mp_tac
    \\ ‘¬is_fresh « len»’ by gvs [is_fresh_def, isprefix_thm]
    \\ impl_tac \\ gvs []
    >- (drule_all state_rel_env_push_not_fresh \\ gvs []
        \\ strip_tac
        \\ irule env_rel_env_change
        \\ conj_tac
        >- (gvs [env_rel_def, has_cons_def])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt gen_tac \\ disch_tac
        \\ ‘n ≠ " len"’ by (Cases_on ‘n’ \\ gvs [])
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
        \\ irule_at Any store_preserve_all_trans \\ gvs [SF SFY_ss])
    \\ rename [‘do_app _ _ [len_cml_v; init_cml_v]’]
    \\ namedCases_on ‘alloc_array s₂ len_v init_v’ ["", "r"] \\ gvs []
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
        \\ ‘explode n ≠ " len"’ by
          (Cases_on ‘explode n’ \\ gvs [is_fresh_def, isprefix_thm])
        \\ simp [])
    >- intLib.COOPER_TAC
    >- gvs [FLOOKUP_SIMP]
    \\ irule array_rel_submap \\ gvs [state_rel_def])
QED

Theorem correct_map_from_rhs_exp:
  ∀s env_dfy rhss_dfy s' r_dfy (t: 'ffi cml_state) env_cml es_cml m l.
    evaluate_rhs_exps s env_dfy rhss_dfy = (s', r_dfy) ∧
    result_mmap from_rhs_exp rhss_dfy = INR es_cml ∧
    state_rel m l s t env_cml ∧ env_rel env_dfy env_cml ∧
    EVERY (λrhs. is_fresh_rhs_exp rhs) rhss_dfy ∧
    r_dfy ≠ Rerr Rtype_error ⇒
    ∃ck (t': 'ffi cml_state) m' r_cml.
      evaluate$evaluate (t with clock := t.clock + ck) env_cml es_cml =
      (t', r_cml) ∧ store_preserve_all t.refs t'.refs ∧
      state_rel m' l s' t' env_cml ∧ exp_ress_rel m' r_dfy r_cml ∧ m ⊑ m'
Proof
  Induct_on ‘rhss_dfy’ \\ rpt strip_tac
  >- (gvs [evaluate_rhs_exps_def, result_mmap_def]
      \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  \\ rename [‘rhs_dfy::rhss_dfy’]
  \\ gvs [evaluate_rhs_exps_def]
  \\ namedCases_on ‘evaluate_rhs_exp s env_dfy rhs_dfy’ ["s₁ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ drule_all correct_from_rhs_exp
  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’, ‘m₁’] mp_tac
  \\ rpt strip_tac
  \\ reverse $ namedCases_on ‘r’ ["rhs_v", "err"] \\ gvs []
  >- (qexists ‘ck’ \\ simp [Once evaluate_cons] \\ gvs [SF SFY_ss])
  \\ namedCases_on ‘evaluate_rhs_exps s₁ env_dfy rhss_dfy’ ["s₂ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
  \\ last_x_assum drule_all
  \\ disch_then $ qx_choosel_then [‘ck'’, ‘t₂’, ‘m₂’] mp_tac
  \\ rpt strip_tac
  \\ rev_drule evaluate_add_to_clock \\ gvs []
  \\ disch_then $ qspec_then ‘ck'’ assume_tac
  \\ qexists ‘ck + ck'’ \\ gvs []
  \\ simp [Once evaluate_cons]
  \\ reverse $ namedCases_on ‘r’ ["rhss_v", "err"] \\ gvs []
  \\ qexists ‘m₂’
  \\ irule_at Any store_preserve_all_trans \\ gvs []
  \\ irule_at Any SUBMAP_TRANS \\ gvs [SF SFY_ss]
  \\ irule_at Any submap_val_rel \\ gvs [SF SFY_ss]
QED

(* The base can be at most at our lowest locals or the current length of
   t_refs. *)
Definition base_at_most_def:
  base_at_most base t_refs (l: mlstring |-> num) ⇔
    (base ≤ LENGTH t_refs ∧ ∀i. i ∈ FRANGE l ⇒ base ≤ i)
End

Triviality base_at_most_lupdate[simp]:
  base_at_most base (LUPDATE store_v loc xs) l = base_at_most base xs l
Proof
  gvs [base_at_most_def]
QED

Triviality store_preserve_base_at_most:
  store_preserve base t.refs t'.refs ∧ base_at_most base t.refs l ⇒
  base_at_most base t'.refs l
Proof
  gvs [base_at_most_def, store_preserve_def]
QED

Triviality locals_above_extend:
  base_at_most base t_refs l ⇒
  base_at_most base (t_refs ++ xs) (l |+ (n, LENGTH t_refs))
Proof
  gvs [base_at_most_def] \\ rpt strip_tac \\ gvs []
  \\ drule_then assume_tac (SRULE [SUBSET_DEF] FRANGE_DOMSUB_SUBSET)
  \\ gvs []
QED

(* TODO Upstream? *)
Triviality pmatch_list_MAP_Pvar:
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

Triviality store_preserve_lupdate_local:
  FLOOKUP l var = SOME loc ∧
  base_at_most base t.refs l ∧
  store_preserve base (LUPDATE store_v loc t.refs) t'.refs ⇒
  store_preserve base t.refs t'.refs
Proof
  gvs [store_preserve_def]
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ rename [‘store_lookup i _ = SOME (Refv v)’]
  \\ disch_then $ qspec_then ‘v’ mp_tac
  \\ impl_tac \\ gvs []
  \\ gvs [store_lookup_def, base_at_most_def, EL_LUPDATE]
  \\ qsuff_tac ‘i ≠ loc’ \\ gvs []
  \\ drule_then assume_tac (cj 1 FINITE_MAP_LOOKUP_RANGE)
  \\ last_assum $ drule_then assume_tac
  \\ decide_tac
QED

Triviality store_preserve_lupdate_array:
  store_lookup loc t.refs = SOME (Varray varr) ∧
  store_preserve base (LUPDATE store_v loc t.refs) t'.refs ⇒
  store_preserve base t.refs t'.refs
Proof
  gvs [store_preserve_def]
  \\ rpt strip_tac
  \\ rename [‘store_lookup i _ = SOME (Refv v)’]
  \\ gvs [store_lookup_def, EL_LUPDATE]
  \\ Cases_on ‘i = loc’ \\ gvs []
QED

Triviality update_array_some_eqs:
  update_array s (ArrV len loc) (IntV idx) val = SOME s' ⇒
  s'.clock = s.clock ∧ s'.output = s.output ∧ s'.locals = s.locals ∧
  LENGTH s'.heap = LENGTH s.heap ∧
  ∀loc'. loc' ≠ loc ⇒ LLOOKUP s'.heap loc' = LLOOKUP s.heap loc'
Proof
  rpt strip_tac \\ gvs [update_array_def, LLOOKUP_LUPDATE, AllCaseEqs()]
QED

(* TODO Rename? *)
Triviality update_array_some_llookup:
  update_array s arr_v idx_v rhs_v = SOME s' ⇒
  ∃len loc idx arr.
    arr_v = ArrV len loc ∧ idx_v = IntV idx ∧ 0 ≤ idx ∧
    LLOOKUP s.heap loc = SOME (HArr arr) ∧
    Num idx < LENGTH arr ∧
    LLOOKUP s'.heap loc = SOME (HArr (LUPDATE rhs_v (Num idx) arr))
Proof
  rpt strip_tac
  \\ gvs [update_array_def, oneline val_to_num_def, LLOOKUP_LUPDATE,
          AllCaseEqs()]
  \\ gvs [LLOOKUP_EQ_EL]  (* Needs to come after LLOOKUP_LUPDATE rewrite *)
  \\ intLib.COOPER_TAC
QED

Triviality update_array_state_rel:
  update_array s (ArrV arr_len loc) (IntV idx) v = SOME s' ∧
  FLOOKUP m loc = SOME loc_cml ∧
  store_lookup loc_cml t.refs = SOME (Varray varr) ∧
  LLOOKUP s'.heap loc = SOME (HArr (LUPDATE v (Num idx) harr)) ∧
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
  >~ [‘locals_rel _ _ _ _ _ (* g *)’] >-
   (gvs [locals_rel_def] \\ rpt strip_tac
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []
    \\ gvs [store_lookup_def, EL_LUPDATE]
    \\ IF_CASES_TAC \\ gvs [])
  \\ gvs [array_rel_def]
  \\ qx_gen_tac ‘loc'’ \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘loc' = loc’ \\ gvs []
  >- (gvs [store_lookup_def, EL_LUPDATE]
      \\ irule EVERY2_LUPDATE_same \\ gvs [])
  \\ first_x_assum drule \\ rpt strip_tac \\ gvs []
  \\ first_x_assum drule \\ rpt strip_tac \\ gvs []
  \\ gvs [store_lookup_def, EL_LUPDATE]
  \\ IF_CASES_TAC \\ gvs [INJ_DEF, FLOOKUP_DEF]
QED

Triviality update_local_aux_some:
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

Triviality lookup_locals_some:
  state_rel m l s t env_cml ∧
  ALOOKUP s.locals var = SOME ov ∧ is_fresh var ⇒
  ∃loc cml_v.
    FLOOKUP l var = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    nsLookup env_cml.v (Short (explode var)) = SOME (Loc T loc)
Proof
  rpt strip_tac
  \\ gvs [state_rel_def, locals_rel_def]
  \\ first_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
QED

Triviality update_local_some_eqs:
  update_local s var val = SOME s' ⇒
  s'.clock = s.clock ∧ s'.output = s.output ∧ s'.heap = s.heap
Proof
  rpt strip_tac \\ gvs [update_local_def, CaseEq "option"]
QED

Triviality update_local_some_alookup:
  update_local s var val = SOME s' ⇒
  ALOOKUP s'.locals var = SOME (SOME val) ∧
  (∃ov. ALOOKUP s.locals var = SOME ov) ∧
  ∀var'. var' ≠ var ⇒ ALOOKUP s'.locals var' = ALOOKUP s.locals var'
Proof
  strip_tac
  \\ irule update_local_aux_some
  \\ gvs [update_local_def, CaseEq "option"]
QED

Triviality update_local_state_rel:
  update_local s var new_v_dfy = SOME s' ∧
  is_fresh var ∧
  state_rel m l s t env_cml ∧
  FLOOKUP l var = SOME loc ∧
  store_lookup loc t.refs = SOME (Refv old_v_cml) ∧
  nsLookup env_cml.v (Short (explode var)) = SOME (Loc T loc) ∧
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

Triviality evaluate_assign_values:
  ∀s env_dfy lhss rhs_vs s' r_dfy names asss_cml cml_vs m l (t: 'ffi cml_state)
     env_cml base.
    assign_values s env_dfy lhss rhs_vs = (s', r_dfy) ∧
    result_mmap2 assign_single lhss (MAP (Var ∘ Short) names) = INR asss_cml ∧
    state_rel m l s t env_cml ∧
    env_rel env_dfy env_cml ∧
    LIST_REL (val_rel m) rhs_vs cml_vs ∧
    LIST_REL (λn v. nsLookup env_cml.v (Short n) = SOME v) names cml_vs ∧
    EVERY (λlhs. is_fresh_lhs_exp lhs) lhss ∧
    EVERY (λn. " arr" ≠ n) names ∧
    base_at_most base t.refs l ∧
    r_dfy ≠ Rstop (Serr Rtype_error) ⇒
    ∃ck t' r_cml.
      evaluate (t with clock := t.clock + ck) env_cml [Seqs asss_cml] =
      (t', r_cml) ∧
      store_preserve base t.refs t'.refs ∧
      state_rel m l s' t' env_cml ∧ stmt_res_rel r_dfy r_cml
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
    \\ irule store_preserve_lupdate_local
    \\ rpt (last_assum $ irule_at Any))
  (* Array update *)
  \\ namedCases_on ‘evaluate_exp s env_dfy arr’ ["s₁ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
  \\ drule_all (cj 1 correct_from_exp)
  \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac \\ rpt strip_tac \\ gvs []
  \\ reverse $ namedCases_on ‘r’ ["arr_v", "err"] \\ gvs []
  >- (qexists ‘ck’
      \\ gvs [evaluate_def, store_preserve_all_def, store_preserve_def,
              store_lookup_def])
  \\ namedCases_on ‘evaluate_exp s₁ env_dfy idx’ ["s₂ r"] \\ gvs []
  \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
  \\ drule (cj 1 correct_from_exp)
  \\ disch_then drule
  \\ disch_then $
       qspecl_then
         [‘t₁’,
          ‘env_cml with v := nsBind " arr" cml_v env_cml.v’ ,
          ‘m’, ‘l’]
       mp_tac
  \\ ‘¬is_fresh « arr»’ by gvs [is_fresh_def, isprefix_thm]
  \\ impl_tac \\ gvs []
  >- (drule_all state_rel_env_push_not_fresh \\ gvs []
      \\ strip_tac
      \\ irule env_rel_env_change
      \\ conj_tac
      >- (gvs [env_rel_def, has_cons_def])
      \\ first_assum $ irule_at (Pos last)
      \\ rpt gen_tac \\ disch_tac
      \\ rename [‘"dfy_" ≼ n’]
      \\ ‘n ≠ " arr"’ by (Cases_on ‘n’ \\ gvs [])
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
    \\ irule store_preserve_all_weaken
    \\ irule store_preserve_all_trans
    \\ gvs [SF SFY_ss])
  (* Performing the array update *)
  \\ namedCases_on ‘update_array s₂ arr_v idx_v rhs_v’ ["", "s₃"] \\ gvs []
  \\ drule update_array_some_llookup
  \\ disch_then $
       qx_choosel_then [‘arr_len’, ‘arr_loc’, ‘idx_int’, ‘harr’] assume_tac
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
  \\ irule store_preserve_trans
  \\ irule_at (Pos hd) store_preserve_all_weaken
  \\ last_assum $ irule_at (Pos hd)
  \\ irule store_preserve_trans
  \\ irule_at (Pos hd) store_preserve_all_weaken
  \\ last_assum $ irule_at (Pos hd)
  \\ irule store_preserve_lupdate_array
  \\ gvs [store_lookup_def]
  \\ rpt (last_assum $ irule_at Any)
QED

(* TODO Why does this work *)
Triviality cml_tup_vname_neq_arr:
  cml_tup_vname n ≠ " arr"
Proof
  simp [cml_tup_vname_def]
  \\ Cases_on ‘toString n’
  \\ imp_res_tac num_to_str_imp_cons \\ simp []
  \\ strip_tac \\ fs []
QED

Triviality all_distinct_genlist_cml_tup_vname:
  ALL_DISTINCT (GENLIST (λn. cml_tup_vname n) len)
Proof
  simp [ALL_DISTINCT_GENLIST, cml_tup_vname_def, num_to_str_11]
QED

Triviality ALL_DISTINCT_pats_bindings:
  ∀xs ys.
    ALL_DISTINCT (xs ++ ys) ⇒
    ALL_DISTINCT (pats_bindings (MAP Pvar xs) ys)
Proof
  Induct_on ‘xs’ \\ gvs [pat_bindings_def]
  \\ rpt strip_tac \\ gvs [ALL_DISTINCT_APPEND]
QED

Triviality state_rel_pop_env_while:
  state_rel m l s t
    (env with v := nsBind "" v₀ (nsBind (loop_name lvl) v₁ env.v)) ⇒
  state_rel m l s t env
Proof
  rpt strip_tac
  \\ irule state_rel_env_pop_not_fresh
  \\ ‘¬is_fresh (implode (loop_name lvl))’ by
    gvs [loop_name_def, is_fresh_def, isprefix_thm]
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ irule_at (Pos hd) state_rel_env_pop_not_fresh
  \\ ‘¬is_fresh «»’ by gvs [is_fresh_def, isprefix_thm]
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
  \\ first_assum $ irule_at Any
QED

(* TODO Similar to _some_fun_name: Is there a better way than writing them
   separately? *)
Triviality get_member_some_met_name:
  get_member n p = SOME (Method n' ins reqs ens rds decrs outs mods body) ⇒
  n' = n
Proof
  namedCases_on ‘p’ ["members"] \\ Induct_on ‘members’
  \\ gvs [get_member_def, get_member_aux_def]
  \\ qx_gen_tac ‘member’ \\ rpt strip_tac
  \\ namedCases_on ‘member’ ["mem_n _ _ _ _ _ _ _ _", "mem_n _ _ _ _ _ _"]
  \\ Cases_on ‘mem_n = n’ \\ gvs []
QED

Triviality evaluate_cml_new_refs:
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
Triviality NOT_MEM_FLOOKUP_UPDATE_LIST:
  ¬MEM x (MAP FST l) ⇒ FLOOKUP (m |++ l) x = FLOOKUP m x
Proof
  rpt strip_tac
  \\ gvs [flookup_fupdate_list, CaseEq "option"]
  \\ disj1_tac
  \\ gvs [ALOOKUP_NONE, MAP_REVERSE]
QED

Triviality MEM_explode_MAP[simp]:
  ∀xs x. MEM (explode x) (MAP explode xs) ⇔ MEM x xs
Proof
  Induct \\ simp []
QED

Triviality locals_rel_decl_uninit_vars:
  locals_rel m l s_locals t_refs env_v ∧
  ALL_DISTINCT vars ∧
  (∀v. MEM v vars ⇒ ¬MEM v (MAP FST s_locals)) ⇒
  locals_rel m (l |++ enumerate_from (LENGTH t_refs) vars)
    ((REVERSE (ZIP (vars, REPLICATE (LENGTH vars) NONE))) ++ s_locals)
    (t_refs ++ REPLICATE (LENGTH vars) (Refv init))
    (add_refs_to_env env_v (MAP explode vars) (LENGTH t_refs))
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

Triviality locals_rel_decl_uninit_var:
  locals_rel m l s.locals t.refs env_v ∧
  ¬MEM n (MAP FST s.locals) ⇒
  locals_rel m (l |+ (n,LENGTH t.refs)) ((n,NONE)::s.locals)
    (t.refs ++ [Refv (Litv (IntLit 0))])
    (nsBind (explode n) (Loc T (LENGTH t.refs)) env_v)
Proof
  rpt strip_tac
  \\ drule locals_rel_decl_uninit_vars
  \\ disch_then $ qspecl_then [‘[n]’, ‘Litv (IntLit 0)’] mp_tac
  \\ gvs [enumerate_from_def, add_refs_to_env_def,
          FUPDATE_EQ_FUPDATE_LIST]
  \\ pure_rewrite_tac [ONE, REPLICATE] \\ gvs []
QED

Triviality locals_rel_mk_locals_map_outs:
  ALL_DISTINCT (MAP FST outs) ⇒
  locals_rel m (mk_locals_map (MAP FST outs) (LENGTH t_refs))
    (REVERSE (ZIP (MAP FST outs, REPLICATE (LENGTH outs) NONE)))
    (t_refs ++ REPLICATE (LENGTH outs) (Refv (Litv (IntLit 0))))
    (add_refs_to_env env_v (MAP (explode ∘ FST) outs) (LENGTH t_refs))
Proof
  gvs [mk_locals_map_def]
  \\ ‘locals_rel m FEMPTY [] t_refs env_v’ by gvs [locals_rel_def]
  \\ drule locals_rel_decl_uninit_vars \\ gvs []
  \\ disch_then $ qspecl_then [‘MAP FST outs’, ‘Litv (IntLit 0)’] mp_tac
  \\ gvs [MAP_MAP_o]
QED

Triviality locals_rel_mk_locals_map_ins:
  ALL_DISTINCT (MAP FST ins) ∧
  LIST_REL (val_rel m) in_vs in_vs_cml ∧
  LENGTH in_vs = LENGTH ins ⇒
  locals_rel m (mk_locals_map (MAP FST ins) (LENGTH t_refs))
    (REVERSE (ZIP (MAP FST ins, MAP SOME in_vs)))
    (t_refs ++ MAP Refv in_vs_cml)
    (add_refs_to_env env_v (MAP (explode ∘ FST) ins) (LENGTH t_refs))
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

Triviality locals_mk_locals_map_ins_outs:
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
       (add_refs_to_env env.v (MAP (explode ∘ FST) ins) (LENGTH t.refs))
       (MAP (explode ∘ FST) outs)
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

Triviality locals_rel_submap:
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

Triviality evaluate_cml_read_var:
  read_local s.locals var = SOME val ∧
  state_rel m l s (t: 'ffi cml_state) env ∧
  is_fresh var ⇒
  ∃val_cml.
    evaluate t env [cml_read_var (explode var)] =
    (t, Rval [val_cml]) ∧ val_rel m val val_cml
Proof
  rpt strip_tac
  \\ drule_all read_local_some_imp
  \\ rpt strip_tac
  \\ gvs [evaluate_def, cml_read_var_def, do_app_def]
QED

Triviality evaluate_map_cml_read_var:
  ∀s vars vals m l t env.
    OPT_MMAP (read_local s.locals) vars = SOME vals ∧
    state_rel m l s (t: 'ffi cml_state) env ∧
    EVERY (λv. is_fresh v) vars ⇒
    ∃val_cmls.
      evaluate t env (REVERSE (MAP (cml_read_var ∘ explode) vars)) =
      (t, Rval val_cmls) ∧ LIST_REL (val_rel m) vals (REVERSE val_cmls)
Proof
  Induct_on ‘vars’ \\ gvs []
  \\ rpt strip_tac
  \\ drule_all read_local_some_imp \\ rpt strip_tac
  \\ last_x_assum $ drule_all \\ rpt strip_tac \\ gvs []
  \\ gvs [evaluate_append, cml_read_var_def, evaluate_def, do_app_def]
QED

(* TODO Merge with state_rel_restore_caller *)
Triviality state_rel_restore_caller1:
  state_rel m l s (t: 'ffi cml_state) env ∧
  state_rel m' l' s' (t': 'ffi cml_state) env' ∧
  store_preserve_all t.refs t'.refs ∧
  m ⊑ m' ⇒
  state_rel m' l (restore_caller s' s) t' env
Proof
  rpt strip_tac
  \\ gvs [restore_caller_def, state_rel_def]
  \\ irule store_preserve_all_locals_rel
  \\ last_x_assum $ irule_at Any \\ gvs []
  \\ irule locals_rel_submap \\ gvs []
  \\ first_assum $ irule_at (Pos hd) \\ gvs []
QED

Triviality OPT_MMAP_SOME_LENGTH:
  ∀f xs ys. OPT_MMAP f xs = SOME ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct_on ‘xs’ \\ gvs []
  \\ rpt strip_tac \\ gvs []
  \\ last_assum drule \\ gvs []
QED

Triviality GENLIST_lambda_MAP:
  GENLIST (λx. f (g x)) len = MAP f (GENLIST (λx. g x) len)
Proof
  gvs [MAP_GENLIST, o_DEF]
QED

Triviality GENLIST_MAP_Pvar:
  GENLIST (λn. Pvar (cml_tup_vname n)) len =
  MAP Pvar (GENLIST (λn. cml_tup_vname n) len)
Proof
  gvs [GENLIST_lambda_MAP]
QED

Triviality evaluate_map_var_short:
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

Triviality MEM_explode_implode:
  ∀xs x. MEM (implode x) xs ⇔ MEM x (MAP explode xs)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ rename [‘implode _ = y’]
  \\ ‘implode x = y ⇔ x = explode y’ by (eq_tac \\ rpt strip_tac \\ gvs [])
  \\ simp []
QED

Triviality evaluate_Apps_with_clock:
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

Triviality nsappend_alist_to_ns_concat:
  ∀xs ys ns.
    nsAppend (alist_to_ns (xs ++ ys)) ns =
    nsAppend (alist_to_ns xs) (nsAppend (alist_to_ns ys) ns)
Proof
  gvs []
QED

Triviality is_fresh_cml_tup_vname_neq:
  is_fresh n ⇒ explode n ≠ cml_tup_vname i
Proof
  rpt strip_tac \\ gvs [is_fresh_def, isprefix_thm, cml_tup_vname_def]
QED

Triviality dfy_pfx_cml_tup_vname_neq:
  "dfy_" ≼ n ⇒ n ≠ cml_tup_vname i
Proof
  rpt strip_tac \\ gvs [cml_tup_vname_def]
QED

Triviality is_fresh_neq_cml_tup_vname:
  is_fresh n ⇒ explode n ≠ cml_tup_vname i
Proof
  Cases_on ‘explode n’
  \\ simp [cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Triviality is_fresh_not_mem_genlist:
  ∀n. is_fresh n ⇒ ¬MEM (explode n) (GENLIST (λn. cml_tup_vname n) len)
Proof
  rpt strip_tac
  \\ gvs [MEM_GENLIST, cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Triviality dfy_pfx_not_mem_genlist:
  ∀n. "dfy_" ≼ n ⇒ ¬MEM n (GENLIST (λn. cml_tup_vname n) len)
Proof
  rpt strip_tac
  \\ gvs [MEM_GENLIST, cml_tup_vname_def, is_fresh_def, isprefix_thm]
QED

Triviality MEM_LAST:
  xs ≠ [] ⇒ MEM (LAST xs) xs
Proof
  Induct_on ‘xs’ using SNOC_INDUCT \\ gvs []
QED

Theorem correct_from_stmt:
  ∀s env_dfy stmt_dfy s' r_dfy lvl (t: 'ffi cml_state) env_cml e_cml m l base.
    evaluate_stmt s env_dfy stmt_dfy = (s', r_dfy) ∧
    from_stmt stmt_dfy lvl = INR e_cml ∧ state_rel m l s t env_cml ∧
    base_at_most base t.refs l ∧
    env_rel env_dfy env_cml ∧ is_fresh_stmt stmt_dfy ∧
    no_shadow (set (MAP FST s.locals)) stmt_dfy ∧
    r_dfy ≠ Rstop (Serr Rtype_error)
    ⇒ ∃ck (t': 'ffi cml_state) m' r_cml.
        evaluate$evaluate (t with clock := t.clock + ck) env_cml [e_cml] =
        (t', r_cml) ∧
        store_preserve base t.refs t'.refs ∧ state_rel m' l s' t' env_cml ∧
        m ⊑ m' ∧ stmt_res_rel r_dfy r_cml
Proof
  ho_match_mp_tac evaluate_stmt_ind
  \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, evaluate_def, do_con_check_def,
         build_conv_def]
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Assert e’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, evaluate_def, do_con_check_def,
         build_conv_def]
    \\ ‘env_dfy.is_running’ by gvs [env_rel_def] \\ gvs []
    \\ qexistsl [‘0’, ‘m’] \\ gvs [])
  >~ [‘Then stmt₁ stmt₂’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_stmt s env_dfy stmt₁’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
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
    \\ irule_at Any store_preserve_trans
    \\ qexistsl [‘t₁.refs’, ‘m₂’] \\ gvs []
    \\ irule_at Any SUBMAP_TRANS \\ gvs [SF SFY_ss])
  >~ [‘If tst thn els’] >-
   (gvs [evaluate_stmt_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ namedCases_on ‘evaluate_exp s env_dfy tst’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (Cases_on ‘r’ \\ gvs []) \\ gvs []
    \\ drule_all (cj 1 correct_from_exp)
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ ‘store_preserve base t.refs t₁.refs’ by
      gvs [store_preserve_all_def, store_preserve_def, base_at_most_def]
    \\ gvs [evaluate_def]
    \\ reverse $ namedCases_on ‘r’ ["tst_v", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs [] \\ first_assum $ irule_at (Pos hd) \\ gvs [])
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
    \\ irule_at Any store_preserve_trans
    \\ qexistsl [‘t₁.refs’, ‘m₁’] \\ gvs [])
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
               nsBind (explode n) (Loc T (LENGTH t.refs)) env_cml.v’,
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
        \\ conj_tac >- (gvs [env_rel_def, has_cons_def])
        \\ first_assum $ irule_at (Pos last)
        \\ rpt strip_tac
        \\ rename [‘"dfy_" ≼ n'’]
        \\ ‘n' ≠ (explode n)’ by
          (Cases_on ‘explode n’
           \\ Cases_on ‘n'’
           \\ gvs [is_fresh_def, isprefix_thm])
        \\ simp [])
    \\ disch_then $ qx_choosel_then [‘ck’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qexists ‘ck’
    \\ gvs [cml_new_refs_def]
    \\ gvs [evaluate_def, do_app_def, store_alloc_def]
    \\ drule store_preserve_decat \\ rpt strip_tac \\ gvs []
    \\ qexists ‘m₁’ \\ gvs []
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
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
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
      \\ ‘¬is_fresh (implode (cml_tup_vname 0))’ by
        gvs [is_fresh_def, implode_def, cml_tup_vname_def, isprefix_thm]
      \\ drule_all state_rel_env_push_not_fresh \\ gvs []
      \\ disch_then $ qspec_then ‘rhs_v_cml’ assume_tac
      \\ drule evaluate_assign_values \\ gvs []
      \\ disch_then $ drule_at $ Pos (el 2) \\ gvs []
      \\ disch_then $ qspec_then ‘[cml_tup_vname 0]’ mp_tac \\ gvs []
      \\ disch_then $ qspec_then ‘base’ mp_tac \\ gvs []
      \\ ‘cml_tup_vname 0 ≠ " arr"’ by (gvs [cml_tup_vname_neq_arr]) \\ gvs []
      \\ impl_tac >-
       (gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]
        \\ irule env_rel_env_change
        \\ conj_tac >- (gvs [env_rel_def, has_cons_def])
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
      \\ last_assum $ irule_at (Pos hd) \\ gvs [])
    \\ imp_res_tac result_mmap_len
    \\ gvs [Stuple_Tuple, evaluate_def, do_con_check_def, build_conv_def]
    \\ reverse $ namedCases_on ‘r’ ["rhs_vs", "err"] \\ gvs []
    >- (qexists ‘ck’ \\ gvs []
        \\ first_x_assum $ irule_at Any
        \\ gvs [store_preserve_all_def, store_preserve_def, base_at_most_def])
    \\ qmatch_asmsub_abbrev_tac ‘MAP (Var ∘ Short) names’
    \\ ‘EVERY (λn. " arr" ≠ n) names’ by
      gvs [Abbr ‘names’, EVERY_GENLIST, cml_tup_vname_neq_arr]
    \\ ‘LENGTH names = LENGTH cml_vs’ by
      (imp_res_tac evaluate_length \\ simp [Abbr ‘names’])
    \\ ‘EVERY (λn. ¬("dfy_" ≼ n)) names’ by
      (simp [Abbr ‘names’, EVERY_GENLIST, cml_tup_vname_def])
    \\ ‘∀n. is_fresh n ⇒ ¬MEM (explode n) names’ by
      (simp [Abbr ‘names’, MAP_ZIP, is_fresh_not_mem_genlist])
    \\ qabbrev_tac
       ‘env₁ =
          env_cml with v :=
            nsAppend (alist_to_ns (ZIP (names,cml_vs))) env_cml.v’
    \\ ‘env_rel env_dfy env₁’ by
      (simp [Abbr ‘env₁’]
       \\ irule env_rel_env_change
       \\ conj_tac >- (gvs [env_rel_def, has_cons_def])
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
    \\ irule_at Any store_preserve_trans \\ gvs []
    \\ irule_at (Pos hd) store_preserve_all_weaken
    \\ first_x_assum $ irule_at (Pos hd) \\ gvs []
    \\ first_x_assum $ irule_at Any
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
        \\ rpt (last_assum $ irule_at Any) \\ gvs [])
    \\ namedCases_on ‘evaluate_exp (dec_clock s) env_dfy grd’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs [])
    (* TODO Better way to do this than writing this big block? *)
    \\ qabbrev_tac
       ‘env_cml₁ =
          env_cml with v :=
            nsBind "" (Conv NONE [])
              (nsBind (loop_name lvl)
                 (Recclosure env_cml
                    [(loop_name lvl,"",
                      If cml_grd
                        (Let NONE cml_body
                           (App Opapp
                              [Var (Short (loop_name lvl)); Unit]))
                        Unit)] (loop_name lvl)) env_cml.v)’
    \\ ‘env_rel env_dfy env_cml₁’ by
      (irule env_rel_env_change
       \\ strip_tac
       >- (gvs [env_rel_def, has_cons_def, Abbr ‘env_cml₁’])
       \\ first_x_assum $ irule_at (Pos last)
       \\ rpt strip_tac
       \\ simp [Abbr ‘env_cml₁’]
       \\ DEP_REWRITE_TAC [neq_nslookup_nsbind]
       \\ rpt strip_tac
       \\ gvs [loop_name_def])
    \\ drule (cj 1 correct_from_exp) \\ gvs []
    \\ disch_then $ qspecl_then [‘dec_clock t’, ‘env_cml₁’, ‘m’, ‘l’] mp_tac
    \\ ‘∀n. is_fresh n ⇒ explode n ≠ ""’ by
      (rpt strip_tac
       \\ Cases_on ‘explode n’ \\ gvs [is_fresh_def, isprefix_thm])
    \\ ‘∀n lvl. is_fresh n ⇒ explode n ≠ loop_name lvl’ by
      (ntac 2 (strip_tac)
       \\ Cases_on ‘explode n’
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
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
    \\ Cases_on ‘grd_v = BoolV F’ \\ gvs []
    >- (qexists ‘ck’
        \\ gvs [evaluateTheory.dec_clock_def]
        \\ gvs [do_if_def, evaluate_def, do_con_check_def, build_conv_def]
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ gvs [Abbr ‘env_cml₁’]
        \\ irule_at (Pos hd) state_rel_pop_env_while
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
    \\ Cases_on ‘grd_v = BoolV T’ \\ gvs []
    \\ namedCases_on ‘evaluate_stmt s₁ env_dfy body’ ["s₂ r"] \\ gvs []
    \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (spose_not_then assume_tac \\ gvs [])
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
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
    \\ gvs [STOP_def, from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ last_x_assum $ qspecl_then [‘lvl’, ‘t₂’, ‘env_cml’] mp_tac
    \\ gvs []
    \\ disch_then $ qspecl_then [‘m₁’, ‘l’, ‘base’] mp_tac \\ gvs []
    \\ impl_tac
    >- (gvs [dec_clock_def, evaluateTheory.dec_clock_def, state_rel_def]
        \\ gvs [base_at_most_def, store_preserve_all_def, store_preserve_def]
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
    \\ disch_then kall_tac
    \\ irule_at (Pos hd) store_preserve_trans
    \\ irule_at (Pos hd) store_preserve_trans
    \\ irule_at (Pos hd) store_preserve_all_weaken
    \\ gvs [evaluateTheory.dec_clock_def]
    \\ rpt (last_assum $ irule_at (Pos hd))
    \\ irule SUBMAP_TRANS
    \\ rpt (last_assum $ irule_at (Pos hd)))
  >~ [‘Print e t’] >-
   (cheat)
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
    \\ qabbrev_tac ‘mname = "dfy_" ++ (explode name)’ \\ gvs []
    (* "Simulate" evaluating arguments *)
    \\ gvs [from_stmt_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [cml_fapp_def, mk_id_def]
    \\ rename [‘map_from_exp _ = INR cml_args’]
    \\ imp_res_tac map_from_exp_len \\ gvs []
    \\ namedCases_on ‘evaluate_exps s env_dfy args’ ["s₁ r"] \\ gvs []
    \\ ‘r ≠ Rerr Rtype_error’ by (spose_not_then assume_tac \\ gvs []) \\ gvs []
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
    \\ ‘∀n. "dfy_" ≼ n ⇒ ¬MEM n (MAP (explode ∘ FST) outs)’ by
      (rpt strip_tac
       \\ ‘is_fresh (implode n)’ by
         (fs [EVERY_MEM]
          \\ first_assum irule
          \\ fs [GSYM MAP_MAP_o]
          \\ first_x_assum $ qspec_then ‘implode n’ mp_tac
          \\ gvs [MEM_explode_implode])
       \\ gvs [is_fresh_def, isprefix_thm]
       \\ Cases_on ‘n’ \\ gvs [])
    \\‘∀n. "dfy_" ≼ n ⇒ ¬MEM n (MAP (explode ∘ FST) ins)’ by
      (rpt strip_tac
       \\ ‘is_fresh (implode n)’ by
         (fs [EVERY_MEM]
          \\ last_assum irule
          \\ fs [GSYM MAP_MAP_o]
          \\ first_x_assum $ qspec_then ‘implode n’ mp_tac
          \\ gvs [MEM_explode_implode])
       \\ gvs [is_fresh_def, isprefix_thm]
       \\ Cases_on ‘n’ \\ gvs [])
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
      \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (spose_not_then assume_tac \\ gvs [])
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
          \\ conj_tac
          >- (gvs [has_cons_def, Abbr ‘call_env₁’, Abbr ‘call_env’])
          \\ ntac 3 strip_tac
          \\ first_x_assum drule
          \\ strip_tac
          \\ simp [Abbr ‘call_env₁’]
          \\ DEP_REWRITE_TAC [not_mem_nslookup_add_refs_to_env] \\ simp []
          \\ simp [Abbr ‘call_env’]
          \\ drule_all nslookup_build_rec_env_reclos
          \\ disch_then $ qspec_then ‘env.v’ mp_tac
          \\ rpt strip_tac
          \\ first_assum $ irule_at (Pos last) \\ gvs [])
        >- (gvs [dec_clock_def, Abbr ‘dfy_locals’, REVERSE_ZIP, MAP_ZIP]))
      \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’, ‘m₁’] mp_tac
      \\ rpt strip_tac \\ gvs []
      \\ gvs [Abbr ‘call_t’]
      (* Will be useful for finishing up proofs *)
      \\ ‘store_preserve_all t.refs t₂.refs’ by
        (gvs [store_preserve_all_def]
         \\ irule_at Any store_preserve_decat
         \\ first_assum $ irule_at (Pos hd))
      \\ qrefine ‘ck₂ + ck₁’
      \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
      \\ reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
      >-
       (qexists ‘0’
        \\ Cases_on ‘err’ \\ gvs []
        (* Timed out *)
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ gvs [state_rel_def, restore_caller_def]
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ irule store_preserve_all_locals_rel \\ gvs []
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ irule locals_rel_submap
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
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
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        \\ gvs [state_rel_def, restore_caller_def]
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ irule store_preserve_all_locals_rel \\ gvs []
        \\ first_assum $ irule_at (Pos hd) \\ gvs []
        \\ irule locals_rel_submap
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
      \\ Cases_on ‘LENGTH outs = 1’ \\ gvs []
      >- (* Assigning a single value (no tuple used) *)
       (gvs [LENGTH_EQ_1, Stuple_def, Pstuple_def]
        \\ gvs [par_assign_def, oneline bind_def, CaseEq "sum"]
        \\ rename [‘explode (FST out)’]
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
           (irule state_rel_restore_caller1 \\ gvs []
            \\ first_assum $ irule_at (Pos hd) \\ gvs []
            \\ qexists ‘t with clock := ck + t.clock’ \\ gvs []
            \\ first_assum $ irule_at (Pos last) \\ gvs []
            \\ irule state_rel_env_change
            \\ first_assum $ irule_at (Pos last)
            \\ rpt strip_tac
            \\ drule is_fresh_cml_tup_vname_neq \\ simp [])
          >- (* env_rel *)
           (irule env_rel_env_change
            \\ strip_tac
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
        \\ irule_at (Pos hd) store_preserve_trans
        \\ irule_at (Pos hd) store_preserve_all_weaken
        \\ ntac 2 (first_assum $ irule_at (Pos hd))
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
      \\ imp_res_tac OPT_MMAP_SOME_LENGTH \\ gvs []
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
          \\ strip_tac
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
      \\ first_assum $ irule_at (Pos last) \\ gvs []
      \\ irule_at (Pos hd) store_preserve_trans
      \\ irule_at (Pos hd) store_preserve_all_weaken
      \\ ntac 2 (first_assum $ irule_at (Pos hd))
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
    \\ qabbrev_tac ‘params = MAP (explode ∘ FST) ins’
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
        \\ qexists ‘m’ \\ gvs [restore_caller_def, state_rel_def])
    (* Dafny ran the call *)
    \\ ‘cml_param = HD (REVERSE params)’ by
      (Cases_on ‘REVERSE params’ \\ gvs [cml_fun_def])
    (* Start chipping away at the compilation of a method *)
    \\ qmatch_goalsub_abbrev_tac ‘evaluate _ call_env₁’
    \\ ‘nsLookup call_env₁.c (mk_id [] "Return") = SOME (0, ret_stamp)’
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
    \\ ‘r ≠ Rstop (Serr Rtype_error)’ by (spose_not_then assume_tac \\ gvs [])
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
      \\ rpt strip_tac
      >- (* array_rel *)
       (gvs [Abbr ‘call_refs’] \\ ntac 2 (irule array_rel_append) \\ gvs [])
      >- (* locals_rel *)
       (gvs [Abbr ‘params’, Abbr ‘call_refs’, Abbr ‘call_env₂’]
        \\ irule locals_mk_locals_map_ins_outs \\ gvs [])
      >- (* base_at_most *)
       (gvs [base_at_most_def, Abbr ‘call_refs’] \\ rpt strip_tac
        \\ drule (cj 1 FRANGE_mk_locals_map) \\ gvs [])
      (* env_rel *)
      \\ gvs [env_rel_def]
      \\ conj_tac
      >- (gvs [Abbr ‘call_env₂’, Abbr ‘call_env₁’, Abbr ‘call_env’,
               has_cons_def])
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
      \\ ‘LENGTH (FRONT cml_vs) = LENGTH args'’ by
        (imp_res_tac evaluate_length
         \\ ‘cml_vs ≠ []’ by (spose_not_then assume_tac \\ gvs [])
         \\ imp_res_tac LIST_REL_LENGTH
         \\ gvs [LENGTH_FRONT])
      \\ simp [MAP_ZIP]
      \\ DEP_REWRITE_TAC [NOT_MEM_TL] \\ simp []
      \\ DEP_REWRITE_TAC [neq_nslookup_nsbind] \\ simp []
      \\ strip_tac
      >- (‘MEM (HD (REVERSE params)) params’ by
            (Cases_on ‘(REVERSE params) = []’ \\ gvs []
             \\ DEP_REWRITE_TAC [HD_REVERSE, MEM_LAST] \\ simp [])
          \\ ‘is_fresh (implode (HD (REVERSE params)))’ by
            (fs [EVERY_MEM]
             \\ last_assum irule
             \\ fs [GSYM MAP_MAP_o]
             \\ first_x_assum $
                  qspec_then ‘(implode (HD (REVERSE params)))’ mp_tac
             \\ gvs [MEM_explode_implode])
          \\ drule is_fresh_not_dfy_pfx \\ simp [])
      \\ gvs [])
    \\ disch_then $ qx_choosel_then [‘ck₁’, ‘t₂’, ‘m₁’] mp_tac
    \\ rpt strip_tac \\ gvs []
    \\ qrefine ‘ck₁ + ck₂’ \\ gvs []
    \\ namedCases_on ‘r’ ["", "stp"] \\ gvs []
    \\ reverse $ namedCases_on ‘stp’ ["", "err"] \\ gvs []
    >- (Cases_on ‘err’ \\ gvs []
        (* Evaluating the body timed out *)
        \\ qexists ‘0’ \\ gvs []
        \\ gvs [evaluateTheory.dec_clock_def, ADD1, Abbr ‘call_refs’]
        \\ ‘store_preserve_all t₁.refs t₂.refs’ by
          (ntac 2 $ drule_then assume_tac store_preserve_decat
           \\ gvs [store_preserve_all_def])
        (* store_preserve *)
        \\ irule_at (Pos hd) store_preserve_trans
        \\ irule_at (Pos hd) store_preserve_all_weaken
        \\ last_assum $ irule_at (Pos hd)
        \\ irule_at (Pos hd) store_preserve_all_weaken \\ gvs []
        (* state_rel *)
        \\ irule_at (Pos hd) state_rel_restore_caller1
        \\ last_assum $ irule_at (Pos hd) \\ gvs []
        \\ first_assum $ irule_at (Pos hd) \\ gvs [])
    (* Dafny: read_locals *)
    \\ namedCases_on ‘OPT_MMAP (read_local s₂.locals) (MAP FST outs)’
         ["", "out_vs"]
    \\ gvs []
    \\ ‘LENGTH lhss = LENGTH out_vs’ by (spose_not_then assume_tac \\ gvs [])
    \\ gvs []
    \\ gvs [par_assign_def, oneline bind_def, CaseEq "sum"]
    \\ gvs [evaluateTheory.dec_clock_def, ADD1]
    \\ drule evaluate_add_to_clock \\ gvs []
    \\ disch_then kall_tac
    \\ gvs [can_pmatch_all_def, pmatch_def, ret_stamp_def, same_type_def,
            same_ctor_def, pat_bindings_def]
    \\ ‘store_preserve_all t₁.refs t₂.refs’ by
      (gvs [store_preserve_all_def, Abbr ‘call_refs’]
       \\ ntac 2 $ irule_at (Pos hd) store_preserve_decat
       \\ first_assum $ irule_at (Pos hd))
    \\ Cases_on ‘LENGTH outs = 1’ \\ gvs []
    >- (* Method returns value directly, instead of a tuple *)
     (gvs [LENGTH_EQ_1]
      \\ rename [‘explode (FST out)’]
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
            \\ strip_tac
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
      \\ irule_at (Pos hd) store_preserve_trans
      \\ irule_at (Pos hd) store_preserve_all_weaken
      \\ first_assum $ irule_at (Pos hd)
      \\ irule_at (Pos hd) store_preserve_trans
      \\ irule_at (Pos hd) store_preserve_all_weaken
      \\ ntac 2 (first_assum $ irule_at (Pos hd))
      \\ gvs [state_rel_def]
      \\ first_assum $ irule_at (Pos hd) \\ gvs []
      \\ irule locals_rel_env_change
      \\ first_assum $ irule_at (Pos last)
      \\ rpt gen_tac \\ disch_tac
      \\ simp [is_fresh_neq_cml_tup_vname])
    \\ DEP_REWRITE_TAC [Stuple_Tuple] \\ gvs []
    \\ imp_res_tac OPT_MMAP_SOME_LENGTH \\ gvs []
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
        \\ conj_tac
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
    \\ first_assum $ irule_at (Pos last) \\ gvs []
    \\ irule_at (Pos hd) store_preserve_trans
    \\ irule_at (Pos hd) store_preserve_all_weaken
    \\ irule_at (Pos hd) store_preserve_all_trans
    \\ ntac 3 (first_assum $ irule_at (Pos hd))
    \\ gvs [state_rel_def]
    \\ irule locals_rel_env_change
    \\ first_assum $ irule_at (Pos last)
    \\ rpt gen_tac \\ disch_tac
    \\ simp [Abbr ‘ass_env₁’]
    \\ DEP_REWRITE_TAC [not_mem_nslookup_nsappend_alist]
    \\ simp [MAP_ZIP, is_fresh_not_mem_genlist])
QED

Triviality from_member_decl_name:
  from_member_decl member = INR cml_f ⇒
  (λ(x,y,z). x) $ cml_f = "dfy_" ++ explode (member_name member)
Proof
  rpt strip_tac
  \\ gvs [from_member_decl_def, oneline bind_def, set_up_cml_fun_def,
          AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality map_from_member_decl_name:
  ∀members cml_fs.
    result_mmap from_member_decl members = INR cml_fs ⇒
    MAP (λ(x,y,z). x) cml_fs =
    MAP (STRCAT "dfy_" ∘ explode ∘ member_name) members
Proof
  Induct \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ imp_res_tac from_member_decl_name \\ gvs []
QED

Triviality MEM_dfy_MAP:
  ∀xs x. MEM ("dfy_" ++ x) (MAP (λx. "dfy_" ++ x) xs) = MEM x xs
Proof
  Induct \\ gvs []
QED

Triviality ALL_DISTINCT_member_name:
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
       [‘MAP (explode ∘ member_name) members’, ‘explode (member_name member)’]
       assume_tac MEM_dfy_MAP
  \\ gvs [MAP_MAP_o, o_DEF]
  \\ simp [GSYM o_DEF, GSYM MAP_MAP_o]
QED

(* Proving that a generated CakeML expression e satisfies
   every_exp (one_con_check env_c) e *)

Triviality Apps_one_con_check:
  ∀xs env_c f.
    every_exp (one_con_check env_c) f ∧
    EVERY (every_exp (one_con_check env_c)) xs ⇒
    every_exp (one_con_check env_c) (Apps f xs)
Proof
  Induct \\ gvs [Apps_def]
QED

Triviality Funs_one_con_check:
  ∀xs env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (Funs xs body)
Proof
  Induct \\ gvs [Funs_def]
QED

Triviality from_exp_one_con_check:
  (∀body cml_body (env: cml_env).
     from_exp body = INR cml_body ∧
     has_cons env ⇒
     every_exp (one_con_check env.c) cml_body) ∧
  (∀bodys cml_bodys (env: cml_env).
     map_from_exp bodys = INR cml_bodys ∧
     has_cons env ⇒
     EVERY (every_exp (one_con_check env.c)) cml_bodys)
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

Triviality cml_new_refs_one_con_check:
  ∀names env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (cml_new_refs names body)
Proof
  Induct \\ gvs [cml_new_refs_def]
QED

Triviality from_rhs_exp_one_con_check:
  ∀rhs cml_rhs (env: cml_env).
    from_rhs_exp rhs = INR cml_rhs ∧
    has_cons env ⇒
    every_exp (one_con_check env.c) cml_rhs
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

Triviality map_from_rhs_exp_one_con_check:
  ∀rhss cml_rhss (env: cml_env).
    result_mmap from_rhs_exp rhss = INR cml_rhss ∧
    has_cons env ⇒
    EVERY (λe. every_exp (one_con_check env.c) e) cml_rhss
Proof
  Induct
  \\ simp [result_mmap_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac from_rhs_exp_one_con_check \\ gvs []
QED

Triviality Seqs_one_con_check:
  ∀es env.
    EVERY (λe. every_exp (one_con_check env.c) e) es ⇒
    every_exp (one_con_check env.c) (Seqs es)
Proof
  Induct \\ gvs [Seqs_def, do_con_check_def]
QED

Triviality assign_single_one_con_check:
  assign_single lhs (Var (Short n)) = INR ass ∧
  has_cons (env: cml_env) ⇒
  every_exp (one_con_check env.c) ass
Proof
  Cases_on ‘lhs’
  \\ simp [assign_single_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac (cj 1 from_exp_one_con_check)
  \\ gvs [cml_get_arr_data_def, cml_tup_select_def, cml_tup_case_def]
QED

Triviality map_assign_single_one_con_check:
  ∀lhss ns ass (env: cml_env).
    result_mmap2 assign_single lhss (MAP (Var ∘ Short) ns) = INR ass ∧
    has_cons env ⇒
    EVERY (λe. every_exp (one_con_check env.c) e) ass
Proof
  Induct \\ Cases_on ‘ns’
  \\ simp [result_mmap2_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ imp_res_tac assign_single_one_con_check
  \\ res_tac \\ gvs []
QED

Triviality Stuple_one_con_check:
  EVERY (λe. every_exp (one_con_check env_c) e) es ⇒
  every_exp (one_con_check env_c) (Stuple es)
Proof
  Cases_on ‘LENGTH es = 1’
  >- (gvs [LENGTH_EQ_1, Stuple_def])
  \\ DEP_REWRITE_TAC [Stuple_Tuple]
  \\ simp [do_con_check_def]
QED

Triviality par_assign_one_con_check:
  par_assign lhss cml_rhss = INR cml_body ∧
  EVERY (λe. every_exp (one_con_check env.c) e) cml_rhss ∧
  has_cons (env: cml_env) ⇒
  every_exp (one_con_check env.c) cml_body
Proof
  simp [par_assign_def, oneline bind_def, CaseEq "sum"] \\ rpt strip_tac
  \\ Cases_on ‘LENGTH lhss = LENGTH cml_rhss’ \\ gvs []
  \\ DEP_REWRITE_TAC [Seqs_one_con_check, Stuple_one_con_check]
  \\ imp_res_tac map_assign_single_one_con_check \\ gvs []
QED

Triviality to_string_one_con_check:
  to_string cml_e t = INR cml_str ∧
  every_exp (one_con_check env_c) cml_e ⇒
  every_exp (one_con_check env_c) cml_str
Proof
  Cases_on ‘t’ \\ simp [to_string_def] \\ rpt strip_tac
  \\ gvs [cml_fapp_def, cml_apps_def, Apps_def]
QED

Triviality from_stmt_one_con_check:
  ∀body lvl cml_body (env: cml_env).
    from_stmt body lvl = INR cml_body ∧
    has_cons env ⇒
    every_exp (one_con_check env.c) cml_body
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

Triviality set_up_in_refs_one_con_check:
  ∀names env_c body.
    every_exp (one_con_check env_c) body ⇒
    every_exp (one_con_check env_c) (set_up_in_refs names body)
Proof
  Induct \\ gvs [set_up_in_refs_def]
QED

Triviality set_up_cml_fun_one_con_check:
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

Triviality MAP_cml_read_var_one_con_check:
  ∀ns env_c e.
    EVERY (λe. every_exp (one_con_check env_c) e) (MAP cml_read_var ns)
Proof
  Induct \\ gvs [one_con_check_def, cml_read_var_def]
QED

Triviality from_member_decl_one_con_check:
  from_member_decl member = INR cml_f ∧
  has_cons (env: cml_env) ⇒
  (λ(f,n,e). every_exp (one_con_check env.c) e) cml_f
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

Triviality map_from_member_decl_one_con_check:
  ∀members cml_fs env.
    result_mmap from_member_decl members = INR cml_fs ∧
    has_cons (env: cml_env) ⇒
    EVERY (λ(f,n,e). every_exp (one_con_check env.c) e) cml_fs
Proof
  Induct
  \\ simp [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ rpt strip_tac
  \\ imp_res_tac from_member_decl_one_con_check
  \\ res_tac \\ gvs []
QED

Definition has_main_def:
  has_main prog ⇔
    (∃name reqs ens reads decrs mods body.
       get_member «Main» prog =
       SOME (Method name [] reqs ens reads decrs [] mods body))
End

Definition valid_prog_def:
  valid_prog (Program members) ⇔
    has_main (Program members) ∧
    EVERY is_fresh_member members ∧
    EVERY no_shadow_method members
End

Triviality find_recfun_main:
  ∀members reqs ens rds decrs mod body cml_funs.
    get_member_aux «Main» members =
      SOME (Method «Main» [] reqs ens rds decrs [] mod body) ∧
    result_mmap from_member_decl members = INR cml_funs ∧
    EVERY is_fresh_member members ∧
    EVERY no_shadow_method members ⇒
    ∃cml_param cml_body.
      from_stmt body 0 = INR cml_body ∧
      is_fresh_stmt body ∧
      no_shadow ∅ body ∧
      ¬("dfy" ≼ cml_param) ∧
      find_recfun "dfy_Main" cml_funs =
        SOME (cml_param,
              Handle cml_body [(Pcon (SOME (Short "Return")) [], Unit)])
Proof
  Induct
  \\ simp [get_member_aux_def]
  \\ rpt gen_tac
  \\ reverse CASE_TAC
  \\ rename [‘m = «Main»’]
  >- (* Function *)
   (IF_CASES_TAC \\ simp []
    \\ ‘explode m ≠ "Main"’ by
      (spose_not_then assume_tac \\ Cases_on ‘m’ \\ gvs [])
    \\ disch_tac
    \\ gvs [result_mmap_def, oneline bind_def, from_member_decl_def,
            CaseEq "sum"]
    \\ simp [Once find_recfun_def, set_up_cml_fun_def]
    \\ rpt (pairarg_tac \\ gvs []))
  (* Method *)
  \\ IF_CASES_TAC
  \\ disch_tac
  \\ gvs [result_mmap_def, from_member_decl_def, oneline bind_def,
          CaseEq "sum"]
  >- (* found main at head *)
   (simp [set_up_cml_fun_def, cml_fun_def, set_up_in_refs_def,
          cml_new_refs_def, mk_id_def, Stuple_def, Once find_recfun_def])
  (* main is in tail *)
  \\ ‘explode m ≠ "Main"’ by
    (spose_not_then assume_tac \\ Cases_on ‘m’ \\ gvs [])
  \\ simp [set_up_cml_fun_def, Once find_recfun_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality valid_main_nslookup:
  get_member «Main» (Program members) =
    SOME (Method «Main» [] reqs ens rds decrs [] mod body) ∧
  result_mmap from_member_decl members = INR cml_funs ∧
  EVERY is_fresh_member members ∧
  EVERY no_shadow_method members ⇒
  ∃cml_param cml_body.
    from_stmt body 0 = INR cml_body ∧
    is_fresh_stmt body ∧
    no_shadow ∅ body ∧
    ¬("dfy" ≼ cml_param) ∧
    find_recfun "dfy_Main" cml_funs =
      SOME (cml_param,
            Handle cml_body [(Pcon (SOME (Short "Return")) [], Unit)]) ∧
    nsLookup (nsAppend (build_rec_env cml_funs cl_env env) env₁.v)
      (Short "dfy_Main") =
    SOME (Recclosure cl_env cml_funs "dfy_Main")
Proof
  rpt strip_tac
  \\ fs [get_member_def]
  \\ drule_all find_recfun_main
  \\ rpt strip_tac \\ gvs []
  \\ simp [nsLookup_nsAppend_some]
  \\ disj1_tac
  \\ simp [build_rec_env_def]
  \\ drule_all nslookup_build_rec_env_reclos_aux \\ simp []
QED

Triviality get_member_MEM_aux:
  ∀members. get_member_aux name members = SOME member ⇒ MEM member members
Proof
  Induct
  \\ simp [get_member_aux_def]
  \\ gen_tac
  \\ CASE_TAC
  \\ IF_CASES_TAC \\ simp []
QED

Triviality get_member_MEM:
  get_member name (Program members) = SOME member ⇒ MEM member members
Proof
  simp [get_member_def] \\ disch_tac \\ imp_res_tac get_member_MEM_aux
QED

Definition has_basic_cons_def:
  has_basic_cons env ⇔
    nsLookup env.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env.c (Short "False") = SOME (0, TypeStamp "False" 0)
End

Theorem correct_from_program:
  ∀dfy_ck prog s' r_dfy cml_decs env_cml (t: 'ffi cml_state).
    evaluate_program dfy_ck T prog = (s', r_dfy) ∧
    from_program prog = INR cml_decs ∧
    valid_prog prog ∧ has_basic_cons env_cml ∧
    0 < dfy_ck ∧ t.clock = dfy_ck ∧ ExnStamp t.next_exn_stamp = ret_stamp ∧
    r_dfy ≠ Rstop (Serr Rtype_error) ⇒
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
  \\ gvs [evaluate_decs_def]
  \\ drule_all_then assume_tac ALL_DISTINCT_member_name \\ simp []
  \\ DEP_REWRITE_TAC [map_from_member_decl_one_con_check] \\ simp []
  \\ last_assum $ irule_at (Pos hd)
  \\ simp [pat_bindings_def, cml_fapp_def, cml_apps_def, Apps_def, evaluate_def,
           do_con_check_def, build_conv_def, mk_id_def, extend_dec_env_def]
  \\ gvs [has_cons_def, has_basic_cons_def]
  \\ qmatch_goalsub_abbrev_tac ‘build_rec_env _ cl_env _’
  \\ drule_all valid_main_nslookup
  \\ disch_then $ qspecl_then [‘env_cml’, ‘nsEmpty’, ‘cl_env’] mp_tac
  \\ rpt strip_tac
  \\ simp [do_opapp_def, evaluate_def]
  \\ drule correct_from_stmt
  \\ disch_then drule
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env_cml₁’
  \\ disch_then $
       qspecl_then
         [‘dec_clock (t with next_exn_stamp := t.next_exn_stamp + 1)’,
          ‘env_cml₁’, ‘FEMPTY’, ‘FEMPTY’, ‘LENGTH t.refs’]
         mp_tac
  \\ impl_tac >-
   (unabbrev_all_tac
    \\ rpt strip_tac
    \\ gvs [dec_clock_def, evaluateTheory.dec_clock_def]
    >- (* state_rel *)
     (gvs [state_rel_def, array_rel_def, LLOOKUP_def, locals_rel_def]
      \\ cheat (* TODO print_rel: ARB *))
    >- (* base_at_most *)
     (gvs [base_at_most_def])
    >- (* env_rel *)
     (gvs [env_rel_def, has_cons_def]
      \\ rpt gen_tac \\ disch_tac
      \\ drule get_member_MEM
      \\ gvs [EVERY_MEM]
      \\ disch_then kall_tac
      \\ ‘∀n. cml_param ≠ "dfy_" ++ explode n’ by (rpt strip_tac \\ gvs [])
      \\ gvs []
      \\ drule nslookup_build_rec_env_reclos
      \\ simp [dest_program_def, has_cons_def]))
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

val _ = export_theory ();
