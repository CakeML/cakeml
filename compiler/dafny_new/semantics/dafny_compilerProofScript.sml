(*
  Correctness proof for the Dafny to CakeML compiler.
*)

open preamble
open semanticPrimitivesTheory
open evaluateTheory
open dafny_semanticPrimitivesTheory
open dafny_evaluateTheory

(* For compiler definitions *)
open result_monadTheory

val _ = new_theory "dafny_compilerProof";

(* ************************************************************************** *)
(* TODO Move definitions back to dafny_to_cakeml at the end *)

Overload Unit = “Con NONE []”
Overload False = “Con (SOME (Short "False")) []”
Overload True = “Con (SOME (Short "True")) []”

(* Generates strings of the form _0, _1, etc., to be used for matching tuples *)
Definition cml_tup_vname_def:
  cml_tup_vname (idx : num) = explode («_» ^ (num_to_str idx))
End

(* Generates code of the form: case cml_te of (_0, _1, ...) => cml_e *)
Definition cml_tup_case_def:
  cml_tup_case len cml_te cml_e =
  let tup_pvars = GENLIST (λn. Pvar (cml_tup_vname n)) len in
    Mat cml_te [Pcon NONE tup_pvars, cml_e]
End

Definition cml_tup_select_def:
  cml_tup_select len cml_te (idx: num) =
  cml_tup_case len cml_te (Var (Short (cml_tup_vname idx)))
End

Definition cml_get_arr_dim_def:
  cml_get_arr_dim cml_e = cml_tup_select 2 cml_e 0
End

Definition cml_get_arr_data_def:
  cml_get_arr_data cml_e = cml_tup_select 2 cml_e 1
End

Definition cml_arr_sel_def:
  cml_arr_sel cml_arr cml_idx = App Asub [cml_get_arr_data cml_arr; cml_idx]
End

Definition cml_fapp_aux_def:
  cml_fapp_aux id [] = App Opapp [id; Unit] ∧
  cml_fapp_aux id [cml_e] = App Opapp [id; cml_e] ∧
  cml_fapp_aux id (cml_e::rest) = App Opapp [id; cml_e]
End

Definition cml_fapp_def:
  cml_fapp mns n cml_es = cml_fapp_aux (Var (mk_id mns n)) (REVERSE cml_es)
End

Definition cml_read_var_def:
  cml_read_var v = App Opderef [Var (Short (explode v))]
End

Definition from_un_op_def:
  from_un_op Not cml_e = If cml_e False True
End

Definition from_bin_op_def:
  from_bin_op Lt cml_e₀ cml_e₁ =
    App (Opb Lt) [cml_e₀; cml_e₁] ∧
  from_bin_op Le cml_e₀ cml_e₁ =
    App (Opb Leq) [cml_e₀; cml_e₁] ∧
  from_bin_op Ge cml_e₀ cml_e₁ =
    App (Opb Geq) [cml_e₀; cml_e₁] ∧
  from_bin_op Eq cml_e₀ cml_e₁ =
    App Equality [cml_e₀; cml_e₁] ∧
  from_bin_op Neq cml_e₀ cml_e₁ =
    from_un_op Not (from_bin_op Eq cml_e₀ cml_e₁) ∧
  from_bin_op Sub cml_e₀ cml_e₁ =
    App (Opn Minus) [cml_e₀; cml_e₁] ∧
  from_bin_op Add cml_e₀ cml_e₁ =
    App (Opn Plus) [cml_e₀; cml_e₁] ∧
  from_bin_op Mul cml_e₀ cml_e₁ =
    App (Opn Times) [cml_e₀; cml_e₁] ∧
  from_bin_op And cml_e₀ cml_e₁ =
    Log And cml_e₀ cml_e₁ ∧
  from_bin_op Or cml_e₀ cml_e₁ =
    Log Or cml_e₀ cml_e₁ ∧
  from_bin_op Imp cml_e₀ cml_e₁ =
    from_bin_op Or (from_un_op Not cml_e₀) cml_e₁ ∧
  from_bin_op Div cml_e₀ cml_e₁ =
    cml_fapp ["Dafny"] "ediv" [cml_e₀; cml_e₁]
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | (Neq, _, _) => bin_op_size Neq + 1
                           | (Imp, _, _) => bin_op_size Imp + 1
                           | (bop, _, _) => bin_op_size bop)’
End

Definition from_lit_def:
  from_lit (BoolL b) = (if b then True else False) ∧
  from_lit (IntL i) = Lit (IntLit i) ∧
  from_lit (StrL s) = Lit (StrLit (explode s))
End

Definition from_exp_def:
  from_exp (Lit l) = return (from_lit l) ∧
  from_exp (Var v) = return (cml_read_var v) ∧
  from_exp (If tst thn els) =
  do
    cml_tst <- from_exp tst;
    cml_thn <- from_exp thn;
    cml_els <- from_exp els;
    return (If cml_tst cml_thn cml_els)
  od ∧
  from_exp (UnOp uop e) =
  do
    cml_e <- from_exp e;
    return (from_un_op uop cml_e)
  od ∧
  from_exp (BinOp bop e₀ e₁) =
  do
    cml_e₀ <- from_exp e₀;
    cml_e₁ <- from_exp e₁;
    return (from_bin_op bop cml_e₀ cml_e₁)
  od ∧
  from_exp (ArrLen arr) =
  do
    cml_arr <- from_exp arr;
    return (cml_get_arr_dim cml_arr)
  od ∧
  from_exp (ArrSel arr idx) =
  do
    cml_arr <- from_exp arr;
    cml_idx <- from_exp idx;
    return (cml_arr_sel cml_arr cml_idx)
  od ∧
  from_exp (FunCall n args) =
  do
    cml_args <- map_from_exp args;
    return (cml_fapp [] (explode n) cml_args)
  od ∧
  from_exp (Forall _ _) = fail «from_exp:Forall: Unsupported» ∧
  map_from_exp [] = return [] ∧
  map_from_exp (e::es) =
  do
    cml_e <- from_exp e;
    cml_es <- map_from_exp es;
    return (cml_e::cml_es)
  od
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL e => exp_size e
                           | INR es => list_size exp_size es)’
End

(* ************************************************************************** *)

Type dfy_state[pp] = “:dafny_semanticPrimitives$state”
Type dfy_env[pp] = “:dafny_semanticPrimitives$sem_env”
Type dfy_exp[pp] = “:dafny_ast$exp”
Type dfy_exp_res[pp] = “:'a dafny_semanticPrimitives$exp_result”

Type cml_state[pp] = “:α semanticPrimitives$state”
Type cml_env[pp] = “:v semanticPrimitives$sem_env”
Type cml_exp[pp] = “:ast$exp”
Type cml_res[pp] = “:(v list, v) semanticPrimitives$result”

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    nsLookup env_cml.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env_cml.c (Short "False") = SOME (0, TypeStamp "False" 0)
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

Definition array_rel_def:
  array_rel m s_heap c_store ⇔
  INJ (λx. m ' x) (FDOM m) 𝕌(:num) ∧
  ∀loc vs.
    LLOOKUP s_heap loc = SOME (HArr vs) ⇒
    ∃loc' vs'.
      FLOOKUP m loc = SOME loc' ∧
      store_lookup loc' c_store = SOME (Varray vs') ∧
      LIST_REL (val_rel m) vs vs'
End

Definition locals_rel_def:
  locals_rel m (l: mlstring |-> num) s_locals t_refs (env_cml: cml_env) ⇔
    INJ (λx. l ' x) (FDOM l) 𝕌(:num) ∧
    ∀var dfy_v.
      (* SOME dfy_v means that the local was initialized *)
      read_local s_locals var = (SOME dfy_v) ⇒
      ∃loc cml_v.
        FLOOKUP l var = SOME loc ∧
        (* locals map to references in CakeML *)
        store_lookup loc t_refs = SOME (Refv cml_v) ∧
        val_rel m dfy_v cml_v ∧
        nsLookup env_cml.v (Short (explode var)) = SOME (Loc T loc)
End

(* TODO *)
Definition print_rel_def:
  print_rel _ _ = ARB
End

Definition state_rel_def:
  state_rel m l s t env_cml ⇔
    array_rel m s.heap t.refs ∧
    locals_rel m l s.locals t.refs env_cml ∧
    print_rel s.output t.ffi.io_events
End

(* We don't define the relation to be true between type errors, as we could
   otherwise define a "verified" compiler that always outputs garbage. *)
Definition exp_res_rel_def[simp]:
  (exp_res_rel m (Rval dfy_v) (Rval [cml_v]) ⇔ val_rel m dfy_v cml_v) ∧
  (exp_res_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_res_rel _ _ _ ⇔ F)
End

Definition exp_ress_rel_def[simp]:
  (exp_ress_rel m (Rval dfy_vs) (Rval cml_vs) ⇔
     LIST_REL (val_rel m) dfy_vs cml_vs) ∧
  (exp_ress_rel m (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) ⇔
     T) ∧
  (exp_ress_rel _ _ _ ⇔ F)
End

Triviality read_local_some_imp:
  read_local s.locals name = SOME dfy_v ∧
  state_rel m l s t env_cml ⇒
  ∃loc cml_v.
    FLOOKUP l name = SOME loc ∧
    store_lookup loc t.refs = SOME (Refv cml_v) ∧
    val_rel m dfy_v cml_v ∧
    nsLookup env_cml.v (Short (explode name)) = SOME (Loc T loc)
Proof
  gvs [state_rel_def, locals_rel_def]
QED

Triviality exp_res_rel_rval:
  exp_res_rel m (Rval dfy_v) r_cml ⇒ ∃cml_v. r_cml = Rval [cml_v]
Proof
  cheat
QED

Triviality exp_res_rel_rerr:
  exp_res_rel m (Rerr dfy_err) r_cml ⇒
  dfy_err = Rtimeout_error ∧ r_cml = (Rerr (Rabort Rtimeout_error))
Proof
  cheat
QED

Theorem correct_exp:
  (∀s env_dfy e_dfy s' r_dfy t env_cml e_cml m l.
     evaluate_exp s env_dfy e_dfy = (s', r_dfy) ∧
     from_exp e_dfy = INR e_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ r_dfy ≠ Rerr Rtype_error
     ⇒ ∃t' r_cml.
         evaluate$evaluate t env_cml [e_cml] = (t', r_cml) ∧
         state_rel m l s' t' env_cml ∧ exp_res_rel m r_dfy r_cml) ∧
  (∀s env_dfy es_dfy s' rs_dfy t env_cml es_cml m l.
     evaluate_exps s env_dfy es_dfy = (s', rs_dfy) ∧
     map_from_exp es_dfy = INR es_cml ∧ state_rel m l s t env_cml ∧
     env_rel env_dfy env_cml ∧ rs_dfy ≠ Rerr Rtype_error
     ⇒ ∃t' rs_cml.
         evaluate$evaluate t env_cml es_cml = (t', rs_cml) ∧
         state_rel m l s' t' env_cml ∧ exp_ress_rel m rs_dfy rs_cml)
Proof
  ho_match_mp_tac evaluate_exp_ind
  \\ rpt strip_tac
  >~ [‘Lit l’] >-
   (Cases_on ‘l’
    \\ gvs [from_exp_def, from_lit_def, evaluate_def, do_con_check_def,
            env_rel_def, build_conv_def, exp_res_rel_def, evaluate_exp_def,
            val_rel_cases, Boolv_def, bool_type_num_def, AllCaseEqs()])
  >~ [‘Var name’] >-
   (gvs [evaluate_exp_def, AllCaseEqs()]
    \\ drule_all read_local_some_imp \\ rpt strip_tac
    \\ gvs [from_exp_def, cml_read_var_def]
    \\ gvs [evaluate_def, do_app_def, state_rel_def])
  >~ [‘If grd thn els’] >-
   (reverse $
      gvs [evaluate_exp_def, from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ first_x_assum drule_all \\ rpt strip_tac
    >- (gvs [evaluate_def] \\ TOP_CASE_TAC \\ gvs [])
    \\ rename [‘do_cond v _ _ = SOME _’] \\ Cases_on ‘v’
    \\ gvs [do_cond_def]
    \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [val_rel_cases]
    \\ gvs [evaluate_def, do_if_def]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’
    \\ gvs [Boolv_def])
  >~ [‘UnOp uop e’] >-
   (reverse $
      gvs [evaluate_exp_def, from_exp_def, oneline bind_def,
           oneline from_un_op_def, AllCaseEqs()]
    \\ first_x_assum drule_all \\ rpt strip_tac
    >- (drule exp_res_rel_rerr \\ rpt strip_tac \\ gvs [evaluate_def])
    \\ gvs [oneline do_uop_def, AllCaseEqs()]
    \\ drule exp_res_rel_rval \\ rpt strip_tac \\ gvs [val_rel_cases]
    \\ gvs [evaluate_def, do_if_def]
    \\ rename [‘Boolv b’] \\ Cases_on ‘b’
    \\ gvs [evaluate_def, do_con_check_def, build_conv_def, env_rel_def,
            val_rel_cases, Boolv_def, bool_type_num_def])
  >~ [‘BinOp bop e₀ e₁’] >-

   (gvs [from_exp_def, oneline bind_def, AllCaseEqs()]
    \\ gvs [evaluate_exp_def]
    \\ namedCases_on ‘evaluate_exp s env_dfy e₀’ ["s₁ r"] \\ gvs []
    \\ Cases_on ‘r = Rerr Rtype_error’ \\ gvs []
    \\ first_x_assum drule_all \\ rpt strip_tac \\ gvs []

    \\ reverse $ Cases_on ‘r’ \\ gvs []
    >- (Cases_on ‘bop’ \\ gvs [from_bin_op_def, evaluate_def] \\ cheat)
    \\ cheat)
  \\ cheat
QED

val _ = export_theory ();
