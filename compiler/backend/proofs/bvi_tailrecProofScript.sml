(*
  Correctness proof for bvi_tailrec
*)
open preamble bviSemTheory bviPropsTheory bvi_tailrecTheory

(* TODO

   - It should be possible to prove that we can replace the simplified
     compile_exp by the old compile_exp without touching the evaluate-
     theorem. Benefits:
       * Less code duplication
       * Can inline auxiliary calls more easily
*)

val _ = new_theory "bvi_tailrecProof";

val _ = set_grammar_ancestry ["bvi_tailrec","bviProps","bviSem"];

val find_code_def = bvlSemTheory.find_code_def;
val s = mk_var("s",
  type_of ``bviSem$evaluate`` |> strip_fun |> snd |> dest_prod |> snd
  |> type_subst [alpha|->``:num#'c``,beta|->``:'ffi``]);

Theorem get_bin_args_SOME[simp]:
   ∀exp q. get_bin_args exp = SOME q
    ⇔
    ∃e1 e2 op. q = (e1, e2) ∧ exp = Op op [e1; e2]
Proof
  Cases \\ rw [get_bin_args_def]
  \\ rw[bvlPropsTheory.case_eq_thms]
  \\ rw[EQ_IMP_THM]
QED

Theorem opbinargs_SOME[simp]:
   !exp opr. opbinargs opr exp = SOME q
   <=>
   opr <> Noop /\ ?x y. q = (x, y) /\ exp = Op (to_op opr) [x;y]
Proof
   Cases \\ Cases \\ fs [opbinargs_def, to_op_def, op_eq_def]
   \\ rw [EQ_IMP_THM]
QED

Theorem decide_ty_simp1[simp]:
   (decide_ty ty1 ty2 = Int  <=> ty1 = Int  /\ ty2 = Int) /\
   (decide_ty ty1 ty2 = List <=> ty1 = List /\ ty2 = List)
Proof
  Cases_on `ty1` \\ Cases_on `ty2` \\ fs [decide_ty_def]
QED

Theorem list_to_v_simp[simp]:
   !xs. v_to_list (list_to_v xs) = SOME xs
Proof
  Induct \\ fs [bvlSemTheory.v_to_list_def, bvlSemTheory.list_to_v_def]
QED

Theorem to_op_11[simp]:
   to_op op1 = to_op op2 <=> op1 = op2
Proof
  Cases_on `op1` \\ Cases_on `op2` \\ rw [to_op_def]
QED

Theorem to_op_eq_simp[simp]:
   (to_op x = Add        <=> (x = Plus))   /\
   (to_op x = Mult       <=> (x = Times))  /\
   (to_op x = Mod        <=> (x = Noop))   /\
   (to_op x = ListAppend <=> (x = Append)) /\
   (Add        = to_op x <=> (x = Plus))   /\
   (Mult       = to_op x <=> (x = Times))  /\
   (ListAppend = to_op x <=> (x = Append)) /\
   (Mod        = to_op x <=> (x = Noop))
Proof
   Cases_on`x` \\ rw[to_op_def]
QED

Theorem op_eq_simp[simp]:
   (op_eq Plus x   <=> (?xs. x = Op Add xs))  /\
   (op_eq Times x  <=> (?xs. x = Op Mult xs)) /\
   (op_eq Append x <=> (?xs. x = Op ListAppend xs))
Proof
  Cases_on`x` \\ rw[op_eq_def]
QED

Theorem scan_expr_EVERY_SING[simp]:
   EVERY P (scan_expr ts loc [x]) ⇔ P (HD (scan_expr ts loc [x]))
Proof
  `LENGTH (scan_expr ts loc [x]) = 1` by fs []
  \\ Cases_on `scan_expr ts loc [x]` \\ fs []
QED

Theorem try_update_LENGTH[simp]:
   LENGTH (try_update ty idx ts) = LENGTH ts
Proof
  Cases_on `idx` \\ rw [try_update_def]
QED

Theorem update_context_LENGTH[simp]:
   LENGTH (update_context ty ts x y) = LENGTH ts
Proof
  rw [update_context_def, try_update_LENGTH]
QED

Theorem decide_ty_simp[simp]:
   decide_ty ty1 ty2 = ty3 /\ ty3 <> Any <=>
   ty1 = ty3 /\ ty2 = ty3 /\ ty3 <> Any
Proof
  Cases_on `ty1` \\ Cases_on `ty2`
  \\ fs [decide_ty_def] \\ rw [EQ_IMP_THM]
  \\ Cases_on `ty3` \\ fs []
QED

val ty_rel_def = Define `
  ty_rel = LIST_REL
    (\v t. (t = Int  ==> ?k. v = Number k) /\
           (t = List ==> ?ys. v_to_list v = SOME ys))`;

val v_ty_thms = { nchotomy = v_ty_nchotomy, case_def = v_ty_case_def };
val v_ty_cases = prove_case_eq_thm v_ty_thms
val assoc_op_ty_thms = { nchotomy = assoc_op_nchotomy, case_def = assoc_op_case_def }
val assoc_op_cases = prove_case_eq_thm assoc_op_ty_thms
val case_eq_thms = CONJ v_ty_cases (CONJ assoc_op_cases bviPropsTheory.case_eq_thms)

Theorem list_to_v_imp:
   !x xs. v_to_list x = SOME xs ==> list_to_v xs = x
Proof
  recInduct bvlSemTheory.v_to_list_ind
  \\ rw [bvlSemTheory.v_to_list_def]
  \\ fs [case_eq_thms] \\ rw []
  \\ fs [bvlSemTheory.list_to_v_def]
QED

val s1 = mk_var("s",
  type_of ``bviSem$evaluate`` |> strip_fun |> snd |> dest_prod |> snd
  |> type_subst [alpha|->``:'c``,beta|->``:'ffi``]);

Theorem term_ok_int_SING:
   !ts exp env ^s1 r t.
     term_ok_int ts exp /\
     ty_rel env ts /\
     evaluate ([exp], env, s) = (r, t) ==>
       s = t /\
       ?v. r = Rval [v] /\
       (!^s1. evaluate ([exp], env, s) = (r, s)) /\
       ?k. v = Number k
Proof
  recInduct term_ok_int_ind \\ rw [] \\ Cases_on `expr`
  \\ qhdtm_x_assum `term_ok_int` mp_tac
  \\ once_rewrite_tac [term_ok_int_def]
  \\ fs [case_elim_thms, case_eq_thms, pair_case_eq, bool_case_eq] \\ rw []
  \\ TRY
   (fs [ty_rel_def, LIST_REL_EL_EQN, evaluate_def, pair_case_eq, bool_case_eq]
    \\ NO_TAC)
  \\ TRY
   (rename1 `is_const op` \\ Cases_on `op` \\ fs []
    \\ fs [evaluate_def, pair_case_eq, bool_case_eq, do_app_def,
           do_app_aux_def, bvlSemTheory.do_app_def, small_int_def,
           backend_commonTheory.small_enough_int_def]
    \\ rw [] \\ fs [])
  \\ rename1 `is_arith op` \\ Cases_on `op` \\ fs [is_arith_def]
  \\ fs [evaluate_def, pair_case_eq, bool_case_eq, do_app_def,
         do_app_aux_def, bvlSemTheory.do_app_def, small_int_def,
         backend_commonTheory.small_enough_int_def,
         case_elim_thms, case_eq_thms]
  \\ rw [] \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rw []
  \\ res_tac \\ rw [] \\ fs []
  \\ fs [bvl_to_bvi_id]
QED

Theorem term_ok_any_SING:
   (!ts list exp env ^s1 r t.
     term_ok_any ts list exp /\
     ty_rel env ts /\
     evaluate ([exp], env, s) = (r, t) ==>
       s = t /\
       ?v. r = Rval [v] /\
       (!^s1. evaluate ([exp], env, s) = (r, s)) /\
       (list ==> ?ys. v_to_list v = SOME ys))
Proof
  recInduct term_ok_any_ind \\ rw []
  \\ qhdtm_x_assum `term_ok_any` mp_tac
  \\ once_rewrite_tac [term_ok_any_def] \\ fs []
  \\ TRY PURE_TOP_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ TRY
   (rename1 `Var n` \\ rw []
    \\ rfs [ty_rel_def, evaluate_def, LIST_REL_EL_EQN, case_elim_thms,
            case_elim_thms, pair_case_eq, bool_case_eq] \\ rw [] \\ fs []
    \\ NO_TAC)
  \\ TRY
   (rename1 `is_const op` \\ Cases_on `op`
    \\ fs [evaluate_def, do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
           case_eq_thms, case_elim_thms, pair_case_eq]
    \\ fs [backend_commonTheory.small_enough_int_def, small_int_def])
  \\ fs [is_op_thms]
  \\ TRY
   (rename1 `Op (Cons 0) []`
    \\ fs [evaluate_def, do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
           case_eq_thms, case_elim_thms, pair_case_eq]
    \\ fs [bvl_to_bvi_id]
    \\ rw [] \\ fs [bvlSemTheory.v_to_list_def]
    \\ EVAL_TAC)
  \\ TRY
   (rename1 `is_rel op` \\ Cases_on `op` \\ fs [is_rel_def]
    \\ fs [evaluate_def, pair_case_eq, case_elim_thms, case_eq_thms] \\ rw []
    \\ imp_res_tac evaluate_SING_IMP \\ rw [] \\ fs []
    \\ imp_res_tac term_ok_int_SING \\ fs []
    \\ rfs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def] \\ rw []
    \\ fs [bvl_to_bvi_id])
  \\ TRY
   (rename1 `is_arith op` \\ Cases_on `op` \\ fs [is_arith_def]
    \\ fs [evaluate_def, pair_case_eq, case_elim_thms, case_eq_thms] \\ rw []
    \\ imp_res_tac term_ok_int_SING \\ fs [] \\ rw []
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def] \\ rw []
    \\ fs [bvl_to_bvi_id])
  \\ fs [evaluate_def, pair_case_eq, case_eq_thms, case_elim_thms] \\ rw []
  \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
  \\ fs [LENGTH_EQ_NUM_compute] \\ rw []
  \\ fs [LENGTH_EQ_NUM_compute] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def] \\ rw []
  \\ fs [bvl_to_bvi_id]
  \\ fs [bvlSemTheory.v_to_list_def] \\ EVAL_TAC
QED

Theorem term_ok_SING:
   !ts ty exp env ^s1 r t.
     term_ok ts ty exp /\
     ty_rel env ts /\
     evaluate ([exp], env, s) = (r, t) ==>
       s = t /\
       ?v. r = Rval [v] /\
       (!^s1. evaluate ([exp], env, s) = (r, s)) /\
       case ty of
         Int  => ?k. v = Number k
       | List => ?ys. v_to_list v = SOME ys
       | _    => T
Proof
  rw [term_ok_def, case_elim_thms, case_eq_thms] \\ every_case_tac \\ fs []
  \\ metis_tac [term_ok_int_SING, term_ok_any_SING]
QED

val op_id_val_def = Define `
  op_id_val Plus   = Number 0 /\
  op_id_val Times  = Number 1 /\
  op_id_val Append = Block nil_tag [] /\
  op_id_val Noop   = Number 6333
  `;

Theorem scan_expr_not_Noop:
   ∀exp ts loc tt ty r ok op.
     scan_expr ts loc [exp] = [(tt, ty, r, SOME op)] ⇒
       op ≠ Noop
Proof
  Induct
  \\ rw [scan_expr_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs[bvlPropsTheory.case_eq_thms]
  \\ fs [from_op_def] \\ rveq
  \\ rfs [case_eq_thms, bool_case_eq] \\ fs []
  \\ metis_tac []
QED

val env_rel_def = Define `
  env_rel ty opt acc env1 env2 <=>
    isPREFIX env1 env2 /\
    (opt ⇒
      LENGTH env1 = acc /\
      LENGTH env2 > acc /\
      case ty of
        Int => ?k. EL acc env2 = Number k
      | List => ?ys. v_to_list (EL acc env2) = SOME ys
      | Any => F)`;

val _ = temp_overload_on("in_ns_2",``λn. n MOD bvl_to_bvi_namespaces = 2``);

val code_rel_def = Define `
  code_rel c1 c2 ⇔
    ∀loc arity exp op.
      lookup loc c1 = SOME (arity, exp) ⇒
      (check_exp loc arity exp = NONE ⇒
        lookup loc c2 = SOME (arity, exp)) ∧
      (check_exp loc arity exp = SOME op ⇒
        ∃n.
          ∀exp_aux exp_opt.
          compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
            lookup loc c2 = SOME (arity, exp_aux) ∧
            lookup n c2 = SOME (arity + 1, exp_opt))`;

val code_rel_find_code_SOME = Q.prove (
  `∀c1 c2 (args: v list) a exp.
     code_rel c1 c2 ∧
     find_code (SOME n) args c1 = SOME (a, exp) ⇒
       find_code (SOME n) args c2 ≠ NONE`,
  rw [find_code_def, code_rel_def]
  \\ pop_assum mp_tac
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ first_x_assum drule
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []);

val code_rel_find_code_NONE = Q.prove (
  `∀c1 c2 (args: v list) a exp.
     code_rel c1 c2 ∧
     find_code NONE args c1 = SOME (a, exp) ⇒
       find_code NONE args c2 ≠ NONE`,
  rw [find_code_def, code_rel_def]
  \\ pop_assum mp_tac
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
  >-
   (first_x_assum drule
    \\ fs [compile_exp_def]
    \\ CASE_TAC \\ fs [] \\ rw []
    \\ pairarg_tac \\ fs [])
  \\ first_x_assum drule
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []);

Theorem code_rel_domain:
   ∀c1 c2.
     code_rel c1 c2 ⇒ domain c1 ⊆ domain c2
Proof
  simp [code_rel_def, SUBSET_DEF]
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  \\ fs [GSYM lookup_NONE_domain]
  \\ rename1 `SOME z`
  \\ PairCases_on `z`
  \\ first_x_assum drule
  \\ fs [compile_exp_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ pairarg_tac \\ fs []
QED

Theorem evaluate_let_wrap:
   ∀x op vs ^s1 r t.
     op ≠ Noop ⇒
     evaluate ([let_wrap (LENGTH vs) (id_from_op op) x], vs, s) =
     evaluate ([x], vs ++ [op_id_val op] ++ vs, s)
Proof
  rw []
  \\ `LENGTH vs + 0 ≤ LENGTH vs` by fs []
  \\ drule (GEN_ALL (ISPEC s1 (Q.GEN `st` (SPEC_ALL evaluate_genlist_vars))))
  \\ disch_then (qspec_then `s` mp_tac)
  \\ simp [let_wrap_def, evaluate_def]
  \\ once_rewrite_tac [evaluate_APPEND]
  \\ simp [pair_case_eq, case_eq_thms, case_elim_thms, PULL_EXISTS, bool_case_eq]
  \\ Cases_on `op` \\ EVAL_TAC \\ rw []
  \\ AP_TERM_TAC
  \\ fs [state_component_equality]
QED

Theorem evaluate_complete_ind:
   ∀P.
    (∀xs s.
      (∀ys t.
        exp2_size ys < exp2_size xs ∧ t.clock ≤ s.clock ∨ t.clock < s.clock ⇒
        P ys t) ⇒
      P xs s) ⇒
    ∀(xs: bvi$exp list) ^s. P xs s
Proof
  rpt strip_tac
  \\ `∃sz. exp2_size xs = sz` by fs []
  \\ `∃ck0. s.clock = ck0` by fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ qspec_tac (`xs`,`xs`)
  \\ qspec_tac (`s`,`s`)
  \\ qspec_tac (`sz`,`sz`)
  \\ completeInduct_on `ck0`
  \\ strip_tac
  \\ completeInduct_on `sz`
  \\ fs [PULL_FORALL, AND_IMP_INTRO, GSYM CONJ_ASSOC]
  \\ rpt strip_tac \\ rveq
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ simp []
  \\ fs [LESS_OR_EQ]
QED

Theorem EVERY_LAST1:
   !xs y. EVERY P xs /\ LAST1 xs = SOME y ==> P y
Proof
  ho_match_mp_tac LAST1_ind \\ rw [LAST1_def] \\ fs []
QED

Theorem scan_expr_LENGTH:
   ∀ts loc xs ys.
     scan_expr ts loc xs = ys ⇒
       EVERY (λy. LENGTH (FST y) = LENGTH ts) ys
Proof
  ho_match_mp_tac scan_expr_ind
  \\ rw [scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (PURE_CASE_TAC \\ fs [case_eq_thms, case_elim_thms, pair_case_eq])
  \\ rw [try_update_LENGTH]
  \\ fs [LAST1_def, case_eq_thms] \\ rw [] \\ fs []
  \\ imp_res_tac EVERY_LAST1 \\ fs []
  \\ Cases_on `op` \\ fs [arg_ty_def, update_context_def, check_op_def]
QED

Theorem ty_rel_decide_ty:
   ∀ts tt env.
     (ty_rel env ts ∨ ty_rel env tt) ∧ LENGTH ts = LENGTH tt ⇒
       ty_rel env (MAP2 decide_ty ts tt)
Proof
  Induct \\ rw [] \\ fs []
  \\ Cases_on `tt` \\ rfs [ty_rel_def]
  \\ EVAL_TAC \\ fs [] \\ rveq
  \\ Cases_on `h`  \\ fs [] \\ Cases_on `h'` \\ simp [decide_ty_def]
QED

val ty_rel_APPEND = Q.prove (
  `∀env ts ws vs.
     ty_rel env ts ∧ ty_rel vs ws ⇒ ty_rel (vs ++ env) (ws ++ ts)`,
  rw []
  \\ sg `LENGTH ws = LENGTH vs`
  >- (fs [ty_rel_def, LIST_REL_EL_EQN])
  \\ fs [ty_rel_def, LIST_REL_APPEND_EQ]);

Theorem LAST1_thm:
   !xs. LAST1 xs = NONE <=> xs = []
Proof
  Induct \\ rw [LAST1_def]
  \\ Cases_on `xs` \\ fs [LAST1_def]
QED

Theorem try_update_EL:
   n < LENGTH ts ==>
   EL n (try_update ty idx ts) =
     case idx of
       NONE => EL n ts
     | SOME m =>
         if n < m then
           EL n ts
         else if n > m then
           EL n ts
         else if EL n ts = Any \/ EL n ts = ty then
           ty
         else
           EL n ts
Proof
  Cases_on `idx`
  \\ rw [try_update_def]
  \\ fs [EL_LENGTH_APPEND, EL_APPEND1, EL_TAKE, EL_APPEND2, EL_DROP]
  \\ `n = x` by fs [] \\ fs []
QED

Theorem try_update_twice:
   n < LENGTH ts ==>
   EL n (try_update ty idx1 (try_update ty idx2 ts)) =
     case (idx1, idx2) of
       (NONE, NONE) => EL n ts
     | (NONE, SOME b) =>
         if n <> b then EL n ts
         else if EL n ts = Any then ty
         else EL n ts
     | (SOME a, NONE) =>
         if n <> a then EL n ts
         else if EL n ts = Any then ty
         else EL n ts
     | (SOME a, SOME b) =>
         if n <> a /\ n <> b then EL n ts
         else if EL n ts = Any then ty
         else EL n ts
Proof
  rw [] \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ fs [try_update_EL]
  \\ rpt (PURE_CASE_TAC \\ fs [])
QED

Theorem index_of_simp[simp]:
   index_of exp = SOME n <=> exp = Var n
Proof
  Cases_on `exp` \\ rw [index_of_def]
QED

Theorem scan_expr_ty_rel:
   ∀ts loc xs env ys s vs t.
     ty_rel env ts ∧
     scan_expr ts loc xs = ys ∧
     evaluate (xs, env, s) = (Rval vs, t) ⇒
       EVERY (ty_rel env o FST) ys ∧
       ty_rel vs (MAP (FST o SND) ys)
Proof
  ho_match_mp_tac scan_expr_ind
  \\ fs [scan_expr_def]
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [evaluate_def]
  \\ TRY (fs [ty_rel_def] \\ NO_TAC)
  >- (* Cons *)
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, PULL_EXISTS] \\ rw []
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [ty_rel_def]
    \\ res_tac \\ fs [] \\ rw [])
  >- (* Var *)
   (rw []
    \\ fs [ty_rel_def, LIST_REL_EL_EQN]
    \\ rw []
    \\ metis_tac [])
  \\ strip_tac
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ TRY (* All but Let, Op, If *)
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, bool_case_eq, PULL_EXISTS]
    \\ rw []
    \\ res_tac \\ fs [] \\ rw []
    \\ TRY (metis_tac [])
    \\ imp_res_tac evaluate_SING_IMP \\ fs []
    \\ imp_res_tac scan_expr_LENGTH \\ fs []
    \\ TRY (fs [ty_rel_def] \\ NO_TAC)
    \\ Cases_on `ty1` \\ fs []
    \\ TRY (metis_tac [ty_rel_decide_ty])
    \\ fs [decide_ty_def, ty_rel_def]
    \\ metis_tac [])
  >- (* If *)
   (fs [pair_case_eq, case_eq_thms, case_elim_thms, PULL_EXISTS] \\ rw []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [] \\ rveq
    \\ fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM) \\ fs []
    \\ TRY
     (imp_res_tac scan_expr_LENGTH \\ fs []
      \\ metis_tac [ty_rel_decide_ty])
    \\ rpt (PURE_CASE_TAC \\ fs [])
    \\ res_tac
    \\ fs [ty_rel_def, decide_ty_def])
  >- (* Let *)
   (fs [case_eq_thms, pair_case_eq, case_elim_thms, bool_case_eq]
    \\ fs [PULL_EXISTS]
    \\ rpt (gen_tac ORELSE DISCH_TAC) \\ fs []
    \\ reverse conj_tac
    \\ qpat_x_assum `scan_expr _ _ [x] = _` mp_tac
    \\ CASE_TAC \\ fs [LAST1_thm]
    \\ strip_tac
    \\ res_tac \\ rfs []
    \\ TRY (fs [ty_rel_def, LIST_REL_LENGTH] \\ NO_TAC)
    \\ TRY
     (pop_assum mp_tac
      \\ rw [ty_rel_def] \\ fs [] \\ rfs []
      \\ pop_assum mp_tac
      \\ rw [ty_rel_def]
      \\ res_tac
      \\ fs [LIST_REL_EL_EQN]
      \\ imp_res_tac scan_expr_LENGTH \\ fs []
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [] \\ rveq
      \\ fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ NO_TAC)
    \\ rw []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [] \\ rveq
    \\ fs [LENGTH_EQ_NUM_compute] \\ rveq
    \\ imp_res_tac EVERY_LAST1 \\ fs []
    \\ fs [ty_rel_APPEND]
    \\ rpt (qpat_x_assum `ty_rel _ _` mp_tac)
    \\ rw [ty_rel_def, LIST_REL_EL_EQN]
    \\ rfs [EL_DROP]
    \\ `n + LENGTH vs' < LENGTH tu` by fs []
    \\ rpt (first_x_assum drule) \\ rw []
    \\ rfs [EL_APPEND1, EL_APPEND2, EL_LENGTH_APPEND])
  \\ CASE_TAC \\ fs []
  >-
   (rw [case_eq_thms, case_elim_thms, IS_SOME_EXISTS, PULL_EXISTS, bool_case_eq,
        pair_case_eq, from_op_def, arg_ty_def, op_ty_def]
    \\ fs [pair_case_eq, case_elim_thms, case_eq_thms] \\ rw [] \\ fs []
    \\ fs [op_type_def, arg_ty_def, ty_rel_def, get_bin_args_def, case_elim_thms,
           case_eq_thms] \\ rw [] \\ fs [evaluate_def] \\ rw [] \\ fs []
    \\ fs [check_op_def, opbinargs_def, try_swap_def, get_bin_args_def]
    \\ TRY (Cases_on `op`) \\ fs [do_app_def, do_app_aux_def,
                                  bvlSemTheory.do_app_def, bool_case_eq,
                                  case_elim_thms, case_eq_thms] \\ rw [] \\ fs []
    \\ fs [bvlSemTheory.v_to_list_def] \\ EVAL_TAC)
  \\ rveq
  \\ fs [evaluate_def]
  \\ Cases_on `op` \\ fs [from_op_def, arg_ty_def]
  \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq] \\ rw []
  \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
  \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq] \\ rw []
  \\ fs [check_op_def, term_ok_def, opbinargs_def, get_bin_args_def, op_type_def]
  \\ fs [ty_rel_def, LIST_REL_EL_EQN] \\ rw []
  \\ fs [bool_case_eq, try_swap_def]
  \\ pop_assum mp_tac
  \\ fs [update_context_def, try_update_twice]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rveq
  \\ fs [evaluate_def, bool_case_eq, pair_case_eq, case_eq_thms, case_elim_thms] \\ rveq
  \\ fs [] \\ rveq \\ rfs []
  \\ metis_tac []
QED

Theorem check_op_thm:
   check_op ts opr loc exp = SOME expr ==>
   ?x y.
     is_rec loc x /\
     term_ok ts (op_type opr) y /\
     expr = Op (to_op opr) [y; x] /\
     (exp = Op (to_op opr) [x; y] \/ exp = Op (to_op opr) [y; x])
Proof
  rw [check_op_def, opbinargs_def] \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ Cases_on `opr` \\ fs [try_swap_def, opbinargs_def, get_bin_args_def,
                           apply_op_def, op_type_def, term_ok_def, case_eq_thms,
                           IS_SOME_EXISTS, case_elim_thms]
  \\ rw [] \\ fs [to_op_def]
  \\ metis_tac []
QED

Theorem rewrite_scan_expr:
   !loc next op acc ts exp tt ty p exp2 r opr.
   rewrite loc next op acc ts exp = (p,exp2) /\
   op <> Noop /\
   scan_expr ts loc [exp] = [(tt, ty, r, opr)] ==>
     case opr of
       SOME op1 => op = op1 ==> p
     | NONE     => ~p
Proof
  recInduct rewrite_ind
  \\ rw [rewrite_def, scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ fs [IS_SOME_EXISTS, case_elim_thms, pair_case_eq, case_eq_thms] \\ rw [] \\ fs []
  \\ imp_res_tac check_op_thm \\ fs []
  \\ rw [] \\ fs [to_op_def, is_const_def]
  \\ TRY (Cases_on `opr` \\ fs [])
  \\ fs [opbinargs_def, get_bin_args_def, from_op_def, to_op_def]
QED

Theorem scan_expr_op_type:
   !ts loc xs ys.
     scan_expr ts loc xs = ys ==>
     EVERY (\(tt,ty,r,opr).
       case opr of
         SOME op => ty <> Any ==> op_type op = ty
       | NONE => T) ys
Proof
  recInduct scan_expr_ind \\ rw [scan_expr_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [case_elim_thms] \\ rw []
  \\ fs [] \\ rw []
  \\ Cases_on `op` \\ fs [op_type_def, from_op_def]
  \\ fs [get_bin_args_def, arg_ty_def, check_op_def, opbinargs_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ Cases_on `ty1` \\ Cases_on `ty2` \\ rfs [decide_ty_def]
QED

val optimized_code_def = Define `
  optimized_code loc arity exp n c op =
    ∃exp_aux exp_opt.
        compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ∧
        check_exp loc arity exp     = SOME op ∧
        lookup loc c                = SOME (arity, exp_aux) ∧
        lookup n c                  = SOME (arity + 1, exp_opt)`;

Theorem code_rel_subspt:
   code_rel c1 x1 ∧ subspt x1 x2 ⇒ code_rel c1 x2
Proof
  rw[code_rel_def]
  \\ fs[subspt_lookup]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`op`mp_tac)
  \\ rw[] \\ qexists_tac`n` \\ rw[]
QED

Theorem compile_prog_LENGTH:
   ∀n prog. LENGTH (SND (bvi_tailrec$compile_prog n prog)) ≥ LENGTH prog
Proof
  recInduct compile_prog_ind
  \\ conj_tac
  >- fs [compile_prog_def]
  \\ rw []
  \\ Cases_on `compile_exp loc next arity exp` \\ fs []
  >-
   (fs [compile_prog_def]
    \\ pairarg_tac \\ fs [])
  \\ PairCases_on `x`
  \\ fs [compile_prog_def]
  \\ pairarg_tac \\ fs []
QED

val free_names_def = Define `
  free_names n (name: num) ⇔ ∀k. n + bvl_to_bvi_namespaces*k ≠ name
  `;

val more_free_names = Q.prove (
  `free_names n name ⇒ free_names (n + bvl_to_bvi_namespaces) name`,
  fs [free_names_def] \\ rpt strip_tac
  \\ first_x_assum (qspec_then `k + 1` mp_tac) \\ strip_tac
  \\ rw []);

val is_free_name = Q.prove (
  `free_names n name ⇒ n ≠ name`,
  fs [free_names_def] \\ strip_tac
  \\ first_x_assum (qspec_then `0` mp_tac) \\ strip_tac \\ rw []);

val compile_exp_next_addr = Q.prove (
  `compile_exp loc next args exp = NONE ⇒
     compile_exp loc (next + bvl_to_bvi_namespaces) args exp = NONE`,
  fs [compile_exp_def]
  \\ every_case_tac
  \\ pairarg_tac \\ fs []);

Theorem compile_prog_untouched:
   ∀next prog prog2 loc exp arity.
     free_names next loc ∧
     lookup loc (fromAList prog) = SOME (arity, exp) ∧
     check_exp loc arity exp = NONE ∧
     compile_exp loc next arity exp = NONE ∧
     compile_prog next prog = (next1, prog2) ⇒
       lookup loc (fromAList prog2) = SOME (arity, exp)
Proof
  ho_match_mp_tac compile_prog_ind \\ rw []
  \\ fs [fromAList_def, lookup_def]
  \\ Cases_on `loc' = loc` \\ rw []
  >-
   (Cases_on `lookup loc (fromAList xs)`
    \\ fs [compile_prog_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rfs [] \\ rw []
    \\ simp [fromAList_def])
  \\ fs [lookup_insert]
  \\ Cases_on `compile_exp loc next arity exp` \\ fs []
  >-
   (fs [compile_prog_def]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [fromAList_def, lookup_insert])
  \\ PairCases_on `x`
  \\ imp_res_tac more_free_names
  \\ imp_res_tac compile_exp_next_addr
  \\ fs [compile_prog_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [fromAList_def, lookup_insert]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ rw [fromAList_def, lookup_insert, is_free_name]
QED

val EVERY_free_names_SUCSUC = Q.prove (
  `∀xs.
     EVERY (free_names n o FST) xs ⇒
       EVERY (free_names (n + bvl_to_bvi_namespaces) o FST) xs`,
  Induct
  \\ strip_tac \\ fs []
  \\ strip_tac
  \\ imp_res_tac more_free_names);

Theorem compile_prog_touched:
   ∀next prog prog2 loc exp arity.
     ALL_DISTINCT (MAP FST prog) ∧
     EVERY (free_names next o FST) prog ∧
     free_names next loc ∧
     lookup loc (fromAList prog) = SOME (arity, exp) ∧
     check_exp loc arity exp = SOME op ∧
     compile_prog next prog = (next1, prog2) ⇒
       ∃k. ∀exp_aux exp_opt.
         compile_exp loc (next + bvl_to_bvi_namespaces * k) arity exp = SOME (exp_aux, exp_opt) ⇒
           lookup loc (fromAList prog2) = SOME (arity, exp_aux) ∧
           lookup (next + bvl_to_bvi_namespaces * k) (fromAList prog2) = SOME (arity + 1, exp_opt)
Proof
  ho_match_mp_tac compile_prog_ind \\ rw []
  \\ fs [fromAList_def, lookup_def]
  \\ pop_assum mp_tac
  \\ simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_TOP_CASE_TAC \\ fs []
  >-
   (rw []
    \\ qpat_x_assum `compile_exp _ _ _ _ = _` mp_tac
    \\ simp [Once compile_exp_def, check_exp_def]
    \\ `LENGTH (scan_expr (REPLICATE arity Any) loc [exp]) = LENGTH [exp]` by fs []
    \\ CASE_TAC \\ fs []
    \\ PairCases_on `h` \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = SOME (_, _)` mp_tac
    \\ simp [lookup_insert, fromAList_def]
    \\ IF_CASES_TAC \\ strip_tac
    \\ rw [] \\ rfs []
    \\ rveq \\ fs []
    \\ TRY (pairarg_tac \\ fs [])
    \\ first_x_assum drule
    \\ disch_then drule \\ rw []
    \\ fs [lookup_insert, fromAList_def]
    \\ qexists_tac `k` \\ rw []
    \\ fs [free_names_def,backend_commonTheory.bvl_to_bvi_namespaces_def])
  \\ PURE_CASE_TAC \\ rw []
  \\ qpat_x_assum `lookup _ _ = SOME (_,_)` mp_tac
  \\ fs [lookup_insert, fromAList_def]
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ imp_res_tac more_free_names
  \\ rfs [EVERY_free_names_SUCSUC]
  \\ fs [lookup_insert, fromAList_def, free_names_def]
  \\ TRY (qexists_tac `0` \\ fs [backend_commonTheory.bvl_to_bvi_namespaces_def] \\ NO_TAC)
  \\ first_x_assum (qspec_then `loc'` assume_tac)
  \\ first_x_assum drule
  \\ disch_then drule \\ rw []
  \\ qexists_tac `k + 1` \\ fs []
  \\ simp [LEFT_ADD_DISTRIB]
  \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
QED

val check_exp_NONE_compile_exp = Q.prove (
  `check_exp loc arity exp = NONE ⇒ compile_exp loc next arity exp = NONE`,
  fs [compile_exp_def]);

val check_exp_SOME_compile_exp = Q.prove (
  `check_exp loc arity exp = SOME p ⇒
     ∃q. compile_exp loc next arity exp = SOME q`,
  fs [compile_exp_def, check_exp_def]
  \\ rw [] \\ rw []
  \\ pairarg_tac \\ fs []);

val EVERY_free_names_thm = Q.prove (
  `EVERY (free_names next o FST) prog ∧
   lookup loc (fromAList prog) = SOME x ⇒
     free_names next loc`,
  rw [lookup_fromAList, EVERY_MEM]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then `(loc, x)` mp_tac) \\ rw []);

Theorem compile_prog_code_rel:
   compile_prog next prog = (next1, prog2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ⇒
     code_rel (fromAList prog) (fromAList prog2)
Proof
  rw [code_rel_def]
  \\ imp_res_tac EVERY_free_names_thm
  >- metis_tac [check_exp_NONE_compile_exp, compile_prog_untouched]
  \\ drule compile_prog_touched
  \\ rpt (disch_then drule) \\ rw []
  \\ qexists_tac `bvl_to_bvi_namespaces * k + next` \\ fs []
  \\ `0 < bvl_to_bvi_namespaces` by EVAL_TAC
  \\ simp[ADD_MODULUS]
QED

Theorem compile_prog_next_mono:
   ∀n xs n1 ys. compile_prog n xs = (n1,ys) ⇒ ∃k. n1 = n + bvl_to_bvi_namespaces * k
Proof
  recInduct compile_prog_ind
  \\ rw[compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[bvlPropsTheory.case_eq_thms])
  \\ rveq \\ fs[]
  \\ TRY(qexists_tac`0` \\ simp[] \\ NO_TAC)
  \\ TRY(qexists_tac`k` \\ simp[] \\ NO_TAC)
  \\ TRY(qexists_tac`k+1` \\ simp[] \\ NO_TAC)
QED

Theorem compile_prog_MEM:
   compile_prog n xs = (n1,ys) /\ MEM e (MAP FST ys) ==>
   MEM e (MAP FST xs) \/ (n <= e /\ e < n1 /\ (∃k. e = n + k * bvl_to_bvi_namespaces))
Proof
  qspec_tac (`e`,`e`)
  \\ qspec_tac (`n1`,`n1`)
  \\ qspec_tac (`ys`,`ys`)
  \\ qspec_tac (`n`,`n`)
  \\ qspec_tac (`xs`,`xs`)
  \\ Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rename1 `(name, arity, exp)`
  \\ simp [compile_prog_def]
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_CASE_TAC \\ fs []
  \\ TRY (PURE_CASE_TAC \\ fs [])
  \\ fs [MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ TRY (metis_tac [])
  \\ rveq
  \\ imp_res_tac compile_prog_next_mono \\ fs[]
  \\ first_x_assum drule
  \\ TRY (simp[backend_commonTheory.bvl_to_bvi_namespaces_def] \\
    rw[] \\ rpt disj2_tac \\ qexists_tac`0` \\ simp[] \\ NO_TAC)
  \\ disch_then drule
  \\ strip_tac
  >- metis_tac []
  \\ fs []
  \\ rpt disj2_tac
  \\ qexists_tac`k'' + 1` \\ simp[]
QED

val compile_prog_intro = Q.prove (
  `∀xs n ys n1 name.
    ¬MEM name (MAP FST xs) ∧
    free_names n name ∧
    compile_prog n xs = (n1, ys) ⇒
      ¬MEM name (MAP FST ys) ∧
      free_names n1 name
      `,
  Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rpt gen_tac
  \\ simp [compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_TOP_CASE_TAC \\ fs []
  >-
    (rpt strip_tac \\ rveq \\ fs []
    \\ metis_tac [])
  \\ PURE_CASE_TAC \\ fs []
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ metis_tac [is_free_name,more_free_names]);

Theorem compile_prog_ALL_DISTINCT:
   compile_prog n xs = (n1,ys) /\ ALL_DISTINCT (MAP FST xs) /\
   EVERY (free_names n o FST) xs ==>
   ALL_DISTINCT (MAP FST ys) /\
   EVERY (free_names n1 o FST) ys
Proof
  qspec_tac (`n1`,`n1`)
  \\ qspec_tac (`ys`,`ys`)
  \\ qspec_tac (`n`,`n`)
  \\ qspec_tac (`xs`,`xs`)
  \\ Induct
  >- fs [compile_prog_def]
  \\ gen_tac
  \\ PairCases_on `h`
  \\ rename1 `(name, arity, exp)`
  \\ simp [compile_prog_def]
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ PURE_CASE_TAC \\ fs []
  >-
    (rpt strip_tac \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = (_, ys'')` kall_tac
    \\ res_tac
    \\ simp [MAP]
    \\ metis_tac [more_free_names, compile_prog_intro])
  \\ PURE_CASE_TAC \\ fs []
  \\ reverse(rpt strip_tac) \\ rveq
  \\ fs [is_free_name]
  \\ imp_res_tac EVERY_free_names_SUCSUC
  \\ res_tac
  \\ simp []
  >- (
    fs[free_names_def]
    \\ imp_res_tac compile_prog_next_mono
    \\ rveq \\ fs[]
    \\ `bvl_to_bvi_namespaces ≠ 0` by EVAL_TAC
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
    \\ first_x_assum(qspec_then`k+k''+1`mp_tac)
    \\ simp[] )
  \\ reverse conj_tac
  >-
    (CCONTR_TAC \\ fs []
    \\ drule (GEN_ALL compile_prog_MEM)
    \\ disch_then drule
    \\ simp [MEM_MAP]
    \\ fs [EVERY_MEM]
    \\ `0 < bvl_to_bvi_namespaces` by EVAL_TAC \\ fs[]
    \\ gen_tac
    \\ Cases_on `MEM y xs` \\ fs []
    \\ res_tac
    \\ fs [is_free_name])
  \\ CCONTR_TAC \\ fs []
  \\ drule (GEN_ALL compile_prog_MEM)
  \\ disch_then drule
  \\ simp [MEM_MAP]
  \\ metis_tac [compile_prog_intro, more_free_names]
QED

val namespace_rel_def = Define`
  namespace_rel (c1:'a spt) (c2:'a spt) ⇔
    (∀n. n ∈ domain c2 ∧ bvl_num_stubs ≤ n ⇒ if in_ns_2 n then n ∉ domain c1 else n ∈ domain c1) ∧
    (∀n. n ∈ domain c1 ∧ bvl_num_stubs ≤ n ⇒ ¬(in_ns_2 n)) ∧
    (∀n. n ∈ domain c2 ∧ n < bvl_num_stubs ⇒ n ∈ domain c1)`;

val mk_co_def = Define`
  mk_co co = λn.
   let
     ((next,cfg),prog) = co n;
     (next,prog) = compile_prog next prog
   in
     (cfg,prog)`;

val mk_cc_def = Define`
  mk_cc cc = λ(next,cfg) prog.
    let (next,prog) = compile_prog next prog in
      OPTION_MAP (λ(code,data,cfg). (code,data,(next,cfg))) (cc cfg prog)`;

val input_condition_def = Define`
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY ($~ o in_ns_2 o FST) (FILTER ((<=) bvl_num_stubs o FST) prog) ∧
   bvl_num_stubs ≤ next ∧ in_ns_2 next`;

val state_rel_def = Define`
  state_rel s (t:('a,'ffi) bviSem$state) ⇔
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = mk_co s.compile_oracle ∧
    s.compile = mk_cc t.compile ∧
    code_rel s.code t.code ∧
    namespace_rel s.code t.code ∧
    (∀n. let ((next,cfg),prog) = s.compile_oracle n in
            input_condition next prog) ∧
    (∀n. n ∈ domain t.code ∧ in_ns_2 n ⇒ n < FST(FST(s.compile_oracle 0)))`;

Theorem state_rel_const:
   state_rel s t ⇒
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi
Proof
rw[state_rel_def]
QED

Theorem state_rel_with_clock:
   state_rel s t ⇒ state_rel (s with clock := k) (t with clock := k)
Proof
  rw[state_rel_def]
QED

Theorem state_rel_code_rel:
   state_rel s t ⇒ code_rel s.code t.code
Proof
  rw[state_rel_def]
QED

Theorem code_rel_union:
   code_rel x y ∧ code_rel t s ∧
   (*
   (∀a. a ∉ domain x ∧ a ∈ domain s ⇒ a ∉ domain y) ∧
   (∀a. a ∉ domain x ∧ a ∈ domain y ⇒ a ∉ domain s)
   *)
   DISJOINT (domain s) (domain y)
   (* DISJOINT (domain s DIFF domain t) (domain y DIFF domain x) *)
   ⇒
    code_rel (union x t) (union y s)
Proof
  rw[code_rel_def,lookup_union]
  \\ fs[bvlPropsTheory.case_eq_thms]
  \\ fs[IN_DISJOINT,IN_DIFF,domain_lookup]
  \\ res_tac
  \\ TRY(qexists_tac`n` \\ simp[])
  \\ metis_tac[option_nchotomy,NOT_SOME_NONE]
QED

Theorem namespace_rel_union:
   namespace_rel x y ∧ namespace_rel t s ∧
   DISJOINT (domain s) (domain y)
  ⇒
   namespace_rel (union x t) (union y s)
Proof
  rw[namespace_rel_def,domain_union,IN_DISJOINT]
  \\ metis_tac[]
QED

Theorem compile_prog_namespace_rel:
   compile_prog next prog = (next1,prog2) ∧ in_ns_2 next ∧ bvl_num_stubs ≤ next ∧
   EVERY ($~ o in_ns_2 o FST) (FILTER ((<=) bvl_num_stubs o FST) prog) ⇒
   namespace_rel (fromAList prog) (fromAList prog2)
Proof
  rw[namespace_rel_def,EVERY_MEM,domain_fromAList,MEM_MAP,PULL_EXISTS,MEM_FILTER] \\
  imp_res_tac compile_prog_MEM \\
  fs[MEM_MAP,PULL_EXISTS]
  \\ res_tac \\ fs[]
  \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
  \\ CCONTR_TAC \\ fs[] >|[metis_tac[],ALL_TAC,metis_tac[]]
  \\ qpat_x_assum`FST _ = _`(assume_tac o SYM) \\ fs[]
  \\ last_x_assum drule
  \\ rpt(qpat_x_assum`_ + _ = FST _`(assume_tac o SYM) \\ fs[])
QED

Theorem state_rel_do_app_aux:
   do_app_aux op vs s = res ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   ∃res'.
     do_app_aux op vs t = res' ∧
     OPTREL (OPTREL ($= ### state_rel)) res res'
Proof
  simp[do_app_aux_def] \\ strip_tac
  \\ Cases_on`res` \\ fs[]
  >- (
    fs[case_eq_thms,OPTREL_def]
    \\ fs[state_rel_def] )
  \\ imp_res_tac state_rel_const
  \\ fs[case_eq_thms]
  \\ rveq \\ fs[OPTREL_def,quotient_pairTheory.PAIR_REL_THM]
  \\ fs[state_rel_def]
QED

Theorem state_rel_do_app:
   bviSem$do_app op vs s = Rval (r,s') ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   ∃t'.
     bviSem$do_app op vs t = Rval (r,t') ∧
     state_rel s' t'
Proof
  rw[do_app_def]
  \\ imp_res_tac state_rel_do_app_aux \\ fs[]
  \\ first_x_assum(qspec_then`vs`strip_assume_tac)
  \\ fs[case_eq_thms,OPTREL_def] \\ rw[] \\ rfs[]
  \\ fs[PULL_EXISTS]
  \\ rveq \\ fs[quotient_pairTheory.PAIR_REL]
  \\ TRY(pairarg_tac \\ fs[])
  \\ imp_res_tac state_rel_const
  \\ fs[bvlSemTheory.do_app_def,case_eq_thms,bvl_to_bvi_id]
  \\ rveq \\ fs[bvl_to_bvi_id]
  \\ fs[do_app_aux_def]
  \\ fs[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
QED

Theorem state_rel_do_app_err:
   bviSem$do_app op vs s = Rerr e ∧
   state_rel s t ∧ op ≠ Install ∧ (∀n. op ≠ Label n)
   ⇒
   bviSem$do_app op vs t = Rerr e
Proof
  rw[do_app_def]
  \\ imp_res_tac state_rel_do_app_aux \\ fs[]
  \\ first_x_assum(qspec_then`vs`strip_assume_tac)
  \\ fs[case_eq_thms,OPTREL_def] \\ rw[] \\ rfs[]
  \\ imp_res_tac state_rel_const \\ rw[]
  \\ fs[bvi_to_bvl_def]
  \\ fs[bvlSemTheory.do_app_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ fs[case_eq_thms,do_app_aux_def]
QED

Theorem do_app_to_op_state:
   bviSem$do_app (to_op op) vs s = Rval (r,t) ⇒ t = s
Proof
  rw[]
  \\ Cases_on`op` \\ fs[to_op_def,do_app_def,do_app_aux_def,bvlSemTheory.do_app_def]
  \\ fs[case_eq_thms] \\ rw[bvl_to_bvi_id]
  \\ rw[bvl_to_bvi_id]
QED

Theorem scan_expr_check_op:
   scan_expr ts loc [Op op xs] = [(tt, ty, r, SOME opr)] ==>
     IS_SOME (check_op ts opr loc (Op op xs))
Proof
  once_rewrite_tac [scan_expr_def] \\ rw [] \\ fs []
  \\ pop_assum mp_tac
  \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw []
  \\ fs [get_bin_args_def, check_op_def]
QED

Theorem from_op_to_op[simp]:
   from_op (to_op opr) = opr
Proof
  Cases_on `opr` \\ fs [from_op_def, to_op_def]
QED

Theorem scan_expr_op_same:
   scan_expr ts loc [Op op xs] = [(tt, ty, r, SOME opr)] ==>
     op = to_op opr
Proof
  once_rewrite_tac [scan_expr_def]
  \\ rw [check_op_def, opbinargs_def, get_bin_args_def, case_elim_thms,
         case_eq_thms, bool_case_eq, IS_SOME_EXISTS]
  \\ Cases_on `op` \\ fs []
QED

Theorem term_ok_int_extend:
   !ts exp extra.
     term_ok_int ts exp ==> term_ok_int (ts ++ extra) exp
Proof
  recInduct term_ok_int_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [term_ok_int_def] \\ fs []
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ rw [EL_APPEND1]
QED

Theorem term_ok_any_extend:
   !ts list exp extra.
     term_ok_any ts list exp ==> term_ok_any (ts ++ extra) list exp
Proof
  recInduct term_ok_any_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [term_ok_any_def] \\ fs []
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ rw [EL_APPEND1]
  \\ metis_tac [term_ok_int_extend]
QED

Theorem term_ok_extend:
   !ts ty exp extra.
     term_ok ts ty exp ==> term_ok (ts ++ extra) ty exp
Proof
  rw [term_ok_def] \\ CASE_TAC \\ fs []
  \\ metis_tac [term_ok_any_extend, term_ok_int_extend]
QED

Theorem decide_ty_imp:
   decide_ty ty1 ty2 <> Any ==> ty1 <> Any /\ ty2 <> Any
Proof
  Cases_on `ty1` \\ Cases_on `ty2` \\ fs [decide_ty_def]
QED

Theorem op_type_simp:
   (List = op_type op <=> op = Append) /\
   (Any  = op_type op <=> op = Noop)   /\
   (Int  = op_type op <=> op = Plus \/ op = Times)
Proof
  Cases_on `op` \\ rw [op_type_def]
QED

Theorem scan_expr_Op:
   scan_expr ts loc [Op op xs] = [(tt, ty, r, SOME opr)] /\
   rewrite loc n op1 acc ts (Op op xs) = (lr, x) ==>
     op = to_op opr /\
     (op1 = opr <=> lr)
Proof
  rw [scan_expr_def, rewrite_def, case_elim_thms, case_eq_thms, IS_SOME_EXISTS]
  \\ Cases_on `op` \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs []
  \\ TRY (Cases_on `op1`) \\ fs [check_op_def, try_swap_def, opbinargs_def,
                                 get_bin_args_def, IS_SOME_EXISTS, case_eq_thms,
                                 case_elim_thms] \\ rw [] \\ fs []
  \\ fs [apply_op_def]
QED

Theorem is_rec_term_ok:
   !exp ts loc ty.
     (is_rec loc exp ==> ~term_ok ts ty exp) /\
     (term_ok ts ty exp ==> ~is_rec loc exp)
Proof
  Cases \\ simp [is_rec_def, term_ok_def]
  \\ once_rewrite_tac [term_ok_int_def, term_ok_any_def] \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs []
QED

Theorem op_type_lem[simp]:
   op <> Noop <=> op_type op <> Any
Proof
  Cases_on `op` \\ fs [op_type_def]
QED

Theorem evaluate_rewrite_tail:
   ∀xs ^s env1 r t opt s' acc env2 loc ts ty.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel ty opt acc env1 env2 ∧
     state_rel s s' /\
     ty_rel env1 ts ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       ?t'.
       evaluate (xs, env2, s') = (r, t') /\
       state_rel t t' /\
       (opt ⇒
         ∀op n exp arity.
           lookup loc s.code = SOME (arity, exp) ∧
           optimized_code loc arity exp n s'.code op ∧
           op_type op = ty /\
           (∃op1 tt ty r.
             scan_expr ts loc [HD xs] = [(tt, ty, r, SOME op1)] ∧
             ty <> Any /\ op1 <> Noop /\ op_type op1 = op_type op) ⇒
               let (lr, x) = rewrite loc n op acc ts (HD xs) in
                 ?rrr t1 t2.
                 evaluate ([x], env2, s') = (rrr,t1) /\
                 evaluate ([apply_op op (Var acc) (HD xs)],
                   env2, s') = (rrr,t2) /\
                 state_rel t t1 /\
                 state_rel t t2)
Proof
  ho_match_mp_tac evaluate_complete_ind
  \\ ntac 2 (rpt gen_tac \\ strip_tac)
  \\ Cases_on `xs` \\ fs []
  >- (fs [evaluate_def] \\ rw [])
  \\ qpat_x_assum `evaluate _ = _` mp_tac
  \\ reverse (Cases_on `t'`) \\ fs []
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw []
      \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs []
      \\ rw [] \\ fs [])
    \\ qmatch_goalsub_rename_tac `evaluate (y::ys, env1, s2)`
    \\ first_assum (qspecl_then [`[h]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ ntac 2 PURE_TOP_CASE_TAC \\ fs [] \\ rveq
    \\ strip_tac
    \\ first_assum (qspecl_then [`y::ys`,`s2`] mp_tac)
    \\ imp_res_tac evaluate_clock
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ rw [] \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ metis_tac [])
  \\ fs [bviTheory.exp_size_def]
  \\ Cases_on `∃v. h = Var v` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ `LENGTH env1 ≤ LENGTH env2` by metis_tac [env_rel_def, IS_PREFIX_LENGTH]
    \\ fs [env_rel_def, scan_expr_def] \\ rw []
    \\ fs [is_prefix_el])
  \\ Cases_on `∃x1. h = Tick x1` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ imp_res_tac state_rel_const
    \\ rw [] \\ fs []
    >- (fs [rewrite_def, evaluate_def, apply_op_def, ELIM_UNCURRY, env_rel_def])
    \\ first_x_assum (qspecl_then [`[x1]`,`dec_clock 1 s`] mp_tac)
    \\ impl_tac
    >- fs [bviTheory.exp_size_def, evaluate_clock, dec_clock_def]
    \\ `state_rel (dec_clock 1 s) (dec_clock 1 s')` by fs [dec_clock_def, state_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw [] \\ fs []
    \\ rw [rewrite_def] \\ fs []
    \\ first_x_assum drule \\ fs [scan_expr_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw []
    \\ rfs [evaluate_def, apply_op_def, env_rel_def])
  \\ Cases_on `∃x1. h = Raise x1` \\ fs [] \\ rveq
  >-
   (simp [scan_expr_def, evaluate_def, rewrite_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ CASE_TAC \\ fs []
    \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq, PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ rw [] \\ rfs [])
  \\ Cases_on `∃xs x1. h = Let xs x1` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ first_assum (qspecl_then [`xs`,`s`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
    \\ rw [] \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs [] \\ rw []
    >- (fs [rewrite_def, scan_expr_def, ELIM_UNCURRY, evaluate_def,
            apply_op_def, env_rel_def])
    \\ rename1 `evaluate (xs,env1,s) = (Rval zz, s2)`
    \\ sg `env_rel ty opt (LENGTH zz + acc) (zz ++ env1) (zz ++ env2)`
    >-
     (fs [env_rel_def]
      \\ strip_tac
      \\ fs [IS_PREFIX_LENGTH, IS_PREFIX_APPEND, EL_LENGTH_APPEND, EL_APPEND1]
      \\ simp_tac std_ss [ADD_ASSOC] \\ fs []
      \\ rfs [case_eq_thms, case_elim_thms, bool_case_eq, v_ty_cases,
              EL_LENGTH_APPEND, EL_APPEND1, EL_APPEND2])
    \\ qabbrev_tac `ttt = scan_expr ts loc xs`
    \\ sg `ty_rel (zz ++ env1) (MAP (FST o SND) ttt ++
           (case LAST1 ttt of SOME z => FST z | NONE => ts))`
    >-
     (match_mp_tac ty_rel_APPEND
      \\ Q.ISPECL_THEN [`ts`,`loc`,`xs`,`env1`,`ttt`,`s`] mp_tac scan_expr_ty_rel
      \\ disch_then drule \\ fs [] \\ rw []
      \\ qunabbrev_tac `ttt`
      \\ CASE_TAC \\ fs []
      \\ imp_res_tac EVERY_LAST1 \\ fs [])
    \\ qunabbrev_tac `ttt`
    \\ imp_res_tac evaluate_clock
    \\ first_assum (qspecl_then [`[x1]`,`s2`] mp_tac)
    \\ impl_tac >- simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ fs [] \\ rw []
    \\ imp_res_tac evaluate_code_mono \\ fs [] \\ rw [] \\ fs []
    \\ `lookup loc s2.code = lookup loc s.code` by fs [subspt_lookup]
    \\ `optimized_code loc arity exp n t'.code op`
      by fs [optimized_code_def, subspt_lookup]
    \\ first_x_assum (qspec_then `op` mp_tac) \\ fs []
    \\ disch_then drule \\ fs [scan_expr_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ `acc < LENGTH env2` by fs [env_rel_def]
    \\ qhdtm_x_assum `rewrite` mp_tac
    \\ rw [rewrite_def] \\ pairarg_tac \\ fs [] \\ rw []
    \\ `LENGTH xs = LENGTH zz` by metis_tac [evaluate_IMP_LENGTH] \\ rw []
    \\ fs [rewrite_def, evaluate_def, apply_op_def, EL_LENGTH_APPEND, EL_APPEND2]
    \\ rfs [])
  \\ Cases_on `∃x1 x2 x3. h = If x1 x2 x3` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ reverse PURE_TOP_CASE_TAC \\ fs []
    >-
     (strip_tac \\ rveq \\ fs []
      \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ fs [rewrite_def, ELIM_UNCURRY, evaluate_def, apply_op_def, env_rel_def]
      \\ rw [] \\ fs [])
    \\ first_assum (qspecl_then [`[x1]`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ rename1 `evaluate ([x1],_,s) = (_,s2)`
    \\ reverse (Cases_on `opt`) \\ fs []
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ strip_tac
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ strip_tac
    \\ simp [LEFT_EXISTS_AND_THM, CONJ_ASSOC]
    \\ conj_tac
    >-
     (IF_CASES_TAC \\ fs []
      >-
       (first_x_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ imp_res_tac evaluate_clock \\ fs []
        \\ simp [bviTheory.exp_size_def]
        \\ rpt (disch_then drule) \\ fs [])
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ simp [bviTheory.exp_size_def]
      \\ rpt (disch_then drule) \\ fs [])
    \\ rw []
    \\ fs [rewrite_def, evaluate_def, scan_expr_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ sg `ty_rel env1 ti`
    >-
     (drule (GEN_ALL (ISPEC s (Q.GEN `s` (SPEC_ALL scan_expr_ty_rel))))
      \\ rpt (disch_then drule)
      \\ rw [])
    \\ rw []
    >- (* xt ∧ xe optimized *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
        \\ sg `lookup loc s2.code = lookup loc s.code`
        >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
        \\ sg `optimized_code loc arity exp n t'.code op`
        >-
         (imp_res_tac evaluate_code_mono
          \\ fs [optimized_code_def, subspt_lookup])
        \\ fs []
        \\ first_x_assum drule
        \\ disch_then drule \\ fs []
        \\ impl_tac
        >-
         (drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs []
          \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs [] \\ rveq
          \\ imp_res_tac scan_expr_op_type \\ fs []
          \\ Cases_on `ty1` \\ fs [decide_ty_def])
        \\ rw [evaluate_def, apply_op_def] \\ rw [] \\ rfs [env_rel_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ fs []
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule) \\ fs []
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
      \\ first_x_assum drule \\ fs []
      \\ impl_tac
      >-
       (drule rewrite_scan_expr \\ fs [] \\ CASE_TAC \\ fs []
        \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
        \\ drule rewrite_scan_expr \\ fs [] \\ CASE_TAC \\ fs [] \\ rveq
        \\ imp_res_tac scan_expr_op_type \\ fs []
        \\ imp_res_tac scan_expr_not_Noop \\ fs []
        \\ metis_tac [decide_ty_imp, decide_ty_simp])
      \\ rw [evaluate_def, apply_op_def] \\ rw []
      \\ rfs [env_rel_def])
    >- (* xt optimized, xe untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
        \\ sg `lookup loc s2.code = lookup loc s.code`
        >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
        \\ sg `optimized_code loc arity exp n t'.code op`
        >-
         (imp_res_tac evaluate_code_mono
          \\ fs [optimized_code_def, subspt_lookup])
        \\ disch_then drule
        \\ disch_then (qspec_then `T` drule)
        \\ rpt (disch_then drule)
        \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
        \\ first_x_assum drule \\ fs []
        \\ impl_tac
        >-
         (qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
          \\ drule rewrite_scan_expr \\ fs []
          \\ CASE_TAC \\ fs [] \\ rveq
          \\ metis_tac [decide_ty_imp, decide_ty_simp])
        \\ rw [evaluate_def, apply_op_def] \\ rw []
        \\ rfs [env_rel_def])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ rpt (disch_then drule) \\ fs []
      \\ `acc < LENGTH env2` by fs [env_rel_def]
      \\ rw [evaluate_def, apply_op_def] \\ rw [] \\ rfs [] \\ fs []
      \\ rpt (CASE_TAC \\ rw []) \\ fs []
      \\ imp_res_tac do_app_to_op_state \\ fs [])
    >- (* xe optimized, xt untouched *)
     (qpat_x_assum `_ = (r, t)` mp_tac
      \\ IF_CASES_TAC \\ fs []
      >-
       (strip_tac
        \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
        \\ impl_tac
        >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
        \\ rpt (disch_then drule) \\ fs []
        \\ `acc < LENGTH env2` by fs [env_rel_def]
        \\ rw [evaluate_def, apply_op_def] \\ rw []
        \\ rpt (CASE_TAC \\ rw []) \\ fs []
        \\ imp_res_tac do_app_to_op_state \\ fs [])
      \\ IF_CASES_TAC \\ fs [] \\ rw []
      \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
      \\ sg `lookup loc s2.code = lookup loc s.code`
      >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup])
      \\ sg `optimized_code loc arity exp n t'.code op`
      >-
       (imp_res_tac evaluate_code_mono
        \\ fs [optimized_code_def, subspt_lookup])
      \\ disch_then drule
      \\ disch_then (qspec_then `T` drule)
      \\ rpt (disch_then drule)
      \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
      \\ first_x_assum drule \\ fs []
      \\ impl_tac
      >-
       (drule rewrite_scan_expr \\ fs []
        \\ qpat_x_assum `rewrite _ _ _ _ _ x3 = _` kall_tac
        \\ drule rewrite_scan_expr \\ fs []
        \\ rw [case_elim_thms]
        \\ drule scan_expr_op_type \\ fs [] \\ rw []
        \\ metis_tac [decide_ty_imp, decide_ty_simp])
      \\ rw [evaluate_def, apply_op_def] \\ rw []
      \\ rfs [env_rel_def])
    \\ qpat_x_assum `_ = (r, t)` mp_tac
    \\ IF_CASES_TAC \\ fs []
    >-
     (strip_tac
      \\ first_assum (qspecl_then [`[x2]`,`s2`] mp_tac)
      \\ impl_tac
      >-
       (imp_res_tac evaluate_clock
        \\ simp [bviTheory.exp_size_def])
      \\ rpt (disch_then drule)
      \\ rw [evaluate_def, apply_op_def]
      \\ `acc < LENGTH env2` by fs[env_rel_def]
      \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ CASE_TAC \\ rw[]
      \\ imp_res_tac do_app_to_op_state \\ fs[])
    \\ IF_CASES_TAC \\ fs [] \\ rw []
    \\ first_assum (qspecl_then [`[x3]`,`s2`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [bviTheory.exp_size_def])
    \\ rpt (disch_then drule)
    \\ rw [evaluate_def, apply_op_def]
    \\ `acc < LENGTH env2` by fs[env_rel_def]
    \\ rpt (CASE_TAC \\ rw[]) \\ fs []
    \\ imp_res_tac do_app_to_op_state \\ fs[])
  \\ Cases_on `∃xs op. h = Op op xs` \\ fs [] \\ rveq
  >-
   (simp [evaluate_def]
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ strip_tac
    \\ simp [LEFT_EXISTS_AND_THM, CONJ_ASSOC]
    \\ conj_tac
    >-
     (first_x_assum (qspecl_then [`xs`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ `env_rel ty F acc env1 env2` by fs [env_rel_def]
      \\ rpt (disch_then drule) \\ fs []
      \\ impl_tac >- (strip_tac \\ fs [])
      \\ rw [] \\ fs []
      \\ Cases_on `op = Install`
      >- (
        reverse (fs[bvlPropsTheory.case_eq_thms] \\ rveq \\ fs[do_app_def])
        >-
         (fs[do_install_def,bvlPropsTheory.case_eq_thms]
          \\ rveq \\ fs[]
          \\ rpt(pairarg_tac \\ fs[bvlPropsTheory.case_eq_thms])
          \\ rveq \\ fs[])
        \\ fs[do_install_def,bvlPropsTheory.case_eq_thms] \\ rveq \\ fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
        \\ qhdtm_x_assum`state_rel`mp_tac
        \\ simp[state_rel_def,mk_cc_def,mk_co_def]
        \\ strip_tac \\ fs[]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq
        \\ rename1`compile_prog next1 prog1 = (next2, prog2)`
        \\ `LENGTH prog1 ≤ LENGTH prog2` by metis_tac[compile_prog_LENGTH,SND,GREATER_EQ]
        \\ `prog1 ≠ []` by (strip_tac \\ fs[])
        \\ `prog2 ≠ []` by (strip_tac \\ fs[])
        \\ fs[bvlPropsTheory.case_eq_thms,pair_case_eq,PULL_EXISTS]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ fs[shift_seq_def]
        \\ qpat_x_assum`_ = FST _`(assume_tac o SYM) \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ simp[RIGHT_EXISTS_AND_THM]
        \\ simp[LEFT_EXISTS_AND_THM]
        \\ qmatch_assum_rename_tac`code_rel src.code tgt.code`
        \\ qmatch_assum_abbrev_tac`compile_prog next1 prog1 = (next2, prog2)`
        \\ `DISJOINT (domain src.code) (set (MAP FST prog1))` by simp[Abbr`prog1`]
        \\ `in_ns_2 next1` by (fs[input_condition_def] \\ rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[]))
        \\ qpat_x_assum`compile_prog next1 prog1 = _`assume_tac
        \\ drule (GEN_ALL compile_prog_code_rel)
        \\ impl_tac
        >- (
          simp[Abbr`prog1`]
          \\ fs[input_condition_def]
          \\ rpt(first_x_assum(qspec_then`0`mp_tac) \\ simp[] ))
        \\ strip_tac
        \\ `∀n. in_ns_2 n ∧ bvl_num_stubs <= n ⇒ ¬MEM n (MAP FST prog1)`
        by (
          rw[] \\ fs[input_condition_def] \\
          qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac) \\
          simp[] \\
          strip_tac \\ fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_FILTER]
          \\ metis_tac[] )
        \\ conj_asm1_tac
        >- (
          fs[IN_DISJOINT]
          \\ qx_gen_tac`n`
          \\ spose_not_then strip_assume_tac
          \\ qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac)
          \\ simp[input_condition_def]
          \\ CCONTR_TAC \\ fs[]
          \\ Cases_on`in_ns_2 n ∧ bvl_num_stubs <= n`
          >- (
            `¬MEM n (MAP FST prog1)` by ( metis_tac[] )
            \\ drule (GEN_ALL compile_prog_MEM)
            \\ disch_then drule \\ simp[]
            \\ CCONTR_TAC \\ fs[]
            \\ res_tac \\ fs[] )
          \\ qhdtm_x_assum`namespace_rel`mp_tac
          \\ simp[namespace_rel_def]
          \\ spose_not_then strip_assume_tac
          \\ `n ∈ domain src.code` by metis_tac[NOT_LESS]
          \\ drule (GEN_ALL compile_prog_MEM)
          \\ disch_then drule
          \\ strip_tac >- metis_tac[]
          \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def]
          \\ res_tac \\ fs[])
        \\ qpat_x_assum`∀n. _ (src.compile_oracle n)`(qspec_then`0`mp_tac)
        \\ simp[] \\ strip_tac
        \\ conj_asm1_tac
        >- ( drule compile_prog_ALL_DISTINCT \\ fs[input_condition_def] )
        \\ conj_tac >- (
          Cases_on`prog2` \\ fs[compile_prog_def,Abbr`prog1`]
          \\ Cases_on`prog` \\ fs[compile_prog_def,case_eq_thms]
          \\ pairarg_tac \\ fs[] \\ rw[] )
        \\ conj_asm1_tac
        >- (
          match_mp_tac code_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM] )
        \\ `namespace_rel (fromAList prog1) (fromAList prog2)`
        by (
          match_mp_tac (GEN_ALL compile_prog_namespace_rel)
          \\ asm_exists_tac \\ fs[input_condition_def])
        \\ conj_asm1_tac
        >- (
          match_mp_tac namespace_rel_union
          \\ fs[domain_fromAList,DISJOINT_SYM])
        \\ simp[domain_union]
        \\ imp_res_tac compile_prog_next_mono
        \\ rveq \\ rw[]
        >- ( res_tac \\ simp[] )
        \\ fs[domain_fromAList,input_condition_def]
        \\ drule (GEN_ALL compile_prog_MEM)
        \\ disch_then drule
        \\ strip_tac \\ fs[]
        \\ Cases_on`n < bvl_num_stubs` >- decide_tac
        \\ fs[NOT_LESS] \\ metis_tac[])
      \\ Cases_on`∃n. op = Label n`
      >- (
        fs[] \\ rveq \\
        fs[do_app_def,do_app_aux_def] \\
        imp_res_tac state_rel_code_rel \\
        imp_res_tac code_rel_domain \\
        fs[SUBSET_DEF] \\
        fs[case_eq_thms] \\ rveq \\ fs[] ) \\ fs[]
      \\ fs[case_eq_thms] \\ rveq \\ fs[]
      \\ imp_res_tac state_rel_do_app \\ fs[]
      \\ imp_res_tac state_rel_do_app_err \\ fs[])
    \\ rw []
    \\ pairarg_tac \\ fs []
    \\ drule (GEN_ALL scan_expr_Op)
    \\ disch_then drule \\ rw []
    \\ drule scan_expr_op_type \\ rw []
    \\ rename1 `op_type op1 = op_type op2` \\ fs [] \\ rw []
    \\ `env_rel (op_type op') F acc env1 env2` by fs [env_rel_def]
    \\ first_assum (qspecl_then [`xs`, `s`] mp_tac)
    \\ impl_tac >- fs [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac >- fs [bool_case_eq, case_eq_thms, case_elim_thms]
    \\ rw []
    \\ qhdtm_x_assum `rewrite` mp_tac
    \\ simp [rewrite_def]
    \\ sg `to_op op2 <> Install /\ (!n. to_op op2 <> Label n)`
    >- (Cases_on `op2` \\ fs [to_op_def])
    \\ sg `to_op op1 <> Install /\ (!n. to_op op1 <> Label n)`
    >- (Cases_on `op1` \\ fs [to_op_def])
    \\ sg `to_op op' <> Install /\ (!n. to_op op' <> Label n)`
    >- (Cases_on `op'` \\ fs [to_op_def])
    \\ PURE_TOP_CASE_TAC \\ fs []
    >-
     (rw [apply_op_def, evaluate_def]
      \\ rw [evaluate_def]
      \\ `acc < LENGTH env2` by fs [env_rel_def] \\ fs []
      \\ every_case_tac \\ fs [] \\ rw []
      \\ imp_res_tac do_app_to_op_state \\ fs [])
    \\ drule (GEN_ALL check_op_thm)
    \\ once_rewrite_tac [METIS_PROVE [] ``p \/ q <=> ~p ==> q``]
    \\ strip_tac \\ rveq \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    >- (rw [apply_op_def, evaluate_def] \\ imp_res_tac do_app_to_op_state \\ fs [])
    \\ rw [] \\ fs []
    \\ qhdtm_x_assum `scan_expr` mp_tac
    \\ fs [rewrite_def, scan_expr_def, opbinargs_def]
    \\ rename1 `op_type op`
    \\ Cases_on `op = Noop`
    >- fs [case_eq_thms, case_elim_thms, bool_case_eq, PULL_EXISTS]
    \\ strip_tac \\ rveq
    (*\\ qhdtm_x_assum `check_op` mp_tac*)
    (*\\ simp [check_op_def, opbinargs_def, get_bin_args_def]*)
    (*\\ rw []*)
    \\ rename1 `is_rec loc f`
    \\ sg `∃ticks args. f = Call ticks (SOME loc) args NONE`
    >-
     (Cases_on `f` \\ fs [is_rec_def]
      \\ rename1 `_ /\ z = NONE`
      \\ Cases_on `z` \\ fs [is_rec_def])
    \\ rw []
    \\ simp [args_from_def, push_call_def, apply_op_def]
    (*\\ rename1 `evaluate ([_;e2],env1,s)`*)
    \\ Cases_on `evaluate ([y], env1, s)`
    \\ drule (GEN_ALL (ISPEC s (Q.GEN `s` (SPEC_ALL term_ok_SING))))
    \\ rpt (disch_then drule) \\ rw []
    \\ rename1 `([y], env1, s)`
    \\ sg `ty_rel env2 (ts ++ (REPLICATE (LENGTH env2 - LENGTH env1) Any))`
    >-
     (fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ `LENGTH ts < LENGTH env2` by fs [env_rel_def, IS_PREFIX_LENGTH]
      \\ rw []
      \\ Cases_on `n' < LENGTH ts`
      \\ TRY
       (imp_res_tac is_prefix_el \\ rfs [env_rel_def]
        \\ fs [EL_REPLICATE, EL_LENGTH_APPEND, EL_APPEND1, EL_APPEND2]
        \\ `n' < LENGTH ts` by fs []
        \\ first_x_assum drule
        \\ rw []
        \\ drule is_prefix_el
        \\ fs [IS_PREFIX_LENGTH]
        \\ disch_then drule
        \\ rw [] \\ metis_tac [])
      \\ fs [EL_APPEND2]
      \\ `n' - LENGTH ts < LENGTH env2 - LENGTH ts` by fs []
      \\ fs [EL_REPLICATE])
    \\ drule term_ok_extend
    \\ disch_then (qspec_then `REPLICATE (LENGTH env2 - LENGTH env1) Any` mp_tac)
    \\ rw []
    \\ Cases_on `evaluate ([y], env2, s')`
    \\ drule (GEN_ALL term_ok_SING)
    \\ rpt (disch_then drule) \\ rw []
    \\ rename1 `evaluate ([y],env2,s') = (Rval [v1],_)`
    \\ qmatch_assum_abbrev_tac `xs <> A ==> _`
    \\ Cases_on `xs = A` \\ fs [Abbr`A`] \\ rveq
    \\ qpat_x_assum `evaluate ([_;_],env1,s) = _` mp_tac
    \\ qmatch_goalsub_abbrev_tac `_ ==> goal`
    \\ simp [evaluate_def]
    \\ CASE_TAC \\ fs []
    \\ rename1 `_ = (res_args, st_args)`
    \\ strip_tac
    \\ `res_args <> Rerr (Rabort Rtype_error)`
      by (fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq] \\ rw [])
    \\ qunabbrev_tac `goal`
    \\ simp [evaluate_def]
    \\ once_rewrite_tac [evaluate_APPEND]
    \\ `acc < LENGTH env2` by fs [env_rel_def] \\ fs []
    \\ first_assum (qspecl_then [`args`,`s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ rpt (disch_then drule) \\ fs [] \\ rw [] \\ fs []
    \\ simp [evaluate_def] \\ rfs [] \\ fs []
    \\ `v = v1` by
     (first_x_assum (qspecl_then [`[y]`, `s`] mp_tac)
      \\ simp [bviTheory.exp_size_def]
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ Cases_on `evaluate ([y],env1,s)`
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ first_x_assum (qspec_then `s` assume_tac)
      \\ first_x_assum (qspec_then `s'` assume_tac)
      \\ rfs [] \\ rw [])
    \\ rveq \\ fs []
    \\ rename1 `state_rel st_args t_args`
    \\ `?val.
           do_app (to_op op) [v; EL acc env2] t_args =
             Rval (val, t_args) /\
           case op_type op of
             Int => ?k. val = Number k
           | List => ?ys. v_to_list val = SOME ys
           | Any => T` by
     (Cases_on `op` \\ fs [to_op_def, from_op_def, op_type_def]
      \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, env_rel_def]
      \\ fs [bvl_to_bvi_id])
    \\ fs []
    \\ (reverse (Cases_on `res_args`) \\ fs []
        >- (rw [] \\ fs [] \\ rw [] \\ fs []))
    \\ `code_rel st_args.code t_args.code`
      by (imp_res_tac state_rel_code_rel \\ fs [])
    \\ pop_assum mp_tac
    \\ rw [code_rel_def]
    \\ fs [find_code_def]
    \\ (Cases_on `lookup loc st_args.code` \\ fs [] >- (rw [] \\ fs []))
    \\ PairCases_on `x`
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_code_mono
    \\ fs [subspt_lookup, optimized_code_def]
    \\ rfs [] \\ rveq
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ first_x_assum drule \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ disch_then (qspec_then `op` mp_tac) \\ fs []
    \\ simp [check_exp_def]
    \\ strip_tac \\ fs []
    \\ (reverse IF_CASES_TAC \\ fs [] >- (rw [] \\ fs []))
    \\ (IF_CASES_TAC \\ fs []
        >-
         (imp_res_tac state_rel_const \\ fs []
          \\ rveq \\ rfs [] \\ fs [] \\ rw []
          \\ `code_rel st_args.code t_args.code` by imp_res_tac state_rel_code_rel
          \\ pop_assum mp_tac
          \\ simp [code_rel_def]
          \\ disch_then (qspec_then `loc` drule)
          \\ rw [check_exp_def, compile_exp_def]
          \\ pairarg_tac \\ fs []
          \\ fs [state_rel_with_clock]))
    \\ `~(st_args.clock < ticks+1)` by (imp_res_tac state_rel_const \\ fs[])
    \\ fs []
    \\ qpat_x_assum `_ = (q,_)` mp_tac
    \\ PURE_CASE_TAC \\ fs []
    \\ strip_tac
    \\ rename1 `evaluate ([exp], a, _) = (res_exp, st_exp)`
    \\ `res_exp <> Rerr (Rabort Rtype_error)` by
      (fs [pair_case_eq, case_eq_thms, case_elim_thms] \\ rw [])
    \\ rveq \\ rfs []
    \\ `env_rel (op_type op) T (LENGTH a) a (a ++ [val])`
      by (fs [env_rel_def]
          \\ Cases_on `op` \\ fs [op_type_def, EL_APPEND1, EL_LENGTH_APPEND])
    \\ `ty_rel a (REPLICATE (LENGTH a) Any)`
      by fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) st_args`] mp_tac)
    \\ (impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def]))
    \\ `state_rel (dec_clock (ticks+1) st_args) (dec_clock (ticks+1) t_args)`
      by (imp_res_tac state_rel_const \\ fs [state_rel_with_clock,dec_clock_def])
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ first_x_assum (qspecl_then [`op`,`n`] mp_tac) \\ fs []
    \\ (impl_tac >- (imp_res_tac evaluate_code_mono \\ fs [subspt_lookup]))
    \\ pairarg_tac \\ fs []
    \\ simp [apply_op_def]
    \\ strip_tac
    \\ qhdtm_x_assum `compile_exp` mp_tac
    \\ simp [compile_exp_def, check_exp_def] \\ rw [] \\ fs []
    \\ `env_rel (op_type op) T (LENGTH a) a (a ++ [op_id_val op] ++ a)`
      by (fs [env_rel_def]
          \\ Cases_on `op` \\ fs [op_id_val_def, op_type_def, EL_APPEND1,
                                  EL_LENGTH_APPEND, IS_PREFIX_APPEND,
                                  bvlSemTheory.v_to_list_def])
    \\ first_x_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) st_args`] mp_tac)
    \\ (impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def]))
    \\ rpt (disch_then drule) \\ fs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `loc` mp_tac) \\ rw []
    \\ (Cases_on `compile_exp loc n' (LENGTH a) exp` \\ fs []
        >-
         (fs [compile_exp_def, check_exp_def]
          \\ rfs []
          \\ pairarg_tac \\ fs []))
    \\ PairCases_on `x` \\ fs []
    \\ first_x_assum (qspecl_then [`op`, `n'`] mp_tac) \\ fs []
    \\ pairarg_tac \\ fs []
    \\ simp [evaluate_def, apply_op_def]
    \\ rw [] \\ rfs [] \\ fs []
    \\ qpat_x_assum `evaluate ([_;_],_,_) = _` mp_tac
    \\ simp [evaluate_def, find_code_def]
    \\ fs [compile_exp_def, check_exp_def] \\ rfs []
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ fs [evaluate_let_wrap] \\ rfs []
    \\ qpat_x_assum `_ = (rrr,_)` mp_tac
    \\ simp [evaluate_def]
    \\ strip_tac
    \\ (reverse (Cases_on `res_exp`) \\ fs []
        >-
         (rw [] \\ fs []
          \\ rw [] \\ fs []
          \\ pop_assum mp_tac
          \\ rpt (PURE_CASE_TAC \\ fs []) \\ rw []))
    \\ fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1]
    \\ rw [] \\ fs []
    \\ drule (INST_TYPE [alpha|->``:num#'c``,beta|->``:'ffi``] scan_expr_ty_rel)
    \\ rpt (disch_then drule) \\ fs [] \\ rw []
    \\ pop_assum mp_tac
    \\ simp [ty_rel_def] \\ rw []
    \\ Cases_on `op` \\ fs [to_op_def, op_type_def, op_id_val_def] \\ rw []
    \\ fs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, bvlSemTheory.v_to_list_def]
    \\ fs [bvl_to_bvi_id] \\ rveq \\ fs []
    \\ fs [bvl_to_bvi_id]
    \\ rfs [] \\ rveq
    \\ TRY intLib.COOPER_TAC
    \\ fs [bvl_to_bvi_id] \\ rw []
    \\ fs [check_op_def, try_swap_def, opbinargs_def, get_bin_args_def, apply_op_def]
    \\ rw [] \\ metis_tac [is_rec_term_ok])
  \\ Cases_on `∃ticks dest xs hdl. h = Call ticks dest xs hdl` \\ fs [] \\ rveq
  >-
   (simp [scan_expr_def, evaluate_def]
    \\ IF_CASES_TAC >- fs []
    \\ `dest = NONE ⇒ ¬IS_SOME hdl` by fs []
    \\ qpat_x_assum `¬(_)` kall_tac
    \\ TOP_CASE_TAC
    \\ first_assum (qspecl_then [`xs`, `s`] mp_tac)
    \\ simp [bviTheory.exp_size_def]
    \\ sg `env_rel ty F acc env1 env2` >- fs [env_rel_def]
    \\ rpt (disch_then drule) \\ fs []
    \\ strip_tac
    \\ reverse PURE_TOP_CASE_TAC \\ fs [] >- (rw [] \\ fs [])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >-
     (rw [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq, PULL_EXISTS]
      \\ rename1 `state_rel t t'`
      \\ `code_rel t.code t'.code` by (imp_res_tac state_rel_code_rel \\ fs [])
      \\ Cases_on `find_code dest a t'.code` \\ fs [] \\ rveq
      >-
       (Cases_on `dest` \\ fs []
        \\ metis_tac [code_rel_find_code_NONE, code_rel_find_code_SOME])
      \\ PairCases_on `x` \\ fs [state_rel_def])
    \\ rename1 `state_rel t1 t2`
    \\ rename1 `([exp],args, _)`
    \\ Cases_on `dest` \\ fs []
    >-
     (strip_tac
      \\ PURE_TOP_CASE_TAC \\ fs []
      >- metis_tac [evaluate_code_mono, code_rel_find_code_NONE, state_rel_code_rel]
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ qpat_x_assum `_ = (r, t)` mp_tac
      \\ PURE_TOP_CASE_TAC \\ fs []
      \\ rpt (qpat_x_assum `find_code _ _ _ = _` mp_tac)
      \\ simp [find_code_def]
      \\ ntac 3 (CASE_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ ntac 2 (CASE_TAC \\ fs [])
      \\ strip_tac \\ rveq
      \\ imp_res_tac state_rel_code_rel \\ fs []
      \\ pop_assum kall_tac
      \\ qpat_assum `code_rel _ _` mp_tac
      \\ simp_tac std_ss [code_rel_def]
      \\ disch_then drule
      \\ simp [compile_exp_def]
      \\ CASE_TAC \\ fs []
      >-
       (strip_tac \\ rveq
        \\ sg `env_rel ty F (LENGTH (FRONT a)) (FRONT a) (FRONT a)`
        >- fs [env_rel_def]
        \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
        >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
        \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`] mp_tac)
        \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [dec_clock_def])
        \\ simp []
        \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1) t2)`
        >- (imp_res_tac state_rel_const \\ fs [dec_clock_def, state_rel_with_clock])
        \\ rpt (disch_then drule) \\ fs []
        \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq, PULL_EXISTS]
        \\ rw [] \\ fs [state_rel_def])
      \\ strip_tac
      \\ pairarg_tac \\ fs [] \\ rveq
      \\ IF_CASES_TAC \\ fs []
      >- (imp_res_tac state_rel_const \\ fs [])
      \\ rename1 `let_wrap qs _ _`
      \\ `qs = LENGTH (FRONT a)` by fs [LENGTH_FRONT]
      \\ pop_assum (fn th => fs [th])
      \\ imp_res_tac scan_expr_not_Noop
      \\ fs [evaluate_let_wrap]
      \\ sg `env_rel (op_type x) T (LENGTH (FRONT a)) (FRONT a)
                                   (FRONT a ++ [op_id_val x] ++ FRONT a)`
      >-
        (fs [env_rel_def, EL_LENGTH_APPEND, EL_APPEND1, IS_PREFIX_APPEND]
         \\ Cases_on `x` \\ fs [op_id_val_def, op_type_def, v_ty_cases,
                                bvlSemTheory.v_to_list_def])
      \\ sg `ty_rel (FRONT a) (REPLICATE (LENGTH (FRONT a)) Any)`
      >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
      \\ Cases_on `q' = Rerr (Rabort Rtype_error)`
      >- fs [pair_case_eq, bool_case_eq, case_eq_thms, case_elim_thms]
      \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [dec_clock_def])
      \\ simp []
      \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1) t2)`
      >- (imp_res_tac state_rel_const \\ fs [dec_clock_def, state_rel_with_clock])
      \\ rpt (disch_then drule) \\ fs []
      \\ disch_then (qspec_then `n` mp_tac) \\ fs []
      \\ strip_tac
      \\ first_x_assum (qspecl_then [`x`,`n'`] mp_tac) \\ rw [] \\ fs []
      \\ rfs [optimized_code_def, compile_exp_def, check_exp_def]
      \\ fs [apply_op_def]
      \\ rfs [] \\ rveq
      \\ fs [evaluate_def, apply_op_def, EL_LENGTH_APPEND, EL_APPEND1]
      \\ fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
      \\ fs [PULL_EXISTS] \\ rw []
      \\ drule (GEN_ALL (INST_TYPE [alpha|->``:num#'c``,beta|->``:'ffi``] (SPEC_ALL scan_expr_ty_rel)))
      \\ rpt (disch_then drule) \\ strip_tac \\ fs []
      \\ pop_assum mp_tac \\ fs [] \\ once_rewrite_tac [ty_rel_def] \\ strip_tac
      \\ fs []
      \\ Cases_on `x`
      \\ fs [to_op_def, op_id_val_def, do_app_def, do_app_aux_def,
             bvlSemTheory.do_app_def, bvl_to_bvi_id, op_type_def]
      \\ fs [bvlSemTheory.v_to_list_def]
      \\ fs [case_eq_thms, case_elim_thms, pair_case_eq, bool_case_eq] \\ rw []
      \\ fs [bvl_to_bvi_id, list_to_v_imp])
    \\ PURE_TOP_CASE_TAC \\ fs [] \\ strip_tac
    \\ PURE_TOP_CASE_TAC \\ fs []
    >- (imp_res_tac state_rel_code_rel \\ metis_tac [code_rel_find_code_SOME])
    \\ PURE_TOP_CASE_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- (imp_res_tac state_rel_const \\ fs [])
    \\ first_assum (qspecl_then [`[exp]`, `dec_clock (ticks+1) t1`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ simp [dec_clock_def])
    \\ `env_rel ty F acc args args` by fs [env_rel_def]
    \\ sg `ty_rel args (REPLICATE (LENGTH args) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ sg `state_rel (dec_clock (ticks+1) t1) (dec_clock (ticks+1) t2)`
    >- (imp_res_tac state_rel_const \\ fs [state_rel_with_clock, dec_clock_def])
    \\ rpt (disch_then drule) \\ fs []
    \\ impl_tac
    >- fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
    \\ rpt (qhdtm_x_assum `find_code` mp_tac)
    \\ simp [find_code_def]
    \\ ntac 4 (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac state_rel_code_rel
    \\ qpat_assum `code_rel t1.code _` mp_tac
    \\ simp_tac std_ss [code_rel_def]
    \\ disch_then drule \\ fs []
    \\ simp [compile_exp_def]
    \\ CASE_TAC \\ fs []
    >-
     (fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq,
          PULL_EXISTS] \\ rw []
      \\ rename1 `([z], aa::env1, s2)`
      \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
      \\ impl_tac
      >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
      \\ `env_rel ty F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
      \\ sg `ty_rel (aa::env1) (Any::ts)`
      >- fs [ty_rel_def, LIST_REL_EL_EQN]
      \\ imp_res_tac state_rel_const \\ fs []
      \\ rpt (disch_then drule) \\ rw [])
    \\ rw []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ imp_res_tac scan_expr_not_Noop \\ fs []
    \\ simp [evaluate_let_wrap]
    \\ first_assum (qspecl_then [`[exp]`,`dec_clock (ticks+1) t1`] mp_tac)
    \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
    \\ sg `env_rel (op_type x') T (LENGTH a) a (a ++ [op_id_val x'] ++ a)`
    >-
     (Cases_on `x'`
      \\ fs [op_id_val_def, op_type_def, env_rel_def, EL_LENGTH_APPEND,
             EL_APPEND1, IS_PREFIX_APPEND, bvlSemTheory.v_to_list_def])
    \\ sg `ty_rel a (REPLICATE (LENGTH a) Any)`
    >- fs [ty_rel_def, LIST_REL_EL_EQN, EL_REPLICATE]
    \\ rpt (disch_then drule) \\ fs []
    \\ disch_then (qspec_then `x` mp_tac)
    \\ impl_tac >- fs [pair_case_eq, case_eq_thms, case_elim_thms, bool_case_eq]
    \\ simp [optimized_code_def, compile_exp_def, check_exp_def, apply_op_def, evaluate_def]
    \\ rw []
    \\ first_x_assum (qspecl_then [`x'`,`n`] mp_tac)
    \\ simp [optimized_code_def,compile_exp_def, check_exp_def]
    \\ simp [apply_op_def, evaluate_def]
    \\ reverse (PURE_CASE_TAC \\ fs [])
    >-
     (fs [case_eq_thms, PULL_EXISTS, pair_case_eq, case_elim_thms] \\ rw []
      \\ rename1 `([z], aa::env1, s2)`
      \\ qpat_x_assum `code_rel t1.code _` mp_tac
      \\ simp [code_rel_def]
      \\ disch_then drule \\ fs []
      \\ rw [compile_exp_def, check_exp_def]
      \\ pairarg_tac \\ fs [] \\ rw []
      \\ first_x_assum (qspecl_then [`[z]`,`s2`] mp_tac)
      \\ impl_tac >- (imp_res_tac evaluate_clock \\ fs [dec_clock_def])
      \\ `env_rel ty F (LENGTH env1 + 1) (aa::env1) (aa::env2)` by fs [env_rel_def]
      \\ `ty_rel (aa::env1) (Any::ts)` by fs [ty_rel_def]
      \\ rpt (disch_then drule) \\ rw [])
    \\ rw [] \\ fs []
    \\ qpat_x_assum `_ = (rrr,_)` mp_tac
    \\ simp [EL_LENGTH_APPEND, EL_APPEND1]
    \\ drule (GEN_ALL (INST_TYPE [alpha|->``:num#'c``,beta|->``:'ffi``] (SPEC_ALL scan_expr_ty_rel)))
    \\ rpt (disch_then drule) \\ fs [] \\ strip_tac
    \\ pop_assum mp_tac
    \\ simp [ty_rel_def] \\ strip_tac \\ fs []
    \\ Cases_on `x'`
    \\ fs [to_op_def, op_type_def, do_app_def, do_app_aux_def, op_id_val_def,
           bvlSemTheory.do_app_def, bvl_to_bvi_id, bvlSemTheory.v_to_list_def]
    \\ rw [] \\ fs []
    \\ fs [list_to_v_imp]
    \\ fs [bvl_to_bvi_id])
  \\ Cases_on `h` \\ fs []
QED

Theorem evaluate_compile_prog:
   input_condition next prog ∧
   (∀n next cfg prog. co n = ((next,cfg),prog) ⇒ input_condition next prog) ∧
   (∀n. MEM n (MAP FST (SND (compile_prog next prog))) ∧ in_ns_2 n ⇒ n < FST (FST (co 0))) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) co (mk_cc cc) k) = (r, s) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog))) (mk_co co) cc k)
      = (r, s2) ∧
     state_rel s s2
Proof
  rw []
  \\ qmatch_asmsub_abbrev_tac `(es,env,st1)`
  \\ `env_rel ty F 0 env env` by fs [env_rel_def]
  \\ qabbrev_tac `ts: v_ty list = []`
  \\ `ty_rel env ts` by fs [ty_rel_def, Abbr`ts`]
  \\ Cases_on `compile_prog next prog` \\ fs []
  \\ drule (GEN_ALL compile_prog_code_rel)
  \\ simp[]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`(es,env,st2)`
  \\ `state_rel st1 st2`
  by (
    simp[state_rel_def,Abbr`st1`,Abbr`st2`,domain_fromAList]
    \\ rfs[input_condition_def]
    \\ reverse conj_tac >- (
      rw[] \\
      last_x_assum(qspec_then`n`mp_tac)
      \\ pairarg_tac \\ fs[] )
    \\ match_mp_tac (GEN_ALL compile_prog_namespace_rel)
    \\ asm_exists_tac \\ fs[] )
  \\ drule evaluate_rewrite_tail
  \\ disch_then (qspec_then `F` drule)
  \\ rpt (disch_then drule) \\ fs []
QED

Theorem compile_prog_semantics:
   input_condition n prog ∧
   (∀k n cfg prog. co k = ((n,cfg),prog) ⇒ input_condition n prog) ∧
   (∀k. MEM k (MAP FST prog2) ∧ in_ns_2 k ⇒ k < FST(FST (co 0))) ∧
   SND (compile_prog n prog) = prog2 ∧
   semantics ffi (fromAList prog) co (mk_cc cc) start ≠ ffi$Fail ⇒
   semantics ffi (fromAList prog) co (mk_cc cc) start =
   semantics ffi (fromAList prog2) (mk_co co) cc start
Proof
   simp [GSYM AND_IMP_INTRO]
   \\ ntac 4 strip_tac
   \\ fs[AND_IMP_INTRO]
   \\ simp [Ntimes semantics_def 2]
   \\ IF_CASES_TAC \\ fs []
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac >- (
     gen_tac \\ strip_tac \\ rveq \\ simp []
     \\ simp [semantics_def]
     \\ IF_CASES_TAC \\ fs [] >- (
       qpat_x_assum`_ = (r,s)`kall_tac
       \\ first_assum(qspec_then`k'`mp_tac)
       \\ disch_then(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
       \\ drule (GEN_ALL evaluate_compile_prog)
       \\ rpt(disch_then drule)
       \\ first_x_assum (qspec_then `k'` strip_assume_tac)
       \\ rfs [] \\ CCONTR_TAC \\ fs [] \\ rfs[] \\ fs[] \\ rfs[])
     \\ DEEP_INTRO_TAC some_intro \\ simp []
     \\ conj_tac >- (
       gen_tac \\ strip_tac \\ rveq \\ fs []
       \\ qmatch_assum_abbrev_tac `evaluate (opts,[],sopt) = _`
       \\ qmatch_assum_abbrev_tac `evaluate (exps,[],st) = (r,s)`
       \\ qspecl_then [`opts`,`[]`,`sopt`] mp_tac evaluate_add_to_clock_io_events_mono
       \\ qspecl_then [`exps`,`[]`,`st`] mp_tac (INST_TYPE[alpha|->``:num#'a``]evaluate_add_to_clock_io_events_mono)
       \\ simp [inc_clock_def, Abbr`sopt`, Abbr`st`]
       \\ ntac 2 strip_tac
       \\ qpat_x_assum `evaluate _ = (r',s')` assume_tac
       \\ drule bviPropsTheory.evaluate_add_clock
       \\ disch_then(qspec_then `k` mp_tac)
       \\ impl_tac >- (rpt(PURE_FULL_CASE_TAC >> fs[]))
       \\ qpat_x_assum `evaluate _ = (r,s)` assume_tac
       \\ drule bviPropsTheory.evaluate_add_clock
       \\ disch_then(qspec_then `k'` mp_tac)
       \\ impl_tac >- (rpt(PURE_FULL_CASE_TAC >> fs[]))
       \\ simp[inc_clock_def] >> ntac 2 strip_tac
       \\ drule (GEN_ALL evaluate_compile_prog)
       \\ rpt(disch_then drule)
       \\ unabbrev_all_tac \\ disch_then drule
       \\ impl_tac >- (rpt(PURE_FULL_CASE_TAC >> fs[]))
       \\ strip_tac
       \\ rpt(PURE_FULL_CASE_TAC >> fs[state_rel_def,state_component_equality]))
     \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ ntac 3 (disch_then drule) \\ simp []
     \\ impl_tac
     >-
       (spose_not_then assume_tac
       \\ rpt(last_x_assum (qspec_then `k` mp_tac))
       \\ fs [])
     \\ strip_tac
     \\ asm_exists_tac
     \\ imp_res_tac state_rel_const \\ fs[]
     \\ TOP_CASE_TAC \\ fs[]
     \\ TOP_CASE_TAC \\ fs[]
     \\ TOP_CASE_TAC \\ fs[])
   \\ strip_tac
   \\ simp [semantics_def]
   \\ IF_CASES_TAC \\ fs [] >- (
     qpat_x_assum`∀k. _`mp_tac
     \\ first_x_assum (qspec_then `k` assume_tac)
     \\ strip_tac \\ rfs[]
     \\ drule (GEN_ALL evaluate_compile_prog)
     \\ rveq \\ disch_then drule
     \\ disch_then drule
     \\ first_x_assum (qspec_then `k` assume_tac)
     \\ qmatch_asmsub_abbrev_tac`FST(evaluate p)`
     \\ Cases_on`evaluate p` \\ pop_assum(assume_tac o SIMP_RULE std_ss [markerTheory.Abbrev_def])
     \\ unabbrev_all_tac \\ disch_then drule
     \\ impl_tac >- (fs[] >> every_case_tac >> fs[])
     \\ strip_tac
     \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[])
   \\ DEEP_INTRO_TAC some_intro \\ simp []
   \\ conj_tac >- (
    spose_not_then assume_tac \\ rw []
    \\ qpat_x_assum`∀k. _`mp_tac
    \\ first_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ rveq
    \\ (disch_then drule)
    \\ (disch_then drule)
    \\ (disch_then drule)
    \\ impl_tac >- (
      strip_tac \\ fs[]
      \\ rpt(first_x_assum(qspec_then`k`mp_tac))\\ simp[] )
    \\ strip_tac
    \\ qmatch_assum_rename_tac `state_rel rr _`
    \\ fs[] \\ rveq \\ metis_tac[])
  \\ strip_tac
  \\ qmatch_abbrev_tac `lprefix_lub$build_lprefix_lub l1 = lprefix_lub$build_lprefix_lub l2`
  \\ `(lprefix_lub$lprefix_chain l1 ∧
       lprefix_lub$lprefix_chain l2) ∧
       lprefix_lub$equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bviPropsTheory.initial_state_with_simp,
         bvlPropsTheory.initial_state_with_simp,
         bviPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bviPropsTheory.inc_clock_def],
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ ntac 2 (pop_assum kall_tac)
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac \\ rveq
  \\ drule (GEN_ALL evaluate_compile_prog)
  \\ rpt(disch_then drule)
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["start","k","ffi0","cc"])))
  \\ disch_then (qspecl_then [`start`,`k`,`ffi`,`cc`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac`p = (_,_)`
  \\ Cases_on`p` \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
  \\ simp []
  \\ impl_tac >- (
    strip_tac
    \\ rpt(last_x_assum (qspec_then `k` mp_tac))
    \\ fs [])
  \\ strip_tac
  \\ imp_res_tac state_rel_const
  \\ conj_tac \\ rw []
  \\ qexists_tac `k` \\ fs []
QED

Theorem compile_prog_labels:
   !next1 code1 next2 code2.
     compile_prog next1 code1 = (next2, code2)
     ==>
     set (MAP FST code1) UNION { next1 + k * bvl_to_bvi_namespaces | k
                               | next1 + k * bvl_to_bvi_namespaces < next2 } =
     set (MAP FST code2) /\
     next1 <= next2
Proof
   recInduct bvi_tailrecTheory.compile_prog_ind
   \\ rw [bvi_tailrecTheory.compile_prog_def] \\ fs []
   \\ pop_assum mp_tac
   \\ fs [CaseEq"prod", CaseEq"option"]
   \\ rpt (pairarg_tac \\ fs []) \\ rw [] \\ fs []
   \\ fs [INSERT_UNION_EQ]
   \\ last_x_assum (SUBST1_TAC o GSYM)
   \\ rw [EXTENSION]
   \\ eq_tac \\ rw []
   \\ simp [METIS_PROVE [] ``a \/ b <=> ~a ==> b``]
   \\ rw []
   >- (Cases_on `k` \\ fs [ADD1, LEFT_ADD_DISTRIB])
   >-
    (qexists_tac `0` \\ fs []
     \\ `0n < bvl_to_bvi_namespaces` by fs [backend_commonTheory.bvl_to_bvi_namespaces_def]
     \\ match_mp_tac (GEN_ALL (DECIDE ``0n < z /\ x + z <= y ==> x < y``))
     \\ asm_exists_tac \\ fs [])
   \\ qexists_tac `k + 1` \\ fs [LEFT_ADD_DISTRIB]
QED

Theorem compile_prog_keeps_names:
   ∀next xs next' ys. compile_prog next xs = (next',ys) ∧ MEM x (MAP FST xs) ⇒ MEM x (MAP FST ys)
Proof
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ rw[bvi_tailrecTheory.compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
QED

Theorem get_code_labels_rewrite:
   ∀loc next op arity foo exp bar exp_opt.
    rewrite loc next op arity foo exp = (bar, exp_opt) ⇒
    get_code_labels exp_opt ⊆ next INSERT get_code_labels exp
Proof
  recInduct bvi_tailrecTheory.rewrite_ind
  \\ rw[bvi_tailrecTheory.rewrite_def] \\ simp[]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ fs[CaseEq"option"] \\ rveq
  \\ fs[bvi_tailrecTheory.check_op_def,CaseEq"option",CaseEq"prod",CaseEq"bool"] \\ rveq \\ fs[]
  \\ rveq \\ fs[bvi_tailrecTheory.apply_op_def] \\ rw[] \\ fs[SUBSET_DEF]
  \\ Cases_on`opr` \\ fs[bvi_tailrecTheory.to_op_def, closLangTheory.assign_get_code_label_def]
  \\ fs[bvi_tailrecTheory.opbinargs_def, bvi_tailrecTheory.get_bin_args_def]
  \\ imp_res_tac is_rec_term_ok \\ fs[]
  \\ TRY(metis_tac[])
  \\ Cases_on`f` \\ fs[bvi_tailrecTheory.is_rec_def]
  \\ rename1`Call _ opt _ _`
  \\ Cases_on`opt` \\ fs[bvi_tailrecTheory.is_rec_def]
  \\ fs[bvi_tailrecTheory.args_from_def,bvi_tailrecTheory.push_call_def]
  \\ fs[bvi_tailrecTheory.apply_op_def, bvi_tailrecTheory.to_op_def, closLangTheory.assign_get_code_label_def]
  \\ fs[bvi_tailrecTheory.try_swap_def, bvi_tailrecTheory.opbinargs_def]
  \\ fs[CaseEq"bool",CaseEq"option"] \\ rveq
  \\ fs[CaseEq"option",bvi_tailrecTheory.get_bin_args_def,CaseEq"bool",bvi_tailrecTheory.apply_op_def] \\ rveq \\ fs[]
  \\ fs[PULL_EXISTS, closLangTheory.assign_get_code_label_def]
  \\ TRY(EVAL_TAC \\ rw[] \\ NO_TAC)
  \\ fsrw_tac[DNF_ss][PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem get_code_labels_let_wrap[simp]:
   ∀a b c. get_code_labels (let_wrap a b c) = get_code_labels b ∪ get_code_labels c
Proof
  rw[bvi_tailrecTheory.let_wrap_def, MAP_GENLIST, o_DEF]
  \\ rw[EXTENSION, MEM_GENLIST]
  \\ rw[EQ_IMP_THM] \\ rw[] \\ fs[]
QED

Theorem get_code_labels_compile_exp:
   ∀loc next arity exp exp_aux exp_opt.
   compile_exp loc next arity exp = SOME (exp_aux, exp_opt) ⇒
   get_code_labels exp_aux ∪ get_code_labels exp_opt ⊆ next INSERT get_code_labels exp
Proof
  simp[bvi_tailrecTheory.compile_exp_def,CaseEq"option"]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ drule get_code_labels_rewrite
  \\ simp[] \\ strip_tac
  \\ Cases_on`op` \\ simp[bvi_tailrecTheory.id_from_op_def, closLangTheory.assign_get_code_label_def]
  \\ EVAL_TAC
QED

Theorem compile_prog_good_code_labels:
   ∀n c n2 c2.
   bvi_tailrec$compile_prog n c = (n2,c2) ∧
   BIGUNION (set (MAP (get_code_labels o SND o SND) c)) ⊆ all ∧ set (MAP FST p) ⊆ all ∧
   { n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2 } ⊆ all ⇒
   BIGUNION (set (MAP (get_code_labels o SND o SND) c2)) ⊆ all
Proof
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ simp[bvi_tailrecTheory.compile_prog_def]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ rpt(pairarg_tac \\ fs[])
  \\ drule (GEN_ALL compile_prog_keeps_names) \\ strip_tac
  \\ qpat_x_assum`_ next xs = _`assume_tac
  \\ drule (GEN_ALL compile_prog_keeps_names) \\ strip_tac
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
  \\ drule get_code_labels_compile_exp
  \\ fs[SUBSET_DEF,PULL_EXISTS]
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ TRY (metis_tac[])
  \\ TRY (
    first_x_assum(qspecl_then[`0`](fn th => mp_tac th \\ simp[] \\ disch_then irule))
    \\ qpat_x_assum`_ (next + _) xs = _`assume_tac
    \\ drule compile_prog_next_mono
    \\ rw[] \\ simp[]
    \\ EVAL_TAC \\ simp[])
  \\ last_x_assum irule
  \\ reverse conj_tac >- metis_tac[]
  \\ gen_tac
  \\ rpt(first_x_assum(qspec_then`SUC k`mp_tac))
  \\ simp[ADD1,LEFT_ADD_DISTRIB]
QED

val _ = export_theory();
