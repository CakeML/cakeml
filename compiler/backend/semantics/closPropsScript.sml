(*
  Properties about closLang and its semantics
*)
open preamble closLangTheory closSemTheory backendPropsTheory

val _ = new_theory"closProps"

Theorem with_same_clock[simp]:
   (s:('c,'ffi) closSem$state) with clock := s.clock = s
Proof
  srw_tac[][closSemTheory.state_component_equality]
QED

Theorem dec_clock_code:
   (dec_clock x y).code = y.code
Proof
  EVAL_TAC
QED

Theorem dec_clock_ffi:
   (dec_clock x y).ffi = y.ffi
Proof
  EVAL_TAC
QED

Theorem dec_clock_compile_oracle[simp]:
   (closSem$dec_clock n s).compile_oracle = s.compile_oracle
Proof
  EVAL_TAC
QED

Theorem dec_clock_compile[simp]:
   (closSem$dec_clock n s).compile = s.compile
Proof
  EVAL_TAC
QED

Theorem list_to_v_EVERY_APPEND:
   !(x: closSem$v) y xs ys.
     v_to_list x = SOME xs /\
     v_to_list y = SOME ys /\
     (!t l. P (Block t l) <=> EVERY P l) /\
     P x /\ P y ==>
       P (list_to_v (xs ++ ys))
Proof
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, case_eq_thms] \\ fs []
  >-
   (qpat_x_assum `v_to_list _ = _` mp_tac
    \\ pop_assum mp_tac
    \\ ConseqConv.SPEC_ALL_TAC
    \\ ho_match_mp_tac v_to_list_ind
    \\ rw [v_to_list_def, case_eq_thms]
    \\ fs [list_to_v_def])
  \\ rfs []
  \\ res_tac
  \\ fs [list_to_v_def]
QED

val ref_rel_def = Define`
  (ref_rel R (ValueArray vs) (ValueArray ws) ⇔ LIST_REL R vs ws) ∧
  (ref_rel R (ByteArray f as) (ByteArray g bs) ⇔ f = g ∧ as = bs) ∧
  (ref_rel _ _ _ = F)`
val _ = export_rewrites["ref_rel_def"];

Theorem ref_rel_simp[simp]:
   (ref_rel R (ValueArray vs) y ⇔ ∃ws. y = ValueArray ws ∧ LIST_REL R vs ws) ∧
   (ref_rel R (ByteArray f bs) y ⇔ y = ByteArray f bs)
Proof
  Cases_on`y`>>simp[ref_rel_def] >> srw_tac[][EQ_IMP_THM]
QED

val code_locs_def = tDefine "code_locs" `
  (code_locs [] = []) /\
  (code_locs (x::y::xs) =
     let c1 = code_locs [x] in
     let c2 = code_locs (y::xs) in
       c1 ++ c2) /\
  (code_locs [Var _ v] = []) /\
  (code_locs [If _ x1 x2 x3] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
     let c3 = code_locs [x3] in
       c1 ++ c2 ++ c3) /\
  (code_locs [Let _ xs x2] =
     let c1 = code_locs xs in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Raise _ x1] =
     code_locs [x1]) /\
  (code_locs [Tick _ x1] =
     code_locs [x1]) /\
  (code_locs [Op _ op xs] =
     code_locs xs) /\
  (code_locs [App _ loc_opt x1 xs] =
     let c1 = code_locs [x1] in
     let c2 = code_locs xs in
         c1++c2) /\
  (code_locs [Fn _ loc_opt vs num_args x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let c1 = code_locs [x1] in
       c1 ++ [loc]) /\
  (code_locs [Letrec _ loc_opt vs fns x1] =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let c1 = code_locs (MAP SND fns) in
     let c2 = code_locs [x1] in
     c1 ++ GENLIST (λn. loc + 2*n) (LENGTH fns) ++ c2) /\
  (code_locs [Handle _ x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Call _ ticks dest xs] =
     code_locs xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);

Theorem code_locs_cons:
   ∀x xs. code_locs (x::xs) = code_locs [x] ++ code_locs xs
Proof
  gen_tac >> Cases >> simp[code_locs_def]
QED

Theorem code_locs_append:
   !l1 l2. code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2
Proof
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[Once code_locs_cons,SimpRHS]
QED

Theorem code_locs_map:
   !xs f. code_locs (MAP f xs) = FLAT (MAP (\x. code_locs [f x]) xs)
Proof
  Induct \\ full_simp_tac(srw_ss())[code_locs_def]
  \\ ONCE_REWRITE_TAC [code_locs_cons] \\ full_simp_tac(srw_ss())[code_locs_def]
QED

Theorem BIGUNION_MAP_code_locs_SND_SND:
   BIGUNION (set (MAP (set ∘ code_locs ∘ (λx. [SND (SND x)])) xs)) =
    set (code_locs (MAP (SND o SND) xs))
Proof
  Induct_on `xs` \\ fs [code_locs_def]
  \\ once_rewrite_tac [code_locs_cons]
  \\ fs [code_locs_def]
QED

val contains_App_SOME_def = tDefine "contains_App_SOME" `
  (contains_App_SOME max_app [] ⇔ F) /\
  (contains_App_SOME max_app (x::y::xs) ⇔
     contains_App_SOME max_app [x] ∨
     contains_App_SOME max_app (y::xs)) /\
  (contains_App_SOME max_app [Var _ v] ⇔ F) /\
  (contains_App_SOME max_app [If _ x1 x2 x3] ⇔
     contains_App_SOME max_app [x1] ∨
     contains_App_SOME max_app [x2] ∨
     contains_App_SOME max_app [x3]) /\
  (contains_App_SOME max_app [Let _ xs x2] ⇔
     contains_App_SOME max_app [x2] ∨
     contains_App_SOME max_app xs) /\
  (contains_App_SOME max_app [Raise _ x1] ⇔
     contains_App_SOME max_app [x1]) /\
  (contains_App_SOME max_app [Tick _ x1] ⇔
     contains_App_SOME max_app [x1]) /\
  (contains_App_SOME max_app [Op _ op xs] ⇔
     contains_App_SOME max_app xs) /\
  (contains_App_SOME max_app [App _ loc_opt x1 x2] ⇔
     IS_SOME loc_opt ∨ max_app < LENGTH x2 ∨
     contains_App_SOME max_app [x1] ∨
     contains_App_SOME max_app x2) /\
  (contains_App_SOME max_app [Fn _ loc vs num_args x1] ⇔
     contains_App_SOME max_app [x1]) /\
  (contains_App_SOME max_app [Letrec _ loc vs fns x1] ⇔
     contains_App_SOME max_app (MAP SND fns) ∨
     contains_App_SOME max_app [x1]) /\
  (contains_App_SOME max_app [Handle _ x1 x2] ⇔
     contains_App_SOME max_app [x1] ∨
     contains_App_SOME max_app [x2]) /\
  (contains_App_SOME max_app [Call _ ticks dest xs] ⇔
     contains_App_SOME max_app xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);

Theorem contains_App_SOME_EXISTS:
   ∀ls max_app. contains_App_SOME max_app ls ⇔ EXISTS (λx. contains_App_SOME max_app [x]) ls
Proof
  Induct >> simp[contains_App_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[contains_App_SOME_def]
QED

val every_Fn_SOME_def = tDefine "every_Fn_SOME" `
  (every_Fn_SOME [] ⇔ T) ∧
  (every_Fn_SOME (x::y::xs) ⇔
     every_Fn_SOME [x] ∧
     every_Fn_SOME (y::xs)) ∧
  (every_Fn_SOME [Var _ v] ⇔ T) ∧
  (every_Fn_SOME [If _ x1 x2 x3] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME [x2] ∧
     every_Fn_SOME [x3]) ∧
  (every_Fn_SOME [Let _ xs x2] ⇔
     every_Fn_SOME [x2] ∧
     every_Fn_SOME xs) ∧
  (every_Fn_SOME [Raise _ x1] ⇔
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Tick _ x1] ⇔
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Op _ op xs] ⇔
     every_Fn_SOME xs) ∧
  (every_Fn_SOME [App _ loc_opt x1 x2] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME x2) ∧
  (every_Fn_SOME [Fn _ loc_opt vs num_args x1] ⇔
     IS_SOME loc_opt ∧
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Letrec _ loc_opt vs fns x1] ⇔
     IS_SOME loc_opt ∧
     every_Fn_SOME (MAP SND fns) ∧
     every_Fn_SOME [x1]) ∧
  (every_Fn_SOME [Handle _ x1 x2] ⇔
     every_Fn_SOME [x1] ∧
     every_Fn_SOME [x2]) ∧
  (every_Fn_SOME [Call _ ticks dest xs] ⇔
     every_Fn_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_SOME_def"];

Theorem every_Fn_SOME_EVERY:
   ∀ls. every_Fn_SOME ls ⇔ EVERY (λx. every_Fn_SOME [x]) ls
Proof
  Induct >> simp[every_Fn_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_SOME_def]
QED

Theorem every_Fn_SOME_APPEND[simp]:
   every_Fn_SOME (l1 ++ l2) ⇔ every_Fn_SOME l1 ∧ every_Fn_SOME l2
Proof
  once_rewrite_tac[every_Fn_SOME_EVERY] \\ rw[]
QED

val every_Fn_vs_NONE_def = tDefine "every_Fn_vs_NONE" `
  (every_Fn_vs_NONE [] ⇔ T) ∧
  (every_Fn_vs_NONE (x::y::xs) ⇔
     every_Fn_vs_NONE [x] ∧
     every_Fn_vs_NONE (y::xs)) ∧
  (every_Fn_vs_NONE [Var _ v] ⇔ T) ∧
  (every_Fn_vs_NONE [If _ x1 x2 x3] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE [x2] ∧
     every_Fn_vs_NONE [x3]) ∧
  (every_Fn_vs_NONE [Let _ xs x2] ⇔
     every_Fn_vs_NONE [x2] ∧
     every_Fn_vs_NONE xs) ∧
  (every_Fn_vs_NONE [Raise _ x1] ⇔
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Tick _ x1] ⇔
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Op _ op xs] ⇔
     every_Fn_vs_NONE xs) ∧
  (every_Fn_vs_NONE [App _ loc_opt x1 x2] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE x2) ∧
  (every_Fn_vs_NONE [Fn _ loc vs_opt num_args x1] ⇔
     IS_NONE vs_opt ∧
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Letrec _ loc vs_opt fns x1] ⇔
     IS_NONE vs_opt ∧
     every_Fn_vs_NONE (MAP SND fns) ∧
     every_Fn_vs_NONE [x1]) ∧
  (every_Fn_vs_NONE [Handle _ x1 x2] ⇔
     every_Fn_vs_NONE [x1] ∧
     every_Fn_vs_NONE [x2]) ∧
  (every_Fn_vs_NONE [Call _ ticks dest xs] ⇔
     every_Fn_vs_NONE xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_vs_NONE_def"];

Theorem every_Fn_vs_NONE_EVERY:
   ∀ls. every_Fn_vs_NONE ls ⇔ EVERY (λx. every_Fn_vs_NONE [x]) ls
Proof
  Induct >> simp[every_Fn_vs_NONE_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_vs_NONE_def]
QED

Theorem IMP_every_Fn_vs_NONE_TAKE:
   every_Fn_vs_NONE ls ⇒ every_Fn_vs_NONE (TAKE n ls)
Proof
  once_rewrite_tac[every_Fn_vs_NONE_EVERY]
  \\ Cases_on`n <= LENGTH ls` \\ simp[EVERY_TAKE, TAKE_LENGTH_TOO_LONG]
QED

Theorem every_Fn_vs_NONE_APPEND[simp]:
   every_Fn_vs_NONE (l1 ++ l2) ⇔ every_Fn_vs_NONE l1 ∧ every_Fn_vs_NONE l2
Proof
  once_rewrite_tac[every_Fn_vs_NONE_EVERY] \\ rw[]
QED

val every_Fn_vs_SOME_def = tDefine "every_Fn_vs_SOME" `
  (every_Fn_vs_SOME [] ⇔ T) ∧
  (every_Fn_vs_SOME (x::y::xs) ⇔
     every_Fn_vs_SOME [x] ∧
     every_Fn_vs_SOME (y::xs)) ∧
  (every_Fn_vs_SOME [Var _ v] ⇔ T) ∧
  (every_Fn_vs_SOME [If _ x1 x2 x3] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME [x2] ∧
     every_Fn_vs_SOME [x3]) ∧
  (every_Fn_vs_SOME [Let _ xs x2] ⇔
     every_Fn_vs_SOME [x2] ∧
     every_Fn_vs_SOME xs) ∧
  (every_Fn_vs_SOME [Raise _ x1] ⇔
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Tick _ x1] ⇔
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Op _ op xs] ⇔
     every_Fn_vs_SOME xs) ∧
  (every_Fn_vs_SOME [App _ loc_opt x1 x2] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME x2) ∧
  (every_Fn_vs_SOME [Fn _ loc vs_opt num_args x1] ⇔
     IS_SOME vs_opt ∧
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Letrec _ loc vs_opt fns x1] ⇔
     IS_SOME vs_opt ∧
     every_Fn_vs_SOME (MAP SND fns) ∧
     every_Fn_vs_SOME [x1]) ∧
  (every_Fn_vs_SOME [Handle _ x1 x2] ⇔
     every_Fn_vs_SOME [x1] ∧
     every_Fn_vs_SOME [x2]) ∧
  (every_Fn_vs_SOME [Call _ ticks dest xs] ⇔
     every_Fn_vs_SOME xs)`
  (WF_REL_TAC `measure (exp3_size)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[exp_size_def] >>
   decide_tac);
val _ = export_rewrites["every_Fn_vs_SOME_def"];

Theorem every_Fn_vs_SOME_EVERY:
   ∀ls. every_Fn_vs_SOME ls ⇔ EVERY (λx. every_Fn_vs_SOME [x]) ls
Proof
  Induct >> simp[every_Fn_vs_SOME_def] >>
  Cases_on`ls`>>full_simp_tac(srw_ss())[every_Fn_vs_SOME_def]
QED

Theorem every_Fn_vs_SOME_APPEND[simp]:
   every_Fn_vs_SOME (l1 ++ l2) ⇔ every_Fn_vs_SOME l1 ∧ every_Fn_vs_SOME l2
Proof
  once_rewrite_tac[every_Fn_vs_SOME_EVERY] \\ rw[]
QED

val fv_def = tDefine "fv" `
  (fv n [] <=> F) /\
  (fv n ((x:closLang$exp)::y::xs) <=>
     fv n [x] \/ fv n (y::xs)) /\
  (fv n [Var _ v] <=> (n = v)) /\
  (fv n [If _ x1 x2 x3] <=>
     fv n [x1] \/ fv n [x2] \/ fv n [x3]) /\
  (fv n [Let _ xs x2] <=>
     fv n xs \/ fv (n + LENGTH xs) [x2]) /\
  (fv n [Raise _ x1] <=> fv n [x1]) /\
  (fv n [Tick _ x1] <=> fv n [x1]) /\
  (fv n [Op _ op xs] <=> fv n xs) /\
  (fv n [App _ loc_opt x1 x2] <=>
     fv n [x1] \/ fv n x2) /\
  (fv n [Fn _ loc vs num_args x1] <=>
     fv (n + num_args) [x1]) /\
  (fv n [Letrec _ loc vs fns x1] <=>
     EXISTS (\(num_args, x). fv (n + num_args + LENGTH fns) [x]) fns \/ fv (n + LENGTH fns) [x1]) /\
  (fv n [Handle _ x1 x2] <=>
     fv n [x1] \/ fv (n+1) [x2]) /\
  (fv n [Call _ ticks dest xs] <=> fv n xs)`
 (WF_REL_TAC `measure (exp3_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [exp_size_def] >>
  res_tac >>
  srw_tac [ARITH_ss] [exp_size_def]);

val fv_ind = theorem"fv_ind";

Theorem fv_append[simp]:
   ∀v l1. fv v (l1 ++ l2) ⇔ fv v l1 ∨ fv v l2
Proof
  ho_match_mp_tac fv_ind
  \\ rpt strip_tac
  \\ rw[fv_def]
  \\ fs[]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`l2`\\fs[fv_def]
QED

Theorem fv_nil[simp]:
   fv v [] ⇔ F
Proof
rw[fv_def]
QED

val fv1_def = Define`fv1 v e = fv v [e]`;
val fv1_intro = save_thm("fv1_intro[simp]",GSYM fv1_def)
val fv1_thm =
  fv_def |> SIMP_RULE (srw_ss())[]
  |> curry save_thm "fv1_thm"

Theorem fv_cons[simp]:
   fv v (x::xs) ⇔ fv1 v x ∨ fv v xs
Proof
  metis_tac[CONS_APPEND,fv_append,fv1_def]
QED

Theorem fv_exists:
   ∀ls. fv v ls ⇔ EXISTS (fv1 v) ls
Proof
  Induct \\ fs[] \\ rw[Once fv_cons]
QED

Theorem fv_MAPi:
   ∀l x f. fv x (MAPi f l) ⇔ ∃n. n < LENGTH l ∧ fv x [f n (EL n l)]
Proof
  Induct >> simp[fv_def] >> simp[] >> dsimp[indexedListsTheory.LT_SUC]
QED

Theorem fv_GENLIST_Var:
   ∀n. fv v (GENLIST (Var tra) n) ⇔ v < n
Proof
  Induct \\ simp[fv_def,GENLIST,SNOC_APPEND]
  \\ rw[fv_def]
QED

Theorem fv_REPLICATE[simp]:
   fv n (REPLICATE m e) ⇔ 0 < m ∧ fv1 n e
Proof
  Induct_on `m` >> simp[REPLICATE, fv_def,fv1_thm] >>
  simp[] >> metis_tac[]
QED

val v_ind =
  TypeBase.induction_of``:closSem$v``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE(srw_ss())[]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`
  |> curry save_thm "v_ind";

Theorem do_app_err:
   ∀op ls s e.
     do_app op ls s = Rerr e ⇒
     (op ≠ Equal ⇒ ∃a. e = Rabort a)
Proof
  Cases >>
  srw_tac[][do_app_def,case_eq_thms] >>
  fs[case_eq_thms,bool_case_eq,pair_case_eq] >> rw[]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
QED

Theorem Boolv_11[simp]:
  closSem$Boolv b1 = Boolv b2 ⇔ b1 = b2
Proof
EVAL_TAC>>srw_tac[][]
QED

Theorem do_eq_list_rel:
   ∀l1 l2 l3 l4.
     LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧
     LIST_REL (λp1 p2. UNCURRY do_eq p1 = UNCURRY do_eq p2) (ZIP(l1,l2)) (ZIP(l3,l4)) ⇒
     closSem$do_eq_list l1 l2 = do_eq_list l3 l4
Proof
   Induct >> simp[LENGTH_NIL_SYM] >- (
     simp[GSYM AND_IMP_INTRO, ZIP_EQ_NIL] ) >>
   gen_tac >> Cases >> simp[PULL_EXISTS] >>
   Cases >> simp[LENGTH_NIL_SYM] >>
   Cases >> simp[CONJUNCT2 do_eq_def] >>
   strip_tac >> BasicProvers.CASE_TAC >> srw_tac[][]
QED

val evaluate_LENGTH_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,s,env).
       (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T)`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (Rval res,s1) => (LENGTH res = 1)
            | _ => T)`

val evaluate_LENGTH = prove(evaluate_LENGTH_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_LENGTH_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [FORALL_PROD]

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

Theorem evaluate_IMP_LENGTH:
   (evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`s`,`env`] MP_TAC)
  \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_app_IMP_LENGTH:
   (evaluate_app x1 x2 x3 x4 = (Rval res,s1)) ==> (LENGTH res = 1)
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_LENGTH |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] MP_TAC)
  \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SING:
   (evaluate ([x],s,env) = (Rval r,s2)) ==> ?r1. r = [r1]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `r` \\ full_simp_tac(srw_ss())[] \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_CONS:
   evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t
Proof
  Cases_on `xs` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_SNOC:
   !xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ full_simp_tac(srw_ss())[LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ full_simp_tac(srw_ss())[]
QED

val evaluate_const_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          (s1.max_app = s.max_app))`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (_,s1) =>
          (s1.max_app = x4.max_app))`;

Theorem do_install_const:
   do_install vs s = (res,s') ⇒
   s'.max_app = s.max_app ∧
   s'.ffi = s.ffi
Proof
   rw[do_install_def,case_eq_thms]
   \\ pairarg_tac \\ fs[bool_case_eq,case_eq_thms,pair_case_eq]
   \\ rw[]
QED

val evaluate_const_lemma = prove(
  evaluate_const_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_const_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC do_app_const
  \\ IMP_RES_TAC do_install_const
  \\ full_simp_tac(srw_ss())[dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]

Theorem evaluate_const:
   (evaluate (xs,env,s) = (res,s1)) ==>
      (s1.max_app = s.max_app)
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`env`,`s`] mp_tac)
  \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_app_const:
   (evaluate_app x1 x2 x3 x4 = (res,s1)) ==>
      (s1.max_app = x4.max_app)
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_const_lemma |> CONJUNCT2 |> Q.ISPECL_THEN [`x1`,`x2`,`x3`,`x4`] mp_tac)
  \\ full_simp_tac(srw_ss())[]
QED

val evaluate_code_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          ∃n.
            s1.compile_oracle = shift_seq n s.compile_oracle ∧
            let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n)) in
            s1.code = s.code |++ ls ∧
            ALL_DISTINCT (MAP FST ls) ∧
            DISJOINT (FDOM s.code) (set(MAP FST ls)))`
  |> Q.SPEC `\x1 x2 x3 s.
       (case evaluate_app x1 x2 x3 s of (_,s1) =>
          ∃n.
            s1.compile_oracle = shift_seq n s.compile_oracle ∧
            let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n)) in
            s1.code = s.code |++ ls ∧
            ALL_DISTINCT (MAP FST ls) ∧
            DISJOINT (FDOM s.code) (set(MAP FST ls)))`

val evaluate_code_lemma = prove(
  evaluate_code_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_code_ind \\ rw[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs[] \\ rw []
  \\ every_case_tac \\ fs[] \\ rfs[shift_seq_def,FUN_EQ_THM]
  \\ fs[dec_clock_def]
  \\ TRY(qexists_tac`0` \\ simp[FUPDATE_LIST_THM] \\ NO_TAC)
  \\ TRY (
    qmatch_goalsub_rename_tac`(n1 + (n2 + (n3 + _)))` \\
    qexists_tac`n3+n2+n1` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_goalsub_rename_tac`(z1 + (z2 + _))` \\
    qexists_tac`z2+z1` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_goalsub_rename_tac`(z1 + (z2 + _))` \\
    qexists_tac`z1+z2` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_asmsub_rename_tac`_ = _ ((nn:num) + _)` \\
    qexists_tac`nn` \\
    imp_res_tac do_app_const \\
    fs[] \\ NO_TAC)
  \\ TRY
   (qmatch_asmsub_rename_tac`_ = _ ((z:num) + _)`
    \\ qmatch_asmsub_rename_tac`s.compile_oracle (y + _)`
    \\ fs[do_install_def,case_eq_thms,pair_case_eq,UNCURRY,bool_case_eq,shift_seq_def]
    \\ qexists_tac`1+y`
    \\ fs[GENLIST_APPEND,FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\ rfs[]
    \\ fs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\ rveq \\ fs[]
    \\ metis_tac[])
  \\ TRY
   (qmatch_asmsub_rename_tac`_ = _ ((z:num) + _)`
    \\ qmatch_asmsub_rename_tac`s.compile_oracle (y + _)`
    \\ fs[do_install_def,case_eq_thms,pair_case_eq,UNCURRY,bool_case_eq,shift_seq_def]
    \\ qexists_tac`z+1+y`
    \\ fs[GENLIST_APPEND,FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\ rfs[]
    \\ fs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\ rveq \\ fs[]
    \\ metis_tac[])
  (*
  >-
   (fs [do_install_def]
    \\ fs [case_eq_thms, pair_case_eq, UNCURRY, bool_case_eq] \\ TRY (metis_tac [])
    \\ rw [] \\ fs [shift_seq_def]
    \\ qmatch_goalsub_rename_tac `nn + _`
    \\ qexists_tac `nn+1` \\ fs []
    \\ once_rewrite_tac [ADD_COMM]
    \\ fs [GENLIST_APPEND] \\ rfs []
    \\ last_x_assum (qspec_then `0` (assume_tac o GSYM)) \\ fs []
    \\ fs [FUPDATE_LIST_APPEND, ALL_DISTINCT_APPEND, IN_DISJOINT]
    \\ rfs []
    \\ fs [FDOM_FUPDATE_LIST]
    \\ metis_tac [])
  *)
  \\ qmatch_goalsub_rename_tac`(n1 + (n2 + (n3 + _)))`
  \\ qexists_tac `n1+n2+n3` \\ fs []
  \\ sg `GENLIST r.compile_oracle n1 = GENLIST (\x. s.compile_oracle (n2 + x)) n1`
  >- fsrw_tac [ETA_ss] [GSYM FUN_EQ_THM]
  \\ fs []
  \\ rfs []
  \\ sg `GENLIST r'.compile_oracle n3 = GENLIST (\x. s.compile_oracle (n1 + (n2 + x))) n3`
  >- (fsrw_tac [ETA_ss] [GSYM FUN_EQ_THM] \\ fs [])
  \\ fs []
  \\ once_rewrite_tac [ADD_ASSOC]
  \\ once_rewrite_tac [ADD_COMM]
  \\ fs [GSYM FUPDATE_LIST_APPEND, GENLIST_APPEND, ALL_DISTINCT_APPEND,
         IN_DISJOINT, FDOM_FUPDATE_LIST]
  \\ metis_tac [])
  |> SIMP_RULE std_ss [FORALL_PROD];

Theorem evaluate_code:
   (evaluate (xs,env,s) = (res,s1)) ==>
      ∃n. s1.compile_oracle = shift_seq n s.compile_oracle ∧
          let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n)) in
          s1.code = s.code |++ ls ∧
          ALL_DISTINCT (MAP FST ls) ∧
          DISJOINT (FDOM s.code) (set (MAP FST ls))
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_code_lemma |> CONJUNCT1 |> Q.ISPECL_THEN [`xs`,`env`,`s`] mp_tac)
  \\ fs[]
QED

Theorem evaluate_app_code:
   (evaluate_app lopt f args s = (res,s1)) ==>
      ∃n. s1.compile_oracle = shift_seq n s.compile_oracle ∧
          let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n)) in
          s1.code = s.code |++ ls ∧
          ALL_DISTINCT (MAP FST ls) ∧
          DISJOINT (FDOM s.code) (set (MAP FST ls))
Proof
  REPEAT STRIP_TAC
  \\ (evaluate_code_lemma |> CONJUNCT2 |> Q.ISPECL_THEN [`lopt`,`f`,`args`,`s`] mp_tac)
  \\ fs[]
QED

Theorem evaluate_mono:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==>
     s1.code SUBMAP s2.code
Proof
  rw[] \\ imp_res_tac evaluate_code \\ fs[]
  \\ rw[DISTINCT_FUPDATE_LIST_UNION]
  \\ match_mp_tac SUBMAP_FUNION \\ rw[]
QED

Theorem evaluate_MAP_Op_Const:
   ∀f env s ls.
      evaluate (MAP (λx. Op tra (Const (f x)) []) ls,env,s) =
      (Rval (MAP (Number o f) ls),s)
Proof
  ntac 3 gen_tac >> Induct >>
  simp[evaluate_def] >>
  simp[Once evaluate_CONS] >>
  simp[evaluate_def,do_app_def]
QED

Theorem evaluate_REPLICATE_Op_AllocGlobal:
   ∀n env s. evaluate (REPLICATE n (Op tra AllocGlobal []),env,s) =
              (Rval (GENLIST (K Unit) n),s with globals := s.globals ++ GENLIST (K NONE) n)
Proof
  Induct >> simp[evaluate_def,REPLICATE] >- (
    simp[state_component_equality] ) >>
  simp[Once evaluate_CONS,evaluate_def,do_app_def,GENLIST_CONS] >>
  simp[state_component_equality]
QED

Theorem lookup_vars_NONE:
   !vs. (lookup_vars vs env = NONE) <=> ?v. MEM v vs /\ LENGTH env <= v
Proof
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h < LENGTH env` \\ full_simp_tac(srw_ss())[NOT_LESS]
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[]
  THEN1 METIS_TAC []
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [NOT_LESS]
QED

Theorem lookup_vars_SOME:
   !vs env xs.
      (lookup_vars vs env = SOME xs) ==>
      (LENGTH vs = LENGTH xs)
Proof
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ RES_TAC
QED

val lookup_vars_MEM = Q.prove(
  `!ys n x (env2:closSem$v list).
      (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
      (EL n ys) < LENGTH env2 /\
      (EL n x = EL (EL n ys) env2)`,
  Induct \\ full_simp_tac(srw_ss())[lookup_vars_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `lookup_vars ys env2` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL
  |> curry save_thm "lookup_vars_MEM";

Theorem clock_lemmas:
 !s. (s with clock := s.clock) = s
Proof
 srw_tac[][state_component_equality]
QED

Theorem evaluate_app_rw:
 (!args loc_opt f s.
  args ≠ [] ⇒
  evaluate_app loc_opt f args s =
    case dest_closure s.max_app loc_opt f args of
       | NONE => (Rerr(Rabort Rtype_error),s)
       | SOME (Partial_app v) =>
           if s.clock < LENGTH args then
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else (Rval [v], dec_clock (LENGTH args) s)
       | SOME (Full_app exp env rest_args) =>
           if s.clock < (LENGTH args - LENGTH rest_args) then
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else
             case evaluate ([exp],env,dec_clock (LENGTH args - LENGTH rest_args) s) of
                | (Rval [v], s1) =>
                    evaluate_app loc_opt v rest_args s1
                | res => res)
Proof
 Cases_on `args` >>
 full_simp_tac(srw_ss())[evaluate_def]
QED

Theorem EVERY_pure_correct = Q.prove(`
  (∀t es E (s:('c,'ffi) closSem$state). t = (es,E,s) ∧ EVERY closLang$pure es ⇒
               case evaluate(es, E, s) of
                 (Rval vs, s') => s' = s ∧ LENGTH vs = LENGTH es
               | (Rerr (Rraise a), _) => F
               | (Rerr (Rabort a), _) => a = Rtype_error) ∧
   (∀(n: num option) (v:closSem$v)
     (vl : closSem$v list) (s : ('c,'ffi) closSem$state). T)`,
  ho_match_mp_tac evaluate_ind >> simp[pure_def] >>
  rpt strip_tac >> simp[evaluate_def]
  >- (every_case_tac >> full_simp_tac(srw_ss())[] >>
      rpt (qpat_x_assum `_ ==> _` mp_tac) >> simp[] >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[EVERY_MEM, EXISTS_MEM] >> metis_tac[])
  >- srw_tac[][]
  >- (full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (full_simp_tac (srw_ss() ++ ETA_ss) [] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])
  >- (Cases_on`op=Install` >- fs[pure_op_def] >>
      fsrw_tac[ETA_ss][]
      \\ PURE_CASE_TAC \\ fs[]
      \\ PURE_CASE_TAC \\ fs[]
      \\ rveq
      \\ reverse PURE_CASE_TAC \\ fs[]
      >- (
        rename1 `closLang$pure_op opn` >> Cases_on `opn` >>
        full_simp_tac(srw_ss())[pure_op_def, do_app_def, case_eq_thms, bool_case_eq] >>
        rveq \\ fs[] \\ fs[CaseEq"prod"] )
      \\ rename1 `closLang$pure_op opn` >> Cases_on `opn`
      \\ fs[pure_op_def, do_app_def, case_eq_thms, bool_case_eq] \\ rveq \\ fs[]
      \\ fs[CaseEq"prod"]
      \\ rveq \\ fs[])
  >- (every_case_tac >> simp[])
  >- (every_case_tac >> full_simp_tac(srw_ss())[]))
  |> SIMP_RULE (srw_ss()) []

val pure_correct = save_thm(
  "pure_correct",
  EVERY_pure_correct |> Q.SPECL [`[e]`, `env`, `s`]
                     |> SIMP_RULE (srw_ss()) [])

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 srw_tac[][]);

val do_app_split_list = prove(
  ``do_app op vs s = res
    <=>
    vs = [] /\ do_app op [] s = res \/
    ?v vs1. vs = v::vs1 /\ do_app op (v::vs1) s = res``,
  Cases_on `vs` \\ fs []);

val do_app_cases_val = save_thm ("do_app_cases_val",
  ``do_app op vs s = Rval (v,s')`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

val do_app_cases_err = save_thm ("do_app_cases_err",
``do_app op vs s = Rerr (Rraise v)`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

val do_app_cases_timeout = save_thm ("do_app_cases_timeout",
``do_app op vs s = Rerr (Rabort Rtimeout_error)`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

val do_app_cases_type_error = save_thm ("do_app_cases_type_error",
``do_app op vs s = Rerr (Rabort Rtype_error)`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss++boolSimps.DNF_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

val do_app_cases_ffi_error = save_thm ("do_app_cases_ffi_error",
``do_app op vs s = Rerr (Rabort(Rffi_error f))`` |>
  (ONCE_REWRITE_CONV [do_app_split_list] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, case_eq_thms, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss++boolSimps.DNF_ss) [LET_THM, case_eq_thms] THENC
   ALL_CONV));

Theorem dest_closure_none_loc:
 !max_app l cl vs v e env rest.
  (dest_closure max_app l cl vs = SOME (Partial_app v) ⇒ l = NONE) ∧
  (dest_closure max_app l cl vs = SOME (Full_app e env rest) ∧ rest ≠ [] ⇒ l = NONE)
Proof
 rpt gen_tac >>
 simp [dest_closure_def] >>
 Cases_on `cl` >>
 simp [] >>
 srw_tac[][] >>
 Cases_on `l` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[DROP_NIL] >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[DROP_NIL]
QED

val is_closure_def = Define `
(is_closure (Closure _ _ _ _ _) ⇔ T) ∧
(is_closure (Recclosure _ _ _ _ _) ⇔ T) ∧
(is_closure _ ⇔ F)`;
val _ = export_rewrites ["is_closure_def"]

val clo_to_loc_def = Define `
(clo_to_loc (Closure l _ _ _ _) = l) ∧
(clo_to_loc (Recclosure l _ _ _ i) = OPTION_MAP ((+) (2 * i)) l)`;
val _ = export_rewrites ["clo_to_loc_def"]

val clo_to_env_def = Define `
(clo_to_env (Closure _ _ env _ _) = env) ∧
(clo_to_env (Recclosure loc _ env fns _) =
  GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env)`;
val _ = export_rewrites ["clo_to_env_def"]

val clo_to_partial_args_def = Define `
(clo_to_partial_args (Closure _ args _ _ _) = args) ∧
(clo_to_partial_args (Recclosure _ args _ _ _) = args)`;
val _ = export_rewrites ["clo_to_partial_args_def"]

val clo_add_partial_args_def = Define `
(clo_add_partial_args args (Closure x1 args' x2 x3 x4) =
  Closure x1 (args ++ args') x2 x3 x4) ∧
(clo_add_partial_args args (Recclosure x1 args' x2 x3 x4) =
  Recclosure x1 (args ++ args') x2 x3 x4)`;
val _ = export_rewrites ["clo_add_partial_args_def"]

val clo_to_num_params_def = Define `
(clo_to_num_params (Closure _ _ _ n _) = n) ∧
(clo_to_num_params (Recclosure _ _ _ fns i) = FST (EL i fns))`;
val _ = export_rewrites ["clo_to_num_params_def"]

val rec_clo_ok_def = Define `
(rec_clo_ok (Recclosure _ _ _ fns i) ⇔ i < LENGTH fns) ∧
(rec_clo_ok (Closure _ _ _ _ _) ⇔ T)`;
val _ = export_rewrites ["rec_clo_ok_def"]

Theorem dest_closure_full_length:
 !max_app l v vs e args rest.
  dest_closure max_app l v vs = SOME (Full_app e args rest)
  ⇒
  LENGTH (clo_to_partial_args v) < clo_to_num_params v ∧
  LENGTH vs + LENGTH (clo_to_partial_args v) = clo_to_num_params v + LENGTH rest ∧
  LENGTH args = clo_to_num_params v + LENGTH (clo_to_env v)
Proof
 rpt gen_tac >>
 simp [dest_closure_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 full_simp_tac(srw_ss())[is_closure_def, clo_to_partial_args_def, clo_to_num_params_def, clo_to_env_def]
 >- (`n - LENGTH l' ≤ LENGTH vs` by decide_tac >>
     srw_tac[][] >>
     simp [LENGTH_TAKE]) >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 simp []
QED

Theorem evaluate_app_clock_less:
 !loc_opt f args s1 vs s2.
  args ≠ [] ∧
  evaluate_app loc_opt f args s1 = (Rval vs, s2)
  ⇒
  s2.clock < s1.clock
Proof
 srw_tac[][] >>
 rev_full_simp_tac(srw_ss())[evaluate_app_rw] >>
 BasicProvers.EVERY_CASE_TAC >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 TRY decide_tac >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_clock >>
 full_simp_tac(srw_ss())[dec_clock_def] >>
 imp_res_tac dest_closure_full_length >>
 TRY decide_tac >>
 Cases_on `args` >>
 full_simp_tac(srw_ss())[] >>
 decide_tac
QED

Theorem clo_add_partial_args_nil[simp]:
 !x. is_closure x ⇒ clo_add_partial_args [] x = x
Proof
 Cases_on `x` >>
 srw_tac[][is_closure_def, clo_add_partial_args_def]
QED

val clo_can_apply_def = Define `
clo_can_apply loc cl num_args ⇔
  LENGTH (clo_to_partial_args cl) < clo_to_num_params cl ∧
  rec_clo_ok cl ∧
  (loc ≠ NONE ⇒
   loc = clo_to_loc cl ∧
   num_args = clo_to_num_params cl ∧
   clo_to_partial_args cl = [])`;

val check_closures_def = Define `
check_closures cl cl' ⇔
  !loc num_args.
    clo_can_apply loc cl num_args ⇒ clo_can_apply loc cl' num_args`;

Theorem dest_closure_partial_is_closure:
   dest_closure max_app l v vs = SOME (Partial_app v') ⇒
   is_closure v'
Proof
  dsimp[dest_closure_def, case_eq_thms, bool_case_eq, is_closure_def, UNCURRY]
QED

Theorem is_closure_add_partial_args_nil:
   is_closure v ⇒ (clo_add_partial_args [] v = v)
Proof
  Cases_on `v` >> simp[]
QED

Theorem evaluate_app_clock0:
   s0.clock = 0 ∧ args ≠ [] ⇒
   evaluate_app lopt r args s0 ≠ (Rval vs, s)
Proof
  strip_tac >> `∃a1 args0. args = a1::args0` by (Cases_on `args` >> full_simp_tac(srw_ss())[]) >>
  simp[evaluate_def] >>
  Cases_on `dest_closure s0.max_app lopt r (a1::args0)` >> simp[] >>
  rename1 `dest_closure s0.max_app lopt r (a1::args0) = SOME c` >>
  Cases_on `c` >> simp[] >>
  rename1 `dest_closure max_app lopt r (a1::args0) = SOME (Full_app b env rest)` >>
  srw_tac[][] >>
  `SUC (LENGTH args0) ≤ LENGTH rest` by simp[] >>
  imp_res_tac dest_closure_full_length >> lfs[]
QED

Theorem evaluate_app_clock_drop:
   ∀args f lopt s0 s vs.
     evaluate_app lopt f args s0 = (Rval vs, s) ⇒
     s.clock + LENGTH args ≤ s0.clock
Proof
  gen_tac >> completeInduct_on `LENGTH args` >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `args` >>
  `args = [] ∨ ∃a1 as. args = a1::as` by (Cases_on `args` >> simp[]) >>
  dsimp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq, dec_clock_def] >>
  rpt strip_tac >> imp_res_tac evaluate_SING >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  rename1 `evaluate_app lopt r1 args' s1` >>
  Cases_on `args' = []`
  >- (full_simp_tac(srw_ss())[evaluate_def] >> srw_tac[][] >> imp_res_tac evaluate_clock >> full_simp_tac(srw_ss())[] >> simp[])
  >- (`SUC (LENGTH as) ≤ LENGTH args' + s0.clock` by simp[] >>
      `LENGTH args' < SUC (LENGTH as)`
        by (imp_res_tac dest_closure_full_length >> lfs[]) >>
      `s.clock + LENGTH args' ≤ s1.clock` by metis_tac[] >>
      imp_res_tac evaluate_clock  >> full_simp_tac(srw_ss())[] >> simp[])
QED

Theorem dest_closure_is_closure:
   dest_closure max_app lopt f vs = SOME r ⇒ is_closure f
Proof
  Cases_on `f` >> simp[is_closure_def, dest_closure_def]
QED

Theorem stage_partial_app:
   is_closure c ∧
   dest_closure max_app NONE v (rest ++ used) =
     SOME (Partial_app (clo_add_partial_args rest c)) ⇒
   dest_closure max_app NONE c rest =
     SOME (Partial_app (clo_add_partial_args rest c))
Proof
  Cases_on `v` >> simp[dest_closure_def, case_eq_thms, bool_case_eq, UNCURRY] >>
  Cases_on `c` >>
  simp[clo_add_partial_args_def, is_closure_def, check_loc_def]
QED

Theorem dest_closure_full_addargs:
   dest_closure max_app NONE c vs = SOME (Full_app b env r) ∧
   LENGTH more + LENGTH vs ≤ max_app ⇒
   dest_closure max_app NONE c (more ++ vs) = SOME (Full_app b env (more ++ r))
Proof
  Cases_on `c` >> csimp[dest_closure_def, bool_case_eq, revdroprev, UNCURRY] >>
  simp[DROP_APPEND1, revdroprev, TAKE_APPEND1, TAKE_APPEND2] >>
  simp[check_loc_def]
QED

Theorem evaluate_append:
 !es1 es2 env s.
  evaluate (es1 ++ es2, env, s) =
    case evaluate (es1, env, s) of
    | (Rval vs1, s') =>
        (case evaluate (es2, env, s') of
         | (Rval vs2, s'') => (Rval (vs1++vs2), s'')
         | x => x)
    | x => x
Proof
 Induct_on `es1` >>
 srw_tac[][evaluate_def]
 >- (
   every_case_tac >>
   srw_tac[][]) >>
 ONCE_REWRITE_TAC [evaluate_CONS] >>
 every_case_tac >>
 srw_tac[][]
QED

Theorem evaluate_GENLIST_Var:
   ∀n env s.
   evaluate (GENLIST (Var tra) n, env, s) =
   if n ≤ LENGTH env then
     (Rval (TAKE n env),s)
   else
     (Rerr (Rabort Rtype_error),s)
Proof
  Induct \\ simp[evaluate_def,GENLIST,SNOC_APPEND,evaluate_append]
  \\ rw[]
  \\ REWRITE_TAC[GSYM SNOC_APPEND]
  \\ match_mp_tac SNOC_EL_TAKE
  \\ simp[]
QED

Theorem evaluate_length_imp:
 evaluate (es,env,s1) = (Rval vs, s2) ⇒ LENGTH es = LENGTH vs
Proof
 srw_tac[][] >>
 Q.ISPECL_THEN [`es`, `env`, `s1`] mp_tac (hd (CONJUNCTS evaluate_LENGTH)) >>
 srw_tac[][]
QED

Theorem evaluate_app_length_imp:
 evaluate_app l f args s = (Rval vs, s2) ⇒ LENGTH vs = 1
Proof
 srw_tac[][] >>
 Q.ISPECL_THEN [`l`, `f`, `args`, `s`] mp_tac (hd (tl (CONJUNCTS evaluate_LENGTH))) >>
 srw_tac[][]
QED

Theorem dest_closure_none_append:
 !max_app l f args1 args2.
  dest_closure max_app NONE f args2 = NONE ⇒
  dest_closure max_app NONE f (args1 ++ args2) = NONE
Proof
 srw_tac[][dest_closure_def] >>
 Cases_on `f` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 simp []
QED

Theorem dest_closure_none_append2:
 !max_app l f args1 args2.
  LENGTH args1 + LENGTH args2 ≤ max_app ∧
  dest_closure max_app NONE f (args1 ++ args2) = NONE ⇒
  dest_closure max_app NONE f args2 = NONE
Proof
 srw_tac[][dest_closure_def] >>
 Cases_on `f` >>
 full_simp_tac(srw_ss())[check_loc_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 simp []
QED

Theorem dest_closure_rest_length:
 dest_closure max_app NONE f args = SOME (Full_app e l rest) ⇒ LENGTH rest < LENGTH args
Proof
 simp [dest_closure_def] >>
 Cases_on `f` >>
 simp [check_loc_def]
 >- (srw_tac[][] >> simp []) >>
 Cases_on `EL n l1`
 >- (srw_tac[][] >> simp [])
QED

Theorem dest_closure_partial_twice:
 ∀max_app f args1 args2 cl res.
  LENGTH args1 + LENGTH args2 ≤ max_app ∧
  dest_closure max_app NONE f (args1 ++ args2) = res ∧
  dest_closure max_app NONE f args2 = SOME (Partial_app cl)
  ⇒
  dest_closure max_app NONE cl args1 = res
Proof
 simp [dest_closure_def] >>
 Cases_on `f` >>
 simp [check_loc_def]
 >- (
   Cases_on `cl` >>
   simp [] >>
   TRY (srw_tac[][] >> NO_TAC) >>
   srw_tac[][] >>
   simp [TAKE_APPEND, DROP_APPEND] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS, NOT_LESS_EQUAL]
   >- (
     Q.ISPECL_THEN [`REVERSE args2`, `n - LENGTH l`] mp_tac TAKE_LENGTH_TOO_LONG >>
     srw_tac[][] >>
     full_simp_tac (srw_ss()++ARITH_ss) [])
   >- (
     Q.ISPECL_THEN [`REVERSE args2`, `n - LENGTH l`] mp_tac DROP_LENGTH_TOO_LONG >>
     srw_tac[][] >>
     full_simp_tac (srw_ss()++ARITH_ss) []) >>
   CCONTR_TAC >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) []) >>
 Cases_on `EL n l1` >>
 full_simp_tac(srw_ss())[] >>
 Cases_on `cl` >>
 simp [] >>
 TRY (srw_tac[][] >> NO_TAC) >>
 srw_tac[][] >>
 simp [TAKE_APPEND, DROP_APPEND] >>
 full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS, NOT_LESS_EQUAL] >>
 srw_tac[][]
 >- (
   Q.ISPECL_THEN [`REVERSE args2`, `q - LENGTH l`] mp_tac TAKE_LENGTH_TOO_LONG >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) [])
 >- (
   Q.ISPECL_THEN [`REVERSE args2`, `q - LENGTH l`] mp_tac DROP_LENGTH_TOO_LONG >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) [])
QED

Theorem evaluate_app_append:
 !args2 f args1 s.
  LENGTH (args1 ++ args2) ≤ s.max_app ⇒
  evaluate_app NONE f (args1 ++ args2) s =
    case evaluate_app NONE f args2 s of
    | (Rval vs1, s1) => evaluate_app NONE (HD vs1) args1 s1
    | err => err
Proof
 gen_tac >>
 completeInduct_on `LENGTH args2` >>
 srw_tac[][] >>
 Cases_on `args1++args2 = []`
 >- full_simp_tac(srw_ss())[evaluate_def, APPEND_eq_NIL] >>
 Cases_on `args2 = []`
 >- full_simp_tac(srw_ss())[evaluate_def, APPEND_eq_NIL] >>
 srw_tac[][evaluate_app_rw] >>
 `dest_closure s.max_app NONE f args2 = NONE ∨
   ?x. dest_closure s.max_app NONE f args2 = SOME x` by metis_tac [option_nchotomy] >>
 full_simp_tac(srw_ss())[]
 >- (
   imp_res_tac dest_closure_none_append >>
   srw_tac[][]) >>
 Cases_on `x` >>
 full_simp_tac(srw_ss())[]
 >- ( (* args2 partial app *)
   `dest_closure s.max_app NONE f (args1++args2) = NONE ∨
    ?x. dest_closure s.max_app NONE f (args1++args2) = SOME x` by metis_tac [option_nchotomy] >>
   simp []
   >- (imp_res_tac dest_closure_none_append2 >> full_simp_tac(srw_ss())[]) >>
   imp_res_tac dest_closure_partial_twice >>
   srw_tac[][] >>
   simp [] >>
   Cases_on `x` >>
   simp [] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS] >>
   imp_res_tac dest_closure_rest_length >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS] >>
   Cases_on `args1 = []` >>
   full_simp_tac (srw_ss()++ARITH_ss) [] >>
   full_simp_tac(srw_ss())[evaluate_app_rw, dec_clock_def] >>
   simp [evaluate_def] >>
   srw_tac[][] >>
   full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS])
 >- ( (* args2 full app *)
   imp_res_tac dest_closure_full_addargs >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[] >>
   srw_tac[][] >>
   first_x_assum (qspec_then `LENGTH l0` mp_tac) >>
   srw_tac[][] >>
   `LENGTH l0 < LENGTH args2` by metis_tac [dest_closure_rest_length] >>
   full_simp_tac(srw_ss())[] >>
   first_x_assum (qspec_then `l0` mp_tac) >>
   srw_tac[][] >>
   pop_assum (qspecl_then [`h`, `args1`, `r`] mp_tac) >>
   imp_res_tac evaluate_const >> fs[dec_clock_def] >>
   simp [])
QED

val revnil = Q.prove(`[] = REVERSE l ⇔ l = []`,
  CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) >> simp[])

Theorem dest_closure_full_maxapp:
   dest_closure max_app NONE c vs = SOME (Full_app b env r) ∧ r ≠ [] ⇒
   LENGTH vs ≤ max_app
Proof
  Cases_on `c` >> simp[dest_closure_def, check_loc_def, UNCURRY]
QED

Theorem dest_closure_full_split':
   dest_closure max_app loc v vs = SOME (Full_app e env rest) ⇒
   ∃used.
    vs = rest ++ used ∧ dest_closure max_app loc v used = SOME (Full_app e env [])
Proof
  simp[dest_closure_def] >> Cases_on `v` >>
  simp[bool_case_eq, revnil, DROP_NIL, DECIDE ``0n >= x ⇔ x = 0``, UNCURRY,
       NOT_LESS, DECIDE ``x:num >= y ⇔ y ≤ x``, DECIDE ``¬(x:num ≤ y) ⇔ y < x``]
  >- (strip_tac >> rename1 `TAKE (n - LENGTH l) (REVERSE vs)` >>
      dsimp[LENGTH_NIL] >> rveq >>
      simp[revdroprev] >>
      qexists_tac `DROP (LENGTH l + LENGTH vs - n) vs` >> simp[] >>
      reverse conj_tac
      >- (`vs = TAKE (LENGTH l + LENGTH vs - n) vs ++
                DROP (LENGTH l + LENGTH vs - n) vs`
             by simp[] >>
          pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
          simp[TAKE_APPEND1]) >>
      Cases_on `loc` >> lfs[check_loc_def]) >>
  simp[revdroprev] >> dsimp[LENGTH_NIL] >> rpt strip_tac >> rveq >>
  rename1 `vs = TAKE (LENGTH l + LENGTH vs - N) vs ++ _` >>
  qexists_tac `DROP (LENGTH l + LENGTH vs - N) vs` >> simp[] >>
  reverse conj_tac
  >- (`vs = TAKE (LENGTH l + LENGTH vs - N) vs ++
            DROP (LENGTH l + LENGTH vs - N) vs`
         by simp[] >>
      pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
      simp[TAKE_APPEND1]) >>
  Cases_on `loc` >> lfs[check_loc_def]
QED

Theorem dest_closure_partial_split:
 !max_app v1 vs v2 n.
  dest_closure max_app NONE v1 vs = SOME (Partial_app v2) ∧
  n ≤ LENGTH vs
  ⇒
  ?v3.
    dest_closure max_app NONE v1 (DROP n vs) = SOME (Partial_app v3) ∧
    v2 = clo_add_partial_args (TAKE n vs) v3
Proof
 srw_tac[][dest_closure_def] >>
 Cases_on `v1` >>
 simp [] >>
 full_simp_tac(srw_ss())[check_loc_def]
 >- (Cases_on `LENGTH vs + LENGTH l < n'` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][clo_add_partial_args_def] >>
     decide_tac) >>
 full_simp_tac(srw_ss())[LET_THM] >>
 Cases_on `EL n' l1` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][clo_add_partial_args_def] >>
 full_simp_tac(srw_ss())[] >>
 simp [] >>
 Cases_on `LENGTH vs + LENGTH l < q` >>
 full_simp_tac(srw_ss())[] >>
 decide_tac
QED

Theorem dest_closure_partial_split':
   ∀max_app n v vs cl.
      dest_closure max_app NONE v vs = SOME (Partial_app cl) ∧ n ≤ LENGTH vs ⇒
      ∃cl0 used rest.
         vs = rest ++ used ∧ LENGTH rest = n ∧
         dest_closure max_app NONE v used = SOME (Partial_app cl0) ∧
         cl = clo_add_partial_args rest cl0
Proof
  rpt strip_tac >>
  IMP_RES_THEN
    (IMP_RES_THEN (qx_choose_then `cl0` strip_assume_tac))
    (REWRITE_RULE [GSYM AND_IMP_INTRO] dest_closure_partial_split) >>
  map_every qexists_tac [`cl0`, `DROP n vs`, `TAKE n vs`] >> simp[]
QED

Theorem dest_closure_NONE_Full_to_Partial:
   dest_closure max_app  NONE v (l1 ++ l2) = SOME (Full_app b env []) ∧ l1 ≠ [] ⇒
   ∃cl. dest_closure max_app NONE v l2 = SOME (Partial_app cl) ∧
        dest_closure max_app NONE cl l1 = SOME (Full_app b env [])
Proof
  Cases_on `v` >>
  dsimp[dest_closure_def, bool_case_eq, revnil, DROP_NIL, GREATER_EQ,
        check_loc_def, UNCURRY] >> srw_tac[][] >>
  `0 < LENGTH l1` by (Cases_on `l1` >> full_simp_tac(srw_ss())[]) >> simp[] >>
  simp[TAKE_APPEND2] >> Cases_on `l2` >> full_simp_tac(srw_ss())[]
QED

Theorem dec_clock_with_clock[simp]:
   dec_clock s with clock := y = s with clock := y
Proof
  EVAL_TAC
QED

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
val case_eq_thms = pair_case_eq::bool_case_eq::list_case_eq::option_case_eq::map (prove_case_eq_thm o get_thms)
  [``:'a ffi_result``,``:v``,``:'a ref``,``:closLang$op``,``:word_size``, ``:eq_result``, ``:('a,'b) result``, ``:'a error_result``, ``:app_kind``] |> LIST_CONJ

Theorem do_app_ffi_error_IMP:
   do_app op vs s = Rerr (Rabort (Rffi_error f)) ==> ?i. op = FFI i
Proof
  fs [case_eq_thms,do_app_def] \\ rw [] \\ fs []
QED

Theorem do_app_add_to_clock:
   (do_app op vs (s with clock := s.clock + extra) =
    map_result (λ(v,s). (v,s with clock := s.clock + extra)) I (do_app op vs s))
Proof
  Cases_on`do_app op vs s` >>
  TRY(rename1`Rerr e`>>Cases_on`e`)>>
  TRY(rename1`Rval a`>>Cases_on`a`)>>
  TRY(rename1`Rabort a`>>Cases_on`a`)>>
  full_simp_tac(srw_ss())[do_app_cases_val,do_app_cases_err,do_app_cases_timeout] >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def,ffiTheory.call_FFI_def] >>
  srw_tac[][] >>
  fs [case_eq_thms] \\ rveq \\ fs []
  \\ rpt (pop_assum (mp_tac o GSYM))
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ rw [] \\ rpt (pop_assum (mp_tac o GSYM)) \\ rw []
  \\ TRY (drule do_app_ffi_error_IMP
          \\ rw [] \\ fs [do_app_def,case_eq_thms] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ simp [Once do_app_def]
  \\ fs [case_eq_thms]
  \\ rpt strip_tac \\ fs []
  \\ rveq \\ simp [do_app_def]
QED

Theorem do_install_add_to_clock:
   do_install vs s = (Rval e,s') ⇒
   do_install vs (s with clock := s.clock + extra) =
     (Rval e, s' with clock := s'.clock + extra)
Proof
  rw[do_install_def,case_eq_thms]
  \\ pairarg_tac
  \\ fs[case_eq_thms,pair_case_eq,bool_case_eq]
  \\ rw[] \\ fs[]
QED

Theorem do_install_type_error_add_to_clock:
   do_install vs s = (Rerr(Rabort Rtype_error),t) ⇒
   do_install vs (s with clock := s.clock + extra) =
     (Rerr(Rabort Rtype_error),t with clock := t.clock + extra)
Proof
  rw[do_install_def,case_eq_thms] \\ fs []
  \\ pairarg_tac
  \\ fs[case_eq_thms,pair_case_eq,bool_case_eq]
  \\ rw[] \\ fs[]
QED

Theorem do_install_not_Rraise[simp]:
   do_install vs s = (res,t) ==> res ≠ Rerr(Rraise r)
Proof
  rw[do_install_def,case_eq_thms,UNCURRY,bool_case_eq,pair_case_eq]
QED

Theorem do_install_not_Rffi_error[simp]:
   do_install vs s = (res,t) ==> res ≠ Rerr(Rabort (Rffi_error f))
Proof
  rw[do_install_def,case_eq_thms,UNCURRY,bool_case_eq,pair_case_eq]
QED

val s = ``s:('c,'ffi) closSem$state``;

Theorem evaluate_add_to_clock:
   (∀p es env ^s r s'.
       p = (es,env,s) ∧
       evaluate (es,env,s) = (r,s') ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate (es,env,s with clock := s.clock + extra) =
         (r,s' with clock := s'.clock + extra)) ∧
   (∀loc_opt v rest_args ^s r s'.
       evaluate_app loc_opt v rest_args s = (r,s') ∧
       r ≠ Rerr (Rabort Rtimeout_error) ⇒
       evaluate_app loc_opt v rest_args (s with clock := s.clock + extra) =
         (r,s' with clock := s'.clock + extra))
Proof
  ho_match_mp_tac evaluate_ind >>
  srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    reverse(BasicProvers.CASE_TAC) >> full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )
    >- (
      qpat_x_assum`_ = (r,_)`mp_tac >>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] )
    >> ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )) >>
  TRY (
    rename1`dest_closure` >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_length_imp >>
    fsrw_tac[ARITH_ss][] >> rev_full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[dec_clock_def] >>
    simp[state_component_equality] >>
    rename1`extra + (s.clock - (SUC n - m))` >>
    `extra + (s.clock - (SUC n - m)) = extra + s.clock - (SUC n - m)` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
  unabbrev_all_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock,LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[do_app_add_to_clock,LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def] >>
  imp_res_tac do_install_add_to_clock >> fs[] >> rw[] >>
  qpat_x_assum `evaluate (xs,env,s) = _` assume_tac >>
  TRY (drule do_install_add_to_clock \\ fs [] \\ NO_TAC) >>
  rename1 `_ = (Rerr e4,_)` >>
  Cases_on `e4` >> fs [] >>
  imp_res_tac do_install_not_Rraise >> fs [] >>
  imp_res_tac do_install_not_Rffi_error >> fs [] >>
  rename1`Rerr(Rabort abt)` >> Cases_on`abt` \\ fs[] >>
  imp_res_tac do_install_type_error_add_to_clock \\ fs[]
QED

val evaluate_add_clock = save_thm("evaluate_add_clock",
  evaluate_add_to_clock
  |> CONJUNCT1 |> SIMP_RULE std_ss []
  |> SPEC_ALL |> UNDISCH |> Q.GEN `extra`
  |> DISCH_ALL |> GEN_ALL);

Theorem evaluate_add_clock_initial_state:
   evaluate (es,env,initial_state ffi ma code co cc k) = (r,s') ∧
    r ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀extra.
      evaluate (es,env,initial_state ffi ma code co cc (k + extra)) =
      (r,s' with clock := s'.clock + extra)
Proof
  rw [] \\ drule evaluate_add_clock \\ fs []
  \\ disch_then (qspec_then `extra` mp_tac)
  \\ fs [initial_state_def]
QED

val do_app_io_events_mono = Q.prove(
  `do_app op vs s = Rval(v,s') ⇒
   s.ffi.io_events ≼ s'.ffi.io_events`,
  srw_tac[][do_app_cases_val] >>
  full_simp_tac(srw_ss())[LET_THM,
     semanticPrimitivesTheory.store_alloc_def,
     semanticPrimitivesTheory.store_lookup_def,
     semanticPrimitivesTheory.store_assign_def] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

Theorem evaluate_io_events_mono:
   (∀p. ((SND(SND p)):('c,'ffi) closSem$state).ffi.io_events ≼ (SND (evaluate p)).ffi.io_events) ∧
   (∀loc_opt v rest ^s.
     s.ffi.io_events ≼ (SND(evaluate_app loc_opt v rest s)).ffi.io_events)
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono,do_install_const]
QED

val evaluate_io_events_mono_imp = Q.prove(
  `evaluate (es,env,s) = (r,s') ⇒
    s.ffi.io_events ≼ s'.ffi.io_events`,
  metis_tac[evaluate_io_events_mono,FST,SND,PAIR])

val with_clock_ffi = Q.prove(
  `(s with clock := k).ffi = s.ffi`,EVAL_TAC)
val lemma = DECIDE``¬(x < y - z) ⇒ ((a:num) + x - (y - z) = x - (y - z) + a)``
val lemma2 = DECIDE``x ≠ 0n ⇒ a + (x - 1) = a + x - 1``
val lemma3 = DECIDE``¬(x:num < t+1) ⇒ a + (x - (t+1)) = a + x - (t+1)``

val tac =
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_def] >> full_simp_tac(srw_ss())[do_app_add_to_clock] >>
  imp_res_tac do_install_add_to_clock >> fs[] >>
  TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> full_simp_tac(srw_ss())[]) >>
  imp_res_tac do_app_io_events_mono >>
  imp_res_tac do_install_const >>
  rveq >>
  fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_COMM] >>
  rveq >> fs[] >>
  metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,SND,IS_PREFIX_TRANS,lemma,Boolv_11,lemma2,lemma3]

Theorem evaluate_add_to_clock_io_events_mono:
   (∀p es env ^s.
     p = (es,env,s) ⇒
     (SND(evaluate p)).ffi.io_events ≼
     (SND(evaluate (es,env,s with clock := s.clock + extra))).ffi.io_events) ∧
   (∀l v r ^s.
     (SND(evaluate_app l v r s)).ffi.io_events ≼
     (SND(evaluate_app l v r (s with clock := s.clock + extra))).ffi.io_events)
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][evaluate_def] >>
  TRY (
    rename1`Boolv T` >>
    qmatch_assum_rename_tac`IS_SOME _.ffi.final_event` >>
    ntac 6 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> tac) >>
  TRY (
    rename1`dest_closure` >>
    ntac 4 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[dec_clock_ffi]) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[dec_clock_def] >>
    imp_res_tac lemma >> full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][] >> tac) >>
  unabbrev_all_tac >> full_simp_tac(srw_ss())[LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[evaluate_def] >>
  tac
QED

Theorem do_app_never_timesout[simp]:
   do_app op args s ≠ Rerr (Rabort Rtimeout_error)
Proof
  Cases_on `op` >> Cases_on `args` >>
  simp[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq]
QED

Theorem evaluate_timeout_clocks0:
   (∀v (s:('c,'ffi) closSem$state).
      evaluate v = (Rerr (Rabort Rtimeout_error), s) ⇒ s.clock = 0) ∧
   (∀locopt v env (s:('c,'ffi) closSem$state) s'.
       evaluate_app locopt v env s = (Rerr (Rabort Rtimeout_error), s') ⇒
       s'.clock = 0)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  dsimp[evaluate_def, case_eq_thms, pair_case_eq, bool_case_eq] >>
  rw[] >> pop_assum mp_tac >>
  simp_tac (srw_ss()) [do_install_def,case_eq_thms,bool_case_eq,pair_case_eq,UNCURRY,LET_THM] >>
  rw[] >> fs []
QED

val _ = export_rewrites ["closLang.exp_size_def"]

Theorem exp_size_MEM:
   (∀e elist. MEM e elist ⇒ exp_size e < exp3_size elist) ∧
   (∀x e ealist. MEM (x,e) ealist ⇒ exp_size e < exp1_size ealist)
Proof
  conj_tac >| [Induct_on `elist`, Induct_on `ealist`] >> dsimp[] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem evaluate_eq_nil[simp]:
   closSem$evaluate(es,env,s0) = (Rval [], s) ⇔ s0 = s ∧ es = []
Proof
  Cases_on `es` >> simp[evaluate_def] >>
  strip_tac >> rename1 `evaluate(h::t, env, s0)` >>
  Q.ISPECL_THEN [`h::t`, `env`, `s0`] mp_tac (CONJUNCT1 evaluate_LENGTH) >>
  simp[]
QED


(* finding the SetGlobal operations *)
val op_gbag_def = Define`
  op_gbag (SetGlobal n) = BAG_INSERT n {||} ∧
  op_gbag _ = {||}
`;

Theorem exp2_size_rw[simp]:
   exp2_size h = 1 + FST h + exp_size (SND h)
Proof
  Cases_on `h` >> simp[]
QED

Theorem exp1_size_rw[simp]:
   exp1_size fbinds =
     exp3_size (MAP SND fbinds) + SUM (MAP FST fbinds) + LENGTH fbinds
Proof
  Induct_on `fbinds` >> simp[]
QED

val set_globals_def = tDefine "set_globals" `
  (set_globals (Var _ _) = {||}) ∧
  (set_globals (If _ e1 e2 e3) =
    set_globals e1 ⊎ set_globals e2 ⊎ set_globals e3) ∧
  (set_globals (Let _ binds e) = set_globals e ⊎ elist_globals binds) ∧
  (set_globals (Raise _ e) = set_globals e) ∧
  (set_globals (Handle _ e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Tick _ e) = set_globals e) ∧
  (set_globals (Call _ _ _ args) = elist_globals args) ∧
  (set_globals (App _ _ f args) = set_globals f ⊎ elist_globals args) ∧
  (set_globals (Fn _ _ _ _ bod) = set_globals bod) ∧
  (set_globals (Letrec _ _ _ fbinds bod) =
    set_globals bod ⊎ elist_globals (MAP SND fbinds)) ∧
  (set_globals (Op _ opn args) = op_gbag opn ⊎ elist_globals args) ∧
  (elist_globals [] = {||}) ∧
  (elist_globals (e::es) = set_globals e ⊎ elist_globals es)
`
  (WF_REL_TAC `
      measure (λa. case a of INL e => exp_size e | INR x => exp3_size x)` >>
   simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])
val _ = export_rewrites ["set_globals_def"]

(* {foo}sgc_free: foo is free of SetGlobal closures, meaning closures that
   include calls to SetGlobal, for
     foo = {(e)xpr, (v)alue, (r)esult, and (s)tate}
*)
Theorem v_size_lemma:
   MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl
Proof
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]
QED

(* value is setglobal-closure free *)
val vsgc_free_def = tDefine "vsgc_free" `
  (vsgc_free (Closure _ VL1 VL2 _ body) ⇔
     set_globals body = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Recclosure _ VL1 VL2 bods _) ⇔
     elist_globals (MAP SND bods) = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Block _ VL) ⇔ EVERY vsgc_free VL) ∧
  (vsgc_free _ ⇔ T)
` (WF_REL_TAC `measure closSem$v_size` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])

val vsgc_free_def = save_thm(
  "vsgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] vsgc_free_def)

Theorem vsgc_free_Unit[simp]:
   vsgc_free Unit
Proof
  simp[Unit_def]
QED

Theorem vsgc_free_Boolv[simp]:
   vsgc_free (Boolv b)
Proof
  simp[Boolv_def]
QED

(* result is setglobal-closure free *)
val rsgc_free_def = Define`
  (rsgc_free (Rval vs) ⇔ EVERY vsgc_free vs) ∧
  (rsgc_free (Rerr (Rabort _)) ⇔ T) ∧
  (rsgc_free (Rerr (Rraise v)) ⇔ vsgc_free v)
`;
val _ = export_rewrites ["rsgc_free_def"]

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Var _ _) ⇔ T) ∧
  (esgc_free (If _ e1 e2 e3) ⇔ esgc_free e1 ∧ esgc_free e2 ∧ esgc_free e3) ∧
  (esgc_free (Let _ binds e) ⇔ EVERY esgc_free binds ∧ esgc_free e) ∧
  (esgc_free (Raise _ e) ⇔ esgc_free e) ∧
  (esgc_free (Handle _ e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Tick _ e) ⇔ esgc_free e) ∧
  (esgc_free (Call _ _ _ args) ⇔ EVERY esgc_free args) ∧
  (esgc_free (App _ _ e args) ⇔ esgc_free e ∧ EVERY esgc_free args) ∧
  (esgc_free (Fn _ _ _ _ b) ⇔ set_globals b = {||}) ∧
  (esgc_free (Letrec _ _ _ binds bod) ⇔
    elist_globals (MAP SND binds) = {||} ∧ esgc_free bod) ∧
  (esgc_free (Op _ _ args) ⇔ EVERY esgc_free args)
` (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])
val esgc_free_def = save_thm("esgc_free_def[simp,compute]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

(* state is setglobal-closure free *)
val ssgc_free_def = Define`
  ssgc_free ^s ⇔
    (∀n m e. FLOOKUP s.code n = SOME (m,e) ⇒ set_globals e = {||}) ∧
    (∀n vl. FLOOKUP s.refs n = SOME (ValueArray vl) ⇒ EVERY vsgc_free vl) ∧
    (∀v. MEM (SOME v) s.globals ⇒ vsgc_free v) ∧
    (∀n exp aux. SND (s.compile_oracle n) = (exp, aux) ⇒ EVERY esgc_free exp ∧
         elist_globals (MAP (SND o SND) aux) = {||})
`;

Theorem ssgc_free_clockupd[simp]:
   ssgc_free (s with clock updated_by f) = ssgc_free s
Proof
  simp[ssgc_free_def]
QED

Theorem ssgc_free_dec_clock[simp]:
   ssgc_free (dec_clock n s) ⇔ ssgc_free s
Proof
  simp[dec_clock_def]
QED

Theorem elglobals_EQ_EMPTY:
   elist_globals l = {||} ⇔ ∀e. MEM e l ⇒ set_globals e = {||}
Proof
  Induct_on `l` >> dsimp[]
QED

Theorem set_globals_empty_esgc_free:
   set_globals e = {||} ⇒ esgc_free e
Proof
  completeInduct_on `exp_size e` >> fs[PULL_FORALL] >> Cases >>
  simp[] >> strip_tac >> rveq >> fs[AND_IMP_INTRO] >>
  simp[EVERY_MEM, elglobals_EQ_EMPTY, MEM_MAP] >>
  rw[] >> rw[] >>
  first_x_assum irule >> simp[] >> imp_res_tac exp_size_MEM >> simp[]
QED

Theorem elist_globals_append:
   ∀a b. elist_globals (a++b) =
  elist_globals a ⊎ elist_globals b
Proof
  Induct>>fs[set_globals_def,ASSOC_BAG_UNION]
QED
Theorem elist_globals_FOLDR:
   elist_globals es = FOLDR BAG_UNION {||} (MAP set_globals es)
Proof
  Induct_on `es` >> simp[]
QED

Theorem elist_globals_reverse:
   ∀ls. elist_globals (REVERSE ls) = elist_globals ls
Proof
  Induct>>fs[set_globals_def,elist_globals_append,COMM_BAG_UNION]
QED

val ignore_table_def = Define`
  ignore_table f st (code,aux) = let (st',code') = f st code in (st',(code',aux))`;

Theorem ignore_table_imp:
   ignore_table f st p = (st',p') ⇒ SND p' = SND p
Proof
  Cases_on`p` \\ EVAL_TAC
  \\ pairarg_tac \\ rw[] \\ rw[]
QED

Theorem SND_SND_ignore_table:
   SND (SND (ignore_table f st p)) = SND p
Proof
  Cases_on`p` \\ EVAL_TAC \\ pairarg_tac \\ fs[]
QED

Theorem FST_SND_ignore_table:
   FST (SND (ignore_table f st p)) = SND (f st (FST p))
Proof
  Cases_on`p` \\ EVAL_TAC \\ pairarg_tac \\ fs[]
QED

(* generic do_app compile proof *)

val isClos_def = Define `
  isClos (Closure x1 x2 x3 x4 x5) = T /\
  isClos (Recclosure y1 y2 y3 y4 y5) = T /\
  isClos _ = F`
val _ = export_rewrites ["isClos_def"];

Theorem isClos_cases:
   isClos x <=>
    (?x1 x2 x3 x4 x5. x = Closure x1 x2 x3 x4 x5) \/
    (?y1 y2 y3 y4 y5. x = Recclosure y1 y2 y3 y4 y5)
Proof
  Cases_on `x` \\ fs []
QED

val simple_val_rel_def = Define `
  simple_val_rel vr <=>
   (∀x n. vr x (Number n) ⇔ x = Number n) ∧
   (∀x p n.
      vr x (Block n p) ⇔
      ∃xs. x = Block n xs ∧ LIST_REL vr xs p) ∧
   (∀x p. vr x (Word64 p) ⇔ x = Word64 p) ∧
   (∀x p. vr x (ByteVector p) ⇔ x = ByteVector p) ∧
   (∀x p. vr x (RefPtr p) ⇔ x = RefPtr p) ∧
   (∀x5 x4 x3 x2 x1 x.
      vr x (Closure x1 x2 x3 x4 x5) ==> isClos x) ∧
   (∀y5 y4 y3 y2 y1 x.
      vr x (Recclosure y1 y2 y3 y4 y5) ==> isClos x)`

val simple_val_rel_alt = prove(
  ``simple_val_rel vr <=>
     (∀x n. vr x (Number n) ⇔ x = Number n) ∧
     (∀x p n.
        vr x (Block n p) ⇔
        ∃xs. x = Block n xs ∧ LIST_REL vr xs p) ∧
     (∀x p. vr x (Word64 p) ⇔ x = Word64 p) ∧
     (∀x p. vr x (ByteVector p) ⇔ x = ByteVector p) ∧
     (∀x p. vr x (RefPtr p) ⇔ x = RefPtr p) ∧
     (∀x5 x4 x3 x2 x1 x.
        vr x (Closure x1 x2 x3 x4 x5) ==> isClos x) ∧
     (∀y5 y4 y3 y2 y1 x.
        vr x (Recclosure y1 y2 y3 y4 y5) ==> isClos x) /\
     (!b1 b2. vr (Boolv b1) (Boolv b2) <=> (b1 = b2))``,
  rw [simple_val_rel_def] \\ eq_tac \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ Cases_on `b1` \\ Cases_on `b2` \\ fs [Boolv_def] \\ EVAL_TAC);

val simple_state_rel_def = Define `
  simple_state_rel vr sr <=>
    (!s t ptr. FLOOKUP t.refs ptr = NONE /\ sr s t ==>
               FLOOKUP s.refs ptr = NONE) /\
    (∀w t s ptr b.
      FLOOKUP t.refs ptr = SOME (ByteArray b w) ∧ sr s t ⇒
      FLOOKUP s.refs ptr = SOME (ByteArray b w)) /\
    (∀w (t:('c,'ffi) closSem$state) (s:('d,'ffi) closSem$state) ptr.
      FLOOKUP t.refs ptr = SOME (ValueArray w) ∧ sr s t ⇒
      ∃w1.
        FLOOKUP s.refs ptr = SOME (ValueArray w1) ∧
        LIST_REL vr w1 w) /\
    (!s t. sr s t ==> s.ffi = t.ffi /\ FDOM s.refs = FDOM t.refs /\
                      LIST_REL (OPTREL vr) s.globals t.globals) /\
    (!f s t.
      sr s t ==> sr (s with ffi := f)
                    (t with ffi := f)) /\
    (!f bs s t p.
      sr s t ==> sr (s with refs := s.refs |+ (p,ByteArray f bs))
                    (t with refs := t.refs |+ (p,ByteArray f bs))) /\
    (!s t p xs ys.
      sr s t /\ LIST_REL vr xs ys ==>
      sr (s with refs := s.refs |+ (p,ValueArray xs))
         (t with refs := t.refs |+ (p,ValueArray ys))) /\
    (!s t xs ys.
      sr s t /\ LIST_REL (OPTREL vr) xs ys ==>
      sr (s with globals := xs) (t with globals := ys))`

Theorem simple_state_rel_ffi:
   simple_state_rel vr sr /\ sr s t ==> s.ffi = t.ffi
Proof
  fs [simple_state_rel_def]
QED

Theorem simple_state_rel_fdom:
   simple_state_rel vr sr /\ sr s t ==> FDOM s.refs = FDOM t.refs
Proof
  fs [simple_state_rel_def]
QED

val simple_state_rel_update_ffi = prove(
  ``simple_state_rel vr sr /\ sr s t ==>
    sr (s with ffi := f) (t with ffi := f)``,
  fs [simple_state_rel_def]);

val simple_state_rel_update_bytes = prove(
  ``simple_state_rel vr sr /\ sr s t ==>
    sr (s with refs := s.refs |+ (p,ByteArray f bs))
       (t with refs := t.refs |+ (p,ByteArray f bs))``,
  fs [simple_state_rel_def]);

val simple_state_rel_update = prove(
  ``simple_state_rel vr sr /\ sr s t /\ LIST_REL vr xs ys ==>
    sr (s with refs := s.refs |+ (p,ValueArray xs))
       (t with refs := t.refs |+ (p,ValueArray ys))``,
  fs [simple_state_rel_def]);

val simple_state_rel_update_globals = prove(
  ``simple_state_rel vr sr /\ sr s t /\ LIST_REL (OPTREL vr) xs ys ==>
    sr (s with globals := xs) (t with globals := ys)``,
  fs [simple_state_rel_def]);

val simple_state_rel_get_global = prove(
  ``simple_state_rel vr sr /\ sr s t /\ get_global n t.globals = x ⇒
    case x of
    | NONE => get_global n s.globals = NONE
    | SOME NONE => get_global n s.globals = SOME NONE
    | SOME (SOME y) => ?x. get_global n s.globals = SOME (SOME x) /\ vr x y``,
  fs [simple_state_rel_def] \\ fs [get_global_def] \\ rw [] \\ fs []
  \\ `LIST_REL (OPTREL vr) s.globals t.globals` by fs []
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ fs [LIST_REL_EL_EQN]
  \\ qpat_x_assum `_ = _` assume_tac \\ fs []
  \\ first_x_assum drule
  \\ Cases_on `EL n t.globals` \\ fs [OPTREL_def]);

val isClos_IMP_v_to_list_NONE = prove(
  ``isClos x ==> v_to_list x = NONE``,
  Cases_on `x` \\ fs [v_to_list_def]);

val v_rel_to_list_ByteVector = prove(
  ``simple_val_rel vr ==>
    !lv x.
      vr x lv ==>
      !wss. (v_to_list x = SOME (MAP ByteVector wss) <=>
             v_to_list lv = SOME (MAP ByteVector wss))``,
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ rveq
  \\ imp_res_tac isClos_IMP_v_to_list_NONE \\ fs []
  \\ first_x_assum drule
  \\ fs [case_eq_thms]
  \\ Cases_on `wss` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ rfs []
  \\ Cases_on `h` \\ fs [] \\ rfs []
  \\ res_tac \\ fs []);

val v_rel_to_list_byte = prove(
  ``simple_val_rel vr ==>
    !y x.
      vr x y ==>
      !ns. (v_to_list x = SOME (MAP (Number ∘ $&) ns) ∧
            EVERY (λn. n < 256) ns) <=>
           (v_to_list y = SOME (MAP (Number ∘ $&) ns) ∧
            EVERY (λn. n < 256) ns)``,
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def] \\ res_tac
  \\ imp_res_tac isClos_IMP_v_to_list_NONE \\ fs []
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ first_x_assum drule \\ strip_tac
  \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ rfs []
  \\ res_tac \\ fs []);

val v_to_list_SOME = prove(
  ``simple_val_rel vr ==>
    !y ys x.
      vr x y /\ v_to_list y = SOME ys ==>
      ∃xs. LIST_REL vr xs ys ∧ v_to_list x = SOME xs``,
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def] \\ rveq \\ fs []
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ res_tac \\ fs []);

val v_to_list_NONE = prove(
  ``simple_val_rel vr ==>
    !y x. vr x y /\ v_to_list y = NONE ==>
          v_to_list x = NONE``,
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def] \\ res_tac
  \\ imp_res_tac isClos_IMP_v_to_list_NONE \\ fs []
  \\ rw [] \\ fs [case_eq_thms]);

val v_rel_do_eq = prove(
  ``simple_val_rel vr ==>
    (!y1 y2 x1 x2.
      vr x1 y1 /\ vr x2 y2 ==>
      do_eq x1 x2 = do_eq y1 y2) /\
    (!y1 y2 x1 x2.
      LIST_REL vr x1 y1 /\ LIST_REL vr x2 y2 ==>
      do_eq_list x1 x2 = do_eq_list y1 y2)``,
  strip_tac \\ fs [simple_val_rel_def]
  \\ ho_match_mp_tac do_eq_ind \\ rw []
  THEN1
   (Cases_on `y1` \\ fs [] \\ rfs [] \\ rveq \\ fs []
    \\ Cases_on `y2` \\ rfs [do_eq_def]
    \\ res_tac \\ fs [isClos_cases]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ once_rewrite_tac [do_eq_def]
  \\ fs [case_eq_thms]
  \\ Cases_on `do_eq y1 y2` \\ fs []
  \\ Cases_on `b` \\ fs []);

Theorem simple_state_rel_FLOOKUP_refs_IMP:
   simple_state_rel vr sr /\ sr s t /\
    FLOOKUP t.refs p = x ==>
    case x of
    | NONE => FLOOKUP s.refs p = NONE
    | SOME (ByteArray f bs) => FLOOKUP s.refs p = SOME (ByteArray f bs)
    | SOME (ValueArray vs) =>
        ?xs. FLOOKUP s.refs p = SOME (ValueArray xs) /\ LIST_REL vr xs vs
Proof
  fs [simple_state_rel_def] \\ Cases_on `x` \\ rw []
  \\ res_tac \\ fs [] \\ rename1 `_ = SOME yy` \\ Cases_on `yy` \\ fs []
QED

val refs_ffi_lemma = prove(
  ``((s:('c,'ffi) closSem$state) with <|refs := refs'; ffi := ffi'|>) =
    ((s with refs := refs') with ffi := ffi')``,
  fs []);

Theorem simple_val_rel_list:
   !x x1 xs vr.
     simple_val_rel vr /\
     vr x x1 /\
     v_to_list x1 = SOME xs
     ==>
     ?xs1.
     vr (list_to_v xs1) (list_to_v xs) /\
     v_to_list x = SOME xs1
Proof
   recInduct v_to_list_ind \\ rw []
   \\ fs [v_to_list_def, list_to_v_def]
   \\ rfs [simple_val_rel_alt] \\ rw [] \\ rfs []
   \\ Cases_on `x1` \\ fs [] \\ rfs [] \\ rw []
   \\ fs [v_to_list_def, list_to_v_def] \\ rw []
   \\ fs [v_to_list_def, list_to_v_def] \\ rw []
   \\ fs [case_eq_thms] \\ rw []
   \\ Cases_on `y'` \\ fs [v_to_list_def] \\ rfs [] \\ fs [] \\ rw []
   \\ fs [list_to_v_def, PULL_EXISTS]
   \\ first_x_assum drule
   \\ rpt (disch_then drule \\ fs []) \\ rw []
   \\ metis_tac []
QED

Theorem simple_val_rel_APPEND:
   !xs1 ys1 xs2 ys2 vr.
   simple_val_rel vr /\
   vr (list_to_v xs1) (list_to_v xs2) /\
   vr (list_to_v ys1) (list_to_v ys2)
   ==>
   vr (list_to_v (xs1++ys1)) (list_to_v (xs2++ys2))
Proof
  Induct \\ rw []
  \\ rfs [simple_val_rel_alt]
  \\ fs [list_to_v_def]
  \\ Cases_on `xs2` \\ rfs [list_to_v_def]
  \\ first_x_assum drule
  \\ fs [PULL_EXISTS]
  \\ metis_tac []
QED

Theorem vr_list_NONE:
   !x x1 vr.
   simple_val_rel vr /\
   vr x x1 /\
   v_to_list x1 = NONE ==>
   v_to_list x = NONE
Proof
  recInduct v_to_list_ind \\ rw []
  \\ Cases_on `x1` \\ rfs [simple_val_rel_alt]
  \\ fs [v_to_list_def] \\ rw [] \\ fs [v_to_list_def, case_eq_thms]
  \\ TRY (first_x_assum drule)
  \\ rpt (disch_then drule \\ fs [])
  \\ rw [] \\ metis_tac [isClos_def]
QED

val _ = print "The following proof is slow due to Rerr cases.\n"
val simple_val_rel_do_app_rev = time store_thm("simple_val_rel_do_app_rev",
  ``simple_val_rel vr /\ simple_state_rel vr sr ==>
    sr s (t:('c,'ffi) closSem$state) /\ LIST_REL vr xs ys ==>
    case do_app opp ys t of
    | Rerr err2 => (?err1. do_app opp xs s = Rerr err1 /\
                           exc_rel vr err1 err2)
    | Rval (y,t1) => ?x s1. vr x y /\ sr s1 t1 /\
                            do_app opp xs s = Rval (x,s1)``,
  strip_tac
  \\ `?this_is_case. this_is_case opp` by (qexists_tac `K T` \\ fs [])
  \\ Cases_on `opp = ListAppend`
  THEN1
   (Cases_on `do_app opp ys t` \\ pop_assum mp_tac
    \\ rw [do_app_def, case_eq_thms, pair_case_eq, bool_case_eq, PULL_EXISTS]
    \\ TRY CASE_TAC \\ fs [] \\ rw []
    \\ metis_tac [simple_val_rel_list, simple_val_rel_APPEND, vr_list_NONE])
  \\ Cases_on `opp = Add \/ opp = Sub \/ opp = Mult \/ opp = Div \/ opp = Mod \/
               opp = Less \/ opp = LessEq \/ opp = Greater \/ opp = GreaterEq \/
               opp = LengthBlock \/ (?i. opp = Const i) \/ opp = WordFromInt \/
               (?f. opp = FP_cmp f) \/ (?s. opp = String s) \/
               (?f. opp = FP_uop f) \/ (opp = BoundsCheckBlock) \/
               (?f. opp = FP_bop f) \/ (?f. opp = FP_top f) \/
               opp = WordToInt \/ opp = ConfigGC \/
               (?n. opp = Label n) \/ (?n. opp = Cons n) \/
               (?i. opp = LessConstSmall i) \/ opp = LengthByteVec \/
               (?i. opp = EqualInt i) \/ (?n. opp = TagEq n) \/
               (?n n1. opp = TagLenEq n n1) \/ opp = Install \/
               (?w oo k. opp = WordShift w oo k) \/
               (?b. opp = WordFromWord b) \/
               (?w oo. opp = WordOp w oo) \/ opp = ConcatByteVec`
  THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq,bool_case_eq,Unit_def]
    \\ strip_tac \\ rveq
    \\ drule v_rel_to_list_ByteVector
    \\ rfs [simple_val_rel_alt] \\ rveq \\ fs []
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC))
  \\ Cases_on `opp = Length \/ (?b. opp = BoundsCheckByte b) \/
               opp = BoundsCheckArray \/ opp = LengthByte \/
               opp = DerefByteVec \/ opp = DerefByte \/ opp = Deref \/
               opp = GlobalsPtr \/ opp = El \/ opp = SetGlobalsPtr`
  THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq,bool_case_eq]
    \\ strip_tac \\ rveq \\ fs [] \\ rpt strip_tac \\ rveq \\ fs []
    \\ rfs [simple_val_rel_alt] \\ rveq \\ fs []
    \\ drule (GEN_ALL simple_state_rel_FLOOKUP_refs_IMP)
    \\ disch_then drule \\ disch_then imp_res_tac \\ fs []
    \\ rpt strip_tac \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [LIST_REL_EL_EQN]
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC)
    \\ first_x_assum match_mp_tac
    \\ imp_res_tac (prove(``0 <= (i:int) ==> ?n. i = & n``,Cases_on `i` \\ fs []))
    \\ rveq \\ fs [])
  \\ Cases_on `?n. opp = ConsExtend n` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq,bool_case_eq]
    \\ strip_tac \\ rveq \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC)
    \\ match_mp_tac EVERY2_APPEND_suff \\ fs []
    \\ match_mp_tac EVERY2_TAKE \\ fs []
    \\ match_mp_tac EVERY2_DROP \\ fs [])
  \\ Cases_on `opp = FromListByte` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ drule v_rel_to_list_byte \\ fs []
    \\ disch_then drule
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs [])
  \\ Cases_on `?b. opp = FromList b` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ drule v_to_list_SOME \\ disch_then drule \\ fs []
    \\ drule v_to_list_NONE \\ disch_then drule \\ fs []
    \\ strip_tac \\ fs []
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs [])
  \\ Cases_on `?n. opp = Global n` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ drule (GEN_ALL simple_state_rel_get_global)
    \\ rpt (disch_then drule \\ fs [])
    \\ disch_then (qspec_then `n` mp_tac) \\ fs []
    \\ strip_tac \\ fs [])
  \\ Cases_on `opp = Equal` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ imp_res_tac v_rel_do_eq \\ fs []
    \\ Cases_on `b` \\ fs [Boolv_def]
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs [])
  \\ Cases_on `?n. opp = SetGlobal n` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ fs [] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ fs [closSemTheory.Unit_def]
    \\ drule (GEN_ALL simple_state_rel_get_global)
    \\ rpt (disch_then drule) \\ fs [] \\ rpt strip_tac \\ fs []
    \\ match_mp_tac simple_state_rel_update_globals \\ fs []
    \\ match_mp_tac EVERY2_LUPDATE_same \\ fs []
    \\ fs [OPTREL_def] \\ fs [simple_state_rel_def])
  \\ Cases_on `opp = AllocGlobal` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ fs [closSemTheory.Unit_def]
    \\ match_mp_tac simple_state_rel_update_globals \\ fs []
    \\ fs [OPTREL_def] \\ fs [simple_state_rel_def])
  \\ Cases_on `opp = RefArray \/ opp = Ref \/ (?b. opp = RefByte b)` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC)
    \\ `FDOM s.refs = FDOM t.refs` by fs [simple_state_rel_def] \\ fs []
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update))
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update_bytes))
    \\ asm_exists_tac \\ fs [LIST_REL_REPLICATE_same])
  \\ Cases_on `opp = UpdateByte \/ opp = Update \/ ?n. opp = FFI n` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq] \\ strip_tac \\ rveq
    \\ simp [PULL_EXISTS] \\ rpt strip_tac \\ rveq
    \\ fs [case_eq_thms,pair_case_eq,bool_case_eq]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ fs [closSemTheory.Unit_def]
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC)
    \\ drule (GEN_ALL simple_state_rel_FLOOKUP_refs_IMP)
    \\ rpt (disch_then drule) \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ `s.ffi = t.ffi` by fs [simple_state_rel_def] \\ fs []
    \\ rewrite_tac [refs_ffi_lemma]
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update_ffi))
    \\ TRY (asm_exists_tac \\ fs [])
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update_bytes))
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update))
    \\ asm_exists_tac \\ fs []
    \\ match_mp_tac EVERY2_LUPDATE_same \\ fs [])
  \\ Cases_on `?b. opp = CopyByte b` THEN1
   (Cases_on `do_app opp ys t` \\ fs [] \\ rveq \\ pop_assum mp_tac
    \\ simp [do_app_def,case_eq_thms,pair_case_eq,bool_case_eq]
    \\ strip_tac \\ rveq
    \\ rfs [simple_val_rel_def] \\ rveq \\ fs []
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ TRY (res_tac \\ fs [isClos_cases] \\ NO_TAC)
    \\ drule (GEN_ALL simple_state_rel_FLOOKUP_refs_IMP)
    \\ disch_then drule
    \\ disch_then imp_res_tac \\ fs []
    \\ fs [closSemTheory.Unit_def]
    \\ TRY (match_mp_tac (GEN_ALL simple_state_rel_update_bytes))
    \\ asm_exists_tac \\ fs [LIST_REL_REPLICATE_same])
  \\ Cases_on `opp` \\ fs []);

Theorem simple_val_rel_do_app:
   simple_val_rel vr /\ simple_state_rel vr sr ==>
    sr s (t:('c,'ffi) closSem$state) /\ LIST_REL vr xs ys ==>
    case do_app opp xs s of
    | Rerr err1 => (?err2. do_app opp ys t = Rerr err2 /\
                           exc_rel vr err1 err2)
    | Rval (x,s1) => ?y t1. vr x y /\ sr s1 t1 /\
                            do_app opp ys t = Rval (y,t1)
Proof
  rpt strip_tac
  \\ mp_tac simple_val_rel_do_app_rev \\ fs []
  \\ Cases_on `do_app opp xs s` \\ fs []
  \\ Cases_on `do_app opp ys t` \\ fs []
  \\ TRY (PairCases_on `a` \\ fs [])
  \\ TRY (PairCases_on `a'` \\ fs [])
QED

(* a generic semantics preservation lemma *)

val FST_EQ_LEMMA = prove(
  ``FST x = y <=> ?y1. x = (y,y1)``,
  Cases_on `x` \\ fs []);

Theorem initial_state_max_app[simp]:
   (initial_state ffi max_app code co cc k).max_app = max_app
Proof
  EVAL_TAC
QED

val eval_sim_def = Define `
  eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2 rel allow_fail =
    !k res1 s2.
      evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k) = (res1,s2) /\
      (allow_fail \/ res1 <> Rerr (Rabort Rtype_error)) /\
      rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
      ?ck res2 t2.
        evaluate (es2,[],
          initial_state ffi max_app code2 co2 cc2 (k+ck)) = (res2,t2) /\
        result_rel (\x y. T) (\x y. T) res1 res2 /\ s2.ffi = t2.ffi`

val evaluate_add_to_clock_io_events_mono_alt =
  evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> CONJUNCT1 |> SPEC_ALL
  |> DISCH ``evaluate (es,env,s) = (res,s1:('c,'ffi) closSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;

val initial_state_with_clock = prove(
  ``(initial_state ffi ma code co cc k with clock :=
      (initial_state ffi ma code co cc k).clock + ck) =
    initial_state ffi ma code co cc (k + ck)``,
  fs [initial_state_def]);

Theorem IMP_semantics_eq:
   eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2 rel F /\
   semantics (ffi:'ffi ffi_state) max_app code1 co1 cc1 es1 <> Fail ==>
   rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
   semantics ffi max_app code2 co2 cc2 es2 =
   semantics ffi max_app code1 co1 cc1 es1
Proof
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ simp [Once semantics_def]
  \\ IF_CASES_TAC \\ fs [] \\ disch_then kall_tac
  \\ strip_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once semantics_def] \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs [] THEN1
     (first_x_assum (qspec_then `k'` mp_tac)
      \\ strip_tac
      \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k')`
      \\ fs [eval_sim_def]
      \\ last_x_assum drule \\ fs []
      \\ CCONTR_TAC \\ fs[]
      \\ fs [FST_EQ_LEMMA]
      \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
      \\ drule evaluate_add_clock_initial_state \\ fs []
      \\ qexists_tac `ck` \\ fs []
      \\ CCONTR_TAC \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ reverse conj_tac
    THEN1
     (fs [FST_EQ_LEMMA]
      \\ rveq \\ fs [eval_sim_def]
      \\ first_x_assum drule \\ fs []
      \\ impl_tac
      THEN1 (fs [FST_EQ_LEMMA] \\ strip_tac \\ fs [] \\ rfs [])
      \\ strip_tac
      \\ asm_exists_tac \\ fs []
      \\ every_case_tac \\ fs [] \\ rveq \\ fs []
      \\ Cases_on `r` \\ fs []
      \\ Cases_on `e` \\ fs [])
    \\ gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ qabbrev_tac `st1 = initial_state ffi max_app code1 co1 cc1`
    \\ qabbrev_tac `st2 = initial_state ffi max_app code2 co2 cc2`
    \\ drule evaluate_add_to_clock_io_events_mono_alt
    \\ qpat_x_assum `evaluate (es1,[],st1 k) = _` assume_tac
    \\ drule evaluate_add_to_clock_io_events_mono_alt
    \\ `!extra k. st1 k with clock := (st1 k).clock + extra = st1 (k + extra)`
          by (unabbrev_all_tac \\ fs [initial_state_def])
    \\ `!extra k. st2 k with clock := (st2 k).clock + extra = st2 (k + extra)`
          by (unabbrev_all_tac \\ fs [initial_state_def])
    \\ fs []
    \\ ntac 2 (disch_then assume_tac)
    \\ qpat_x_assum `∀extra._` mp_tac
    \\ first_x_assum (qspec_then `k'` assume_tac)
    \\ first_assum (subterm (fn tm =>
          Cases_on`^(assert has_pair_type tm)`) o concl)
    \\ fs []
    \\ strip_tac
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ impl_tac THEN1 (fs [FST_EQ_LEMMA] \\ strip_tac \\ fs [] \\ rfs [])
    \\ strip_tac \\ rveq \\ fs []
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac
    >- (strip_tac \\ rveq \\ fs [FST_EQ_LEMMA] \\ rfs [])
    \\ disch_then (qspec_then `ck + k` mp_tac)
    \\ unabbrev_all_tac \\ fs [initial_state_def]
    \\ ntac 2 strip_tac \\ rveq \\ fs []
    \\ qpat_x_assum `_ ==> _` mp_tac \\ impl_tac THEN1 (strip_tac \\ fs [])
    \\ qpat_x_assum `_ ==> _` mp_tac \\ impl_tac THEN1 (strip_tac \\ fs [])
    \\ disch_then (qspec_then `0` assume_tac)
    \\ disch_then (qspec_then `k'` assume_tac)
    \\ fs []
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (last_x_assum (qspec_then `k` assume_tac) \\ rfs [FST_EQ_LEMMA]
    \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)` \\ fs []
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ qexists_tac `ck` \\ fs [initial_state_def]
    \\ CCONTR_TAC \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  THEN1
   (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac \\ fs[]
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (assume_tac o GSYM)
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ qpat_x_assum `∀x y. ¬z` mp_tac \\ simp []
    \\ qexists_tac `k` \\ simp []
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ disch_then (qspec_then `ck` mp_tac)
    \\ fs [initial_state_with_clock]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ rpt (CASE_TAC \\ fs []))
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  THEN1
   (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ strip_tac \\ fs [LESS_EQ_EXISTS] \\ rveq
    \\ metis_tac
        [evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)`
  \\ rveq \\ fs [eval_sim_def]
  \\ first_x_assum drule \\ fs []
  \\ impl_tac
  THEN1 (CCONTR_TAC \\ fs [FST_EQ_LEMMA] \\ rfs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  THEN1 (qexists_tac `ck + k` \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < (LENGTH (_ ffi1))`
  \\ qsuff_tac `ffi1.io_events ≼ r.ffi.io_events`
  THEN1 (rw [] \\ fs [IS_PREFIX_APPEND] \\ simp [EL_APPEND1])
  \\ qunabbrev_tac `ffi1`
  \\ metis_tac
        [evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock,SND,ADD_SYM]
QED

Theorem IMP_semantics_eq_no_fail:
   eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2 rel T ==>
   rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
   semantics ffi max_app code2 co2 cc2 es2 =
   semantics ffi max_app code1 co1 cc1 es1
Proof
  strip_tac
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once semantics_def] \\ rw []
  THEN1
   (fs[semantics_def] \\ IF_CASES_TAC \\ fs []
    \\ sg `F` \\ fs [FST_EQ_LEMMA]
    \\ fs [eval_sim_def]
    \\ last_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs[])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs [] THEN1
     (first_x_assum (qspec_then `k'` mp_tac)
      \\ strip_tac
      \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k')`
      \\ fs [eval_sim_def]
      \\ last_x_assum drule \\ fs []
      \\ CCONTR_TAC \\ fs[]
      \\ fs [FST_EQ_LEMMA]
      \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
      \\ drule evaluate_add_clock_initial_state \\ fs []
      \\ qexists_tac `ck` \\ fs []
      \\ CCONTR_TAC \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ reverse conj_tac
    THEN1
     (fs [FST_EQ_LEMMA]
      \\ rveq \\ fs [eval_sim_def]
      \\ first_x_assum drule \\ strip_tac
      \\ asm_exists_tac \\ fs []
      \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
    \\ gen_tac \\ strip_tac \\ rveq \\ fs []
    \\ qabbrev_tac `st1 = initial_state ffi max_app code1 co1 cc1`
    \\ qabbrev_tac `st2 = initial_state ffi max_app code2 co2 cc2`
    \\ drule evaluate_add_to_clock_io_events_mono_alt
    \\ qpat_x_assum `evaluate (es1,[],st1 k) = _` assume_tac
    \\ drule evaluate_add_to_clock_io_events_mono_alt
    \\ `!extra k. st1 k with clock := (st1 k).clock + extra = st1 (k + extra)`
          by (unabbrev_all_tac \\ fs [initial_state_def])
    \\ `!extra k. st2 k with clock := (st2 k).clock + extra = st2 (k + extra)`
          by (unabbrev_all_tac \\ fs [initial_state_def])
    \\ fs []
    \\ ntac 2 (disch_then assume_tac)
    \\ qpat_x_assum `∀extra._` mp_tac
    \\ first_x_assum (qspec_then `k'` assume_tac)
    \\ first_assum (subterm (fn tm =>
          Cases_on`^(assert has_pair_type tm)`) o concl)
    \\ fs []
    \\ strip_tac
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ strip_tac \\ rveq \\ fs []
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac
    >- (strip_tac \\ rveq \\ fs [FST_EQ_LEMMA] \\ rfs [])
    \\ disch_then (qspec_then `ck + k` mp_tac)
    \\ unabbrev_all_tac \\ fs [initial_state_def]
    \\ ntac 2 strip_tac \\ rveq \\ fs []
    \\ qpat_x_assum `_ ==> _` mp_tac \\ impl_tac THEN1 (strip_tac \\ fs [])
    \\ qpat_x_assum `_ ==> _` mp_tac \\ impl_tac THEN1 (strip_tac \\ fs [])
    \\ disch_then (qspec_then `0` assume_tac)
    \\ disch_then (qspec_then `k'` assume_tac)
    \\ fs []
    \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (last_x_assum (qspec_then `k` assume_tac) \\ rfs [FST_EQ_LEMMA]
    \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)` \\ fs []
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ qpat_x_assum `_ = (Rerr (Rabort Rtype_error),_)` assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ qexists_tac `ck` \\ fs [initial_state_def]
    \\ CCONTR_TAC \\ fs [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  THEN1
   (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac \\ fs[]
    \\ rveq \\ fs [eval_sim_def]
    \\ first_x_assum drule \\ fs []
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (assume_tac o GSYM)
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ qpat_x_assum `∀x y. ¬z` mp_tac \\ simp []
    \\ qexists_tac `k` \\ simp []
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ disch_then (qspec_then `ck` mp_tac)
    \\ fs [initial_state_with_clock]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ rpt (CASE_TAC \\ fs []))
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  THEN1
   (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ strip_tac \\ fs [LESS_EQ_EXISTS] \\ rveq
    \\ metis_tac
        [evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate (es1,[],initial_state ffi max_app code1 co1 cc1 k)`
  \\ rveq \\ fs [eval_sim_def]
  \\ first_x_assum drule \\ fs []
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  THEN1 (qexists_tac `ck + k` \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < (LENGTH (_ ffi1))`
  \\ qsuff_tac `ffi1.io_events ≼ r.ffi.io_events`
  THEN1 (rw [] \\ fs [IS_PREFIX_APPEND] \\ simp [EL_APPEND1])
  \\ qunabbrev_tac `ffi1`
  \\ metis_tac
        [evaluate_add_to_clock_io_events_mono,
         initial_state_with_clock,SND,ADD_SYM]
QED

val CURRY_I_rel_def = Define`
  CURRY_I_rel s1 s2 ⇔
    s1.globals = s2.globals ∧
    s1.refs = s2.refs ∧
    s1.ffi = s2.ffi ∧
    s1.clock = s2.clock ∧
    s1.compile = state_cc (CURRY I) s2.compile ∧
    s2.compile_oracle = state_co (CURRY I) s1.compile_oracle ∧
    s1.code = s2.code ∧
    s1.max_app = s2.max_app`;

Theorem do_install_CURRY_I:
   do_install xs z1 = (r,s1) ∧ r ≠ Rerr (Rabort Rtype_error) ∧
   CURRY_I_rel z1 z2 ⇒
   ∃s2.
     do_install xs z2 = (r,s2) ∧
     CURRY_I_rel s1 s2
Proof
  rw[closSemTheory.do_install_def]
  \\ fs[CaseEq"list",CaseEq"option"] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac CURRY_I_rel_def
  \\ fs[backendPropsTheory.state_cc_def, backendPropsTheory.state_co_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ IF_CASES_TAC \\ fs[] \\ fs[]
  \\ TRY (fs[CURRY_I_rel_def] \\ rveq \\ fs[] \\ NO_TAC)
  \\ fs[FUN_EQ_THM, FORALL_PROD]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ fs[shift_seq_def]
  \\ pairarg_tac \\ fs[]
  \\ IF_CASES_TAC \\ fs[] \\ rveq \\ fs[]
  \\ IF_CASES_TAC \\ fs[CaseEq"bool"] \\ rveq \\ fs[CURRY_I_rel_def, FUN_EQ_THM]
  \\ fs[backendPropsTheory.state_cc_def, backendPropsTheory.state_co_def]
QED

val do_app_lemma_simp = prove(
  ``(exc_rel $= err1 err2 <=> err1 = err2) /\
    LIST_REL $= xs xs /\
    simple_state_rel $= CURRY_I_rel /\
    simple_val_rel $=``,
  rw [] \\ fs [simple_state_rel_def,CURRY_I_rel_def]
  THEN1
   (Cases_on `err1` \\ fs [semanticPrimitivesPropsTheory.exc_rel_def]
    \\ eq_tac \\ rw [])
  \\ fs [simple_val_rel_def] \\ fs []);

val do_app_lemma =
  simple_val_rel_do_app
  |> Q.GENL [`vr`,`sr`]
  |> ISPEC ``(=):closSem$v -> closSem$v -> bool``
  |> ISPEC ``CURRY_I_rel``
  |> Q.INST [`opp`|->`op`,`s`|->`s1`,`t`|->`s2`,`ys`|->`xs`]
  |> SIMP_RULE std_ss [do_app_lemma_simp]

Theorem do_app_CURRY_I_Rerr:
   ∀op xs s1 s2 r.
    do_app op xs s1 = Rerr r ∧
    CURRY_I_rel s1 s2 ⇒
    do_app op xs s2 = Rerr r
Proof
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []
QED

Theorem do_app_CURRY_I_Rval:
   ∀op xs s1 s2 r z1.
    do_app op xs s1 = Rval (r,z1) ∧
    CURRY_I_rel s1 s2 ⇒
    ∃z2.
    do_app op xs s2 = Rval (r,z2) ∧
    CURRY_I_rel z1 z2
Proof
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []
QED

Theorem evaluate_CURRY_I:
   (∀p x y (z1:('a # 'c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    p = (x,y,z1) ∧
    closSem$evaluate (x,y,z1) = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    CURRY_I_rel z1 z2
    ⇒
    ∃s2.
    closSem$evaluate (x,y,z2) = (r,s2) ∧
    CURRY_I_rel s1 s2) ∧
   (∀w x y (z1:('a # 'c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    evaluate_app w x y z1 = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    CURRY_I_rel z1 z2
    ⇒
    ∃s2.
    evaluate_app w x y z2 = (r,s2) ∧
    CURRY_I_rel s1 s2)
Proof
  ho_match_mp_tac closSemTheory.evaluate_ind
  \\ rw[closSemTheory.evaluate_def]
  \\ TRY (
       fs[closSemTheory.evaluate_def,
          bool_case_eq,
          CaseEq"prod", CaseEq"option", CaseEq"list",
          CaseEq"semanticPrimitives$result",
          CaseEq"app_kind",
          CaseEq"error_result"]
    \\ rw[]
    \\ fs[PULL_EXISTS]
    \\ res_tac \\ fs[]
    \\ rpt(qpat_x_assum`(_,_) = _`(assume_tac o SYM) \\ fs[])
    \\ res_tac \\ fs[]
    \\ fs[CURRY_I_rel_def, CaseEq"prod", CaseEq"option",
          bool_case_eq, PULL_EXISTS]
    \\ rveq \\ fs[closSemTheory.dec_clock_def] \\ rfs[]
    \\ fsrw_tac[DNF_ss][]
    \\ qmatch_goalsub_abbrev_tac`evaluate (_,_,ss)`
    \\ TRY(last_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`] \\ strip_tac \\ fs[] \\ NO_TAC)
    \\ TRY(first_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`] \\ strip_tac \\ fs[] \\ NO_TAC)
    \\ NO_TAC)
    (* only Install and do_app *)
  \\ fs[CaseEq"option",CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS] \\ fs[]
  \\ rveq \\ fs[]
  \\ res_tac \\ fs[]
  \\ Cases_on`op = Install`
  \\ fs[CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS]
  \\ rveq \\ fs[]
  \\ TRY (
    drule (GEN_ALL do_install_CURRY_I)
    \\ simp[]
    \\ disch_then drule
    \\ rw[] \\ fs[]
    \\ res_tac \\ fs []
    \\ NO_TAC )
  \\ imp_res_tac do_app_CURRY_I_Rval
  \\ fs[]
  \\ imp_res_tac do_app_CURRY_I_Rerr
QED

Theorem semantics_CURRY_I:
   semantics ffi max_app code co (state_cc (CURRY I) cc) es ≠ Fail ⇒
   semantics ffi max_app code (state_co (CURRY I) co) cc es =
   semantics ffi max_app code co (state_cc (CURRY I) cc) es
Proof
  rw[]
  \\ irule IMP_semantics_eq
  \\ rw[eval_sim_def]
  \\ qexists_tac`K (K (K (K (K (K (K (K T)))))))` \\ rw[]
  \\ imp_res_tac(CONJUNCT1 evaluate_CURRY_I)
  \\ fs[PULL_FORALL,PULL_EXISTS]
  \\ qexists_tac`0` \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`(es,[],sz)`
  \\ last_x_assum(qspec_then`sz`mp_tac)
  \\ impl_tac
  >- (
    simp[CURRY_I_rel_def]
    \\ simp[Abbr`sz`]
    \\ EVAL_TAC )
  \\ strip_tac \\ fs[]
  \\ imp_res_tac CURRY_I_rel_def
QED

Theorem semantics_nil[simp]:
   semantics ffi maxapp code co cc [] = Terminate Success ffi.io_events
Proof
  rw[semantics_def, evaluate_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[] \\ EVAL_TAC
QED

Theorem find_code_SUBMAP:
   find_code dest vs code1 = SOME p ∧ code1 ⊑ code2 ⇒
   find_code dest vs code2 = SOME p
Proof
  rw[closSemTheory.find_code_def, CaseEq"option", pair_case_eq]
  \\ imp_res_tac FLOOKUP_SUBMAP
QED

val SUBMAP_rel_def = Define`
  SUBMAP_rel z1 z2 ⇔
    z2 = z1 with code := z2.code ∧ z1.code ⊑ z2.code (*∧
    (∀n. DISJOINT (FDOM z2.code) (set (MAP FST (SND (SND (z1.compile_oracle n))))) ∧
         (∀m. m < n ⇒ DISJOINT (set (MAP FST (SND (SND (z1.compile_oracle m))))) (set (MAP FST (SND (SND (z1.compile_oracle n)))))))*)`;

Theorem find_code_SUBMAP_rel:
   find_code dest vs s1.code = SOME p ∧ SUBMAP_rel s1 s2 ⇒
   find_code dest vs s2.code = SOME p
Proof
  rw[SUBMAP_rel_def]
  \\ imp_res_tac find_code_SUBMAP
QED

(*
Theorem do_install_SUBMAP:
   do_install xs z1 = (r,s1) ∧ r ≠ Rerr (Rabort Rtype_error) ∧
   SUBMAP_rel z1 z2 ⇒
   ∃s2.
     do_install xs z2 = (r,s2) ∧
     SUBMAP_rel s1 s2
Proof
  rw[closSemTheory.do_install_def]
  \\ fs[CaseEq"list",CaseEq"option"] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac SUBMAP_rel_def
  \\ imp_res_tac closSemTheory.state_component_equality
  \\ fs[] \\ rveq
  \\ reverse IF_CASES_TAC \\ fs[] \\ fs[]
  >- ( last_x_assum(qspec_then`0`mp_tac) \\ simp[] )
  \\ fs[bool_case_eq,CaseEq"option",CaseEq"prod"]
  \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality,shift_seq_def]
  \\ rveq \\ fs[]
  \\ (
    conj_tac >- (
      irule SUBMAP_mono_FUPDATE_LIST
      \\ fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_DRESTRICT] ))
  \\ gen_tac
  \\ first_x_assum(qspec_then`n+1`mp_tac)
  \\ fs[IN_DISJOINT, FDOM_FUPDATE_LIST]
  \\ CCONTR_TAC \\ fs[]
  \\ first_x_assum(qspec_then`0`mp_tac) \\ simp[]
  \\ metis_tac[]
QED
*)

val do_app_lemma_simp = prove(
  ``(exc_rel $= err1 err2 <=> err1 = err2) /\
    LIST_REL $= xs xs /\
    simple_state_rel $= SUBMAP_rel /\
    simple_val_rel $=``,
  rw [] \\ fs [simple_state_rel_def]
  THEN1
   (Cases_on `err1` \\ fs [semanticPrimitivesPropsTheory.exc_rel_def]
    \\ eq_tac \\ rw [])
  \\ fs [simple_val_rel_def]
  \\ fs[SUBMAP_rel_def, closSemTheory.state_component_equality]
  \\ metis_tac[]);

val do_app_lemma =
  simple_val_rel_do_app
  |> Q.GENL [`vr`,`sr`]
  |> ISPEC ``(=):closSem$v -> closSem$v -> bool``
  |> ISPEC ``SUBMAP_rel``
  |> Q.INST [`opp`|->`op`,`s`|->`s1`,`t`|->`s2`,`ys`|->`xs`]
  |> SIMP_RULE std_ss [do_app_lemma_simp]

Theorem do_app_SUBMAP_Rerr:
   ∀op xs s1 s2 r.
    do_app op xs s1 = Rerr r ∧
    SUBMAP_rel s1 s2 ⇒
    do_app op xs s2 = Rerr r
Proof
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []
QED

Theorem do_app_SUBMAP_Rval:
   ∀op xs s1 s2 r z1.
    do_app op xs s1 = Rval (r,z1) ∧
    SUBMAP_rel s1 s2 ⇒
    ∃z2.
    do_app op xs s2 = Rval (r,z2) ∧
    SUBMAP_rel z1 z2
Proof
  rw [] \\ imp_res_tac do_app_lemma
  \\ pop_assum (assume_tac o SPEC_ALL) \\ rfs []
QED

Theorem evaluate_code_SUBMAP:
   (∀p x y (z1:('c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    p = (x,y,z1) ∧
    closSem$evaluate (x,y,z1) = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    SUBMAP_rel z1 z2
    ⇒
    ∃s2.
    closSem$evaluate (x,y,z2) = (r,s2) ∧
    SUBMAP_rel s1 s2) ∧
   (∀w x y (z1:('c, 'ffi)closSem$state) r s1 s2 (z2:('c,'ffi)closSem$state).
    evaluate_app w x y z1 = (r,s1) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    SUBMAP_rel z1 z2
    ⇒
    ∃s2.
    evaluate_app w x y z2 = (r,s2) ∧
    SUBMAP_rel s1 s2)
Proof
  ho_match_mp_tac closSemTheory.evaluate_ind
  \\ rw[closSemTheory.evaluate_def]
  \\ TRY (
    rename1`dest_closure`
    \\ imp_res_tac SUBMAP_rel_def
    \\ imp_res_tac closSemTheory.state_component_equality
    \\ fs[CaseEq"option",CaseEq"app_kind",CaseEq"bool",closSemTheory.dec_clock_def]
    \\ rveq \\ res_tac \\ fs[]
    \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality] \\ rw[] \\ rfs[]
    \\ fs[CaseEq"prod",CaseEq"semanticPrimitives$result",CaseEq"list",PULL_EXISTS]
    \\ rveq \\ fsrw_tac[DNF_ss][] \\ rfs[]
    \\ fs[GSYM CONJ_ASSOC]
    \\ qmatch_goalsub_abbrev_tac`evaluate (_,_,ss)`
    \\ fs[AND_IMP_INTRO]
    \\ last_x_assum(qspec_then`ss`(fn th => mp_tac th \\ impl_tac >- fs[Abbr`ss`]))
    \\ strip_tac \\ fs[] \\ NO_TAC )
  \\ TRY (
       fs[closSemTheory.evaluate_def,
          bool_case_eq,
          CaseEq"prod", CaseEq"option", CaseEq"list",
          CaseEq"semanticPrimitives$result",
          CaseEq"app_kind",
          CaseEq"error_result",
          closSemTheory.dec_clock_def]
    \\ rw[]
    \\ fs[PULL_EXISTS]
    \\ TRY (fs[closSemTheory.state_component_equality,SUBMAP_rel_def] \\
            HINT_EXISTS_TAC \\ fs[] \\ NO_TAC)
    \\ res_tac \\ fs[]
    \\ rpt(qpat_x_assum`(_,_) = _`(assume_tac o SYM) \\ fs[])
    \\ res_tac \\ fs[]
    \\ fs[CaseEq"prod", CaseEq"option", bool_case_eq, PULL_EXISTS]
    \\ rveq \\ fs[] \\ rfs[]
    \\ fsrw_tac[DNF_ss][]
    \\ imp_res_tac find_code_SUBMAP_rel \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`evaluate (_,_,ss)`
    \\ TRY(last_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`]
           \\ strip_tac \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality]
           \\ rfs[]
           \\ HINT_EXISTS_TAC \\ fs[]
           \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
           \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
           \\ fs[closSemTheory.state_component_equality]
           \\ NO_TAC)
    \\ TRY(first_x_assum(qspec_then`ss`mp_tac) \\ simp[Abbr`ss`]
           \\ strip_tac \\ fs[SUBMAP_rel_def,closSemTheory.state_component_equality]
           \\ rfs[]
           \\ HINT_EXISTS_TAC \\ fs[]
           \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
           \\ rpt(AP_TERM_TAC ORELSE AP_THM_TAC)
           \\ fs[closSemTheory.state_component_equality]
           \\ NO_TAC)
    \\ NO_TAC)
    (* only Install and do_app *)
  \\ fs[CaseEq"option",CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS] \\ fs[]
  \\ rveq \\ fs[] \\ res_tac \\ fs[]
  \\ Cases_on`op = Install`
  \\ fs[CaseEq"prod",CaseEq"semanticPrimitives$result",PULL_EXISTS]
  \\ rveq \\ fs[]
  (*
  \\ TRY (
    drule (GEN_ALL do_install_SUBMAP)
    \\ simp[]
    \\ disch_then drule
    \\ rw[] \\ fs[]
    \\ fs[PULL_EXISTS]
    \\ res_tac \\ fs[]
    \\ NO_TAC )
  *)
  \\ imp_res_tac do_app_SUBMAP_Rval
  \\ fs[]
  \\ imp_res_tac do_app_SUBMAP_Rerr
QED

val obeys_max_app_def = tDefine"obeys_max_app"`
  (obeys_max_app m (Var _ _) ⇔ T) ∧
  (obeys_max_app m (If _ e1 e2 e3) ⇔ obeys_max_app m e1 ∧ obeys_max_app m e2 ∧ obeys_max_app m e3) ∧
  (obeys_max_app m (Let _ es e) ⇔ EVERY (obeys_max_app m) es ∧ obeys_max_app m e) ∧
  (obeys_max_app m (Raise _ e) ⇔ obeys_max_app m e) ∧
  (obeys_max_app m (Handle _ e1 e2) ⇔ obeys_max_app m e1 ∧ obeys_max_app m e2) ∧
  (obeys_max_app m (Tick _ e) ⇔ obeys_max_app m e) ∧
  (obeys_max_app m (Call _ _ _ es) ⇔ EVERY (obeys_max_app m) es) ∧
  (obeys_max_app m (App _ _ e es) ⇔ LENGTH es ≤ m ∧ obeys_max_app m e ∧ EVERY (obeys_max_app m) es) ∧
  (obeys_max_app m (Fn _ _ _ _ e) ⇔ obeys_max_app m e) ∧
  (obeys_max_app m (Letrec _ _ _ es e) ⇔ EVERY (obeys_max_app m) (MAP SND es) ∧ obeys_max_app m e) ∧
  (obeys_max_app m (Op _ _ es) ⇔ EVERY (obeys_max_app m) es)`
(wf_rel_tac`measure (exp_size o SND)`
 \\ simp [closLangTheory.exp_size_def]
 \\ rpt conj_tac \\ rpt gen_tac
 \\ Induct_on`es`
 \\ rw [closLangTheory.exp_size_def]
 \\ simp [] \\ res_tac \\ simp []);

val obeys_max_app_def =
  obeys_max_app_def
  |> SIMP_RULE (srw_ss()++ETA_ss)[MAP_MAP_o]
  |> curry save_thm "obeys_max_app_def[simp,compute]"

val no_Labels_def = tDefine"no_Labels"`
  (no_Labels (Var _ _) ⇔ T) ∧
  (no_Labels (If _ e1 e2 e3) ⇔ no_Labels e1 ∧ no_Labels e2 ∧ no_Labels e3) ∧
  (no_Labels (Let _ es e) ⇔ EVERY no_Labels es ∧ no_Labels e) ∧
  (no_Labels (Raise _ e) ⇔ no_Labels e) ∧
  (no_Labels (Handle _ e1 e2) ⇔ no_Labels e1 ∧ no_Labels e2) ∧
  (no_Labels (Tick _ e) ⇔ no_Labels e) ∧
  (no_Labels (Call _ _ _ es) ⇔ EVERY no_Labels es) ∧
  (no_Labels (App _ _ e es) ⇔ no_Labels e ∧ EVERY no_Labels es) ∧
  (no_Labels (Fn _ _ _ _ e) ⇔ no_Labels e) ∧
  (no_Labels (Letrec _ _ _ es e) ⇔ EVERY no_Labels (MAP SND es) ∧ no_Labels e) ∧
  (no_Labels (Op _ op es) ⇔ (∀n. op ≠ Label n) ∧ EVERY no_Labels es)`
(wf_rel_tac`measure exp_size`
 \\ simp [closLangTheory.exp_size_def]
 \\ rpt conj_tac \\ rpt gen_tac
 \\ Induct_on`es`
 \\ rw [closLangTheory.exp_size_def]
 \\ simp [] \\ res_tac \\ simp []);

val no_Labels_def =
  no_Labels_def
  |> SIMP_RULE (srw_ss()++ETA_ss)[MAP_MAP_o]
  |> curry save_thm "no_Labels_def[simp,compute]"

val app_call_dests_def = tDefine "app_call_dests" `
  (app_call_dests opt [] = {}) /\
  (app_call_dests opt (x::y::xs) =
     let c1 = app_call_dests opt [x] in
     let c2 = app_call_dests opt (y::xs) in
       c1 ∪ c2) /\
  (app_call_dests opt [Var _ v] = {}) /\
  (app_call_dests opt [If _ x1 x2 x3] =
     let c1 = app_call_dests opt [x1] in
     let c2 = app_call_dests opt [x2] in
     let c3 = app_call_dests opt [x3] in
       c1 ∪ c2 ∪ c3) /\
  (app_call_dests opt [Let _ xs x2] =
     let c1 = app_call_dests opt xs in
     let c2 = app_call_dests opt [x2] in
       c1 ∪ c2) /\
  (app_call_dests opt [Raise _ x1] =
     app_call_dests opt [x1]) /\
  (app_call_dests opt [Tick _ x1] =
     app_call_dests opt [x1]) /\
  (app_call_dests opt [Op _ op xs] =
     app_call_dests opt xs) /\
  (app_call_dests opt [App _ loc_opt x1 xs] =
     let ll = if opt = SOME T then {} else
                case loc_opt of SOME n => {n} | _ => {} in
     let c1 = app_call_dests opt [x1] in
     let c2 = app_call_dests opt xs in
         ll ∪ c1 ∪ c2) /\
  (app_call_dests opt [Fn _ loc_opt vs num_args x1] =
     let c1 = app_call_dests opt [x1] in c1) /\
  (app_call_dests opt [Letrec _ loc_opt vs fns x1] =
     let c1 = app_call_dests opt (MAP SND fns) in
     let c2 = app_call_dests opt [x1] in
     c1 ∪ c2) /\
  (app_call_dests opt [Handle _ x1 x2] =
     let c1 = app_call_dests opt [x1] in
     let c2 = app_call_dests opt [x2] in
       c1 ∪ c2) /\
  (app_call_dests opt [Call _ ticks dest xs] =
     if opt = SOME F then app_call_dests opt xs else
       dest INSERT app_call_dests opt xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC >>
   Induct_on `fns` >>
   srw_tac [ARITH_ss] [closLangTheory.exp_size_def] >>
   Cases_on `h` >>
   full_simp_tac(srw_ss())[closLangTheory.exp_size_def] >>
   decide_tac);

val _ = save_thm("app_call_dests_def[simp,compute]",app_call_dests_def);

val _ = overload_on("call_dests",``app_call_dests (SOME T)``);
val _ = overload_on("app_dests",``app_call_dests (SOME F)``);
val _ = overload_on("any_dests",``app_call_dests NONE``);

val app_call_dests_ind = theorem"app_call_dests_ind";

Theorem app_call_dests_cons:
   ∀y x. app_call_dests opt (x::y) =
         app_call_dests opt [x] ∪ app_call_dests opt y
Proof
  Induct \\ rw[app_call_dests_def]
QED

val any_dest_cons = save_thm("any_dest_cons",
  app_call_dests_cons |> Q.INST [`opt`|->`NONE`]);
val call_dest_cons = save_thm("call_dest_cons",
  app_call_dests_cons |> Q.INST [`opt`|->`SOME T`]);
val app_dest_cons = save_thm("app_dest_cons",
  app_call_dests_cons |> Q.INST [`opt`|->`SOME F`]);

Theorem app_call_dests_append:
   ∀l1 l2. app_call_dests opt (l1 ++ l2) =
           app_call_dests opt l1 ∪ app_call_dests opt l2
Proof
  Induct_on `l1` \\ fs [app_call_dests_def]
  \\ once_rewrite_tac [app_call_dests_cons]
  \\ fs [AC UNION_COMM UNION_ASSOC]
QED

val any_dest_append = save_thm("any_dest_append",
  app_call_dests_append |> Q.INST [`opt`|->`NONE`]);
val call_dest_append = save_thm("call_dest_append",
  app_call_dests_append |> Q.INST [`opt`|->`SOME T`]);
val app_dest_append = save_thm("app_dest_append",
  app_call_dests_append |> Q.INST [`opt`|->`SOME F`]);

Theorem app_call_dests_map:
   ∀ls. app_call_dests opt (MAP f ls) =
        BIGUNION (set (MAP (λx. app_call_dests opt [f x]) ls))
Proof
  Induct \\ rw[app_call_dests_def]
  \\ rw[Once app_call_dests_cons]
QED

Theorem any_dests_call_dests_app_dests:
   !xs. any_dests xs = call_dests xs UNION app_dests xs
Proof
  qid_spec_tac `opt:bool option`
  \\ ho_match_mp_tac app_call_dests_ind
  \\ fs [app_call_dests_def] \\ rw []
  \\ fs [AC UNION_COMM UNION_ASSOC]
  \\ Cases_on `opt = SOME F` \\ fs []
  \\ fs [EXTENSION] \\ rw[] \\ eq_tac \\ rw [] \\ fs []
QED

val get_code_labels_def = tDefine"get_code_labels" `
  (get_code_labels (Var _ _) = {}) ∧
  (get_code_labels (If _ e1 e2 e3) =
    get_code_labels e1 ∪
    get_code_labels e2 ∪
    get_code_labels e3) ∧
  (get_code_labels (Let _ es e) =
    BIGUNION (set (MAP get_code_labels es)) ∪
    get_code_labels e) ∧
  (get_code_labels (Raise _ e) = get_code_labels e) ∧
  (get_code_labels (Handle _ e1 e2) =
    get_code_labels e1 ∪
    get_code_labels e2) ∧
  (get_code_labels (Tick _ e) = get_code_labels e) ∧
  (get_code_labels (Call _ _ l es) =
    {l} ∪ BIGUNION (set (MAP get_code_labels es))) ∧
  (get_code_labels (App _ l e es) =
    (case l of NONE => {} | SOME n => {n}) ∪
    get_code_labels e ∪
    BIGUNION (set (MAP get_code_labels es))) ∧
  (get_code_labels (Fn _ l _ _ e) =
   (case l of NONE => {} | SOME n => {n}) ∪
   get_code_labels e) ∧
  (get_code_labels (Letrec _ l _ es e) =
   (case l of NONE => {} | SOME n =>
     IMAGE (λk. n + 2 * k) (count (LENGTH es))) ∪
    get_code_labels e ∪
    BIGUNION (set (MAP get_code_labels (MAP SND es)))) ∧
  (get_code_labels (Op _ op es) =
    BIGUNION (set (MAP get_code_labels es)) ∪
    closLang$assign_get_code_label op)`
  (wf_rel_tac `measure exp_size`
   \\ simp [closLangTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw [closLangTheory.exp_size_def]
   \\ simp [] \\ res_tac \\ simp []);

val get_code_labels_def =
  get_code_labels_def
  |> SIMP_RULE (srw_ss()++ETA_ss)[MAP_MAP_o]
  |> curry save_thm "get_code_labels_def[simp,compute]"

val code_locs_ind = theorem"code_locs_ind";

Theorem get_code_labels_code_locs:
   ∀xs. EVERY no_Labels xs ∧ every_Fn_SOME xs ⇒
        BIGUNION (set (MAP get_code_labels xs)) =
        set (code_locs xs) ∪ any_dests xs
Proof
  recInduct code_locs_ind
  \\ rw[code_locs_def, app_call_dests_def] \\ fs[]
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( Cases_on`op` \\ fs[closLangTheory.assign_get_code_label_def] )
  >- (
    rw[EXTENSION]
    \\ PURE_TOP_CASE_TAC \\ fs[]
    \\ metis_tac[] )
  >- (
    fs[IS_SOME_EXISTS]
    \\ rw[EXTENSION]
    \\ metis_tac[] )
  >- (
    fs[IS_SOME_EXISTS]
    \\ fs[MAP_MAP_o]
    \\ rw[EXTENSION, MEM_GENLIST, MEM_MAP, PULL_EXISTS, code_locs_map, MEM_FLAT]
    \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
QED

val _ = export_theory();
