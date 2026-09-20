(*
  Uses monadic translator to produce locally stateful CakeML code
  implementing xprune_for
*)
Theory xpruneProg
Libs
  preamble ml_monad_translator_interfaceLib
Ancestors
  ml_monad_translator xaig_to_cnf

val _ = set_up_monadic_translator ();

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| seen_array : bool list |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Subscript
End

val _ = local_state_config
        |> with_state “:state_refs”
        |> with_exception “:state_exn”
        |> with_fixed_arrays [("seen_array", “0:num”, 0, “Subscript”, “Subscript”)]
        |> start_translation;

Definition max_each_def:
  (max_each [] acc = acc) ∧
  (max_each ((x,b)::xs) acc =
    case x of
    | Gate n => max_each xs (MAX n acc)
    | _      => max_each xs acc)
End

val _ = translate MAX_DEF; (* needed? *)
val _ = translate max_each_def;

Definition max_gt_def:
  (max_gt [] acc = acc) ∧
  (max_gt ((m,gt)::xs) acc = max_gt xs (MAX m (max_each (gty_lits gt) acc)))
End

val _ = translate gty_lits_def;
val _ = translate max_gt_def;

Definition mark_each_gate_def:
  (mark_each_gate [] = return ()) ∧
  (mark_each_gate ((x,b)::xs) =
    case x of
    | Gate n => do u <- update_seen_array n T; mark_each_gate xs od
    | _      => mark_each_gate xs)
End

val _ = m_translate mark_each_gate_def;

Definition xprune_loop_def:
  (xprune_loop [] acc = return acc) ∧
  (xprune_loop ((m,gt)::xs) acc =
     do
       b <- seen_array_sub m;
       if b then
         do
           u <- update_seen_array m F;
           u <- mark_each_gate (gty_lits gt);
           xprune_loop xs ((m,gt)::acc)
         od
       else
         xprune_loop xs acc
     od)
End

val _ = m_translate xprune_loop_def;

Definition xprune_for_array_def:
  xprune_for_array name aig =
    do
      u <- update_seen_array name T;
      xprune_loop aig []
    od
End

val _ = m_translate xprune_for_array_def;

val run_init_state_def = define_run “:state_refs” ["seen_array"] "init_state"

Definition run_xprune_def:
  run_xprune name aig l =
    run_init_state (xprune_for_array name aig) <| seen_array := (l,F) |>
End

val run_xprune_v_thm = m_translate_run run_xprune_def;

Theorem run_eq_M_success:
  (run f x = M_success r) ⇔ ∃s1. f x = (M_success r, s1)
Proof
  simp [ml_monadBaseTheory.run_def]
  \\ Cases_on ‘f x’ \\ gvs []
QED

Theorem IMP_Mupdate_M_success:
  (y = LUPDATE x n l) ∧ n < LENGTH l ⇒
  (Mupdate e x n l = M_success y)
Proof
  simp [ml_monadBaseTheory.Mupdate_eq]
QED

Theorem max_each_acc:
  ∀xs m. max_each xs m = MAX (max_each xs 0) m
Proof
  Induct \\ simp [max_each_def]
  \\ Cases
  \\ Cases_on ‘q’
  \\ simp_tac (srw_ss()) [max_each_def]
  \\ pop_assum (fn th => once_rewrite_tac [th] \\ assume_tac th)
  \\ rewrite_tac [GSYM MAX_ASSOC, MAX_0] \\ rw []
QED

Theorem max_gt_acc:
  ∀xs m. max_gt xs m = MAX (max_gt xs 0) m
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ once_rewrite_tac [max_gt_def] >- rw [MAX_DEF]
  \\ PairCases \\ rewrite_tac [max_gt_def]
  \\ pop_assum (fn th => simp [Once (GSYM th)] \\ assume_tac th)
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp [Once (GSYM th)] \\ assume_tac th)
  \\ rewrite_tac [GSYM MAX_ASSOC] \\ rw []
  \\ rpt AP_TERM_TAC
  \\ simp [Once max_each_acc]
QED

Definition state_rel_def:
  state_rel s seen aig ⇔
    max_gt aig 0 < LENGTH s.seen_array ∧
    ∀i. i < LENGTH s.seen_array ⇒
        (EL i s.seen_array = i ∈ FDOM seen)
End

Theorem mark_each_gate_thm:
  ∀xs s seen aig.
    state_rel s seen aig ∧
    max_each xs 0 < LENGTH s.seen_array ⇒
    ∃s1. (mark_each_gate xs s = (M_success (),s1)) ∧
         state_rel s1 (new_live xs seen) aig
Proof
  Induct
  \\ gvs [aig_to_cnfTheory.new_live_def, mark_each_gate_def,
          ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases
  \\ gvs [aig_to_cnfTheory.new_live_def, mark_each_gate_def,
          ml_monadBaseTheory.st_ex_return_def]
  \\ CASE_TAC \\ fs [max_each_def]
  \\ simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ rw [Once state_rel_def, AllCaseEqs(), PULL_EXISTS]
  \\ simp [fetch "-" "update_seen_array_def"]
  \\ simp [ml_monadBaseTheory.Marray_update_def]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ conj_tac >- fs [Once max_each_acc]
  \\ cheat
QED

Theorem xprune_loop_thm:
  ∀aig seen acc s.
    state_rel s seen aig ⇒
    ∃s1. xprune_loop aig acc s =
         (M_success (xprune_rev aig seen acc),s1)
Proof
  Induct
  >- simp [xprune_loop_def, ml_monadBaseTheory.st_ex_return_def, xprune_rev_def]
  \\ PairCases \\ rw []
  \\ simp [xprune_loop_def, ml_monadBaseTheory.st_ex_bind_def]
  \\ gvs [fetch "-" "seen_array_sub_def"]
  \\ simp [ml_monadBaseTheory.Marray_sub_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq] \\ simp []
  \\ have ‘oEL h0 s.seen_array = SOME (h0 ∈ FDOM seen)’
  >- (gvs [state_rel_def, max_gt_def]
      \\ pop_assum $ qspec_then ‘h0’ mp_tac
      \\ fs [Once max_gt_def]
      \\ fs [Once max_gt_acc]
      \\ simp [oEL_THM])
  \\ gvs [oEL_THM]
  \\ simp [xprune_rev_def, FLOOKUP_DEF]
  \\ have ‘state_rel s seen aig’
  >- (gvs [state_rel_def, max_gt_def] \\ rw []
      \\ fs [Once max_gt_def]
      \\ fs [Once max_gt_acc])
  \\ reverse IF_CASES_TAC >- simp []
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ simp [fetch "-" "update_seen_array_def"]
  \\ simp [ml_monadBaseTheory.Marray_update_def]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ qabbrev_tac ‘s0 = <|seen_array := s.seen_array❲h0 ↦ F❳|>’
  \\ have ‘state_rel s0 (seen \\ h0) aig’
  >- (gvs [state_rel_def, Abbr‘s0’] \\ rw [EL_LUPDATE]
      \\ eq_tac \\ simp [])
  \\ have ‘max_each (gty_lits h1) 0 < LENGTH s0.seen_array’
  >-
   (gvs [state_rel_def, max_gt_def]
    \\ fs [Once max_gt_acc] \\ gvs [Abbr ‘s0’])
  \\ drule_all mark_each_gate_thm
  \\ strip_tac \\ gvs []
QED

Theorem xprune_for_eq:
  xprune_for name aig =
    case run_xprune name aig (max_gt aig name + 1) of
    | M_success x => x
    | _           => []
Proof
  suff ‘run_xprune name aig (max_gt aig name + 1) =
        M_success $ xprune_for name aig’
  >- simp []
  \\ gvs [run_xprune_def, run_init_state_def, run_eq_M_success]
  \\ gvs [xprune_for_array_def, ml_monadBaseTheory.st_ex_bind_def]
  \\ gvs [definition "update_seen_array_def"]
  \\ simp [AllCaseEqs(), ml_monadBaseTheory.Marray_update_def]
  \\ simp [PULL_EXISTS]
  \\ irule_at Any IMP_Mupdate_M_success \\ simp []
  \\ gvs [xprune_for_def, GSYM PULL_EXISTS]
  \\ conj_tac >- (simp [Once max_gt_acc] \\ rw [MAX_DEF])
  \\ irule xprune_loop_thm
  \\ simp [state_rel_def, oEL_THM]
  \\ rw [] >- (once_rewrite_tac [max_gt_acc] \\ rw [MAX_DEF])
  \\ simp [listTheory.EL_LUPDATE]
  \\ Cases_on ‘i = name’ \\ gvs []
  \\ DEP_REWRITE_TAC [EL_REPLICATE]
  \\ simp [Once max_gt_acc] \\ rw [MAX_DEF]
QED

val _ = translate xprune_for_eq;
