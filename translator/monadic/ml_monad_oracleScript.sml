(*
  Oracle-aware specifications for the state-and-exception monad.
*)
Theory ml_monad_oracle
Ancestors
  ml_monad_translator ml_monad_translatorBase ml_monadBase
  evaluate evaluateProps semanticPrimitives
Libs
  preamble

(* The oracle field models epoch 0 of the source oracle *)
Definition ORACLE_REFS_PRED_def:
  ORACLE_REFS_PRED get H st s <=>
    REFS_PRED H st s /\ get st = s.ptr_eq_oracle 0
End

Definition ORACLE_REFS_FRAME_def:
  ORACLE_REFS_FRAME get ro H (st,s) (st',s') <=>
    REFS_PRED_FRAME ro H (st,s) (st',s') /\
    get st' = s'.ptr_eq_oracle 0
End

Definition EvalOM_def:
  EvalOM get ro env st exp P H <=>
    !s. ORACLE_REFS_PRED get H st s ==>
      ?s2 res st2 ck.
        evaluate (s with clock := ck) env [exp] = (s2,res) /\
        P st (st2,res) /\
        ORACLE_REFS_FRAME get ro H (st,s) (st2,s2)
End

Theorem ORACLE_REFS_FRAME_imp:
  ORACLE_REFS_PRED get H st s /\
  ORACLE_REFS_FRAME get ro H (st,s) (st',s') ==>
  ORACLE_REFS_PRED get H st' s'
Proof
  rw [ORACLE_REFS_PRED_def, ORACLE_REFS_FRAME_def]
  \\ irule REFS_PRED_FRAME_imp
  \\ asm_exists_tac \\ qexists_tac `ro` \\ simp []
QED

Theorem ORACLE_REFS_FRAME_trans:
  ORACLE_REFS_FRAME get ro H (st1,s1) (st2,s2) /\
  ORACLE_REFS_FRAME get ro H (st2,s2) (st3,s3) ==>
  ORACLE_REFS_FRAME get ro H (st1,s1) (st3,s3)
Proof
  rw [ORACLE_REFS_FRAME_def]
  \\ irule REFS_PRED_FRAME_trans
  \\ asm_exists_tac \\ simp []
QED

Theorem evaluate_PtrEq_vars:
  nsLookup env.v n1 = SOME v1 /\ nsLookup env.v n2 = SOME v2 /\
  do_eq v1 v2 = Eq_val b ==>
  evaluate (s:'ffi state) env [App PtrEq [Var n1; Var n2]] =
    (s with ptr_eq_oracle :=
       (0 =+ shift_seq 1 (s.ptr_eq_oracle 0)) s.ptr_eq_oracle,
     Rval [Boolv (b /\ s.ptr_eq_oracle 0 0)])
Proof
  simp [evaluate_def]
QED

(* Updating the logical oracle changes no heap resource. *)
Definition ORACLE_ACCESSORS_def:
  ORACLE_ACCESSORS get put H <=>
    !st oracle.
      get (put oracle st) = oracle /\
      FST H (put oracle st) = FST H st
End

Theorem EvalOM_PtrEq:
  ORACLE_ACCESSORS get put (H:('s -> hprop) # 'ffi ffi_proj) /\
  nsLookup env.v n1 = SOME v1 /\ nsLookup env.v n2 = SOME v2 /\
  do_eq v1 v2 = Eq_val (x = y) ==>
  EvalOM get ro env st (App PtrEq [Var n1; Var n2])
    (MONAD BOOL exn (Mptr_eq get put x y)) H
Proof
  rw [EvalOM_def, ORACLE_REFS_PRED_def]
  \\ drule_all evaluate_PtrEq_vars
  \\ strip_tac
  \\ simp [MONAD_def, Mptr_eq_def, ORACLE_REFS_FRAME_def]
  \\ qexists_tac `s.clock`
  \\ Cases_on `H`
  \\ fs [ORACLE_ACCESSORS_def, miscTheory.shift_seq_def,
         REFS_PRED_FRAME_def, state_component_equality,
         cfStoreTheory.st2heap_def]
  \\ simp [ADD1, H_STAR_GC_SAT_IMP]
QED

Theorem evaluate_Let_clocks:
  evaluate (s with clock := ck1) env [e1] = (s1,Rval [v]) /\
  evaluate (s1 with clock := ck2) (write name v env) [e2] = (s2,res) ==>
  ?ck. evaluate (s with clock := ck) env [Let (SOME name) e1 e2] =
       (s2,res)
Proof
  strip_tac
  \\ qpat_x_assum `evaluate _ env [e1] = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] evaluate_set_clock))
  \\ simp []
  \\ disch_then (qspec_then `ck2` strip_assume_tac)
  \\ qmatch_asmsub_rename_tac `evaluate (s with clock := start_clock) env [e1]`
  \\ qexists_tac `start_clock`
  \\ simp [evaluate_def]
  \\ fs [ml_progTheory.write_def, namespaceTheory.nsOptBind_def]
QED

Theorem EvalOM_bind:
  EvalOM get ro env st e1 (MONAD b exn x) H /\
  (!z v. b z v ==>
    EvalOM get ro (write name v env) (SND (x st)) e2
      (MONAD a exn (f z)) H) ==>
  EvalOM get ro env st (Let (SOME name) e1 e2)
    (MONAD a exn (st_ex_bind x f)) H
Proof
  rw [EvalOM_def]
  \\ qpat_x_assum `!s. ORACLE_REFS_PRED get H st s ==> _` drule
  \\ strip_tac
  \\ namedCases_on `x st` ["outcome next"]
  \\ namedCases_on `outcome` ["value", "err"]
  \\ fs [MONAD_def]
  >- (
    Cases_on `res` \\ fs []
    \\ drule evaluate_sing \\ strip_tac \\ gvs [st_ex_bind_def]
    \\ imp_res_tac ORACLE_REFS_FRAME_imp
    \\ qpat_x_assum `!z v. b z v ==> _` drule
    \\ disch_then drule \\ strip_tac
    \\ drule_all evaluate_Let_clocks \\ strip_tac
    \\ imp_res_tac ORACLE_REFS_FRAME_trans
    \\ asm_exists_tac \\ simp []
    \\ asm_exists_tac \\ simp [])
  \\ namedCases_on `res` ["vals", "error"] \\ fs []
  \\ namedCases_on `error` ["raised", "abort"] \\ gvs [st_ex_bind_def]
  \\ qmatch_asmsub_rename_tac
       `evaluate (s with clock := start_clock) env [e1] = (final_state,_)`
  \\ qexistsl_tac [`final_state`, `Rerr (Rraise raised)`, `next`, `start_clock`]
  \\ simp [evaluate_def]
QED

(* Reuse EvalM certificates that touch neither oracle *)
Theorem EvalOM_from_EvalM:
  EvalM ro env st exp P H /\ no_ptr_eq exp /\
  (!st2 res. P st (st2,res) ==> get st2 = get st) ==>
  EvalOM get ro env st exp P H
Proof
  rw [EvalM_def, EvalOM_def, ORACLE_REFS_PRED_def, ORACLE_REFS_FRAME_def]
  \\ qpat_x_assum `!s. REFS_PRED H st s ==> _` drule
  \\ strip_tac
  \\ drule_all evaluate_no_ptr_eq_preserves_oracle \\ simp [] \\ strip_tac
  \\ asm_exists_tac \\ simp []
  \\ qpat_x_assum `!st2 res. P st (st2,res) ==> _` drule
  \\ strip_tac \\ asm_exists_tac \\ simp []
QED

Theorem EvalOM_return:
  Eval env exp (a x) /\ no_ptr_eq exp ==>
  EvalOM get ro env st exp (MONAD a exn (st_ex_return x)) H
Proof
  strip_tac
  \\ irule EvalOM_from_EvalM
  \\ simp [EvalM_return]
  \\ rpt gen_tac
  \\ namedCases_on `res` ["values", "err"]
  \\ simp [MONAD_def, st_ex_return_def]
  \\ namedCases_on `values` ["", "v rest"] \\ simp []
  \\ Cases_on `rest` \\ simp []
QED

Theorem EvalOM_PtrEq_Eval:
  ORACLE_ACCESSORS get put H /\ EqualityType a /\
  Eval env (Var n1) (a x) /\ Eval env (Var n2) (a y) ==>
  EvalOM get ro env st (App PtrEq [Var n1; Var n2])
    (MONAD BOOL exn (Mptr_eq get put x y)) H
Proof
  rw [ml_translatorTheory.Eval_Var_nsLookup]
  \\ namedCases_on `nsLookup env.v n1` ["", "v1"] \\ fs []
  \\ namedCases_on `nsLookup env.v n2` ["", "v2"] \\ fs []
  \\ irule EvalOM_PtrEq
  \\ fs [ml_translatorTheory.EqualityType_def]
  \\ res_tac
  \\ imp_res_tac ml_translatorTheory.type_match_implies_do_eq_succeeds
  \\ Cases_on `v1 = v2` \\ fs []
QED

(* A callable value whose body uses the oracle-aware monadic judgment. *)
Definition ArrowOM_def:
  ArrowOM get ro H a b exn f closure <=>
    !x v st. a x v ==>
      ?env body. do_opapp [closure;v] = SOME (env,body) /\
        EvalOM get ro env st body (MONAD b exn (f x)) H
End

Theorem Eval_ArrowOM:
  (!x v st. a x v ==>
    EvalOM get ro (write name v env) st body (MONAD b exn (f x)) H) ==>
  Eval env (Fun name body) (ArrowOM get ro H a b exn f)
Proof
  simp [ml_translatorTheory.Eval_Fun_rw, ArrowOM_def,
        semanticPrimitivesTheory.do_opapp_def, ml_progTheory.write_def]
QED

Theorem EvalOM_If_Var:
  Eval env (Var name) (BOOL test) /\
  (test ==> EvalOM get ro env st e1 (MONAD a exn x) H) /\
  (~test ==> EvalOM get ro env st e2 (MONAD a exn y) H) ==>
  EvalOM get ro env st (If (Var name) e1 e2)
    (MONAD a exn (if test then x else y)) H
Proof
  rw [ml_translatorTheory.Eval_Var_nsLookup]
  \\ Cases_on `nsLookup env.v name` \\ fs [ml_translatorTheory.BOOL_def]
  \\ gvs [EvalOM_def, evaluate_def, semanticPrimitivesTheory.do_if_def,
          semanticPrimitivesTheory.Boolv_def]
QED
