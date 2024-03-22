(*
    Props for assisting equivalence proof in panItreeSemEquiv
*)

open preamble panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           itreeTauTheory
           panSemTheory
           panLangTheory
           panItreeSemTheory in end;

val _ = new_theory "panItreeSemProps";

(* Infrastructure for ITree-semantics-based program verification. *)
val dummy_ffi_state = “<| oracle := (λs x y z. Oracle_final FFI_failed):unit oracle;
                        ffi_state := ();
                        io_events := NIL |>”;

val sem_self_rec_st = “<| locals := FEMPTY;
                          code := FEMPTY |+ («main»,(NIL:(varname # shape) list, panLang$Call Tail (Label «main») (NIL:('a panLang$exp) list)));
                          eshapes := FEMPTY;
                          memory := λw:('a word). Word w;
                          memaddrs := EMPTY;
                          clock := 0:num;
                          be := F;
                          ffi := ^dummy_ffi_state;
                          base_addr := ARB |>”;

val sem_no_code = “<| locals := FEMPTY;
                      code := FEMPTY;
                      eshapes := FEMPTY;
                      memory := λw:('a word). Word w;
                      memaddrs := EMPTY;
                      clock := 0:num;
                      be := F;
                      ffi := ^dummy_ffi_state;
                      base_addr := ARB |>”;

val seq_ffi_prog = “Seq
                    (ExtCall «main» (Const 0w) (Const 0w) (Const 0w) (Const 0w))
                    (ExtCall «main» (Const 0w) (Const 0w) (Const 0w) (Const 0w))”;

val seq_ffi_itree = “(Tau (Vis (FFI_call "main" NIL NIL) (λr. (Tau (Vis (FFI_call "main" NIL NIL) (K (Ret NONE))))))):('b ffi_result, sem_vis_event, 'a result option) itree”;

Type h_prog_ty = “:(α result option # (α, β) state,
                    α panLang$prog # (α, β) state +
                    sem_vis_event # (β ffi_result -> (β ffi_result, sem_vis_event, 'a result option # (α, β) state) itree),
                    α result option # (α, β) state) itree”;

Triviality itree_monad_right_ident:
  do
    (res,s') <- Ret (NONE,s');
    if res = NONE then
      Vis
      (INL
       (ExtCall «main» (Const 0w) (Const 0w)
                (Const 0w) (Const 0w),s')) Ret
    else Ret (res,s')
  od = Vis
       (INL
        (ExtCall «main» (Const 0w) (Const 0w)
                 (Const 0w) (Const 0w),s')) Ret
Proof
  rw [itreeTauTheory.itree_bind_thm]
QED


(* Theorem seq_ffi: *)
(*   h_prog_rule_ext_call «main» (Const 0w) (Const 0w) (Const 0w) (Const 0w) s = (Ret (NONE,s')):('a,'b) h_prog_ty ∧ *)
(*   h_prog_rule_ext_call «main» (Const 0w) (Const 0w) (Const 0w) (Const 0w) s' = (Ret (NONE,s'')):('a,'b) h_prog_ty ⇒ *)
(*   itree_evaluate ^seq_ffi_prog s = ^seq_ffi_itree *)
(* Proof *)
(*   cheat *)
(* QED *)

(* Bisimulation proof of isomorphism between semantics *)
(* Can be interred once the evaluate_biject is proven by itree_el_eqv. *)

(* NOTE: Because the intermediate semantics has Vis nodes with constant ktrees,
 we can prove the bijection that our semantics produces in every branch a Ret node
    containing the result identical to that produced by the operational semantics. *)
(* The outer-most semantics then modifies this shape by allowing Vis nodes to have ktrees
 dependent on FFI results. *)

(* Proof of correspondence between operational and ITree semantics *)
(* observational big-step semantics has three possible outcomes, defined in ffi$behaviour
 - Terminate
 - Diverge
 - Fail

 The isomorphism can be such that:

 Diverge equates to an ITree with infinitely many Tau:s, i.e. t = Tau t

 Terminate requires the outcome of both semantics to be the same (the return value)

 Fail should only happen when it occurs in the other semantics.

 In other words, these behaviours are the properties preserved by the isomorphism.
 *)

(* The ITree branches represent choices for the ExtCall return value.
    The oracle mechanism used in the op semantics makes this choice.
    Hence we need an "oracle choice" function which produces the leaf of an ITree
    by choosing the correct branch at every Vis.

    This "oracle choice" forms the basis of the isomorphism.
 *)

(* converts a tree t into a Tau-Ret tree s.t. if the final tree
 is terminal then the tree t had a terminal path when the oracle or
    chooses branches; otherwise the final tree with be an infinite (divergent) tau
    tree, indicating the tree t was divergent. *)
Definition itree_oracle_walk_def:
  itree_oracle_walk oracle t =
  itree_iter
  (λt'. case t' of
         Ret r => Ret (INR r)
        | Tau u => Ret (INL u)
        | Vis e k => Ret (INL (k (oracle e))))
  t
End

Theorem itree_oracle_walk_cases:
  ∀t or. (∃u. itree_oracle_walk or t = Tau u) ∨ (∃r. itree_oracle_walk or t = Ret r)
Proof
  rw [] >>
  Cases_on ‘t’ >>
  rw [itree_oracle_walk_def] >>
  rw [itreeTauTheory.itree_iter_def]
  >- (DISJ2_TAC >>
      rw [Once itreeTauTheory.itree_unfold])
  >- (DISJ1_TAC >>
      rw [Once itreeTauTheory.itree_unfold])
  >- (Cases_on ‘g (or a)’ >>
      DISJ1_TAC >>
      rw [Once itreeTauTheory.itree_unfold])
QED

(* Definition ext_call_oracle_h_def: *)
(*   ext_call_oracle_h (FFI_call fs name args bytes) = call_FFI fs name args bytes *)
(* End *)

Definition itree_diverges_def:
  itree_diverges t = ∀r. ¬∃p. itree_el t p = Return r
End

Definition itree_fails_def:
  itree_fails t = ∃p. case itree_el t p of
                        Return (SOME TimeOut) => F
                       | Return (SOME (FinalFFI _)) => F
                       | Return (SOME (Return _)) => F
                       | _ => T
End

Definition itree_terminates_def:
  itree_terminates t ⇔ ∃p. case itree_el t p of
                             Return (SOME (FinalFFI _)) => T
                            | Return (SOME (Return _)) => T
                            | _ => F
End


(* Relating panSemTheory.evaluate and panItreeSemTheory.mrec *)
val s = “s:(('a,'ffi) panSem$state)”;

Definition fix_clock_small_def:
  fix_clock_small old_s (p,r,new_s) =
  (p,r,new_s with clock :=
       if old_s.clock < new_s.clock then old_s.clock else new_s.clock)
End

(* Relate evaluate and h_prog/mrec by the conditions that lead to the
 outcomes of interest. *)

(* Build a relation between evaluate_small and evaluate *)
(* Then build a relation between evaluate_small and mrec *)
(* Thus relating evaluate and mrec in a small-step way. *)
Inductive evaluate_small_rel:
  (eval s g = SOME (ValWord w) ∧ w ≠ 0w ⇒
   evaluate_small (SOME (While g p),NONE,s) (SOME (Seq p (While g p)),r,s)) ∧
  (eval s g = SOME (ValWord w) ∧ w ≠ 0w ∧ s.clock = 0 ⇒
        evaluate_small (SOME (While g p),NONE,s) (NONE,SOME TimeOut,s)) ∧
  (eval s g = SOME (ValWord w) ∧ w = 0w ⇒ evaluate_small (SOME (While g p),NONE,s) (NONE,NONE,s)) ∧
  (eval s g ≠ SOME (ValWord w) ⇒ evaluate_small (SOME (While g p),NONE,s) (NONE,SOME Error,s))
End



Theorem evaluate_small_while_error_eq:
  evaluate (While g p,s) = (SOME Error,s) ⇔
           evaluate_small (SOME (While g p),NONE,s) (NONE,SOME Error,s)
Proof
  EQ_TAC >> rw[]
  >- (gvs [Once panSemTheory.evaluate_def] >>
      every_case_tac >>
      rw [evaluate_small_rel_rules] >>
      cheat) >>
      cheat
QED

Theorem evaluate_small_eq:
  evaluate (p,s) = (res,s') ⇔
    evaluate_small^* (SOME p,NONE,s) (NONE,res,s')
Proof
  cheat
QED

Theorem evaluate_error_eq:
  evaluate (p,s) = (SOME Error,s') ⇔
    h_prog (p,s) = Ret (SOME Error,s')
Proof
  cheat
QED

Theorem evaluate_itree_while_eq:
  evaluate (While g p,s) = (SOME Error,s) ⇔
           strip_tau (itree_mrec h_prog (While g p,s)) (Ret (SOME Error,s))
Proof
  EQ_TAC >> rw []
  >- (rw [panItreeSemTheory.itree_mrec_def] >>
      rw [itreeTauTheory.itree_iter_def] >>
      rw [Once itreeTauTheory.itree_unfold] >>
      cheat) >>
      cheat
QED

(* Find a way to relate the small-step decisions of evaluate to those of mrec (which are designed in a small-step-manner) *)
(* Then it will become clear that the isomorphism at this level preserves all relevant decisions to, at the top level,
 prove presevation of outcomes and (eventually) event traces. *)

(* How to describe evaluate in a small-step way and show preservation of meaning and also connect this description to mrec. *)

(* Theorem evaluate_while_div_clock: *)
(*   (∃s'. evaluate (p,s) = (_,s') ∧ s'.clock = 0) ⇔ *)
(*     ∀s'. ¬∃(n:num). evaluate (p,s with clock := n) ≠ (SOME TimeOut,s') *)
(* Proof *)
(* QED *)

Theorem evaluate_while_div:
  evaluate (While g p,s) = (SOME TimeOut,s') ⇔
    itree_diverges (itree_mrec h_prog (While g p,s))
Proof
  EQ_TAC >> rw [] >>
  simp [panItreeSemTheory.itree_mrec_def,panItreeSemTheory.h_prog_def]  >>
  simp [panItreeSemTheory.h_prog_rule_while_def] >>
  cheat
QED

Theorem itree_iter_simps[simp]:
  itree_iter (λx. Ret (INR (r))) s = Ret r
Proof
  rw [itreeTauTheory.itree_iter_def] >>
  rw [Once itreeTauTheory.itree_unfold]
QED

Theorem itree_iter_case_simps[simp]:
  itree_iter
  (λt. itree_CASE t (λr. Ret (INR r)) tau vis)
  (Ret r) = (Ret r)
Proof
  rw [itreeTauTheory.itree_iter_def] >>
  rw [Once itreeTauTheory.itree_unfold]
QED

(* Define properties that cause mrec outcomes of interest *)
Theorem while_itree_err_cases:
  eval s g ≠ SOME (ValWord w) ⇔
  itree_mrec h_prog (While g p,s) = Ret (SOME Error,s)
Proof
  cheat
QED

Theorem evaluate_while_err_cases:
  evaluate (While g p,s) = (SOME Error,s) ⇔
    eval s g ≠ SOME (ValWord w)
Proof
  cheat
QED

(* Theorem evaluate_itree_while_err_eq: *)
(*   evaluate (While g p,s) = (SOME Error,s) ⇔ *)
(*     itree_mrec h_prog (While g p,s) = Ret (SOME Error,s) *)
(* Proof *)
(*   EQ_TAC >> rw[] *)
(*   >- (IMP_RES_TAC evaluate_while_err_cases >> *)
(*       ASSUME_TAC while_itree_err_cases >> gvs[]) *)
(*   >- (IMP_RES_TAC while_itree_err_cases >> *)
(*       ASSUME_TAC evaluate_while_err_cases >> gvs[]) *)
(* QED *)

(* Need to say: for every state that comes from one or more evaluations of the while body,
 the outcome of evaluation is not Break and the guard holds true in the resulting state. *)
(* This seems to be the exact property that we need also for evaluate.
 Only the notion of "evaluate" is different between the two semantics so perhaps this is better
 expressed as existence of a general function or relation which can be instantiated as the respective function
 for that semantics during the proof.'*)

Theorem evaluate_itree_while_div_cases:
  itree_diverges (itree_mrec h_prog (While g p,s)) ⇔
    eval s g = SOME (ValWord w) ∧ w ≠ 0w ∧
    (∃R. ∀s'. R^* s s' ⇒ (eval s' g = SOME (ValWord w) ∧ w ≠ 0w))
Proof
  cheat
QED

Theorem evaluate_while_div_cases:
  evaluate (While g p,s) = (SOME TimeOut,s') ⇔
    eval s g = SOME (ValWord w) ∧ w ≠ 0w ∧
    (∃R. ∀s'. R^* s s' ⇒ (eval s' g = SOME (ValWord w) ∧ w ≠ 0w))
Proof
  cheat
QED

(* Theorem evaluate_while_div_eq: *)
(*   evaluate (While g p,s) = (SOME TimeOut,s') ⇔ *)
(*     itree_diverges (itree_mrec h_prog (While g p,s)) *)
(* Proof *)
(*   EQ_TAC >> rw [] *)
(*   >- (IMP_RES_TAC evaluate_while_div_cases >> *)
(*       ASSUME_TAC evaluate_itree_while_div_cases >> *)
(*       gvs []) *)
(*   >- (IMP_RES_TAC evaluate_itree_while_div_cases >> *)
(*       ASSUME_TAC evaluate_while_div_cases >> *)
(*       gvs[]) *)
(* QED *)

Theorem evaluate_itree_while_ret_cases:
  r = SOME (FinalFFI e) ∨ r = SOME (Return _) ⇒
  (strip_tau (itree_mrec h_prog (While g p,s)) (Ret (r,s'')) ⇔
     eval s g = SOME (ValWord w) ∧ w ≠ 0w ∧
     ∃R s' f. R^* s s' ∧ f (p,s') = (r,s''))
Proof
  cheat
QED

Theorem evaluate_while_ret_cases:
  r = SOME (FinalFFI e) ∨ r = SOME (Return _) ⇒
  (evaluate (While g p,s) = (r,s'') ⇔
     eval s g = SOME (ValWord w) ∧ w ≠ 0w ∧
     ∃R s' f. R^* s s' ∧ f (p,s') = (r,s''))
Proof
  cheat
QED

Theorem evaluate_while_ret_eq:
  r = SOME (FinalFFI e) ∨ r = SOME (Return _) ⇒
  (evaluate (While g p,s) = (r,s') ⇔
     strip_tau (itree_mrec h_prog (While g p,s)) (Ret (r,s')))
Proof
  cheat
QED

val _ = export_theory();
