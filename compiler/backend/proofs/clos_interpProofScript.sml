(*
  Correctness proof for closLang interpreter used by the REPL, i.e. Install,
  to avoid spending time compiling simple run-once code in declarations.
*)
open preamble backendPropsTheory closLangTheory closSemTheory closPropsTheory
     clos_interpTheory;

val _ = new_theory "clos_interpProof";

val _ = set_grammar_ancestry ["closLang", "closProps", "clos_interp"];

Definition insert_interp_def:
  insert_interp xs = (xs : closLang$exp list)
End

Definition state_rel_def:
  state_rel (s:('c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) ∧
    s.code = FEMPTY ∧ t.code = FEMPTY ∧
    t.max_app = s.max_app ∧ 1 <= s.max_app ∧
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    s.globals = t.globals ∧
    s.refs = t.refs ∧
    s.compile = pure_cc (insert_interp ## I) t.compile ∧
    t.compile_oracle = pure_co (insert_interp ## I) o s.compile_oracle
End

Theorem evaluate_interp_thm:
   (!tmp xs env (s1:('c,'ffi) closSem$state) t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) ∧ res <> Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ==>
     ?ck t2.
        (evaluate (xs,env,(t1 with clock := t1.clock + ck)) = (res,t2)) ∧
        state_rel s2 t2) ∧
   (!loc f args (s:('c,'ffi) closSem$state) res s2 t1.
       evaluate_app loc f args s = (res,s2) ∧ res <> Rerr (Rabort Rtype_error) ⇒
       state_rel s t1
       ⇒
       ?ck t2.
          (evaluate_app loc f args (t1 with clock := t1.clock + ck) = (res,t2)) ∧
          state_rel s2 t2)
Proof
  ho_match_mp_tac evaluate_ind \\ srw_tac[][]
  \\ cheat
QED

(* preservation of observable semantics *)

Theorem semantics_intro_multi:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (insert_interp ## I) cc) (attach_interpreter xs) <> Fail ==>
   (∀n. SND (SND (co n)) = []) ∧ 0 < max_app ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (pure_co (insert_interp ## I) ∘ co) cc (attach_interpreter xs) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (insert_interp ## I) cc) (attach_interpreter xs)
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq \\ rw []
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ qmatch_asmsub_abbrev_tac ‘evaluate (_,_,iis) = _’
  \\ qspecl_then [‘attach_interpreter xs’,‘[]’,‘iis’] mp_tac
        (evaluate_interp_thm |> SIMP_RULE std_ss [] |> CONJUNCT1)
  \\ disch_then drule \\ fs []
  \\ disch_then $ qspec_then ‘initial_state ffi max_app
        FEMPTY (pure_co (insert_interp ## I) ∘ co) cc k’ mp_tac
  \\ impl_tac
  >- simp [Abbr‘iis’,state_rel_def,initial_state_def]
  \\ strip_tac \\ fs [closPropsTheory.initial_state_clock]
  \\ first_x_assum $ irule_at $ Pos hd
  \\ fs [state_rel_def]
QED

val _ = export_theory();
