(*
  Defines functional big-step semantics for Dafny.
*)

open preamble
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluate";

(* Related papers:
   "Functional Big-step Semantics", https://cakeml.org/esop16.pdf
   "Clocked Definitions in HOL", https://arxiv.org/pdf/1803.03417 *)

(* Helpers for clocked definition of semantics, which were adapted from
   semantics/evaluateScript.sml. *)

Definition fix_clock_def:
  fix_clock st₀ (st₁, res) =
  (st₁ with clock := if st₁.clock ≤ st₀.clock then st₁.clock else st₀.clock, res)
End

Triviality fix_clock_IMP:
  fix_clock st₀ x = (st₁, res) ⇒ st₁.clock ≤ st₀.clock
Proof
  Cases_on ‘x’ >> rw[fix_clock_def] >> gvs[]
QED

Definition dec_clock_def:
  dec_clock st = (st with clock := st.clock − 1)
End

(* Semantics for expressions *)

Definition evaluate_exp_ann_def[nocompute]:
  evaluate_exp st env (Lit l) = (st, Rval (lit_to_val l)) ∧
  evaluate_exp st env (Var name) =
  (case read_local st name of
   | NONE => (st, Rerr Rtype_error)
   | SOME v => (st, Rval v)) ∧
  evaluate_exp st₀ env (If tst thn els) =
  (case fix_clock st₀ (evaluate_exp st₀ env tst) of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v) =>
     (case do_cond v thn els of
      | NONE => (st₁, Rerr Rtype_error)
      | SOME branch => evaluate_exp st₁ env branch)) ∧
  evaluate_exp st₀ env (UnOp uop e) =
  (case evaluate_exp st₀ env e of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v) =>
     (case do_uop uop v of
      | NONE => (st₁, Rerr Rtype_error)
      | SOME res => (st₁, Rval res))) ∧
  evaluate_exp st₀ env (BinOp bop e₀ e₁) =
  (case fix_clock st₀ (evaluate_exp st₀ env e₀) of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v₀) =>
     (case try_sc bop v₀ of
      | SOME v => (st₁, Rval v)
      | NONE =>
        (case evaluate_exp st₁ env e₁ of
         | (st₂, Rerr err) => (st₂, Rerr err)
         | (st₂, Rval v₁) =>
           (case do_bop bop v₀ v₁ of
            | NONE => (st₂, Rerr Rtype_error)
            | SOME res => (st₂, Rval res))))) ∧
  evaluate_exp st₀ env (ArrLen e) =
  (case evaluate_exp st₀ env e of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v) =>
     (case get_array_len v of
      | NONE => (st₁, Rerr Rtype_error)
      | SOME len => (st₁, Rval (IntV &len)))) ∧
  evaluate_exp st₀ env (ArrSel arr idx) =
  (case fix_clock st₀ (evaluate_exp st₀ env arr) of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval arr) =>
     (case fix_clock st₁ (evaluate_exp st₁ env idx) of
      | (st₂, Rerr err) => (st₂, Rerr err)
      | (st₂, Rval idx) =>
        (case index_array st₂ arr idx of
         | NONE => (st₂, Rerr Rtype_error)
         | SOME v => (st₂, Rval v)))) ∧
  evaluate_exp st₀ env (FunCall name args) =
  (case FLOOKUP env.functions name of
   | NONE => (st₀, Rerr Rtype_error)
   | SOME (in_names, body) =>
     (case fix_clock st₀ (evaluate_exps st₀ env args) of
      | (st₁, Rerr err) => (st₁, Rerr err)
      | (st₁, Rval in_vs) =>
        (case set_up_call st₁ in_names in_vs [] of
         | NONE => (st₁, Rerr Rtype_error)
         | SOME (old_locals, st₂) =>
           if st₂.clock = 0 then (st₂, Rerr Rtimeout_error) else
           (case evaluate_exp (dec_clock st₂) env body of
            | (st₃, Rerr err) => (st₃, Rerr err)
            | (st₃, Rval v) => (restore_locals st₃ old_locals, Rval v))))) ∧
  evaluate_exp st env (Forall (var, t) e) =
  (if env.is_running then (st, Rerr Rtype_error)
   else if st.clock = 0 then (st, Rerr Rtimeout_error) else
   let eval = (λv. evaluate_exp (dec_clock (push_local st var v)) env e) in
     if (∃v. v ∈ all_values t ∧ SND (eval v) = Rerr Rtype_error)
     then (st, Rerr Rtype_error)
     else if (∃v. v ∈ all_values t ∧ SND (eval v) = Rerr Rtimeout_error)
     then (st, Rerr Rtimeout_error)
     else if (∀v. v ∈ all_values t ⇒ SND (eval v) = Rval (BoolV T))
     then (st, Rval (BoolV T))
     (* NOTE For now, for simplicity reasons, we do not check whether (eval v)
        is a Bool to throw a type error if not. Instead, we return (BoolV F). *)
     else (st, Rval (BoolV F))) ∧
  evaluate_exps st env [] = (st, Rval []) ∧
  evaluate_exps st₀ env (e::es) =
  (case fix_clock st₀ (evaluate_exp st₀ env e) of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v) =>
     (case evaluate_exps st₁ env es of
      | (st₂, Rerr err) => (st₂, Rerr err)
      | (st₂, Rval vs) => (st₂, Rval (v::vs))))
Termination
  wf_rel_tac ‘inv_image ($< LEX $<)
              (λx. case x of
                   | INL (s, _, exp) =>
                       (s.clock, exp_size exp)
                   | INR (s, _, exps) =>
                       (s.clock, list_size exp_size exps))’
  >> rpt strip_tac
  >> imp_res_tac fix_clock_IMP
  >> gvs [try_sc_def, dec_clock_def, set_up_call_def, push_local_def,
          oneline do_cond_def, AllCaseEqs ()]
End

Theorem evaluate_exp_clock:
  (∀st₀ env e st₁ r.
     evaluate_exp st₀ env e = (st₁, r) ⇒ st₁.clock ≤ st₀.clock) ∧
  (∀st₀ env es st₁ r.
     evaluate_exps st₀ env es = (st₁, r) ⇒ st₁.clock ≤ st₀.clock)
Proof
  ho_match_mp_tac evaluate_exp_ann_ind
  >> rpt strip_tac
  >> gvs [AllCaseEqs (), dec_clock_def, fix_clock_def, restore_locals_def,
          evaluate_exp_ann_def]
  >> EVERY (map imp_res_tac
                [set_up_call_clock, restore_locals_clock, fix_clock_IMP])
  >> gvs[]
QED

Theorem fix_clock_evaluate_exp:
  (fix_clock st (evaluate_exp st env exp) = evaluate_exp st env exp) ∧
  (fix_clock st (evaluate_exps st env exps) = evaluate_exps st env exps)
Proof
  Cases_on ‘evaluate_exp st env exp’ >> Cases_on ‘evaluate_exps st env exps’
  >> imp_res_tac evaluate_exp_clock
  >> gvs [fix_clock_def, state_component_equality]
QED

Theorem evaluate_exp_def[compute] =
  REWRITE_RULE [fix_clock_evaluate_exp] evaluate_exp_ann_def

Theorem evaluate_exp_ind =
  REWRITE_RULE [fix_clock_evaluate_exp] evaluate_exp_ann_ind

(* Semantics for rhs_exp *)

Definition evaluate_rhs_exp_def:
  evaluate_rhs_exp st env (ExpRhs e) = evaluate_exp st env e ∧
  evaluate_rhs_exp st₀ env (ArrAlloc _ len init) =
  (case evaluate_exp st₀ env len of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval len) =>
     (case evaluate_exp st₁ env init of
      | (st₂, Rerr err) => (st₂, Rerr err)
      | (st₂, Rval init) =>
        (case alloc_array st₂ len init of
         | NONE => (st₂, Rerr Rtype_error)
         | SOME (st₃, arr) => (st₃, Rval arr))))
End

Theorem evaluate_rhs_exp_clock:
  ∀st₀ env e st₁ res.
    evaluate_rhs_exp st₀ env e = (st₁, res) ⇒ st₁.clock ≤ st₀.clock
Proof
  rpt strip_tac
  >> gvs [oneline evaluate_rhs_exp_def, alloc_array_def, AllCaseEqs ()]
  >> imp_res_tac evaluate_exp_clock >> gvs []
QED

Definition evaluate_rhs_exps_def:
  evaluate_rhs_exps st env [] = (st, Rval []) ∧
  evaluate_rhs_exps st₀ env (e::es) =
  (case evaluate_rhs_exp st₀ env e of
   | (st₁, Rerr err) => (st₁, Rerr err)
   | (st₁, Rval v) =>
     (case evaluate_rhs_exps st₁ env es of
      | (st₂, Rerr err) => (st₂, Rerr err)
      | (st₂, Rval vs) => (st₂, Rval (v::vs))))
End

Theorem evaluate_rhs_exps_clock:
  ∀st₀ env es st₁ res.
    evaluate_rhs_exps st₀ env es = (st₁, res) ⇒ st₁.clock ≤ st₀.clock
Proof
  Induct_on ‘es’
  >> rpt strip_tac
  >> gvs [evaluate_rhs_exps_def, AllCaseEqs ()]
  >> imp_res_tac evaluate_rhs_exp_clock
  >> last_assum drule >> gvs []
QED

(* Semantics for assigning values *)

Definition assign_value_def:
  assign_value st₀ env (Var var) val =
  (case update_local st₀ var val of
   | NONE => (st₀, Rstop (Serr Rtype_error))
   | SOME st₁ => (st₁, Rcont)) ∧
  assign_value st₀ env (ArrSel arr idx) val =
  (case evaluate_exp st₀ env arr of
   | (st₁, Rerr err) => (st₁, Rstop (Serr err))
   | (st₁, Rval arr) =>
     (case evaluate_exp st₁ env idx of
      | (st₂, Rerr err) => (st₂, Rstop (Serr err))
      | (st₂, Rval idx) =>
        (case update_array st₂ arr idx val of
         | NONE => (st₂, Rstop (Serr Rtype_error))
         | SOME st₃ => (st₃, Rcont)))) ∧
  assign_value st env _ val = (st, Rstop (Serr Rtype_error))
End

Theorem assign_value_clock:
  ∀st₀ env e v st₁ res.
    assign_value st₀ env e v = (st₁, res) ⇒ st₁.clock ≤ st₀.clock
Proof
  rpt strip_tac
  >> gvs [update_local_def, update_array_def,
          oneline assign_value_def, AllCaseEqs ()]
  >> imp_res_tac evaluate_exp_clock >> gvs []
QED

Definition assign_values_def:
  assign_values st env [] [] = (st, Rcont) ∧
  assign_values st₀ env (lhs::lhss) (v::vs) =
  (case assign_value st₀ env lhs v of
   | (st₁, Rstop stp) => (st₁, Rstop stp)
   | (st₁, Rcont) => assign_values st₁ env lhss vs) ∧
  assign_values st env _ _ = (st, Rstop (Serr Rtype_error))
End

Theorem assign_values_clock:
  ∀st₀ env lhss vs st₁ res.
    assign_values st₀ env lhss vs = (st₁, res) ⇒ st₁.clock ≤ st₀.clock
Proof
  Induct_on ‘lhss’ >> Induct_on ‘vs’
  >> rpt strip_tac
  >> gvs [assign_values_def, AllCaseEqs ()]
  >> imp_res_tac assign_value_clock
  >> last_assum drule >> gvs []
QED

(* Semantics for statements *)

(* Stops the simplifier from non-terminating rewrites. *)
Definition STOP_def:
  STOP = I
End

Definition evaluate_stmt_ann_def[nocompute]:
  evaluate_stmt st env Skip = (st, Rcont) ∧
  evaluate_stmt st₀ env (Assert e) =
  (case evaluate_exp st₀ env e of
   | (st₁, Rerr err) => (st₁, Rstop (Serr err))
   | (st₁, Rval vs) =>
       if vs = BoolV T then (st₁, Rcont)
       else (st₁, Rstop (Serr Rtype_error))) ∧
  evaluate_stmt st₀ env (Then stmt₁ stmt₂) =
  (case fix_clock st₀ (evaluate_stmt st₀ env stmt₁) of
   | (st₁, Rstop stp) => (st₁, Rstop stp)
   | (st₁, Rcont) => evaluate_stmt st₁ env stmt₂) ∧
  evaluate_stmt st₀ env (If tst thn els) =
  (case evaluate_exp st₀ env tst of
   | (st₁, Rerr err) => (st₁, Rstop (Serr err))
   | (st₁, Rval tst) =>
     (case do_cond tst thn els of
      | NONE => (st₁, Rstop (Serr Rtype_error))
      | SOME branch => evaluate_stmt st₁ env branch)) ∧
  evaluate_stmt st env (Dec locals scope) =
  (let names = MAP FST locals in
     evaluate_stmt (declare_locals st names) env scope) ∧
  evaluate_stmt st₀ env (Assign lhss rhss) =
  (case evaluate_rhs_exps st₀ env rhss of
   | (st₁, Rerr err) => (st₁, Rstop (Serr err))
   | (st₁, Rval vals) => assign_values st₁ env lhss vals) ∧
  evaluate_stmt st₀ env (While guard invs decrs mods body) =
  (case evaluate_exp st₀ env guard of
   | (st₁, Rerr err) => (st₁, Rstop (Serr err))
   | (st₁, Rval guard_v) =>
     if guard_v = BoolV F then (st₁, Rcont)
     else if guard_v = BoolV T then
       (case fix_clock st₁ (evaluate_stmt st₁ env body) of
        | (st₂, Rstop stp) => (st₂, Rstop stp)
        | (st₂, Rcont) =>
          if st₂.clock = 0 then (st₂, Rstop (Serr Rtimeout_error)) else
          evaluate_stmt (dec_clock st₂) env
                        (STOP (While guard invs decrs mods body)))
     else (st₁, Rstop (Serr Rtype_error))) ∧
  evaluate_stmt st₀ env (Print ets) =
  (let es = MAP FST ets in
     (case evaluate_exps st₀ env es of
      | (st₁, Rerr err) => (st₁, Rstop (Serr err))
      | (st₁, Rval vs) =>
        (case print_string st₁ vs of
         | NONE => (st₁, Rstop (Serr Rtype_error))
         | SOME st₂ => (st₂, Rcont)))) ∧
  evaluate_stmt st₀ env (MetCall lhss name args) =
  (case FLOOKUP env.methods name of
   | NONE => (st₀, Rstop (Serr Rtype_error))
   | SOME (in_ns, out_ns, body) =>
     (case evaluate_exps st₀ env args of
      | (st₁, Rerr err) => (st₁, Rstop (Serr err))
      | (st₁, Rval in_vs) =>
        (case set_up_call st₁ in_ns in_vs out_ns of
         | NONE => (st₁, Rstop (Serr Rtype_error))
         | SOME (old_locals, st₂) =>
           if st₂.clock = 0 then (st₂, Rstop (Serr Rtimeout_error)) else
           (case evaluate_stmt (dec_clock st₂) env body of
            | (st₃, Rcont) => (st₃, Rstop (Serr Rtype_error))
            | (st₃, Rstop (Serr err)) => (st₃, Rstop (Serr err))
            | (st₃, Rstop Sret) =>
              (case read_outs st₃ out_ns of
               | NONE => (st₃, Rstop (Serr Rtype_error))
               | SOME out_vs =>
                 (case assign_values st₃ env lhss out_vs of
                  | (st₄, Rstop (Serr err)) => (st₄, Rstop (Serr err))
                  | (st₄, Rstop Sret) => (st₄, Rstop (Serr Rtype_error))
                  | (st₄, Rcont) =>
                      (restore_locals st₄ old_locals, Rcont))))))) ∧
  evaluate_stmt st env Return = (st, Rstop Sret)
Termination
  wf_rel_tac ‘inv_image ($< LEX $<)
              (λx. case x of (s, _, stmt) => (s.clock, statement_size stmt))’
  >> rpt strip_tac
  >> imp_res_tac fix_clock_IMP
  >> imp_res_tac evaluate_exp_clock
  >> gvs [dec_clock_def, set_up_call_def, declare_locals_def,
          oneline do_cond_def, AllCaseEqs ()]
End

Theorem evaluate_stmt_clock:
  ∀st₀ env e st₁ r.
    evaluate_stmt st₀ env e = (st₁, r) ⇒ st₁.clock ≤ st₀.clock
Proof
  ho_match_mp_tac evaluate_stmt_ann_ind
  >> rpt strip_tac
  >> gvs [AllCaseEqs (), dec_clock_def, fix_clock_def, restore_locals_def,
          declare_locals_def, print_string_def, evaluate_stmt_ann_def]
  >> EVERY (map imp_res_tac
                [set_up_call_clock, restore_locals_clock, fix_clock_IMP,
                 evaluate_rhs_exps_clock, evaluate_exp_clock,
                 assign_values_clock]) >> gvs[]
QED

Theorem fix_clock_evaluate_stmt:
  fix_clock st (evaluate_stmt st env stmt) = evaluate_stmt st env stmt
Proof
  Cases_on ‘evaluate_stmt st env stmt’
  >> imp_res_tac evaluate_stmt_clock
  >> gvs [fix_clock_def, state_component_equality]
QED

Theorem evaluate_stmt_def[compute] =
  REWRITE_RULE [fix_clock_evaluate_stmt] evaluate_stmt_ann_def

Theorem evaluate_stmt_ind =
  REWRITE_RULE [fix_clock_evaluate_stmt] evaluate_stmt_ann_ind

val _ = export_theory ();
