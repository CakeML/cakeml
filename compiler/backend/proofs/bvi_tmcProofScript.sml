(*
  Correctness proof for bvi_tailrec
*)
Theory bvi_tmcProof
Ancestors
  bvi_tmc bviProps bviSem
Libs
  preamble

val s = mk_var("s",
  type_of ``bviSem$evaluate`` |> strip_fun |> snd |> dest_prod |> snd
  |> type_subst [alpha|->``:num#'c``,beta|->``:'ffi``]);

Definition env_rel_def:
  env_rel opt l env1 env2 <=>
    isPREFIX env1 env2 ∧
    (opt ⇒
      LENGTH env1 = l ∧
      LENGTH env2 > l ∧
      ∃hole_ptr hole_idx.
        EL l env2 = RefPtr F hole_ptr ∧
        EL (l + 1) env2 = Number hole_idx)
End

Overload in_ns_2[local] = ``λn. n MOD bvl_to_bvi_namespaces = 2``

Definition code_rel_def:
  code_rel c1 c2 ⇔
    ∀loc arity exp exp_aux.
      lookup loc c1 = SOME (arity, exp) ⇒
      ∃n.
        (rewrite_aux loc n arity exp = NONE ⇒
          lookup loc c2 = SOME (arity, exp)) ∧
        (rewrite_aux loc n arity exp = SOME exp_aux ⇒
          ∀exp_opt.
            compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
              lookup loc c2 = SOME (arity, exp_aux) ∧
              lookup n c2 = SOME (arity + 1, exp_opt))
End

Definition optimized_code_def:
  optimized_code loc arity exp n c =
    ∃exp_aux exp_opt.
        compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ∧
        lookup loc c                = SOME (arity, exp_aux) ∧
        lookup n c                  = SOME (arity + 1, exp_opt)
End

(* Copied *)
Definition free_names_def:
  free_names n (name: num) ⇔ ∀k. n + bvl_to_bvi_namespaces*k ≠ name
End

(* Copied *)
Definition namespace_rel_def:
  namespace_rel (c1:'a spt) (c2:'a spt) ⇔
    (∀n. n ∈ domain c2 ∧ bvl_num_stubs ≤ n ⇒ if in_ns_2 n then n ∉ domain c1 else n ∈ domain c1) ∧
    (∀n. n ∈ domain c1 ∧ bvl_num_stubs ≤ n ⇒ ¬(in_ns_2 n)) ∧
    (∀n. n ∈ domain c2 ∧ n < bvl_num_stubs ⇒ n ∈ domain c1)
End

(* Copied *)
Definition input_condition_def:
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY ($~ o in_ns_2 o FST) (FILTER ((<=) bvl_num_stubs o FST) prog) ∧
   bvl_num_stubs ≤ next ∧ in_ns_2 next
End

(* Copied *)
Definition state_rel_def:
  state_rel s (t:('a,'ffi) bviSem$state) ⇔
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = state_co compile_prog s.compile_oracle ∧
    s.compile = state_cc compile_prog t.compile ∧
    code_rel s.code t.code ∧
    namespace_rel s.code t.code ∧
    (∀n. let ((next,cfg),prog) = s.compile_oracle n in
            input_condition next prog) ∧
    (∀n. n ∈ domain t.code ∧ in_ns_2 n ⇒ n < FST(FST(s.compile_oracle 0)))
End

Theorem compile_prog_code_rel:
   compile_prog next prog = (next1, prog2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ⇒
     code_rel (fromAList prog) (fromAList prog2)
Proof
  cheat
QED

(* Copied *)
(* Original with types:
     ∀(xs :bvi$exp list) (s :(num # γ, 'ffi) state) (env1 :v list)
         (r :(v list, v) result) (t :(num # γ, 'ffi) state) (opt :bool)
         (s' :(γ, 'ffi) state) (acc :num) (env2 :v list) (loc :num)
         (ts :v_ty list) (ty :v_ty).
       evaluate (xs,env1,s) = (r,t) ∧ env_rel ty opt acc env1 env2 ∧
       state_rel s s' ∧ ty_rel env1 ts ∧ (opt ⇒ LENGTH xs = (1 :num)) ∧
       r ≠ (Rerr (Rabort Rtype_error :v error_result) :(v list, v) result) ⇒
       ∃(t' :(γ, 'ffi) state).
         evaluate (xs,env2,s') = (r,t') ∧ state_rel t t' ∧
         (opt ⇒
          ∀(op :assoc_op) (n :num) (exp :bvi$exp) (arity :num).
            lookup loc s.code = SOME (arity,exp) ∧
            optimized_code loc arity exp n s'.code op ∧ op_type op = ty ∧
            (∃(op1 :assoc_op) (tt :v_ty list) (ty :v_ty) (r :bool).
               scan_expr ts loc [HD xs] = [(tt,ty,r,SOME op1)] ∧ ty ≠ Any ∧
               op1 ≠ Noop ∧ op_type op1 = op_type op) ⇒
            (let
               ((lr :bool),(x :bvi$exp)) = rewrite loc n op acc ts (HD xs)
             in
               ∃(rrr :(v list, v) result) (t1 :(γ, 'ffi) state)
                   (t2 :(γ, 'ffi) state).
                 evaluate ([x],env2,s') = (rrr,t1) ∧
                 evaluate ([apply_op op (Var acc :bvi$exp) (HD xs)],env2,s') =
                 (rrr,t2) ∧ state_rel t t1 ∧ state_rel t t2)): thm
*)
Theorem evaluate_rewrite_tmc:
   ∀xs ^s l env1 r t opt s' env2 loc.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel opt l env1 env2 ∧
     state_rel s s' ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
       ?t'.
       evaluate (xs, env2, s') = (r, t') ∧
       state_rel t t' ∧
       (opt ⇒
         ∀n exp arity.
           lookup loc s.code = SOME (arity, exp) ∧
           optimized_code loc arity exp n s'.code ∧
           (∃loc_op.
             rewrite_aux loc loc_op arity (HD xs) = SOME aux) ⇒
               (* let x = rewrite_opt loc arity (arity + 1) (arity + 2) (HD xs) in *)
                 ∃rrr t1 t2.
                   evaluate ([aux], env2, s') = (rrr,t1) ∧
                   evaluate (xs, env2, s') = (rrr,t2) ∧
                   state_rel t t1 ∧
                   state_rel t t2)
Proof
  cheat
QED

(* Copied *)
Theorem evaluate_compile_prog:
   input_condition next prog ∧
   (∀n next cfg prog. co n = ((next,cfg),prog) ⇒ input_condition next prog) ∧
   (∀n. MEM n (MAP FST (SND (compile_prog next prog))) ∧ in_ns_2 n ⇒ n < FST (FST (co 0))) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) co
                 (state_cc compile_prog cc) k) = (r, s) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog)))
            (state_co compile_prog co) cc k)
      = (r, s2) ∧
     state_rel s s2
Proof
  rw []
  >> qmatch_asmsub_abbrev_tac `(es,env,st1)`
  >> `env_rel F 0 env env` by fs [env_rel_def]
  >> Cases_on `compile_prog next prog`
  >> fs []
  >> drule (GEN_ALL compile_prog_code_rel)
  >> strip_tac
  >> qmatch_goalsub_abbrev_tac`(es,env,st2)`
  >> `state_rel st1 st2` by cheat
  >> drule evaluate_rewrite_tmc
  >> disch_then (qspec_then `F` drule)
  cheat
QED

(* Copied *)
Theorem compile_prog_semantics:
   input_condition n prog ∧
   (∀k n cfg prog. co k = ((n,cfg),prog) ⇒ input_condition n prog) ∧
   (∀k. MEM k (MAP FST prog2) ∧ in_ns_2 k ⇒ k < FST(FST (co 0))) ∧
   SND (compile_prog n prog) = prog2 ∧
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start ≠
      ffi$Fail ⇒
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start =
   semantics ffi (fromAList prog2) (state_co compile_prog co) cc start
Proof
  cheat
QED

