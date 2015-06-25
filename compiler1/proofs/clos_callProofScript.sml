open preamble clos_callTheory;

val _ = new_theory"clos_callProof";

(* value relation *)

val (approx_rules,approx_ind,approx_cases) = Hol_reln`
  (approx (Clos n a e) (Closure n arg_env clo_env a exp)) ∧
  (* I don't think Recclosures are ever tracked (they will just be Other)
  (i < LENGTH fns ∧ a = FST(EL i fns)
   ⇒
   approx (Clos n a e) (Recclosure n arg_env clo_env fns i)) ∧
  *)
  (LIST_REL approx as vs
   ⇒
   approx (Tuple as) (Block t vs)) ∧
  (approx (Int i) (Number i)) ∧
  (approx Other x)`;

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln`
  (approx a (Number j)
   ⇒
   v_rel code a (Number j) (Number j)) ∧
  (approx a (Block t ys) ∧
   LIST_REL (v_rel code a) xs ys
   ⇒
   v_rel code a (Block t xs) (Block t ys)) ∧
  (approx a (RefPtr r)
   ⇒
   v_rel code a (RefPtr r) (RefPtr r)) ∧
  (v_rel code Other
     (Closure loc arg_env clo_env num_args exp)
     (Closure loc arg_env clo_env num_args exp)) ∧
  (v_rel code Other
     (Recclosure loc arg_env clo_env fns i)
     (Recclosure loc arg_env clo_env fns i)) ∧
  (fs1 = get_free_vars [Fn loc [] num_args exp] ∧
   fs = MAP (λi. i + num_args) fs1 ∧
   FLOOKUP code loc = SOME (num_args+LENGTH fs1,calls_body num_args fs1 exp)
   ⇒
   v_rel code (Clos loc num_args fs)
     (Closure loc arg_env clo_env num_args exp)
     (Closure loc arg_env clo_env num_args (Call loc (GENLIST Var num_args ++ MAP Var fs)))) ∧
  (i < LENGTH fns ∧ FST(EL i fns) = num_args ∧
   fs1 = get_free_vars ARB (* TODO: need to pull this out of calls_def? *) ∧
   fs = MAP (λi. i + num_args) fs1 ∧
   FLOOKUP code (loc+i) = SOME (num_args+LENGTH fs1,calls_body num_args fs1 (SND(EL i fns)))
   ⇒
   v_rel code (Clos loc num_args fs)
     (Recclosure loc arg_env clo_env fns i)
     (Closure loc arg_env clo_env num_args (Call (loc+i) (GENLIST Var num_args ++ MAP Var fs))))`;

val state_rel_def = Define`
  state_rel g (s:closSem$state) (t:closSem$state) ⇔
    (s.io = t.io) ∧
    (s.clock = t.clock) ∧
    ¬s.restrict_envs ∧ ¬t.restrict_envs ∧
    (∀i. i < LENGTH s.globals ⇒
         i < LENGTH t.globals ∧
         ∃a. lookup i g = SOME a ∧
             OPTREL (v_rel s.code a) (EL i s.globals) (EL i t.globals)) ∧
    fmap_rel (ref_rel (v_rel s.code Other)) s.refs t.refs ∧
    s.code = FEMPTY ∧
    (* could say more here, not sure what is required... *)
    (∀a c. (a,c) ∈ FRANGE t.code ⇒
      ∃n fs b.
        a = n + LENGTH fs ∧
        c = calls_body n fs b)`;

val env_rel_def = Define`
  env_rel code as env1 env2 ⇔
    LENGTH as = LENGTH env1 ∧
    LIST_REL (UNCURRY (v_rel code)) (ZIP(as,env1)) env2`;

(* compiler correctness *)

(*
val calls_correct = Q.prove(
  `evaluate xs
   calls xs env g0 = (ys,as,g) ⇒
*)

val _ = export_theory();
