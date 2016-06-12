open preamble
     closSemTheory closPropsTheory
     clos_callTheory;

val _ = new_theory"clos_callProof";

(* value relation *)

open clos_knownProofTheory

(* TODO: above open is just for subspt *)

(* TODO: move *)

val v_size_lemma = prove(
  ``MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl``,
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);
(* -- *)

val v_rel_def = tDefine"v_rel"`
  (v_rel g (Number i) v ⇔ v = Number i) ∧
  (v_rel g (Word64 w) v ⇔ v = Word64 w) ∧
  (v_rel g (Block n vs) v ⇔
    ∃vs'. v = Block n vs' ∧ LIST_REL (v_rel g) vs vs') ∧
  (v_rel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (v_rel g (Closure loco vs1 env1 n bod1) v ⇔
     ∃loc vs2 env2 n bod2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Closure loco vs2 env2 n bod2 ∧
       subspt (FST g0) (FST g) ∧
       let es = FST(calls [bod1] g0) in
       if (∀v. has_var v (SND (free es)) ⇒ v < n) then
         bod2 = Call (loc+1) (GENLIST Var n) ∧
         ALOOKUP (SND g) (loc+1) = SOME (n, HD es)
       else
         bod2 = HD(FST(calls [bod1] g0))) ∧
  (v_rel g (Recclosure loco vs1 env1 fns1 i) v ⇔
     ∃loc vs2 env2 fns2 g0.
       loco = SOME loc ∧ EVEN loc ∧
       LIST_REL (v_rel g) vs1 vs2 ∧ LIST_REL (v_rel g) env1 env2 ∧
       v = Recclosure loco vs2 env2 fns2 i ∧
       subspt (FST g0) (FST g) ∧
       let es = FST (calls (MAP SND fns1) (insert_each loc (LENGTH fns1) g0)) in
       if EVERY2 (λ(n,_) p. ∀v. has_var v (SND (free [p])) ⇒ v < n) fns1 es then
         fns2 = calls_list loc fns1 ∧
         LIST_RELi (λi (n,_) p. ALOOKUP (SND g) (loc + 2*i) = SOME (n,p)) fns1 es
       else
         fns2 = ZIP (MAP FST fns1, FST (calls (MAP SND fns1) g0)))`
  (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[]);

val state_rel_def = Define`
  state_rel g (s:'ffi closSem$state) (t:'ffi closSem$state) ⇔
    (s.ffi = t.ffi) ∧
    (s.clock = t.clock) ∧
    LIST_REL (OPTREL (v_rel g)) s.globals t.globals ∧
    fmap_rel (ref_rel (v_rel g)) s.refs t.refs ∧
    s.code = FEMPTY ∧ t.code = FEMPTY |++ SND g`;

(* compiler correctness *)

val calls_correct = Q.store_thm("calls_correct",
  `(∀tmp xs env1 s0 env2 t0 res s.
    tmp = (xs,env1,s0) ∧
    evaluate (xs,env1,s0) = (res,s) ∧
    calls xs g0 = (ys,g) ∧
    LIST_REL (v_rel g) env1 env2 ∧
    state_rel g s0 t0
    ⇒
    ∃res' t.
    evaluate (ys,env2,t0) = (res',t) ∧
    state_rel g s t ∧
    result_rel (LIST_REL (v_rel g)) (v_rel g) res res')`,
  cheat);

val _ = export_theory();
