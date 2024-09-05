(*
  Defines a new incremental backend which is
  meant to be syntactically equal to backend but allows
  compiling program in a part-by-part manner
*)

open preamble backendTheory;

val _ = new_theory"ibackend";

(*
  High-level idea:

  We'll define incremental compilation in three steps to
    simulate to_lab:

  1. init_icompile:

    This should initialize incremental compilation by running
    the CakeML compiler to insert all of its initial stubs.

  2. icompile:

    This should run incremental compilation on a chunk of
    input source program.

  3. end_icompile:

    This should "end" compilation by inserting the main
    entry point of the whole program.

  Then, we'll do a whole program assembly step

  4. assemble/finalize

*)

(******************************************************************************)
(*                                                                            *)
(* Temporary def of compile_alt                                               *)
(*                                                                            *)
(******************************************************************************)

(* An alternative version compile_def that we'll prove correctness against
  TODO: this is being defined incrementally
  TODO: the _alt parts of this definition will need to be moved into backend/ *)

(* TODO: need to remove builtin call to flat_elim *)
Definition compile_flat_alt_def:
  compile_flat_alt pcfg =
    MAP (flat_pattern$compile_dec pcfg)
End

(* TODO: we'll need to re-insert the global allocations here *)
Definition source_to_flat_compile_prog_alt_def:
  source_to_flat_compile_prog_alt (c: source_to_flat$config) p =
  let next = c.next with <| vidx := c.next.vidx + 1 |> in
  let envs = <| next := 0; generation := c.envs.next; envs := LN |> in
  let (_, next, e, gen, p') = compile_decs [] 1n next c.mod_env envs p in
  let envs2 = <| next := c.envs.next + 1;
                 env_gens := insert c.envs.next gen.envs c.envs.env_gens |> in
    (c with <| next := next; envs := envs2; mod_env := e |>,
     alloc_env_ref :: p')
End



Definition source_to_flat_compile_alt_def:
  source_to_flat_compile_alt (c: source_to_flat$config) p =
  let (c', p') = source_to_flat_compile_prog_alt c p in
  let p' = MAP (flat_pattern$compile_dec c'.pattern_cfg) p' in
  (c', p')
End

(* we always insert the clos_interpreter code, this should be put into config *)
Definition flat_to_clos_compile_alt_def:
  flat_to_clos_compile_alt p =
  (clos_interp$compile_init T) :: flat_to_clos$compile_decs p
End


(* partial, to delete this when complete *)
Definition clos_to_bvl_compile_common_def:
  clos_to_bvl_compile_common (c: clos_to_bvl$config) p =
  let p = clos_mti$compile c.do_mti c.max_app p in
  p
End







(* TODO: extend this step-by-step *)
Definition compile_alt_def:
  compile_alt c p =
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat_compile_alt c.source_conf p in
    let p = flat_to_clos_compile_alt p in
    (c',p)
End

(******************************************************************************)
(*                                                                            *)
(* Defining icompile                                                          *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(* Source to flat                                                             *)
(*                                                                            *)
(******************************************************************************)

(* Some diagram to remind me *)

(*
      Given P as input

      mono_compile

      P --- source_to_source ---> P ---source_to_flat---> [source_to_flat_stub] ++ P ---flat_to_clos---> [flat_to_clos_stub] ++ P


      icompile_init                                     icompile                icompile_end

        conf                               +------->  (iconf, p: source)        +---> iconf
          |                                |              |                     |       |
          | s_to_f_init                    |              |                     |       |
          |                                |              |                     |       |
          ∨                                |              ∨                     |       ∨
      (iconf, s_to_f_stub)                 |           (iconf, p: flat)         |     conf
          |                                |              |                     |       |
          | f_to_c init                    |              |                     |       |
          |                                |              |                     |       |
          ∨                                |              ∨                     |       ∨
      (iconf, -----------------------------+            (iconf,-----------------+      conf
       f_to_c_compile (s_to_f_stub)                      p: clos)
       ++ f_to_c_stub)

-------> boundary




*)




Datatype:
  source_iconfig =
  <| n : num ;
     next : next_indices;
     env : environment;
     env_gens : environment_generation_store;
     pattern_cfg : flat_pattern$config
     |>
End

Datatype:
  clos_iconfig =
  <| do_mti : bool;
     max_app: num;
     next_loc : num;
     known_conf : clos_known$config option;
     known_g : val_approx sptree$num_map;
     do_call : bool;
     clos_call_aux : (num # num# closLang$exp) list;
     clos_call_g : sptree$num_set;
     es_to_chain : closLang$exp list
  |>
End





Definition icompile_source_to_flat_def:
  icompile_source_to_flat (source_iconf: source_iconfig) p =
  let n = source_iconf.n in
  let next = source_iconf.next in
  let env = source_iconf.env in
  let envs = source_iconf.env_gens in
  let (n', next1, new_env1, env_gens1, p') = compile_decs [] n next env envs p in
  let source_iconf = source_iconf with <| n := n'; next := next1; env := extend_env new_env1 env; env_gens := env_gens1|> in
  (source_iconf, MAP (flat_pattern$compile_dec source_iconf.pattern_cfg) p')
End

Definition icompile_flat_to_clos_def:
  icompile_flat_to_clos p =
  flat_to_clos$compile_decs p
End



Definition icompile_clos_to_bvl_common_def:
  icompile_clos_to_bvl_common (clos_iconf: clos_iconfig) p =
  let p = clos_mti$compile clos_iconf.do_mti clos_iconf.max_app p in
  let loc = clos_iconf.next_loc in
  let (n, p) = renumber_code_locs_list loc p in
  let (kc, p, g) = (case clos_iconf.known_conf of
                 | NONE => (NONE, p, LN)
                 | SOME c =>
                     let p = clos_fvs$compile p in
                     let (p, g) = known c p [] clos_iconf.known_g in
                     let p = remove_ticks (MAP FST p) in
                     let p = let_op p in
                       (SOME c, p, g)) in

  let (p, (clos_call_g, aux)) = ( case clos_iconf.do_call of
                           | F => (p, (LN, []))
                           | T => clos_call$calls p (clos_iconf.clos_call_g,[])
                                ) in

  let clos_iconf = clos_iconf with <| known_conf := kc;
                                      next_loc := n;
                                      known_g := g;
                                      (* keep it for now, just to make config same *)
                                      clos_call_aux :=  aux ++ clos_iconf.clos_call_aux;
                                      clos_call_g := clos_call_g;
                                      es_to_chain := clos_iconf.es_to_chain ++ p;
                                   |> in
    let p = clos_annotate$compile aux in
  (clos_iconf, p)
End



Definition init_icompile_def:
  init_icompile (source_conf : source_to_flat$config) =
  let next = source_conf.next with <| vidx := source_conf.next.vidx + 1 |> in
  let env_gens = <| next := 0; generation := source_conf.envs.next; envs := LN |> in
  let flat_stub = flat_pattern$compile_dec source_conf.pattern_cfg source_to_flat$alloc_env_ref in
  (* always insert interpreter code *)
  let clos_stub = (clos_interp$compile_init T) :: (flat_to_clos$compile_decs [flat_stub]) in

    (<| n := 1n;
       next := next;
       env := source_conf.mod_env;
       env_gens := env_gens;
       pattern_cfg := source_conf.pattern_cfg |> : source_iconfig,
     clos_stub)

End

Definition icompile_def:
  icompile (source_iconf : source_iconfig) (clos_iconf: clos_iconfig)  p =
  let p = source_to_source$compile p in
  let (source_iconf, p) = icompile_source_to_flat source_iconf p in
  let p = icompile_flat_to_clos p in
  let (clos_iconf, p) = icompile_clos_to_bvl_compile_common clos_iconf p in
  (source_iconf, clos_iconf, p)

End


Definition fold_icompile_def:
  fold_icompile c []  = (c, [])
  /\
  fold_icompile c (prog :: progs) =
  let (c', prog') = icompile c prog in
  let (c'', progs') = fold_icompile c' progs in
    (c'', prog' ++ progs')

End


Definition end_icompile_def:
  end_icompile (source_iconf: source_iconfig) (source_conf: source_to_flat$config) =
  let envs =
      <| next := source_conf.envs.next + 1;
         env_gens :=
         insert source_conf.envs.next
                source_iconf.env_gens.envs
                source_conf.envs.env_gens;
      |> in
    source_conf with
                <| next := source_iconf.next;
                   envs := envs;
                   mod_env := source_iconf.env |>
End

(******************************************************************************)
(*                                                                            *)
(* Syntactic correctness or icompile                                          *)
(*                                                                            *)
(******************************************************************************)




Triviality extend_env_assoc:
  extend_env e1 ( extend_env e2 e3) = extend_env (extend_env e1 e2) e3
Proof
  rw[source_to_flatTheory.extend_env_def, namespacePropsTheory.nsAppend_assoc]
QED

Triviality extend_env_empty_env:
  extend_env empty_env env = env ∧
  extend_env env empty_env = env

Proof

  rw[source_to_flatTheory.extend_env_def,
     namespacePropsTheory.nsAppend_assoc,
     source_to_flatTheory.empty_env_def,
     namespaceTheory.nsAppend_def] >>
  simp[source_to_flatTheory.environment_component_equality]
QED

Theorem source_to_flat_compile_decs_lemma_cons:
  compile_decs t n next env envs (d :: ds) =
  let (n', next1, new_env1, envs1, d') = compile_decs t n next env envs [d] in
  let (n'', next2, new_env2, envs2, ds') =
      compile_decs t n' next1 (extend_env new_env1 env) envs1 ds
  in
    (n'', next2, extend_env new_env2 new_env1, envs2, d'++ds')
Proof
  rw [source_to_flatTheory.compile_decs_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on ‘ds’
  >- (
    fs[source_to_flatTheory.compile_decs_def] >> gvs[extend_env_empty_env] )
  >- (
    rw[source_to_flatTheory.compile_decs_def])
QED

Theorem source_to_flat_compile_decs_lemma:
  ∀xs n next env envs .
  source_to_flat$compile_decs t n next env envs (xs ++ ys) =
  let (n', next1, new_env1, envs1, xs') = source_to_flat$compile_decs t n next env envs xs in
  let (n'', next2, new_env2, envs2, ys') = source_to_flat$compile_decs t n' next1 (extend_env new_env1 env) envs1 ys in
  (n'', next2, extend_env new_env2 new_env1, envs2, xs' ++ ys')

Proof
  Induct >- (
  rw[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[source_to_flatTheory.compile_decs_def]  >> gvs[extend_env_empty_env]
  ) >- (
  rpt gen_tac >>
  simp[] >>
  once_rewrite_tac[source_to_flat_compile_decs_lemma_cons] >>
  rw[] >> rpt (pairarg_tac >> gvs[])  >> gvs[extend_env_assoc])
QED



Theorem flat_to_clos_compile_decs_and_append_commute:
  ∀p1.
  flat_to_clos$compile_decs (p1 ++ p2) =
  (flat_to_clos$compile_decs p1) ++ (flat_to_clos$compile_decs p2)
Proof
  Induct >> rw[flat_to_closTheory.compile_decs_def] >>
  Cases_on ‘h’ >> simp[flat_to_closTheory.compile_decs_def]
QED

Theorem flat_to_clos_compile_decs_cons:
  flat_to_clos$compile_decs (p :: ps) =
  flat_to_clos$compile_decs ([p] ++ ps)
Proof
  rw[flat_to_closTheory.compile_decs_def]
QED



Theorem icompile_flat_to_clos_and_append_commute:
  icompile_flat_to_clos (p1 ++ p2) =
  (icompile_flat_to_clos p1) ++ (icompile_flat_to_clos p2)
Proof
  rw[icompile_flat_to_clos_def] >> simp[flat_to_clos_compile_decs_and_append_commute]
QED


Theorem source_to_source_compile_append:
  ∀p1 p2.
  source_to_source$compile (p1 ++ p2) =
  (source_to_source$compile p1 ++ source_to_source$compile p2)
Proof
  simp[source_to_sourceTheory.compile_def] >>
  Induct >> rw[source_letTheory.compile_decs_def] >>
  every_case_tac >> gs[]
QED

Theorem intro_multi_cons:
  ∀e es. intro_multi max_app (e::es) = HD(intro_multi max_app [e])::intro_multi max_app es
Proof
  Induct_on ‘es’ >> gvs[clos_mtiTheory.intro_multi_def,clos_mtiTheory.intro_multi_length]
QED

Theorem intro_multi_append:
  ∀p1. intro_multi max_app (p1 ++ p2) = (intro_multi max_app p1) ++ (intro_multi max_app p2)
Proof
  Induct >> rw[clos_mtiTheory.intro_multi_def] >>
  once_rewrite_tac[intro_multi_cons] >>
  every_case_tac >> gvs[]
QED

Theorem clos_mti_compile_append:
  clos_mti$compile do_mti max_app (p1 ++ p2) =
  clos_mti$compile do_mti max_app p1 ++ clos_mti$compile do_mti max_app p2
Proof
  rw[clos_mtiTheory.compile_def] >>
  Cases_on ‘do_mti’ >- (
  rw[clos_mtiTheory.compile_def, intro_multi_append]
  ) >- (
  fs[clos_mtiTheory.compile_def]
  )
QED

Theorem renumber_code_locs_lemma:
  ∀n p1 p1_renumbered.
  renumber_code_locs_list n p1 = (n1, p1_renumbered) ∧
  renumber_code_locs_list n1 p2 = (n2, p2_renumbered) ⇒
  renumber_code_locs_list n (p1 ++ p2) = (n2, p1_renumbered ++ p2_renumbered)
Proof
  Induct_on ‘p1’ >> rw[clos_numberTheory.renumber_code_locs_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 ‘renumber_code_locs n h = (n_h, h_renumbered)’ >>
  rename1 ‘renumber_code_locs_list n_h p1 = (n_p1, p1_renumbered)’ >>
  rename1 ‘renumber_code_locs_list n_h (p1 ++ p2) = (n_p1p2, p1p2_renumbered)’ >>
  last_x_assum drule_all >> gvs[]
QED



Theorem remove_fvs_cons:
  remove_fvs 0 (p :: ps) = remove_fvs 0 [p] ++ remove_fvs 0 ps
Proof
  Cases_on ‘ps’ >- (
  gvs[clos_fvsTheory.remove_fvs_def]
  ) >- (
  rw[clos_fvsTheory.remove_fvs_def] >>
  Cases_on ‘p’ >> rw[clos_fvsTheory.remove_fvs_def]
  )
QED

Theorem clos_fvs_compile_append:
  clos_fvs$compile (p1 ++ p2) = clos_fvs$compile p1 ++ clos_fvs$compile p2
Proof
  Induct_on ‘p1’ >> gvs[clos_fvsTheory.compile_def, clos_fvsTheory.remove_fvs_def] >>
  once_rewrite_tac[remove_fvs_cons] >> rw[]
QED

Theorem known_cons:
  known c (p :: ps) vs g =
  let (p_head,g) = known c [p] vs g in
  let (p_tail,g) = known c ps vs g in
    (p_head ++ p_tail,g)

Proof
  rw[] >> pairarg_tac >> gvs[] >>
  Cases_on ‘ps’ >> gvs[clos_knownTheory.known_def]
QED


Theorem known_append:
  ∀ p1 p2 vs g p1_known p2_known g1 g2.
  known c p1 vs g = (p1_known, g1) ∧
  known c p2 vs g1 = (p2_known, g2) ⇒
  known c (p1 ++ p2) vs g = (p1_known ++ p2_known, g2)
Proof
  Induct_on ‘p1’  >> rw[clos_knownTheory.known_def] >> gvs[] >>
  once_rewrite_tac[known_cons] >>
  rw[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum ‘ known c (h::p1) vs g = (p1_known,g1)’ $ mp_tac >>
  once_rewrite_tac[known_cons] >>
  rw[] >>
  rpt (pairarg_tac >> gvs[]) >>
  last_x_assum drule_all >>
  gvs[]
QED

Theorem clos_remove_ticks_cons:
   clos_ticks$remove_ticks (p :: ps) = clos_ticks$remove_ticks [p] ++ clos_ticks$remove_ticks ps
Proof
  Cases_on ‘ps’ >> rw[clos_ticksTheory.remove_ticks_def] >>
  rw[clos_ticksTheory.remove_ticks_sing_eq]
QED

Theorem clos_remove_ticks_append:
  clos_ticks$remove_ticks (p1 ++ p2) =
  clos_ticks$remove_ticks p1 ++ clos_ticks$remove_ticks p2
Proof
  Induct_on ‘p1’ >> rw[clos_ticksTheory.remove_ticks_def] >>

  rw[] >>
  once_rewrite_tac[clos_remove_ticks_cons] >>
  rw[clos_ticksTheory.remove_ticks_def]
QED

Theorem clos_let_op_cons:
  clos_letop$let_op (p :: ps) =
  clos_letop$let_op [p] ++ clos_letop$let_op ps
Proof
  Cases_on ‘ps’ >> rw[clos_letopTheory.let_op_def] >>
  rw[clos_letopTheory.let_op_sing_eq]
QED
Theorem clos_let_op_append:
  clos_letop$let_op (p1 ++ p2) =
  clos_letop$let_op p1 ++ clos_letop$let_op p2
Proof
  Induct_on ‘p1’ >> rw[clos_letopTheory.let_op_def] >>
  rw[] >>
  once_rewrite_tac[clos_let_op_cons] >>
  rw[]
QED


Theorem let_op_remove_ticks_append:
  clos_letop$let_op (remove_ticks (p1 ++ p2)) =
  clos_letop$let_op (remove_ticks p1) ++ clos_letop$let_op (remove_ticks p2)
Proof
  rw[clos_remove_ticks_append, clos_let_op_append]
QED

Theorem clos_call_calls_cons:
  clos_call$calls (p :: ps) g =
  let (p_head, g) = clos_call$calls [p] g in
  let (p_tail, g) = clos_call$calls ps g in
  (p_head ++ p_tail, g)
Proof
  Cases_on ‘ps’ >> rw[clos_callTheory.calls_def] >>
  pairarg_tac >> gvs[]
QED


Theorem clos_call_calls_cons_alt:
  clos_call$calls (p :: ps) (g, []) =
  let (p_head, g, acc_head) = clos_call$calls [p] (g, []) in
  let (p_tail, g, acc_tail) = clos_call$calls ps (g, []) in
  (p_head ++ p_tail, g, acc_tail ++ acc_head)
Proof
  Cases_on ‘ps’ >> gvs[] >> rpt (pairarg_tac >> gvs[])
  >- (gvs[clos_callTheory.calls_def])
  >- (gvs[clos_callTheory.calls_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      qspecl_then [‘(h::t)’, ‘g'’, ‘acc_head’] mp_tac calls_acc >>
      gvs[] >> strip_tac >> gvs[])

QED

Theorem clos_call_calls_append:
  ∀p1 p2 p1_calls p2_calls g g1 g2.
  clos_call$calls p1 g = (p1_calls, g1) ∧
  clos_call$calls p2 g1 = (p2_calls, g2) ⇒
  clos_call$calls (p1 ++ p2) g = (p1_calls ++ p2_calls, g2)

Proof
  Induct >> rw[clos_callTheory.calls_def] >> rpt (pairarg_tac >> gvs[]) >>
  once_rewrite_tac[clos_call_calls_cons] >>
  rw [] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum ‘calls (h :: p1) g = _’ $ mp_tac >>
  once_rewrite_tac[clos_call_calls_cons] >> rw[] >> pairarg_tac >> gvs[] >>
  last_x_assum drule_all >> gvs[]
QED

Theorem clos_annotate_compile_append:
  clos_annotate$compile (p1 ++ p2) = clos_annotate$compile p1 ++ clos_annotate$compile p2
Proof
  rw[clos_annotateTheory.compile_def]
QED


Theorem calls_acc:
   !xs d old res d1 aux.
     clos_call$calls xs (d, []) = (res, d1, aux) ==>
     clos_call$calls xs (d, old) = (res, d1, aux ++ old)
Proof
  cheat (* proved in clos_callProofScript *)
QED

Theorem clos_call_calls_append_alt:
  ∀p1 p2 p1_calls p2_calls g g1 g2 acc1 acc2.
  clos_call$calls p1 (g, []) = (p1_calls, g1, acc1) ∧
  clos_call$calls p2 (g1, []) = (p2_calls, g2, acc2) ⇒
  clos_call$calls (p1 ++ p2) (g, []) = (p1_calls ++ p2_calls, g2,  acc2 ++ acc1)
Proof
  Induct >> rw[clos_callTheory.calls_def] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum ‘calls (h :: p1) _ = _’ $ mp_tac >>once_rewrite_tac[clos_call_calls_cons_alt] >>
  rw [] >> rpt (pairarg_tac >> gvs[]) >>
  last_x_assum drule_all >> gvs[]
QED



Theorem icompile_icompile_clos_to_bvl:
  icompile_clos_to_bvl_common clos_iconf p1 = (clos_iconf_p1, p1_bvl) ∧
  icompile_clos_to_bvl_common clos_iconf_p1 p2 = (clos_iconf_p2, p2_bvl) ⇒
  icompile_clos_to_bvl_common clos_iconf (p1 ++ p2) = (clos_iconf_p2, p2_bvl ++ p1_bvl)

Proof
  rw[icompile_clos_to_bvl_common_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[clos_mti_compile_append] >>
  qabbrev_tac ‘clos_mti_compiled_p1 = compile clos_iconf.do_mti clos_iconf.max_app p1’ >> pop_assum kall_tac >>
  qabbrev_tac ‘clos_mti_compiled_p2 = compile clos_iconf.do_mti clos_iconf.max_app p2’ >> pop_assum kall_tac >>
  drule_all (GEN_ALL renumber_code_locs_lemma) >> gvs[] >> strip_tac >> gvs[] >>
  rename1 ‘ renumber_code_locs_list clos_iconf.next_loc
            (_ ++ _) = (n,p1_renamed ++ p2_renamed)’  >>
  rpt (qpat_x_assum ‘renumber_code_locs_list _ _ = _’ kall_tac) >>

  Cases_on ‘clos_iconf.known_conf’ >> gvs[]
  >- ( Cases_on ‘clos_iconf.do_call’ >> gvs[]
       >- (drule_all (GEN_ALL clos_call_calls_append_alt) >>
           gvs[] >> rpt (strip_tac) >> gvs[clos_annotate_compile_append])
       >- (rw[clos_annotateTheory.compile_def]))
  >- ( gvs[clos_fvs_compile_append] >>
       rpt (pairarg_tac >> gvs[]) >>
       drule_all known_append  >> gvs[] >> strip_tac >> gvs[] >>
       Cases_on ‘clos_iconf.do_call’ >> gvs[]
       >- ( gvs[let_op_remove_ticks_append] >>
            rev_drule_all (GEN_ALL clos_call_calls_append_alt) >>
            gvs[] >> rpt strip_tac >> gvs[] >>
            gvs[clos_annotate_compile_append])
       >- ( gvs[let_op_remove_ticks_append] >>
            rw[clos_annotateTheory.compile_def]))
QED


Theorem icompile_icompile_source_to_flat:
  icompile_source_to_flat source_iconf p1 = (source_iconf_p1, p1_flat) ∧
  icompile_source_to_flat source_iconf_p1 p2 = (source_iconf_p2, p2_flat) ⇒
  icompile_source_to_flat source_iconf (p1 ++ p2) = (source_iconf_p2, p1_flat ++ p2_flat)
Proof
  rw[icompile_source_to_flat_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flat_compile_decs_lemma, extend_env_assoc]

QED



(* Composing adjacent icompile runs *)
Theorem icompile_icompile:
  icompile source_iconf clos_iconf prog1 = (source_iconf', clos_iconf', prog1') ∧
  icompile source_iconf' clos_iconf' prog2 = (source_iconf'', clos_iconf'', prog2') ⇒
  icompile source_iconf clos_iconf (prog1 ++ prog2) = (source_iconf'', clos_iconf'',  prog1' ++ prog2')
Proof
  rw[] >>
  gvs[icompile_def] >> rpt (pairarg_tac >> gvs[]) >>
  (* yikes naming mistakes, note to self, DO NOT USE "'" *)
  rename1 ‘icompile_source_to_flat source_iconf (compile (prog1 ++ prog2)) = (source_iconf_p1_p2, p1_p2_flat)’ >>
  rename1 ‘ icompile_clos_to_bvl_compile_common clos_iconf (icompile_flat_to_clos p1_p2_flat) = (clos_iconf_p1_p2, p1_p2_bvl)’ >>
  rename1 ‘icompile_source_to_flat source_iconf (compile prog1) = (source_iconf_p1, p1_flat)’ >>
  rename1 ‘icompile_source_to_flat source_iconf_p1 (compile prog2) = (source_iconf_p2, p2_flat)’ >>
  rename1 ‘icompile_clos_to_bvl_compile_common clos_iconf (icompile_flat_to_clos p1_flat) = (clos_iconf_p1 , p1_bvl)’ >>
  rename1 ‘icompile_clos_to_bvl_compile_common clos_iconf_p1 (icompile_flat_to_clos p2_flat) = (clos_iconf_p2,p_2_bvl)’ >>

  fs[source_to_source_compile_append] >>

  qabbrev_tac ‘p1 = compile prog1’ >> pop_assum kall_tac >>
  qabbrev_tac ‘p2 = compile prog2’ >> pop_assum kall_tac >>

  drule_all icompile_icompile_source_to_flat >> strip_tac >> gvs[] >>

  fs[icompile_flat_to_clos_and_append_commute] >>

  qabbrev_tac ‘p1_clos = icompile_flat_to_clos p1_flat’ >> pop_assum kall_tac >>
  qabbrev_tac ‘p2_clos = icompile_flat_to_clos p2_flat’ >> pop_assum kall_tac >>

  drule_all icompile_icompile_clos_to_bvl >>
  gvs[]
QED

Definition config_prog_rel_def:
  config_prog_rel source_conf' progs' c' ps' ⇔
    source_conf' = c' ∧
    progs' = ps'
End



Theorem init_icompile_icompile_end_icompile:
  ∀prog.
  init_icompile (source_conf : source_to_flat$config) = (source_iconf : source_iconfig, stub_prog)
  ∧
  icompile source_iconf prog = (source_iconf', icompiled_prog)
  ∧
  end_icompile source_iconf' source_conf = source_conf'
  ∧
  compile_alt (c : 'a config) prog = (c', compiled_prog)
  ∧
  source_conf = c.source_conf
  ∧
  c.source_conf.mod_env = empty_env
  ⇒
  config_prog_rel source_conf' (stub_prog ++ icompiled_prog) c' compiled_prog
Proof
  rw[] >>
  fs [init_icompile_def, icompile_def, end_icompile_def, icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs [compile_alt_def,source_to_flat_compile_alt_def]>>
  rpt (pairarg_tac >> gvs[]) >>
  fs[source_to_flat_compile_prog_alt_def] >>
  rpt (pairarg_tac >> gvs[])  >>
  rw[extend_env_empty_env] >>
  rw[flat_to_clos_compile_alt_def, icompile_flat_to_clos_def, APPEND] >>
  rw[config_prog_rel_def] >>
  once_rewrite_tac[flat_to_clos_compile_decs_cons] >>
  assume_tac (GEN_ALL flat_to_clos_compile_decs_and_append_commute) >>
  (* i dont know how else to avoid this... *)
  first_x_assum $ qspecl_then [‘MAP (compile_dec c.source_conf.pattern_cfg) p'’, ‘[compile_dec c.source_conf.pattern_cfg alloc_env_ref]’] assume_tac >>
  gvs[]
QED


Theorem fold_icompile_collapse:
  ∀progs source_iconf.
  fold_icompile source_iconf progs =
  icompile source_iconf (FLAT (progs))
Proof
  Induct >> rw[fold_icompile_def] >- (
  rw[icompile_def, icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flatTheory.compile_decs_def,
      source_to_sourceTheory.compile_def,
      source_letTheory.compile_decs_def] >>
  rw[theorem "source_iconfig_component_equality", extend_env_empty_env] >>
  rw[icompile_flat_to_clos_def, flat_to_closTheory.compile_decs_def]
  )
  >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[icompile_icompile]
QED

Theorem icompile_eq:
  init_icompile (source_conf : source_to_flat$config) = (source_iconf : source_iconfig, stub_prog)
  ∧
  fold_icompile source_iconf progs = (source_iconf', icompiled_prog)
  ∧
  end_icompile source_iconf' source_conf = source_conf'
  ∧
  compile_alt (c : 'a config) (FLAT progs) = (c', compiled_prog)
  ∧
  source_conf = c.source_conf
  ∧
  c.source_conf.mod_env = empty_env
  ⇒
  config_prog_rel source_conf' (stub_prog ++ icompiled_prog) c' compiled_prog
Proof
  rw[] >>
  fs[fold_icompile_collapse] >>
  metis_tac[init_icompile_icompile_end_icompile]
QED


val _ = export_theory();
