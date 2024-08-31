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
     next_loc : num; |>
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
  let next_loc = clos_iconf.next_loc in
  let loc = if next_loc MOD 2 = 0 then next_loc else next_loc + 1 in
  let (n, p) = renumber_code_locs_list loc p in
  let clos_iconf = clos_iconf with <| next_loc := n |> in
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

Theorem renumber_code_locs_even_lemma:
  renumber_code_locs_list n p1 = (n1, p1_renumbered) ∧
  (n1 MOD 2 = 0) ∧
  renumber_code_locs_list n1 p2 = (n2, p2_renumbered) ⇒
  renumber_code_locs_list n (p1 ++ p2) = (n2, p1_renumbered ++p2_renumbered)
Proof
  cheat
QED

Theorem renumber_code_locs_odd_lemma:
  renumber_code_locs_list n p1 = (n1, p1_renumbered) ∧
  (n1 MOD 2 ≠ 0) ∧
  renumber_code_locs_list (n1 + 1) p2 = (n2, p2_renumbered) ⇒
  renumber_code_locs_list n (p1 ++ p2) = (n2, p1_renumbered ++p2_renumbered)
Proof
  cheat
QED


Theorem icompile_icompile_clos_to_bvl:
  icompile_clos_to_bvl_compile_common clos_iconf p1 = (clos_iconf_p1, p1_bvl) ∧
  icompile_clos_to_bvl_compile_common clos_iconf_p1 p2 = (clos_iconf_p2, p2_bvl) ⇒
  icompile_clos_to_bvl_compile_common clos_iconf (p1 ++ p2) = (clos_iconf_p2, p1_bvl ++ p2_bvl)

Proof
  rw[icompile_clos_to_bvl_compile_common_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[clos_mti_compile_append] >>
  qabbrev_tac ‘p1_compiled_mti = (compile clos_iconf.do_mti clos_iconf.max_app p1)’ >>
  qabbrev_tac ‘p2_compiled_mti = (compile clos_iconf.do_mti clos_iconf.max_app p2)’ >>
  pop_assum kall_tac >> pop_assum kall_tac >>

  qabbrev_tac ‘n1 = n''’ >> pop_assum kall_tac >>
  qabbrev_tac ‘n2 = n'’ >> pop_assum kall_tac
  >- (drule_all renumber_code_locs_even_lemma >> gvs[])
  >- (drule_all renumber_code_locs_odd_lemma >> gvs[])
  >- (drule_all renumber_code_locs_even_lemma >> gvs[])
  >- (drule_all renumber_code_locs_odd_lemma >> gvs[])
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
