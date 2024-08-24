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
Datatype:
  source_iconfig =
  <| n : num ;
     next : next_indices;
     env : environment;
     env_gens : environment_generation_store;
     pattern_cfg : flat_pattern$config
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

Definition init_icompile_def:
  init_icompile (source_conf : source_to_flat$config) =
  let next = source_conf.next with <| vidx := source_conf.next.vidx + 1 |> in
  let env_gens = <| next := 0; generation := source_conf.envs.next; envs := LN |> in
  let source_to_flat_stub = flat_pattern$compile_dec source_conf.pattern_cfg source_to_flat$alloc_env_ref in
    (<| n := 1n;
       next := next;
       env := source_conf.mod_env;
       env_gens := env_gens;
       pattern_cfg := source_conf.pattern_cfg |> : source_iconfig,
     [source_to_flat_stub])

End

Definition icompile_def:
  icompile (source_iconf : source_iconfig)  p =
  let p = source_to_source$compile p in
  icompile_source_to_flat source_iconf p
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
(* Syntactic correctness or icompile                                         *)
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
  rw[] >> rpt (pairarg_tac >> gvs[])  >> gvs[extend_env_assoc]
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



(* Composing adjacent icompile runs *)
Theorem icompile_icompile:
  icompile source_iconf prog1 = (source_iconf', prog1') ∧
  icompile source_iconf' prog2 = (source_iconf'', prog2') ⇒
  icompile source_iconf (prog1 ++ prog2) = (source_iconf'', prog1' ++ prog2')
Proof
  rw[icompile_def, icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_source_compile_append, source_to_flat_compile_decs_lemma, extend_env_assoc]
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
  pairarg_tac >> gvs[] >>
  fs [compile_alt_def,source_to_flat_compile_alt_def]>>
  rpt (pairarg_tac >> gvs[]) >>
  fs[source_to_flat_compile_prog_alt_def] >>
  rpt (pairarg_tac >> gvs[])  >>
  rw[extend_env_empty_env] >>
  rw[config_prog_rel_def]
QED


Theorem fold_icompile_collapse:
  ∀progs source_iconf.
  fold_icompile source_iconf progs =
  icompile source_iconf (FLAT (progs))
Proof
  Induct >> rw[fold_icompile_def] >- (
  rw[icompile_def, icompile_source_to_flat_def] >>
  pairarg_tac >> gvs[] >>
  gvs[source_to_flatTheory.compile_decs_def,
      source_to_sourceTheory.compile_def,
      source_letTheory.compile_decs_def] >>
  rw[theorem "source_iconfig_component_equality", extend_env_empty_env] )
  >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[icompile_icompile]
QED

Theorem icompile_eq:
  init_icompile (source_conf : source_to_flat$config) = (source_iconf : source_iconfig, stub_prog : dec list)
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
