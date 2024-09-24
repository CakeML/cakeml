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

Definition clos_to_bvl_compile_alt_def:
  clos_to_bvl_compile_alt clos_conf p =
  let (c, p, _) = clos_to_bvl$compile clos_conf p in
    (c, p)
End



(* TODO: extend this step-by-step *)
Definition compile_alt_def:
  compile_alt c p =
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat_compile_alt c.source_conf p in
    let c = c with source_conf := c' in
    let p = flat_to_clos_compile_alt p in
    let (c',p, names) = clos_to_bvl$compile c.clos_conf p in
    let c = c with clos_conf := c' in
    (c, p) (* to add names later *)
End


Definition compile_alt1_def:
  compile_alt1 source_conf clos_conf p =
 (* skip source to source for now *)
  let (source_conf', compiled_p_flat) = source_to_flat_compile_alt source_conf p in
  let compiled_p_clos = flat_to_clos_compile_alt compiled_p_flat in
  let (clos_conf', compiled_p_bvl) = clos_to_bvl_compile_alt clos_conf compiled_p_clos in
    (source_conf', clos_conf', compiled_p_bvl)
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
     es_to_chain : closLang$exp list;
     length_acc : num;
  |>
End

Datatype:
  clos_iconfig1 =
  <| max_app: num;
     new_bvl_exps: (num # num # bvl$exp) list;
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

  let (p, (clos_call_g, aux)) = (case clos_iconf.do_call of
                           | F => (p, (LN, []))
                           | T => clos_call$calls p (clos_iconf.clos_call_g,[])) in
  let clos_iconf = clos_iconf with length_acc := clos_iconf.length_acc + LENGTH p in
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

Definition icompile_clos_to_bvl_prog_def:
  icompile_clos_to_bvl_prog (clos_iconf1: clos_iconfig1) p =
  let prog = MAP (SND o SND) p in
  let (new_exps, aux) = clos_to_bvl$compile_exps clos_iconf1.max_app prog [] in
  let new_bvl_exps = MAP2 (λ(loc,args,_) exp. (loc + num_stubs clos_iconf1.max_app, args, exp)) p new_exps in
  let clos_iconf1 = clos_iconf1 with <| new_bvl_exps := new_bvl_exps ++ clos_iconf1.new_bvl_exps; |> in
    (clos_iconf1, aux)
End

Definition icompile_clos_to_bvl_def:
  icompile_clos_to_bvl (clos_iconf: clos_iconfig) (clos_iconf1 : clos_iconfig1) p =
  let (clos_iconf, p) = icompile_clos_to_bvl_common clos_iconf p in
  let (clos_iconf1, p) = icompile_clos_to_bvl_prog clos_iconf1 p in
    (clos_iconf, clos_iconf1, p)
End

Definition init_icompile_source_to_flat_def:
  init_icompile_source_to_flat source_conf =
  let next = source_conf.next with <| vidx := source_conf.next.vidx + 1 |> in
  let env_gens = <| next := 0; generation := source_conf.envs.next; envs := LN |> in
  let source_iconf = <| n := 1n;
                        next := next;
                        env := source_conf.mod_env;
                        env_gens := env_gens;
                        pattern_cfg := source_conf.pattern_cfg |> in
  let flat_stub = flat_pattern$compile_dec source_conf.pattern_cfg source_to_flat$alloc_env_ref in
  (source_iconf, [flat_stub])

End

Definition end_icompile_source_to_flat_def:
  end_icompile_source_to_flat (source_iconf: source_iconfig) (source_conf: source_to_flat$config) =
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

Definition init_icompile_flat_to_clos_def:
  init_icompile_flat_to_clos flat_stub =
  let clos_stub = (clos_interp$compile_init T) :: (flat_to_clos$compile_decs flat_stub) in
  clos_stub
End

Definition end_icompile_flat_to_clos_def:
  end_icompile_flat_to_clos = ()
End

Definition init_icompile_clos_to_bvl_def:
  init_icompile_clos_to_bvl (clos_conf:clos_to_bvl$config) clos_stub =
  let clos_iconf = <| do_mti := clos_conf.do_mti;
                      max_app := clos_conf.max_app;
                      next_loc := 0;
                      known_conf:= clos_conf.known_conf;
                      known_g := LN;
                      do_call := clos_conf.do_call;
                      clos_call_aux := [];
                      clos_call_g := LN;
                      es_to_chain := [];
                      length_acc := 0 |> in
  let clos_iconf1 = <| max_app := clos_conf.max_app;
                       new_bvl_exps := [] |> in

  let (clos_iconf, clos_iconf1, bvl_stub) = icompile_clos_to_bvl clos_iconf clos_iconf1 clos_stub in
    (clos_iconf, clos_iconf1, bvl_stub)
End


Definition end_icompile_clos_to_bvl_def:
  end_icompile_clos_to_bvl clos_iconf clos_iconf1 clos_conf p bvl_stub =

  let es_chained = clos_to_bvl$chain_exps clos_iconf.next_loc
                                          clos_iconf.es_to_chain in
  let es_chained = clos_annotate$compile es_chained in
  let (new_exps, aux) = clos_to_bvl$compile_exps clos_iconf.max_app (MAP (SND o SND) es_chained) [] in
  let prelude_p = MAP2 (λ(loc,args,_) exp. (loc + clos_to_bvl$num_stubs clos_conf.max_app, args, exp)) es_chained new_exps in
  let clos_conf = clos_conf with (* to add in more later *)
                            <| next_loc :=
                               clos_iconf.next_loc + MAX 1 (clos_iconf.length_acc); (* need to add the length of the es *)
                               start := num_stubs clos_iconf.max_app - 1;
                               known_conf := OPTION_MAP (\kc. kc with val_approx_spt := clos_iconf.known_g) clos_iconf.known_conf;
                               call_state := (clos_iconf.clos_call_g, clos_iconf.clos_call_aux) |> in
  let c = clos_iconf in
  let init_stubs = toAList (init_code c.max_app) in
  let init_globs = [(num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.next_loc))] in
  let icompiled_p_finalised = prelude_p ++ clos_iconf1.new_bvl_exps ++ bvl_stub ++ p ++ aux in
    (clos_conf, init_stubs ++ init_globs ++ icompiled_p_finalised)
End



Definition init_icompile_def:
  init_icompile source_conf clos_conf=
  let (source_iconf, flat_stub) = init_icompile_source_to_flat source_conf in
  let clos_stub = init_icompile_flat_to_clos flat_stub in
  let (clos_iconf, clos_iconf1, bvl_stub) = init_icompile_clos_to_bvl clos_conf clos_stub in
  (source_iconf, clos_iconf, clos_iconf1, bvl_stub)
End



Definition end_icompile_def:
  end_icompile source_iconf source_conf
                   clos_iconf clos_iconf1 clos_conf p bvl_stub =
  let source_conf_after_ic = end_icompile_source_to_flat source_iconf source_conf in
  let (clos_conf_after_ic, icompiled_p_finalised) = end_icompile_clos_to_bvl clos_iconf clos_iconf1 clos_conf p bvl_stub in
    (source_conf_after_ic, clos_conf_after_ic, icompiled_p_finalised)

End


Definition icompile_def:
  icompile source_iconf clos_iconf clos_iconf1 p =
  let (source_iconf', icompiled_p_flat) = icompile_source_to_flat source_iconf p in
  let icompiled_p_clos = icompile_flat_to_clos icompiled_p_flat in
  let (clos_iconf', clos_iconf1', icompiled_p_bvl) = icompile_clos_to_bvl clos_iconf clos_iconf1 icompiled_p_clos in
      (source_iconf', clos_iconf', clos_iconf1', icompiled_p_bvl)
End



Definition fold_icompile_def:
  fold_icompile source_iconf clos_iconf clos_iconf1 []  = icompile source_iconf clos_iconf clos_iconf1 []
  /\
  fold_icompile source_iconf clos_iconf clos_iconf1 (p :: ps)  =
  let (source_iconf', clos_iconf', clos_iconf1', p') = icompile source_iconf clos_iconf clos_iconf1 p in
  let (source_iconf'', clos_iconf'', clos_iconf1'', ps') = fold_icompile source_iconf' clos_iconf' clos_iconf1' ps in
    (source_iconf'', clos_iconf'', clos_iconf1'', p' ++ ps')

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

Theorem icompile_icompile_source_to_flat:
  icompile_source_to_flat source_iconf p1 = (source_iconf_p1, p1_flat) ∧
  icompile_source_to_flat source_iconf_p1 p2 = (source_iconf_p2, p2_flat) ⇒
  icompile_source_to_flat source_iconf (p1 ++ p2) = (source_iconf_p2, p1_flat ++ p2_flat)
Proof
  rw[icompile_source_to_flat_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flat_compile_decs_lemma, extend_env_assoc]

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
      qspecl_then [‘(h::t)’, ‘g'’, ‘acc_head’] mp_tac clos_callTheory.calls_acc >>
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



(* Super ugly, to fix, also how to do a drule for this *)
Theorem clos_to_bvl_compile_exps_append :
  ∀ p1 p2 p1' aux_p1 p2' aux_p2.
  compile_exps max_app p1 [] = (p1', aux_p1) ∧
  compile_exps max_app p2 [] = (p2', aux_p2) ⇒
  compile_exps max_app (p2 ++ p1) [] = (p2' ++ p1', aux_p1 ++ aux_p2)
Proof
  Induct_on ‘p2’
  >- (gvs[clos_to_bvlTheory.compile_exps_def])
  >- (once_rewrite_tac[clos_to_bvlTheory.compile_exps_CONS] >>
      rw[] >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum mp_tac >>
      once_rewrite_tac[clos_to_bvlTheory.compile_exps_eq_append] >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum mp_tac >>
      once_rewrite_tac[clos_to_bvlTheory.compile_exps_CONS] >> rw[] >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum mp_tac >>
      once_rewrite_tac[clos_to_bvlTheory.compile_exps_eq_append] >>
      rpt (pairarg_tac >> gvs[]) >>
      rw[] >>
      last_x_assum rev_drule >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum mp_tac >>
      once_rewrite_tac[clos_to_bvlTheory.compile_exps_eq_append] >>
      rpt (pairarg_tac >> gvs[]) >>
      last_x_assum rev_drule >> gvs[])
QED




Theorem icompile_icompile_clos_to_bvl_common:
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


Theorem icompile_icompile_clos_to_bvl_prog:
  icompile_clos_to_bvl_prog clos_iconf p1 = (clos_iconf_p1, p1_bvl) ∧
  icompile_clos_to_bvl_prog clos_iconf_p1 p2 = (clos_iconf_p2, p2_bvl) ⇒
  icompile_clos_to_bvl_prog clos_iconf (p2 ++ p1) = (clos_iconf_p2, p1_bvl ++ p2_bvl)
Proof
  rw[icompile_clos_to_bvl_prog_def] >> rpt (pairarg_tac >> gvs[]) >>
  qabbrev_tac ‘p1' = (MAP (SND ∘ SND) p1)’ >>
  qabbrev_tac ‘p2' = (MAP (SND ∘ SND) p2)’ >>
  rename1 ‘compile_exps _ p1' _ = (new_exps_p1, aux_p1)’ >>
  rename1 ‘compile_exps _ p2' _ = (new_exps_p2, aux_p2)’ >>
  qspecl_then [‘clos_iconf.max_app’, ‘p1'’, ‘p2'’, ‘new_exps_p1’, ‘aux_p1’, ‘new_exps_p2’, ‘aux_p2’] mp_tac (GEN_ALL clos_to_bvl_compile_exps_append) >>
  rw[] >> gvs[] >>
  (* how to handle this more elegantly, is it betteer to do qspec or play around with the stack *)
  qspecl_then [‘p1’, ‘(SND ∘ SND)’] assume_tac LENGTH_MAP >>
  qspecl_then [‘p2’, ‘(SND ∘ SND)’] assume_tac LENGTH_MAP >>

  drule clos_to_bvlTheory.compile_exps_LENGTH >>
  (* how to change thee order of the quantifieers *)
  (* qspecl_then [‘p2'’, ‘new_exps_p1’] mp_tac (GEN_ALL clos_to_bvlTheory.compile_exps_LENGTH) *)
  last_x_assum assume_tac >>
  rev_drule clos_to_bvlTheory.compile_exps_LENGTH >>
  rw[theorem "clos_iconfig1_component_equality"] >>
  qmatch_goalsub_rename_tac `MAP2 f _ _ = _` >>
  qspecl_then [‘p2’, ‘p1’, ‘new_exps_p2’,‘new_exps_p1’, ‘f’] mp_tac MAP2_APPEND >> rw[] >>
  fs[Abbr ‘p2'’]

QED



Theorem icompile_icompile_clos_to_bvl:
  icompile_clos_to_bvl clos_iconf clos_iconf1 p1 = (clos_iconf_p1, clos_iconf1_p1, p1_bvl) ∧
  icompile_clos_to_bvl clos_iconf_p1 clos_iconf1_p1 p2 = (clos_iconf_p2, clos_iconf1_p2, p2_bvl) ⇒
  icompile_clos_to_bvl clos_iconf clos_iconf1 (p1 ++ p2) = (clos_iconf_p2, clos_iconf1_p2, p1_bvl ++ p2_bvl)
Proof
  rw[icompile_clos_to_bvl_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 ‘icompile_clos_to_bvl_common clos_iconf (p1 ++ p2) = (clos_iconf_p1_p2, p2_p1_clos_common)’ >>
  rename1 ‘icompile_clos_to_bvl_prog clos_iconf1 p2_p1_clos_common = (clos_iconf1_p2p1, p1_p2_bvl)’ >>
  rename1 ‘icompile_clos_to_bvl_common clos_iconf p1 = (clos_iconf_p1, p1_clos_common)’ >>
  rename1 ‘icompile_clos_to_bvl_prog clos_iconf1 p1_clos_common = (clos_iconf1_p1, p1_bvl)’ >>
  rename1 ‘icompile_clos_to_bvl_common clos_iconf_p1 p2 = (clos_iconf_p2, p2_clos_common)’ >>
  rename1 ‘ icompile_clos_to_bvl_prog clos_iconf1_p1 p2_clos_common = (clos_iconf1_p2, p2_bvl)’ >>


  drule_all icompile_icompile_clos_to_bvl_common >> gvs[] >>
  ntac 3 (qpat_x_assum ‘icompile_clos_to_bvl_prog _ _ = _’ mp_tac) >> ntac 3 (strip_tac) >>
  strip_tac >> gvs[] >>

  drule_all icompile_icompile_clos_to_bvl_prog >>
  strip_tac >> gvs[] >>
  rev_drule_all icompile_icompile_clos_to_bvl_prog >>
  strip_tac >> gvs[]
QED



(* Composing adjacent icompile runs *)
Theorem icompile_icompile:
  icompile source_iconf clos_iconf clos_iconf1 prog1 = (source_iconf', clos_iconf', clos_iconf1', prog1') ∧
  icompile source_iconf' clos_iconf' clos_iconf1' prog2 = (source_iconf'', clos_iconf'', clos_iconf1'', prog2') ⇒
  icompile source_iconf clos_iconf clos_iconf1 (prog1 ++ prog2) = (source_iconf'', clos_iconf'',  clos_iconf1'', prog1' ++ prog2')
Proof
  rw[] >>
  gvs[icompile_def] >> rpt (pairarg_tac >> gvs[]) >>

  ntac 3 (qpat_x_assum ‘icompile_source_to_flat _ _ = _’ mp_tac) >> ntac 3 (strip_tac) >>
  drule_all icompile_icompile_source_to_flat >> strip_tac >> gvs[] >>
  rename1 ‘icompile_source_to_flat _ prog1 = (source_iconf_p1, p1_flat)’ >>
  rename1 ‘icompile_source_to_flat _ prog2 = (source_iconf_p2, p2_flat)’ >>


  ntac 3 (qpat_x_assum ‘icompile_clos_to_bvl _ _ _ = _’ mp_tac) >> ntac 3 (strip_tac) >>
  fs[icompile_flat_to_clos_and_append_commute] >>
  qabbrev_tac ‘p1_clos = icompile_flat_to_clos p1_flat’ >> pop_assum kall_tac >>
  qabbrev_tac ‘p2_clos = icompile_flat_to_clos p2_flat’ >> pop_assum kall_tac >>
  rev_drule_all icompile_icompile_clos_to_bvl >>
  strip_tac >> gvs[]
QED


Definition config_prog_rel_def:
  config_prog_rel source_conf' clos_conf' cat_prog c' compiled_prog ⇔
    source_conf' = c'.source_conf ∧
    clos_conf' = c'.clos_conf ∧
    cat_prog = compiled_prog
End

Definition init_config_rel_def:
  init_config_rel (c: 'a config) source_conf clos_conf =
  (c.source_conf = source_conf ∧
  c.clos_conf = clos_conf ∧
  source_conf = source_to_flat$empty_config ∧
  clos_conf = clos_to_bvl$default_config)
End

Definition init_config_rel_s2f_def:
  init_config_rel c source_conf =
  (c.source_conf = source_conf
  ∧
  source_conf = source_to_flat$empty_config)
End


Definition config_prog_rel_s2b_def:
  config_prog_rel_s2b source_conf_after_ic clos_conf_after_ic icompiled_p
                      source_conf_after_c clos_conf_after_c compiled_p ⇔
    source_conf_after_ic = source_conf_after_c ∧
    clos_conf_after_ic = clos_conf_after_c ∧
    icompiled_p = compiled_p

End

Definition config_prog_pair_rel_def:
  config_prog_pair_rel c1 p1 c2 p2 ⇔
    c1 = c2 ∧ p1 = p2
End



Definition config_prog_rel_alt_def:
  config_prog_rel_alt source_conf_after_ic icompiled_p_finalised source_conf_after_c compiled_p ⇔
    source_conf_after_ic = source_conf_after_c
    ∧
    icompiled_p_finalised = compiled_p
End



Theorem init_icompile_icompile_end_icompile_s2f:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub)
  ∧
  icompile_source_to_flat source_iconf p = (source_iconf', icompiled_p)
  ∧
  end_icompile_source_to_flat source_iconf' source_conf = source_conf_after_ic
  ∧
  source_to_flat_compile_alt source_conf p = (source_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ⇒
  config_prog_pair_rel source_conf_after_ic (flat_stub ++ icompiled_p)
                      source_conf_after_c compiled_p
Proof
  rw[] >>
  fs[init_icompile_source_to_flat_def,
     icompile_source_to_flat_def,
     source_to_flat_compile_alt_def,
     source_to_flat_compile_prog_alt_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[source_to_flatTheory.empty_config_def] >>
  rw[end_icompile_source_to_flat_def] >>
  rw[extend_env_empty_env] >>
  gvs[source_to_flatTheory.compile_decs_def] >>
  rw[config_prog_pair_rel_def]
QED

Theorem init_icompile_icompile_end_icompile_f2c:
  (init_icompile_flat_to_clos flat_stub = clos_stub)
  ∧
  (icompile_flat_to_clos flat_p = icompiled_p)
  ∧
  (flat_to_clos_compile_alt (flat_stub ++ flat_p) = compiled_p)
  ⇒
  clos_stub ++ icompiled_p = compiled_p
Proof
  rw[init_icompile_flat_to_clos_def,
     icompile_flat_to_clos_def,
     flat_to_clos_compile_alt_def] >>
  once_rewrite_tac[flat_to_clos_compile_decs_cons] >>
  qspecl_then [‘flat_p’, ‘flat_stub’] mp_tac (GEN_ALL flat_to_clos_compile_decs_and_append_commute) >>
  rw[]
QED

Theorem init_icompile_icompile_end_icompile_c2b:
  init_icompile_clos_to_bvl clos_conf clos_stub = (clos_iconf, clos_iconf1, bvl_stub)
  ∧
  icompile_clos_to_bvl clos_iconf clos_iconf1 p = (clos_iconf', clos_iconf1', icompiled_p)
  ∧
  end_icompile_clos_to_bvl clos_iconf' clos_iconf1' clos_conf (icompiled_p) bvl_stub =
  (clos_conf_after_ic, icompiled_p_finalised)
  ∧
  clos_to_bvl_compile_alt clos_conf (clos_stub ++ p) =
  (clos_conf_after_c, compiled_p)
  ∧
  clos_conf = clos_to_bvl$default_config
  ⇒
  config_prog_pair_rel clos_conf_after_ic (icompiled_p_finalised)
                       clos_conf_after_c compiled_p
Proof
  rw[clos_to_bvlTheory.default_config_def,
     init_icompile_clos_to_bvl_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rev_drule_all icompile_icompile_clos_to_bvl >> gvs[] >>
  rw[] >>
  last_x_assum kall_tac >>
  pop_assum mp_tac >>
  pop_assum kall_tac >>
  strip_tac >>
  fs[clos_to_bvl_compile_alt_def,
     clos_to_bvlTheory.compile_def,
     clos_to_bvlTheory.compile_common_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[icompile_clos_to_bvl_def, icompile_clos_to_bvl_common_def] >> rpt (pairarg_tac >> gvs[]) >>
  fs[clos_knownTheory.compile_def, clos_callTheory.compile_def] >>
  pairarg_tac >> gvs[] >>
  gvs[end_icompile_clos_to_bvl_def] >>
  pairarg_tac >> gvs[] >>
  gvs[icompile_clos_to_bvl_prog_def] >>
  pairarg_tac >> gvs[] >>
  rw[clos_annotate_compile_append] >>
  rw[clos_to_bvlTheory.compile_prog_def] >>
  fs[end_icompile_clos_to_bvl_def] >>
  rpt (pairarg_tac >> gvs[] ) >>
  pop_assum mp_tac >>
  drule clos_to_bvl_compile_exps_append >>
  strip_tac >>
  pop_assum rev_drule >>
  rw[] >> gvs[] >>
  rw[config_prog_pair_rel_def] >>
  qmatch_goalsub_rename_tac ‘MAP2 f _ _ ++ MAP2 f _ _ = _’ >>
  rev_drule clos_to_bvlTheory.compile_exps_LENGTH >>
  strip_tac >>
  pop_assum (fn t => assume_tac (GSYM t)) >>
  fs[LENGTH_MAP] >>
  drule (INST_TYPE [gamma|->“:(num#num#bvl$exp)”] MAP2_APPEND) >>
  strip_tac >>
  pop_assum $ qspecl_then [‘clos_annotate$compile aux’, ‘new_exps'’, ‘f’] mp_tac >>
  strip_tac >> rw[]


QED



Theorem init_icompile_icompile_end_icompile_s2b:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub)
  ∧
  init_icompile_flat_to_clos flat_stub = clos_stub
  ∧
  init_icompile_clos_to_bvl clos_conf clos_stub = (clos_iconf, clos_iconf1, bvl_stub)
  ∧
  icompile_source_to_flat source_iconf p = (source_iconf', icompiled_p_flat)
  ∧
  icompile_flat_to_clos icompiled_p_flat = icompiled_p_clos
  ∧
  icompile_clos_to_bvl clos_iconf clos_iconf1 icompiled_p_clos = (clos_iconf', clos_iconf1', icompiled_p_bvl)
  ∧
  end_icompile_source_to_flat source_iconf' source_conf = source_conf_after_ic
  ∧
  end_icompile_clos_to_bvl clos_iconf' clos_iconf1' clos_conf icompiled_p_bvl bvl_stub = (clos_conf_after_ic, icompiled_p_bvl_finalised)
  ∧
  source_to_flat_compile_alt source_conf p = (source_conf_after_c, compiled_p_flat)
  ∧
  flat_to_clos_compile_alt compiled_p_flat = compiled_p_clos
  ∧
  clos_to_bvl_compile_alt clos_conf compiled_p_clos = (clos_conf_after_c, compiled_p_bvl)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ⇒
  config_prog_rel_s2b source_conf_after_ic clos_conf_after_ic (icompiled_p_bvl_finalised)
                      source_conf_after_c clos_conf_after_c compiled_p_bvl
Proof
  strip_tac >>
  drule_all init_icompile_icompile_end_icompile_s2f >>
  simp[config_prog_pair_rel_def] >>
  strip_tac >> pop_assum (fn f => assume_tac (GSYM f)) >>
  qpat_x_assum ‘flat_to_clos_compile_alt _ = _’ mp_tac >>
  simp[] >> strip_tac  >>
  drule_all init_icompile_icompile_end_icompile_f2c >>
  strip_tac >>
  pop_assum (fn f => assume_tac (GSYM f)) >>
  qpat_x_assum ‘clos_conf = _ ’ mp_tac >>
  qpat_x_assum ‘clos_to_bvl_compile_alt _ _ = _ ’ mp_tac >> simp[] >>
  rpt strip_tac >>
  drule_all init_icompile_icompile_end_icompile_c2b >>
  rw[config_prog_pair_rel_def] >>
  rw[config_prog_rel_s2b_def]
QED


Theorem init_icompile_icompile_end_icompile_f2c_alt:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub) ⇒
  flat_to_clos_compile_alt (flat_stub ++ icompiled_p_flat) =
  init_icompile_flat_to_clos flat_stub ++ icompile_flat_to_clos icompiled_p_flat
Proof
  metis_tac[init_icompile_icompile_end_icompile_f2c]
QED



Theorem init_icompile_icompile_end_icompile:
  init_icompile source_conf clos_conf = (source_iconf, clos_iconf, clos_iconf1, stub_p)
  ∧
  icompile source_iconf clos_iconf clos_iconf1 p = (source_iconf', clos_iconf', clos_iconf1', icompiled_p)
  ∧
  end_icompile source_iconf' source_conf
                   clos_iconf' clos_iconf1' clos_conf icompiled_p stub_p
                   = (source_conf_after_ic, clos_conf_after_ic, icompiled_p_finalised)
  ∧
  compile_alt1 source_conf clos_conf p = (source_conf_after_c, clos_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ⇒
  config_prog_rel_s2b source_conf_after_ic clos_conf_after_ic (icompiled_p_finalised)
                      source_conf_after_c clos_conf_after_c compiled_p
Proof
  once_rewrite_tac[init_icompile_def, icompile_def, end_icompile_def, compile_alt1_def] >>
  simp[] >>
  strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  rpt (pairarg_tac >> fs[]) >>
  qpat_x_assum ‘end_icompile_source_to_flat _ _ = _’ mp_tac >>
  gvs[] >> rpt strip_tac >>
  drule_all init_icompile_icompile_end_icompile_s2f >>
  simp[config_prog_pair_rel_def] >>
  strip_tac >>
  pop_assum (fn f => assume_tac (GSYM f)) >>
  qpat_x_assum ‘clos_conf = _ ’ mp_tac >>
  qpat_x_assum ‘clos_to_bvl_compile_alt _ _ = _ ’ mp_tac >> simp[] >>
  strip_tac >>
  drule_all init_icompile_icompile_end_icompile_f2c_alt >>
  strip_tac >> pop_assum $ qspec_then ‘icompiled_p_flat’ assume_tac >>
  gvs[] >>
  strip_tac >>
  drule_all init_icompile_icompile_end_icompile_c2b >>
  rw[config_prog_pair_rel_def] >>
  rw[config_prog_rel_s2b_def]
QED

Theorem fold_icompile_collapse:
  ∀pss source_iconf clos_iconf clos_iconf1.
  fold_icompile source_iconf clos_iconf clos_iconf1 pss =
  icompile source_iconf clos_iconf clos_iconf1 (FLAT (pss))
Proof
  Induct >> rw[fold_icompile_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[icompile_icompile]
QED


Theorem icompile_eq:
  init_icompile source_conf clos_conf = (source_iconf, clos_iconf, clos_iconf1, stub_p)
  ∧
  fold_icompile source_iconf clos_iconf clos_iconf1 pss = (source_iconf', clos_iconf', clos_iconf1', icompiled_p)
  ∧
  end_icompile source_iconf' source_conf
                   clos_iconf' clos_iconf1' clos_conf icompiled_p stub_p
                   = (source_conf_after_ic, clos_conf_after_ic, icompiled_p_finalised)
  ∧
  compile_alt1 source_conf clos_conf (FLAT pss) = (source_conf_after_c, clos_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ⇒
  config_prog_rel_s2b source_conf_after_ic clos_conf_after_ic (icompiled_p_finalised)
                      source_conf_after_c clos_conf_after_c compiled_p
Proof
  rw[] >>
  fs[fold_icompile_collapse] >>
  metis_tac[init_icompile_icompile_end_icompile]
QED



val _ = export_theory();
