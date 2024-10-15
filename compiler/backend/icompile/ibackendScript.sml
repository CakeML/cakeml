(*
  Defines a new incremental backend which is
  meant to be syntactically equal to backend but allows
  compiling program in a part-by-part manner
*)

open preamble backendTheory namespacePropsTheory;

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

(* we always insert the clos_interpreter code, this should be put into config *)
Definition flat_to_clos_compile_alt_def:
  flat_to_clos_compile_alt p =
  (clos_interp$compile_init T) :: flat_to_clos$compile_decs p
End

(* change the order of chain_exps *)
Definition clos_to_bvl_compile_common_alt_def:
  clos_to_bvl_compile_common_alt c es =
    let es = clos_mti$compile c.do_mti c.max_app es in
    let loc = c.next_loc in
    (* Alignment padding *)
    let loc = if loc MOD 2 = 0 then loc else loc + 1 in
    let (n,es) = renumber_code_locs_list loc es in
    let (kc, es) = clos_known$compile c.known_conf es in
    let (es,g,aux) = clos_call$compile c.do_call es in
    let aux = REVERSE aux in
    let prog = aux ++ (chain_exps n es) in
    let prog = clos_annotate$compile prog in
      (c with <| start := n; next_loc := n + MAX 1 (LENGTH es); known_conf := kc;
                 call_state := (g,aux) |>,
       prog)
End


(* TODO: just to remove the names field, probably just use
  original instead *)
Definition clos_to_bvl_compile_alt_def:
  clos_to_bvl_compile_alt c0 es =
    let (c, prog) = clos_to_bvl_compile_common_alt c0 es in
    let init_stubs = toAList (init_code c.max_app) in
    let init_globs = [(num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.start))] in
    let comp_progs = clos_to_bvl$compile_prog c.max_app prog in
    let prog' = init_stubs ++ comp_progs ++ init_globs in
    let c = c with start := num_stubs c.max_app - 1 in
      (c, prog')
End

Definition bvi_stubs_without_init_globs_def:
  bvi_stubs_without_init_globs =
  [(AllocGlobal_location, AllocGlobal_code);
   (CopyGlobals_location, CopyGlobals_code);
   (ListLength_location, ListLength_code);
   (FromListByte_location, FromListByte_code);
   (ToListByte_location, ToListByte_code);
   (SumListLength_location, SumListLength_code);
   (ConcatByte_location, ConcatByte_code)]
End


Definition bvl_to_bvi_compile_prog_alt_def:
  bvl_to_bvi_compile_prog_alt start n prog =
    let k = alloc_glob_count (MAP (\(_,_,p). p) prog) in
    let (code,n1) = bvl_to_bvi$compile_list n prog in
    let init_globs_start = backend_common$bvl_num_stubs + bvl_to_bvi_namespaces * start in
    let init_globs_stub = [(InitGlobals_location, InitGlobals_code init_globs_start k)] in
      (InitGlobals_location, bvi_stubs_without_init_globs ++ append code ++ init_globs_stub, n1)
End

(* change the order of the stubs *)
Definition bvl_to_bvi_compile_alt_def:
  bvl_to_bvi_compile_alt start (c: bvl_to_bvi$config) names prog =
    let (inlines, prog) = bvl_inline$compile_prog c.inline_size_limit
           c.split_main_at_seq c.exp_cut prog in
    let (loc, code, n1) = bvl_to_bvi_compile_prog_alt start 0 prog in
    let (n2, code') = bvi_tailrec$compile_prog (backend_common$bvl_num_stubs + 2) code in
      (loc, code', inlines, n1, n2, get_names (MAP FST code') names)
End

(* collate all the things *)
Definition bvl_to_bvi_compile_update_config_def:
  bvl_to_bvi_compile_update_config clos_conf bvl_conf p =
  let (s, p, l, n1, n2, _) =
    bvl_to_bvi_compile_alt clos_conf.start bvl_conf LN p in (* no names *)
  let clos_conf = clos_conf with start := s in
  let bvl_conf = bvl_conf with <| inlines := l; next_name1 := n1; next_name2 := n2 |> in
    (clos_conf, bvl_conf, p)
End


Definition compile_alt1_def:
  compile_alt1 source_conf clos_conf bvl_conf p =
 (* skip source to source for now *)
  let (source_conf', compiled_p_flat) =
    source_to_flat$compile source_conf p in
  let compiled_p_clos =
    flat_to_clos_compile_alt compiled_p_flat in
  let (clos_conf', compiled_p_bvl) =
    clos_to_bvl_compile_alt clos_conf compiled_p_clos in
  let (clos_conf', bvl_conf', compiled_p_bvi) =
    bvl_to_bvi_compile_update_config clos_conf' bvl_conf compiled_p_bvl in
  let compiled_p_data = bvi_to_data$compile_prog compiled_p_bvi in
    (source_conf', clos_conf', bvl_conf', compiled_p_data)
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
     pattern_cfg : flat_pattern$config ;
     init_vidx : num
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
     compile_exps_aux: (num # num # bvl$exp) list;
  |>
End

Datatype:
  bvl_iconfig = <| inline_size_limit : num (* zero disables inlining *)
                   ; exp_cut : num (* huge number effectively disables exp splitting *)
                   ; split_main_at_seq : bool (* split main expression at Seqs *)
                   ; inlines : (num # bvl$exp) spt
                   ; n1 : num
                   ; n2 : num
                   ; alloc_glob_count : num
            |>
End

Definition icompile_source_to_flat_def:
  icompile_source_to_flat (source_iconf: source_iconfig) p =
  let n = source_iconf.n in
  let init_vidx = source_iconf.init_vidx in
  let next = source_iconf.next in
  let env = source_iconf.env in
  let envs = source_iconf.env_gens in
  let (n', next1, new_env1, env_gens1, p') =
    compile_decs [] n next env envs p in
  if next1.vidx < init_vidx
  then
    let source_iconf = source_iconf with <| n := n'; next := next1; env := extend_env new_env1 env; env_gens := env_gens1|> in
    SOME (source_iconf, MAP (flat_pattern$compile_dec source_iconf.pattern_cfg) p')
  else NONE
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
    let aux = REVERSE aux in
    let p = clos_annotate$compile aux in
  (clos_iconf, p)
End

(* TODO: modify this and try the rest *)
Definition icompile_clos_to_bvl_prog_def:
  icompile_clos_to_bvl_prog max_app config_aux p  =
  let prog = MAP (SND o SND) p in
  let (new_exps, aux) = clos_to_bvl$compile_exps max_app prog [] in
  let new_bvl_exps = MAP2 (λ(loc,args,_) exp. (loc + num_stubs max_app, args, exp)) p new_exps in
  let new_config_aux = aux ++ config_aux in
    (new_config_aux, new_bvl_exps)
End

Definition icompile_clos_to_bvl_def:
  icompile_clos_to_bvl (clos_iconf: clos_iconfig)  p =
  let (clos_iconf, p) = icompile_clos_to_bvl_common clos_iconf p in
  let (aux, p) = icompile_clos_to_bvl_prog clos_iconf.max_app clos_iconf.compile_exps_aux p in
  let clos_iconf = clos_iconf with compile_exps_aux := aux in
    (clos_iconf, p)
End

Definition icompile_bvl_to_bvi_inline_def:
  icompile_bvl_to_bvi_inline limit split_seq cut_size cs p =
  bvl_inline$compile_inc limit split_seq cut_size cs p
End

(* will this result in inefficiencies due to the append code*)
Definition icompile_bvl_to_bvi_prog_def:
  icompile_bvl_to_bvi_prog n p k_acc =
  let k = bvl_to_bvi$alloc_glob_count (MAP (\(_,_,p). p) p) in
  let (code, n1) = bvl_to_bvi$compile_list n p in
    (append code, n1, k_acc + k)
End

Definition icompile_bvl_to_bvi_def:
  icompile_bvl_to_bvi bvl_iconf p =
  let (inlines, p) = icompile_bvl_to_bvi_inline bvl_iconf.inline_size_limit
                                                bvl_iconf.split_main_at_seq
                                                bvl_iconf.exp_cut
                                                bvl_iconf.inlines p in
  let (code, n1, k) = icompile_bvl_to_bvi_prog bvl_iconf.n1 p bvl_iconf.alloc_glob_count in
  let (n2, code) = bvi_tailrec$compile_prog bvl_iconf.n2 code in
  let bvl_iconf = bvl_iconf with <| n1 := n1; n2 := n2; inlines := inlines; alloc_glob_count := k|> in
    (bvl_iconf, code)
End



Definition init_icompile_bvl_to_bvi_def:
  init_icompile_bvl_to_bvi (bvl_conf: bvl_to_bvi$config) bvl_init =
  let bvl_iconf = <| inline_size_limit := bvl_conf.inline_size_limit;
                     exp_cut := bvl_conf.exp_cut;
                     split_main_at_seq := bvl_conf.split_main_at_seq;
                     n1 := 0 ;
                     n2 := backend_common$bvl_num_stubs + 2;
                     inlines := LN ;
                     alloc_glob_count := 0|>
  in
  let (n2, bvi_stubs) = bvi_tailrec$compile_prog bvl_iconf.n2 bvi_stubs_without_init_globs in
  let bvl_iconf = bvl_iconf with n2 := n2 in
  let (bvl_iconf, bvi_stubs1) = icompile_bvl_to_bvi bvl_iconf bvl_init in
  (bvl_iconf,  bvi_stubs ++ bvi_stubs1)
End



Definition end_icompile_bvl_to_bvi_def:
  end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf bvl_conf =
  let (bvl_iconf, bvi_stubs) = icompile_bvl_to_bvi bvl_iconf bvl_end in
  let init_globs_start = backend_common$bvl_num_stubs + bvl_to_bvi_namespaces * clos_conf.start in
  let init_globs_stub = [(InitGlobals_location, InitGlobals_code init_globs_start bvl_iconf.alloc_glob_count)] in
  let (n2, init_globs_stub) = bvi_tailrec$compile_prog bvl_iconf.n2 init_globs_stub in
  let bvl_conf = bvl_conf with
                          <| next_name1 := bvl_iconf.n1;
                             next_name2 := n2;
                             inlines := bvl_iconf.inlines |> in
  let clos_conf = clos_conf with start := InitGlobals_location in
    (clos_conf, bvl_conf: bvl_to_bvi$config, bvi_stubs ++ init_globs_stub)
End


Definition glob_alloc_fixed_def:
  glob_alloc_fixed init =
    Dlet
      (Let om_tra NONE
        (App om_tra
          (GlobalVarAlloc init) [])
        (flatLang$Con om_tra NONE []))
End

Definition init_icompile_source_to_flat_def:
  init_icompile_source_to_flat source_conf =
  let next = source_conf.next with <| vidx := source_conf.next.vidx + 1 |> in
  let env_gens = <| next := 0; generation := source_conf.envs.next; envs := LN |> in
  let source_iconf =
    <| n := 1n;
       next := next;
       env := source_conf.mod_env;
       env_gens := env_gens;
       pattern_cfg := source_conf.pattern_cfg;
       init_vidx := source_conf.init_vidx |> in
  let flat_stubs = MAP (flat_pattern$compile_dec source_conf.pattern_cfg) [glob_alloc_fixed source_conf.init_vidx; source_to_flat$alloc_env_ref] in
  (source_iconf, flat_stubs)
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
                <| next :=
                    (source_iconf.next with
                      vidx := source_iconf.init_vidx);
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
                      length_acc := 0 ;
                      compile_exps_aux := []|> in
  let init_stubs = toAList (init_code clos_iconf.max_app) in
  let (clos_iconf, bvl_stub) = icompile_clos_to_bvl clos_iconf clos_stub in

    (clos_iconf, init_stubs ++ bvl_stub)
End

Definition end_icompile_clos_to_bvl_def:
  end_icompile_clos_to_bvl clos_iconf clos_conf =
  let es_chained = clos_to_bvl$chain_exps clos_iconf.next_loc
                                          clos_iconf.es_to_chain in
  let es_chained = clos_annotate$compile es_chained in
  let (new_aux, es_chained) = icompile_clos_to_bvl_prog clos_iconf.max_app clos_iconf.compile_exps_aux es_chained in
  let clos_conf = clos_conf with
                            <| next_loc :=
                               clos_iconf.next_loc + MAX 1 (clos_iconf.length_acc); (* need to add the length of the es *)
                               start := num_stubs clos_iconf.max_app - 1;
                               known_conf := OPTION_MAP (\kc. kc with val_approx_spt := clos_iconf.known_g) clos_iconf.known_conf;
                               call_state := (clos_iconf.clos_call_g, REVERSE clos_iconf.clos_call_aux) |> in
  let c = clos_iconf in
  let init_globs = [(num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.next_loc))] in
  (clos_conf, es_chained ++ new_aux  ++ init_globs)
End

Definition init_icompile_def:
  init_icompile source_conf clos_conf bvl_conf =
  let (source_iconf, flat_stub) = init_icompile_source_to_flat source_conf in
  let clos_stub = init_icompile_flat_to_clos flat_stub in
  let (clos_iconf, bvl_init) = init_icompile_clos_to_bvl clos_conf clos_stub in
  let (bvl_iconf, bvi_init) = init_icompile_bvl_to_bvi bvl_conf bvl_init in
  let data_init = bvi_to_data$compile_prog bvi_init in
    (source_iconf, clos_iconf, bvl_iconf, data_init)
End

Definition end_icompile_def:
  end_icompile source_iconf source_conf
               clos_iconf clos_conf
               bvl_iconf bvl_conf

  =
  let source_conf_after_ic = end_icompile_source_to_flat source_iconf source_conf in
  let (clos_conf_after_ic, bvl_end) = end_icompile_clos_to_bvl clos_iconf clos_conf in
  let (clos_conf_after_ic_bvi, bvl_conf_after_ic, bvi_end) =
      end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf_after_ic bvl_conf in
  let data_end = bvi_to_data$compile_prog bvi_end in
    (source_conf_after_ic, clos_conf_after_ic_bvi, bvl_conf_after_ic, data_end)

End

Definition icompile_def:
  icompile source_iconf clos_iconf bvl_iconf p =
  case icompile_source_to_flat source_iconf p of NONE => NONE
  | SOME (source_iconf', icompiled_p_flat) =>
  let icompiled_p_clos = icompile_flat_to_clos icompiled_p_flat in
  let (clos_iconf', icompiled_p_bvl) = icompile_clos_to_bvl clos_iconf icompiled_p_clos in
  let (bvl_iconf', icompiled_p_bvi) = icompile_bvl_to_bvi bvl_iconf icompiled_p_bvl in
  let icompiled_p_data = bvi_to_data$compile_prog icompiled_p_bvi in
    SOME (source_iconf', clos_iconf', bvl_iconf', icompiled_p_data)

End


Definition fold_icompile_def:
  fold_icompile source_iconf clos_iconf bvl_iconf [] =
    icompile source_iconf clos_iconf bvl_iconf []
  ∧
  fold_icompile source_iconf clos_iconf bvl_iconf (p :: ps)  =
  case icompile source_iconf clos_iconf bvl_iconf p of NONE => NONE
  | SOME (source_iconf', clos_iconf' , bvl_iconf', p') =>
    (case fold_icompile source_iconf' clos_iconf' bvl_iconf' ps of NONE => NONE
    | SOME (source_iconf'', clos_iconf'', bvl_iconf'', ps') =>
      SOME (source_iconf'', clos_iconf'', bvl_iconf'', p' ++ ps'))
End


(******************************************************************************)
(*                                                                            *)
(* Syntactic correctness for icompile                                          *)
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
  icompile_source_to_flat source_iconf p1 =
    SOME (source_iconf_p1, p1_flat) ∧
  icompile_source_to_flat source_iconf_p1 p2 =
    SOME (source_iconf_p2, p2_flat) ⇒
  icompile_source_to_flat source_iconf (p1 ++ p2) =
    SOME (source_iconf_p2, p1_flat ++ p2_flat)
Proof
  rw[icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flat_compile_decs_lemma, extend_env_assoc]
QED



Theorem compile_decs_num_bindings:
  !t n next env envs decs n' next' env' envs' decs'.
    compile_decs t n next env envs decs = (n', next', env', envs', decs') ⇒
     next.vidx ≤ next'.vidx
Proof
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ simp [markerTheory.Abbrev_def]
  \\ rw[]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fsrw_tac [ETA_ss] []
  \\ DECIDE_TAC
QED

Theorem icompile_icompile_source_to_flat_none:
  icompile_source_to_flat source_iconf p1 =
    NONE  ⇒
  icompile_source_to_flat source_iconf (p1 ++ p2) =
  NONE
Proof
  rw[icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flat_compile_decs_lemma] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule compile_decs_num_bindings >>
  rev_drule compile_decs_num_bindings >>
  simp[]
QED



Theorem icompile_icompile_source_to_flat_none1:
  icompile_source_to_flat source_iconf p1 = SOME (source_iconf', p1') ∧
  icompile_source_to_flat source_iconf' p2 = NONE ⇒
  icompile_source_to_flat source_iconf (p1 ++ p2) = NONE
Proof
  rw[icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_to_flat_compile_decs_lemma]
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
  icompile_clos_to_bvl_common clos_iconf (p1 ++ p2) = (clos_iconf_p2, p1_bvl ++ p2_bvl)
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

Theorem icompile_clos_to_bvl_common_no_compile_exps:
  icompile_clos_to_bvl_common clos_iconf p = (clos_iconf', p') ⇒
  clos_iconf.compile_exps_aux = clos_iconf'.compile_exps_aux
Proof
  rw[icompile_clos_to_bvl_common_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem icompile_clos_to_bvl_common_rest_same:
  icompile_clos_to_bvl_common clos_iconf p = (clos_iconf', p') ⇒
  icompile_clos_to_bvl_common (clos_iconf with compile_exps_aux := aux) p = (clos_iconf' with compile_exps_aux := aux, p')
Proof
  rw[icompile_clos_to_bvl_common_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Triviality clos_iconfig_helper:
  clos_iconf = clos_iconf with compile_exps_aux := clos_iconf.compile_exps_aux
Proof
  rw[fetch "-" "clos_iconfig_component_equality"]
QED





Theorem icompile_icompile_clos_to_bvl_prog:
  icompile_clos_to_bvl_prog max_app aux p1 = (aux_p1, p1') ∧
  icompile_clos_to_bvl_prog max_app aux_p1 p2 = (aux_p2, p2') ⇒
  icompile_clos_to_bvl_prog max_app aux (p1 ++ p2) = (aux_p2, p1' ++ p2')
Proof
  rw[icompile_clos_to_bvl_prog_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_goalsub_rename_tac `MAP2 f _ _ = _` >>
  last_x_assum mp_tac >>
  rev_drule clos_to_bvl_compile_exps_append >>

  disch_then drule >>
  ntac 2 strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  drule clos_to_bvlTheory.compile_exps_LENGTH >>
  simp[LENGTH_MAP] >>
  disch_then (fn t => assume_tac (GSYM t)) >>
  strip_tac >>
  irule MAP2_APPEND >> rw[]
QED


Theorem icompile_clos_to_bvl_common_max_app_constant:
  icompile_clos_to_bvl_common clos_iconf p = (clos_iconf', p') ⇒
  clos_iconf.max_app = clos_iconf'.max_app
Proof
  rw[icompile_clos_to_bvl_common_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem icompile_clos_to_bvl_max_app_constant:
  icompile_clos_to_bvl c p = (c', p') ⇒
  c.max_app = c'.max_app
Proof
  rw[icompile_clos_to_bvl_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_clos_to_bvl_common_max_app_constant >> rw[]
QED



Theorem icompile_icompile_clos_to_bvl:
  icompile_clos_to_bvl clos_iconf p1 = (clos_iconf_p1, p1_bvl) ∧
  icompile_clos_to_bvl clos_iconf_p1 p2 = (clos_iconf_p2, p2_bvl) ⇒
  icompile_clos_to_bvl clos_iconf (p1 ++ p2) = (clos_iconf_p2, p1_bvl ++ p2_bvl)
Proof
  strip_tac >>
  fs[icompile_clos_to_bvl_def] >> rpt (pairarg_tac >> gvs[]) >>
  last_x_assum assume_tac >>
  rev_drule icompile_clos_to_bvl_common_max_app_constant >>
  simp[] >>
  disch_then (fn t => assume_tac (GSYM t) >> gvs[]) >>
  drule icompile_clos_to_bvl_common_max_app_constant >>
  ntac 2 (pop_assum mp_tac) >>
  drule icompile_clos_to_bvl_common_max_app_constant >>
  ntac 4 strip_tac >>
  gvs[] >>
  rename1 ‘icompile_clos_to_bvl_prog max_app _ _ = _’ >>
  rpt (qpat_x_assum ‘_ = max_app’ kall_tac) >>
  pop_assum mp_tac >>
  drule icompile_clos_to_bvl_common_rest_same >>
  disch_then $ qspec_then ‘aux''’ mp_tac >>
  strip_tac >>
  drule_all icompile_icompile_clos_to_bvl_common >>
  strip_tac >>
  strip_tac >>
  drule icompile_clos_to_bvl_common_rest_same >>
  disch_then $ qspec_then ‘aux''’ assume_tac >> gvs[] >>
  drule_all icompile_icompile_clos_to_bvl_prog >>
  strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  drule icompile_clos_to_bvl_common_no_compile_exps >>
  disch_then (fn t => assume_tac (GSYM t) >> gvs[]) >>
  pop_assum kall_tac >>
  ntac 2 (pop_assum mp_tac) >>
  drule icompile_clos_to_bvl_common_no_compile_exps >>
  strip_tac >> gvs[]

QED

Theorem bvl_tick_inline_all_aux_disch:
  ∀ cs p aux cs' p'.
  bvl_inline$tick_inline_all limit cs p aux = (cs', p') ⇒
  bvl_inline$tick_inline_all limit cs p (aux ++ aux_extra) = (cs', (REVERSE aux_extra) ++ p')
Proof
  Induct_on ‘p’ >> rw[bvl_inlineTheory.tick_inline_all_def] >>
  namedCases_on ‘h’ ["n arity es1"] >>
  fs[bvl_inlineTheory.tick_inline_all_eq] >>
  rw[] >> gvs[] >>
  qspecl_then [‘aux’, ‘aux_extra’, ‘(n,arity,tick_inline_sing cs es1)’] mp_tac (cj 2 (GSYM APPEND) ) >>
  disch_then (fn t => once_rewrite_tac[t]) >>
  last_x_assum drule >>
  rw[]
QED

Theorem bvl_tick_inline_all_cons:
  bvl_inline$tick_inline_all limit cs (x :: xs) [] =
  let (cs1, aux1) = bvl_inline$tick_inline_all limit cs [x] [] in
  let (cs2, aux2) = bvl_inline$tick_inline_all limit cs1 xs [] in
    (cs2, aux1 ++ aux2)
Proof
  rw[] >>
  pairarg_tac >> gvs[] >>
  namedCases_on ‘x’ ["n arity es1"] >>
  pairarg_tac >> gvs[] >>
  rw[bvl_inlineTheory.tick_inline_all_eq] >>
  gvs[bvl_inlineTheory.tick_inline_all_def] >>
  fs[bvl_inlineTheory.tick_inline_sing] >>
  drule bvl_tick_inline_all_aux_disch >>
  rw[]
QED

Theorem bvl_tick_inline_all_append:
  ∀p1 p2 cs cs1 aux aux1 cs2 aux2.
  bvl_inline$tick_inline_all limit cs p1 [] = (cs1, aux1) ∧
  bvl_inline$tick_inline_all limit cs1 p2 [] = (cs2, aux2) ⇒
  bvl_inline$tick_inline_all limit cs (p1 ++ p2) [] = (cs2, aux1 ++ aux2)
Proof
  Induct_on ‘p1’ >>
  rw[bvl_inlineTheory.tick_inline_all_def] >> simp[] >>
  ntac 2 (pop_assum mp_tac) >>
  once_rewrite_tac[bvl_tick_inline_all_cons] >>
  simp[] >> rpt (pairarg_tac >> simp[]) >>
  strip_tac >>
  pop_assum mp_tac >>
  pop_assum (fn t => simp[GSYM t]) >>
  strip_tac >>
  strip_tac >>
  last_x_assum rev_drule_all >>
  rw[]

QED

Theorem bvl_tick_compile_prog_append:
  bvl_inline$tick_compile_prog limit cs p1 = (cs1, p1') ∧
  bvl_inline$tick_compile_prog limit cs1 p2 = (cs2, p2') ⇒
  bvl_inline$tick_compile_prog limit cs (p1 ++ p2) = (cs2, p1' ++ p2')
Proof
  rw[bvl_inlineTheory.tick_compile_prog_def] >>
  metis_tac[bvl_tick_inline_all_append]
QED

Theorem bvl_inline_compile_inc_append:
  bvl_inline$compile_inc limit split_seq cut_size cs p1 = (cs1, p1') ∧
  bvl_inline$compile_inc limit split_seq cut_size cs1 p2 = (cs2, p2') ⇒
  bvl_inline$compile_inc limit split_seq cut_size cs (p1 ++ p2) = (cs2, p1' ++ p2')
Proof
  rw[bvl_inlineTheory.compile_inc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rev_drule_all bvl_tick_compile_prog_append >>
  rw[]
QED

Theorem bvl_to_bvi_compile_list_append:
  ∀p1 p2 p1' p2' n n1 n2 p1'p2'.
  bvl_to_bvi$compile_list n p1 = (p1', n1) ∧
  bvl_to_bvi$compile_list n1 p2 = (p2', n2) ∧
  bvl_to_bvi$compile_list n (p1 ++ p2) = (p1'p2', n12)
  ⇒
  append p1' ++ append p2' = append p1'p2' ∧
  n12 = n2
Proof
  Induct_on ‘p1’ >>
  rw[bvl_to_bviTheory.compile_list_def] >>
  gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  last_x_assum drule >>
  disch_then rev_drule >>
  disch_then drule >> rw[]
QED

(*
Theorem bvl_to_bvi_tailrec_compile_prog_cons:
  bvi_tailrec$compile_prog next (x :: xs) =

*)

Theorem bvl_to_bvi_tailrec_compile_prog_append:
  ∀p1 p2 next next1 next2 p1' p2'.
  bvi_tailrec$compile_prog next p1 = (next1, p1') ∧
  bvi_tailrec$compile_prog next1 p2 = (next2, p2') ⇒
  bvi_tailrec$compile_prog next (p1 ++ p2) = (next2, p1' ++ p2')
Proof
  Induct_on ‘p1’ >>
  rw[bvi_tailrecTheory.compile_prog_def] >>
  namedCases_on ‘h’ ["loc arity exp"]  >>
  gvs[bvi_tailrecTheory.compile_prog_def] >>
  Cases_on ‘compile_exp loc next arity exp’ >> simp[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      last_x_assum drule >>
      disch_then rev_drule >>
      rw[])
  >- (namedCases_on ‘x’ ["exp_aux exp_opt"] >>
      gvs[] >>
      rpt (pairarg_tac >> gvs[]) >>
      last_x_assum drule >>
      disch_then rev_drule >>
      rw[])
QED

Theorem alloc_glob_count_bvl_to_bvi_append:
  ∀p1 p2 p1_num p2_num.
  bvl_to_bvi$alloc_glob_count p1 = p1_num ∧
  bvl_to_bvi$alloc_glob_count p2 = p2_num ⇒
  bvl_to_bvi$alloc_glob_count (p1 ++ p2) = p1_num + p2_num

Proof
  Induct_on ‘p1’ >>
  rw[bvl_to_bviTheory.alloc_glob_count_def] >>
  gvs[GSYM bvl_to_bviTheory.alloc_glob_count_eq_global_count_list] >>
  once_rewrite_tac[bvl_to_bviTheory.global_count_sing_def] >>
  rw[]
QED


Theorem  icompile_icompile_bvl_to_bvi_inline:
  icompile_bvl_to_bvi_inline limit split_seq cut_size cs p1 = (cs1, p1') ∧
  icompile_bvl_to_bvi_inline limit split_seq cut_size cs1 p2 = (cs2, p2') ⇒
  icompile_bvl_to_bvi_inline limit split_seq cut_size cs (p1 ++ p2) = (cs2, p1' ++ p2')
Proof
  rw[icompile_bvl_to_bvi_inline_def] >>
  rw[bvl_inline_compile_inc_append]
QED


Theorem icompile_icompile_bvl_to_bvi_prog:
  ∀ p1 p2 n n1 n2 p1' p2' k k1 k2.
  icompile_bvl_to_bvi_prog n p1 k = (p1', n1, k1) ∧
  icompile_bvl_to_bvi_prog n1 p2 k1 = (p2', n2, k2) ⇒
  icompile_bvl_to_bvi_prog n (p1 ++ p2) k = (p1' ++ p2', n2, k2)
Proof
  rw[icompile_bvl_to_bvi_prog_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule bvl_to_bvi_compile_list_append >>
  last_x_assum assume_tac >>
  disch_then rev_drule >>
  disch_then drule >>
  rw[alloc_glob_count_bvl_to_bvi_append]
QED

Theorem icompile_icompile_bvl_to_bvi:
  icompile_bvl_to_bvi bvl_iconf p1 = (bvl_iconf', p') ∧
  icompile_bvl_to_bvi bvl_iconf' p2 = (bvl_iconf'', p'') ⇒
  icompile_bvl_to_bvi bvl_iconf (p1 ++ p2) = (bvl_iconf'', p' ++ p'')
Proof
  rw[icompile_bvl_to_bvi_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_icompile_bvl_to_bvi_inline >>
  disch_then (fn t =>
                ntac 3 (pop_assum mp_tac) >>
              drule t) >>
  strip_tac >> gvs[] >>
  ntac 2 strip_tac >>
  drule icompile_icompile_bvl_to_bvi_prog >>
  disch_then (fn t =>
                pop_assum mp_tac >>
              drule t) >>
  strip_tac >> gvs[] >>
  ntac 2 strip_tac >>
  drule bvl_to_bvi_tailrec_compile_prog_append >>
  disch_then (fn t =>
                pop_assum mp_tac >>
              drule t) >>
  strip_tac >> gvs[]
QED


Theorem icompile_icompile:
  icompile source_iconf clos_iconf bvl_iconf prog1 = SOME (source_iconf', clos_iconf', bvl_iconf', prog1') ∧
  icompile source_iconf' clos_iconf' bvl_iconf' prog2 = SOME (source_iconf'', clos_iconf'', bvl_iconf'', prog2') ⇒
  icompile source_iconf clos_iconf bvl_iconf (prog1 ++ prog2) =
    SOME (source_iconf'', clos_iconf'', bvl_iconf'', prog1' ++ prog2')
Proof
  rw[] >>
  gvs[icompile_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all icompile_icompile_source_to_flat >> strip_tac >> gvs[] >>
  fs[icompile_flat_to_clos_and_append_commute] >>
  rev_drule_all icompile_icompile_clos_to_bvl >>
  rpt (strip_tac >> gvs[]) >>
  drule_all icompile_icompile_bvl_to_bvi >>
  rpt (strip_tac >> gvs[]) >>
  rw[bvi_to_dataTheory.compile_prog_def]
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


Definition config_prog_rel_s2d_def:
  config_prog_rel_s2d source_conf_after_ic source_conf_after_c
                      clos_conf_after_c clos_conf_after_ic
                      clos_conf_after_c_bvi clos_conf_after_ic_bvi
                      bvl_conf_after_ic bvl_conf_after_c
                      icompiled_p_data_combined compiled_p_data
  =
  (source_conf_after_ic = source_conf_after_c
   ∧
   clos_conf_after_c = clos_conf_after_ic
   ∧
   clos_conf_after_c_bvi = clos_conf_after_ic_bvi
   ∧
   bvl_conf_after_ic = bvl_conf_after_c
   ∧
   icompiled_p_data_combined = compiled_p_data)

End

Definition config_prog_pair_rel_def:
  config_prog_pair_rel c1 p1 c2 p2 ⇔
    c1 = c2 ∧ p1 = p2
End

Definition config_prog_rel_b2b_def:
  config_prog_rel_b2b clos_conf_after_ic bvl_conf_after_ic (icompiled_bvi_combined)
                      clos_conf_after_c bvl_conf_after_c compiled_p_bvi
  =
  (clos_conf_after_ic = clos_conf_after_c
  ∧
  bvl_conf_after_ic = bvl_conf_after_c
  ∧
  icompiled_bvi_combined = compiled_p_bvi)
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
  icompile_source_to_flat source_iconf p = SOME (source_iconf', icompiled_p)
  ∧
  end_icompile_source_to_flat source_iconf' source_conf = source_conf_after_ic
  ∧
  source_to_flat$compile source_conf p = (source_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ⇒
  config_prog_pair_rel source_conf_after_ic (flat_stub ++ icompiled_p)
                      source_conf_after_c compiled_p
Proof
  rw[] >>
  fs[init_icompile_source_to_flat_def,
     icompile_source_to_flat_def,
     source_to_flatTheory.compile_def,
     source_to_flatTheory.compile_prog_def] >>
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



Theorem init_icompile_icompile_end_icompile_c2b_alt:
  init_icompile_clos_to_bvl clos_conf clos_stub = (clos_iconf, bvl_stub)
  ∧
  icompile_clos_to_bvl clos_iconf p = (clos_iconf', p_bvl)
  ∧
  end_icompile_clos_to_bvl clos_iconf' clos_conf = (clos_conf_after_ic, p_bvl_end)
  ∧
  clos_to_bvl_compile_alt clos_conf (clos_stub ++ p) =
  (clos_conf_after_c, compiled_p)
  ∧
  clos_conf = clos_to_bvl$default_config ⇒
  config_prog_pair_rel clos_conf_after_ic (bvl_stub ++ p_bvl ++ p_bvl_end)
                       clos_conf_after_c compiled_p

Proof
  rw[clos_to_bvlTheory.default_config_def,
      init_icompile_clos_to_bvl_def] >>
  drule icompile_clos_to_bvl_max_app_constant >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_icompile_clos_to_bvl >>
  disch_then rev_drule >>
  pop_assum kall_tac >>
  last_x_assum kall_tac >>
  strip_tac >>
  fs[clos_to_bvl_compile_alt_def,
     clos_to_bvl_compile_common_alt_def,
     clos_to_bvlTheory.compile_prog_def] >> rpt (pairarg_tac >> gvs[]) >>
  fs[icompile_clos_to_bvl_def, icompile_clos_to_bvl_prog_def, icompile_clos_to_bvl_common_def] >> rpt (pairarg_tac >> gvs[]) >>
  fs[clos_knownTheory.compile_def, clos_callTheory.compile_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[end_icompile_clos_to_bvl_def] >> rpt (pairarg_tac >> gvs[]) >>
  rw[config_prog_pair_rel_def] >>
  gvs[icompile_clos_to_bvl_prog_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ntac 4 (last_x_assum mp_tac) >>
  disch_then (fn t => assume_tac (GSYM t)) >>
  ntac 3 strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[] >>
  qmatch_goalsub_rename_tac ‘MAP2 f _ _ ++ MAP2 f _ _ ++ _ ++ _ = MAP2 f _ _ ++ _’ >> rpt (pairarg_tac >> gvs[]) >>
  gvs[clos_annotate_compile_append] >>
  pop_assum mp_tac >>
  drule clos_to_bvl_compile_exps_append >>
  disch_then rev_drule >>
  rpt (strip_tac >> gvs[]) >>
  rev_drule clos_to_bvlTheory.compile_exps_LENGTH >>
  simp[LENGTH_MAP] >>
  disch_then (fn t => assume_tac (GSYM t)) >>
  drule (INST_TYPE [gamma|->“:(num#num#bvl$exp)”] MAP2_APPEND) >>
  disch_then (fn t => qspecl_then [‘compile (chain_exps n es'')’, ‘new_exps''’, ‘f’] mp_tac t) >>
  rw[]
QED


Theorem init_icompile_icompile_end_icompile_b2b:
  init_icompile_bvl_to_bvi (bvl_conf: bvl_to_bvi$config) bvl_init = (bvl_iconf, bvi_init)
  ∧
  icompile_bvl_to_bvi bvl_iconf p = (bvl_iconf', p_bvi)
  ∧
  end_icompile_bvl_to_bvi bvl_end bvl_iconf' clos_conf bvl_conf = (clos_conf_after_ic, bvl_conf_after_ic, bvi_end)
  ∧
  bvl_to_bvi_compile_update_config clos_conf bvl_conf (bvl_init ++ p ++ bvl_end)  = (clos_conf_after_c, bvl_conf_after_c, compiled_p_bvi)
  ∧
  bvl_conf = bvl_to_bvi$default_config ⇒
  config_prog_rel_b2b clos_conf_after_ic bvl_conf_after_ic (bvi_init ++ p_bvi ++ bvi_end)
                      clos_conf_after_c bvl_conf_after_c compiled_p_bvi
Proof
  strip_tac >>
  fs[init_icompile_bvl_to_bvi_def, end_icompile_bvl_to_bvi_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_icompile_bvl_to_bvi >>
  disch_then rev_drule >>
  strip_tac >>
  drule icompile_icompile_bvl_to_bvi >>
  last_x_assum assume_tac >>
  disch_then rev_drule >>
  rpt (qpat_x_assum ‘icompile_bvl_to_bvi _ _ = _’ kall_tac) >>
  strip_tac >>
  fs[icompile_bvl_to_bvi_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum ‘(n2', bvi_stubs') = _’ (fn t => assume_tac (GSYM t)) >>
  drule bvl_to_bvi_tailrec_compile_prog_append >>
  disch_then (fn t => pop_assum mp_tac >> drule t) >>
  simp[] >> strip_tac >>
  disch_then (fn t => mp_tac (GSYM t)) >>
  drule bvl_to_bvi_tailrec_compile_prog_append >>
  disch_then rev_drule >>
  strip_tac >> gvs[] >>
  disch_then kall_tac >>
  pop_assum mp_tac >>
  rpt (qpat_x_assum ‘compile_prog _ _ = _’ kall_tac) >>
  strip_tac >>
  gvs[bvl_to_bvi_compile_update_config_def,
      icompile_bvl_to_bvi_inline_def,
      icompile_bvl_to_bvi_prog_def,
      bvl_to_bviTheory.default_config_def,
      bvl_to_bvi_compile_alt_def,
      bvl_to_bvi_compile_prog_alt_def,
      bvl_inlineTheory.compile_prog_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[config_prog_rel_b2b_def]
QED


(* deprecate this
Theorem init_icompile_icompile_end_icompile_s2b:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub)
  ∧
  init_icompile_flat_to_clos flat_stub = clos_stub
  ∧
  init_icompile_clos_to_bvl clos_conf clos_stub = (clos_iconf, bvl_init)
  ∧
  init_icompile_bvl_to_bvi bvl_conf bvl_init = (bvl_iconf, bvi_init)
  ∧
  icompile_source_to_flat source_iconf p = SOME (source_iconf', icompiled_p_flat)
  ∧
  icompile_flat_to_clos icompiled_p_flat = icompiled_p_clos
  ∧
  icompile_clos_to_bvl clos_iconf icompiled_p_clos = (clos_iconf', icompiled_p_bvl)
  ∧
  icompile_bvl_to_bvi bvl_iconf icompiled_p_bvl = (bvl_iconf, icompiled_p_bvi)
  ∧
  end_icompile_source_to_flat source_iconf' source_conf = source_conf_after_ic
  ∧
  end_icompile_clos_to_bvl clos_iconf' clos_conf  = (clos_conf_after_ic, bvl_end)
  ∧
  end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf_after_ic bvl_conf = (clos_conf_after_ic_bvi, bvl_conf_after_ic, bvi_end)
  ∧
  source_to_flat$compile source_conf p = (source_conf_after_c, compiled_p_flat)
  ∧
  flat_to_clos_compile_alt compiled_p_flat = compiled_p_clos
  ∧
  clos_to_bvl_compile_alt clos_conf compiled_p_clos = (clos_conf_after_c, compiled_p_bvl)
  ∧
  bvl_to_bvi_compile_update_config clos_conf_after_c bvl_conf compiled_p_bvl = (clos_conf_after_c_bvi, bvl_conf_after_c, compiled_p_bvi)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ∧
  bvl_conf = bvl_to_bvi$default_config ⇒
  config_prog_rel_s2b source_conf_after_ic source_conf_after_c
                      clos_conf_after_c clos_conf_after_ic
                      clos_conf_after_c_bvi clos_conf_after_ic_bvi (* dont think i need to define a separate one but just for clarity *)
                      bvl_conf_after_ic bvl_conf_after_c
                      (bvi_init ++ icompiled_p_bvi ++ bvi_end) compiled_p_bvi



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
  qpat_x_assum ‘bvl_conf = _’ mp_tac >>
  drule_all init_icompile_icompile_end_icompile_c2b_alt >>
  strip_tac >> gvs[config_prog_pair_rel_def] >> gvs[] >>
  strip_tac >>
  drule_all init_icompile_icompile_end_icompile_b2b >>
  rw[config_prog_rel_b2b_def] >>
  rw[config_prog_rel_s2b_def]
QED
*)

Theorem init_icompile_icompile_end_icompile_f2c_alt:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub) ⇒
  flat_to_clos_compile_alt (flat_stub ++ icompiled_p_flat) =
  init_icompile_flat_to_clos flat_stub ++ icompile_flat_to_clos icompiled_p_flat
Proof
  metis_tac[init_icompile_icompile_end_icompile_f2c]
QED




Theorem init_icompile_icompile_end_icompile:
  init_icompile source_conf clos_conf bvl_conf = (source_iconf, clos_iconf, bvl_iconf,  data_init)
  ∧
  icompile source_iconf clos_iconf bvl_iconf p = SOME (source_iconf', clos_iconf', bvl_iconf', icompiled_p_data)
  ∧
  end_icompile source_iconf' source_conf
               clos_iconf' clos_conf
               bvl_iconf' bvl_conf
  = (source_conf_after_ic, clos_conf_after_ic, bvl_conf_after_ic, data_end)
  ∧
  compile_alt1 source_conf clos_conf bvl_conf p = (source_conf_after_c, clos_conf_after_c, bvl_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ∧
  bvl_conf = bvl_to_bvi$default_config
  ⇒
  config_prog_rel_s2d source_conf_after_ic source_conf_after_c
                      clos_conf_after_c clos_conf_after_ic
                      clos_conf_after_c clos_conf_after_ic (* dont think i need to define a separate one but just for clarity *)
                      bvl_conf_after_ic bvl_conf_after_c
                      (data_init ++ icompiled_p_data ++ data_end) compiled_p
Proof
  once_rewrite_tac[init_icompile_def, icompile_def, end_icompile_def, compile_alt1_def] >>
  simp[] >>
  strip_tac >>
  ntac 3 (pop_assum mp_tac) >>
  rpt (pairarg_tac >> fs[]) >>
  qpat_x_assum ‘end_icompile_source_to_flat _ _ = _’ mp_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >>
  drule_all init_icompile_icompile_end_icompile_s2f >>
  simp[config_prog_pair_rel_def] >>
  strip_tac >>
  pop_assum (fn f => assume_tac (GSYM f)) >>
  qpat_x_assum ‘clos_conf = _ ’ mp_tac >>
  qpat_x_assum ‘bvl_conf = _ ’ mp_tac >>
  qpat_x_assum ‘clos_to_bvl_compile_alt _ _ = _ ’ mp_tac >> simp[] >>
  strip_tac >>
  drule_all init_icompile_icompile_end_icompile_f2c_alt >>
  strip_tac >> pop_assum $ qspec_then ‘icompiled_p_flat’ assume_tac >>
  gvs[] >>
  rpt strip_tac >>
  qpat_x_assum ‘bvl_conf = _ ’ mp_tac >>
  drule_all init_icompile_icompile_end_icompile_c2b_alt >>
  simp[config_prog_pair_rel_def] >>
  strip_tac >> qpat_x_assum ‘clos_conf = _’ mp_tac >>
  gvs[] >> rpt strip_tac >>
  drule_all init_icompile_icompile_end_icompile_b2b >>
  simp[config_prog_rel_b2b_def] >>
  strip_tac >> gvs[config_prog_rel_s2d_def] >> rw[config_prog_rel_s2d_def] >>
  rw[bvi_to_dataTheory.compile_prog_def]
QED


Theorem icompile_none:
  icompile a b c p = NONE ⇒
  icompile a b c (p ++ p') = NONE
Proof
  rw[icompile_def] >>
  rw[icompile_icompile_source_to_flat] >>
  Cases_on ‘icompile_source_to_flat a p’
  >- (gvs[] >> drule icompile_icompile_source_to_flat_none >> rw[])
  >- (Cases_on ‘x’ >>
      gvs[] >> rpt (pairarg_tac >> gvs[]))
QED

Theorem icompile_none1:
  ∀ a b c a' b' c' p p'.
  icompile a b c p = SOME (a', b', c', _) ∧
  icompile a' b' c' p' = NONE ⇒
  icompile a b c (p ++ p') = NONE
Proof
  rw[icompile_def] >>
  Cases_on ‘icompile_source_to_flat a p’ >> gvs[] >>
  namedCases_on ‘x’ ["a' b'"] >>
  gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on ‘icompile_source_to_flat a' p'’
  >- (gvs[icompile_icompile_source_to_flat_none1])
  >- (namedCases_on ‘x’ ["a'' b''"] >> gvs[] >> rpt (pairarg_tac >> gvs[]))
QED



Theorem fold_icompile_collapse:
  ∀pss source_iconf clos_iconf bvl_iconf.
  fold_icompile source_iconf clos_iconf bvl_iconf pss =
  icompile source_iconf clos_iconf bvl_iconf (FLAT pss)
Proof
  Induct >>
  rw[fold_icompile_def] >>
  Cases_on ‘icompile source_iconf clos_iconf bvl_iconf h’
  >- (simp[] >>
      drule icompile_none >> rw[])
  >- (namedCases_on ‘x’ ["source_iconf' clos_iconf' bvl_iconf' p'"] >>
      rw[] >>
      drule icompile_none1 >> strip_tac >>
      Cases_on ‘icompile source_iconf' clos_iconf' bvl_iconf' (FLAT pss)’ >>
      simp[] >>
      namedCases_on ‘x’ ["source_iconf'' clos_iconf'' clos_iconf'' ps'"] >>
      simp[] >>
      rev_drule_all icompile_icompile >> rw[])
QED



Theorem icompile_eq:
  init_icompile source_conf clos_conf bvl_conf = (source_iconf, clos_iconf, bvl_iconf, bvi_init)
  ∧
  fold_icompile source_iconf clos_iconf bvl_iconf pss = SOME (source_iconf', clos_iconf', bvl_iconf', icompiled_p_bvi)
  ∧
  end_icompile source_iconf' source_conf
               clos_iconf' clos_conf
               bvl_iconf' bvl_conf
  = (source_conf_after_ic, clos_conf_after_ic, bvl_conf_after_ic, bvi_end)
  ∧
  compile_alt1 source_conf clos_conf bvl_conf (FLAT pss) = (source_conf_after_c, clos_conf_after_c, bvl_conf_after_c, compiled_p)
  ∧
  source_conf = source_to_flat$empty_config
  ∧
  clos_conf = clos_to_bvl$default_config
  ∧
  bvl_conf = bvl_to_bvi$default_config
  ⇒
  config_prog_rel_s2d source_conf_after_ic source_conf_after_c
                      clos_conf_after_c clos_conf_after_ic
                      clos_conf_after_c clos_conf_after_ic (* dont think i need to define a separate one but just for clarity *)
                      bvl_conf_after_ic bvl_conf_after_c
                      (bvi_init ++ icompiled_p_bvi ++ bvi_end) compiled_p
Proof
  once_rewrite_tac[fold_icompile_collapse] >>
  metis_tac[init_icompile_icompile_end_icompile]
QED




val _ = export_theory();
