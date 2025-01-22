(*
  Defines a new incremental backend which is
  meant to be syntactically equal to backend but allows
  compiling program in a part-by-part manner
*)
open preamble backend_asmTheory namespacePropsTheory;

val _ = new_theory"ibackend";

(*
  High-level idea:

  We'll define incremental compilation in three steps to
    simulate to_lab:

  1. init_icompile:

    This should initialize incremental compilation by running
    the CakeML compiler to insert all of its initial stubs.

  2. icompile:

    This should run incremental compilation on separate
    chunks of an incrementally defined input source program.

  3. end_icompile:

    This should "end" compilation by inserting the main
    entry point of the whole program and cleaning up.

  The above steps will get us to labLang.

  Then, we'll do a whole program assembly step to get the
  final program.
*)

(******************************************************************************)
(*                                                                            *)
(* Temporary def of compile_alt                                               *)
(*                                                                            *)
(******************************************************************************)

(* An alternative version compile_def that we'll prove correctness against
  TODO: the _alt parts of this definition will eventually need to be proved
  and moved into backend/ *)

(* NOTE: change the order of prog going into clos_annotate
  clos_to_bvlTheory.compile_common_def *)
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
      (c with <| start := n; next_loc := n + MAX 1 (LENGTH es);
        known_conf := kc; call_state := (g,aux) |>,
       prog)
End

(* A new "top" function that keeps a compiled exp and
  its auxliaries (aux) close by.
  clos_to_bvlTheory.compile_prog_def *)
Definition clos_to_bvl_compile_prog_top_def:
  clos_to_bvl_compile_prog_top max_app (prog: (num # num # closLang$exp) list) =
  MAP (\(loc, args, e).
         let (new_exp, aux) = compile_exp_sing max_app e [] in
           (loc + num_stubs max_app, args, new_exp) ::  aux
      ) prog
End

(* Replaces compile_common and compile_prog.
  clos_to_bvlTheory.compile_def *)
Definition clos_to_bvl_compile_alt_def:
  clos_to_bvl_compile_alt c0 es =
    let (c, prog) = clos_to_bvl_compile_common_alt c0 es in
    let init_stubs = toAList (init_code c.max_app) in
    let init_globs = [(num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.start))] in
    let comp_progs = clos_to_bvl_compile_prog_top c.max_app prog in
    let comp_progs = FLAT comp_progs in
    let prog' = init_stubs ++ comp_progs ++ init_globs in
    let c = c with start := num_stubs c.max_app - 1 in
      (c, prog')
End

(* bvl_to_bviTheory.stubs_def *)
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

(* bvl_to_bviTheory.compile_prog_def *)
Definition bvl_to_bvi_compile_prog_alt_def:
  bvl_to_bvi_compile_prog_alt start n prog =
    let k = alloc_glob_count (MAP (\(_,_,p). p) prog) in
    let (code,n1) = bvl_to_bvi$compile_list n prog in
    let init_globs_start = backend_common$bvl_num_stubs + bvl_to_bvi_namespaces * start in
    let init_globs_stub = [(InitGlobals_location, InitGlobals_code init_globs_start k)] in
      (InitGlobals_location, bvi_stubs_without_init_globs ++ append code ++ init_globs_stub, n1)
End

(* change the order of the stubs
  bvl_to_bviTheory.compile_def *)
Definition bvl_to_bvi_compile_alt_def:
  bvl_to_bvi_compile_alt start (c: bvl_to_bvi$config) names prog =
    let (inlines, prog) = bvl_inline$compile_prog c.inline_size_limit
           c.split_main_at_seq c.exp_cut prog in
    let (loc, code, n1) = bvl_to_bvi_compile_prog_alt start 0 prog in
    let (n2, code') = bvi_tailrec$compile_prog (backend_common$bvl_num_stubs + 2) code in
      (loc, code', inlines, n1, n2, get_names (MAP FST code') names)
End

(* collate all the config updates *)
Definition bvl_to_bvi_compile_update_config_def:
  bvl_to_bvi_compile_update_config clos_conf bvl_conf p =
  let (s, p, l, n1, n2, _) =
    bvl_to_bvi_compile_alt clos_conf.start bvl_conf LN p in (* no names *)
  let clos_conf = clos_conf with start := s in
  let bvl_conf = bvl_conf with <| inlines := l; next_name1 := n1; next_name2 := n2 |> in
    (clos_conf, bvl_conf, p)
End

Definition compile_alt_def:
  compile_alt (asm_conf: 'a asm_config) (c : inc_config) p =
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let data_conf = c.inc_data_conf in
  let word_to_word_conf = c.inc_word_to_word_conf in
  let stack_conf = c.inc_stack_conf in
  let p = source_to_source$compile p in
  let (source_conf', compiled_p_flat) =
    source_to_flat$compile source_conf p in
  let compiled_p_clos =
    flat_to_clos$compile_prog compiled_p_flat in
  let (clos_conf', compiled_p_bvl) =
    clos_to_bvl_compile_alt clos_conf compiled_p_clos in
  let (clos_conf', bvl_conf', compiled_p_bvi) =
    bvl_to_bvi_compile_update_config clos_conf' bvl_conf compiled_p_bvl in
  let compiled_p_data =
    bvi_to_data$compile_prog compiled_p_bvi in
  let (_, compiled_p_word1) =
    data_to_word$compile data_conf word_to_word_conf asm_conf compiled_p_data in
  let (bm, word_to_stack_conf ,fs, compiled_p_stack) =
    word_to_stack$compile asm_conf compiled_p_word1 in
  let max_heap = (2 * data_to_word$max_heap_limit (:'a) data_conf - 1) in
  let sp = (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3)) in
  let offset = asm_conf.addr_offset in
  let compiled_p_lab = stack_to_lab$compile stack_conf data_conf max_heap sp offset compiled_p_stack in
  let c' = c with
             <| inc_source_conf := source_conf';
                inc_clos_conf := clos_conf';
                inc_bvl_conf := bvl_conf';
                inc_word_conf := word_to_stack_conf
             |> in
    (c', bm, compiled_p_lab)
End

(* Configurations for incremental compilation *)
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

Datatype:
  word_iconfig = <| k : num ;
                    bm : 'a word app_list # num ;
                    sfs_list : (num # num) list;
                    fs : num list
                  |>
End

(*
Definition empty_word_to_stack_iconf_def:
    empty_word_to_stack_iconf = (<| k := 0n;
                                   bm := ((Nil, 1n) : 'a word app_list # num);
                                   sfs_list := [];
                                   fs := [] |> : 'a word_to_stack_iconfig)
End
*)

Datatype:
  iconfig =
  <| source_iconf : source_iconfig;
     clos_iconf: clos_iconfig;
     bvl_iconf: bvl_iconfig;
     data_conf : data_to_word$config;
     word_to_word_conf : word_to_word$config;
     word_iconf: 'a word_iconfig;
     stack_conf : stack_to_lab$config
  |>
End

(* source_to_flat *)
Definition icompile_source_to_flat_def:
  icompile_source_to_flat source_iconf p =
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

(* flat_to_clos *)
Definition icompile_flat_to_clos_def:
  icompile_flat_to_clos p = flat_to_clos$compile_decs p
End

Definition init_icompile_flat_to_clos_def:
  init_icompile_flat_to_clos flat_stub =
  let clos_stub = (clos_interp$compile_init T) :: (flat_to_clos$compile_decs flat_stub) in
  clos_stub
End

(* clos_to_bvl *)
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

Definition icompile_clos_to_bvl_alt_def:
  icompile_clos_to_bvl_alt (clos_iconf: clos_iconfig) p =
  let (clos_iconf, p) = icompile_clos_to_bvl_common clos_iconf p in
  let p = FLAT (clos_to_bvl_compile_prog_top clos_iconf.max_app p) in
    (clos_iconf, p)
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
  let (clos_iconf, bvl_stub) = icompile_clos_to_bvl_alt clos_iconf clos_stub in
    (clos_iconf, init_stubs ++ bvl_stub)
End

Definition end_icompile_clos_to_bvl_def:
  end_icompile_clos_to_bvl clos_iconf clos_conf =
  let es_chained = clos_to_bvl$chain_exps clos_iconf.next_loc
                                          clos_iconf.es_to_chain in
  let es_chained = clos_annotate$compile es_chained in
  let es_chained = FLAT (clos_to_bvl_compile_prog_top clos_iconf.max_app es_chained) in
  let clos_conf = clos_conf with
                            <| next_loc :=
                               clos_iconf.next_loc + MAX 1 (clos_iconf.length_acc); (* need to add the length of the es *)
                               start := num_stubs clos_iconf.max_app - 1;
                               known_conf := OPTION_MAP (\kc. kc with val_approx_spt := clos_iconf.known_g) clos_iconf.known_conf;
                               call_state := (clos_iconf.clos_call_g, REVERSE clos_iconf.clos_call_aux) |> in
  let c = clos_iconf in
  let init_globs = [(num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.next_loc))] in
  (clos_conf, es_chained  ++ init_globs)
End

(* bvl_to_bvi *)
Definition icompile_bvl_to_bvi_inline_def:
  icompile_bvl_to_bvi_inline limit split_seq cut_size cs p =
  bvl_inline$compile_inc limit split_seq cut_size cs p
End

(* TODO: will this result in inefficiencies due to the append code *)
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

(* data_to_word *)
Definition icompile_data_to_word_def:
  icompile_data_to_word data_conf p =
  MAP (compile_part data_conf) p
End

Definition init_icompile_data_to_word_def:
  init_icompile_data_to_word data_conf asm_conf data_init =
  let data_conf =
      (data_conf with <| has_fp_ops := (1 < asm_conf.fp_reg_count);
                         has_fp_tern := (asm_conf.ISA = ARMv7 /\ 2 < asm_conf.fp_reg_count) |>) in
    let stubs1 = icompile_data_to_word data_conf data_init in
    (data_conf, stubs (:'a) data_conf ++ stubs1)
End

(* word_to_stack *)
Definition icompile_word_to_stack_def:
  icompile_word_to_stack asm_conf word_iconf p =
  let k = word_iconf.k in
  let bm = word_iconf.bm in
  let (p, fs, bm') = word_to_stack$compile_word_to_stack asm_conf k p bm in
  let sfs_list = (MAP (λ((i,_),n). (i,n)) (ZIP (p,fs))) in
  let word_iconf = word_iconf with <| bm := bm';
                                      sfs_list := word_iconf.sfs_list ++ sfs_list;
                                      fs:= word_iconf.fs ++ fs |> in
    (word_iconf, p)
End

Definition init_icompile_word_to_stack_def:
  init_icompile_word_to_stack asm_conf word1_init =
  let k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs) in
  let word_iconf = <| k := k;
                      bm := (List [4w], 1);
                      sfs_list := [];
                      fs := [0]
                   |> in
  let (word_iconf, stack_init) = icompile_word_to_stack asm_conf word_iconf word1_init in
  let stack_init =
      (raise_stub_location,raise_stub k) ::
      (store_consts_stub_location,store_consts_stub k) :: stack_init in
    (word_iconf, stack_init)
End

Definition end_icompile_word_to_stack_def:
  end_icompile_word_to_stack asm_conf word_iconf word1_end =
  let (word_iconf, stack_end) = icompile_word_to_stack asm_conf word_iconf word1_end in
  let sfs = fromAList word_iconf.sfs_list in
  let bitmaps = word_iconf.bm in
    (append (FST bitmaps),
       <| bitmaps_length := SND bitmaps;
          stack_frame_size := sfs |>, word_iconf.fs, stack_end)
End

(* stack_to_lab *)
Definition icompile_stack_to_lab_def:
  icompile_stack_to_lab stack_conf offset k p =
  let p = MAP stack_alloc$prog_comp p in
  let p = MAP (stack_remove$prog_comp stack_conf.jump offset k) p in
  let p = MAP (stack_names$prog_comp stack_conf.reg_names) p in
    MAP stack_to_lab$prog_to_section p
End

Definition init_icompile_stack_to_lab_def:
  init_icompile_stack_to_lab stack_conf data_conf max_heap sp offset stack_init =
  let stubs = stack_alloc$compile data_conf [] in
  let stubs = stack_remove$compile stack_conf.jump offset (stack_to_lab$is_gen_gc data_conf.gc_kind)
                                   max_heap sp bvl_to_bvi$InitGlobals_location stubs in
  let stubs = stack_names$compile stack_conf.reg_names stubs in
  let stubs = MAP stack_to_lab$prog_to_section stubs in
  let p = icompile_stack_to_lab stack_conf offset sp stack_init in
    stubs ++ p
End

Definition init_icompile_def:
  init_icompile (asm_conf: 'a asm_config) (c: inc_config) =
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let data_conf = c.inc_data_conf in
  let word_to_word_conf = c.inc_word_to_word_conf in
  let stack_conf = c.inc_stack_conf in
  let (source_iconf, flat_stub) = init_icompile_source_to_flat source_conf in
  let clos_stub = init_icompile_flat_to_clos flat_stub in
  let (clos_iconf, bvl_init) = init_icompile_clos_to_bvl clos_conf clos_stub in
  let (bvl_iconf, bvi_init) = init_icompile_bvl_to_bvi bvl_conf bvl_init in
  let data_init = bvi_to_data$compile_prog bvi_init in
  let (data_conf', word_init) = init_icompile_data_to_word data_conf asm_conf data_init in
  let (_, word_init1) = word_to_word$compile word_to_word_conf asm_conf word_init in
  let (word_iconf, stack_init) = init_icompile_word_to_stack asm_conf word_init1 in
  let max_heap = (2 * data_to_word$max_heap_limit (:'a) data_conf - 1) in
  let lab_init = init_icompile_stack_to_lab stack_conf data_conf
                                            max_heap
                                            (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3))
                                            asm_conf.addr_offset stack_init in
  let ic = <| source_iconf := source_iconf;
              clos_iconf := clos_iconf;
              bvl_iconf := bvl_iconf;
              data_conf := data_conf';
              word_to_word_conf := word_to_word_conf;
              word_iconf := word_iconf;
              stack_conf := stack_conf
           |>
  in
    (ic, lab_init)
End

Definition end_icompile_def:
  end_icompile asm_conf (ic: 'a iconfig) (c : inc_config)
  =
  let source_iconf = ic.source_iconf in
  let clos_iconf = ic.clos_iconf in
  let bvl_iconf = ic.bvl_iconf in
  let data_conf = ic.data_conf in
  let word_to_word_conf = c.inc_word_to_word_conf in
  let word_iconf = ic.word_iconf in
  let stack_conf = c.inc_stack_conf in
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let source_conf_after_ic = end_icompile_source_to_flat source_iconf source_conf in
  let (clos_conf_after_ic, bvl_end) = end_icompile_clos_to_bvl clos_iconf clos_conf in
  let (clos_conf_after_ic_bvi, bvl_conf_after_ic, bvi_end) =
      end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf_after_ic bvl_conf in
  let data_end = bvi_to_data$compile_prog bvi_end in
  let word_end = icompile_data_to_word data_conf data_end in
  let (_, word_end1) = word_to_word$compile word_to_word_conf asm_conf word_end in
  let (bm, w2s_conf, fs, stack_end) = end_icompile_word_to_stack asm_conf word_iconf word_end1 in
  let offset = asm_conf.addr_offset in
  let k = (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3)) in
  let lab_end = icompile_stack_to_lab stack_conf offset k stack_end in
  let c' = c with
             <| inc_source_conf := source_conf_after_ic;
                inc_clos_conf := clos_conf_after_ic_bvi;
                inc_bvl_conf := bvl_conf_after_ic;
                inc_word_conf := w2s_conf |> in
    (c', bm, lab_end)
End

Definition icompile_def:
  icompile (ic:'a iconfig) asm_conf p =
  let source_iconf = ic.source_iconf in
  let clos_iconf = ic.clos_iconf in
  let bvl_iconf = ic.bvl_iconf in
  let data_conf = ic.data_conf in
  let word_to_word_conf = ic.word_to_word_conf in
  let word_conf = ic.word_iconf in
  let stack_conf = ic.stack_conf in
  let p = source_to_source$compile p in
  case icompile_source_to_flat source_iconf p of NONE => NONE
  | SOME (source_iconf', icompiled_p_flat) =>
  let icompiled_p_clos = icompile_flat_to_clos icompiled_p_flat in
  let (clos_iconf', icompiled_p_bvl) = icompile_clos_to_bvl_alt clos_iconf icompiled_p_clos in
  let (bvl_iconf', icompiled_p_bvi) = icompile_bvl_to_bvi bvl_iconf icompiled_p_bvl in
  let icompiled_p_data = bvi_to_data$compile_prog icompiled_p_bvi in
  let icompiled_p_word = icompile_data_to_word data_conf icompiled_p_data in
  let (_, icompiled_p_word1) = word_to_word$compile word_to_word_conf asm_conf icompiled_p_word in
  let (word_iconf', icompiled_p_stack) = icompile_word_to_stack asm_conf word_conf icompiled_p_word1 in
  let offset = asm_conf.addr_offset in
  let k = (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3)) in
  let icompiled_p_lab = icompile_stack_to_lab stack_conf offset k icompiled_p_stack in
  let ic' = ic with <| source_iconf := source_iconf';
                      clos_iconf := clos_iconf';
                      bvl_iconf := bvl_iconf';
                      word_iconf := word_iconf'; |> in

    SOME (ic', icompiled_p_lab)
End

Definition fold_icompile_def:
  fold_icompile ic asm_conf [] =
    icompile ic asm_conf []
  ∧
  fold_icompile ic asm_conf (p :: ps)  =
  case icompile ic asm_conf p of NONE => NONE
  | SOME (ic',  p') =>
    (case fold_icompile ic' asm_conf ps of NONE => NONE
    | SOME (ic'', ps') =>
      SOME (ic'', p' ++ ps'))
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



Theorem clos_to_bvl_compile_prog_top_append:
  clos_to_bvl_compile_prog_top max_app (p1 ++ p2) =
  clos_to_bvl_compile_prog_top max_app p1 ++ clos_to_bvl_compile_prog_top max_app p2
Proof
  rw[clos_to_bvl_compile_prog_top_def]
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

Theorem icompile_clos_to_bvl_max_app_constant_alt:
  icompile_clos_to_bvl_alt c p = (c', p') ⇒
  c.max_app = c'.max_app
Proof
  rw[icompile_clos_to_bvl_alt_def] >>
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


Theorem icompile_icompile_clos_to_bvl_alt:
  icompile_clos_to_bvl_alt clos_iconf p1 = (clos_iconf_p1, p1_bvl) ∧
  icompile_clos_to_bvl_alt clos_iconf_p1 p2 = (clos_iconf_p2, p2_bvl) ⇒
  icompile_clos_to_bvl_alt clos_iconf (p1 ++ p2) = (clos_iconf_p2, p1_bvl ++ p2_bvl)
Proof
  rw[] >>
  drule icompile_clos_to_bvl_max_app_constant_alt >>
  rev_drule icompile_clos_to_bvl_max_app_constant_alt >>
  gvs[icompile_clos_to_bvl_alt_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_icompile_clos_to_bvl_common >>
  disch_then (fn t => last_x_assum assume_tac >> rev_drule t) >>
  rw[clos_to_bvl_compile_prog_top_def]
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


Theorem icompile_icompile_data_to_word:
  icompile_data_to_word data_conf (p1 ++ p2) =
  icompile_data_to_word data_conf p1 ++ icompile_data_to_word data_conf p2
Proof
  rw[icompile_data_to_word_def]
QED

Theorem icompile_icompile_word_to_word:
  word_conf.col_oracle = [] ∧
  word_to_word$compile word_conf asm_conf p1 = (col1, p1') ∧
  word_to_word$compile word_conf asm_conf p2 = (col2, p2') ⇒
  word_to_word$compile word_conf asm_conf (p1 ++ p2) = (col1 ++ col2, p1' ++ p2')
Proof
  rw[word_to_wordTheory.compile_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[word_to_wordTheory.next_n_oracle_def] >>
  every_case_tac >> gvs[] >>
  once_rewrite_tac[GSYM MAP_APPEND] >>
  qspecl_then [‘LENGTH p1’, ‘NONE’] assume_tac (INST_TYPE [alpha |-> “:num sptree$num_map option”] (GSYM LENGTH_REPLICATE)) >>
  qspecl_then [‘LENGTH p2’, ‘NONE’] assume_tac (INST_TYPE [alpha |-> “:num sptree$num_map option”] (GSYM LENGTH_REPLICATE)) >>   rev_drule ZIP_APPEND >> disch_then drule >>
  disch_then (fn t => once_rewrite_tac[t]) >>
  simp[REPLICATE_APPEND]
QED

Theorem compile_word_to_stack_append:
  ∀p1 p2 bs bs1 bs2 fs1 fs2 p1' p2' asm_conf.
  compile_word_to_stack asm_conf k p1 bs = (p1', fs1, bs1) ∧
  compile_word_to_stack asm_conf k p2 bs1 = (p2', fs2, bs2) ⇒
  compile_word_to_stack asm_conf k (p1 ++ p2) bs = (p1' ++ p2', fs1 ++ fs2, bs2)
Proof
  Induct_on ‘p1’ >> rw[word_to_stackTheory.compile_word_to_stack_def] >>
  ntac 2 (pop_assum mp_tac) >>
  namedCases_on ‘h’ ["i n p"] >>
  once_rewrite_tac[word_to_stackTheory.compile_word_to_stack_def] >> simp[] >>
  rpt (pairarg_tac >> simp[]) >>
  ntac 2 strip_tac >> gvs[] >>
  last_x_assum rev_drule >> disch_then drule >>
  rw[]
QED

Theorem compile_word_to_stack_length:
  ∀ k p b p' fs bm' asm_conf.
  compile_word_to_stack asm_conf k p b = (p', fs, bm') ⇒
  LENGTH p' = LENGTH fs
Proof
  Induct_on ‘p’ >>
  rw[word_to_stackTheory.compile_word_to_stack_def] >>
  namedCases_on ‘h’ ["i n p"]  >>
  pop_assum mp_tac >>
  once_rewrite_tac[word_to_stackTheory.compile_word_to_stack_def] >>
  simp[] >> rpt (pairarg_tac >> simp[]) >>
  last_x_assum drule >> rpt strip_tac >>
  rw[LENGTH_CONS]
QED

Theorem icompile_icompile_word_to_stack:
  icompile_word_to_stack asm_conf word_iconf p1 = (word_iconf1, p1') ∧
  icompile_word_to_stack asm_conf word_iconf1 p2 = (word_iconf2, p2') ⇒
  icompile_word_to_stack asm_conf word_iconf (p1 ++ p2) = (word_iconf2, p1' ++ p2')
Proof
  rw[icompile_word_to_stack_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_word_to_stack_append >>
  strip_tac >> gvs[] >>
  rw[fetch "-" "word_iconfig_component_equality"] >>
  pop_assum mp_tac >>
  drule compile_word_to_stack_length >>
  rev_drule compile_word_to_stack_length >>
  ntac 2 strip_tac >>
  drule ZIP_APPEND >>
  disch_then rev_drule >>
  disch_then (fn t => assume_tac (GSYM t)) >>
  rw[]
QED

Theorem icompile_icompile_stack_to_lab:
  icompile_stack_to_lab c offset k p1 = p1' ∧
  icompile_stack_to_lab c offset k p2 = p2' ⇒
  icompile_stack_to_lab c offset k (p1 ++ p2) = (p1' ++ p2')
Proof
  rw[] >>
  gvs[icompile_stack_to_lab_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem icompile_icompile:
  ic.word_to_word_conf.col_oracle = [] ∧
  icompile ic asm_conf prog1 =
    SOME (ic', prog1') ∧
  icompile ic' asm_conf prog2 =
    SOME (ic'', prog2') ⇒
  icompile ic asm_conf (prog1 ++ prog2) =
    SOME (ic'', prog1' ++ prog2')
Proof
  rw[] >>
  gvs[icompile_def] >> rpt (pairarg_tac >> gvs[]) >> rw[source_to_source_compile_append] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all icompile_icompile_source_to_flat >> strip_tac >> gvs[] >>
  fs[icompile_flat_to_clos_and_append_commute] >>
  rev_drule_all icompile_icompile_clos_to_bvl_alt >>
  rpt (strip_tac >> gvs[]) >>
  drule_all icompile_icompile_bvl_to_bvi >>
  rpt (strip_tac >> gvs[]) >>
  rw[bvi_to_dataTheory.compile_prog_def] >> pairarg_tac >> simp[] >>
  pop_assum mp_tac >>
  simp[icompile_icompile_data_to_word] >>
  drule icompile_icompile_word_to_word >> last_x_assum kall_tac >>
  disch_then drule >>
  disch_then rev_drule >> simp[bvi_to_dataTheory.compile_prog_def] >> rw[] >>
  pairarg_tac >> simp[] >>
  pop_assum mp_tac >>
  drule icompile_icompile_word_to_stack >>
  disch_then rev_drule  >> rw[] >>
  simp[icompile_icompile_stack_to_lab]
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

Definition config_prog_rel_s2l_def:
  config_prog_rel_s2l     source_conf_after_ic source_conf_after_c
                          clos_conf_after_c clos_conf_after_ic
                          bvl_conf_after_ic bvl_conf_after_c
                          w2s_conf_after_ic w2s_conf_after_c
                          stack_conf_after_ic stack_conf_after_c
                          bm_after_ic bm_after_c
                          icompiled_p_data_combined compiled_p_data
  =
  (source_conf_after_ic = source_conf_after_c
   ∧
   clos_conf_after_c = clos_conf_after_ic
   ∧
   bvl_conf_after_ic = bvl_conf_after_c
   ∧
   w2s_conf_after_ic = w2s_conf_after_c
   ∧
   bm_after_ic = bm_after_c
   ∧
   stack_conf_after_ic = stack_conf_after_c
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

Definition source_conf_ok_def:
  source_conf_ok source_conf =
  (source_conf.mod_env = source_to_flat$empty_env
  ∧
  source_conf.do_elim = F
  ∧
  source_conf.next.vidx = 0)
End

Theorem init_icompile_icompile_end_icompile_s2f:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub)
  ∧
  icompile_source_to_flat source_iconf p = SOME (source_iconf', icompiled_p)
  ∧
  source_to_flat$compile source_conf p = (source_conf_after_c, compiled_p)
  ∧
  source_conf_ok source_conf
  ⇒
  let source_conf_after_ic = end_icompile_source_to_flat source_iconf' source_conf in
  config_prog_pair_rel source_conf_after_c compiled_p
                       source_conf_after_ic (flat_stub ++ icompiled_p)
Proof
  rw[] >>
  fs[init_icompile_source_to_flat_def,
     icompile_source_to_flat_def,
     source_to_flatTheory.compile_def,
     source_to_flatTheory.compile_prog_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_conf_ok_def] >>
  rw[end_icompile_source_to_flat_def] >>
  rw[extend_env_empty_env, source_to_flatTheory.init_next_vidx_def] >>
  rw[config_prog_pair_rel_def] >>
  rw[source_to_flatTheory.compile_flat_def] >>
  rw[glob_alloc_fixed_def, source_to_flatTheory.glob_alloc_def]
QED


Theorem init_icompile_icompile_end_icompile_f2c:
  (init_icompile_flat_to_clos flat_stub = clos_stub)
  ∧
  (icompile_flat_to_clos flat_p = icompiled_p)
  ∧
  (flat_to_clos$compile_prog (flat_stub ++ flat_p) = compiled_p)
  ⇒
  clos_stub ++ icompiled_p = compiled_p
Proof
  rw[init_icompile_flat_to_clos_def,
     icompile_flat_to_clos_def,
     flat_to_closTheory.compile_prog_def] >>
  once_rewrite_tac[flat_to_clos_compile_decs_cons] >>
  qspecl_then [‘flat_p’, ‘flat_stub’] mp_tac (GEN_ALL flat_to_clos_compile_decs_and_append_commute) >>
  rw[]
QED

Definition clos_conf_ok_def:
  clos_conf_ok clos_conf =
  (clos_conf = clos_to_bvl$default_config)
End

Theorem init_icompile_icompile_end_icompile_c2b:
  init_icompile_clos_to_bvl clos_conf clos_stub = (clos_iconf, bvl_stub)
  ∧
  icompile_clos_to_bvl_alt clos_iconf p = (clos_iconf', p_bvl)
  ∧
  end_icompile_clos_to_bvl clos_iconf' clos_conf = (clos_conf_after_ic, p_bvl_end)
  ∧
  clos_to_bvl_compile_alt clos_conf (clos_stub ++ p) =
  (clos_conf_after_c, compiled_p)
  ∧
  clos_conf_ok clos_conf
   ⇒
  config_prog_pair_rel clos_conf_after_ic (bvl_stub ++ p_bvl ++ p_bvl_end)
                       clos_conf_after_c compiled_p
Proof
  rw[clos_to_bvlTheory.default_config_def,
     init_icompile_clos_to_bvl_def, clos_conf_ok_def] >>
  drule icompile_clos_to_bvl_max_app_constant_alt >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule icompile_icompile_clos_to_bvl_alt >>
  disch_then rev_drule >>
  pop_assum kall_tac >>
  strip_tac >>
  strip_tac >>
  fs[clos_to_bvl_compile_alt_def,
     clos_to_bvl_compile_common_alt_def] >> rpt (pairarg_tac >> gvs[]) >>
  fs[icompile_clos_to_bvl_alt_def,  icompile_clos_to_bvl_common_def] >> rpt (pairarg_tac >> gvs[]) >>
  fs[clos_knownTheory.compile_def, clos_callTheory.compile_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[end_icompile_clos_to_bvl_def, clos_conf_ok_def] >> rpt (pairarg_tac >> gvs[]) >>
  rw[config_prog_pair_rel_def] >>
  rw[clos_annotate_compile_append, clos_to_bvl_compile_prog_top_append]
QED

(*hd
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
*)

Definition bvl_conf_ok_def:
  bvl_conf_ok bvl_conf =
  (bvl_conf = bvl_to_bvi$default_config)
End


Theorem init_icompile_icompile_end_icompile_b2b:
  init_icompile_bvl_to_bvi (bvl_conf: bvl_to_bvi$config) bvl_init = (bvl_iconf, bvi_init)
  ∧
  icompile_bvl_to_bvi bvl_iconf p = (bvl_iconf', p_bvi)
  ∧
  end_icompile_bvl_to_bvi bvl_end bvl_iconf' clos_conf bvl_conf = (clos_conf_after_ic, bvl_conf_after_ic, bvi_end)
  ∧
  bvl_to_bvi_compile_update_config clos_conf bvl_conf (bvl_init ++ p ++ bvl_end)  = (clos_conf_after_c, bvl_conf_after_c, compiled_p_bvi)
  ∧
  bvl_conf_ok bvl_conf ⇒
  config_prog_rel_b2b clos_conf_after_ic bvl_conf_after_ic (bvi_init ++ p_bvi ++ bvi_end)
                      clos_conf_after_c bvl_conf_after_c compiled_p_bvi
Proof
  strip_tac >>
  fs[init_icompile_bvl_to_bvi_def, end_icompile_bvl_to_bvi_def, bvl_conf_ok_def] >>
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

Theorem bvi_to_data_prog_compile_append_all:
  bvi_to_data$compile_prog (bvi_init ++ icompiled_p_bvi ++ bvi_end) =
  bvi_to_data$compile_prog bvi_init ++
  bvi_to_data$compile_prog icompiled_p_bvi ++
  bvi_to_data$compile_prog bvi_end
Proof
  rw[bvi_to_dataTheory.compile_prog_def] >> gvs[]
QED



Theorem init_icompile_icompile_end_icompile_f2c_alt:
  init_icompile_source_to_flat source_conf = (source_iconf, flat_stub) ⇒
  flat_to_clos$compile_prog (flat_stub ++ icompiled_p_flat) =
  init_icompile_flat_to_clos flat_stub ++ icompile_flat_to_clos icompiled_p_flat
Proof
  metis_tac[init_icompile_icompile_end_icompile_f2c]
QED




Theorem init_icompile_icompile_end_icompile_d2w0:
  init_icompile_data_to_word data_conf asm_conf data_init = (data_conf', word0_stub)
  ⇒
  (let icompiled_p_word0 = icompile_data_to_word data_conf' icompiled_p_data in
   let word0_end = icompile_data_to_word data_conf' data_end in
   data_to_word$compile_0 data_conf asm_conf (data_init ++ icompiled_p_data ++ data_end)
   =
   word0_stub ++ icompiled_p_word0 ++ word0_end)
Proof
  rw[init_icompile_data_to_word_def,
     data_to_wordTheory.compile_0_def,
     icompile_data_to_word_def]
QED


Definition word_conf_ok_def:
  word_conf_ok word_conf =
  (word_conf.col_oracle = [])
End



(* for some reason if i dont use a, b, c , i cannot qpat *)
Theorem init_icompile_icompile_end_icompile_d2w1:
  word_conf_ok word_conf ∧
  init_icompile_data_to_word data_conf asm_conf data_init = (data_conf', word_stub) ∧
  word_to_word$compile word_conf asm_conf word_stub = (a, word1_init)
  ∧
  (let icompiled_p_word = icompile_data_to_word data_conf' icompiled_p_data in
   word_to_word$compile word_conf asm_conf icompiled_p_word = (b, icompiled_p_word1))
  ∧
  (let word_end = icompile_data_to_word data_conf' data_end in
   word_to_word$compile word_conf asm_conf word_end = (c, word1_end)) ⇒
  data_to_word$compile data_conf word_conf
                                 asm_conf (data_init ++ icompiled_p_data ++ data_end) =
  (a++b++c, word1_init ++ icompiled_p_word1 ++ word1_end)
Proof
  strip_tac >>
  fs[init_icompile_data_to_word_def, word_conf_ok_def] >>
  once_rewrite_tac[data_to_wordTheory.compile_def] >>
  qpat_x_assum ‘_ = data_conf'’ (fn t => assume_tac (GSYM t)) >>
  gvs[] >>
  drule icompile_icompile_word_to_word >>
  qpat_x_assum ‘compile _ _ _ = (b, _)’ assume_tac >>
  disch_then drule >>
  qpat_x_assum ‘compile _ _ _ = (c, _)’ assume_tac >>
  disch_then drule >>
  strip_tac >>
  drule icompile_icompile_word_to_word >>
  disch_then rev_drule >> disch_then drule >>
  gvs[icompile_data_to_word_def]
QED

Theorem init_icompile_icompile_end_icompile_w12s:
  init_icompile_word_to_stack asm_conf word1_init = (word_iconf, stack_init) ∧
  icompile_word_to_stack asm_conf word_iconf p = (word_iconf', icompiled_p_stack) ∧
  end_icompile_word_to_stack asm_conf word_iconf' word1_end = (bm, w2s_conf_after_ic, fs_after_ic, stack_end) ⇒
  word_to_stack$compile asm_conf (word1_init ++ p ++ word1_end) =
  (bm, w2s_conf_after_ic, fs_after_ic, stack_init ++ icompiled_p_stack ++ stack_end)
Proof
  strip_tac >>
  fs[init_icompile_word_to_stack_def] >>
  pairarg_tac >> gvs[] >>
  drule icompile_icompile_word_to_stack >>
  disch_then rev_drule >>
  rpt (qpat_x_assum ‘icompile_word_to_stack _ _ _ = _’ kall_tac) >>
  strip_tac >>
  fs[end_icompile_word_to_stack_def] >>
  pairarg_tac >> gvs[] >>
  rev_drule icompile_icompile_word_to_stack >>
  disch_then drule >>
  rpt (qpat_x_assum ‘icompile_word_to_stack _ _ _ = _’ kall_tac) >>
  strip_tac >>
  rw[word_to_stackTheory.compile_def] >>
  pairarg_tac >> simp[] >>
  gvs[icompile_word_to_stack_def]
QED

Definition stack_conf_ok_def:
   stack_conf_ok stack_conf =
   (stack_conf.do_rawcall = F)
End

Theorem init_icompile_icompile_end_icompile_stack2l:
  init_icompile_stack_to_lab stack_conf data_conf max_heap sp offset stack_init = lab_init ∧
  icompile_stack_to_lab stack_conf offset sp icompiled_p_stack = icompiled_p_lab ∧
  icompile_stack_to_lab stack_conf offset sp stack_end = lab_end ∧
  stack_to_lab$compile stack_conf data_conf max_heap sp offset (stack_init ++ icompiled_p_stack ++ stack_end) = compiled_p_lab ∧
  stack_conf_ok stack_conf
  ⇒
  compiled_p_lab = (lab_init ++ icompiled_p_lab ++ lab_end)
Proof
  rw[] >>
  fs[init_icompile_stack_to_lab_def,stack_conf_ok_def] >>
  simp[stack_to_labTheory.compile_def,icompile_stack_to_lab_def]>>
  rw[stack_allocTheory.compile_def, stack_removeTheory.compile_def, stack_namesTheory.compile_def]
QED

Definition conf_ok_def:
  conf_ok (c:inc_config) =
  (source_conf_ok c.inc_source_conf
   ∧
   clos_conf_ok c.inc_clos_conf
   ∧
   bvl_conf_ok c.inc_bvl_conf
   ∧
   word_conf_ok c.inc_word_to_word_conf
   ∧
   stack_conf_ok c.inc_stack_conf)
End

Definition config_prog_rel_top_def:
  config_prog_rel_top c1 c2 p1 p2 bm1 bm2

  =
  (c1 = c2 ∧ p1 = p2 ∧ bm1 = bm2)
End

Theorem init_icompile_icompile_end_icompile:
  init_icompile (asm_conf: 'a asm_config) (c: inc_config) =
    (ic, lab_init)
  ∧
  icompile ic asm_conf p = SOME (ic', icompiled_p_lab)
  ∧
  end_icompile asm_conf ic' c = (c_after_ic, bm_after_ic, lab_end)
  ∧
  compile_alt asm_conf c p = (c_after_c, bm_after_c, compiled_p)
  ∧
  conf_ok c
  ⇒
  config_prog_rel_top c_after_ic c_after_c
                      (lab_init ++ icompiled_p_lab ++ lab_end) compiled_p
                      bm_after_ic bm_after_c
Proof
  rw[init_icompile_def, icompile_def, end_icompile_def, compile_alt_def, conf_ok_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all init_icompile_icompile_end_icompile_s2f >>
  simp[config_prog_pair_rel_def] >> strip_tac >>
  gvs[] >>
  drule_all init_icompile_icompile_end_icompile_f2c_alt >>
  strip_tac >> gvs[] >>
  drule_all init_icompile_icompile_end_icompile_c2b >>
  simp[config_prog_pair_rel_def] >> strip_tac >>
  gvs[] >>
  drule_all init_icompile_icompile_end_icompile_b2b >>
  simp[config_prog_rel_b2b_def] >> strip_tac >> gvs[] >>
  drule init_icompile_icompile_end_icompile_d2w1 >> (* change this part.. split d2w1 *)
  simp[] >> ntac 3 (disch_then drule) >> disch_then rev_drule >>
  strip_tac >> gvs[] >>
  ‘bvi_to_data$compile_prog (bvi_init ++ icompiled_p_bvi ++ bvi_end) =
   bvi_to_data$compile_prog bvi_init ++
   bvi_to_data$compile_prog icompiled_p_bvi ++
   bvi_to_data$compile_prog bvi_end’ by rw[bvi_to_dataTheory.compile_prog_def] >> gvs[] >>
  drule_all init_icompile_icompile_end_icompile_w12s >>
  strip_tac >> gvs[] >>
  gvs[config_prog_pair_rel_def] >>
  rw[config_prog_rel_top_def]>>
  metis_tac[init_icompile_icompile_end_icompile_stack2l]
QED

Theorem icompile_none:
  icompile a b p = NONE ⇒
  icompile a b (p ++ p') = NONE
Proof
  rw[icompile_def, source_to_source_compile_append] >>
  rw[icompile_icompile_source_to_flat] >>
  Cases_on ‘icompile_source_to_flat a.source_iconf (compile p)’
  >- (gvs[] >> drule icompile_icompile_source_to_flat_none >> rw[])
  >- (Cases_on ‘x’ >>
      gvs[] >> rpt (pairarg_tac >> gvs[]))
QED

Theorem icompile_none1:
  ∀ a a' b p p'.
  icompile a b p = SOME (a', _) ∧
  icompile a' b p' = NONE ⇒
  icompile a b (p ++ p') = NONE
Proof
  rw[icompile_def, source_to_source_compile_append] >>
  rw[icompile_icompile_source_to_flat] >>
  Cases_on ‘icompile_source_to_flat a.source_iconf (compile p)’ >> gvs[] >>
  namedCases_on ‘x’ ["a' b'"] >>
  gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on ‘icompile_source_to_flat a'' (compile p')’
  >- (gvs[icompile_icompile_source_to_flat_none1])
  >- (namedCases_on ‘x’ ["a'' b''"] >> gvs[] >> rpt (pairarg_tac >> gvs[]))
QED

Theorem fold_icompile_collapse:
  ∀pss ic asm_conf.
  ic.word_to_word_conf.col_oracle = [] ⇒
  fold_icompile ic asm_conf pss =
  icompile ic asm_conf (FLAT pss)
Proof
  Induct >>
  rw[fold_icompile_def] >>
  Cases_on ‘icompile ic asm_conf h’
  >- (simp[] >>
      drule icompile_none >> rw[])
  >- (namedCases_on ‘x’ ["ic' p'"] >>
      simp[] >>
      ‘ic.word_to_word_conf.col_oracle = ic'.word_to_word_conf.col_oracle’
        by (qpat_x_assum ‘icompile ic asm_conf h = SOME (ic', p')’ mp_tac >>
            rw[icompile_def] >>
            Cases_on ‘icompile_source_to_flat ic.source_iconf (compile h)’ >>
            gvs[] >> every_case_tac >> rpt (pairarg_tac >> gvs[])) >>
      Cases_on ‘icompile ic' asm_conf (FLAT pss)’
      >- (rev_drule icompile_none1 >>
          disch_then drule >>
          strip_tac >> gvs[])
      >- (namedCases_on ‘x’ ["ic'' p''"] >> drule_all icompile_icompile >> gvs[]))
QED


Theorem icompile_eq:
  init_icompile (asm_conf: 'a asm_config) (c: inc_config) = (ic, lab_init)
  ∧
  fold_icompile ic asm_conf p = SOME (ic', icompiled_p_lab)
  ∧
  end_icompile asm_conf ic' c = (c_after_ic, bm_after_ic, lab_end)
  ∧
  compile_alt asm_conf c (FLAT p) = (c_after_c, bm_after_c, compiled_p)
  ∧
  conf_ok c
  ⇒
  config_prog_rel_top c_after_ic c_after_c
                      (lab_init ++ icompiled_p_lab ++ lab_end) compiled_p
                      bm_after_ic bm_after_c
Proof
  rpt strip_tac >>
  ‘ic.word_to_word_conf.col_oracle = []’
    by (fs[init_icompile_def, conf_ok_def, word_conf_ok_def] >>
        rpt (pairarg_tac >> gvs[])) >>
  drule fold_icompile_collapse >> strip_tac >>
  ‘icompile ic asm_conf (FLAT p) = SOME (ic', icompiled_p_lab)’ by gvs[] >>
  drule_all init_icompile_icompile_end_icompile >> simp[]
QED

(* livesets *)

(* backend_asmTheory.to_word_0_def *)
Definition to_word_0_alt_def:
  to_word_0_alt asm_conf (c : inc_config) p =
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let data_conf = c.inc_data_conf in
  let p = source_to_source$compile p in
  let (source_conf', compiled_p_flat) =
    source_to_flat$compile source_conf p in
  let compiled_p_clos =
    flat_to_clos$compile_prog compiled_p_flat in
  let (clos_conf', compiled_p_bvl) =
    clos_to_bvl_compile_alt clos_conf compiled_p_clos in
  let (clos_conf', bvl_conf', compiled_p_bvi) =
    bvl_to_bvi_compile_update_config clos_conf' bvl_conf compiled_p_bvl in
  let compiled_p_data =
    bvi_to_data$compile_prog compiled_p_bvi in
  let p_word0 = data_to_word$compile_0 data_conf asm_conf compiled_p_data in
  let c' = c with <| inc_source_conf := source_conf';
                     inc_clos_conf := clos_conf';
                     inc_bvl_conf := bvl_conf' |> in
    (c', p_word0)
End

(* backend_asmTheory.to_livesets_0_def *)
Definition to_livesets_0_alt_def:
  to_livesets_0_alt asm_conf word_conf p =
  let p = word_internal asm_conf p in
  let reg_count = asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs) in
  let alg = word_conf.reg_alg in
  let data = MAP (\(name_num,arg_count,prog).
    let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
    (get_clash_tree prog,heu_moves,spillcosts,
      get_forced asm_conf prog [],get_stack_only prog)) p
  in
    ((reg_count,data),p)
End

(* backend_asmTheory.to_livesets_def *)
Definition to_livesets_alt_def:
  to_livesets_alt asm_conf (c:inc_config) p =
  let (c', pword0) = to_word_0_alt asm_conf c p in
  let ((reg_count, data), pword) =
    to_livesets_0_alt asm_conf c'.inc_word_to_word_conf pword0 in
    (c', (reg_count, data), pword)
End

Theorem to_livesets_0_consts:
  to_livesets_0 asm_conf (c,p,names) = ((a, data), c',names',p') ⇒
  c = c' ∧ names = names'
Proof
  rw[to_livesets_0_def]
QED

Theorem to_livesets_0_append:
  to_livesets_0 asm_conf (c,p1,names1) = ((a, data1), _, _, p1') ∧
  to_livesets_0 asm_conf (c,p2,names2) = ((_, data2),_, _, p2') ⇒
  to_livesets_0 asm_conf (c,p1++p2,names3) =
    ((a,data1++data2), c, names3, p1' ++ p2')
Proof
  rw[to_livesets_0_def]
QED

Theorem to_livesets_0_alt_append:
  to_livesets_0_alt asm_conf word_conf p1 = ((a, data1), p1') ∧
  to_livesets_0_alt asm_conf word_conf p2 = ((_, data2), p2') ⇒
  to_livesets_0_alt asm_conf word_conf (p1 ++ p2) = ((a, data1 ++ data2), p1' ++ p2')
Proof
  rw[to_livesets_0_alt_def, backendTheory.word_internal_def]
QED


Definition icompile_source_to_livesets_def:
  icompile_source_to_livesets asm_conf (ic: 'a iconfig) p =
  let source_iconf = ic.source_iconf in
  let clos_iconf = ic.clos_iconf in
  let bvl_iconf = ic.bvl_iconf in
  let data_conf = ic.data_conf in
  let word_to_word_conf = ic.word_to_word_conf in
  let p = source_to_source$compile p in
  case icompile_source_to_flat source_iconf p of NONE => NONE
  | SOME (source_iconf', icompiled_p_flat) =>
  let icompiled_p_clos = icompile_flat_to_clos icompiled_p_flat in
  let (clos_iconf', icompiled_p_bvl) = icompile_clos_to_bvl_alt clos_iconf icompiled_p_clos in
  let (bvl_iconf', icompiled_p_bvi) = icompile_bvl_to_bvi bvl_iconf icompiled_p_bvl in
  let icompiled_p_data = bvi_to_data$compile_prog icompiled_p_bvi in
  let icompiled_p_word0 = icompile_data_to_word data_conf icompiled_p_data in
  let ((reg_count, data), pword0) =
    to_livesets_0_alt asm_conf word_to_word_conf icompiled_p_word0 in
  let ic' = ic with <| source_iconf := source_iconf';
                      clos_iconf := clos_iconf';
                      bvl_iconf := bvl_iconf'; |> in
    SOME (ic', data, pword0: (num # num # 'a wordLang$prog) list)
End

Definition init_icompile_source_to_livesets_def:
  init_icompile_source_to_livesets (asm_conf: 'a asm_config) (c: inc_config) =
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let data_conf = c.inc_data_conf in
  let word_to_word_conf = c.inc_word_to_word_conf in
  let (source_iconf, flat_stub) = init_icompile_source_to_flat source_conf in
  let clos_stub = init_icompile_flat_to_clos flat_stub in
  let (clos_iconf, bvl_init) = init_icompile_clos_to_bvl clos_conf clos_stub in
  let (bvl_iconf, bvi_init) = init_icompile_bvl_to_bvi bvl_conf bvl_init in
  let data_init = bvi_to_data$compile_prog bvi_init in
  let (data_conf', word0_init) = init_icompile_data_to_word data_conf asm_conf data_init in
  let ((reg_count, data), word0_init_lvs) =
    to_livesets_0_alt asm_conf word_to_word_conf word0_init in
  let ic = <| source_iconf := source_iconf;
              clos_iconf := clos_iconf;
              bvl_iconf := bvl_iconf;
              data_conf := data_conf';
              word_to_word_conf := word_to_word_conf;
              word_iconf := ARB;
              stack_conf := c.inc_stack_conf;
           |>
  in
    (ic, (reg_count, data), word0_init_lvs)
End

Definition end_icompile_source_to_livesets_def:
  end_icompile_source_to_livesets asm_conf ic (c : inc_config)
  =
  let source_iconf = ic.source_iconf in
  let clos_iconf = ic.clos_iconf in
  let bvl_iconf = ic.bvl_iconf in
  let data_conf = ic.data_conf in
  let word_to_word_conf = ic.word_to_word_conf in
  let source_conf = c.inc_source_conf in
  let clos_conf = c.inc_clos_conf in
  let bvl_conf = c.inc_bvl_conf in
  let source_conf_after_ic = end_icompile_source_to_flat source_iconf source_conf in
  let (clos_conf_after_ic, bvl_end) = end_icompile_clos_to_bvl clos_iconf clos_conf in
  let (clos_conf_after_ic_bvi, bvl_conf_after_ic, bvi_end) =
      end_icompile_bvl_to_bvi bvl_end bvl_iconf clos_conf_after_ic bvl_conf in
  let data_end = bvi_to_data$compile_prog bvi_end in
  let word0_end = icompile_data_to_word data_conf data_end in
  let ((reg_count, data), word0_end_lvs) =
    to_livesets_0_alt asm_conf word_to_word_conf word0_end in
  let c' = c with
             <| inc_source_conf := source_conf_after_ic;
                inc_clos_conf := clos_conf_after_ic_bvi;
                inc_bvl_conf := bvl_conf_after_ic |> in
    (c', data, word0_end_lvs)
End


Theorem bvi_to_data_compile_prog_append:
  bvi_to_data$compile_prog (p1 ++ p2) =
  bvi_to_data$compile_prog p1 ++ bvi_to_data$compile_prog p2
Proof
  rw[bvi_to_dataTheory.compile_prog_def]
QED

Theorem icompile_icompile_source_to_livesets:
  icompile_source_to_livesets asm_conf ic p1 = SOME (ic', d1, p1') ∧
  icompile_source_to_livesets asm_conf ic' p2 = SOME (ic'', d2, p2') ⇒
  icompile_source_to_livesets asm_conf ic (p1 ++ p2) = SOME (ic'', d1 ++ d2, p1' ++ p2')
Proof
  rw[icompile_source_to_livesets_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  rw[source_to_source_compile_append] >>
  drule_all icompile_icompile_source_to_flat >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[icompile_flat_to_clos_and_append_commute] >>
  rev_drule_all icompile_icompile_clos_to_bvl_alt >>
  strip_tac >> gvs[] >>
  drule_all icompile_icompile_bvl_to_bvi >>
  strip_tac >> gvs[] >>
  gvs[bvi_to_data_compile_prog_append] >>
  qpat_x_assum ‘_ _ _ = ((_, d1), _)’ assume_tac >>
  drule to_livesets_0_alt_append >>
  qpat_x_assum ‘_ _ _ = ((_, d2), _)’ assume_tac >>
  disch_then drule >>
  gvs[icompile_icompile_data_to_word]
QED

Definition fold_icompile_source_to_livesets_def:
  fold_icompile_source_to_livesets asm_conf ic [] =
    icompile_source_to_livesets asm_conf ic []
  ∧
  fold_icompile_source_to_livesets asm_conf ic (p :: ps)  =
  case icompile_source_to_livesets asm_conf ic p of NONE => NONE
  | SOME (ic', d, p') =>
    (case fold_icompile_source_to_livesets asm_conf ic' ps of NONE => NONE
    | SOME (ic'', d', ps') =>
      SOME (ic'', d ++ d', p' ++ ps'))
End

Theorem icompile_source_to_livesets_none:
  (icompile_source_to_livesets asm_conf ic p = NONE ⇒
   icompile_source_to_livesets asm_conf ic (p ++ p') = NONE)
  ∧
  (icompile_source_to_livesets asm_conf ic p = SOME (ic', some_p) ∧
   icompile_source_to_livesets asm_conf ic' p' = NONE ⇒
   icompile_source_to_livesets asm_conf ic (p ++ p') = NONE)
Proof
  once_rewrite_tac [icompile_source_to_livesets_def] >>
  simp[source_to_source_compile_append] >>
  Cases_on ‘icompile_source_to_flat ic.source_iconf (compile p)’ >> simp[]
  >- (drule icompile_icompile_source_to_flat_none >> strip_tac >> gvs[])
  >- (namedCases_on ‘x’ ["source_iconf' icompiled_p_flat"] >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      Cases_on ‘icompile_source_to_flat ic'.source_iconf (compile p')’ >> gvs[]
      >- (drule_all icompile_icompile_source_to_flat_none1  >> rw[])
      >- (every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[])))
QED

Theorem fold_icompile_source_to_livesets_collapse:
  ∀pss ic.
    fold_icompile_source_to_livesets asm_conf ic pss =
    icompile_source_to_livesets asm_conf ic (FLAT pss)
Proof
  Induct >> rw[fold_icompile_source_to_livesets_def] >>
  Cases_on ‘icompile_source_to_livesets asm_conf ic h’ >> gvs[]
  >- (drule $ CONJUNCT1 icompile_source_to_livesets_none >> rw[])
  >- (namedCases_on ‘x’ ["ic' d p'"] >> simp[] >>
      Cases_on ‘icompile_source_to_livesets asm_conf ic' (FLAT pss)’ >> simp[]
      >- (drule $ CONJUNCT2 icompile_source_to_livesets_none >> rw[])
      >- (namedCases_on ‘x’ ["ic'' d' ps'"] >> simp[] >>
          drule_all icompile_icompile_source_to_livesets >>
          rw[]))
QED

Definition config_prog_rel4_def:
  config_prog_rel4 c1 c2 p1 p2 d1 d2 rc1 rc2=
  (c1 = c2 ∧ p1 = p2 ∧ d1 = d2 ∧ rc1 = rc2)
End

Theorem init_icompile_icompile_end_icompile_s2lvs:
  init_icompile_source_to_livesets asm_conf c = (ic, (reg_count_ic, d_init), word0_init)
  ∧
  icompile_source_to_livesets asm_conf ic p = SOME (ic', d_ic, icompiled_p)
  ∧
  end_icompile_source_to_livesets asm_conf ic' c = (c_after_ic, d_end, word0_end)
  ∧
  to_livesets_alt asm_conf (c:inc_config) p = (c_after_c, (reg_count_c, d_c), compiled_p)
  ∧
  conf_ok c ⇒
  config_prog_rel4 c_after_ic c_after_c
                   (word0_init ++ icompiled_p ++ word0_end) compiled_p
                   (d_init ++ d_ic ++ d_end) d_c
                   reg_count_ic reg_count_c
Proof
  rw[init_icompile_source_to_livesets_def,
     icompile_source_to_livesets_def,
     end_icompile_source_to_livesets_def,
     to_livesets_alt_def,
     to_word_0_alt_def,
     conf_ok_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all init_icompile_icompile_end_icompile_s2f >>
  simp[config_prog_pair_rel_def] >> strip_tac >>
  gvs[] >>
  drule_all init_icompile_icompile_end_icompile_f2c_alt >>
  strip_tac >> gvs[] >>
  drule_all init_icompile_icompile_end_icompile_c2b >>
  simp[config_prog_pair_rel_def] >> strip_tac >>
  gvs[] >>
  drule_all init_icompile_icompile_end_icompile_b2b >>
  simp[config_prog_rel_b2b_def] >> strip_tac >> gvs[] >>
  gvs[bvi_to_data_prog_compile_append_all] >>
  drule init_icompile_icompile_end_icompile_d2w0 >> strip_tac >> gvs[] >>
  qpat_x_assum ‘_ _ _ = ((_, d_init), _)’ assume_tac >> (* weird, it cannot pattern match when given own name *)
  drule to_livesets_0_alt_append >>
  qpat_x_assum ‘_ _ _ = ((_, d_ic), _)’ assume_tac >>
  disch_then drule >> strip_tac >>
  drule to_livesets_0_alt_append >>
  qpat_x_assum ‘_ _ _ = ((_, d_end), _)’ assume_tac >>
  disch_then drule  >>
  strip_tac >> gvs[] >>
  simp[config_prog_rel4_def]
QED

Theorem icompile_eq_s2livesets:
  init_icompile_source_to_livesets asm_conf c = (ic, (reg_count_ic, d_init), word0_init)
  ∧
  fold_icompile_source_to_livesets asm_conf ic p = SOME (ic', d_ic, icompiled_p)
  ∧
  end_icompile_source_to_livesets asm_conf ic' c = (c_after_ic, d_end, word0_end)
  ∧
  to_livesets_alt asm_conf (c:inc_config) (FLAT p) = (c_after_c, (reg_count_c, d_c), compiled_p)
  ∧
  conf_ok c ⇒
  config_prog_rel4 c_after_ic c_after_c
                   (word0_init ++ icompiled_p ++ word0_end) compiled_p
                   (d_init ++ d_ic ++ d_end) d_c
                   reg_count_ic reg_count_c
Proof
  once_rewrite_tac[fold_icompile_source_to_livesets_collapse] >>
  metis_tac[init_icompile_icompile_end_icompile_s2lvs]
QED

val _ = export_theory();
