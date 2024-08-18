(*
  Defines a new incremental backend which is
  meant to be syntactically equal to backend but allows
  compiling program in a part-by-part manner
*)

open preamble
     backend_asmTheory
     backend_arm8Theory
     to_data_cvTheory
     cv_transLib
     arm8_configTheory;
open backendTheory;

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

  4. assembl/finalize

*)

(* end icompilation, ready for assembly *)
Definition end_icompile_def:
  end_icompile (asm_conf: 'a asm_config)
    (c: inc_config) = ARB
    
End

(* Quick testing *)

(* using the default config for arm8 *)
val c = arm8_backend_config_def |> concl |> lhs
val arm8_ic_term = backendTheory.config_to_inc_config_def
       |> ISPEC c |> CONV_RULE (RAND_CONV EVAL) |> rconc
val arm8_c_term = EVAL c |> rconc


           
                                                
Definition decs_to_eval_def:
  decs_to_eval =
  [Dlet unknown_loc (Pvar "it")
     (App Opassign [Var (Short "the_string_ref");
                    Lit (StrLit "eval'd code did this\n")])]
End

val decs_term = decs_to_eval_def |> concl |> rhs        


Definition icompile_init_v1_def:
  icompile_init_v1 (c: 'a config) =
(* dont need source to source *)
(* dont need source_to_flat, because we return empty config for empty programs, cannot inc compile *) 
(* just do regular flat_to_close$compile_prog to attach interpreter (why) *)
  let p = flat_to_clos$compile_prog [] in
  let (c',p, names) = clos_to_bvl$compile c.clos_conf p in 
  let c = c with clos_conf := c' in
  let (s,p,l,n1,n2,names) = bvl_to_bvi$compile c.clos_conf.start c.bvl_conf names p in
  let c = c with clos_conf updated_by (λc. c with start:=s) in
  let c = c with bvl_conf updated_by (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
  let p = bvi_to_data$compile_prog p in
  let (col,p) = data_to_word$compile c.data_conf c.word_to_word_conf c.lab_conf.asm_conf p in
  let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
  let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
                                                word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
                                                stack_remove$stub_names ())) names in
  let (bm,c',fs,p) = word_to_stack$compile c.lab_conf.asm_conf p in
  let c = c with word_conf := c' in
  let p = stack_to_lab$compile
          c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1)
          (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs +3))
          (c.lab_conf.asm_conf.addr_offset) p
  in (c, bm, p, names)
End

Definition icompile_v1_def:
  icompile_v1 (c: 'a config) p =
  if p = [] then (c, [], [])
  else                   
  let p = source_to_source$compile p in 
  let (c', p) = source_to_flat$compile c.source_conf p in
  let c = c with source_conf := c' in
  let p = flat_to_clos_inc_compile p in
  let (c', p) = clos_to_bvl_compile_inc c.clos_conf p in
  let c = c with clos_conf := c' in
  let (c', p) = bvl_to_bvi_compile_inc_all c.bvl_conf p in
  let c = c with <| bvl_conf := c' |> in
  let p = bvi_to_data_compile_prog p in
  let asm_c = c.lab_conf.asm_conf in
  let dc = ensure_fp_conf_ok asm_c c.data_conf in
  let p = MAP (compile_part dc) p in
  let reg_count1 = asm_c.reg_count - (5 + LENGTH asm_c.avoid_regs) in
  let p = MAP (\p. full_compile_single asm_c.two_reg_arith reg_count1
      c.word_to_word_conf.reg_alg asm_c (p, NONE)) p in
  let bm0 = c.word_conf.bitmaps_length in
  let (p, fs, bm) = compile_word_to_stack reg_count1 p (Nil, bm0) in
  let cur_bm = append (FST bm) in
  let c = c with word_conf := (c.word_conf with bitmaps_length := SND bm) in
  let reg_count2 = asm_c.reg_count - (3 + LENGTH asm_c.avoid_regs) in
  let p = stack_to_lab$compile_no_stubs
      c.stack_conf.reg_names c.stack_conf.jump asm_c.addr_offset
      reg_count2 p in
  (c, cur_bm, p)
End

Definition to_lab_without_names_def:
  to_lab_without_names c p =
  case to_lab c p of
  | (bm, c, p, names) => (c, bm, p)
End
        
        
(* final theorem should give us a syntactic equality

  TODO: not sure what to do with "names" output of to_lab *)
Theorem icompile_eq:
  init_icompile (c:'a config) = (ic, bm, ip) /\
  fold_icompile (asm_c:'a asm_config) ic progs = (ic', bm', ip') /\
  end_icompile asm_c ic' = (ic'', bm'', ip'') ==>
  to_lab c (FLAT prog) = (
    bm ++ bm' ++ bm'',
    inc_config_to_config asm_c ic'',
    ip ++ ip' ++ ip'',
    ARB
  )
Proof
  cheat
QED

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

Triviality append_assoc_rev :
  (h :: (xs ++ ys)) = (h :: xs ++ ys)
Proof
  cheat
QED

Triviality extend_env_assoc:
  extend_env e1 ( extend_env e2 e3) = extend_env (extend_env e1 e2) e3
Proof
  cheat
QED

Triviality extend_env_empty_env:
  extend_env empty_env env = env ∧
  extend_env env empty_env = env
                                
Proof
  rw[source_to_flatTheory.extend_env_def] >> cheat
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
  Cases_on ‘ds’ >- (
  fs[source_to_flatTheory.compile_decs_def] >> gvs[extend_env_empty_env]
  ) >- (
  rw[source_to_flatTheory.compile_decs_def] 
  )              
QED
        
Theorem source_to_flat_compile_decs_lemma:
  ∀ t n next env envs xs ys.
  source_to_flat$compile_decs t n next env envs (xs ++ ys) =
  let (n', next1, new_env1, envs1, xs') = source_to_flat$compile_decs t n next env envs xs in
  let (n'', next2, new_env2, envs2, ys') = source_to_flat$compile_decs t n' next1 (extend_env new_env1 env) envs1 ys in
  (n'', next2, extend_env new_env2 new_env1, envs2, xs' ++ ys')
        
Proof
  Induct_on ‘xs’ >- (
  rw[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[source_to_flatTheory.compile_decs_def]  >> gvs[extend_env_empty_env]      
  ) >- (
  rpt gen_tac >>
  once_rewrite_tac[source_to_flat_compile_decs_lemma_cons] >>
                                       
  rw[] >> rpt (pairarg_tac >> gvs[])  >>
  last_x_assum $ qspecl_then [‘t’, ‘n'³'’, ‘next1'’, ‘(extend_env new_env1' env)’, ‘envs1'’] assume_tac >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum ‘∀ys''.
               compile_decs t n'³' next1' (extend_env new_env1' env) envs1'
                       (xs ++ ys'') =
          (λ(n'',next2,new_env2,envs2,ys').
             (n'',next2,extend_env new_env2 new_env1'',envs2,ds' ++ ys'))
          (compile_decs t n' next1
                        (extend_env new_env1'' (extend_env new_env1' env)) envs1 ys'')’ $ qspec_then ‘ys’ assume_tac >>
  fs[extend_env_assoc] >> gvs[] >> gvs[] >>
  once_rewrite_tac[source_to_flat_compile_decs_lemma_cons] >> gvs[]
   )
QED
        

Definition source_to_flat_compile_prog_alt_def:
  source_to_flat_compile_prog (c: source_to_flat$config) p =
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
  let (c', p') = source_to_flat_compile_prog c p in
  let p' = MAP (flat_pattern$compile_dec c'.pattern_cfg) p' in 
  (c', p')                              
End

Definition to_flat_alt_def:
  to_flat_alt (c: 'a config) p =
  let p = source_to_source$compile p in
  let (c': source_to_flat$config, p) = source_to_flat_compile_alt c.source_conf p in
  let c = c with source_conf := c' in
    (c, p)
End

      

(************************************************************)


   
        
Definition init_icompile_def:
  init_icompile (source_conf : source_to_flat$config) =
  let next = source_conf.next with <| vidx := source_conf.next.vidx + 1 |> in
  let env_gens = <| next := 0; generation := source_conf.envs.next; envs := LN |> in
    <| n := 1n;
       next := next;
       env := source_conf.mod_env;
       env_gens := env_gens;
       pattern_cfg := source_conf.pattern_cfg |> : source_iconfig
                
End

                          
Definition icompile_def:
  icompile (source_iconf : source_iconfig)  p =
  icompile_source_to_flat source_iconf p
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
        
                   
        
                

        
        
Definition fold_icompile_def:
  fold_icompile c []  = (c, [])
  /\
  fold_icompile c (prog :: progs) =
  let (c', prog') = icompile c prog in
    let (c'', progs') = fold_icompile c progs in
      (c'', prog' ++ progs')
        
End

Definition config_prog_rel_def:
  config_prog_rel source_conf' progs' c' ps' =
  progs' = ps'
End


Theorem icompile_icompile:
  icompile source_iconf prog1 = (source_iconf', prog1') /\
  icompile source_iconf' prog2 = (source_iconf'', prog2') ==>
  icompile source_iconf (prog1 ++ prog2) = (source_iconf'', prog1' ++ prog2')
Proof
  rw[icompile_def, icompile_source_to_flat_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qspecl_then [‘[]’,
               ‘source_iconf.n’,
               ‘source_iconf.next’,
               ‘source_iconf.env’,
               ‘source_iconf.env_gens’,
               ‘prog1’,
               ‘prog2’]
              assume_tac
              source_to_flat_compile_decs_lemma >>
  fs[] >> pairarg_tac >> gvs[] >>
  rw[extend_env_assoc]
QED

        
Theorem icompile_eq:
  init_icompile (source_conf : source_to_flat$config) = (source_iconf : source_iconfig) ∧
  icompile source_iconf prog = (source_iconf', icompiled_prog) ∧
  end_icompile source_iconf' source_conf = source_conf' ∧
  to_flat_alt (c : 'a config) prog = (c', compiled_prog) ==>
  config_prog_rel source_conf' icompiled_prog c' compiled_prog
Proof
  rw[] >>
  fs [init_icompile_def, icompile_def, end_icompile_def, icompile_source_to_flat_def] >>
  pairarg_tac >> gvs[] >>              
  fs [to_flat_alt_def, source_to_flat_compile_alt_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[source_to_flat_compile_prog_alt_def] >>
  rpt (pairarg_tac >> gvs[]) >> fs[] >>
  (* more knot tying stuff to happen *)
  >>cheat
  
QED
        




        

val _ = export_theory();
