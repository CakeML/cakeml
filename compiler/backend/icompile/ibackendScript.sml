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


        
Definition icompile_source_to_flat_def:
  ARB
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
        
   

        
Definition init_icompile_def:
  init_icompile = ()
End

                          
Definition icompile_def:
  icompile source_config p =
  icompile_source_to_flat source_config p
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
  (source_conf' = c'.source_conf /\
  progs' = ps')                
End
                
Theorem icompile_eq:
  icompile c.source_conf prog = (source_conf', prog') /\
  to_flat c prog = (c', prog'') ==>
  config_prog_rel source_conf' progs'' c' ps'
Proof
  rw [to_flat_def] >>
  fs [source_to_sourceTheory.compile_def, source_letTheory.compile_decs_def] >>
     cheat
QED
        
Theorem icompile_icompile:
  icompile source_conf prog1 = (source_conf', prog1') /\
  icompile source_conf' prog2 = (source_conf'', prog2') ==>
  icompile source_conf (prog1 ++ prog2) = (source_conf'', prog1' ++ prog2')
Proof
  rw[icompile_def, icompile_source_to_flat_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> cheat
       
QED
        
                  
 


        
        
val _ = export_theory();
