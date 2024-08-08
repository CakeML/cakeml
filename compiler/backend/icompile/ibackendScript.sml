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


val _ = new_theory"ibackend";

Definition     

    
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

(* TODO: fill the "ARBs" in, the types might be wrong *)
Definition init_icompile_def:
  init_icompile (c: 'a config) =
  let asm_conf = c.lab_conf.asm_conf in
  let (bm, c, p, names) = to_lab c [] in
  (* ignore the names for now *)      
  let ic = config_to_inc_config c in
  (ic, bm, p)
End

Overload bvi_to_data_compile_prog[local] = ``bvi_to_data$compile_prog``
Overload bvl_to_bvi_compile_prog[local] = ``bvl_to_bvi$compile_prog``
Overload bvl_to_bvi_compile_inc[local] = ``bvl_to_bvi$compile_inc``
Overload flat_to_clos_inc_compile[local] = ``flat_to_clos$inc_compile_decs``
       
(* incrementally compile a chunk of source program, a super naive version that probably doesnt work*)
Definition icompile_def:
  icompile (asm_conf: 'a asm_config)
  (ic: inc_config) (prog : ast$dec list) =
  let c = inc_config_to_config asm_conf ic in      
  let p = source_to_source$compile prog in 
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




Definition comile_decs_here:
  compile_decs_here = source_to_flat$compile_decs
End
val _ = EVAL “compile_decs_here []”        
           

(* Random cakeml value got from some example file *)        
Definition decs_to_eval_def:
  decs_to_eval =
  [Dlet unknown_loc (Pvar "it")
     (App Opassign [Var (Short "the_string_ref");
                    Lit (StrLit "eval'd code did this\n")])]
End

(* end icompilation, ready for assembly *)
Definition end_icompile_def:
  end_icompile (asm_conf: 'a asm_config)
    (c: inc_config) = ARB
    
End

(* Virtual fold of icompile over a list of source programs
    and accumulate its output.
   In reality, we run this as separate compile steps *)

Definition fold_icompile_aux_def:
  fold_icompile_aux asm_conf ic [] bm_acc prog_acc = (ic, REV bm_acc, REV prog_acc)
  ∧
  fold_icompile_aux asm_conf ic (prog :: progs') bm_acc prog_acc =
  let (c, bm, prog') = icompile asm_conf ic prog in
  let ic' = config_to_inc_config c in
  fold_icompile_aux asm_conf ic' progs' (bm ++ bm_acc) (prog ++ prog_acc)
End

Definition fold_icompile_def:
  fold_icompile (asm_conf: 'a asm_config)
  (ic: inc_config) (progs : (ast$dec list) list) =
  fold_icompile_aux asm_conf ic progs [] [] 
End

        
(* final theorem should give us a syntactic equality

  TODO: not sure what to do with "names" output of to_lab *)
Theorem icompile_eq:
  init_icompile (c:'a config) = (ic, bm, ip) ∧
  fold_icompile (asm_c:'a asm_config) ic progs = (ic', bm', ip') ∧
  end_icompile asm_c ic' = (ic'', bm'', ip'') ⇒
  to_lab c (FLAT prog) = (
    bm ++ bm' ++ bm'',
    inc_config_to_config asm_c ic'',
    ip ++ ip' ++ ip'',
    ARB
  )
Proof
  cheat
QED

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


(* Testing with empty programs up to source_to_flat *)                                                        
      
Definition icompile_incomplete:
  icompile_incomplete c prog =       
  let p = source_to_source$compile prog in 
  let (c', p) = source_to_flat$compile c.source_conf p in
  let c = c with source_conf := c' in
    c
End

Definition mcompile_incomplete:
  mcompile_incomplete c p =
  let (c, p) = backend$to_flat c p in
  c      
End

Definition init_then_icompile:
  init_then_icompile c p =
  let (c', p') = backend$to_flat c [] in
  icompile_incomplete c' p                             
End

(* we see a discrepency here *)        
val config_from_mcompile = EVAL “(mcompile_incomplete ^(arm8_c_term) []).source_conf” |> rconc 
val config_from_init_then_icompile = EVAL “(init_then_icompile ^(arm8_c_term) []).source_conf” |> rconc 

(* do not increment the vidx *)                   
Definition icompile_to_flat_def:
  icompile_to_flat (c : source_to_flat$config)  p =
  let next = c.next in                    
  let envs = <| next := 0; generation := c.envs.next; envs := LN |> in
  let (_,next,e,gen,p') = compile_decs [] 1n next c.mod_env envs p in
    let envs2 = <| next := c.envs.next + 1;
        env_gens := insert c.envs.next gen.envs c.envs.env_gens |> in
    (c with <| next := next; envs := envs2; mod_env := e |>,
        glob_alloc next c :: alloc_env_ref :: p')
End

val test = EVAL “icompile_to_flat arm8_backend_config.source_conf decs_to_eval”        
            


     
val _ = export_theory();
