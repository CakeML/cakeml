(*
  cv-compute-specific versions of lab_to_target and later passes
  where asm_conf is lifted out. Used for in-logic evaluation by cv_translator.
*)
Theory backend_asm
Ancestors
  backend lab_to_target backend_enc_dec backend_passes
  evaluate_dec
Libs
  preamble


(*----------------------------------------------------------------*
    Adjustments to lab_to_target
 *----------------------------------------------------------------*)

Definition enc_line_def:
  enc_line (c:'a asm_config) skip_len (Label n1 n2 n3) =
    Label n1 n2 skip_len ∧
  enc_line c skip_len (Asm a v0 v1) =
    (let bs = c.encode (cbw_to_asm a) in Asm a bs (LENGTH bs)) ∧
  enc_line c skip_len (LabAsm l v2 v3 v4) =
    (let bs = c.encode (lab_inst 0w l) in LabAsm l 0w bs (LENGTH bs))
End

Definition enc_sec_def:
  enc_sec (c:'a asm_config) skip_len (Section k xs) =
    Section k (MAP (enc_line c skip_len) xs)
End

Definition enc_sec_list_def:
  enc_sec_list (c:'a asm_config) xs =
    let skip_len = LENGTH (c.encode (Inst Skip)) in
      MAP (enc_sec c skip_len) xs
End

Definition enc_lines_again_def:
  (enc_lines_again labs ffis pos c [] (acc,ok) = (REVERSE acc,pos,ok:bool)) /\
  (enc_lines_again labs ffis pos c ((Label k1 k2 l)::xs) (acc,ok) =
     enc_lines_again labs ffis (pos+l) c xs ((Label k1 k2 l)::acc,ok)) /\
  (enc_lines_again labs ffis pos c ((Asm x1 x2 l)::xs) (acc,ok) =
     enc_lines_again labs ffis (pos+l) c xs ((Asm x1 x2 l) :: acc,ok)) /\
  (enc_lines_again labs ffis pos c ((LabAsm a w bytes l)::xs) (acc,ok) =
     let w1 = get_jump_offset a ffis labs pos in
       if w = w1 then
         enc_lines_again labs ffis (pos + l) c xs ((LabAsm a w bytes l)::acc,ok)
       else
         let bs = c.encode (lab_inst w1 a) in
         let l1 = MAX (LENGTH bs) l in
           enc_lines_again labs ffis (pos + l1) c xs
                           ((LabAsm a w1 bs l1)::acc, ok /\ (l1 = l)))
End

Definition enc_secs_again_def:
  enc_secs_again pos labs ffis (c:'a asm_config) [] = ([],T) ∧
  enc_secs_again pos labs ffis c (Section s lines::rest) =
    let (lines1,pos1,ok) = enc_lines_again labs ffis pos c lines ([],T);
        (rest1,ok1) = enc_secs_again pos1 labs ffis c rest
    in (Section s lines1::rest1,ok ∧ ok1)
End

Theorem enc_line_eq[local]:
  lab_to_target$enc_line c.encode skip_len l = enc_line c skip_len l
Proof
  Cases_on ‘l’ \\ gvs [enc_line_def,lab_to_targetTheory.enc_line_def]
QED

Theorem enc_sec_eq[local]:
  lab_to_target$enc_sec c.encode skip_len l = enc_sec c skip_len l
Proof
  Induct_on ‘l’ \\ gvs [enc_sec_def,lab_to_targetTheory.enc_sec_def]
  \\ Induct_on ‘l’ \\ gvs [enc_line_eq]
QED

Theorem enc_sec_list_eq[local]:
  lab_to_target$enc_sec_list c.encode l = enc_sec_list c l
Proof
  Induct_on ‘l’
  \\ gvs [enc_sec_list_def,lab_to_targetTheory.enc_sec_list_def,enc_sec_eq]
QED

Theorem enc_lines_again_eq[local]:
  ∀xs pos acc ok.
    lab_to_target$enc_lines_again labs ffis pos c.encode xs (acc,ok) =
    enc_lines_again labs ffis pos c xs (acc,ok)
Proof
  Induct \\ gvs [enc_lines_again_def,lab_to_targetTheory.enc_lines_again_def]
  \\ Cases \\ gvs [enc_lines_again_def,lab_to_targetTheory.enc_lines_again_def]
QED

Theorem enc_secs_again_eq[local]:
  ∀xs pos labs ffis.
    lab_to_target$enc_secs_again pos labs ffis c.encode xs =
    enc_secs_again pos labs ffis c xs
Proof
  Induct \\ gvs [enc_secs_again_def,lab_to_targetTheory.enc_secs_again_def]
  \\ Cases \\ gvs [enc_secs_again_def,lab_to_targetTheory.enc_secs_again_def]
  \\ gvs [enc_lines_again_eq]
QED

Theorem remove_labels_def =
  lab_to_targetTheory.remove_labels_def |> REWRITE_RULE [enc_sec_list_eq];

Theorem remove_labels_loop_def =
  lab_to_targetTheory.remove_labels_loop_def |> REWRITE_RULE [enc_secs_again_eq]

Definition compile_lab_def:
  compile_lab asm_conf c sec_list =
    let current_ffis = find_ffi_names sec_list in
    let (ffis,ffis_ok) =
        (case c.ffi_names of
         | SOME ffis => (ffis, list_subset current_ffis ffis)
         | _ => (current_ffis,T))
    in
    if ffis_ok then
      case remove_labels c.init_clock asm_conf c.pos c.labels ffis sec_list of
      | SOME (sec_list,l1) =>
          let bytes = prog_to_bytes sec_list in
          let (new_ffis,shmem_infos) = get_shmem_info sec_list c.pos [] [] in
          SOME (bytes,
                c with <| labels := l1;
                          pos := LENGTH bytes + c.pos;
                          sec_pos_len := get_symbols c.pos sec_list;
                          ffi_names := SOME (ffis ++ new_ffis) ;
                          shmem_extra := shmem_infos |>)
      | NONE => NONE
    else NONE
End

Definition lab_to_target_def:
  lab_to_target asm_conf c sec_list = compile_lab asm_conf c (filter_skip sec_list)
End

Definition attach_bitmaps_def:
  attach_bitmaps names (c:config) data (SOME (code_bytes,c')) =
    (let ffi_names = ffinames_to_string_list (the [] c'.ffi_names) in
     let syms = MAP (λ(n,p,l). (lookup_any n names «NOTFOUND»,p,l))
                    c'.sec_pos_len
     in
       SOME (code_bytes, LENGTH code_bytes,
             data, LENGTH data,
             ffi_names, LENGTH c'.shmem_extra,
             syms, encode_backend_config $ c with
               <| lab_conf := c'; symbols := syms |>)) ∧
  attach_bitmaps names c bm NONE = NONE
End

Definition from_lab_def:
  from_lab (asm_conf :'a asm_config) (c:config) names p bm =
    attach_bitmaps names c bm (lab_to_target asm_conf c.lab_conf p)
End

(*----------------------------------------------------------------*
    Remaining middle passes
 *----------------------------------------------------------------*)

Definition from_stack_def:
  from_stack (asm_conf :'a asm_config) (c :config) names p bm =
    let p = stack_to_lab$compile
      c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1)
      (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs +3))
      (asm_conf.addr_offset) p in
    from_lab asm_conf c names p bm
End

Definition from_word_def:
  from_word (asm_conf :'a asm_config) (c :config) names p =
    let (bm,c',fs,p) = word_to_stack$compile asm_conf p in
    let c = c with word_conf := c' in
      from_stack asm_conf c names p bm
End

Definition word_alloc_inlogic_def:
  word_alloc_inlogic c prog col_opt =
    let tree = get_clash_tree prog [] in
    let forced = get_forced c prog [] in
      oracle_colour_ok (c.reg_count − (5 + LENGTH c.avoid_regs))
                       col_opt tree prog forced
End

Definition each_inlogic_def:
  each_inlogic asm_conf [] = SOME [] ∧
  each_inlogic asm_conf (((name_num,arg_count,prog),col_opt)::rest) =
   let prog = compile_exp prog;
       maxv = max_var prog + 1;
       inst_prog = inst_select asm_conf maxv prog;
       ssa_prog = full_ssa_cc_trans arg_count inst_prog;
       rm_ssa_prog = remove_dead_prog ssa_prog;
       cse_prog = word_common_subexp_elim rm_ssa_prog;
       cp_prog = copy_prop cse_prog;
       two_prog = three_to_two_reg_prog asm_conf.two_reg_arith cp_prog;
       unreach_prog = remove_unreach two_prog;
       rm_prog = remove_dead_prog unreach_prog;
   in
     case word_alloc_inlogic asm_conf rm_prog col_opt
     of NONE => NONE
      | SOME reg_prog =>
        case each_inlogic asm_conf rest of
          NONE => NONE
        | SOME progs => SOME ((name_num,arg_count,remove_must_terminate reg_prog) :: progs)
End

Definition word_to_word_inlogic_def:
  word_to_word_inlogic asm_conf word_conf progs =
    let (n_oracles,col) = next_n_oracle (LENGTH progs) word_conf.col_oracle in
    let progs = ZIP (progs,n_oracles) in
      case each_inlogic asm_conf progs of
      | NONE => NONE
      | SOME res => SOME (col,res)
End

Definition from_word_0_def:
  from_word_0 (asm_conf :'a asm_config) (c,p,names) =
    case word_to_word_inlogic asm_conf c.word_to_word_conf p of
    | NONE => NONE
    | SOME (col,prog) =>
        let c = c with word_to_word_conf updated_by
                  (λc. c with col_oracle := col) in
          from_word asm_conf c names prog
End

(*----------------------------------------------------------------*
   End-to-end compiler
 *----------------------------------------------------------------*)

Definition compile_cake_def:
  compile_cake (asm_conf :'a asm_config) (c :config) p =
    if ml_prog$prog_syntax_ok p then
      from_word_0 asm_conf (to_word_0 asm_conf c p)
    else NONE
End

(*----------------------------------------------------------------*
   Correspondence proofs
 *----------------------------------------------------------------*)

Theorem from_lab_thm[local]:
  from_lab asm_conf c names p bm =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_lab asm_conf c names p bm = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_lab_def,backendTheory.from_lab_def]
  \\ gvs [attach_bitmaps_def |> DefnBase.one_line_ify NONE, AllCaseEqs()] \\ rw []
  \\ gvs [compile_lab_def,lab_to_target_def,
          lab_to_targetTheory.compile_def,lab_to_targetTheory.compile_lab_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ pop_assum kall_tac
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [backendTheory.attach_bitmaps_def]
QED

Theorem from_stack_thm[local]:
  from_stack asm_conf c names p bm =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_stack asm_conf c names p bm = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_stack_def,backendTheory.from_stack_def] \\ rw []
  \\ drule from_lab_thm \\ strip_tac \\ gvs []
QED

Theorem word_to_word_inlogic_thm[local]:
  word_to_word_inlogic asm_conf c.word_to_word_conf p = SOME (col,prog) ⇒
  compile c.word_to_word_conf asm_conf p = (col,prog)
Proof
  gvs [word_to_word_inlogic_def,word_to_wordTheory.compile_def]
  \\ pairarg_tac \\ gvs [AllCaseEqs()] \\ rw []
  \\ last_x_assum kall_tac
  \\ pop_assum mp_tac
  \\ qspec_tac (‘ZIP (p,n_oracles)’,‘xs’)
  \\ qid_spec_tac ‘prog’
  \\ Induct_on ‘xs’
  \\ gvs [each_inlogic_def]
  \\ PairCases
  \\ gvs [each_inlogic_def,AllCaseEqs(),word_alloc_inlogic_def]
  \\ rpt strip_tac \\ gvs []
  \\ gvs [word_to_wordTheory.full_compile_single_def]
  \\ gvs [word_to_wordTheory.compile_single_def]
  \\ rw [] \\ gvs [word_allocTheory.word_alloc_def]
QED

Theorem from_word_0_thm[local]:
  from_word_0 asm_conf (c,p,names) =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_word_0 asm_conf c names p = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config c1
Proof
  gvs [from_word_0_def,from_word_def,AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ gvs [backendTheory.from_word_0_def,backendTheory.from_word_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac word_to_word_inlogic_thm \\ gvs []
  \\ drule from_stack_thm
  \\ strip_tac
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem compile_cake_thm:
  ∀asm_conf:'a asm_config.
    compile_cake asm_conf c p =
    SOME (bytes,bytes_len,bm,bm_len,ffi_names,shmem_len,syms,conf_str) ⇒
    ∃c1.
      backend$compile asm_conf c p = SOME (bytes,bm,c1) ∧
      ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
      syms = c1.symbols ∧
      LENGTH bytes = bytes_len ∧
      LENGTH bm = bm_len ∧
      LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
      ml_prog$prog_syntax_ok p ∧
      conf_str = encode_backend_config c1
Proof
  rw [compile_cake_def]
  \\ ‘∃y. to_word_0 asm_conf c p = y’ by fs []
  \\ PairCases_on ‘y’ \\ gvs []
  \\ drule from_word_0_thm \\ strip_tac
  \\ pop_assum $ irule_at Any
  \\ last_x_assum kall_tac
  \\ gvs [backendTheory.compile_oracle_word_0]
QED

(*----------------------------------------------------------------*
   Explorer for in-logic evaluation of it
 *----------------------------------------------------------------*)

Definition to_word_all_def:
  to_word_all asm_conf (c:config) p =
    let (ps,c,p,names) = to_data_all c p in
    let data_conf = c.data_conf in
    let word_conf = c.word_to_word_conf in
    let data_conf =
            data_conf with
            <|has_fp_ops := (1 < asm_conf.fp_reg_count);
              has_fp_tern :=
                (asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count)|> in
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) p in
    let ps = ps ++ [(«after data_to_word»,Word p names)] in
    let (p,ps) = word_internal_all asm_conf ps names p in
    let reg_count = asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs) in
    let alg = word_conf.reg_alg in
    let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
              ((name_num,arg_count,
               remove_must_terminate
                 (case word_alloc_inlogic asm_conf prog col_opt of
                  | NONE => FFI «reg alloc fail» 0 0 0 0 (LN,LN)
                  | SOME x => x)))) (ZIP (p,n_oracles)) in
    let ps = ps ++ [(«after word_alloc (and remove_must_terminate)»,Word p names)] in
    let c = c with word_to_word_conf updated_by (λc. c with col_oracle := col) in
      ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Definition to_stack_all_def:
  to_stack_all asm_conf (c:config) p =
    let (ps,c,p,names) = to_word_all asm_conf c p in
    let (bm,c',fs,p) = word_to_stack$compile asm_conf p in
    let ps = ps ++ [(«after word_to_stack»,Stack p names)] in
    let c = c with word_conf := c' in
      ((ps: (mlstring # 'a any_prog) list),bm,c,p,names)
End

Definition to_lab_all_def:
  to_lab_all (asm_conf:'a asm_config) (c:config) p =
    let (ps,bm,c,p,names) = to_stack_all asm_conf c p in
    let stack_conf = c.stack_conf in
    let data_conf = c.data_conf in
    let max_heap = 2 * max_heap_limit (:'a) c.data_conf - 1 in
    let sp = asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3) in
    let offset = asm_conf.addr_offset in
    let prog = stack_rawcall$compile p in
    let ps = ps ++ [(«after stack_rawcall»,Stack prog names)] in
    let prog = stack_alloc$compile data_conf prog in
    let ps = ps ++ [(«after stack_alloc»,Stack prog names)] in
    let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                 max_heap sp InitGlobals_location prog in
    let ps = ps ++ [(«after stack_remove»,Stack prog names)] in
    let prog = stack_names$compile stack_conf.reg_names prog in
    let ps = ps ++ [(«after stack_names»,Stack prog names)] in
    let p = MAP prog_to_section prog in
    let ps = ps ++ [(«after stack_to_lab»,Lab p names)] in
      ((ps: (mlstring # 'a any_prog) list),bm:'a word list,c,p,names)
End

Definition compile_cake_explore_def:
  compile_cake_explore (asm_conf :'a asm_config) (c :config) p =
    let (ps,bm,c,p,names) = to_lab_all asm_conf c p in
    let p = filter_skip p in
    let ps = ps ++ [(«after filter_skip»,Lab p names)] in
      concat (append (FOLDR (pp_with_title any_prog_pp) Nil ps))
End

(*----------------------------------------------------------------*
   Misc
 *----------------------------------------------------------------*)

Theorem exists_oracle:
  P x ⇒ ∃oracle. P oracle
Proof
  metis_tac []
QED
