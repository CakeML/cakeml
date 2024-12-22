(*
  Define new version of CakeML complier where asm_conf is lifted out to
  be a separate argument and where inc_config is used instead of config.
*)

open preamble backendTheory lab_to_targetTheory backend_enc_decTheory;
open backend_passesTheory evaluate_decTheory;

val _ = new_theory "backend_asm";

(*----------------------------------------------------------------*
    Early passes adjusted to use inc_config
 *----------------------------------------------------------------*)

Definition to_flat_def:
  to_flat c p =
    let p = source_to_source$compile p in
    let (c',p) = source_to_flat$compile c.inc_source_conf p in
    let c = c with inc_source_conf := c' in
      (c,p)
End

Definition to_clos_def:
  to_clos c p =
    let (c,p) = to_flat c p in
    let p = flat_to_clos$compile_prog p in
      (c,p)
End

Definition to_bvl_def:
  to_bvl c p =
    let (c,p) = to_clos c p in
    let (c',p,names) = clos_to_bvl$compile c.inc_clos_conf p in
    let c = c with inc_clos_conf := c' in
      (c,p,names)
End

Definition to_bvi_def:
  to_bvi c p =
    let (c,p,names) = to_bvl c p in
    let (s,p,l,n1,n2,names) =
      bvl_to_bvi$compile c.inc_clos_conf.start c.inc_bvl_conf names p in
    let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
      word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
      stack_remove$stub_names ())) names in
    let c = c with inc_clos_conf updated_by (λc. c with start := s) in
    let c = c with inc_bvl_conf updated_by (λc. c with
                  <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
      (c,p,names)
End

Definition to_data_def:
  to_data c p =
    let (c,p,names) = to_bvi c p in
    let p = bvi_to_data$compile_prog p in
      (c,p,names)
End

Definition to_word_0_def:
  to_word_0 asm_conf c p =
    let (c,p,names) = to_data c p in
    let p = data_to_word$compile_0 c.inc_data_conf asm_conf p in
      (c,p,names)
End

Definition to_livesets_0_def:
  to_livesets_0 asm_conf (c:inc_config,p,names: mlstring num_map) =
  let word_conf = c.inc_word_to_word_conf in
  let alg = word_conf.reg_alg in
  let p =
    MAP (λ(name_num,arg_count,prog).
    let prog = word_simp$compile_exp prog in
    let maxv = max_var prog + 1 in
    let inst_prog = inst_select asm_conf maxv prog in
    let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
    let rm_ssa_prog = remove_dead_prog ssa_prog in
    let cse_prog = word_common_subexp_elim rm_ssa_prog in
    let cp_prog = copy_prop cse_prog in
    let two_prog = three_to_two_reg_prog asm_conf.two_reg_arith cp_prog in
    let unreach_prog = remove_unreach two_prog in
    let rm_prog = remove_dead_prog unreach_prog in
        (name_num,arg_count,rm_prog))
      p in
    let data = MAP (\(name_num,arg_count,prog).
    let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
    (get_clash_tree prog,heu_moves,spillcosts,
      get_forced asm_conf prog [],get_stack_only prog)) p
  in
    ((asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs),data),c,names,p)
End

Definition to_livesets_def:
  to_livesets asm_conf c p =
    to_livesets_0 asm_conf (to_word_0 asm_conf c p)
End

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
        (case c.inc_ffi_names of
         | SOME ffis => (ffis, list_subset current_ffis ffis)
         | _ => (current_ffis,T))
    in
    if ffis_ok then
      case remove_labels c.inc_init_clock asm_conf c.inc_pos c.inc_labels ffis sec_list of
      | SOME (sec_list,l1) =>
          let bytes = prog_to_bytes sec_list in
          let (new_ffis,shmem_infos) = get_shmem_info sec_list c.inc_pos [] [] in
          SOME (bytes,
                c with <| inc_labels := l1;
                          inc_pos := LENGTH bytes + c.inc_pos;
                          inc_sec_pos_len := get_symbols c.inc_pos sec_list;
                          inc_ffi_names := SOME (ffis ++ new_ffis) ;
                          inc_shmem_extra := MAP to_inc_shmem_info shmem_infos |>)
      | NONE => NONE
    else NONE
End

Definition lab_to_target_def:
  lab_to_target asm_conf c sec_list = compile_lab asm_conf c (filter_skip sec_list)
End

Definition attach_bitmaps_def:
  attach_bitmaps names (c:inc_config) data (SOME (code_bytes,c')) =
    (let ffi_names = ffinames_to_string_list (the [] c'.inc_ffi_names) in
     let syms = MAP (λ(n,p,l). (lookup_any n names «NOTFOUND»,p,l))
                    c'.inc_sec_pos_len
     in
       SOME (code_bytes, LENGTH code_bytes,
             data, LENGTH data,
             ffi_names, LENGTH c'.inc_shmem_extra,
             syms, encode_backend_config $ c with
               <| inc_lab_conf := c'; inc_symbols := syms |>)) ∧
  attach_bitmaps names c bm NONE = NONE
End

Definition from_lab_def:
  from_lab (asm_conf :'a asm_config) (c:inc_config) names p bm =
    attach_bitmaps names c bm (lab_to_target asm_conf c.inc_lab_conf p)
End

(*----------------------------------------------------------------*
    Remaining middle passes
 *----------------------------------------------------------------*)

Definition from_stack_def:
  from_stack (asm_conf :'a asm_config) (c :inc_config) names p bm =
    let (c',p) = stack_to_lab$compile
      c.inc_stack_conf c.inc_data_conf (2 * max_heap_limit (:'a) c.inc_data_conf - 1)
      (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs +3))
      (asm_conf.addr_offset) p in
    let c = c with inc_stack_conf := c' in
    from_lab asm_conf c names p bm
End

Definition from_word_def:
  from_word (asm_conf :'a asm_config) (c :inc_config) names p =
    let (bm,c',fs,p) = word_to_stack$compile asm_conf p in
    let c = c with inc_word_conf := c' in
      from_stack asm_conf c names p bm
End

Definition word_alloc_inlogic_def:
  word_alloc_inlogic c prog col_opt =
    let tree = get_clash_tree prog in
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
    case word_to_word_inlogic asm_conf c.inc_word_to_word_conf p of
    | NONE => NONE
    | SOME (col,prog) =>
        let c = c with inc_word_to_word_conf :=
                  (c.inc_word_to_word_conf with col_oracle := col) in
          from_word asm_conf c names prog
End

(*----------------------------------------------------------------*
   End-to-end compiler
 *----------------------------------------------------------------*)

Definition compile_cake_def:
  compile_cake (asm_conf :'a asm_config) (c :inc_config) p =
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
    backend$from_lab (inc_config_to_config asm_conf c) names p bm =
      SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config (config_to_inc_config c1)
Proof
  gvs [from_lab_def,backendTheory.from_lab_def]
  \\ gvs [attach_bitmaps_def |> DefnBase.one_line_ify NONE, AllCaseEqs()] \\ rw []
  \\ gvs [compile_lab_def,lab_to_targetTheory.compile_def,lab_to_target_def,
          lab_to_targetTheory.compile_lab_def,inc_config_to_config_def,
          inc_config_to_config_def,backendTheory.inc_config_to_config_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ pop_assum kall_tac
  \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [backendTheory.attach_bitmaps_def,backendTheory.config_to_inc_config_def,
          lab_to_targetTheory.config_to_inc_config_def]
  \\ AP_TERM_TAC
  \\ gvs [backendTheory.inc_config_component_equality]
  \\ gvs [lab_to_targetTheory.inc_config_component_equality]
QED

Theorem from_stack_thm[local]:
  from_stack asm_conf c names p bm =
  SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ⇒
  ∃c1.
    backend$from_stack (inc_config_to_config asm_conf c) names p bm = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config (config_to_inc_config c1)
Proof
  gvs [from_stack_def,backendTheory.from_stack_def] \\ rw []
  \\ rpt(pairarg_tac \\ gvs[])
  \\ drule from_lab_thm \\ strip_tac
  \\ gvs [backendTheory.inc_config_to_config_def]
  \\ gvs [lab_to_targetTheory.inc_config_to_config_def]
QED

Theorem word_to_word_inlogic_thm[local]:
  word_to_word_inlogic asm_conf c.inc_word_to_word_conf p = SOME (col,prog) ⇒
  compile c.inc_word_to_word_conf asm_conf p = (col,prog)
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
    backend$from_word_0 (inc_config_to_config asm_conf c) names p = SOME (bytes,bm1,c1) ∧
    ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
    syms = c1.symbols ∧
    LENGTH bytes = bytes_len ∧
    LENGTH bm1 = bm1_len ∧
    LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
    conf_str = encode_backend_config (config_to_inc_config c1)
Proof
  gvs [from_word_0_def,from_word_def,AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ gvs [backendTheory.from_word_0_def,backendTheory.from_word_def]
  \\ gvs [backendTheory.inc_config_to_config_def]
  \\ gvs [lab_to_targetTheory.inc_config_to_config_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac word_to_word_inlogic_thm \\ gvs []
  \\ drule from_stack_thm
  \\ strip_tac
  \\ pop_assum $ irule_at Any
  \\ fs [backendTheory.inc_config_to_config_def]
  \\ fs [lab_to_targetTheory.inc_config_to_config_def]
QED

Theorem to_flat_thm[local]:
  to_flat c p = (y0,y1) ∧
  backend$to_flat (inc_config_to_config asm_conf c) p = (z0,z1) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1
Proof
  gvs [to_flat_def,backendTheory.to_flat_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs [backendTheory.inc_config_to_config_def]
QED

Theorem to_clos_thm[local]:
  to_clos c p = (y0,y1) ∧
  backend$to_clos (inc_config_to_config asm_conf c) p = (z0,z1) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1
Proof
  gvs [to_clos_def,backendTheory.to_clos_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ drule_all_then strip_assume_tac to_flat_thm \\ gvs []
QED

Theorem to_bvl_thm[local]:
  to_bvl c p = (y0,y1) ∧
  backend$to_bvl (inc_config_to_config asm_conf c) p = (z0,z1) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1
Proof
  gvs [to_bvl_def,backendTheory.to_bvl_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ drule_all_then strip_assume_tac to_clos_thm \\ gvs []
  \\ gvs [backendTheory.inc_config_to_config_def]
QED

Theorem to_bvi_thm[local]:
  to_bvi c p = (y0,y1) ∧
  backend$to_bvi (inc_config_to_config asm_conf c) p = (z0,z1) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1
Proof
  gvs [to_bvi_def,backendTheory.to_bvi_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ drule_all_then strip_assume_tac to_bvl_thm \\ gvs []
  \\ gvs [backendTheory.inc_config_to_config_def]
QED

Theorem to_data_thm[local]:
  to_data c p = (y0,y1,y2) ∧
  backend$to_data (inc_config_to_config asm_conf c) p = (z0,z1,z2) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1 ∧ y2 = z2
Proof
  gvs [to_data_def,backendTheory.to_data_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ drule_all_then strip_assume_tac to_bvi_thm \\ gvs []
QED

Theorem to_word_0_thm[local]:
  to_word_0 asm_conf c p = (y0,y1,y2) ∧
  backend$to_word_0 (inc_config_to_config asm_conf c) p = (z0,z1,z2) ⇒
  inc_config_to_config asm_conf y0 = z0 ∧ y1 = z1 ∧ y2 = z2
Proof
  gvs [to_word_0_def,backendTheory.to_word_0_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac \\ gvs []
  \\ drule_all_then strip_assume_tac to_data_thm \\ gvs []
  \\ gvs [backendTheory.inc_config_to_config_def]
  \\ gvs [lab_to_targetTheory.inc_config_to_config_def]
QED

Theorem to_livesets_thm:
  ∀asm_conf:'a asm_config.
    to_livesets asm_conf c p = (sets,c1,rest) ⇒
    backend$to_livesets (inc_config_to_config asm_conf c) p =
                        (sets,inc_config_to_config asm_conf c1,rest)
Proof
  rw [to_livesets_def,backendTheory.to_liveset_0_thm]
  \\ ‘∃t. to_word_0 asm_conf c p = t’ by fs [] \\ PairCases_on ‘t’
  \\ ‘∃u. to_word_0 (inc_config_to_config asm_conf c) p = u’ by fs [] \\ PairCases_on ‘u’
  \\ drule_all_then strip_assume_tac to_word_0_thm \\ gvs []
  \\ gvs [to_livesets_0_def,backendTheory.to_livesets_0_def]
  \\ gvs [backendTheory.inc_config_to_config_def]
  \\ gvs [lab_to_targetTheory.inc_config_to_config_def]
  \\ rw [] \\ rpt CASE_TAC
QED

Theorem compile_cake_thm:
  ∀asm_conf:'a asm_config.
    compile_cake asm_conf c p =
    SOME (bytes,bytes_len,bm,bm_len,ffi_names,shmem_len,syms,conf_str) ⇒
    ∃c1.
      backend$compile (inc_config_to_config asm_conf c) p = SOME (bytes,bm,c1) ∧
      ffi_names = ffinames_to_string_list (the [] c1.lab_conf.ffi_names) ∧
      syms = c1.symbols ∧
      LENGTH bytes = bytes_len ∧
      LENGTH bm = bm_len ∧
      LENGTH c1.lab_conf.shmem_extra = shmem_len ∧
      ml_prog$prog_syntax_ok p ∧
      conf_str = encode_backend_config (config_to_inc_config c1)
Proof
  rw [compile_cake_def]
  \\ ‘∃y. to_word_0 asm_conf c p = y’ by fs []
  \\ PairCases_on ‘y’ \\ gvs []
  \\ drule from_word_0_thm \\ strip_tac
  \\ pop_assum $ irule_at Any
  \\ last_x_assum kall_tac
  \\ gvs [backendTheory.compile_oracle_word_0]
  \\ pairarg_tac \\ gvs []
  \\ drule_all to_word_0_thm
  \\ rw [] \\ gvs []
QED

(*----------------------------------------------------------------*
   Explorer for in-logic evaluation of it
 *----------------------------------------------------------------*)

Definition to_flat_all_def:
  to_flat_all (c:inc_config) p =
    let ps = [] in
    let ps = ps ++ [(strlit "original source code",Source p)] in
    let p = source_let$compile_decs p in
    let ps = ps ++ [(strlit "after source_let",Source p)] in
    let (c',p) = source_to_flat$compile_prog c.inc_source_conf p in
    let ps = ps ++ [(strlit "after source_to_flat",Flat p)] in
    let p = flat_elim$remove_flat_prog p in
    let ps = ps ++ [(strlit "after remove_flat",Flat p)] in
    let p = MAP (flat_pattern$compile_dec c'.pattern_cfg) p in
    let ps = ps ++ [(strlit "after flat_pattern",Flat p)] in
    let c = c with inc_source_conf := c' in
      ((ps: (mlstring # 'a any_prog) list),c,p)
End

Definition to_clos_all_def:
  to_clos_all (c:inc_config) p =
    let (ps,c,p) = to_flat_all c p in
    let p = flat_to_clos$compile_prog p in
    let ps = ps ++ [(strlit "after flat_to_clos",Clos p [])] in
      ((ps: (mlstring # 'a any_prog) list),c,p)
End

Definition to_bvl_all_def:
  to_bvl_all (c:inc_config) p =
    let (ps,c,es0) = to_clos_all c p in
    let c0 = c.inc_clos_conf in
    let es = clos_mti$compile c0.do_mti c0.max_app es0 in
    let ps = ps ++ [(strlit "after clos_mti",Clos es [])] in
    let loc = c0.next_loc + MAX 1 (LENGTH es) in
    let loc = if loc MOD 2 = 0 then loc else loc + 1 in
    let (n,es) = clos_number$renumber_code_locs_list loc es in
    let ps = ps ++ [(strlit "after clos_number",Clos es [])] in
    let (kc,es) = clos_known$compile c0.known_conf es in
    let ps = ps ++ [(strlit "after clos_known",Clos es [])] in
    let (es,g,aux) = clos_call$compile c0.do_call es in
    let ps = ps ++ [(strlit "after clos_call",Clos es aux)] in
    let prog = chain_exps c0.next_loc es ++ aux in
    let prog = clos_annotate$compile prog in
    let ps = ps ++ [(strlit "after clos_annotate",Clos [] prog)] in
    let c1 = c0 with
         <|start := c0.next_loc; next_loc := n; known_conf := kc;
           call_state := (g,aux)|> in
    let init_stubs = toAList (init_code c1.max_app) in
    let init_globs =
            [(num_stubs c1.max_app − 1,0,
              init_globals c1.max_app (num_stubs c1.max_app + c1.start))] in
    let comp_progs = clos_to_bvl$compile_prog c1.max_app prog in
    let prog' = init_stubs ++ init_globs ++ comp_progs in
    let func_names =
            make_name_alist (MAP FST prog') prog (num_stubs c1.max_app)
              c0.next_loc (LENGTH es0) in
    let ps = ps ++ [(strlit "after clos_to_bvl",Bvl prog' func_names)] in
    let c2 = c1 with start := num_stubs c1.max_app − 1 in
    let p = code_sort prog' in
    let c = c with inc_clos_conf := c2 in
      ((ps: (mlstring # 'a any_prog) list),c,p,func_names)
End

Definition to_bvi_all_def:
  to_bvi_all (c:inc_config) p =
    let (ps,c,p,names) = to_bvl_all c p in
    let start = c.inc_clos_conf.start in
    let c0 = c.inc_bvl_conf in
    let limit = c0.inline_size_limit in
    let split_seq = c0.split_main_at_seq in
    let cut_size = c0.exp_cut in
    let (inlines,prog1) = bvl_inline$tick_compile_prog limit LN p in
    let prog = MAP (λ(name,arity,exp). (name,arity, HD (remove_ticks [exp]))) prog1 in
    let ps = ps ++ [(strlit "after bvl_inline and remove_ticks",Bvl prog names)] in
    let prog = MAP (λ(name,arity,exp). (name,arity, let_op_sing exp)) prog in
    let ps = ps ++ [(strlit "after let_op_sing",Bvl prog names)] in
    let prog = MAP (λ(name,arity,exp). (name,arity,
                       bvl_handle$compile_any split_seq cut_size arity exp)) prog in
    let ps = ps ++ [(strlit "after bvl_handle",Bvl prog names)] in
    let (loc,code,n1) = bvl_to_bvi$compile_prog start 0 prog in
    let (n2,code') = bvi_tailrec$compile_prog (bvl_num_stubs + 2) code in
    let (s,p,l,n1,n2,names) = (loc,code',inlines,n1,n2,get_names (MAP FST code') names) in
    let names = sptree$union (sptree$fromAList $ (data_to_word$stub_names () ++
      word_to_stack$stub_names () ++ stack_alloc$stub_names () ++
      stack_remove$stub_names ())) names in
    let ps = ps ++ [(strlit "after bvl_to_bvi",Bvi code names)] in
    let ps = ps ++ [(strlit "after bvi_tailrec",Bvi code' names)] in
    let c = c with inc_clos_conf updated_by (λc. c with start := s) in
    let c = c with inc_bvl_conf updated_by
      (λc. c with <| inlines := l; next_name1 := n1; next_name2 := n2 |>) in
     ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Definition to_data_all_def:
  to_data_all (c:inc_config) p =
    let (ps,c,p,names) = to_bvi_all c p in
    let p = MAP (λ(a,n,e). (a,n,FST (compile n (COUNT_LIST n) T [] [e]))) p in
    let ps = ps ++ [(strlit "after bvi_to_data",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,FST (data_live$compile e LN))) p in
    let ps = ps ++ [(strlit "after data_live",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,data_simp$simp e Skip)) p in
    let ps = ps ++ [(strlit "after data_simp",Data p names)] in
    let p = MAP (λ(a,n,e). (a,n,data_space$compile e)) p in
    let ps = ps ++ [(strlit "after data_space",Data p names)] in
      ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Definition to_word_all_def:
  to_word_all asm_conf (c:inc_config) p =
    let (ps,c,p,names) = to_data_all c p in
    let data_conf = c.inc_data_conf in
    let word_conf = c.inc_word_to_word_conf in
    let data_conf =
            data_conf with
            <|has_fp_ops := (1 < asm_conf.fp_reg_count);
              has_fp_tern :=
                (asm_conf.ISA = ARMv7 ∧ 2 < asm_conf.fp_reg_count)|> in
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) p in
    let ps = ps ++ [(strlit "after data_to_word",Word p names)] in
    let (p,ps) = word_internal asm_conf ps names p in
    let reg_count = asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs) in
    let alg = word_conf.reg_alg in
    let (n_oracles,col) = next_n_oracle (LENGTH p) word_conf.col_oracle in
    let p = MAP (λ((name_num,arg_count,prog),col_opt).
              ((name_num,arg_count,
               remove_must_terminate
                 (case word_alloc_inlogic asm_conf prog col_opt of
                  | NONE => Skip
                  | SOME x => x)))) (ZIP (p,n_oracles)) in
    let ps = ps ++ [(strlit "after word_alloc (and remove_must_terminate)",Word p names)] in
    let c = c with inc_word_to_word_conf updated_by (λc. c with col_oracle := col) in
      ((ps: (mlstring # 'a any_prog) list),c,p,names)
End

Definition to_stack_all_def:
  to_stack_all asm_conf (c:inc_config) p =
    let (ps,c,p,names) = to_word_all asm_conf c p in
    let (bm,c',fs,p) = word_to_stack$compile asm_conf p in
    let ps = ps ++ [(strlit "after word_to_stack",Stack p names)] in
    let c = c with inc_word_conf := c' in
      ((ps: (mlstring # 'a any_prog) list),bm,c,p,names)
End

Definition to_lab_all_def:
  to_lab_all (asm_conf:'a asm_config) (c:inc_config) p =
    let (ps,bm,c,p,names) = to_stack_all asm_conf c p in
    let stack_conf = c.inc_stack_conf in
    let data_conf = c.inc_data_conf in
    let max_heap = 2 * max_heap_limit (:'a) c.inc_data_conf - 1 in
    let sp = asm_conf.reg_count - (LENGTH asm_conf.avoid_regs + 3) in
    let offset = asm_conf.addr_offset in
    let prog = stack_rawcall$compile p in
    let ps = ps ++ [(strlit "after stack_rawcall",Stack prog names)] in
    let prog = stack_alloc$compile data_conf prog in
    let ps = ps ++ [(strlit "after stack_alloc",Stack prog names)] in
    let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                 max_heap sp InitGlobals_location prog in
    let ps = ps ++ [(strlit "after stack_remove",Stack prog names)] in
    let prog = stack_names$compile stack_conf.reg_names prog in
    let ps = ps ++ [(strlit "after stack_names",Stack prog names)] in
    let p = MAP prog_to_section prog in
    let ps = ps ++ [(strlit "after stack_to_lab",Lab p names)] in
      ((ps: (mlstring # 'a any_prog) list),bm:'a word list,c,p,names)
End

Definition compile_cake_explore_def:
  compile_cake_explore (asm_conf :'a asm_config) (c :inc_config) p =
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

val _ = export_theory();
