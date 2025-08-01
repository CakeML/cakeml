(*
  Correctness proof for lab_to_target
*)
open preamble ffiTheory BasicProvers
     wordSemTheory labSemTheory labPropsTheory
     lab_to_targetTheory
     lab_filterProofTheory
     asmTheory asmSemTheory asmPropsTheory
     targetSemTheory targetPropsTheory
local open stack_removeProofTheory in end

val _ = new_theory "lab_to_targetProof";
val drule = old_drule

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)

Triviality evaluate_ignore_clocks:
  evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ r1 <> TimeOut /\
    evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ r2 <> TimeOut ==>
    (r1,ms1,st1) = (r2,ms2,st2)
Proof
  srw_tac[][] \\ imp_res_tac evaluate_add_clock \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (qspec_then `k'` mp_tac)
  \\ pop_assum (qspec_then `k` mp_tac)
  \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM]
QED

Definition sec_loc_to_pc_def:
  (sec_loc_to_pc n2 xs =
   if n2 = 0 then SOME 0
   else case xs of [] => NONE
   | (z::zs) =>
     if (?n1 k. z = Label n1 n2 k) then SOME 0
     else if is_Label z then sec_loc_to_pc n2 zs
     else OPTION_MAP SUC (sec_loc_to_pc n2 zs))
End

val sec_loc_to_pc_ind = theorem"sec_loc_to_pc_ind"

Theorem sec_loc_to_pc_cons:
   sec_loc_to_pc n2 (l::lines) =
   if n2 = 0 ∨ (∃n1 k. l = Label n1 n2 k)then SOME 0
   else OPTION_MAP (if is_Label l then I else SUC) (sec_loc_to_pc n2 lines)
Proof
  rw[Once sec_loc_to_pc_def] \\ fs[]
QED

Overload len_no_lab[local] = ``λxs. LENGTH (FILTER ($~ o is_Label) xs)``

Theorem loc_to_pc_thm:
   ∀n1 n2 ls.
     EVERY sec_labels_ok ls ⇒
     loc_to_pc n1 n2 ls =
       case ls of [] => NONE
       | (Section k xs::ys) =>
         if n1 = k then
           case sec_loc_to_pc n2 xs of
           | NONE => OPTION_MAP ($+ (LENGTH (FILTER ($~ o is_Label) xs))) (loc_to_pc n1 n2 ys)
           | x => x
         else OPTION_MAP ($+ (LENGTH (FILTER ($~ o is_Label) xs))) (loc_to_pc n1 n2 ys)
Proof
  ho_match_mp_tac loc_to_pc_ind
  \\ rw[]
  >- rw[Once loc_to_pc_def]
  >- (
    rw[Once loc_to_pc_def]
    >- ( rw[Once sec_loc_to_pc_def] )
    \\ rw[Once sec_loc_to_pc_def]
    \\ TOP_CASE_TAC \\ fs[plus_0_I]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    >- ( Cases_on`h` \\ fs[] \\ fs[] )
    \\ IF_CASES_TAC \\ fs[] \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[] )
  \\ rw[Once loc_to_pc_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ Cases_on`is_Label h`
  >- ( Cases_on`h` \\ fs[] )
  \\ simp[]
  \\ `¬(∃k. h = Label n1 n2 k)` by (CCONTR_TAC \\ fs[] \\ fs[])
  \\ simp[] \\ rfs[]
  \\ Cases_on`loc_to_pc n1 n2 ls` \\ fs[]
QED

(* -- *)

(* -- evaluate-level semantics preservation of compiler -- *)

(* relate asm step to evaluate step *)

val _ = temp_remove_rules_for_term"step";

Definition enc_with_nop_def:
  enc_with_nop enc (b:'a asm) bytes =
    let init = enc b in
    let step = enc (asm$Inst Skip) in
      if LENGTH step = 0 then bytes = init else
        let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
          bytes = init ++ FLAT (REPLICATE n step)
End

Triviality enc_with_nop_thm:
  enc_with_nop enc (b:'a asm) bytes =
      ?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm$Inst Skip)))
Proof
  fs [enc_with_nop_def,LENGTH_NIL]
  \\ IF_CASES_TAC \\ fs [FLAT_REPLICATE_NIL]
  \\ EQ_TAC \\ rw [] THEN1 metis_tac []
  \\ fs [LENGTH_APPEND,LENGTH_FLAT,map_replicate,SUM_REPLICATE]
  \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,MULT_DIV]
QED

Definition asm_step_nop_def:
  asm_step_nop bytes c s1 i s2 <=>
    bytes_in_memory s1.pc bytes s1.mem s1.mem_domain /\
    enc_with_nop c.encode i bytes /\
    (case c.link_reg of NONE => T | SOME r => s1.lr = r) /\
    (s1.be <=> c.big_endian) /\ s1.align = c.code_alignment /\
    asm i (s1.pc + n2w (LENGTH bytes)) s1 = s2 /\ ~s2.failed /\
    asm_ok i c
End

val evaluate_nop_step =
  asm_step_IMP_evaluate_step
    |> SIMP_RULE std_ss [asm_step_def]
    |> SPEC_ALL |> Q.INST [`i`|->`Inst Skip`]
    |> SIMP_RULE (srw_ss()) [asm_def,inst_def,asm_ok_def,inst_ok_def,
         Once upd_pc_def,GSYM CONJ_ASSOC]

Triviality shift_interfer_0:
  shift_interfer 0 = I
Proof
  full_simp_tac(srw_ss())[shift_interfer_def,FUN_EQ_THM,shift_seq_def,
      machine_config_component_equality]
QED

Triviality upd_pc_with_pc:
  upd_pc s1.pc s1 = s1:'a asm_state
Proof
  full_simp_tac(srw_ss())[asm_state_component_equality,upd_pc_def]
QED

Theorem shift_interfer_twice[simp]:
   shift_interfer l' (shift_interfer l c) =
    shift_interfer (l + l') c
Proof
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,AC ADD_COMM ADD_ASSOC]
QED

Triviality evaluate_nop_steps:
  !n s1 ms1 c.
      encoder_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint c s1
        (n * LENGTH (c.target.config.encode (Inst Skip))) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc
        (FLAT (REPLICATE n (c.target.config.encode (Inst Skip)))) s1.mem
        s1.mem_domain /\
      (case c.target.config.link_reg of NONE => T | SOME r => s1.lr = r) /\
      (s1.be <=> c.target.config.big_endian) /\
      s1.align = c.target.config.code_alignment /\ ~s1.failed /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2.
        !k.
          evaluate c io (k + l) ms1 =
          evaluate (shift_interfer l c) io k ms2 /\
          target_state_rel c.target
            (upd_pc
              (s1.pc +
               n2w (n * LENGTH (c.target.config.encode (Inst Skip)))) s1)
            ms2
Proof
  Induct \\ full_simp_tac(srw_ss())[] THEN1
   (rpt strip_tac \\ Q.LIST_EXISTS_TAC [`0`,`ms1`]
    \\ full_simp_tac(srw_ss())[shift_interfer_0,upd_pc_with_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[REPLICATE,bytes_in_memory_APPEND]
  \\ mp_tac evaluate_nop_step \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (
    fs[ffi_entry_pcs_disjoint_def,IN_DISJOINT,DISJOINT_SUBSET]
    \\ rw[]
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ fs[addressTheory.word_arith_lemma1,MULT_SUC]
    \\ disj2_tac
    \\ strip_tac
    \\ first_x_assum $ qspec_then `a` assume_tac
    \\ disch_then assume_tac
    \\ first_x_assum $ drule_then assume_tac
    \\ rw[]
  )
  \\ strip_tac
  \\ first_x_assum (mp_tac o
       Q.SPECL [`(upd_pc (s1.pc +
          n2w (LENGTH ((c:('a,'state,'b) machine_config).target.config.encode
            (Inst Skip)))) s1)`,`ms2`,`shift_interfer l c`])
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (
    fs[shift_interfer_def,upd_pc_def,interference_ok_def,shift_seq_def,
      ffi_entry_pcs_disjoint_def,IN_DISJOINT,DISJOINT_SUBSET]
    \\ strip_tac
    \\ last_x_assum $ qspec_then `x` assume_tac
    \\ fs[addressTheory.word_arith_lemma1,MULT_SUC]
    \\ disj2_tac
    \\ strip_tac
    \\ first_x_assum $ qspec_then `a + LENGTH (c.target.config.encode (Inst Skip))` assume_tac
    \\ disch_then assume_tac
    \\ first_x_assum $ drule_then assume_tac
    \\ rw[]
  )
  \\ rpt strip_tac
  \\ `(shift_interfer l c).target = c.target` by full_simp_tac(srw_ss())[shift_interfer_def]
  \\ full_simp_tac(srw_ss())[upd_pc_def]
  \\ Q.LIST_EXISTS_TAC [`l'+l`,`ms2'`]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,
       word_add_n2w,AC ADD_COMM ADD_ASSOC,MULT_CLAUSES]
  \\ full_simp_tac(srw_ss())[ADD_ASSOC] \\ rpt strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k`)
  \\ first_x_assum (mp_tac o Q.SPEC `k+l'`)
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ gvs [word_add_n2w]
QED

Theorem ffi_entry_pcs_disjoint_LENGTH_shorter:
!l1 l2.
  ffi_entry_pcs_disjoint c s1 l1 /\
  l2 <= l1 ==>
  ffi_entry_pcs_disjoint c s1 l2
Proof
  rpt strip_tac >>
  fs[ffi_entry_pcs_disjoint_def,IN_DISJOINT] >>
  strip_tac >>
  first_x_assum $ qspec_then `x` assume_tac >>
  fs[] >>
  disj2_tac >>
  strip_tac >>
  disch_then assume_tac >>
  first_x_assum drule >>
  rpt strip_tac >>
  fs[LE_LT1]
QED

Theorem asm_step_IMP_evaluate_step_nop:
   !c s1 ms1 io i s2 bytes.
      encoder_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      ffi_entry_pcs_disjoint c s1 (LENGTH bytes) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc bytes s2.mem s1.mem_domain /\
      asm_step_nop bytes c.target.config s1 i s2 /\
      s2 = asm i (s1.pc + n2w (LENGTH bytes)) s1 /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) /\
      (!x. i <> Call x) ==>
      ?l ms2.
        !k.
          evaluate c io (k + l) ms1 =
          evaluate (shift_interfer l c) io k ms2 /\
          target_state_rel c.target s2 ms2 /\ l <> 0
Proof
  full_simp_tac(srw_ss())[asm_step_nop_def] \\ rpt strip_tac
  \\ (asm_step_IMP_evaluate_step
      |> SIMP_RULE std_ss [asm_step_def] |> SPEC_ALL |> mp_tac) \\ fs[]
  \\ full_simp_tac(srw_ss())[enc_with_nop_thm]
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (conj_tac
    >- (
      fs[LENGTH_APPEND]
      \\ drule ffi_entry_pcs_disjoint_LENGTH_shorter
      \\ disch_then $ qspec_then `LENGTH (c.target.config.encode i)` assume_tac
      \\ fs[])
    \\ fs[bytes_in_memory_APPEND]
    \\ Cases_on `i`
    \\ fs[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def,LET_DEF,assert_def]
    \\ srw_tac[][] \\ fs[] \\ rfs[])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Cases_on `?w. i = Jump w` \\ full_simp_tac(srw_ss())[]
  THEN1 (
    full_simp_tac(srw_ss())[asm_def]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?c n r w. (i = JumpCmp c n r w) /\
                  word_cmp c (read_reg n s1) (reg_imm r s1)` \\ fs[]
  THEN1 (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[asm_def]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?r. (i = JumpReg r)` \\ fs[]
  THEN1 (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[asm_def,LET_DEF]
    \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
    \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[])
  \\ qspecl_then
      [`n`,`asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1`,`ms2`,
       `shift_interfer l c`] mp_tac evaluate_nop_steps
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[shift_interfer_def] \\ rpt strip_tac
    THEN1 (
      fs[ffi_entry_pcs_disjoint_def,IN_DISJOINT]
      \\ Cases_on `i`
      \\ fs[asm_def]
      \\ rw[]
      \\ first_x_assum $ qspec_then `x` assume_tac
      \\ fs[addressTheory.word_arith_lemma1]
      \\ disj2_tac
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ gvs[]
    )
    THEN1 (fs[interference_ok_def,shift_seq_def])
    THEN1
     (Q.ABBREV_TAC
        `mm = (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1).mem`
      \\ full_simp_tac(srw_ss())[Once (asm_mem_ignore_new_pc |> Q.SPECL [`i`,`0w`])]
      \\ `!w. (asm i w s1).pc = w` by (Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def])
      \\ full_simp_tac(srw_ss())[bytes_in_memory_APPEND])
    \\ metis_tac [asm_failed_ignore_new_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Q.LIST_EXISTS_TAC [`l+l'`,`ms2'`]
  \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k:num`)
  \\ qpat_x_assum `!k. xx = yy` (mp_tac o Q.SPEC `k+l':num`)
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[shift_interfer_def]
  \\ qpat_x_assum `target_state_rel c.target xx yy` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x = z) ==> (f x y ==> f z y)``)
  \\ Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def]
  \\ full_simp_tac(srw_ss())[LENGTH_FLAT,SUM_REPLICATE,map_replicate]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ fs [GSYM word_add_n2w]
  THEN1 (Cases_on `i'` \\ full_simp_tac(srw_ss())[inst_def,upd_pc_def]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])
  \\ full_simp_tac(srw_ss())[jump_to_offset_def,upd_pc_def]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
QED

(* define relation between labSem and targetSem states *)

Definition lab_lookup_def:
  lab_lookup k1 k2 labs =
    case lookup k1 labs of
    | NONE => NONE
    | SOME f => lookup k2 f
End

Triviality lab_lookup_IMP:
  (lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)
Proof
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC
QED

Definition labs_domain_def:
  labs_domain labs = { (n1, n2) | lab_lookup n1 n2 labs ≠ NONE }
End

Theorem labs_domain_LN[simp]:
   labs_domain LN = {}
Proof
  EVAL_TAC \\ rw[lookup_def]
QED

Theorem labs_domain_insert:
   k ∉ domain labs ⇒
   labs_domain (insert k s labs) = IMAGE (λn2. (k,n2)) (domain s) ∪ labs_domain labs
Proof
  rw[labs_domain_def,lab_lookup_def, lookup_insert, EXTENSION, EQ_IMP_THM]
  \\ fs[case_eq_thms] \\ fs[domain_lookup]
  \\ metis_tac[NOT_SOME_NONE,option_CASES]
QED


Definition has_odd_inst_def:
  (has_odd_inst [] = F) /\
  (has_odd_inst ((Section k [])::xs) = has_odd_inst xs) /\
  (has_odd_inst ((Section k (y::ys))::xs) <=>
     ~EVEN (line_length y) \/ has_odd_inst ((Section k ys)::xs))
End

Definition line_similar_def:
  (line_similar (Label k1 k2 l) (Label k1' k2' l') <=> (k1 = k1') /\ (k2 = k2')) /\
  (line_similar (Asm b bytes l) (Asm b' bytes' l') <=> (b = b')) /\
  (line_similar (LabAsm a w bytes l) (LabAsm a' w' bytes' l') <=> (a = a')) /\
  (line_similar _ _ <=> F)
End

val line_similar_ind = theorem"line_similar_ind";

Definition code_similar_def:
  (code_similar [] [] = T) /\
  (code_similar ((Section s1 lines1)::rest1) ((Section s2 lines2)::rest2) <=>
     code_similar rest1 rest2 /\
     EVERY2 line_similar lines1 lines2 /\ (s1 = s2)) /\
  (code_similar _ _ = F)
End

val code_similar_ind = theorem "code_similar_ind";

Theorem line_similar_sym:
   line_similar l1 l2 ⇒ line_similar l2 l1
Proof
  Cases_on`l1`>>Cases_on`l2`>>EVAL_TAC>>srw_tac[][]
QED

Theorem code_similar_sym:
   ∀code1 code2. code_similar code1 code2 ⇒ code_similar code2 code1
Proof
  Induct >> simp[code_similar_def]
  >> Cases_on`code2`>>simp[code_similar_def]
  >> Cases >> simp[code_similar_def]
  >> Cases_on`h` >> simp[code_similar_def]
  >> srw_tac[][]
  >> match_mp_tac (GEN_ALL (MP_CANON EVERY2_sym))
  >> metis_tac[line_similar_sym]
QED

Theorem line_similar_refl[simp]:
   ∀l. line_similar l l
Proof
  Cases >> EVAL_TAC
QED

Theorem code_similar_refl[simp]:
   ∀code. code_similar code code
Proof
  Induct >> simp[code_similar_def] >>
  Cases >> simp[code_similar_def] >>
  match_mp_tac EVERY2_refl >> simp[]
QED

Triviality line_similar_trans:
  line_similar x y /\ line_similar y z ==> line_similar x z
Proof
  Cases_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ fs[line_similar_def]
QED

Theorem code_similar_trans:
   !c1 c2 c3. code_similar c1 c2 /\ code_similar c2 c3 ==> code_similar c1 c3
Proof
  HO_MATCH_MP_TAC code_similar_ind \\ fs [] \\ rw []
  \\ Cases_on `c3` \\ fs [code_similar_def] \\ rw []
  \\ Cases_on `h` \\ fs [code_similar_def] \\ rw []
  \\ metis_tac [line_similar_trans,LIST_REL_trans]
QED

Theorem code_similar_nil:
   (code_similar [] l ⇔ l = []) ∧
   (code_similar l [] ⇔ l = [])
Proof
   Cases_on`l`>>EVAL_TAC
QED

Theorem code_similar_append:
  ∀l1 l2 r1 r2.
    code_similar l1 l2 ∧
    code_similar r1 r2 ⇒
    code_similar (l1++r1) (l2++r2)
Proof
  ho_match_mp_tac code_similar_ind>>fs[code_similar_def]
QED

Theorem line_similar_sec_label_ok:
    ∀l1 l2.
  EVERY (sec_label_ok s) l1 /\
  LIST_REL line_similar l1 l2 ⇒
  EVERY (sec_label_ok s) l2
Proof
  Induct>>rw[]>>
  fs[]>>
  Cases_on`h`>>Cases_on`y`>>fs[line_similar_def]
QED

Theorem code_similar_sec_labels_ok:
    ∀c1 c2.
  EVERY sec_labels_ok c1 ∧
  code_similar c1 c2 ⇒
  EVERY sec_labels_ok c2
Proof
  ho_match_mp_tac code_similar_ind>>fs[code_similar_def]>>rw[]>>
  fs[]>>
  metis_tac[line_similar_sec_label_ok]
QED

Theorem line_similar_len_no_lab:
    ∀l1 l2.
  LIST_REL line_similar l1 l2 ⇒
  len_no_lab l1 = len_no_lab l2
Proof
  Induct>>rw[]>>
  res_tac>>fs[]>>
  Cases_on`h`>> Cases_on`y`>>fs[line_similar_def]
QED

Theorem code_similar_len_no_lab:
    ∀(c1:'a labLang$prog) (c2:'a labLang$prog).
  code_similar c1 c2 ⇒
  MAP (len_no_lab ∘ Section_lines) c1 =
  MAP (len_no_lab ∘ Section_lines) c2
Proof
  recInduct code_similar_ind>>
  fs[code_similar_def]>>rw[]>>
  metis_tac[line_similar_len_no_lab]
QED

Definition word_loc_val_def:
  (word_loc_val p labs (Word w) = SOME w) /\
  (word_loc_val p labs (Loc k1 k2) =
     case lab_lookup k1 k2 labs of
     | NONE => NONE
     | SOME q => SOME (p + n2w q))
End

Definition has_io_name_def:
  (has_io_name index [] = F) /\
  (has_io_name index ((Section k [])::xs) = has_io_name index xs) /\
  (has_io_name index ((Section k (y::ys))::xs) <=>
     has_io_name index ((Section k ys)::xs) \/
     case y of LabAsm (CallFFI i) _ _ _ => (i = index) | _ => F)
End

val has_io_name_ind = theorem"has_io_name_ind"

Definition word_loc_val_byte_def:
  word_loc_val_byte p labs m a be =
    case word_loc_val p labs (m (byte_align a)) of
    | SOME w => SOME (get_byte a w be)
    | NONE => NONE
End

Definition line_ok_def:
  (line_ok (c:'a asm_config) labs ffis pos (Label _ _ l) <=>
     EVEN pos /\ (l = 0)) /\
  (line_ok c labs ffis pos (Asm b bytes l) <=>
     enc_with_nop c.encode (cbw_to_asm b) bytes /\
     (LENGTH bytes = l) /\ asm_ok (cbw_to_asm b) c) /\
  (line_ok c labs ffis pos (LabAsm Halt w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + ffi_offset) in
       enc_with_nop c.encode (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c labs ffis pos (LabAsm Install w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + 2 * ffi_offset) in
       enc_with_nop c.encode (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c labs ffis pos (LabAsm (CallFFI index) w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + (3 + get_ffi_index ffis (ExtCall index)) * ffi_offset) in
       enc_with_nop c.encode (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c labs ffis pos (LabAsm (Call v24) w bytes l) <=>
     F (* Call not yet supported *)) /\
  (line_ok c labs ffis pos (LabAsm a w bytes l) <=>
     case get_label a of Lab l1 l2 =>
     (case lab_lookup l1 l2 labs of
       NONE => F
     | SOME t =>
     let w1 = n2w t- n2w pos in
       enc_with_nop c.encode (lab_inst w1 a) bytes /\
       (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c))
End

val line_ok_ind = theorem"line_ok_ind";

Definition lines_ok_def:
  (lines_ok c labs ffis pos [] = T) ∧
  (lines_ok c labs ffis pos (y::ys) ⇔
   line_ok c labs ffis pos y ∧
   lines_ok c labs ffis (pos + line_length y) ys)
End

Definition all_enc_ok_def:
  (all_enc_ok c labs ffis pos [] = T) /\
  (all_enc_ok c labs ffis pos ((Section k [])::xs) <=>
     EVEN pos /\ all_enc_ok c labs ffis pos xs) /\
  (all_enc_ok c labs ffis pos ((Section k (y::ys))::xs) <=>
     line_ok c labs ffis pos y /\
     all_enc_ok c labs ffis (pos + line_length y) ((Section k ys)::xs))
End

val all_enc_ok_ind = theorem"all_enc_ok_ind";

Theorem all_enc_ok_cons:
   ∀ls pos.
   all_enc_ok c labs ffis pos (Section k ls::xs) ⇔
   all_enc_ok c labs ffis (pos + SUM (MAP line_length ls)) xs ∧
   EVEN (pos + SUM (MAP line_length ls)) ∧
   lines_ok c labs ffis pos ls
Proof
  Induct >> srw_tac[][all_enc_ok_def,lines_ok_def] >>
  simp[] >> metis_tac[]
QED

Definition pos_val_def:
  (pos_val i pos [] = (pos:num)) /\
  (pos_val i pos ((Section k [])::xs) = pos_val i pos xs) /\
  (pos_val i pos ((Section k (y::ys))::xs) =
     if is_Label y
     then pos_val i (pos + line_length y) ((Section k ys)::xs)
     else if i = 0:num then pos
          else pos_val (i-1) (pos + line_length y) ((Section k ys)::xs))
End

val pos_val_ind = theorem"pos_val_ind";

Theorem pos_val_0:
   !xs c enc labs ffis pos.
      all_enc_ok c labs ffis pos xs ==> (pos_val 0 pos xs = pos)
Proof
  Induct \\ full_simp_tac(srw_ss())[pos_val_def] \\ Cases_on `h`
  \\ Induct_on `l` \\ full_simp_tac(srw_ss())[pos_val_def,all_enc_ok_def]
  \\ rpt strip_tac  \\ res_tac  \\ srw_tac[][]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[line_ok_def,line_length_def,is_Label_def]
QED

Definition sec_pos_val_def:
  (sec_pos_val i pos [] = NONE) ∧
  (sec_pos_val i pos (y::ys) =
   if is_Label y then
     sec_pos_val i (pos + line_length y) ys
   else if i = 0n then SOME pos
   else sec_pos_val (i-1) (pos + line_length y) ys)
End

Theorem sec_pos_val_too_big:
   ∀i pos lines.
    LENGTH (FILTER ($~ o is_Label) lines) ≤ i ⇒ sec_pos_val i pos lines = NONE
Proof
  Induct_on`lines` \\ rw[sec_pos_val_def]
QED

Theorem EVERY_is_Label_sec_pos_val:
   ∀n pos lines. EVERY is_Label lines ⇒ sec_pos_val n pos lines = NONE
Proof
  Induct_on`lines` \\ rw[sec_pos_val_def]
QED

Triviality pos_val_thm0:
  ∀i pos acc.
    pos_val i pos acc =
      case acc of [] => pos
      | Section k s :: ss =>
        case sec_pos_val i pos s of NONE =>
        pos_val (i - LENGTH (FILTER ($~ o is_Label) s)) (pos + SUM (MAP line_length s)) ss
        | SOME x => x
Proof
  ho_match_mp_tac pos_val_ind
  \\ rw[pos_val_def,sec_pos_val_def,ADD1]
QED

Theorem pos_val_thm:
   (pos_val i pos [] = pos) ∧
   (pos_val i pos (Section k s::ss) =
    case sec_pos_val i pos s of NONE =>
      pos_val (i - LENGTH (FILTER ($~ o is_Label) s)) (pos + SUM (MAP line_length s)) ss
    | SOME x => x)
Proof
  rw[Once pos_val_thm0] \\ rw[Once pos_val_thm0]
QED

Definition good_code_def:
  good_code c labs code ⇔
   EVERY sec_ends_with_label code /\
   EVERY sec_labels_ok code /\
   ALL_DISTINCT (MAP Section_num code) /\
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) code /\
   DISJOINT (domain labs) (set (MAP Section_num code)) ∧
   restrict_nonzero (get_labels code) ⊆ get_code_labels code ∪ labs_domain labs ∧
   all_enc_ok_pre c code
End

Definition num_pcs_def:
  num_pcs [] = (0:num) /\
  num_pcs ((Section _ [])::rest) = num_pcs rest /\
  num_pcs ((Section k (x::xs))::rest) = if is_Label x
    then num_pcs ((Section k xs)::rest)
    else 1 + num_pcs ((Section k xs)::rest)
End

Definition share_mem_domain_code_rel_def:
  share_mem_domain_code_rel mc_conf p code2 (s1_shared_mem_domain: ('a word->bool))
  <=>
    (* whenever the pc is accessing share mem, the pc is in ffi_entry_pcs
    * after mmio_pcs_min_index and the mmio_info for it is correct *)
    (!pc op re a inst len i.
        (asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst len) /\
        mmio_pcs_min_index mc_conf.ffi_names = SOME i)
        ==>
        (?index.
          i <= index /\
          find_index (p + n2w (pos_val pc 0 code2)) mc_conf.ffi_entry_pcs 0 =
            SOME index /\
          (let (name, nb) = get_memop_info op in
            EL index mc_conf.ffi_names = SharedMem name /\
            (ALOOKUP mc_conf.mmio_info index
             = SOME (nb, a, re, p + n2w (pos_val pc 0 code2 + len)))))) /\
     (* if the bytes of the instruction intersect with the ffi_entry_pcs,
     * it must be fetching ShareMem instruction *)
    (!pc line.
      asm_fetch_aux pc code2 = SOME line /\
      (!op re a inst len. line <> Asm (ShareMem op re a) inst len) ==>
      DISJOINT (set mc_conf.ffi_entry_pcs)
        {p + n2w a + n2w (pos_val pc 0 code2) |
          a < LENGTH (line_bytes line)}) /\
     (* restriction for shared memory domain *)
     (!a.
        byte_align a IN s1_shared_mem_domain ==>
        a IN s1_shared_mem_domain) /\
     (mc_conf.shared_addresses = s1_shared_mem_domain)
End

Definition share_mem_state_rel_def:
  share_mem_state_rel mc_conf (s1:('a, 'a lab_to_target$config,'ffi) labSem$state) t1 ms1 <=>
     (* ffi interfers for mapped read/write are ok *)
     (!ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i.
      mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
      i <= index /\ index < LENGTH mc_conf.ffi_names /\
      call_FFI_rel^* s1.ffi st /\
      ALOOKUP mc_conf.mmio_info index = SOME (nb,Addr ad offs,re,pc') /\
      (mc_conf.prog_addresses = t1.mem_domain) ∧
      ad' = mc_conf.target.get_reg ms2 ad + offs /\ (* eval the address value *)
      target_state_rel mc_conf.target
        (t1 with pc := EL index mc_conf.ffi_entry_pcs) ms2 ==>
      (∃op. EL index mc_conf.ffi_names = SharedMem op /\
         (case op of
          | MappedRead =>
        (* If we are doing mapped read, and addresses are fine *)
         ((if nb = 0w
          then (w2n ad' MOD (dimindex (:'a) DIV 8)) = 0 else T) ∧
         (ad' IN mc_conf.shared_addresses) /\
         is_valid_mapped_read (mc_conf.target.get_pc ms2) nb (Addr ad offs) re pc'
           mc_conf.target ms2 mc_conf.prog_addresses /\
         call_FFI st (SharedMem MappedRead)
           [nb]
           (word_to_bytes ad' F) =
           FFI_return new_st new_bytes ==>
          target_state_rel mc_conf.target
            (t1 with
            <|pc := pc'
              ; regs := (\n. if n = re then
                   (word_of_bytes F 0w new_bytes) else t1.regs n)|>)
              (mc_conf.ffi_interfer k (index,new_bytes,ms2)))
          | MappedWrite =>
        (* If we are doing mapped write, and the addresses are fine *)
         ((if nb = 0w
           then (w2n ad' MOD (dimindex (:'a) DIV 8)) = 0 else T) /\
          (ad' IN mc_conf.shared_addresses) /\
          is_valid_mapped_write (mc_conf.target.get_pc ms2) nb (Addr ad offs) re pc'
            mc_conf.target ms2 mc_conf.prog_addresses /\
         call_FFI st (SharedMem MappedWrite)
          [nb]
          ((let w = mc_conf.target.get_reg ms2 re in
              if nb = 0w then word_to_bytes w F
              else word_to_bytes_aux (w2n nb) w F)
           ++ (word_to_bytes ad' F)) =
          FFI_return new_st new_bytes ==>
          target_state_rel mc_conf.target
            (t1 with pc := pc')
            (mc_conf.ffi_interfer k (index,new_bytes,ms2)))
    ))) /\
   (* requirements for location of share memory access pcs *)
   (!index i. mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
      index < LENGTH mc_conf.ffi_names /\ i <= index ==>
      mc_conf.halt_pc <> (EL index mc_conf.ffi_entry_pcs) /\
      mc_conf.ccache_pc <> (EL index mc_conf.ffi_entry_pcs))
End

Definition no_install_or_no_share_mem_def:
  no_install_or_no_share_mem code ffi_names <=>
   (no_share_mem_inst code /\
    EVERY (\x. ∃s. x = ExtCall s) ffi_names) \/
    no_install code
End

(* The code buffer is set-up to immediately follow the current code:
  |---code---|---cb---|
*)
Definition state_rel_def:
  state_rel (mc_conf, code2, labs, p) (s1:('a,'a lab_to_target$config,'ffi) labSem$state) t1 ms1 <=>
    target_state_rel mc_conf.target t1 ms1 /\ good_dimindex (:'a) /\
    (mc_conf.prog_addresses = t1.mem_domain) /\
    ~(mc_conf.halt_pc IN mc_conf.prog_addresses) /\
    ~(mc_conf.ccache_pc IN mc_conf.prog_addresses) /\
    reg_ok s1.ptr_reg mc_conf.target.config /\ (mc_conf.ptr_reg = s1.ptr_reg) /\
    reg_ok s1.len_reg mc_conf.target.config /\ (mc_conf.len_reg = s1.len_reg) /\
    reg_ok s1.ptr2_reg mc_conf.target.config /\ (mc_conf.ptr2_reg = s1.ptr2_reg) /\
    reg_ok s1.len2_reg mc_conf.target.config /\ (mc_conf.len2_reg = s1.len2_reg) /\
    reg_ok s1.link_reg mc_conf.target.config /\
    (* FFI behaves correctly *)
    (?i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ∧
         (∀index. if i ≤ index ∧ index < LENGTH mc_conf.ffi_names
                  then ∃info. ALOOKUP mc_conf.mmio_info index = SOME info
                  else ALOOKUP mc_conf.mmio_info index = NONE)) /\
    (!ms2 k index new_bytes t1 bytes bytes2 st new_st i. (* for normal ffis *)
       mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
       index < i ∧
       read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) ∧
       call_FFI_rel^* s1.ffi st ∧
       call_FFI st (EL index mc_conf.ffi_names) bytes bytes2 = FFI_return new_st new_bytes ∧
       (mc_conf.prog_addresses = t1.mem_domain) ∧
       target_state_rel mc_conf.target
         (t1 with pc := p - n2w ((3 + index) * ffi_offset)) ms2 /\
       aligned mc_conf.target.config.code_alignment (t1.regs s1.link_reg) ==>
       target_state_rel mc_conf.target
         (t1 with
         <|regs := (\a. get_reg_value (s1.io_regs k (EL index mc_conf.ffi_names) a) (t1.regs a) I);
           mem := asm_write_bytearray (t1.regs s1.ptr2_reg) new_bytes t1.mem;
           pc := t1.regs s1.link_reg|>)
        (mc_conf.ffi_interfer k (index,new_bytes,ms2))) /\
    (* clear cache behaves correctly *)
    (∀ms2 t1 k a1 a2.
      target_state_rel mc_conf.target
        (t1 with pc := p - n2w ((2 * ffi_offset))) ms2 /\
      aligned mc_conf.target.config.code_alignment (t1.regs s1.link_reg) ⇒
      target_state_rel mc_conf.target
        (t1 with
          <|regs :=
            (s1.ptr_reg =+ t1.regs s1.ptr_reg)
              (λa. get_reg_value (s1.cc_regs k a) (t1.regs a) I);
            pc := t1.regs s1.link_reg|>)
        (mc_conf.ccache_interfer k (a1,a2,ms2))) /\
    s1.compile = compile_lab ∧
    (no_share_mem_inst code2 ==> (∀k. let (cfg,code) = s1.compile_oracle k in
            good_code mc_conf.target.config cfg.labels code ∧
            no_share_mem_inst code /\
            (* Initial configuration for oracle
               Note: this should not be stated as a record cfg = <|...|>
               because some parts of it can be freely chosen (e.g. the clock)
            *)
            (k = 0 ⇒
            cfg.labels = labs ∧
            cfg.pos = LENGTH (prog_to_bytes code2) ∧
            cfg.asm_conf = mc_conf.target.config ∧
            cfg.ffi_names = SOME(mc_conf.ffi_names)
            ))) ∧
    (!l1 l2 x.
       (lab_lookup l1 l2 labs = SOME x) ==> EVEN x) /\
    ((1w && p) = 0w) /\
    (list_subset
      (FILTER (λx. ∃s. x = ExtCall s) $ find_ffi_names s1.code)
      mc_conf.ffi_names) ∧
    (* this is possibly already implied *)
    EVEN (LENGTH (prog_to_bytes code2)) ∧
    (* FFIs are located at the right positions *)
    (!name i.
        MEM name mc_conf.ffi_names /\
        mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
        get_ffi_index mc_conf.ffi_names name < i ==>
        (∃s. name = ExtCall s) ∧
       ~(p - n2w ((3 + get_ffi_index mc_conf.ffi_names name) * ffi_offset) IN mc_conf.prog_addresses) /\
       ~(p - n2w ((3 + get_ffi_index mc_conf.ffi_names name) * ffi_offset) = mc_conf.halt_pc) /\
       ~(p - n2w ((3 + get_ffi_index mc_conf.ffi_names name) * ffi_offset) = mc_conf.ccache_pc) /\
       (find_index (p - n2w ((3 + get_ffi_index mc_conf.ffi_names name) * ffi_offset))
                   mc_conf.ffi_entry_pcs 0 = SOME (get_ffi_index mc_conf.ffi_names name))) /\
    (* Halt/ClearCache are at the right positions *)
    (p - n2w ffi_offset = mc_conf.halt_pc) /\
    (p - n2w (2*ffi_offset) = mc_conf.ccache_pc) /\
    (* Small interference oracle is okay *)
    interference_ok mc_conf.next_interfer (mc_conf.target.proj t1.mem_domain) /\
    (!l1 l2 x2.
       (loc_to_pc l1 l2 s1.code = SOME x2) ==>
       (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
    (* Relating register *)
    (!r. s1.fp_regs r = t1.fp_regs r) /\
    (!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)) /\
    (* Relating (data) memories *)
    (!a. byte_align a IN s1.mem_domain ==>
         a IN t1.mem_domain /\ a IN s1.mem_domain /\
         (word_loc_val_byte p labs s1.mem a s1.be = SOME (t1.mem a))) /\
    (* Remaining space for code buffer exists *)
    (∀n.
      n < s1.code_buffer.space_left ⇒
      let addr = s1.code_buffer.position + n2w (LENGTH (s1.code_buffer.buffer) + n) in
      addr ∈ t1.mem_domain ∧
      addr ∉ s1.mem_domain ) ∧
    (* Position of code memory *)
    bytes_in_mem p (prog_to_bytes code2)
      t1.mem t1.mem_domain s1.mem_domain /\
    (* Position of code buffer pointer *)
    s1.code_buffer.position = p + n2w (LENGTH (prog_to_bytes code2)) /\
    (* Code buffer's bytes are in the right position *)
    bytes_in_mem s1.code_buffer.position s1.code_buffer.buffer
      t1.mem t1.mem_domain s1.mem_domain /\
    (* Code buffer writes do not overwrite memory *)
    LENGTH (prog_to_bytes code2) + LENGTH s1.code_buffer.buffer + s1.code_buffer.space_left < dimword(:'a) /\
    (* code buffer does not intersect with ffi_entry_pcs *)
    (∀bn.
      bn < LENGTH s1.code_buffer.buffer + s1.code_buffer.space_left ==>
      ~MEM (s1.code_buffer.position + n2w bn) mc_conf.ffi_entry_pcs ) /\
    ~s1.failed /\ ~t1.failed /\ (s1.be = t1.be) /\
    (t1.pc = p + n2w (pos_val s1.pc 0 code2)) /\
    ((p && n2w (2 ** t1.align - 1)) = 0w) /\
    (case mc_conf.target.config.link_reg of NONE => T | SOME r => t1.lr = r) /\
    (t1.be <=> mc_conf.target.config.big_endian) /\
    (t1.align = mc_conf.target.config.code_alignment) /\
    (enc_ok mc_conf.target.config) ∧
    all_enc_ok mc_conf.target.config labs
      (TAKE (THE $ mmio_pcs_min_index mc_conf.ffi_names) mc_conf.ffi_names) 0 code2 /\
    EVERY sec_labels_ok code2 /\
    code_similar s1.code code2 /\
    share_mem_state_rel mc_conf s1 t1 ms1 /\
    share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain /\
    LENGTH mc_conf.ffi_names = LENGTH mc_conf.ffi_entry_pcs /\
    no_install_or_no_share_mem code2 mc_conf.ffi_names
End

Theorem state_rel_clock:
  state_rel x s1 t1 ms ==>
    state_rel x (s1 with clock := k) (t1) ms
Proof
  PairCases_on `x`
  \\ full_simp_tac(srw_ss())[state_rel_def, share_mem_state_rel_def]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[]
  \\ TRY (
    Q.MATCH_GOALSUB_RENAME_TAC `~ MEM _ _.ffi_entry_pcs`
    \\ qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` mp_tac
    \\ simp[] )
  \\ metis_tac[]
QED

Theorem share_mem_state_rel_shift_interfer:
  share_mem_state_rel mc_conf s1 t1 x ==>
    share_mem_state_rel (mc_conf with next_interfer := (λi. mc_conf.next_interfer (i + l)))
      s1 t1 x
Proof
  rpt strip_tac
  \\ fs[share_mem_state_rel_def]
  \\ metis_tac[]
QED

Theorem share_mem_domain_code_rel_shift_interfer:
  share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain ==>
  share_mem_domain_code_rel
    (mc_conf with next_interfer := (λi. mc_conf.next_interfer (i + l)))
    p code2 s1.shared_mem_domain
Proof
  rpt strip_tac >> fs[share_mem_domain_code_rel_def] >>
  metis_tac[]
QED

Theorem state_rel_shift_interfer:
  state_rel (mc_conf,code2,labs,p) s1 t1 x ==>
    state_rel (shift_interfer l mc_conf,code2,labs,p) s1 t1 x
Proof
  full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def]
  \\ rpt strip_tac \\ gvs[]
  \\ gvs[interference_ok_def,shift_seq_def,
    share_mem_state_rel_shift_interfer,share_mem_domain_code_rel_shift_interfer]
  >- (first_x_assum irule
    \\ fs[read_ffi_bytearrays_def, read_ffi_bytearray_def]
    \\ metis_tac[])
  >- metis_tac[]
QED

(* bytes_in_memory lemmas *)
Triviality prog_to_bytes_lemma:
  !code2 code1 pc i pos.
      code_similar code1 code2 /\
      all_enc_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names pos code2 /\
      (asm_fetch_aux pc code1 = SOME i) ==>
      ?bs j bs2.
        (prog_to_bytes code2 = bs ++ line_bytes j ++ bs2) /\
        (LENGTH bs + pos = pos_val pc pos code2) /\
        (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc+1) pos code2) /\
        line_similar i j /\
        line_ok mc_conf.target.config labs ffi_names (pos_val pc pos code2) j
Proof
  HO_MATCH_MP_TAC asm_code_length_ind \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,all_enc_ok_def] \\ metis_tac [])
  \\ Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on`l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def]
  \\ rpt var_eq_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `line_similar x1 x2`
  \\ Q.MATCH_ASSUM_RENAME_TAC `LIST_REL line_similar ys1 ys2`
  \\ `is_Label x2 = is_Label x1` by
    (Cases_on `x1` \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_similar_def,is_Label_def])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `is_Label x1` \\ full_simp_tac(srw_ss())[]
  THEN1
   (full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
    \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def] \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[line_length_def,line_bytes_def]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (full_simp_tac(srw_ss())[listTheory.LENGTH_NIL] \\ qexists_tac `x2`
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF,all_enc_ok_def] \\ full_simp_tac(srw_ss())[pos_val_0]
    \\ imp_res_tac pos_val_0
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `x2`
    \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def,line_bytes_def,line_length_def] \\ srw_tac[][])
  \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
  \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 ++ bs`,
        `j`,`bs2`] \\ full_simp_tac(srw_ss())[] \\ `pc - 1 + 1 = pc` by decide_tac
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
QED

val prog_to_bytes_lemma = prog_to_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [];

Triviality bytes_in_mem_APPEND:
  !xs ys a m md md1.
      bytes_in_mem a (xs ++ ys) m md md1 <=>
      bytes_in_mem a xs m md md1 /\
      bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,ADD1,GSYM word_add_n2w,CONJ_ASSOC]
QED

Theorem bytes_in_mem_UPDATE:
   ∀ls a m md md2 w1 w2.
  (∀n. n < LENGTH ls ⇒
    a + n2w n ≠ w1) /\
  bytes_in_mem a ls m md md2 ⇒
  bytes_in_mem a ls ((w1 =+ w2) m) md md2
Proof
  Induct>>fs[bytes_in_mem_def]>>rw[]
  >-
    (first_x_assum (qspec_then `0` assume_tac)>>
    rfs[APPLY_UPDATE_THM])
  >>
  first_x_assum match_mp_tac>>rw[]>>
  first_x_assum (qspec_then `n+1` assume_tac)>>
  rfs[GSYM word_add_n2w]
QED

val s1 = ``s1:('a,'a lab_to_target$config,'ffi) labSem$state``;

Triviality IMP_bytes_in_memory:
  code_similar code1 code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_mem p (prog_to_bytes code2) m (dm:'a word set) dm1 ==>
    ?j.
      bytes_in_mem (p + n2w (pos_val pc 0 code2)) (line_bytes j) m dm dm1 /\
      line_ok (mc_conf:('a,'state,'b) machine_config).target.config
        labs ffi_names (pos_val pc 0 code2) j /\
      (pos_val (pc+1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j)) /\
      line_similar i j
Proof
  rpt strip_tac
  \\ mp_tac prog_to_bytes_lemma \\ fs[] \\ rpt strip_tac
  \\ fs[bytes_in_mem_APPEND]
  \\ Q.EXISTS_TAC `j` \\ fs[] \\ decide_tac
QED

Triviality IMP_bytes_in_memory_JumpReg:
  code_similar s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi (JumpReg r1)) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.target.config.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm] \\ srw_tac[][] \\ fs[]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
val lab_thms = get_thms ``:lab``
val option_thms = get_thms ``:'a option``
val case_eq_thms0 = map prove_case_eq_thm [lab_thms, option_thms]
val bool_case_eq_thms = map (fn th =>
  let val v = th |> concl |> lhs |> rhs
  in th |> GEN v |> Q.ISPEC`T` |> SIMP_RULE bool_ss [] end) case_eq_thms0

Triviality IMP_bytes_in_memory_Jump:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Triviality IMP_bytes_in_memory_JumpCmp:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.config.encode (JumpCmp cmp rr ri tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Triviality IMP_bytes_in_memory_JumpCmp_1:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (JumpCmp cmp rr ri tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def]
  \\ rveq
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF,get_label_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ Q.EXISTS_TAC `l'` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[line_bytes_def]
  \\ rveq \\ fs[lab_inst_def]
  \\ metis_tac[]
QED

Triviality IMP_bytes_in_memory_Call:
  code_similar ^s1.code code2 /\
    all_enc_ok
      (mc_conf: ('a,'state,'b) machine_config).target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem
      (t1:'a asm_state).mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n)) ==>
    F
Proof
  rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ imp_res_tac IMP_bytes_in_memory
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def] \\ rev_full_simp_tac(srw_ss())[]
QED

Triviality IMP_bytes_in_memory_LocValue:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos (Lab l1 l2) labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.config.encode (Loc reg tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Loc reg tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ Q.EXISTS_TAC `l'` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][] \\ metis_tac[]
QED

Triviality IMP_bytes_in_memory_Inst:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Asmi(Inst i)) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.config.encode (Inst i) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst i) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n` \\ fs[]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]
QED

Triviality IMP_bytes_in_memory_Cbw:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Cbw r1 r2) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.config.encode (Inst (Mem Store8 r2 (Addr r1 0w))) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst (Mem Store8 r2 (Addr r1 0w))) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l` \\ fs[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n` \\ fs[]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]
QED

Triviality IMP_bytes_in_memory_CallFFI:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (CallFFI name) l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + (3 + get_ffi_index ffi_names (ExtCall name)) * ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Triviality IMP_bytes_in_memory_Halt:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Halt l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ fs[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Triviality IMP_bytes_in_memory_Install:
  code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Install c l n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + 2 * ffi_offset)) /\
      (enc = mc_conf.target.config.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  fs[asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`m`,`dm`,`i`,`dm1`]) \\ fs[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs[line_similar_def] \\ srw_tac[][]
  \\ fs[line_ok_def,enc_with_nop_thm] \\ srw_tac[][]
  \\ fs[lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ fs[]
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]
QED

Theorem all_enc_ok_asm_fetch_aux_IMP_line_ok:
  !pc n code2.
    all_enc_ok c labs ffis n code2 /\
    asm_fetch_aux pc code2 = SOME line ==>
    line_ok c labs ffis (pos_val pc n code2) line
Proof
  ho_match_mp_tac pos_val_ind >>
  rpt strip_tac
  >- gvs[asm_fetch_aux_def]
  >- gvs[asm_fetch_aux_def,all_enc_ok_def,pos_val_def]
  >- (
    Cases_on `y` >>
    fs[is_Label_def,all_enc_ok_def,line_ok_def,pos_val_def,asm_fetch_aux_def] >>
    Cases_on `pc` >>
    fs[] >>
    Cases_on `a` >>
    gvs[line_ok_def])
QED

Theorem code_similar_IMP_asm_fetch_aux_line_similar:
  !pc code1 code2.
    code_similar code1 code2 ==>
    OPTREL line_similar (asm_fetch_aux pc code1) (asm_fetch_aux pc code2)
Proof
  ho_match_mp_tac asm_fetch_aux_ind >>
  rpt strip_tac >>
  Cases_on `code2` >>
  fs[code_similar_def] >>
  Cases_on `h` >>
  fs[code_similar_def,line_similar_def,asm_fetch_aux_def] >>
  Cases_on `y` >>
  Cases_on `y'` >>
  fs[line_similar_def,asm_fetch_aux_def,code_similar_def] >>
  Cases_on `pc` >>
  fs[line_similar_def,code_similar_def,asm_fetch_aux_def]
QED

Theorem asm_fetch_aux_pos_val_LENGTH_EQ:
!pc n code2 line.
  asm_fetch_aux pc code2 = SOME line /\
  all_enc_ok conf labs ffi_names n code2 /\
  pos_val (pc + 1) n code2 = LENGTH bytes' + pos_val pc n code2 ==>
  LENGTH (line_bytes line) = LENGTH (bytes': word8 list)
Proof
  ho_match_mp_tac pos_val_ind >>
  rpt strip_tac
  >- gvs[asm_fetch_aux_def]
  >- gvs[all_enc_ok_def, pos_val_def,asm_fetch_aux_def]
  >- (
    Cases_on `y` >> gvs[is_Label_def]
    >- gvs[pos_val_def,all_enc_ok_def,asm_fetch_aux_def] >>
    Cases_on `pc` >>
    gvs[line_length_def,all_enc_ok_def,pos_val_def,line_ok_def,asm_fetch_aux_def] >>
    drule pos_val_0 >>
    gvs[])
QED

Theorem IMP_bytes_in_memory_ShareMem:
  (asm_fetch_aux s1.pc s1.code = SOME (Asm (ShareMem mop r ad) l n)) /\
  code_similar ^s1.code code2 /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
  bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain
  ==>
  ?bytes.
    asm_fetch_aux s1.pc code2 = SOME (Asm (ShareMem mop r ad)
      bytes (LENGTH bytes)) /\
    enc_with_nop mc_conf.target.config.encode (Inst (Mem mop r ad)) bytes /\
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      bytes t1.mem t1.mem_domain /\
    bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      bytes t1.mem t1.mem_domain s1.mem_domain /\
    (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
    asm_ok (Inst (Mem mop r ad)) (mc_conf: ('a,'state,'b) machine_config).target.config
Proof
  rpt strip_tac
  \\ drule_all IMP_bytes_in_memory
  \\ rpt strip_tac
  \\ Cases_on `j` >> gvs[line_similar_def,line_ok_def,enc_with_nop_thm]
  \\ rw[PULL_EXISTS]
  \\ imp_res_tac bytes_in_mem_IMP
  \\ qexists `n''`
  \\ fs[asm_fetch_aux_def,prog_to_bytes_def,line_bytes_def,
    bytes_in_mem_APPEND,line_length_def]
  \\ drule_all $ GEN_ALL code_similar_IMP_asm_fetch_aux_line_similar
  \\ disch_then $ qspec_then `s1.pc` assume_tac o REWRITE_RULE[OPTREL_def]
  \\ gvs[AllCaseEqs()]
  \\ drule_all $ GEN_ALL all_enc_ok_asm_fetch_aux_IMP_line_ok
  \\ Cases_on `y0`
  \\ gvs[line_similar_def,line_ok_def, cbw_to_asm_def]
  \\ strip_tac
  \\ `l' = mc_conf.target.config.encode (Inst (Mem mop r ad)) ++
        FLAT (REPLICATE n'' (mc_conf.target.config.encode (Inst Skip)))`
     suffices_by gvs[]
  \\ qabbrev_tac
     `bytes = mc_conf.target.config.encode (Inst (Mem mop r ad)) ++
        FLAT (REPLICATE n'' (mc_conf.target.config.encode (Inst Skip)))`
  \\ drule $ GEN_ALL asm_fetch_aux_pos_val_LENGTH_EQ
  \\ disch_then imp_res_tac
  \\ first_x_assum $ qspec_then `bytes` mp_tac
  \\ impl_tac
  >- (qunabbrev_tac `bytes` >> fs[LENGTH_APPEND])
  \\ strip_tac
  \\ qunabbrev_tac `bytes`
  \\ gvs[line_length_def,enc_with_nop_thm,FLAT_REPLICATE_NIL]
QED

Triviality bytes_in_mem_IMP_memory:
  !xs a.
      (!a. ~(a IN dm1) ==> m a = m1 a) ==>
      bytes_in_mem a xs m dm dm1 ==>
      bytes_in_memory a xs m1 dm
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_memory_def,bytes_in_mem_def]
QED

(* read/write bytearrays for FFI *)

Triviality read_bytearray_state_rel:
  !n a x.
      state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
      (read_bytearray a n (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)
Proof
  Induct
  \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux s1.mem s1.mem_domain s1.be a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (a + 1w) n (mem_load_byte_aux s1.mem s1.mem_domain s1.be)` \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def,mem_load_byte_aux_def]
  \\ Cases_on `s1.mem (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ FIRST_X_ASSUM (Q.SPEC_THEN `a` mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_byte_def,word_loc_val_def]
QED

Triviality IMP_has_io_name:
  (asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_name index s1.code
Proof
  full_simp_tac(srw_ss())[asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`)
  \\ Q.SPEC_TAC (`s1.code`,`code`)
  \\ HO_MATCH_MP_TAC asm_code_length_ind \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,has_io_name_def] \\ res_tac
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  THEN1 (Cases_on `y` \\ full_simp_tac(srw_ss())[is_Label_def] \\ res_tac)
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[]
QED

Triviality bytes_in_mem_asm_write_bytearray_lemma:
  !xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def]
QED

Triviality bytes_in_mem_asm_write_bytearray:
  (∀a. byte_align a ∈ s1.mem_domain ⇒ a ∈ s1.mem_domain) ∧
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) ==>
    bytes_in_mem p xs t1.mem t1.mem_domain s1.mem_domain ==>
    bytes_in_mem p xs
      (asm_write_bytearray c1 new_bytes t1.mem) t1.mem_domain s1.mem_domain
Proof
  STRIP_TAC \\ match_mp_tac bytes_in_mem_asm_write_bytearray_lemma
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`c1`,`a`)
  \\ Q.SPEC_TAC (`x`,`x`)
  \\ Q.SPEC_TAC (`t1.mem`,`m`)
  \\ Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ res_tac
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ full_simp_tac(srw_ss())[mem_load_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ srw_tac[][combinTheory.APPLY_UPDATE_THM]
  \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

Triviality write_bytearray_NOT_Loc:
  !xs c1 s1 a c.
      (s1.mem a = Word c) ==>
      (write_bytearray c1 xs s1.mem s1.mem_domain s1.be) a <> Loc n n0
Proof
  Induct \\ full_simp_tac(srw_ss())[write_bytearray_def,mem_store_byte_aux_def]
  \\ rpt strip_tac \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
QED

Triviality CallFFI_bytearray_lemma:
  byte_align (a:'a word) IN s1.mem_domain /\ good_dimindex (:'a) /\
    a IN t1.mem_domain /\
    a IN s1.mem_domain /\
    (s1.be = mc_conf.target.config.big_endian) /\
    (read_bytearray c1 (LENGTH new_bytes) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME x) /\
    (word_loc_val_byte p labs s1.mem a mc_conf.target.config.big_endian =
       SOME (t1.mem a)) ==>
    (word_loc_val_byte p labs (write_bytearray c1 new_bytes s1.mem s1.mem_domain s1.be) a
       mc_conf.target.config.big_endian =
     SOME (asm_write_bytearray c1 new_bytes t1.mem a))
Proof
  Q.SPEC_TAC (`s1`,`s1`) \\ Q.SPEC_TAC (`t1`,`t1`) \\ Q.SPEC_TAC (`c1`,`c1`)
  \\ Q.SPEC_TAC (`x`,`x`) \\ Q.SPEC_TAC (`new_bytes`,`xs`) \\ Induct
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def,write_bytearray_def,read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux s1.mem s1.mem_domain s1.be c1` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (c1 + 1w) (LENGTH xs) (mem_load_byte_aux s1.mem s1.mem_domain s1.be)`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ qmatch_assum_rename_tac
       `read_bytearray (c1 + 1w) (LENGTH xs) (mem_load_byte_aux s1.mem s1.mem_domain s1.be) = SOME y`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y`,`c1+1w`,`t1`,`s1`])
  \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[mem_store_byte_aux_def]
  \\ reverse (Cases_on `(write_bytearray (c1 + 1w)
       xs s1.mem s1.mem_domain mc_conf.target.config.big_endian) (byte_align c1)`)
  \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[mem_load_byte_aux_def]
    \\ Cases_on `s1.mem (byte_align c1)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac write_bytearray_NOT_Loc \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  \\ `byte_align c1 IN s1.mem_domain` by
    (full_simp_tac(srw_ss())[mem_load_byte_aux_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def,word_loc_val_byte_def,APPLY_UPDATE_THM]
  \\ Cases_on `a = c1` \\ full_simp_tac(srw_ss())[word_loc_val_def,good_dimindex_get_byte_set_byte]
  \\ Cases_on `byte_align c1 = byte_align a` \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ full_simp_tac(srw_ss())[get_byte_set_byte_diff]
QED

(* inst correct *)

Triviality MULT_ADD_LESS_MULT:
  !m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num
Proof
  rpt strip_tac
  \\ `SUC m <= l` by asm_rewrite_tac [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by asm_simp_tac bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by asm_simp_tac bool_ss [LE_MULT_LCANCEL]
  \\ decide_tac
QED

Triviality aligned_IMP_ADD_LESS_dimword:
  aligned k (x:'a word) /\ k <= dimindex (:'a) ==>
    w2n x + (2 ** k - 1) < dimword (:'a)
Proof
  Cases_on `x` \\ fs [aligned_w2n,dimword_def] \\ rw []
  \\ full_simp_tac std_ss [ONCE_REWRITE_RULE [ADD_COMM]LESS_EQ_EXISTS]
  \\ pop_assum (fn th => full_simp_tac std_ss [th])
  \\ full_simp_tac std_ss [MOD_EQ_0_DIVISOR]
  \\ var_eq_tac
  \\ full_simp_tac std_ss [EXP_ADD]
  \\ match_mp_tac MULT_ADD_LESS_MULT \\ fs []
QED

Theorem aligned_2_imp:
   aligned 2 (x:'a word) /\ dimindex (:'a) = 32 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x
Proof
  rw [alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
  \\ match_mp_tac alignmentTheory.align_add_aligned
  \\ simp [wordsTheory.dimword_def]
QED

Theorem aligned_2_not_eq:
   aligned 2 (x:'a word) ∧ dimindex(:'a) = 32 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a
Proof
  metis_tac[aligned_2_imp]
QED

Theorem aligned_3_imp:
   aligned 3 (x:'a word) /\ dimindex (:'a) = 64 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x ∧
    byte_align (x + 4w) = x ∧
    byte_align (x + 5w) = x ∧
    byte_align (x + 6w) = x ∧
    byte_align (x + 7w) = x
Proof
  rw [alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
  \\ match_mp_tac alignmentTheory.align_add_aligned
  \\ simp [wordsTheory.dimword_def]
QED

Theorem aligned_3_not_eq:
   aligned 3 (x:'a word) ∧ dimindex(:'a) = 64 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a ∧
    x+4w ≠ a ∧
    x+5w ≠ a ∧
    x+6w ≠ a ∧
    x+7w ≠ a
Proof
    metis_tac[aligned_3_imp]
QED

Triviality dimword_eq_32_imp_or_bytes:
  dimindex (:'a) = 32 ==>
    (w2w ((w2w (x:'a word)):word8) ||
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ||
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ||
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24) = x
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] []
QED

Triviality dimword_eq_64_imp_or_bytes:
  dimindex (:'a) = 64 ==>
    (w2w ((w2w (x:'a word)):word8) ||
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ||
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ||
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24 ||
     w2w ((w2w (x ⋙ 32)):word8) ≪ 32 ||
     w2w ((w2w (x ⋙ 40)):word8) ≪ 40 ||
     w2w ((w2w (x ⋙ 48)):word8) ≪ 48 ||
     w2w ((w2w (x ⋙ 56)):word8) ≪ 56) = x
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] []
QED

Triviality byte_align_32_eq:
  dimindex (:'a) = 32 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 4) = a
Proof
  Cases_on`a`>>
  rw[alignmentTheory.byte_align_def]>>
  fs[alignmentTheory.align_w2n,word_add_n2w]>>rfs[dimword_def]>>
  Q.SPEC_THEN `4n` mp_tac DIVISION>>
  fs[]>>disch_then (Q.SPEC_THEN`n` assume_tac)>>
  simp[]
QED

Triviality byte_align_64_eq:
  dimindex (:'a) = 64 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 8) = a
Proof
  Cases_on`a`>>
  rw[alignmentTheory.byte_align_def]>>
  fs[alignmentTheory.align_w2n,word_add_n2w]>>rfs[dimword_def]>>
  Q.SPEC_THEN `8n` mp_tac DIVISION>>
  fs[]>>disch_then (Q.SPEC_THEN`n` assume_tac)>>
  simp[]
QED

Triviality byte_align_32_IMP:
  dimindex(:'a) = 32 ⇒
  (byte_align a = a ⇒ w2n a MOD 4 = 0) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 4 = 1) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 4 = 2) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 4 = 3)
Proof
  rw[]>>imp_res_tac byte_align_32_eq>>fs[]>>
  qpat_x_assum`_=a` mp_tac>>
  qabbrev_tac`ba = byte_align a`>>
  qabbrev_tac`ca = w2n a MOD 4`>>
  first_x_assum(qspec_then`a` (SUBST1_TAC o SYM))>>
  unabbrev_all_tac>>
  fs[dimword_def,addressTheory.WORD_EQ_ADD_CANCEL]>>
  Q.ISPECL_THEN[`32n`,`w2n a MOD 4`] assume_tac bitTheory.MOD_ZERO_GT>>
  fs[]>>
  Q.ISPECL_THEN [`w2n a`,`4n`] assume_tac MOD_LESS>>
  DECIDE_TAC
QED

Triviality MOD4_CASES:
  ∀n. n MOD 4 = 0 ∨ n MOD 4 = 1 ∨ n MOD 4 = 2 ∨ n MOD 4 = 3
Proof
  rw[]>>`n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []
QED

Triviality byte_align_32_CASES:
  dimindex(:'a) = 32 ⇒
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a
Proof
  rw[]>>imp_res_tac byte_align_32_eq>>
  pop_assum(qspec_then`a` assume_tac)>>
  Q.SPEC_THEN `w2n a` mp_tac MOD4_CASES>>rw[]>>
  fs[]
QED

Triviality MOD8_CASES:
  ∀n. n MOD 8 = 0 ∨ n MOD 8 = 1 ∨ n MOD 8 = 2 ∨ n MOD 8 = 3 ∨
      n MOD 8 = 4 ∨ n MOD 8 = 5 ∨ n MOD 8 = 6 ∨ n MOD 8 = 7
Proof
  rw[]>>`n MOD 8 < 8` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 8 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                   (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``)
  \\ fs []
QED

Triviality byte_align_64_CASES:
  dimindex(:'a) = 64 ⇒
  byte_align a + (7w:'a word) = a ∨
  byte_align a + (6w:'a word) = a ∨
  byte_align a + (5w:'a word) = a ∨
  byte_align a + (4w:'a word) = a ∨
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a
Proof
  rw[]>>imp_res_tac byte_align_64_eq>>
  pop_assum(qspec_then`a` assume_tac)>>
  Q.SPEC_THEN `w2n a` mp_tac MOD8_CASES>>rw[]>>
  fs[]
QED

Triviality byte_align_64_IMP:
  dimindex(:'a) = 64 ⇒
  (byte_align a + (7w:'a word) = a ⇒ w2n a MOD 8 = 7) ∧
  (byte_align a + (6w:'a word) = a ⇒ w2n a MOD 8 = 6) ∧
  (byte_align a + (5w:'a word) = a ⇒ w2n a MOD 8 = 5) ∧
  (byte_align a + (4w:'a word) = a ⇒ w2n a MOD 8 = 4) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 8 = 3) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 8 = 2) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 8 = 1) ∧
  (byte_align a = a ⇒ w2n a MOD 8 = 0)
Proof
  rw[]>>imp_res_tac byte_align_64_eq>>fs[]>>
  qpat_x_assum`_=a` mp_tac>>
  qabbrev_tac`ba = byte_align a`>>
  qabbrev_tac`ca = w2n a MOD 8`>>
  first_x_assum(qspec_then`a` (SUBST1_TAC o SYM))>>
  unabbrev_all_tac>>
  fs[dimword_def,addressTheory.WORD_EQ_ADD_CANCEL]>>
  Q.ISPECL_THEN[`64n`,`w2n a MOD 8`] assume_tac bitTheory.MOD_ZERO_GT>>
  fs[]>>
  Q.ISPECL_THEN [`w2n a`,`8n`] assume_tac MOD_LESS>>
  DECIDE_TAC
QED

Triviality arith_upd_lemma:
  (∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)) ∧ ¬(arith_upd a s1).failed ⇒
   ∀r. word_loc_val p labs (read_reg r (arith_upd a s1)) =
       SOME ((arith_upd a t1).regs r)
Proof
  Cases_on`a`>>srw_tac[][arith_upd_def]>- (
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    EVAL_TAC >> srw_tac[][] >>
    metis_tac[] )
  >- (
    pop_assum mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- EVAL_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- EVAL_TAC >>
    qmatch_assum_rename_tac`read_reg rr _ = _` >>
    first_assum(qspec_then`rr`mp_tac) >>
    first_assum(SUBST1_TAC) >>
    EVAL_TAC >> strip_tac >>
    Cases_on`b` >> EVAL_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    EVAL_TAC >>
    qpat_x_assum`_ = Word c`mp_tac >>
    Cases_on`r` >> EVAL_TAC >> srw_tac[][] >>
    qmatch_assum_rename_tac`read_reg r2 _ = _` >>
    first_x_assum(qspec_then`r2`mp_tac) >>
    simp[] >> EVAL_TAC >> srw_tac[][])
  >- (
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[APPLY_UPDATE_THM] >> srw_tac[][] >>
    gvs [] >>
    rpt $ pop_assum mp_tac >>
    EVAL_TAC >>
    rw [] >>
    qmatch_assum_rename_tac`read_reg r _ = _` >>
    first_x_assum(qspec_then`r`mp_tac) >>
    simp[] >> EVAL_TAC >> srw_tac[][] )
  >> (
    unabbrev_all_tac
    \\ first_assum(qspec_then`n0`mp_tac)
    \\ first_assum(qspec_then`n1`mp_tac)
    \\ first_assum(qspec_then`n2`mp_tac)
    \\ first_assum(qspec_then`n3`mp_tac)
    \\ first_x_assum(qspec_then`r`mp_tac)
    \\ every_case_tac \\ fs[]
    \\ EVAL_TAC \\ rw[] \\ EVAL_TAC \\ fs[]
    \\ fs[read_reg_def]
    \\ fs[labSemTheory.assert_def])
QED

(* The lab and asm versions should be in their individual props *)
Theorem arith_upd_fp_regs[simp]:
    ((arith_upd a s).fp_regs = s.fp_regs ∧
  (arith_upd a (t:'a asm_state)).fp_regs = t.fp_regs)
Proof
  Cases_on`a`>>
  TRY(Cases_on`b`)>>
  EVAL_TAC>>fs[]>>every_case_tac>>
  fs[]
QED

Triviality fp_upd_lemma:
  (∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)) ∧
  (!r. s1.fp_regs r = t1.fp_regs r) /\
   ¬(fp_upd f s1).failed ⇒
  (∀r. (fp_upd f s1).fp_regs r = (fp_upd f t1).fp_regs r) ∧
  ∀r.
    word_loc_val p labs (read_reg r (fp_upd f s1)) =
    SOME ((fp_upd f t1).regs r)
Proof
  strip_tac>>Cases_on`f`>>fs[fp_upd_def,read_fp_reg_def,labSemTheory.read_fp_reg_def,upd_reg_def,labSemTheory.upd_reg_def]>>
  TRY(rw[]>>EVAL_TAC>>rw[]>>EVAL_TAC>>NO_TAC)
  >-
    (IF_CASES_TAC>>fs[]>>
    Cases_on`read_reg n0 s1`>>fs[labSemTheory.assert_def]
    >-
      (last_assum(qspec_then`n0` mp_tac)>>
      pop_assum SUBST1_TAC>>EVAL_TAC>>rw[])
    >>
      Cases_on`read_reg n1 s1`>>fs[labSemTheory.assert_def]>>
      last_assum(qspec_then`n0` mp_tac)>>
      last_assum(qspec_then`n1` mp_tac)>>
      pop_assum SUBST1_TAC>>
      pop_assum SUBST1_TAC>>
      EVAL_TAC>>rw[])
  >>
    TOP_CASE_TAC>>rfs[]>>fs[labSemTheory.assert_def]>>
    IF_CASES_TAC>>fs[]>>
    rw[]>>EVAL_TAC>>rw[]
QED

Theorem Inst_share_mem_pc_update_helper:
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.target (t1 with pc := pc') ms2 ==>
  share_mem_state_rel mc_conf (s1 with <|pc := s1.pc + 1; clock := s1.clock − 1|>)
    (t1 with pc := pc') ms2
Proof
  rw[share_mem_state_rel_def]
  >> metis_tac[]
QED

Theorem Inst_share_mem_reg_update_helper:
  share_mem_state_rel mc_conf s1 t1 ms1 /\
  target_state_rel mc_conf.target
    (t1 with <| regs := (n =+ c) t1.regs; pc := pc'|>) ms2 ==>
  share_mem_state_rel mc_conf (s1 with
    <| regs := (n =+ Word c) s1.regs; pc := s1.pc + 1; clock := s1.clock − 1|>)
    (t1 with <|regs := (n =+ c) t1.regs; pc := pc'|>) ms2
Proof
  rw[share_mem_state_rel_def]
  >> metis_tac[]
QED

Theorem arith_upd_share_mem_domain_unchange:
  (arith_upd a s1).shared_mem_domain = s1.shared_mem_domain
Proof
  Cases_on `a`
  \\ fs[arith_upd_def]
  \\ rpt (TOP_CASE_TAC >> fs[labSemTheory.upd_reg_def,labSemTheory.assert_def])
  \\ Cases_on `b`
  \\ fs[labSemTheory.binop_upd_def, labSemTheory.upd_reg_def]
QED

Theorem fp_upd_share_mem_domain_unchange:
  (fp_upd f s1).shared_mem_domain = s1.shared_mem_domain
Proof
  Cases_on `f` >> fs[fp_upd_def,labSemTheory.upd_reg_def, labSemTheory.upd_fp_reg_def]
  \\ rpt (TOP_CASE_TAC >>
  fs[labSemTheory.assert_def,labSemTheory.upd_fp_reg_def,APPLY_UPDATE_THM])
QED

val share_mem_state_rel_tac =
  rw[] >>
  gvs[IMP_CONJ_THM, AND_IMP_INTRO]
  >- (first_x_assum $ ho_match_mp_tac o cj 1 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 2 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 1 >> fs[] >> metis_tac[])
  >- (first_x_assum $ ho_match_mp_tac o cj 2 >> fs[] >> metis_tac[])

Theorem align2_not_align3_4w:
  ¬ aligned 3 x ∧ aligned 2 (x:'a word) ∧ dimindex (:'a) = 64 ⇒
  x = byte_align x + 4w ∧
  x + 1w = byte_align x + 5w ∧
  x + 2w = byte_align x + 6w ∧
  x + 3w = byte_align x + 7w
Proof
  strip_tac>>
  drule (Q.SPEC ‘x’ (GEN_ALL byte_align_64_CASES))>>
  strip_tac
  >~[‘byte_align x + 4w = x’]
  >- (rw[]>>pop_assum (fn h => simp[Once (GSYM h),SimpLHS]))>>
  TRY (qpat_x_assum ‘¬aligned 3 _’ mp_tac>>
  pop_assum (fn h => fs[Once (GSYM h)])>>
  strip_tac>>fs[byte_align_def,aligned_def]>>
  gvs[align_align]>>NO_TAC)>>
  qpat_x_assum ‘aligned 2 _’ mp_tac>>
  pop_assum (fn h => fs[Once (GSYM h)])>>
  fs[aligned_def,byte_align_def]>>
  ‘aligned 2 (align 3 x)’ by fs[aligned_def,align_align_MAX]>>
  fs[align_add_aligned_gen]>>
  rfs[align_w2n,dimword_def]>>gvs[]
QED

Theorem Inst_lemma:
  ~(asm_inst i s1).failed /\
   state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,p) s1 t1 ms1 /\
   (pos_val (s1.pc + 1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes') ==>
   ~(inst i t1).failed /\
    (!a. ~(a IN s1.mem_domain) ==> (inst i t1).mem a = t1.mem a) /\
   (target_state_rel mc_conf.target
      (upd_pc (t1.pc + n2w (LENGTH bytes')) (inst i t1)) ms2 ==>
    state_rel (mc_conf,code2,labs,p)
      (inc_pc (dec_clock (asm_inst i s1)))
      (upd_pc (t1.pc + n2w (LENGTH (bytes':word8 list))) (inst i t1)) ms2)
Proof
  Cases_on `i` \\ full_simp_tac(srw_ss())[asm_inst_def,inst_def]
  THEN1
   (full_simp_tac(srw_ss())[state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,dec_clock_def]
    \\ rpt strip_tac \\ rfs[] \\ res_tac
    \\ fs[GSYM word_add_n2w]
    \\ gvs[Inst_share_mem_reg_update_helper]
    >- (drule_all Inst_share_mem_pc_update_helper >> fs[]))
  THEN1
   (full_simp_tac(srw_ss())[state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,
        dec_clock_def,asmSemTheory.upd_reg_def,labSemTheory.upd_reg_def]
    \\ rpt strip_tac \\ rfs[] \\ res_tac \\ fs[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][word_loc_val_def]
    >- (drule_all Inst_share_mem_reg_update_helper >> fs[]))
  THEN1
   (strip_tac >>
    conj_asm1_tac >- (
      Cases_on`a`>> full_simp_tac(srw_ss())[asmSemTheory.arith_upd_def,labSemTheory.arith_upd_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[labSemTheory.assert_def] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[reg_imm_def,binop_upd_def,labSemTheory.binop_upd_def] >>
      full_simp_tac(srw_ss())[upd_reg_def,labSemTheory.upd_reg_def,state_rel_def] >>
      TRY (Cases_on`b`)>>EVAL_TAC >> full_simp_tac(srw_ss())[state_rel_def]
      (*Div*)
      >-
        (unabbrev_all_tac \\ fs[]
        \\ qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac
        \\ first_x_assum(qspec_then`n1`mp_tac)>>
        first_x_assum(qspec_then`n1`mp_tac)>>
        simp[]>>EVAL_TAC>>metis_tac[])
      (*LongDiv*)
      >>
      unabbrev_all_tac \\ fs[]
      \\ qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac
      \\ first_x_assum(qspec_then`n0`kall_tac)
      \\ first_assum(qspec_then`n0`mp_tac)
      \\ first_assum(qspec_then`n1`mp_tac)
      \\ first_assum(qspec_then`n2`mp_tac)
      \\ first_x_assum(qspec_then`n3`mp_tac)
      \\ simp[word_loc_val_def] \\ ntac 3 strip_tac
      \\ rveq \\ fs[asmSemTheory.read_reg_def]) >>
    srw_tac[][] >>
    simp[inc_pc_dec_clock] >>
    simp[dec_clock_def] >>
    match_mp_tac state_rel_clock >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    simp[GSYM word_add_n2w] >>
    fsrw_tac[ARITH_ss][] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- (srw_tac[][] >> metis_tac[]) >>
    conj_tac >- metis_tac[] >>
    conj_tac>- (match_mp_tac arith_upd_lemma >> srw_tac[][]) >>
    conj_tac>- fs[GSYM word_add_n2w]>>
    conj_tac >- metis_tac[] >>
    conj_tac >- rfs[] >>
    fs[upd_pc_def, inc_pc_def, arith_upd_def, share_mem_state_rel_def] >> rw[]>>
    gvs[IMP_CONJ_THM, AND_IMP_INTRO])
  THEN1
    (strip_tac >>
    Cases_on`m`>>fs[mem_op_def,labSemTheory.assert_def]
  >-
    (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_load_byte_def,labSemTheory.assert_def,labSemTheory.upd_reg_def,dec_clock_def,assert_def,
       read_mem_word_compute,mem_load_def,upd_reg_def,upd_pc_def,mem_load_byte_aux_def,
       labSemTheory.addr_def,addr_def,read_reg_def,labSemTheory.mem_load_def]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac>>fs[state_rel_def]>>
    `t1.regs n' = c'` by
      (
      qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      rfs[word_loc_val_def])>>
    fs[]
    >-
      (`aligned 2 x` by fs [aligned_w2n]>>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (reverse (rw[])
       >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)
       >- rfs[]
       >- metis_tac[]
       >-
         (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
          fs[asmSemTheory.read_mem_def]>>
          qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
          fs[word_loc_val_byte_def]>>
          ntac 4 (FULL_CASE_TAC>>fs[])>>
          rfs[get_byte_def,byte_index_def]>>rveq>>
          Cases_on `c + t1.regs n'`>>
          rename1 `k < dimword (:α)`>>
          drule aligned_IMP_ADD_LESS_dimword >>
          full_simp_tac std_ss [] \\ fs [] >>
          strip_tac \\ fs [word_add_n2w] >>
          rfs [ADD_MOD_EQ_LEMMA] >>
          rpt (qpat_x_assum `w2w _ = _` (mp_tac o GSYM)) >>
          imp_res_tac dimword_eq_32_imp_or_bytes >> fs [])
        >>
          metis_tac[]
        ))
    >>
      `aligned 3 x` by fs [aligned_w2n]>>
       drule aligned_3_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align (x+4w) ∈ s1.mem_domain ∧
       byte_align (x+5w) ∈ s1.mem_domain ∧
       byte_align (x+6w) ∈ s1.mem_domain ∧
       byte_align (x+7w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (reverse(rw[])
       >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)
       >- rfs[]
       >- metis_tac[]
       >-
         (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
          fs[asmSemTheory.read_mem_def]>>
          qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
          fs[word_loc_val_byte_def]>>
          ntac 8 (FULL_CASE_TAC>>fs[])>>
          rfs[get_byte_def,byte_index_def]>>rveq>>
          Cases_on `c + t1.regs n'`>>
          rename1 `k < dimword (:α)`>>
          drule aligned_IMP_ADD_LESS_dimword >>
          full_simp_tac std_ss [] \\ fs [] >>
          strip_tac \\ fs [word_add_n2w] >>
          rfs [ADD_MOD_EQ_LEMMA] >>
          rpt (qpat_x_assum `w2w _ = _` (mp_tac o GSYM)) >>
          imp_res_tac dimword_eq_64_imp_or_bytes >> fs [])
        >>
          metis_tac[]))
  >- (*Load8*)
    (Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_load_byte_def,labSemTheory.assert_def,labSemTheory.upd_reg_def,dec_clock_def,state_rel_def,assert_def,
       read_mem_word_compute,mem_load_def,upd_reg_def,upd_pc_def,mem_load_byte_aux_def,labSemTheory.addr_def,addr_def,read_reg_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 2 (pop_assum mp_tac)>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 2 strip_tac>>
    qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
    fs[word_loc_val_byte_def]>>
    FULL_CASE_TAC>>fs[]>>
    qpat_x_assum `!n. n < s1.code_buffer.space_left ==> _` kall_tac >>
    qpat_assum `!r.word_loc_val _ _ _ = SOME _` (qspec_then`n'` assume_tac)>>
    qpat_x_assum`_=Word c'` SUBST_ALL_TAC>>
    fs[word_loc_val_def,GSYM word_add_n2w,alignmentTheory.aligned_extract]>>
    rw[]
    >- metis_tac[]
    >- metis_tac[]
    >- metis_tac[]
    >-
      (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
      fs[asmSemTheory.read_mem_def]>>
      rfs[word_loc_val_def])
    >- metis_tac[]
    >- rfs[]
    >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
        share_mem_state_rel_tac))
  >- (*Load32*)
    (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_load32_def,labSemTheory.assert_def,labSemTheory.upd_reg_def,dec_clock_def,assert_def,
       read_mem_word_compute,mem_load_def,upd_reg_def,upd_pc_def,mem_load_32_def,
       labSemTheory.addr_def,addr_def,read_reg_def,labSemTheory.mem_load_def]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac>>fs[state_rel_def]>>
    `t1.regs n' = c'` by
      (
      qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      rfs[word_loc_val_def])>>

    ntac 2 (pop_assum mp_tac)>>TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac >>
    fs[]
    >- (* 32 word *)
     (`aligned 2 x` by fs[aligned_w2n] >>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (reverse (rw[])
       >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)
       >- rfs[]
       >- metis_tac[]
       >-
         (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
          fs[asmSemTheory.read_mem_def]>>
          ‘byte_align (c + t1.regs n') ∈ s1.mem_domain’ by fs[]>>
          qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
          fs[word_loc_val_byte_def]>>
          ntac 4 (FULL_CASE_TAC>>fs[])>>
          rfs[get_byte_def,byte_index_def]>>
          fs[word_loc_val_def]>>
          simp[GSYM WORD_w2w_OVER_BITWISE]>>
          simp[w2w_LSL,word_bits_w2w,WORD_ALL_BITS,w2w_w2w])
        >>
          metis_tac[]
        ))

    >> (* word64 *)
    Cases_on ‘aligned 3 x’>>fs[]
     >- (drule aligned_3_imp>>
         disch_then (strip_assume_tac o UNDISCH)>>
         `byte_align (x+1w) ∈ s1.mem_domain ∧
         byte_align (x+2w) ∈ s1.mem_domain ∧
         byte_align (x+3w) ∈ s1.mem_domain ∧
         byte_align x ∈ s1.mem_domain` by fs[]>>
         IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
         (reverse(rw[])
          >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
              share_mem_state_rel_tac)
          >- rfs[]
          >- metis_tac[]
          >-
           (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
            fs[asmSemTheory.read_mem_def]>>
            ‘byte_align (c + t1.regs n') ∈ s1.mem_domain’ by fs[]>>
            qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
            fs[word_loc_val_byte_def]>>
            ntac 4 (FULL_CASE_TAC>>fs[])>>
            rfs[get_byte_def,byte_index_def]>>
            fs[word_loc_val_def]>>
            simp[GSYM WORD_w2w_OVER_BITWISE]>>
            simp[w2w_LSL,word_bits_w2w,WORD_ALL_BITS,w2w_w2w])
          >>
          metis_tac[]))
     >>
     ‘aligned 3 (byte_align x)’ by fs[byte_align_def,aligned_align]>>
     drule aligned_3_imp>>
     disch_then (strip_assume_tac o UNDISCH)>>
     `byte_align (byte_align x+4w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+5w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+6w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+7w) ∈ s1.mem_domain` by fs[]>>
     drule_all align2_not_align3_4w>>
     strip_tac>>
     IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
     (reverse(rw[])
      >- (fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)
      >- rfs[]
      >- metis_tac[]
      >-
       (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
        fs[asmSemTheory.read_mem_def]>>
        ‘byte_align (c + t1.regs n') ∈ s1.mem_domain’ by fs[]>>
        qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
        fs[word_loc_val_byte_def]>>
        PURE_FULL_CASE_TAC>-fs[]>>
        rfs[word_loc_val_def]>>
        rfs[get_byte_def,byte_index_def]>>
        fs[word_loc_val_def]>>
        simp[GSYM WORD_w2w_OVER_BITWISE]>>
        simp[w2w_LSL,word_bits_w2w,WORD_ALL_BITS,w2w_w2w])
      >>
      metis_tac[]))
  >-
    (*Store*)
    (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_store_byte_def,labSemTheory.assert_def,mem_store_byte_aux_def,mem_store_def,labSemTheory.addr_def,
       addr_def,write_mem_word_compute,upd_pc_def,read_reg_def,assert_def,upd_mem_def,dec_clock_def,
       labSemTheory.mem_store_def,read_reg_def,labSemTheory.upd_mem_def]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac>>fs[state_rel_def]>>
    `t1.regs n' = c'` by
      (
      qpat_x_assum `!bn.bn < _ ==> ~(MEM _ _)`kall_tac>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      first_x_assum(qspec_then`n'` assume_tac)>>
      rfs[word_loc_val_def])>>
    fs[]
    >-
      (`aligned 2 x` by fs [aligned_w2n]>>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
         fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (simp[word_loc_val_byte_def,APPLY_UPDATE_THM]>>
         IF_CASES_TAC>>fs[]
         >-
           (fs[get_byte_def,byte_index_def]>>
           drule byte_align_32_IMP>>
           rpt IF_CASES_TAC>>fs[]>>
           metis_tac[byte_align_32_CASES])
         >>
           qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
           imp_res_tac aligned_2_not_eq>>fs[word_loc_val_byte_def])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >- rfs[]
       >- (
          fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)))
     >>
       (`aligned 3 x` by fs [aligned_w2n]>>
       drule aligned_3_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
       `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align (x+4w) ∈ s1.mem_domain ∧
       byte_align (x+5w) ∈ s1.mem_domain ∧
       byte_align (x+6w) ∈ s1.mem_domain ∧
       byte_align (x+7w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (simp[word_loc_val_byte_def,APPLY_UPDATE_THM]>>
         IF_CASES_TAC>>fs[]
         >-
           (fs[get_byte_def,byte_index_def]>>
           drule byte_align_64_IMP>>
           rpt IF_CASES_TAC>>fs[]>>
           metis_tac[byte_align_64_CASES])
         >>
           qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
           imp_res_tac aligned_3_not_eq>>fs[word_loc_val_byte_def])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>HINT_EXISTS_TAC>>fs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >-rfs[]
       >- (
          fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac))))
  >-
    (* Store8 *)
    (Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_store_byte_def,labSemTheory.assert_def,mem_store_byte_aux_def,mem_store_def,labSemTheory.addr_def,
       addr_def,write_mem_word_compute,upd_pc_def,read_reg_def,assert_def,upd_mem_def,dec_clock_def]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    ntac 3 (pop_assum mp_tac)>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 3 strip_tac>>
    fs[state_rel_def]>>
    qpat_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
    fs[word_loc_val_byte_def]>>
    FULL_CASE_TAC>>fs[]>>
    qpat_x_assum `!n. n < s1.code_buffer.space_left ==> _` kall_tac >>
    qpat_assum `!r.word_loc_val _ _ _ = SOME _` (qspec_then`n'` assume_tac)>>
    qpat_x_assum`_=Word c''` SUBST_ALL_TAC>>
    fs[word_loc_val_def,GSYM word_add_n2w,alignmentTheory.aligned_extract]>>
    rw[]
      >-
        (fs[APPLY_UPDATE_THM]>>
        IF_CASES_TAC>>fs[])
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[]
      >-
        (simp[APPLY_UPDATE_THM]>>
        IF_CASES_TAC>>fs[word_loc_val_def]>>
        IF_CASES_TAC>>fs[]
        >-
          (simp[good_dimindex_get_byte_set_byte]>>
          qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
            (qspec_then`n` assume_tac)>>
          rfs[word_loc_val_def])
        >>
        simp[get_byte_set_byte_diff]>>
        first_x_assum(qspec_then`a` mp_tac)>>
        TOP_CASE_TAC>>rfs[word_loc_val_def])
      >-
        (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
        qexists_tac`t1.mem`>>rfs[]>>
        rw[APPLY_UPDATE_THM]>>
        rfs[])
    >-
      (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
      qexists_tac`t1.mem`>>rfs[]>>
      rw[APPLY_UPDATE_THM]>>
      rfs[])
    >- rfs[]
    >- (
      fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
      share_mem_state_rel_tac))
  >-
    (* Store32 *)
   (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_store32_def,labSemTheory.assert_def,mem_store_32_def,mem_store_def,labSemTheory.addr_def,
       addr_def,write_mem_word_compute,upd_pc_def,read_reg_def,assert_def,upd_mem_def,dec_clock_def,
       labSemTheory.mem_store_def,read_reg_def,labSemTheory.upd_mem_def]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    ntac 4 (pop_assum mp_tac)>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 5 strip_tac>>fs[state_rel_def]>>

    qpat_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
    fs[word_loc_val_byte_def]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>
    strip_tac>>
    qpat_x_assum `!n. n < s1.code_buffer.space_left ==> _` kall_tac >>
    qpat_assum `!r.word_loc_val _ _ _ = SOME _` (qspec_then`n'` assume_tac)>>
    qpat_x_assum`_=Word c''` SUBST_ALL_TAC>>
    fs[word_loc_val_def]
    >- (* store32 - word32 *)
      (`aligned 2 x` by fs [aligned_w2n]>>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
         fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
        (simp[APPLY_UPDATE_THM]>>
         Cases_on ‘s1.be’>>fs[]>>gvs[]>>
         rpt (IF_CASES_TAC>>fs[word_loc_val_def])>>
         TRY (simp[good_dimindex_get_byte_set_byte,
                   get_byte_set_byte_diff]>>
              qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
                                       (qspec_then`n` assume_tac)>>
              rfs[word_loc_val_def,w2w_w2w,WORD_ALL_BITS]>>
              rfs[word_lsr_n2w,word_bits_w2w]>>
              simp[w2w_w2w,WORD_BITS_COMP_THM]>>NO_TAC)>>
         TRY (qmatch_asmsub_abbrev_tac ‘aligned 2 X’>>
              ‘X ≠ X + 1w ∧ X ≠ X + 2w ∧ X ≠ X + 3w ∧ X + 1w ≠ X + 2w ∧
               X + 1w ≠ X + 3w ∧ X + 2w ≠ X + 3w’ by
                (‘¬aligned 2 (X + 1w) ∧ ¬aligned 2 (X + 2w) ∧
                  ¬aligned 2 (X + 3w)’
                   by (rpt strip_tac>>
                       pop_assum $ assume_tac o SIMP_RULE std_ss [aligned_def]>>
                       rfs[align_add_aligned_gen]>>
                       rfs[align_w2n,dimword_def])>>
                 drule aligned_2_imp>>
                 strip_tac>>rfs[aligned_def,byte_align_def,dimword_def])>>
              TRY (qpat_assum ‘_ = a’ (fn h => rewrite_tac[GSYM h]))>>
              simp[good_dimindex_get_byte_set_byte,
                   get_byte_set_byte_diff]>>
              qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
                               (qspec_then`n` assume_tac)>>
              rfs[word_loc_val_def,w2w_w2w,WORD_ALL_BITS]>>
              rfs[word_lsr_n2w,word_bits_w2w]>>
              simp[w2w_w2w,WORD_BITS_COMP_THM]>>NO_TAC)>>
         simp[APPLY_UPDATE_THM]>>simp[]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
         FULL_CASE_TAC>>fs[]>>gvs[word_loc_val_def]>>
         simp[good_dimindex_get_byte_set_byte,
              get_byte_set_byte_diff])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >- rfs[]
       >- (
          fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)))

     >> (* store32 - word64 *)
     Cases_on ‘aligned 3 x’>>fs[]
    >-
     (drule aligned_3_imp>>
      disch_then (strip_assume_tac o UNDISCH)>>
       `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
        (simp[APPLY_UPDATE_THM]>>
         Cases_on ‘s1.be’>>fs[]>>gvs[]>>
         rpt (IF_CASES_TAC>>fs[word_loc_val_def])>>
         TRY (simp[good_dimindex_get_byte_set_byte,
                   get_byte_set_byte_diff]>>
              qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
                                (qspec_then`n` assume_tac)>>
              rfs[word_loc_val_def]>>
              simp[WORD_w2w_EXTRACT]>>
              simp[word_extract_def]>>
              simp[word_lsr_n2w]>>
              simp[WORD_BITS_COMP_THM]>>
              simp[word_bits_w2w]>>
              simp[WORD_BITS_COMP_THM]>>
              simp[WORD_w2w_EXTRACT]>>
              simp[WORD_BITS_EXTRACT]>>
              simp[WORD_EXTRACT_COMP_THM]>>
              simp[WORD_EXTRACT_MIN_HIGH]>>NO_TAC)>>
         TRY (qmatch_asmsub_abbrev_tac ‘aligned 3 X’>>
              ‘X ≠ X + 1w ∧ X ≠ X + 2w ∧ X ≠ X + 3w ∧ X + 1w ≠ X + 2w ∧
               X + 1w ≠ X + 3w ∧ X + 2w ≠ X + 3w’ by
                (‘¬aligned 3 (X + 1w) ∧ ¬aligned 3 (X + 2w) ∧
                  ¬aligned 3 (X + 3w)’
                   by (rpt strip_tac>>
                       pop_assum $ assume_tac o SIMP_RULE std_ss [aligned_def]>>
                       rfs[align_add_aligned_gen]>>
                       rfs[align_w2n,dimword_def])>>
                 drule aligned_3_imp>>
                 strip_tac>>rfs[aligned_def,byte_align_def,dimword_def])>>
              TRY (qpat_assum ‘_ = a’ (fn h => rewrite_tac[GSYM h]))>>
              simp[good_dimindex_get_byte_set_byte,
                   get_byte_set_byte_diff]>>
              qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
                                (qspec_then`n` assume_tac)>>
              rfs[word_loc_val_def]>>
              simp[WORD_w2w_EXTRACT]>>
              simp[word_extract_def]>>
              simp[word_lsr_n2w]>>
              simp[WORD_BITS_COMP_THM]>>
              simp[word_bits_w2w]>>
              simp[WORD_BITS_COMP_THM]>>
              simp[WORD_w2w_EXTRACT]>>
              simp[WORD_BITS_EXTRACT]>>
              simp[WORD_EXTRACT_COMP_THM]>>
              simp[WORD_EXTRACT_MIN_HIGH]>>NO_TAC)>>
         simp[APPLY_UPDATE_THM]>>simp[]>>
         qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
         FULL_CASE_TAC>>fs[]>>gvs[word_loc_val_def]>>
         simp[good_dimindex_get_byte_set_byte,
              get_byte_set_byte_diff])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
         simp[APPLY_UPDATE_THM]>>
         qexists_tac`t1.mem`>>rfs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])
       >- rfs[]
       >- (
          fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
          share_mem_state_rel_tac)))

       >> (* word64, off by 4w *)
     ‘aligned 3 (byte_align x)’ by fs[byte_align_def,aligned_align]>>
     drule aligned_3_imp>>
     disch_then (strip_assume_tac o UNDISCH)>>
     `byte_align (byte_align x+4w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+5w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+6w) ∈ s1.mem_domain ∧
     byte_align (byte_align x+7w) ∈ s1.mem_domain` by fs[]>>
     drule_all align2_not_align3_4w>>
     strip_tac>>
     IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
        >-
         (simp[APPLY_UPDATE_THM]>>
          qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>fs[]>>
          rpt(IF_CASES_TAC>>fs[]))
        >-
         metis_tac[]
        >-
         metis_tac[]
        >-
         (simp[APPLY_UPDATE_THM]>>
          Cases_on ‘s1.be’>>fs[]>>gvs[]>>
          rpt (IF_CASES_TAC>>fs[word_loc_val_def])>>
          TRY (simp[good_dimindex_get_byte_set_byte,
                    get_byte_set_byte_diff]>>
               qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`                         (qspec_then`n` assume_tac)>>
               rfs[word_loc_val_def]>>
               simp[WORD_w2w_EXTRACT]>>
               simp[word_extract_def]>>
               simp[word_lsr_n2w]>>
               simp[WORD_BITS_COMP_THM]>>
               simp[word_bits_w2w]>>
               simp[WORD_BITS_COMP_THM]>>
               simp[WORD_w2w_EXTRACT]>>
               simp[WORD_BITS_EXTRACT]>>
               simp[WORD_EXTRACT_COMP_THM]>>
               simp[WORD_EXTRACT_MIN_HIGH]>>NO_TAC)>>
          TRY (qmatch_asmsub_abbrev_tac ‘aligned 3 X’>>
               ‘X + 4w ≠ X + 5w ∧ X + 4w ≠ X + 6w ∧ X + 4w ≠ X + 7w ∧
                X + 5w ≠ X + 6w ∧ X + 5w ≠ X + 7w ∧ X + 6w ≠ X + 7w’ by
                 (‘¬aligned 3 (X + 5w) ∧ ¬aligned 3 (X + 6w) ∧
                   ¬aligned 3 (X + 7w)’
                    by (rpt strip_tac>>
                        pop_assum $ assume_tac o SIMP_RULE std_ss [aligned_def]>>
                        rpt (qpat_x_assum ‘_ = a’ kall_tac)>>
                        rfs[align_add_aligned_gen]>>
                        rfs[align_w2n,dimword_def])>>
                  drule aligned_3_imp>>
                  strip_tac>>rfs[aligned_def,byte_align_def,dimword_def])>>
               TRY (qpat_assum ‘_ = a’ (fn h => rewrite_tac[GSYM h]))>>
               simp[good_dimindex_get_byte_set_byte,
                    get_byte_set_byte_diff]>>
               qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = SOME _`
                               (qspec_then`n` assume_tac)>>
               rfs[word_loc_val_def]>>
               simp[WORD_w2w_EXTRACT]>>
               simp[word_extract_def]>>
               simp[word_lsr_n2w]>>
               simp[WORD_BITS_COMP_THM]>>
               simp[word_bits_w2w]>>
               simp[WORD_BITS_COMP_THM]>>
               simp[WORD_w2w_EXTRACT]>>
               simp[WORD_BITS_EXTRACT]>>
               simp[WORD_EXTRACT_COMP_THM]>>
               simp[WORD_EXTRACT_MIN_HIGH]>>NO_TAC)>>
          simp[APPLY_UPDATE_THM]>>simp[]>>
          IF_CASES_TAC>>fs[]>>
          simp[word_loc_val_def]>>
          gvs[get_byte_set_byte_diff]>>
          qpat_x_assum `!a. byte_align a IN s1.mem_domain ==> _` imp_res_tac >>
          FULL_CASE_TAC>>gvs[word_loc_val_def])
        >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>HINT_EXISTS_TAC>>fs[]>>
          rw[APPLY_UPDATE_THM]>>
          rfs[])
        >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>
          simp[APPLY_UPDATE_THM]>>
          qexists_tac`t1.mem`>>rfs[]>>
          rw[APPLY_UPDATE_THM]>>
          rfs[])
        >- rfs[]
        >- (
         fs[read_mem_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
         share_mem_state_rel_tac))
    ))
  THEN1
  (strip_tac>>CONJ_ASM1_TAC>-
    (Cases_on`f`>>TRY(EVAL_TAC>>fs[state_rel_def]>>NO_TAC)
    >-
      (EVAL_TAC>>rw[]>>fs[state_rel_def])
    >>
      fs[fp_upd_def]>>
      `read_fp_reg n0 s1 = read_fp_reg n0 t1` by
        (EVAL_TAC>>fs[state_rel_def])>>
      TOP_CASE_TAC>>fs[assert_def,labSemTheory.assert_def]>>
      IF_CASES_TAC>-
        fs[state_rel_def,labSemTheory.upd_fp_reg_def,upd_fp_reg_def]>>
      IF_CASES_TAC>>
      fs[state_rel_def,labSemTheory.upd_fp_reg_def,upd_fp_reg_def])
  >>
  strip_tac>>
  simp[inc_pc_dec_clock] >>
  simp[dec_clock_def] >>
  match_mp_tac state_rel_clock >>
  full_simp_tac(srw_ss())[state_rel_def] >>
  simp[GSYM word_add_n2w] >>
  fsrw_tac[ARITH_ss][] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- ( srw_tac[][] >> first_x_assum drule >> simp[] ) >>
  conj_tac >- metis_tac[] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >-
    (
    fs[fp_upd_def,upd_pc_def,APPLY_UPDATE_THM,share_mem_state_rel_def] >>
    share_mem_state_rel_tac) >>
  reverse conj_tac >- rfs[] >>
  reverse conj_tac >- metis_tac[] >>
  reverse conj_tac >- (
    rw[] >> fs[] >> fs[GSYM word_add_n2w] ) >>
  match_mp_tac fp_upd_lemma>> fs[])
QED

(* compile correct *)

Triviality line_length_MOD_0:
  encoder_correct mc_conf.target /\
    (~EVEN p ==> (mc_conf.target.config.code_alignment = 0)) /\
    line_ok mc_conf.target.config labs ffi_names p h ==>
    (line_length h MOD 2 ** mc_conf.target.config.code_alignment = 0)
Proof
  Cases_on `h` \\ TRY (Cases_on `a`) \\ full_simp_tac(srw_ss())[line_ok_def,line_length_def]
  \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[encoder_correct_def,target_ok_def,enc_ok_def]
  \\ fs(bool_case_eq_thms)
  \\ full_simp_tac(srw_ss())[LET_DEF,enc_with_nop_thm] \\ srw_tac[][LENGTH_FLAT,LENGTH_REPLICATE]
  \\ qpat_x_assum `2 ** nn = xx:num` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,map_replicate,SUM_REPLICATE]
QED

Triviality pos_val_MOD_0_lemma:
  (0 MOD 2 ** mc_conf.target.config.code_alignment = 0)
Proof
  full_simp_tac(srw_ss())[]
QED

val pos_val_MOD_0 = Q.prove(
  `!x pos code2.
      encoder_correct mc_conf.target /\
      (has_odd_inst code2 ==> (mc_conf.target.config.code_alignment = 0)) /\
      (~EVEN pos ==> (mc_conf.target.config.code_alignment = 0)) /\
      (pos MOD 2 ** mc_conf.target.config.code_alignment = 0) /\
      all_enc_ok mc_conf.target.config labs ffi_names pos code2 ==>
      (pos_val x pos code2 MOD 2 ** mc_conf.target.config.code_alignment = 0)`,
  reverse (Cases_on `encoder_correct mc_conf.target`)
  \\ asm_simp_tac pure_ss [] THEN1 full_simp_tac(srw_ss())[]
  \\ HO_MATCH_MP_TAC pos_val_ind
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[pos_val_def] \\ full_simp_tac(srw_ss())[all_enc_ok_def]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x = 0` \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[has_odd_inst_def]
  \\ Cases_on `EVEN pos` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVEN_ADD]
  \\ `0:num < 2 ** mc_conf.target.config.code_alignment` by full_simp_tac(srw_ss())[]
  \\ imp_res_tac (GSYM MOD_PLUS)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ imp_res_tac line_length_MOD_0 \\ full_simp_tac(srw_ss())[])
  |> Q.SPECL [`x`,`0`,`y`] |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [pos_val_MOD_0_lemma]
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

val IMP_IMP2 = METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)``

Theorem EVEN_add_AND:
   (1w && p) = 0w ∧
  EVEN x ⇒
  (1w && (p + n2w x)) = 0w
Proof
  rw[]>>
  `p = n2w(w2n p)` by fs[n2w_w2n]>>
  pop_assum SUBST1_TAC>>
  simp[word_add_n2w]>>
  PURE_REWRITE_TAC [Once WORD_AND_COMM]>>
  PURE_REWRITE_TAC [addressTheory.n2w_and_1]>>
  FULL_SIMP_TAC std_ss [arithmeticTheory.EVEN_MOD2]>>
  `0 < 2n` by fs[]>>
  drule (GSYM arithmeticTheory.MOD_PLUS)>>
  disch_then(qspecl_then [`x`,`w2n p`] SUBST_ALL_TAC)>>
  first_x_assum SUBST_ALL_TAC>>
  SIMP_TAC (std_ss++ARITH_ss) []>>
  PURE_REWRITE_TAC [GSYM addressTheory.n2w_and_1]>>
  simp[]
QED

Triviality word_cmp_lemma:
  state_rel (mc_conf,code2,labs,p) s1 t1 ms1 /\
    (word_cmp cmp (read_reg rr s1) (reg_imm ri s1) = SOME x) ==>
    (x = word_cmp cmp (read_reg rr t1) (reg_imm ri t1))
Proof
  Cases_on `ri` \\ full_simp_tac(srw_ss())[labSemTheory.reg_imm_def,asmSemTheory.reg_imm_def]
  \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
  \\ Cases_on `s1.regs rr` \\ full_simp_tac(srw_ss())[]
  \\ TRY (Cases_on `s1.regs n`) \\ full_simp_tac(srw_ss())[] \\ Cases_on `cmp`
  \\ full_simp_tac(srw_ss())[labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ qpat_x_assum `!bn. bn < _ ==> ~(MEM _ _)` kall_tac
  \\ first_x_assum (kall_tac o Q.SPEC `rr:num`)
  \\ first_assum (assume_tac o Q.SPEC `rr:num`)
  \\ first_x_assum (assume_tac o Q.SPEC `n:num`)
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rpt (qpat_x_assum `1w = xxx` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ rpt (qpat_x_assum `p + n2w xxx = t1.regs rr` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ metis_tac[EVEN_add_AND]
QED

Triviality list_add_if_fresh_simp:
  !n s. list_add_if_fresh s l =
    if find_index s l n = NONE then
      APPEND l [s]
    else l
Proof
  Induct_on `l`
  >- fs [list_add_if_fresh_def, find_index_def]
  >-
    (rpt strip_tac
     >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `n+1` thm))
     >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `s` thm))
     >> fs [list_add_if_fresh_def, find_index_def]
     >> every_case_tac
     >> fs [list_add_if_fresh_def, find_index_def])
QED

Theorem list_add_if_fresh_thm:
   list_add_if_fresh s l =
    if MEM s l then l else l ++ [s]
Proof
   fs[list_add_if_fresh_simp |> Q.SPEC`0`]>>rw[]>>
   metis_tac[find_index_NOT_MEM]
QED

val list_add_if_fresh_simp = Q.SPECL [`n`,`s`] list_add_if_fresh_simp

Triviality find_index_append:
  !n. find_index s (l++l') n =
  (case find_index s l n of NONE => find_index s l' (n + LENGTH l) | SOME i => SOME i)
Proof
  Induct_on `l`
  >- fs [find_index_def]
  >-
  (rpt strip_tac
   >> FIRST_X_ASSUM (fn thm => ASSUME_TAC(Q.SPEC `n+1` thm))
   >> fs [find_index_def]
   >> every_case_tac
   >> fs [find_index_def,ADD1])
QED

Triviality has_io_name_find_index:
  !l s. has_io_name s l
  ==> ?y. find_index (ExtCall s) (find_ffi_names l) 0 = SOME y
Proof
  ho_match_mp_tac find_ffi_names_ind
  >> rpt strip_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >> every_case_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >> every_case_tac
  >> fs[has_io_name_def,find_index_def, find_ffi_names_def,Q.INST [`n`|->`0`] list_add_if_fresh_simp,find_index_append]
  >- metis_tac [NOT_NONE_SOME]
  >- (Cases_on `find_index (ExtCall s) (find_ffi_names (Section k xs::rest)) 0`
      >> metis_tac [NOT_NONE_SOME])
QED

Triviality find_index_in_range:
  !n. find_index s l n = SOME x ==> x < n + LENGTH l /\ x >= n
Proof
  Induct_on `l`
  >> fs [find_index_def]
  >> rpt strip_tac
  >> every_case_tac
  >> FIRST_X_ASSUM (fn thm => TRY(ASSUME_TAC(Q.SPEC `n+1` thm)))
  >> rfs [find_index_def]
QED

Triviality find_index_in_range0:
  find_index s l 0 = SOME x ==> x < LENGTH l /\ x >= 0
Proof
  ASSUME_TAC (Q.SPEC `0` find_index_in_range) >> rfs []
QED

Theorem EL_get_ffi_index_MEM:
   MEM s ls ⇒ EL (get_ffi_index ls s) ls = s
Proof
  rw[get_ffi_index_def,find_index_LEAST_EL]
  \\ numLib.LEAST_ELIM_TAC
  \\ fs[MEM_EL,miscTheory.the_def]
  \\ metis_tac[]
QED

Theorem has_io_name_EXISTS:
   ∀name ls. has_io_name name ls ⇔
    EXISTS (λx. case x of LabAsm (CallFFI i) _ _ _ => i = name | _ => F)
    (FLAT (MAP Section_lines ls))
Proof
  recInduct has_io_name_ind
  \\ rw[has_io_name_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ Cases_on`s = index` \\ fs[]
QED

(* -- syntactic properties of remove_labels -- *)

(* annotated line length *)

Definition line_len_def:
  (line_len (Label _ _ l) = l) ∧
  (line_len (Asm _ _ l) = l) ∧
  (line_len (LabAsm _ _ _ l) = l)
End
val _ = export_rewrites["line_len_def"];

(* annotated section length *)

Theorem sec_length_add:
   ∀ls n m. sec_length ls (n+m) = sec_length ls n + m
Proof
  ho_match_mp_tac sec_length_ind >>
  simp[sec_length_def]
QED

Theorem sec_length_sum_line_len:
   ∀ls n.
    sec_length ls n = SUM (MAP line_len ls) + n
Proof
  ho_match_mp_tac sec_length_ind \\ rw[sec_length_def]
QED

(* simple syntactic properties of compiler functions *)

Definition enc_lines_again_simp_def:
  (enc_lines_again_simp labs ffis pos enc [] = ([],T)) ∧
  (enc_lines_again_simp labs ffis pos enc (LabAsm a w bytes l::xs) =
    let w1 = get_jump_offset a ffis labs pos
    in
      if w = w1 then
        let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
          (LabAsm a w bytes l::rest,ok)
      else
        let bs = enc (lab_inst w1 a) in
        let l1 = MAX (LENGTH bs) l in
        let (rest,ok) = enc_lines_again_simp labs ffis (pos + l1) enc xs in
          (LabAsm a w1 bs l1::rest,l1 = l ∧ ok)) ∧
  (enc_lines_again_simp labs ffis pos enc (Label k1 k2 l::xs) =
    let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
    (Label k1 k2 l::rest,ok)) ∧
  (enc_lines_again_simp labs ffis pos enc (Asm x1 x2 l::xs) =
    let (rest,ok) = enc_lines_again_simp labs ffis (pos + l) enc xs in
    (Asm x1 x2 l::rest,ok))
End

val enc_lines_again_simp_ind = theorem"enc_lines_again_simp_ind";

Triviality enc_lines_again_simp_EQ:
  ∀labs ffis pos enc ls acc b.
  let (ls',flag) = enc_lines_again_simp labs ffis pos enc ls in
  enc_lines_again labs ffis pos enc ls (acc,b) = (REVERSE acc ++ ls',sec_length ls' pos,b ∧ flag)
Proof
  ho_match_mp_tac enc_lines_again_simp_ind >>
  fs[enc_lines_again_simp_def,enc_lines_again_def]>>rw[sec_length_def]>>
  rpt(pairarg_tac>>fs[])>>
  rw[EQ_IMP_THM,sec_length_def]
QED

Theorem enc_lines_again_simp_len:
   ∀labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ⇒
    MAP line_len res = MAP line_len lines
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
QED

Theorem LENGTH_pad_bytes:
   0 < LENGTH nop ∧ LENGTH bytes ≤ l ⇒
    LENGTH (pad_bytes bytes l nop) = l
Proof
  srw_tac[][pad_bytes_def] >> srw_tac[][] >> fsrw_tac[ARITH_ss][]
  \\ match_mp_tac LENGTH_TAKE
  \\ simp[LENGTH_FLAT,SUM_MAP_LENGTH_REPLICATE]
  \\ Cases_on`LENGTH nop`>>full_simp_tac(srw_ss())[]>>simp[MULT,Once MULT_COMM]
QED

Theorem section_labels_sec_length:
   ∀pos lines acc.
    FST (section_labels pos lines acc) = sec_length lines pos
Proof
  ho_match_mp_tac section_labels_ind
  \\ rw[section_labels_def,sec_length_def]
QED

Theorem section_labels_append:
   ∀pos l1 labs l2.
    section_labels pos (l1 ++ l2) labs =
    section_labels (pos + (SUM (MAP line_len l1))) l2 (SND (section_labels pos l1 labs))
Proof
  recInduct section_labels_ind
  \\ rw[section_labels_def]
QED

Theorem line_length_add_nop1:
   ∀nop ls.
   ¬EVERY is_Label ls ⇒
   SUM (MAP line_length (add_nop nop ls)) =
   SUM (MAP line_length ls) + LENGTH nop
Proof
  ho_match_mp_tac add_nop_ind
  \\ rw[add_nop_def,line_length_def]
QED

Theorem line_length_add_nop:
   ∀nop ls.
   EVERY is_Label ls ⇒
   SUM (MAP line_length (add_nop nop ls)) =
   SUM (MAP line_length ls)
Proof
  ho_match_mp_tac add_nop_ind
  \\ rw[add_nop_def,line_length_def]
QED

Theorem line_len_add_nop1:
   ∀nop ls. ¬(EVERY is_Label ls) ⇒
    SUM (MAP line_len (add_nop nop ls)) =
    SUM (MAP line_len ls) + 1
Proof
  recInduct add_nop_ind \\ rw[add_nop_def]
QED

Theorem line_len_add_nop:
   ∀nop ls. EVERY is_Label ls ⇒
    SUM (MAP line_len (add_nop nop ls)) =
    SUM (MAP line_len ls)
Proof
  recInduct add_nop_ind \\ rw[add_nop_def]
QED

Theorem add_nop_append:
   ∀nop l1 l2.
    add_nop nop (l1++l2) = if EVERY is_Label l1 then l1 ++ add_nop nop l2 else add_nop nop l1 ++ l2
Proof
  ho_match_mp_tac add_nop_ind
  \\ rw[add_nop_def] \\ rw[] \\ fs[add_nop_def]
QED

Theorem EXISTS_not_Label_add_nop[simp]:
   ∀nop acc.
     EXISTS ($~ o is_Label) (add_nop nop acc) ⇔ EXISTS ($~ o is_Label) acc
Proof
  ho_match_mp_tac add_nop_ind \\ rw[add_nop_def]
QED

Theorem EVERY_is_Label_add_nop_preserved[simp]:
   ∀nop acc.
     EVERY is_Label (add_nop nop acc) ⇔ EVERY is_Label acc
Proof
  ho_match_mp_tac add_nop_ind \\ rw[add_nop_def]
QED

Theorem EVERY_is_Label_add_nop:
   ∀nop ls. EVERY is_Label ls ⇒ add_nop nop ls = ls
Proof
  recInduct add_nop_ind \\ rw[add_nop_def]
QED

Theorem SND_lines_upd_lab_len:
   ∀pos lines acc.
     SND (lines_upd_lab_len pos lines acc) =
     pos + SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc))) - SUM (MAP line_len acc)
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ rw[MAP_REVERSE,SUM_REVERSE]
QED

(* code_similar preservation *)

Triviality line_similar_add_nop:
  ∀ls ls' h.
  LIST_REL line_similar ls ls' ⇒
  LIST_REL line_similar ls (add_nop h ls')
Proof
  Induct_on`ls`>>rw[add_nop_def]>>
  Cases_on`y`>>Cases_on`h`>>fs[add_nop_def,line_similar_def]
QED

Theorem line_similar_pad_section:
   ∀nop l2 aux l1.
     LIST_REL line_similar l1 (REVERSE aux ++ l2) ⇒
     LIST_REL line_similar l1 (pad_section nop l2 aux)
Proof
   ho_match_mp_tac pad_section_ind >>
   srw_tac[][pad_section_def] >>
   first_x_assum match_mp_tac>>
   imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[] >>
   qmatch_assum_rename_tac`LIST_REL _ ls (_ ++ _)` >>
   qmatch_assum_abbrev_tac`LENGTH ls = m + _` >>
   qispl_then[`m`,`ls`]strip_assume_tac TAKE_DROP >>
   ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
   `m < LENGTH ls` by DECIDE_TAC>>
   qpat_x_assum`LIST_REL _ _ _` mp_tac>>
   first_x_assum (SUBST1_TAC o SYM) >>
   strip_tac>>
   match_mp_tac EVERY2_APPEND_suff >>
   drule LIST_REL_APPEND_IMP >>
   rw[]
   >-
     (`LIST_REL line_similar aux (add_nop nop aux)` by
       (match_mp_tac line_similar_add_nop>>
       match_mp_tac EVERY2_refl>>
       fs[line_similar_refl])>>
      ho_match_mp_tac LIST_REL_trans>>HINT_EXISTS_TAC>>
      metis_tac[line_similar_trans,LIST_REL_REVERSE_EQ])
   >>
     TRY(Cases_on`x`)>>TRY(Cases_on`x'`)>>fs[line_similar_def]
QED

Theorem code_similar_pad_code:
   ∀code1 code2.
   code_similar code1 code2 ⇒
   code_similar code1 (pad_code nop code2)
Proof
  Induct
  >- ( Cases >> simp[code_similar_def,pad_code_def] )
  >> Cases_on`code2` >- simp[code_similar_def]
  >> Cases >> simp[code_similar_def]
  >> Cases_on`h` >> simp[code_similar_def,pad_code_def]
  >> strip_tac >> rveq >>
  match_mp_tac line_similar_pad_section>>
  simp[]
QED

Triviality LIST_REL_enc_line:
  ∀ls ls'.
  LIST_REL line_similar ls ls' ⇔
  LIST_REL line_similar (MAP (enc_line enc len) ls) ls'
Proof
  Induct>>rw[]>>Cases_on`h`>>rw[enc_line_def,EQ_IMP_THM]>>Cases_on`y`>>
  fs[line_similar_def]
QED

Theorem code_similar_enc_sec_list[simp]:
   ∀code1 code2 n.
     code_similar (enc_sec_list n code1) code2 ⇔
     code_similar code1 code2
Proof
   simp[enc_sec_list_def]
   >> Induct >> simp[]
   >> Cases_on`code2`>>simp[code_similar_def]
   >> Cases_on`h`>>simp[code_similar_def]
   >> Cases>>simp[code_similar_def,enc_sec_def]>>
   rw[EQ_IMP_THM]>>
   metis_tac[LIST_REL_enc_line]
QED

Triviality enc_lines_again_IMP_similar:
  ∀labs ffis pos enc lines acc ok lines' ok' curr.
  enc_lines_again labs ffis pos enc lines (acc,ok) = (lines',ok') ⇒
  LIST_REL line_similar curr (REVERSE acc) ⇒
  LIST_REL line_similar (curr++lines) lines'
Proof
  Induct_on`lines`>>fs[enc_lines_again_def]>>rw[]>>
  fs[AND_IMP_INTRO]>>
  `curr ++ h ::lines = SNOC h curr ++ lines` by fs[]>>
  pop_assum SUBST1_TAC>>
  first_assum match_mp_tac>>
  Cases_on`h`>>fs[enc_lines_again_def]>>EVERY_CASE_TAC>>
  asm_exists_tac>>fs[SNOC_APPEND,line_similar_def]
QED

Theorem enc_secs_again_IMP_similar:
   ∀pos labs ffis enc code code1 ok.
  enc_secs_again pos labs ffis enc code = (code1,ok) ==> code_similar code code1
Proof
  ho_match_mp_tac enc_secs_again_ind>>fs[enc_secs_again_def]>>rw[]>>
  ntac 2 (pairarg_tac>>fs[])>>
  rveq>>fs[code_similar_def]>>
  imp_res_tac enc_lines_again_IMP_similar>>
  fs[]
QED

val lines_upd_lab_len_AUX = Q.prove(
  `!l aux pos.
      REVERSE aux ++ FST (lines_upd_lab_len pos l []) =
      FST (lines_upd_lab_len pos l aux)`,
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ simp_tac std_ss [lines_upd_lab_len_def,LET_DEF]
  \\ pop_assum (fn th => once_rewrite_tac [GSYM th]) \\ fs []) |> GSYM

Triviality line_similar_lines_upd_lab_len:
  !l aux pos l1.
      LIST_REL line_similar (FST (lines_upd_lab_len pos l [])) l1 =
      LIST_REL line_similar l l1
Proof
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ fs [lines_upd_lab_len_def]
  \\ once_rewrite_tac [lines_upd_lab_len_AUX]
  \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  \\ Cases_on `y` \\ fs [line_similar_def]
QED

Theorem code_similar_upd_lab_len:
   !code pos code1.
      code_similar (upd_lab_len pos code) code1 = code_similar code code1
Proof
  Induct \\ fs [code_similar_def] \\ Cases
  \\ Cases_on `code1` \\ fs [upd_lab_len_def,code_similar_def,UNCURRY]
  \\ Cases_on `h` \\ fs [upd_lab_len_def,code_similar_def]
  \\ rw [] \\ fs [line_similar_lines_upd_lab_len]
QED

Theorem lines_upd_lab_len_similar:
   ∀pos lines aux.
    LIST_REL line_similar (FST (lines_upd_lab_len pos lines aux)) (REVERSE aux ++ lines)
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def] \\ fs[]
  \\ TRY ( simp[LIST_REL_EL_EQN,line_similar_refl] \\ NO_TAC )
  \\ match_mp_tac LIST_REL_trans
  \\ first_assum(part_match_exists_tac (el 2 o strip_conj) o concl) \\ simp[]
  \\ (conj_tac >- metis_tac[line_similar_trans])
  \\ once_rewrite_tac[GSYM APPEND_ASSOC]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ simp[line_similar_def]
  \\ simp[LIST_REL_EL_EQN,line_similar_refl]
QED

(* implications of code_similar *)

Theorem code_similar_MAP_Section_num:
   ∀c1 c2.
   code_similar c1 c2 ⇒
   MAP Section_num c1 = MAP Section_num c2
Proof
  recInduct code_similar_ind
  \\ rw[code_similar_def]
QED

Theorem code_similar_extract_labels:
   ∀code1 code2. code_similar code1 code2 ⇒
   MAP (extract_labels o Section_lines) code1 =
   MAP (extract_labels o Section_lines) code2
Proof
  recInduct code_similar_ind
  \\ rw[code_similar_def]
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ qid_spec_tac`lines2`
  \\ qid_spec_tac`lines1`
  \\ Induct \\ simp[]
  \\ Cases \\ simp[extract_labels_def,PULL_EXISTS]
  \\ Cases \\ simp[line_similar_def]
QED

Theorem code_similar_loc_to_pc:
   ∀l1 l2 c1 c2. code_similar c1 c2 ⇒
     loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2
Proof
  ho_match_mp_tac loc_to_pc_ind
  >> simp[code_similar_nil]
  >> srw_tac[][]
  >> Cases_on`c2`>>full_simp_tac(srw_ss())[code_similar_def]
  >> Cases_on`h`>>full_simp_tac(srw_ss())[code_similar_def]
  >> Cases_on`xs`>>full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][Once loc_to_pc_def]
    >> srw_tac[][Once loc_to_pc_def,SimpRHS]
    >> first_x_assum (match_mp_tac o MP_CANON)
    >> full_simp_tac(srw_ss())[] )
  \\ rveq
  \\ simp[Once loc_to_pc_def]
  \\ simp[Once loc_to_pc_def,SimpRHS]
  \\ match_mp_tac COND_CONG \\ simp[]
  \\ disch_then assume_tac
  \\ match_mp_tac COND_CONG \\ simp[]
  \\ conj_asm1_tac >- (
    Cases_on`h`>>Cases_on`y`>>full_simp_tac(srw_ss())[line_similar_def] )
  \\ disch_then assume_tac
  \\ match_mp_tac COND_CONG
  \\ conj_asm1_tac >- (
    Cases_on`h`>>Cases_on`y`>>full_simp_tac(srw_ss())[line_similar_def] )
  \\ srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  rveq >> rev_full_simp_tac(srw_ss())[]
  \\ TRY (ntac 2 AP_THM_TAC >> AP_TERM_TAC)
  \\ first_x_assum (match_mp_tac o MP_CANON)
  \\ srw_tac[][code_similar_def]
QED

(* sec_label_ok preservation *)

Theorem enc_sec_list_sec_labels_ok:
   ∀enc code.
   EVERY sec_labels_ok code
   ⇒ EVERY sec_labels_ok (enc_sec_list enc code)
Proof
  rw[enc_sec_list_def,EVERY_MAP]
  \\ Induct_on`code` \\ fs[]
  \\ Cases \\ fs[sec_labels_ok_def,enc_sec_def,EVERY_MAP]
  \\ rw[] \\ fs[EVERY_MEM]
  \\ Cases \\ fs[enc_line_def]
  \\ strip_tac \\ res_tac \\ fs[]
QED

Triviality enc_lines_again_sec_labels_ok:
  ∀labs ffis pos enc lines acc ok res ok' k.
    enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
    EVERY (sec_label_ok k) acc ∧
    EVERY (sec_label_ok k) lines ⇒
    EVERY (sec_label_ok k) res
Proof
  recInduct enc_lines_again_ind \\ rw[enc_lines_again_def]
  \\ rw[EVERY_REVERSE]
QED

Theorem enc_secs_again_sec_labels_ok:
   ∀pos ffis labs enc ls res ok k.
    enc_secs_again pos ffis labs enc ls = (res,ok) ∧ EVERY sec_labels_ok ls ⇒
    EVERY sec_labels_ok res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ match_mp_tac enc_lines_again_sec_labels_ok
  \\ asm_exists_tac \\ fs[]
QED

Triviality lines_upd_lab_len_sec_label_ok:
  ∀pos lines acc k.
     EVERY (sec_label_ok k) lines ∧
     EVERY (sec_label_ok k) acc ⇒
     EVERY (sec_label_ok k) (FST (lines_upd_lab_len pos lines acc))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ rw[EVERY_REVERSE]
QED

Theorem upd_lab_len_sec_labels_ok:
   ∀n ls. EVERY sec_labels_ok ls ⇒ EVERY sec_labels_ok (upd_lab_len n ls)
Proof
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def]
  \\ pairarg_tac \\ fs[]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac lines_upd_lab_len_sec_label_ok
  \\ rw[]
QED

Triviality add_nop_sec_label_ok:
  ∀nop aux.
    EVERY (sec_label_ok k) aux ⇒
    EVERY (sec_label_ok k) (add_nop nop aux)
Proof
  recInduct add_nop_ind
  \\ rw[add_nop_def]
QED

Triviality pad_section_sec_label_ok:
  ∀nop xs acc k.
    EVERY (sec_label_ok k) xs ∧
    EVERY (sec_label_ok k) acc ⇒
    EVERY (sec_label_ok k) (pad_section nop xs acc)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def]
  \\ rw[EVERY_REVERSE] \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ metis_tac[add_nop_sec_label_ok]
QED

Theorem pad_code_sec_labels_ok:
   ∀nop code.
    EVERY sec_labels_ok code ⇒
    EVERY sec_labels_ok (pad_code nop code)
Proof
  recInduct pad_code_ind
  \\ rw[pad_code_def]
  \\ match_mp_tac pad_section_sec_label_ok
  \\ rw[]
QED

Theorem sec_labels_ok_filter_skip[simp]:
   ∀code. EVERY sec_labels_ok (filter_skip code) ⇔ EVERY sec_labels_ok code
Proof
  Induct \\ simp[lab_filterTheory.filter_skip_def]
  \\ Cases \\ fs[lab_filterTheory.filter_skip_def,EVERY_FILTER]
  \\ rw[EQ_IMP_THM,EVERY_MEM]
  \\ Cases_on`e` \\ fs[]
  \\ res_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ EVAL_TAC
QED

(* invariant: lines are encoded and non-label lengths annotated *)

Definition line_encd0_def:
  (line_encd0 enc (Asm b bytes len) ⇔
    enc (cbw_to_asm b) = bytes ∧ len = LENGTH bytes) ∧
  (line_encd0 enc (LabAsm l w bytes len) ⇔
     enc (lab_inst w l) = bytes ∧ LENGTH bytes ≤ len ∧
     (∃w'. len = LENGTH (enc (lab_inst w' l)))) ∧
  (line_encd0 enc _ ⇔ T)
End

Definition sec_encd0_def:
  sec_encd0 enc (Section _ ls) = EVERY (line_encd0 enc) ls
End
val _ = export_rewrites["sec_encd0_def"];

Overload all_encd0 = ``λenc l. EVERY (sec_encd0 enc) l``

(* establishing encd0 *)

Theorem enc_sec_list_encd0:
   ∀ls. all_encd0 enc (enc_sec_list enc ls)
Proof
  Induct \\ fs[enc_sec_list_def]
  \\ Cases \\ simp[enc_sec_def,EVERY_MAP]
  \\ simp[EVERY_MEM]
  \\ Cases \\ simp[enc_line_def,line_encd0_def]
  \\ metis_tac[]
QED

(* encd0 preservation *)

Theorem enc_lines_again_encd0:
   ∀labs ffis pos enc lines acc ok res ok'.
    enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
    EVERY (line_encd0 enc) lines ∧
    EVERY (line_encd0 enc) acc ⇒
    EVERY (line_encd0 enc) res
Proof
  recInduct enc_lines_again_ind
  \\ rw[enc_lines_again_def]
  \\ rw[EVERY_REVERSE] \\ fs[]
  \\ fs[line_encd0_def]
  \\ first_x_assum match_mp_tac
  \\ rw[MAX_DEF] \\ metis_tac[]
QED

Theorem enc_secs_again_encd0:
   ∀pos labs ffis enc ls res ok.
    enc_secs_again pos labs ffis enc ls = (res,ok) ∧
    all_encd0 enc ls ⇒
    all_encd0 enc res
Proof
  ho_match_mp_tac enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[] \\ rw[]
  \\ match_mp_tac enc_lines_again_encd0
  \\ asm_exists_tac \\ fs[]
QED

Theorem lines_upd_lab_len_encd0:
   ∀pos ls acc.
    EVERY (line_encd0 enc) ls ∧
    EVERY (line_encd0 enc) acc ⇒
    EVERY (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ fs[EVERY_REVERSE,line_encd0_def]
QED

Theorem upd_lab_len_encd0:
   ∀pos ss. all_encd0 enc ss ⇒ all_encd0 enc (upd_lab_len pos ss)
Proof
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def] \\ fs[]
  \\ rw[UNCURRY]
  >- (
    match_mp_tac lines_upd_lab_len_encd0
    \\ fs[])
  \\ first_x_assum match_mp_tac
  \\ metis_tac[PAIR]
QED

(* invariant: annotated lengths are not too small *)
(* this is a consequence of encd (below) and not treated separately much *)

Definition line_length_leq_def:
  (line_length_leq (LabAsm _ _ bytes l) ⇔
    LENGTH bytes ≤ l) ∧
  (line_length_leq (Asm _ bytes l) ⇔
    LENGTH bytes ≤ l) ∧
  (line_length_leq _ ⇔ T)
End
val _ = export_rewrites["line_length_leq_def"];

Definition sec_length_leq_def:
  sec_length_leq (Section _ ls) = EVERY line_length_leq ls
End
val _ = export_rewrites["sec_length_leq_def"];

Overload all_length_leq = ``λl. EVERY sec_length_leq l``

(* invariant: label annotated lengths are 0 or 1 *)

Definition label_one_def:
  (label_one (Label _ _ n) ⇔ n ≤ 1) ∧
  (label_one _ ⇔ T)
End
val _ = export_rewrites["label_one_def"];

Definition sec_label_one_def:
  sec_label_one (Section _ ls) = EVERY label_one ls
End
val _ = export_rewrites["sec_label_one_def"];

(* establishing label_one *)

Theorem lines_upd_lab_len_label_one:
   ∀pos ls acc.
    EVERY label_one acc ⇒
    EVERY label_one (FST (lines_upd_lab_len pos ls acc))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def] \\ fs[EVERY_REVERSE]
QED

Theorem upd_lab_len_label_one:
   ∀pos ss. EVERY sec_label_one (upd_lab_len pos ss)
Proof
  ho_match_mp_tac upd_lab_len_ind
  \\ rw[upd_lab_len_def]
  \\ pairarg_tac \\ fs[]
  \\ metis_tac[lines_upd_lab_len_label_one,FST,EVERY_DEF]
QED

(* label_one preservation *)

Theorem enc_lines_again_simp_label_one:
   ∀labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) ∧
    EVERY label_one ls ⇒
    EVERY label_one res
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def] \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
QED

Theorem enc_secs_again_label_one:
   ∀pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) ∧
    EVERY sec_label_one lines ⇒
    EVERY sec_label_one res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ match_mp_tac enc_lines_again_simp_label_one
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ rw[]
  \\ metis_tac[]
QED

(* simple consequences of label_one *)

Theorem line_length_pad_section1:
   ∀nop ls acc.
   LENGTH nop = 1 ∧
   EVERY label_one ls ∧
   EVERY line_length_leq ls ∧
   ¬EVERY is_Label acc ∧
   SUM (MAP line_length acc) = SUM (MAP line_len acc)
   ⇒
   SUM (MAP line_length (pad_section nop ls acc)) =
   SUM (MAP line_len ls) + SUM (MAP line_len acc)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def]
  \\ fs[MAP_REVERSE,SUM_REVERSE,line_length_def,LENGTH_pad_bytes]
  \\ fs[line_length_add_nop1,line_len_add_nop1]
QED

Theorem line_len_pad_section1:
   ∀nop xs aux.
   LENGTH nop = 1 ∧
   EVERY label_one xs ∧
   ¬EVERY is_Label aux
   ⇒
   SUM (MAP line_len (pad_section nop xs aux)) =
   SUM (MAP line_len xs) + SUM (MAP line_len aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,MAP_REVERSE,SUM_REVERSE,line_len_add_nop1]
QED

(* invariant: lines are encoded and annotated lengths are correct *)

Definition line_encd_def:
  (line_encd enc labs ffis pos (Asm b bytes len) ⇔
    enc (cbw_to_asm b) = bytes ∧ len = LENGTH bytes) ∧
  (line_encd enc labs ffis pos (LabAsm Halt _ bytes len) ⇔
    enc (Jump (-n2w (pos + ffi_offset))) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm Install _ bytes len) ⇔
    enc (Jump (-n2w (pos + 2 * ffi_offset))) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm (CallFFI s) _ bytes len) ⇔
    enc (Jump (-n2w (pos + (get_ffi_index ffis (ExtCall s) + 3) * ffi_offset))) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm (Jump l) _ bytes len) ⇔
    enc (Jump (n2w (find_pos l labs) + -n2w pos)) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm (JumpCmp a b c l) _ bytes len) ⇔
    enc (JumpCmp a b c (n2w (find_pos l labs) + -n2w pos)) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm (LocValue k l) _ bytes len) ⇔
    enc (Loc k (n2w (find_pos l labs) + -n2w pos)) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos (LabAsm (Call l) _ bytes len) ⇔
    enc (Call (n2w (find_pos l labs) + -n2w pos)) = bytes ∧
    LENGTH bytes ≤ len) ∧
  (line_encd enc labs ffis pos _ ⇔ T)
End

val line_encd_ind = theorem"line_encd_ind";

Definition lines_encd_def:
  (lines_encd enc labs ffis pos [] ⇔ T) ∧
  (lines_encd enc labs ffis pos (l::ls) ⇔
   line_encd enc labs ffis pos l ∧
   lines_encd enc labs ffis (pos+line_len l) ls)
End

Definition all_encd_def:
  (all_encd enc labs ffis pos [] ⇔ T) ∧
  (all_encd enc labs ffis pos (Section k ls::ss) ⇔
   lines_encd enc labs ffis pos ls ∧
   all_encd enc labs ffis (pos + SUM (MAP line_len ls)) ss)
End

(* length_leq follows from encd *)

Theorem line_encd_length_leq:
   ∀enc labs ffis pos l. line_encd enc labs ffis pos l ⇒ line_length_leq l
Proof
  recInduct line_encd_ind \\ rw[line_encd_def,line_length_leq_def]
QED

Theorem lines_encd_length_leq:
   ∀enc labs ffis pos ls. lines_encd enc labs ffis pos ls ⇒ EVERY line_length_leq ls
Proof
  Induct_on`ls` \\ rw[lines_encd_def]
  \\ metis_tac[line_encd_length_leq]
QED

Theorem all_encd_length_leq:
   ∀enc labs ffis pos ls. all_encd enc labs ffis pos ls ⇒ all_length_leq ls
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ simp[all_encd_def]
  \\ metis_tac[lines_encd_length_leq]
QED

(* establishing encd *)

Theorem enc_lines_again_simp_encd:
   ∀labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ∧
    EVERY label_one lines ∧
    EVERY (line_encd0 enc) lines
    ⇒
    lines_encd enc labs ffis pos res
Proof
  ho_match_mp_tac enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ fs[lines_encd_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ simp[lines_encd_def]
  \\ fs[line_encd0_def,line_encd_def,line_length_def]
  \\ TRY (
    qmatch_assum_abbrev_tac`MAX l1 l = l`
    \\ `l1 ≤ l` by fs[MAX_DEF])
  \\ Cases_on`a` \\ fs[line_encd_def,get_jump_offset_def,lab_inst_def,get_label_def]
QED

Theorem enc_secs_again_encd:
   ∀pos labs ffis enc ls res.
    enc_secs_again pos labs ffis enc ls = (res,T) ∧
    EVERY sec_label_one ls ∧
    EVERY (sec_encd0 enc) ls
    ⇒
    all_encd enc labs ffis pos res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def]
  \\ fs[all_encd_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[all_encd_def]
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ fs[] \\ strip_tac \\ rveq
  \\ fs[sec_length_sum_line_len]
  \\ imp_res_tac enc_lines_again_simp_len \\ fs[]
  \\ imp_res_tac enc_lines_again_simp_encd
QED

(* invariant: annotated lengths are correct *)

Definition line_length_ok_def:
  line_length_ok l ⇔ LENGTH (line_bytes l) = line_len l
End

Definition sec_length_ok_def:
  sec_length_ok (Section _ ls) = EVERY line_length_ok ls
End

(* simple consequences of length_ok *)

Theorem sec_length_sum_line_length:
   ∀ls n.
    EVERY line_length_ok ls ⇒
    (sec_length ls n = SUM (MAP line_length ls) + n)
Proof
  ho_match_mp_tac sec_length_ind
  \\ rw[sec_length_def,line_length_def]
  \\ fs[line_length_ok_def,line_bytes_def,line_length_def]
QED

(* invariant: all labels annotated with length 0 *)

Definition label_zero_def:
  (label_zero (Label _ _ n) ⇔ n = 0) ∧
  (label_zero _ ⇔ T)
End
val _ = export_rewrites["label_zero_def"];

Definition sec_label_zero_def:
  sec_label_zero (Section _ ls) = EVERY label_zero ls
End

(* label_zero preservation *)

Triviality EVERY_label_zero_add_nop:
  !xs. EVERY label_zero (add_nop nop xs) = EVERY label_zero xs
Proof
  Induct \\ fs [add_nop_def,EVERY_REVERSE]
  \\ Cases \\ fs [add_nop_def,EVERY_REVERSE]
QED

Theorem EVERY_label_zero_pad_section[simp]:
   ∀nop xs aux.
     EVERY label_zero aux ⇒
     EVERY label_zero (pad_section nop xs aux)
Proof
  ho_match_mp_tac pad_section_ind
  >> srw_tac[][pad_section_def]
  >> srw_tac[][EVERY_REVERSE]>>
  first_assum match_mp_tac>>fs[EVERY_label_zero_add_nop]
QED

Theorem EVERY_sec_label_zero_pad_code[simp]:
   ∀nop ls. EVERY sec_label_zero (pad_code nop ls)
Proof
  ho_match_mp_tac pad_code_ind
  \\ srw_tac[][pad_code_def] \\ fs []
  \\ srw_tac[][sec_label_zero_def]
  \\ unabbrev_all_tac \\ fs []
  \\ fs [EVERY_REVERSE,EVERY_label_zero_add_nop]
QED

Theorem enc_lines_again_simp_label_zero:
   ∀labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) ∧
    EVERY label_zero ls ⇒
    EVERY label_zero res
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def] \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
QED

Theorem enc_secs_again_label_zero:
   ∀pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) ∧
    EVERY sec_label_zero lines ⇒
    EVERY sec_label_zero res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[sec_label_zero_def]
  \\ match_mp_tac enc_lines_again_simp_label_zero
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ rw[]
  \\ metis_tac[]
QED

Theorem lines_upd_lab_len_encd0_label_zero:
   ∀pos lines aux.
    enc_ok c ∧ enc = c.encode ∧ c.code_alignment ≠ 0 ∧
    EVERY (line_encd0 enc) lines ∧ EVEN pos ∧
    EVERY label_zero aux ⇒
    EVERY label_zero (FST (lines_upd_lab_len pos lines aux))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def,EVERY_REVERSE]
  \\ first_x_assum match_mp_tac
  \\ fs[EVEN_ADD,line_encd0_def]
  \\ fs[enc_ok_def]
  \\ rfs[GSYM bitTheory.MOD_2EXP_def]
  \\ metis_tac[MOD_2EXP_0_EVEN,NOT_ZERO_LT_ZERO]
QED

Theorem EVEN_sec_length_lines_upd_lab_len:
   ∀pos lines acc.
    (if NULL lines then
     EVEN pos ∧ EVEN (SUM (MAP line_len acc))
    else is_Label (LAST lines) ∧
         EVEN (pos + (SUM (MAP line_len acc))))
    ⇒
    EVEN (SUM (MAP line_len (FST (lines_upd_lab_len pos lines acc))))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def,MAP_REVERSE,SUM_REVERSE]
  \\ Cases_on`xs` \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ fs[EVEN_ADD,EVEN_MULT]
QED

Theorem upd_lab_len_encd0_label_zero:
   ∀pos code.
    enc_ok c ∧ enc = c.encode ∧ c.code_alignment ≠ 0 ∧
    all_encd0 enc code ∧ EVEN pos ∧ EVERY sec_ends_with_label code ⇒
    EVERY sec_label_zero (upd_lab_len pos code)
Proof
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def,sec_label_zero_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[sec_label_zero_def]
  \\ conj_tac
  >- (
    qspecl_then[`c.encode`,`pos`,`lines`,`[]`]mp_tac (Q.GEN`enc` lines_upd_lab_len_encd0_label_zero)
    \\ simp[] )
  \\ first_x_assum match_mp_tac \\ fs[]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac  SND_lines_upd_lab_len
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac  EVEN_sec_length_lines_upd_lab_len
  \\ fs[sec_ends_with_label_def,EVEN_ADD]
QED

(* simple consequences of label_zero *)

Theorem sec_pos_val_0:
   ∀pos lines. ¬EVERY is_Label lines ∧ EVERY label_zero lines ⇒ sec_pos_val 0 pos lines = SOME pos
Proof
  Induct_on`lines` \\ rw[sec_pos_val_def]
  \\ Cases_on`h` \\ fs[line_length_def]
QED

Theorem line_len_pad_section0:
   ∀nop ls aux.
   EVERY label_zero ls ⇒
   SUM (MAP line_len (pad_section nop ls aux)) =
   SUM (MAP line_len ls) + SUM (MAP line_len aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,MAP_REVERSE,SUM_REVERSE]
QED

Theorem sec_label_zero_pos_val_0:
    ∀xs pos.
  EVERY sec_label_zero xs ⇒
  pos_val 0 pos xs = pos
Proof
  Induct_on`xs`>>srw_tac[][pos_val_def]>>full_simp_tac(srw_ss())[]
  >> Cases_on`h`>>srw_tac[][pos_val_def]
  >> Induct_on`l`
  >> srw_tac[][pos_val_def]
  >> full_simp_tac(srw_ss())[sec_label_zero_def]
  >> Cases_on`h`>>full_simp_tac(srw_ss())[]
  >> srw_tac[][line_length_def]
QED

Theorem all_enc_ok_imp_sec_label_zero:
    !conf labs ffis n code.
  all_enc_ok conf labs ffis n code ⇒
  EVERY sec_label_zero code
Proof
  ho_match_mp_tac all_enc_ok_ind>>
  rw[]>>fs[sec_label_zero_def,all_enc_ok_def]>>
  Cases_on`y`>>fs[line_ok_def]
QED

(* invariant: lines aligned *)

Definition line_aligned_def:
  line_aligned m l ⇔
    line_len l MOD m = 0 ∧
    line_length l MOD m = 0
End

Definition sec_aligned_def:
  sec_aligned noplen (Section _ ls) = EVERY (line_aligned noplen) ls
End
val _ = export_rewrites["sec_aligned_def"];

(* establishing aligned *)

Theorem all_encd0_aligned:
   ∀c enc code.
   enc_ok c ∧ enc = c.encode ∧
   all_encd0 enc code ∧
   EVERY sec_label_zero code ⇒
   EVERY (sec_aligned (LENGTH (enc (Inst Skip)))) code
Proof
  ntac 2 gen_tac
  \\ Induct \\ simp[]
  \\ Cases \\ simp[sec_label_zero_def]
  \\ strip_tac \\ fs[]
  \\ Induct_on`l` \\ fs[]
  \\ Cases
  \\ fs[line_encd0_def,line_aligned_def,line_length_def,enc_ok_def]
  \\ strip_tac \\ rfs[] \\ rveq \\ fs[] \\ rw[]
  \\ match_mp_tac ZERO_MOD
  \\ simp[]
  \\ metis_tac[bitTheory.ZERO_LT_TWOEXP]
QED

(* aligned preservation *)

Theorem enc_lines_again_simp_aligned:
   ∀labs ffis pos enc ls res ok.
    (∀a. LENGTH (enc a) MOD len = 0) ∧
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) ∧
    EVERY (line_aligned len) ls ⇒
    EVERY (line_aligned len) res
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def] \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ fs[line_aligned_def,line_length_def,MAX_DEF]
  \\ IF_CASES_TAC \\ fs[]
QED

Theorem enc_secs_again_aligned:
   ∀pos labs ffis enc lines res ok.
    (∀a. LENGTH (enc a) MOD len = 0) ∧
    enc_secs_again pos labs ffis enc lines = (res,ok) ∧
    EVERY (sec_aligned len) lines ⇒
    EVERY (sec_aligned len) res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ fs[]
  \\ match_mp_tac enc_lines_again_simp_aligned
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ rw[]
  \\ metis_tac[]
QED

(* invariant: all initial labels have annotated length 0 *)

Definition label_prefix_zero_def:
  label_prefix_zero ls ⇔
     (∀n. n < LENGTH ls ∧ (∀m. m ≤ n ⇒ is_Label (EL m ls)) ⇒
        ∀m. m ≤ n ⇒ line_len (EL m ls) = 0)
End

Definition sec_label_prefix_zero_def:
  sec_label_prefix_zero (Section k ls) ⇔ label_prefix_zero ls
End
val _ = export_rewrites["sec_label_prefix_zero_def"];

Theorem label_prefix_zero_cons:
   (label_prefix_zero (Label l1 l2 len::ls) ⇔ ((len = 0) ∧ label_prefix_zero ls)) ∧
   (label_prefix_zero (Asm a b c::ls) ⇔ T) ∧
   (label_prefix_zero (LabAsm d e f g::ls) ⇔ T)
Proof
  rw[label_prefix_zero_def]
  \\ TRY (
    Cases_on`n` \\ fs[]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ simp[] \\ NO_TAC)
  \\ rw[EQ_IMP_THM]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ simp[] )
  >- (
    last_x_assum(qspec_then`SUC m`mp_tac) \\ simp[]
    \\ impl_tac >- (Cases \\ simp[])
    \\ disch_then(qspec_then`SUC m`mp_tac) \\ simp[] )
  \\ Cases_on`m` \\ fs[]
  \\ Cases_on`n` \\ fs[]
  \\ first_x_assum(match_mp_tac o MP_CANON)
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
  \\ simp[]
  \\ qx_gen_tac`z` \\ strip_tac
  \\ first_x_assum(qspec_then`SUC z`mp_tac)
  \\ simp[]
QED

(* establishing label_prefix_zero *)

Theorem label_prefix_zero_append_suff:
   ∀l1 l2.
   label_prefix_zero l1 ∧ label_prefix_zero l2 ⇒
   label_prefix_zero (l1 ++ l2)
Proof
  Induct
  >- simp[label_prefix_zero_def]
  \\ Cases \\ simp[label_prefix_zero_cons]
QED

Theorem label_prefix_zero_append_suff2:
   ∀l1 l2.
   label_prefix_zero l1 ∧ EXISTS ($~ o is_Label) l1 ⇒
   label_prefix_zero (l1 ++ l2)
Proof
  Induct
  >- simp[label_prefix_zero_def]
  \\ Cases \\ simp[label_prefix_zero_cons]
QED

Theorem lines_upd_lab_len_label_prefix_zero:
   ∀pos ls acc.
    (EVERY is_Label acc ⇒ EVEN pos) ∧ label_prefix_zero (REVERSE acc) ⇒
    label_prefix_zero (FST (lines_upd_lab_len pos ls acc))
Proof
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ first_x_assum match_mp_tac \\ fs[EVEN_ADD]
  \\ TRY (
    match_mp_tac label_prefix_zero_append_suff \\ fs[]
    \\ fs[label_prefix_zero_def] \\ NO_TAC)
  \\ match_mp_tac label_prefix_zero_append_suff2
  \\ simp[EXISTS_REVERSE]
QED

Theorem upd_lab_len_label_prefix_zero:
   ∀pos ss.
    EVEN pos ∧ EVERY sec_ends_with_label ss ⇒
    EVERY sec_label_prefix_zero (upd_lab_len pos ss)
Proof
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def]
  \\ pairarg_tac \\ fs[]
  \\ conj_tac
  >- (
    `label_prefix_zero (REVERSE [])` by simp[label_prefix_zero_def]
    \\ metis_tac[lines_upd_lab_len_label_prefix_zero,FST])
  \\ first_x_assum match_mp_tac
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac SND_lines_upd_lab_len
  \\ simp[EVEN_ADD]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac EVEN_sec_length_lines_upd_lab_len
  \\ fs[sec_ends_with_label_def]
QED

(* label_prefix_zero preservation *)

Theorem enc_lines_again_simp_label_prefix_zero:
   ∀labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) ∧
    label_prefix_zero ls ⇒
    label_prefix_zero res
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ fs[]
  \\ rveq \\ fs[label_prefix_zero_cons]
QED

Theorem enc_secs_again_label_prefix_zero:
   ∀pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) ∧
    EVERY sec_label_prefix_zero lines ⇒
    EVERY sec_label_prefix_zero res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ match_mp_tac enc_lines_again_simp_label_prefix_zero
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ rw[]
  \\ metis_tac[]
QED

(* simple consequences of label_prefix_zero *)

Theorem line_length_pad_section:
   ∀nop ls acc.
   LENGTH nop = 1 ∧
   EVERY label_one ls ∧
   EVERY line_length_leq ls ∧
   SUM (MAP line_length acc) = SUM (MAP line_len acc) ∧
   EVERY is_Label acc ∧ label_prefix_zero ls
   ⇒
   SUM (MAP line_length (pad_section nop ls acc)) =
   SUM (MAP line_len ls) + SUM (MAP line_len acc)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def]
  \\ fs[MAP_REVERSE,SUM_REVERSE,line_length_def,LENGTH_pad_bytes,label_prefix_zero_cons]
  \\ fs[line_length_add_nop,line_len_add_nop]
  \\ qmatch_goalsub_abbrev_tac`pad_section nop xs acc'`
  \\ qspecl_then[`nop`,`xs`,`acc'`]mp_tac line_length_pad_section1
  \\ simp[Abbr`acc'`,line_length_def,LENGTH_pad_bytes]
QED

Theorem label_zero_line_length_pad_section:
   ∀nop ls acc.
   0 < LENGTH nop ∧
   EVERY label_zero ls ∧
   MAP line_length acc = MAP line_len acc ∧
   EVERY line_length_leq ls
   ⇒
   MAP line_length (pad_section nop ls acc) =
   MAP line_len (REVERSE acc ++ ls)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,line_length_def,MAP_REVERSE]
  \\ fs[pad_section_def]
  \\ fs[LENGTH_pad_bytes]
QED

(* invariant: lines encd with nops *)

Definition line_enc_with_nop_def:
  (line_enc_with_nop enc labs ffis pos (Asm b bytes len) ⇔
    enc_with_nop enc (cbw_to_asm b) bytes ∧ LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm Halt _ bytes len) ⇔
    enc_with_nop enc (Jump (-n2w (pos + ffi_offset))) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm Install _ bytes len) ⇔
    enc_with_nop enc (Jump (-n2w (pos + 2 * ffi_offset))) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm (CallFFI s) _ bytes len) ⇔
    enc_with_nop enc (Jump (-n2w (pos + (get_ffi_index ffis (ExtCall s) + 3) * ffi_offset))) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm (Jump l) _ bytes len) ⇔
    enc_with_nop enc (Jump (n2w (find_pos l labs) + -n2w pos)) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm (JumpCmp a b c l) _ bytes len) ⇔
    enc_with_nop enc (JumpCmp a b c (n2w (find_pos l labs) + -n2w pos)) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm (LocValue k l) _ bytes len) ⇔
    enc_with_nop enc (Loc k (n2w (find_pos l labs) + -n2w pos)) bytes ∧
    LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (LabAsm _ _ bytes len) ⇔ LENGTH bytes = len) ∧
  (line_enc_with_nop enc labs ffis pos (Label _ _ len) ⇔ len = 0)
End

val line_enc_with_nop_ind = theorem"line_enc_with_nop_ind";

Definition lines_enc_with_nop_def:
  (lines_enc_with_nop enc labs ffis pos [] ⇔ T) ∧
  (lines_enc_with_nop enc labs ffis pos (l::ls) ⇔
   line_enc_with_nop enc labs ffis pos l ∧
   lines_enc_with_nop enc labs ffis (pos+line_length l) ls)
End

Theorem lines_enc_with_nop_append:
   ∀enc labs ffis pos l1 l2.
   lines_enc_with_nop enc labs ffis pos (l1 ++ l2) ⇔
   lines_enc_with_nop enc labs ffis pos l1 ∧
   lines_enc_with_nop enc labs ffis (pos + SUM (MAP line_length l1)) l2
Proof
  Induct_on`l1` \\ rw[lines_enc_with_nop_def,EQ_IMP_THM]
QED

Definition all_enc_with_nop_def:
  (all_enc_with_nop enc labs ffis pos [] ⇔ T) ∧
  (all_enc_with_nop enc labs ffis pos (Section k []::xs) ⇔
   all_enc_with_nop enc labs ffis pos xs) ∧
  (all_enc_with_nop enc labs ffis pos (Section k (y::ys)::xs) ⇔
   line_enc_with_nop enc labs ffis pos y ∧
   all_enc_with_nop enc labs ffis (pos + line_length y) (Section k ys::xs))
End

val all_enc_with_nop_ind = theorem"all_enc_with_nop_ind";

Theorem all_enc_with_nop_alt:
   (all_enc_with_nop enc labs ffis pos [] ⇔ T) ∧
   (all_enc_with_nop enc labs ffis pos (Section k ls::ss) ⇔
    lines_enc_with_nop enc labs ffis pos ls ∧
    all_enc_with_nop enc labs ffis (pos + SUM (MAP line_length ls)) ss)
Proof
  rw[all_enc_with_nop_def]
  \\ map_every qid_spec_tac[`pos`,`ls`]
  \\ Induct \\ rw[all_enc_with_nop_def,lines_enc_with_nop_def]
  \\ rw[EQ_IMP_THM]
QED

(* enc_with_nop implies length_ok *)

Theorem line_enc_with_nop_length_ok:
   ∀enc labs ffis pos line.
    line_enc_with_nop enc labs ffis pos line ⇒ line_length_ok line
Proof
  recInduct line_enc_with_nop_ind
  \\ rw[line_enc_with_nop_def,line_length_ok_def,line_length_def,line_bytes_def]
QED

Theorem lines_enc_with_nop_length_ok:
   ∀enc labs ffis pos ls. lines_enc_with_nop enc labs ffis pos ls ⇒ EVERY line_length_ok ls
Proof
  Induct_on`ls` \\ simp[lines_enc_with_nop_def]
  \\ Cases \\ simp[line_length_ok_def,line_bytes_def,line_enc_with_nop_def,line_length_def]
  \\ rw[]
  \\ TRY(first_x_assum match_mp_tac \\ metis_tac[])
  \\ Cases_on`a` \\ fs[line_enc_with_nop_def]
QED

(* enc_with_nop implies label_zero *)

Theorem line_enc_with_nop_label_zero:
   ∀enc labs ffis pos line.
    line_enc_with_nop enc labs ffis pos line ⇒ label_zero line
Proof
  recInduct line_enc_with_nop_ind
  \\ rw[line_enc_with_nop_def]
QED

Theorem lines_enc_with_nop_label_zero:
   ∀enc labs ffis pos lines.
     lines_enc_with_nop enc labs ffis pos lines ⇒ EVERY label_zero lines
Proof
  Induct_on`lines`
  \\ rw[lines_enc_with_nop_def]
  \\ metis_tac[line_enc_with_nop_label_zero]
QED

Theorem all_enc_with_nop_label_zero:
   ∀enc labs ffis pos ls.
    all_enc_with_nop enc labs ffis pos ls ⇒
    EVERY sec_label_zero ls
Proof
  recInduct all_enc_with_nop_ind
  \\ rw[all_enc_with_nop_def,sec_label_zero_def]
  \\ metis_tac[line_enc_with_nop_label_zero]
QED

(* line_ok implies enc_with_nop *)

Theorem line_ok_line_enc_with_nop:
   ∀c labs ffis pos line.
    line_ok c labs ffis pos line ⇒
    line_enc_with_nop c.encode labs ffis pos line
Proof
  recInduct line_ok_ind
  \\ rw[line_ok_def,line_enc_with_nop_def,get_label_def,lab_inst_def]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP
  \\ rw[line_ok_def,line_enc_with_nop_def,get_label_def,lab_inst_def]
QED

Theorem lines_ok_lines_enc_with_nop:
   ∀c labs ffis pos lines.
    lines_ok c labs ffis pos lines ⇒
    lines_enc_with_nop c.encode labs ffis pos lines
Proof
  Induct_on`lines` \\ rw[lines_ok_def,lines_enc_with_nop_def]
  \\ metis_tac[line_ok_line_enc_with_nop]
QED

(* establishing enc_with_nop *)

Theorem enc_with_nop_pad_bytes_length:
   enc_with_nop enc x (pad_bytes (enc x) (LENGTH (enc x)) (enc (Inst Skip)))
Proof
  rw[enc_with_nop_thm,pad_bytes_def]
  \\ qexists_tac`0` \\ simp[REPLICATE]
QED

Theorem enc_with_nop_pad_bytes:
   nop = enc (Inst Skip) ∧ LENGTH (enc x) ≤ len ∧
   LENGTH (enc x) MOD (LENGTH nop) = 0 ∧
   len MOD (LENGTH nop) = 0 ∧
   0 < LENGTH nop
   ⇒ enc_with_nop enc x (pad_bytes (enc x) len nop)
Proof
  rw[enc_with_nop_thm,pad_bytes_def]
  >- (qexists_tac`0` \\ simp[REPLICATE])
  \\ simp[TAKE_APPEND2]
  \\ drule (GEN_ALL MOD_EQ_0_DIVISOR)
  \\ disch_then (drule o #1 o EQ_IMP_RULE o SPEC_ALL)
  \\ qpat_x_assum`LENGTH _ MOD _ = _`assume_tac
  \\ drule (GEN_ALL MOD_EQ_0_DIVISOR)
  \\ disch_then (drule o #1 o EQ_IMP_RULE o SPEC_ALL)
  \\ rw[] \\ rw[] \\ fs[]
  \\ fs[NOT_LESS_EQUAL]
  \\ fs[GSYM RIGHT_SUB_DISTRIB]
  \\ qmatch_goalsub_rename_tac`a:num - b`
  \\ qexists_tac`a-b`
  \\ once_rewrite_tac[MULT_COMM]
  \\ match_mp_tac TAKE_FLAT_REPLICATE_LEQ \\ simp[]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`a * LENGTH (enc (Inst Skip))`
  \\ simp[]
QED

Theorem lines_enc_with_nop_add_nop:
   ∀enc labs ffis pos ls.
    LENGTH (enc (Inst Skip)) = 1 ∧
    lines_enc_with_nop enc labs ffis pos (REVERSE ls) ⇒
    lines_enc_with_nop enc labs ffis pos
      (REVERSE (add_nop (enc (Inst Skip)) ls))
Proof
  Induct_on`ls`
  \\ rw[lines_enc_with_nop_def,add_nop_def]
  \\ simp[add_nop_append,REVERSE_APPEND,lines_enc_with_nop_append,lines_enc_with_nop_def]
  \\ Cases_on`h`\\fs[add_nop_def,line_enc_with_nop_def,EVERY_REVERSE]
  \\ rw[] \\ fs[lines_enc_with_nop_append,REVERSE_APPEND,lines_enc_with_nop_def,line_enc_with_nop_def]
  \\ fs[line_length_def]
  >- (
    fs[enc_with_nop_thm,LENGTH_EQ_NUM_compute]
    \\ qmatch_goalsub_rename_tac`REPLICATE z`
    \\ qexists_tac`SUC z`
    \\ rewrite_tac[REPLICATE_GENLIST]
    \\ simp[GENLIST,SNOC_APPEND] )
  \\ Cases_on`a` \\ fs[line_enc_with_nop_def]
  \\ fs[enc_with_nop_thm,LENGTH_EQ_NUM_compute]
  \\ qmatch_goalsub_rename_tac`REPLICATE z`
  \\ qexists_tac`SUC z`
  \\ rewrite_tac[REPLICATE_GENLIST]
  \\ simp[GENLIST,SNOC_APPEND]
QED

Theorem lines_enc_with_nop_pad_section1:
   ∀nop code aux pos.
    nop = enc (Inst Skip) ∧ LENGTH nop = 1 ∧
    lines_encd enc labs ffis (pos + (SUM (MAP line_len aux))) code ∧
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) ∧
    ¬EVERY is_Label aux ∧
    EVERY label_one code
    ⇒
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lines_enc_with_nop_append]
  \\ fs[lines_enc_with_nop_def,line_enc_with_nop_def]
  \\ first_x_assum match_mp_tac
  \\ fs[lines_encd_def]
  \\ fs[line_encd_def]
  \\ fs[line_len_add_nop1,LENGTH_pad_bytes]
  >- (
    `len=1` by simp[] \\ fs[]
    \\ match_mp_tac lines_enc_with_nop_add_nop
    \\ fs[])
  >- (
    rveq
    \\ MATCH_ACCEPT_TAC enc_with_nop_pad_bytes_length )
  >- (
    imp_res_tac lines_enc_with_nop_length_ok
    \\ imp_res_tac sec_length_sum_line_length
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[sec_length_sum_line_len]
    \\ Cases_on`y` \\ fs[line_encd_def,line_enc_with_nop_def]
    \\ rveq \\ fs[MAP_REVERSE,SUM_REVERSE,LENGTH_pad_bytes]
    \\ qmatch_abbrev_tac`enc_with_nop enc x (pad_bytes (enc x) len nop)`
    \\ match_mp_tac enc_with_nop_pad_bytes \\ fs[])
QED

Theorem lines_enc_with_nop_pad_section01:
   ∀nop code aux pos.
    nop = enc (Inst Skip) ∧ 0 < LENGTH nop ∧
    EVERY (line_aligned (LENGTH nop)) code ∧
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code ∧
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) ∧
    ¬EVERY is_Label aux ∧ EVERY label_zero code ⇒
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lines_enc_with_nop_def]
  \\ first_x_assum match_mp_tac
  \\ fs[lines_enc_with_nop_append,lines_enc_with_nop_def,line_enc_with_nop_def]
  \\ fs[lines_encd_def,line_encd_def,LENGTH_pad_bytes]
  \\ rveq
  \\ TRY (MATCH_ACCEPT_TAC enc_with_nop_pad_bytes_length)
  \\ fs[line_aligned_def,line_length_def]
  \\ Cases_on`y`
  \\ fs[lines_encd_def,line_encd_def,LENGTH_pad_bytes,line_enc_with_nop_def]
  \\ rveq
  \\ imp_res_tac lines_enc_with_nop_length_ok
  \\ imp_res_tac sec_length_sum_line_length
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ rw[sec_length_sum_line_len]
  \\ fs[MAP_REVERSE,SUM_REVERSE]
  \\ match_mp_tac enc_with_nop_pad_bytes \\ fs[]
QED

Theorem lines_enc_with_nop_pad_section0:
   ∀nop code aux pos.
    nop = enc (Inst Skip) ∧ 0 < LENGTH nop ∧
    EVERY (line_aligned (LENGTH nop)) code ∧
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code ∧
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) ∧
    EVERY is_Label aux ∧ EVERY label_zero code ⇒
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lines_enc_with_nop_def]
  \\ TRY (
    first_x_assum match_mp_tac
    \\ fs[lines_enc_with_nop_append,lines_enc_with_nop_def,line_enc_with_nop_def,lines_encd_def])
  \\ match_mp_tac lines_enc_with_nop_pad_section01
  \\ fs[lines_enc_with_nop_append,lines_encd_def,
        lines_enc_with_nop_def,line_enc_with_nop_def,line_encd_def]
  \\ rveq \\ fs[LENGTH_pad_bytes]
  \\ TRY (MATCH_ACCEPT_TAC enc_with_nop_pad_bytes_length)
  \\ fs[line_aligned_def,line_length_def]
  \\ Cases_on`y`
  \\ fs[line_enc_with_nop_def,line_encd_def,LENGTH_pad_bytes]
  \\ rveq
  \\ imp_res_tac lines_enc_with_nop_length_ok
  \\ imp_res_tac sec_length_sum_line_length
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ rw[sec_length_sum_line_len]
  \\ fs[MAP_REVERSE,SUM_REVERSE]
  \\ match_mp_tac enc_with_nop_pad_bytes \\ fs[]
QED

Theorem lines_enc_with_nop_pad_section:
   ∀nop code aux pos.
    nop = enc (Inst Skip) ∧ LENGTH nop = 1 ∧
    lines_encd enc labs ffis (pos + SUM (MAP line_len aux)) code ∧
    lines_enc_with_nop enc labs ffis pos (REVERSE aux) ∧
    EVERY is_Label aux ∧ EVERY label_one code ∧ label_prefix_zero code ⇒
    lines_enc_with_nop enc labs ffis pos (pad_section nop code aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lines_enc_with_nop_append]
  \\ rfs[EVERY_is_Label_add_nop,label_prefix_zero_cons]
  \\ TRY (
    first_x_assum match_mp_tac
    \\ fs[lines_encd_def,line_encd_def,lines_enc_with_nop_def,line_enc_with_nop_def] )
  \\ match_mp_tac lines_enc_with_nop_pad_section1
  \\ simp[lines_enc_with_nop_append]
  \\ TRY (qmatch_goalsub_rename_tac`LabAsm y` \\ Cases_on`y`)
  \\ fs[lines_encd_def,lines_enc_with_nop_def,line_enc_with_nop_def,LENGTH_pad_bytes,line_encd_def]
  \\ rveq \\ TRY (MATCH_ACCEPT_TAC enc_with_nop_pad_bytes_length)
  \\ imp_res_tac lines_enc_with_nop_length_ok
  \\ imp_res_tac sec_length_sum_line_length
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ rw[sec_length_sum_line_len]
  \\ fs[MAP_REVERSE,SUM_REVERSE]
  \\ match_mp_tac enc_with_nop_pad_bytes \\ fs[]
QED

Theorem all_enc_with_nop_pad_code:
   ∀nop code pos.
   0 < LENGTH nop ∧ nop = enc (Inst Skip) ∧
   (LENGTH nop ≠ 1 ⇒ EVERY (sec_aligned (LENGTH nop)) code ∧ EVERY sec_label_zero code) ∧
   EVERY sec_label_one code ∧
   EVERY sec_length_leq code ∧
   EVERY sec_label_prefix_zero code ∧
   all_encd enc labs ffis pos code ⇒
   all_enc_with_nop enc labs ffis pos (pad_code nop code)
Proof
  recInduct pad_code_ind
  \\ reverse(rw[pad_code_def,all_enc_with_nop_alt,all_encd_def])
  \\ fs[]
  >- (
    first_x_assum match_mp_tac
    \\ fs[sec_label_zero_def]
    \\ Cases_on`LENGTH (enc (Inst Skip)) = 1`
    >- (
      qspecl_then[`enc (Inst Skip)`,`xs`,`[]`]mp_tac line_length_pad_section
      \\ simp[] )
    \\ fs[label_zero_line_length_pad_section])
  \\ Cases_on`LENGTH (enc (Inst Skip)) = 1`
  >- (
    match_mp_tac lines_enc_with_nop_pad_section
    \\ fs[lines_enc_with_nop_def] )
  \\ match_mp_tac lines_enc_with_nop_pad_section0
  \\ fs[sec_label_zero_def,lines_enc_with_nop_def]
QED

(* invariant: label annotation correctly records alignment *)

Definition line_lab_len_pos_ok_def:
  (line_lab_len_pos_ok pos (Label _ _ l) ⇔
     if EVEN pos then l = 0 else l = 1) ∧
  (line_lab_len_pos_ok _ _ ⇔ T)
End

Definition lab_len_pos_ok_def:
  (lab_len_pos_ok pos [] ⇔ T) ∧
  (lab_len_pos_ok pos (l::ls) ⇔
     line_lab_len_pos_ok pos l ∧
     lab_len_pos_ok (pos + line_len l) ls)
End

Theorem lab_len_pos_ok_append:
   ∀l1 pos l2.
   lab_len_pos_ok pos (l1 ++ l2) ⇔
   lab_len_pos_ok pos l1 ∧
   lab_len_pos_ok (pos + SUM (MAP line_len l1)) l2
Proof
  Induct \\ simp[lab_len_pos_ok_def]
  \\ metis_tac[]
QED

Definition all_lab_len_pos_ok_def:
  (all_lab_len_pos_ok _ [] ⇔ T) ∧
  (all_lab_len_pos_ok pos (Section k ls::ss) ⇔
   lab_len_pos_ok pos ls ∧
   all_lab_len_pos_ok (pos + sec_length ls 0) ss)
End

val all_lab_len_pos_ok_ind = theorem"all_lab_len_pos_ok_ind";

(* establishing pos_ok *)

Theorem lines_upd_lab_len_pos_ok:
   ∀pos lines.
    lab_len_pos_ok pos (FST (lines_upd_lab_len pos lines []))
Proof
  Induct_on`lines`
  \\ simp[lines_upd_lab_len_def,lab_len_pos_ok_def]
  \\ reverse Cases \\ simp[lines_upd_lab_len_def]
  \\ simp[Once lines_upd_lab_len_AUX,lab_len_pos_ok_def]
  \\ simp[line_lab_len_pos_ok_def]
QED

Theorem upd_lab_len_pos_ok:
   ∀pos code.
    all_lab_len_pos_ok pos (upd_lab_len pos code)
Proof
  recInduct upd_lab_len_ind
  \\ rw[all_lab_len_pos_ok_def,upd_lab_len_def]
  \\ pairarg_tac \\ fs[all_lab_len_pos_ok_def]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac SND_lines_upd_lab_len
  \\ qspecl_then[`pos`,`lines`]mp_tac lines_upd_lab_len_pos_ok
  \\ rw[sec_length_sum_line_len] \\ fs[]
QED

(* pos_ok preservation *)

Theorem enc_lines_again_simp_pos_ok:
   ∀labs ffis pos enc lines res.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ∧
    lab_len_pos_ok pos lines ⇒
    lab_len_pos_ok pos res
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def] \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ fs[lab_len_pos_ok_def]
  \\ fs[line_lab_len_pos_ok_def]
QED

Theorem enc_secs_again_pos_ok:
   ∀pos labs ffis enc code res.
    enc_secs_again pos labs ffis enc code = (res,T) ∧
    all_lab_len_pos_ok pos code ⇒
    all_lab_len_pos_ok pos res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ rw[] \\ pairarg_tac \\ fs[] \\ rveq
  \\ imp_res_tac enc_lines_again_simp_len
  \\ fs[sec_length_sum_line_len,all_lab_len_pos_ok_def]
  \\ imp_res_tac enc_lines_again_simp_pos_ok
QED

Theorem lab_len_pos_ok_even_prefix_zero:
   ∀pos ls.
    EVEN pos ∧
    lab_len_pos_ok pos ls ⇒
    label_prefix_zero ls
Proof
  Induct_on`ls`
  >- rw[lab_len_pos_ok_def,label_prefix_zero_def]
  \\ Cases
  \\ rw[lab_len_pos_ok_def,label_prefix_zero_cons,line_lab_len_pos_ok_def]
  \\ fs[] \\ metis_tac[]
QED

Theorem pad_section_pos_ok:
   ∀nop lines aux pos.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines  ∧
    lab_len_pos_ok pos (REVERSE aux) ∧
    EVERY label_zero aux ∧
    ((NULL aux ∨ is_Label (HD aux)) ⇒ label_prefix_zero lines)
    ⇒
    lab_len_pos_ok pos (pad_section nop lines aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lab_len_pos_ok_def]
  \\ fs[pad_section_def]
  \\ first_x_assum match_mp_tac
  \\ fs[lab_len_pos_ok_append,SUM_REVERSE,MAP_REVERSE]
  \\ fs[lab_len_pos_ok_def,line_lab_len_pos_ok_def,label_prefix_zero_cons]
  \\ rfs[]
  >- (
    match_mp_tac lab_len_pos_ok_even_prefix_zero
    \\ metis_tac[] )
  \\ fs[EVEN_ADD]
  \\ `¬EVERY is_Label aux`
  by ( Cases_on`aux` \\ fs[])
  \\ fs[line_len_add_nop1,EVEN_ADD,EVERY_label_zero_add_nop]
  \\ reverse conj_tac
  >- (
    match_mp_tac lab_len_pos_ok_even_prefix_zero
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ fs[EVEN_ADD]
    \\ metis_tac[] )
  \\ reverse conj_tac >- metis_tac[]
  \\ pop_assum kall_tac
  \\ Cases_on`aux`\\fs[]
  \\ Cases_on`h` \\ fs[add_nop_def,lab_len_pos_ok_append]
  \\ fs[lab_len_pos_ok_def,line_lab_len_pos_ok_def]
QED

Theorem line_len_pad_section:
   ∀nop xs aux.
    LENGTH nop = 1 ∧
    EVERY label_one xs ∧
    (EVERY is_Label aux ⇒ label_prefix_zero xs)
    ⇒
    SUM (MAP line_len (pad_section nop xs aux)) =
    SUM (MAP line_len xs) + SUM (MAP line_len aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,SUM_REVERSE,MAP_REVERSE,label_prefix_zero_cons]
  \\ fs[line_len_add_nop1]
  \\ `len=1` by decide_tac \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ metis_tac[NOT_EVERY]
QED

Theorem all_lab_len_pos_ok_pad_code:
   ∀nop code pos.
    all_lab_len_pos_ok pos code ∧
    (LENGTH nop ≠ 1 ⇒ EVERY sec_label_zero code) ∧
    EVERY sec_label_one code ∧
    EVERY sec_label_prefix_zero code
    ⇒
    all_lab_len_pos_ok pos (pad_code nop code)
Proof
  recInduct pad_code_ind
  \\ rw[all_lab_len_pos_ok_def,pad_code_def]
  >- (
    match_mp_tac pad_section_pos_ok
    \\ simp[lab_len_pos_ok_def] )
  \\ first_x_assum match_mp_tac \\ fs[]
  \\ reverse(Cases_on`LENGTH nop = 1`) \\ fs[]
  >- (
    fs[sec_length_sum_line_len,sec_label_zero_def,line_len_pad_section0] )
  \\ fs[sec_length_sum_line_len]
  \\ qspecl_then[`nop`,`xs`,`[]`]mp_tac line_len_pad_section
  \\ simp[]
QED

(* invariant: jump offsets ok *)

Definition line_offset_ok_def:
  (line_offset_ok labs ffis pos (LabAsm a w bytes _) ⇔
    w = get_jump_offset a ffis labs pos) ∧
  (line_offset_ok _ _ _ _ ⇔ T)
End

Definition lines_offset_ok_def:
  (lines_offset_ok labs ffis pos [] ⇔ T) ∧
  (lines_offset_ok labs ffis pos (l::ls) ⇔
   line_offset_ok labs ffis pos l ∧
   lines_offset_ok labs ffis (pos + line_len l) ls)
End

Theorem lines_offset_ok_append:
   ∀labs ffis pos l1 l2.
    lines_offset_ok labs ffis pos (l1 ++ l2) ⇔
    lines_offset_ok labs ffis pos l1 ∧
    lines_offset_ok labs ffis (pos + SUM (MAP line_len l1)) l2
Proof
  Induct_on`l1` \\ rw[lines_offset_ok_def,EQ_IMP_THM]
QED

Definition offset_ok_def:
  (offset_ok labs ffis pos [] ⇔ T) ∧
  (offset_ok labs ffis pos (Section k ls::ss) ⇔
   lines_offset_ok labs ffis pos ls ∧
   offset_ok labs ffis (pos + SUM (MAP line_len ls)) ss)
End

val offset_ok_ind = theorem"offset_ok_ind";

(* establishing offset_ok *)

Theorem enc_lines_again_simp_offset_ok:
   ∀labs ffis pos enc lines res ok.
    enc_lines_again_simp labs ffis pos enc lines = (res,ok)
    ⇒
    lines_offset_ok labs ffis pos res
Proof
  ho_match_mp_tac enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ fs[lines_offset_ok_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[lines_offset_ok_def]
  \\ fs[line_offset_ok_def]
QED

Theorem enc_secs_again_offset_ok:
   ∀pos labs ffis enc ls res ok.
    enc_secs_again pos labs ffis enc ls = (res,ok) ⇒
    offset_ok labs ffis pos res
Proof
  ho_match_mp_tac enc_secs_again_ind
  \\ rw[enc_secs_again_def]
  \\ fs[offset_ok_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[offset_ok_def]
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ fs[] \\ strip_tac \\ rveq
  \\ fs[sec_length_sum_line_len]
  \\ match_mp_tac enc_lines_again_simp_offset_ok
  \\ metis_tac[]
QED

(* offset_ok preservation *)

Theorem lines_offset_ok_pad_section:
   ∀nop lines aux labs ffis pos.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines ∧
    lab_len_pos_ok pos (REVERSE aux) ∧ EVERY label_zero aux ∧
    (¬NULL lines ∧ is_Label (HD lines) ∧ line_len (HD lines) = 1 ⇒
     ¬NULL aux ∧ ¬is_Label (HD aux)) ∧
    lines_offset_ok labs ffis pos (REVERSE aux ++ lines) ⇒
    lines_offset_ok labs ffis pos (pad_section nop lines aux)
Proof
  recInduct pad_section_ind
  \\ rw[pad_section_def,lines_offset_ok_append,lines_offset_ok_def,
        lab_len_pos_ok_append,lab_len_pos_ok_def,line_lab_len_pos_ok_def]
  \\ fs[MAP_REVERSE,SUM_REVERSE,SUM_APPEND]
  \\ TRY (
    first_x_assum match_mp_tac \\ fs[line_offset_ok_def]
    \\ spose_not_then strip_assume_tac
    \\ Cases_on`xs` \\ fs[lab_len_pos_ok_def]
    \\ Cases_on`h` \\ fs[line_lab_len_pos_ok_def]
    \\ NO_TAC)
  \\ Cases_on`aux` \\ fs[]
  \\ Cases_on`h`
  \\ fs[lines_offset_ok_append,MAP_REVERSE,SUM_REVERSE,add_nop_def,
        lines_offset_ok_def,line_offset_ok_def]
  \\ first_x_assum match_mp_tac
  \\ fs[lab_len_pos_ok_append,lab_len_pos_ok_def,line_lab_len_pos_ok_def,EVEN_ADD]
  \\ (conj_tac >- metis_tac[])
  \\ spose_not_then strip_assume_tac
  \\ Cases_on`xs` \\ fs[lab_len_pos_ok_def]
  \\ Cases_on`h` \\ fs[line_lab_len_pos_ok_def]
  \\ fs[EVEN_ADD]
  \\ metis_tac[]
QED

Theorem offset_ok_pad_code:
   ∀labs ffis pos code.
    (LENGTH nop ≠ 1 ⇒ EVERY sec_label_zero code) ∧
    EVERY sec_label_one code ∧
    EVERY sec_label_prefix_zero code ∧
    all_lab_len_pos_ok pos code ∧
    offset_ok labs ffis pos code ⇒
    offset_ok labs ffis pos (pad_code nop code)
Proof
  recInduct offset_ok_ind
  \\ rw[offset_ok_def,pad_code_def,sec_label_zero_def]
  \\ fs[]
  \\ `SUM (MAP line_len (pad_section nop ls [])) =
      SUM (MAP line_len ls)`
  by (
    Cases_on`LENGTH nop = 1` \\ fs[]
    >- simp[line_len_pad_section]
    \\ simp[line_len_pad_section0] )
  \\ fs[all_lab_len_pos_ok_def,sec_length_sum_line_len]
  \\ qspecl_then[`nop`,`ls`,`[]`,`labs`,`ffis`,`pos`]mp_tac lines_offset_ok_pad_section
  \\ fs[lab_len_pos_ok_def]
  \\ disch_then match_mp_tac
  \\ spose_not_then strip_assume_tac
  \\ Cases_on`ls` \\ fs[]
  \\ Cases_on`h` \\ fs[label_prefix_zero_cons]
QED

(* invariant: referenced labels exist *)

Definition line_labs_exist_def:
  (line_labs_exist labs (LabAsm a _ _ _) ⇔
    ∀n1 n2. (n1,n2) ∈ labs_of a ⇒ lab_lookup n1 n2 labs ≠ NONE) ∧
  (line_labs_exist _ _ ⇔ T)
End

val line_labs_exist_ind = theorem "line_labs_exist_ind";

val _ = export_rewrites["line_labs_exist_def"];

Definition sec_labs_exist_def:
  sec_labs_exist labs (Section _ ls) ⇔ EVERY (line_labs_exist labs) ls
End
val _ = export_rewrites["sec_labs_exist_def"];

Overload all_labs_exist = ``λlabs code. EVERY (sec_labs_exist labs) code``

(* Remove tail recursion from zero_labs_acc_exist *)
Triviality zero_labs_acc_of_eq_zero_labs_of:
  domain (zero_labs_acc_of l acc) =
  IMAGE FST (restrict_zero (labs_of l)) ∪ domain acc
Proof
  Cases_on`l`>> (TRY (Cases_on`l'`))>>
  simp[backendPropsTheory.restrict_zero_def]>>
  rw[]>>
  simp[EXTENSION]
QED

Triviality line_get_zero_labs_acc_eq_line_get_zero_labels:
  domain (line_get_zero_labs_acc l acc) =
  IMAGE FST (restrict_zero (line_get_labels l)) ∪ domain acc
Proof
  Cases_on`l`>>fs[line_get_zero_labs_acc_def,line_get_labels_def]>>
  simp[backendPropsTheory.restrict_zero_def]>>
  fs[zero_labs_acc_of_eq_zero_labs_of,backendPropsTheory.restrict_zero_def]
QED

Triviality sec_get_zero_labs_acc_eq_sec_get_zero_labels:
  domain (sec_get_zero_labs_acc sec acc) =
  IMAGE FST (restrict_zero (sec_get_labels sec)) ∪ domain acc
Proof
  Cases_on`sec`>>Induct_on`l`>>
  fs[sec_get_zero_labs_acc_def,sec_get_labels_def]>>
  simp[line_get_zero_labs_acc_eq_line_get_zero_labels]>>
  simp[EXTENSION,backendPropsTheory.restrict_zero_def]>>
  metis_tac[]
QED

Triviality get_zero_labs_acc_eq_get_zero_labels:
  domain (FOLDR sec_get_zero_labs_acc acc code) =
  IMAGE FST (restrict_zero (get_labels code)) ∪ domain acc
Proof
  Induct_on`code`>>fs[get_labels_def]>>
  simp[sec_get_zero_labs_acc_eq_sec_get_zero_labels]>>
  simp[EXTENSION,backendPropsTheory.restrict_zero_def]>>
  metis_tac[]
QED

Theorem zero_labs_acc_exist_eq:
  zero_labs_acc_exist labs code ⇔
  restrict_zero (get_labels code) ⊆ labs_domain labs
Proof
  simp[zero_labs_acc_exist_def,EVERY_MEM,MEM_toAList,FORALL_PROD]>>
  `∀p. lookup p (get_zero_labs_acc code) = SOME () ⇔
    p ∈ domain (get_zero_labs_acc code)`
    by
    simp[domain_lookup]>>
  simp[get_zero_labs_acc_def,get_zero_labs_acc_eq_get_zero_labels]>>
  simp[labs_domain_def,lab_lookup_def]>>
  simp[SUBSET_DEF,EXISTS_PROD,FORALL_PROD]>>
  rw[EQ_IMP_THM]>>fs[backendPropsTheory.restrict_zero_def]>>
  rw[]>>
  first_x_assum drule>>fs[]>>
  every_case_tac>>fs[]
QED;

(* labs_exist preservation *)
Theorem line_similar_line_labs_exist:
   ∀l1 l2. line_similar l1 l2 ⇒ (line_labs_exist labs l1 ⇔ line_labs_exist labs l2)
Proof
  recInduct line_similar_ind
  \\ rw[line_similar_def]
QED

Theorem code_similar_all_labs_exist:
   ∀c1 c2. code_similar c1 c2 ⇒ (all_labs_exist labs c1 ⇔ all_labs_exist labs c2)
Proof
  recInduct code_similar_ind
  \\ rw[code_similar_def]
  \\ fs[LIST_REL_EL_EQN, EVERY_MEM, MEM_EL]
  \\ metis_tac[line_similar_line_labs_exist]
QED

Theorem all_labs_exist_pad_code[simp]:
   ∀nop code. all_labs_exist labs (pad_code nop code) ⇔ all_labs_exist labs code
Proof
  metis_tac[code_similar_pad_code, code_similar_all_labs_exist, code_similar_refl]
QED

Theorem enc_lines_again_line_labs_exist:
   ∀labs ffis pos enc lines acc ok res ok' k.
   enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
   EVERY (line_labs_exist labs') acc ∧
   EVERY (line_labs_exist labs') lines ⇒
   EVERY (line_labs_exist labs') res
Proof
  recInduct enc_lines_again_ind
  \\ rw[enc_lines_again_def]
  \\ rw[EVERY_REVERSE]
QED

Theorem enc_secs_again_all_labs_exist:
   ∀pos ffis labs enc ls res ok k.
    enc_secs_again pos ffis labs enc ls = (res,ok) ∧ all_labs_exist labs' ls ⇒
    all_labs_exist labs' res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ match_mp_tac enc_lines_again_line_labs_exist
  \\ asm_exists_tac \\ fs[]
QED

Theorem upd_lab_len_all_labs_exist:
   ∀pos code. all_labs_exist labs (upd_lab_len pos code) ⇔ all_labs_exist labs code
Proof
  metis_tac[code_similar_upd_lab_len, code_similar_all_labs_exist, code_similar_refl]
QED

(* establishing labs_exist *)

Theorem line_similar_line_get_code_labels:
   ∀l1 l2. line_similar l1 l2 ⇒ line_get_code_labels l1 = line_get_code_labels l2
Proof
  recInduct line_similar_ind
  \\ rw[line_similar_def]
QED

Theorem code_similar_get_code_labels:
   ∀c1 c2. code_similar c1 c2 ⇒ get_code_labels c1 = get_code_labels c2
Proof
  recInduct code_similar_ind
  \\ rw[code_similar_def, get_code_labels_cons]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[sec_get_code_labels_def]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ fs[Once EXTENSION,MEM_EL,LIST_REL_EL_EQN,PULL_EXISTS]
  \\ metis_tac[line_similar_line_get_code_labels]
QED

Theorem line_labs_exist_get_labels:
   ∀labs line. line_labs_exist labs line ⇔ line_get_labels line ⊆ labs_domain labs
Proof
  recInduct line_labs_exist_ind
  \\ rw[line_labs_exist_def, line_get_labels_def, labs_domain_def, SUBSET_DEF, FORALL_PROD]
QED

Theorem sec_labs_exist_get_labels:
   ∀labs sec. sec_labs_exist labs sec ⇔ sec_get_labels sec ⊆ labs_domain labs
Proof
  Cases_on`sec`
  \\ rw[sec_labs_exist_def, sec_get_labels_def, line_labs_exist_get_labels,
        EVERY_MEM, SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem all_labs_exist_get_labels:
   all_labs_exist labs code ⇔ get_labels code ⊆ labs_domain labs
Proof
  rw[EVERY_MEM, sec_labs_exist_get_labels, get_labels_def,
     SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem line_similar_line_get_labels:
   ∀l1 l2. line_similar l1 l2 ⇒ (line_get_labels l1 = line_get_labels l2)
Proof
  recInduct line_similar_ind
  \\ rw[line_similar_def, line_get_labels_def]
QED

Theorem code_similar_get_labels:
   ∀c1 c2. code_similar c1 c2 ⇒ get_labels c1 = get_labels c2
Proof
  recInduct code_similar_ind
  \\ rw[code_similar_def, get_labels_def, sec_get_labels_def]
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ fs[LIST_REL_EL_EQN, MEM_EL]
  \\ metis_tac[line_similar_line_get_labels]
QED

Theorem get_labels_upd_lab_len[simp]:
   get_labels (upd_lab_len pos code) = get_labels code
Proof
  metis_tac[code_similar_get_labels, code_similar_upd_lab_len, code_similar_refl]
QED

Theorem section_labels_line_get_code_labels:
   ∀pos lines aux new_pos labs. section_labels pos lines aux = (new_pos, labs) ⇒
   0 INSERT set (MAP FST labs) = 0 INSERT set (MAP FST aux) ∪ BIGUNION (IMAGE line_get_code_labels (set lines))
Proof
  recInduct section_labels_ind
  \\ rw[section_labels_def]
  \\ rw[EXTENSION]
  \\ metis_tac[]
QED

Theorem labs_domain_compute_labels_alt:
   ∀pos code labs.
     ALL_DISTINCT (MAP Section_num code) ∧
     DISJOINT (domain labs) (set (MAP Section_num code)) ⇒
     labs_domain (compute_labels_alt pos code labs) =
     get_code_labels code ∪ labs_domain labs
Proof
  recInduct compute_labels_alt_ind
  \\ rw[compute_labels_alt_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[labs_domain_insert, domain_fromAList]
  \\ simp[get_code_labels_cons]
  \\ fs[sec_get_code_labels_def]
  \\ imp_res_tac section_labels_line_get_code_labels
  \\ fs[UNION_ASSOC]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[UNION_COMM]
  \\ AP_TERM_TAC
  \\ fs[Once EXTENSION,PULL_EXISTS, FORALL_PROD]
  \\ metis_tac[]
QED

(* invariant: labels aligned at even positions *)

Definition even_labels_def:
  (even_labels pos [] ⇔ T) ∧
  (even_labels pos (Section _ []::ls) ⇔ even_labels pos ls) ∧
  (even_labels pos (Section k (y::ys)::ls) ⇔
   (is_Label y ⇒ EVEN pos) ∧
   even_labels (pos + line_len y) (Section k ys::ls))
End

val even_labels_ind = theorem"even_labels_ind";

Definition lines_even_labels_def:
  (lines_even_labels pos [] ⇔ T) ∧
  (lines_even_labels pos (y::ys) ⇔
   (is_Label y ⇒ EVEN pos) ∧
   lines_even_labels (pos + line_len y) ys)
End

Theorem even_labels_alt:
   (even_labels pos [] ⇔ T) ∧
   (even_labels pos (Section _ ls::ss) ⇔
    lines_even_labels pos ls ∧
    even_labels (pos + SUM (MAP line_len ls)) ss)
Proof
  rw[even_labels_def]
  \\ qid_spec_tac `pos`
  \\ Induct_on`ls`
  \\ rw[even_labels_def,lines_even_labels_def]
  \\ Cases_on`h` \\ fs[line_length_def]
  \\ metis_tac[]
QED

Definition even_labels_strong_def:
  (even_labels_strong pos [] ⇔ T) ∧
  (even_labels_strong pos (Section _ []::ls) ⇔
    EVEN pos ∧ even_labels_strong pos ls) ∧
  (even_labels_strong pos (Section k (y::ys)::ls) ⇔
   (is_Label y ⇒ EVEN pos) ∧
   even_labels_strong (pos + line_len y) (Section k ys::ls))
End

Theorem even_labels_ends_imp_strong:
   ∀pos code.
    even_labels pos code ∧
    EVERY sec_ends_with_label code ∧
    EVERY sec_label_zero code
    ⇒
    even_labels_strong pos code
Proof
  Induct_on`code`
  \\ simp[even_labels_def,even_labels_strong_def,sec_ends_with_label_def]
  \\ Cases \\ simp[sec_ends_with_label_def,sec_label_zero_def]
  \\ Induct_on`l` \\ fs[]
  \\ fs[even_labels_def,even_labels_strong_def]
  \\ Cases_on`l` \\ fs[even_labels_def,even_labels_strong_def]
  \\ Cases \\ fs[EVEN_ADD] \\ rw[] \\ fs[]
QED

Theorem ALOOKUP_section_labels_ignore:
   ∀pos lines acc.
   ¬MEM n2 (MAP SND (extract_labels lines)) ⇒
   ALOOKUP (SND (section_labels pos lines acc)) n2 =
   ALOOKUP acc n2
Proof
  recInduct section_labels_ind
  \\ rw[section_labels_def] \\ fs[]
QED

Theorem lines_ok_section_lab_lookup_even:
   ∀pos lines acc.
   lines_ok c labs ffis pos lines ∧
   (∀l2 x. ALOOKUP acc l2 = SOME x ⇒ EVEN x) ∧
   ALOOKUP (SND (section_labels pos lines acc)) l2 = SOME x
   ⇒
   EVEN x
Proof
  ho_match_mp_tac section_labels_ind
  \\ rw[lines_ok_def,section_labels_def,line_ok_def,line_length_def] \\ fs[]
  \\ TRY ( last_x_assum match_mp_tac \\ asm_exists_tac \\ fs[] \\ NO_TAC)
  \\ TRY ( last_x_assum match_mp_tac \\ rw[] \\ fs[]
        \\ last_x_assum match_mp_tac \\ asm_exists_tac \\ fs[] \\ NO_TAC)
  \\ rename1`LabAsm xxx`
  \\ Cases_on`xxx` \\ fs[line_ok_def] \\ rw[]
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ asm_exists_tac \\ fs[]
QED

Triviality all_enc_ok_split:
  ∀c labs ffis pos k lines xs.
  all_enc_ok c labs ffis pos (Section k lines::xs) ⇒
  all_enc_ok c labs ffis pos [Section k lines] ∧
  all_enc_ok c labs ffis (pos + sec_length lines 0) xs
Proof
  Induct_on`lines`>>rw[all_enc_ok_def,sec_length_def,all_enc_ok_def]>>
  Cases_on`h`>>TRY(Cases_on`a`)>>
  fs[sec_length_def,sec_length_add,line_length_def,line_ok_def]>>rveq>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[] >>
  rfs[]>>
  metis_tac[ADD_ASSOC]
QED

Triviality all_enc_ok_even:
  ∀lines pos.
  all_enc_ok c labs ffis pos [Section k lines] ⇒
  EVEN (sec_length lines pos)
Proof
  Induct>>fs[all_enc_ok_def,sec_length_def]>>Cases>>
  TRY(Cases_on`a`)>>
  rw[]>>fs[line_ok_def,line_length_def,sec_length_add,sec_length_def]>>
  rfs[]>>
  `n + sec_length lines pos = sec_length lines (n + pos)` by
    metis_tac[sec_length_add,ADD_COMM]>>
  fs[]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]
QED

Triviality all_enc_ok_lab_lookup_even:
  ∀c labs ffis pos sec_list l1 l2 acc x.
      all_enc_ok c labs ffis pos sec_list ∧
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME x ∧
      (∀x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) ∧
      EVEN pos ⇒
      EVEN x
Proof
  Induct_on`sec_list`>>
  fs[all_enc_ok_def,compute_labels_alt_def]>>
  Cases \\ fs[compute_labels_alt_def] \\
  rw[] \\
  imp_res_tac all_enc_ok_split
  \\ pairarg_tac \\ fs[]
  \\ last_x_assum(match_mp_tac o MP_CANON)
  \\ fs[]
  \\ asm_exists_tac \\ fs[]
  \\ imp_res_tac all_enc_ok_even
  \\ qspecl_then[`pos`,`l`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`l`,`0`,`pos`]mp_tac sec_length_add \\ rw[] \\ fs[]
  \\ asm_exists_tac \\ fs[EVEN_ADD]
  \\ rw[lab_lookup_def,lookup_insert]
  \\ fs[lookup_fromAList]
  \\ pop_assum mp_tac \\ rw[] \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ match_mp_tac lines_ok_section_lab_lookup_even
  \\ asm_exists_tac \\ fs[]
  \\ qexists_tac`[]` \\ simp[]
QED

Theorem line_ok_pre_light_imp_line_ok:
   ∀c labs ffis pos line.
     line_ok_pre c line ∧
     line_enc_with_nop c.encode labs ffis pos line ∧
     line_offset_ok labs ffis pos line ∧
     line_labs_exist labs line ∧
     line_ok_light c line ∧ (is_Label line ⇒ EVEN pos) ⇒
     line_ok c labs ffis pos line
Proof
  ho_match_mp_tac line_ok_ind
  \\ rw[line_ok_def,line_ok_light_def,get_label_def,lab_inst_def,line_enc_with_nop_def,
        line_ok_pre_def,line_offset_ok_def,get_jump_offset_def]
  \\ fs[] \\ CASE_TAC
  \\ CASE_TAC \\ imp_res_tac lab_lookup_IMP \\ rveq \\ fs[]
QED

Theorem all_enc_ok_pre_light_imp_all_enc_ok:
   ∀c labs ffis pos code.
    all_enc_with_nop c.encode labs ffis pos code ∧
    all_enc_ok_pre c code ∧
    all_enc_ok_light c code ∧
    even_labels_strong pos code ∧
    all_labs_exist labs code ∧
    offset_ok labs ffis pos code
    ⇒
    all_enc_ok c labs ffis pos code
Proof
  ho_match_mp_tac all_enc_ok_ind
  \\ rw[all_enc_ok_def,all_enc_with_nop_def,
        even_labels_strong_def,line_ok_pre_light_imp_line_ok,
        offset_ok_def,lines_offset_ok_def]
  \\ imp_res_tac line_enc_with_nop_length_ok
  \\ imp_res_tac line_enc_with_nop_label_zero
  \\ fs[line_length_ok_def,line_length_def,sec_ends_with_label_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on`y` \\ fs[even_labels_alt,line_length_def]
QED

(*
val tm = ``[Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0 4 1]``;
val tm = ``[Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0 4 1; Asm a [b] 1]``;
val tm = ``[Asm a [b] 1; Label 0 1 0; Label 0 2 1; Label 0 3 0; Label 0 4 1]``;
val th = EVAL ``pad_section nop ^tm  []``
val tm2 = th |> concl |> rhs
EVAL ``SUM (MAP line_length ^tm)``
EVAL ``SUM (MAP line_length ^tm2)``
*)

Theorem upd_lab_len_ends_with_label:
   ∀pos ss.
    EVERY sec_ends_with_label ss ⇒
    EVERY sec_ends_with_label (upd_lab_len pos ss)
Proof
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def]
  \\ fs[sec_ends_with_label_def]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac lines_upd_lab_len_similar
  \\ pairarg_tac \\ fs[]
  \\ Q.ISPEC_THEN`lines`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[]
  \\ fs[LIST_REL_SNOC]
  \\ strip_tac \\ fs[SNOC_APPEND]
  \\ Cases_on`x` \\ Cases_on`x'`
  \\ fs[line_similar_def,sec_ends_with_label_def]
QED

Theorem lab_lookup_compute_labels_alt_ignore:
   ∀pos secs acc.
   ¬MEM n1 (MAP Section_num secs) ⇒
   lab_lookup n1 n2 (compute_labels_alt pos secs acc) = lab_lookup n1 n2 acc
Proof
  recInduct compute_labels_alt_ind
  \\ rw[compute_labels_alt_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[lab_lookup_def,lookup_insert]
QED

Theorem ALOOKUP_section_labels:
   ∀pos lines acc pc.
   EVERY (sec_label_ok n1) lines ∧
   EVERY line_length_ok lines ∧
   EVERY label_zero lines ∧
   ALL_DISTINCT (extract_labels lines) ∧
   sec_loc_to_pc n2 lines = SOME pc ∧
   n2 ≠ 0 ==>
   ∃i.
     ALOOKUP (SND (section_labels pos lines acc)) n2 = SOME i ∧
     ((sec_pos_val pc pos lines = NONE ∧
       i = pos + SUM (MAP line_length lines) ∧
       pc = LENGTH (FILTER ($~ o is_Label) lines)) ∨
      sec_pos_val pc pos lines = SOME i)
Proof
  ho_match_mp_tac section_labels_ind
  \\ rw[sec_pos_val_def]
  \\ fs[sec_loc_to_pc_cons]
  >- ( fs[sec_loc_to_pc_def] )
  >- ( fs[sec_loc_to_pc_def] )
  >- (
    fs[section_labels_def]
    \\ fs[line_length_ok_def,line_bytes_def,line_length_def]
    \\ Cases_on`l2=n2`\\fs[]
    \\ qspecl_then[`pos`,`lines`,`(n2,pos)::acc`]mp_tac ALOOKUP_section_labels_ignore
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ impl_tac
    >- (
      spose_not_then strip_assume_tac \\
      imp_res_tac sec_label_ok_extract_labels \\
      fs[] )
    \\ simp[] \\ disch_then kall_tac \\ rw[]
    \\ reverse(Cases_on`EVERY is_Label lines`)
    >- metis_tac[sec_pos_val_0]
    \\ simp[EVERY_is_Label_sec_pos_val]
    \\ `FILTER ($~ o is_Label) lines = []` by srw_tac[ETA_ss][FILTER_EQ_NIL]
    \\ `SUM (MAP line_length lines) = 0` suffices_by rw[]
    \\ simp[SUM_eq_0,MEM_MAP]
    \\ fs[EVERY_MEM,PULL_EXISTS]
    \\ Cases \\  strip_tac \\ res_tac \\ fs[]
    \\ simp[line_length_def])
  \\ fs[section_labels_def,line_length_def,line_length_ok_def]
  \\ rveq \\ fs[]
QED

Theorem lab_lookup_compute_labels_test[local]:
  ∀pos sec_list acc l1 l2 x2 c labs ffis nop.
      EVERY sec_labels_ok sec_list /\
      ALL_DISTINCT (MAP Section_num sec_list) ∧
      EVERY (ALL_DISTINCT o extract_labels o Section_lines) sec_list ∧
      EVERY sec_label_zero sec_list /\
      all_enc_ok c labs ffis pos sec_list /\
      loc_to_pc l1 l2 sec_list = SOME x2 ==>
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
      SOME (pos_val x2 pos sec_list)
Proof
  ho_match_mp_tac compute_labels_alt_ind>>fs[]>>
  CONJ_TAC >- (rw[]>> fs[compute_labels_alt_def,loc_to_pc_def])
  \\ rw[compute_labels_alt_def,pos_val_thm]
  \\ pop_assum mp_tac
  \\ simp[Once loc_to_pc_thm]
  \\ pairarg_tac \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ drule lines_ok_lines_enc_with_nop \\ strip_tac
  \\ drule lines_enc_with_nop_length_ok \\ strip_tac
  \\ IF_CASES_TAC \\ fs[]
  >- (
    rveq
    \\ TOP_CASE_TAC
    >- (
      Cases_on`loc_to_pc k l2 sec_list` \\ fs[]
      \\ strip_tac \\ rveq
      \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
      \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
      \\ impl_tac >- simp[Abbr`i`]
      \\ simp[] \\ strip_tac
      \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
      \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
      \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[])
    \\ strip_tac \\ rveq
    \\ simp[lab_lookup_compute_labels_alt_ignore]
    \\ simp[lab_lookup_def]
    \\ Cases_on`l2=0`
    >- (
      simp[lookup_fromAList]
      \\ fs[Once sec_loc_to_pc_def]
      \\ rveq
      \\ imp_res_tac lines_enc_with_nop_label_zero
      \\ Cases_on`EVERY is_Label lines`
      >- (
        `FILTER ($~ o is_Label) lines = []`
        by srw_tac[ETA_ss][FILTER_EQ_NIL] \\ simp[]
        \\ simp[EVERY_is_Label_sec_pos_val]
        \\ imp_res_tac pos_val_0 \\ simp[]
        \\ `SUM (MAP line_length lines) = 0` suffices_by simp[]
        \\ rw[SUM_eq_0,MEM_MAP] \\ fs[EVERY_MEM]
        \\ res_tac
        \\ Cases_on`y` \\ fs[line_length_def] )
      \\ imp_res_tac sec_pos_val_0
      \\ simp[] )
    \\ simp[lookup_fromAList]
    \\ drule (GEN_ALL ALOOKUP_section_labels)
    \\ fs[sec_label_zero_def]
    \\ disch_then drule \\ simp[]
    \\ disch_then(qspecl_then[`pos`,`[]`]strip_assume_tac) \\ rfs[]
    \\ match_mp_tac EQ_SYM
    \\ simp[lookup_insert, lookup_fromAList]
    \\ match_mp_tac pos_val_0
    \\ asm_exists_tac \\ fs[])
  \\ strip_tac
  \\ rveq
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
  \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
  \\ impl_tac >- simp[Abbr`i`]
  \\ simp[] \\ strip_tac
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[]
QED

Theorem enc_lines_again_simp_ends_with_label:
   ∀labs ffis pos enc ls res ok.
    enc_lines_again_simp labs ffis pos enc ls = (res,ok) ∧
    ¬NULL ls ∧ is_Label (LAST ls) ⇒
    ¬NULL res ∧ is_Label (LAST res)
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ fs[]
  \\ rveq \\ fs[LAST_CONS_cond]
  \\ rw[] \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ fs[enc_lines_again_simp_def]
QED

Theorem enc_secs_again_ends_with_label:
   ∀pos labs ffis enc lines res ok.
    enc_secs_again pos labs ffis enc lines = (res,ok) ∧
    EVERY sec_ends_with_label lines ⇒
    EVERY sec_ends_with_label res
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ fs[sec_ends_with_label_def]
  \\ match_mp_tac enc_lines_again_simp_ends_with_label
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ rw[]
  \\ metis_tac[]
QED

Theorem enc_sec_list_ends_with_label:
   ∀enc code.
   EVERY sec_ends_with_label code ⇒
   EVERY sec_ends_with_label (enc_sec_list enc code)
Proof
  Induct_on`code` \\ fs[enc_sec_list_def]
  \\ Cases \\ fs[enc_sec_def,sec_ends_with_label_def]
  \\ Induct_on`l` \\ fs[LAST_CONS_cond]
  \\ Cases \\ gen_tac \\ IF_CASES_TAC \\ fs[enc_line_def,NULL_EQ]
QED

Theorem lines_even_labels_append:
   ∀l1 l2 pos.
    lines_even_labels pos (l1 ++ l2) ⇔
    lines_even_labels pos l1 ∧
    lines_even_labels (pos + SUM (MAP line_len l1)) l2
Proof
  Induct \\ simp[lines_even_labels_def]
  \\ fsrw_tac[DNF_ss][EQ_IMP_THM] \\ rw[]
  \\ full_simp_tac std_ss [ADD_COMM]
  \\ full_simp_tac std_ss [ADD_ASSOC]
  \\ metis_tac[]
QED

Theorem label_zero_pos_ok_lines_even_labels:
   ∀pos ls.
    EVERY label_zero ls ∧
    lab_len_pos_ok pos ls
    ⇒
    lines_even_labels pos ls
Proof
  Induct_on`ls` \\ simp[lines_even_labels_def,lab_len_pos_ok_def]
  \\ Cases \\ simp[line_lab_len_pos_ok_def]
  \\ rpt strip_tac \\ rfs[]
QED

Theorem label_zero_pos_ok_even_labels:
   ∀pos code.
   EVERY sec_label_zero code ∧
   all_lab_len_pos_ok pos code
   ⇒
   even_labels pos code
Proof
  recInduct all_lab_len_pos_ok_ind
  \\ rw[all_lab_len_pos_ok_def,even_labels_alt,
        sec_length_sum_line_len,sec_label_zero_def]
  \\ match_mp_tac label_zero_pos_ok_lines_even_labels
  \\ fs[]
QED

(*
  val code = ``[Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]``
  EVAL ``lab_len_pos_ok 0 ^code``
  EVAL ``(pad_section nop ^code [])``
  EVAL ``lab_len_pos_ok 0 (pad_section nop ^code [])``

  [Label a1 b1 0; Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
  []

  [Label a2 b2 0; Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
  [Label a1 b1 0]

  [Asm x3 [b3] 1; Label a4 b4 1; Label a5 b5 0]
  [Label a2 b2 0; Label a1 b1 0]

  [Label a4 b4 1; Label a5 b5 0]
  [Asm x3 [b3] 1; Label a2 b2 0; Label a1 b1 0]

  [Label a5 b5 0]
  [Label a4 b4 0; Asm x3 [b3;nop] 2; Label a2 b2 0; Label a1 b1 0]
*)

Theorem pad_code_ends_with_label:
   ∀nop ls.
    EVERY sec_ends_with_label ls ⇒
    EVERY sec_ends_with_label (pad_code nop ls)
Proof
  recInduct pad_code_ind
  \\ simp[pad_code_def,sec_ends_with_label_def]
  \\ rpt gen_tac \\ ntac 2 strip_tac
  \\ qspecl_then[`nop`,`xs`,`[]`,`xs`]mp_tac line_similar_pad_section
  \\ simp[]
  \\ impl_tac >- ( metis_tac[EVERY2_refl,line_similar_refl] )
  \\ Q.ISPEC_THEN`xs`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[]
  \\ rw[LIST_REL_SNOC,SNOC_APPEND] \\ fs[]
  \\ Cases_on`x`
  \\ Cases_on`y` \\ fs[line_similar_def]
QED

Theorem enc_lines_again_section_labels:
   ∀labs ffis pos enc lines res acc.
    enc_lines_again_simp labs ffis pos enc lines = (res,T) ⇒
    section_labels pos lines acc = section_labels pos res acc
Proof
  recInduct enc_lines_again_simp_ind
  \\ rw[enc_lines_again_simp_def,section_labels_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[section_labels_def]
QED

Theorem enc_secs_again_compute_labels:
   ∀pos labs ffis enc secs res acc.
   enc_secs_again pos labs ffis enc secs = (res,T)
   ⇒
   compute_labels_alt pos res acc =
   compute_labels_alt pos secs acc
Proof
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[compute_labels_alt_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ qspecl_then[`labs`,`ffis`,`pos`,`enc`,`lines`,`[]`,`T`]mp_tac enc_lines_again_simp_EQ
  \\ simp[] \\ pairarg_tac \\ fs[] \\ strip_tac \\ rveq
  \\ imp_res_tac enc_lines_again_section_labels \\ fs[] \\ rveq
  \\ AP_THM_TAC
  \\ qspecl_then[`pos`,`lines1`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ rw[FUN_EQ_THM]
QED

(*
  val code = ``[Label 1 1 0; Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]``
  EVAL ``section_labels 0 ^code LN``
  EVAL ``(pad_section nop ^code [])``
  EVAL ``section_labels 0 (pad_section nop ^code []) LN``

  [Label 1 1 0; Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  []

  [Label 1 2 0; Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  [Label 1 1 0]

  [Asm x3 [b3] 1; Label 1 3 1; Label 1 4 0]
  [Label 1 2 0; Label 1 1 0]

  [Label 1 3 1; Label 1 4 0]
  [Asm x3 [b3] 1; Label 1 2 0; Label 1 1 0]

  [Label 1 4 0]
  [Label 1 3 0; Asm x3 [b3;nop] 2; Label 1 2 0; Label 1 1 0]
*)

Theorem pad_section_labels:
   ∀nop lines aux pos labs.
    lab_len_pos_ok (pos + SUM (MAP line_len aux)) lines ∧
    lab_len_pos_ok pos (REVERSE aux) ∧ EVERY label_zero aux ∧
    (¬NULL lines ∧ is_Label (HD lines) ∧ line_len (HD lines) = 1 ⇒
     ¬NULL aux ∧ ¬is_Label (HD aux))
    ⇒
    section_labels pos (pad_section nop lines aux) labs =
    section_labels pos (REVERSE aux ++ lines) labs
Proof
  recInduct pad_section_ind
  \\ rw[section_labels_def,pad_section_def,section_labels_append,
        lab_len_pos_ok_append,lab_len_pos_ok_def,line_lab_len_pos_ok_def,
        label_prefix_zero_cons]
  \\ fs[MAP_REVERSE,SUM_REVERSE,line_len_add_nop1,SUM_APPEND]
  \\ rw[] \\ fs[]
  \\ TRY (
    CONV_TAC(LAND_CONV(REWR_CONV(GSYM PAIR)))
    \\ rw[section_labels_sec_length,sec_length_sum_line_len,MAP_REVERSE,SUM_REVERSE]
    \\ NO_TAC)
  \\ TRY (
    first_x_assum match_mp_tac \\ fs[]
    \\ spose_not_then strip_assume_tac
    \\ Cases_on`xs` \\ fs[lab_len_pos_ok_def]
    \\ Cases_on`h` \\ fs[line_lab_len_pos_ok_def] )
  \\ Cases_on`aux` \\ fs[]
  \\ Cases_on`h` \\ fs[section_labels_append,MAP_REVERSE,SUM_REVERSE,add_nop_def,section_labels_def]
  \\ first_x_assum match_mp_tac
  \\ fs[lab_len_pos_ok_append,lab_len_pos_ok_def,line_lab_len_pos_ok_def,EVEN_ADD]
  \\ (conj_tac >- metis_tac[])
  \\ spose_not_then strip_assume_tac
  \\ Cases_on`xs` \\ fs[lab_len_pos_ok_def]
  \\ Cases_on`h` \\ fs[line_lab_len_pos_ok_def]
  \\ fs[EVEN_ADD]
  \\ metis_tac[]
QED

Theorem pad_code_compute_labels:
   ∀pos code acc.
    EVERY sec_label_one code ∧
    (LENGTH nop ≠ 1 ⇒ EVERY sec_label_zero code) ∧
    EVERY sec_label_prefix_zero code ∧
    all_lab_len_pos_ok pos code
    ⇒
    compute_labels_alt pos (pad_code nop code) acc =
    compute_labels_alt pos code acc
Proof
  recInduct compute_labels_alt_ind
  \\ rw[compute_labels_alt_def,pad_code_def,all_lab_len_pos_ok_def]
  \\ fs[sec_length_sum_line_len,sec_label_zero_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ `SUM (MAP line_len (pad_section nop lines [])) =
      SUM (MAP line_len lines)`
  by (
    Cases_on`LENGTH nop = 1` \\ fs[]
    >- simp[line_len_pad_section]
    \\ simp[line_len_pad_section0] )
  \\ qspecl_then[`pos`,`pad_section nop lines []`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ fs[sec_length_sum_line_len]
  \\ qspecl_then[`nop`,`lines`,`[]`,`pos`,`[]`]mp_tac pad_section_labels
  \\ fs[lab_len_pos_ok_def]
  \\ impl_tac
  >- (
    spose_not_then strip_assume_tac
    \\ Cases_on`lines` \\ fs[]
    \\ Cases_on`h` \\ fs[label_prefix_zero_cons] )
  \\ simp[]
QED

Triviality enc_lines_again_all_enc_ok_pre:
  ∀labs ffis pos enc lines acc ok res ok' c.
  enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
  EVERY (line_ok_pre c) lines ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) res
Proof
  recInduct enc_lines_again_ind>>rw[enc_lines_again_def]>>
  rw[EVERY_REVERSE]>>fs[line_ok_pre_def]
QED

Triviality enc_secs_again_all_enc_ok_pre:
  ∀pos labs ffis enc ls res ok c.
  enc_secs_again pos labs ffis enc ls = (res,ok) ∧ all_enc_ok_pre c ls ⇒
  all_enc_ok_pre c res
Proof
  ho_match_mp_tac enc_secs_again_ind>>rw[enc_secs_again_def]>>
  rw[]>>
  rpt (pairarg_tac>>fs[])>>
  rw[]>>
  match_mp_tac enc_lines_again_all_enc_ok_pre>>asm_exists_tac>>fs[]
QED

Triviality line_ok_pre_add_nop:
  EVERY (line_ok_pre c) xs ⇒
  EVERY (line_ok_pre c) (add_nop nop xs)
Proof
  Induct_on`xs`>>EVAL_TAC>>Cases>>fs[]>>rw[]>>EVAL_TAC>>fs[line_ok_pre_def]
QED

Triviality line_ok_pre_pad_section:
  ∀nop xs acc c.
  EVERY (line_ok_pre c) xs ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (pad_section nop xs acc)
Proof
  ho_match_mp_tac pad_section_ind>>rw[pad_section_def]>>
  fs[EVERY_REVERSE]>>
  first_x_assum match_mp_tac>>fs[line_ok_pre_def]>>
  metis_tac[line_ok_pre_add_nop]
QED

Triviality all_enc_ok_pre_pad_code:
  ∀nop code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (pad_code nop code)
Proof
  ho_match_mp_tac pad_code_ind>>rw[]>>EVAL_TAC>>rw[]>>
  rfs[]>>
  match_mp_tac line_ok_pre_pad_section>>fs[]
QED

Triviality all_enc_ok_pre_lines_upd_lab_len:
  ∀n lines acc.
  EVERY (line_ok_pre c) lines ∧
  EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))
Proof
  ho_match_mp_tac lines_upd_lab_len_ind>>rw[lines_upd_lab_len_def]>>
  fs[EVERY_REVERSE,line_ok_pre_def]
QED

Triviality all_enc_ok_pre_upd_lab_len:
  ∀n code.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (upd_lab_len n code)
Proof
  ho_match_mp_tac upd_lab_len_ind>>rw[]>> EVAL_TAC>>fs[]>>
  pairarg_tac \\ fs[] \\
  qspecl_then[`n`,`lines`,`[]`]mp_tac all_enc_ok_pre_lines_upd_lab_len
  \\ rw[]
QED

Triviality EXP_IMP_ZERO_LT:
  (2n ** y = x) ⇒ 0 < x
Proof
  metis_tac[bitTheory.TWOEXP_NOT_ZERO,NOT_ZERO_LT_ZERO]
QED

Theorem line_ok_alignment:
   ∀c labs ffis pos line.
   enc_ok c
   ∧ line_ok c labs ffis pos line
   ∧ ODD (line_length line)
   ⇒ c.code_alignment = 0
Proof
  ho_match_mp_tac line_ok_ind
  \\ srw_tac[][line_ok_def,line_length_def,LET_THM]
  \\ full_simp_tac(srw_ss())[enc_ok_def]
  \\ TRY(Cases_on`b`)
  \\ fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]
  \\ rename1 `asm_ok b c`
  \\ qpat_x_assum `!w. xxx /\ yyy` (qspec_then `b` mp_tac)
  \\ full_simp_tac(srw_ss())[enc_with_nop_thm]
  \\ rveq >> full_simp_tac(srw_ss())[]
  \\ srw_tac[][]
  \\ spose_not_then (assume_tac o MATCH_MP (#2(EQ_IMP_RULE (SPEC_ALL EXP2_EVEN))))
  \\ rev_full_simp_tac(srw_ss())[LENGTH_FLAT_REPLICATE]
  \\ full_simp_tac(srw_ss())[ODD_ADD,ODD_EVEN,EVEN_MULT]
  \\ imp_res_tac EXP_IMP_ZERO_LT
  \\ imp_res_tac MOD_EQ_0_DIVISOR
  \\ full_simp_tac(srw_ss())[EVEN_MULT]
QED

Theorem has_odd_inst_alignment:
   ∀c labs ffis pos code.
   enc_ok c
   ∧ all_enc_ok c labs ffis pos code
   ∧ has_odd_inst code
   ⇒ c.code_alignment = 0
Proof
  ho_match_mp_tac all_enc_ok_ind
  \\ simp[all_enc_ok_def,has_odd_inst_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ metis_tac[line_ok_alignment,ODD_EVEN]
QED

Triviality remove_labels_loop_thm:
  ∀n c init_pos init_labs ffis code code2 labs.
    remove_labels_loop n c init_pos init_labs ffis code = SOME (code2,labs) ∧
    EVERY sec_ends_with_label code ∧
    EVERY sec_labels_ok code ∧
    ALL_DISTINCT (MAP Section_num code) ∧
    EVERY (ALL_DISTINCT o extract_labels o Section_lines) code ∧
    DISJOINT (domain init_labs) (set (MAP Section_num code)) ∧
    (* TODO this is stronger:
      get_labels code ⊆ get_code_labels code ∪ labs_domain init_labs ∧
    *)
    restrict_nonzero (get_labels code) ⊆ get_code_labels code ∪ labs_domain init_labs ∧
    all_enc_ok_pre c code ∧ (* new loop invariant *)
    all_encd0 c.encode code ∧
    enc_ok c ∧
    EVEN init_pos ∧
    (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs))
    ⇒
    all_enc_ok_pre c code2 ∧
    EVERY sec_labels_ok code2 ∧
    all_enc_ok c labs ffis init_pos code2 /\
    code_similar code code2 /\
    (has_odd_inst code2 ⇒ c.code_alignment = 0) /\
    (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
    (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
               lab_lookup l1 l2 labs = SOME x) /\
    !l1 l2 x2.
      loc_to_pc l1 l2 code = SOME x2 ==>
      lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)
Proof
  HO_MATCH_MP_TAC remove_labels_loop_ind  >> rpt gen_tac >> strip_tac
  >> simp[Once remove_labels_loop_def]
  >> rpt gen_tac
  >> pairarg_tac \\ fs []
  >> reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >> strip_tac >> rveq THEN1
   (   fs[]
    >> last_x_assum mp_tac
    >> impl_tac >- (
      srw_tac[][]
      >- (
        match_mp_tac enc_secs_again_ends_with_label
        \\ metis_tac[] )
      >- (match_mp_tac enc_secs_again_sec_labels_ok>>metis_tac[])
      >- (metis_tac[code_similar_MAP_Section_num,enc_secs_again_IMP_similar])
      >- (fs[GSYM ALL_EL_MAP]
          \\ metis_tac[enc_secs_again_IMP_similar,code_similar_extract_labels])
      >- (metis_tac[code_similar_MAP_Section_num,enc_secs_again_IMP_similar])
      >- (metis_tac[code_similar_get_labels, code_similar_get_code_labels, enc_secs_again_IMP_similar])
      >- (match_mp_tac enc_secs_again_all_enc_ok_pre>>metis_tac[])
      >- (match_mp_tac enc_secs_again_encd0 \\ metis_tac[] ))
    >> simp[] >> strip_tac >> fs []
    >> drule enc_secs_again_IMP_similar
    >> metis_tac [code_similar_trans,code_similar_loc_to_pc])
  \\ pairarg_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qmatch_goalsub_abbrev_tac`_ ∧ all_enc_ok c labs ffis _ (pad_code nop sec_list) ∧ _`
  \\ qmatch_assum_abbrev_tac`enc_secs_again _ labs0 ffis enc code = (code1,T)`
  \\ qpat_x_assum`Abbrev(code1 = _)`kall_tac
  \\ `all_encd0 enc code1` by imp_res_tac enc_secs_again_encd0
  \\ qmatch_assum_abbrev_tac`enc_secs_again _ labs ffis enc code2 = (sec_list,T)`
  \\ `EVERY sec_label_one code2` by metis_tac[upd_lab_len_label_one]
  \\ `all_encd0 enc code2` by metis_tac[upd_lab_len_encd0,enc_secs_again_encd0]
  \\ `all_encd enc labs ffis init_pos sec_list` by metis_tac[enc_secs_again_encd]
  \\ `LENGTH nop ≠ 1 ⇒
      EVERY (sec_aligned (LENGTH nop)) sec_list ∧
      EVERY sec_label_zero sec_list`
  by (
    strip_tac
    \\ qmatch_assum_abbrev_tac`enc_ok c`
    \\ `c.code_alignment ≠ 0`
    by ( strip_tac \\ fs[enc_ok_def] )
    \\ `EVERY sec_ends_with_label code1`
    by metis_tac[enc_secs_again_ends_with_label]
    \\ `EVERY sec_label_zero code2`
    by (
      simp[Abbr`code2`]
      \\ match_mp_tac (GEN_ALL upd_lab_len_encd0_label_zero)
      \\ asm_exists_tac \\ fs[] )
    \\ reverse conj_tac
    >- metis_tac[enc_secs_again_label_zero]
    \\ match_mp_tac enc_secs_again_aligned
    \\ fs[enc_ok_def] \\ rfs[]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["enc"]))
    \\ qexists_tac`enc` \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ simp[Abbr`nop`]
    \\ match_mp_tac all_encd0_aligned
    \\ fs[enc_ok_def]
    \\ metis_tac[])
  \\ `EVERY sec_label_one sec_list` by metis_tac[enc_secs_again_label_one]
  \\ `all_length_leq sec_list` by metis_tac[all_encd_length_leq]
  \\ `EVERY sec_label_prefix_zero code2`
  by (
    simp[Abbr`code2`]
    \\ match_mp_tac upd_lab_len_label_prefix_zero
    \\ simp[]
    \\ match_mp_tac enc_secs_again_ends_with_label
    \\ asm_exists_tac \\ fs[])
  \\ `EVERY sec_label_prefix_zero sec_list`
  by metis_tac[enc_secs_again_label_prefix_zero]
  \\ `all_lab_len_pos_ok init_pos sec_list`
  by metis_tac[enc_secs_again_pos_ok,upd_lab_len_pos_ok]
  (* all_enc_ok_pre *)
  \\ conj_asm1_tac
  >-
    (match_mp_tac all_enc_ok_pre_pad_code>>
    match_mp_tac enc_secs_again_all_enc_ok_pre>>asm_exists_tac>>
    fs[Abbr`code2`]>>
    match_mp_tac all_enc_ok_pre_upd_lab_len>>
    match_mp_tac enc_secs_again_all_enc_ok_pre>>asm_exists_tac>>fs[])
  (* sec_labels_ok *)
  \\ conj_asm1_tac >-
     metis_tac[enc_secs_again_sec_labels_ok,upd_lab_len_sec_labels_ok,pad_code_sec_labels_ok]
  (* all_enc_ok *)
  \\ conj_asm1_tac
  >- (
    match_mp_tac all_enc_ok_pre_light_imp_all_enc_ok \\ fs[]
    \\ conj_asm1_tac
    >- (
      match_mp_tac all_enc_with_nop_pad_code
      \\ fs[enc_ok_def]
      \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
      \\ simp[] )
    \\ conj_tac
    >- (
      match_mp_tac even_labels_ends_imp_strong
      \\ reverse conj_asm2_tac
      >- metis_tac[enc_secs_again_ends_with_label,upd_lab_len_ends_with_label,
                   pad_code_ends_with_label,all_enc_with_nop_label_zero]
      \\ match_mp_tac label_zero_pos_ok_even_labels \\ fs[]
      \\ match_mp_tac all_lab_len_pos_ok_pad_code \\ fs[])
    \\ conj_tac >- (
      (* TODO: this is slightly weird: zero_labs_acc_exist is moved upwards *)
      fs[zero_labs_acc_exist_eq]>>
      `get_labels (pad_code nop sec_list) = get_labels code` by
        metis_tac[code_similar_pad_code, code_similar_get_labels,
          code_similar_refl, code_similar_upd_lab_len,enc_secs_again_IMP_similar]>>
      fs[]>>
      match_mp_tac enc_secs_again_all_labs_exist
      \\ asm_exists_tac \\ simp[]
      \\ rw[all_labs_exist_get_labels]
      \\ `MAP Section_num code2 = MAP Section_num code`
      by metis_tac[code_similar_MAP_Section_num,
                   enc_secs_again_IMP_similar,
                   code_similar_upd_lab_len]
      \\ qspecl_then[`init_pos`,`code2`,`init_labs`]mp_tac labs_domain_compute_labels_alt
      \\ impl_tac >- metis_tac[]
      \\ simp[] \\ strip_tac \\
      `get_labels code2 = get_labels code ∧ get_code_labels code2 = get_code_labels code`
      by
        (qspecl_then[`code2`,`code1`]mp_tac code_similar_get_code_labels
        \\ impl_tac >- metis_tac[code_similar_upd_lab_len,code_similar_refl]
        \\ rw[] \\ simp[Abbr`code2`]
        \\ metis_tac [enc_secs_again_IMP_similar, code_similar_get_code_labels, code_similar_get_labels])>>
      simp[]>>
      `get_labels code = restrict_zero (get_labels code) ∪ restrict_nonzero (get_labels code)` by
      (fs[EXTENSION,FORALL_PROD,backendPropsTheory.restrict_zero_def,backendPropsTheory.restrict_nonzero_def]>>
      metis_tac[])>>
      pop_assum SUBST1_TAC>>fs[]>>
      metis_tac[SUBSET_TRANS,SUBSET_UNION])
    \\ match_mp_tac offset_ok_pad_code \\ fs[]
    \\ metis_tac[enc_secs_again_offset_ok])
  \\ conj_asm1_tac
  THEN1 (imp_res_tac enc_secs_again_IMP_similar \\
         metis_tac [code_similar_trans,code_similar_sym,code_similar_upd_lab_len,code_similar_pad_code])
  \\ conj_tac THEN1
   (strip_tac
    \\ match_mp_tac has_odd_inst_alignment
    \\ asm_exists_tac \\ srw_tac[][]
    \\ asm_exists_tac \\ srw_tac[][])
  \\ drule pad_code_compute_labels
  \\ disch_then(qspecl_then[`init_pos`,`init_labs`]mp_tac)
  \\ impl_tac >- fs[]
  \\ drule enc_secs_again_compute_labels \\ fs[]
  \\ rw [Abbr`labs`]
  \\ qhdtm_assum`compute_labels_alt`sym_sub_tac
  THEN1 (
    match_mp_tac all_enc_ok_lab_lookup_even>>
    first_assum (match_exists_tac o concl)>>fs[]>>
    CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac`init_labs`
    \\ asm_exists_tac \\ fs[]
    \\ fs[lab_lookup_def]
    \\ metis_tac[OPTION_ALL_def])
  THEN1 (
    fs[IN_DISJOINT]>>
    first_assum (fn th => mp_tac (SIMP_RULE std_ss [lab_lookup_def] th))>>
    CASE_TAC>> rw[]>>
    fs[domain_lookup]>>
    metis_tac[lab_lookup_compute_labels_alt_ignore,code_similar_MAP_Section_num]
  )
  \\ fs [] \\ match_mp_tac (lab_lookup_compute_labels_test |> GEN_ALL)
  \\ fs[GSYM PULL_EXISTS]
  \\ conj_tac
    >- metis_tac[code_similar_MAP_Section_num,code_similar_pad_code]
  \\ conj_tac >- (
    fs[GSYM ALL_EL_MAP]
    \\ metis_tac[code_similar_extract_labels,code_similar_pad_code] )
  \\ CONJ_TAC >- metis_tac[]
  \\ qpat_x_assum `_ = SOME x2` (fn th => fs [GSYM th])
  \\ match_mp_tac code_similar_loc_to_pc
  \\ match_mp_tac code_similar_sym
  \\ match_mp_tac code_similar_pad_code
  \\ imp_res_tac enc_secs_again_IMP_similar
  \\ fs [code_similar_upd_lab_len,Abbr`code2`]
  \\ metis_tac [code_similar_trans]
QED

Theorem loc_to_pc_enc_sec_list[simp]:
   ∀l1 l2 code.
     loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2 code
Proof
  simp[enc_sec_list_def]
  >> (ho_match_mp_tac loc_to_pc_ind
  >> srw_tac[][]
  >> srw_tac[][Once loc_to_pc_def,enc_sec_def]
  >> srw_tac[][Once loc_to_pc_def,SimpRHS]
  >> match_mp_tac EQ_SYM
  >> BasicProvers.TOP_CASE_TAC
  >- full_simp_tac(srw_ss())[]
  >> simp[]
  >> IF_CASES_TAC
  >- full_simp_tac(srw_ss())[enc_line_def]
  >> IF_CASES_TAC
  >- (
    Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def]
    >> rev_full_simp_tac(srw_ss())[enc_sec_def] >> full_simp_tac(srw_ss())[]
    >> metis_tac [])
  >> IF_CASES_TAC
  >- ( Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def,LET_THM] )
  >> IF_CASES_TAC
  >- ( Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def,LET_THM] )
  >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[enc_sec_def]
  >> BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[])
QED

Triviality all_enc_ok_pre_enc_sec_list:
  ∀code enc c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (enc_sec_list enc code)
Proof
  fs[enc_sec_list_def]>>Induct>>fs[]>>
  Cases>>fs[enc_sec_def]>>rw[]>>
  Induct_on`l`>>fs[]>>Cases>>fs[enc_line_def,line_ok_pre_def]
QED

Theorem remove_labels_thm:
   remove_labels clock conf init_pos init_labs ffi_names code = SOME (code2,labs) /\
   enc_ok conf /\
   EVERY sec_ends_with_label code /\
   EVERY sec_labels_ok code /\
   ALL_DISTINCT (MAP Section_num code) /\
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) code /\
   DISJOINT (domain init_labs) (set (MAP Section_num code)) ∧
   restrict_nonzero (get_labels code) ⊆ get_code_labels code ∪ labs_domain init_labs ∧
   all_enc_ok_pre conf code /\
   EVEN init_pos ∧
   (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs)) ==>
   all_enc_ok conf labs ffi_names init_pos code2 /\
   code_similar code code2 /\
   (has_odd_inst code2 ⇒ conf.code_alignment = 0) /\
   (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
   (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
              lab_lookup l1 l2 labs = SOME x) /\
   !l1 l2 x2.
     loc_to_pc l1 l2 code = SOME x2 ==>
     lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)
Proof
  simp[remove_labels_def]
  >> strip_tac
  >> drule (GEN_ALL remove_labels_loop_thm)
  >> impl_tac
  >- (
    simp[enc_sec_list_encd0,all_enc_ok_pre_enc_sec_list]
    \\ conj_tac
    >- ( match_mp_tac enc_sec_list_ends_with_label \\ fs[])
    \\ conj_tac
    >- ( match_mp_tac enc_sec_list_sec_labels_ok \\ fs[])
    \\ conj_tac
    >- ( metis_tac[code_similar_enc_sec_list,code_similar_refl,
                   code_similar_MAP_Section_num] )
    \\ conj_tac
    >- (
      fs[GSYM ALL_EL_MAP]
      \\ metis_tac[code_similar_enc_sec_list,code_similar_refl,
                   code_similar_extract_labels])
    >>
       metis_tac[code_similar_enc_sec_list,code_similar_MAP_Section_num,
                 code_similar_get_code_labels, code_similar_get_labels,
                 code_similar_refl])
  >> strip_tac >> simp[] >> full_simp_tac(srw_ss())[]
  >> rw [] >> res_tac
QED

Theorem compute_labels_alt_domain_labs:
   ∀pos code labs.
     domain (compute_labels_alt pos code labs) =
     IMAGE FST (get_code_labels code) ∪ domain labs
Proof
  recInduct lab_to_targetTheory.compute_labels_alt_ind
  \\ rw[lab_to_targetTheory.compute_labels_alt_def]
  \\ pairarg_tac \\ fs[]
  \\ simp[labPropsTheory.get_code_labels_cons]
  \\ fs[labPropsTheory.sec_get_code_labels_def]
  \\ simp[GSYM IMAGE_COMPOSE, o_DEF]
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem remove_labels_loop_domain_labs:
   ∀a b c d e f g h. remove_labels_loop a b c d e f = SOME (g,h) ⇒
   domain h = IMAGE FST (get_code_labels f) ∪ domain d
Proof
   recInduct lab_to_targetTheory.remove_labels_loop_ind
   \\ rw[]
   \\ pop_assum mp_tac
   \\ simp[Once lab_to_targetTheory.remove_labels_loop_def]
   \\ pairarg_tac \\ fs[]
   \\ pairarg_tac \\ fs[]
   \\ reverse IF_CASES_TAC \\ fs[]
   >- (
     strip_tac \\ fs[]
     \\ imp_res_tac enc_secs_again_IMP_similar
     \\ metis_tac[code_similar_get_code_labels])
   \\ strip_tac
   \\ rveq
   \\ simp[compute_labels_alt_domain_labs]
   \\ metis_tac[
     code_similar_upd_lab_len,
     code_similar_get_code_labels,
     enc_secs_again_IMP_similar]
QED

Theorem remove_labels_domain_labs:
   remove_labels c t k init_labs f p = SOME (q,labs) ⇒
   domain labs = IMAGE FST (get_code_labels p) ∪ domain init_labs
Proof
  rw[lab_to_targetTheory.remove_labels_def]
  \\ imp_res_tac remove_labels_loop_domain_labs
  \\ simp[]
  \\ metis_tac[code_similar_enc_sec_list,
               code_similar_refl,
               code_similar_get_code_labels]
QED

(** End syntactic stuff **)

Theorem LENGTH_prog_to_bytes:
   ∀code n c labs ffi pos.
   all_enc_ok c labs ffi pos code ⇒
   FOLDL (λpos sec. sec_length (Section_lines sec) pos) n code =
   LENGTH (prog_to_bytes code) + n
Proof
  recInduct prog_to_bytes_ind>>
  fs[all_enc_ok_def,prog_to_bytes_def,sec_length_def]>>rw[]
  >-
    metis_tac[]
  >>
  Cases_on`y`>>simp[sec_length_def,line_bytes_def]>>
  TRY(Cases_on`a`)>>
  fs[line_ok_def,line_length_def]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[] >>
  metis_tac[ADD_ASSOC]
QED

Theorem LENGTH_prog_to_bytes2:
   ∀code n c labs ffi pos.
   all_enc_ok c labs ffi pos code ⇒
   SUM (MAP (SUM o MAP line_length o Section_lines) code) =
   LENGTH (prog_to_bytes code)
Proof
  recInduct prog_to_bytes_ind>>
  fs[all_enc_ok_def,prog_to_bytes_def,sec_length_def]>>rw[]
  >-
    metis_tac[]
  >>
  Cases_on`y`>>simp[sec_length_def,line_bytes_def]>>
  TRY(Cases_on`a`)>>
  fs[line_ok_def,line_length_def]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]>>
  metis_tac[ADD_ASSOC]
QED

Theorem prog_to_bytes_APPEND:
    prog_to_bytes (c1++c2) = prog_to_bytes c1 ++ prog_to_bytes c2
Proof
  fs[prog_to_bytes_MAP]
QED

Theorem line_ok_line_byte_length:
    line_ok c labs ffi n l ⇒
  LENGTH (line_bytes l) = line_length l
Proof
  Cases_on`l`>>EVAL_TAC>>rw[]
QED

Theorem lines_ok_MAP_line_byte_length:
    ∀ls c labs ffi n.
  lines_ok c labs ffi n ls ⇒
  MAP LENGTH (MAP line_bytes ls) = MAP line_length ls
Proof
  Induct>>rw[lines_ok_def]>> metis_tac[line_ok_line_byte_length]
QED

Triviality all_enc_ok_prog_to_bytes_EVEN:
  ∀code n c labs ffi pos.
   EVEN pos ∧
   all_enc_ok c labs ffi pos code ⇒
   EVEN (LENGTH (prog_to_bytes code))
Proof
  fs[prog_to_bytes_MAP]>>
  Induct>>fs[]>>Cases>>
  fs[all_enc_ok_cons]>>rw[EVEN_ADD]>>
  rfs[]>>
  fs[LENGTH_FLAT]>>
  `MAP line_length l = MAP LENGTH (MAP line_bytes l)` by
    metis_tac[lines_ok_MAP_line_byte_length]>>
  pop_assum SUBST_ALL_TAC >>simp[]>>
  metis_tac[EVEN_ADD]
QED

Triviality loc_to_pc_append:
  ∀l1 l2 c1 c2 conf labs ffis pos.
  EVERY sec_labels_ok (c1++c2) ⇒
  loc_to_pc l1 l2 (c1++c2) =
  case loc_to_pc l1 l2 c1 of
    SOME x => SOME x
  | NONE =>
    case loc_to_pc l1 l2 c2 of
      SOME x => SOME (x + SUM (MAP (len_no_lab o Section_lines) c1))
    | NONE => NONE
Proof
  Induct_on`c1`
  >-
    (fs[loc_to_pc_thm]>>
    rw[]>>every_case_tac>>fs[]>>metis_tac[])
  >>
  simp[Once loc_to_pc_thm,SimpLHS]>>
  simp[Once loc_to_pc_thm,SimpRHS]>>
  rw[]>>
  rpt(TOP_CASE_TAC>>fs[])
QED

Theorem all_enc_ok_append:
   ∀conf labs ffi n c1 c2.
  all_enc_ok conf labs ffi n c1 ∧
  all_enc_ok conf labs ffi (n+LENGTH (prog_to_bytes c1)) c2 ⇒
  all_enc_ok conf labs ffi n (c1++c2)
Proof
  Induct_on`c1`>>fs[prog_to_bytes_def,all_enc_ok_def] >>
  Cases>>rw[]>>
  fs[all_enc_ok_cons]>>
  first_x_assum match_mp_tac>>
  fs[prog_to_bytes_MAP,LENGTH_FLAT]>>
  drule lines_ok_MAP_line_byte_length>>
  rw[]>>
  metis_tac[ADD_COMM]
QED

Theorem extract_labels_loc_to_pc:
    !l1 l2 code.
  EVERY sec_labels_ok code ∧
  MEM (l1,l2) (FLAT (MAP (extract_labels o Section_lines) code)) ==>
  ∃y. loc_to_pc l1 l2 code = SOME y
Proof
  ho_match_mp_tac loc_to_pc_ind>>rw[]>>
  simp[Once loc_to_pc_def]
  >-
    (IF_CASES_TAC>- simp[]>>
    pop_assum (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])>>
    TOP_CASE_TAC>>fs[]>>
    Cases_on`h`>>fs[]>>
    rw[]>>rfs[markerTheory.Abbrev_def])
  >>
    IF_CASES_TAC>- simp[]>>
    pop_assum (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])>>
    TOP_CASE_TAC>>fs[]
    >-
      rfs[markerTheory.Abbrev_def]
    >>
    Cases_on`h`>>fs[]>>
    rw[]>>rfs[markerTheory.Abbrev_def]
QED

Theorem all_enc_ok_labs_mono:
    ∀conf labs ffi n c labs2.
  (∀l1 l2 x.
    lab_lookup l1 l2 labs = SOME x ⇒
    lab_lookup l1 l2 labs2 = SOME x) ∧
  all_enc_ok conf labs ffi n c ==>
  all_enc_ok conf labs2 ffi n c
Proof
  ho_match_mp_tac all_enc_ok_ind>>rw[]>>
  fs[all_enc_ok_def]>>
  Cases_on`y`>>fs[line_ok_def]>>
  Cases_on`a`>>fs[line_ok_def]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]>>
  metis_tac[]
QED

Theorem pos_val_append:
    ∀c1 i pos c2.
  EVERY sec_label_zero c2 ⇒
  pos_val i pos (c1++c2) =
  if i <= (SUM (MAP (len_no_lab o Section_lines) c1)) then
    pos_val i pos c1
  else
     pos_val (i - (SUM (MAP (len_no_lab o Section_lines) c1))) (pos+ (SUM (MAP (SUM o MAP line_length o Section_lines) c1))) c2
Proof
  Induct
  >- (
    fs[pos_val_def]>>rw[]>>
    metis_tac[sec_label_zero_pos_val_0])
  >>
  rw[]
  >-(
    Cases_on`h`>>simp[pos_val_thm,SimpLHS]>>
    simp[pos_val_thm,SimpRHS]>>
    TOP_CASE_TAC>>fs[]
  )>>
    Cases_on`h`>>simp[pos_val_thm,SimpLHS]>>
    fs[]>>
    TOP_CASE_TAC>>fs[]>>
    `sec_pos_val i pos l = NONE` suffices_by fs[]>>
    match_mp_tac sec_pos_val_too_big>>
    fs[]
QED

Theorem sec_pos_val_acc:
    ∀l n i.
  len_no_lab l ≤ i ⇒
  sec_pos_val i n l = NONE
Proof
  Induct>>
  rw[sec_pos_val_def]
QED

Theorem pos_val_acc:
    ∀ls n.
  pos_val (SUM (MAP (len_no_lab o Section_lines) ls)) n ls =
  n+ SUM (MAP (SUM o (MAP line_length) ∘ Section_lines) ls)
Proof
  Induct>>fs[pos_val_thm]>>
  Cases>>rw[pos_val_thm]>>
  TOP_CASE_TAC >> fs[]>>
  qmatch_asmsub_abbrev_tac`sec_pos_val ll _ _`>>
  `sec_pos_val ll n' l = NONE` suffices_by fs[]>>
  match_mp_tac sec_pos_val_acc>>
  fs[Abbr`ll`]
QED

Theorem pos_val_bound:
    ∀i pos code conf labs ffi n.
  all_enc_ok conf labs ffi n code ==>
  pos_val i pos code ≤ pos + LENGTH(prog_to_bytes code)
Proof
  ho_match_mp_tac pos_val_ind>>
  rw[]>>fs[prog_to_bytes_def,pos_val_def,all_enc_ok_def]
  >-
    metis_tac[]
  >>
  IF_CASES_TAC>-
    (Cases_on`y`>>fs[is_Label_def,line_ok_def,line_length_def,line_bytes_def]>>
    rfs[]>>
    metis_tac[])>>
  IF_CASES_TAC>- fs[]>>
  fs[]>>
  metis_tac[]
QED

Theorem sec_loc_to_pc_bound:
    ∀n xs x.
  sec_loc_to_pc n xs = SOME x ⇒
  x ≤ len_no_lab xs
Proof
  ho_match_mp_tac sec_loc_to_pc_ind>>rw[]>>
  pop_assum mp_tac>>
  simp[Once sec_loc_to_pc_def]>>
  every_case_tac>>fs[]>>
  rw[]>>
  res_tac>>fs[]
QED

Theorem loc_to_pc_bound:
    ∀code l1 l2 x.
  EVERY sec_labels_ok code ∧
  loc_to_pc l1 l2 code = SOME x ⇒
  x ≤  SUM (MAP (len_no_lab ∘ Section_lines) code)
Proof
  Induct>>rw[]>>rfs[Once loc_to_pc_thm]>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
  >-(
    TOP_CASE_TAC>>fs[]>>
    rw[]>>res_tac>>fs[]>>
    drule sec_loc_to_pc_bound>>
    fs[])
  >>
    rw[]>>
    res_tac>>fs[]
QED

Triviality find_ffi_names_append:
  ∀l1 l2.
  find_ffi_names (l1++l2) =
  (find_ffi_names l2) ++
  FILTER (λn. ¬ MEM n (find_ffi_names l2)) (find_ffi_names l1)
Proof
  ho_match_mp_tac find_ffi_names_ind>>rw[find_ffi_names_def]>>
  fs[FILTER_EQ_ID]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  fs[list_add_if_fresh_thm]>>rw[]>>
  fs[MEM_FILTER,FILTER_APPEND]>>
  fs[]
QED

Theorem all_enc_ok_aligned_pos_val:
  !(mc_conf : ('a, 'b, 'c) machine_config) labs code2 pc ffi_names.
   all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
   (has_odd_inst code2 ==> mc_conf.target.config.code_alignment = 0) /\
   encoder_correct mc_conf.target ==>
   aligned mc_conf.target.config.code_alignment (n2w (pos_val pc 0 code2):'a word)
Proof
  metis_tac [MOD_0_aligned,pos_val_MOD_0]
QED

Theorem read_ffi_bytearrays_with_next_interfer[simp]:
   read_ffi_bytearrays (mc with next_interfer := foo) =
   read_ffi_bytearrays mc
Proof
  rw[FUN_EQ_THM, read_ffi_bytearrays_def, read_ffi_bytearray_def]
QED

Theorem read_ffi_bytearrays_shift_interfer[simp]:
   read_ffi_bytearrays (shift_interfer x y) = read_ffi_bytearrays y
Proof
  rw[shift_interfer_def]
QED

Theorem read_ffi_bytearrays_ffi_interfer[simp]:
  read_ffi_bytearrays (mc with ffi_interfer := ffi) = read_ffi_bytearrays mc
Proof
  rw[FUN_EQ_THM, read_ffi_bytearrays_def, read_ffi_bytearray_def]
QED

Theorem IMP_ffi_entry_pcs_disjoint_Asm:
!^s1 (mc_conf: ('a,'state,'b) machine_config).
  code_similar s1.code code2 /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
  asm_fetch_aux s1.pc s1.code = SOME (Asm instr _bytes _len) /\
  (!op re a. instr <> ShareMem op re a) /\
  share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain /\
  bytes_in_mem (p + n2w (pos_val s1.pc 0 code2)) bytes' t1.mem
    t1.mem_domain s1.mem_domain /\
  pos_val (s1.pc + 1) 0 code2 = LENGTH bytes' + pos_val s1.pc 0 code2 /\
  t1.pc = p + n2w (pos_val s1.pc 0 code2)
  ==>
  ffi_entry_pcs_disjoint (mc_conf: ('a, 'state, 'b) machine_config) t1 (LENGTH bytes')
Proof
  rpt strip_tac >>
  fs[ffi_entry_pcs_disjoint_def, addressTheory.word_arith_lemma1] >>
  drule code_similar_IMP_asm_fetch_aux_line_similar >>
  disch_then $ qspec_then `s1.pc` (assume_tac o
    REWRITE_RULE[OPTREL_def]) >>
  gvs[] >>
  Cases_on `y0` >> gvs[line_similar_def] >>
  gvs[share_mem_domain_code_rel_def] >>
  first_x_assum drule >>
  gvs[addressTheory.word_arith_lemma1, line_length_def] >>
  `LENGTH l = LENGTH bytes'` suffices_by simp[] >>
  drule_all asm_fetch_aux_pos_val_LENGTH_EQ >>
  PURE_REWRITE_TAC[line_bytes_def] >>
  simp[]
QED

Theorem IMP_ffi_entry_pcs_disjoint_LabAsm:
!^s1 (mc_conf: ('a,'state,'b) machine_config).
  code_similar s1.code code2 /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 code2 /\
  asm_fetch_aux s1.pc s1.code = SOME (LabAsm instr _pos _bytes _len) /\
  share_mem_domain_code_rel mc_conf p code2 s1.shared_mem_domain /\
  bytes_in_mem (p + n2w (pos_val s1.pc 0 code2)) bytes' t1.mem
    t1.mem_domain s1.mem_domain /\
  pos_val (s1.pc + 1) 0 code2 = LENGTH bytes' + pos_val s1.pc 0 code2 /\
  t1.pc = p + n2w (pos_val s1.pc 0 code2)
  ==>
  ffi_entry_pcs_disjoint (mc_conf: ('a, 'state, 'b) machine_config) t1 (LENGTH bytes')
Proof
  rpt strip_tac >>
  fs[ffi_entry_pcs_disjoint_def, addressTheory.word_arith_lemma1] >>
  drule code_similar_IMP_asm_fetch_aux_line_similar >>
  disch_then $ qspec_then `s1.pc` (assume_tac o
    REWRITE_RULE[OPTREL_def]) >>
  gvs[] >>
  Cases_on `y0` >> gvs[line_similar_def] >>
  gvs[share_mem_domain_code_rel_def] >>
  first_x_assum drule >>
  gvs[addressTheory.word_arith_lemma1, line_length_def] >>
  `LENGTH l = LENGTH bytes'` suffices_by simp[] >>
  drule_all asm_fetch_aux_pos_val_LENGTH_EQ >>
  PURE_REWRITE_TAC[line_bytes_def] >>
  simp[]
QED

Theorem asm_fetch_SOME_IMP_LESS_num_pcs:
  !pc secs x.
    asm_fetch_aux pc secs = SOME x ==>
    pc < num_pcs secs
Proof
  ho_match_mp_tac asm_fetch_aux_ind >>
  rpt strip_tac >>
  gvs[asm_fetch_aux_def,num_pcs_def] >>
  Cases_on `is_Label y` >>
  gvs[] >>
  Cases_on `pc` >>
  gvs[num_pcs_def]
QED

Theorem GENLIST_asm_fetch_aux_next:
  ~is_Label x ==>
  GENLIST (\i.
    (i,asm_fetch_aux i (Section k (x::xs)::rest)))
    (n+1) =
  (0,SOME x)::(
    GENLIST (\i.
      (i+1, asm_fetch_aux i (Section k xs::rest))) n)
Proof
  rpt strip_tac >>
  Induct_on `n` >>
  gvs[GENLIST,asm_fetch_aux_def,GSYM ADD1]
QED

Theorem pos_val_acc_sum:
  !i pos secs x y.
    x + y = pos ==>
    x + pos_val i y secs = pos_val i pos secs
Proof
  ho_match_mp_tac pos_val_ind >>
  rpt strip_tac >>
  gvs[pos_val_def] >>
  Cases_on `is_Label y` >>
  gvs[pos_val_def] >>
  Cases_on `i` >>
  gvs[pos_val_def]
QED

Theorem pos_val_acc_0:
  !i pos secs.
  pos + pos_val i 0 secs = pos_val i pos secs
Proof
  gvs[pos_val_acc_sum]
QED

Theorem FILTER_mmio_pcs_min_index:
  EVERY (\x. ∃op. x = SharedMem op) l ==>
  mmio_pcs_min_index
    (FILTER (λx. ∃s. x = ExtCall s) ffis ++ l) =
  SOME $ LENGTH $
    FILTER (λx. ∃s. x = ExtCall s) ffis
Proof
  rpt strip_tac >>
  qpat_abbrev_tac `P = λx. ∃s. x = ExtCall s` >>
  fs[mmio_pcs_min_index_def] >>
  gvs[some_def] >>
  SELECT_ELIM_TAC >>
  rw[]
  >~ [ `x = LENGTH _`]
  >- (
    spose_not_then assume_tac >>
    Cases_on `x < LENGTH (FILTER P ffis)`>>
    gvs[]
    >- (
      first_x_assum $ qspec_then `x`assume_tac >>
      gvs[EL_APPEND_EQN,EVERY_EL] >>
      qspecl_then [`P`,`P`, `ffis`] assume_tac EVERY_FILTER >>
      gvs[EVERY_EL,Abbr`P`]>>
      first_x_assum $ qspec_then `x`assume_tac >>gvs[]
    ) >>
    `LENGTH (FILTER P ffis) < x` by gvs[] >>
    gvs[] >>
    last_x_assum drule >>
    first_x_assum drule >>
    gvs[EVERY_EL,EL_APPEND_EQN,Abbr`P`] >>
    Cases_on ‘LENGTH l’>>fs[]>>
    last_x_assum $ qspec_then ‘0’ assume_tac>>fs[]
  ) >> (
   qexists_tac `LENGTH $ FILTER P ffis` >>
   gvs[] >>
   rw[] >>
   gvs[EL_APPEND_EQN,EVERY_EL] >>
   qspecl_then [`P`,`P`,`ffis`]
     assume_tac EVERY_FILTER >>
   gvs[EVERY_EL,Abbr`P`]
  )
QED

Theorem pos_val_GE_pc:
!i p code2.
  p <= pos_val i p code2
Proof
  ho_match_mp_tac pos_val_ind >>
  gvs[pos_val_def] >>
  rw[]
QED

Theorem enc_ok_LENGTH_GT_0:
  enc_ok c ==>
  0 < LENGTH (c.encode l)
Proof
  rw[enc_ok_def] >>
  last_x_assum $ qspec_then `l` mp_tac >>
  gvs[NOT_NIL_EQ_LENGTH_NOT_0]
QED

Theorem pos_val_mono:
!i p code2 j p'.
  i < j /\
  j <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c ==>
  pos_val i p code2 < pos_val j p code2
Proof
  ho_match_mp_tac pos_val_ind >>
  rw[] >>
  gvs[pos_val_def,num_pcs_def,all_enc_ok_def]
  >- res_tac >>
  IF_CASES_TAC >>
  gvs[all_enc_ok_def,pos_val_def]
  >- res_tac >>
  IF_CASES_TAC >>
  gvs[pos_val_def]
  >- (
    simp[Once $ GSYM pos_val_acc_0] >>
    Cases_on `y` >>
    gvs[is_Label_def,line_length_def,line_ok_def] >>
    gvs[enc_with_nop_thm] >>
    gvs[ZERO_LESS_ADD] >>
    disj1_tac
    >- (
      irule enc_ok_LENGTH_GT_0 >>
      gvs[]
    ) >>
    gvs[DefnBase.one_line_ify NONE line_ok_def,AllCaseEqs(),
      enc_with_nop_thm,is_Label_def,line_length_def,line_ok_def] >>
    rpt (pop_assum mp_tac) >>
    rpt (TOP_CASE_TAC >> gvs[]) >>
    rpt strip_tac >>
    gvs[enc_with_nop_thm] >>
    gvs[ZERO_LESS_ADD] >>
    disj1_tac >>
    irule enc_ok_LENGTH_GT_0 >>
    simp[]
  ) >>
  res_tac >>
  gvs[]
QED

Theorem pos_val_mono_inv:
!i p code2 j.
  pos_val i p code2 < pos_val j p code2 /\
  i <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c
  ==>
  i < j
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  `j <= i` by decide_tac >>
  Cases_on `j = i`>>
  gvs[] >>
  `j < i` by decide_tac >>
  gvs[] >>
  drule_at_then (Pos $ el 2) drule pos_val_mono >>
  disch_then drule_all >>
  simp[] >>
  qexists `p` >>
  simp[]
QED

Theorem pos_val_inj:
!p code2 j.
  pos_val i p code2 = pos_val j p code2 /\
  i <= num_pcs code2 /\ j <= num_pcs code2 /\
  all_enc_ok c labs ffis p' code2 /\
  enc_ok c ==>
  i = j
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  Cases_on `i < j`
  >- (
    drule_all pos_val_mono >>
    simp[] >>
    qexists `p` >>
    simp[]
  ) >>
  `j < i` by decide_tac >>
  drule_all pos_val_mono >>
  simp[] >>
  qexists `p` >>
  simp[]
QED

Theorem pos_val_num_pcs:
!c labs ffis p' code2.
  all_enc_ok c labs ffis p' code2 ==>
  pos_val (num_pcs code2) p code2 = p + LENGTH (prog_to_bytes code2)
Proof
  ho_match_mp_tac all_enc_ok_ind >>
  rpt strip_tac >>
  gvs[pos_val_def,num_pcs_def,prog_to_bytes_def,all_enc_ok_def,
    line_bytes_def] >>
  qpat_x_assum `line_ok _ _ _ _ _` mp_tac >>
  simp[DefnBase.one_line_ify NONE line_ok_def] >>
  TOP_CASE_TAC >>
  gvs[pos_val_def,num_pcs_def,prog_to_bytes_def,all_enc_ok_def,
    line_bytes_def,line_length_def,line_ok_def] >>
  simp[Once $ GSYM pos_val_acc_0] >>
  fs[Once $ GSYM pos_val_acc_0]
QED

Theorem pos_val_GE_num_pcs:
!pc p code2.
  num_pcs code2 <= pc ==>
  pos_val (num_pcs code2) p code2 = pos_val pc p code2
Proof
  ho_match_mp_tac pos_val_ind >>
  rpt strip_tac >>
  gvs[num_pcs_def,pos_val_def] >>
  Cases_on `y` >>
  gvs[num_pcs_def,pos_val_def]
QED

Theorem pos_val_0_aux:
!c labs ffis p xs pos.
  all_enc_ok c labs ffis p xs ==> (pos_val 0 pos xs = pos)
Proof
  ho_match_mp_tac all_enc_ok_ind >>
  gvs[pos_val_def,all_enc_ok_def] >>
  rpt strip_tac >>
  res_tac >>
  Cases_on `y` >>
  gvs[is_Label_def,line_length_def,line_ok_def,pos_val_def]
QED

Theorem asm_fetch_aux_pos_val_SUC:
!pc p code2 p'.
  all_enc_ok c labs ffi p' code2 /\
  asm_fetch_aux pc (code2: 'a sec list) = SOME line ==>
  LENGTH (line_bytes line) + pos_val pc p code2 = pos_val (pc+1) p code2
Proof
  ho_match_mp_tac pos_val_ind >>
  rpt strip_tac >>
  gvs[asm_fetch_aux_def,pos_val_def,all_enc_ok_def]
  >- res_tac >>
  Cases_on `y` >>
  gvs[is_Label_def,asm_fetch_aux_def,pos_val_def,all_enc_ok_def]
  >- res_tac >>
  Cases_on `pc` >>
  gvs[asm_fetch_aux_def,pos_val_def] >>
  metis_tac[pos_val_0_aux]
QED

Theorem pos_val_asm_fetch_aux_distinct:
  all_enc_ok c labs ffis p' (code2: 'a sec list) /\
  enc_ok c /\
  asm_fetch_aux pc code2 = SOME line /\
  a < LENGTH (line_bytes line) /\
  LENGTH (prog_to_bytes code2) < dimword (:'a) /\
  pc' <> pc ==>
  ((n2w (a + pos_val pc p code2)): 'a word) <> n2w (pos_val pc' p code2)
Proof
  rpt strip_tac >>
  drule_then (qspec_then `0` assume_tac) pos_val_num_pcs >>
  `p + pos_val pc 0 code2 = pos_val pc p code2` by irule pos_val_acc_0 >>
  `p + pos_val pc' 0 code2 = pos_val pc' p code2` by irule pos_val_acc_0 >>
  gvs[] >>
  drule pos_val_bound >>
  disch_then $ qspecl_then [`pc`, `0`] assume_tac >>
  drule pos_val_bound >>
  disch_then $ qspecl_then [`pc'`, `0`] assume_tac >>
  drule asm_fetch_aux_pos_val_SUC >>
  disch_then imp_res_tac >>
  first_x_assum $ qspec_then `0` assume_tac >>
  gvs[] >>
  drule pos_val_bound >>
  disch_then $ qspecl_then [`pc + 1`, `0`] assume_tac >>
  gvs[] >>
  drule_then assume_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
  drule_then assume_tac LESS_OR >>
  gvs[arithmeticTheory.ADD1] >>
  assume_tac ZERO_LT_dimword >>
  `(a + pos_val pc 0 code2) MOD dimword (:'a) =
    (pos_val pc' 0 code2) MOD dimword (:'a)` by (
      drule_then match_mp_tac $ iffLR ADD_MOD >>
      gvs[] >>
      metis_tac[]
  ) >>
  Cases_on `num_pcs code2 <= pc'`
  >- (
    drule pos_val_GE_num_pcs >>
    disch_then $ qspec_then `0` assume_tac >>
    gvs[]
  ) >>
  `pc' < num_pcs code2` by decide_tac >>
  gvs[] >>
  `pos_val pc p code2 < pos_val pc' p code2` by (
    Cases_on `a` >>
    gvs[] >>
    drule pos_val_inj >>
    gvs[]
  ) >>
  drule pos_val_mono_inv >>
  disch_then imp_res_tac >>
  gvs[] >>
  `pc' < pc + 1` suffices_by gvs[] >>
  `pos_val pc' 0 code2 < pos_val (pc+1) 0 code2` by gvs[] >>
  drule pos_val_mono_inv >>
  disch_then imp_res_tac >>
  gvs[]
QED

Theorem bytes_in_memory_eq_mem:
  !pc bytes.
    (∀a. a ∈ t1.mem_domain ⇒ mc_conf.target.get_byte ms1 a = t1.mem a) /\
    bytes_in_memory pc bytes t1.mem t1.mem_domain ==>
    bytes_in_memory pc bytes (mc_conf.target.get_byte ms1) t1.mem_domain
Proof
  Induct_on `bytes`
  \\ rpt strip_tac
  \\ fs[bytes_in_memory_def]
QED

fun map_first_cj t =
  let
    fun gen_list n =
      case total (cj n) t of
        NONE => []
      | SOME t' => t'::gen_list (n+1)
  in
  MAP_FIRST ho_match_mp_tac $ gen_list 1
end

val enc_is_valid_mapped_access_tac =
    fs[is_valid_mapped_read_def,is_valid_mapped_write_def]
    \\ fs[enc_with_nop_thm]
    \\ rfs[]
    \\ drule_then assume_tac $
        cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM] bytes_in_memory_APPEND
    \\ drule_then assume_tac bytes_in_memory_in_domain
    \\ irule bytes_in_memory_change_mem
    \\ qexists `t1.mem`
    \\ simp[];

fun share_mem_load_compile_correct_tac ffi_name new_t1 nb new_ffi =
  qpat_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs i` $
    qspec_then `n''` drule_all
  \\ strip_tac
  \\ fs[call_FFI_def]
  \\ last_x_assum irule
  \\ simp[]
  \\ conj_tac
  >- (rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then [`ms2`, `t1'`, `k`, `a1`, `a2`] mp_tac
      \\ simp[] )
  \\ conj_tac
  >- (rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ fs[IMP_CONJ_THM, AND_IMP_INTRO]
    \\ conj_tac
    \\ strip_tac
    \\ first_x_assum map_first_cj
    \\ fs[]
    \\ qexistsl [`st`, `new_st`]
    \\ simp[]
    \\ irule $ cj 2 RTC_RULES
    \\ qexists new_ffi
    \\ simp[evaluatePropsTheory.call_FFI_rel_def]
    \\ qexists ffi_name
    \\ simp[call_FFI_def, AllCaseEqs()]
    \\ metis_tac[] )
  >- (
    rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ conj_tac
    >- (
      rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then
        [`ms2`,`k+1`,`index'`,`new_bytes`,`t1'`,`bytes'`,`bytes2`,`st`,`new_st`]
        assume_tac
      \\ first_x_assum ho_match_mp_tac
      \\ fs[]
      \\ irule $ cj 2 RTC_RULES
      \\ qexists new_ffi
      \\ simp[evaluatePropsTheory.call_FFI_rel_def]
      \\ qexists ffi_name
      \\ simp[call_FFI_def, AllCaseEqs()]
      \\ metis_tac[] )
    >- (
      simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
      \\ first_x_assum $ qspecl_then
        [`ms1`, `0`,`index`,`v4`, `t1`, nb,`n''`,`c`,`n'`,
          `p + n2w (LENGTH bytes + pos_val s1.pc 0 code2)`,`s1.ffi`,
          new_ffi] mp_tac
      \\ simp[]
      \\ impl_tac
      >- (
        simp[target_state_rel_def]
        \\ drule find_index_LESS_LENGTH
        \\ simp[]
        \\ disch_then kall_tac
        \\ fs[find_index_INDEX_OF, INDEX_OF_eq_SOME] )
      \\ impl_tac
      >- (
        gvs[is_valid_mapped_write_def,is_valid_mapped_read_def,good_dimindex_def]
        \\ gvs[enc_with_nop_thm]
        \\ drule $ cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM] bytes_in_memory_APPEND
        \\ strip_tac
        \\ drule_all bytes_in_memory_eq_mem
        \\ simp[]
      )
      \\ rpt strip_tac
      \\ fs[target_state_rel_def]
      \\ first_x_assum $ irule_at (Pat `all_enc_ok`)
      \\ qexists new_t1
      \\ rw[]
      >- (first_x_assum irule >> metis_tac[])
      \\ simp[APPLY_UPDATE_THM]
      \\ IF_CASES_TAC
      \\ fs[word_loc_val_def]
    )
  );

fun share_mem_store_compile_correct_tac ffi_name new_t1 (nb: term frag list) new_ffi =
  let
    val (wnb: term frag list) = `n2w (` @ nb @ `)`
  in
  qpat_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs i` $
    qspec_then `n''` drule_all
  \\ rpt strip_tac
  \\ `mc_conf.target.get_reg ms1 n' = t1.regs n'` by (
        qpat_x_assum `!i. _ ==> mc_conf.target.get_reg ms1 i = t1.regs i` $
          qspec_then `n'` irule
        \\ simp[] )
  \\ `(dimindex (:α) DIV 8) MOD 256 = dimindex (:α) DIV 8` by fs[good_dimindex_def]
  \\ gvs[call_FFI_def,LENGTH_APPEND,inc_pc_def,dec_clock_def]
  \\ last_x_assum irule
  \\ simp[]
  \\ conj_tac
  >- (rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then [`ms2`, `t1'`, `k`, `a1`, `a2`] mp_tac
      \\ simp[] )
  \\ conj_tac
  >- (rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ fs[IMP_CONJ_THM, AND_IMP_INTRO]
    \\ conj_tac
    \\ strip_tac
    \\ first_x_assum map_first_cj
    \\ fs[]
    \\ qexistsl [`st`, `new_st`]
    \\ simp[]
    \\ irule $ cj 2 RTC_RULES
    \\ qexists new_ffi
    \\ simp[evaluatePropsTheory.call_FFI_rel_def]
    \\ qexists ffi_name
    \\ simp[call_FFI_def, AllCaseEqs()]
    \\ qexistsl [
      `[` @ wnb @ `]`,
      `w2wlist_le (t1.regs n') (`  @ nb @ `) ++ addr2w8list (c + t1.regs n'')`,
      `v4`, `ffi'`]
    \\ gvs[LENGTH_APPEND] )
  >- (
    rpt gen_tac
    \\ simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
    \\ conj_tac
    >- (
      rpt gen_tac
      \\ strip_tac
      \\ first_x_assum $ qspecl_then
        [`ms2`,`k+1`,`index'`,`new_bytes`,`t1'`,`bytes'`,`bytes2`,`st`,`new_st`]
        assume_tac
      \\ first_x_assum ho_match_mp_tac
      \\ fs[]
      \\ irule $ cj 2 RTC_RULES
      \\ qexists new_ffi
      \\ simp[evaluatePropsTheory.call_FFI_rel_def]
      \\ qexists ffi_name
      \\ simp[call_FFI_def, AllCaseEqs()]
      \\ qexistsl [
        `[` @ wnb @ `]`,
        `w2wlist_le (t1.regs n') (`  @ nb @ `) ++ addr2w8list (c + t1.regs n'')`,
        `v4`, `ffi'`]
      \\ fs[LENGTH_APPEND] )
    >- (
      simp[apply_oracle_def,shift_interfer_def,shift_seq_def]
      \\ first_x_assum $ qspecl_then
        [`ms1`, `0`,`index`,`v4`, `t1`, wnb,`n''`,`c`,`n'`,
          `p + n2w (LENGTH bytes + pos_val s1.pc 0 code2)`,`s1.ffi`,
          new_ffi] mp_tac
      \\ simp[]
      \\ impl_tac
      >- (
        simp[target_state_rel_def]
        \\ drule find_index_LESS_LENGTH
        \\ simp[]
        \\ disch_then kall_tac
        \\ fs[find_index_INDEX_OF, INDEX_OF_eq_SOME] )
      \\ impl_tac
      >- (
        gvs[is_valid_mapped_write_def,is_valid_mapped_read_def,good_dimindex_def]
        \\ gvs[enc_with_nop_thm]
        \\ drule $ cj 1 $ cj 1 $ PURE_REWRITE_RULE [EQ_IMP_THM] bytes_in_memory_APPEND
        \\ strip_tac
        \\ drule_all bytes_in_memory_eq_mem
        \\ simp[]
      )
      \\ rpt strip_tac
      \\ fs[target_state_rel_def]
      \\ first_x_assum $ irule_at (Pat `all_enc_ok`)
      \\ qexists new_t1
      \\ rw[]
      >- (first_x_assum irule >> metis_tac[])
      \\ simp[APPLY_UPDATE_THM]
      \\ IF_CASES_TAC
      \\ fs[word_loc_val_def]
    )
  )
end

Theorem ffi_entry_pcs_NOT_ccache_OR_halt_pc:
   find_index pc mc_conf.ffi_entry_pcs 0 =
      SOME index /\
   mc_conf.halt_pc <> EL index mc_conf.ffi_entry_pcs /\
   mc_conf.ccache_pc <> EL index mc_conf.ffi_entry_pcs ==>
   pc <> mc_conf.ccache_pc /\
   pc <> mc_conf.halt_pc
Proof
  rpt strip_tac >>
  gvs[find_index_INDEX_OF,INDEX_OF_eq_SOME]
QED

val share_mem_eval_expand_tac =
  fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,AllCaseEqs(),call_FFI_def]
  \\ simp[Once targetSemTheory.evaluate_def]
  \\ fs[state_rel_def,share_mem_domain_code_rel_def,asm_fetch_def,
    ELIM_UNCURRY,get_memop_info_def]
  \\ drule_all $ GEN_ALL IMP_bytes_in_memory_ShareMem
  \\ strip_tac
  \\ qpat_assum `!pc op re a inst len i. asm_fetch_aux _ _ = SOME _ /\
      mmio_pcs_min_index _ = SOME _ ==> _` drule_all
  \\ strip_tac
  \\ drule find_index_is_MEM
  \\ fs[target_state_rel_def]
  \\ disch_then kall_tac
  \\ fs[share_mem_state_rel_def]
  \\ qpat_assum `!index' i'. mmio_pcs_min_index _ = SOME i' /\ index' < _ /\
      _ ==> _` $ qspec_then `index` drule
  \\ (
    impl_tac >- (drule find_index_LESS_LENGTH >> fs[])
    \\ disch_then assume_tac
    \\ `mc_conf.target.get_pc ms1 <> mc_conf.ccache_pc /\
        mc_conf.target.get_pc ms1 <> mc_conf.halt_pc` by (
          irule ffi_entry_pcs_NOT_ccache_OR_halt_pc >> gvs[])
    \\ rfs[get_memop_info_def]
    \\ TOP_CASE_TAC
    \\ fs[labSemTheory.addr_def,AllCaseEqs()]
    \\ rw[GSYM PULL_EXISTS]
    \\ `(dimindex (:'a) DIV 8) MOD 256 <> 1` by (
      rfs[good_dimindex_def] >> fs[])
    \\ fs[asm_ok_def,inst_ok_def,reg_ok_def]
  );

Theorem ffi_name_NOT_Mapped:
  mmio_pcs_min_index ffi_names = SOME i /\ (∃str. s = ExtCall str) ∧
  MEM s ffi_names ==>
  get_ffi_index ffi_names s < i
Proof
  rpt strip_tac >>
  drule_then assume_tac EL_get_ffi_index_MEM >>
  fs[mmio_pcs_min_index_def] >>
  gvs[some_def] >>
  SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  ntac 3 $ last_x_assum kall_tac >>
  res_tac >>
  Cases_on `get_ffi_index ffi_names s < x'` >>
  gvs[get_ffi_index_def] >>
  drule_then assume_tac find_index_MEM >>
  first_x_assum $ qspec_then `0` assume_tac >>
  rw[] >>
  gvs[backendPropsTheory.the_eqn] >>
  spose_not_then assume_tac>>fs[NOT_LESS]>>
  first_x_assum $ qspec_then `i` assume_tac >>gvs[]
QED

Theorem mmio_pcs_min_index_is_SOME:
!ffi_names.
  mmio_pcs_min_index ffi_names = SOME i ==>
  i <= LENGTH ffi_names /\
  (∀j. j < i ⇒
    (∃s. EL j ffi_names = ExtCall s)) ∧
   (∀j. i ≤ j ∧ j < LENGTH ffi_names ⇒
     (∃op. EL j ffi_names = SharedMem op))
Proof
  ntac 2 strip_tac >>
  gvs[mmio_pcs_min_index_def,some_def] >>
  SELECT_ELIM_TAC >>
  gvs[] >>
  qexists `x` >>
  gvs[]
QED

Theorem no_share_mem_lemma:
  mmio_pcs_min_index ffi_names = SOME i /\
  asm_fetch_aux pc code = SOME (LabAsm Install c l n) /\
  no_install_or_no_share_mem code ffi_names ==>
  i = LENGTH ffi_names
Proof
  rpt strip_tac >>
  drule mmio_pcs_min_index_is_SOME >>
  rpt strip_tac >>
  gvs[no_install_or_no_share_mem_def,no_install_def,no_share_mem_inst_def,EVERY_EL] >>
  spose_not_then assume_tac>>fs[LESS_OR_EQ]>>
  first_x_assum $ qspec_then `i` assume_tac >>
  first_x_assum $ qspec_then `i` assume_tac >>gvs[]
QED

Theorem asm_fetch_aux_APPEND1:
!pc code.
  pc < num_pcs code ==>
  asm_fetch_aux pc (code ++ sec_list) = asm_fetch_aux pc code
Proof
  ho_match_mp_tac asm_fetch_aux_ind >>
  rpt strip_tac >>
  gvs[num_pcs_def,asm_fetch_aux_def] >>
  Cases_on `y` >>
  gvs[is_Label_def,asm_fetch_aux_def,num_pcs_def]
QED

Theorem pos_val_APPEND1:
!pc code.
  pc < num_pcs code ==>
  pos_val pc 0 (code ++ sec_list) = pos_val pc 0 code
Proof
  Induct_on `code` >>
  gvs[num_pcs_def, pos_val_def] >>
  Induct_on `h` >>
  Induct_on `l` >>
  rw[num_pcs_def, pos_val_def]
  >- metis_tac[pos_val_acc_0]
  >- metis_tac[pos_val_acc_0]
  >- (
    first_x_assum $ qspecl_then [`n`,`pc-1`] mp_tac >>
    impl_tac
    >- decide_tac >>
    metis_tac[pos_val_acc_0]
  )
QED

Theorem asm_fetch_aux_APPEND2:
!code.
  asm_fetch_aux (pc + num_pcs code) (code ++ sec_list) =
    asm_fetch_aux pc sec_list
Proof
  ho_match_mp_tac num_pcs_ind >>
  rpt strip_tac >>
  gvs[num_pcs_def,asm_fetch_aux_def] >>
  Cases_on `x` >>
  gvs[is_Label_def,num_pcs_def,asm_fetch_def]
QED

Theorem pos_val_APPEND2:
!c labs ffis p code.
  all_enc_ok c labs ffis p code ==>
  pos_val (pc + num_pcs code) 0 (code ++ sec_list) =
    LENGTH (prog_to_bytes code) + pos_val pc 0 sec_list
Proof
  ho_match_mp_tac all_enc_ok_ind >>
  rpt strip_tac >>
  gvs[num_pcs_def,pos_val_def,all_enc_ok_def,prog_to_bytes_def] >>
  Cases_on `y` >>
  gvs[is_Label_def,num_pcs_def,pos_val_def,line_length_def,
    line_ok_def,prog_to_bytes_def,line_bytes_def] >>
  metis_tac[pos_val_acc_0]
QED

Theorem get_shmem_info_MappedRead_or_MappedWrite:
!sec pos ffi_names info new_ffi_names new_info.
  get_shmem_info sec pos ffi_names info =
    (new_ffi_names,new_info) ==>
  ?l. new_ffi_names = ffi_names ++ l /\
    EVERY (\x. ∃op. x = SharedMem op) l
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  Cases_on `m` >>
  gvs[get_memop_info_def]
QED

Theorem no_share_mem_APPEND:
  no_share_mem_inst code /\
  no_share_mem_inst secs ==>
  no_share_mem_inst (code ++ secs)
Proof
  rpt strip_tac >>
  gvs[no_share_mem_inst_def] >>
  rpt strip_tac >>
  Cases_on `p < num_pcs code`
  >- metis_tac[asm_fetch_aux_APPEND1] >>
  `num_pcs code <= p` by decide_tac >>
  drule LESS_EQUAL_ADD >>
  strip_tac >>
  gvs[] >>
  metis_tac[asm_fetch_aux_APPEND2]
QED

Theorem no_install_APPEND_IMP:
  no_install (code ++ secs) ==>
  no_install code /\ no_install secs
Proof
  rw[] >>
  gvs[no_install_def] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  drule_then assume_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
  irule_at (Pos hd) EQ_TRANS >>
  first_x_assum $ irule_at (Pos last) >>
  metis_tac[asm_fetch_aux_APPEND1,asm_fetch_aux_APPEND2]
QED

Theorem code_similar_IMP_both_no_share_mem:
  code_similar code sec_list /\
  no_share_mem_inst code ==>
  no_share_mem_inst sec_list
Proof
  rpt strip_tac >>
  drule code_similar_IMP_asm_fetch_aux_line_similar >>
  gvs[no_share_mem_inst_def,OPTREL_def,line_similar_def] >>
  rw[] >>
  first_x_assum $ qspec_then `p` assume_tac >>
  gvs[DefnBase.one_line_ify NONE line_similar_def] >>
  pop_assum mp_tac >>
  rpt TOP_CASE_TAC >>
  metis_tac[]
QED

Theorem code_similar_IMP_both_no_install_or_no_share_mem:
  code_similar code sec_list /\
  no_install_or_no_share_mem code ffi_names ==>
  no_install_or_no_share_mem sec_list ffi_names
Proof
  rpt strip_tac >>
  drule code_similar_IMP_asm_fetch_aux_line_similar >>
  gvs[OPTREL_def,no_install_or_no_share_mem_def] >>
  rw[]
  >- (
    disj1_tac >>
    gvs[no_share_mem_inst_def] >>
    rw[] >>
    first_x_assum $ qspec_then `p` assume_tac >>
    rw[] >>
    gvs[] >>
    pop_assum mp_tac >>
    simp[DefnBase.one_line_ify NONE line_similar_def] >>
    rpt TOP_CASE_TAC >>
    metis_tac[]
  ) >>
  disj2_tac >>
  gvs[no_install_def] >>
  rw[] >>
  first_x_assum $ qspec_then `p` assume_tac >>
  rw[] >>
  gvs[] >>
  pop_assum mp_tac >>
  simp[DefnBase.one_line_ify NONE line_similar_def] >>
  rpt TOP_CASE_TAC >>
  metis_tac[]
QED

Theorem no_share_mem_IMP_get_shmem_info:
!code p ffi_names shmem_info.
  no_share_mem_inst code ==>
  get_shmem_info code p ffi_names shmem_info = (ffi_names,shmem_info)
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rw[] >>
  gvs[no_share_mem_inst_def,get_shmem_info_def,asm_fetch_aux_def]
  >- (
    pairarg_tac >>
    fs[] >>
    irule EQ_TRANS >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[] >>
    last_x_assum mp_tac >>
    simp[AllCaseEqs()] >>
    metis_tac[]
  ) >>
  last_x_assum irule >>
  rw[] >>
  strip_tac >>
  last_x_assum mp_tac >>
  simp[AllCaseEqs()] >>
  qexists `p + 1` >>
  simp[]
QED

(* move *)
Theorem Sh_not_Ext:
  (∃s. x = SharedMem s) ⇔ (∀s. x ≠ ExtCall s)
Proof
  Cases_on ‘x’>>gvs[]
QED

Theorem not_Sh_Ext:
  (∀s. x ≠ SharedMem s) ⇔ (∃s. x = ExtCall s)
Proof
  Cases_on ‘x’>>gvs[]
QED

val say = say0 "compile_correct";

Theorem compile_correct:
  !^s1 res (mc_conf: ('a,'state,'b) machine_config) s2 code2 labs t1 ms1.
     (evaluate s1 = (res,s2)) /\ (res <> Error) /\
     encoder_correct mc_conf.target /\
     state_rel (mc_conf,code2,labs,p) s1 t1 ms1 ==>
     ?k t2 ms2.
       (evaluate mc_conf s1.ffi (s1.clock + k) ms1 =
          (res,
           ms2,s2.ffi))
Proof
  HO_MATCH_MP_TAC labSemTheory.evaluate_ind \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [labSemTheory.evaluate_def]
  \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC)) \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ full_simp_tac(srw_ss())[Once targetSemTheory.evaluate_def]
         \\ metis_tac [])
  \\ Cases_on `asm_fetch s1` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC)) \\ full_simp_tac(srw_ss())[LET_DEF]
  THEN1 (
    fs[case_eq_thms]>>rw[]
    THEN1 (* Asm Inst *) (
       say "Asm Inst"
       \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (Asm (Asmi(Inst i)) bytes len)`
       \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
       \\ mp_tac IMP_bytes_in_memory_Inst
       \\ full_simp_tac(srw_ss())[]
       \\ impl_tac
       THEN1 (full_simp_tac(srw_ss())[state_rel_def])
       \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
       \\ qpat_abbrev_tac `jj = asm$Inst i` \\ rpt strip_tac
       \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
            asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
       \\ disch_then (mp_tac o Q.SPEC `bytes'`)
       \\ impl_tac>-
        (imp_res_tac Inst_lemma \\ pop_assum (K all_tac)
         \\ full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
         \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
         \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
         \\ conj_tac
         >- (fs[asm_fetch_def] >>
          `!op re a. Asmi (Inst i) <> ShareMem op re a` by simp[] >>
          drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm >>
          simp[])
         \\ qpat_x_assum `bytes_in_mem ww bytes' t1.mem
               t1.mem_domain s1.mem_domain` mp_tac
         \\ match_mp_tac bytes_in_mem_IMP_memory \\ full_simp_tac(srw_ss())[])
       \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
       \\ rfs[] \\ fs[]
       \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
            `code2`,`labs`,
            `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
       \\ impl_tac THEN1
        (unabbrev_all_tac \\ rpt strip_tac \\ full_simp_tac(srw_ss())[asm_def]
         THEN1 (full_simp_tac(srw_ss())[shift_interfer_def])
         \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
         \\ match_mp_tac state_rel_shift_interfer
         \\ drule Inst_lemma \\ fs[])
       \\ rpt strip_tac \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
       \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
       \\ rpt strip_tac
       \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
       \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
       \\ fs[asm_inst_consts])
    THEN1 (* Asm JumpReg *) (
      say "Asm JumpReg"
      \\ qmatch_assum_rename_tac `read_reg r1 s1 = Loc l1 l2`
      \\ Cases_on `loc_to_pc l1 l2 s1.code` \\ full_simp_tac(srw_ss())[]
      \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`, `s1.ffi`, `JumpReg r1`]MP_TAC
           asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >-
       (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
        \\ conj_tac
        >- (fs[asm_fetch_def]
          \\ drule_all $ GEN_ALL IMP_bytes_in_memory
          \\ strip_tac
          \\ fs[]
          \\ `!op re a. Asmi (JumpReg r1) <> ShareMem op re a` by simp[]
          \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm
          \\ `LENGTH ((mc_conf.target.config.encode (JumpReg r1))) <=
            LENGTH (line_bytes j)`
            suffices_by metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
          \\ Cases_on `j`
          \\ fs[line_similar_def,line_ok_def]
          \\ fs[enc_with_nop_thm,line_length_def]
          \\ Cases_on `a` >> fs[]
          \\ metis_tac[LENGTH_APPEND,LESS_EQ_ADD])
        \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
        \\ imp_res_tac bytes_in_mem_IMP
        \\ full_simp_tac(srw_ss())[IMP_bytes_in_memory_JumpReg,asmSemTheory.upd_pc_def,
               asmSemTheory.assert_def]
        \\ imp_res_tac IMP_bytes_in_memory_JumpReg \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
        \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
        \\ FIRST_X_ASSUM (kall_tac o Q.SPEC `r1:num`)
        \\ qpat_x_assum `!n. n<s1.code_buffer.space_left ==> _` kall_tac
        \\ qpat_x_assum `!r. word_loc_val _ _ (read_reg r _) = _` (MP_TAC o Q.SPEC `r1:num`)
        \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[word_loc_val_def]
        \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `xx = t1.regs r1` (fn th => full_simp_tac(srw_ss())[GSYM th])
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ (alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> irule)
        \\ conj_tac >- fs[alignmentTheory.aligned_bitwise_and]
        \\ simp[aligned_w2n]
        \\ qmatch_goalsub_abbrev_tac`pv MOD dw MOD _`
        \\ `pv MOD dw = pv` by (
          simp[Abbr`pv`,Abbr`dw`]
          \\ irule LESS_EQ_LESS_TRANS
          \\ qexists_tac`LENGTH (prog_to_bytes code2)`
          \\ simp[]
          \\ drule pos_val_bound
          \\ disch_then(qspec_then`0`mp_tac o CONV_RULE SWAP_FORALL_CONV)
          \\ simp[] )
        \\ simp[]
        \\ qunabbrev_tac`pv`
        \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
        \\ match_mp_tac pos_val_MOD_0 \\ gvs[]
        \\ metis_tac[has_odd_inst_alignment] )
      \\ rpt strip_tac
      \\ rfs[] \\ fs[] \\ rfs[]
      \\ FIRST_X_ASSUM (qspecl_then [`shift_interfer l' mc_conf`,
           `code2`,`labs`,`(asm (JumpReg r1)
              (t1.pc + n2w (LENGTH (mc_conf.target.config.encode (JumpReg r1)))) t1)`,`ms2`] mp_tac)
      \\ impl_tac >-
       (full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
               asmSemTheory.read_reg_def,dec_clock_def,labSemTheory.upd_pc_def,
               labSemTheory.assert_def]
        \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
        \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
        \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
        \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
        \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[word_loc_val_def]
        \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `xx = t1.regs r1` (fn th => full_simp_tac(srw_ss())[GSYM th])
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ res_tac \\ srw_tac[][]
        >- ((alignmentTheory.aligned_add_sub_cor
            |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> irule)
          \\ conj_tac >- fs[alignmentTheory.aligned_bitwise_and]
          \\ simp[aligned_w2n]
          \\ qmatch_goalsub_abbrev_tac`pv MOD dw MOD _`
          \\ `pv MOD dw = pv` by (
            simp[Abbr`pv`,Abbr`dw`]
            \\ irule LESS_EQ_LESS_TRANS
            \\ qexists_tac`LENGTH (prog_to_bytes code2)`
            \\ simp[]
            \\ drule pos_val_bound
            \\ disch_then(qspec_then`0`mp_tac o CONV_RULE SWAP_FORALL_CONV)
            \\ simp[] )
          \\ simp[]
          \\ qunabbrev_tac`pv`
          \\ match_mp_tac $ Q.GEN `ffi_names` pos_val_MOD_0 \\ fs[]
          \\ metis_tac[has_odd_inst_alignment])
        >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
        >- fs[share_mem_domain_code_rel_def] )
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ srw_tac[][]
      \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
      \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
      \\ Q.EXISTS_TAC `ms2'` \\ fs[state_rel_def,shift_interfer_def] ))
  THEN1 ( (* CBW *)
    say "CBW" >>
    fs[case_eq_thms]>>
    fs[dec_clock_def]>>
    qmatch_asmsub_rename_tac `Asm (Cbw r1 r2) bytes len`>>
    qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names` >>
    mp_tac IMP_bytes_in_memory_Cbw>> impl_tac>-
      fs[state_rel_def]>>
    strip_tac>>
    `t1.regs r1 = w1 ∧ t1.regs r2 = w2` by
      (fs[state_rel_def]>>
      qpat_assum`!r. word_loc_val _ _ _ = SOME _` (qspec_then`r1` mp_tac)>>
      qpat_x_assum`!r. word_loc_val _ _ _ = SOME _` (qspec_then`r2` mp_tac)>>
      simp[word_loc_val_def])>>
    qpat_x_assum`buffer_write _ _ _ = _ `mp_tac>>
    simp[buffer_write_def]>>
    strip_tac>>
    qmatch_asmsub_abbrev_tac`Inst jj`>>
    (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`Inst jj`]MP_TAC
            asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (mp_tac o Q.SPEC `bytes'`)
    \\ fs[asm_def] >>
    `inst jj t1 = t1 with mem := ((w1 =+ w2w w2) t1.mem)` by
      (unabbrev_all_tac >>
      simp[inst_def,mem_op_def,mem_store_def,alignmentTheory.aligned_0]>>
      EVAL_TAC>> simp[asm_state_component_equality]>>
      fs[state_rel_def]>>rw[]>>
      first_x_assum drule>>simp[])
    \\ impl_tac>-
      (fs[state_rel_def]>>
      conj_tac >- (
        fs[asm_fetch_def]
        \\ drule_all $ GEN_ALL IMP_bytes_in_memory
        \\ strip_tac
        \\ fs[]
        \\ `!op re a. Cbw r1 r2 <> ShareMem op re a` by simp[]
        \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_Asm
        \\ `LENGTH bytes' <= LENGTH (line_bytes j)` suffices_by
          metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
        \\ Cases_on `j`
        \\ fs[line_similar_def,line_ok_def]) >>
      conj_tac>-
        (match_mp_tac (GEN_ALL bytes_in_mem_IMP)>>
        qexists_tac`s1.mem_domain`>>
        match_mp_tac bytes_in_mem_UPDATE>>
        rw[]>>
        PURE_REWRITE_TAC [GSYM WORD_ADD_ASSOC]>>
        `LENGTH bytes' + pos_val s1.pc 0 code2 <= LENGTH (prog_to_bytes code2)` by
          (qpat_x_assum`pos_val _ _ _ = _` sym_sub_tac>>
          drule pos_val_bound>>
          disch_then(qspecl_then [`s1.pc+1`,`0`] assume_tac)>>
          fs[])>>
        rw[]>>
        simp[word_add_n2w])>>
      simp[asm_step_nop_def,asm_def]) >>
    strip_tac>>
    first_x_assum (qspecl_then [`shift_interfer l mc_conf`,
          `code2`,`labs`,
          `(asm (Inst jj) (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`] mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac \\ rpt strip_tac \\ full_simp_tac(srw_ss())[asm_def]
      >-
        (full_simp_tac(srw_ss())[shift_interfer_def])
      >>
      qpat_x_assum`_ = new_cb` sym_sub_tac >> fs[]>>
      match_mp_tac state_rel_shift_interfer>>
      fs[state_rel_def]>>
      rfs[]>>fs[]>>
      conj_tac>- metis_tac[]>>
      conj_tac>- metis_tac[]>>
      conj_tac>-
        (rw[APPLY_UPDATE_THM]>>
        first_x_assum drule>>
        fs[])
      \\ conj_tac>-
        (strip_tac>>
        qpat_x_assum`!n. n <s1.code_buffer.space_left ⇒ _`
          (qspec_then`n+1` assume_tac)>>
        fs[])
      \\ conj_tac >-
        (* non-overlap of cb with code *)
        (match_mp_tac bytes_in_mem_UPDATE>>rw[]>>
        PURE_REWRITE_TAC [GSYM WORD_ADD_ASSOC]>>
        simp[word_add_n2w])
      \\ conj_tac >-
        (simp[bytes_in_mem_APPEND]
      \\ conj_tac >-
        (* non-overlap of cb with itself *)
        (match_mp_tac bytes_in_mem_UPDATE>>
          rw[])
      \\ simp[bytes_in_mem_def,APPLY_UPDATE_THM]>>
         first_x_assum drule>>fs[])
      \\ simp[GSYM word_add_n2w]
       >> fs[upd_pc_def, inc_pc_def, share_mem_state_rel_def] >>
        share_mem_state_rel_tac)
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
    \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
    \\ fs[])
  THEN1 ( (* share_mem_op *)
    say "share_mem_op"
    \\ Cases_on `m` >>
    fs[share_mem_op_def,share_mem_load_def,share_mem_store_def]>>
    gvs[pair_case_eq,option_case_eq, ffi_result_case_eq,CaseEq"word_loc"]>>
    fs[asm_fetch_def,state_rel_def]>>
    drule_all IMP_bytes_in_memory_ShareMem>>strip_tac>>
    fs[share_mem_domain_code_rel_def]>>
    qpat_assum `!pc op re a inst len i. asm_fetch_aux _ _ = SOME _ /\
    mmio_pcs_min_index _ = SOME _ ==> _` drule_all>>strip_tac>>
    fs[get_memop_info_def]>>
    drule find_index_is_MEM>>strip_tac>>
    simp[Once targetSemTheory.evaluate_def]>>
    qpat_x_assum ‘target_state_rel _ _ _’ assume_tac>>
    fs[target_state_rel_def]>>

    qpat_assum ‘share_mem_state_rel _ _ _ _ ’ assume_tac>>
    fs[share_mem_state_rel_def]>>
    qpat_assum `!index' i'. mmio_pcs_min_index _ = SOME i' /\ index' < _ /\
    _ ==> _` $ qspecl_then [`index`, `i`] drule>>

    (impl_tac>-(drule find_index_LESS_LENGTH >> fs[]))>>
    strip_tac>>
    `mc_conf.target.get_pc ms1 <> mc_conf.ccache_pc /\
    mc_conf.target.get_pc ms1 <> mc_conf.halt_pc` by (
      irule ffi_entry_pcs_NOT_ccache_OR_halt_pc >> gvs[])>>
    fs[]>>

    Cases_on ‘a'’>>
    fs[labSemTheory.addr_def,CaseEq"word_loc"]>>
    qpat_assum ‘∀r. word_loc_val _ _ _ = SOME _’ $ qspec_then ‘n''’ assume_tac>>
    TRY (qpat_assum ‘∀r. word_loc_val _ _ _ = SOME _’ $ qspec_then ‘n'’ assume_tac)>>
    fs[option_case_eq,CaseEq"word_loc"]>>
    qpat_x_assum ‘read_reg n'' _ = _ ’ $ assume_tac>>
    TRY (qpat_x_assum ‘read_reg n' _ = _ ’ $ assume_tac)>>
    fs[word_loc_val_def]>>
    qpat_x_assum ‘_ = v'’ $ assume_tac o GSYM>>

    qpat_assum ‘asm_ok _ _’ mp_tac>>
    rewrite_tac[asm_ok_def,inst_ok_def,reg_ok_def]>>strip_tac>>
    rfs[]>>
    ‘∀x. word_to_bytes_aux 1n x F = [get_byte 0w x F]’
      by (rewrite_tac[word_to_bytes_aux_def,ONE]>>simp[])>>
    ‘∀x:'a word. TAKE 1 (word_to_bytes x F) = [get_byte 0w x F]’
      by (qhdtm_x_assum ‘good_dimindex’ mp_tac >>
          rw[good_dimindex_def] >>
          rw[word_to_bytes_def,
             CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV word_to_bytes_aux_def]) >>
    ‘∀x:'a word. TAKE 4 (word_to_bytes x F) = word_to_bytes_aux 4 x F’
      by (qhdtm_x_assum ‘good_dimindex’ mp_tac >>
          rw[good_dimindex_def] >>
          rw[word_to_bytes_def,
             CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV word_to_bytes_aux_def]) >>
    Cases_on ‘ALOOKUP mc_conf.mmio_info index’>>fs[]>>
    fs[]
    >>~- ([‘Halt (FFI_outcome _)’],
          IF_CASES_TAC>>fs[]>>
          pop_assum irule>>
          enc_is_valid_mapped_access_tac>>fs[])>>
    gvs[]>>
    simp[bool_case_eq]>>
    simp[GSYM PULL_EXISTS]>>
    (conj_asm1_tac >-
      enc_is_valid_mapped_access_tac)>>fs[]>>
    pairarg_tac>>fs[inc_pc_def,dec_clock_def]>>
    last_x_assum $ irule>>fs[]>>
    (conj_tac >-
     (rpt strip_tac>>
      first_x_assum $ irule o cj 1>>
      first_assum $ irule_at Any>>
      metis_tac[]))>>
      rename1 ‘apply_oracle _ _ = (ms1', new_oracle)’>>
    (conj_tac >-
     (rpt gen_tac>>strip_tac>>
      fs[apply_oracle_def,shift_seq_def]>>
      qpat_x_assum ‘_ = new_oracle’ $ assume_tac o GSYM>>fs[]>>
      first_x_assum irule>>
      fs[]>>
      irule (cj 2 RTC_RULES)>>
      rfs[evaluatePropsTheory.call_FFI_rel_def]>>
      last_assum $ irule_at Any>>fs[]))>>
    (conj_tac >-
     (rpt gen_tac>>strip_tac>>
      fs[apply_oracle_def,shift_seq_def]>>
      qpat_x_assum ‘_ = new_oracle’ $ assume_tac o GSYM>>fs[]>>
      first_x_assum irule>>fs[]>>
      first_x_assum $ irule_at Any>>
      irule (cj 2 RTC_RULES)>>
      rfs[evaluatePropsTheory.call_FFI_rel_def]>>
      last_assum $ irule_at Any>>fs[]))>>


    fs[apply_oracle_def,shift_seq_def]>>
    qpat_x_assum ‘_ = ms1'’ $ assume_tac o GSYM>>fs[]>>
    qpat_x_assum ‘∀a b c d e f g h i j k l. _ ⇒ _’ mp_tac>>
    disch_then $ drule>>fs[]>>
    drule find_index_LESS_LENGTH>>strip_tac>>
    strip_tac>>
    (conj_tac >-
      (pop_assum mp_tac>>
       simp[target_state_rel_def]>>strip_tac>>
       pop_assum $ irule o cj 1>>
       fs[find_index_INDEX_OF, INDEX_OF_eq_SOME]>>
       rpt (last_x_assum $ irule_at Any)>>fs[]))>>

    qabbrev_tac ‘pc = p + n2w (LENGTH bytes + pos_val s1.pc 0n code2)’>>
    qmatch_asmsub_abbrev_tac ‘call_FFI _ _ [nb] _ = _’>>
    last_x_assum $ qspecl_then [‘ms1’, ‘0’, ‘new_bytes’, ‘t1’, ‘s1.ffi’, ‘new_ffi’] mp_tac>>
    (impl_tac>-
      fs[target_state_rel_def,find_index_INDEX_OF, INDEX_OF_eq_SOME])>>
    strip_tac>>rfs[Abbr ‘nb’]>>

    qmatch_asmsub_abbrev_tac ‘target_state_rel mc_conf.target t1_new’>>

    qexistsl [‘code2’, ‘labs’, ‘t1_new’] >> fs[]>>
    fs[Abbr ‘t1_new’]>>
    qpat_x_assum ‘∀a b c d e f. _ ⇒ _’ mp_tac>>
    ‘call_FFI_rel꙳ s1.ffi s1.ffi’ by fs[cj 1 RTC_RULES]>>
    rpt (disch_then $ drule_at Any)>>
    fs[find_index_INDEX_OF, INDEX_OF_eq_SOME]>>
    fs[target_state_rel_def,UPDATE_def]>>
    rw[word_loc_val_def]>>
    metis_tac[word_loc_val_def])
  THEN1 ( (* Jump *)
    say "Jump"
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)`
    \\ Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ mp_tac IMP_bytes_in_memory_Jump \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ `LENGTH
            ((mc_conf.target.config.encode
              (Jump
                 (n2w (find_pos jtarget labs) +
                  -n2w (pos_val s1.pc 0 code2)))))
          <= LENGTH (line_bytes j)` suffices_by
        metis_tac[ffi_entry_pcs_disjoint_LENGTH_shorter]
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      \\ fs[get_label_def]
      \\ Cases_on `jtarget`
      \\ fs[]
      \\ Cases_on `lab_lookup n'' n0 labs`
      \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
      \\ drule lab_lookup_IMP
      \\ fs[]
    )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.config.encode jj))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
      \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[]
      >- metis_tac[]
      >- metis_tac[]
      >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
      >- fs[share_mem_domain_code_rel_def] )
    \\ rpt strip_tac>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at Any>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at (Pos last)>>
    `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
    metis_tac[])
  THEN1 (* JumpCmp *)
   (say "JumpCmp"
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)`
    \\ `word_cmp cmp (read_reg rr s1) (labSem$reg_imm ri s1) =
        SOME (asm$word_cmp cmp (read_reg rr t1) (reg_imm ri t1))` by
     (Cases_on `word_cmp cmp (read_reg rr s1) (reg_imm ri s1)` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac word_cmp_lemma \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[]
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ Cases_on `word_cmp cmp (read_reg rr t1) (reg_imm ri t1)` \\ full_simp_tac(srw_ss())[]


    THEN1
     (Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
      \\ mp_tac IMP_bytes_in_memory_JumpCmp \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac IMP_IMP \\ strip_tac
      THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
      \\ rpt strip_tac \\ pop_assum mp_tac
      \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
      \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
           asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
        \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
        \\ imp_res_tac bytes_in_mem_IMP
        \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
        \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
        \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def]
        \\ fs[asm_fetch_def]
        \\ drule_all $ GEN_ALL IMP_bytes_in_memory
        \\ strip_tac
        \\ fs[]
        \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
        \\ ho_match_mp_tac (
          PURE_REWRITE_RULE [satTheory.AND_IMP] o
          PURE_REWRITE_RULE [Once CONJ_SYM] $
          GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
        \\ Cases_on `j`
        \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
        \\ fs[get_label_def]
        \\ Cases_on `jtarget`
        \\ fs[]
        \\ Cases_on `lab_lookup n'' n0 labs`
        \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
        \\ drule lab_lookup_IMP
        \\ fs[]
      )
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
           `code2`,`labs`,
           `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.config.encode jj))) t1)`,`ms2`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (unabbrev_all_tac
        \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
               asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
               labSemTheory.assert_def,asm_def,
               jump_to_offset_def]
        \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
        \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
              WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
        \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
        \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[]
        >- metis_tac []
        >- metis_tac []
        >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
        >- fs[share_mem_domain_code_rel_def] )
      \\ rpt strip_tac>>
      irule_at Any EQ_TRANS>>
      first_x_assum $ irule_at Any>>
      irule_at Any EQ_TRANS>>
      first_x_assum $ irule_at (Pos last)>>
      `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
      metis_tac[])
    \\ mp_tac (IMP_bytes_in_memory_JumpCmp_1) \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def] )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
      >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
      >- fs[share_mem_domain_code_rel_def] )
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`mp_tac)
    \\ rpt strip_tac>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at Any>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at (Pos last)>>
    `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC>>
    metis_tac[])
  THEN1 (* Call *)
   (say "Call"
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call (Lab l1 l2)) l bytes len)`
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ (Q.SPECL_THEN [`Lab l1 l2`,`len`]mp_tac
            (Q.GENL[`ww`,`n`]IMP_bytes_in_memory_Call))
    \\ match_mp_tac IMP_IMP \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  THEN1 (* LocValue *)
   (say "LocValue"
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) ww bytes len)`
    \\ full_simp_tac(srw_ss())[lab_to_loc_def]
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ mp_tac (Q.INST [`l`|->`ww`,`n`|->`len`]
               IMP_bytes_in_memory_LocValue) \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ Cases_on `get_pc_value (Lab l1 l2) s1` \\ fs []
    \\ qpat_abbrev_tac `jj = asm$Loc reg lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def] )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF]
      \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][word_loc_val_def]
      \\ res_tac \\ full_simp_tac(srw_ss())[]
      >- (
        Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac lab_lookup_IMP \\ srw_tac[][] )
      >- (fs[share_mem_state_rel_def] >> share_mem_state_rel_tac)
      >- fs[share_mem_domain_code_rel_def] )
    \\ rpt strip_tac>>
    gvs[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at Any>>
    first_x_assum $ qspec_then ‘k + s1.clock - 1’ assume_tac>>
    fs[]>>
    qpat_x_assum ‘evaluate _ _ _ _ = evaluate _ _ _ _’ mp_tac>>
    `k + s1.clock - 1 + l = k + l - 1 + s1.clock` by DECIDE_TAC>>
    pop_assum (fn h => rewrite_tac[h])>>strip_tac>>
    first_assum $ irule_at Any)
  THEN1 (* CallFFI *)
   (say "CallFFI"
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (CallFFI s) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (CallFFI s) l bytes n)`
    \\ Cases_on `s1.regs s1.len_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.len2_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.link_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.ptr2_reg` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `read_reg _.len2_reg _ = Word c2`
    \\ qmatch_assum_rename_tac `read_reg _.ptr2_reg _ = Word c2'`
    \\ qmatch_assum_rename_tac `read_reg _.ptr_reg _ = Word c'`
    \\ Cases_on `read_bytearray c' (w2n c) (mem_load_byte_aux s1.mem s1.mem_domain s1.be)`
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `read_bytearray c2' (w2n c2) (mem_load_byte_aux s1.mem s1.mem_domain s1.be)`
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `s1.regs s1.link_reg = Loc n1 n2`
    \\ qmatch_asmsub_abbrev_tac `loc_to_pc a1 a2 a3`
    \\ Cases_on `loc_to_pc a1 a2 a3` >- fs[]
    \\ unabbrev_all_tac \\ fs[]
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ mp_tac (Q.GEN `name` IMP_bytes_in_memory_CallFFI) \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def,asm_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      \\ gvs[lab_inst_def,enc_with_nop_thm, LENGTH_APPEND]
    )
    \\ rpt strip_tac
    \\ Cases_on `loc_to_pc n1 n2 s1.code` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `loc_to_pc n1 n2 s1.code = SOME new_pc`
    \\ `mc_conf.target.get_pc ms2 = p - n2w ((3 + get_ffi_index ffi_names (ExtCall s)) * ffi_offset)` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())
           [encoder_correct_def,target_ok_def,target_state_rel_def]
      \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asm_def,asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def]
      \\ rewrite_tac [GSYM word_sub_def,WORD_SUB_PLUS,
           GSYM word_add_n2w,WORD_ADD_SUB]) \\ full_simp_tac(srw_ss())[]
    \\ `has_io_name s s1.code` by
          (imp_res_tac IMP_has_io_name \\ NO_TAC)
    \\ `MEM (ExtCall s) mc_conf.ffi_names` by (
      imp_res_tac has_io_name_find_index>>
      imp_res_tac find_index_is_MEM>>
      gvs[list_subset_def,state_rel_def,EVERY_MEM,Abbr`ffi_names`]>>
      drule_all mmio_pcs_min_index_is_SOME >>
      strip_tac >>
      gvs[MEM_FILTER] >>
      `MEM s mc_conf.ffi_names` by (
        first_x_assum irule >> gvs[]) >>
      gvs[MEM_EL] >>
      `n'' < i` by (
        spose_not_then assume_tac >>
        `i <= n''` by decide_tac >>
        first_x_assum drule_all >>
        gvs[]
      ) >>
      qexists `n''` >>
      gvs[] >>
      irule $ GSYM EL_TAKE >>
      simp[]
    )
    \\ `~(mc_conf.target.get_pc ms2 IN mc_conf.prog_addresses) /\
        ~(mc_conf.target.get_pc ms2 = mc_conf.halt_pc) /\
        ~(mc_conf.target.get_pc ms2 = mc_conf.ccache_pc) /\
        (find_index (mc_conf.target.get_pc ms2) mc_conf.ffi_entry_pcs 0 =
           SOME (get_ffi_index mc_conf.ffi_names (ExtCall s))) /\
        get_ffi_index mc_conf.ffi_names (ExtCall s) = get_ffi_index ffi_names (ExtCall s)` by (
       full_simp_tac(srw_ss())[state_rel_def]>>
       first_x_assum $ qspecl_then [`ExtCall s`, `i`] drule >>
       gvs[] >>
       impl_keep_tac
       >- (irule ffi_name_NOT_Mapped >> fs[]) >>
       `get_ffi_index mc_conf.ffi_names (ExtCall s) = get_ffi_index ffi_names (ExtCall s)`
         suffices_by gvs[] >>
       gvs[get_ffi_index_def,backendPropsTheory.the_eqn] >>
       gvs[Abbr`ffi_names`] >>
       imp_res_tac find_index_MEM >>
       first_x_assum $ qspec_then `0` assume_tac >>fs[]>>
       fs[CaseEq"option"]>>irule OR_INTRO_THM2>>
       Cases_on ‘i ≤ LENGTH mc_conf.ffi_names’>>fs[]>-
        (
        drule LENGTH_TAKE>>strip_tac>>
        irule find_index_APPEND1>>fs[]>>
        qexists_tac `DROP i mc_conf.ffi_names` >>
        fs[TAKE_DROP])>>
       fs[NOT_LESS_EQUAL,TAKE_LENGTH_TOO_LONG])

    \\ `EL (get_ffi_index mc_conf.ffi_names (ExtCall s)) mc_conf.ffi_names = (ExtCall s)` by (
      irule EL_get_ffi_index_MEM >> simp[]
    )
    \\ `(mc_conf.target.get_reg ms2 mc_conf.ptr_reg = t1.regs mc_conf.ptr_reg) /\
        (mc_conf.target.get_reg ms2 mc_conf.len_reg = t1.regs mc_conf.len_reg) /\
        (mc_conf.target.get_reg ms2 mc_conf.ptr2_reg = t1.regs mc_conf.ptr2_reg) /\
        (mc_conf.target.get_reg ms2 mc_conf.len2_reg = t1.regs mc_conf.len2_reg) /\
        !a. a IN mc_conf.prog_addresses ==>
            (mc_conf.target.get_byte ms2 a = t1.mem a)` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())
           [encoder_correct_def,target_ok_def,target_state_rel_def]
      \\ full_simp_tac(srw_ss())[encoder_correct_def |> REWRITE_RULE [GSYM reg_ok_def]]
      \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[state_rel_def,asm_def,
           jump_to_offset_def,asmSemTheory.upd_pc_def,AND_IMP_INTRO]
      \\ rpt strip_tac \\ first_x_assum match_mp_tac
      \\ full_simp_tac(srw_ss())[reg_ok_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[]
    \\ `(t1.regs mc_conf.ptr_reg = c') /\
        (t1.regs mc_conf.len_reg = c) /\
        (t1.regs mc_conf.ptr2_reg = c2') /\
        (t1.regs mc_conf.len2_reg = c2)` by
     (full_simp_tac(srw_ss())[state_rel_def]
      \\ Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (fn th =>
          MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).ptr_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).len_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).ptr2_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).len2_reg` th))
      \\ Q.PAT_X_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_X_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_X_ASSUM `xx = s1.ptr2_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_X_ASSUM `xx = s1.len2_reg` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_state_rel \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `call_FFI s1.ffi (ExtCall s) x x'`) THEN1
     ((* FFI_final *)
     FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ rpt strip_tac
     \\ fs[] \\ rveq \\ fs[]
     \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
     \\ once_rewrite_tac [targetSemTheory.evaluate_def]
     \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
     \\ simp[]
     \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
     \\ simp[]
     \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
     \\ simp[]
     \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
     \\ simp[]
     \\ PURE_TOP_CASE_TAC >- (fs[shift_interfer_def])
     \\ simp[]
     >> ‘EL x'' (shift_interfer l' mc_conf).ffi_names = ExtCall s’
       by gvs[shift_interfer_def]>>
     first_assum (fn h => simp[h])
     \\ rpt (PURE_TOP_CASE_TAC \\ simp[])>>
     TRY (fs[shift_interfer_def,read_ffi_bytearrays_def,read_ffi_bytearray_def]>>
          gvs[]>>NO_TAC)>>

     fs[shift_interfer_def]>>
     fs[state_rel_def]>>
     drule mmio_pcs_min_index_is_SOME>>
     strip_tac>>fs[]>>
     last_x_assum $ qspec_then ‘x''’ assume_tac>>fs[]>>
     Cases_on ‘x'' < i’>>fs[NOT_LESS]>>
     drule find_index_LESS_LENGTH>>strip_tac>>fs[]>>
     first_x_assum $ qspec_then ‘x''’ assume_tac>>gvs[])
    (* FFI_return *)
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac
         `call_FFI s1.ffi (ExtCall s) x x' = FFI_return new_ffi new_bytes`
    \\ FIRST_X_ASSUM (Q.SPECL_THEN [
         `shift_interfer l' mc_conf with
          ffi_interfer := shift_seq 1 mc_conf.ffi_interfer`,
         `code2`,`labs`,
         `t1 with <| pc := p + n2w (pos_val new_pc 0 (code2:'a sec list)) ;
                     mem := asm_write_bytearray c2' new_bytes t1.mem ;
                     regs := \a. get_reg_value (s1.io_regs 0 (ExtCall s) a) (t1.regs a) I |>`,
         `mc_conf.ffi_interfer 0 (get_ffi_index mc_conf.ffi_names (ExtCall s),new_bytes,ms2)`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (rpt strip_tac
      THEN1 (full_simp_tac(srw_ss())[encoder_correct_def,shift_interfer_def]
             \\ metis_tac [])
      \\ unabbrev_all_tac
      \\ imp_res_tac bytes_in_mem_asm_write_bytearray
      \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def,
             asm_def,jump_to_offset_def,
             asmSemTheory.upd_pc_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ full_simp_tac bool_ss [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ `interference_ok (shift_seq l' mc_conf.next_interfer)
            (mc_conf.target.proj t1.mem_domain)` by
               (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
                \\ NO_TAC) \\ full_simp_tac(srw_ss())[]
      \\ `p + n2w (pos_val new_pc 0 code2) = t1.regs s1.link_reg` by
       (Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (Q.SPEC_THEN `s1.link_reg`mp_tac)
        \\ full_simp_tac(srw_ss())[word_loc_val_def]
        \\ Cases_on `lab_lookup n1 n2 labs` \\ full_simp_tac(srw_ss())[]
        \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[]
        \\ res_tac \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ `w2n c2 = LENGTH new_bytes` by
       (imp_res_tac read_bytearray_LENGTH
        \\ imp_res_tac evaluatePropsTheory.call_FFI_LENGTH \\ full_simp_tac(srw_ss())[])
      \\ qmatch_goalsub_abbrev_tac`mc_conf.ffi_interfer _ (index,_,_)`
      \\ `index < i` by (
        imp_res_tac mmio_pcs_min_index_is_SOME>>gvs[]>>
        simp[get_ffi_index_def,backendPropsTheory.the_eqn] >>
       imp_res_tac find_index_MEM >>
        first_x_assum $ qspec_then `0` assume_tac >>fs[]>>
        Cases_on ‘i' < i’>>fs[NOT_LESS]>>
        first_x_assum $ qspec_then `i'` assume_tac >>gvs[]
      )
      \\ `index < LENGTH mc_conf.ffi_names` by (
        drule mmio_pcs_min_index_is_SOME >> gvs[]
        )
      \\ qunabbrev_tac`index`
      \\ conj_tac
      THEN1
       (rw [] \\
        qpat_x_assum `EL (get_ffi_index (TAKE i mc_conf.ffi_names) (ExtCall s)) mc_conf.ffi_names = ExtCall s` $ assume_tac o GSYM
        \\ first_assum (fn th => CONV_TAC(LAND_CONV(ONCE_REWRITE_CONV[th])))
        \\ first_x_assum match_mp_tac \\ simp []
        \\ pop_assum(SUBST_ALL_TAC o SYM)
        \\ `aligned mc_conf.target.config.code_alignment p` by fs [alignmentTheory.aligned_bitwise_and]
        \\ qpat_x_assum `_ = t1.regs s1.link_reg` (fn th => rewrite_tac [GSYM th])
        \\ simp [ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
        \\ drule all_enc_ok_aligned_pos_val \\ simp []
        \\ fs[read_ffi_bytearrays_def,read_ffi_bytearray_def]
        \\ disch_then (qspec_then`new_pc`mp_tac)
        \\ impl_tac >- metis_tac[has_odd_inst_alignment]
        \\ rw[]
        \\ imp_res_tac EL_get_ffi_index_MEM
        \\ simp[]
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ simp[]
        \\ irule ffi_name_NOT_Mapped
        \\ gvs[]
      )
      \\ conj_tac
      THEN1
       (full_simp_tac(srw_ss())[shift_seq_def,PULL_FORALL,AND_IMP_INTRO,
         read_ffi_bytearrays_def,read_ffi_bytearray_def]
        \\ rw[]
        \\ first_x_assum irule
        \\ rw[]
        \\ asm_exists_tac \\ simp[] \\ fs[]
        \\ simp[Once RTC_CASES1]
        \\ disj2_tac
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ simp[evaluatePropsTheory.call_FFI_rel_def]
        \\ goal_assum(first_assum o mp_then Any mp_tac))
      \\ conj_tac THEN1 metis_tac[]
      \\ conj_tac THEN1
       (Cases_on `s1.io_regs 0 (ExtCall s) r`
        \\ full_simp_tac(srw_ss())[get_reg_value_def,word_loc_val_def])
      \\ conj_tac THEN1
       (rpt strip_tac \\ qpat_x_assum `!a.
           byte_align a IN s1.mem_domain ==> bbb` (MP_TAC o Q.SPEC `a`)
        \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
        \\ match_mp_tac (SIMP_RULE std_ss [] (Q.INST [`x` |-> `x'`] CallFFI_bytearray_lemma))
        \\ full_simp_tac(srw_ss())[])
      \\ rw[]
      >- (
        match_mp_tac (MP_CANON (Q.INST [`x`|->`x'`] bytes_in_mem_asm_write_bytearray))
        \\ simp[] \\ fs[])
      >- (
        match_mp_tac (MP_CANON (Q.INST [`x`|->`x'`] bytes_in_mem_asm_write_bytearray))
        \\ simp[] \\ fs[])
      >- (
          fs[share_mem_state_rel_def] >>
          gvs[]>>
          rpt gen_tac>>strip_tac>>fs[]>>
          gvs[IMP_CONJ_THM,AND_IMP_INTRO,shift_seq_def] >>
          first_assum $ irule_at Any>>
          fs[]>>
          irule $ cj 2 RTC_RULES >>
          qexists `new_ffi` >>
          gvs[evaluatePropsTheory.call_FFI_rel_def] >>
          metis_tac[]
      )
      >- fs[share_mem_domain_code_rel_def]
    )
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock + k`mp_tac) \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ms2'`] \\ full_simp_tac(srw_ss())[]
    \\ fs[]
    \\ simp_tac std_ss [Once evaluate_def]
    \\ full_simp_tac(srw_ss())[shift_interfer_def]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,AC MULT_COMM MULT_ASSOC]
    \\ rev_full_simp_tac(srw_ss())[LET_DEF]
    \\ rewrite_tac[read_ffi_bytearrays_def, read_ffi_bytearray_def]
    \\ TOP_CASE_TAC>>fs[]
    \\ TRY (TOP_CASE_TAC>>fs[])
    \\ TRY (TOP_CASE_TAC>>fs[])
    >- (pairarg_tac>>fs[]>>
        irule EQ_TRANS>>
        first_x_assum $ irule_at (Pos last)>>
        simp[]>>
        fs[apply_oracle_def])>>
    qabbrev_tac ‘j = get_ffi_index ffi_names (ExtCall s)’>>
    fs[state_rel_def]>>
    drule mmio_pcs_min_index_is_SOME>>
    strip_tac>>fs[]>>
    last_x_assum $ qspec_then ‘j’ assume_tac>>fs[]>>
    Cases_on ‘j < i’>>fs[NOT_LESS]>>
    drule find_index_LESS_LENGTH>>strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘j’ assume_tac>>gvs[])
  THEN1 (* Install *)
    (say "Install" >>
    qpat_x_assum`_ =(res,s2)` mp_tac >>
    ntac 6 (TOP_CASE_TAC >> fs[])>>
    pairarg_tac \\ fs[] \\
    ntac 5 (TOP_CASE_TAC \\ fs[]) >>
    strip_tac >> rfs[]>>
    qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names` >>
    mp_tac IMP_bytes_in_memory_Install>>
    fs[]>>impl_tac>-
      fs[state_rel_def]>>
    strip_tac>>
    pop_assum mp_tac >>
    qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac>>
    (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]>>
    impl_tac>-
      (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def,asm_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      \\ gvs[enc_with_nop_thm,LENGTH_APPEND] )>>
    strip_tac
    \\ `mc_conf.target.get_pc ms2 = mc_conf.ccache_pc` by
     (
      fs[Abbr`jj`,asm_def]>>
      fs[encoder_correct_def,target_ok_def,target_state_rel_def]>>
      fs[jump_to_offset_def,state_rel_def]>>
      metis_tac[GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
           WORD_ADD_SUB])
    \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by
      (fs[state_rel_def]>>rfs[])
    \\ `(t1.regs mc_conf.ptr_reg = c') /\
        (t1.regs mc_conf.len_reg = c'')` by
      (fs[state_rel_def]>>
      Q.PAT_X_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (fn th =>
          MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).ptr_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).len_reg` th))
      \\ Q.PAT_X_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_X_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[word_loc_val_def])
    \\ rfs[]
    \\ qmatch_asmsub_abbrev_tac`evaluate mc_conf2 s1.ffi _ ms2`
    \\ qmatch_assum_rename_tac`s1.compile cfg _ = SOME (bytes,new_cfg)`
    \\ fs[asm_def,Abbr`jj`,jump_to_offset_def,upd_pc_def,FORALL_AND_THM]
    \\ `target_state_rel mc_conf.target
        (t1 with  <| regs := (s1.ptr_reg =+ t1.regs s1.ptr_reg)
                              (λa. get_reg_value (s1.cc_regs 0 a) (t1.regs a) I);
                      pc := t1.regs s1.link_reg |>)
        (mc_conf.ccache_interfer 0 (t1.regs s1.ptr_reg, t1.regs s1.len_reg, ms2))`
    by (
      fs[state_rel_def]
      \\ first_x_assum match_mp_tac
      \\ conj_tac THEN1
       (qmatch_abbrev_tac`_ _ t11 _`
        \\ qmatch_assum_abbrev_tac`_ _ t12 _`
        \\ `t11 = t12` by (
          simp[Abbr`t11`,Abbr`t12`,asmSemTheory.asm_state_component_equality]
          \\ simp[GSYM WORD_LITERAL_ADD]
          \\ qpat_x_assum`_ = mc_conf.ccache_pc`(kall_tac)
          \\ qpat_x_assum`_ = mc_conf.ccache_pc`(mp_tac o SYM)
          \\ rw[]
          \\ qmatch_abbrev_tac`p + b = p + e + b + -e`>>
          `p+e+b = p+b+e` by
            simp[]>>
          simp[])
        \\ rw[] )
      \\ qpat_x_assum `∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)`
            (qspec_then `s1.link_reg` mp_tac) \\ simp [] \\ strip_tac
      \\ rename [`word_loc_val p labs (Loc l1 l2) = SOME (t1.regs r1)`]
      \\ full_simp_tac(srw_ss())[word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (qspecl_then [`l1`,`l2`] mp_tac) \\ fs [] \\ rw []
      \\ `aligned mc_conf.target.config.code_alignment p` by
             fs [alignmentTheory.aligned_bitwise_and]
      \\ qpat_x_assum `_ = t1.regs r1` (fn th => rewrite_tac [GSYM th])
      \\ simp [ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
      \\ drule all_enc_ok_aligned_pos_val \\ simp []
      \\ disch_then match_mp_tac \\ fs []
      \\ metis_tac[has_odd_inst_alignment])
    \\ qmatch_assum_abbrev_tac`target_state_rel _ t2 ms12`
    \\ qpat_assum`s1.compile _ _ = _`mp_tac
    \\ `s1.compile = compile_lab` by fs[state_rel_def]
    \\ pop_assum SUBST1_TAC
    \\ simp[compile_lab_def]
    \\ pairarg_tac \\ simp[]
    \\ qmatch_assum_abbrev_tac`s1.compile cfg new_code = _`
    \\ TOP_CASE_TAC
    \\ split_pair_case_tac \\ fs[]
    \\ strip_tac
    \\ first_x_assum(qspecl_then
        [`mc_conf2 with ccache_interfer := shift_seq 1 mc_conf.ccache_interfer`,
         `code2 ++ sec_list`,
         `new_cfg.labels`,`t2`,`ms12`]mp_tac)
    \\ impl_tac
    >- (
       fs[Abbr`mc_conf2`,shift_interfer_def,ELIM_UNCURRY]
       \\ pop_assum $ assume_tac o GSYM
       \\ fs[state_rel_def,Abbr`t2`,Abbr`ms12`]
       \\ reverse $ rfs[no_install_or_no_share_mem_def]
       >- (
         fs[no_install_def,asm_fetch_def] >>
         drule code_similar_IMP_asm_fetch_aux_line_similar >>
         disch_then $ qspec_then `s1.pc` assume_tac >>
         gvs[DefnBase.one_line_ify NONE line_similar_def,OPTREL_def] >>
         pop_assum mp_tac >>
         TOP_CASE_TAC >>
         strip_tac >>
         gvs[]) >>
       qpat_assum `_ ==> !k. _ (s1.compile_oracle k)`
         (drule_then $ qspec_then`0` mp_tac)>>
       qpat_assum`s1.compile_oracle 0 = _` SUBST1_TAC>>
       SIMP_TAC (srw_ss()) [] >>
       strip_tac>>
       drule remove_labels_thm >> impl_tac>-
         (fs[good_code_def]>>
         rw[]>>fs[]>>
         Cases_on`lab_lookup l1' l2 cfg.labels`>>
         fs[]>>
         metis_tac[])>>
      strip_tac >>
      fs[]>>rfs[] >>
      drule_all code_similar_IMP_both_no_share_mem >>
      strip_tac >>
      `no_share_mem_inst (code2 ++ sec_list)` by (
        irule no_share_mem_APPEND >>
        simp[]) >>
      simp[] >>
      `~(no_install (code2 ++ sec_list))` by (
        irule $ SRULE[Once $ DECIDE ``(B ==> A) <=> (~A ==> ~B)``] $
          cj 1 no_install_APPEND_IMP >>
        simp[no_install_def] >>
        rev_drule code_similar_IMP_asm_fetch_aux_line_similar >>
        disch_then $ qspec_then `s1.pc` (assume_tac o
          SRULE[DefnBase.one_line_ify NONE OPTREL_def,
            DefnBase.one_line_ify NONE line_similar_def]) >>
        gvs[asm_fetch_def] >>
        pop_assum mp_tac >>
        TOP_CASE_TAC >>
        strip_tac >>
        var_eq_tac >>
        metis_tac[])
      \\ conj_tac >- (
        fs[read_ffi_bytearrays_def, read_ffi_bytearray_def, shift_seq_def]
        \\ rw[] \\ first_x_assum irule
        \\ rw[] \\ asm_exists_tac \\ rw[]
        \\ fs[])
      \\ conj_tac >- fs[shift_seq_def]
      \\ conj_tac
      >- (
        fs[shift_seq_def]
        \\ rw[]
        \\ pairarg_tac \\ fs[]
        \\ conj_tac
        >- (
          rpt(first_x_assum(qspec_then`k+1`mp_tac))
          \\ simp[] ) \\
        conj_tac
        >- (
          rpt(first_x_assum(qspec_then`k+1`mp_tac))
          \\ simp[] ) \\
        strip_tac \\
        rpt(first_x_assum(qspec_then`0` assume_tac))>>
        rfs[]>>
        fs[]>>
        simp[prog_to_bytes_MAP,no_share_mem_IMP_get_shmem_info]
      )
      \\ conj_tac >- (
        rw[]>>
        metis_tac[])
      \\ conj_tac >-(
        fs[find_ffi_names_append,list_subset_def]>>
        fs[EVERY_FILTER,EVERY_MEM])
      \\ conj_tac >- (
        fs[prog_to_bytes_APPEND,EVEN_ADD]>>
        metis_tac[all_enc_ok_prog_to_bytes_EVEN])
      \\ conj_tac >- ( fs[interference_ok_def,shift_seq_def] )
      \\ conj_asm2_tac >- (
        `EVERY sec_labels_ok (s1.code++new_code)` by
          (fs[good_code_def]>>
          metis_tac[code_similar_sym,code_similar_sec_labels_ok])>>
        `EVERY sec_label_zero sec_list` by
          metis_tac[all_enc_ok_imp_sec_label_zero]>>
        simp[loc_to_pc_append]>>
        ntac 3 strip_tac>>
        reverse (TOP_CASE_TAC >> fs[])
        >-
          (rw[]>> first_x_assum drule>>
          strip_tac>>
          first_x_assum drule>>
          simp[pos_val_append]>>
          rw[]>>
          metis_tac[code_similar_loc_to_pc,loc_to_pc_bound])
        >>
          TOP_CASE_TAC>>fs[]>>
          first_x_assum drule>>rw[]>>
          simp[pos_val_append]>>
          rw[]
          >-
            (imp_res_tac code_similar_len_no_lab>>
            fs[]>>
            `x''=0` by fs[]>>
            simp[]>>
            simp[pos_val_acc]>>
            imp_res_tac pos_val_0>>
            simp[]>>
            metis_tac[LENGTH_prog_to_bytes2])
          >>
            imp_res_tac code_similar_len_no_lab>>
            simp[]>>
            metis_tac[LENGTH_prog_to_bytes2])
      \\ conj_tac >- (
        rw[]
        \\ reverse(rw[APPLY_UPDATE_THM])
        \\ rfs[]
        >- (
          qmatch_goalsub_rename_tac`s1.cc_regs 0 reg`
          \\ Cases_on`s1.cc_regs 0 reg`
          >- (
            simp[get_reg_value_def]
            \\ first_assum(qspec_then`reg`(CHANGED_TAC o SUBST1_TAC o SYM))
            \\ Cases_on`read_reg reg s1` \\ simp[word_loc_val_def]
            \\ match_mp_tac EQ_SYM
            \\ TOP_CASE_TAC
            >- (
              rpt(first_x_assum(qspec_then`reg`mp_tac))
              \\ simp[word_loc_val_def] )
            \\ first_x_assum drule
            \\ simp[])
          \\ simp[get_reg_value_def]
          \\ simp[word_loc_val_def] )
        \\ simp[word_loc_val_def]
        \\ fs[Abbr`new_code`]
        \\ first_x_assum (qspecl_then [`n''`,`0`,`0`] mp_tac)
        \\ simp[Once loc_to_pc_def]
        \\ imp_res_tac pos_val_0
        \\ rw[]
        \\ qhdtm_x_assum`buffer_flush`mp_tac
        \\ simp[buffer_flush_def]
        \\ strip_tac
        \\ rfs[])
      \\ conj_tac >- (
        rw[]
        \\ res_tac
        \\ fs[word_loc_val_byte_def]
        \\ ntac 2 (pop_assum mp_tac)
        \\ TOP_CASE_TAC \\ simp[]
        \\ strip_tac
        \\ qmatch_asmsub_abbrev_tac`word_loc_val p labs w = _`
        \\ Cases_on`w` \\ fs[word_loc_val_def]
        \\ ntac 4 (pop_assum mp_tac)
        \\ TOP_CASE_TAC \\ simp[]
        \\ ntac 4 strip_tac
        \\ first_x_assum drule \\ simp[])
      \\ conj_tac >- (
        strip_tac \\
        qhdtm_x_assum`buffer_flush`mp_tac \\
        simp[buffer_flush_def] \\ ntac 2 strip_tac \\
        qpat_x_assum `∀n. n < _ ⇒ _`(qspec_then`n'''` mp_tac)>>
        rw[]>>rfs[] >> fs[GSYM word_add_n2w])
      \\ conj_tac >- (
        simp[prog_to_bytes_APPEND]
        \\ fs[bytes_in_mem_APPEND]
        \\ qhdtm_x_assum`buffer_flush`mp_tac
        \\ simp[buffer_flush_def]
        \\ rw[]
        \\ fs[])
      \\ conj_tac >- (
        simp[prog_to_bytes_APPEND]
        \\ fs[buffer_flush_def] \\ rw[]
        \\ qpat_x_assum`_ = t1.regs s1.len_reg` sym_sub_tac
        \\ simp[GSYM word_add_n2w])
      \\ conj_tac >- (
        fs[buffer_flush_def]>>rw[]>>
        simp[bytes_in_mem_def])
      \\ conj_tac >-
        (fs[buffer_flush_def] \\ rw[] >>
        fs[LENGTH_prog_to_bytes2,prog_to_bytes_APPEND])
      \\ conj_tac >- (
         gvs[buffer_flush_def] >>
         rw[] >>
         qpat_x_assum `!bn. bn < _ + _ ==> ~(MEM _ _)` $
           qspec_then `bn + LENGTH (prog_to_bytes sec_list)` mp_tac >>
         gvs[GSYM word_add_n2w] >>
         metis_tac[WORD_ADD_ASSOC]
      )
      \\ conj_tac>- (
        `EVERY sec_label_zero sec_list` by
          metis_tac[all_enc_ok_imp_sec_label_zero]>>
        qmatch_assum_rename_tac `loc_to_pc ll1 ll2 s1.code = SOME xx`>>
        rfs[]>>fs[]>>
        `pos_val xx 0 (code2 ++ sec_list) = pos_val xx 0 code2` by
          (simp[pos_val_append]>>
          metis_tac[loc_to_pc_bound,code_similar_sec_labels_ok,code_similar_loc_to_pc])>>
        simp[]>>
        last_x_assum(qspecl_then[`ll1`,`ll2`,`xx`] assume_tac)>>
        last_x_assum(qspecl_then[`ll1`,`ll2`,`xx`] assume_tac)>>
        rfs[]>>
        fs[]>>
        qpat_x_assum`!r. word_loc_val _ _ _ = _` (qspec_then`s1.link_reg` assume_tac)>>
        rfs[word_loc_val_def])
      \\ conj_tac>-
        (match_mp_tac all_enc_ok_append>>
        rw[]>>fs[]>>
        match_mp_tac all_enc_ok_labs_mono
        >- metis_tac[] >>
        (* TODO: remove qexists `l1` *)
        (* irule (Pos hd) $ DECIDE``A ==> A`` *)
        qexists `l1` >>
        gvs[asm_fetch_def] >>
        rev_drule code_similar_IMP_asm_fetch_aux_line_similar >>
        simp[OPTREL_def,DefnBase.one_line_ify NONE line_similar_def,AllCaseEqs()] >>
        disch_then $ qspec_then `s1.pc` assume_tac >>
        gvs[] >>
        first_x_assum mp_tac >>
        TOP_CASE_TAC >>
        strip_tac >>
        var_eq_tac >>
        drule $ GEN_ALL no_share_mem_lemma >>
        rpt strip_tac >>
        gvs[Abbr`ffi_names`] >>
        pop_assum drule >>
        impl_tac >-
        simp[no_install_or_no_share_mem_def] >>
        metis_tac[TAKE_LENGTH_ID] )
      \\ conj_tac>-
        (fs[good_code_def]>>
        metis_tac[code_similar_sec_labels_ok])
      \\ conj_tac >- metis_tac[code_similar_append]
      \\ conj_tac >-
        (gvs[share_mem_state_rel_def] >>
         share_mem_state_rel_tac)
      \\ gvs[share_mem_domain_code_rel_def] >>
         conj_tac >- gvs[no_share_mem_inst_def] >>
         rw[IN_DISJOINT] >>
         spose_not_then assume_tac >>
         gvs[asm_fetch_def] >>
         Cases_on `pc < num_pcs code2`
         >- (
           gvs[asm_fetch_aux_APPEND1,pos_val_APPEND1] >>
           first_x_assum drule_all >>
           gvs[IN_DISJOINT] >>
           metis_tac[]
         ) >>
         `?pc'. pc = num_pcs code2 + pc'` by (
           irule LESS_EQUAL_ADD >>
           decide_tac
         ) >>
         gvs[asm_fetch_aux_APPEND2] >>
         rev_drule_then (qspecl_then [`sec_list`,`pc'`] assume_tac)
           pos_val_APPEND2 >>
         gvs[] >>
         pop_assum kall_tac >>
         drule_then drule $ GEN_ALL no_share_mem_lemma >>
         impl_tac >- (
           irule code_similar_IMP_both_no_install_or_no_share_mem >>
           irule_at (Pos hd) code_similar_sym >>
           first_x_assum $ irule_at (Pos hd) >>
           simp[no_install_or_no_share_mem_def]) >>
         strip_tac >>
         gvs[buffer_flush_def] >>
         drule_all $ GEN_ALL asm_fetch_aux_pos_val_SUC >>
         disch_then $ qspec_then `0` assume_tac >>
         drule_then (qspecl_then [`pc'+1`,`0`] (assume_tac o SIMP_RULE(srw_ss())[]))
           pos_val_bound >>
         qpat_x_assum `!bn. bn < _ + _ ==> ~(MEM _ _)` mp_tac >>
         simp[] >>
         qexists `a + pos_val pc' 0 sec_list` >>
         simp[GSYM word_add_n2w] >>
         metis_tac[word_add_n2w,WORD_ADD_ASSOC,WORD_ADD_COMM]
    )
    \\ disch_then(qx_choose_then`k`strip_assume_tac)
    \\ first_x_assum(qspec_then`s1.clock+k`assume_tac)
    \\ qmatch_asmsub_rename_tac`s1.clock + k + k0`
    \\ qexists_tac`k + k0` \\ fs[]
    \\ simp[Abbr`mc_conf2`,Abbr`ms12`]
    \\ simp[Once evaluate_def]
    \\ fs[shift_interfer_def]
    \\ IF_CASES_TAC >- fs[state_rel_def]
    \\ IF_CASES_TAC >- (
      fs[state_rel_def]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ rfs[good_dimindex_def,ffi_offset_def]
      \\ rpt(qpat_x_assum`_ = _.halt_pc`(mp_tac o SYM))
      \\ simp[]
      \\ EVAL_TAC
      \\ simp[dimword_def] )
    \\ rfs[apply_oracle_def,target_state_rel_def,state_rel_def,reg_ok_def])
  THEN1 (* Halt *)
   (say "Halt"
    \\ srw_tac[][]
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l1 l2 l3)`
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l bytes n)`
    \\ qabbrev_tac `ffi_names = TAKE (THE (mmio_pcs_min_index mc_conf.ffi_names)) mc_conf.ffi_names`
    \\ mp_tac IMP_bytes_in_memory_Halt \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP2 \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def,asm_def]
      \\ fs[asm_fetch_def]
      \\ drule_all $ GEN_ALL IMP_bytes_in_memory
      \\ strip_tac
      \\ fs[]
      \\ drule_all $ GEN_ALL IMP_ffi_entry_pcs_disjoint_LabAsm
      \\ ho_match_mp_tac (
        PURE_REWRITE_RULE [satTheory.AND_IMP] o
        PURE_REWRITE_RULE [Once CONJ_SYM] $
        GEN_ALL ffi_entry_pcs_disjoint_LENGTH_shorter )
      \\ Cases_on `j`
      \\ gvs[line_similar_def,line_ok_def,line_length_def,line_bytes_def]
      \\ gvs[enc_with_nop_thm,LENGTH_APPEND]
    )
    \\ rpt strip_tac
    \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[asm_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ srw_tac[][]
    \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[]
    \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[shift_interfer_def]
    \\ `mc_conf.target.get_pc ms2 = mc_conf.halt_pc` by
     (full_simp_tac(srw_ss())
        [encoder_correct_def,target_ok_def,target_state_rel_def]
      \\ res_tac
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ full_simp_tac(srw_ss())[state_rel_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
           WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[])
    \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by
            full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[state_rel_def,jump_to_offset_def,
          asmSemTheory.upd_pc_def]
    \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
    \\ `word_loc_val p labs (s1.regs s1.ptr_reg) =
         SOME (t1.regs s1.ptr_reg)` by full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.ptr_reg`
    \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
    \\ `s1 = s2` by (Cases_on `t1.regs s1.ptr_reg = 0w`
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]) \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())
         [encoder_correct_def,target_ok_def,target_state_rel_def]
    \\ first_x_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ first_x_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ full_simp_tac(srw_ss())[reg_ok_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
QED


(* relating observable semantics *)

Definition init_ok_def:
  init_ok (mc_conf, p) s ms <=>
    ?code2 labs t1.
      state_rel (mc_conf,code2,labs,p) s t1 ms
End

Theorem machine_sem_EQ_sem:
   !mc_conf p (ms:'state) ^s1.
     encoder_correct mc_conf.target /\
     init_ok (mc_conf,p) s1 ms /\ semantics s1 <> Fail ==>
     machine_sem mc_conf s1.ffi ms = { semantics s1 }
Proof
  simp[GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac(srw_ss())[init_ok_def] >>
  simp[semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >>
  conj_tac
  >- (
    qx_gen_tac`ffi`>>strip_tac>> full_simp_tac(srw_ss())[]
    \\ drule compile_correct \\ full_simp_tac(srw_ss())[]
    \\ disch_then drule
    \\ imp_res_tac state_rel_clock
    \\ pop_assum (qspec_then `k` assume_tac)
    \\ disch_then drule \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[machine_sem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
    \\ Cases \\ full_simp_tac(srw_ss())[machine_sem_def]
    THEN1 (disj1_tac \\ qexists_tac `k+k'` \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
    THEN1
     (eq_tac THEN1
       (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ drule (GEN_ALL evaluate_ignore_clocks) \\ full_simp_tac(srw_ss())[]
        \\ pop_assum (K all_tac)
        \\ disch_then drule \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
    \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
    \\ PairCases_on `y`
    \\ drule (GEN_ALL evaluate_ignore_clocks) \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ pop_assum (K all_tac)
    \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[machine_sem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
  \\ strip_tac
  \\ Cases \\ full_simp_tac(srw_ss())[machine_sem_def]
  \\ imp_res_tac state_rel_clock
  THEN1 (
    qmatch_abbrev_tac`a ∧ b ⇔ c` >>
    `a` by (
      unabbrev_all_tac >> gen_tac >>
      qspec_then `s1 with clock := k` mp_tac compile_correct >>
      Cases_on`evaluate (s1 with clock := k)`>>simp[]>>
      last_assum(qspec_then`k`mp_tac)>>
      pop_assum mp_tac >> simp_tac(srw_ss())[] >>
      ntac 2 strip_tac >>
      disch_then drule >>
      first_x_assum(qspec_then`k`strip_assume_tac) >>
      disch_then drule >> strip_tac >>
      first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>
      `∃x y z. evaluate mc_conf s1.ffi k ms = (x,y,z)` by metis_tac[PAIR] >>
      `x = TimeOut` by (
        spose_not_then strip_assume_tac >>
        drule (GEN_ALL evaluate_add_clock) >>
        simp[] >> qexists_tac`k'`>>simp[] ) >>
      full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_add_clock_io_events_mono,SND,option_CASES,
                IS_SOME_EXISTS,LESS_EQ_EXISTS]) >>
    simp[] >> full_simp_tac(srw_ss())[Abbr`a`] >>
    unabbrev_all_tac >> simp[] >>
    qmatch_abbrev_tac`lprefix_lub l1 l ⇔ l = build_lprefix_lub l2` >>
    `lprefix_chain l1 ∧ lprefix_chain l2` by (
      unabbrev_all_tac >>
      conj_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      metis_tac[
        targetPropsTheory.evaluate_add_clock_io_events_mono,
        labPropsTheory.evaluate_add_clock_io_events_mono
        |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
        LESS_EQ_EXISTS]) >>
    `equiv_lprefix_chain l1 l2` by (
      simp[equiv_lprefix_chain_thm] >>
      unabbrev_all_tac >> simp[PULL_EXISTS] >>
      ntac 2 (pop_assum kall_tac) >>
      simp[LNTH_fromList,PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM] >>
      rpt gen_tac >>
      qspec_then `s1 with clock := k` mp_tac compile_correct >>
      Cases_on`evaluate (s1 with clock := k)`>>full_simp_tac(srw_ss())[] >>
      last_assum(qspec_then`k`mp_tac)>>
      pop_assum mp_tac >> simp_tac(srw_ss())[] >>
      ntac 2 strip_tac >>
      disch_then drule >>
      first_x_assum(qspec_then`k`(fn th => assume_tac th >> disch_then drule)) >>
      strip_tac >>
      reverse conj_tac >> strip_tac >- (
        qexists_tac`k+k'`>>simp[] ) >>
      qmatch_assum_abbrev_tac`n < (LENGTH (_ ffi))` >>
      qexists_tac`k`>>simp[] >>
      `ffi.io_events ≼ r.ffi.io_events` by (
        qunabbrev_tac`ffi` >>
        metis_tac[
          targetPropsTheory.evaluate_add_clock_io_events_mono,
          SND,LESS_EQ_EXISTS] ) >>
      full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
      simp[EL_APPEND1]) >>
    metis_tac[build_lprefix_lub_thm,unique_lprefix_lub,lprefix_lub_new_chain])
  THEN1 (
    spose_not_then strip_assume_tac >> var_eq_tac >>
    qspec_then `s1 with clock := k` mp_tac compile_correct >>
    Cases_on`evaluate (s1 with clock := k)`>>simp[]>>
    last_assum(qspec_then`k`mp_tac)>>
    pop_assum mp_tac >> simp_tac(srw_ss())[] >> rpt strip_tac >>
    asm_exists_tac >> simp[] >>
    first_x_assum(qspec_then`k`strip_assume_tac) >>
    asm_exists_tac >> simp[] >>
    rpt gen_tac >>
    drule (GEN_ALL evaluate_add_clock) >> simp[] >>
    disch_then kall_tac >>
    first_x_assum(qspec_then`k`mp_tac) >> simp[])
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
  \\ last_x_assum (qspec_then `k` mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (s1 with clock := k)` \\ full_simp_tac(srw_ss())[]
  \\ drule compile_correct
  \\ Cases_on `q = Error` \\ full_simp_tac(srw_ss())[]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (qspec_then `k` assume_tac)
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[] \\ gen_tac
  \\ PairCases_on `y`
  \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
QED

(*
val () = PolyML.SaveState.saveState "lab_to_target_syntactic";
val () = PolyML.SaveState.loadState "lab_to_target_syntactic";
*)

(* introducing make_init *)

Definition set_bytes_def:
  (set_bytes a be [] = 0w) /\
  (set_bytes a be (b::bs) = set_byte a b (set_bytes (a+1w) be bs) be)
End

Definition make_word_def:
  make_word be m (a:'a word) =
    if dimindex (:'a) = 32 then
      Word (set_bytes a be [m a; m (a+1w); m (a+2w); m (a+3w)])
    else
      Word (set_bytes a be [m a; m (a+1w); m (a+2w); m (a+3w);
                            m (a+4w); m (a+5w); m (a+6w); m (a+7w)])
End

Definition make_init_def:
  make_init mc_conf (ffi:'ffi ffi_state) io_regs cc_regs t m dm sdm (ms:'state) code
    comp cbpos cbspace coracle =
    <| regs           := \k. Word ((t.regs k):'a word)
     ; fp_regs    := t.fp_regs
     ; mem            := m
     ; mem_domain     := dm
     ; shared_mem_domain := sdm
     ; pc             := 0
     ; be             := mc_conf.target.config.big_endian
     ; ffi            := ffi
     ; io_regs        := \n i k. if MEM k mc_conf.callee_saved_regs then NONE else (io_regs n i k)
     ; cc_regs        := \n k. if MEM k mc_conf.callee_saved_regs then NONE else (cc_regs n k)
     ; code           := code
     ; clock          := 0
     ; failed         := F
     ; ptr_reg        := mc_conf.ptr_reg
     ; len_reg        := mc_conf.len_reg
     ; ptr2_reg       := mc_conf.ptr2_reg
     ; len2_reg       := mc_conf.len2_reg
     ; link_reg       := case mc_conf.target.config.link_reg of SOME n => n | _ => 0
     ; compile        := comp
     (* Initialize with code buffer empty *)
     ; code_buffer    := <|position:=cbpos; buffer:=[] ; space_left:=cbspace|>
     ; compile_oracle := coracle
     |>
End

val IMP_LEMMA = METIS_PROVE [] ``(a ==> b) ==> (b ==> c) ==> (a ==> c)``

Definition compiler_oracle_ok_def:
  compiler_oracle_ok coracle init_labs init_pos c ffis ⇔
    (* Assumptions about initial compile oracle *)
    (∀k:num. let (cfg,code) = coracle k in good_code c cfg.labels code /\
      no_share_mem_inst code) ∧
    (let (cfg,code) = coracle 0 in
        cfg.labels = init_labs ∧
        cfg.pos = init_pos ∧
        cfg.asm_conf = c ∧
        cfg.ffi_names = SOME ffis)
End

(* mc_conf_ok: conditions on the machine configuration
   which will be discharged for the particular configuration of each target
*)
Definition mc_conf_ok_def:
  mc_conf_ok (mc_conf:('a,'b,'c) machine_config) ⇔
    good_dimindex(:'a) ∧
    encoder_correct mc_conf.target ∧
    reg_ok mc_conf.ptr_reg mc_conf.target.config /\
    reg_ok mc_conf.len_reg mc_conf.target.config /\
    reg_ok mc_conf.ptr2_reg mc_conf.target.config /\
    reg_ok mc_conf.len2_reg mc_conf.target.config /\
    reg_ok (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n)
      mc_conf.target.config ∧
    enc_ok mc_conf.target.config
End

Theorem get_shmem_info_APPEND:
!secs pos ffi_names shmem_info ffis1 ffis2 info1 info2 new_ffi_names new_shmem_info.
  get_shmem_info secs pos ffi_names (shmem_info: 'a shmem_info) =
    (new_ffi_names,new_shmem_info) /\
  ffi_names = ffis1 ++ ffis2 /\
  shmem_info = info1 ++ info2 ==>
  new_ffi_names = ffis1 ++ (FST $ get_shmem_info secs pos ffis2 info2) /\
  new_shmem_info = info1 ++ (SND $ get_shmem_info secs pos ffis2 info2)
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  Cases_on `m` >>
  fs[get_memop_info_def,get_shmem_info_def]
QED

Theorem get_shmem_info_PREPEND:
  get_shmem_info secs pos ffi_names (shmem_info: 'a shmem_info) =
    (new_ffi_names,new_shmem_info) ==>
  new_ffi_names = ffi_names ++ (FST $ get_shmem_info secs pos [] []) /\
  new_shmem_info = shmem_info ++ (SND $ get_shmem_info secs pos [] [])
Proof
  strip_tac >>
  irule get_shmem_info_APPEND >>
  fs[]
QED

Definition line_to_info_def:
  line_to_info (secs: 'a sec list) p x = case SND x of
    SOME (Asm (ShareMem m r ad) bytes l) =>
      let (name,nb) = get_memop_info m in
      [(SharedMem name,
       <|entry_pc := n2w (pos_val (FST x) p secs)
        ;nbytes:=nb
        ;access_addr:=ad
        ;reg:=r
        ;exit_pc:=n2w (pos_val (FST x) p secs + LENGTH bytes)|>
        )]
    | _ => []
End

Theorem line_to_info_next:
  line_to_info (Section k1 (LabAsm a b bytes1 len1::xs1)::rest1) p1 (i1+1,l1)
    = line_to_info ((Section k1 xs1)::rest1) (p1 + LENGTH bytes1) (i1,l1) /\
  line_to_info (Section k2 (Asm c2 bytes2 len2::xs2)::rest2) p2 (i2+1,l2)
    = line_to_info ((Section k2 xs2)::rest2) (p2 + LENGTH bytes2) (i2,l2)
Proof
  rw[line_to_info_def] >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  Cases_on `m` >>
  gvs[get_memop_info_def,pos_val_def,line_length_def]
QED

Theorem line_to_info_hd_empty:
  line_to_info (Section k []::rest) p t =
    line_to_info rest p t
Proof
  gvs[line_to_info_def] >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  gvs[pos_val_def]
QED

Theorem line_to_info_hd_Label:
  line_to_info (Section k ((Label a b 0)::xs)::rest)
    p t
    = line_to_info (Section k xs::rest) p t
Proof
  gvs[line_to_info_def] >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  TOP_CASE_TAC >>
  Cases_on `m` >>
  gvs[pos_val_def,line_length_def,get_memop_info_def]
QED

Theorem get_shmem_info_thm:
  !secs p ffi_names shmem_info p'.
  all_enc_ok c labs ffis p' secs ==>
  get_shmem_info secs p ffi_names shmem_info =
    let (new_ffis, new_info) =
      UNZIP $ FLAT $
      MAP (line_to_info secs p) $
      GENLIST (\i. (i, asm_fetch_aux i secs)) $
      num_pcs secs
    in (ffi_names ++ new_ffis, shmem_info ++ new_info)
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac
  >- (
    gvs[get_shmem_info_def,pos_val_def,
      asm_fetch_aux_def] >>
    gvs[GENLIST,line_to_info_def,num_pcs_def]
  )
  >- (
    gvs[get_shmem_info_def,pos_val_def,
      asm_fetch_aux_def,num_pcs_def,all_enc_ok_def] >>
    metis_tac[line_to_info_hd_empty]
  )
  >- (
    gvs[get_shmem_info_def,pos_val_def,
      asm_fetch_aux_def,num_pcs_def,all_enc_ok_def,line_length_def,line_ok_def] >>
    metis_tac[line_to_info_hd_Label]
  )
  >- (
    `~is_Label (Asm(ShareMem m r ad) bytes shmem_info)`
      by simp[is_Label_def] >>
    gvs[num_pcs_def,combinTheory.o_DEF,
      GENLIST_asm_fetch_aux_next] >>
    gvs[MAP_GENLIST,combinTheory.o_DEF] >>
    gvs[asm_fetch_aux_def,line_to_info_def] >>
    gvs[pos_val_def,line_length_def] >>
    gvs[all_enc_ok_def,line_ok_def,line_length_def] >>
    gvs[get_shmem_info_def] >>
    pairarg_tac >>
    gvs[UNZIP_MAP] >>
    last_x_assum $ qspec_then `p' + LENGTH bytes` mp_tac >>
    gvs[]
  ) >>
  gvs[all_enc_ok_def,line_ok_def,line_length_def] >>
  gvs[get_shmem_info_def,num_pcs_def] >>
  gvs[GENLIST_asm_fetch_aux_next] >>
  gvs[MAP_GENLIST,line_to_info_next,combinTheory.o_DEF,line_to_info_def] >>
  last_x_assum $ qspec_then `p' + LENGTH bytes` mp_tac >>
  gvs[]
QED

Triviality FILTER_NOT_MEM_Mapped:
  ~MEM "MappedRead" (FILTER (\x. x <> "MappedRead" /\ x <> "MappedWrite") l) /\
  ~MEM "MappedWrite" (FILTER (\x. x <> "MappedRead" /\ x <> "MappedWrite") l)
Proof
  gvs[MEM_FILTER]
QED

Theorem mmio_pcs_min_index_APPEND_thm:
  EVERY (λx. ∀s. x ≠ ExtCall s) l ∧
  EVERY (λx. ∃s. x = ExtCall s) ffis ⇒
  mmio_pcs_min_index (ffis ++ l) = SOME $ LENGTH ffis
Proof
  rpt strip_tac >>
  fs[mmio_pcs_min_index_def] >>
  gvs[some_def,Sh_not_Ext] >>
  SELECT_ELIM_TAC >>
  rw[]
  >~ [ `x = LENGTH _`]
  >- (
    spose_not_then assume_tac >>
    Cases_on `x < LENGTH ffis` >>
    gvs[EL_APPEND_EQN,EVERY_EL]
    >- (
    first_x_assum $ qspec_then `x`assume_tac >>gvs[]>>res_tac>>metis_tac[]
    ) >>
    imp_res_tac LESS_CASES_IMP>>
    qpat_x_assum ‘∀j. j < x => _’ $ qspec_then `LENGTH ffis` assume_tac >>
    gvs[]>>
    last_x_assum $ qspec_then `0` assume_tac >>
    gvs[EL]
  ) >>
    qexists_tac `LENGTH ffis` >>
    gvs[EL_APPEND_EQN,EVERY_EL,MEM_EL,EL_MEM]
QED

Theorem MEM_get_shmem_info:
  all_enc_ok c labs ffis p' (code2: 'a sec list) /\
  asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst' len) /\
  get_memop_info op = (q,r:word8) ==>
  MEM
    (SharedMem q,
    <|entry_pc:=n2w (pos_val pc p code2)
      ;nbytes:=r
      ;access_addr:=a
      ;reg:=re
      ;exit_pc:=n2w (pos_val pc (p+LENGTH inst') code2)|>)
    (ZIP (get_shmem_info code2 p [] []))
Proof
  rw[] >>
  drule $ get_shmem_info_thm >>
  disch_then $ qspecl_then [`p`,`[]`,`[]`] assume_tac >>
  gvs[UNZIP_MAP,MAP_GENLIST,combinTheory.o_DEF,ZIP_MAP_FST_SND_EQ] >>
  rw[MEM_FLAT,MEM_GENLIST,line_to_info_def] >>
  irule_at (Pos last) $ METIS_PROVE[MEM] ``MEM x [x]`` >>
  gvs[] >>
  drule_then assume_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
  first_x_assum $ irule_at (Pos hd) >>
  gvs[AllCaseEqs()] >>
  `(LENGTH inst' + pos_val pc p code2) = pos_val pc (p + LENGTH inst') code2`
    suffices_by gvs[] >>
  irule pos_val_acc_sum >>
  metis_tac[ADD_COMM]
QED

Theorem get_shmem_info_ALL_DISTINCT:
  LENGTH (prog_to_bytes code2) < dimword (:'a) /\
  enc_ok c /\
  all_enc_ok c labs ffis p' (code2: 'a sec list) ==>
  ALL_DISTINCT (MAP (\rec. rec.entry_pc) $ SND $ get_shmem_info code2 p [] [])
Proof
  rw[] >>
  drule get_shmem_info_thm >>
  disch_then $ qspecl_then [`p`,`[]`,`[]`] assume_tac >>
  gvs[UNZIP_MAP,MAP_GENLIST,combinTheory.o_DEF,MAP_MAP_o,MAP_FLAT,
    ALL_DISTINCT_FLAT,MEM_GENLIST] >>
  rw[] >>
  gvs[line_to_info_def] >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  pairarg_tac >>
  gvs[PULL_EXISTS,ELIM_UNCURRY,MEM_MAP] >>
  qmatch_asmsub_abbrev_tac `MEM x a1` >>
  pop_assum $ assume_tac o GSYM o PURE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  gvs[AllCaseEqs()] >>
  `pos_val i 0 code2 < pos_val j 0 code2` by (
    irule pos_val_mono >>
    gvs[] >>
    metis_tac[]
  ) >>
  gvs[] >>
  `pos_val j 0 code2 < pos_val (num_pcs code2) 0 code2` by (
    irule pos_val_mono >>
    gvs[] >>
    metis_tac[]
  ) >>
  drule_then assume_tac pos_val_num_pcs >>
  PURE_ONCE_REWRITE_TAC[GSYM pos_val_acc_0] >>
  assume_tac ZERO_LT_dimword >>
  `(pos_val i 0 code2) MOD dimword (:'a) < (pos_val j 0 code2) MOD dimword (:'a)` by
    gvs[LESS_TRANS,LESS_MOD] >>
  spose_not_then assume_tac >>
  `(pos_val i 0 code2) MOD dimword (:'a) = (pos_val j 0 code2) MOD dimword (:'a)` by
    metis_tac[ADD_MOD,ADD_COMM] >>
  gvs[]
QED

Theorem get_shmem_info_EMPTY_LENGTH_EQ:
  all_enc_ok c labs ffis p' (code2: 'a sec list) ==>
  LENGTH (FST (get_shmem_info code2 p [] [])) =
    LENGTH (SND (get_shmem_info code2 p [] []))
Proof
  mp_tac get_shmem_info_thm >>
  disch_then $ qspecl_then [`code2`, `p`,`[]`,`[]`,`p'`] assume_tac >>
  gvs[] >>
  rpt strip_tac >>
  gvs[UNZIP_MAP]
QED

Theorem line_to_info_offset_FST_eq:
  MAP FST (line_to_info code p accum) = MAP FST (line_to_info code 0 accum)
Proof
  gvs[line_to_info_def] >>
  Cases_on `accum` >>
  gvs[AllCaseEqs()] >>
  ntac 3 TOP_CASE_TAC >>
  gvs[ELIM_UNCURRY]
QED

Theorem line_to_info_offset_SND_eq:
  MAP SND (line_to_info code p accum) = MAP (\x. SND x with
    <|entry_pc := n2w p + (SND x).entry_pc
     ;exit_pc := n2w p + (SND x).exit_pc |>)
    (line_to_info code 0 accum)
Proof
  gvs[line_to_info_def] >>
  CASE_TAC >>
  gvs[AllCaseEqs()] >>
  rpt (TOP_CASE_TAC >> gvs[ELIM_UNCURRY]) >>
  gvs[word_add_n2w] >>
  once_rewrite_tac[GSYM pos_val_acc_0] >>
  gvs[]
QED

Theorem get_shmem_info_init_pc_offset:
  all_enc_ok c labs ffis p' code ==>
  FST (get_shmem_info code 0 [] []) = FST (get_shmem_info code p [] []) /\
  MAP (\rec. rec with
    <|entry_pc:=n2w p + rec.entry_pc
     ;exit_pc:=n2w p + rec.exit_pc|>) (SND $ get_shmem_info code 0 [] []) =
  SND (get_shmem_info code p [] [])
Proof
  strip_tac >>
  drule_then assume_tac get_shmem_info_thm >>
  gvs[UNZIP_MAP,MAP_FLAT,MAP_GENLIST,combinTheory.o_DEF,MAP_MAP_o] >>
  gvs[IN_DISJOINT,MEM_FLAT,MEM_GENLIST,MEM_MAP] >>
  gvs[line_to_info_offset_FST_eq,line_to_info_offset_SND_eq]
QED

Theorem mmio_pcs_min_index_get_shmem_info_ok:
  all_enc_ok c labs ffis' p' (code2: 'a sec list) /\
  enc_ok c /\ EVERY (λx. ∃s. x = ExtCall s) ffis ∧
  get_shmem_info code2 p ffis [] = (new_ffi_names, new_shmem_info) ==>
  mmio_pcs_min_index new_ffi_names = SOME $ LENGTH ffis
Proof
  rpt strip_tac >>
  drule get_shmem_info_PREPEND >>
  drule_then assume_tac get_shmem_info_MappedRead_or_MappedWrite >>
  gvs[Sh_not_Ext] >>
  rpt strip_tac >>
  drule_then assume_tac mmio_pcs_min_index_APPEND_thm >>
  gvs[]
QED

Theorem get_shmem_info_ok_lemma:
  all_enc_ok c labs ffis' p' (code2: 'a sec list) /\
  enc_ok c /\
  LENGTH (prog_to_bytes code2) < dimword (:'a) /\
  EVERY (λx. ∃s. x = ExtCall s) ffis ∧
  get_shmem_info code2 p ffis [] = (new_ffi_names, new_shmem_info)
  ==>
  (!pc op re a inst len i.
    (asm_fetch_aux pc code2 = SOME (Asm (ShareMem op re a) inst len) /\
    mmio_pcs_min_index new_ffi_names = SOME i) ==>
    (?index.
      find_index (n2w p + n2w (pos_val pc 0 code2)) (MAP (\rec. rec.entry_pc) new_shmem_info) 0 =
        SOME index /\
      (let (name, nb) = get_memop_info op in
        EL (index+i) new_ffi_names = SharedMem name /\
        EL index new_shmem_info =
          <|entry_pc := (EL index new_shmem_info).entry_pc
           ;nbytes := nb
           ;access_addr := a
           ;reg := re
           ;exit_pc :=n2w p + n2w (pos_val pc 0 code2 + len)|>))) /\
  (!pc line.
      asm_fetch_aux pc code2 = SOME line /\
      (!op re a inst len. line <> Asm (ShareMem op re a) inst len) ==>
      DISJOINT (set (MAP (\rec. rec.entry_pc) new_shmem_info))
        {n2w p + n2w a + n2w (pos_val pc 0 code2) |
          a < LENGTH (line_bytes line)})
Proof
  rw[] >>
  drule_all mmio_pcs_min_index_get_shmem_info_ok >>
  drule get_shmem_info_PREPEND >>
  drule_then assume_tac get_shmem_info_MappedRead_or_MappedWrite >>
  gvs[] >>
  rpt strip_tac >>
  gvs[EL_APPEND_EQN,word_add_n2w]
  >- (
    pairarg_tac >>
    drule_all MEM_get_shmem_info >>
    strip_tac >>
    first_x_assum $ qspec_then `p` assume_tac >>
    gvs[] >>
    drule $ GEN_ALL get_shmem_info_ALL_DISTINCT >>
    gvs[] >>
    disch_then imp_res_tac >>
    gvs[find_index_ALL_DISTINCT_EL_eq,MEM_EL] >>
    `LENGTH (SND (get_shmem_info code2 p [] [])) =
      LENGTH (ZIP (get_shmem_info code2 p [] []))` by (
      drule get_shmem_info_EMPTY_LENGTH_EQ >>
      Cases_on `get_shmem_info code2 p [] []` >>
      gvs[LENGTH_ZIP,AllCaseEqs()]
    ) >>
    simp[] >>
    first_assum $ irule_at (Pos hd) >>
    gvs[EL_ZIP,get_shmem_info_EMPTY_LENGTH_EQ] >>
    gvs[EL_MAP] >>
    simp[pos_val_acc_0] >>
    drule get_shmem_info_EMPTY_LENGTH_EQ >>
    strip_tac >>
    Cases_on `get_shmem_info code2 p [] []` >>
    gvs[EL_ZIP] >>
    qpat_x_assum `_ = EL n r'` $ assume_tac o PURE_REWRITE_RULE[Once EQ_SYM_EQ] >>
    gvs[shmem_rec_accessors] >>
    drule_all all_enc_ok_asm_fetch_aux_IMP_line_ok >>
    disch_then assume_tac >>
    gvs[line_ok_def] >>
    `pos_val pc (p + LENGTH inst') code2 = (LENGTH inst' + pos_val pc p code2)`
      suffices_by gvs[] >>
    gvs[pos_val_acc_sum]
  ) >>
  gvs[pos_val_acc_0] >>
  rw[] >>
  drule get_shmem_info_thm >>
  disch_then $ qspecl_then [`p`,`[]`,`[]`] assume_tac >>
  gvs[UNZIP_MAP,MAP_FLAT,MAP_GENLIST,combinTheory.o_DEF,MAP_MAP_o] >>
  gvs[IN_DISJOINT,MEM_FLAT,MEM_GENLIST,MEM_MAP] >>
  rpt strip_tac >>
  spose_not_then assume_tac >>
  gvs[] >>
  qpat_x_assum `!op re a inst len. line <> _` mp_tac >>
  gvs[line_to_info_def,MEM_MAP,PULL_EXISTS] >>
  qmatch_asmsub_abbrev_tac `MEM x a1` >>
  qpat_x_assum `Abbrev(a1 = _)` $ assume_tac o GSYM o PURE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  gvs[AllCaseEqs()] >>
  pairarg_tac >>
  imp_res_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
  `pc = x'` suffices_by (rpt strip_tac >> gvs[]) >>
  spose_not_then assume_tac >>
  drule $ GEN_ALL pos_val_asm_fetch_aux_distinct >>
  disch_then imp_res_tac >>
  gvs[]
QED

Theorem asm_fetch_NOT_ffi_entry_pcs:
  LENGTH (prog_to_bytes code2) < dimword (:'a) /\
  mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
  LENGTH mc_conf.ffi_names = LENGTH mc_conf.ffi_entry_pcs /\
  all_enc_ok mc_conf.target.config labs ffi_names 0 (code2:'a sec list) /\
  enc_ok mc_conf.target.config /\
  (∀index.
    index < i ⇒
    -n2w (ffi_offset * (index + 3)) + mc_conf.target.get_pc (ms: 'state) ∉
    mc_conf.prog_addresses ∧
    -n2w (ffi_offset * (index + 3)) + mc_conf.target.get_pc ms ∉
    mc_conf.shared_addresses ∧
    -n2w (ffi_offset * (index + 3)) + mc_conf.target.get_pc ms ≠
    mc_conf.halt_pc ∧
    -n2w (ffi_offset * (index + 3)) + mc_conf.target.get_pc ms ≠
    mc_conf.ccache_pc ∧
    find_index
      (-n2w (ffi_offset * (index + 3)) + mc_conf.target.get_pc ms)
      mc_conf.ffi_entry_pcs 0 = SOME index) /\
  bytes_in_mem (mc_conf.target.get_pc ms) (prog_to_bytes code2) t.mem
     (mc_conf:('a,'state,'b) machine_config).prog_addresses dm /\
  asm_fetch_aux pos code2 = SOME line /\
  a < LENGTH (line_bytes line) ==>
  ~MEM (mc_conf.target.get_pc ms + n2w a + (n2w $ pos_val pos 0 code2))
    (TAKE i mc_conf.ffi_entry_pcs)
Proof
  rw[] >>
  drule_then assume_tac bytes_in_mem_IMP >>
  drule_then assume_tac bytes_in_memory_in_domain >>
  drule_then assume_tac mmio_pcs_min_index_is_SOME >>
  gvs[MEM_EL,LENGTH_TAKE] >>
  rpt strip_tac >>
  gvs[EL_TAKE] >>
  drule_then (qspec_then `0` assume_tac) pos_val_num_pcs >>
  gvs[] >>
  last_x_assum drule >>
  gvs[] >>
  strip_tac >>
  drule find_index_is_MEM >>
  rpt strip_tac >>
  drule find_index_MEM >>
  disch_then $ qspec_then `0` assume_tac >>
  gvs[] >>
  imp_res_tac asm_fetch_aux_pos_val_SUC >>
  pop_assum $ qspec_then `0` assume_tac >>
  drule pos_val_bound >>
  disch_then $ qspecl_then [`pos+1`,`0`] assume_tac >>
  gvs[] >>
  qpat_x_assum `!k. _ < LENGTH (prog_to_bytes code2) ==> _` $
    qspec_then `a+pos_val pos 0 code2` mp_tac >>
  impl_tac >- gvs[] >>
  gvs[addressTheory.word_arith_lemma1]
QED

Theorem list_subset_refl:
!xs.
  list_subset xs xs
Proof
  Induct_on `xs` >>
  gvs[list_subset_def] >>
  rw[] >>
  drule_at_then Any irule MONO_EVERY >>
  simp[]
QED

Theorem list_subset_TAKE:
!i xs.
  list_subset (TAKE i xs) xs
Proof
  Induct_on `xs` >>
  gvs[list_subset_def] >>
  Induct_on `i` >>
  gvs[] >>
  rw[] >>
  irule MONO_EVERY >>
  first_x_assum $ irule_at (Pos last) >>
  gvs[]
QED

Theorem list_subset_trans:
  list_subset a b /\ list_subset b c ==>
  list_subset a c
Proof
  gvs[list_subset_def] >>
  Induct_on `a` >>
  gvs[] >>
  rw[] >>
  gvs[EVERY_MEM]
QED

Theorem genlist_line_to_info_entry_pc_max:
  all_enc_ok c labs ffis p' code2 /\ enc_ok c ==>
  EVERY (\x. w2n (SND x).entry_pc < pos_val (num_pcs code2) 0 code2)
    (FLAT (GENLIST
      (λi. line_to_info code2 0 (i,asm_fetch_aux i code2))
      (num_pcs code2)))
Proof
  gvs[EVERY_FLAT,EVERY_GENLIST,line_to_info_def] >>
  rpt strip_tac >>
  qpat_abbrev_tac `y = asm_fetch_aux _ _` >>
  TOP_CASE_TAC >>
  simp[] >>
  TOP_CASE_TAC >>
  simp[] >>
  TOP_CASE_TAC >>
  simp[ELIM_UNCURRY] >>
  `pos_val i 0 code2 < pos_val (num_pcs code2) 0 code2` suffices_by (
    strip_tac >>
    drule_at_then (Pos $ el 2) irule LESS_EQ_LESS_TRANS >>
    irule MOD_LESS_EQ >>
    simp[] ) >>
  irule $ GEN_ALL pos_val_mono >>
  gvs[] >>
  metis_tac[]
QED

(* This is set up for the very first compile call *)
Triviality IMP_state_rel_make_init:
  good_code mc_conf.target.config LN (code: 'a sec list) ∧
   mc_conf_ok mc_conf ∧
   (no_share_mem_inst code ==>
     compiler_oracle_ok coracle labs (LENGTH (prog_to_bytes code2)) mc_conf.target.config mc_conf.ffi_names) ∧
   list_subset (FILTER (\x. ∃s. x= ExtCall s) $
      find_ffi_names code) $ TAKE i mc_conf.ffi_names ∧
   remove_labels clock mc_conf.target.config 0 LN (TAKE i mc_conf.ffi_names) code =
      SOME (code2,labs) /\
   good_init_state mc_conf ms (prog_to_bytes code2)
      cbspace t m dm sdm io_regs cc_regs /\
   get_shmem_info code2 0 [] [] = (new_ffi_names, shmem_info) /\
   new_shmem_info = MAP (\rec. rec with
    <|entry_pc:= mc_conf.target.get_pc ms + rec.entry_pc
     ;exit_pc:= mc_conf.target.get_pc ms + rec.exit_pc|>) shmem_info /\
   DROP i mc_conf.ffi_names = new_ffi_names /\
   mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
   MAP (\rec. rec.entry_pc) new_shmem_info = DROP i (mc_conf.ffi_entry_pcs) /\
   (mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH new_shmem_info),
                              (MAP (\rec. (rec.nbytes, rec.access_addr, rec.reg,
                                           rec.exit_pc))
                                   new_shmem_info))) /\
   no_install_or_no_share_mem code mc_conf.ffi_names /\
   (!bn. bn < cbspace ==>
      ~MEM (n2w bn + n2w (LENGTH (prog_to_bytes code2)) +
             mc_conf.target.get_pc ms) (TAKE i mc_conf.ffi_entry_pcs))
   ==>
   state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,
       mc_conf.target.get_pc ms)
     (make_init mc_conf (ffi:'ffi ffi_state) io_regs cc_regs t m dm sdm ms code
      compile_lab (mc_conf.target.get_pc ms+n2w(LENGTH(prog_to_bytes code2))) cbspace coracle) t ms
Proof
  rw[] \\ drule $ GEN_ALL remove_labels_thm
  \\ impl_tac >- (
    fs[good_code_def,mc_conf_ok_def]
    \\ rw[lab_lookup_def]>>
    TOP_CASE_TAC>>fs[lookup_def])
  \\ qabbrev_tac `new_shmem_info=MAP (\rec. rec with
      <|entry_pc:=mc_conf.target.get_pc ms + rec.entry_pc
       ;exit_pc:=mc_conf.target.get_pc ms + rec.exit_pc|>) shmem_info`
  \\ rw[]
  \\ fs[state_rel_def,
        word_loc_val_def,
        make_init_def,
        good_init_state_def,
        mc_conf_ok_def,
        compiler_oracle_ok_def,
        target_configured_def,
        good_code_def,
        start_pc_ok_def,
        ffi_interfer_ok_def,
        ccache_interfer_ok_def]
  \\ rfs[]
  \\ conj_tac >- (
        fs[Abbr ‘new_shmem_info’]>>
        fs[MAP_MAP_o,o_DEF]>>
        qmatch_goalsub_abbrev_tac ‘ZIP (l1,MAP ff _)’>>
        ‘LENGTH l1 = LENGTH (MAP ff shmem_info)’ by fs[Abbr ‘l1’,LENGTH_GENLIST]>>
        fs[ALOOKUP_ZIP_MAP_SND]>>
        ‘LENGTH shmem_info = LENGTH (DROP i mc_conf.ffi_entry_pcs)’
          by (qpat_assum ‘MAP _ shmem_info = DROP _ _’ (fn h => rewrite_tac[GSYM h])>>
              simp[])>>
        rw[Abbr ‘l1’]
        >- (‘shmem_info ≠ []’ by (strip_tac>>fs[])>>
            irule_at Any ALOOKUP_ALL_DISTINCT_MEM>>
            simp[MEM_ZIP,MAP_ZIP,ALL_DISTINCT_GENLIST,EL_GENLIST]>>
            qexists_tac ‘index - i’>>
            reverse conj_asm1_tac>- fs[EL_GENLIST]>>fs[])>>
        rewrite_tac[ALOOKUP_FAILS]>>
        rpt strip_tac>>
        gvs[NOT_LESS,NOT_LESS_EQUAL,MEM_ZIP])>>
  conj_tac >- (
    rw[]>>
    gvs[IMP_CONJ_THM,AND_IMP_INTRO] >>
    first_x_assum $ map_first_cj >>
    simp[] >>
    gvs[call_FFI_def, AllCaseEqs()] >>
    drule mmio_pcs_min_index_is_SOME >>
    rpt strip_tac >>
    drule_all LESS_LESS_EQ_TRANS >>
    gvs[]
  )
  \\ conj_tac >-
    (ntac 2 strip_tac >>
    pairarg_tac >> fs[]>>
    drule_then assume_tac code_similar_sym >>
    drule_all_then assume_tac code_similar_IMP_both_no_share_mem >>
    fs[] >>
    qpat_x_assum`!k. _ (coracle k)`(qspec_then`k` assume_tac)>>rfs[]>>
    strip_tac>>fs[])
  \\ conj_tac >- metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
  \\ conj_tac >- metis_tac[list_subset_TAKE,list_subset_trans]
  \\ conj_tac >- metis_tac[EVEN,all_enc_ok_prog_to_bytes_EVEN]
  \\ conj_tac >- (
        imp_res_tac mmio_pcs_min_index_is_SOME>>
        rpt strip_tac>>fs[]>>
        fs[get_ffi_index_def,backendPropsTheory.the_eqn]>>
        imp_res_tac find_index_MEM>>
        first_x_assum $ qspecl_then [‘0’] assume_tac>>gvs[])
  \\ conj_tac >- (
    simp[word_loc_val_byte_def,case_eq_thms]
    \\ metis_tac[SUBSET_DEF,word_loc_val_def] )
  \\ conj_tac >- metis_tac[word_add_n2w]
  \\ conj_tac >- simp[bytes_in_mem_def]
  \\ conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `!bn. bn < cbspace ==> _` $ imp_res_tac >>
    gvs[MEM_EL] >>
    drule_then assume_tac $ cj 1 mmio_pcs_min_index_is_SOME>>
    gvs[LENGTH_TAKE] >>
    first_x_assum $ qspec_then`n` assume_tac >>
    Cases_on `n < i`
    >- gvs[EL_TAKE] >>
    `i <= n` by decide_tac >>
    gvs[] >>
    drule get_shmem_info_thm >>
    disch_then $ qspecl_then [`0`,`[]`,`[]`] assume_tac >>
    gvs[UNZIP_MAP,MAP_GENLIST,combinTheory.o_DEF,ZIP_MAP_FST_SND_EQ,MAP_MAP_o,
      Abbr`new_shmem_info`,EL_MAP] >>
    qspecl_then [`n - i`, `i`,`mc_conf.ffi_entry_pcs`]
      assume_tac $ GSYM EL_DROP >>
    gvs[] >>
    pop_assum kall_tac >>
    qpat_x_assum `_ = DROP i mc_conf.ffi_entry_pcs` $ assume_tac o GSYM >>
    qmatch_assum_abbrev_tac `DROP i mc_conf.ffi_entry_pcs = MAP offset_func flatten_genlist` >>
    gvs[] >>
    `n - i < LENGTH (MAP offset_func flatten_genlist)` by (
      qpat_x_assum `DROP i mc_conf.ffi_entry_pcs = _` $ assume_tac o GSYM >>
      asm_rewrite_tac[LENGTH_DROP] >>
      simp[]
    ) >>
    gvs[EL_MAP,Abbr`offset_func`] >>
    drule_all genlist_line_to_info_entry_pc_max >>
    strip_tac >>
    drule_then (qspec_then `n-i` assume_tac) $ iffLR EVERY_EL >>
    gvs[Abbr`flatten_genlist`] >>
    qmatch_asmsub_abbrev_tac `w2n entry_pc' < pos_val _ _ _` >>
    drule_then (fn t =>
      gvs[t,addressTheory.word_arith_lemma1]) $
      GEN_ALL pos_val_num_pcs
  )
  \\ conj_tac>-
    (drule pos_val_0 \\ simp[])
  \\ conj_tac >- metis_tac[code_similar_sec_labels_ok]
  \\ conj_tac >- (
    gvs[share_mem_state_rel_def]
    \\ rpt strip_tac
    \\ gvs[IMP_CONJ_THM, AND_IMP_INTRO]
    \\ first_x_assum $ qspecl_then [`ms2`, `k`, `index`, `new_bytes`, `t1`, `B`, `C`] mp_tac
    \\ gvs[] >> strip_tac>>fs[]>>
    drule mmio_pcs_min_index_is_SOME>>
    strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘index’ assume_tac>>gvs[]>>
    TOP_CASE_TAC>>fs[])
  \\ simp[share_mem_domain_code_rel_def]
  \\ fs[MAP_MAP_o,o_DEF,ELIM_UNCURRY]
  \\ drule $ GEN_ALL get_shmem_info_ok_lemma
  \\ disch_then $ qspecl_then [
      `w2n (mc_conf.target.get_pc ms)`,`new_shmem_info`,`mc_conf.ffi_names`,
      `TAKE i mc_conf.ffi_names`] mp_tac
  \\ gvs[]
  \\ impl_tac
  >- (
    drule mmio_pcs_min_index_is_SOME >>
    strip_tac >>
    reverse $ rw[EVERY_EL]
   >- (
      qpat_abbrev_tac `info = get_shmem_info _ _ _ _` >>
      first_x_assum $ assume_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
      Cases_on `info` >>
      drule $ GEN_ALL get_shmem_info_PREPEND >>
      gvs[] >>
      strip_tac >>
      drule $ GEN_ALL get_shmem_info_init_pc_offset >>
      disch_then $ qspec_then `w2n (mc_conf.target.get_pc ms)` mp_tac >>
      strip_tac >>
      gvs[markerTheory.Abbrev_def] >>
      metis_tac[TAKE_DROP] ) >>
    first_x_assum $ mp_tac o GSYM >>
    spose_not_then assume_tac >>fs[]>>
    qpat_x_assum`∀s. EL _ (TAKE i mc_conf.ffi_names) ≠ _` $ mp_tac >>
    fs[EL_TAKE]
  )
  \\ rw[]
  >- (
    qpat_x_assum `!pc op re a inst len. asm_fetch_aux _ _ = _ ==> ?i._` $ imp_res_tac
    \\ qexists `index + i`
    \\ drule find_index_LESS_LENGTH
    \\ `LENGTH (MAP (\rec. rec.entry_pc) new_shmem_info) =
        LENGTH mc_conf.ffi_entry_pcs - i`
          by metis_tac[LENGTH_DROP]
    \\ fs[LENGTH_MAP,LESS_SUB_ADD_LESS,EL_MAP,LENGTH_TAKE]
    \\ strip_tac
    \\ qspecl_then [`TAKE i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
      `DROP i (mc_conf: ('a,'state,'b) machine_config).ffi_entry_pcs`,
      `n2w (pos_val pc 0 code2) + (mc_conf.target.get_pc ms: 'a word)`,
      `0`] assume_tac find_index_APPEND
    \\ gvs[AllCaseEqs()]
    \\ Cases_on `get_memop_info op`
    >- (
      drule find_index_shift
      \\ fs[]
      \\ disch_then $ qspec_then `i` assume_tac
      \\ gvs[ELIM_UNCURRY,shmem_rec_component_equality]>>
      irule ALOOKUP_ALL_DISTINCT_MEM>>
      qmatch_goalsub_abbrev_tac ‘ZIP (l1, l2)’>>
      ‘LENGTH l1 = LENGTH l2’ by (unabbrev_all_tac>>fs[LENGTH_GENLIST,LENGTH_MAP])>>
      fs[MAP_ZIP,MEM_ZIP]>>unabbrev_all_tac>>fs[]>>
      fs[ALL_DISTINCT_GENLIST]>>fs[MAP_MAP_o,o_DEF]>>gvs[]>>simp[EL_MAP]>>

      qexists_tac ‘index’>>fs[EL_MAP]>>
      fs[EL_GENLIST])
    \\ qpat_x_assum `SOME _ = find_index _ _ _` $ assume_tac o GSYM
    \\ `~MEM (n2w (pos_val pc 0 code2) + mc_conf.target.get_pc ms)
        (TAKE i mc_conf.ffi_entry_pcs)` suffices_by (
      strip_tac
      \\ drule_then assume_tac (iffLR find_index_NOT_MEM)
      \\ pop_assum $ qspec_then `0` assume_tac
      \\ gvs[ELIM_UNCURRY,shmem_rec_component_equality,LENGTH_TAKE]
    )
    \\ `LENGTH (prog_to_bytes code2) < dimword (:α)` by gvs[]
    \\ drule $ GEN_ALL asm_fetch_NOT_ffi_entry_pcs
    \\ rpt $ disch_then $ drule_at Any
    \\ disch_then $ qspec_then `0` $ mp_tac o PURE_REWRITE_RULE[WORD_ADD_0]
    \\ impl_tac
    >- (
      drule $ GEN_ALL enc_ok_LENGTH_GT_0
      \\ drule_all $ GEN_ALL all_enc_ok_asm_fetch_aux_IMP_line_ok
      \\ gvs[line_ok_def,line_length_def,enc_with_nop_thm]
      \\ rpt strip_tac
      \\ pop_assum $ qspec_then `Inst (Mem op re a)` assume_tac
      \\ gvs[]
    )
    \\ gvs[]
  )
  >- (
    qpat_x_assum `!pc line. asm_fetch_aux _ _ = _ /\ _ ==> _` imp_res_tac
    \\ gvs[IN_DISJOINT]
    \\ rw[]
    \\ pop_assum $ qspec_then `x` assume_tac
    \\ gvs[]
    \\ spose_not_then assume_tac
    \\ `LENGTH (prog_to_bytes code2) < dimword (:α)` by gvs[]
    \\ drule $ GEN_ALL asm_fetch_NOT_ffi_entry_pcs
    \\ rpt $ disch_then $ drule_at Any
    \\ rw[]
    \\ qexists_tac `a`
    \\ gvs[]
    \\ metis_tac[MEM_APPEND,TAKE_DROP]
  )
  \\ drule_then (drule_then irule) $ GEN_ALL code_similar_IMP_both_no_install_or_no_share_mem
QED

Theorem make_init_simp[simp]:
    (make_init a b d e f g h i j k l m n p).ffi = b ∧
  (make_init a b d e f g h i j k l m n p).pc = 0 ∧
  (make_init a b d e f g h i j k l m n p).code = k
Proof
  EVAL_TAC
QED

Theorem semantics_make_init =
  machine_sem_EQ_sem |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH |> REWRITE_RULE []
  |> SIMP_RULE std_ss [init_ok_def,PULL_EXISTS,GSYM CONJ_ASSOC,GSYM AND_IMP_INTRO]
  |> SPEC_ALL |> Q.GEN `s1` |> Q.GEN `p`
  |> Q.GEN `t1` |> Q.SPEC `t`
  |> Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).target.get_pc ms`
  |> Q.SPEC `make_init (mc_conf: ('a,'state,'b) machine_config)
       ffi io_regs cc_regs t m dm sdm (ms:'state) code
       compile_lab (mc_conf.target.get_pc ms + (n2w (LENGTH (prog_to_bytes (code2:'a labLang$prog)))))
       cbspace coracle`
  |> SIMP_RULE std_ss [make_init_simp]
  |> MATCH_MP (MATCH_MP IMP_LEMMA IMP_state_rel_make_init)
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]

Theorem make_init_filter_skip:
   semantics
    (make_init mc_conf ffi io_regs cc_regs t m dm sdm ms (filter_skip code)
       compile_lab cbpos cbspace((λ(a,b). (a,filter_skip b)) o coracle)) =
   semantics
    (make_init mc_conf ffi io_regs cc_regs t m dm sdm ms code
      (λc p. compile_lab c (filter_skip p)) cbpos cbspace coracle)
Proof
  match_mp_tac (filter_skip_semantics)>>
  rw[]>>
  simp[make_init_def]>>
  qexists_tac`compile_lab`>>fs[]
QED

(* TODO: move *)
Theorem find_ffi_names_filter_skip:
   !code. find_ffi_names (filter_skip code) = find_ffi_names code
Proof
  recInduct find_ffi_names_ind
  \\ fs [lab_filterTheory.filter_skip_def,find_ffi_names_def]
  \\ rpt strip_tac \\ every_case_tac
  \\ fs [lab_filterTheory.not_skip_def,find_ffi_names_def]
QED

Triviality all_enc_ok_pre_filter_skip:
  ∀code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (filter_skip code)
Proof
  Induct>>TRY(Cases)>>fs[lab_filterTheory.filter_skip_def]>>rw[]>>
  Induct_on`l`>>fs[]>>rw[]
QED

Theorem MAP_Section_num_filter_skip[simp]:
   ∀code. MAP Section_num (filter_skip code) = MAP Section_num code
Proof
  Induct \\ simp[lab_filterTheory.filter_skip_def]
  \\ Cases \\ fs[lab_filterTheory.filter_skip_def]
QED

Theorem filter_skip_extract_labels[simp]:
   ∀code. MAP (extract_labels o Section_lines) (filter_skip code) =
   MAP (extract_labels o Section_lines) code
Proof
  Induct \\ simp[lab_filterTheory.filter_skip_def]
  \\ Cases \\ fs[lab_filterTheory.filter_skip_def] \\
  Induct_on`l` \\ fs[] \\
  Cases \\ fs[lab_filterTheory.not_skip_def] \\
  every_case_tac \\ fs[]
QED

Theorem get_code_labels_filter_skip[simp]:
   ∀code. get_code_labels (filter_skip code) = get_code_labels code
Proof
  recInduct lab_filterTheory.filter_skip_ind
  \\ rw[lab_filterTheory.filter_skip_def, get_code_labels_cons]
  \\ rw[sec_get_code_labels_def, LIST_TO_SET_FILTER]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ rw[Once EXTENSION, EQ_IMP_THM, PULL_EXISTS]
  >- metis_tac[]
  \\ asm_exists_tac \\ rw[]
  \\ fs[lab_filterTheory.not_skip_def]
  \\ CASE_TAC \\ fs[]
QED

Theorem get_labels_filter_skip[simp]:
   ∀code. get_labels (filter_skip code) = get_labels code
Proof
  recInduct lab_filterTheory.filter_skip_ind
  \\ rw[lab_filterTheory.filter_skip_def, get_labels_def]
  \\ rw[sec_get_labels_def, LIST_TO_SET_FILTER]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[Once EXTENSION, EQ_IMP_THM, PULL_EXISTS]
  >- metis_tac[]
  \\ asm_exists_tac \\ rw[]
  \\ fs[lab_filterTheory.not_skip_def]
  \\ CASE_TAC \\ fs[line_get_labels_def]
QED

Theorem implements_intro_gen:
   (b /\ x <> Fail ==> y = {x}) ==> b ==> implements' T y {x}
Proof
  fs[semanticsPropsTheory.implements'_def,
     semanticsPropsTheory.extend_with_resource_limit'_def]
QED

Theorem find_ffi_names_ALL_DISTINCT:
    ∀code. ALL_DISTINCT (find_ffi_names code)
Proof
  ho_match_mp_tac find_ffi_names_ind>>rw[find_ffi_names_def]>>
  TOP_CASE_TAC>>fs[find_ffi_names_def]>>
  TOP_CASE_TAC>>fs[find_ffi_names_def]>>
  fs[list_add_if_fresh_thm]>>
  IF_CASES_TAC>>fs[ALL_DISTINCT_APPEND]
QED

Triviality not_not_skip_IMP_Skip:
  ~not_skip inst' ==> ?l n. inst' = Asm (Asmi (Inst Skip)) l n
Proof
  gvs[DefnBase.one_line_ify NONE lab_filterTheory.not_skip_def] >>
  rpt TOP_CASE_TAC
QED

Theorem asm_fetch_aux_filter_skip:
!code p.
  asm_fetch_aux p (filter_skip code) = SOME inst' /\
  not_skip inst' ==>
  ?p'. asm_fetch_aux p' code = SOME inst'
Proof
  ho_match_mp_tac num_pcs_ind >>
  gvs[asm_fetch_aux_def,lab_filterTheory.filter_skip_def] >>
  rw[DefnBase.one_line_ify NONE is_Label_def] >>
  CASE_TAC
  >- (gvs[lab_filterTheory.not_skip_def,asm_fetch_aux_def] >> metis_tac[])
  >- (
    gvs[asm_fetch_aux_def] >>
    rpt $ last_x_assum mp_tac >>
    IF_CASES_TAC
    >- (gvs[] >- metis_tac[]) >>
    gvs[] >>
    rpt strip_tac >>
    res_tac >>
    qexists `p'+1` >>
    gvs[]
  )
  >- (
    gvs[asm_fetch_aux_def] >>
    rpt $ last_x_assum mp_tac >>
    IF_CASES_TAC
    >- metis_tac[] >>
    gvs[asm_fetch_aux_def] >>
    rpt strip_tac >>
    res_tac >>
    qexists `p'+1` >>
    gvs[]
  )
  >- gvs[lab_filterTheory.not_skip_def,asm_fetch_aux_def]
  >- (
    drule_then assume_tac not_not_skip_IMP_Skip >>
    gvs[] >>
    res_tac >>
    qexists `p'+1` >>
    gvs[]
  )
  >- gvs[lab_filterTheory.not_skip_def,asm_fetch_aux_def]
QED

Theorem IMP_asm_fetch_aux_filter_skip:
  !p code i.
    asm_fetch_aux p code = SOME i /\ not_skip i ==>
    ?p'. asm_fetch_aux p' (filter_skip code) = SOME i
Proof
  ho_match_mp_tac asm_fetch_aux_ind >>
  rw[asm_fetch_aux_def,lab_filterTheory.filter_skip_def]
  >- (
    simp[AllCaseEqs()] >>
    metis_tac[]) >>
  first_x_assum $ drule_all >>
  rw[] >>
  irule_at (Pos hd) EQ_TRANS >>
  first_x_assum $ irule_at (Pos last) >>
  qexists `p'+1` >>
  simp[]
QED

Theorem no_share_mem_filter_skip:
  no_share_mem_inst (filter_skip code) <=> no_share_mem_inst code
Proof
  eq_tac >- (
    gvs[no_share_mem_inst_def] >>
    spose_not_then assume_tac >>
    rw[] >>
    last_x_assum mp_tac >>
    simp[] >>
    drule IMP_asm_fetch_aux_filter_skip >>
    simp[lab_filterTheory.not_skip_def] >>
    metis_tac[]) >>
  gvs[no_share_mem_inst_def] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  fs[] >>
  drule asm_fetch_aux_filter_skip >>
  gvs[lab_filterTheory.not_skip_def] >>
  metis_tac[]
QED


Theorem all_pc_adjust_pc:
!code p.
  p < num_pcs (filter_skip code) ==>
  ?k. adjust_pc k code = p
Proof
  ho_match_mp_tac num_pcs_ind >>
  gvs[num_pcs_def,lab_filterTheory.filter_skip_MAP] >>
  rw[]
  >- (
    first_x_assum $ drule_then assume_tac >>
    gvs[] >>
    qexists `k` >>
    Cases_on `k` >>
    rpt $ simp[Once adjust_pc_def]
  )
  >- (
    Cases_on `p`
    >- (
      qexists`0` >>
      rpt $ simp[Once adjust_pc_def]
    ) >>
    Cases_on `is_Label x` >>
    gvs[num_pcs_def]
    >- (
      first_x_assum $ drule_then assume_tac >>
      gvs[] >>
      Cases_on `k'`
      >- (
        spose_not_then kall_tac >>
        pop_assum mp_tac >>
        simp[Once adjust_pc_def]
      ) >>
      qexists`SUC n'`>>
      simp[Once adjust_pc_def]
    ) >>
    first_x_assum $ qspec_then `n` assume_tac >>
    gvs[] >>
    Cases_on `k'`
    >- (
      DEP_ONCE_REWRITE_TAC[adjust_pc_def] >>
      simp[] >>
      qexists `1` >>
      gvs[] >>
      simp[Once adjust_pc_def]
    ) >>
    qexists `SUC(SUC n)` >>
    simp[Once adjust_pc_def]
  ) >>
  Cases_on `is_Label x` >>
  gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  gvs[]
  >- (
    Cases_on `k'`
    >- (
      qexists `0` >>
      rpt $ simp[Once adjust_pc_def]
    ) >>
    simp[Once adjust_pc_def] >>
    qexists `SUC n` >> gvs[]
  )
  >- (
    Cases_on `k'`
    >- (
      qexists `0` >>
      rpt $ simp[Once adjust_pc_def]
    ) >>
    simp[Once adjust_pc_def] >>
    qexists `SUC(SUC n)` >> gvs[]
  )
QED

Theorem no_install_or_no_share_mem_filter_skip:
  no_install_or_no_share_mem code ffi_names ==>
  no_install_or_no_share_mem (filter_skip code) ffi_names
Proof
  gvs[no_install_or_no_share_mem_def,no_install_def,no_share_mem_inst_def] >>
  rw[] >>
  gvs[]
  >- (
    disj1_tac >>
    rw[] >>
    spose_not_then assume_tac >>
    last_x_assum mp_tac >> simp[] >>
    drule_then assume_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
    drule_then assume_tac all_pc_adjust_pc >>
    gvs[] >>
    metis_tac[asm_fetch_aux_eq]
  ) >>
  disj2_tac >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >> simp[] >>
  drule_then assume_tac asm_fetch_SOME_IMP_LESS_num_pcs >>
  drule_then assume_tac all_pc_adjust_pc >>
  gvs[] >>
  metis_tac[asm_fetch_aux_eq]
QED
(*
Theorem no_share_mem_inst_APPEND_IMP:
  no_share_mem_inst (l ++ sec_list) ==>
  no_share_mem_inst l /\ no_share_mem_inst sec_list
Proof
  simp[no_share_mem_inst_def] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  irule_at (Pos hd) EQ_TRANS >>
  first_assum $ irule_at (Pos last) >>
  irule_at (Pos hd) EQ_TRANS
  >- (
    irule_at (Pos last) asm_fetch_aux_APPEND1 >>
    drule asm_fetch_SOME_IMP_LESS_num_pcs >>
    metis_tac[]
  ) >>
  irule_at (Pos last) asm_fetch_aux_APPEND2 >>
  metis_tac[]
QED
*)
Theorem asm_fetch_aux_MEM:
  MEM x l /\ ~(is_Label x) ==>
  ?p. asm_fetch_aux p [Section n l] = SOME x
Proof
  Induct_on `l` >>
  simp[asm_fetch_aux_def] >>
  rw[]
  >- (
    qexists `0` >>
    simp[]
  ) >>
  fs[] >>
  TOP_CASE_TAC
  >- metis_tac[] >>
  qexists `p+1` >>
  simp[]
QED
(*
Theorem no_share_mem_inst_EVERY:
  no_share_mem_inst sec_list =
  EVERY (
    (EVERY (\x. !op re a inst len.
       x <> (Asm (ShareMem op re a)) inst len)) o
    Section_lines) sec_list
Proof
  Induct_on `sec_list`
  >- (
    fs[no_share_mem_inst_def] >>
    simp[DefnBase.one_line_ify NONE asm_fetch_aux_def]) >>
  rw[] >>
  eq_tac
  >- (
    strip_tac >>
    pop_assum $ assume_tac o
      PURE_REWRITE_RULE[Once $
        Q.prove (`(x::y) = [x] ++ y`,simp[])] >>
    reverse conj_tac
    >- (
      drule no_share_mem_inst_APPEND_IMP >>
      simp[]) >>
    dxrule $ cj 1 no_share_mem_inst_APPEND_IMP >>
    pop_assum kall_tac >>
    simp[no_share_mem_inst_def] >>
    simp[DefnBase.one_line_ify NONE labLangTheory.Section_lines_def] >>
    TOP_CASE_TAC >>
    strip_tac >>
    spose_not_then assume_tac >>
    last_x_assum mp_tac >>
    fs[NOT_EVERY,o_DEF,EXISTS_MEM] >>
    simp[Once $ DefnBase.one_line_ify NONE asm_fetch_aux_def] >>
    TOP_CASE_TAC >>
    gvs[is_Label_def]
    >- (qexists `0` >>simp[]) >>
    TOP_CASE_TAC >>
    drule asm_fetch_aux_MEM >>
    simp[is_Label_def] >>
    strip_tac >>
    irule_at (Pos hd) EQ_TRANS >>
    first_assum $ irule_at (Pos last)
    >- metis_tac[] >>
    qexists `p + 1` >> simp[]
  ) >>
  rw[] >>
  PURE_REWRITE_TAC[Once $ Q.prove(`(x::y) = [x] ++ y`,simp[])] >>
  irule no_share_mem_APPEND >>
  reverse conj_tac >- metis_tac[] >>
  pop_assum kall_tac >>
  last_x_assum kall_tac >>
  first_x_assum mp_tac >>
  fs[DefnBase.one_line_ify NONE labLangTheory.Section_lines_def] >>
  TOP_CASE_TAC >>
  rw[no_share_mem_inst_def] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[o_DEF,EXISTS_MEM] >>
  pop_assum mp_tac >>
  qid_spec_tac `p` >>
  Induct_on `l`
  >- simp[asm_fetch_aux_def] >>
  rw[] >>
  pop_assum mp_tac >>
  simp[asm_fetch_aux_def] >>
  TOP_CASE_TAC
  >- (
    strip_tac >>
    gvs[] >>
    metis_tac[]
  ) >>
  TOP_CASE_TAC >>
  metis_tac[]
QED

*)
Theorem find_ffi_names_EVERY:
  ∀code ls. find_ffi_names code = ls ⇒ EVERY (λx. ∃s. x = ExtCall s) ls
Proof
  recInduct find_ffi_names_ind>>
  rw[list_add_if_fresh_thm,find_ffi_names_def]>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[EVERY_MEM]>>
  IF_CASES_TAC>>fs[]>>
  rpt strip_tac>>fs[]
QED

(*
Theorem compile_lab_ffi_names_SOME:
  compile_lab c sec_list = SOME (bytes,c') /\
  c.ffi_names = SOME ffis /\
  EVERY (\x. x <> "MappedRead" /\ x <> "MappedWrite") ffis ==>
  ?ffi_names. c'.ffi_names = SOME ffi_names /\
  mmio_pcs_min_index ffi_names = SOME $ LENGTH ffis
Proof
  simp[compile_lab_def] >>
  pairarg_tac >>
  fs[] >>
  pop_assum $ mp_tac o SRULE[AllCaseEqs()] >>
  rpt TOP_CASE_TAC >>
  pairarg_tac >>
  rw[] >>
  gvs[] >>
  pop_assum mp_tac >>
  simp[GSYM FILTER_EQ_ID] >>
  disch_then assume_tac >>
  first_assum (fn thm => CONV_TAC (LHS_CONV $ REWRITE_CONV[Once $ GSYM thm])) >>
  first_assum (fn thm => CONV_TAC (RHS_CONV $ REWRITE_CONV[Once $ GSYM thm])) >>
  irule FILTER_mmio_pcs_min_index >>
  drule get_shmem_info_MappedRead_or_MappedWrite >>
  simp[]
QED

Theorem compile_lab_no_share_mem_ffi_names_SOME:
  compile_lab c sec_list = SOME (bytes,c') /\
  no_share_mem_inst sec_list /\
  c.ffi_names = SOME ffi_names /\
  (EVERY $ \x. x <> "MappedRead" /\ x <> "MappedWrite") ffi_names ==>
  c'.ffi_names = SOME ffi_names /\
  mmio_pcs_min_index ffi_names = SOME $ LENGTH ffi_names
Proof
  strip_tac >>
  drule_all_then assume_tac compile_lab_ffi_names_SOME >>
  fs[] >>
  conj_asm1_tac >- (
    rpt (pop_assum mp_tac) >>
    simp[compile_lab_def] >>
    pairarg_tac >>
    fs[] >>
    pop_assum $ mp_tac o SRULE[AllCaseEqs()] >>
    rpt TOP_CASE_TAC >>
    pairarg_tac >>
    rw[] >>
    gvs[remove_labels_def] >>
    drule_then assume_tac remove_labels_loop_no_share_mem_inst >>
    pop_assum mp_tac >>
    impl_tac
    >- drule_then irule enc_sec_list_no_share_mem_inst >>
    strip_tac >>
    drule_all no_share_mem_IMP_get_shmem_info >>
    strip_tac >>
    gvs[]) >>
  metis_tac[]
QED
*)

val semantics_compile_lemma = Q.prove(
  ` mc_conf_ok mc_conf ∧
    (no_share_mem_inst code ==>
      compiler_oracle_ok coracle c'.labels (LENGTH bytes) c.asm_conf mc_conf.ffi_names) ∧
    (* Assumptions on input code *)
    good_code mc_conf.target.config LN code ∧
    (* Config state *)
    c.asm_conf = mc_conf.target.config /\
    c.labels = LN ∧ c.pos = 0 ∧
    lab_to_target$compile (c:'a lab_to_target$config) code = SOME (bytes,c') /\
    (* FFI is either given or computed *)
    c'.ffi_names = SOME mc_conf.ffi_names /\
    good_init_state mc_conf ms bytes cbspace t m dm sdm io_regs cc_regs /\
    (* set up mmio_info and ffi_entry_pcs for mmio *)
    MAP (\rec. rec.entry_pc + mc_conf.target.get_pc ms) c'.shmem_extra =
      DROP i mc_conf.ffi_entry_pcs /\
    mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH c'.shmem_extra),
                              (MAP (\rec. (rec.nbytes, rec.access_addr, rec.reg,
                                           rec.exit_pc + mc_conf.target.get_pc ms))
                                   c'.shmem_extra)) ∧
    no_install_or_no_share_mem code mc_conf.ffi_names /\
   (mmio_pcs_min_index mc_conf.ffi_names = SOME i) /\
    (* to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer *)
    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a) /\
    (* the original ffi names provided does not contain MappedRead or MappedWrite *)
    (!ffis. c.ffi_names = SOME ffis ==> EVERY (λx. ∃s. x = ExtCall s) ffis) /\
    semantics (make_init mc_conf ffi io_regs cc_regs t m dm sdm ms code
      lab_to_target$compile (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
      coracle
    ) <> Fail ==>
    machine_sem mc_conf ffi ms =
    {semantics (make_init mc_conf ffi io_regs cc_regs t m dm sdm ms code
      lab_to_target$compile (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
      coracle
    )}`,
  fs[compile_def,compile_lab_def]>>
  pairarg_tac \\ fs[] \\
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  rw[]>>
  `compile =  (λc p. compile_lab c (filter_skip p)) ` by
    fs[FUN_EQ_THM,compile_def]>>
  pop_assum SUBST_ALL_TAC>>
  gvs[] >>
  fs[GSYM make_init_filter_skip]>>
  SIMP_TAC (bool_ss) [Once WORD_ADD_COMM]>>
  qabbrev_tac `info=get_shmem_info q 0 [] []` >>
  first_x_assum $ mp_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  pairarg_tac >>
  strip_tac >>
  gvs[ELIM_UNCURRY] >>
  match_mp_tac (GEN_ALL $ SRULE[] semantics_make_init)>>
  fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
  fs[find_ffi_names_filter_skip,GSYM PULL_EXISTS,MAP_MAP_o,o_DEF]>>
  qpat_x_assum `_ ++ _ = mc_conf.ffi_names` $ assume_tac o GSYM >>
  conj_tac >- fs[mc_conf_ok_def] >>
  conj_tac >- (
    fs[good_code_def] >>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
    fs[GSYM ALL_EL_MAP])>>
  rename1`_ = SOME (q,r)` >>
  qexists `r` >>
  fs[good_init_state_def] >>
  conj_tac >- (
    rpt strip_tac >>
    fs[compiler_oracle_ok_def,no_share_mem_filter_skip] >>
    rw[] >>
    rename1 `coracle k` >>
    last_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\ rw[] \\
    fs[good_code_def]>>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
    fs[GSYM ALL_EL_MAP]
  )>>
  qmatch_asmsub_rename_tac `mmio_pcs_min_index (ffis ++ rest) = SOME i` >>
  `mmio_pcs_min_index (ffis ++ rest) = SOME (LENGTH ffis)`
  by (
    Cases_on`c.ffi_names`
    >- (
      gvs[] >>
      drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      qmatch_assum_abbrev_tac`mmio_pcs_min_index (ffi' ++ _) = SOME _` >>
      disch_then $ qspec_then ‘ffi'’ mp_tac>>impl_tac >-
       (irule find_ffi_names_EVERY>> gvs[Abbr`ffi'`]>>metis_tac[])>>
      strip_tac>>fs[]
    ) >>
      gvs[] >>
      drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      disch_then $ qspec_then ‘ffis’ mp_tac>>fs[]
  ) >>
  gvs[] >>
  conj_tac >- (
    gvs[TAKE_LENGTH_APPEND] >>
    Cases_on `c.ffi_names` >- (
      mp_tac find_ffi_names_EVERY>>
      disch_then $ qspec_then ‘code’ mp_tac>>
      simp[GSYM FILTER_EQ_ID]>>strip_tac>>fs[list_subset_refl])>>
    gvs[list_subset_TAKE,list_subset_refl]>>
    irule list_subset_trans>>
    last_assum $ irule_at Any>>
    mp_tac find_ffi_names_EVERY>>
    simp[GSYM FILTER_EQ_ID]>>
    strip_tac>>fs[list_subset_refl]
  ) >>
  conj_tac >- (
    qexists `c.init_clock` >>
    gvs[TAKE_LENGTH_APPEND]
  ) >>
  simp[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
  simp[no_install_or_no_share_mem_filter_skip] >>
  gvs[start_pc_ok_def,MEM_EL]>>
  rw[] >>
  spose_not_then assume_tac >>
  gvs[] >>
  last_x_assum $ drule_then assume_tac >>
  rw[]>>
  gvs[find_index_LEAST_EL] >>
  qpat_x_assum `(LEAST n'. _) = n` mp_tac >>
  DEEP_INTRO_TAC whileTheory.LEAST_ELIM >>
  conj_tac
  >- (fs[MEM_EL] >> metis_tac[]) >>
  simp[] >>
  strip_tac >>
  spose_not_then kall_tac >>
  first_x_assum $ assume_tac o GSYM >>
  gvs[addressTheory.word_arith_lemma1,EL_TAKE] >>
  qpat_x_assum `n2w _ = -n2w _ ` $ assume_tac >>
  drule $ iffLR o GSYM $ cj 1 addressTheory.WORD_EQ_ADD_CANCEL >>
  disch_then $ qspec_then `n2w (ffi_offset * (n + 3))` mp_tac >>
  first_x_assum kall_tac >>
  PURE_REWRITE_TAC[cj 1 addressTheory.word_arith_lemma1,WORD_LITERAL_ADD,WORD_ADD_COMM] >>
  simp[] >>
  `cbspace + (LENGTH (prog_to_bytes q) + ffi_offset * (n + 3)) < dimword (:'a)`
    by (
      drule_at_then Any irule LESS_TRANS >>
      simp[ADD_COMM,ffi_offset_def]
  ) >>
  `bn  + (LENGTH (prog_to_bytes q) + ffi_offset * (n + 3)) < dimword (:'a)`
    by (
      drule_at_then (Pos $ el 2) irule LESS_TRANS >>
      simp[LESS_MONO_ADD]
  ) >>
  gvs[ffi_offset_def])
  |> REWRITE_RULE [CONJ_ASSOC]
  |> MATCH_MP implements_intro_gen
  |> REWRITE_RULE [GSYM CONJ_ASSOC]

(* try to show the condition of semantics_compile is not vacuous *)
(* prove that mmio_min_min_index actually exists,
  and LENGTH ffi_names = LENGTH ffi_entry_pcs,
  which are stated in start_pc_ok
Theorem get_shmem_info_FST_eq:
!q p names info p' info'.
  FST (get_shmem_info q p names info) = FST (get_shmem_info q p' names info')
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  pairarg_tac >>
  gvs[get_shmem_info_def]
QED

Theorem get_shmem_info_FST_SND_LENGTH_eq:
!q p names info.
  LENGTH (FST (get_shmem_info q p names info)) + LENGTH info =
  LENGTH (SND (get_shmem_info q p names info)) + LENGTH names
Proof
  ho_match_mp_tac get_shmem_info_ind >>
  rpt strip_tac >>
  gvs[get_shmem_info_def] >>
  pairarg_tac >>
  gvs[get_shmem_info_def]
QED
*)
(*
Theorem start_pc_ok_not_vacuous_lemma:
  LENGTH  <= LENGTH mc_conf.ffi_entry_pcs /\
  compile c (code: 'a sec list) = SOME (bytes,c') ∧
  c'.ffi_names = SOME mc_conf.ffi_names /\
  MAP (\rec. rec.entry_pc + mc_conf.target.get_pc ms) c'.shmem_extra =
    DROP (LENGTH old_ffi_names) mc_conf.ffi_entry_pcs /\
  (!ffis. c.ffi_names = SOME ffis ==>
    ~MEM "MappedRead" ffis /\ ~MEM "MappedWrite" ffis )
  ==>
  ?i. mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
  LENGTH mc_conf.ffi_names = LENGTH mc_conf.ffi_entry_pcs
Proof
  fs[compile_def,compile_lab_def]>>
  pairarg_tac \\ fs[] >>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  rw[]>>
  `compile =  (λc p. compile_lab c (filter_skip p)) ` by
    fs[FUN_EQ_THM,compile_def]>>
  pop_assum SUBST_ALL_TAC>>
  fs[find_ffi_names_filter_skip,GSYM PULL_EXISTS,MAP_MAP_o,o_DEF]>>
  SIMP_TAC (bool_ss) [Once WORD_ADD_COMM]>>
  qabbrev_tac `info=get_shmem_info q 0 [] []` >>
  first_x_assum $ assume_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  Cases_on `info` >>
  gvs[] >>
  `FST(get_shmem_info q c.pos [] []) = FST(get_shmem_info q 0 [] [])`
    by metis_tac[get_shmem_info_FST_eq] >>
  simp[] >>
  conj_tac >- (
    qexists_tac `LENGTH ffis` >>
    irule mmio_pcs_min_index_APPEND_thm >>
    gvs[] >>
    drule_then assume_tac get_shmem_info_MappedRead_or_MappedWrite >>
    gvs[] >>
    Cases_on `c.ffi_names` >>
    gvs[FILTER_NOT_MEM_Mapped]
  ) >>
  qspecl_then [`q`,`c.pos`,`[]`,`[]`] assume_tac get_shmem_info_FST_SND_LENGTH_eq >>
  gvs[] >>
  qpat_x_assum `MAP _ _ = DROP _ _` $
    assume_tac o Q.AP_TERM `LENGTH` >>
  gvs[LENGTH_MAP,LENGTH_DROP]
QED
*)

Theorem semantics_compile:
   mc_conf_ok mc_conf ∧
   (no_share_mem_inst code ==>
     compiler_oracle_ok coracle c'.labels (LENGTH bytes) c.asm_conf mc_conf.ffi_names) ∧
   good_code c.asm_conf c.labels code ∧
   c.asm_conf = mc_conf.target.config ∧
   c.labels = LN ∧ c.pos = 0 ∧
   compile c (code: 'a sec list) = SOME (bytes,c') ∧
   c'.ffi_names = SOME mc_conf.ffi_names /\
   good_init_state mc_conf ms bytes cbspace t m dm sdm io_regs cc_regs /\
   mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
   MAP (\rec. rec.entry_pc + mc_conf.target.get_pc ms) c'.shmem_extra =
    DROP i mc_conf.ffi_entry_pcs /\
   mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH c'.shmem_extra),
                              (MAP (\rec. (rec.nbytes, rec.access_addr, rec.reg,
                                           rec.exit_pc + mc_conf.target.get_pc ms))
                                   c'.shmem_extra)) ∧
  no_install_or_no_share_mem code mc_conf.ffi_names /\
  (* to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer *)
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a) /\
  (* the original ffi names provided does not contain MappedRead or MappedWrite *)
  (!ffis. c.ffi_names = SOME ffis ==> EVERY (λx. ∃s. x = ExtCall s) ffis ) ⇒
   implements' T (machine_sem mc_conf ffi ms)
     {semantics
        (make_init mc_conf ffi io_regs cc_regs t m (dm ∩ byte_aligned) (sdm ∩ byte_aligned) ms code
           compile (mc_conf.target.get_pc ms + n2w (LENGTH bytes))
           cbspace coracle)}
Proof
  rw[]>>
  match_mp_tac semanticsPropsTheory.implements'_trans>>
  qho_match_abbrev_tac`∃y. implements' T y {semantics (ss (dm ∩ byte_aligned))} ∧ P y` >>
  qexists_tac`{semantics (ss dm)}` >>
  `ss (dm ∩ byte_aligned) = align_dm (ss dm)` by (
    simp[align_dm_def,Abbr`ss`,make_init_def] ) \\

  pop_assum SUBST_ALL_TAC \\
  conj_tac >- (
    match_mp_tac implements_align_dm \\
    fs[mc_conf_ok_def] ) \\
  simp[Abbr`P`,Abbr`ss`] \\

        irule semanticsPropsTheory.implements'_trans>>
  qho_match_abbrev_tac`∃y. P y ∧ implements' T y {semantics (ss (sdm ∩ byte_aligned))}` >>
  qexists_tac`{semantics (ss sdm)}` >>
  `ss (sdm ∩ byte_aligned) = align_sdm (ss sdm)` by (
    simp[Abbr`ss`,make_init_def,align_sdm_def] ) \\

  pop_assum SUBST_ALL_TAC \\
  reverse conj_tac >- (
    match_mp_tac implements_align_sdm \\
    fs[mc_conf_ok_def] ) \\
  simp[Abbr`P`,Abbr`ss`] \\

  PURE_REWRITE_TAC[Once WORD_ADD_COMM] \\
  match_mp_tac semantics_compile_lemma \\
  fs[good_code_def]
QED

val _ = export_theory();
