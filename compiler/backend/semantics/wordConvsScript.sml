(*
  Syntactic properties used by wordLang across passes.
*)
Theory wordConvs
Ancestors
  wordLang asm reg_alloc
Libs
  preamble BasicProvers

val _ = temp_delsimps ["misc.max3_def"];
(*** Mono and conj lemmas for every_var/every_stack_var ***)
Theorem every_var_inst_mono:
  ∀P inst Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_inst P inst
  ⇒
  every_var_inst Q inst
Proof
  ho_match_mp_tac every_var_inst_ind>>srw_tac[][every_var_inst_def]>>
  Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def]
QED

Theorem every_var_exp_mono:
  ∀P exp Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_exp P exp
  ⇒
  every_var_exp Q exp
Proof
  ho_match_mp_tac every_var_exp_ind>>srw_tac[][every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]
QED

Theorem every_name_mono:
  ∀P names Q.
  (∀x. P x ⇒ Q x) ∧
  every_name P names ⇒ every_name Q names
Proof
  srw_tac[][every_name_def]>>
  metis_tac[EVERY_MONOTONIC]
QED

Theorem every_var_mono:
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_var P prog
  ⇒
  every_var Q prog
Proof
  ho_match_mp_tac every_var_ind>>srw_tac[][every_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[]>>PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[]>>TRY(Cases_on`x`)>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  metis_tac[EVERY_MONOTONIC,every_var_inst_mono,every_var_exp_mono,every_name_mono]
QED

(*Conjunct*)
Theorem every_var_inst_conj:
  ∀P inst Q.
  every_var_inst P inst ∧ every_var_inst Q inst ⇔
  every_var_inst (λx. P x ∧ Q x) inst
Proof
  ho_match_mp_tac every_var_inst_ind>>srw_tac[][every_var_inst_def]>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  metis_tac[]
QED

Theorem every_var_exp_conj:
  ∀P exp Q.
  every_var_exp P exp ∧ every_var_exp Q exp ⇔
  every_var_exp (λx. P x ∧ Q x) exp
Proof
  ho_match_mp_tac every_var_exp_ind>>srw_tac[][every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>
  metis_tac[]
QED

Theorem every_name_conj:
  ∀P names Q.
  every_name P names ∧ every_name Q names ⇔
  every_name (λx. P x ∧ Q x) names
Proof
  srw_tac[][every_name_def]>>
  metis_tac[EVERY_CONJ]
QED

Theorem every_var_conj:
  ∀P prog Q.
  every_var P prog  ∧ every_var Q prog ⇔
  every_var (λx. P x ∧ Q x) prog
Proof
  ho_match_mp_tac every_var_ind>>srw_tac[][every_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`x`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  TRY(metis_tac[EVERY_CONJ,every_var_inst_conj,every_var_exp_conj,every_name_conj])
QED

(*Similar lemmas about every_stack_var*)
Theorem every_var_imp_every_stack_var:
  ∀P prog.
  every_var P prog ⇒ every_stack_var P prog
Proof
  ho_match_mp_tac every_stack_var_ind>>
  srw_tac[][every_stack_var_def,every_var_def]>>
  Cases_on`ret`>>
  Cases_on`h`>>full_simp_tac(srw_ss())[]>>
  PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
  Cases_on`x'`>>Cases_on`r`>>full_simp_tac(srw_ss())[]
QED

Theorem every_stack_var_mono:
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_stack_var P prog
  ⇒
  every_stack_var Q prog
Proof
  ho_match_mp_tac every_stack_var_ind>>srw_tac[][every_stack_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[]>>PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[]>>TRY(Cases_on`x`>>Cases_on`r`>>full_simp_tac(srw_ss())[]))>>
  metis_tac[every_name_mono]
QED

Theorem every_stack_var_conj:
  ∀P prog Q.
  every_stack_var P prog  ∧ every_stack_var Q prog ⇔
  every_stack_var (λx. P x ∧ Q x) prog
Proof
  ho_match_mp_tac every_stack_var_ind>>srw_tac[][every_stack_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`x`>>Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(metis_tac[EVERY_CONJ,every_name_conj])
QED

(*** labels_rel ***)
Definition labels_rel_def:
  labels_rel old_labs new_labs <=>
    (ALL_DISTINCT old_labs ==> ALL_DISTINCT new_labs) /\
    set new_labs SUBSET set old_labs
End

Theorem labels_rel_refl[simp]:
   !xs. labels_rel xs xs
Proof
  fs [labels_rel_def]
QED

Theorem labels_rel_APPEND:
   labels_rel xs xs1 /\ labels_rel ys ys1 ==>
   labels_rel (xs++ys) (xs1++ys1)
Proof
  fs [labels_rel_def,ALL_DISTINCT_APPEND,SUBSET_DEF] \\ metis_tac []
QED

Theorem labels_rel_CONS =
   labels_rel_APPEND |> Q.GENL [`xs`, `xs1`] |> Q.SPECL [`[x]`, `[x1]`]
   |> SIMP_RULE std_ss [APPEND]

Theorem PERM_IMP_labels_rel:
   PERM xs ys ==> labels_rel ys xs
Proof
  fs [labels_rel_def] \\ rw [] \\ fs [SUBSET_DEF]
  \\ metis_tac [ALL_DISTINCT_PERM,MEM_PERM]
QED

Theorem labels_rel_TRANS:
  labels_rel xs ys /\ labels_rel ys zs ==> labels_rel xs zs
Proof
  fs [labels_rel_def] \\ rw [] \\ fs [SUBSET_DEF]
QED

(***
  Expressions in ShareInst must be Var or Op Add;
  No other expressions occur except in Set,
  where it must be a Var expr ***)
Definition flat_exp_conventions_def:
  (* These should be converted to Insts *)
  (flat_exp_conventions (Assign v exp) ⇔ F) ∧
  (flat_exp_conventions (Store exp num) ⇔ F) ∧
  (*The only place where top level (expression) vars are allowed*)
  (flat_exp_conventions (Set store_name (Var r)) ⇔ T) ∧
  (flat_exp_conventions (Set store_name _) ⇔ F) ∧
  (flat_exp_conventions (ShareInst op v (Var r)) ⇔ T) ∧
  (flat_exp_conventions (ShareInst op v (Op Add [Var r;Const c])) ⇔ T) ∧
  (flat_exp_conventions (ShareInst op v _) ⇔ F) ∧
  (flat_exp_conventions (Seq p1 p2) ⇔
    flat_exp_conventions p1 ∧ flat_exp_conventions p2) ∧
  (flat_exp_conventions (If cmp r1 ri e2 e3) ⇔
    flat_exp_conventions e2 ∧ flat_exp_conventions e3) ∧
  (flat_exp_conventions (MustTerminate p) ⇔ flat_exp_conventions p) ∧
  (flat_exp_conventions (Call ret dest args h) ⇔
    ((case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
        flat_exp_conventions ret_handler) ∧
    (case h of
      NONE => T
    | SOME (v,prog,l1,l2) => flat_exp_conventions prog))) ∧
  (flat_exp_conventions _ ⇔ T)
End

(*** Well-formed instructions. This also includes the FP conditions since we do not allocate them ***)
Definition inst_ok_less_def:
  (inst_ok_less (c:'a asm_config) (Arith (Binop b r1 r2 (Imm w))) ⇔
    c.valid_imm (INL b) w) ∧
  (inst_ok_less c (Arith (Shift l r1 r2 (Imm i))) ⇔
    (((i = 0w) ==> (l = Lsl)) ∧ w2n i < dimindex(:'a))) ∧
  (inst_ok_less c (Arith (Div r1 r2 r3)) ⇔
    (c.ISA ∈ {ARMv8; MIPS; RISC_V})) ∧
  (inst_ok_less c (Arith (LongMul r1 r2 r3 r4)) ⇔
    ((c.ISA = ARMv7 ⇒ r1 ≠ r2) ∧
    (c.ISA = ARMv8 ∨ c.ISA = RISC_V ∨ c.ISA = Ag32 ⇒ r1 ≠ r3 ∧ r1 ≠ r4))) ∧
  (inst_ok_less c (Arith (LongDiv r1 r2 r3 r4 r5)) =
    (c.ISA = x86_64)) ∧
  (inst_ok_less c (Arith (AddCarry r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3  ∧ r1 ≠ r4)) ∧
  (inst_ok_less c (Arith (AddOverflow r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3)) ∧
  (inst_ok_less c (Arith (SubOverflow r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3)) ∧
  (inst_ok_less c (Mem m r (Addr r' w)) ⇔
     if m IN {Load; Store; Load16; Store16; Load32; Store32}
     then addr_offset_ok c w
     else if m IN {Load16; Store16}
     then hw_offset_ok c w
     else byte_offset_ok c w) ∧
  (inst_ok_less c (FP (FPLess r d1 d2)) ⇔  fp_reg_ok d1 c ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPLessEqual r d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPEqual r d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c)  ∧
  (inst_ok_less c (FP (FPAbs d1 d2)) ⇔
    (c.two_reg_arith ==> (d1 <> d2)) ∧ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPNeg d1 d2)) ⇔
    (c.two_reg_arith ==> (d1 <> d2)) ∧ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPSqrt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPAdd d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPSub d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPMul d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPDiv d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPFma d1 d2 d3)) <=>
    (c.ISA = ARMv7) /\
    2 < c.fp_reg_count /\
    fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (inst_ok_less c (FP (FPMov d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPMovToReg r1 r2 d)) ⇔
      ((dimindex(:'a) = 32) ==> r1 <> r2) ∧ fp_reg_ok d c) ∧
  (inst_ok_less c (FP (FPMovFromReg d r1 r2)) ⇔
      ((dimindex(:'a) = 32) ==> r1 <> r2) ∧ fp_reg_ok d c) ∧
  (inst_ok_less c (FP (FPToInt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPFromInt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less _ _ = T)
End

(*** Instructions have distinct targets and read vars -- set by SSA form ***)
Definition distinct_tar_reg_def:
  (distinct_tar_reg (Arith (Binop bop r1 r2 ri))
    ⇔ ri ≠ Reg r1) ∧
  (distinct_tar_reg (Arith (AddCarry r1 r2 r3 r4))
    ⇔ r1 ≠ r3 ∧ r1 ≠ r4) ∧
  (distinct_tar_reg (Arith (AddOverflow r1 r2 r3 r4))
    ⇔ r1 ≠ r3) ∧
  (distinct_tar_reg (Arith (SubOverflow r1 r2 r3 r4))
    ⇔ r1 ≠ r3) ∧
  (distinct_tar_reg _ ⇔ T)
End

(***
  Instructions are 2 register code for arith ok
  Currently no two_reg for Mul and Div ***)
Definition two_reg_inst_def:
  (two_reg_inst (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (Shift l r1 r2 ri))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (AddCarry r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (AddOverflow r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (SubOverflow r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst _ ⇔ T)
End

(*** Recursor over instructions ***)
Definition every_inst_def:
  (every_inst P (Inst i) ⇔ P i) ∧
  (every_inst P (Seq p1 p2) ⇔ (every_inst P p1 ∧ every_inst P p2)) ∧
  (every_inst P (If cmp r1 ri c1 c2) ⇔ every_inst P c1 ∧ every_inst P c2) ∧
  (every_inst P (OpCurrHeap bop r1 r2) ⇔ P (Arith (Binop bop r1 r2 (Reg r2)))) ∧
  (every_inst P (MustTerminate p) ⇔ every_inst P p) ∧
  (every_inst P (Call ret dest args handler)
    ⇔ (case ret of
        NONE => T
      | SOME (n,names,ret_handler,l1,l2) => every_inst P ret_handler ∧
      (case handler of
        NONE => T
      | SOME (n,h,l1,l2) => every_inst P h))) ∧
  (every_inst P prog ⇔ T)
End

(*** Every instruction is well-formed ***)
Definition full_inst_ok_less_def:
  (full_inst_ok_less c (Inst i) ⇔ inst_ok_less c i) ∧
  (full_inst_ok_less c (Seq p1 p2) ⇔
    (full_inst_ok_less c p1 ∧ full_inst_ok_less c p2)) ∧
  (full_inst_ok_less c (If cmp r1 ri c1 c2) ⇔
    (full_inst_ok_less c c1 ∧ full_inst_ok_less c c2)) ∧
  (full_inst_ok_less c (MustTerminate p) ⇔ full_inst_ok_less c p) ∧
  (full_inst_ok_less c (Call ret dest args handler)
    ⇔ (case ret of
        NONE => T
      | SOME (n,names,ret_handler,l1,l2) => full_inst_ok_less c ret_handler ∧
      (case handler of
        NONE => T
      | SOME (n,h,l1,l2) => full_inst_ok_less c h))) ∧
  (full_inst_ok_less c (ShareInst op r ad) =
    case exp_to_addr ad of
    | SOME (Addr _ w) =>
      if op IN {Load; Store; Load32; Store32}
      then addr_offset_ok c w
      else if op IN {Load16; Store16}
      then hw_offset_ok c w
      else byte_offset_ok c w
    | NONE => F) ∧
  (full_inst_ok_less c prog ⇔ T)
End

(*** All cutsets are well-formed ***)
Definition wf_names_def:
  wf_names t =
    (wf (FST t) ∧ wf (SND t))
End

Definition wf_cutsets_def:
  (wf_cutsets (Alloc n s) = wf_names s) ∧
  (wf_cutsets (Install _ _ _ _ s) = wf_names s) ∧
  (wf_cutsets (Call ret dest args h) =
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      wf_names cutset ∧
      wf_cutsets ret_handler ∧
      (case h of
        NONE => T
      | SOME (v,prog,l1,l2) =>
        wf_cutsets prog))) ∧
  (wf_cutsets (FFI x1 y1 x2 y2 z args) = wf_names args) ∧
  (wf_cutsets (MustTerminate s) = wf_cutsets s) ∧
  (wf_cutsets (Seq s1 s2) =
    (wf_cutsets s1 ∧ wf_cutsets s2)) ∧
  (wf_cutsets (If cmp r1 ri e2 e3) =
    (wf_cutsets e2 ∧
     wf_cutsets e3)) ∧
  (wf_cutsets _ = T)
End

(*** Conventions for args to instructions ***)
Definition inst_arg_convention_def:
  (inst_arg_convention (Arith (AddCarry r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (inst_arg_convention (Arith (Shift _ _ _ (Reg r))) ⇔ r = 8) ∧
  (* Note: these are not necessary *)
  (inst_arg_convention (Arith (AddOverflow r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (inst_arg_convention (Arith (SubOverflow r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (inst_arg_convention (Arith (LongMul r1 r2 r3 r4)) ⇔ r1 = 6 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 4) ∧
  (* LongDiv follows conventions for x86 as it is the only possibility *)
  (inst_arg_convention (Arith (LongDiv r1 r2 r3 r4 r5)) ⇔ r1 = 0 ∧ r2 = 6 ∧ r3 = 6 ∧ r4 = 0) ∧
  (inst_arg_convention _ = T)
End

(*** Calling conventions ***)
Definition call_arg_convention_def:
  (call_arg_convention (Inst i) =
    inst_arg_convention i) ∧
  (call_arg_convention (Return x ys) = (ys = GENLIST (\x.2*(x+1)) (LENGTH ys))) ∧
  (call_arg_convention (Raise y) = (y=2)) ∧
  (call_arg_convention (Install ptr len _ _ _) = (ptr = 2 ∧ len = 4)) ∧
  (call_arg_convention (FFI x ptr len ptr2 len2 args) = (ptr = 2 ∧ len = 4 ∧
                                                         ptr2 = 6 ∧ len2 = 8)) ∧
  (call_arg_convention (Alloc n s) = (n=2)) ∧
  (call_arg_convention (StoreConsts a b c d ws) =
    ((a=0) ∧ (b=2) ∧ (c=4) ∧ (d=6))) ∧
  (call_arg_convention (Call ret dest args h) =
    (case ret of
      NONE => args = GENLIST (\x.2*x) (LENGTH args)
    | SOME (vs,cutset,ret_handler,l1,l2) =>
      args = GENLIST (\x.2*(x+1)) (LENGTH args) ∧
      (vs = GENLIST (\x.2*(x+1)) (LENGTH vs)) ∧ call_arg_convention ret_handler ∧
    (case h of  (*Does not check the case where Calls are ill-formed*)
      NONE => T
    | SOME (v,prog,l1,l2) =>
      (v = 2) ∧ call_arg_convention prog))) ∧
  (call_arg_convention (MustTerminate s1) =
    call_arg_convention s1) ∧
  (call_arg_convention (Seq s1 s2) =
    (call_arg_convention s1 ∧ call_arg_convention s2)) ∧
  (call_arg_convention (If cmp r1 ri e2 e3) =
    (call_arg_convention e2 ∧
     call_arg_convention e3)) ∧
  (call_arg_convention p = T)
End

(*** Before allocation, generated by SSA CC ***)
Definition pre_alloc_conventions_def:
  pre_alloc_conventions p =
    (every_stack_var is_stack_var p ∧
    call_arg_convention p)
End

(*** After allocation, generated by allocator and/or the oracles ***)
Definition post_alloc_conventions_def:
  post_alloc_conventions k prog =
    (every_var is_phy_var prog ∧
    every_stack_var (λx. x ≥ 2*k) prog ∧
    call_arg_convention prog)
End

(*** This is for label preservation -- wordLang shouldn't need to inspect the labels explicitly. ***)
Definition extract_labels_def:
  (extract_labels (Call ret dest args h) =
    (case ret of
      NONE => []
    | SOME (v,cutset,ret_handler,l1,l2) =>
      let ret_rest = extract_labels ret_handler in
    (case h of
      NONE => [(l1,l2)] ++ ret_rest
    | SOME (v,prog,l1',l2') =>
      let h_rest = extract_labels prog in
      [(l1,l2);(l1',l2')]++ret_rest++h_rest))) ∧
  (extract_labels (MustTerminate s1) = extract_labels s1) ∧
  (extract_labels (Seq s1 s2) =
    extract_labels s1 ++ extract_labels s2) ∧
  (extract_labels (If cmp r1 ri e2 e3) =
    (extract_labels e2 ++ extract_labels e3)) ∧
  (extract_labels _ = [])
End

(*** Property on max_var ***)
Theorem max_var_exp_IMP[local]:
  ∀exp.
  P 0 ∧ every_var_exp P exp ⇒
  P (max_var_exp exp)
Proof
  ho_match_mp_tac max_var_exp_ind>>fs[max_var_exp_def,every_var_exp_def]>>
  srw_tac[][]
  >- (match_mp_tac MAX_LIST_intro>> fs[EVERY_MAP,EVERY_MEM])
  >> metis_tac [MAX_CASES]
QED

Theorem max_var_intro:
  ∀prog.
  P 0 ∧ every_var P prog ⇒
  P (max_var prog)
Proof
  ho_match_mp_tac max_var_ind >> rpt strip_tac
  >~ [`Inst`]
  >- (fs[every_var_def,max_var_def,max_var_exp_IMP] >>
      rpt $ pop_assum mp_tac >>
      MAP_EVERY qid_spec_tac $ List.rev [`P`,`i`] >>
      ho_match_mp_tac every_var_inst_ind >> rpt strip_tac >>
      fs[every_var_inst_def,max_var_inst_def] >>
      simp_tac(pure_ss)[MAX_DEF,max3_def] >>
      rpt TOP_CASE_TAC >> fs[] >> fs[every_var_imm_def])
  (*Remaining cases*)
  >> fs[every_var_def,max_var_def,max_var_exp_IMP] >>
  simp_tac(pure_ss)[MAX_DEF,max3_def] >>
  rpt TOP_CASE_TAC >> fs[] >>
  TRY (MAP_FIRST irule [MAX_LIST_intro,max_var_exp_IMP]) >>
  fs[] >> fs[every_name_def,every_var_imm_def]
QED

(*** code_labels ***)
Definition get_code_labels_def[simp]:
  (get_code_labels (Call r d a h) =
    (case d of SOME x => {x} | _ => {}) ∪
    (case r of SOME (_,_,x,_,_) => get_code_labels x | _ => {}) ∪
    (case h of SOME (_,x,l1,l2) => get_code_labels x | _ => {})) ∧
  (get_code_labels (Seq p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (If _ _ _ p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (MustTerminate p) = get_code_labels p) ∧
  (get_code_labels (LocValue _ l1) = {l1}) ∧
  (get_code_labels _ = {})
End

(*** TODO: This seems like it must have been established before
  handler labels point only within the current table entry
***)
Definition good_handlers_def[simp]:
  (good_handlers n (Call r d a h) <=>
    case r of
      NONE => T
    | SOME (_,_,x,_,_) => good_handlers n x ∧
    (case h of SOME (_,x,l1,_) => l1 = n ∧ good_handlers n x | _ => T)) ∧
  (good_handlers n (Seq p1 p2) <=> good_handlers n p1 ∧ good_handlers n p2) ∧
  (good_handlers n (If _ _ _ p1 p2) <=> good_handlers n p1 ∧ good_handlers n p2) ∧
  (good_handlers n (MustTerminate p) <=> good_handlers n p) ∧
  (good_handlers n _ <=> T)
End

Definition good_code_labels_def:
  good_code_labels p elabs ⇔
  EVERY (λ(n,m,pp). good_handlers n pp) p ∧
  (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) ⊆
  (set (MAP FST p) ∪ elabs)
End

(*** not_created_subprogs ***)

(* Examines various syntactic elements within programs that some phases are
   expected to possibly remove but not create. *)
Definition not_created_subprogs_def:
  not_created_subprogs P (MustTerminate p : 'a prog) =
    (P (MustTerminate (Skip : 'a prog)) /\ not_created_subprogs P p) /\
  not_created_subprogs P (Seq p1 p2) = (not_created_subprogs P p1 /\
    not_created_subprogs P p2) /\
  not_created_subprogs P (If _ _ _ p1 p2) = (not_created_subprogs P p1 /\
    not_created_subprogs P p2) /\
  not_created_subprogs P (wordLang$Call r dest args h) =
    (P (wordLang$Call NONE dest [] NONE) /\
    (case r of NONE => T | SOME (_, _, p, _) => not_created_subprogs P p) /\
    (case h of NONE => T | SOME (_, p, h1, _) =>
        P (wordLang$Call NONE NONE [] (SOME (0, Skip, h1, 0))) /\
        not_created_subprogs P p)) /\
  not_created_subprogs P (Alloc _ _) = P (Alloc 0 (LN,LN)) /\
  not_created_subprogs P (LocValue _ l) = P (LocValue 0 l) /\
  not_created_subprogs P (ShareInst _ _ _) = P (ShareInst ARB 0 (Var 0)) /\
  not_created_subprogs P (Install _ _ _ _ _) = P (Install 0 0 0 0 (LN,LN)) /\
  not_created_subprogs _ _ = T
End

Theorem not_created_subprogs_P_def = not_created_subprogs_def
  |> BODY_CONJUNCTS
  |> map (fn t => GEN (hd (snd (strip_comb (lhs (concl t))))) t)
  |> map (Q.SPEC `P`) |> LIST_CONJ
  |> Q.GEN `P`

(* no_alloc specialisation *)

val no_alloc_P = ``((<>) (Alloc 0 (LN,LN)))``

Definition no_alloc_subprogs_def:
  no_alloc p = not_created_subprogs ^no_alloc_P p
End

Theorem no_alloc_def = not_created_subprogs_P_def
  |> ISPEC no_alloc_P
  |> REWRITE_RULE [GSYM no_alloc_subprogs_def]

val no_install_P = ``((<>) (Install 0 0 0 0 (LN,LN)))``

Definition no_install_subprogs_def:
  no_install p = not_created_subprogs ^no_install_P p
End

Theorem no_install_def = not_created_subprogs_P_def
  |> ISPEC no_install_P
  |> REWRITE_RULE [GSYM no_install_subprogs_def]

(****** no_mt : no MustTerminate ******)

val no_mt_P = ``((<>) (MustTerminate Skip))``

Definition no_mt_subprogs_def:
  no_mt p = not_created_subprogs ^no_mt_P p
End

Theorem no_mt_def = not_created_subprogs_P_def
  |> ISPEC no_mt_P
  |> REWRITE_RULE [GSYM no_mt_subprogs_def]

(* no_share_inst: no ShareInst *)

val no_share_inst_P = ``((<>) (ShareInst ARB 0 (Var 0)))``

Definition no_share_inst_subprogs_def:
  no_share_inst p = not_created_subprogs ^no_share_inst_P p
End

Theorem no_share_inst_def = not_created_subprogs_P_def
  |> ISPEC no_share_inst_P
  |> REWRITE_RULE [GSYM no_share_inst_subprogs_def]

Overload word_get_code_labels = ``wordConvs$get_code_labels``
Overload word_good_handlers = ``wordConvs$good_handlers``
Overload word_good_code_labels = ``wordConvs$good_code_labels``
