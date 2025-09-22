(*
  Correctness proof for compilation from stackLang to wasmLang
*)
Theory stack_to_wasmProof
Ancestors
  wasmLang words arithmetic list rich_list sptree mlstring
  wasmSem stackSem stackLang pair
Libs
  wordsLib helperLib markerLib BasicProvers

(* compiler definition (TODO: move to another file when ready) *)

(* shorthands for wasm instructions *)
Definition I64_EQ_def:
  I64_EQ = Numeric (N_compare (Eq Int W64))
End
Definition I64_NE_def:
  I64_NE = Numeric (N_compare (Ne Int W64))
End
Definition I64_CONST_def:
  I64_CONST w = Numeric (N_const64 Int w)
End
Definition I32_CONST_def:
  I32_CONST w = Numeric (N_const32 Int w)
End
Definition I64_ADD_def:
  I64_ADD = Numeric (N_binary (Add Int W64))
End
Definition I64_SUB_def:
  I64_SUB = Numeric (N_binary (Sub Int W64))
End
Definition I64_AND_def:
  I64_AND = Numeric (N_binary (And W64))
End
Definition I64_OR_def:
  I64_OR = Numeric (N_binary (Or W64))
End
Definition I64_XOR_def:
  I64_XOR = Numeric (N_binary (Xor W64))
End
Definition I64_SHL_def:
  I64_SHL = Numeric (N_binary (Shl W64))
End
Definition I64_SHR_S_def:
  I64_SHR_S = Numeric (N_binary (Shr_ Signed W64))
End
Definition I64_SHR_U_def:
  I64_SHR_U = Numeric (N_binary (Shr_ Unsigned W64))
End
Definition I64_ROTR_def:
  I64_ROTR = Numeric (N_binary (Rotr W64))
End
Definition I64_DIV_S_def:
  I64_DIV_S = Numeric (N_binary (Div_ Signed W64))
End
Definition I64_DIV_U_def:
  I64_DIV_U = Numeric (N_binary (Div_ Unsigned W64))
End
Definition GLOBAL_GET_def:
  GLOBAL_GET i = Variable (GlobalGet (n2w i))
End
Definition GLOBAL_SET_def:
  GLOBAL_SET i = Variable (GlobalSet (n2w i))
End

(* reg_imm = Reg reg | Imm ('a imm) *)
Definition comp_ri_def:
  comp_ri (Reg r) = GLOBAL_GET r ∧
  comp_ri (Imm n) = I64_CONST n
End

(* cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest *)
Definition comp_cmp_def:
  comp_cmp (Equal: cmp) a_r b_ri =
    List [GLOBAL_GET a_r; comp_ri b_ri; I64_EQ]
End

(*
  arith = Binop binop reg reg ('a reg_imm)
        | Shift shift reg reg num
        | Div reg reg reg
        | LongMul reg reg reg reg (* use multiword thy *)
        | LongDiv reg reg reg reg reg
        | AddCarry reg reg reg reg
        | AddOverflow reg reg reg reg
        | SubOverflow reg reg reg reg

  binop = Add | Sub | And | Or | Xor

  shift = Lsl | Lsr | Asr | Ror
*)
Definition compile_arith_def:
(
  compile_arith (asm$Binop op t s1 s2) =
    let wasm_op =
      case op of
        Add => I64_ADD
      | Sub => I64_SUB
      | And => I64_AND
      | Or  => I64_OR
      | Xor => I64_XOR
    in
    List [GLOBAL_GET s1; comp_ri s2; wasm_op; GLOBAL_SET t]
) ∧
(
  compile_arith (asm$Shift op t s n) =
(*
  | (* inn *) Shl        width
  | (* inn *) Shr_ sign  width
  | (* inn *) Rotl       width
  | (* inn *) Rotr       width
*)
    let wasm_op =
      case op of
        Lsl => I64_SHL
      | Lsr => I64_SHR_U
      | Asr => I64_SHR_S
      | Ror => I64_ROTR
    in
    List [GLOBAL_GET s; I64_CONST (n2w n); wasm_op; GLOBAL_SET t]
) ∧
(
  compile_arith (asm$Div t s1 s2) = (* signed div *)
    List [GLOBAL_GET s1; GLOBAL_GET s2; I64_DIV_S; GLOBAL_SET t]
)
End



Definition compile_inst_def:
  compile_inst (asm$Skip) = List [] ∧
  compile_inst (asm$Const (r:reg) (v:64 word)) =
    List [I64_CONST v; GLOBAL_SET r] ∧
  compile_inst (asm$Arith a) = compile_arith a
End



Definition compile_def:
  compile stackLang$Skip = List ([]:wasmLang$instr list) ∧
  compile (Seq p1 p2) = Append (compile p1) (compile p2) ∧
  (* If cmp num ('a reg_imm) stackLang$prog stackLang$prog *)
  (* no values are left on the wasm operand stack, hence BlkNil *)
  compile (stackLang$If cmp a_r b_ri p1 p2) =
    Append (comp_cmp cmp a_r b_ri)
           (List [wasmLang$If BlkNil (append (compile p1)) (append (compile p2))])
  ∧
  compile (stackLang$Inst inst) = compile_inst inst
End

(* definitions used in the correctness statement *)

val s = “s:(64,'c,'ffi) stackSem$state”
val t = “t:wasmSem$state”

Definition empty_buffer_def:
  empty_buffer b ⇔
    b.position = 0w ∧
    b.buffer = [] ∧
    b.space_left = 0
End

Definition to_value_def:
  to_value (Word w) = I64 w ∧
  to_value (Loc l _) = I64 (n2w l << 1)
End

Definition regs_rel_def:
  regs_rel regs globals <=>
    32 <= LENGTH globals (* no. of avail. regs. of wasm backend *) ∧
    LENGTH globals < 4294967296 (* 2**32; wasm binary encoding *) ∧
    ∀n wl. FLOOKUP regs n = SOME wl ==> EL n globals = to_value wl
End


(* code_rel: we can find long mul at const index i *)


Definition state_rel_def:
  state_rel ^s ^t ⇔
    ¬ s.use_stack ∧ ¬ s.use_store ∧ ¬ s.use_alloc ∧ ¬ s.be ∧
    empty_buffer s.code_buffer ∧ empty_buffer s.data_buffer ∧
    regs_rel s.regs t.globals (* ∧ code_rel s.code t.code *)
End

Definition res_rel_def:
  (res_rel NONE r     ⇔ r = RNormal) ∧
  (res_rel (SOME v) r ⇔ r ≠ RNormal ∧ ∀l. r ≠ RBreak l (* TODO: fix *))
End

(* set up for one theorem per case *)

val goal_tm =
  “λ(p,^s). ∀res s1 t.
     evaluate (p,s) = (res,s1) ∧
     state_rel s t ∧ (* syntax_ok p ∧ *)
     res ≠ SOME Error ⇒
     ∃ck t1 res1.
       exec_list (append (compile p)) (t with clock := t.clock + ck) = (res1,t1) ∧
       res_rel res res1 ∧
       state_rel s1 t1 ∧
       (res1 = RNormal ==> t1.stack = t.stack)
  ”

local
  val ind_thm = stackSemTheory.evaluate_ind |> ISPEC goal_tm
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s =
    first (can (find_term (can (match_term (Term [QUOTE ("stackLang$"^s)]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

(* Lemmas *)

Theorem exec_list_append:
  ∀xs ys s.
    exec_list (xs ++ ys) s =
    let (res,s1) = exec_list xs s in
    if res = RNormal then exec_list ys s1
    else (res,s1)
Proof
  Induct_on‘xs’>>rw[exec_def]
  >>rpt(pairarg_tac>>fs[])
  >>gvs[AllCaseEqs()]
  >>first_x_assum $ qspecl_then[‘[]’,‘s'’]assume_tac
  >>gvs[]
  >>Cases_on‘res'=RNormal’>>fs[]
QED

Theorem exec_list_cons:
  exec_list (i::rest) s =
    let (res1,s1) = exec i s in
    if res1=RNormal then exec_list rest s1
    else (res1,s1)
Proof
rw[exec_def]
>>rpt(pairarg_tac>>fs[])
>>(PURE_TOP_CASE_TAC>>fs[])
QED

Theorem pop_with_clock[simp]:
  pop (s with clock:=c) = OPTION_MAP (I ## \t. t with clock:=c) (pop s)
Proof
  rw[pop_def]>>PURE_TOP_CASE_TAC>>fs[]
QED

Theorem pop_n_with_clock[simp]:
  pop_n n (s with clock:=c) = OPTION_MAP (I ## \t. t with clock:=c) (pop_n n s)
Proof
  rw[pop_n_def]
QED

Theorem pop_i32_with_clock[simp]:
  pop_i32 (s with clock:=c) = OPTION_MAP (I ## \t. t with clock:=c) (pop_i32 s)
Proof
  rw[pop_i32_def]>>rpt(PURE_TOP_CASE_TAC>>fs[])
QED

Theorem pop_i32_clock:
  pop_i32 s = SOME (x,s') ==> s'.clock = s.clock
Proof
  gvs[pop_i32_def,AllCaseEqs()]
  \\ rpt strip_tac
  \\ rw[]
QED

Theorem set_local_with_clock[simp]:
  set_local n x (s with clock:=c) =
  OPTION_MAP (\t. t with clock:=c) (set_local n x s)
Proof
  rw[set_local_def]
QED

Theorem set_local_clock:
  set_local n x s = SOME t ==> t.clock = s.clock
Proof
  rw[set_local_def]
  >>simp[state_component_equality]
QED

Theorem set_global_with_clock[simp]:
  set_global n x (s with clock:=c) =
  OPTION_MAP (\t. t with clock:=c) (set_global n x s)
Proof
  rw[set_global_def]
QED

Theorem set_global_clock:
  set_global n x s = SOME t ==> t.clock = s.clock
Proof
  rw[set_global_def]
  >>simp[state_component_equality]
QED

Theorem OPTION_CASE_OPTION_MAP:
  (option_CASE (OPTION_MAP f a) e g) = option_CASE a e (λx. g (f x))
Proof
  Cases_on `a`
  >> fs[]
QED

Theorem PAIR_CASE_PAIR_MAP:
  pair_CASE ((f ## g) e) h = case e of (x,y) => h(f x)(g y)
Proof
  Cases_on`e`>>simp[]
QED

Theorem exec_list_add_clock_aux:
( ∀c s res s1.
  exec c s = (res,s1) ∧ res ≠ RTimeout ==>
  ∀ck. exec c (s with clock := ck + s.clock) =
       (res, s1 with clock := ck + s1.clock)
) ∧
( ∀c s res s1.
  exec_list c s = (res,s1) ∧ res ≠ RTimeout ==>
  ∀ck. exec_list c (s with clock := ck + s.clock) =
       (res, s1 with clock := ck + s1.clock)
)
Proof
ho_match_mp_tac exec_ind>>rpt strip_tac
>~[`Unreachable`]
>-fs[exec_def]
>~[`Nop`]
>-fs[exec_def]
>~[`Block`]
>-(
  qpat_x_assum `exec _ _ = _` mp_tac
  >>simp[exec_def]
  >>(pairarg_tac>>fs[])
  >>(IF_CASES_TAC>>simp[])
  >>rpt(pairarg_tac>>fs[])
  >>(Cases_on`res'=RTimeout`>>gvs[AllCaseEqs()])
  >>rw[]
)
>~[‘Loop’]
>-(
  qpat_x_assum `exec _ _ = _` mp_tac
  >>once_rewrite_tac[exec_def]
  >>simp[]
  >>rpt(pairarg_tac>>fs[])
  >>(IF_CASES_TAC>>simp[])
  >>(Cases_on`res'=RTimeout`>>gvs[AllCaseEqs()])
  >>rw[]
)
>~[‘If’]
>-(
  qpat_x_assum `exec _ _ = _` mp_tac
  >>once_rewrite_tac[exec_def]
  >>simp[CaseEqs["prod","option"]]
  >>rw[]>-metis_tac[pop_clock]
  >>fs[]
  >>metis_tac[pop_clock]
)
>~[‘Br’]
>-fs[exec_def]
>~[‘BrIf’]
>-(
  fs[exec_def]
  >>(Cases_on`s.stack`>>fs[pop_def])
  >>(PURE_TOP_CASE_TAC>>gvs[state_accfupds])
  >>(IF_CASES_TAC>>gvs[state_accfupds])
)
>~[‘BrTable’]
>-(
  fs[exec_def]
  >>(Cases_on`s.stack`>>fs[pop_def])
  >>(PURE_TOP_CASE_TAC>>gvs[state_accfupds])
)
>~[‘Return’]
>-fs[exec_def]
>~[‘ReturnCall’]
>-(
  fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(Cases_on`pop_n (LENGTH q) s`>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>imp_res_tac pop_n_clock
  >>(Cases_on`s.clock=0`>>fs[])
  >>rpt(pairarg_tac>>fs[])
  >>gvs[AllCaseEqs()]
)
>~[‘ReturnCallIndirect’]
>-(
  fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>gvs[])
  >>(PURE_TOP_CASE_TAC>>gvs[])
  >>drule pop_clock
  >>strip_tac
  >>rpt(PURE_TOP_CASE_TAC>>gvs[])
)
>~[‘Call’]
>-(
  qpat_x_assum`exec _ _ = _`mp_tac
  >>simp[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>imp_res_tac pop_n_clock
  >>gvs[]
  >>(IF_CASES_TAC>>fs[])
  >>rpt(pairarg_tac>>fs[])
  >>(Cases_on`res'=RTimeout`>>fs[])
  >>first_x_assum $ qspec_then`ck`SUBST_ALL_TAC
  >>gvs[AllCaseEqs()]
  >>rw[]
)
>~[‘CallIndirect’]
>-(
  qpat_x_assum`exec _ _ = _`mp_tac
  >>fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>imp_res_tac pop_clock
  >>(PURE_TOP_CASE_TAC>>fs[])>-metis_tac[]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>metis_tac[]
)
>~[`Numeric`]
>-(
  fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>rpt VAR_EQ_TAC
  >>simp[]
)
>~[`Parametric Drop`]
>-(
  fs[exec_def]
  >>Cases_on`pop s`>>fs[]
  >>(split_pair_case_tac>>gvs[])
  >>metis_tac[pop_clock]
)
>~[`Parametric Select`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>fs[push_def]
  >>rpt(PURE_TOP_CASE_TAC>>fs[])
  >>(imp_res_tac pop_clock>>gvs[])
)
>~[`LocalGet`]
>-(
  fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>gvs[push_def]
)
>~[`LocalSet`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>imp_res_tac pop_clock
  >>(PURE_TOP_CASE_TAC>>gvs[])
  >>metis_tac[set_local_clock]
)
>~[`LocalTee`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>(split_pair_case_tac>>gvs[])
  >>imp_res_tac pop_clock
  >>(PURE_TOP_CASE_TAC>>gvs[])
  >>metis_tac[set_local_clock]
)
>~[`GlobalGet`]
>-(
  fs[exec_def]
  >>(PURE_TOP_CASE_TAC>>fs[])
  >>fs[push_def]
  >>gvs[state_component_equality]
)
>~[`GlobalSet`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>(PURE_TOP_CASE_TAC>>fs[]>>split_pair_case_tac>>gvs[]>>imp_res_tac pop_clock)
  >>(PURE_TOP_CASE_TAC>>fs[]>-gvs[state_component_equality])
  >>metis_tac[set_global_clock]
)
>~[`MemRead`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>(PURE_TOP_CASE_TAC>>fs[]>>split_pair_case_tac>>gvs[]>>imp_res_tac pop_i32_clock)
  >>(PURE_TOP_CASE_TAC>>gvs[])
)
>~[`MemWrite`]
>-(
  fs[exec_def]
  >>simp[OPTION_CASE_OPTION_MAP,PAIR_CASE_PAIR_MAP]
  >>(PURE_TOP_CASE_TAC>>fs[]>>split_pair_case_tac>>gvs[]>>imp_res_tac pop_clock)
  >>(PURE_TOP_CASE_TAC>>gvs[]>>split_pair_case_tac>>gvs[]>>imp_res_tac pop_i32_clock)
  >>(PURE_TOP_CASE_TAC>>gvs[])
)
>-fs[exec_def]
>-(
  fs[exec_def]
  >>rpt(pairarg_tac>>fs[])
  >>(Cases_on`res''=RTimeout`>>fs[])
  >>first_x_assum $ qspec_then`ck`SUBST_ALL_TAC
  >>gvs[AllCaseEqs()]
)
QED

Theorem exec_list_add_clock:
  exec_list c s = (res,s1) ∧ res ≠ RTimeout ==>
  ∀ck. exec_list c (s with clock := ck + s.clock) =
       (res, s1 with clock := ck + s1.clock)
Proof
  metis_tac[exec_list_add_clock_aux]
QED

Theorem comp_cmp_thm:
  get_var a s = SOME va ∧
  get_var_imm b s = SOME vb ∧
  labSem$word_cmp cmp va vb = SOME v ∧
  state_rel ^s ^t ==>
  exec_list (append (comp_cmp cmp a b)) (t with clock := ck) =
    (RNormal, push (I32 (b2w v)) (t with clock := ck))
Proof
  cheat
QED

Theorem pop_push:
  pop (push v t) = SOME (v,t)
Proof
  rw[push_def,pop_def,wasmSemTheory.state_component_equality]
QED

Theorem nonzero_b2w:
  nonzero (I32 (b2w v)) = SOME v
Proof
  Cases_on‘v’>>rw[nonzero_def]
QED

(* a proof for each case *)

Theorem compile_Skip:
  ^(get_goal "Skip")
Proof
  rpt strip_tac
  \\ gvs [compile_def,exec_def,stackSemTheory.evaluate_def]
  \\ simp [res_rel_def]
  \\ qexists_tac ‘0’ \\ fs [state_rel_def]
QED

fun component_equality_of ty = let
val accfn_terms = map (fn (_, rcd) => #accessor rcd) (TypeBase.fields_of ty)
val cases_thm =  TypeBase.nchotomy_of ty
val oneone_thm = TypeBase.one_one_of ty
val accessor_thms = TypeBase.accessors_of ty
    val var1 = mk_var("a", ty)
    val var2 = mk_var("b", ty)
    val lhs = mk_eq(var1, var2)
    val rhs_tms =
      map (fn tm => mk_eq(mk_comb(tm, var1), mk_comb(tm, var2)))
      accfn_terms
    val rhs = list_mk_conj rhs_tms
    val goal = mk_eq(lhs, rhs)
    val tactic =
      REPEAT GEN_TAC THEN
      MAP_EVERY (STRUCT_CASES_TAC o C SPEC cases_thm) [var1, var2] THEN
      REWRITE_TAC (oneone_thm::accessor_thms)
    in prove(goal, tactic) end

fun trivial_simps ty =
let
val t = mk_var ("t", ty)
fun f accessor fupd fty =
(* fupd (K (accessor t)) *)
let val lhs =
mk_comb (mk_comb (fupd, mk_comb (mk_const("K",fty-->fty-->fty), mk_comb (accessor, t))), t)
in
prove (mk_eq (lhs, t), simp[component_equality_of ty])
end
in
map (fn (_, {accessor=accessor, fupd=fupd, ty=ty}) => f accessor fupd ty) (TypeBase.fields_of ty)
end

(* BANNED *)
(*
val _ = save_thm("state_trivial_simps[simp]", LIST_CONJ (trivial_simps ``:wasmSem$state``));
*)

Theorem state_trivial_simps[simp] = LIST_CONJ (trivial_simps ``:wasmSem$state``);

Theorem compile_Inst:
  ^(get_goal "Inst")
Proof
rw[compile_def]
>>qexists_tac`0`
>>(Cases_on`i`>>fs[compile_inst_def])
>-(
  fs[evaluate_def,inst_def]
  >>fs[exec_def,res_rel_def]
  >>gvs[]
)
(* Const *)
>-(
  fs[evaluate_def,inst_def]
  >>fs[assign_def]
  >>gvs[CaseEq"option"]
  >>fs[exec_list_cons]
  >>rpt(pairarg_tac>>fs[])
  >>rename1`exec (I64_CONST c) t = (res1,t1)`
  >>rename1`exec (GLOBAL_SET n) t1 = (res2,t2)`
  >>subgoal`res1=RNormal∧res2=RNormal`
  >-(
    fs[I64_CONST_def,GLOBAL_SET_def,exec_def]
    >>gvs[num_stk_op_def]
    >>fs[pop_def]
    >>fs[set_global_def]
    >>`n MOD 4294967296 < LENGTH t.globals` by cheat (* use names_ok? stack_asm_name? *)
    >>fs[]
  )
  >>fs[exec_def,res_rel_def]
  (*
      0.  word_exp s (Const c) = SOME w
      1.  state_rel s t
      2.  exec (I64_CONST c) t = (RNormal,t1)
      3.  exec (GLOBAL_SET n) t1 = (RNormal,t2)
      4.  res1 = RNormal
      5.  res2 = RNormal
     ------------------------------------
          state_rel (set_var n (Word w) s) t2 ∧ t2.stack = t.stack
  *)
  >>fs[I64_CONST_def,GLOBAL_SET_def,exec_def]
  >>gvs[AllCaseEqs()]
  >>gvs[num_stk_op_def]
  >>gvs[pop_def]
  >>gvs[set_global_def]
  `n < LENGTH t.globals` by cheat(*syntactic*)
`LENGTH t.globals < 4294967296` by cheat(*global*)


  >>cheat
)

QED

Theorem compile_Seq:
  ^(get_goal "Seq")
Proof
  rpt gen_tac
  >>strip_tac
  >>rw[evaluate_def]
  >>rpt(pairarg_tac>>fs[])
  >>simp[compile_def]
  >>simp[exec_list_append]
  >>rename[‘_ = (res_mid, s_mid)’]
  >>reverse $ Cases_on‘res_mid’
  >-(
    gvs[]
    >>last_x_assum drule
    >>strip_tac
    >>qexists_tac‘ck’
    >>simp[]
    >>fs[res_rel_def]
  )
  >>gvs[]
  >>last_x_assum $ ASSUME_NAMED_TAC "H1"
  >>qpat_x_assum ‘∀t'. _’ $ ASSUME_NAMED_TAC "H2"
  >>LABEL_X_ASSUM "H2" drule
  >>strip_tac
  >>drule exec_list_add_clock
  >>gvs[res_rel_def]
  >>LABEL_X_ASSUM "H1" drule
  >>rpt strip_tac
  >>pop_assum $ qspec_then ‘ck'’ assume_tac
  >>qexists_tac‘ck+ck'’
  >>fs[]
QED

Theorem state_rel_with_stack:
  state_rel s (t with stack := st) = state_rel s t
Proof
  fs[state_rel_def]
QED
(* delsimps["state_rel_with_stack"] *)

Theorem compile_If:
  ^(get_goal "If")
Proof
  rpt strip_tac
  >>fs[evaluate_def]
  >>gvs[CaseEq"option"]
  >>simp[compile_def]
  >>simp[exec_list_append]
  >>drule_all comp_cmp_thm
  >>strip_tac
  >>simp[]
  >>pop_assum kall_tac
  >>simp[exec_def,pop_push]
  >>simp[nonzero_b2w]
  >>simp[functype_of_blocktype_def]
  >>‘state_rel s (t with stack:=[])’ by simp[state_rel_with_stack]
  >>IF_CASES_TAC>>gvs[]>>first_x_assum drule>>strip_tac
  >>(
    qexists_tac‘ck’
    >>fs[]
    >>Cases_on‘res’>>fs[res_rel_def]
    >>simp[state_rel_with_stack]
    >>Cases_on‘res1’>>gvs[]
  )
QED

Theorem compile_While:
  ^(get_goal "While")
Proof
  cheat
QED

Theorem compile_Call:
  ^(get_goal "Call")
Proof
  cheat
QED

Theorem compile_JumpLower:
  ^(get_goal "JumpLower")
Proof
  cheat
QED

Theorem compile_Raise:
  ^(get_goal "Raise")
Proof
  cheat
QED

Theorem compile_Return:
  ^(get_goal "Return")
Proof
  cheat
QED

Theorem compile_FFI:
  ^(get_goal "FFI")
Proof
  cheat
QED

Theorem compile_Tick:
  ^(get_goal "Tick")
Proof
  cheat
QED

Theorem compile_LocValue:
  ^(get_goal "LocValue")
Proof
  cheat
QED

Theorem compile_BitmapLoad:
  ^(get_goal "BitmapLoad")
Proof
  cheat
QED

Theorem compile_Halt:
  ^(get_goal "Halt")
Proof
  cheat
QED

Theorem compile_Install: (* will be banned *)
  ^(get_goal "Install")
Proof
  cheat
QED

Theorem compile_ShMemOp: (* will be banned *)
  ^(get_goal "ShMemOp")
Proof
  cheat
QED

Theorem compile_RawCall: (* will be banned *)
  ^(get_goal "RawCall")
Proof
  cheat
QED

Theorem compile_CodeBufferWrite:
  ^(get_goal "CodeBufferWrite")
Proof
  rw [evaluate_def,wordSemTheory.buffer_write_def]
  \\ fs [state_rel_def,empty_buffer_def,AllCaseEqs()]
QED

Theorem compile_DataBufferWrite:
  ^(get_goal "DataBufferWrite")
Proof
  rw [evaluate_def,wordSemTheory.buffer_write_def]
  \\ fs [state_rel_def,empty_buffer_def,AllCaseEqs()]
QED

(* combining all the cases to prove main simulation theorem *)

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Inst,
       compile_Call, compile_Seq, compile_If, compile_While,
       compile_JumpLower, compile_Raise, compile_Return, compile_FFI,
       compile_Tick, compile_LocValue, compile_Install,
       compile_ShMemOp, compile_CodeBufferWrite, compile_Halt,
       compile_DataBufferWrite, compile_RawCall, compile_BitmapLoad])
  \\ asm_rewrite_tac []
  \\ rpt $ pop_assum kall_tac
  \\ rw [evaluate_def,state_rel_def]
QED

(*
  TypeBase.constructors_of “:'a stackLang$prog”
  |> map term_to_string
  |> map (fn s => print ("\n    compile_" ^ s ^ ","))
*)

