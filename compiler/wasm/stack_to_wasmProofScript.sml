(*
  Correctness proof for compilation from stackLang to wasmLang
*)
Theory stack_to_wasmProof
Libs
  preamble helperLib shLib
Ancestors
  wasmLang words arithmetic list rich_list sptree mlstring
  wasmSem stackSem stackLang stackProps pair asm

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

Definition I32_SHR_U_def:
  I32_SHR_U = Numeric (N_binary (Shr_ Unsigned W32))
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

Definition I32_WRAP_I64_def:
  I32_WRAP_I64 = Numeric (N_convert WrapI64)
End

Definition GLOBAL_GET_def:
  GLOBAL_GET i = Variable (GlobalGet (n2w i))
End

Definition GLOBAL_SET_def:
  GLOBAL_SET i = Variable (GlobalSet (n2w i))
End

Definition RETURN_def:
  RETURN = wasmLang$Return
End

Definition CALL_def:
  CALL i = wasmLang$Call (n2w i)
End

Definition CALL_INDIRECT_def:
  CALL_INDIRECT ft = CallIndirect 0w ft
End

Definition RETURN_CALL_def:
  RETURN_CALL i = ReturnCall (n2w i)
End

Definition RETURN_CALL_INDIRECT_def:
  RETURN_CALL_INDIRECT ft = ReturnCallIndirect 0w ft
End

(* more wasm instructions go here *)
(* see wasmLangScript.sml *)

(* ⌂compiler definition (TODO: move to another file when ready) *)

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
  compile_arith (asm$Binop op t s1 s2) =
  (
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
  compile_arith (asm$Shift op t s n) =
  (
    let wasm_op =
      case op of
        Lsl => I64_SHL
      | Lsr => I64_SHR_U
      | Asr => I64_SHR_S
      | Ror => I64_ROTR
    in
    List [GLOBAL_GET s; I64_CONST (n2w n); wasm_op; GLOBAL_SET t]
  ) ∧
  compile_arith (asm$Div t s1 s2) = (* signed div *)
    List [GLOBAL_GET s1; GLOBAL_GET s2; I64_DIV_S; GLOBAL_SET t]
End

Definition compile_inst_def:
  compile_inst (asm$Skip) = List [] ∧
  compile_inst (asm$Const (r:reg) (v:64 word)) =
    List [I64_CONST v; GLOBAL_SET r] ∧
  compile_inst (asm$Arith a) = compile_arith a
End

Definition ftype_def:
  ftype = ([], [Tnum Int W32])
End

Definition wasm_support_function_list_def:
  wasm_support_function_list = []: instr list list (*DUMMY*)
End

Definition tail_call_def:
  tail_call l = RETURN_CALL (LENGTH wasm_support_function_list + l)
End

(*
  This abomination makes me question my life choices. Wading through the
  actual implementation of CakeML completely destroys the joy of software
  engineering.

       | Call ((stackLang$prog # num # num # num) option)
              (* return-handler code, link reg, labels l1,l2*)
              (num + num) (* target of call (Direct or Reg) *)
              ((stackLang$prog # num # num) option)
              (* handler: exception-handler code, labels l1,l2*)
*)
(* ⌂Call *)
Definition compile_call_def:
  (* no return handler -- tail call *)
  compile_call NONE (INL l) _ _ = List [tail_call l] ∧
  compile_call NONE (INR r) _ _ =
  (
    List [
      GLOBAL_GET r; I32_WRAP_I64; I32_CONST 1w; I32_SHR_U;
      RETURN_CALL_INDIRECT ftype
    ]
  ) ∧
  compile_call (SOME (ret_hdlr, lr, ret_loc)) (INL l) _ exn =
  (
    let exn_hdlr =
      case exn of
        NONE => List[]
      | SOME (exn_hdlr, _) => exn_hdlr
    in
    List [
      I64_CONST 0w; GLOBAL_SET lr;
      CALL l;
      wasmLang$If BlkNil (append exn_hdlr) (append ret_hdlr)
    ]
  ) ∧
  compile_call (SOME (ret_hdlr, lr, ret_loc)) (INR r) _ exn =
  (
    let exn_hdlr =
      case exn of
        NONE => List[]
      | SOME (exn_hdlr, _) => exn_hdlr
    in
    List [
      I64_CONST 0w; GLOBAL_SET lr;
      GLOBAL_GET r; I32_WRAP_I64; I32_CONST 1w; I32_SHR_U;
      CALL_INDIRECT ftype;
      wasmLang$If BlkNil (append exn_hdlr) (append ret_hdlr)
    ]
  )
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
  compile (stackLang$Inst inst) = compile_inst inst ∧
  compile (stackLang$Return r) = List [I32_CONST 0w; RETURN] ∧
  compile (stackLang$Raise  r) = List [I32_CONST 1w; RETURN]
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

Definition conf_ok_def:
  conf_ok (c: 64 asm_config) ⇔
  c.reg_count < 4294967296 (* 2**32; wasm binary encoding *) ∧
  c.fp_reg_count = 0 ∧
  c.ISA = Ag32 (* placeholder *)
End

Definition regs_rel_def:
  regs_rel c regs globals ⇔
  LENGTH globals = c.reg_count ∧
  ∀n wl. FLOOKUP regs n = SOME wl ⇒
    EL n globals = to_value wl
End

(* TODO: code_rel: we can find long mul at const index i *)

Definition state_rel_def:
  state_rel c ^s ^t ⇔
    ¬ s.use_stack ∧ ¬ s.use_store ∧ ¬ s.use_alloc ∧ ¬ s.be ∧
    empty_buffer s.code_buffer ∧ empty_buffer s.data_buffer ∧
    regs_rel c s.regs t.globals (* ∧ code_rel s.code t.code *)
End

Definition res_rel_def:
  (res_rel NONE r s    ⇔ r = RNormal) ∧
  (res_rel (SOME TimeOut) r s <=> r = RTimeout) ∧
  (res_rel (SOME (Result    _)) r s <=> r = RReturn ∧ oHD s = SOME (I32 0w)) ∧
  (res_rel (SOME (Exception _)) r s <=> r = RReturn ∧ oHD s = SOME (I32 1w)) ∧
  (* ignore Error *)
  (* Halt?? FinalFFI?? *)
  (res_rel (SOME (Halt     _)) r s <=> r ≠ RNormal ∧ ∀n. r ≠ RBreak n) ∧
  (res_rel (SOME (FinalFFI _)) r s <=> r ≠ RNormal ∧ ∀n. r ≠ RBreak n)
End

(* set up for one theorem per case *)

val goal_tm =
  “λ(p,^s). ∀s_res s_fin t.
     evaluate (p,s) = (s_res, s_fin) ∧
     conf_ok c ∧
     state_rel c s t ∧
     stack_asm_ok c p ∧
     s_res ≠ SOME Error ⇒
     ∃ck t_res t_fin.
       exec_list (append (compile p)) (t with clock := t.clock + ck) = (t_res, t_fin) ∧
       res_rel s_res t_res t_fin.stack ∧
       state_rel c s_fin t_fin ∧
       (t_res = RNormal ⇒ t_fin.stack = t.stack)
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

Theorem exec_list_append_RNormal:
  ∀xs ys s s1.
    exec_list xs s = (RNormal, s1) ⇒
    exec_list (xs ++ ys) s = exec_list ys s1
Proof
  simp[exec_list_append]
QED

Theorem exec_list_nil[simp]:
  exec_list [] s = (RNormal,s)
Proof
  rw[exec_def]
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

Theorem pop_push:
  pop (push v t) = SOME (v,t)
Proof
  rw[push_def,pop_def,wasmSemTheory.state_component_equality]
QED

Theorem exec_If:
  exec (If bt b1 b2) (push (I32 v) s) =
    exec (Block bt (if v≠0w then b1 else b2)) s
Proof
  simp[SimpLHS, Once exec_def, pop_push, nonzero_def]
QED

Theorem exec_list_single:
  exec_list [ins] s = exec ins s
Proof
  simp[exec_def]
  >>pairarg_tac
  >>(Cases_on`res`>>fs[])
QED

Theorem wasm_state_useless_fupd[simp]:
  (^t with clock:=t.clock) = t ∧ (t with stack:=t.stack) = t
Proof
  simp[wasmSemTheory.state_component_equality]
QED

Theorem exec_Block_BlkNil_RNormal:
  exec_list Ins s = (RNormal, s') ∧
  s.stack=[] ∧ s'.stack=[] ⇒
  exec (Block BlkNil Ins) (s with stack:=stack) = (RNormal, s' with stack:=stack)
Proof
  rw[exec_def]>>fs[]
  >>subgoal`(s with stack := []) = s`
  >-metis_tac[wasm_state_useless_fupd]
  >>simp[]
QED

Theorem exec_Block_BlkNil_RBreak0:
  exec_list Ins s = (RBreak 0, s') ∧
  s.stack=[] ⇒
  exec (Block BlkNil Ins) (s with stack:=stack) = (RNormal, s' with stack:=stack)
Proof
  rw[exec_def]>>fs[]
  >>subgoal`(s with stack := []) = s`
  >-metis_tac[wasm_state_useless_fupd]
  >>simp[]
QED

Theorem UNCURRY_pair_CASE:
  ∀f x. UNCURRY f x = pair$pair_CASE x f
Proof
Cases_on`x`>>simp[]
QED

(*
TypeBase.  is_case ``case x of NONE => a | SOME y => b y``;
TypeBase.dest_case ``case x of NONE => a | SOME y => b y``;
TypeBase.  is_case ``if x then a else b``;
TypeBase.dest_case ``if x then a else b``;
dest_let ``let a=x in f a``;
*)

fun find_map_term_shallow f tm =
  case f tm of SOME t => SOME t | NONE =>
  if is_comb tm then let
    val (r,d) = dest_comb tm
    in
      case find_map_term_shallow f r of SOME t => SOME t | NONE =>
      find_map_term_shallow f d
    end
  else NONE

fun peel thms = let
  fun my_case_tac (g as (_, concl)) = let
    datatype kind = CASE | LET
    fun f tm =
      if TypeBase.is_case tm then let
        val (_, examined, _) = TypeBase.dest_case tm
        in SOME (CASE, examined) end
      else if is_let tm then
        SOME (LET, #2 (dest_let tm))
      else NONE
    val (tm, _) = dest_imp concl
    in case find_map_term_shallow f tm of
      NONE => NO_TAC g
    | SOME (CASE, t) => let
      val imp_res =
        pop_assum (fn eq =>
          foldl (fn(th,a) => a >> assume_tac th) (assume_tac eq) $
            List.mapPartial (fn th => SOME (MATCH_MP th eq) handle HOL_ERR _ => NONE) thms
        )
      in (Cases_on `^t` >> gvs[] >> imp_res) g end
    | SOME (LET, _) =>
      gvs[UNCURRY_pair_CASE] g
    end
  in
    PURE_REWRITE_TAC[UNCURRY_pair_CASE] >> my_case_tac
  end

(* wasmProps *)
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
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[])
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[‘Loop’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[])
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[‘If’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[‘Br’]
  >-fs[exec_def]
  >~[‘BrIf’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[‘BrTable’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[‘Return’]
  >-fs[exec_def]
  >~[‘ReturnCall’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_n_clock])
    >-(strip_tac>>fs[])
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[‘ReturnCallIndirect’]
  >-(
    qpat_x_assum `exec _ _ = _` mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[‘Call’]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_n_clock])
    >-(strip_tac>>fs[])
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[‘CallIndirect’]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[`Numeric`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>peel[]
    >-(strip_tac>>fs[])
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[`Parametric Drop`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >>metis_tac[]
  )
  >~[`Parametric Select`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock])
    >-metis_tac[]
    >-metis_tac[]
    >-metis_tac[]
    >>simp[push_def,wasmSemTheory.state_component_equality]
  )
  >~[`LocalGet`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>peel[]
    >-(strip_tac>>fs[])
    >>simp[push_def,wasmSemTheory.state_component_equality]
  )
  >~[`LocalSet`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock,set_local_clock])
    >>metis_tac[]
  )
  >~[`LocalTee`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock,set_local_clock])
    >>metis_tac[]
  )
  >~[`GlobalGet`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>peel[]
    >-(strip_tac>>fs[])
    >>simp[push_def,wasmSemTheory.state_component_equality]
  )
  >~[`GlobalSet`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock,set_global_clock])
    >>metis_tac[]
  )
  >~[`MemRead`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_i32_clock])
    >-metis_tac[]
    >>simp[wasmSemTheory.state_component_equality]
  )
  >~[`MemWrite`]
  >-(
    qpat_x_assum`exec _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[pop_clock,pop_i32_clock])
    >-metis_tac[]
    >-metis_tac[]
    >>simp[wasmSemTheory.state_component_equality]
  )
  >-fs[exec_def]
  >-(
    qpat_x_assum`exec_list _ _ = _`mp_tac
    >>once_rewrite_tac[exec_def]
    >>rpt(peel[])
    >>strip_tac
    >>(PURE_TOP_CASE_TAC>>fs[])
  )
QED

Theorem exec_list_add_clock = CONJUNCT1 exec_list_add_clock_aux;

Theorem comp_cmp_thm:
  get_var a s = SOME va ∧
  get_var_imm b s = SOME vb ∧
  labSem$word_cmp cmp va vb = SOME v ∧
  state_rel c ^s ^t ==>
  exec_list (append (comp_cmp cmp a b)) (t with clock := ck) =
    (RNormal, push (I32 (b2w v)) (t with clock := ck))
Proof
  cheat
QED

Theorem nonzero_b2w:
  nonzero (I32 (b2w v)) = SOME v
Proof
  Cases_on‘v’>>rw[nonzero_def]
QED

Theorem exec_I32_CONST:
  exec (I32_CONST c) s =
    (RNormal,s with stack := I32 c::s.stack)
Proof
  rw[exec_def,I32_CONST_def,num_stk_op_def]
QED

Theorem exec_I64_CONST:
  exec (I64_CONST c) s =
    (RNormal,s with stack := I64 c::s.stack)
Proof
  rw[exec_def,I64_CONST_def,num_stk_op_def]
QED

Theorem exec_GLOBAL_SET:
  exec (GLOBAL_SET n) s = (res,s') ∧
  n < LENGTH s.globals ∧
  LENGTH s.globals < 4294967296 ∧
  s.stack = v :: t ⇒
  res = RNormal ∧
  s' = s with
     <|stack := t;
       globals := LUPDATE v n s.globals|>
Proof
  rw[exec_def,GLOBAL_SET_def,pop_def,set_global_def]
  >>gvs[AllCaseEqs()]
QED

Theorem state_rel_set_var:
  to_value v = w ∧
  n < LENGTH t.globals ∧
  state_rel c s t ⇒
  state_rel c (set_var n v s)
    (t with globals := LUPDATE w n t.globals)
Proof
  rw[state_rel_def,regs_rel_def,EL_LUPDATE,set_var_def]>>
  fs[FLOOKUP_UPDATE]>>
  rw[]>>
  gvs[AllCaseEqs()]
QED

Theorem state_rel_with_stack:
  state_rel c s (t with stack := st) = state_rel c s t
Proof
  fs[state_rel_def]
QED

(* a ⌂proof for each case *)

Theorem compile_Skip:
  ^(get_goal "Skip")
Proof
  rpt strip_tac
  >> gvs [compile_def,exec_def,stackSemTheory.evaluate_def]
  >> simp [res_rel_def]
  >> qexists_tac ‘0’ >> fs [state_rel_def]
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
    rename1‘_ = (SOME res_mid, s_mid)’
    >>gvs[stack_asm_ok_def]
    >>last_x_assum drule
    >>strip_tac
    >>qexists_tac‘ck’
    >>simp[]
    >>(Cases_on`res_mid`>>fs[res_rel_def])
  )
  >>gvs[stack_asm_ok_def]
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

Theorem res_rel_RNormal:
  res ≠ SOME Error ∧ res_rel res RNormal stack ⇒ res_rel res RNormal stack'
Proof
  Cases_on`res`>-simp[res_rel_def]
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RBreak:
  res ≠ SOME Error ∧ res_rel res (RBreak n) stack ⇒ F
Proof
  Cases_on`res`>-simp[res_rel_def]
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem compile_If:
  ^(get_goal "If")
Proof
  rpt strip_tac
  >>fs[evaluate_def]
  >>gvs[CaseEq"option",stack_asm_ok_def]
  >>rename1`word_cmp cmp v1 v2 = SOME b`
  >>(Cases_on`b`>>fs[])
  >>(
    first_x_assum $ qspec_then`t with stack:=[]`mp_tac
    >>simp[state_rel_with_stack]
    >>rpt strip_tac
    >>qexists_tac`ck`
    >>simp[compile_def]
    >>drule_all_then (qspec_then`ck+t.clock`assume_tac) comp_cmp_thm
    >>dxrule_then (simp o single) exec_list_append_RNormal
    >>simp[exec_list_single,exec_If]
    >>(Cases_on`t_res`>>fs[])
    >~[`exec_list _ _ = (RNormal, _)`]
    >-(
      drule_then (qspec_then`t.stack`assume_tac) exec_Block_BlkNil_RNormal
      >>fs[]
      >>simp[state_rel_with_stack]
      >>metis_tac[res_rel_RNormal]
    )
    >~[`exec_list _ _ = (RBreak _, _)`]
    >-(
      Cases_on`n`
      >-(
        drule_then (qspec_then`t.stack`assume_tac) exec_Block_BlkNil_RBreak0
        >>fs[]
        >>simp[state_rel_with_stack]
        >>metis_tac[res_rel_RBreak]
      )
      >>simp[exec_def]
      >>metis_tac[res_rel_RBreak]
    )
    >>simp[exec_def]
  )
QED

(*⌂⌂*)

Theorem compile_Inst:
  ^(get_goal "Inst")
Proof
  rw[compile_def]
  >>qexists_tac`0`
  >>(Cases_on`i`>>fs[compile_inst_def])
  >~[`Skip`]
  >-gvs[evaluate_def,exec_def,res_rel_def,inst_def]
  >~[`Const`]
  >-(
    fs[evaluate_def,inst_def,assign_def,CaseEq"option"]
    >>fs[exec_list_cons,exec_I64_CONST]
    >>rpt(pairarg_tac>>fs[])
    >>drule exec_GLOBAL_SET
    >>simp[]
    >>CONV_TAC(DEPTH_CONV record_canon_simp_conv)
    >>impl_keep_tac
    >-fs[stack_asm_ok_def,inst_ok_def,reg_ok_def,conf_ok_def,state_rel_def,regs_rel_def]
    >>rw[]
    >-simp[res_rel_def]
    >>irule state_rel_set_var
    >>fs[word_exp_def,to_value_def]
  )
  >~[`Arith`]
  >-(
    rename1`Arith a`>>Cases_on`a`
    >~[`Binop`] >- cheat
    >~[`Shift`] >- cheat
    >~[`Div`] >- cheat
    >~[`LongMul`] >- cheat
    >~[`LongDiv`] >- fs[stack_asm_ok_def,inst_ok_def,arith_ok_def,conf_ok_def]
    >~[`AddCarry`] >- cheat
    >~[`AddOverflow`] >- cheat
    >~[`SubOverflow`] >- cheat
  )
  >~[`Mem`] >-
    cheat
  >~[`FP`] >-
    gvs[stack_asm_ok_def,inst_ok_def,oneline fp_ok_def,AllCasePreds(),fp_reg_ok_def,conf_ok_def]
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

(*lemma*)
Theorem exec_RETURN:
  exec RETURN s = (RReturn,s)
Proof
  fs[RETURN_def,exec_def]
QED

Theorem compile_Return:
  ^(get_goal "Return")
Proof
rw[evaluate_def]
>>gvs[CaseEqs["option","prod","word_loc"]]
>>qexists_tac`0`
>>simp[compile_def]
(* Goal: ∃t_res t_fin. exec_list [I32_CONST 0w; RETURN] t = (res1,t1) ∧ ... *)
>>simp[exec_list_cons]
>>rpt(pairarg_tac>>fs[])
>>rename1 `exec RETURN t1 = (res2, t2)`
>>gvs[exec_I32_CONST,exec_RETURN]
>>simp[res_rel_def]
>>metis_tac[state_rel_with_stack]
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

