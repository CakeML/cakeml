(*
  Correctness proof for compilation from stackLang to CWasm
*)
Theory stack_to_wasmProof
Libs
  preamble helperLib shLib
Ancestors
  misc wasmLang
  wasmSem stackSem stackLang stackProps asm

(* TODO: move Irvin's simps *)
Theorem option_CASE_OPTION_MAP[simp]:
  (option_CASE (OPTION_MAP f e) a b) = option_CASE e a (λx. b (f x))
Proof
  Cases_on`e`>>simp[]
QED

Theorem pair_CASE_PAIR_MAP[simp]:
  pair_CASE ((f ## g) e) a = pair_CASE e (\x y. a (f x) (g y))
Proof
  Cases_on`e`>>simp[]
QED

(* shorthands for wasm instructions *)
Definition I64_EQ_def:
  I64_EQ = Numeric (N_compare (Eq Int W64))
End

Definition I64_NE_def:
  I64_NE = Numeric (N_compare (Ne Int W64))
End

Definition I64_LT_U_def:
  I64_LT_U = Numeric (N_compare (Lt_ Unsigned W64))
End

Definition I64_GT_U_def:
  I64_GT_U = Numeric (N_compare (Gt_ Unsigned W64))
End

Definition I64_LE_U_def:
  I64_LE_U = Numeric (N_compare (Le_ Unsigned W64))
End

Definition I64_GE_U_def:
  I64_GE_U = Numeric (N_compare (Ge_ Unsigned W64))
End

Definition I64_LT_S_def:
  I64_LT_S = Numeric (N_compare (Lt_ Signed W64))
End

Definition I64_GT_S_def:
  I64_GT_S = Numeric (N_compare (Gt_ Signed W64))
End

Definition I64_LE_S_def:
  I64_LE_S = Numeric (N_compare (Le_ Signed W64))
End

Definition I64_GE_S_def:
  I64_GE_S = Numeric (N_compare (Ge_ Signed W64))
End

Definition I64_EQZ_def:
  I64_EQZ = Numeric (N_eqz W64)
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

(* compiler definition (TODO: move to another file when ready) *)

(* reg_imm = Reg reg | Imm ('a imm) *)
Definition comp_ri_def:  comp_ri (Reg r) = GLOBAL_GET r ∧
  comp_ri (Imm n) = I64_CONST n
End

(* cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest *)
Definition compile_comp_def:
  compile_comp (cmp: cmp) a b =
    let op =
      case cmp of
        Equal    => [I64_EQ]
      | NotEqual => [I64_NE]
      | Lower    => [I64_LT_U]
      | NotLower => [I64_GE_U]
      | Less     => [I64_LT_S]
      | NotLess  => [I64_GE_S]
      | Test     => [I64_AND; I64_EQZ] (* Test a b <=> bitwise_and a b = 0 *)
      | NotTest  => [I64_AND; I64_CONST 0w; I64_NE]
    in
    List (GLOBAL_GET a :: comp_ri b :: op)
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
  wasm_support_function_list = []: func list (*DUMMY*)
End

Definition tail_call_def:
  tail_call l = RETURN_CALL (LENGTH wasm_support_function_list + l)
End

(*
       | Call ((stackLang$prog # num # num # num) option)   (* return-handler code, link reg, label *)
              (num + num)                                   (* target of call (Direct or Reg) *)
              (stackLang$prog # num # num) option           (* exception-handler code, label *)
*)

Overload flatten = “append”;

Definition compile_def:
  compile stackLang$Skip = List ([]:wasmLang$instr list) ∧
  compile (Seq p1 p2) = Append (compile p1) (compile p2) ∧
  (* If cmp num ('a reg_imm) stackLang$prog stackLang$prog *)
  (* no values are left on the wasm operand stack, hence BlkNil *)
  compile (stackLang$If cmp a_r b_ri p1 p2) =
    Append (compile_comp cmp a_r b_ri)
           (List [wasmLang$If BlkNil (flatten (compile p1)) (flatten (compile p2))])
  ∧
  compile (stackLang$Inst inst) = compile_inst inst ∧
  compile (stackLang$Return r) = List [I32_CONST 0w; RETURN] ∧
  compile (stackLang$Raise  r) = List [I32_CONST 1w; RETURN] ∧

  (* Call *)

  (* no return handler -- tail call *)
  compile (stackLang$Call NONE dest _) =
  (
    case dest of
      INL l => List [tail_call l]
    | INR r =>
      List [
        GLOBAL_GET r; I64_CONST 1w; I64_SHR_U; I32_WRAP_I64;
        RETURN_CALL_INDIRECT ftype
      ]
  ) ∧
  compile (stackLang$Call (SOME (ret_hdlr, lr, ret_loc)) dest exn) =
  (
    let exn_hdlr =
      case exn of
        NONE => List [I32_CONST 1w; RETURN] (* re-raise exception *)
      | SOME (exn_hdlr, _) => compile exn_hdlr
    in
    let rest =
      wasmLang$If BlkNil (flatten exn_hdlr) (flatten (compile ret_hdlr))
    in
    let call_sequence =
      case dest of
        INL l => [CALL (LENGTH wasm_support_function_list + l); rest]
      | INR r => [GLOBAL_GET r; I64_CONST 1w; I64_SHR_U; I32_WRAP_I64; CALL_INDIRECT ftype; rest]
    in
    (* the I64_CONST-GLOBAL_SET sequence is just to maintain state_rel *)
    List (I64_CONST (n2w (FST ret_loc) << 1) :: GLOBAL_SET lr :: call_sequence)
  )

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

Definition wl_word_def:
  wl_word w = case w of Word w => w | Loc l _ => n2w l << 1
End

Definition wl_value_def:
  wl_value w = I64 (case w of Word w => w | Loc l _ => n2w l << 1)
End

Theorem wl_value_wl_word:
  wl_value w = I64 (wl_word w)
Proof
  simp[wl_value_def,wl_word_def]
QED

Definition conf_ok_def:
  conf_ok (c: 64 asm_config) ⇔
  c.reg_count < 4294967296 (* 2**32; wasm binary encoding *) ∧
  c.fp_reg_count = 0 ∧
  c.ISA = Wasm
End

Definition regs_rel_def:
  regs_rel c regs globals ⇔
  LENGTH globals = c.reg_count ∧
  ( ∀n w. FLOOKUP regs n = SOME w ⇒
    n < c.reg_count ∧
    (* already have ‘LENGTH globals = c.reg_count’ *)
    EL n globals = wl_value w
  )
End

Definition cakeml_ftype_index_def:
  cakeml_ftype_index = 0w:word32
End

Definition stack_wasm_ok_def:
  (stack_wasm_ok c (ShMemOp _ _ _) <=> F) ∧
  (stack_wasm_ok c (JumpLower _ _ _) ⇔ F) ∧
  (stack_wasm_ok c (Install _ _ _ _ _) ⇔ F) ∧
  (stack_wasm_ok c (CodeBufferWrite _ _) ⇔ F) ∧
  (stack_wasm_ok c (DataBufferWrite _ _) ⇔ F) ∧
  (stack_wasm_ok c (RawCall _) ⇔ F) ∧
  (stack_wasm_ok c (Seq p1 p2) ⇔ stack_wasm_ok c p1 ∧ stack_wasm_ok c p2) ∧
  (stack_wasm_ok c (If cmp n r p1 p2) ⇔ stack_wasm_ok c p1 ∧ stack_wasm_ok c p2) ∧
  (stack_wasm_ok c (While cmp n r p) ⇔ stack_wasm_ok c p) ∧
  (stack_wasm_ok c (Call r tar h) ⇔
    case r of NONE => T
    | SOME (rp,lr,_,_) =>
      stack_wasm_ok c rp ∧ lr < c.reg_count ∧
      (case h of NONE=>T | SOME (hp,_,_) => stack_wasm_ok c hp)
  )
End

(*
Datatype: func =
  <| ftype  : index
   ; locals : valtype list
   ; body   : expr
   |>
End
*)

(* TODO: code_rel: we can find long mul at const index i *)
(* see HOL/examples/machine-code/multiword *)

Definition code_rel_def:
  code_rel (s_code: 64 stackLang$prog sptree$num_map) (t_funcs: func list) =
  ∀i prog.
    lookup i s_code = SOME prog ==>
    oEL (LENGTH wasm_support_function_list + i) t_funcs = SOME
      <|
        ftype := cakeml_ftype_index;
        locals := []; (* we don't use wasm local variables lol *)
        body := flatten (compile prog)
      |> (*/\
    stack_wasm_ok c prog*)
End

Definition wasm_state_ok_def:
  wasm_state_ok ^t <=>
  LENGTH t.funcs < 4294967296 ∧
  (* presence of support functions *)
  (∀i. i < LENGTH wasm_support_function_list ==> oEL i t.funcs = SOME (EL i wasm_support_function_list)) ∧
  (* func type table *)
  oEL (w2n cakeml_ftype_index) t.types = SOME ([], [Tnum Int W32]) ∧
  (* every wasm func is present in the func_table for indirect calls *)
  (∀i. i < LENGTH t.funcs ⇒ oEL i t.func_table = SOME (n2w (LENGTH wasm_support_function_list + i)))
End

Definition state_rel_def:
  state_rel c ^s ^t ⇔
    (* s only *)
    ¬ s.use_stack ∧ ¬ s.use_store ∧ ¬ s.use_alloc ∧ ¬ s.be ∧
    empty_buffer s.code_buffer ∧ empty_buffer s.data_buffer ∧
    (∀i p. lookup i s.code = SOME p ⇒ stack_wasm_ok c p) ∧ (* TODO: move to code_rel? *)
    (* t only *)
    wasm_state_ok t ∧
    (* actually relate s and t *)
    regs_rel c s.regs t.globals ∧
    s.clock = t.clock ∧
    code_rel s.code t.funcs
End

Definition res_rel_def:
  (res_rel  NONE                r (stk, stk') <=> r = RNormal ∧ stk' = stk) ∧
  (res_rel (SOME  TimeOut     ) r (stk, stk') <=> r = RTimeout) ∧
  (res_rel (SOME (Result    _)) r (stk, stk') <=> r = RReturn ∧ oHD stk' = SOME (I32 0w) (* don't care about the rest of the stk' *)) ∧
  (res_rel (SOME (Exception _)) r (stk, stk') <=> r = RReturn ∧ oHD stk' = SOME (I32 1w)) ∧
  (res_rel (SOME (Halt      _)) r (stk, stk') <=> r = RHalt) (* tentative *) ∧
  (res_rel (SOME (FinalFFI  _)) r (stk, stk') <=> r = RHalt) (* tentative *) ∧
  (res_rel (SOME  Error       ) r (stk, stk') <=> F)
  (* the Error case doesn't really matter since we always assume ‘res ≠ SOME Error’ when asked to prove res_rel *)
End

Theorem res_rel_RNormal:
  res_rel s_res RNormal (stk, stk') <=> s_res = NONE ∧ stk' = stk
Proof
  Cases_on`s_res`>-simp[res_rel_def]
  >>(Cases_on`x`>>simp[res_rel_def])
QED

(*
Definition stack_asm_ok_def:
  (stack_asm_ok c ((Inst i):'a stackLang$prog) ⇔ asm$inst_ok i c) ∧
  (stack_asm_ok c (ShMemOp op r ad) ⇔ reg_ok r c ∧ addr_ok op ad c) ∧
  (stack_asm_ok c (CodeBufferWrite r1 r2) ⇔ r1 < c.reg_count ∧ r2 < c.reg_count ∧ ¬MEM r1 c.avoid_regs ∧ ¬MEM r2 c.avoid_regs) ∧
  (stack_asm_ok c (Seq p1 p2) ⇔ stack_asm_ok c p1 ∧ stack_asm_ok c p2) ∧
  (stack_asm_ok c (If cmp n r p p') ⇔ stack_asm_ok c p ∧ stack_asm_ok c p') ∧
  (stack_asm_ok c (While cmp n r p) ⇔ stack_asm_ok c p) ∧
  (stack_asm_ok c (Raise n) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Return n) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Call r tar h) ⇔
    (case tar of INR r => r < c.reg_count ∧ ¬MEM r c.avoid_regs | _ => T) ∧
    case r of
      (SOME (p,_,_,_) => stack_asm_ok c p ∧
      case h of
      SOME (p',_,_) => stack_asm_ok c p'
      | _ => T)
    | _ => T) ∧
  (stack_asm_ok c _ ⇔  T)
End
*)

(* set up for one theorem per case *)

val goal_tm = “
  λ(p,^s). ∀s_res s_fin t.
    evaluate (p,s) = (s_res, s_fin) ∧
    conf_ok c ∧
    stack_wasm_ok c p ∧
    s_res ≠ SOME Error ∧
    state_rel c s t ⇒
    ∃ck t_res t_fin.
      (* wasm program may consume more clock *)
      exec_list (flatten (compile p)) (t with clock := ck + t.clock) = (t_res, t_fin) ∧
      res_rel s_res t_res (t.stack, t_fin.stack) ∧
      state_rel c s_fin t_fin
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

Theorem oHD_SOME_drule:
  oHD L = SOME a ==> ∃L'. L=a::L'
Proof
  Cases_on`L`>>simp[]
QED

(* use miscTheory.LLOOKUP_EQ_EL *)
(*
Theorem LLOOKUP_SOME_LENGTH:
  ∀i x. LLOOKUP L i = SOME x ==> i < LENGTH L
Proof
  Induct_on`L`>>rw[LLOOKUP_def]
  >>first_x_assum drule
  >>decide_tac
QED
*)

Theorem exec_list_append:
  ∀xs ys s.
    exec_list (xs ++ ys) s =
    let (res,s1) = exec_list xs s in
    if res = RNormal then exec_list ys s1
    else (res,s1)
Proof
  Induct_on‘xs’>>rw[exec_def]
  >>(pairarg_tac>>fs[])
  >>(PURE_TOP_CASE_TAC>>fs[])
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
  simp[exec_def,UNCURRY_pair_CASE]>>every_case_tac
QED

Theorem exec_list_cons_RNormal:
  exec i s = (RNormal, s1) ⇒
  exec_list (i::rest) s = exec_list rest s1
Proof
  simp[exec_list_cons]
QED

Theorem pop_with_clock[simp]:
  pop (s with clock updated_by f) = OPTION_MAP (I ## \t. t with clock updated_by f) (pop s)
Proof
  rw[pop_def]>>PURE_TOP_CASE_TAC>>fs[]
QED

Theorem pop_n_with_clock[simp]:
  pop_n n (s with clock updated_by f) = OPTION_MAP (I ## \t. t with clock updated_by f) (pop_n n s)
Proof
  rw[pop_n_def]
QED

Theorem pop_i32_with_clock[simp]:
  pop_i32 (s with clock updated_by f) = OPTION_MAP (I ## \t. t with clock updated_by f) (pop_i32 s)
Proof
  rw[pop_i32_def]>>rpt(PURE_TOP_CASE_TAC>>fs[])
QED

(* drule *)
Theorem pop_i32_clock:
  pop_i32 s = SOME (x,s') ==> s'.clock = s.clock
Proof
  simp[pop_i32_def,AllCaseEqs()]
  >>strip_tac
  >>gvs[]
QED

Theorem set_local_with_clock[simp]:
  set_local n x (s with clock updated_by f) =
  OPTION_MAP (\t. t with clock updated_by f) (set_local n x s)
Proof
  rw[set_local_def]
QED

(* drule *)
Theorem set_local_clock:
  set_local n x s = SOME t ==> t.clock = s.clock
Proof
  rw[set_local_def]
  >>simp[state_component_equality]
QED

Theorem set_global_with_clock[simp]:
  set_global n x (s with clock updated_by f) =
  OPTION_MAP (\t. t with clock updated_by f) (set_global n x s)
Proof
  rw[set_global_def]
QED

(* drule *)
Theorem set_global_clock:
  set_global n x s = SOME t ==> t.clock = s.clock
Proof
  rw[set_global_def]
  >>simp[state_component_equality]
QED

Theorem pop_push[simp]:
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

Theorem exec_list_single[simp]:
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

(*
set_trace "Goalstack.howmany_printed_subgoals" 99;
*)

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
  ho_match_mp_tac exec_ind
  >>rpt strip_tac
  >>(qpat_x_assum `exec _ _ = _` mp_tac ORELSE qpat_x_assum `exec_list _ _ = _` mp_tac)
  >>once_rewrite_tac[exec_def]
  >>rpt(peel[pop_clock, pop_n_clock, pop_i32_clock, set_local_clock, set_global_clock])
  >>TRY(strip_tac>>gvs[])
  >>simp[push_def]
QED

Theorem exec_list_add_clock = CONJUNCT2 exec_list_add_clock_aux;

Theorem exec_GLOBAL_GET:
  get_var r s = SOME w ∧
  conf_ok c ∧
  state_rel c s t ⇒
  exec (GLOBAL_GET r) t = (RNormal, push (wl_value w) t)
Proof
  rw[get_var_def,exec_def,GLOBAL_GET_def]
  >>`regs_rel c s.regs t.globals` by fs[state_rel_def]
  >>subgoal`r MOD 4294967296 = r`
  >-(
    `r < c.reg_count` by fs[regs_rel_def]
    >>`c.reg_count < 4294967296` by fs[conf_ok_def]
    >>irule LESS_MOD
    >>decide_tac
  )
  >>pop_assum (simp o single)
  >>subgoal`∀n wl. FLOOKUP s.regs n = SOME wl ⇒ LLOOKUP t.globals n = SOME (wl_value wl)`
  >-(
    fs[regs_rel_def]
    >>rw[]
    >>first_x_assum drule
    >>simp[LLOOKUP_THM]
  )
  >>pop_assum imp_res_tac
  >>simp[]
QED

Theorem state_rel_with_clock:
  state_rel c s t ⇒
  state_rel c (s with clock updated_by f) (t with clock updated_by f)
Proof
  fs[state_rel_def,wasm_state_ok_def]>>rw[]
QED

Theorem state_rel_with_stack[simp]:
  state_rel c s (t with stack updated_by _) = state_rel c s t
Proof
  fs[state_rel_def,wasm_state_ok_def]
QED

Theorem state_rel_with_locals[simp]:
  state_rel c s (t with locals updated_by _) = state_rel c s t
Proof
  fs[state_rel_def,wasm_state_ok_def]
QED

Theorem regs_rel_FEMPTY:
  regs_rel c s_regs t_globals ⇒
  regs_rel c FEMPTY t_globals
Proof
  simp[regs_rel_def]
QED

Theorem state_rel_empty_env:
  state_rel c s t ⇒
  state_rel c (empty_env s) t
Proof
  simp[empty_env_def,state_rel_def]
  >>metis_tac[regs_rel_FEMPTY]
QED

Theorem state_rel_empty_env_t_with_globals:
  state_rel c s t ∧
  t' = t with globals := LUPDATE x r t.globals ⇒
  state_rel c (empty_env s) t'
Proof
  rw[empty_env_def,state_rel_def]
  >-metis_tac[]
  >-fs[wasm_state_ok_def]
  >-fs[regs_rel_def]
QED

Theorem exec_I32_CONST:
  exec (I32_CONST c) s = (RNormal, push (I32 c) s)
Proof
  rw[exec_def,I32_CONST_def,num_stk_op_def,push_def]
QED

Theorem exec_I64_CONST:
  exec (I64_CONST c) s = (RNormal, push (I64 c) s)
Proof
  rw[exec_def,I64_CONST_def,num_stk_op_def,push_def]
QED

Theorem exec_comp_ri:
  get_var_imm ri s = SOME w ∧
  conf_ok c ∧ state_rel c s t ⇒
  exec (comp_ri ri) t = (RNormal, push (wl_value w) t)
Proof
rpt strip_tac
>>(Cases_on`ri`>>fs[get_var_imm_def,comp_ri_def])
>-metis_tac[exec_GLOBAL_GET]
>>simp[exec_I64_CONST]
>>gvs[push_def,wl_value_def]
QED

(* Overload b2v = “(λ b. if b then I32 1w else I32 0w) : bool -> value” *)
Theorem b2v_b2w:
  b2v b = I32 (b2w b)
Proof
  Cases_on`b`>>simp[]
QED

Theorem exec_I64_EQ:
  exec I64_EQ (push (I64 b) (push (I64 a) t)) =
  (RNormal, push (I32 (b2w (a=b))) t)
Proof
simp[I64_EQ_def,exec_def,num_stk_op_def,push_def,do_cmp_eq,b2v_b2w]
QED

Theorem exec_I64_EQ':
  labSem$word_cmp Equal wa wb = SOME ☯ ⇒
  exec I64_EQ (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
simp[wl_value_wl_word,exec_I64_EQ]
>>(Cases_on`wa`>>Cases_on`wb`>>simp[wl_word_def,labSemTheory.word_cmp_def])
QED

Theorem exec_I64_NE:
  exec I64_NE (push (I64 b) (push (I64 a) t)) =
  (RNormal, push (I32 (b2w (a≠b))) t)
Proof
simp[I64_NE_def,exec_def,num_stk_op_def,push_def,do_cmp_eq,b2v_b2w]
QED

Theorem exec_I64_NE':
  labSem$word_cmp NotEqual wa wb = SOME ☯ ⇒
  exec I64_NE (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_NE_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w]
QED

Theorem exec_I64_LT_U':
  labSem$word_cmp Lower wa wb = SOME ☯ ⇒
  exec I64_LT_U (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_LT_U_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w]
QED

Theorem exec_I64_LE_U':
  labSem$word_cmp NotLower wb wa = SOME ☯ ⇒
  exec I64_LE_U (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_LE_U_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_NOT_LOWER]
QED

Theorem exec_I64_GT_U':
  labSem$word_cmp Lower wb wa = SOME ☯ ⇒
  exec I64_GT_U (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_GT_U_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_HIGHER]
QED

Theorem exec_I64_GE_U':
  labSem$word_cmp NotLower wa wb = SOME ☯ ⇒
  exec I64_GE_U (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_GE_U_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_NOT_LOWER,WORD_HIGHER_EQ]
QED

Theorem exec_I64_LT_S':
  labSem$word_cmp Less wa wb = SOME ☯ ⇒
  exec I64_LT_S (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_LT_S_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w]
QED

Theorem exec_I64_LE_S':
  labSem$word_cmp NotLess wb wa = SOME ☯ ⇒
  exec I64_LE_S (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_LE_S_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_NOT_LESS]
QED

Theorem exec_I64_GT_S':
  labSem$word_cmp Less wb wa = SOME ☯ ⇒
  exec I64_GT_S (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_GT_S_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_GREATER]
QED

Theorem exec_I64_GE_S':
  labSem$word_cmp NotLess wa wb = SOME ☯ ⇒
  exec I64_GE_S (push (wl_value wb) (push (wl_value wa) t)) =
  (RNormal, push (I32 (b2w ☯)) t)
Proof
strip_tac
>>simp[I64_GE_S_def,exec_def]
>>(PURE_TOP_CASE_TAC>>fs[])
>>fs[push_def,num_stk_op_def,wl_value_def,do_cmp_eq]
>>(Cases_on`wa`>>Cases_on`wb`>>fs[labSemTheory.word_cmp_def])
>>gvs[b2v_b2w,WORD_NOT_LESS,WORD_GREATER_EQ]
QED

Theorem case_case_option[simp]:
  option_CASE (case e of NONE => NONE | SOME x => SOME (f x)) a b =
  case e of NONE => a | SOME x => b (f x)
Proof
Cases_on`e`>>simp[]
QED

Theorem exec_I64_AND:
  exec I64_AND (push (I64 b) (push (I64 a) t)) =
  (RNormal, push (I64 (a && b)) t)
Proof
simp[I64_AND_def,exec_def,num_stk_op_def,push_def,do_bin_eq]
QED

Theorem exec_I64_EQZ:
  exec I64_EQZ (push (I64 a) t) =
  (RNormal, push (I32 (b2w (a=0w))) t)
Proof
simp[I64_EQZ_def,exec_def,num_stk_op_def,push_def,b2v_b2w]
QED

Theorem exec_I32_WRAP_I64:
  exec I32_WRAP_I64 (push (I64 a) t) =
  (RNormal, push (I32 (w2w a)) t)
Proof
simp[I32_WRAP_I64_def,exec_def,num_stk_op_def,push_def,do_cvt_eq]
QED

Theorem exec_I32_SHR_U:
  exec I32_SHR_U (push (I32 b) (push (I32 a) t)) =
  (RNormal, push (I32 (a >>> w2n (b && 31w))) t)
Proof
  simp[I32_SHR_U_def,exec_def,num_stk_op_def,push_def,do_bin_eq]
QED

Theorem exec_I64_SHR_U:
  exec I64_SHR_U (push (I64 b) (push (I64 a) t)) =
  (RNormal, push (I64 (a >>> w2n (b && 63w))) t)
Proof
  simp[I64_SHR_U_def,exec_def,num_stk_op_def,push_def,do_bin_eq]
QED

Theorem push_inj[simp]:
  push a t = push b t <=> a = b
Proof
simp[push_def,wasmSemTheory.state_component_equality]
QED

(* proving this in-line doesn't work -- maybe due to polymorphism? *)
Theorem AND_1:
  1w && x << 1 = 0w
Proof
  irule word_and_lsl_eq_0
  >>simp[]
QED

Theorem compile_comp_thm:
  get_var a s = SOME wa ∧
  get_var_imm b s = SOME wb ∧
  labSem$word_cmp cmp wa wb = SOME ☯ ∧
  conf_ok c ∧
  state_rel c ^s ^t ==>
  exec_list (flatten (compile_comp cmp a b)) t = (RNormal, push (I32 (b2w ☯)) t)
Proof
rpt strip_tac
>>simp[compile_comp_def,exec_list_cons]
>>(pairarg_tac>>fs[])
>>drule_all_then assume_tac exec_GLOBAL_GET
>>gvs[]
>>(pairarg_tac>>fs[])
>>subgoal`state_rel c s (push (wl_value wa) t)`
>- simp[push_def]
>>drule_all_then assume_tac exec_comp_ri
>>gvs[]
(* *)
>>(PURE_TOP_CASE_TAC>>fs[])
>-(irule exec_I64_EQ'>>first_assum ACCEPT_TAC)
>-(irule exec_I64_LT_U'>>first_assum ACCEPT_TAC)
>-(irule exec_I64_LT_S'>>first_assum ACCEPT_TAC)
>-(
  simp[exec_list_cons,wl_value_wl_word,exec_I64_AND]
  >>simp[exec_I64_EQZ]
  >>qpat_x_assum `word_cmp _ _ _ = _` mp_tac
  >>(Cases_on`wa`>>Cases_on`wb`>>simp[labSemTheory.word_cmp_def,wl_word_def])
  >>simp[AND_1]
)
>-(irule exec_I64_NE'>>first_assum ACCEPT_TAC)
>-(irule exec_I64_GE_U'>>first_assum ACCEPT_TAC)
>-(irule exec_I64_GE_S'>>first_assum ACCEPT_TAC)
>-(
  simp[exec_list_cons,wl_value_wl_word,exec_I64_AND,exec_I64_CONST,exec_I64_NE]
  >>qpat_x_assum `word_cmp _ _ _ = _` mp_tac
  >>(Cases_on`wa`>>Cases_on`wb`>>simp[labSemTheory.word_cmp_def,wl_word_def])
  >>simp[AND_1]
)
QED

Theorem nonzero_b2w:
  nonzero (I32 (b2w v)) = SOME v
Proof
  Cases_on‘v’>>rw[nonzero_def]
QED

Theorem exec_GLOBAL_SET_drule:
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

Theorem exec_GLOBAL_SET:
  r < LENGTH t.globals ∧
  LENGTH t.globals <= 4294967296 ⇒
  exec (GLOBAL_SET r) (push v t) = (RNormal, t with globals := LUPDATE v r t.globals)
Proof
  rw[GLOBAL_SET_def,exec_def]
  >>simp[set_global_def]
QED

(* irule?? *)
Theorem state_rel_set_var:
  state_rel c s t ∧
  wl_value v = w ∧
  n < LENGTH t.globals ⇒
  state_rel c (set_var n v s) (t with globals := LUPDATE w n t.globals)
Proof
  rw[state_rel_def,wasm_state_ok_def,regs_rel_def,EL_LUPDATE,set_var_def,FLOOKUP_UPDATE]
  >>gvs[bool_case_eq]
  >>metis_tac[]
QED

(* a proof for each case *)

Theorem compile_Skip:
  ^(get_goal "Skip")
Proof
  rpt strip_tac
  >> gvs [compile_def,exec_def,stackSemTheory.evaluate_def]
  >> qexists_tac `0`
  >> fs[res_rel_def]
QED

Theorem res_rel_SOME:
  x ≠ Error ⇒
  res_rel (SOME x) t_res stk_pair ⇒ t_res ≠ RNormal
Proof
  Cases_on`stk_pair`
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem compile_Seq:
  ^(get_goal "Seq")
Proof
rpt strip_tac
>>fs[stack_asm_ok_def,compile_def]
>>qpat_x_assum `evaluate _ = _` mp_tac
>>once_rewrite_tac[evaluate_def]
>>rpt$peel[]
>-(
  (* c1 finishes normally *)
  fs[stack_wasm_ok_def] (* unfold ‘stack_wasm_ok c (Seq c1 c2)’ *)
  >>first_x_assum drule (* use IH *)
  >>strip_tac
  >>strip_tac
  >>fs[]
  >>rename1 `evaluate (c1,s) = (_,s1)`
  >>rename1 `exec_list (flatten (compile c1)) (t with clock := ck1 + t.clock) = (t_res1, t1)`
  >>`t_res1 = RNormal` by fs[res_rel_def] (* because s_res1 is NONE *)
  >>first_x_assum drule
  >>strip_tac
  >>rename1 `exec_list (flatten (compile c2)) (t1 with clock := ck2 + t1.clock) = _`
  >>qexists_tac`ck2+ck1`
  >>subgoal `exec_list (flatten (compile c1)) (t with clock := ck2 + ck1 + t.clock) = (t_res1, t1 with clock := ck2 + t1.clock)`
  >-(
    `t_res1 ≠ RTimeout` by simp[]
    >>drule_all exec_list_add_clock
    >>strip_tac
    >>pop_assum $ qspec_then`ck2`mp_tac
    >>simp[]
  )
  >>simp[exec_list_append]
  (* goal: res_rel s_res t_res (t.stack,t_fin.stack) *)
  (* we have ‘res_rel NONE t_res1 (t.stack,t1.stack)’; note that ‘t1.stack = t.stack’ (from ‘res_rel NONE t_res1 (t.stack,t1.stack)’) *)
  >>‘t1.stack = t.stack’ by (qpat_x_assum ‘res_rel NONE t_res1 (t.stack,t1.stack)’ mp_tac >> simp[res_rel_def])
  >>metis_tac[] (*equational*)
)
>>rename1 `evaluate (c1,s) = (s_res1,s1)`
>>strip_tac
>>(Cases_on`s_res1`>>gvs[]) (* obtain x where ‘s_res1 = SOME x’ *)
>>fs[stack_wasm_ok_def]
>>first_x_assum drule
>>strip_tac
>>imp_res_tac res_rel_SOME
>>qexists_tac`ck`
>>simp[exec_list_append]
QED

Theorem res_rel_RBreak:
  res_rel res (RBreak n) stack_pair ⇒ F
Proof
  Cases_on`stack_pair`
  >>(Cases_on`res`>-simp[res_rel_def])
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RInvalid:
  res_rel res RInvalid stack_pair ⇒ F
Proof
  Cases_on`stack_pair`
  >>(Cases_on`res`>-simp[res_rel_def])
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RTrap:
  res_rel res RTrap stack_pair ⇒ F
Proof
  Cases_on`stack_pair`
  >>(Cases_on`res`>-simp[res_rel_def])
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RTimeout:
  res_rel res RTimeout stack_pair <=> res = SOME TimeOut
Proof
  Cases_on`stack_pair`
  >>(Cases_on`res`>-simp[res_rel_def])
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RHalt:
  res_rel res RHalt stack_pair <=> (∃x. res = SOME (Halt x)) ∨ (∃x. res = SOME (FinalFFI x))
Proof
  Cases_on`stack_pair`
  >>(Cases_on`res`>-simp[res_rel_def])
  >>(Cases_on`x`>>simp[res_rel_def])
QED

(* NO.
Theorem res_rel_stack:
  res_rel s_res t_res (stk0, stk1) ⇒
  ∀stk. res_rel s_res t_res (stk0++stk, stk1++stk)
Proof
  Cases_on`s_res`>-simp[res_rel_def]
  >>(Cases_on`x`>>simp[res_rel_def])
QED
*)

Theorem exec_list_add_clock_RNormal:
  exec_list p t = (RNormal, t') ⇒
  exec_list p (t with clock := ck + t.clock) = (RNormal, t' with clock := ck + t'.clock)
Proof
  simp[exec_list_add_clock]
QED

Theorem push_with_clock:
  push v t with clock updated_by f = push v (t with clock updated_by f)
Proof
  simp[push_def]
QED

Theorem res_rel_RReturn:
  res_rel res RReturn (stk0, stk1) <=>
  ((∃wl. res = SOME (Result    wl)) ∧ oHD stk1 = SOME (I32 0w)) ∨
  ((∃wl. res = SOME (Exception wl)) ∧ oHD stk1 = SOME (I32 1w))
Proof
  Cases_on`res`>-simp[res_rel_def]
  >>(Cases_on`x`>>simp[res_rel_def])
QED

Theorem res_rel_RReturn_stack:
  res_rel res RReturn (stk0, stk1) ∧
  oHD stk1' = oHD stk1 ⇒
  res_rel res RReturn (stk0', stk1')
Proof
  simp[res_rel_RReturn]
QED

Theorem Block_rel:
  exec_list Ins
    (t with <|clock := ck + t.clock; stack := []|>) = (t_res1,t1) ∧
  s_res ≠ SOME Error ∧
  res_rel s_res t_res1 ([], t1.stack) ∧ state_rel c s_fin t1 ⇒
  ∃t_res t_fin.
    exec (Block BlkNil Ins) (t with clock := ck + t.clock) = (t_res,t_fin) ∧
    res_rel s_res t_res (t.stack, t_fin.stack) ∧ state_rel c s_fin t_fin
Proof
rw[exec_def]
>>(Cases_on`t_res1`>>fs[])
>-metis_tac[res_rel_RInvalid]
>-metis_tac[res_rel_RBreak]
>-metis_tac[res_rel_RReturn_stack]
>-metis_tac[res_rel_RTrap]
>-(
  (* RNormal *)
  drule_then (qspec_then`t.stack`assume_tac) exec_Block_BlkNil_RNormal
  (* from ‘res_rel s_res RNormal ([],t1.stack)’ have ‘t1.stack=[]’ *)
  >>‘t1.stack=[]’ by metis_tac[res_rel_RNormal]
  >>fs[res_rel_RNormal])
>-metis_tac[res_rel_RTimeout]
>-metis_tac[res_rel_RHalt]
QED

Theorem compile_If:
  ^(get_goal "If")
Proof
  rpt strip_tac
  >>qpat_x_assum `evaluate _ = _` mp_tac
  >>fs[evaluate_def,stack_wasm_ok_def]
  >>rpt(peel[])
  >>(
    strip_tac
    >>fs[]
    >>first_x_assum $ qspec_then`t with stack:=[]`mp_tac
    >>simp[]
    >>strip_tac
    >>qexists_tac`ck`
    >>simp[compile_def]
    >>drule_all_then assume_tac compile_comp_thm
    >>dxrule_then (qspec_then`ck`mp_tac) exec_list_add_clock_RNormal
    >>simp[]
    >>strip_tac
    >>dxrule_then (fn a=>simp[a]) exec_list_append_RNormal
    >>simp[push_with_clock,exec_If]
    >>simp[push_def]
    (* exec Block *)
    >>metis_tac[Block_rel]
  )
QED

Theorem compile_Call_aux:
  res_rel (SOME s_res) callee_t_res ([], callee_t_fin.stack) ∧
  s_res ≠ Error ∧
  state_rel c s' callee_t_fin ⇒
  ∃t_res t_fin.
    (case callee_t_res of
     | RBreak v1 => (RInvalid, callee_t_fin)
     | RReturn =>
       if callee_t_fin.stack = [] then (RInvalid, callee_t_fin)
       else (RReturn, callee_t_fin)
     | RNormal =>
       if LENGTH callee_t_fin.stack ≠ 1 then (RInvalid, callee_t_fin)
       else (RReturn, callee_t_fin)
     | _ => (callee_t_res, callee_t_fin)
    ) = (t_res, t_fin) ∧
    res_rel (SOME s_res) t_res (t_stack, t_fin.stack) ∧
    state_rel c s' t_fin
Proof
  (Cases_on`callee_t_res`>>simp[])
  >-metis_tac[res_rel_RInvalid]
  >-metis_tac[res_rel_RBreak]
  >-(
    (* RReturn *)
    strip_tac
    >>`∃ret junk. callee_t_fin.stack = ret::junk` by metis_tac[res_rel_RReturn,oHD_SOME_drule]
    >>fs[] (* only res_rel remains *)
    >-(
      dxrule res_rel_RReturn_stack
      >>simp[]
    )
  )
  >-metis_tac[res_rel_RTrap]
  >-fs[res_rel_RNormal]
  >-metis_tac[res_rel_RTimeout]
  >-metis_tac[res_rel_RHalt]
QED

Theorem wasm_state_ok_LLOOKUP_cakeml_ftype_index:
  wasm_state_ok t ⇒
  LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ([], [Tnum Int W32])
Proof
  fs[wasm_state_ok_def]
QED

fun simp1 thm = simp[thm];

Theorem state_rel_with_clock':
  state_rel c s (t with <| clock:=ck; stack:=st ; locals :=l|>) ⇔
  state_rel c s (t with <| clock := ck|>)
Proof
  simp[state_rel_def,wasm_state_ok_def]
QED

Theorem compile_Call_aux2:
  (
    ∀s2 h l1' l2'.
      s.clock ≠ 0 ∧
      evaluate (prog, dec_clock (set_var link_reg (Loc l m) s)) =
      (SOME (Exception (Loc l1' l2')),s2) ∧ handler = SOME (h,l1',l2') ⇒
      ∀s_res' s_fin' t'.
        evaluate (h,s2) = (s_res',s_fin') ∧ stack_wasm_ok c h ∧
        s_res' ≠ SOME Error ∧ state_rel c s2 t' ⇒
        ∃ck t_res t_fin.
          exec_list (flatten (compile h))
            (t' with clock := ck + t'.clock) = (t_res,t_fin) ∧
          res_rel s_res' t_res (t'.stack,t_fin.stack) ∧
          state_rel c s_fin' t_fin
  ) ∧
  (
    ∀s2.
      s.clock ≠ 0 ∧
      evaluate (prog, dec_clock (set_var link_reg (Loc l m) s)) =
      (SOME (Result (Loc l m)),s2) ⇒
      ∀s_res' s_fin' t'.
        evaluate (ret_handler,s2) = (s_res',s_fin') ∧
        stack_wasm_ok c ret_handler ∧ s_res' ≠ SOME Error ∧
        state_rel c s2 t' ⇒
        ∃ck t_res t_fin.
          exec_list (flatten (compile ret_handler))
            (t' with clock := ck + t'.clock) = (t_res,t_fin) ∧
          res_rel s_res' t_res (t'.stack,t_fin.stack) ∧
          state_rel c s_fin' t_fin
  ) ∧
  (
    s.clock ≠ 0 ⇒
    ∀s_res' s_fin' t'.
      evaluate (prog, dec_clock (set_var link_reg (Loc l m) s)) =
      (s_res',s_fin') ∧ stack_wasm_ok c prog ∧ s_res' ≠ SOME Error ∧
      state_rel c (dec_clock (set_var link_reg (Loc l m) s)) t' ⇒
      ∃ck t_res t_fin.
        exec_list (flatten (compile prog)) (t' with clock := ck + t'.clock) =
        (t_res,t_fin) ∧ res_rel s_res' t_res (t'.stack,t_fin.stack) ∧
        state_rel c s_fin' t_fin
  ) ∧
  (
    if s.clock = 0 then (SOME TimeOut, empty_env s) else
    case evaluate (prog, dec_clock (set_var link_reg (Loc l m) s)) of
      (NONE,s2) => (SOME Error,s2)
    | (SOME (Result x),s2) =>
      if x ≠ Loc l m then (SOME Error,s2)
      else evaluate (ret_handler,s2)
    | (SOME (Exception x'),s2) =>
      (case handler of
         NONE => (SOME (Exception x'),s2)
       | SOME (h,l1',l2') =>
         if x' ≠ Loc l1' l2' then (SOME Error,s2)
         else evaluate (h,s2))
    | (res2,s2) => (res2,s2)
  ) = (s_res,s_fin) ∧
  conf_ok c ∧
  stack_wasm_ok c (stackLang$Call (SOME (ret_handler, link_reg, l, m)) callee handler) ∧
  s_res ≠ SOME Error ∧
  state_rel c s t ∧
  lookup prog_index s.code = SOME prog ⇒

  ∃ck t_res t_fin.
    (λ(res1,s1).
         if res1 = RNormal then
           exec
             (If BlkNil
                (flatten
                   (case handler of
                      NONE => List [I32_CONST 1w; RETURN]
                    | SOME (exn_hdlr,v2) => compile exn_hdlr))
                (flatten (compile ret_handler))) s1
         else (res1,s1))
      (exec
         (Call (n2w (prog_index + LENGTH wasm_support_function_list)))
         (t with
          <|clock := ck + t.clock;
            globals := LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>)) =
    (t_res,t_fin) ∧ res_rel s_res t_res (t.stack,t_fin.stack) ∧
    state_rel c s_fin t_fin
Proof
rpt strip_tac
>>`code_rel s.code t.funcs ∧ wasm_state_ok t` by fs[state_rel_def]
>>simp[first (can (find_term (can (match_term“wasmLang$Call”))) o concl) (CONJUNCTS exec_def)]
(* show `LLOOKUP t.funcs ((x + LENGTH wasm_support_function_list) MOD 4294967296) = SOME ...`
   using `lookup prog_index s.code = SOME prog` *)
>>`LLOOKUP t.funcs (prog_index + LENGTH wasm_support_function_list) =
   SOME
     <|ftype := cakeml_ftype_index; locals := [];
       body := flatten (compile prog)|>`
  by fs[code_rel_def]
>>subgoal `LENGTH wasm_support_function_list + prog_index < 4294967296`
>-(
  `LENGTH t.funcs < 4294967296` by fs[state_rel_def,wasm_state_ok_def]
  >>fs[LLOOKUP_EQ_EL]
)
(* done *)
>>pop_assum simp1
>>DEP_REWRITE_TAC[wasm_state_ok_LLOOKUP_cakeml_ftype_index]
>>simp[]

>>simp[pop_n_def]
>>`t.clock=s.clock` by fs[state_rel_def]
(* timeout or not? *)
>>(Cases_on`s.clock=0`>>fs[])
>-(
  (* timeout case *)
  qexists_tac`0` (*ck*)
  >>gvs[res_rel_RTimeout]
  >>irule state_rel_empty_env_t_with_globals
  >>simp[wasmSemTheory.state_component_equality]
  >>metis_tac[]
  (* auto[state_rel_empty_env_t_with_globals] *)
)
(* non-timeout case *)
>>gvs[pair_case_eq,option_case_eq]
>>rename1 `evaluate (prog, dec_clock (set_var link_reg (Loc l m) s)) = (SOME s_res_call, s_call)`
(* use IH 2 to obtain ck, t_res_call, t_call *)
(* premise 1/3 *)
>>subgoal `stack_wasm_ok c prog`
>-(
  qpat_x_assum `state_rel c s t` mp_tac >> simp[state_rel_def]
  >>metis_tac[]
)
(* premise 2/3 *)
>>`s_res_call ≠ Error` by gvs[AllCaseEqs()]
(* premise 3/3 *)
>>subgoal `state_rel c (dec_clock (set_var link_reg (Loc l m) s)) (t with <|clock:=t.clock-1; stack:=[]; locals:=[]; globals:=LUPDATE (I64 (n2w l<<1)) link_reg t.globals|>)`
>-(
  simp[dec_clock_def]
  >>subgoal `state_rel c (s with clock:=s.clock-1) (t with clock:=t.clock-1)`
  >-(
    `t.clock=s.clock` by fs[state_rel_def]
    >>simp[state_rel_with_clock]
  )
  >>`wl_value (Loc l m) = I64 (n2w l<<1)` by simp[wl_value_def]
  >>subgoal `link_reg < LENGTH (t with clock:=t.clock-1).globals`
  >-(
    qpat_x_assum `stack_wasm_ok c (Call _ _ _)` mp_tac >> simp[stack_wasm_ok_def]
    >>(qpat_x_assum `state_rel c s t` mp_tac >> simp[state_rel_def,regs_rel_def])
  )
  >>dxrule_all state_rel_set_var
  >>simp[state_rel_with_clock'])
>>first_x_assum dxrule_all (* apply IH *)
>>strip_tac
>>fs[]
>>rename1 `exec_list (flatten (compile prog)) _ = (t_call_res, t_call)`
>>(Cases_on`t_call_res`>>simp[] (* 7 subgoals *))
>-fs[res_rel_RInvalid]
>-fs[res_rel_RBreak]
>-(
  (* RReturn *)
  qpat_x_assum `res_rel (SOME s_res_call) RReturn ([],t_call.stack)` mp_tac
  >>simp[res_rel_RReturn]
  >>strip_tac (* 2 subgoals: Result, Exception *)
  >-(
    (* Result *)
    (Cases_on`wl = Loc l m`>>fs[])
    (* use IH 1 *)
    >>`stack_wasm_ok c ret_handler` by fs[stack_wasm_ok_def]
    (* BE CAREFUL WITH ∀t'!! *)
    >>`state_rel c s_call (t_call with stack:=[])` by metis_tac[state_rel_with_stack]
    >>(first_x_assum drule_all >> strip_tac (* apply IH; obtain ck' *))
    >>qexists_tac`ck+ck'`

    >>subgoal `exec_list (flatten (compile prog))
              (t with
               <|clock := ck + ck' + s.clock − 1; stack := []; locals := [];
                 globals := LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>) =
            (RReturn, t_call with clock:=ck'+t_call.clock)`
    >-(
      qpat_x_assum `exec_list (flatten (compile prog)) _ = _` assume_tac
      >>drule exec_list_add_clock
      >>simp[]
    )
    >>pop_assum simp1
    >>(dxrule oHD_SOME_drule >> strip_tac)
    >>simp[exec_def,pop_def,nonzero_def]
    >>fs[]
    >>(Cases_on`t_res`>>fs[res_rel_RInvalid,res_rel_RBreak,res_rel_RTrap,res_rel_RTimeout,res_rel_RHalt])
    >-metis_tac[res_rel_RReturn_stack]
    >-(fs[res_rel_RNormal]>>metis_tac[state_rel_with_stack])
  )
  >-(
    (* Exception *)
    Cases_on`handler`>>fs[]
    >-((* no exn handler *)
      qexists_tac`ck`
      >>gvs[]
      >>(dxrule oHD_SOME_drule >> strip_tac)
      >>simp[exec_def,pop_def,nonzero_def]
      >>simp[exec_I32_CONST,RETURN_def,exec_def]
      (* res_rel and state_rel *)
      >>simp[res_rel_def,push_def,oHD_def] (* res_rel proved *)
      >>metis_tac[state_rel_with_stack]
    )
    (* has exn handler *)
    >>(`∃eh eh_l eh_m. x = (eh, eh_l, eh_m)` by metis_tac[pair_CASES]>>gvs[])
    >>(Cases_on`wl = Loc eh_l eh_m`>>fs[])
    >>`stack_wasm_ok c eh` by fs[stack_wasm_ok_def]
    (* BE CAREFUL WITH ∀t'!! *)
    >>`state_rel c s_call (t_call with stack:=[])` by metis_tac[state_rel_with_stack]
    >>(first_x_assum drule_all >> strip_tac (* apply IH; obtain ck' *))
    >>qexists_tac`ck+ck'`
    >>subgoal `exec_list (flatten (compile prog))
              (t with
               <|clock := ck + ck' + s.clock − 1; stack := []; locals := [];
                 globals := LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>) =
            (RReturn, t_call with clock:=ck'+t_call.clock)`
    >-(
      qpat_x_assum `exec_list (flatten (compile prog)) _ = _` assume_tac
      >>drule exec_list_add_clock
      >>simp[]
    )
    >>pop_assum simp1
    >>(dxrule oHD_SOME_drule >> strip_tac)
    >>simp[exec_def,pop_def,nonzero_def]
    >>fs[]
    >>(Cases_on`t_res`>>fs[res_rel_RInvalid,res_rel_RBreak,res_rel_RTrap,res_rel_RTimeout,res_rel_RHalt])
    >-metis_tac[res_rel_RReturn_stack]
    >-(fs[res_rel_RNormal]>>metis_tac[state_rel_with_stack])
  )
)
>-metis_tac[res_rel_RTrap]
>-fs[res_rel_RNormal]
>-(
  (* RTimeout in call *)
  qexists_tac`ck`
  >>simp[]
  >>gvs[res_rel_RTimeout]
)
>-(
  (* RHalt in call *)
  qexists_tac`ck`
  >>simp[]
  >>gvs[res_rel_RHalt]
)
QED

Theorem get_var_set_var[simp]:
get_var r (set_var r v s) = SOME v
Proof
simp[get_var_def,set_var_def,FLOOKUP_SIMP]
QED

Theorem compile_Call:
  ^(get_goal "Call")
Proof
rpt strip_tac
>>`wasm_state_ok t ∧ code_rel s.code t.funcs` by fs[state_rel_def]
>>(Cases_on`ret`>>gvs[]) (* tail-call or not? *)
>-(
  (* tail-call case *)
  Cases_on`handler`>>fs[evaluate_def,option_case_eq]
  >>(Cases_on`dest`>>simp[])
  >-(
    (* RETURN_CALL case *)
    simp[compile_def,tail_call_def]
    >>simp[RETURN_CALL_def,exec_def]
    (* show `LLOOKUP t.funcs ((x + LENGTH wasm_support_function_list) MOD 4294967296) = SOME ...`
       using `find_code (INL x) s.regs s.code = SOME prog` *)
    >>fs[find_code_def]
    >>rename1 `lookup prog_index s.code = SOME prog`
    >>`LLOOKUP t.funcs (prog_index + LENGTH wasm_support_function_list) =
       SOME
         <|ftype := cakeml_ftype_index; locals := [];
           body := flatten (compile prog)|>`
      by fs[code_rel_def,find_code_def]
    >>subgoal `LENGTH wasm_support_function_list + prog_index < 4294967296`
    >-(
      `LENGTH t.funcs < 4294967296` by fs[state_rel_def,wasm_state_ok_def]
      >>fs[LLOOKUP_EQ_EL]
    )
    (* done *)
    >>pop_assum simp1
    >>‘LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ([], [Tnum Int W32])’ by fs[wasm_state_ok_def]
    >>pop_assum simp1
    >>simp[pop_n_def]
    (* timeout or not? *)
    >>`t.clock=s.clock` by fs[state_rel_def]
    >>(Cases_on`s.clock=0`>>fs[])
    >-(
      (* timeout case *)
      qexists_tac`0` (*∃ck*)
      >>rw[] (* 2 goals: res_rel and state_rel *)
      >-simp[res_rel_def]
      >>`(t with clock:=0) = t` by metis_tac[wasm_state_useless_fupd]
      >>pop_assum simp1
      >>metis_tac[state_rel_empty_env]
    )
    (* non-timeout case *)
    >>gvs[pair_case_eq,option_case_eq] (* `evaluate (prog,dec_clock s)` does not result in Error *)
    >>`stack_wasm_ok c prog` by (fs[state_rel_def]>>metis_tac[])
    >>subgoal `state_rel c (dec_clock s) (t with <| clock := s.clock-1; stack:=[]; locals:=[] |>)`
    >-(
      simp[dec_clock_def]
      >>metis_tac[state_rel_with_clock,state_rel_with_stack,state_rel_with_locals]
    )
    >>first_x_assum drule_all (* IH *)
    >>strip_tac
    >>fs[]
    >>rename1 `res_rel (SOME s_res) callee_t_res ([], callee_t_fin.stack)`
    >>qexists_tac`ck`
    >>gvs[]
    >>metis_tac[compile_Call_aux]
  ) (* RETURN_CALL case done *)
  >-(
    (* RETURN_CALL_INDIRECT case *)
    qpat_x_assum `code_rel s.code t.funcs` mp_tac >> simp[code_rel_def]
    >>subgoal `∃prog_index. get_var y s = SOME (Loc prog_index 0)`
    >-(
      fs[find_code_def,get_var_def]
      >>gvs[AllCaseEqs()]
    )
    >>`lookup prog_index s.code = SOME prog` by fs[find_code_def,get_var_def]
    >>(strip_tac >> pop_assum $ drule_then assume_tac)
    >>`prog_index + LENGTH wasm_support_function_list < LENGTH t.funcs` by fs[LLOOKUP_EQ_EL]
    >>`LENGTH t.funcs < 4294967296` by fs[wasm_state_ok_def]
    >>`LLOOKUP t.func_table prog_index = SOME (n2w (LENGTH wasm_support_function_list + prog_index))` by fs[wasm_state_ok_def]
    (* *)
    >>simp[compile_def]
    (* timeout or not? *)
    >>`t.clock=s.clock` by fs[state_rel_def]
    >>(Cases_on`s.clock=0`>>fs[])
    >-(
      (* timeout case *)
      qexists_tac`0` (*ck*)
      >>subgoal ‘exec (GLOBAL_GET y) t = (RNormal, push (wl_value (Loc prog_index 0)) t)’
      >-metis_tac[exec_GLOBAL_GET,state_rel_with_clock]
      >>once_rewrite_tac[exec_list_cons]
      >>`(t with clock:=0) = t` by metis_tac[wasm_state_useless_fupd]
      >>pop_assum simp1
      >>pop_assum simp1
      >>simp[wl_value_def]
      >>once_rewrite_tac[exec_list_cons]
      >>simp[exec_I64_CONST]
      >>once_rewrite_tac[exec_list_cons]
      >>simp[exec_I64_SHR_U]
      >>once_rewrite_tac[exec_list_cons]
      >>simp[exec_I32_WRAP_I64]
      >>simp[RETURN_CALL_INDIRECT_def,exec_def] (* gets ugly from here *)
      >>simp[dest_i32_def]
      >>simp[lookup_func_tables_def, prove(“LLOOKUP [^t.func_table] 0 = SOME t.func_table”, simp[LLOOKUP_def])]
      (* from `prog_index < LENGTH t.funcs` and `wasm_state_ok t` have `prog_index < 2**32` *)
      >>subgoal `w2n ((w2w:word64->word32) (n2w prog_index ≪ 1 ⋙ 1)) = prog_index`
      >-(
        `prog_index < 4294967296` by decide_tac
        >>simp[lsl_lsr,w2w_n2w]
      )
      >>pop_assum simp1
      >>`LLOOKUP t.func_table prog_index = SOME (n2w (LENGTH wasm_support_function_list + prog_index))` by fs[wasm_state_ok_def]
      >>simp[]
      >>`LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ([], [Tnum Int W32])` by fs[wasm_state_ok_def]
      >>simp[pop_n_def] (* get rid of all 'case's *)
      (* res_rel and state_rel *)
      >>(strip_tac>-simp[res_rel_RTimeout])
      >>metis_tac[state_rel_empty_env]
    )
    (* non-timeout case *)
    >>gvs[pair_case_eq,option_case_eq] (* `evaluate (prog,dec_clock s)` does not result in Error *)
    >>`stack_wasm_ok c prog` by (fs[state_rel_def]>>metis_tac[])
    >>subgoal `state_rel c (dec_clock s) (t with <| clock := s.clock-1; stack:=[]; locals:=[] |>)`
    >-(
      simp[dec_clock_def]
      >>metis_tac[state_rel_with_clock,state_rel_with_stack,state_rel_with_locals]
    )
    >>first_x_assum drule_all (* IH *)
    >>strip_tac
    >>fs[]
    >>rename1 `res_rel (SOME s_res) callee_t_res ([], callee_t_fin.stack)`
    >>qexists_tac`ck`
    >>subgoal ‘exec (GLOBAL_GET y) (t with clock := ck + s.clock) = (RNormal, push (wl_value (Loc prog_index 0)) (t with clock := ck + s.clock))’
    >-(
      `get_var y (s with clock:=ck+s.clock) = SOME (Loc prog_index 0)` by simp[]
      >>metis_tac[exec_GLOBAL_GET,state_rel_with_clock]
    )
    >>once_rewrite_tac[exec_list_cons]
    >>pop_assum simp1
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I64_CONST]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[wl_value_def,exec_I64_SHR_U]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I32_WRAP_I64]
    >>simp[RETURN_CALL_INDIRECT_def,exec_def] (* cases appear *)
    >>simp[dest_i32_def]
    >>simp[lookup_func_tables_def, prove(“LLOOKUP [^t.func_table] 0 = SOME t.func_table”, simp[LLOOKUP_def])]
    (* from `prog_index < LENGTH t.funcs` and `wasm_state_ok t` have `prog_index < 2**32` *)
    >>subgoal `w2n ((w2w:word64->word32) (n2w prog_index ≪ 1 ⋙ 1)) = prog_index`
    >-(
      `prog_index < 4294967296` by decide_tac
      >>simp[lsl_lsr,w2w_n2w]
    )
    >>pop_assum simp1
    >>`LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ([], [Tnum Int W32])` by fs[wasm_state_ok_def]
    >>simp[pop_n_def]
    >>(qpat_x_assum `exec_list (flatten (compile prog)) _ = _` mp_tac >> simp[])
    >>(strip_tac >> pop_assum kall_tac)
    >>metis_tac[compile_Call_aux]
  ) (* RETURN_CALL_INDIRECT case done *)
) (* tail-call case done *)
>-(
  (* non-tail-call case *)
  `∃ret_handler link_reg l m. x = (ret_handler, link_reg, l, m)` by metis_tac[pair_CASES]
  >>gvs[evaluate_def]
  >>(Cases_on `find_code dest (s.regs \\ link_reg) s.code` >> fs[] (* have ‘find_code ... = SOME ...’ *))
  >>(Cases_on`dest` >> fs[] (* direct call or indirect call? *))
  >-(
    (* CALL case *)
    fs[find_code_def]
    >>rename1 ‘lookup prog_index s.code = SOME prog’
    >>simp[compile_def]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I64_CONST]
    >>once_rewrite_tac[exec_list_cons]
    >>subgoal `∀ck. exec (GLOBAL_SET link_reg) (push (I64 (n2w l ≪ 1)) (t with clock:=ck+t.clock)) =
      (RNormal,t with <|clock:=ck+t.clock; globals := LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>)`
    >-(
      strip_tac
      >>`link_reg < LENGTH (t with clock:=ck+t.clock).globals ∧ LENGTH (t with clock:=ck+t.clock).globals ≤ 4294967296` by fs[state_rel_def,regs_rel_def,conf_ok_def,stack_wasm_ok_def]
      >>dxrule_all exec_GLOBAL_SET
      >>simp[]
    )
    >>pop_assum simp1
    >>simp[CALL_def,exec_list_cons]
    >>(dxrule_all compile_Call_aux2 >> rewrite_tac[] >> NO_TAC)
  )
  >-(
    (* CALL_INDIRECT case *)
    simp[compile_def]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I64_CONST]
    >>once_rewrite_tac[exec_list_cons]
    >>subgoal `∀ck. exec (GLOBAL_SET link_reg) (push (I64 (n2w l << 1)) (t with clock := ck+t.clock)) =
                    (RNormal, t with <|clock := ck+t.clock; globals := LUPDATE (I64 (n2w l << 1)) link_reg t.globals|>)`
    >-((* by auto[exec_GLOBAL_SET] *)
      strip_tac
      >>`LENGTH (t with clock := ck+t.clock).globals <= 4294967296 /\ link_reg < LENGTH (t with clock:=ck+t.clock).globals` by fs[stack_wasm_ok_def,state_rel_def,regs_rel_def,conf_ok_def]
      >>dxrule_all exec_GLOBAL_SET
      >>simp[]
    )
    >>pop_assum simp1
    >>fs[find_code_def]
    >>`∃prog_index. FLOOKUP (s.regs\\link_reg) y = SOME (Loc prog_index 0)` by fs[AllCaseEqs()]
    >>subgoal ‘∀ck. exec (GLOBAL_GET y) (t with <|clock:=ck+t.clock; globals:=LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>) =
                    (RNormal, push (wl_value (Loc prog_index 0)) (t with <|clock:=ck+t.clock; globals:=LUPDATE (I64 (n2w l ≪ 1)) link_reg t.globals|>))’
    (* y: register holding pointer to callee *)
    >-(
      strip_tac
      >>subgoal `get_var y ((set_var link_reg (Loc l m) s) with clock:=ck+s.clock) = SOME (Loc prog_index 0)`
      >-(
        subgoal `get_var y (set_var link_reg (Loc l m) s) = SOME (Loc prog_index 0)`
        >-(
          Cases_on`y=link_reg`>-fs[]
          >>simp[get_var_def,set_var_def,FLOOKUP_SIMP]
          >>metis_tac[DOMSUB_FLOOKUP_NEQ]
        )
        >>simp[get_var_def]
      )
      >>`t.clock=s.clock` by fs[state_rel_def]
      >>subgoal `state_rel c ((set_var link_reg (Loc l m) s) with clock:=ck+s.clock) (t with <|clock:=ck+t.clock; globals:=LUPDATE (I64 (n2w l<<1)) link_reg t.globals|>)`
      >-(
        subgoal `state_rel c (set_var link_reg (Loc l m) s) (t with globals:=LUPDATE (I64 (n2w l<<1)) link_reg t.globals)`
        >-(
          irule state_rel_set_var
          >>`link_reg < LENGTH t.globals` by fs[stack_wasm_ok_def,state_rel_def,regs_rel_def]
          >>simp[wl_value_def]
        )
        >>metis_tac[state_rel_with_clock]
      )
      >>(dxrule_all exec_GLOBAL_GET >> simp[])
    )
    >>once_rewrite_tac[exec_list_cons]
    >>pop_assum simp1
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I64_CONST]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I64_SHR_U,wl_value_def]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[exec_I32_WRAP_I64]
    >>once_rewrite_tac[exec_list_cons]
    >>simp[CALL_INDIRECT_def, first (can (find_term (can (match_term“CallIndirect”))) o concl) (CONJUNCTS exec_def)] (* exec CALL_INDIRECT *)
    >>simp[dest_i32_def]
    >>simp[lookup_func_tables_def, LLOOKUP_def]
    >>fs[]
    >>rename1 `lookup prog_index s.code = SOME prog`
    >>`LLOOKUP t.funcs (prog_index + LENGTH wasm_support_function_list) =
       SOME
         <|ftype := cakeml_ftype_index; locals := [];
           body := flatten (compile prog)|>`
      by fs[code_rel_def,find_code_def]
    >>subgoal `LENGTH wasm_support_function_list + prog_index < 4294967296`
    >-(
      `LENGTH t.funcs < 4294967296` by fs[state_rel_def,wasm_state_ok_def]
      >>fs[LLOOKUP_EQ_EL]
    )
    >>subgoal `w2n ((w2w:word64->word32) (n2w prog_index ≪ 1 ⋙ 1)) = prog_index`
    >-(
      `prog_index < 4294967296` by decide_tac
      >>simp[lsl_lsr,w2w_n2w]
    )
    >>pop_assum simp1
    >>subgoal `LLOOKUP t.func_table prog_index = SOME (n2w (LENGTH wasm_support_function_list + prog_index))`
    >-(
      `prog_index + LENGTH wasm_support_function_list < LENGTH t.funcs` by fs[LLOOKUP_EQ_EL]
      >>`prog_index < LENGTH t.funcs` by decide_tac
      >>fs[wasm_state_ok_def]
    )
    >>pop_assum simp1
    >>(dxrule_all compile_Call_aux2 >> rewrite_tac[] >> NO_TAC)
  )
)
QED

Theorem compile_Inst:
  ^(get_goal "Inst")
Proof cheat
(*
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
    >>drule exec_GLOBAL_SET_drule
    >>simp[]
    >>CONV_TAC(DEPTH_CONV record_canon_simp_conv)
    >>impl_keep_tac
    >-fs[stack_wasm_ok_def,inst_ok_def,reg_ok_def,conf_ok_def,state_rel_def,regs_rel_def]
    >>rw[]
    >-simp[res_rel_def]
    >>irule state_rel_set_var
    >>fs[word_exp_def,wl_value_def]
  )
  >~[`Arith`]
  >-(
    rename1`Arith a`>>Cases_on`a`
    >~[`Binop`] >- cheat
    >~[`Shift`] >- cheat
    >~[`Div`] >- cheat
    >~[`LongMul`] >- cheat
    >~[`LongDiv`] >- fs[stack_wasm_ok_def,inst_ok_def,arith_ok_def,conf_ok_def]
    >~[`AddCarry`] >- cheat
    >~[`AddOverflow`] >- cheat
    >~[`SubOverflow`] >- cheat
  )
  >~[`Mem`] >-
    cheat
  >~[`FP`] >-
    gvs[stack_wasm_ok_def,inst_ok_def,oneline fp_ok_def,AllCasePreds(),fp_reg_ok_def,conf_ok_def]
*)
QED

Theorem compile_While:
  ^(get_goal "While")
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
rpt strip_tac
>>qpat_x_assum `evaluate _ = _` mp_tac
>>simp[evaluate_def]
>>rpt$peel[]
>>strip_tac
>>qexists_tac`0`
>>simp[compile_def]
(* Goal: ∃t_res t_fin. exec_list [I32_CONST 0w; RETURN] t = (res1,t1) ∧ ... *)
>>simp[exec_list_cons,exec_I32_CONST,exec_RETURN]
(* prove res_rel *)
>>gvs[res_rel_def,push_def]
(* prove state_rel *)
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
