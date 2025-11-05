(*
  Correctness proof for compilation from stackLang to CWasm
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

(* ⌂compiler definition (TODO: move to another file when ready) *)

(* reg_imm = Reg reg | Imm ('a imm) *)
Definition comp_ri_def:
  comp_ri (Reg r) = GLOBAL_GET r ∧
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
        GLOBAL_GET r; I32_WRAP_I64; I32_CONST 1w; I32_SHR_U;
        RETURN_CALL_INDIRECT ftype
      ]
  ) ∧
  compile (stackLang$Call (SOME (ret_hdlr, lr, ret_loc)) dest exn) =
  (
    let exn_hdlr =
      case exn of
        NONE => Nil
      | SOME (exn_hdlr, _) => compile exn_hdlr
    in
    let rest =
      wasmLang$If BlkNil (flatten exn_hdlr) (flatten (compile ret_hdlr))
    in
    let call_sequence =
      case dest of
        INL l => [CALL l; rest]
      | INR r => [GLOBAL_GET r; I32_WRAP_I64; I32_CONST 1w; I32_SHR_U; CALL_INDIRECT ftype; rest]
    in
    List (
      I64_CONST 0w :: GLOBAL_SET lr :: call_sequence
    )
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
    (* LLOOKUP globals n = SOME (wl_value w) *)
    EL n globals = wl_value w
  )
End

(* TODO: code_rel: we can find long mul at const index i *)

Definition cakeml_ftype_index_def:
  cakeml_ftype_index = 0w:word32
End

(*
Datatype: func =
  <| ftype  : index
   ; locals : valtype list
   ; body   : expr
   |>
End
*)

Definition code_rel_def:
  code_rel (s_code: 64 stackLang$prog sptree$num_map) (t_funcs: func list) =
  ∀i prog.
    lookup i s_code = SOME prog ==>
    oEL (LENGTH wasm_support_function_list + i) t_funcs = SOME
      <|
        ftype := cakeml_ftype_index;
        locals := []; (* we don't use wasm local variables lol *)
        body := flatten (compile prog)
      |>
End

Definition wasm_state_ok_def:
  wasm_state_ok ^t <=>
  LENGTH t.funcs < 4294967296 ∧
  (* presence of support functions *)
  (∀i. i < LENGTH wasm_support_function_list ==> oEL i t.funcs = SOME (EL i wasm_support_function_list)) ∧
  (* func type table *)
  oEL (w2n cakeml_ftype_index) t.types = SOME ([], [Tnum Int W32]) ∧
  (* func table *)
  (∀i. i < LENGTH t.func_table ⇒ EL i t.func_table = LENGTH wasm_support_function_list + i)
End

Definition state_rel_def:
  state_rel c ^s ^t ⇔
    ¬ s.use_stack ∧ ¬ s.use_store ∧ ¬ s.use_alloc ∧ ¬ s.be ∧
    empty_buffer s.code_buffer ∧ empty_buffer s.data_buffer ∧
    wasm_state_ok t ∧
    (* *)
    regs_rel c s.regs t.globals ∧
    s.clock = t.clock ∧
    code_rel s.code t.funcs
End

Definition res_rel_def:
  (res_rel NONE r s    ⇔ r = RNormal) ∧
  (res_rel (SOME TimeOut) r s <=> r = RTimeout) ∧
  (res_rel (SOME (Result    _)) r s <=> r = RReturn ∧ oHD s = SOME (I32 0w)) ∧
  (res_rel (SOME (Exception _)) r s <=> r = RReturn ∧ oHD s = SOME (I32 1w)) ∧
  (* ignore Error since we always assume ‘res ≠ SOME Error’ when asked to prove res_rel *)
  (* Halt?? FinalFFI?? *)
  (res_rel (SOME (Halt     _)) r s <=> r ≠ RNormal ∧ ∀n. r ≠ RBreak n) ∧
  (res_rel (SOME (FinalFFI _)) r s <=> r ≠ RNormal ∧ ∀n. r ≠ RBreak n)
End

(* set up for one theorem per case *)

Definition conf_rel_def:
  conf_rel c (s_res, s_fin) t (t_res, t_fin) <=>
    res_rel s_res t_res t_fin.stack ∧
    state_rel c s_fin t_fin ∧
    (t_res = RNormal ⇒ t_fin.stack = t.stack) (* no garbage left on stack *)
End

val goal_tm = “
  λ(p,^s). ∀s_res s_fin t.
    evaluate (p,s) = (s_res, s_fin) ∧
    conf_ok c ∧
    stack_asm_ok c p ∧ (* from stackProps *)
    s_res ≠ SOME Error ∧
    state_rel c s t ⇒
    ∃ck t_res t_fin.
      exec_list (flatten (compile p)) (t with clock := ck + t.clock) = (t_res, t_fin) ∧
      conf_rel c (s_res, s_fin) t (t_res, t_fin)
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
  get_var r s = SOME w ⇒
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
  fs[state_rel_def,wasm_state_ok_def]
QED

Theorem state_rel_with_stack:
  state_rel c s (t with stack updated_by _) = state_rel c s t
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
>-(
  simp[push_def]
  >>metis_tac[state_rel_with_stack]
)
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

(* irule?? *)
Theorem state_rel_set_var:
  state_rel c s t ∧
  wl_value v = w ∧
  n < LENGTH t.globals ⇒
  state_rel c (set_var n v s) (t with globals := LUPDATE w n t.globals)
Proof
  rw[state_rel_def,wasm_state_ok_def,regs_rel_def,EL_LUPDATE,set_var_def,FLOOKUP_UPDATE]
  >>gvs[bool_case_eq]
QED

(* a ⌂proof for each case *)

Theorem compile_Skip:
  ^(get_goal "Skip")
Proof
  rpt strip_tac
  >> gvs [compile_def,exec_def,stackSemTheory.evaluate_def]
  >> qexists_tac `0`
  >> fs[conf_rel_def,res_rel_def]
QED

(* drule *)
Theorem conf_rel_state_rel:
  conf_rel c (s_res, s') t (t_res, t') ⇒
  state_rel c s' t'
Proof
  simp[conf_rel_def]
QED

Theorem res_rel_SOME:
  x ≠ Error ⇒
  res_rel (SOME x) t_res _ ⇒ t_res ≠ RNormal
Proof
Cases_on`x`>>simp[res_rel_def]
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
  first_x_assum drule
  >>strip_tac
  >>strip_tac
  >>fs[]
  >>rename1 `evaluate (c1,s) = (_,s1)`
  >>rename1 `exec_list (flatten (compile c1)) (t with clock := ck1 + t.clock) = (t_res1, t1)`
  >>subgoal `t_res1 = RNormal` (* because s_res1 is NONE *)
  >-fs[conf_rel_def,res_rel_def]
  >>imp_res_tac conf_rel_state_rel
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
  (* goal: conf_rel c (s_res,s_fin) t (t_res,t_fin) *)
  (* we have ‘conf_rel c (s_res,s_fin) t1 (t_res,t_fin)’; note that ‘t1.stack = t.stack’ *)
  >>fs[conf_rel_def]
)
>>rename1 `evaluate (c1,s) = (s_res1,s1)`
>>strip_tac
>>(Cases_on`s_res1`>>gvs[]) (* obtain x where ‘s_res1 = SOME x’ *)
>>first_x_assum drule
>>strip_tac
>>`res_rel (SOME x) t_res t_fin.stack` by fs[conf_rel_def]
>>imp_res_tac res_rel_SOME
>>qexists_tac`ck`
>>simp[exec_list_append]
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

Theorem Block_rel:
  exec_list Ins
    (t with <|clock := ck + t.clock; stack := []|>) = (t_res1,t1) ∧
  s_res ≠ SOME Error ∧
  conf_rel c (s_res,s_fin) (t with stack := []) (t_res1,t1) ⇒
  ∃t_res t_fin.
    exec (Block BlkNil Ins)
      (t with clock := ck + t.clock) = (t_res,t_fin) ∧
    conf_rel c (s_res,s_fin) t (t_res,t_fin)
Proof
strip_tac
>>(Cases_on`t_res1`>>fs[])
>~[`exec_list _ _ = (RNormal, _)`]
>-(
  drule_then (qspec_then`t.stack`assume_tac) exec_Block_BlkNil_RNormal
  >>fs[conf_rel_def]
  >>simp[push_def,state_rel_with_stack]
  >>metis_tac[res_rel_RNormal]
)
>>fs[conf_rel_def]
>~[`exec_list _ _ = (RBreak _, _)`]
>-metis_tac[res_rel_RBreak]
>>simp[push_def,exec_def]
QED

Theorem compile_If:
  ^(get_goal "If")
Proof
  rpt strip_tac
  >>qpat_x_assum `evaluate _ = _` mp_tac
  >>fs[evaluate_def,stack_asm_ok_def]
  >>rpt(peel[])
  >>(
    strip_tac
    >>fs[]
    >>first_x_assum $ qspec_then`t with stack:=[]`mp_tac
    >>simp[state_rel_with_stack]
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

(* ⌂⌂ *)

Theorem compile_Call:
  ^(get_goal "Call")
Proof
(*
rpt strip_tac
>>(Cases_on`ret`>>gvs[])
>-(
  Cases_on`handler`>>fs[evaluate_def,option_case_eq]
  >>(Cases_on`s.clock=0`>>fs[])
  >-(
    (* timeout case *)
    simp[compile_def]
    >>qexists_tac`0`
    >>simp[]
    (* timeout on RETURN_CALL (INL) or RETURN_CALL_INDIRECT (INR) *)
    >>(Cases_on`dest`>>simp[])
    >-(
      (* RETURN_CALL case *)
      simp[tail_call_def]
      >>simp[RETURN_CALL_def,exec_def]
      (* show `LLOOKUP t.funcs ((x + LENGTH wasm_support_function_list) MOD 4294967296) = SOME ...`
         using `find_code (INL x) s.regs s.code = SOME prog` *)
      >>fs[find_code_def]
      >>rename1 `lookup prog_index s.code = SOME prog`
      >>`LLOOKUP t.funcs (prog_index + LENGTH wasm_support_function_list) =
         SOME
           <|ftype := cakeml_ftype_index; locals := [];
             body := flatten (compile prog)|>`
        by fs[state_rel_def,code_rel_def,find_code_def]
      >>subgoal `LENGTH wasm_support_function_list + prog_index < 4294967296`
      >-(
        `LENGTH t.funcs < 4294967296` by fs[state_rel_def,wasm_state_ok_def]
        >>fs[LLOOKUP_EQ_EL]
      )
      >>simp[]
      (*done*)
      (* show ‘LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ...’ *)
      >>subgoal ‘LLOOKUP t.types (w2n cakeml_ftype_index) = SOME ([], [Tnum Int W32])’
      >-(
        `wasm_state_ok t` by fs[state_rel_def]
        >>fs[wasm_state_ok_def]
      )
      >>simp[]
      (*done*)
      >>simp[pop_n_def]
      >>`t.clock=0` by fs[state_rel_def]
      (* goal: `conf_rel c (SOME TimeOut,s_fin) t (RTimeout,t)` *)
      >>rw[conf_rel_def]
      >-simp[res_rel_def]
      >>metis_tac[state_rel_empty_env]
    )
    >-(
      (* RETURN_CALL_INDIRECT case *)
subgoal `∃prog_index. get_var y s = SOME (Loc prog_index 0)`
>-(
  fs[find_code_def,get_var_def]
  >>gvs[AllCaseEqs()]
)
>>once_rewrite_tac[exec_list_cons]
>>drule_all_then (fn eq=>simp[eq]) exec_GLOBAL_GET
>>simp[wl_value_def]
>>once_rewrite_tac[exec_list_cons]
>>simp[exec_I32_WRAP_I64]
>>once_rewrite_tac[exec_list_cons]
>>simp[exec_I32_CONST]
>>once_rewrite_tac[exec_list_cons]
>>simp[exec_I32_SHR_U]
>>simp[RETURN_CALL_INDIRECT_def,exec_def]
>>simp[dest_i32_def]
>>simp[lookup_func_tables_def, prove(“LLOOKUP [^t.func_table] 0 = SOME t.func_table”, simp[LLOOKUP_def])]

*)
  cheat
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
    >>drule exec_GLOBAL_SET
    >>simp[]
    >>CONV_TAC(DEPTH_CONV record_canon_simp_conv)
    >>impl_keep_tac
    >-fs[stack_asm_ok_def,inst_ok_def,reg_ok_def,conf_ok_def,state_rel_def,regs_rel_def]
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
    >~[`LongDiv`] >- fs[stack_asm_ok_def,inst_ok_def,arith_ok_def,conf_ok_def]
    >~[`AddCarry`] >- cheat
    >~[`AddOverflow`] >- cheat
    >~[`SubOverflow`] >- cheat
  )
  >~[`Mem`] >-
    cheat
  >~[`FP`] >-
    gvs[stack_asm_ok_def,inst_ok_def,oneline fp_ok_def,AllCasePreds(),fp_reg_ok_def,conf_ok_def]
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
>>simp[conf_rel_def]
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
