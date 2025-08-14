(*
  Correctness proof for compilation from stackLang to wasmLang
*)
Theory stack_to_wasmProof
Ancestors
  wasmLang words arithmetic list rich_list sptree mlstring
  wasmSem stackSem stackLang
Libs
  wordsLib helperLib

(* compiler definition (TODO: move to another file when ready) *)

Definition compile_def:
  compile stackLang$Skip = List ([]:wasmLang$instr list) ∧
  compile (Seq p1 p2) = Append (compile p1) (compile p2) ∧
  compile _ = ARB
End

(* definitions used in the correctness statement *)

val s = “s:('a,'c,'ffi) stackSem$state”
val t = “t:wasmSem$state”

Definition empty_buffer_def:
  empty_buffer b ⇔
    b.position = 0w ∧
    b.buffer = [] ∧
    b.space_left = 0
End

Definition state_rel_def:
  state_rel ^s ^t ⇔
    ¬ s.use_stack ∧ ¬ s.use_store ∧ ¬ s.use_alloc ∧ ¬ s.be ∧
    empty_buffer s.code_buffer ∧ empty_buffer s.data_buffer
End

Definition res_rel_def:
  (res_rel NONE r     ⇔ r = RNormal) ∧
  (res_rel (SOME v) r ⇔ T (* TODO: fix *))
End

(* set up for one theorem per case *)

val goal_tm =
  “λ(p,^s). ∀res s1 t.
     evaluate (p,s) = (res,s1) ∧
     state_rel s t ∧ syntax_ok p ∧
     res ≠ SOME Error ⇒
     ∃ck t1 res1.
       exec_list (append (compile p)) (t with clock := t.clock + ck) = (res1,t1) ∧
       res_rel res res1 ∧
       state_rel s1 t1”

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

(* a proof for each case *)

Theorem compile_Skip:
  ^(get_goal "Skip")
Proof
  rpt strip_tac
  \\ gvs [compile_def,exec_def,stackSemTheory.evaluate_def]
  \\ simp [res_rel_def]
  \\ qexists_tac ‘0’ \\ fs [state_rel_def]
QED

Theorem compile_Inst:
  ^(get_goal "Inst")
Proof
  cheat
QED

Theorem compile_Seq:
  ^(get_goal "Seq")
Proof
  cheat
QED

Theorem compile_If:
  ^(get_goal "If")
Proof
  cheat
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
