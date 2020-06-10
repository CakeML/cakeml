(*
  loopLang intermediate language
*)
open preamble
     asmTheory (* for importing binop and cmp *)
     backend_commonTheory (* for overloading shift operation  *);

val _ = new_theory "loopLang";

Type shift = ``:ast$shift``

Datatype:
  exp = Const ('a word)
      | Var num
      | Lookup (5 word)
      | Load exp
      | Op binop (exp list)
      | Shift shift exp num
End

Datatype:
  prog = Skip
       | Assign num ('a exp)           (* dest, source *)
       | Store ('a exp) num            (* dest, source *)
       | SetGlobal (5 word) ('a exp)   (* dest, source *)
       | LoadByte num num               (* TODISC: have removed imm, why num num? *)
       | StoreByte num num
       | Seq prog prog
       | If cmp num ('a reg_imm) prog prog num_set
       | Loop num_set prog num_set     (* names in, body, names out *)
       | Break
       | Continue
       | Raise num
       | Return num
       | Tick
       | Mark prog
       | Fail
       | LocValue num num  (* assign v1 := Loc v2 0 *)
       | Call ((num # num_set) option) (* return var *)
              (num option) (* target of call *)
              (num list)   (* arguments *)
              ((num # prog # prog # num_set) option) (* var to store exception,
                                                        exception-handler code,
                                                        normal-return handler code,
                                                        live vars after call *)
       | FFI string num num num num num_set (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End

Definition locals_touched_def:
  (locals_touched (Const w) = []) /\
  (locals_touched (Var v) = [v]) /\
  (locals_touched (Lookup name) = []) /\
  (locals_touched (Load addr) = locals_touched addr) /\
  (locals_touched (Op op wexps) = FLAT (MAP locals_touched wexps)) /\
  (locals_touched (Shift sh wexp n) = locals_touched wexp)
Termination
  cheat
End

Definition assigned_vars_def:
  (assigned_vars Skip = []) ∧
  (assigned_vars (Assign n e) = [n]) ∧
  (assigned_vars (LoadByte n m) = [m]) ∧
  (assigned_vars (Seq p q) = assigned_vars p ++ assigned_vars q) ∧
  (assigned_vars (If cmp n r p q ns) = assigned_vars p ++ assigned_vars q) ∧
  (assigned_vars (LocValue n m) = [n]) ∧
  (assigned_vars _ = [])
End


val _ = export_theory();
