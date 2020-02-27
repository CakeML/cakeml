(*
  wheatLang intermediate language
*)
open preamble
     asmTheory (* for importing binop and cmp *)
     backend_commonTheory (* for overloading shift operation  *);;

val _ = new_theory "wheatLang";

Type shift = ``:ast$shift``

Datatype:
  exp = Const ('a word)
      | Var num
      | Load exp
      | Op binop (exp list)
      | Shift shift exp num
End

Datatype:
  prog = Skip
       | Assign num ('a exp)           (* dest, source *)
       | Store ('a exp) num            (* dest, source *)
       | StoreGlob ('a exp) (5 word)   (* dest, source *)
       | LoadGlob  (5 word) ('a exp)   (* dest, source *)
       | LoadByte num num
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
              ((num # prog) option) (* var to store exception, exception-handler code *)
              num_set      (* live vars on completion *)
       | FFI string num num num num (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Overload shift = “backend_common$word_shift”

val _ = export_theory();
