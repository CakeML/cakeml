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
   (* TODISC: crepLang has LoadByte, while wordLand doesn't have, should we have it here?  *)
   (* | LoadByte exp *)
      | Op binop (exp list)
      | Shift shift exp num
   (* TODISC: panLang and crepLang has Cmp, wordLang doesnot have it  *)
End

Datatype:
  prog = Skip
       | Assign num ('a exp)           (* dest, source *)
       | Store ('a exp) num            (* dest, source *)
       | StoreGlob ('a exp) (5 word)   (* dest, source *)
       | LoadGlob  (5 word) ('a exp)   (* dest, source *)
       | Inst ('a inst)
       | Seq prog prog
       | If cmp num ('a reg_imm) prog prog
       | While cmp num ('a reg_imm) prog
       | Break
       | Continue
       | Raise num
       | Return num
       | Tick
       | LocValue num num  (* assign v1 := Loc v2 0 *)
       | Call (num option) (* return var *)
              (num option) (* target of call *)
              (num list)   (* arguments *)
              ((num # prog) option)  (* var to store exception, exception-handler code *)
       | FFI string num num num num (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
End

(* Remove_me_later: word_op and word_sh to be taken from wordLangScript *)


Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


Overload shift = “backend_common$word_shift”

val _ = export_theory();
