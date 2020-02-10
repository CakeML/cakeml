(*
  pre-wordLang intermediate language
*)
open preamble
     asmTheory (* for importing binop and cmp *)
     backend_commonTheory (* for overloading shift operation  *);;

val _ = new_theory "prewordLang";

Type shift = ``:ast$shift``

Datatype:
  exp = Const ('a word)
      | Var num   (* variables can hold either Word or Loc *)
      | Load exp
      | Op binop (exp list)
      | Shift shift exp num
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Datatype:
  prog = Skip
       | Assign num ('a exp)  (* dest,source *)
       | Store ('a exp) num   (* dest,source *)
       | StoreGlob ('a exp) (5 word)   (* dest, source *)
       | LoadGlob  (5 word) ('a exp)   (* dest, source *)
       | Inst ('a inst)
       | Seq prewordLang$prog prewordLang$prog
       | If cmp num ('a reg_imm) prewordLang$prog prewordLang$prog
       | Raise num
       | Return num
       | Tick
       | LocValue num num  (* assign v1 := Loc v2 0 *)
       | Call (num option) (* return var *)
              (num option) (* target of call *)
              (num list)   (* arguments *)
              ((num # prewordLang$prog) option)  (* var to store exception, exception-handler code *)
       | FFI string num num num num (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
End

Definition word_op_def:
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (And,ws) => SOME (FOLDR word_and (¬0w) ws)
    | (Add,ws) => SOME (FOLDR word_add 0w ws)
    | (Or,ws) => SOME (FOLDR word_or 0w ws)
    | (Xor,ws) => SOME (FOLDR word_xor 0w ws)
    | (Sub,[w1;w2]) => SOME (w1 - w2)
    | _ => NONE
End

Definition word_sh_def:
  word_sh sh (w:'a word) n =
    if n <> 0 /\ n ≥ dimindex (:'a) then NONE else
      case sh of
      | Lsl => SOME (w << n)
      | Lsr => SOME (w >>> n)
      | Asr => SOME (w >> n)
      | Ror => SOME (word_ror w n)
End

Overload shift = “backend_common$word_shift”

val _ = export_theory();
