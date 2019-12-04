(*
  This language is a cleaner version of wordLang
  with a simplified stack and
  no garbage collector, assembly instructions,
  and global variables
*)

open preamble
     asmTheory (* for importing binop and cmp *)
     backend_commonTheory (* for overloading the shift operation  *);

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

val _ = Datatype `
  exp = Const ('a word)
      | Var num
      | Load exp
      | LoadByte exp
      | Op binop (exp list)
      | Shift shift exp num`

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

(* cannot reuse Var, Str (stored) instead *)
val _ = Datatype `
  var_imm = Str num | Imm ('a word)`


val _ = Datatype `
  prog = Skip
       | Assign num ('a exp)
       | Store ('a exp) num
       | StoreByte ('a exp) num
       | Call (num option)
              (* return var *)
              (num option) (* target of call *)
              (num list) (* arguments *)
              ((num # panLang$prog) option)
              (* handler: var to store exception (number?), exception-handler code *)
       | Seq panLang$prog panLang$prog
       | If cmp num num panLang$prog panLang$prog
       | While cmp num ('a var_imm) panLang$prog
       | Break
       | Raise num
       | Return num
       | Tick
       | FFI string num num num num num_set (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *) `;
(* num_set is abbreviation for unit num_map *)

      (* | Handle
       | Return
       | Continue

*)



(* op:asm$binop  *)
val word_op_def = Define `
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (And,ws) => SOME (FOLDR word_and (¬0w) ws)
    | (Add,ws) => SOME (FOLDR word_add 0w ws)
    | (Or,ws) => SOME (FOLDR word_or 0w ws)
    | (Xor,ws) => SOME (FOLDR word_xor 0w ws)
    | (Sub,[w1;w2]) => SOME (w1 - w2)
    | _ => NONE`;


(* sh:ast$shift  *)
val word_sh_def = Define `
  word_sh sh (w:'a word) n =
    if n <> 0 /\ n ≥ dimindex (:'a) then NONE else
      case sh of
      | Lsl => SOME (w << n)
      | Lsr => SOME (w >>> n)
      | Asr => SOME (w >> n)
      | Ror => SOME (word_ror w n)`;

Overload shift = “backend_common$word_shift”

val _ = export_theory();
