(*
  The abstract syntax of Pancake language
*)

open preamble
     asmTheory (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation*);

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

val _ = Datatype `
  exp = Const ('a word)
      | Var num    (* TOASK: plan is to make all accesses to variables through exp, is it ok? *)
      | Loc num    (* destination of call, right now its taking a num *)
      | Load exp
      | LoadByte exp
      | Op binop (exp list)
      | Shift shift exp num`


val _ = Datatype `
  bexp = Bconst bool
       | Bcomp cmp ('a exp) ('a exp)
       | Bbinop (bool -> bool -> bool) bexp bexp (* TOASK: should we allow a generic Bbinop?
                                                            as we already have cmp *)
       | Bnot bexp` (* TOASK: should we have Bnot? *)


val _ = Datatype `
  ret = NoRet
      | Ret num
      | Hndl num num prog;  (* variable for storing retv and exception *)
        (* Handle and Handler give overloading errors in panSem *)

  prog = Skip
       | Assign    ('a exp) ('a exp)   (* TOASK: semantics dictates destination as (Var num) *)
       | Store     ('a exp) ('a exp)   (* TOASK: semantics dictates source as (Var num) *)
       | StoreByte ('a exp) ('a exp)   (* TOASK: semantics dictates source as (Var num) *)
       | Seq prog prog
       | If    ('a bexp) prog prog
       | While ('a bexp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)   (* TOASK: about destination *)
       | Raise ('a exp)    (* TOASK: semantics dictates exp as (Var num) *)
       | Return ('a exp)   (* TOASK: semantics dictates exp as (Var num) *)
       | Tick
       | FFI string num num num num num_set (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
   (*  | Handle panLang$prog (num # panLang$prog)  (* not sure about num right now *) *) `;


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

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


Overload shift = “backend_common$word_shift”

val _ = export_theory();
