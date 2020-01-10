(*
  The abstract syntax of Pancake language
*)

open preamble
     mlstringTheory
     asmTheory (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type time = ``:num``


val _ = Datatype `
  exp = Const ('a word)
      | Var varname
      | Load exp
      | LoadByte exp
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num`


val _ = Datatype `
  ret = Tail
      | Ret varname
      | Handle varname varname prog; (* ret var, excp var *)

  prog = Skip
       | Assign    varname ('a exp)
       | Store     ('a exp) varname
       | StoreByte ('a exp) varname
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall varname funname (('a exp) list)
       | Raise ('a exp)
       | Return ('a exp)
       | Delay time
       | Tick
`;


Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


Overload shift = “backend_common$word_shift”

val _ = export_theory();
