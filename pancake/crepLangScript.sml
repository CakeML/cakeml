(*
  Abstract syntax of Crepe language
  Crepe: instrctuons are similar to that of
  Pancake, but we flatten locals from
  struct-layout to word-layout
*)

open preamble
     mlstringTheory
     asmTheory            (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "crepLang";

Type shift = ``:ast$shift``

Type varname = ``:num``

Type funname = ``:mlstring``

Type eid = ``:num``

Datatype:
  exp = Const ('a word)
      | Var varname
      | Label funname
      | Load exp
      | LoadByte exp
      | LoadGlob  (5 word)
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
End

Datatype:
  prog = Skip
       | Dec varname ('a exp) prog
       | Assign    varname  ('a exp)   (* dest, source *)
       | Store     ('a exp) ('a exp)   (* dest, source *)
       | StoreByte ('a exp) ('a exp)   (* dest, source *)
       | StoreGlob (5 word) ('a exp)   (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall string varname varname varname varname
      (* FFI name, conf_ptr, conf_len, array_ptr, array_len *)
       | Raise eid ('a exp)
       | Return ('a exp)
       | Tick;

  ret = Tail | Ret varname prog (handler option);

  handler = Handle eid prog
End


(*
  later we would have:
  ExtCall funname varname (('a exp) list)
  Information for FFI:
  C types: bool, int, arrays (mutable/immuatable, w/wo length)
  arguments to be passed from pancake: list of expressions.
  array with length is passed as two arguments: start of the array + length.
  length should evaluate to Word *)

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Overload shift = “backend_common$word_shift”

val _ = export_theory();
