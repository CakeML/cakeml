(*
  Abstract syntax of struct language
*)

open preamble
     mlstringTheory
     asmTheory            (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "structLang";

Type shift = ``:ast$shift``

Type sname = ``:mlstring``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type index = ``:num``


Datatype:
  shape = One
        | Comb (shape list)
End

Datatype:
  exp = Const ('a word)
      | Var varname       (* TODISC: do we need individual lookups? *)
      | Label funname
      | Struct sname shape
      | Lookup sname shape index  (* TODISC: do we need shape here? *)
      | Load exp shape
      | LoadByte exp
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
End

Datatype:
  ret = Tail
      | Ret varname
      | Handle varname varname prog; (* ret variable, excp variable *)

  prog = Skip
       | Assign    varname  shape ('a exp)   (* dest, source *)
       | Store     ('a exp) ('a exp) shape   (* dest, source *)
       | StoreByte ('a exp) ('a exp)   (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall funname varname varname varname varname (* FFI name, conf_ptr, conf_len, array_ptr, array_len *)
       | Raise  ('a exp) shape
       | Return ('a exp) shape
       | Tick
End


Datatype:
  dec = Dec varname shape ('a exp) ('a prog)
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
