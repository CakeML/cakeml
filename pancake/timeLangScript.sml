(*
  Abstract syntax for timeLang
*)

open preamble
     stringTheory
     realTheory

val _ = new_theory "timeLang";

(* location identifies TA-states *)
Type loc = ``:num``

(* state specific input and output *)
Type response = ``:num``
Type signal   = ``:num``

Datatype:
  ioAction = Input  response
           | Output signal
End

(*
  IMP:
  time:rat in the Coq formalism,
  Pancake has discrete time:num  *)
Type time   = ``:num``


(* clock variable(s) *)
Datatype:
  clock = CVar string
End

Type clocks  = ``:clock list``

(* time expression *)
Datatype:
  expr = ELit time
       | EClock clock
       | ESub expr expr
End

(* relational time expression *)
Datatype:
  cond = CndLe expr expr  (* e <= e *)
       | CndLt expr expr  (* e < e *)
End

Datatype:
  term = Tm ioAction
            (cond list)
            clocks
            loc
            ((time # clock) list) (* to calculate wait time *)
End

Type program = ``:(loc # term list) list``

val _ = export_theory();
