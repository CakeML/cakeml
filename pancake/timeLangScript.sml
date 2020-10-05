(*
  Abstract syntax for an imperative language
  compiling timed-automata based specifications
*)
open preamble
     mlstringTheory

val _ = new_theory "timeLang";

(* term *)

Type action = ``:num``
Type effect = ``:num``
Type loc    = ``:num``

Datatype:
  ioAction = Input action
           | Output effect
End

(* TOASK *)
(*
from Clocks.v
(* Clock variables *)
Inductive clock : Set :=
 CVar : string -> clock.
*)

Datatype:
  clock = CVar mlstring
End

(* TOASK *)
(*
Definition time : Set := Q.
*)

Datatype:
  time = Time num
End

Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End

(*
cond ::= e <= e
       | e < e
*)

Datatype:
  cond = CndLe expr expr
       | CndLt expr expr
End


Datatype:
  term = Tm ioAction
            (cond list)
            (clock list)
            loc
            ((time#clock) list)
End

Type program = ``:(loc # term list) list``


val _ = export_theory();
