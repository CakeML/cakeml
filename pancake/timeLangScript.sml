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
from Time.v
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

(* term from DSL *)
(* action is remaining *)
Datatype:
  dterm = TmSkip                       (* No-op *)
        | TmPanic                      (* Panic *)
        | TmWait (expr list)           (* Wait _at most_ a certain time *)
        | TmGoto loc                   (* Decide next location *)
        | TmReset (clock list)         (* Reset some clocks *)
        | TmOutput effect              (* Perform output *)
        | TmConsume action             (* Consume input *)
        | TmSeq dterm dterm            (* Sequencing *)
        | TmSwitch (action option)     (* Switch *)
                   (cond list)
                   dterm
                   dterm

End

(* state and sematics of program *)

val _ = export_theory();
