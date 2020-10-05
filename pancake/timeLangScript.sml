(*
  Abstract syntax for an imperative language
  compiling timed-automata based specifications
*)
open preamble
     mlstringTheory
     realTheory

val _ = new_theory "timeLang";

(* term *)

Type action = ``:num``
Type effect = ``:num``
Type loc    = ``:num``

Datatype:
  ioAction = Input action
           | Output effect
End

(* clock names basically *)

Datatype:
  clock = CVar mlstring
End

(* clock values *)
Datatype:
  time = Time real
End

Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End


Datatype:
  cond = CndLe expr expr  (* e <= e *)
       | CndLt expr expr  (* e < e *)
End


Datatype:
  term = Tm ioAction
            (cond list)
            (clock list)
            loc
            ((time#clock) list)
End

Type program = ``:(loc # term list) list``


(*
generic DSL, that is infact too generic for our purposes

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
*)



val _ = export_theory();
