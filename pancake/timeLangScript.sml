(*
  Abstract syntax for an imperative language
  compiling timed-automata based specifications
*)
open preamble
     mlstringTheory
     ratTheory
     realTheory

val _ = new_theory "timeLang";

(* term *)

Type action = ``:num``
Type effect = ``:num``
Type loc    = ``:num``


(* toask: what do Input num and Output num represent *)
(* how can we model action and effect with num datatype *)
Datatype:
  ioAction = Input action
           | Output effect
End

(* clock variable name *)
Datatype:
  clock = CVar mlstring
End


(* clock value
   time is modeled as rat in the Coq formalism,
   we are modeling it as real for the time being  *)
Datatype:
  time = Time real
End


(* time expression:
   an expression can be either
     -- a time literal
     -- a clock variable
     -- subtraction of expressions *)
Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End

(* relational expressions:
   -- less than and equal to
   -- less than *)
Datatype:
  cond = CndLe expr expr  (* e <= e *)
       | CndLt expr expr  (* e < e *)
End

(* what does this term represent?
   terms would later constitute a program

   1. what does "current branch" mean?
   2. Labels are nums
   3. time gaurds on the transition:
      cond list are the list of conditions that
      should be true in order for a transition to be
      taken.
   4. reset clocks: clock values to be reset in the current branch
   5. the next location if the branch is taken
   6. what is maximum wait time:
      the last argument is used to calculate the maximum wait time *)
Datatype:
  term = Tm ioAction
            (cond list)
            (clock list)
            loc
            ((time # clock) list)
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
