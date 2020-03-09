(*
 something
*)

open preamble
     mlstringTheory;


val _ = new_theory "timed";

(* it would be the type to represent the locations of timed-automata *)
Type Loc = “:'a set”

(* sigma is the alphabet of the timed-automata *)
Type sigma = “:'a set”

Type time = “:num”


Datatype:
  clock = Cvar string
End

Type valuation = “: clock -> time”

Datatype:
  constraint = LE clock time
             | LT clock time
             | EQ clock time
             | GT clock time
             | GE clock time
End


Datatype:
  transition =
  <| source : 'a Loc
   ; act    : 'a sigma
   ; consts : constraint list
   ; toReset : clock list
   ; dest : 'a Loc |>
End


Datatype:
  tautomata =
  <| locs : 'a Loc list
   ; l0   : 'a Loc (* initial location *)
   ; transitions : ('a transition) list
   ; inv  : 'a Loc -> constraint list
   ; V : clock set |>
End


Definition constraint_spec_def:
  (constraint_spec (v : valuation) (LE cl t)  =  (v cl <= t)) /\
  (constraint_spec v (LT cl t) =  (v cl < t)) /\
  (constraint_spec v (EQ cl t) =  (v cl = t)) /\
  (constraint_spec v (GE cl t) =  (v cl >= t)) /\
  (constraint_spec v (GT cl t) =  (v cl > t))
End

Definition sat_clist_def:
  sat_clist l v = EVERY (constraint_spec v) l
End


Datatype:
  Label = LDelay time
        | LAction ('a sigma)
End


Inductive ta_sem_def:
  (!ta l (u : valuation) (u' : valuation) d.
    sat_clist (ta.inv l) u /\
    sat_clist (ta.inv l) (\c. (u c) + d)  ==>
    ta_sem (LDelay d) (l,u) (l,(\c. (u c) + d))) /\
  (!ta l l' (u : valuation) (u' : valuation) a c s.
   MEM (<| source:= l; act := a; consts := c; toReset := s; dest := l' |>)  (ta.transitions) /\
   sat_clist c u /\
   sat_clist (ta.inv l) (\c. if MEM c s then 0 else u c) ==>
   ta_sem (LAction a)  (l,u) (l', (\c. if MEM c s then 0 else u c)))
End

val _ = export_theory();
