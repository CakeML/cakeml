(*
  Abstract syntax for timeLang
*)

open preamble
     stringTheory
     realTheory

val _ = new_theory "timeLang";

(* location of a state in timed-automata *)
Type loc = ``:num``

(* input and output asscociated with each state *)
Type action = ``:num``
Type effect = ``:num``

Datatype:
  ioAction = Input action
           | Output effect
End

(* real-valued time, equivalent to run-time *)
(* IMP: modeled as rational in the Coq formalism  *)
Type time   = ``:real``


(* clock variable *)
Datatype:
  clock = CVar string (* datatype instead of type_synonym to enable parsing *)
End
(* clock variables *)
Type clocks  = ``:clock list``

(* clock and time expressions *)
Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End

(* relational time expressions *)
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

(*
     = [(0%nat,
        [Tm (Output 1%nat)
           [CndLe (EClock (CVar "x")) (ELit 1);
           CndLe (ELit 1) (EClock (CVar "x"));
           CndLe (EClock (CVar "x")) (ELit 2)] [] 1%nat
	   [(2, CVar "x")]]);
       (1%nat,
       [Tm (Output 0%nat)
          [CndLe (EClock (CVar "x")) (ELit 2);
          CndLe (ELit 2) (EClock (CVar "x"));
	  CndLe (ELit 0) (ELit 1)]
          [CVar "x"] 0%nat [(1, CVar "x")]])]
     : program

*)

(*

  step s
  {
  switch s
  case 0:
     perform this task
     update the state

  case 1:
    perform this task
    update the state


}

*)



val _ = export_theory();
