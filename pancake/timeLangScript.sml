(*
  Abstract syntax for an imperative language
  compiling timed-automata based specifications
*)
open preamble
     mlstringTheory
     ratTheory
     realTheory

val _ = new_theory "timeLang";


Type action = ``:num``
Type effect = ``:num``
Type loc    = ``:num``

Datatype:
  ioAction = Input action
           | Output effect
End

(* clock variable*)
Datatype:
  clock = CVar mlstring
End


(* clock value
   time is rational in the Coq formalism,
   we are modeling it as real *)
Datatype:
  time = Time real
End


(* time expression *)
Datatype:
  expr = ESub expr expr
       | EClock clock
       | ELit time
End

(* relational expressions *)
Datatype:
  cond = CndLe expr expr  (* e <= e *)
       | CndLt expr expr  (* e < e *)
End


Datatype:
  term = Tm ioAction
            (cond list)
            (clock list)
            loc
            ((time # clock) list)
            (* (run-time value # clock variable) list for
                wait time *)
End

Type program = ``:(loc # term list) list``


(*

Variable Dom : Set.
Variable cls : set Dom.


(* Hira: mapping? *)
Definition partial_valuation := mapping Dom Val.
Variable Val : Set.

(* Hira: item_index? *)
Fixpoint traverse_dom (v:partial_valuation) : set Dom :=
match v with
| []      => []
| x :: xs => (item_index x) :: traverse_dom xs
end.


Definition isTotalOver (xs : set Dom) (v:partial_valuation) : Prop :=
 traverse_dom v = xs.

Definition valuation := sig (isTotalOver cls).

Definition val_apply_partial (v:partial_valuation) (x:Dom) : option Val :=
 map_apply Dom_dec v x.

Variable Dom_dec : forall x y : Dom, {x = y} + {x <> y}.
Definition val_apply (v:valuation) (x:Dom) : Val :=
match val_apply_partial (proj1_sig v) x with
| None     => default
| Some val => val
end.

(* Hira: MkStore? *)
(* TODO: Separate persistent state and output state? *)
Inductive store {clocks: list clock} :=
  MkStore
    { clockVal: valuation clock time clocks
    ; location: loc
    ; consumed: option action
    ; output: option effect
    ; waitTime: option time
    }.

(* Hira: clock_dec? *)
Fixpoint evalExpr (clocks : set clock) (st : store) (e : expr) :=
  match e with
  | ELit t => t
  | EClock c => val_apply clock clock_dec time 0 clocks (clockVal st) c
  | ESub e1 e2 => minusT (evalExpr clocks st e1) (evalExpr clocks st e2)
  end.

Definition evalDiff (clocks : set clock) (st : store) (diff : time * clock) :=
  match diff with
  | (t, c) => evalExpr clocks st (ESub (ELit t) (EClock c))
  end.

*)

val _ = export_theory();
