(*
  Formalization of And-Inverter Graphs
*)
Theory aig
Ancestors
  misc mlstring
Libs
  preamble

val _ = numLib.prefer_num()

(* TODO Make aigScript over tuples again *)

(* TODO Replace sg and derivatives by have *)
(* TODO Replace qsuff_tac with suff *)
(* TODO Replay by with have ‘...’ >- ...*)

(* Things that appear in base positions.
   Ff corresponds to the constant false. *)
Datatype:
  bvar = Ff | Input 'i | Latch 'l
End

Datatype:
  var = Gate 'a | Base (('i,'l) bvar)
End

Type istate = “:'i -> bool”
Type lstate = “:'l -> bool”

Definition eval_bvar_def[simp]:
  (eval_bvar (is: 'i istate, ls: 'l lstate) Ff = F) ∧
  (eval_bvar (is,ls) (Input i) = is i) ∧
  (eval_bvar (is,ls) (Latch l) = ls l)
End

Theorem eval_bvar_Ff[simp]:
  eval_bvar isls Ff = F
Proof
  Cases_on ‘isls’ >> simp [eval_bvar_def]
QED

Type lit[pp] = “:('a,'i,'l) var # bool”
Overload TT = “(Base Ff, T)”
Overload FF = “(Base Ff, F)”

Type and[pp] = “:'a # (('a,'i,'l) lit list)”
Type aig[pp] = “:('a,'i,'l) and list”

(* Note that we can conjunction over a list of literals as opposed to a pair.
   If needed, we can apply a reduction at the end, allowing for simpler
   definitions for operations such as equivalence.  *)
Definition eval_lit_def:
  (eval_lit (ss : 'i istate # 'l lstate) aig ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Gate n => b ⇎ eval_gate ss aig n) ∧
  (eval_gate ss ([]:('a,'i,'l) aig) n = F) ∧
  (eval_gate ss (h::tl) n =
   let (n', ins) = h in
     if n' = n then EVERY (eval_lit ss tl) ins
     else eval_gate ss tl n)
End

(*
EVAL``eval_lit (is,ls) aig TT``
EVAL``eval_lit (is,ls) aig FF``
*)

Theorem eval_gate_nil[simp]:
  ¬eval_gate ss [] n
Proof
  simp [eval_lit_def]
QED
