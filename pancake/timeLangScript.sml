(*
  Abstract syntax for timeLang
*)

open preamble
     stringTheory mlstringTheory

val _ = new_theory "timeLang";

Overload CVar[inferior] = “strlit”

(* location identifies TA-states *)
Type loc = ``:num``

(* state specific input and output *)
Type in_signal  = ``:num``
Type out_signal = ``:num``

Datatype:
  ioAction = Input  in_signal
           | Output out_signal
End

(*
  IMP:
  time:rat in the Coq formalism,
  Pancake has discrete time:num  *)
Type time   = ``:num``

(* clock variables *)
Type clock  = ``:mlstring``
Type clocks = ``:clock list``

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

(*
Type program = ``:(loc # term list) list``
*)

Type program = ``:(loc # term list) list # time option``

(* functions for compiler *)
Definition termConditions_def:
  (termConditions (Tm _ cs _ _ _) = cs)
End

Definition termClks_def:
  termClks (Tm _ _ clks _ _) = clks
End

Definition accumClks_def:
  (accumClks ac [] = ac) ∧
  (accumClks ac (clk::clks) =
   if MEM clk ac
   then accumClks ac clks
   else accumClks (clk::ac) clks)
End

Definition clksOf_def:
  clksOf prog =
  let tms = FLAT (MAP SND prog) in
     accumClks [] (FLAT (MAP termClks tms))
End

Definition nClks_def:
  nClks prog = LENGTH (clksOf prog)
End


Definition termInvs_def:
  termInvs (Tm _ _ _ _ tes) = MAP FST tes
End

Definition initTerm_def:
  (initTerm (t::ts) = t) ∧
  (initTerm [] = [])
End

(*
Definition init_term_of_def:
  (init_term_of ((t::ts)::tss) = t) ∧
  (init_term_of [] = Tm (Input 0) [] [] 0 [])
End
*)

Definition initLoc_def:
  initLoc = 0:num
End

Definition waitSet_def:
  (waitSet (Tm _ _ _ _ []) = 0:num) ∧
  (waitSet _ = 1:num)
End

Definition inputSet_def:
  (inputSet (Tm _ _ _ _ []) = 1:num) ∧
  (inputSet _ = 0:num)
End


val _ = export_theory();
