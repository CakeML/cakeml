(*
  Abstract syntax for timeLang
*)

open preamble
     stringTheory mlstringTheory mlintTheory

val _ = new_theory "timeLang";

Overload CVar[inferior] = “strlit”

val _ = set_grammar_ancestry
        ["mlint"];

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

Definition termWaitTimes_def:
  (termWaitTimes (Tm _ _ _ _ wt) = wt)
End

Definition termDest_def:
  (termDest (Tm _ _ _ loc _) = loc)
End

Definition termAction_def:
  (termAction (Tm io _ _ _ _) = io)
End


Definition terms_out_signals_def:
  (terms_out_signals [] = []) ∧
  (terms_out_signals (Tm (Output out) _ _ _ _::tms) =
   out :: terms_out_signals tms) ∧
  (terms_out_signals (Tm (Input _) _ _ _ _::tms) =
   terms_out_signals tms)
End


Definition terms_in_signals_def:
  (terms_in_signals [] = []) ∧
  (terms_in_signals (Tm (Input i) _ _ _ _::tms) =
   i :: terms_in_signals tms) ∧
  (terms_in_signals (Tm (Output _) _ _ _ _::tms) =
   terms_in_signals tms)
End

Definition accumClks_def:
  (accumClks ac [] = ac) ∧
  (accumClks ac (clk::clks) =
   if MEM clk ac
   then accumClks ac clks
   else accumClks (clk::ac) clks)
End


Definition exprClks_def:
  exprClks clks e =
  case e of
  | ELit t => clks
  | EClock clk =>
     if MEM clk clks then clks else clk::clks
  | ESub e1 e2 =>
     exprClks (exprClks clks e1) e2
End


Definition clksOfExprs_def:
  clksOfExprs es = FOLDL exprClks [] es
End


Definition destCond_def:
  (destCond (CndLe e1 e2) = [e1; e2]) ∧
  (destCond (CndLt e1 e2) = [e1; e2])
End


Definition condClks_def:
  condClks cd = clksOfExprs (destCond cd)
End


Definition condsClks_def:
  condsClks cds = clksOfExprs (FLAT (MAP destCond cds))
End


Definition termClks_def:
  termClks (Tm _ _ clks _ _) = clks
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


Definition out_signals_def:
  out_signals prog =
  let
    tms = FLAT (MAP SND prog)
  in
    MAP num_to_str (terms_out_signals tms)
End

val _ = export_theory();
