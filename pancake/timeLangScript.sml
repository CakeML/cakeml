(*
  Abstract syntax for timeLang
*)

open preamble
     stringTheory mlstringTheory

val _ = new_theory "timeLang";

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

(* clock variable(s) *)
Datatype:
  clock = CVar string
End

Type clocks  = ``:clock list``

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

Type program = ``:(loc # term list) list``


(* functinos for compiler *)

Definition to_mlstring_def:
  to_mlstring (CVar str) = strlit str
End

Definition clks_of_term_def:
  clks_of_term (Tm _ _ clks _ _) = MAP to_mlstring clks
End

Definition clks_accum_def:
  (clks_accum ac [] = ac) ∧
  (clks_accum ac (clk::clks) =
   if MEM clk ac
   then clks_accum ac clks
   else clks_accum (clk::ac) clks)
End

Definition clks_of_def:
  clks_of ps =
     clks_accum [] (FLAT (MAP clks_of_term ps))
End

val _ = export_theory();
