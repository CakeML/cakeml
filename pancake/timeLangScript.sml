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

Type program = ``:(loc # term list) list``

(* functinos for compiler *)

Definition clks_of_term_def:
  clks_of_term (Tm _ _ clks _ _) = clks
End


Definition clks_accum_def:
  (clks_accum ac [] = ac) ∧
  (clks_accum ac (clk::clks) =
   if MEM clk ac
   then clks_accum ac clks
   else clks_accum (clk::ac) clks)
End

Definition clks_of_def:
  clks_of prog =
  let tms = FLAT (MAP SND prog) in
     clks_accum [] (FLAT (MAP clks_of_term tms))
End

val _ = export_theory();
