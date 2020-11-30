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
Definition conditions_of_def:
  (conditions_of (Tm _ cs _ _ _) = cs)
End

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

Definition number_of_clks_def:
  number_of_clks prog = LENGTH (clks_of prog)
End


Definition tinv_of_def:
  tinv_of (Tm _ _ _ _ tes) = MAP FST tes
End

Definition init_term_of_def:
  (init_term_of (t::ts) = t) ∧
  (init_term_of [] = [])
End

(*
Definition init_term_of_def:
  (init_term_of ((t::ts)::tss) = t) ∧
  (init_term_of [] = Tm (Input 0) [] [] 0 [])
End
*)

Definition init_loc_def:
  init_loc = 0:num
End

Definition wait_set_def:
  (wait_set (Tm _ _ _ _ []) = 0:num) ∧
  (wait_set _ = 1:num)
End

Definition input_set_def:
  (input_set (Tm _ _ _ _ []) = 1:num) ∧
  (input_set _ = 0:num)
End


val _ = export_theory();
