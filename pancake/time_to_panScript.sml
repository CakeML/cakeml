(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "timeLang", "panLang"];

(*
  timeLang program turns into list of Pancake functions
*)

Definition to_word:
  (to_word (t:real) = (ARB t): 'a word)
End

Definition to_mlstring:
  (to_mlstring (s:string) = (ARB s): mlstring)
End

Definition comp_exp:
  (comp_exp (ELit time) = Const (to_word time)) ∧
  (comp_exp (EClock (CVar clock)) = Var (to_mlstring clock)) ∧
  (comp_exp (ESub e1 e2) = Op Sub [comp_exp e1; comp_exp e2])
End

(*
 (("asm", "datatype_cmp"),
     (⊢ DATATYPE
          (cmp Equal Lower Less Test NotEqual NotLower NotLess NotTest), Thm))
*)

(* ≤ operator in the cmp datatype *)

Definition comp_condition:
  (comp_condition (CndLe e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2)) ∧
  (comp_condition (CndLt e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2))
End


Definition comp_conditions:
  (comp_conditions [] = Const 1w) ∧
  (* generating true for the time being*)
  (comp_conditions cs = Op And (MAP comp_condition cs))
End

Definition reset_clks:
  (reset_clks [] = Skip) ∧
  (reset_clks (c::cs) = Seq (Assign c (Const 0w)) (reset_clks cs))
End

Definition compile_step:
  (compile_step (Input action) location_var location clks waitad waitval =
   Seq (reset_clks clks)
       (Seq (Assign location_var location)
        (Store (Const waitad) (Const waitval)))) ∧
  (compile_step (Output eff) location_var location clks waitad waitval =
   Seq (reset_clks clks)
       (Seq (Assign location_var location)
        (Store (Const waitad) (Const waitval))))
  (* I think here we should simply state that now the output action should be taken,
     like a flag. And, may be the time wrapper recieve that flag and call the respective
     output action *)
End

Definition compile_term:
  compile_term
    (Tm io cs reset_clocks next_location wait_time) =
     If (compile_conditions cs)
     (compile_step (Input action) location_var location clks waitad waitval)
     (* take step, do the action, goto the next location *)
     Skip (* stay in the same state, maybe *)
End

(* what does it mean conceptually if a state has more than
   one transitions *)
(* to understand how wait time is modeled in the formalism *)

(* keep going in the same direction *)






(*
Type program = ``:(loc # term list) list``
*)


val _ = export_theory();
