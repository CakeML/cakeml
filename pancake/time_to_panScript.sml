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

Definition to_word_def:
  (to_word (t:real) = (ARB t): 'a word)
End

Definition to_mlstring_def:
  (to_mlstring (s:string) = (ARB s): mlstring)
End

Definition comp_exp_def:
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

Definition comp_condition_def:
  (comp_condition (CndLe e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2)) ∧
  (comp_condition (CndLt e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2))
End


Definition comp_conditions_def:
  (comp_conditions [] = Const 1w) ∧
  (* generating true for the time being *)
  (comp_conditions cs = Op And (MAP comp_condition cs))
End

(* provide a value to be reseted at, for the time being *)
Definition reset_clks_def:
  (reset_clks [] n = Skip) ∧
  (reset_clks (CVar c::cs) n = Seq (Assign (to_mlstring c) (Const n)) (reset_clks cs n))
End


(* we might be returning loc *)
Definition comp_step_def:
  (comp_step (Input action) clks reset_val loc nloc adr wait_val out =
    Seq (reset_clks clks reset_val)
        (Seq (Assign loc nloc)
         (Store adr wait_val) (* update later *))) ∧

 (comp_step (Output effect) clks reset_val loc nloc adr wait_val out =
  Seq (reset_clks clks reset_val)
      (Seq (Seq (Assign loc nloc) (Store adr wait_val))
       (Store out (Const 1w))))
End

(*
  I think here we should simply state that now the output action should be taken,
  like a flag. And, may be the time wrapper recieve that flag and call the respective
  output action
*)


(* writing a compiler for the list of terms for the time being *)

Definition comp_terms_def:
  (comp_terms [] = Skip) ∧
  (comp_terms (Tm io cs clks loc wts :: ts) =
     If (comp_conditions cs)
        (comp_step io clks ARB ARB ARB ARB ARB ARB)
        (comp_terms ts))
End

(*
Definition compile_term:
  compile_term
    (Tm io cs reset_clocks next_location wait_time) =
     If (compile_conditions cs)
     (compile_step (Input action) location_var location clks waitad waitval)
     (* take step, do the action, goto the next location *)
     Skip (* stay in the same state, maybe *)
End
*)

(* what does it mean conceptually if a state has more than
   one transitions *)
(* to understand how wait time is modeled in the formalism *)

(* keep going in the same direction *)



(*
Type program = ``:(loc # term list) list``
*)


val _ = export_theory();
