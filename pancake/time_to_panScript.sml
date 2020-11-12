(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "timeLang", "panLang"];


(*
  input trigger is remaining
*)

Definition task_controller_def:
  task_controller initial_loc =
  nested_seq [
      Assign  «location» initial_loc;
      Assign  «task_ret» (Struct [Var «location»; Var «wake_up_at»]);
      Assign  «wait_set» (Const 1w);
      ExtCall «get_time» «sys_time» ARB ARB ARB;
      Assign  «wake_up_at» (Op Add [Var «sys_time»; Const 1w]);
      While (Const 1w)
            (nested_seq [
                While (Op And [Var «wait_set»;
                               Cmp Less (Var «sys_time») (Var «wake_up_at»)])
                (ExtCall «get_time» «sys_time» ARB ARB ARB);
                Call (Ret «task_ret» NONE) (Var «location») [Var «sys_time»]
              ])
    ]
End

Datatype:
  context =
  <| funcs     : timeLang$loc    |-> panLang$funname;
     ext_funcs : timeLang$effect |-> panLang$funname
  |>
End

Definition real_to_word_def:
  (real_to_word (t:real) = (ARB t): 'a word)
End

Definition comp_exp_def:
  (comp_exp (ELit time) = Const (real_to_word time)) ∧
  (comp_exp (EClock (CVar clock)) = Var «clock») ∧
  (comp_exp (ESub e1 e2) = Op Sub [comp_exp e1; comp_exp e2])
End

(* ≤ is missing in the cmp datatype *)

Definition comp_condition_def:
  (comp_condition (CndLe e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2)) ∧
  (comp_condition (CndLt e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2))
End

Definition conditions_of_def:
  (conditions_of (Tm _ cs _ _ _) = cs)
End

Definition comp_conditions_def:
  (comp_conditions [] = Const 1w) ∧
  (* generating true for the time being *)
  (comp_conditions cs = Op And (MAP comp_condition cs))
End


Definition set_clks_def:
  (set_clks [] n = Skip) ∧
  (set_clks (CVar c::cs) n =
    Seq (Assign «c» n) (set_clks cs n))
End

(* does order matter here *)

Definition comp_step_def:
  comp_step ctxt (Tm io cnds clks loc wt) =
  case FLOOKUP ctxt.funcs loc of
  | NONE => Skip (* maybe add a return statement here *)
  | SOME fname =>
      Dec «task_ret» (Struct [Label «»; Const 0w]) (
        nested_seq [
            set_clks clks (Var «sys_time»);
            case io of
            | (Input act)  => Return (Struct [Label «fname»; Const (ARB wt)])
            | (Output eff) =>
                case FLOOKUP ctxt.ext_funcs eff of
                | NONE => Skip
                | SOME efname =>
                    Seq (ExtCall efname ARB ARB ARB ARB)
                        (Return (Struct [Label «fname»; Const (ARB wt)]))])
End


Definition comp_terms_def:
  (comp_terms ctxt [] = Skip) ∧
  (comp_terms ctxt (t::ts) =
   If (comp_conditions (conditions_of t))
        (comp_step ctxt t)
        (comp_terms ctxt ts))
End

Definition comp_location_def:
  comp_location ctxt (loc, ts) =
   case FLOOKUP ctxt.funcs loc of
   | SOME fname => (fname, [(«sys_time»,One)], comp_terms ctxt ts)
   | NONE => («», [], Skip)
End


Definition comp_prog_def:
  (comp_prog ctxt [] = []) ∧
  (comp_prog ctxt (p::ps) =
   comp_location ctxt p :: comp_prog ctxt ps)
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


(*
Definition comp_step_def:
  comp_step ctxt cval loc_var wt_var
  (Tm io cnds clks loc wt) =
  case FLOOKUP ctxt.funcs loc of
  | NONE => Skip (* maybe add a return statement here *)
  | SOME fname =>
      Seq (set_clks clks cval)
          (Seq (Store loc_var (Label fname))
               (Seq (Store wt_var (ARB wt))
                     (case io of
                      | (Input act)  => Skip
                      | (Output eff) =>
                          case FLOOKUP ctxt.ext_funcs eff of
                          | NONE => Skip
                          | SOME efname => ExtCall efname ARB ARB ARB ARB)))
End
*)

val _ = export_theory();
