(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "timeLang", "panLang"];

(*
  things to discuss are under ToDisc
*)

(* controller, imagine the compiler is in place  *)

Definition mk_clks_def:
  mk_clks clks = Struct (MAP (Var o strlit) clks)
End

Definition task_controller_def:
  task_controller iloc clks (ffi_confs: 'a word list) =
    nested_decs
      [«location»; «clks»; «sys_time»;
       «ptr1»; «len1»; «ptr2»; «len2»;
       «wait_set»; «wake_up_at»; «task_ret»]
      [iloc; mk_clks clks; Const 0w;
       Const (EL 0 ffi_confs); Const (EL 1 ffi_confs);
       Const (EL 2 ffi_confs); Const (EL 3 ffi_confs);
       Const 1w; Const 0w; Struct [Var «location»; Var «wake_up_at»]]
      (nested_seq
        [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
         Assign «sys_time» (Load One (Var «ptr2»))
                (* ToDisc: what is the maximum time we support?
                   should we load under len2? *)
        ])
End


(*
   ExtCall «get_time» «sys_time» ARB ARB ARB;
   Assign  «wake_up_at» (Op Add [Var «sys_time»; Const 1w])
*)

Definition task_controller_def:
  task_controller clks iloc =
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



(*
clocks are in the memory
need to pass a parameter that is a pointer to the clock array
*)

Definition mk_clk_var:
  mk_clk_var clk = strlit clk (* «clk» is not the same *)
End


Definition abc_def:
  (mk_clks [] = Struct []) /\
  (mk_clks [] = Struct [])
End




(*
  input trigger is remaining
*)






























Definition comp_exp_def:
  (comp_exp (ELit time) = Const (n2w time)) ∧
  (comp_exp (EClock (CVar clock)) = Var «clock») ∧
  (comp_exp (ESub e1 e2) = Op Sub [comp_exp e1; comp_exp e2])
End


Definition comp_condition_def:
  (comp_condition (CndLt e1 e2) =
    Cmp Less (comp_exp e1) (comp_exp e2)) ∧
  (comp_condition (CndLe e1 e2) =
    Op Or [Cmp Less  (comp_exp e1) (comp_exp e2);
           Cmp Equal (comp_exp e1) (comp_exp e2)])
End

Definition conditions_of_def:
  (conditions_of (Tm _ cs _ _ _) = cs)
End

(*
   ToDisc:
   generating true for [] conditions,
   to double check with semantics
*)

Definition comp_conditions_def:
  (comp_conditions [] = Const 1w) ∧
  (comp_conditions cs = Op And (MAP comp_condition cs))
End

(* fix *)

Definition set_clks_def:
  (set_clks [] n = Skip) ∧
  (set_clks (CVar c::cs) n =
    Seq (Assign «c» n) (set_clks cs n))
End

(* only react to input *)
(* fix *)
Definition time_diffs_def:
  (time_diffs [] = ARB) ∧ (* what should be the wait time if unspecified *)
  (time_diffs ((t,CVar c)::tcs) =
   (Op Sub [Const (r2w t); Var «c»]) :: time_diffs tcs)
End

(* statement for this *)
(* fix *)
Definition cal_wtime_def:
  cal_wtime (min_of:'a exp list -> 'a exp) tcs =
  min_of (time_diffs tcs):'a exp
End


Definition comp_step_def:
  comp_step ctxt (Tm io cnds clks loc wt) =
  case FLOOKUP ctxt.funcs loc of
  | NONE => Skip (* maybe add a return statement here *)
  | SOME fname =>
        nested_seq [
            set_clks clks (Var «sys_time»);
            case io of
            | (Input act)  => Return (Struct [Label «fname»; cal_wtime ARB wt])
            | (Output eff) =>
                case FLOOKUP ctxt.ext_funcs eff of
                | NONE => Skip
                | SOME efname =>
                    Seq (ExtCall efname ARB ARB ARB ARB)
                        (Return (Struct [Label «fname»; cal_wtime ARB wt]))]
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
  start from compiling the functions and then fix the controller,
  because controller is a bit complicated and also a bit involved
*)







(*
num -> mlstring,
basis/pure/mlint
num_to_str
*)



Datatype:
  context =
  <| funcs     : timeLang$loc    |-> panLang$funname;
     ext_funcs : timeLang$effect |-> panLang$funname
  |>
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
