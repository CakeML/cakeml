(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory mlintTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "timeLang", "panLang"];

(*
  things to discuss are under TODISC
*)

Definition mk_clks_def:
  mk_clks clks = Struct (MAP (Var o strlit) clks)
End

(* clks: 'a exp
   Struct [Var «»; Var «»]
*)


(* I thin we need a mapping from mlstring to index of the clock arrays *)


Definition task_controller_def:
  task_controller iloc clks (ffi_confs: 'a word list) =
    nested_decs
      [«location»; «clks»; «sys_time»;
       «ptr1»; «len1»; «ptr2»; «len2»;
       «wait_set»; «wake_up_at»; «task_ret»]
      [iloc; mk_clks clks; Const 0w;
       Const (EL 0 ffi_confs); Const (EL 1 ffi_confs);
       Const (EL 2 ffi_confs); Const (EL 3 ffi_confs);
       Const 1w; Const 0w;
       Struct [Var «location»; Var «clks»; Var «wake_up_at»]]
      (nested_seq
        [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
         Assign «sys_time» (Load One (Var «ptr2»));
                (* TODISC: what is the maximum time we support?
                   should we load under len2? *)
         Assign  «wake_up_at» (Op Add [Var «sys_time»; Const 1w]);
         While (Const 1w)
               (nested_seq [
                   While (Op And [Var «wait_set»;
                                  Cmp Less (Var «sys_time») (Var «wake_up_at»)])
                   (Seq (ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»)
                        (Assign «sys_time» (Load One (Var «ptr2»))));
                   Call (Ret «task_ret» NONE) (Var «location») [Var «sys_time»; Var «clks»]
                 ])
        ])
End


(* compile time expressions *)
Definition comp_exp_def:
  (comp_exp (ELit time) = Const (n2w time)) ∧
  (comp_exp (EClock (CVar clock)) = Var «clock») ∧
  (comp_exp (ESub e1 e2) = Op Sub [comp_exp e1; comp_exp e2])
End


(* compile condistions of time *)
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
   TODISC:
   generating true for [] conditions,
   to double check with semantics
*)
Definition comp_conditions_def:
  (comp_conditions [] = Const 1w) ∧
  (comp_conditions cs = Op And (MAP comp_condition cs))
End


Definition set_clks_def:
  (set_clks clks [] n = Skip) ∧
  (set_clks clks (CVar c::cs) n =
    Seq (Assign «c» n) (set_clks clks cs n))
End

(* only react to input *)
(* fix *)
Definition time_diffs_def:
  (time_diffs [] = ARB) ∧ (* what should be the wait time if unspecified *)
  (time_diffs ((t,CVar c)::tcs) =
   (Op Sub [Const (n2w t); Var «c»]) :: time_diffs tcs)
End

(* statement for this *)
(* fix *)
Definition cal_wtime_def:
  cal_wtime (min_of:'a exp list -> 'a exp) tcs =
  min_of (time_diffs tcs):'a exp
End

Definition comp_step_def:
  comp_step clks (Tm io cnds tclks loc wt) =
  let fname = mlint$num_to_str loc in
    nested_seq [
        set_clks clks tclks (Var «sys_time»);
        case io of
        | (Input in_signal)  => Return (Struct [Label fname; Struct ARB; cal_wtime ARB wt])
        | (Output out_signal) => ARB]
End

Struct [Var «location»; Var «clks»; Var «wake_up_at»]

Definition comp_terms_def:
  (comp_terms [] = Skip) ∧
  (comp_terms (t::ts) =
   If (comp_conditions (conditions_of t))
        (comp_step t)
        (comp_terms ts))
End

(*
Definition comp_location_def:
  comp_location ctxt (loc, ts) =
   case FLOOKUP ctxt.funcs loc of
   | SOME fname => (fname, [(«sys_time»,One)], comp_terms ctxt ts)
   | NONE => («», [], Skip)
End
*)

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

Definition clks_of_prog_def:
  (clks_of_prog ps =
     clks_accum [] (FLAT (MAP clks_of_term ps)))
End

Definition shape_of_clks_def:
  shape_of_clks ps =
    Comb (GENLIST (λ_. One) (LENGTH (clks_of_prog ps)))
End

Definition comp_location_def:
  comp_location clk_shp (loc, ts) =
  (mlint$num_to_str loc,
   [(«sys_time»,One); («clks»,clk_shp)], ARB (* comp_terms ctxt ts*) )

End

Definition comp_prog_def:
  (comp_prog clk_shp [] = []) ∧
  (comp_prog clk_shp (p::ps) =
   comp_location clk_shp p :: comp_prog clk_shp ps)
End


Definition comp_def:
  comp prog = comp_prog (shape_of_clks prog) prog
End

(*
  Thoughts about clocks-passing:
  Pancake only permits declared return values.
  Ideally we should not pass clocks as an arguement of "Call",
  rather each finction should only return the restted clocks, and
  we should then update such clocks to the system time after the call.
  But this would not be possible as figuring out the relevant clocks
  for each function requires some workaround.

  the feasible solution then I guess is to pass all of the clocks
  to the function, the function then updates the clock it needs to and
  returns all of the clock back
*)


(* next steps: add clocks to the return value *)

(*
clocks are in the memory
need to pass a parameter that is a pointer to the clock array
*)

(*
  input trigger is remaining
*)



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
