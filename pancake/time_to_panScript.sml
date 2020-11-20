(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory mlintTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry ["pan_common", "mlint", "timeLang", "panLang"];

Definition empty_consts_def:
  empty_consts n = GENLIST (λ_. Const 0w) n
End

Definition mk_clks_def:
  mk_clks n vname = Struct (GENLIST (λ_. Var vname) n)
End


Definition task_controller_def:
  task_controller iloc n =
     decs
      [(«location»,iloc);
       («sys_time»,Const 0w);
       («ptr1»,Const 0w);
       («len1»,Const 0w);
       («ptr2»,Const 0w); (* TOUPDATE *)
       («len2»,Const 0w); (* TOUPDATE *)
       («wait_set»,Const 1w);
       («wake_up_at»,Const 0w);
       («task_ret»,
        Struct [Struct (empty_consts n); Var «wake_up_at»; Var «location»])]
      (nested_seq
        [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
         Assign «sys_time» (Load One (Var «ptr2»));
                (* TODISC: what is the maximum time we support?
                   should we load under len2? *)

         Assign «task_ret» (Struct (mk_clks n «sys_time» :: [Var «wake_up_at»; Var «location»]));
         Assign «wake_up_at» (Op Add [Var «sys_time»; Const 1w]);
         While (Const 1w)
               (nested_seq [
                   While (Op And [Var «wait_set»;
                                  Cmp Less (Var «sys_time») (Var «wake_up_at»)])
                   (Seq (ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»)
                        (Assign «sys_time» (Load One (Var «ptr2»))));
                   Call (Ret «task_ret» NONE) (Var «location»)
                        [Var «sys_time»; Field 0 (Var «task_ret»)]
                 ])
        ])
End

(* compile time expressions *)
Definition comp_exp_def:
  (comp_exp (ELit time) = Const (n2w time)) ∧
  (comp_exp (EClock (CVar clock)) = Var «clock») ∧
  (comp_exp (ESub e1 e2) = Op Sub [comp_exp e1; comp_exp e2])
End

(* compile conditions of time *)
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

Definition part_to_total_def:
  (part_to_total (SOME x) = x:num) ∧
  (part_to_total NONE = 0)
End

Definition mk_vars_def:
  mk_vars xs ys =
    MAP (λn. (toString o part_to_total o INDEX_OF n) xs)
        ys
End

Definition time_diffs_def:
  (time_diffs [] = ARB) ∧ (* TODISC: what should be the wait time if unspecified *)
  (time_diffs ((t,c)::tcs) =
   (Op Sub [Const (n2w t); Var c]) :: time_diffs tcs)
End


Definition calc_wtime_def:
  calc_wtime (min_of:'a exp list -> 'a exp) tcs =
    min_of (time_diffs tcs):'a exp
End


Definition comp_step_def:
  comp_step clks (Tm io cnds tclks loc wt) =
  let fname  = toString loc;

      reset_clks  = mk_vars clks (MAP to_mlstring tclks);
      times       = MAP FST wt;
      wt_clocks   = MAP (to_mlstring o SND) wt;
      wtime_clks  = mk_vars clks wt_clocks;
      new_wt      = MAP2 (λt c. (t,c)) times wtime_clks;
      return      = Return (Struct [
                               Struct (MAP Var clks);
                               calc_wtime ARB new_wt;
                               Label fname]) in
    nested_seq [
        case io of
        | (Input insig)   => return
        | (Output outsig) =>
            Seq
            (ExtCall (strlit (toString outsig)) ARB ARB ARB ARB)
                     (* TODISC: what should we for ARBs  *)
            return]
End


Definition comp_terms_def:
  (comp_terms clks [] = Skip) ∧
  (comp_terms clks (t::ts) =
   If (comp_conditions (conditions_of t))
        (comp_step clks t)
        (comp_terms clks ts))
End


Definition comp_location_def:
  comp_location clks (loc, ts) =
  let n = LENGTH clks in
    (toString loc,
     MAP2 (λx y. (x,y)) («sys_time»::gen_vnames n) (gen_shape (SUC n)),
     comp_terms clks ts)

End

Definition comp_prog_def:
  (comp_prog clks [] = []) ∧
  (comp_prog clks (p::ps) =
   comp_location clks p :: comp_prog clks ps)
End

Definition comp_def:
  comp prog =
    comp_prog (clks_of prog) prog
End

(*
  Thoughts about FFI

(* Note: instead of ffi_conf, we should have a buffer_size, and that should be the length of

  current time,
  flag:

*)


*)



(*
Definition task_controller_def:
  task_controller iloc clks (ffi_confs: 'a word list) =
     nested_decs
      (clks ++
       [«location»; «sys_time»;
        «ptr1» (*0*); «len1»(*0*); «ptr2»; «len2»;
        «wait_set»; «wake_up_at»; «task_ret»])
      (empty_consts (LENGTH clks) ++
       [iloc; Const 0w;
        Const (EL 0 ffi_confs); Const (EL 1 ffi_confs);
        Const (EL 2 ffi_confs); Const (EL 3 ffi_confs);
        Const 1w; Const 0w;
        Struct [
            Struct (MAP Var clks); Var «wake_up_at»; Var «location»]])
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
                   Call (Ret «task_ret» NONE) (Var «location») (Var «sys_time» :: MAP Var clks)
                 ])
        ])
End

*)


Definition gen_vnames_def:
  gen_vnames n =
    GENLIST (λx. toString x) n
End

Definition gen_shape_def:
  gen_shape n = GENLIST (λ_. One) n
End


Definition comp_step_def:
  comp_step clks (Tm io cnds tclks loc wt) =
  let fname  = toString loc;
      reset_clks  = mk_vars clks (MAP to_mlstring tclks);
      times       = MAP FST wt;
      wt_clocks   = MAP (to_mlstring o SND) wt;
      wtime_clks  = mk_vars clks wt_clocks;
      new_wt      = MAP2 (λt c. (t,c)) times wtime_clks;
      return      = Return (Struct [
                               Struct (MAP Var clks);
                               calc_wtime ARB new_wt;
                               Label fname]) in
    nested_seq [
        assigns reset_clks (Var «sys_time»);
        case io of
        | (Input insig)   => return
        | (Output outsig) =>
            Seq
            (ExtCall (strlit (toString outsig)) ARB ARB ARB ARB)
                     (* TODISC: what should we for ARBs  *)
            return]
End

val _ = export_theory();
