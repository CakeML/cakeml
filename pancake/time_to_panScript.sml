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
       («wait_set»,Const 1w);
       («sys_time»,Const 0w);
       («wake_up_at»,Const 0w);
       («task_ret»,
        Struct [Struct (empty_consts n); Var «wake_up_at»; Var «location»]);
       («ptr1»,Const 0w);
       («len1»,Const 0w);
       («ptr2»,Const 0w); (* TOUPDATE *)
       («len2»,Const 0w)  (* TOUPDATE *)
      ]
      (nested_seq
       [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
        Assign «sys_time» (Load One (Var «ptr2»));
        Assign «wake_up_at» (Op Add [Var «sys_time»; Const 1w]);
        Assign «task_ret»
               (Struct (mk_clks n «sys_time» ::
                        (* to intitalise clocks to the first recorded system time *)
                        [Var «wake_up_at»; (* for pancake purpose only *)
                         Var «location»    (* for pancake purpose only *)]));
         While (Const 1w)
               (nested_seq [
                   While (Op And [Var «wait_set»;
                                  Cmp Less (Var «sys_time») (Var «wake_up_at»)])
                   (Seq (ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»)
                        (Assign «sys_time» (Load One (Var «ptr2»))));
                   Call (Ret «task_ret» NONE)
                        (Var «location»)
                        [Var «sys_time»;
                         Field 0 (Var «task_ret») (* the elapsed time for each clock variable *)]
                 ])
        ])
End

(*
  TODISC: what is the maximum time we support?
  should we load under len2?
*)

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

(* TODISC: system timw should be added to timing constants *)
Definition wait_times_def:
  (wait_times [] = ARB) ∧ (* TODISC: what should be the wait time if unspecified *)
  (wait_times ((t,e)::tes) =
   (Op Sub
    [Op Add [Const (n2w t); Var «sys_time»];
     e]) :: wait_times tes)
End

Definition min_of_def:
  (min_of ([]:'a exp list) =
   (Assign «wtime» (Var «wtime»)):'a prog) ∧
  (min_of (e::es) =
   If (Cmp Less e (Var «wtime»))
      (Assign «wtime» e)
      (min_of es))
End

Definition indices_def:
  indices fm xs =
    mapPartial (λx. FLOOKUP fm x) xs
End

Definition mk_struct_def:
  mk_struct n indices =
  Struct (
    GENLIST
    ((λn. Field n (Var «clks»))
     =++ (MAP (λx. (x, Var «sys_time»)) indices))
    n)
End

Definition destruct_def:
  destruct e xs =
  MAP (λx. Field x e) xs
End


Definition comp_step_def:
  comp_step clks_map (Tm io cnds tclks loc wt) =
  let fname  = Label (toString loc);
      number_of_clks = LENGTH (fmap_to_alist clks_map);
      tclks_indices = indices clks_map tclks;
      clocks = mk_struct number_of_clks tclks_indices;
      (* wait-time should be calculated after resetting the clocks *)
      wait_clks   = MAP SND wt;
      wait_clks_indices = indices clks_map wait_clks;
      wait_clks_exps = destruct clocks wait_clks_indices;
      time_invs_and_clks = MAP2 (λt e. (t,e)) (MAP FST wt) wait_clks_exps;
      wait_time_exps = wait_times time_invs_and_clks;
      wakeup_time = Var «wtime»; (* wait_time ARB time_invs_and_clks; *)
      return  = Return (
        Struct
        [clocks;
         wakeup_time;
         fname]) in
    Dec «wtime» (Const 0w)
        (nested_seq
         [min_of wait_time_exps;
          (* TODISC: add sys_time back *)
          Assign «wtime» (Op Add [Var «wtime»; Var «sys_time»]);
          case io of
          | (Input insig)   => return
          | (Output outsig) =>
              Seq
              (ExtCall (strlit (toString outsig)) ARB ARB ARB ARB)
              (* TODISC: what should we for ARBs  *)
              return])
End


Definition comp_terms_def:
  (comp_terms clks_map [] = Skip) ∧
  (comp_terms clks_map (t::ts) =
   If (comp_conditions (conditions_of t))
        (comp_step clks_map t)
        (comp_terms clks_map ts))
End

Definition gen_shape_def:
  gen_shape n = Comb (GENLIST (λ_. One) n)
End

Definition comp_location_def:
  comp_location clks_map (loc, ts) =
  let n = LENGTH (fmap_to_alist clks_map) in
    (toString loc,
     [(«sys_time», One); («clks», gen_shape n)],
     comp_terms clks_map ts)

End

(*
 MAP2 (λx y. (x,y)) («sys_time»::gen_vnames n) (gen_shape (SUC n)),
*)


Definition comp_prog_def:
  (comp_prog clks_map [] = []) ∧
  (comp_prog clks_map (p::ps) =
   comp_location clks_map p :: comp_prog clks_map ps)
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
val _ = export_theory();
