(*
  Compilation from timeLang to panLang
*)
open preamble pan_commonTheory mlintTheory
     timeLangTheory panLangTheory

val _ = new_theory "time_to_pan"

val _ = set_grammar_ancestry
        ["pan_common", "mlint", "timeLang", "panLang"];


Definition ffi_buffer_address_def:
  ffi_buffer_address = 4000w:'a word
End


Definition ffi_buffer_size_def:
  ffi_buffer_size = 16w:'a word
End


Definition empty_consts_def:
  empty_consts n = GENLIST (λ_. Const 0w) n
End


Definition gen_shape_def:
  gen_shape n = Comb (GENLIST (λ_. One) n)
End


Definition mk_clks_def:
  mk_clks n vname = Struct (GENLIST (λ_. Var vname) n)
End


Definition to_num_def:
  (to_num NONE     = 0:num) ∧
  (to_num (SOME n) = n)
End


Definition indices_of_def:
  indices_of xs ys =
   MAP (to_num o (λx. INDEX_OF x xs)) ys
End

Definition destruct_def:
  destruct e xs =
    MAP (λx. Field x e) xs
End


Definition mk_struct_def:
  mk_struct n indices =
    Struct (
      MAPi (λn e.
             if (MEM n indices)
             then (Var «sys_time»)
             else Field n (Var «clks»))
      (GENLIST I n))
End


Definition wait_times_def:
  wait_times =
    list$MAP2 (λt e. Op Sub [Op Add [Const (n2w t); Var «sys_time»]; e])
End


Definition min_of_def:
  (min_of ([]:'a exp list) = Skip) ∧
  (min_of (e::es) =
    Seq (If (Cmp Less e (Var «wtime»))
         (Assign «wtime» e) Skip)
        (min_of es))
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


Definition comp_step_def:
  comp_step clks (Tm io cnds tclks loc wt) =
  let term_clks = indices_of clks tclks;
      wait_clks = indices_of clks (MAP SND wt);

      (* reset clks of the term to the system time *)
      clocks = mk_struct (LENGTH clks) term_clks;

      (* wait-time should be calculated after resetting the clocks *)
      wait_clocks = destruct clocks wait_clks;
      wait_time_exps = wait_times (MAP FST wt) wait_clocks;

      return  = Return (
        Struct
        [clocks;
         Var «wait_set»; Var «input_set»;
         Var «wake_up_at»; Label (toString loc)]) in
    decs [
        («wait_set»,  case tclks of [] => Const 0w | _ => Const 1w);
        («input_set», case tclks of [] => Const 1w | _ => Const 0w);
        («wake_up_at», Const (-1w))]
         (nested_seq
          [min_of wait_time_exps;
           (* calibrate wait time with system time *)
           Assign «wtime» (Op Add [Var «wtime»; Var «sys_time»]);
           case io of
           | (Input insig)   => return
           | (Output outsig) =>
               decs
               [(«ptr1»,Const 0w);
                («len1»,Const 0w);
                («ptr2»,Const ffi_buffer_address);
                («len2»,Const ffi_buffer_size)
               ] (Seq
                  (ExtCall (strlit (toString outsig)) «ptr1» «len1» «ptr2» «len2»)
                  return)
          ])
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
     [(«sys_time», One); («clks», gen_shape n)],
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

(* either implement it or return from the task *)
(*
Definition not_def:
  not e =
    If _ _ _
End
*)

(*
  init_loc: initial state
  init_wtime: normalised initial wait time
  n : number of clocks
*)

Definition task_controller_def:
  task_controller buffer_size init_loc init_wset init_inset init_wtime n =
     decs
      [(«location»,init_loc);
       («wait_set»,Const (n2w init_wset));
       («input_set»,Const (n2w init_inset));
       («sys_time»,Const 0w);
       («wake_up_at»,Const 0w);
       («task_ret»,
        Struct (Struct (empty_consts n) :: MAP Var
                [«wait_set»; «input_set»;
                 «wake_up_at»; «location»]));
       («ptr1»,Const 0w);
       («len1»,Const 0w);
       («ptr2»,Const ffi_buffer_address);
       («len2»,Const ffi_buffer_size)
      ]
      (nested_seq
       [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
        Assign «sys_time» (Load One (Var «ptr2»));
        Assign «wake_up_at» (Op Add [Var «sys_time»; Const (n2w init_wtime)]);
        (* initialise clocks to the system time *)
        Assign «task_ret»
               (Struct (mk_clks n «sys_time» :: MAP Var
                        [«wait_set»; «input_set»; «wake_up_at»; «location»]));
         While (Const 1w)
               (nested_seq [ (* wait_set and input_set are mutually exclusive *)
                   While (Op Or
                          [Op And [Var «wait_set»;
                                   Cmp Less (Var «sys_time») (Var «wake_up_at»)];
                           Op And [Var «input_set»;
                                   Var «input_arrived»]])
                   (nested_seq [
                       ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
                       Assign «sys_time» (Load One (Var «ptr2»));
                       ExtCall «get_in_flag» «ptr1» «len1» «ptr2» «len2»;
                       Assign «input_arrived» (Load One (Var «ptr2»))]);
                   Call (Ret «task_ret» NONE)
                        (Var «location»)
                        [Var «sys_time»;
                         Field 0 (Var «task_ret») (* elapsed time clock variables *)]
                 ])
        ])
End

(*
  TODISC: what is the maximum time we support?
*)

(*
Definition indices_of_def:
  indices_of xs ys =
   mapPartial (λx. INDEX_OF x xs) ys
End
*)

(*
to ask questions there *)

val _ = export_theory();
