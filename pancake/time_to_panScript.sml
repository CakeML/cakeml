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


Definition indice_of_def:
  indice_of xs =
  to_num o (λx. INDEX_OF x xs)
End

Definition indices_of_def:
  indices_of xs ys =
   MAP (indice_of xs) ys
End

Definition destruct_def:
  destruct e xs =
    MAP (λx. Field x e) xs
End


Definition mk_struct_def:
  mk_struct n (v1,v2) indices =
    Struct (
      MAPi (λn e.
             if (MEM n indices)
             then (Var v1)
             else Field n (Var v2))
      (GENLIST I n))
End


Definition wait_times_def:
  wait_times vname =
    list$MAP2 (λt e. Op Sub [Op Add [Const (n2w t); Var vname]; e])
End


Definition min_of_def:
  (min_of v ([]:'a exp list) = Skip) ∧
  (min_of v (e::es) =
    Seq (If (Cmp Less e (Var v))
         (Assign v e) Skip)
        (min_of v es))
End

(* calibrate wait time with system time *)
Definition update_wakeup_time_def:
  update_wakeup_time (v1,v2) wts =
    Seq (min_of v1 wts)
        (Assign v1 (Op Add [Var v1; Var v2]))
End

(* compile time expressions *)
Definition comp_exp_def:
  (comp_exp _ (ELit t) = Const (n2w t)) ∧
  (comp_exp (vname,clks) (EClock clk) =
    Field (indice_of clks clk) (Var vname)) ∧
  (comp_exp clks (ESub e1 e2) =
   Op Sub [comp_exp clks e1; comp_exp clks e2])
End

(* compile conditions of time *)
Definition comp_condition_def:
  (comp_condition var (CndLt e1 e2) =
    Cmp Less (comp_exp var e1) (comp_exp var e2)) ∧
  (comp_condition var (CndLe e1 e2) =
    Op Or [Cmp Less  (comp_exp var e1) (comp_exp var e2);
           Cmp Equal (comp_exp var e1) (comp_exp var e2)])
End

(*
   TODISC:
   generating true for [] conditions,
   to double check with semantics
*)
Definition comp_conditions_def:
  (comp_conditions clks [] = Const 1w) ∧
  (comp_conditions clks cs = Op And (MAP (comp_condition clks) cs))
End


Definition comp_step_def:
  comp_step (clks:mlstring list) (Tm io cnds tclks loc wt) =
  let clks_of_term = indices_of clks tclks;
      clks_of_wait = indices_of clks (MAP SND wt);

      (* reset clks of the term to the system time *)
      reset_clocks = mk_struct (LENGTH clks) («sys_time»,«clks») clks_of_term;

      (* wait-time should be calculated after resetting the clocks *)
      clks_of_wait = destruct reset_clocks clks_of_wait;
      wait_exps = wait_times «sys_time» (MAP FST wt) clks_of_wait;

      return  = Return (
        Struct
        [reset_clocks;
         Var «wait_set»; Var «input_set»;
         Var «wake_up_at»; Label (toString loc)]) in
    decs [
        («wait_set»,  case tclks of [] => Const 0w | _ => Const 1w);
        («input_set», case tclks of [] => Const 1w | _ => Const 0w);
        («wake_up_at», Const (-1w))]
         (nested_seq
          [update_wakeup_time («wake_up_at»,«sys_time») wait_exps;
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
  (comp_terms (vname, clks:mlstring list) [] = Skip) ∧
  (comp_terms (vname,clks) (t::ts) =
   let cds = conditions_of t
   in
   If (comp_conditions (vname, clks) cds)
      (comp_step clks t)
      (comp_terms (vname,clks) ts))
End


Definition comp_location_def:
  comp_location clks (loc, ts) =
  let n = LENGTH clks in
    (toString loc,
     [(«sys_time», One); («clks», gen_shape n)],
     comp_terms («clks»,clks) ts)
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
Definition min_of_def:
  (min_of ([]:'a exp list) = Skip) ∧
  (min_of (e::es) =
    Seq (If (Cmp Less e (Var «wake_up_at»))
         (Assign «wake_up_at» e) Skip)
        (min_of es))
End

Definition update_wake_up_time_def:
  update_wake_up_time v1 v2 wts =
    Seq (min_of wts)
        (Assign «wake_up_at» (Op Add [Var «wake_up_at»; Var «sys_time»]))
End
*)



Definition comp_init_terms_def:
  (comp_init_terms [] = Skip) ∧
  (comp_init_terms (t::ts) = Skip)
End

(*
Definition comp_terms_def:
  (comp_terms clks [] = Skip) ∧
  (comp_terms clks (t::ts) =
   If (comp_conditions (conditions_of t))
        (comp_step clks t)
        (comp_terms clks ts))
End
*)


Definition task_controller_def:
  task_controller init_loc init_tms n =
     decs
      [(«location»,Label (toString init_loc));
       («wait_set»,Const 0w);
       («input_set»,Const 0w);
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


        comp_init_terms init_tms
        (* set wait_set, input_set and wake_up_at *)




        init_wtime (tinv_of init_tm);
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
                       ExtCall «get_input_flag» «ptr1» «len1» «ptr2» «len2»;
                       Assign «input_arrived» (Load One (Var «ptr2»))]);
                   Call (Ret «task_ret» NONE)
                        (Var «location»)
                        [Var «sys_time»;
                         Field 0 (Var «task_ret») (* elapsed time clock variables *)]
                 ])
        ])
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
  init_wset: inital wake time enable flag
  init_inset: inital input time enable flag
  init_wtime: normalised initial wait time
  n : number of clocks
*)


Definition task_controller_def:
  task_controller init_loc init_tm n =
     decs
      [(«location»,Label (toString init_loc));
       («wait_set»,Const (n2w (wait_set init_tm)));
       («input_set»,Const (n2w (input_set init_tm)));
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

        init_wtime (tinv_of init_tm);
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
                       ExtCall «get_input_flag» «ptr1» «len1» «ptr2» «len2»;
                       Assign «input_arrived» (Load One (Var «ptr2»))]);
                   Call (Ret «task_ret» NONE)
                        (Var «location»)
                        [Var «sys_time»;
                         Field 0 (Var «task_ret») (* elapsed time clock variables *)]
                 ])
        ])
End


Definition start_controller_def:
  start_controller prog =
  let
    terms = MAP SND prog;
    (* the first term of the *)
    init_term = init_term_of terms;
    (* init_loc is set to zero, in timeLang *)
    n = number_of_clks prog
  in
    task_controller init_loc init_term n
End


(*
 min_of wait_time_exps;
 Assign «wake_up_at» (Op Add [Var «wake_up_at»; Var «sys_time»]
 *)

(*
  Remaining is init_wtime
*)


(*
  TODISC: what is the maximum time we support?
*)

(*
Definition indices_of_def:
  indices_of xs ys =
   mapPartial (λx. INDEX_OF x xs) ys
End
*)


val _ = export_theory();
