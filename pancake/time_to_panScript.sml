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


Definition negate_def:
  negate vname =
  If  (Cmp Equal (Var vname) (Const 0w))
      (Assign vname (Const 1w))
      (Assign vname (Const 0w))
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
         Var «wait_set»;
         Var «wake_up_at»; Label (toString loc)]) in
    decs [
        («wait_set»,  case tclks of [] => Const 0w | _ => Const 1w);
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
  (comp_terms fcomp (vname,clks:mlstring list) [] = Skip) ∧
  (comp_terms fcomp (vname,clks) (t::ts) =
   let cds = conditions_of t
   in
   If (comp_conditions (vname, clks) cds)
      (fcomp clks t)
      (comp_terms fcomp (vname,clks) ts))
End


Definition comp_location_def:
  comp_location clks (loc, ts) =
  let n = LENGTH clks in
    (toString loc,
     [(«sys_time», One); («clks», gen_shape n)],
     comp_terms comp_step («clks»,clks) ts)
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
  ¬ (is_input ∨ (wait_set ∧ ¬ (sys_time < wake_up_at))) =
  ¬is_input  ∧ (¬wait_set ∨ (sys_time < wake_up_at))
*)


(* either implement it or return from the task *)
(*
Definition not_def:
  not e =
    If _ _ _
End
*)

(*
  External functions:
  get_time, check_input
*)


Definition poll_def:
  poll =
    Op And [(*Not*) Var «is_input»;
            Op Or
               [(* Not *) Var «wait_set»;
                Cmp Less (Var «sys_time») (Var «wake_up_at»)]]
End


Definition task_controller_def:
  task_controller init_loc init_wake_up n =
     decs
      [(«location»,Label (toString init_loc));
       («wait_set»,
        case init_wake_up of NONE => Const 0w | _ => Const 1w);
       («wake_up_at»,
        case init_wake_up of NONE => Const 0w | SOME n => Const (n2w n));
       («is_input»,Const 0w);
       («sys_time»,Const 0w);
       («task_ret»,
        Struct (Struct (empty_consts n) :: MAP Var
                [«wait_set»; «wake_up_at»; «location»]));
       («ptr1»,Const 0w);
       («len1»,Const 0w);
       («ptr2»,Const ffi_buffer_address);
       («len2»,Const ffi_buffer_size)
      ]
      (nested_seq
       [ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
        Assign «sys_time» (Load One (Var «ptr2»));
        Assign «task_ret»
               (Struct (mk_clks n «sys_time» :: MAP Var
                        [«wait_set»; «wake_up_at»; «location»]));

         While (Const 1w)
               (nested_seq [
                   negate  «wait_set»;
                   (* can be optimised, i.e. return the negated wait_set from the function call *)
                   ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
                   Assign  «sys_time» (Load One (Var «ptr2»));
                   ExtCall «check_input» «ptr1» «len1» «ptr2» «len2»;
                   Assign  «is_input» (Load One (Var «ptr2»));
                   negate  «is_input»;
                   While (Op And [Var «is_input»; (* Not *)
                                  Op Or
                                  [Var «wait_set»; (* Not *)
                                   Cmp Less (Var «sys_time») (Var «wake_up_at»)]])
                     (nested_seq [
                         ExtCall «get_time» «ptr1» «len1» «ptr2» «len2»;
                         Assign  «sys_time» (Load One (Var «ptr2»));
                         ExtCall «check_input» «ptr1» «len1» «ptr2» «len2»;
                         Assign  «is_input» (Load One (Var «ptr2»))]);
                   nested_seq [
                       Call (Ret «task_ret» NONE) (Var «location»)
                       [Var «sys_time»; Field 0 (Var «task_ret»)
                                        (* elapsed time clock variables *)];
                       Assign «wait_set»   (Field 1 (Var «task_ret»));
                       Assign «wake_up_at» (Field 2 (Var «task_ret»));
                       Assign «location»   (Field 3 (Var «task_ret»))
                     ]
                 ])
        ])
End


Definition ohd_def:
  (ohd [] = (0:num,[])) ∧
  (ohd (x::xs) = x)
End

Definition start_controller_def:
  start_controller (ta_prog:program) =
  let
    prog = FST ta_prog;
    init_loc = FST (ohd prog);
    init_wake_up = SND ta_prog;
    n = number_of_clks prog
  in
    task_controller init_loc init_wake_up n
End



val _ = export_theory();
