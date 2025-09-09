(*
  This is a source-to-source transformation that weaken Dletrec to 
  Dlet. It is incomplete and only deals with single Dletrec declarations
 *)
Theory source_weakenlet
Ancestors
  ast evaluate misc[qualified]
Libs
  preamble

(*TODO this is an overapproximation isn't aware of shadowing*)
Definition exists_call_def:
  exists_call fun_name (Raise exp) = exists_call fun_name exp /\
  exists_call fun_name (Handle exp handle_list) = (exists_call fun_name exp \/ 
                                                 EXISTS (exists_call fun_name o SND) (handle_list)) /\
  exists_call fun_name (Lit _) = F /\
  exists_call fun_name (Con _ exps) = EXISTS (exists_call fun_name) exps /\
  exists_call fun_name (Var (Short name)) = (fun_name = name) /\
  exists_call fun_name (Var _) = F /\
  exists_call fun_name (Fun _ exp) = exists_call fun_name exp /\
  exists_call fun_name (App op exps) = EXISTS (exists_call fun_name) exps /\
  exists_call fun_name (Log lop exp1 exp2) = (exists_call fun_name exp1 \/ exists_call fun_name exp2) /\
  exists_call fun_name (If exp1 exp2 exp3) = (exists_call fun_name exp1 \/ exists_call fun_name exp2
                                              \/ exists_call fun_name exp3) /\
  exists_call fun_name (Mat exp match_list) = (exists_call fun_name exp \/ 
                                              EXISTS (exists_call fun_name o SND) match_list) /\
  exists_call fun_name (Let _ exp1 exp2) = (exists_call fun_name exp1 \/ exists_call fun_name exp2) /\
  exists_call fun_name (Letrec _ _ ) = T /\
  exists_call fun_name (Tannot exp _) = exists_call fun_name exp /\
  exists_call fun_name (Lannot exp _) = exists_call fun_name exp
End

(*TODO handle multiple function declaration*)
Definition compile_decs_def:
  (compile_decs [] = []) ∧
  (compile_decs (d::ds) =
    case d of
    | Dmod mn ds1 =>
        Dmod mn (compile_decs ds1) :: compile_decs ds
    | Dlocal ds1 ds2 =>
        Dlocal (compile_decs ds1) (compile_decs ds2) :: compile_decs ds
    | Dletrec locs ([(fun_name,first_arg,exp)]) => (if exists_call fun_name exp then d
                                                   else Dlet locs (Pvar fun_name) (Fun first_arg exp))
                                                   :: compile_decs ds
    | _ => d :: compile_decs ds)
Termination
  wf_rel_tac ‘measure (list_size dec_size)’
End
