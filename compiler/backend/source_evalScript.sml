(*
  This compiler phase inserts a copy of the compiler, if it is needed,
  to convert Eval operations on source declarations into lower-level
  Eval/Install operations on compiled code.
*)

open preamble astTheory terminationTheory stringTheory;

val _ = new_theory "source_eval";
val _ = set_grammar_ancestry ["ast", "string"];
val _ = numLib.prefer_num();

Datatype:
  config = <|
    (* a series of declarations that define a function "compiler", a
       function "load", and maybe other things, but do not change the
       state/refs/ffi *)
    compiler_decs : dec list ;
    (* a filename to give to the "load" function to load the initial state *)
    filename : string
  |>
End

Definition has_Eval_def1:
  (has_Eval (Raise e)) = has_Eval e ∧
  (has_Eval (Handle e pes)) = (has_Eval e ∨ EXISTS has_Eval (MAP SND pes)) ∧
  (has_Eval (Con cn es)) = EXISTS has_Eval es ∧
  (has_Eval (Fun x e)) = has_Eval e ∧
  (has_Eval (ast$App op es)) = (op = Eval ∨ EXISTS has_Eval es) ∧
  (has_Eval (Log lop e1 e2)) = (has_Eval e1 ∨ has_Eval e2) ∧
  (has_Eval (If e1 e2 e3)) = (has_Eval e1 ∨ has_Eval e2 ∨ has_Eval e3) ∧
  (has_Eval (Mat e pes)) = (has_Eval e ∨ EXISTS has_Eval (MAP SND pes)) ∧
  (has_Eval (Let nm e1 e2)) = (has_Eval e1 ∨ has_Eval e2) ∧
  (has_Eval (ast$Letrec funs e)) = (has_Eval e ∨
    EXISTS has_Eval (MAP (SND o SND) funs)) ∧
  (has_Eval (Tannot x t) = has_Eval x) ∧
  (has_Eval (Lannot x locs) = has_Eval x)
Termination
  WF_REL_TAC `measure exp_size`
  \\ rw [exp_size_def]
  \\ fs (map (REWRITE_RULE [size_abbrevs])
    [funs_size_thm, pes_size_thm, exps_size_thm])
  \\ fs [MEM_MAP, EXISTS_PROD]
  \\ fs [MEM_SPLIT, exp_size_def, SUM_APPEND]
End

Theorem has_Eval_def = CONV_RULE (DEPTH_CONV ETA_CONV) has_Eval_def1

Definition has_Eval_dec_def1:
  (has_Eval_dec (Dlet _ _ e) = has_Eval e) ∧
  (has_Eval_dec (Dletrec _ funs) = EXISTS has_Eval (MAP (SND o SND) funs)) ∧
  (has_Eval_dec (Dmod _ ds) = EXISTS has_Eval_dec ds) ∧
  (has_Eval_dec (Dlocal lds ds) = (EXISTS has_Eval_dec lds
    ∨ EXISTS has_Eval_dec ds)) ∧
  (has_Eval_dec _ = F)
Termination
  WF_REL_TAC `measure dec_size`
  \\ rw [dec_size_def, dec1_size_eq]
  \\ fs [MEM_SPLIT, list_size_APPEND, list_size_def]
End

Theorem has_Eval_dec_def = CONV_RULE (DEPTH_CONV ETA_CONV) has_Eval_dec_def1

(* ok. should I be putting the compiler at the start? yeah, make the refs
   simpler. *)

Definition compiler_module_name_def:
  compiler_module_name = "CakeML.Internal"
End

Definition mk_exp_list_def:
  mk_exp_list [] = Con (SOME (Short "[]")) [] /\
  mk_exp_list (x :: xs) = Con (SOME (Short "::")) [x; mk_exp_list xs]
End

Definition mk_matches_def:
  mk_matches [] x = x /\
  mk_matches ((p, x) :: xs) y = Mat x [(p, mk_matches xs y)]
End

Definition eval_fun_def:
  eval_fun fname = Fun "x" (mk_matches [
    (Pvar "s1", Mat (App Opderef [Var (Short "state")])
        [(Pcon (SOME (Short "::")) [Pvar "s"; Pany],
                Var (Short "s"));
            (Pany, App Opapp [Var (Long "Compiler" (Short "load"));
                Lit (StrLit fname)])]);
    (Pcon NONE [Pvar "env_id"; Pvar "decs"], Var (Short "x"));
    (Pcon NONE [Pvar "bytes"; Pvar "words"; Pvar "s2"],
        (App Opapp [Var (Long "Compiler" (Short "compiler"));
                    Con NONE (MAP (Var o Short) ["env_id"; "s1"; "decs"])]));
    (Pany, (App Opassign [Var (Short "state");
                    mk_exp_list [Var (Short "s2")]]));
    (Pvar "env_id", (App Eval (MAP (Var o Short)
                    ["env_id"; "decs"; "s1"; "bytes"; "words"; "s2"])))
  ] (Var (Short "env_id")))
End

Definition compiler_module_def:
  compiler_module cfg = Dmod compiler_module_name [
    Dmod "Compiler" cfg.compiler_decs ;
    Dlet unknown_loc (Pvar "state") (App Opref [Con (SOME (Short "[]")) []]) ;
    Dlet unknown_loc (Pvar "eval") (eval_fun cfg.filename)
  ]
End

Definition adj_mod_name_def:
  (* TODO: check this string code translates to something sane *)
  adj_mod_name mnm = if compiler_module_name ≼ mnm
    then mnm ++ "X"
    else mnm
End

Definition adj_id_def:
  adj_id (Short nm) = Short nm ∧
  adj_id (Long mnm id) = Long (adj_mod_name mnm) (adj_id id)
End

Definition compile_exp_def:
  (compile_exp (Var id)) = Var (adj_id id) ∧
  (compile_exp (Raise e)) = Raise (compile_exp e) ∧
  (compile_exp (Handle e pes)) = Handle (compile_exp e)
    (MAP (\(a, x). (a, compile_exp x)) pes) ∧
  (compile_exp (Con cn es)) = Con cn (MAP compile_exp es) ∧
  (compile_exp (Fun x e)) = Fun x (compile_exp e) ∧
  (compile_exp (App op es)) = (if op = Eval
    then App Opapp [Var (Long compiler_module_name (Short "eval")); Con NONE es]
    else App op (MAP compile_exp es)) ∧
  (compile_exp (Log lop e1 e2)) = Log lop (compile_exp e1) (compile_exp e2) ∧
  (compile_exp (If e1 e2 e3)) =
    If (compile_exp e1) (compile_exp e2) (compile_exp e3) ∧
  (compile_exp (Mat e pes)) = Mat (compile_exp e)
    (MAP (\(a, x). (a, compile_exp x)) pes) ∧
  (compile_exp (Let nm e1 e2)) = Let nm (compile_exp e1) (compile_exp e2) ∧
  (compile_exp (Letrec funs e)) = Letrec
    (MAP (\(a, b, x). (a, b, compile_exp x)) funs)
    (compile_exp e) ∧
  (compile_exp (Tannot x t) = Tannot (compile_exp x) t) ∧
  (compile_exp (Lannot x locs) = Lannot (compile_exp x) locs)
Termination
  WF_REL_TAC `measure exp_size`
  \\ rw [exp_size_def]
  \\ fs (map (REWRITE_RULE [size_abbrevs])
    [funs_size_thm, pes_size_thm, exps_size_thm])
  \\ fs [MEM_MAP, EXISTS_PROD]
  \\ fs [MEM_SPLIT, exp_size_def, SUM_APPEND]
End

Definition compile_dec_def:
  (compile_dec (Dlet loc nm e) = Dlet loc nm (compile_exp e)) ∧
  (compile_dec (Dletrec locs funs) =
        Dletrec locs (MAP (\(a, b, x). (a, b, compile_exp x)) funs)) ∧
  (compile_dec (Dmod mnm ds) = Dmod mnm (MAP compile_dec ds)) ∧
  (compile_dec (Dlocal lds ds) = Dlocal (MAP compile_dec lds)
        (MAP compile_dec ds)) ∧
  (compile_dec d = d)
Termination
  WF_REL_TAC `measure dec_size`
  \\ rw [dec_size_def, dec1_size_eq]
  \\ fs [MEM_SPLIT, list_size_APPEND, list_size_def]
End

Definition compile_def:
  compile cfg decs = if EXISTS has_Eval_dec decs
    then compiler_module cfg :: MAP compile_dec decs
    else decs
End

val _ = export_theory();
