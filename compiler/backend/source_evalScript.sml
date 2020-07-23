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

Definition compile_pat_def:
  (compile_pat (Pcon id ps) = Pcon (OPTION_MAP adj_id id) (MAP compile_pat ps))
  ∧
  (compile_pat (Pref p) = Pref (compile_pat p)) ∧
  (compile_pat (Ptannot p t) = compile_pat p) ∧
  (compile_pat p = p)
Termination
  WF_REL_TAC `measure pat_size`
  \\ simp_tac bool_ss [GSYM size_abbrevs, pats_size_thm]
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND]
End

Definition compile_exp_def:
  (compile_exp (Var id) = Var (adj_id id)) ∧
  (compile_exp (Raise e) = Raise (compile_exp e)) ∧
  (compile_exp (Handle e pes) = Handle (compile_exp e)
    (MAP (\(p, x). (compile_pat p, compile_exp x)) pes)) ∧
  (compile_exp (Con cn es) = Con (OPTION_MAP adj_id cn) (MAP compile_exp es)) ∧
  (compile_exp (Fun x e) = Fun x (compile_exp e)) ∧
  (compile_exp (App op es) = (if op = Eval
    then App Opapp [Var (Long compiler_module_name (Short "eval"));
        Con NONE (MAP compile_exp es)]
    else App op (MAP compile_exp es))) ∧
  (compile_exp (Log lop e1 e2) = Log lop (compile_exp e1) (compile_exp e2)) ∧
  (compile_exp (If e1 e2 e3) =
    If (compile_exp e1) (compile_exp e2) (compile_exp e3)) ∧
  (compile_exp (Mat e pes) = Mat (compile_exp e)
    (MAP (\(p, x). (compile_pat p, compile_exp x)) pes)) ∧
  (compile_exp (Let nm e1 e2) = Let nm (compile_exp e1) (compile_exp e2)) ∧
  (compile_exp (Letrec funs e) = Letrec
    (MAP (\(a, b, x). (a, b, compile_exp x)) funs)
    (compile_exp e)) ∧
  (compile_exp (Tannot x t) = compile_exp x) ∧
  (compile_exp (Lannot x locs) = compile_exp x) ∧
  (compile_exp exp = exp)
Termination
  WF_REL_TAC `measure exp_size`
  \\ rw [exp_size_def]
  \\ fs (map (REWRITE_RULE [size_abbrevs])
    [funs_size_thm, pes_size_thm, exps_size_thm])
  \\ fs [MEM_MAP, EXISTS_PROD]
  \\ fs [MEM_SPLIT, exp_size_def, SUM_APPEND]
End

Theorem ast_t1_size:
  ast_t1_size ts = LENGTH ts + SUM (MAP ast_t_size ts)
Proof
  Induct_on `ts` \\ simp [ast_t_size_def]
QED

Definition compile_type_def:
  (compile_type (Atapp ts id) = Atapp (MAP compile_type ts) (adj_id id)) /\
  (compile_type (Attup ts) = Attup (MAP compile_type ts)) /\
  (compile_type (Atfun t1 t2) = Atfun (compile_type t1) (compile_type t2)) /\
  (compile_type t = t)
Termination
  WF_REL_TAC `measure ast_t_size`
  \\ rw [ast_t_size_def, ast_t1_size]
  \\ fs [MEM_SPLIT, ast_t_size_def, SUM_APPEND]
End

Definition compile_dec_def:
  (compile_dec (Dlet loc nm e) = Dlet loc nm (compile_exp e)) ∧
  (compile_dec (Dletrec locs funs) =
        Dletrec locs (MAP (\(a, b, x). (a, b, compile_exp x)) funs)) ∧
  (compile_dec (Dmod mnm ds) = Dmod (adj_mod_name mnm) (MAP compile_dec ds)) ∧
  (compile_dec (Dlocal lds ds) = Dlocal (MAP compile_dec lds)
        (MAP compile_dec ds)) ∧
  (compile_dec (Dexn locs cn ts) = Dexn locs cn (MAP compile_type ts)) ∧
  (compile_dec (Dtabbrev locs vs nm t) =
        Dtabbrev locs vs nm (compile_type t)) ∧
  (compile_dec (Dtype locs td) = Dtype locs
        (MAP (I ## (I ## MAP (I ## MAP compile_type))) td)) ∧
  (compile_dec d = d)
Termination
  WF_REL_TAC `measure dec_size`
  \\ rw [dec_size_def, dec1_size_eq]
  \\ fs [MEM_SPLIT, list_size_APPEND, list_size_def]
End

Definition has_res_mod_name_def:
  (* TODO: check this string code translates to something sane *)
  has_res_mod_name mnm = (compiler_module_name ≼ mnm)
End

Definition must_adj_id_def:
  must_adj_id (Short nm) = F ∧
  must_adj_id (Long mnm id) = (has_res_mod_name mnm ∨ must_adj_id id)
End

Definition must_adj_pat_def:
  (must_adj_pat (Pcon id ps) = ((case id of SOME c => must_adj_id c | _ => F) ∨
        EXISTS must_adj_pat ps)) ∧
  (must_adj_pat (Pref p) = must_adj_pat p) ∧
  (must_adj_pat (Ptannot p t) = must_adj_pat p) ∧
  (must_adj_pat p = F)
Termination
  WF_REL_TAC `measure pat_size`
  \\ simp_tac bool_ss [GSYM size_abbrevs, pats_size_thm]
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND]
End

Definition must_adj_exp_def:
  (must_adj_exp (Var id) = must_adj_id id) ∧
  (must_adj_exp (Raise e) = must_adj_exp e) ∧
  (must_adj_exp (Handle e pes) = (must_adj_exp e ∨
        (EXISTS (\(p, x). must_adj_pat p ∨ must_adj_exp x) pes))) ∧
  (must_adj_exp (Con cn es) = ((case cn of SOME c => must_adj_id c | _ => F) ∨
        EXISTS must_adj_exp es)) ∧
  (must_adj_exp (Fun x e) = must_adj_exp e) ∧
  (must_adj_exp (App op es) = (op = Eval ∨ EXISTS must_adj_exp es)) ∧
  (must_adj_exp (Log lop e1 e2) = (must_adj_exp e1 ∨ must_adj_exp e2)) ∧
  (must_adj_exp (If e1 e2 e3) = (must_adj_exp e1 ∨ must_adj_exp e2 ∨
        must_adj_exp e3)) ∧
  (must_adj_exp (Mat e pes) = (must_adj_exp e ∨
        (EXISTS (\(p, x). must_adj_pat p ∨ must_adj_exp x) pes))) ∧
  (must_adj_exp (Let nm e1 e2) = (must_adj_exp e1 ∨ must_adj_exp e2)) ∧
  (must_adj_exp (Letrec funs e) = (must_adj_exp e ∨
    (EXISTS (\(a, b, x). must_adj_exp x) funs))) ∧
  (must_adj_exp (Tannot x t) = must_adj_exp x) ∧
  (must_adj_exp (Lannot x locs) = must_adj_exp x)
Termination
  WF_REL_TAC `measure exp_size`
  \\ rw [exp_size_def]
  \\ fs (map (REWRITE_RULE [size_abbrevs])
    [funs_size_thm, pes_size_thm, exps_size_thm])
  \\ fs [MEM_MAP, EXISTS_PROD]
  \\ fs [MEM_SPLIT, exp_size_def, SUM_APPEND]
End

Definition must_adj_type_def:
  (must_adj_type (Atapp ts id) <=> must_adj_id id ∨ EXISTS must_adj_type ts) /\
  (must_adj_type (Attup ts) = EXISTS must_adj_type ts) /\
  (must_adj_type (Atfun t1 t2) <=> must_adj_type t1 ∨ must_adj_type t2) /\
  (must_adj_type t = F)
Termination
  WF_REL_TAC `measure ast_t_size`
  \\ rw [ast_t_size_def, ast_t1_size]
  \\ fs [MEM_SPLIT, ast_t_size_def, SUM_APPEND]
End

Definition must_adj_dec_def:
  (must_adj_dec (Dlet loc nm e) = must_adj_exp e) ∧
  (must_adj_dec (Dletrec locs funs) =
        EXISTS (\(a, b, x). must_adj_exp x) funs) ∧
  (must_adj_dec (Dmod mnm ds) <=> has_res_mod_name mnm ∨
        EXISTS must_adj_dec ds) ∧
  (must_adj_dec (Dlocal lds ds) <=> EXISTS must_adj_dec lds ∨
        EXISTS must_adj_dec ds) ∧
  (must_adj_dec (Dexn locs cn ts) = EXISTS must_adj_type ts) ∧
  (must_adj_dec (Dtabbrev locs vs nm t) = must_adj_type t) ∧
  (must_adj_dec (Dtype locs td) = 
        EXISTS (EXISTS (EXISTS must_adj_type o SND) o SND o SND) td) ∧
  (must_adj_dec d = F)
Termination
  WF_REL_TAC `measure dec_size`
  \\ rw [dec_size_def, dec1_size_eq]
  \\ fs [MEM_SPLIT, list_size_APPEND, list_size_def]
End

Definition fast_compile_dec_def:
  fast_compile_dec dec = if must_adj_dec dec then compile_dec dec else dec
End

Definition compile_def:
  compile cfg decs = if EXISTS has_Eval_dec decs
    then compiler_module cfg :: MAP fast_compile_dec decs
    else decs
End

val _ = export_theory();
