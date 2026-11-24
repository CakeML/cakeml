(*
  A pass within evalSem that runs before source_to_source. The input
  program uses Eval in the EvalPending style: a one-argument call to Eval
  provides the compiler state and a closure implementing the compiler,
  and subsequent two-argument calls give only an environment and the
  declarations. The output program uses Eval in the EvalDecs style.

  The pass puts a prelude in front of the program. The prelude defines
  functions $init and $eval, which keep the compiler state and the
  compiler closure in references; $eval runs the compiler closure and
  hands its result to Eval. In the rest of the program, one-argument
  calls to Eval become calls to $init, two-argument calls become calls
  to $eval, and variable names that start with $ get one more $ in
  front, so that nothing in the program can shadow $init and $eval.
  Type and location annotations (Tannot and Lannot) are removed.
 *)
Theory source_eval_init
Ancestors
  ast mlstring
Libs
  preamble

(* names that start with $ get one more $ in front *)
Definition rename_def:
  rename (n:mlstring) =
    case explode n of
    | #"$"::_ => implode (#"$" :: explode n)
    | _ => n
End

Definition rename_id_def:
  rename_id (Short n) = Short (rename n) ∧
  rename_id (Long m id) = Long m (rename_id id)
End

Definition compile_pat_def:
  compile_pat Pany = Pany ∧
  compile_pat (Pvar n) = Pvar (rename n) ∧
  compile_pat (Plit l) = Plit l ∧
  compile_pat (Pcon cn ps) = Pcon cn (MAP compile_pat ps) ∧
  compile_pat (Pref p) = Pref (compile_pat p) ∧
  compile_pat (Pas p n) = Pas (compile_pat p) (rename n) ∧
  compile_pat (Ptannot p t) = Ptannot (compile_pat p) t
End

Definition compile_exp_def:
  compile_exp (Raise e) = Raise (compile_exp e) ∧
  compile_exp (Handle e pes) =
    Handle (compile_exp e) (MAP (λ(p,e). (compile_pat p, compile_exp e)) pes) ∧
  compile_exp (Lit l) = Lit l ∧
  compile_exp (Con cn es) = Con cn (MAP compile_exp es) ∧
  compile_exp (Var id) = Var (rename_id id) ∧
  compile_exp (Fun n e) = Fun (rename n) (compile_exp e) ∧
  compile_exp (App op es) =
    (if op = Eval then
       (case es of
        | [e] => App Opapp [Var (Short «$init»); compile_exp e]
        | [e1; e2] =>
            App Opapp [Var (Short «$eval»);
                       Con NONE [compile_exp e1; compile_exp e2]]
        | _ => App op (MAP compile_exp es))
     else App op (MAP compile_exp es)) ∧
  compile_exp (Log lop e1 e2) = Log lop (compile_exp e1) (compile_exp e2) ∧
  compile_exp (If e1 e2 e3) =
    If (compile_exp e1) (compile_exp e2) (compile_exp e3) ∧
  compile_exp (Mat e pes) =
    Mat (compile_exp e) (MAP (λ(p,e). (compile_pat p, compile_exp e)) pes) ∧
  compile_exp (Let xo e1 e2) =
    Let (OPTION_MAP rename xo) (compile_exp e1) (compile_exp e2) ∧
  compile_exp (Letrec funs e) =
    Letrec (MAP (λ(f,x,e). (rename f, rename x, compile_exp e)) funs)
           (compile_exp e) ∧
  compile_exp (Tannot e t) = compile_exp e ∧
  compile_exp (Lannot e l) = compile_exp e ∧
  compile_exp (Open path e) = Open path (compile_exp e) ∧
  compile_exp (Assert e sa) = Assert (compile_exp e) sa
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ rw [exp_size_def]
  \\ gvs []
  \\ drule_then (qspec_then ‘exp_size’ assume_tac) MEM_list_size
  \\ gvs []
End

Definition compile_dec_def:
  compile_dec (Dlet locs p e) = Dlet locs (compile_pat p) (compile_exp e) ∧
  compile_dec (Dletrec locs funs) =
    Dletrec locs (MAP (λ(f,x,e). (rename f, rename x, compile_exp e)) funs) ∧
  compile_dec (Dtype locs tds) = Dtype locs tds ∧
  compile_dec (Dtabbrev locs tvs tn t) = Dtabbrev locs tvs tn t ∧
  compile_dec (Dexn locs cn ts) = Dexn locs cn ts ∧
  compile_dec (Dmod mn ds) = Dmod mn (MAP compile_dec ds) ∧
  compile_dec (Dlocal lds ds) =
    Dlocal (MAP compile_dec lds) (MAP compile_dec ds) ∧
  compile_dec (Denv n) = Denv (rename n) ∧
  compile_dec (Dopen locs path) = Dopen locs path
End

(* $init (s,c) stores the compiler state s and the compiler closure c *)
Definition init_body_def:
  init_body =
    Mat (Var (Short «x»))
      [(Pcon NONE [Pvar «s»; Pvar «c»],
        Let NONE (App Opassign [Var (Short «pending»); Lit (IntLit 0)])
          (Let NONE (App Opassign [Var (Short «state»); Var (Short «s»)])
             (App Opassign [Var (Short «compiler»); Var (Short «c»)])))]
End

(* $eval (env,decs) fails, returning (env, "Compiler error"), unless
   $init has been called and the compiler closure succeeds on the
   compiler state and decs; otherwise it stores the new compiler state,
   calls Eval with the compiler's input and output, and pairs the
   resulting environment with "". The compiler closure signals failure
   by raising an exception, which is caught and turned into a result
   tagged 1; a successful result is tagged 0. *)
Definition eval_fail_def:
  eval_fail =
    Con NONE [Var (Short «env»); Lit (StrLit «Compiler error»)]
End

Definition eval_body_def:
  eval_body =
    Mat (Var (Short «x»))
      [(Pcon NONE [Pvar «env»; Pvar «decs»],
        Mat (App Opderef [Var (Short «pending»)])
          [(Plit (IntLit 0),
            Let (SOME «st») (App Opderef [Var (Short «state»)])
              (Mat (Handle
                      (Con NONE
                         [Lit (IntLit 0);
                          App Opapp [App Opderef [Var (Short «compiler»)];
                                     Con NONE [App Env_id [Var (Short «env»)];
                                               Var (Short «st»);
                                               Var (Short «decs»)]]])
                      [(Pany, Con NONE [Lit (IntLit 1);
                                        Con NONE [Lit (IntLit 0);
                                                  Lit (IntLit 0);
                                                  Lit (IntLit 0)]])])
                 [(Pcon NONE [Plit (IntLit 0);
                              Pcon NONE [Pvar «st2»; Pvar «bs»; Pvar «ws»]],
                   Let NONE
                     (App Opassign [Var (Short «state»); Var (Short «st2»)])
                     (Con NONE
                        [App Eval [Var (Short «env»); Var (Short «st»);
                                   Var (Short «decs»); Var (Short «st2»);
                                   Var (Short «bs»); Var (Short «ws»)];
                         Lit (StrLit «»)]));
                  (Pany, eval_fail)]));
           (Pany, eval_fail)])]
End

(* $init and $eval are defined by one declaration so that their
   closures share the same environment *)
Definition prelude_def:
  prelude =
    Dlocal
      [Dlet NoLocs (Pvar «pending») (App Opref [Lit (IntLit 1)]);
       Dlet NoLocs (Pvar «state») (App Opref [Lit (IntLit 0)]);
       Dlet NoLocs (Pvar «compiler») (App Opref [Lit (IntLit 0)])]
      [Dlet NoLocs (Pcon NONE [Pvar «$init»; Pvar «$eval»])
         (Con NONE [Fun «x» init_body; Fun «x» eval_body])]
End

Definition compile_decs_def:
  compile_decs (p:dec list) = prelude :: MAP compile_dec p
End

Definition inc_compile_decs_def:
  inc_compile_decs (p:dec list) = MAP compile_dec p
End
