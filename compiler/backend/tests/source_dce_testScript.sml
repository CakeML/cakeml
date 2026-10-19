(*
  Tests for the source dead-code elimination pass.
*)
Theory source_dce_test[no_sig_docs]
Ancestors
  source_dce
Libs
  preamble

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

(* an unused function is removed, a used one is kept *)
Theorem test_unused[local]:
  compile_decs
    [Dlet l (Pvar «unused») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «used») (Fun «y» (Var (Short «y»)));
     Dlet l Pany (App Opapp [Var (Short «used»); Lit (IntLit 4)])] =
    [Dlet l (Pvar «used») (Fun «y» (Var (Short «y»)));
     Dlet l Pany (App Opapp [Var (Short «used»); Lit (IntLit 4)])]
Proof
  EVAL_TAC
QED

(* unused declarations that are not functions are removed when neither the
   expression nor the pattern can have an effect *)
Theorem test_pure[local]:
  compile_decs
    [Dlet l (Pvar «x») (App (Arith Add IntT) [Lit (IntLit 1); Lit (IntLit 2)]);
     Dlet l (Pcon NONE [Pvar «a»; Pvar «b»])
       (Con NONE [Var (Short «x»); App Opderef [Var (Short «r»)]]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* a declaration that only allocates something that nothing can reach is
   removed too *)
Theorem test_alloc[local]:
  compile_decs
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «a») (App AallocEmpty [Con NONE []]);
     Dlet l (Pvar «v») (App AallocFixed [Lit (IntLit 1); Lit (IntLit 2)]);
     Dlet l (Pvar «arr») (App Aalloc [Lit (IntLit 5); Lit (IntLit 0)]);
     Dlet l (Pvar «arr2»)
       (App Aalloc [Lannot (Tannot (Lit (IntLit 5)) (Atapp [] (Short «int»))) l;
                    Lit (IntLit 0)]);
     Dlet l (Pvar «bs») (App Aw8alloc [Lit (IntLit 5); Lit (Word8 0w)]);
     Dlet l (Pvar «t»)
       (App (ThunkOp (AllocThunk NotEvaluated)) [Fun «u» (Lit (IntLit 1))]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* declarations that can change the state, raise an exception or diverge are
   kept, and so are patterns that can fail to match. Note the two Aalloc:s:
   the length is not known to be non-negative in either. *)
Theorem test_impure[local]:
  compile_decs
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App (Arith Div IntT) [Lit (IntLit 1); Var (Short «n»)]);
     Dlet l Pany (App (FromTo IntT CharT) [Lit (IntLit 300)]);
     Dlet l Pany (App Asub [Var (Short «arr»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Var (Short «n»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Lit (IntLit (-1)); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Tannot (Lit (IntLit (-1)))
                                     (Atapp [] (Short «int»)); Lit (IntLit 0)]);
     Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l Pany (Raise (Con (SOME (Short «Bind»)) []));
     Dlet l (Plit (IntLit 3)) (Lit (IntLit 3))] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App (Arith Div IntT) [Lit (IntLit 1); Var (Short «n»)]);
     Dlet l Pany (App (FromTo IntT CharT) [Lit (IntLit 300)]);
     Dlet l Pany (App Asub [Var (Short «arr»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Var (Short «n»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Lit (IntLit (-1)); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Tannot (Lit (IntLit (-1)))
                                     (Atapp [] (Short «int»)); Lit (IntLit 0)]);
     Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l Pany (Raise (Con (SOME (Short «Bind»)) []));
     Dlet l (Plit (IntLit 3)) (Lit (IntLit 3))]
Proof
  EVAL_TAC
QED

(* type abbreviations are always removed *)
Theorem test_dtabbrev[local]:
  compile_decs
    [Dtabbrev l [] «t» (Atapp [] (Short «int»));
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* in a declaration that is kept, the unused names of the pattern are
   replaced by wildcards *)
Theorem test_prune[local]:
  compile_decs
    [Dlet l (Pcon NONE [Pvar «a»; Pvar «b»])
       (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l (Pas (Pvar «d») «e»)
       (App Opassign [Var (Short «out»); Lit (IntLit 1)]);
     Dlet l (Pvar «c») (App Opassign [Var (Short «out»); Var (Short «b»)])] =
    [Dlet l (Pcon NONE [Pany; Pvar «b»])
       (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)]);
     Dlet l Pany (App Opassign [Var (Short «out»); Var (Short «b»)])]
Proof
  EVAL_TAC
QED

(* a Dlocal of which nothing is left is dropped; a module is emptied but
   kept, since dropping it could change how later qualified names resolve *)
Theorem test_empty_mod[local]:
  compile_decs
    [Dmod «M» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))];
     Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))] [];
     Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] [];
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dmod «M» [];
     Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] [];
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* a Dlocal whose local part is left empty is replaced by its visible part *)
Theorem test_empty_local[local]:
  compile_decs
    [Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)));
             Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
            [Dlet l (Pvar «h») (Fun «x» (Var (Short «x»)))];
     Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]
            [Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 2)])]] =
    [Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
            [Dlet l (Pvar «h») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 2)])]
Proof
  EVAL_TAC
QED

(* a case expression is pure only if one of its patterns always matches *)
Theorem test_pure_mat[local]:
  compile_decs
    [Dlet l (Pvar «x») (Mat (Var (Short «y»)) [(Pany, Lit (IntLit 2))]);
     Dlet l Pany (Mat (Var (Short «y»)) [(Plit (IntLit 1), Lit (IntLit 2))])] =
    [Dlet l Pany (Mat (Var (Short «y»)) [(Plit (IntLit 1), Lit (IntLit 2))])]
Proof
  EVAL_TAC
QED

(* whole chains of unused functions are removed, including Dletrec:s, and
   a Dlet with a wildcard pattern that binds a Fun is always removed *)
Theorem test_chain[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dletrec l [(«g»,«y»,App Opapp [Var (Short «f»); Var (Short «g»)])];
     Dlet l Pany (Fun «z» (App Opapp [Var (Short «g»); Var (Short «z»)]))] = []
Proof
  EVAL_TAC
QED

(* a Dletrec is kept if any of its names is used *)
Theorem test_letrec_used[local]:
  compile_decs
    [Dletrec l [(«f»,«x»,Var (Short «g»)); («g»,«y»,Var (Short «f»))];
     Dlet l Pany (App Opapp [Var (Short «g»); Lit (IntLit 1)])] =
    [Dletrec l [(«f»,«x»,Var (Short «g»)); («g»,«y»,Var (Short «f»))];
     Dlet l Pany (App Opapp [Var (Short «g»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a later declaration of the same name shadows an earlier one, which makes
   the earlier one dead *)
Theorem test_shadow_dletrec[local]:
  compile_decs
    [Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* but the shadowing declaration can itself refer to the shadowed one *)
Theorem test_shadow_dlet[local]:
  compile_decs
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «foo») (Fun «x» (App Opapp [Var (Short «foo»);
                                              Var (Short «x»)]));
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «foo») (Fun «x» (App Opapp [Var (Short «foo»);
                                              Var (Short «x»)]));
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the local part of a Dlocal is not visible after it, so it does not
   shadow anything *)
Theorem test_local_no_shadow[local]:
  compile_decs
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlocal [Dlet l (Pvar «foo») (Fun «x» (Lit (IntLit 1)))] [];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlocal [Dlet l (Pvar «foo») (Fun «x» (Lit (IntLit 1)))] [];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a local variable with the same name does not count as a use *)
Theorem test_shadow[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dlet l Pany
       (Let (SOME «f») (Fun «x» (Var (Short «x»)))
            (App Opapp [Var (Short «f»); Lit (IntLit 1)]))] =
    [Dlet l Pany
       (Let (SOME «f») (Fun «x» (Var (Short «x»)))
            (App Opapp [Var (Short «f»); Lit (IntLit 1)]))]
Proof
  EVAL_TAC
QED

(* an allocation is kept when the location it makes is used, and a name
   bound by a pattern of a case expression is not a use *)
Theorem test_effect[local]:
  compile_decs
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «f») (Fun «x» (App Opassign [Var (Short «r»); Var (Short «x»)]));
     Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)));
     Dlet l Pany
       (Mat (Lit (IntLit 1))
          [(Pvar «g», App Opapp [Var (Short «f»); Var (Short «g»)])])] =
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «f») (Fun «x» (App Opassign [Var (Short «r»); Var (Short «x»)]));
     Dlet l Pany
       (Mat (Lit (IntLit 1))
          [(Pvar «g», App Opapp [Var (Short «f»); Var (Short «g»)])])]
Proof
  EVAL_TAC
QED

(* unused declarations inside modules are removed, and qualified names
   count as uses of the declarations they refer to *)
Theorem test_module[local]:
  compile_decs
    [Dmod «M» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
               Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany
       (App Opapp [Var (Long «M» (Short «g»)); Lit (IntLit 1)])] =
    [Dmod «M» [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany
       (App Opapp [Var (Long «M» (Short «g»)); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* only uses in later declarations count *)
Theorem test_later_use_only[local]:
  compile_decs
    [Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))] =
    [Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* nested modules *)
Theorem test_nested_module[local]:
  compile_decs
    [Dmod «A» [Dmod «B» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
                         Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]];
     Dlet l Pany
       (App Opapp [Var (Long «A» (Long «B» (Short «g»))); Lit (IntLit 1)])] =
    [Dmod «A» [Dmod «B» [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]];
     Dlet l Pany
       (App Opapp [Var (Long «A» (Long «B» (Short «g»))); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the local part of a Dlocal is only used by its visible part *)
Theorem test_local[local]:
  compile_decs
    [Dlocal [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
             Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]
            [Dlet l (Pvar «h») (Fun «x» (App Opapp [Var (Short «f»);
                                                    Var (Short «x»)]))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 1)])] =
    [Dlocal [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))]
            [Dlet l (Pvar «h») (Fun «x» (App Opapp [Var (Short «f»);
                                                    Var (Short «x»)]))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a Denv whose name is never used is dropped, and its presence does not
   stop the other declarations from being removed *)
Theorem test_denv_unused[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the name of a Denv counts as used only in declarations that are kept *)
Theorem test_denv_used_by_dead[local]:
  compile_decs
    [Denv «e»;
     Dlet l (Pvar «f») (Fun «x» (Var (Short «e»)));
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a program where a Denv survives is left alone *)
Theorem test_denv_used[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opapp [Var (Short «g»); Var (Short «e»)])] =
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opapp [Var (Short «g»); Var (Short «e»)])]
Proof
  EVAL_TAC
QED

(* an Eval does not stop the pass by itself: it takes an Env value to
   evaluate anything, and only a Denv makes one. The Eval is kept, since
   it is not a pure expression, but the dead function next to it goes. *)
Theorem test_eval[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dlet l Pany (App Eval [Var (Short «x»)])] =
    [Dlet l Pany (App Eval [Var (Short «x»)])]
Proof
  EVAL_TAC
QED

(* but a program that has both is left alone, because the Denv survives *)
Theorem test_eval_denv[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Eval [Var (Short «e»)])] =
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Eval [Var (Short «e»)])]
Proof
  EVAL_TAC
QED
