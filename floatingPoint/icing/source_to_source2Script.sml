(*
  This file defines the PrincessCake optimiser as a source to source pass.
  Function ‵stos_pass_with_plans‵ corresponds to ‵applyOpts‵
  from the paper.
  General correctness theorems are proven in source_to_sourceProofsScript.
  The optimiser definitions rely on the low-level functions from
  icing_rewriterScript implementing pattern matching and pattern instantiation.
*)
open semanticPrimitivesTheory evaluateTheory
     icing_rewriterTheory icing_optimisationsTheory fpOptTheory fpValTreeTheory;

open preamble;

val _ = new_theory "source_to_source2";

(**
  Rewriter configuration
  optimisations is the list of Icing-optimisations that may be applied by the
  rewriter
  canOpt is a flag that memorizes whether or not optimisation has passed through
  a "Opt" annotation
**)
Datatype:
  config = <|
    optimisations : (fp_pat # fp_pat) list;
    canOpt : bool |>
End

(**
  Define an empty configuration
**)
Definition no_fp_opt_conf_def:
  no_fp_opt_conf = <| optimisations := []; canOpt := F |>
End

Definition extend_conf_def:
  extend_conf (cfg:config) rws =
    cfg with optimisations := cfg.optimisations ++ rws
End

Theorem extend_conf_canOpt[simp]:
  (extend_conf cfg rws).canOpt = cfg.canOpt
Proof
  fs[extend_conf_def]
QED

(* Datatype for opt_path into a tree value. Here is the leaf node meaning that
  the rewrite should be applied *)
Datatype:
  opt_path = Left opt_path | Right opt_path
             | Center opt_path
             | ListIndex (num # opt_path)
             | Here
End

Datatype:
  opt_step = Apply (opt_path # ((fp_pat # fp_pat) list))
             | Label string
             | Expected ast$exp
End

Type fp_plan = “: opt_step list”

Definition MAP_plan_to_path_def:
  MAP_plan_to_path (to_path: opt_path -> opt_path) (plan: fp_plan) =
    MAP (λ step. case step of
                 | Apply (path, rws) => Apply (to_path path, rws)
                 | x => x) plan
End

Definition left_def:
  left path = Left path
End

Definition right_def:
  right path = Right path
End

Definition center_def:
  center path = Center path
End

Definition listIndex_def:
  listIndex i path = ListIndex (i, path)
End

Datatype:
  Result = Success
         | FailOpt (string # opt_path # (fp_pat # fp_pat) list)
         | FailExpect (string # ast$exp)
End

(** Disallow further optimisations **)
Definition no_optimisations_def:
  no_optimisations cfg (Lit l) = Lit l /\
  no_optimisations cfg (Var x) = Var x /\
  no_optimisations (cfg:config) (Raise e) =
    Raise (no_optimisations cfg e) /\
  no_optimisations cfg (Handle e pes) =
    Handle (no_optimisations cfg e) (MAP (\ (p,e). (p, no_optimisations cfg e)) pes) /\
  no_optimisations cfg (Con mod exps) =
    Con mod (MAP (no_optimisations cfg) exps) /\
  no_optimisations cfg (Fun s e) = Fun s e ∧
  no_optimisations cfg (App op exps) = App op (MAP (no_optimisations cfg) exps) /\
  no_optimisations cfg (Log lop e2 e3) =
    Log lop (no_optimisations cfg e2) (no_optimisations cfg e3) /\
  no_optimisations cfg (If e1 e2 e3) =
    If (no_optimisations cfg e1) (no_optimisations cfg e2) (no_optimisations cfg e3) /\
  no_optimisations cfg (Mat e pes) =
    Mat (no_optimisations cfg e) (MAP (\ (p,e). (p, no_optimisations cfg e)) pes) /\
  no_optimisations cfg (Let so e1 e2) =
    Let so (no_optimisations cfg e1) (no_optimisations cfg e2) /\
  no_optimisations cfg (Letrec ses e) =
    Letrec ses (no_optimisations cfg e) /\
  no_optimisations cfg (Tannot e t) =
    Tannot (no_optimisations cfg e) t /\
  no_optimisations cfg (Lannot e l) =
    Lannot (no_optimisations cfg e) l /\
  no_optimisations cfg (FpOptimise sc e) = FpOptimise NoOpt (no_optimisations cfg e)
Termination
  WF_REL_TAC `measure (\ (c,e). exp_size e)`
End

Definition no_optimise_pass_def:
  no_optimise_pass cfg [] = [] ∧
  no_optimise_pass cfg (e1::e2::es) =
    (no_optimise_pass cfg [e1]) ++ (no_optimise_pass cfg (e2::es))  ∧
  no_optimise_pass cfg [Fun s e] =
    [Fun s (HD (no_optimise_pass cfg [e]))] ∧
  no_optimise_pass cfg [e] = [no_optimisations cfg e]
End

Definition no_opt_decs_def:
  no_opt_decs cfg [] = [] ∧
  no_opt_decs cfg (e1::e2::es) =
    (no_opt_decs cfg [e1] ++ no_opt_decs cfg (e2::es)) ∧
  no_opt_decs cfg [Dlet loc p e] =
    [Dlet loc p (HD (no_optimise_pass cfg [e]))] ∧
  no_opt_decs cfg [Dletrec ls exps] =
    [Dletrec ls (MAP (λ (fname, param, e). (fname, param, HD (no_optimise_pass cfg [e]))) exps)] ∧
  no_opt_decs cfg [d] = [d]
End

(** Optimisation pass starts below **)
Definition perform_rewrites_def:
  perform_rewrites (cfg: config) Here rewrites (Lit l) = Lit l ∧
    (* (if (cfg.canOpt) then (rewriteFPexp rewrites (Lit l)) else (Lit l)) ∧ *)
  perform_rewrites (cfg: config) Here rewrites (App op exps) =
    (if (cfg.canOpt) then (rewriteFPexp rewrites (App op exps)) else (App op exps)) ∧
  perform_rewrites (cfg: config) Here rewrites (Var x) = Var x ∧
    (* (if (cfg.canOpt) then (rewriteFPexp rewrites (Var x)) else (Var x)) ∧ *)
  (* Make sure not to optimise away anything else (WAS: the FpOptimise or Let) *)
  perform_rewrites (cfg: config) Here rewrites e = e ∧
  (* If we are not at the end of the path, further navigate through the AST *)
  perform_rewrites cfg (Left _) rewrites (Lit l) = Lit l ∧
  perform_rewrites cfg (Left _) rewrites (Var x) = Var x ∧
  perform_rewrites cfg (Center path) rewrites (Raise e) =
    Raise (perform_rewrites cfg path rewrites e) ∧
  (* We cannot support "Handle" expressions because we must be able to reorder exceptions *)
  perform_rewrites cfg path rewrites (Handle e pes) = Handle e pes ∧
  perform_rewrites cfg (ListIndex (i, path)) rewrites (Con mod exps) =
    Con mod (MAPi (λ n e. (if (n = i) then (perform_rewrites cfg path rewrites e) else e)) exps) ∧
  (* TODO: Why is this not optimized? *)
  perform_rewrites cfg (Left _) rewrites (Fun s e) = Fun s e ∧
  perform_rewrites cfg (ListIndex (i, path)) rewrites (App op exps) =
    App op (MAPi (λ n e. (if (n = i) then (perform_rewrites cfg path rewrites e) else e)) exps) ∧
  perform_rewrites cfg (Left path) rewrites (Log lop e2 e3) =
    Log lop (perform_rewrites cfg path rewrites e2) e3 ∧
  perform_rewrites cfg (Right path) rewrites (Log lop e2 e3) =
    Log lop e2 (perform_rewrites cfg path rewrites e3) ∧
  perform_rewrites cfg (Left path) rewrites (If e1 e2 e3) =
    If (perform_rewrites cfg path rewrites e1) e2 e3 ∧
  perform_rewrites cfg (Center path) rewrites (If e1 e2 e3) =
    If e1 (perform_rewrites cfg path rewrites e2) e3 ∧
  perform_rewrites cfg (Right path) rewrites (If e1 e2 e3) =
    If e1 e2 (perform_rewrites cfg path rewrites e3) ∧
  perform_rewrites cfg (Left path) rewrites (Mat e pes) = Mat (perform_rewrites cfg path rewrites e) pes ∧
  perform_rewrites cfg (ListIndex (i, path)) rewrites (Mat e pes) =
    Mat e (MAPi (λ n (p, e'). (if (n = i) then (p, (perform_rewrites cfg path rewrites e')) else (p, e'))) pes) ∧
  perform_rewrites cfg (Left path) rewrites (Let so e1 e2) =
    Let so (perform_rewrites cfg path rewrites e1) e2 ∧
  perform_rewrites cfg (Right path) rewrites (Let so e1 e2) =
    Let so e1 (perform_rewrites cfg path rewrites e2) ∧
  perform_rewrites cfg (Center path) rewrites (Letrec ses e) =
    Letrec ses (perform_rewrites cfg path rewrites e) ∧
  perform_rewrites cfg (Center path) rewrites (Tannot e t) =
    Tannot (perform_rewrites cfg path rewrites e) t ∧
  perform_rewrites cfg (Center path) rewrites (Lannot e l) =
    Lannot (perform_rewrites cfg path rewrites e) l ∧
  perform_rewrites cfg (Center path) rewrites (FpOptimise sc e) =
    FpOptimise sc (perform_rewrites (cfg with canOpt := if sc = Opt then T else F) path rewrites e) ∧
  perform_rewrites cfg _ _ e = e
End

Definition optimise_with_plan_def:
  optimise_with_plan cfg [] e = (e, Success) ∧
  optimise_with_plan cfg (Label s :: plan) e = optimise_with_plan cfg plan e ∧
  optimise_with_plan cfg (Expected e_opt :: plan) e =
    (if e_opt = e
    then optimise_with_plan cfg plan e
    else (e, FailExpect ("Not correct expression" , e_opt))) ∧
  optimise_with_plan cfg (Apply (path, rewrites)::rest) e =
  let e_opt = perform_rewrites cfg path rewrites e in
    if e = e_opt then (e, FailOpt ("Single app", path, rewrites))
    else if (rest = [])
    then (e_opt, Success)
    else
      let (e_optFull, res) = optimise_with_plan cfg rest e_opt in
        if (e_optFull = e_opt ∧ res ≠ Success) then (e, res)
        else (e_optFull, res)
End

Definition stos_pass_with_plans_def:
  stos_pass_with_plans cfg plans [] = [] ∧
  stos_pass_with_plans cfg [] exps = MAP (λ e. (e, Success)) exps ∧
  stos_pass_with_plans cfg (plan1::plan2::rest) (e1::es) =
    (stos_pass_with_plans cfg [plan1] [e1]) ++
    (stos_pass_with_plans cfg (plan2::rest) es) ∧
  stos_pass_with_plans cfg (plan1::plans) (e1::e2::es) =
    (stos_pass_with_plans cfg [plan1] [e1]) ++
    (stos_pass_with_plans cfg plans (e2::es)) ∧
  stos_pass_with_plans cfg plans [Fun s e] =
  (let (e_opt, res) = HD (stos_pass_with_plans cfg plans [e]) in
      [(Fun s e_opt, res)]) ∧
  stos_pass_with_plans cfg [plan] [e] = [optimise_with_plan cfg plan e] ∧
  stos_pass_with_plans _ _ exps = MAP (\e. (e, Success)) exps
End

Definition stos_pass_with_plans_decs_def:
  stos_pass_with_plans_decs cfg plans [] = [] ∧
  stos_pass_with_plans_decs cfg (plans1::plans2::rest) (d1::ds) =
    (stos_pass_with_plans_decs cfg [plans1] [d1] ++ stos_pass_with_plans_decs cfg (plans2::rest) (ds)) ∧
  stos_pass_with_plans_decs cfg [plans1] [Dlet loc p e] =
  (let (e_opt, res) = HD (stos_pass_with_plans cfg [plans1] [e]) in
    [(Dlet loc p e_opt, res)] )∧
  stos_pass_with_plans_decs cfg plans [d] = [(d, Success)]
End

val _ = export_theory();

(** UNUSED **)
(*
Definition linear_interpolation_def:
     linear_interpolation = FpOptimise Opt
     (App (FP_bop FP_Add)
      [
        (App (FP_bop FP_Mul)
         [
           Var (Short "y");
           (App (FP_bop FP_Sub)
            [
              (App FpFromWord [Lit (Word64 (4607182418800017408w: word64))]);
              Var (Short "z")
            ])
         ]);
        (App (FP_bop FP_Mul)
         [
           Var (Short "x");
           Var (Short "z")
         ])
      ])
End

Theorem test__canonicalize = EVAL (
  Parse.Term ‘
   canonicalize no_fp_opt_conf (
     (FpOptimise Opt
      (App (FP_bop FP_Add) [
         App (FP_bop FP_Add) [
             App (FP_bop FP_Add) [
                 App (FP_bop FP_Add) [
                     Var (Short "c");
                     Var (Short "d")
                   ];
                 Var (Short "b")
               ];
             App (FP_bop FP_Mul) [
                 Var (Short "x");
                 Var (Short "y")
               ]
           ];
         Var (Short "a")
        ])
     )
     )
  ’);

Theorem test__top_level_multiplicants = EVAL (
  Parse.Term ‘
  top_level_multiplicants (App (FP_bop FP_Mul) [
                               App (FP_bop FP_Add) [Var (Short "x"); Lit (Word64 0w)];
                               (App (FP_bop FP_Mul) [
                                   Var (Short "y");
                                   App (FP_bop FP_Mul) [
                                       (Var (Short "a"));
                                       (Lit (Word64 7w))
                                     ]
                                 ]
                               )
                             ])
  ’)


Theorem test__move_multiplicants_to_right = EVAL (
  Parse.Term ‘
   move_multiplicants_to_right (no_fp_opt_conf with canOpt := T) [(Var (Short "d")); (Var (Short "b"))] (
     (App (FP_bop FP_Mul) [
         Var (Short "a");
         App (FP_bop FP_Mul) [
             Var (Short "b");
             App (FP_bop FP_Mul) [
                 Var (Short "c");
                 App (FP_bop FP_Mul) [
                     Var (Short "d");
                     Var (Short "e")
                   ]
               ]
           ]
       ])
     )
  ’);


Theorem test__move_multiplicants_to_right2 = EVAL (
  Parse.Term ‘
   move_multiplicants_to_right (no_fp_opt_conf with canOpt := T) [(Var (Short "x3")); (Var (Short "x3")); (Var (Short "x3"))] (
     (
       App (FP_bop FP_Mul)
           [Var (Short "x3");
            App (FP_bop FP_Mul) [Var (Short "x3"); Var (Short "x3")]]
     )
     )
  ’);

Theorem test__canonicalize_for_distributivity = EVAL (
  Parse.Term ‘
   canonicalize_for_distributivity no_fp_opt_conf (
     (FpOptimise Opt
      (App (FP_bop FP_Add)
        [App (FP_bop FP_Mul)
         [Var (Short "x3");
          App (FP_bop FP_Mul)
              [Var (Short "x3");
               App (FP_bop FP_Mul)
                   [Var (Short "x3"); Var (Short "x3")]]];
         App (FP_bop FP_Add)
             [App (FP_bop FP_Mul)
              [Var (Short "x3");
               App (FP_bop FP_Mul)
                   [Var (Short "x3"); Var (Short "x3")]];
              App (FP_bop FP_Add)
                  [App (FP_bop FP_Mul)
                   [Var (Short "x3"); Var (Short "x3")];
                   App (FP_bop FP_Add)
                       [Var (Short "x3");
                        App FpFromWord
                            [Lit (Word64 0x4010000000000000w)]]]]])
      )
     )
     ’);

Theorem test__canonicalize_for_distributivity2 = EVAL (
  Parse.Term ‘
   let e = (FpOptimise Opt
            (App (FP_bop FP_Add)
             [App (FP_bop FP_Mul)
              [Var (Short "x3");
               App (FP_bop FP_Mul)
                   [Var (Short "x3");
                    App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")]]];
              App (FP_bop FP_Add)
                  [App (FP_bop FP_Mul)
                   [Var (Short "x3");
                    App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")]];
                   App (FP_bop FP_Add)
                       [App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")];
                        App (FP_bop FP_Add)
                            [Var (Short "x3");
                             App FpFromWord
                                 [Lit (Word64 0x4010000000000000w)]]]]])
           ) in
     let (_, plan) = canonicalize_for_distributivity no_fp_opt_conf e in
       optimise_with_plan no_fp_opt_conf plan e
  ’);


Theorem test__apply_distributivity2 = EVAL (
  Parse.Term ‘
   let e = (FpOptimise Opt
            (App (FP_bop FP_Add)
             [App (FP_bop FP_Mul)
              [Var (Short "x3");
               App (FP_bop FP_Mul)
                   [Var (Short "x3");
                    App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")]]];
              App (FP_bop FP_Add)
                  [App (FP_bop FP_Mul)
                   [Var (Short "x3");
                    App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")]];
                   App (FP_bop FP_Add)
                       [App (FP_bop FP_Mul)
                        [Var (Short "x3"); Var (Short "x3")];
                        App (FP_bop FP_Add)
                            [Var (Short "x3");
                             App FpFromWord
                                 [Lit (Word64 0x4010000000000000w)]]]]])) in
     let (_, plan) = apply_distributivity no_fp_opt_conf e in
       optimise_with_plan no_fp_opt_conf plan e
  ’);

Theorem test__apply_distributivity = EVAL (
  Parse.Term ‘
   apply_distributivity no_fp_opt_conf (
     (FpOptimise Opt
      (App (FP_bop FP_Add)
           [App (FP_bop FP_Mul)
              [App (FP_bop FP_Add)
                 [App (FP_bop FP_Mul)
                    [App (FP_bop FP_Add)
                       [App (FP_bop FP_Mul)
                          [Var (Short "x3"); Var (Short "x3")];
                        App (FP_bop FP_Add)
                          [Var (Short "x3");
                           App FpFromWord [Lit (Word64 0x3FF0000000000000w)]]];
                     Var (Short "x3")];
                  App FpFromWord [Lit (Word64 0x3FF0000000000000w)]];
               Var (Short "x3")];
            App FpFromWord [Lit (Word64 0x4010000000000000w)]])
     )
     )
  ’);

*)
