(*
  Source to source optimiser, applying Icing optimizations
  This file defines the high-level Icing optimisers.
  Their general correctness theorems are proven in source_to_sourceProofsScript.
  The optimiser definitions rely on the low-level functions from
  icing_rewriterScript implementing pattern matching and pattern instantiation.
*)
open semanticPrimitivesTheory evaluateTheory terminationTheory
     icing_rewriterTheory icing_optimisationsTheory fpOptTheory fpValTreeTheory;

open preamble;

val _ = new_theory "source_to_source";

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

(** Optimisation pass starts below **)

(** Step 1:
    optimise walks over the body of a function declaration/letrec and
    applies the optimisations in the configuration depending on whether a
    Opt scope was already encountered or not
 **)
Definition optimise_def:
  optimise cfg (Lit l) = Lit l /\
  optimise cfg (Var x) = Var x /\
  optimise (cfg:config) (Raise e) =
    Raise (optimise cfg e) /\
  (* We cannot support "Handle" expressions because we must be able to reorder exceptions *)
  optimise cfg (Handle e pes) = Handle e pes ∧
  optimise cfg (Con mod exps) =
    Con mod (MAP (optimise cfg) exps) /\
  optimise cfg (Fun s e) = Fun s e ∧
  optimise cfg (App op exps) =
    (let exps_opt = MAP (optimise cfg) exps in
      if (cfg.canOpt)
      then (rewriteFPexp (cfg.optimisations) (App op exps_opt))
      else (App op exps_opt)) /\
  optimise cfg (Log lop e2 e3) =
    Log lop (optimise cfg e2) (optimise cfg e3) /\
  optimise cfg (If e1 e2 e3) =
    If (optimise cfg e1) (optimise cfg e2) (optimise cfg e3) /\
  optimise cfg (Mat e pes) =
    Mat (optimise cfg e) (MAP (\ (p,e). (p, optimise cfg e)) pes) /\
  optimise cfg (Let so e1 e2) =
    Let so (optimise cfg e1) (optimise cfg e2) /\
  optimise cfg (Letrec ses e) =
    Letrec ses (optimise cfg e) /\
  optimise cfg (Tannot e t) =
    Tannot (optimise cfg e) t /\
  optimise cfg (Lannot e l) =
    Lannot (optimise cfg e) l /\
  optimise cfg (FpOptimise sc e) =
    FpOptimise sc (optimise (cfg with canOpt := if sc = Opt then T else F) e)
Termination
  WF_REL_TAC `measure (\ (c,e). exp_size e)` \\ fs[]
  \\ rpt conj_tac
  (*
  >- (Induct_on `ses` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]) *)
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
     (*
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]) *)
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

(* Datatype for opt_path into a tree value. Here is the leaf node meaning that the
  rewrite should be applied *)
val _ = Hol_datatype ‘
         opt_path =   Left of opt_path | Right of opt_path | Center of opt_path | ListIndex of (num # opt_path) | Here’;

Type fp_plan = “: (opt_path # (fp_pat # fp_pat) list) list”

Definition MAP_plan_to_path_def:
  MAP_plan_to_path (to_path: opt_path -> opt_path) (plan: fp_plan) = MAP (λ (path, rws). (to_path path, rws)) plan
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

Definition canonicalize_sub_def:
(* Canonicalize sub to add and mul times -1.0 *)
  canonicalize_sub e =
    case e of
    | (App (FP_bop FP_Sub) [e1; e2]) =>
        (App (FP_bop FP_Add) [e1; rewriteFPexp [fp_neg_times_minus_one] e2],
         [(Here, [fp_sub_add]); (ListIndex (1, Here),  [fp_neg_times_minus_one])])
    | _ => (e, [])
End

Definition canonicalize_app_def:
  canonicalize_app e =
    case e of
    (* Canonicalize to right associative *)
    | (App (FP_bop op) [App (FP_bop op2) [e1_1; e1_2]; e2]) =>
        (if (op = op2 ∧ op ≠ FP_Sub ∧ op ≠ FP_Div) then
           let (local_rewritten, local_plan) =
               (App (FP_bop op) [e1_1; App (FP_bop op2) [e1_2; e2]], [(Here, [fp_assoc_gen op])]) in
             case local_rewritten of
             | App (FP_bop op) [e1'; e2'] =>
                 (let (child_rewritten, child_plan) = canonicalize_app e2' in
                    (App (FP_bop op) [e1'; child_rewritten],
                     local_plan ++ (MAP_plan_to_path (listIndex 1) child_plan)))
             | _ => (local_rewritten, local_plan)
         else (canonicalize_sub e))
    (* Canonicalize constants to the rhs *)
    | (App (FP_bop op) [App FpFromWord [l]; e2]) =>
        (if (op ≠ FP_Sub ∧ op ≠ FP_Div) then
           (rewriteFPexp [fp_comm_gen op] e, [(Here, [fp_comm_gen op])])
         else
           (e, []))
    | (App (FP_bop FP_Sub) [e1; e2]) =>
        canonicalize_sub e
    | _ => (e, [])
Termination
  WF_REL_TAC ‘measure (λe. exp_size e)’ \\ fs[]
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def]
  \\ fs[astTheory.op_size_def, fpValTreeTheory.fp_bop_size_def]
End

Definition canonicalize_def:
  canonicalize (cfg: config) (FpOptimise sc e) = (
  let (e_can, plan: fp_plan) = canonicalize (cfg with canOpt := if sc = Opt then T else F) e in
    (FpOptimise sc e_can, MAP_plan_to_path center plan)
  ) ∧
  canonicalize cfg (App op exps) = (
    let individuals = MAP (canonicalize cfg) exps in
      let exps_can = MAP FST individuals;
          plan: fp_plan = FLAT ( MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals ) in
        if (cfg.canOpt) then
          let (new_e, can_plan) = canonicalize_app (App op exps_can) in
            (new_e, plan ++ can_plan)
        else (App op exps_can, plan)
    ) ∧
  canonicalize cfg (Let so e1 e2) = (
    let (e1_can, plan_left) = canonicalize cfg e1;
        (e2_can, plan_right) = canonicalize cfg e2 in
        (Let so e1_can e2_can, (MAP_plan_to_path left plan_left) ++ (MAP_plan_to_path right plan_right))
    ) ∧
  canonicalize cfg (Con mod exps) = (
    let (individuals: (exp # (opt_path # (fp_pat # fp_pat) list) list) list) = MAP (canonicalize cfg) exps in
      let exps_can = MAP FST individuals;
          plan = FLAT ( MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals ) in
        (Con mod exps_can, plan)
    ) ∧
  canonicalize cfg (Log lop e2 e3) = (
    let (e2_can, plan_left) = canonicalize cfg e2;
        (e3_can, plan_right) = canonicalize cfg e3 in
      (Log lop e2_can e3_can, (MAP_plan_to_path left plan_left) ++ (MAP_plan_to_path right plan_right))
    ) ∧
  canonicalize cfg (If e1 e2 e3) = (
    let (e1_can, plan_left) = canonicalize cfg e1;
        (e2_can, plan_center) = canonicalize cfg e2;
        (e3_can, plan_right) = canonicalize cfg e3 in
      (If e1_can e2_can e3_can,
       (MAP_plan_to_path left plan_left)
       ++
       (MAP_plan_to_path center plan_center)
       ++
       (MAP_plan_to_path right plan_right))
    ) ∧
  canonicalize cfg (Lannot e l) = (
    let (e_can, plan_center) = canonicalize cfg e in
      (Lannot e_can l, MAP_plan_to_path center plan_center)
    ) ∧
  canonicalize cfg (Tannot e t) = (
    let (e_can, plan_center) = canonicalize cfg e in
      (Tannot e_can t, MAP_plan_to_path center plan_center)
    ) ∧
  canonicalize cfg (Letrec ses e) = (
    let (e_can, plan_center) = canonicalize cfg e in
      (Letrec ses e_can, MAP_plan_to_path center plan_center)
    ) ∧
  canonicalize cfg (Mat e pes) = (
    let (e_can, plan_left) = canonicalize cfg e;
        individuals = MAP (λ (p, e'). (p, canonicalize cfg e')) pes in
      let pes_can = MAP (λ(p, (e', _)). (p, e')) individuals;
          pes_plan = FLAT (MAPi (λ i (_, (_, plani)). MAP_plan_to_path (listIndex i) plani) individuals);
          e_plan = MAP_plan_to_path left plan_left in
        (Mat e_can pes_can, e_plan ++ pes_plan)
    ) ∧
  (* We do not apply any canonicalization plan to the rest *)
  canonicalize cfg e = (e, [])
Termination
  WF_REL_TAC ‘measure (λ (cfg, e). exp_size e)’ \\ fs[]
  \\ strip_tac
  >- (
  Induct_on ‘pes’ \\ fs[]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspecl_then [‘e’, ‘cfg’, ‘e_can’, ‘plan_left’, ‘p’, ‘e'’] strip_assume_tac)
  \\ pop_assum imp_res_tac \\ fs[astTheory.exp_size_def]
  )
  >- (
  strip_tac
  \\ Induct_on ‘exps’ \\ fs[]
  \\ rpt strip_tac \\ fs[astTheory.exp_size_def]
  >- (
    first_x_assum (qspecl_then [‘op’, ‘a’] strip_assume_tac)
    \\ pop_assum imp_res_tac \\ fs[]
    )
  \\ qpat_x_assum ‘∀ mod a. _ ⇒ exp_size a < _’ (qspecl_then [‘mod’, ‘a’] strip_assume_tac)
  \\ pop_assum imp_res_tac \\ fs[]
  )
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

Definition post_order_dfs_for_plan_def:
  post_order_dfs_for_plan (f: config -> exp -> (exp # fp_plan) option) (cfg: config) (FpOptimise sc e) = (
  let (e_can, plan: fp_plan) = post_order_dfs_for_plan f (cfg with canOpt := if sc = Opt then T else F) e in
    ((FpOptimise sc e_can), MAP (λ (path, rws). (Center path, rws)) plan)
  ) ∧
  post_order_dfs_for_plan f cfg (App op exps) = (
    let individuals = MAP (post_order_dfs_for_plan f cfg) exps in
      let exps_can = MAP FST individuals;
          plan: fp_plan = FLAT ( MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals ) in
        if (cfg.canOpt) then
          case f cfg (App op exps_can) of
          | (SOME (new_e, can_plan)) => (new_e, plan ++ can_plan)
          | NONE => (App op exps_can, plan)
         else (App op exps_can, plan)
    ) ∧
  post_order_dfs_for_plan f cfg (Let so e1 e2) = (
    let (e1_can, plan_left) = post_order_dfs_for_plan f cfg e1;
        (e2_can, plan_right) = post_order_dfs_for_plan f cfg e2 in
        (Let so e1_can e2_can, (MAP_plan_to_path left plan_left) ++ (MAP_plan_to_path right plan_right))
    ) ∧
  post_order_dfs_for_plan f cfg (Con mod exps) = (
    let (individuals: (exp # (opt_path # (fp_pat # fp_pat) list) list) list) =
        MAP (post_order_dfs_for_plan f cfg) exps in
      let exps_can = MAP FST individuals;
          plan = FLAT ( MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals ) in
        (Con mod exps_can, plan)
    ) ∧
  post_order_dfs_for_plan f cfg (Log lop e2 e3) = (
    let (e2_can, plan_left) = post_order_dfs_for_plan f cfg e2;
        (e3_can, plan_right) = post_order_dfs_for_plan f cfg e3 in
      (Log lop e2_can e3_can, (MAP_plan_to_path left plan_left) ++ (MAP_plan_to_path right plan_right))
    ) ∧
  post_order_dfs_for_plan f cfg (If e1 e2 e3) = (
    let (e1_can, plan_left) = post_order_dfs_for_plan f cfg e1;
        (e2_can, plan_center) = post_order_dfs_for_plan f cfg e2;
        (e3_can, plan_right) = post_order_dfs_for_plan f cfg e3 in
      (If e1_can e2_can e3_can,
       (MAP_plan_to_path left plan_left)
       ++
       (MAP_plan_to_path center plan_center)
       ++
       (MAP_plan_to_path right plan_right))
    ) ∧
  post_order_dfs_for_plan f cfg (Lannot e l) = (
    let (e_can, plan_center) = post_order_dfs_for_plan f cfg e in
      (Lannot e_can l, MAP_plan_to_path center plan_center)
    ) ∧
  post_order_dfs_for_plan f cfg (Tannot e t) = (
    let (e_can, plan_center) = post_order_dfs_for_plan f cfg e in
      (Tannot e_can t, MAP_plan_to_path center plan_center)
    ) ∧
  post_order_dfs_for_plan f cfg (Letrec ses e) = (
    let (e_can, plan_center) = post_order_dfs_for_plan f cfg e in
      (Letrec ses e_can, MAP_plan_to_path center plan_center)
    ) ∧
  post_order_dfs_for_plan f cfg (Mat e pes) = (
    let (e_can, plan_left) = post_order_dfs_for_plan f cfg e;
        individuals = MAP (λ (p, e'). (p,  post_order_dfs_for_plan f cfg e')) pes in
      let pes_can = MAP (λ(p, (e', _)). (p, e')) individuals;
          pes_plan = FLAT (MAPi (λ i (_, (_, plani)). MAP_plan_to_path (listIndex i) plani) individuals);
          e_plan = MAP_plan_to_path left plan_left in
        (Mat e_can pes_can, e_plan ++ pes_plan)
    ) ∧
  (* We do not apply any canonicalization plan to the rest *)
  post_order_dfs_for_plan f cfg e = (e, [])
Termination
  WF_REL_TAC ‘measure (λ (f, cfg, e). exp_size e)’ \\ fs[]
  \\ strip_tac
  >- (
  Induct_on ‘pes’ \\ fs[]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspecl_then [‘e’, ‘cfg’, ‘f’, ‘e_can’, ‘plan_left’, ‘p’, ‘e'’] strip_assume_tac)
  \\ pop_assum imp_res_tac \\ fs[astTheory.exp_size_def]
  )
  >- (
  strip_tac
  \\ Induct_on ‘exps’ \\ fs[]
  \\ rpt strip_tac \\ fs[astTheory.exp_size_def]
  >- (
    first_x_assum (qspecl_then [‘op’, ‘a’] strip_assume_tac)
    \\ pop_assum imp_res_tac \\ fs[]
    )
  \\ qpat_x_assum ‘∀ mod a. _ ⇒ exp_size a < _’ (qspecl_then [‘mod’, ‘a’] strip_assume_tac)
  \\ pop_assum imp_res_tac \\ fs[]
  )
End


Definition perform_rewrites_def:
  (* Make sure not to optimise away the FpOptimise or Let *)
  perform_rewrites (cfg: config) Here rewrites (FpOptimise sc e) = FpOptimise sc e ∧
  perform_rewrites (cfg: config) Here rewrites (Let so e1 e2) = Let so e1 e2 ∧

  (* Otherwise, we may optimise everything if we are at the end of the path *)
  perform_rewrites cfg Here rewrites e = (if (cfg.canOpt) then (rewriteFPexp rewrites e) else e) ∧

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
  optimise_with_plan cfg [] e = e ∧
  optimise_with_plan cfg ((path, rewrites)::rest) e = optimise_with_plan cfg rest (
    perform_rewrites (cfg with optimisations := rewrites) path rewrites e)
End


Definition optimise_linear_interpolation_def:
  optimise_linear_interpolation cfg e =
  post_order_dfs_for_plan (λ cfg e.
                             (* Does it match  *)
                             case (matchesFPexp (Binop FP_Add
                                                 (Binop FP_Mul
                                                  (Var 0)
                                                  (Binop FP_Sub
                                                   (Word (4607182418800017408w: word64))
                                                   (Var 1)))
                                                 (Binop FP_Mul
                                                  (Var 2)
                                                  (Var 1))) e []) of
                             | SOME _ =>
                                 let plan = [
                                     (ListIndex (0, Here), [fp_comm_gen FP_Mul;
                                                            fp_undistribute_gen FP_Mul FP_Sub;
                                                            fp_comm_gen FP_Mul;
                                                            fp_sub_add ]);
                                     (Here, [fp_assoc_gen FP_Add]);
                                     (ListIndex (1, Here), [fp_neg_push_mul_r]);
                                     (ListIndex (1, ListIndex (0, Here)), [fp_comm_gen FP_Mul]);
                                     (ListIndex (1, Here), [fp_distribute_gen FP_Mul FP_Add]);
                                     (ListIndex (1, (ListIndex (0, Here))), [fp_comm_gen FP_Add; fp_add_sub]);
                                     (ListIndex (0, Here), [fp_comm_gen FP_Mul; fp_times_one]);
                                     (ListIndex (1, Here), [fp_comm_gen FP_Mul])
                                   ] in
                                   SOME (optimise_with_plan cfg plan e, plan)
                             | NONE => NONE) cfg e
End

(*
Get all top-level multiplicants:
e.g. for ((x + 0) * (y * (a * 7))), this returns [x+0; y; a; 7].
This function requires the input to be canonicalized to right-associative.
*)
Definition top_level_multiplicants_def:
  top_level_multiplicants e = case e of
                              | App (FP_bop FP_Mul) [e1; App (FP_bop FP_Mul) [e1'; e2']] =>
                                  let vs = (top_level_multiplicants e2') in (e1::e1'::vs)
                              | App (FP_bop FP_Mul) [e1; e2] => [e1; e2]
                              | _ => [e]
End

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

Definition remove_first_def:
  remove_first [] a = [] ∧
  remove_first (x::rest) a = if (x = a) then rest else x::(remove_first rest a)
End

Definition intersect_lists_def:
  intersect_lists _ [] = [] ∧
  intersect_lists [] _ = [] ∧
  intersect_lists (a::rest) right =
  case MEM a right of T => a::(intersect_lists rest (remove_first right a))
                   | F => intersect_lists rest right
End

Definition move_multiplicants_to_right_def:
  move_multiplicants_to_right cfg [] e = (e, []) ∧
  move_multiplicants_to_right cfg [m] e =
  (case e of
   | (App (FP_bop FP_Mul) [e1; e2]) =>
       if (m = e1) then
         let plan =  [(Here, [fp_comm_gen FP_Mul])] in
           let commuted = optimise_with_plan cfg plan e in
             (commuted, plan)
       else (
         if (m = e2) then
           let local_plan = [(Here, [fp_assoc2_gen FP_Mul])] in
             (optimise_with_plan cfg local_plan e, local_plan)
         else
           let local_plan = [(Here, [fp_assoc2_gen FP_Mul])];
               (updated_e2, downstream_plan) = move_multiplicants_to_right cfg [m] e2 in
             let updated_e = App (FP_bop FP_Mul) [e1; updated_e2] in
               (optimise_with_plan cfg local_plan updated_e,
                (MAP_plan_to_path (listIndex 1) downstream_plan) ++ local_plan)
         )
   | _ => (e, [])) ∧
  move_multiplicants_to_right cfg (m1::m2::rest) e =
  let (updated_e, plan) = move_multiplicants_to_right cfg [m1] e in
    case updated_e of
    | (App (FP_bop FP_Mul) [e1; e2]) =>
        (let (updated_e1, other_plan) = move_multiplicants_to_right cfg (m2::rest) e1 in
           let left_plan = MAP_plan_to_path (listIndex 0) other_plan;
               local_plan = [(Here, [fp_assoc_gen FP_Mul]); (ListIndex (1, Here), [fp_comm_gen FP_Mul]) ] in
             let final_e = optimise_with_plan cfg local_plan (App (FP_bop FP_Mul) [updated_e1; e2]) in
               (final_e, plan ++ left_plan ++ local_plan))
    | _ => (updated_e, plan)
End


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

Definition canonicalize_for_distributivity_local_def:
  canonicalize_for_distributivity_local cfg e =
  case e of
  | App (FP_bop op) [e1; e2] =>
      if (op = FP_Add ∨ op = FP_Sub)
      then
        let multiplicants1 = top_level_multiplicants e1;
            multiplicants2 = top_level_multiplicants e2 in
          let common_multiplicants = intersect_lists multiplicants1 multiplicants2
          in
            let (e1_to_right, e1_plan) =
                move_multiplicants_to_right cfg common_multiplicants e1;
                (e2_to_right, e2_plan) =
                move_multiplicants_to_right cfg common_multiplicants e2
            in
              let updated_e = App (FP_bop op) [e1_to_right; e2_to_right];
                  plan = (MAP_plan_to_path (listIndex 0) e1_plan)
                         ++ (MAP_plan_to_path (listIndex 1) e2_plan) in
                SOME (updated_e, plan)
      else
        NONE
  | _ => NONE
End

Definition canonicalize_for_distributivity_def:
  canonicalize_for_distributivity cfg e =
  post_order_dfs_for_plan (λ cfg e.
                             case e of
                             | App (FP_bop op) [e1; e2] =>
                                 if (op = FP_Add ∨ op = FP_Sub)
                                 then
                                   let multiplicants1 = top_level_multiplicants e1;
                                       multiplicants2 = top_level_multiplicants e2 in
                                     let common_multiplicants = intersect_lists multiplicants1 multiplicants2
                                     in
                                       let (e1_to_right, e1_plan) =
                                           move_multiplicants_to_right cfg common_multiplicants e1;
                                           (e2_to_right, e2_plan) =
                                           move_multiplicants_to_right cfg common_multiplicants e2
                                       in
                                         let updated_e = App (FP_bop op) [e1_to_right; e2_to_right];
                                             plan = (MAP_plan_to_path (listIndex 0) e1_plan)
                                                    ++ (MAP_plan_to_path (listIndex 1) e2_plan) in
                                           SOME (updated_e, plan)
                                 else
                                   NONE
                             | _ => NONE) cfg e
End


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

Definition apply_distributivity_local_def:
  apply_distributivity_local cfg e =
  (let (can_e, can_plan) = canonicalize_for_distributivity cfg e in
     case can_e of
     | App (FP_bop op) [
         App (FP_bop op') [e1_1;e1_2];
         App (FP_bop op'') [e2_1;e2_2]] =>
         if ((op = FP_Add ∨ op = FP_Sub) ∧ op' = FP_Mul
             ∧ e1_2 = App (FP_bop op'') [e2_1;e2_2])
         then
           (let plan = [(ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen FP_Mul]);
                        (Here, [fp_distribute_gen op' op])] in
              let optimized = optimise_with_plan cfg plan can_e in
                SOME (optimized, can_plan ++ plan)
           )
         else (if ((op = FP_Add ∨ op = FP_Sub) ∧ (op' = FP_Mul ∨ op' = FP_Div) ∧ op'' = op')
               then
                 (let plan = [(Here, [fp_distribute_gen op' op])] in
                    let optimized = optimise_with_plan cfg plan can_e in
                      SOME (optimized, can_plan ++ plan)
                 )
               else NONE)
     | App (FP_bop op) [
         App (FP_bop op') [e1_1; e1_2];
         e2
       ] => if ((op = FP_Add ∨ op = FP_Sub) ∧ op' = FP_Mul ∧ e1_2 = e2)
            then
              (let plan = [(ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen op']);
                           (Here, [fp_distribute_gen op' op])] in
                 let optimized = optimise_with_plan cfg plan can_e in
                   SOME (optimized, can_plan ++ plan)
              )
            else NONE
     | _ => NONE)
End

Definition apply_distributivity_def:
  apply_distributivity cfg e =
  post_order_dfs_for_plan (λ cfg e.
                             case e of
                             | App (FP_bop FP_Add) [e1; App (FP_bop FP_Add) [e2_1; e2_2]] =>
                                 (let e1_new = App (FP_bop FP_Add) [e1; e2_1];
                                      e2_new = e2_2;
                                      pre_plan = [(Here, [fp_assoc2_gen FP_Add])] in
                                    (let (e1_can, e1_plan) = (canonicalize_for_distributivity cfg e1_new);
                                         (e2_can, e2_plan) = (canonicalize_for_distributivity cfg e2_new) in
                                       case (apply_distributivity_local cfg e1_can) of
                                       | SOME (e1_can_dist, e1_dist_plan) =>
                                           (case (apply_distributivity_local cfg e2_can) of
                                            | SOME (e2_can_dist, e2_dist_plan) =>
                                                (let e_here = App (FP_bop FP_Add) [e1_can_dist; e2_can_dist];
                                                     plan_here = pre_plan
                                                                 ++ (MAP_plan_to_path (listIndex 0) e1_plan)
                                                                 ++ (MAP_plan_to_path (listIndex 1) e2_plan)
                                                                 ++ (MAP_plan_to_path (listIndex 0) e1_dist_plan)
                                                                 ++ (MAP_plan_to_path (listIndex 1) e2_dist_plan) in
                                                   let (e_here_can, e_here_can_plan) = canonicalize_for_distributivity cfg e_here in
                                                     (case apply_distributivity_local cfg e_here of
                                                      | SOME (e_here_local, e_here_local_plan) =>
                                                          SOME (e_here_local, plan_here ++ e_here_can_plan ++ e_here_local_plan)
                                                      | NONE => SOME (e_here, plan_here)))
                                            | NONE => (let e_here = App (FP_bop FP_Add) [e1_can_dist; e2_can];
                                                           plan_here = pre_plan
                                                                       ++ (MAP_plan_to_path (listIndex 0) e1_plan)
                                                                       ++ (MAP_plan_to_path (listIndex 1) e2_plan)
                                                                       ++ (MAP_plan_to_path (listIndex 0) e1_dist_plan) in
                                                         let (e_here_can, e_here_can_plan) = canonicalize_for_distributivity cfg e_here in
                                                           (case apply_distributivity_local cfg e_here of
                                                            | SOME (e_here_local, e_here_local_plan) =>
                                                                SOME (e_here_local, plan_here ++ e_here_can_plan ++ e_here_local_plan)
                                                            | NONE => SOME (e_here, plan_here)))
                                           )
                                       | NONE => apply_distributivity_local cfg e
                                    ))
                             | _ => apply_distributivity_local cfg e
                          ) cfg e
End

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


Definition try_rewrite_with_each_def:
  try_rewrite_with_each [] e = (e, []) ∧
  try_rewrite_with_each ((left, right)::rest) e =
  case (matchesFPexp left e []) of
  | SOME _ =>
      (let rewritten = rewriteFPexp [(left, right)] e in
        let (rewritten_with_rest, rest_plan) = try_rewrite_with_each rest rewritten in
          (rewritten_with_rest, (Here, [(left, right)])::rest_plan))
  | NONE => try_rewrite_with_each rest e
End

Definition peephole_optimise_def:
  peephole_optimise cfg e =
  post_order_dfs_for_plan (λ (cfg: config) e.
                             let (rewritten, plan) = try_rewrite_with_each [
                                 fp_neg_push_mul_r;
                                 fp_times_minus_one_neg;
                                 fp_fma_intro;
                                 fp_add_sub;
                                 fp_times_two_to_add;
                                 fp_times_three_to_add;
                                 fp_times_zero;
                                 fp_plus_zero;
                                 fp_times_one;
                                 fp_same_sub;
                                 fp_same_div
                               ] e in
                               if (plan = []) then NONE else SOME (rewritten, plan)
                          ) cfg e
End

Definition compose_plan_generation_def:
  compose_plan_generation [] e = (λ cfg. (e, [])) ∧
  compose_plan_generation ((generator: config -> exp -> (exp # fp_plan))::rest) e =
  (λ cfg.
     let (updated_e, plan) = (generator cfg e) in
        let (final_e, rest_plan) = ((compose_plan_generation rest updated_e) cfg) in
        (final_e, plan ++ rest_plan)
  )
End


Definition balance_expression_tree_def:
  balance_expression_tree cfg e =
  post_order_dfs_for_plan (λ (cfg: config) e.
                             case e of
                             | (App (FP_bop op) [a; App (FP_bop op') [b; App (FP_bop op'') [c; d]]]) =>
                                 (if (op = op') ∧ (op' = op'') then
                                   (let plan = [(Here, [fp_assoc2_gen op])] in
                                      let optimized = optimise_with_plan cfg plan e in
                                        SOME (optimized, plan)
                                   )
                                 else
                                   NONE)
                             | _ => NONE
                          ) cfg e
End

Definition phase_repeater_def:
  phase_repeater 0 (generator: config -> exp -> (exp # fp_plan)) = generator ∧
  phase_repeater (SUC fuel) generator = (λ cfg e.
                                           let (e_upd, plan) = generator cfg e in
                                             if (e_upd ≠ e) then
                                               let (e_final, rest_plan) = (phase_repeater fuel generator) cfg e_upd in
                                                 (e_final, plan ++ rest_plan)
                                             else (e_upd, plan)
                                        )
End

(**
We generate the plan for a single expression. This will get more complicated than only canonicalization.
**)
Definition generate_plan_exp_def:
  generate_plan_exp (cfg: config) (e: exp) = SND (compose_plan_generation [
                                                     canonicalize;
                                                     (phase_repeater 100 apply_distributivity);
                                                     canonicalize;
                                                     optimise_linear_interpolation;
                                                     canonicalize;
                                                     peephole_optimise;
                                                     canonicalize;
                                                     balance_expression_tree
                                                   ] e cfg)
End

Definition generate_plan_exps_def:
  generate_plan_exps cfg [] = [] ∧
  generate_plan_exps cfg [Fun s e] = generate_plan_exps cfg [e] ∧
  generate_plan_exps cfg (e1::(e2::es)) = (generate_plan_exps cfg [e1]) ++ (generate_plan_exps cfg (e2::es)) ∧
  generate_plan_exps cfg [e] = generate_plan_exp cfg e
End

Definition generate_plan_decs_def:
  generate_plan_decs cfg [] = [] ∧
  generate_plan_decs cfg [Dlet loc p e] = [generate_plan_exps cfg [e]] ∧
  generate_plan_decs cfg (d1::(d2::ds)) = (generate_plan_decs cfg [d1]) ++ (generate_plan_decs cfg (d2::ds)) ∧
  generate_plan_decs cfg [d] = []
End

(**
  Step 2: Lifting of optimise to expression lists
  stos_pass walks over a list of expressions and calls optimise on
  function bodies
**)
Definition stos_pass_def:
  stos_pass cfg [] = [] ∧
  stos_pass cfg (e1::e2::es) =
    (stos_pass cfg [e1]) ++ (stos_pass cfg (e2::es))  ∧
  stos_pass cfg [Fun s e] =
    [Fun s (HD (stos_pass cfg [e]))] ∧
  stos_pass cfg [e] = [optimise cfg e]
End

Definition stos_pass_with_plans_def:
  stos_pass_with_plans cfg plans [] = [] ∧
  stos_pass_with_plans cfg (plan1::rest) (e1::e2::es) =
    (stos_pass_with_plans cfg [plan1] [e1]) ++ (stos_pass_with_plans cfg rest (e2::es)) ∧
  stos_pass_with_plans cfg plans [Fun s e] = [Fun s (HD (stos_pass_with_plans cfg plans [e]))] ∧
  stos_pass_with_plans cfg [plan] [e] = [optimise_with_plan cfg plan e] ∧
  stos_pass_with_plans _ _ exps = exps
End

(* Step 3: Disallow further optimisations *)
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
  WF_REL_TAC `measure (\ (c,e). exp_size e)` \\ fs[]
  \\ rpt conj_tac
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

Definition no_optimise_pass_def:
  no_optimise_pass cfg [] = [] ∧
  no_optimise_pass cfg (e1::e2::es) =
    (no_optimise_pass cfg [e1]) ++ (no_optimise_pass cfg (e2::es))  ∧
  no_optimise_pass cfg [Fun s e] =
    [Fun s (HD (no_optimise_pass cfg [e]))] ∧
  no_optimise_pass cfg [e] = [no_optimisations cfg e]
End

(**
  stos_pass_decs: Lift stos_pass to declarations
**)
Definition stos_pass_decs_def:
  stos_pass_decs cfg [] = [] ∧
  stos_pass_decs cfg (d1::d2::ds) =
    (stos_pass_decs cfg [d1] ++ stos_pass_decs cfg (d2::ds)) ∧
  stos_pass_decs cfg [Dlet loc p e] =
    [Dlet loc p (HD (stos_pass cfg [e]))] ∧
  (* No Dletrec support for now -- stos_pass_decs cfg [Dletrec ls exps] =
    [Dletrec ls (MAP (λ (fname, param, e). (fname, param, HD (stos_pass cfg [e]))) exps)] ∧ *)
  stos_pass_decs cfg [d] = [d]
End

Definition stos_pass_with_plans_decs_def:
  stos_pass_with_plans_decs cfg plans [] = [] ∧
  stos_pass_with_plans_decs cfg (plans1::rest) (d1::d2::ds) =
    (stos_pass_with_plans_decs cfg [plans1] [d1] ++ stos_pass_with_plans_decs cfg rest (d2::ds)) ∧
  stos_pass_with_plans_decs cfg [plans1] [Dlet loc p e] =
    [Dlet loc p (HD (stos_pass_with_plans cfg [plans1] [e]))] ∧
  stos_pass_with_plans_decs cfg plans [d] = [d]
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


val test_code =
(** REPLACE AST BELOW THIS LINE **)
“[Dlet unknown_loc (Pvar "out2")
(Fun "x1" (Fun "x2" (Fun "x3" 
(FpOptimise Opt
(App (FP_bop FP_Add)
  [
    (App (FP_bop FP_Add)
    [
      (App (FP_bop FP_Add)
      [
        (App (FP_bop FP_Add)
        [
          (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
            [
              (App (FP_bop FP_Mul)
              [
                Var (Short  "x3");
                Var (Short  "x3")
              ]);
              Var (Short  "x3")
            ]);
            Var (Short  "x3")
          ]);
          (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
            [
              Var (Short  "x3");
              Var (Short  "x3")
            ]);
            Var (Short  "x3")
          ])
        ]);
        (App (FP_bop FP_Mul)
        [
          Var (Short  "x3");
          Var (Short  "x3")
        ])
      ]);
      Var (Short  "x3")
    ]);
    (App FpFromWord [Lit (Word64 (4616189618054758400w:word64))])
  ])))))]”

Definition theAST_def:
  theAST =
  ^test_code
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    fp_comm_gen FP_Add;
    fp_fma_intro
  ]
End

Theorem theAST_plan = EVAL (Parse.Term ‘generate_plan_decs theOpts theAST’);

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (no_opt_decs theOpts (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST))’);


Theorem only_opt_body = EVAL (
  Parse.Term ‘
   compose_plan_generation [
       canonicalize;
      (* apply_distributivity; *)
     ] (
     (FpOptimise Opt
      (App (FP_bop FP_Add)
       [
         (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
             [
               (App (FP_bop FP_Mul)
                [
                  Var (Short  "x3");
                  Var (Short  "x3")
                ]);
               Var (Short  "x3")
             ]);
            Var (Short  "x3")
          ]);
         (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
             [
               Var (Short  "x3");
               Var (Short  "x3")
             ]);
            Var (Short  "x3")
          ])
       ])
     )
     ) theOpts’
  );

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

Theorem opt_linint_test_only_opt = EVAL (
  Parse.Term ‘
     (optimise_linear_interpolation theOpts linear_interpolation)
  ’);


Definition gather_constants_exp_def:
  gather_constants_exp (Lit (Word64 w)) = [w] ∧
  gather_constants_exp (FpOptimise sc e) = gather_constants_exp e ∧
  gather_constants_exp (Lit l) = [] ∧
  gather_constants_exp (Var x) = [] ∧
  gather_constants_exp (Raise e) = gather_constants_exp e ∧
  gather_constants_exp (Handle e pes) =
    (gather_constants_exp e) ++ (FLAT (MAP (λ (p,e). gather_constants_exp e) pes)) ∧
  gather_constants_exp (Con mod exps) =
    FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Fun s e) = gather_constants_exp e ∧
  gather_constants_exp (App op exps) = FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Log lop e2 e3) =
    (gather_constants_exp e2) ++ (gather_constants_exp e3) ∧
  gather_constants_exp (If e1 e2 e3) =
    (gather_constants_exp e1) ++ (gather_constants_exp e2) ++ (gather_constants_exp e3) ∧
  gather_constants_exp (Mat e pes) =
    (gather_constants_exp e) ++ FLAT ((MAP (λ (p,e). gather_constants_exp e) pes)) ∧
  gather_constants_exp (Let so e1 e2) =
    (gather_constants_exp e1) ++ (gather_constants_exp e2) ∧
  gather_constants_exp (Letrec ses e) =
    (gather_constants_exp e) ∧
  gather_constants_exp (Tannot e t) =
    (gather_constants_exp e) ∧
  gather_constants_exp (Lannot e l) =
    (gather_constants_exp e)
Termination
  WF_REL_TAC ‘measure (λ e. exp_size e)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.exp_size_def]
  \\ TRY (
    Induct_on `pes` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    Induct_on `exps` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def, astTheory.lit_size_def, char_size_def, astTheory.lop_size_def,
        fpValTreeTheory.fp_opt_size_def]
  \\ ‘∀ x l. MEM x l ⇒ exp_size x ≤ exp6_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.exp_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Definition gather_used_identifiers_pat_def:
  gather_used_identifiers_pat Pany = [] ∧
  gather_used_identifiers_pat (Pvar v) = [v] ∧
  gather_used_identifiers_pat (Plit _) = [] ∧
  gather_used_identifiers_pat (Pref p) = gather_used_identifiers_pat p ∧
  gather_used_identifiers_pat (Ptannot p _) = gather_used_identifiers_pat p ∧
  gather_used_identifiers_pat (Pcon (SOME id) pats) =
    (let used_in_pats = FLAT (MAP gather_used_identifiers_pat pats) in
      case id of | (Short v) => v::used_in_pats | (Long m (Short v)) => m::v::used_in_pats) ∧
  gather_used_identifiers_pat (Pcon NONE pats) = FLAT (MAP gather_used_identifiers_pat pats)
Termination
  WF_REL_TAC ‘measure (λ p. pat_size p)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.pat_size_def]
  \\ Induct_on ‘pats’ \\ rpt strip_tac \\ fs[astTheory.pat_size_def]
  \\ ‘∀ x l. MEM x l ⇒ pat_size x ≤ pat1_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.pat_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Definition gather_used_identifiers_exp_def:
  gather_used_identifiers_exp (FpOptimise sc e) = gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Lit l) = [] ∧
  gather_used_identifiers_exp (Var x) = (case x of
    | Short v => [v]
    | Long m (Short v) => [m; v]) ∧
  gather_used_identifiers_exp (Raise e) = gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Handle e pes) =
    (gather_used_identifiers_exp e)
    ++
    (FLAT (MAP (λ (p,e). (gather_used_identifiers_pat p) ++ (gather_used_identifiers_exp e)) pes)) ∧
  gather_used_identifiers_exp (Con mod exps) =
    FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Fun s e) = [s] ++ gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (App op exps) = FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Log lop e2 e3) =
    (gather_used_identifiers_exp e2) ++ (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (If e1 e2 e3) =
    (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) ++ (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (Mat e pes) =
    (gather_used_identifiers_exp e)
    ++
    FLAT ((MAP (λ (p,e). (gather_used_identifiers_pat p) ++ gather_used_identifiers_exp e) pes)) ∧
  gather_used_identifiers_exp (Let so e1 e2) =
    (let expression_identifiers =
         (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) in
       case so of
       | NONE => expression_identifiers
       | SOME n => n::expression_identifiers) ∧
  gather_used_identifiers_exp (Letrec ses e) =
    FLAT (MAP (λ (n, p, _). [n; p]) ses) ++ (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Tannot e t) =
    (gather_used_identifiers_exp e) ∧
  gather_used_identifiers_exp (Lannot e l) =
    (gather_used_identifiers_exp e)
Termination
  WF_REL_TAC ‘measure (λ e. exp_size e)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.exp_size_def]
  \\ TRY (
    Induct_on `pes` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    Induct_on `exps` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def, astTheory.lit_size_def, char_size_def, astTheory.lop_size_def,
        fpValTreeTheory.fp_opt_size_def]
  \\ ‘∀ x l. MEM x l ⇒ exp_size x ≤ exp6_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.exp_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End

Definition gather_constants_decs_def:
  gather_constants_decs (d1::d2::rest) = (gather_constants_decs [d1]) ++ (gather_constants_decs (d2::rest)) ∧
  gather_constants_decs [Dlet loc p e] = gather_constants_exp e ∧
  gather_constants_decs [Dletrec ls exps] = FLAT (MAP (λ (_, _, e). gather_constants_exp e) exps) ∧
  gather_constants_decs [] = []
End

Definition gather_used_identifiers_decs_def:
  gather_used_identifiers_decs (d1::d2::rest) = (gather_used_identifiers_decs [d1])
                                                ++ (gather_used_identifiers_decs (d2::rest)) ∧
  gather_used_identifiers_decs [Dlet loc p e] = gather_used_identifiers_exp e ∧
  gather_used_identifiers_decs [Dletrec ls exps] = FLAT (MAP (λ (_, _, e). gather_used_identifiers_exp e) exps) ∧
  gather_used_identifiers_decs [] = []
End

Definition generate_unique_name_def:
  generate_unique_name identifiers base = FIND (λ x. ~ MEM x identifiers)
                                               (GENLIST (λ i. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1))
End

Definition constants_to_variable_names_def:
  constants_to_variable_names identifiers [] (al: (word64 # string) list) = al ∧
  constants_to_variable_names identifiers ((c: word64)::rest) al =
  case ALOOKUP al c of NONE =>
                         (case generate_unique_name identifiers "const" of
                            | SOME name => constants_to_variable_names (name::identifiers) rest ((c, name)::al)
                            (* This will never happen *)
                            | NONE => constants_to_variable_names identifiers rest al)
                    | SOME name => constants_to_variable_names (name::identifiers) rest al
End

Definition replace_constants_exp_def:
  replace_constants_exp al (Lit (Word64 w)) =
    (case (ALOOKUP al w) of
    | NONE => Lit (Word64 w)
    | SOME v => (Var (Short v))) ∧
  replace_constants_exp al (FpOptimise sc e) = FpOptimise sc (replace_constants_exp al e) ∧
  replace_constants_exp al (Lit l) = (Lit l) ∧
  replace_constants_exp al (Var x) = (Var x) ∧
  replace_constants_exp al (Raise e) = Raise (replace_constants_exp al e) ∧
  replace_constants_exp al (Handle e pes) =
    Handle (replace_constants_exp al e)  (MAP (λ (p,e). (p, replace_constants_exp al e)) pes) ∧
  replace_constants_exp al (Con mod exps) =
    Con mod (MAP (replace_constants_exp al) exps) ∧
  replace_constants_exp al (Fun s e) = Fun s (replace_constants_exp al e) ∧
  replace_constants_exp al (App op exps) = App op (MAP (replace_constants_exp al) exps) ∧
  replace_constants_exp al (Log lop e2 e3) =
    Log lop (replace_constants_exp al e2) (replace_constants_exp al e3) ∧
  replace_constants_exp al (If e1 e2 e3) =
    If (replace_constants_exp al e1) (replace_constants_exp al e2) (replace_constants_exp al e3) ∧
  replace_constants_exp al (Mat e pes) =
    Mat (replace_constants_exp al e) ((MAP (λ (p,e). (p, replace_constants_exp al e)) pes)) ∧
  replace_constants_exp al (Let so e1 e2) =
    Let so (replace_constants_exp al e1) (replace_constants_exp al e2) ∧
  replace_constants_exp al (Letrec ses e) =
    Letrec ses (replace_constants_exp al e) ∧
  replace_constants_exp al (Tannot e t) =
    Tannot (replace_constants_exp al e) t ∧
  replace_constants_exp al (Lannot e l) =
    Lannot (replace_constants_exp al e) l
Termination
  WF_REL_TAC ‘measure (λ (al, e). exp_size e)’ \\ fs[]
  \\ rpt conj_tac
  \\ fs[astTheory.exp_size_def]
  \\ TRY (
    Induct_on `pes` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    Induct_on `exps` \\ fs[astTheory.exp_size_def]
    \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
    \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[] \\ NO_TAC
    )
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def, astTheory.lit_size_def, char_size_def, astTheory.lop_size_def,
        fpValTreeTheory.fp_opt_size_def]
  \\ ‘∀ x l. MEM x l ⇒ exp_size x ≤ exp6_size l’ by (
    rpt strip_tac
    \\ Induct_on ‘l’ \\ fs[]
    \\ rpt strip_tac
    \\ fs[astTheory.exp_size_def]
    )
  \\ pop_assum imp_res_tac \\ fs[]
End


Definition replace_constants_decs_def:
  replace_constants_decs al [] = [] ∧
  replace_constants_decs al (d1::d2::rest) = (replace_constants_decs al [d1])
                                             ++ (replace_constants_decs al (d2::rest)) ∧
  replace_constants_decs al [Dlet loc p e] = [Dlet loc p (replace_constants_exp al e)] ∧
  replace_constants_decs al [Dletrec ls exps] = [
      Dletrec ls (MAP (λ (x, y, e). (x, y, replace_constants_exp al e)) exps)
    ]
End

Definition create_fp_constants_decs_def:
  create_fp_constants_decs [] = [] ∧
  create_fp_constants_decs ((w, n)::rest) =
  let declaration = Dlet (Locs <|row := 0; col := 0; offset := 0|> <|row := 0; col := 0; offset := 0|>) (Pvar n) (Lit (Word64 w)) in
    declaration::(create_fp_constants_decs rest)
End

Definition lift_fp_constants_decs_def:
  lift_fp_constants decs =
    let identifiers = gather_used_identifiers_decs decs;
        constants = gather_constants_decs decs in
      let al = constants_to_variable_names identifiers constants [] in
        let replaced_decs = replace_constants_decs al decs in
        create_fp_constants_decs al ++ replaced_decs
End

Theorem theAST_lifted =
  EVAL
    (Parse.Term ‘
      lift_fp_constants (
        (no_opt_decs theOpts (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)))’);

(**
  Translation from floats to reals, needed for correctness proofs, thus we
  define it here
**)
Definition getRealCmp_def:
  getRealCmp (FP_Less) = Real_Less ∧
  getRealCmp (FP_LessEqual) = Real_LessEqual ∧
  getRealCmp (FP_Greater) = Real_Greater ∧
  getRealCmp (FP_GreaterEqual) = Real_GreaterEqual ∧
  getRealCmp (FP_Equal) = Real_Equal
End

Definition getRealUop_def:
  getRealUop (FP_Abs) = Real_Abs ∧
  getRealUop (FP_Neg) = Real_Neg ∧
  getRealUop (FP_Sqrt) = Real_Sqrt
End

Definition getRealBop_def:
  getRealBop (FP_Add) = Real_Add ∧
  getRealBop (FP_Sub) = Real_Sub ∧
  getRealBop (FP_Mul) = Real_Mul ∧
  getRealBop (FP_Div) = Real_Div
End

Definition realify_def:
  realify (Lit (Word64 w)) = Lit (Word64 w) (* RealFromFP added in App case *)∧
  realify (Lit l) = Lit l ∧
  realify (Var x) = Var x ∧
  realify (Raise e) = Raise (realify e) ∧
  realify (Handle e pes) =
    Handle (realify e) (MAP (\ (p,e). (p, realify e)) pes) ∧
  realify (Con mod exps) = Con mod (MAP realify exps) ∧
  realify (Fun s e) = Fun s (realify e) ∧
  realify (App op exps) =
    (let exps_real = MAP realify exps in
     case op of
     | FpFromWord => App  RealFromFP exps_real
     | FP_cmp cmp => App (Real_cmp (getRealCmp cmp)) exps_real
     | FP_uop uop => App (Real_uop (getRealUop uop)) exps_real
     | FP_bop bop => App (Real_bop (getRealBop bop)) exps_real
     | FP_top _ =>
     (case exps of
      | [e1; e2; e3] => App (Real_bop (Real_Add)) [
                          App (Real_bop (Real_Mul)) [realify e2; realify e3]; realify e1]
      | _ => App op exps_real) (* malformed expression, return garbled output *)
     | _ => App op exps_real) ∧
  realify (Log lop e2 e3) =
    Log lop (realify e2) (realify e3) ∧
  realify (If e1 e2 e3) =
    If (realify e1) (realify e2) (realify e3) ∧
  realify (Mat e pes) =
    Mat (realify e) (MAP (λ(p,e). (p, realify e)) pes) ∧
  realify (Let so e1 e2) =
    Let so (realify e1) (realify e2) ∧
  realify (Letrec ses e) =
    Letrec (MAP (λ (s1,s2,e). (s1, s2, realify e)) ses) (realify e) ∧
  realify (Tannot e t) = Tannot (realify e) t ∧
  realify (Lannot e l) = Lannot (realify e) l ∧
  realify (FpOptimise sc e) = FpOptimise sc (realify e)
Termination
  wf_rel_tac ‘measure exp_size’ \\ fs[astTheory.exp_size_def] \\ rpt conj_tac
  >- (Induct_on `ses` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

val _ = export_theory();
