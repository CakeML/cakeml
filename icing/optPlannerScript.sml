(**
  Unverified optimisation planner.
  Definitions in this file correspond to the function ‘planOpts’
  from Section 5 of the PrincessCake paper.
**)
open semanticPrimitivesTheory evaluateTheory icing_rewriterTheory
     icing_optimisationsTheory fpOptTheory fpValTreeTheory
     source_to_source2Theory;

open preamble;

val _ = new_theory "optPlanner";

(* Canonicalize sub to add and mul times -1.0
 TODO: Consider dropping the multiplication with -1.0 *)
Definition canonicalize_sub_def:
  canonicalize_sub e =
    case e of
    | (App (FP_bop FP_Sub) [e1; e2]) =>
        (App (FP_bop FP_Add) [e1; rewriteFPexp [fp_neg_times_minus_one] (App (FP_uop FP_Neg) [e2])],
         [Apply (Here, [fp_sub_add]);
          Apply (ListIndex (1, Here),  [fp_neg_times_minus_one])])
    | _ => (e, [])
End

(** Changes:
    17/06/21: Disabled canonicalize_sub
 **)
Definition canonicalize_app_def:
  canonicalize_app e =
    case e of
    (* Canonicalize to right associative *)
    | (App (FP_bop op) [App (FP_bop op2) [e1_1; e1_2]; e2]) =>
        (if (op = op2 ∧ op ≠ FP_Sub ∧ op ≠ FP_Div) then
           let (local_rewritten, local_plan) =
               (App (FP_bop op) [e1_1; App (FP_bop op2) [e1_2; e2]],
                [Apply (Here, [fp_assoc_gen op])]) in
           case local_rewritten of
           | App (FP_bop op) [e1'; e2'] =>
               (let (child_rewritten, child_plan) = canonicalize_app e2' in
                  (App (FP_bop op) [e1'; child_rewritten],
                   local_plan ++ (MAP_plan_to_path (listIndex 1) child_plan)))
           | _ => (local_rewritten, local_plan)
         else (e,[])) (* (canonicalize_sub e))*)
    (* Canonicalize constants to the rhs *)
    | (App (FP_bop op) [App FpFromWord [l]; e2]) =>
        (if (op ≠ FP_Sub ∧ op ≠ FP_Div ∧ (App FpFromWord [l] ≠ e2)) then
           (rewriteFPexp [fp_comm_gen op] e, [Apply (Here, [fp_comm_gen op])])
         else (e, []))
    | (App (FP_bop FP_Sub) [e1; e2]) =>
        canonicalize_sub e
    | _ => (e, [])
Termination
  wf_rel_tac ‘measure (λe. exp_size e)’ \\ fs[]
  \\ rpt strip_tac
  \\ fs[astTheory.exp_size_def]
  \\ fs[astTheory.op_size_def, fpValTreeTheory.fp_bop_size_def]
End

Definition canonicalize_def:
  canonicalize (cfg: config) (FpOptimise sc e) = (
  let (e_can, plan: fp_plan) =
      canonicalize (cfg with canOpt := if sc = Opt then T else F) e
  in
    (FpOptimise sc e_can, MAP_plan_to_path center plan)) ∧
  canonicalize cfg (App op exps) = (
    let individuals = MAP (canonicalize cfg) exps in
      let exps_can = MAP FST individuals;
          plan: fp_plan =
                FLAT (MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani)
                      individuals)
      in
        if (cfg.canOpt) then
          let (new_e, can_plan) = canonicalize_app (App op exps_can) in
            (new_e, plan ++ can_plan)
        else (App op exps_can, plan)
    ) ∧
  canonicalize cfg (Let so e1 e2) = (
    let (e1_can, plan_left) = canonicalize cfg e1;
        (e2_can, plan_right) = canonicalize cfg e2 in
      (Let so e1_can e2_can, (MAP_plan_to_path left plan_left) ++
                             (MAP_plan_to_path right plan_right))) ∧
  canonicalize cfg (Con mod exps) = (
    let individuals =
        MAP (canonicalize cfg) exps;
        exps_can = MAP FST individuals;
        plan = FLAT
               (MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals)
    in
      (Con mod exps_can, plan)) ∧
  canonicalize cfg (Log lop e2 e3) = (
    let (e2_can, plan_left) = canonicalize cfg e2;
        (e3_can, plan_right) = canonicalize cfg e3 in
      (Log lop e2_can e3_can, (MAP_plan_to_path left plan_left) ++
                              (MAP_plan_to_path right plan_right))) ∧
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
        individuals = MAP (λ (p, e'). (p, canonicalize cfg e')) pes;
        pes_can = MAP (λ(p, (e', _)). (p, e')) individuals;
        pes_plan = FLAT
                   (MAPi (λ i (_, (_, plani)).
                           MAP_plan_to_path (listIndex i) plani) individuals);
        e_plan = MAP_plan_to_path left plan_left in
      (Mat e_can pes_can, e_plan ++ pes_plan)) ∧
  (* We do not apply any canonicalization plan to the rest *)
  canonicalize cfg e = (e, [])
Termination
  wf_rel_tac ‘measure (λ (cfg, e). exp_size e)’
End

Definition post_order_dfs_for_plan_def:
  post_order_dfs_for_plan (f: config -> exp -> (exp # fp_plan) option) (cfg: config) (FpOptimise sc e) = (
  let (e_can, plan: fp_plan) = post_order_dfs_for_plan f (cfg with canOpt := if sc = Opt then T else F) e in
    ((FpOptimise sc e_can), MAP_plan_to_path center plan)
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
    let individuals =
        MAP (post_order_dfs_for_plan f cfg) exps;
        exps_can = MAP FST individuals;
        plan = FLAT (MAPi (λ i (_, plani). MAP_plan_to_path (listIndex i) plani) individuals ) in
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
  wf_rel_tac ‘measure (λ (f, cfg, e). exp_size e)’
End

Definition optimise_linear_interpolation_def:
  optimise_linear_interpolation cfg e =
  post_order_dfs_for_plan
    (λ cfg e.
      (* Does it match  *)
      case (matchesFPexp (Binop FP_Add
                          (Binop FP_Mul
                           (PatVar 0)
                           (Binop FP_Sub
                            (Word (4607182418800017408w: word64))
                            (PatVar 1)))
                          (Binop FP_Mul
                           (PatVar 2)
                           (PatVar 1))) e []) of
      | SOME _ =>
          let plan = [
              Label "Linear Interpolation";
              Apply (ListIndex (0, Here), [fp_comm_gen FP_Mul;
                                     fp_undistribute_gen FP_Mul FP_Sub;
                                     fp_comm_gen FP_Mul;
                                     fp_sub_add ]);
              Apply (Here, [fp_assoc_gen FP_Add]);
              Apply (ListIndex (1, Here), [fp_neg_push_mul_r]);
              Apply (ListIndex (1, ListIndex (0, Here)), [fp_comm_gen FP_Mul]);
              Apply (ListIndex (1, Here), [fp_distribute_gen FP_Mul FP_Add]);
              Apply (ListIndex (1, (ListIndex (0, Here))), [fp_comm_gen FP_Add; fp_add_sub]);
              Apply (ListIndex (0, Here), [fp_comm_gen FP_Mul; fp_times_one]);
              Apply (ListIndex (1, Here), [fp_comm_gen FP_Mul]);
              Label "Linear Interpolation End"
            ];
            expected = FST (optimise_with_plan cfg plan e)
          in
            SOME (expected, plan ++ [Expected expected])
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

Definition remove_first_def:
  remove_first [] a = [] ∧
  remove_first (x::rest) a = if (x = a) then rest else x::(remove_first rest a)
End

Definition intersect_lists_def:
  intersect_lists _ [] = [] ∧
  intersect_lists [] _ = [] ∧
  intersect_lists (a::rest) right =
    if MEM a right then
      a::(intersect_lists rest (remove_first right a))
    else intersect_lists rest right
End

Definition move_multiplicants_to_right_def:
  move_multiplicants_to_right cfg [] e = (e, []) ∧
  move_multiplicants_to_right cfg [m] e =
  (case e of
   | (App (FP_bop FP_Mul) [e1; e2]) =>
       if (m = e1) then
         let plan = [Apply (Here, [fp_comm_gen FP_Mul])];
         res_plan = optimise_with_plan cfg plan e in
           if SND res_plan = Success then
             (FST res_plan, plan)
           else (e, [])
       else (
         let local_plan = [Apply (Here, [fp_assoc2_gen FP_Mul])] in
           if (m = e2 ∧ SND(optimise_with_plan cfg local_plan e) = Success) then
             (FST (optimise_with_plan cfg local_plan e), local_plan)
           else
           let (updated_e2, downstream_plan) = move_multiplicants_to_right cfg [m] e2;
               updated_e = App (FP_bop FP_Mul) [e1; updated_e2];
               update_opt = optimise_with_plan cfg local_plan updated_e in
               if SND update_opt = Success then
               (FST update_opt,
                (MAP_plan_to_path (listIndex 1) downstream_plan) ++ local_plan)
               else
                 (updated_e, MAP_plan_to_path (listIndex 1) downstream_plan)
         )
   | _ => (e, [])) ∧
  move_multiplicants_to_right cfg (m1::m2::rest) e =
  let (updated_e, plan) = move_multiplicants_to_right cfg [m1] e in
    case updated_e of
    | (App (FP_bop FP_Mul) [e1; e2]) =>
        (let (updated_e1, other_plan) = move_multiplicants_to_right cfg (m2::rest) e1;
             left_plan = MAP_plan_to_path (listIndex 0) other_plan;
             local_plan = [Apply (Here, [fp_assoc_gen FP_Mul]);
                           Apply (ListIndex (1, Here), [fp_comm_gen FP_Mul]) ];
             new_e = App (FP_bop FP_Mul) [updated_e1; e2];
             final_e = optimise_with_plan cfg local_plan new_e;
         in
           if SND final_e = Success
           then (FST final_e, plan ++ left_plan ++ local_plan)
           else (new_e, plan ++ left_plan))
    | _ => (updated_e, plan)
End

Definition canonicalize_for_distributivity_local_def:
  canonicalize_for_distributivity_local cfg e =
  case e of
  | App (FP_bop op) [e1; e2] =>
      if (op = FP_Add ∨ op = FP_Sub)
      then
        let multiplicants1 = top_level_multiplicants e1;
            multiplicants2 = top_level_multiplicants e2;
            common_multiplicants = intersect_lists multiplicants1 multiplicants2;
            (e1_to_right, e1_plan) =
              move_multiplicants_to_right cfg common_multiplicants e1;
            (e2_to_right, e2_plan) =
              move_multiplicants_to_right cfg common_multiplicants e2;
            updated_e = App (FP_bop op) [e1_to_right; e2_to_right];
            plan = (MAP_plan_to_path (listIndex 0) e1_plan)
                   ++ (MAP_plan_to_path (listIndex 1) e2_plan) in
          SOME (updated_e, plan)
      else
        NONE
  | _ => NONE
End

(** Move all multiplicants into the same position to make distributivity easier
    to apply
    Replaces e.g. (x * y) + (z * x) -> (y * x) + (z * x)
 **)
Definition canonicalize_for_distributivity_def:
  canonicalize_for_distributivity cfg e =
  post_order_dfs_for_plan
    (λ cfg e.
      case e of
      | App (FP_bop op) [e1; e2] =>
          if (op = FP_Add ∨ op = FP_Sub)
          then
            let multiplicants1 = top_level_multiplicants e1;
                multiplicants2 = top_level_multiplicants e2;
                common_multiplicants = intersect_lists multiplicants1 multiplicants2;
                (e1_to_right, e1_plan) =
                  move_multiplicants_to_right cfg common_multiplicants e1;
                (e2_to_right, e2_plan) =
                  move_multiplicants_to_right cfg common_multiplicants e2;
                updated_e = App (FP_bop op) [e1_to_right; e2_to_right];
                plan = (MAP_plan_to_path (listIndex 0) e1_plan)
                       ++ (MAP_plan_to_path (listIndex 1) e2_plan) in
              SOME (updated_e, plan)
          else
            NONE
      | _ => NONE) cfg e
End

Definition isVar_def:
  isVar ((Var _):ast$exp) = T ∧
  isVar _ = F
End

(** Locally apply one distributivity optimization **)
(** Changes: 04/06/2021: Disabled corner case checks **)
Definition apply_distributivity_local_def:
  apply_distributivity_local cfg e =
  (let (can_e, can_plan) = canonicalize_for_distributivity cfg e in
     case can_e of
     | App (FP_bop op) [
         App (FP_bop op') [e1_1;e1_2];
         App (FP_bop op'') [e2_1;e2_2]] =>
         (** Simple case: (e11 op' e12) op (e21 op' e12) and op in {*,/}, op' in {+,-} **)
         if ((op = FP_Add ∨ op = FP_Sub) ∧ (op' = FP_Mul ∨ op' = FP_Div) ∧
              op'' = op' ∧ e1_2 = e2_2)
         then
           (let plan = [Apply (Here, [fp_distribute_gen op' op])];
                optimized = optimise_with_plan cfg plan can_e in
              SOME (optimized, can_plan ++ plan))
         else NONE
     | _ => NONE)
End

(** Old version with corner cases
Definition apply_distributivity_local_def:
  apply_distributivity_local cfg e =
  (let (can_e, can_plan) = canonicalize_for_distributivity cfg e in
     case can_e of
     | App (FP_bop op) [
         App (FP_bop op') [e1_1;e1_2];
         App (FP_bop op'') [e2_1;e2_2]] =>
         if (e1_2 = e2_2) then (* Check that we can distribute correctly *)
           if ((op = FP_Add ∨ op = FP_Sub) ∧ op' = FP_Mul
               ∧ e1_2 = App (FP_bop op'') [e2_1;e2_2])
           then
             (let plan = [Apply (ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen FP_Mul]);
                          Apply (Here, [fp_distribute_gen op' op])];
                  optimized = optimise_with_plan cfg plan can_e in
                SOME (optimized, can_plan ++ plan))
           else if ((op = FP_Add ∨ op = FP_Sub) ∧ (op' = FP_Mul ∨ op' = FP_Div) ∧ op'' = op')
           then
             (let plan = [Apply (Here, [fp_distribute_gen op' op])];
                  optimized = optimise_with_plan cfg plan can_e in
                SOME (optimized, can_plan ++ plan))
           else NONE
         else NONE
     | App (FP_bop op) [
         App (FP_bop op') [e1_1; e1_2];
         e2] =>
         if ((op = FP_Add ∨ op = FP_Sub) ∧ op' = FP_Mul ∧ e1_2 = e2 ∧ ~isVar(e2))
            then
              (let plan = [Apply (ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen op']);
                           Apply (Here, [fp_distribute_gen op' op])];
                   optimized = optimise_with_plan cfg plan can_e in
                 SOME (optimized, can_plan ++ plan))
            else NONE
     | _ => NONE)
End **)

(** Exploit distributivity of * over + and - to reduce the total number
    of operations.
    Replaces (x * y) {+,-} (x * z) with x * (y {+,-} z)
 **)
Definition apply_distributivity_def:
  apply_distributivity cfg e =
  post_order_dfs_for_plan
    (λ cfg e.
      case e of
      (* e = e1 + (e2_1 + e2_2) *)
      | App (FP_bop FP_Add) [e1; App (FP_bop FP_Add) [e2_1; e2_2]] =>
          (* Reassociate into e = (e1 + e2_1) + e2_2 *)
          (let e1_new = App (FP_bop FP_Add) [e1; e2_1];
               e2_new = e2_2;
               pre_plan = [Apply (Here, [fp_assoc2_gen FP_Add])];
               (e1_can, e1_plan) = (canonicalize_for_distributivity cfg e1_new);
               (e2_can, e2_plan) = (canonicalize_for_distributivity cfg e2_new) in
             case (apply_distributivity_local cfg e1_can) of
             | SOME ((e1_can_dist, _), e1_dist_plan) =>
                 (case (apply_distributivity_local cfg e2_can) of
                  | SOME ((e2_can_dist, _), e2_dist_plan) =>
                      (let e_here = App (FP_bop FP_Add) [e1_can_dist; e2_can_dist];
                           plan_here = pre_plan
                                       ++ (MAP_plan_to_path (listIndex 0) e1_plan)
                                       ++ (MAP_plan_to_path (listIndex 1) e2_plan)
                                       ++ (MAP_plan_to_path (listIndex 0) e1_dist_plan)
                                       ++ (MAP_plan_to_path (listIndex 1) e2_dist_plan);
                           (e_here_can, e_here_can_plan) =
                             canonicalize_for_distributivity cfg e_here in
                         (case apply_distributivity_local cfg e_here of
                          | SOME ((e_here_local, _), e_here_local_plan) =>
                              SOME (e_here_local, plan_here ++ e_here_can_plan ++ e_here_local_plan)
                          | NONE => SOME (e_here, plan_here)))
                  | NONE =>
                      (let e_here = App (FP_bop FP_Add) [e1_can_dist; e2_can];
                           plan_here = pre_plan
                                       ++ (MAP_plan_to_path (listIndex 0) e1_plan)
                                       ++ (MAP_plan_to_path (listIndex 1) e2_plan)
                                       ++ (MAP_plan_to_path (listIndex 0) e1_dist_plan);
                           (e_here_can, e_here_can_plan) = canonicalize_for_distributivity cfg e_here in
                         (case apply_distributivity_local cfg e_here of
                          | SOME ((e_here_local, _), e_here_local_plan) =>
                              SOME (e_here_local, plan_here ++ e_here_can_plan ++ e_here_local_plan)
                          | NONE => SOME (e_here, plan_here))))
             | NONE => case apply_distributivity_local cfg e of
                       |SOME ((e_opt, _), plan) => SOME (e_opt, plan)
                       | NONE => NONE)
      | _ =>case apply_distributivity_local cfg e of
                       |SOME ((e_opt, _), plan) => SOME (e_opt, plan)
                       | NONE => NONE) cfg e
End

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
  post_order_dfs_for_plan
    (λ (cfg: config) e.
      let (rewritten, plan) =
          try_rewrite_with_each [
              fp_neg_push_mul_r;
              fp_times_minus_one_neg;
              fp_fma_intro;
              fp_add_sub;
              fp_times_two_to_add;
              fp_times_three_to_add;
              fp_times_zero;
              fp_plus_zero;
              fp_times_one;
              fp_same_sub
            ] e
      in
        if (plan = []) then NONE else SOME (rewritten, MAP (λ x. Apply x) plan)) cfg e
End

Definition compose_plan_generation_def:
  compose_plan_generation ([]:((config -> exp -> (exp # fp_plan)) # string) list) e cfg =
  (e, []) ∧
  compose_plan_generation ((generator, name)::rest) e cfg =
     let (updated_e, plan) = (generator cfg e);
         (final_e, rest_plan) = compose_plan_generation rest updated_e cfg
     in
       if (updated_e = e)
       then if (final_e = e)
            then (e, [])
            else (final_e, rest_plan)
       else
        (final_e, (Label name) :: plan ++ [Expected updated_e; Label (STRCAT name " end")] ++ rest_plan)
End

Definition balance_expression_tree_def:
  balance_expression_tree cfg e =
  post_order_dfs_for_plan
    (λ (cfg: config) e.
      case e of
      | (App (FP_bop op) [a; App (FP_bop op') [b; App (FP_bop op'') [c; d]]]) =>
          (if (op = op') ∧ (op' = op'') ∧ (op = FP_Add ∨ op = FP_Mul) then
             (let plan = [Apply (Here, [fp_assoc2_gen op])];
                  optimized = FST (optimise_with_plan cfg plan e) in
                SOME (optimized, plan))
           else NONE)
      | _ => NONE) cfg e
End

Definition phase_repeater_def:
  phase_repeater 0 (generator: config -> exp -> (exp # fp_plan)) = generator ∧
  phase_repeater (SUC fuel) generator =
    (λ cfg e.
      let (e_upd, plan) = generator cfg e in
        if (e_upd ≠ e) then
          let (e_final, rest_plan) = (phase_repeater fuel generator) cfg e_upd in
            (e_final, plan ++ rest_plan)
        else (e, []))
End

(**
We generate the plan for a single expression. This will get more complicated
than only canonicalization.
**)
Definition generate_plan_exp_def:
  generate_plan_exp (cfg: config) (e: exp) =
    SND (compose_plan_generation [
            (canonicalize, "Canonical Form");
            ((phase_repeater 100 apply_distributivity), "Distributivity");
            (canonicalize, "Canonical Form");
            (* (optimise_linear_interpolation, "Linear Interpolation"); *)
            (canonicalize, "Canonical Form");
            (peephole_optimise, "Peephole Optimisations");
            (* (canonicalize, "Canonical Form");*)
            (balance_expression_tree, "Balance Trees");
            (* (peephole_optimise, "Peephole to undo bad decisions")*)
          ] e cfg)
End

Definition generate_plan_exp_top_def:
  generate_plan_exp_top cfg (Fun s e) = generate_plan_exp_top cfg e ∧
  generate_plan_exp_top cfg e = generate_plan_exp cfg e
End

Definition generate_plan_decs_def:
  generate_plan_decs cfg [] = [] ∧
  generate_plan_decs cfg [Dlet loc p e] = [generate_plan_exp_top cfg e] ∧
  generate_plan_decs cfg (d1::(d2::ds)) = (generate_plan_decs cfg [d1]) ++ (generate_plan_decs cfg (d2::ds)) ∧
  generate_plan_decs cfg [d] = []
End

Definition fpNum_def:
  fpNum [Lit _] = 0 ∧
  fpNum [Var _] = 0:num ∧
  fpNum [App op es] =
  (case op of
  |FP_uop _ => 1 + fpNum es
  |FP_bop _ => 2 + fpNum es
  |FP_top _ => 3 + fpNum es
  | _ => fpNum es)
  ∧
  fpNum [FpOptimise _ e] = fpNum [e] ∧
  fpNum [Letrec funs e] = fpNum [e] ∧
  fpNum [Let x e1 e2] = fpNum [e1] + fpNum [e2] ∧
  fpNum [Mat e pes] = fpNum [e] + fpNum (MAP SND pes) ∧
  fpNum [If e1 e2 e3] = fpNum [e1] + fpNum [e2] + fpNum [e3] ∧
  fpNum [Log _ e1 e2] = fpNum [e1] + fpNum [e2] ∧
  fpNum [Con cn es] = fpNum es ∧
  fpNum [Handle e pes] = fpNum [e] + fpNum (MAP SND pes) ∧
  fpNum [Raise e] = fpNum [e] ∧
  fpNum [Fun p e] = fpNum [e] ∧
  fpNum (e1::(e2::es)) = fpNum [e1] + fpNum (e2::es) ∧
  fpNum [] = 0
Termination
  wf_rel_tac ‘measure exp6_size’ >> gs[]
  >> Induct_on ‘pes’ >> gs[astTheory.exp_size_def]
  >> rpt strip_tac >> irule LESS_TRANS
  >> qexists_tac ‘exp3_size pes + (exp_size e) + 2 + (exp_size (SND h) + 1)’
  >> gs[]
  >> Cases_on ‘h’ >> gs[astTheory.exp_size_def]
End

Definition fpNum_decs_def:
  fpNum_decs [] = 0:num ∧
  fpNum_decs [Dlet loc p e] = fpNum [e] ∧
  fpNum_decs (d1::(d2::ds)) = fpNum_decs [d1] + fpNum_decs (d2::ds) ∧
  fpNum_decs _ = 0
End

val _ = export_theory();
