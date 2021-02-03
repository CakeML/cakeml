(**
  Unverified optimisation planners
**)
open semanticPrimitivesTheory evaluateTheory terminationTheory
     icing_rewriterTheory icing_optimisationsTheory fpOptTheory fpValTreeTheory
     source_to_sourceTheory;

open preamble;

val _ = new_theory "optPlanner";

Definition gather_constants_exp_def:
  gather_constants_exp (Lit (Word64 w)) = [w] ∧
  gather_constants_exp (FpOptimise sc e) = gather_constants_exp e ∧
  gather_constants_exp (Lit l) = [] ∧
  gather_constants_exp (Var x) = [] ∧
  gather_constants_exp (Raise e) = gather_constants_exp e ∧
  gather_constants_exp (Handle e pes) =
    (gather_constants_exp e) ++
    (FLAT (MAP (λ (p,e). gather_constants_exp e) pes)) ∧
  gather_constants_exp (Con mod exps) =
    FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Fun s e) = gather_constants_exp e ∧
  gather_constants_exp (App op exps) = FLAT (MAP gather_constants_exp exps) ∧
  gather_constants_exp (Log lop e2 e3) =
    (gather_constants_exp e2) ++ (gather_constants_exp e3) ∧
  gather_constants_exp (If e1 e2 e3) =
    (gather_constants_exp e1) ++ (gather_constants_exp e2) ++
    (gather_constants_exp e3) ∧
  gather_constants_exp (Mat e pes) =
    (gather_constants_exp e) ++
    FLAT ((MAP (λ (p,e). gather_constants_exp e) pes)) ∧
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
       case id of
       | (Short v) => v::used_in_pats
       | (Long m (Short v)) => m::v::used_in_pats) ∧
  gather_used_identifiers_pat (Pcon NONE pats) =
    FLAT (MAP gather_used_identifiers_pat pats)
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
  gather_used_identifiers_exp (FpOptimise sc e) =
    gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Lit l) = [] ∧
  gather_used_identifiers_exp (Var x) =
    (case x of
     | Short v => [v]
     | Long m (Short v) => [m; v]) ∧
  gather_used_identifiers_exp (Raise e) = gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (Handle e pes) =
    (gather_used_identifiers_exp e) ++
    (FLAT (MAP (λ (p,e). (gather_used_identifiers_pat p) ++
                         (gather_used_identifiers_exp e)) pes)) ∧
  gather_used_identifiers_exp (Con mod exps) =
    FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Fun s e) = [s] ++ gather_used_identifiers_exp e ∧
  gather_used_identifiers_exp (App op exps) =
    FLAT (MAP gather_used_identifiers_exp exps) ∧
  gather_used_identifiers_exp (Log lop e2 e3) =
    (gather_used_identifiers_exp e2) ++ (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (If e1 e2 e3) =
    (gather_used_identifiers_exp e1) ++ (gather_used_identifiers_exp e2) ++
    (gather_used_identifiers_exp e3) ∧
  gather_used_identifiers_exp (Mat e pes) =
    (gather_used_identifiers_exp e) ++
    FLAT ((MAP (λ (p,e). (gather_used_identifiers_pat p) ++
                         gather_used_identifiers_exp e) pes)) ∧
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
  gather_constants_decs (d1::d2::rest) =
    (gather_constants_decs [d1]) ++ (gather_constants_decs (d2::rest)) ∧
  gather_constants_decs [Dlet loc p e] = gather_constants_exp e ∧
  gather_constants_decs [Dletrec ls exps] =
    FLAT (MAP (λ (_, _, e). gather_constants_exp e) exps) ∧
  gather_constants_decs [] = []
End

Definition gather_used_identifiers_decs_def:
  gather_used_identifiers_decs (d1::d2::rest) =
    (gather_used_identifiers_decs [d1]) ++
    (gather_used_identifiers_decs (d2::rest)) ∧
  gather_used_identifiers_decs [Dlet loc p e] = gather_used_identifiers_exp e ∧
  gather_used_identifiers_decs [Dletrec ls exps] =
    FLAT (MAP (λ (_, _, e). gather_used_identifiers_exp e) exps) ∧
  gather_used_identifiers_decs [] = []
End

Definition generate_unique_name_def:
  generate_unique_name identifiers base =
    FIND (λ x. ~ MEM x identifiers)
         (GENLIST (λ i. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1))
End

Definition constants_to_variable_names_def:
  constants_to_variable_names identifiers [] (al: (word64 # string) list) = al ∧
  constants_to_variable_names identifiers ((c: word64)::rest) al =
  case ALOOKUP al c of
    | NONE =>
        (case generate_unique_name identifiers "const" of
         | SOME name => constants_to_variable_names (name::identifiers) rest ((c, name)::al)
         (* This will never happen *)
         | NONE => constants_to_variable_names identifiers rest al)
    | SOME name => constants_to_variable_names (name::identifiers) rest al
End

(**
  Walk over an AST and replace constants by variables that globally allocate
  their value
**)
Definition replace_constants_exp_def:
  replace_constants_exp al (Lit (Word64 w)) =
    (case (ALOOKUP al w) of
    | NONE => Lit (Word64 w)
    | SOME v => (Var (Short v))) ∧
  replace_constants_exp al (FpOptimise sc e) =
    FpOptimise sc (replace_constants_exp al e) ∧
  replace_constants_exp al (Lit l) = (Lit l) ∧
  replace_constants_exp al (Var x) = (Var x) ∧
  replace_constants_exp al (Raise e) = Raise (replace_constants_exp al e) ∧
  replace_constants_exp al (Handle e pes) =
    Handle (replace_constants_exp al e)
           (MAP (λ (p,e). (p, replace_constants_exp al e)) pes) ∧
  replace_constants_exp al (Con mod exps) =
    Con mod (MAP (replace_constants_exp al) exps) ∧
  replace_constants_exp al (Fun s e) = Fun s (replace_constants_exp al e) ∧
  replace_constants_exp al (App op exps) =
    App op (MAP (replace_constants_exp al) exps) ∧
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

(**
  Walk over a list of declarations and replace constants by a variable
**)
Definition replace_constants_decs_def:
  replace_constants_decs al [] = [] ∧
  replace_constants_decs al (d1::d2::rest) =
    (replace_constants_decs al [d1]) ++ (replace_constants_decs al (d2::rest)) ∧
  replace_constants_decs al [Dlet loc p e] =
    [Dlet loc p (replace_constants_exp al e)] ∧
  replace_constants_decs al [Dletrec ls exps] =
    [Dletrec ls (MAP (λ (x, y, e). (x, y, replace_constants_exp al e)) exps)]
End

(**
  Given a list of constants, create declarations for them
**)
Definition create_fp_constants_decs_def:
  create_fp_constants_decs [] = [] ∧
  create_fp_constants_decs ((w, n)::rest) =
  let declaration = Dlet location$unknown_loc (Pvar n) (Lit (Word64 w)) in
    declaration::(create_fp_constants_decs rest)
End

(**
  Move floating-point constants into decl-nodes and reuse the variables
**)
Definition lift_fp_constants_decs_def:
  lift_fp_constants decs =
    let identifiers = gather_used_identifiers_decs decs;
        constants = gather_constants_decs decs in
      let al = constants_to_variable_names identifiers constants [] in
        let replaced_decs = replace_constants_decs al decs in
        create_fp_constants_decs al ++ replaced_decs
End

(* Canonicalize sub to add and mul times -1.0
 TODO: Consider dropping the multiplication with -1.0 *)
Definition canonicalize_sub_def:
  canonicalize_sub e =
    case e of
    | (App (FP_bop FP_Sub) [e1; e2]) =>
        (App (FP_bop FP_Add) [e1; rewriteFPexp [fp_neg_times_minus_one] e2],
         [Apply (Here, [fp_sub_add]);
          Apply (ListIndex (1, Here),  [fp_neg_times_minus_one])])
    | _ => (e, [])
End

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
         else (canonicalize_sub e))
    (* Canonicalize constants to the rhs *)
    | (App (FP_bop op) [App FpFromWord [l]; e2]) =>
        (if (op ≠ FP_Sub ∧ op ≠ FP_Div) then
           (rewriteFPexp [fp_comm_gen op] e, [Apply (Here, [fp_comm_gen op])])
         else (e, []))
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

Definition post_order_dfs_for_plan_def:
  post_order_dfs_for_plan (f: config -> exp -> (exp # fp_plan) option) (cfg: config) (FpOptimise sc e) = (
  let (e_can, plan: fp_plan) = post_order_dfs_for_plan f (cfg with canOpt := if sc = Opt then T else F) e in
    ((FpOptimise sc e_can),
     MAP (λ step. case step of |Apply (path, rws) => Apply (Center path, rws) |_ => step) plan)
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

Definition optimise_linear_interpolation_def:
  optimise_linear_interpolation cfg e =
  post_order_dfs_for_plan
    (λ cfg e.
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
  case MEM a right of T => a::(intersect_lists rest (remove_first right a))
                   | F => intersect_lists rest right
End

Definition move_multiplicants_to_right_def:
  move_multiplicants_to_right cfg [] e = (e, []) ∧
  move_multiplicants_to_right cfg [m] e =
  (case e of
   | (App (FP_bop FP_Mul) [e1; e2]) =>
       if (m = e1) then
         let plan =  [Apply (Here, [fp_comm_gen FP_Mul])] in
           let commuted = FST (optimise_with_plan cfg plan e) in
             (commuted, plan)
       else (
         if (m = e2) then
           let local_plan = [Apply (Here, [fp_assoc2_gen FP_Mul])] in
             (FST (optimise_with_plan cfg local_plan e), local_plan)
         else
           let local_plan = [Apply (Here, [fp_assoc2_gen FP_Mul])];
               (updated_e2, downstream_plan) = move_multiplicants_to_right cfg [m] e2 in
             let updated_e = App (FP_bop FP_Mul) [e1; updated_e2] in
               (FST (optimise_with_plan cfg local_plan updated_e),
                (MAP_plan_to_path (listIndex 1) downstream_plan) ++ local_plan)
         )
   | _ => (e, [])) ∧
  move_multiplicants_to_right cfg (m1::m2::rest) e =
  let (updated_e, plan) = move_multiplicants_to_right cfg [m1] e in
    case updated_e of
    | (App (FP_bop FP_Mul) [e1; e2]) =>
        (let (updated_e1, other_plan) = move_multiplicants_to_right cfg (m2::rest) e1 in
           let left_plan = MAP_plan_to_path (listIndex 0) other_plan;
               local_plan = [Apply (Here, [fp_assoc_gen FP_Mul]); Apply (ListIndex (1, Here), [fp_comm_gen FP_Mul]) ] in
             let final_e = FST (optimise_with_plan cfg local_plan (App (FP_bop FP_Mul) [updated_e1; e2])) in
               (final_e, plan ++ left_plan ++ local_plan))
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
           (let plan = [Apply (ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen FP_Mul]);
                        Apply (Here, [fp_distribute_gen op' op])];
                optimized = optimise_with_plan cfg plan can_e in
              SOME (optimized, can_plan ++ plan))
         else (if ((op = FP_Add ∨ op = FP_Sub) ∧ (op' = FP_Mul ∨ op' = FP_Div) ∧ op'' = op')
               then
                 (let plan = [Apply (Here, [fp_distribute_gen op' op])];
                      optimized = optimise_with_plan cfg plan can_e in
                    SOME (optimized, can_plan ++ plan))
               else NONE)
     | App (FP_bop op) [
         App (FP_bop op') [e1_1; e1_2];
         e2] =>
         if ((op = FP_Add ∨ op = FP_Sub) ∧ op' = FP_Mul ∧ e1_2 = e2)
            then
              (let plan = [Apply (ListIndex (1, Here), [fp_times_one_reverse; fp_comm_gen op']);
                           Apply (Here, [fp_distribute_gen op' op])];
                   optimized = optimise_with_plan cfg plan can_e in
                 SOME (optimized, can_plan ++ plan))
            else NONE
     | _ => NONE)
End

Definition apply_distributivity_def:
  apply_distributivity cfg e =
  post_order_dfs_for_plan
    (λ cfg e.
      case e of
      | App (FP_bop FP_Add) [e1; App (FP_bop FP_Add) [e2_1; e2_2]] =>
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
              fp_same_sub;
              fp_same_div
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
        (final_e, (Label name) :: plan ++ [Label (STRCAT name " end")] ++ rest_plan)
End

Definition balance_expression_tree_def:
  balance_expression_tree cfg e =
  post_order_dfs_for_plan
    (λ (cfg: config) e.
      case e of
      | (App (FP_bop op) [a; App (FP_bop op') [b; App (FP_bop op'') [c; d]]]) =>
          (if (op = op') ∧ (op' = op'') then
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
            (optimise_linear_interpolation, "Linear Interpolation");
            (canonicalize, "Canonical Form");
            (peephole_optimise, "Peephole Optimisations");
            (canonicalize, "Canonical Form");
            (balance_expression_tree, "Balance Trees")
          ] e cfg)
End

Definition generate_plan_exps_def:
  generate_plan_exps cfg [] = [] ∧
  generate_plan_exps cfg [Fun s e] = generate_plan_exps cfg [e] ∧
  generate_plan_exps cfg (e1::(e2::es)) =
    (generate_plan_exps cfg [e1]) ++ (generate_plan_exps cfg (e2::es)) ∧
  generate_plan_exps cfg [e] = generate_plan_exp cfg e
End

Definition generate_plan_decs_def:
  generate_plan_decs cfg [] = [] ∧
  generate_plan_decs cfg [Dlet loc p e] = [generate_plan_exps cfg [e]] ∧
  generate_plan_decs cfg (d1::(d2::ds)) = (generate_plan_decs cfg [d1]) ++ (generate_plan_decs cfg (d2::ds)) ∧
  generate_plan_decs cfg [d] = []
End

val _ = export_theory();
