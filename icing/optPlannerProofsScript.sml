(**
  Correctness proof for optimization planner
**)
open semanticPrimitivesTheory evaluateTheory
     icing_rewriterTheory icing_optimisationsTheory
     icing_optimisationProofsTheory fpOptTheory fpValTreeTheory
     optPlannerTheory source_to_source2Theory source_to_source2ProofsTheory
     floatToRealProofsTheory icing_realIdProofsTheory;

open preamble;

val _ = new_theory "optPlannerProofs";

fun rnCases_on t = rename1 t >> Cases_on t

(** The phase repeater can only repeat rewrites **)
Theorem phase_repeater_mem:
  ∀ n path rws r cfg e e2.
    MEM (Apply (path, rws)) r ∧
    phase_repeater n apply_distributivity cfg e = (e2, r) ⇒
    ∃ ei. MEM (Apply (path, rws)) (SND (apply_distributivity cfg ei))
Proof
  Induct_on ‘n’ >> gs[phase_repeater_def] >> rpt strip_tac
  >- (qexists_tac ‘e’ >> gs[])
  >> Cases_on ‘apply_distributivity cfg e’ >> gs[]
  >> Cases_on ‘q ≠ e’ >> gs[]
  >> rnCases_on ‘phase_repeater n apply_distributivity cfg e3’ >> gs[]
  >> rveq >> gs[MEM_APPEND]
  >- (qexists_tac ‘e’ >> gs[])
  >> first_x_assum irule >> asm_exists_tac >> gs[]
QED

(** Side-lemmas to ease proofs later **)
fun path_tac index_def =
  Induct_on ‘r’ >> simp[MAP_plan_to_path_def]
  >> rpt strip_tac
  >- (
    Cases_on ‘h’ >> gs[]
    >> Cases_on ‘p’ >> gs[index_def])
  >> last_x_assum mp_tac >> impl_tac >> gs[MAP_plan_to_path_def]
  >> strip_tac >> asm_exists_tac >> gs[];

Theorem MEM_MAP_plan_to_path_index:
  MEM (Apply (path, rws)) (MAP_plan_to_path (listIndex n) r) ⇒
    ∃ spath. path = ListIndex (n, spath) ∧
      MEM (Apply (spath, rws)) r
Proof
  path_tac listIndex_def
QED

Theorem MEM_MAP_plan_to_path_right:
  MEM (Apply (path, rws)) (MAP_plan_to_path right r) ⇒
    ∃ spath. path = Right spath ∧
      MEM (Apply (spath, rws)) r
Proof
  path_tac right_def
QED

Theorem MEM_MAP_plan_to_path_center:
  MEM (Apply (path, rws)) (MAP_plan_to_path center r) ⇒
    ∃ spath. path = Center spath ∧
      MEM (Apply (spath, rws)) r
Proof
  path_tac center_def
QED

Theorem MEM_MAP_plan_to_path_left:
  MEM (Apply (path, rws)) (MAP_plan_to_path left r) ⇒
    ∃ spath. path = Left spath ∧
      MEM (Apply (spath, rws)) r
Proof
  path_tac left_def
QED

Theorem MAP_plan_to_path_SUC_prod:
  (λ i (_, plani). MAP_plan_to_path (listIndex (i+n)) plani) o SUC =
  λ i (_, plani). MAP_plan_to_path (listIndex (i + SUC n)) plani
Proof
  gs[FUN_EQ_THM] >> rpt strip_tac >> gs[SUC_ONE_ADD]
QED

Theorem MAP_plan_to_path_SUC_trip:
  (λ i (_, _, plani). MAP_plan_to_path (listIndex (i+n)) plani) o SUC =
  λ i (_, _, plani). MAP_plan_to_path (listIndex (i + SUC n)) plani
Proof
  gs[FUN_EQ_THM] >> rpt strip_tac >> gs[SUC_ONE_ADD]
QED

Theorem MAPi_plan_to_path_prod:
  MAPi ((λ i (_, plani). MAP_plan_to_path (listIndex (i + n)) plani) o SUC) =
  MAPi (λ i (_, plani). MAP_plan_to_path (listIndex (i+ SUC n)) plani)
Proof
  gs[MAP_plan_to_path_SUC_prod]
QED

Theorem MAPi_plan_to_path_trip:
  MAPi ((λ i (_, _, plani). MAP_plan_to_path (listIndex (i + n)) plani) o SUC) =
  MAPi (λ i (_, _, plani). MAP_plan_to_path (listIndex (i+ SUC n)) plani)
Proof
  gs[MAP_plan_to_path_SUC_trip]
QED

Theorem MEM_list_flat_sub_exp_general:
  ∀ l n f path rws cfg.
    MEM (Apply (path, rws))
        (FLAT (MAPi (λi (_, plani).
                      MAP_plan_to_path (listIndex (i+n)) plani)
               (MAP (λ a. f a) l))) ⇒
  ∃ e path. exp_size e < exp6_size l ∧
            MEM (Apply (path, rws)) (SND (f e)) ∧
            MEM e l
Proof
  Induct_on ‘l’ >> gs[]
  >> rpt strip_tac >> gs[]
  >- (
    qexists_tac ‘h’ >> gs[astTheory.exp_size_def]
    >> Cases_on ‘f h’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_index >> asm_exists_tac >> gs[])
  >> gs[MAPi_plan_to_path_prod]
  >> res_tac >> qexists_tac ‘e’ >> gs[astTheory.exp_size_def]
  >> asm_exists_tac >> gs[]
QED

Theorem MEM_list_flat_sub_exp =
        Q.SPECL [‘l’, ‘0’, ‘f’] MEM_list_flat_sub_exp_general
          |> GEN “l:exp list”
          |> GEN “f:exp -> 'a # opt_step list”
          |> REWRITE_RULE [ADD_CLAUSES];

Theorem MEM_list_flat_sub_patexp_general:
  ∀ l n f path rws cfg.
    MEM (Apply (path, rws))
        (FLAT (MAPi (λi (_, _, plani).
                      MAP_plan_to_path (listIndex (i+n)) plani)
               (MAP (λ (p,e). (p, f e)) l))) ⇒
  ∃ e p path. exp_size e < exp3_size l ∧
            MEM (Apply (path, rws)) (SND (f e)) ∧
            MEM  (p, e) l
Proof
  Induct_on ‘l’ >> gs[]
  >> rpt strip_tac >> gs[]
  >- (
    Cases_on ‘h’ >> gs[]
    >> qexists_tac ‘r’ >> qexists_tac ‘q’ >> gs[astTheory.exp_size_def]
    >> Cases_on ‘f r’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_index >> asm_exists_tac >> gs[])
  >> gs[MAPi_plan_to_path_trip]
  >> res_tac >> qexists_tac ‘e’ >> gs[astTheory.exp_size_def]
  >> asm_exists_tac >> qexists_tac ‘p’ >> gs[]
QED

Theorem MEM_list_flat_sub_patexp =
        Q.SPECL [‘l’, ‘0’] MEM_list_flat_sub_patexp_general
          |> GEN “l:(pat # exp) list”
          |> GEN “f:exp -> 'a # opt_step list”
          |> REWRITE_RULE [ADD_CLAUSES];

(** Now prove that generate_plan_exp can only produce rewrites from its
    components **)
Theorem generate_plan_upper_bound_rws:
  MEM (Apply (path,rws)) (generate_plan_exp cfg e) ⇒
      (∃ e. MEM (Apply (path,rws)) (SND (canonicalize cfg e))) ∨
      (∃ e. MEM (Apply (path,rws)) (SND (apply_distributivity cfg e))) ∨
      (∃ e. MEM (Apply (path,rws)) (SND (peephole_optimise cfg e))) ∨
      (∃ e. MEM (Apply (path,rws)) (SND (balance_expression_tree cfg e)))
Proof
  gs[generate_plan_exp_def, compose_plan_generation_def]
  >> rnCases_on ‘canonicalize cfg e’ >> gs[]
  >> rnCases_on ‘phase_repeater 100 apply_distributivity cfg e2’ >> gs[]
  >> rnCases_on ‘canonicalize cfg e3’ >> gs[]
  >> rnCases_on ‘canonicalize cfg e4’ >> gs[]
  >> rnCases_on ‘peephole_optimise cfg e5’ >> gs[]
  >> rnCases_on ‘balance_expression_tree cfg e6’ >> gs[]
  >> rename1 ‘balance_expression_tree cfg e6 = (e7, r7)’
  >> rpt (TOP_CASE_TAC >> gs[]) >> rveq >> strip_tac
  >> imp_res_tac phase_repeater_mem
  (* canonicalize cases *)
  >> TRY (DISJ1_TAC >> qexists_tac ‘e’ >> gs[] >> NO_TAC)
  >> TRY (DISJ1_TAC >> qexists_tac ‘e2’ >> gs[] >> NO_TAC)
  >> TRY (DISJ1_TAC >> qexists_tac ‘e3’ >> gs[] >> NO_TAC)
  >> TRY (DISJ1_TAC >> qexists_tac ‘e4’ >> gs[] >> NO_TAC)
  (* phase repeater cases *)
  >> TRY (DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘ei’ >> gs[] >> NO_TAC)
  (* peephole optimise cases *)
  >> TRY (ntac 2 DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘e’ >> gs[] >> NO_TAC)
  >> TRY (ntac 2 DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘e2’ >> gs[] >> NO_TAC)
  >> TRY (ntac 2 DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘e3’ >> gs[] >> NO_TAC)
  >> TRY (ntac 2 DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘e4’ >> gs[] >> NO_TAC)
  >> TRY (ntac 2 DISJ2_TAC >> DISJ1_TAC >> qexists_tac ‘e5’ >> gs[] >> NO_TAC)
  (* balance expression tree cases *)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e’ >> gs[] >> NO_TAC)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e2’ >> gs[] >> NO_TAC)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e3’ >> gs[] >> NO_TAC)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e4’ >> gs[] >> NO_TAC)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e5’ >> gs[] >> NO_TAC)
  >> TRY (ntac 3 DISJ2_TAC >> qexists_tac ‘e6’ >> gs[] >> NO_TAC)
QED

(** Bound for canonicalize **)
Theorem canonicalize_app_upper_bound:
  ∀ e op eNew r path rws rw r.
    canonicalize_app e = (eNew, r) ∧
    MEM (Apply (path, rws)) r  ∧
    MEM rw rws ⇒
    MEM rw [fp_neg_times_minus_one; fp_sub_add;
            fp_comm_gen FP_Add; fp_comm_gen FP_Mul;
            fp_assoc_gen FP_Add; fp_assoc_gen FP_Mul]
Proof
  measureInduct_on ‘exp_size e’
  >> simp[Once canonicalize_app_def, CaseEq"op", CaseEq"list"]
  >> rpt strip_tac >> gs[CaseEq "exp", CaseEq "fp_bop", CaseEq"list", CaseEq"op"]
  >> rveq >> gs[canonicalize_sub_def]
  >> qpat_x_assum ‘_ = (_, _)’ mp_tac
  >> COND_CASES_TAC >> gs[] >> rpt strip_tac >> rveq >> gs[]
  >- (
    Cases_on ‘canonicalize_app (App (FP_bop FP_Add) [v315; v153])’
    >> gs[] >> rveq >> gs[MEM]
    >> imp_res_tac MEM_MAP_plan_to_path_index
    >> first_x_assum $ qspec_then ‘App (FP_bop FP_Add) [v315; v153]’ mp_tac
    >> gs[astTheory.exp_size_def]
    >> rpt $ disch_then drule >> gs[])
  >> Cases_on ‘canonicalize_app (App (FP_bop FP_Mul) [v453; v153])’
  >> gs[] >> rveq >> gs[MEM]
  >> imp_res_tac MEM_MAP_plan_to_path_index
  >> first_x_assum $ qspec_then ‘App (FP_bop FP_Mul) [v453; v153]’ mp_tac
  >> gs[astTheory.exp_size_def]
  >> rpt $ disch_then drule >> gs[]
QED

fun trivial_case_tac t =
  first_x_assum $ qspec_then t mp_tac >> gs[]
  >> disch_then $ qspecl_then [‘spath’, ‘rws’, ‘cfg’] mp_tac >> gs[];

(** Prove upper bound on rewrites for canonicalize **)
Theorem canonicalize_upper_bound:
  ∀ e path rws cfg.
    MEM (Apply (path, rws)) (SND (canonicalize cfg e)) ⇒
    ∀ rw. MEM rw rws ⇒
          MEM rw [fp_neg_times_minus_one; fp_sub_add;
                  fp_comm_gen FP_Add; fp_comm_gen FP_Mul;
                  fp_assoc_gen FP_Add; fp_assoc_gen FP_Mul]
Proof
  measureInduct_on  ‘exp_size e’
  >> Cases_on ‘e’ >> gs[canonicalize_def] >> rpt strip_tac
  >> gs[astTheory.exp_size_def]
  >- (
    imp_res_tac MEM_list_flat_sub_exp
    >> first_x_assum $ qspec_then ‘e’ mp_tac >> gs[]
    >> disch_then (fn ith => first_x_assum (fn th => mp_then Any drule ith th))
    >> gs[])
  >- (
    Cases_on  ‘cfg.canOpt’ >> gs[]
    >- (
      Cases_on ‘canonicalize_app (App o' (MAP FST (MAP (λ a. canonicalize cfg a) l)))’ >> gs[]
      >- (
        imp_res_tac MEM_list_flat_sub_exp
        >> first_x_assum $ qspec_then ‘e’ mp_tac >> gs[]
        >> disch_then (fn ith => first_x_assum (fn th => mp_then Any drule ith th))
        >> gs[])
      >> imp_res_tac canonicalize_app_upper_bound >> gs[])
    >> imp_res_tac MEM_list_flat_sub_exp
    >> first_x_assum $ qspec_then ‘e’ mp_tac >> gs[]
    >> disch_then (fn ith => first_x_assum (fn th => mp_then Any drule ith th))
    >> gs[])
  >- (
    Cases_on ‘canonicalize cfg e0’ >> Cases_on ‘canonicalize cfg e'’
    >> gs[MEM_APPEND]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >- trivial_case_tac ‘e'’
    >> trivial_case_tac ‘e0’)
  >- (
    Cases_on ‘canonicalize cfg e1’
    >> Cases_on ‘canonicalize cfg e0’
    >> Cases_on ‘canonicalize cfg e'’
    >> gs[MEM_APPEND]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >- trivial_case_tac ‘e'’
    >- trivial_case_tac ‘e0’
    >> trivial_case_tac ‘e1’)
  >- (
    Cases_on ‘canonicalize cfg e'’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >- trivial_case_tac ‘e'’
    >> imp_res_tac MEM_list_flat_sub_patexp
    >> first_x_assum $ qspec_then ‘e’ mp_tac >> gs[]
    >> disch_then (fn ith => first_x_assum (fn th => mp_then Any drule ith th))
    >> gs[])
  >- (
    Cases_on ‘canonicalize cfg e0’ >> Cases_on ‘canonicalize cfg e'’
    >> gs[MEM_APPEND]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >- trivial_case_tac ‘e'’
    >> trivial_case_tac ‘e0’)
  >- (
    Cases_on ‘canonicalize cfg e'’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> trivial_case_tac ‘e'’)
  >- (
    Cases_on ‘canonicalize cfg e'’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> trivial_case_tac ‘e'’)
  >- (
    Cases_on ‘canonicalize cfg e'’ >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> trivial_case_tac ‘e'’)
  >> Cases_on ‘canonicalize (cfg with canOpt := (f = Opt)) e'’ >> gs[]
  >> imp_res_tac MEM_MAP_plan_to_path_center
  >> first_x_assum $ qspec_then ‘e'’ mp_tac >> gs[]
  >> disch_then $ qspecl_then [‘spath’, ‘rws’, ‘cfg with canOpt := (f = Opt)’] mp_tac
  >> gs[]
QED

(** Intermediate theorem for postorder-traversal of expressions **)
Theorem postorder_upper_bound:
  ∀ f cfg e P.
  (∀ e cfg eOpt plan.
     f cfg e = SOME (eOpt, plan) ⇒
     ∀ path rws.
       MEM (Apply (path, rws)) plan ⇒
       P rws) ⇒
  ∀ eOpt plan path rws.
    (post_order_dfs_for_plan f cfg e) = (eOpt, plan) ⇒
    (MEM (Apply (path, rws)) plan ⇒
     P rws)
Proof
  ho_match_mp_tac post_order_dfs_for_plan_ind >> rw[]
  >> gs[post_order_dfs_for_plan_def]
  >- (
    Cases_on ‘post_order_dfs_for_plan f (cfg with canOpt := (sc = Opt)) e’
    >> gs[] >> rveq
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> first_x_assum drule >> disch_then drule >> gs[])
  >- (
    qpat_x_assum `_ = (_,_)` mp_tac
    >> COND_CASES_TAC >> gs[]
    >- (
      TOP_CASE_TAC >> gs[]
      >- (
        rpt strip_tac >> rveq
        >> imp_res_tac MEM_list_flat_sub_exp
        >> res_tac
        >> Cases_on ‘post_order_dfs_for_plan f cfg e’ >> gs[]
        >> first_x_assum drule >> gs[])
      >> TOP_CASE_TAC >> gs[]
      >> rpt strip_tac >> rveq >> gs[]
      >> imp_res_tac MEM_list_flat_sub_exp
      >> res_tac
      >> Cases_on ‘post_order_dfs_for_plan f cfg e’ >> gs[]
      >> first_x_assum drule >> gs[])
    >> rpt strip_tac >> rveq
    >> imp_res_tac MEM_list_flat_sub_exp
    >> res_tac
    >> Cases_on ‘post_order_dfs_for_plan f cfg e’ >> gs[]
    >> first_x_assum drule >> gs[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e'’
    >> Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq >> gs[MEM_APPEND]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >> res_tac)
  >- (
    rveq
    >> imp_res_tac MEM_list_flat_sub_exp
    >> res_tac
    >> Cases_on ‘post_order_dfs_for_plan f cfg e’ >> gs[]
    >> first_x_assum drule >> gs[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e'’
    >> Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq >> gs[MEM_APPEND]
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >> res_tac)
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e''’
    >> Cases_on ‘post_order_dfs_for_plan f cfg e'’
    >> Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> ntac 5 $ pop_assum mp_tac
    >> disch_then (fn th => mp_tac (SIMP_RULE std_ss [] th))
    >> rpt strip_tac >> rveq
    >> qpat_x_assum `MEM _ _` mp_tac
    >> rewrite_tac[MEM_APPEND] >> strip_tac
    >> imp_res_tac MEM_MAP_plan_to_path_left
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> imp_res_tac MEM_MAP_plan_to_path_right
    >- (
      res_tac >> first_x_assum drule >> rveq
      >> metis_tac[])
    >- (
      res_tac >> first_x_assum drule >> rveq
      >> metis_tac[])
    >> last_x_assum $ qspecl_then [‘q''’, ‘r''’, ‘q'’, ‘r'’] mp_tac
    >> impl_tac >- rewrite_tac[]
    >> disch_then $ qspec_then ‘P’ mp_tac
    >> impl_tac >- first_x_assum MATCH_ACCEPT_TAC
    >> disch_then $ qspecl_then [‘q’, ‘r’, ‘spath’, ‘rws’] mp_tac
    >> impl_tac >- asm_rewrite_tac[]
    >> metis_tac[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> first_x_assum drule >> disch_then drule >> gs[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> first_x_assum drule >> disch_then drule >> gs[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq
    >> imp_res_tac MEM_MAP_plan_to_path_center
    >> first_x_assum drule >> disch_then drule >> gs[])
  >- (
    Cases_on ‘post_order_dfs_for_plan f cfg e’
    >> gs[] >> rveq >> gs[MEM_APPEND]
    >- (
      imp_res_tac MEM_MAP_plan_to_path_left
      >> first_x_assum drule >> disch_then drule >> gs[])
    >> imp_res_tac MEM_list_flat_sub_patexp
    >> res_tac
    >> Cases_on ‘post_order_dfs_for_plan f cfg e'’ >> gs[]
    >> first_x_assum drule >> gs[])
QED

Theorem plan_app_rewrite_with_each_alt:
  ∀ xs e eOpt plan path rws rw.
    (λ (rewritten, plan).
      if plan = [] then NONE
      else SOME (rewritten, MAP (λ x. Apply x) plan))
    (try_rewrite_with_each xs e) = SOME (eOpt, plan) ∧
    MEM (Apply (path, rws)) plan ∧
    MEM rw rws ⇒
    MEM rw xs
Proof
  Induct_on ‘xs’ >> simp[Once try_rewrite_with_each_def]
  >> rpt strip_tac >> qpat_x_assum `_ = SOME _` mp_tac
  >> PairCases_on ‘h’ >> gs[try_rewrite_with_each_def]
  >> TOP_CASE_TAC >> gs[]
  >- (rpt strip_tac >> res_tac >> metis_tac[])
  >> rpt strip_tac >> rveq >> gs[]
  >> ‘∃subplan. plan = (Apply (Here, [(h0,h1)]))::subplan’
    by (
      Cases_on ‘try_rewrite_with_each xs (rewriteFPexp [(h0, h1)] e)’
      >> gs[] >> rveq >> gs[])
  >> rveq >> gs[]
  >> DISJ2_TAC >> first_x_assum irule
  >> qexists_tac ‘rewriteFPexp [(h0,h1)] e’ >> qexists_tac ‘eOpt’
  >> qexists_tac ‘path’ >> qexists_tac ‘subplan’ >> qexists_tac ‘rws’
  >> gs[]
  >> Cases_on ‘try_rewrite_with_each xs (rewriteFPexp [(h0, h1)] e)’
  >> gs[] >> rveq >> Cases_on ‘r’ >> gs[]
QED

Theorem peephole_optimise_upper_bound:
  ∀ e path rws cfg.
    MEM (Apply (path, rws)) (SND (peephole_optimise cfg e)) ⇒
    ∀ rw. MEM rw rws ⇒
          MEM rw [fp_neg_push_mul_r; fp_times_minus_one_neg; fp_add_sub;
                  fp_times_two_to_add; fp_times_three_to_add; fp_times_zero;
                  fp_plus_zero; fp_times_one; fp_same_sub; fp_fma_intro]
Proof
  simp[Once peephole_optimise_def]
  >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM _ (SND (post_order_dfs_for_plan peephole_app cfg e))’
  >> rpt strip_tac
  >> qspecl_then [‘peephole_app’, ‘cfg’, ‘e’,
                  ‘λ rws. ∀ rw. MEM rw rws ⇒
                                rw = fp_neg_push_mul_r ∨ rw = fp_times_minus_one_neg ∨
                                rw = fp_add_sub ∨ rw = fp_times_two_to_add ∨
                                rw = fp_times_three_to_add ∨ rw = fp_times_zero ∨
                                rw = fp_plus_zero ∨ rw = fp_times_one ∨ rw = fp_same_sub ∨
                                rw = fp_fma_intro’]
                 mp_tac postorder_upper_bound
  >> gs[]
  >> impl_tac
  >- (
    unabbrev_all_tac
    >> rpt $ pop_assum kall_tac
    >> gs[] >> rpt strip_tac
    >> drule plan_app_rewrite_with_each_alt
    >> rpt $ disch_then drule >> gs[] >> metis_tac[])
  >> Cases_on ‘post_order_dfs_for_plan peephole_app cfg e’ >> gs[]
  >> rpt $ disch_then drule >> gs[]
QED

Theorem move_multiplicants_to_right_upper_bound:
  ∀ cfg intersect e eOpt plan path rws rw.
    move_multiplicants_to_right cfg intersect e = (eOpt, plan) ∧
    MEM (Apply (path, rws)) plan ∧
    MEM rw rws ⇒
    MEM rw [fp_comm_gen FP_Mul; fp_assoc_gen FP_Mul; fp_assoc2_gen FP_Mul]
Proof
  ho_match_mp_tac move_multiplicants_to_right_ind
  >> rw[]
  >- gs[move_multiplicants_to_right_def]
  >- (
    qpat_x_assum `move_multiplicants_to_right _ _ _ = _` mp_tac
    >> simp[Once move_multiplicants_to_right_def,
            CaseEq "exp", CaseEq"list", CaseEq"op", CaseEq"fp_bop"]
    >> rpt strip_tac >> gs[] >> rveq
    >> Cases_on ‘move_multiplicants_to_right cfg [m] e2’ >> gs[]
    >> qpat_x_assum `(if _ then _ else _) = _` mp_tac
    >> rpt (COND_CASES_TAC >> gs[])
    >> rpt strip_tac >> rveq >> gs[]
    >> imp_res_tac MEM_MAP_plan_to_path_index
    >> first_x_assum drule >> rpt $ disch_then drule >> gs[])
  >> qpat_x_assum `move_multiplicants_to_right _ _ _ = _` mp_tac
  >> simp[Once move_multiplicants_to_right_def]
  >> Cases_on ‘move_multiplicants_to_right cfg [m1] e’ >> gs[]
  >> simp[CaseEq "exp", CaseEq"list", CaseEq"op", CaseEq"fp_bop"]
  >> rpt strip_tac >> gs[] >> rveq
  >> TRY (
    first_x_assum $ drule
    >> rpt $ disch_then drule >> gs[] >> NO_TAC)
  >> Cases_on ‘move_multiplicants_to_right cfg (m2::rest) e1’ >> gs[]
  >> qpat_x_assum `(if _ then _ else _) = _` mp_tac
  >> rpt (COND_CASES_TAC >> gs[])
  >> rpt strip_tac >> rveq >> gs[]
  >> imp_res_tac MEM_MAP_plan_to_path_index
  >> first_x_assum $ drule
  >> rpt $ disch_then drule >> gs[]
QED

Theorem canonicalize_for_distributivity_upper_bound:
  MEM (Apply (path, rws)) (SND (canonicalize_for_distributivity cfg e)) ∧
  MEM rw rws ⇒
  MEM rw [fp_comm_gen FP_Mul; fp_assoc_gen FP_Mul; fp_assoc2_gen FP_Mul]
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM rw canon_rws’
  >> Cases_on `canonicalize_for_distributivity cfg e` >> gs[]
  >> gs[canonicalize_for_distributivity_def]
  >> qpat_x_assum ‘_ = (_, _)’ mp_tac
  >> qmatch_goalsub_abbrev_tac ‘post_order_dfs_for_plan canonicalize_app_fun _ _’
  >> rpt strip_tac
  >> qspecl_then [‘canonicalize_app_fun’, ‘cfg’, ‘e’, ‘λ rws. ∀ rw. MEM rw rws ⇒ MEM rw canon_rws’]
                 mp_tac postorder_upper_bound
  >> gs[]
  >> reverse impl_tac
  >- (rpt $ disch_then drule >> gs[])
  >> unabbrev_all_tac
  >> rpt $ pop_assum kall_tac
  >> rpt strip_tac >> gs[CaseEq"exp", CaseEq"op", CaseEq"list"]
  >> rveq
  >> qpat_x_assum ‘_ = SOME _’ mp_tac
  >> qmatch_goalsub_abbrev_tac ‘move_multiplicants_to_right _ intersect_e1_e2 _’
  >> Cases_on ‘move_multiplicants_to_right cfg' intersect_e1_e2 e1’ >> gs[]
  >> Cases_on ‘move_multiplicants_to_right cfg' intersect_e1_e2 e2’ >> gs[]
  >> rpt strip_tac >> rveq >> gs[MEM_APPEND]
  >> imp_res_tac MEM_MAP_plan_to_path_index
  >> imp_res_tac move_multiplicants_to_right_upper_bound >> gs[]
QED

Theorem canonicalize_for_distributivity_upper_bound_alt:
  canonicalize_for_distributivity cfg e = (eOpt, plan) ∧
  MEM (Apply (path, rws)) plan ∧
  MEM rw rws ⇒
  MEM rw [fp_comm_gen FP_Mul; fp_assoc_gen FP_Mul; fp_assoc2_gen FP_Mul]
Proof
  rpt strip_tac >> irule canonicalize_for_distributivity_upper_bound
  >> qexists_tac ‘cfg’ >> qexists_tac ‘e’ >> gs[]
  >> asm_exists_tac >> gs[]
QED

Theorem apply_distributivity_local_plan:
  apply_distributivity_local cfg e = SOME ((eOpt, res), plan) ∧
  MEM (Apply (path, rws)) plan ∧
  MEM rw rws ⇒
    MEM (Apply (path, rws)) (SND (canonicalize_for_distributivity cfg e))∨
    MEM rw [fp_comm_gen FP_Mul;
            fp_distribute_gen FP_Mul FP_Add; fp_distribute_gen FP_Mul FP_Sub;
            fp_distribute_gen FP_Div FP_Add; fp_distribute_gen FP_Div FP_Sub]
Proof
  gs[apply_distributivity_local_def]
  >> Cases_on ‘canonicalize_for_distributivity cfg e’ >> gs[CaseEq"exp", CaseEq"list", CaseEq"op"]
  >> rpt strip_tac >> rveq >> gs[MEM_APPEND]
  >> qpat_x_assum `_ = SOME _` mp_tac
  >> COND_CASES_TAC >> gs[]
  >> rpt strip_tac >> rveq >> gs[MEM_APPEND]
QED

val simple_case_tac =
  last_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
  >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
  >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
  >> disch_then drule >> gs[];

Theorem apply_distributivity_upper_bound:
  ∀ e path rws cfg.
    MEM (Apply (path, rws)) (SND (apply_distributivity cfg e)) ⇒
    ∀ rw. MEM rw rws ⇒
          MEM rw [fp_comm_gen FP_Mul;
                  fp_distribute_gen FP_Mul FP_Add; fp_distribute_gen FP_Mul FP_Sub;
                  fp_distribute_gen FP_Div FP_Add; fp_distribute_gen FP_Div FP_Sub;
                  fp_assoc2_gen FP_Add; fp_comm_gen FP_Mul; fp_assoc_gen FP_Mul;
                  fp_assoc2_gen FP_Mul]
Proof
  qmatch_goalsub_abbrev_tac ‘MEM _ distrib_rws’
  >> simp[Once apply_distributivity_def]
  >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM _ (SND (post_order_dfs_for_plan distributivity_app cfg e))’
  >> rpt strip_tac
  >> qspecl_then [‘distributivity_app’, ‘cfg’, ‘e’,
                  ‘λ rws. ∀ rw. MEM rw rws ⇒ MEM rw distrib_rws’]
                 mp_tac postorder_upper_bound
  >> gs[]
  >> reverse impl_tac
  >- (
    Cases_on ‘post_order_dfs_for_plan distributivity_app cfg e’ >> gs[]
    >> rpt $ disch_then drule >> gs[])
  >> unabbrev_all_tac
  >> rpt $ pop_assum kall_tac
  >> rpt strip_tac
  >> gs[CaseEq"exp", CaseEq"option", CaseEq"prod"] >> rveq
  >~ [‘App op es’]
  >- (
    gs[CaseEq"op", CaseEq"option", CaseEq"prod", CaseEq"fp_bop", CaseEq"list",
       CaseEq"exp"]
    >> rveq >> gs[]
    >> TRY (simple_case_tac >> NO_TAC)
    >> Cases_on ‘canonicalize_for_distributivity cfg' e2_2’
    >> Cases_on ‘canonicalize_for_distributivity cfg' (App (FP_bop FP_Add) [e1; e2_1])’
    >> gs[CaseEq"option", CaseEq"prod"] >> rveq >> gs[]
    >- simple_case_tac
    >- (
      Cases_on ‘canonicalize_for_distributivity cfg' (App (FP_bop FP_Add) [e1_can_dist; q])’
      >> gs[CaseEq"option", CaseEq"prod"] >> rveq >> gs[]
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
        >> gs[])
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
        >> gs[])
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> simple_case_tac)
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
        >> gs[])
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
        >> gs[])
      >- (
        imp_res_tac MEM_MAP_plan_to_path_index
        >> first_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
        >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
        >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
        >> disch_then drule >> gs[])
      >- (imp_res_tac canonicalize_for_distributivity_upper_bound_alt >> gs[])
      >> qpat_x_assum ‘apply_distributivity_local _ (App _ _) = SOME _’
                      $ mp_then Any mp_tac apply_distributivity_local_plan
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
      >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound_alt
      >> rpt $ disch_then drule >> gs[])
    >> Cases_on ‘canonicalize_for_distributivity cfg' (App (FP_bop FP_Add) [e1_can_dist; e2_can_dist])’
    >> gs[CaseEq"option", CaseEq"prod"] >> rveq >> gs[]
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
      >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
      >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> first_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
      >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
      >> disch_then drule >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> first_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
      >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
      >> disch_then drule >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
      >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> qpat_x_assum `canonicalize_for_distributivity _ _ = (_, r)` $
           mp_then Any mp_tac canonicalize_for_distributivity_upper_bound_alt
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> first_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
      >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
      >> disch_then drule >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> last_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
      >> disch_then kall_tac
      >> last_x_assum $ mp_then Any mp_tac apply_distributivity_local_plan
      >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
      >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound
      >> disch_then drule >> gs[])
    >- (
      imp_res_tac MEM_MAP_plan_to_path_index
      >> imp_res_tac canonicalize_for_distributivity_upper_bound_alt
      >> gs[])
    >> qpat_x_assum ‘apply_distributivity_local _ (App _ _) = SOME _’
                    $ mp_then Any mp_tac apply_distributivity_local_plan
    >> rpt $ disch_then drule >> rpt strip_tac >> gs[]
    >> first_x_assum $ mp_then Any mp_tac canonicalize_for_distributivity_upper_bound_alt
    >> disch_then drule >> gs[])
  >> simple_case_tac
QED

Theorem balance_expression_tree_upper_bound:
  MEM (Apply (path, rws)) (SND(balance_expression_tree cfg e)) ⇒
  ∀ rw.
    MEM rw rws ⇒
    MEM rw [fp_assoc2_gen FP_Add ; fp_assoc2_gen FP_Mul]
Proof
  simp[Once balance_expression_tree_def]
  >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘MEM _ (SND (post_order_dfs_for_plan balance_app cfg e))’
  >> rpt strip_tac
  >> qspecl_then [‘balance_app’, ‘cfg’, ‘e’,
                  ‘λ rws. ∀ rw. MEM rw rws ⇒ MEM rw [fp_assoc2_gen FP_Add; fp_assoc2_gen FP_Mul]’]
                 mp_tac postorder_upper_bound
  >> gs[]
  >> reverse impl_tac
  >- (
    Cases_on ‘post_order_dfs_for_plan balance_app cfg e’ >> gs[]
    >> rpt $ disch_then drule >> gs[])
  >> unabbrev_all_tac >> rpt $ pop_assum kall_tac
  >> gs[CaseEq"exp", CaseEq"op", CaseEq"fp_bop", CaseEq"list"]
  >> rpt strip_tac >> gs[]
QED

Theorem rewriteFPexp_weakening:
  (∀ rw. MEM rw rws2 ⇒
         ∀ (st1:'a semanticPrimitives$state) st2 env e r.
           is_rewriteFPexp_correct [rw] st1 st2 env e r) ∧
  (∀ rw. MEM rw rws1 ⇒ MEM rw rws2) ⇒
  ∀ (st1:'a semanticPrimitives$state) st2 env e r.
    is_rewriteFPexp_correct rws1 st1 st2 env e r
Proof
  Induct_on ‘rws1’ >> gs[empty_rw_correct]
  >> rpt strip_tac
  >> ‘h :: rws1 = [h] ++ rws1’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule rewriteExp_compositional >> reverse conj_tac
  >- (
    first_x_assum $ qspec_then ‘h’ mp_tac >> gs[] >> strip_tac
    >> first_x_assum drule >> gs[])
  >> last_x_assum irule
  >> conj_tac >> gs[]
QED

Theorem is_real_id_exp_weakening:
  (∀ rw. MEM rw rws2 ⇒
         ∀ (st1:'a semanticPrimitives$state) st2 env e r.
           is_real_id_exp [rw] st1 st2 env e r) ∧
  (∀ rw. MEM rw rws1 ⇒ MEM rw rws2) ⇒
  ∀ (st1:'a semanticPrimitives$state) st2 env e r.
    is_real_id_exp rws1 st1 st2 env e r
Proof
  Induct_on ‘rws1’ >> gs[empty_rw_real_id]
  >> rpt strip_tac
  >> ‘h :: rws1 = [h] ++ rws1’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule real_valued_id_compositional >> reverse conj_tac
  >- (
    first_x_assum $ qspec_then ‘h’ mp_tac >> gs[] >> strip_tac
    >> first_x_assum drule >> gs[])
  >> last_x_assum irule
  >> conj_tac >> gs[]
QED

Theorem optPlanner_correct_float_single:
  ∀ e st1 st2 env cfg exps r.
    is_optimise_with_plan_correct (generate_plan_exp cfg e) st1 st2 env cfg exps r
Proof
  rpt strip_tac
  >> irule is_optimise_with_plan_correct_lift
  >> rpt gen_tac >> strip_tac
  >> irule is_rewriteFPexp_correct_lift_perform_rewrites
  >> irule lift_rewriteFPexp_correct_list
  >> first_x_assum $ mp_then Any assume_tac generate_plan_upper_bound_rws
  >> gs[]
  >> imp_res_tac balance_expression_tree_upper_bound
  >> imp_res_tac canonicalize_upper_bound
  >> imp_res_tac apply_distributivity_upper_bound
  >> imp_res_tac peephole_optimise_upper_bound
  >> irule rewriteFPexp_weakening >> asm_exists_tac >> gs[]
  >> rpt strip_tac >> rveq
  >> gs[fp_times_two_to_add_correct_unfold, fp_times_two_to_add_correct,
    fp_times_three_to_add_correct_unfold, fp_times_three_to_add_correct,
    fp_times_one_correct_unfold, fp_times_one_correct,
    fp_times_minus_one_neg_correct_unfold,
    fp_times_minus_one_neg_correct, fp_sub_add_correct_unfold,
    fp_sub_add_correct, fp_plus_zero_correct_unfold,
    fp_plus_zero_correct, fp_neg_times_minus_one_correct_unfold,
    fp_neg_times_minus_one_correct, fp_neg_push_mul_r_correct_unfold,
    fp_neg_push_mul_r_correct, fp_fma_intro_correct_unfold,
    fp_fma_intro_correct, fp_distribute_gen_correct_unfold_add,
    fp_distribute_gen_correct_unfold, fp_distribute_gen_correct,
    fp_comm_gen_correct_unfold_mul, fp_comm_gen_correct_unfold_add,
    fp_comm_gen_correct_unfold, fp_comm_gen_correct,
    fp_assoc_gen_correct_unfold_mul, fp_assoc_gen_correct_unfold_add,
    fp_assoc_gen_correct_unfold, fp_assoc_gen_correct,
    fp_assoc2_gen_correct_unfold_mul, fp_assoc2_gen_correct_unfold_add,
    fp_assoc2_gen_correct_unfold, fp_assoc2_gen_correct,
    fp_add_sub_correct_unfold, fp_add_sub_correct,
    reverse_tuple_def, fp_undistribute_gen_def, fp_times_zero_def,
    fp_times_two_to_add_def, fp_times_three_to_add_def,
    fp_times_one_def,
    fp_times_minus_one_neg_def, fp_times_into_div_def, fp_sub_add_def,
    fp_same_sub_def, fp_plus_zero_def,
    fp_neg_times_minus_one_def, fp_neg_push_mul_r_def,
    fp_mul_sub_undistribute_def, fp_mul_sub_distribute_def,
    fp_mul_comm_def, fp_mul_assoc_def, fp_mul_assoc2_def,
    fp_mul_add_undistribute_def, fp_mul_add_distribute_def,
    fp_fma_intro_def, fp_div_sub_undistribute_def,
    fp_div_sub_distribute_def, fp_div_add_undistribute_def,
    fp_div_add_distribute_def, fp_distribute_gen_def, fp_comm_gen_def,
    fp_assoc_gen_def, fp_assoc2_gen_def, fp_add_sub_def,
    fp_add_comm_def, fp_add_assoc_def, fp_add_assoc2_def,
    fp_times_zero_correct, fp_same_sub_correct]
QED

Theorem optPlanner_correct_real_single:
  ∀ e st1 st2 env cfg exps r.
  is_real_id_optimise_with_plan (generate_plan_exp cfg e) st1 st2 env cfg exps r
Proof
  rpt gen_tac
  >> irule is_real_id_perform_rewrites_optimise_with_plan_lift
  >> rpt gen_tac >> strip_tac
  >> irule is_real_id_list_perform_rewrites_lift
  >> irule lift_real_id_exp_list_strong
  >> first_x_assum $ mp_then Any assume_tac generate_plan_upper_bound_rws
  >> gs[]
  >> imp_res_tac balance_expression_tree_upper_bound
  >> imp_res_tac canonicalize_upper_bound
  >> imp_res_tac apply_distributivity_upper_bound
  >> imp_res_tac peephole_optimise_upper_bound
  >> irule is_real_id_exp_weakening >> asm_exists_tac >> gs[]
  >> rpt strip_tac >> rveq
  >> gs[fp_times_two_to_add_real_id_unfold, fp_times_two_to_add_real_id,
    fp_times_three_to_add_real_id_unfold, fp_times_three_to_add_real_id,
    fp_times_one_real_id_unfold, fp_times_one_real_id,
    fp_times_minus_one_neg_real_id_unfold,
    fp_times_minus_one_neg_real_id, fp_sub_add_real_id_unfold,
    fp_sub_add_real_id, fp_plus_zero_real_id_unfold,
    fp_plus_zero_real_id, fp_neg_times_minus_one_real_id_unfold,
    fp_neg_times_minus_one_real_id, fp_neg_push_mul_r_real_id_unfold,
    fp_neg_push_mul_r_real_id, fma_intro_real_id,
    fma_intro_real_id, fp_distribute_gen_real_id_unfold,
    Q.SPECL [‘FP_Sub’, ‘FP_Mul’] fp_distribute_gen_real_id,
    Q.SPECL [‘FP_Add’, ‘FP_Div’] fp_distribute_gen_real_id,
    Q.SPECL [‘FP_Sub’, ‘FP_Div’] fp_distribute_gen_real_id,
    fp_comm_gen_real_id_unfold_mul, fp_comm_gen_real_id_unfold_add,
    Q.SPEC ‘FP_Sub’ fp_comm_gen_real_id, fp_assoc_gen_real_id_unfold_mul,
    fp_assoc_gen_real_id_unfold_add, fp_assoc_gen_real_id,
    fp_assoc2_gen_real_id_unfold_mul, fp_assoc2_gen_real_id_unfold_add,
    fp_assoc2_gen_real_id, fp_add_sub_real_id_unfold, fp_add_sub_real_id,
    reverse_tuple_def, fp_undistribute_gen_def, fp_times_zero_def,
    fp_times_two_to_add_def, fp_times_three_to_add_def,
    fp_times_one_def,
    fp_times_minus_one_neg_def, fp_times_into_div_def, fp_sub_add_def,
    fp_same_sub_def, fp_plus_zero_def,
    fp_neg_times_minus_one_def, fp_neg_push_mul_r_def,
    fp_mul_sub_undistribute_def, fp_mul_sub_distribute_def,
    fp_mul_comm_def, fp_mul_assoc_def, fp_mul_assoc2_def,
    fp_mul_add_undistribute_def, fp_mul_add_distribute_def,
    fp_fma_intro_def, fp_div_sub_undistribute_def,
    fp_div_sub_distribute_def, fp_div_add_undistribute_def,
    fp_div_add_distribute_def, fp_distribute_gen_def, fp_comm_gen_def,
    fp_assoc_gen_def, fp_assoc2_gen_def, fp_add_sub_def,
    fp_add_comm_def, fp_add_assoc_def, fp_add_assoc2_def,
    fp_times_zero_real_id, fp_same_sub_real_id]
QED

val _ = export_theory();
