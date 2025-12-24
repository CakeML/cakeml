(*
  Proves that the VCG is an implementation of the wp-calculus.
*)
Theory dafny_vcgProof
Ancestors
  result_monad
  dafny_vcg
  dafny_wp_calc
  mlint (* num_to_str_11 *)
Libs
  preamble

Theorem result_mmap_dest_VarLhs[local]:
  ∀lhss vars. result_mmap dest_VarLhs lhss = INR vars ⇒ lhss = MAP VarLhs vars
Proof
  Induct \\ simp [result_mmap_def, oneline bind_def]
  \\ Cases \\ simp [dest_VarLhs_def]
  \\ Cases \\ simp [CaseEq "sum"]
QED

Theorem result_mmap_dest_ExpRhs[local]:
  ∀lhss vars. result_mmap dest_ExpRhs lhss = INR vars ⇒ lhss = MAP ExpRhs vars
Proof
  Induct \\ simp [result_mmap_def, oneline bind_def]
  \\ Cases \\ simp [dest_ExpRhs_def]
  \\ Cases \\ simp [CaseEq "sum"]
QED

Theorem find_met_inr[local]:
  ∀methods name method.
    find_met name methods = INR method ⇒
    ∃spec body. method = Method name spec body ∧ MEM method methods
Proof
  Induct \\ simp [find_met_def]
  \\ Cases \\ simp [find_met_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ simp []
  \\ strip_tac \\ gvs []
  \\ last_x_assum drule
  \\ rpt strip_tac \\ simp []
QED

Theorem freevars_aux_list_eq[local]:
  ∀e. (set ## set) (freevars_aux_list e) = freevars_aux e
Proof
  ho_match_mp_tac freevars_aux_list_ind
  \\ rw[freevars_aux_def,freevars_aux_list_def]
  \\ rpt(pairarg_tac \\ gvs[])
  \\ fs[LIST_TO_SET_FLAT,LIST_TO_SET_FILTER,MAP_MAP_o,o_DEF,EXTENSION,MEM_MAP,PULL_EXISTS]
  \\ metis_tac[PAIR,FST,SND,PAIR_MAP_THM]
QED

Theorem freevars_list_eq[local]:
  ∀e. set (freevars_list e) = freevars e
Proof
  rw[freevars_list_def,freevars_def]>>
  metis_tac[freevars_aux_list_eq,PAIR_MAP_THM,PAIR,FST]
QED

(* TODO Move? (together with list_disjoint_def) *)
Theorem LIST_TO_SET_DISJOINT[local]:
  list_disjoint xs ys = DISJOINT (set xs) (set ys)
Proof
  simp [list_disjoint_def, list_inter_def, FILTER_EQ_NIL, EVERY_MEM]
  \\ SET_TAC []
QED

(* TODO Move? (together with list_subset_def) *)
Theorem LIST_TO_SET_SUBSET[local]:
  list_subset xs ys ⇔ (set xs) ⊆ (set ys)
Proof
  simp [dafny_vcgTheory.list_subset_def, EVERY_MEM]
  \\ SET_TAC []
QED

Theorem ALL_DISTINCT_gen_ds_vars[local]:
  ∀ds. ALL_DISTINCT (gen_ds_vars ds)
Proof
  simp [ALL_DISTINCT_GENLIST, gen_ds_vars_def, num_to_str_11]
QED

Theorem LENGTH_gen_ds_vars[local]:
  ∀ds. LENGTH (gen_ds_vars ds) = LENGTH ds
Proof
  simp [gen_ds_vars_def]
QED

Theorem LIST_TO_SET_MEM[local]:
  set xs x ⇔ MEM x xs
Proof
  Induct_on ‘xs’ \\ gvs []
QED

Theorem MEM_get_VarLhss[local]:
  MEM v (get_VarLhss lhss) ⇔ MEM (VarLhs v) lhss
Proof
  Induct_on ‘lhss’ \\ gvs [get_VarLhss_def]
  \\ Cases \\ gvs []
QED

Theorem set_find_assigned_in[local]:
  set (find_assigned_in stmt) = assigned_in stmt
Proof
  Induct_on ‘stmt’
  \\ gvs [FUN_EQ_THM] \\ rpt strip_tac
  \\ gvs [find_assigned_in_def, assigned_in_def, LIST_TO_SET_MEM, MEM_FILTER,
          MEM_get_VarLhss]
QED

Theorem stmt_vcg_correct:
  ∀m stmt post ens decs mods ls res.
    stmt_vcg m stmt (post:exp list) (ens:exp list) decs mods ls = INR res
    ⇒
    stmt_wp (set m) res stmt (post:exp list) (ens:exp list) decs mods ls
Proof
  ho_match_mp_tac stmt_vcg_ind
  \\ rpt strip_tac
  >~ [‘Skip’] >-
   (gvs [stmt_vcg_def, stmt_wp_Skip])
  >~ [‘Assert’] >-
   (gvs [stmt_vcg_def, stmt_wp_Assert])
  >~ [‘Print’] >-
   (gvs [stmt_vcg_def,assert_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ simp [stmt_wp_Print])
  >~ [‘Return’] >-
   (gvs [stmt_vcg_def, stmt_wp_Return])
  >~ [‘Then’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [CaseEq"option",CaseEq"prod"]
    >-
     (gvs [oneline bind_def, CaseEq "sum"]
      \\ irule stmt_wp_Then
      \\ last_x_assum $ irule_at (Pos last)
      \\ last_x_assum irule \\ simp [])
    \\ gvs [oneline bind_def, AllCaseEqs()]
    \\ gvs [oneline dest_ArrayAlloc_def,AllCaseEqs()]
    \\ irule stmt_wp_ArrayAlloc
    \\ fs [assert_def]
    \\ first_x_assum $ irule_at Any \\ simp [])
  >~ [‘If’] >-
   (gvs [stmt_vcg_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_If \\ simp [])
  >~ [‘Dec’] >-
   (gvs [stmt_vcg_def, assert_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_Dec
    \\ gvs [IN_DEF, freevars_list_eq])
  >~ [‘Assign ass’] >-
   (gvs [stmt_vcg_def,assert_def]
    \\ Cases_on ‘is_AssignArray ass’
    >-
     (gvs [oneline is_AssignArray_def, oneline dest_AssignArray_def,
           oneline bind_def, AllCaseEqs()]
      \\ irule stmt_wp_AssignArray \\ gvs []
      \\ first_assum $ irule_at (Pos last) \\ simp [])
    \\ gvs [UNZIP_MAP]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_Assign
    \\ imp_res_tac result_mmap_len \\ simp []
    \\ drule_then assume_tac result_mmap_dest_VarLhs \\ simp []
    \\ drule_then assume_tac result_mmap_dest_ExpRhs \\ simp []
    \\ gvs [LIST_TO_SET_SUBSET,LIST_TO_SET_DISJOINT]
    \\ fs[DISJOINT_DEF,EVERY_MEM,EXTENSION]
    \\ metis_tac[])
  >~ [‘While’] >-
   (gvs [stmt_vcg_def,assert_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ irule stmt_wp_While
    \\ gvs [LIST_TO_SET_SUBSET, set_find_assigned_in, LIST_TO_SET_DISJOINT]
    \\ CONJ_TAC >- fs[DISJOINT_DEF]
    \\ qexistsl [‘T’, ‘body_wp’, ‘gen_ds_vars ds’]
    \\ simp [ALL_DISTINCT_gen_ds_vars, LENGTH_gen_ds_vars]
    \\ gvs [LIST_TO_SET_DISJOINT, freevars_list_eq]
    \\ fs[DISJOINT_DEF])
  >~ [‘MetCall’] >-
   (gvs [stmt_vcg_def,assert_def]
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ drule find_met_inr \\ rpt strip_tac \\ gvs []
    \\ gvs [oneline bind_def, CaseEq "sum"]
    \\ drule_then assume_tac result_mmap_dest_VarLhs \\ simp []
    \\ irule $ SRULE [rich_listTheory.APPEND] stmt_wp_MetCall
    \\ simp []
    \\ gvs [LIST_TO_SET_SUBSET, LIST_TO_SET_DISJOINT, freevars_list_eq]
    \\ last_assum $ irule_at (Pos hd)
    \\ simp[]
    \\ last_assum $ irule_at Any
    \\ fs[DISJOINT_DEF,EVERY_MEM,EXTENSION]
    \\ metis_tac[])
QED

Theorem mem_wrap_Old_list_eq[local]:
  (∀e. MEM e args ⇒ wrap_Old_list vs e = wrap_Old (set vs) e) ⇒
  MAP (λa. wrap_Old_list vs a) args = MAP (λa. wrap_Old (set vs) a) args
Proof
  rpt strip_tac
  \\ simp [MAP_MAP_o, o_DEF]
  \\ irule MAP_CONG \\ gvs []
QED

Theorem wrap_Old_list_eq_aux[local]:
  ∀vs e. wrap_Old_list vs e = wrap_Old (set vs) e
Proof
  ho_match_mp_tac wrap_Old_list_ind >>
  rw[wrap_Old_list_def,wrap_Old_def,MAP_EQ_f,LIST_TO_SET_FILTER]
  >- (AP_THM_TAC>>AP_TERM_TAC>>SET_TAC[])
  >- (pairarg_tac>>gvs[]>>metis_tac[])
  >- (AP_THM_TAC>>AP_TERM_TAC>>SET_TAC[])
QED

Theorem wrap_Old_list_eq[local]:
  ∀vs. wrap_Old_list vs = wrap_Old (set vs)
Proof
  simp [FUN_EQ_THM, wrap_Old_list_eq_aux]
QED

(* TODO move to result_monad? *)
Theorem mem_result_mmap_inr:
  ∀xs x f ys.
    MEM x xs ∧ result_mmap f xs = INR ys ⇒ ∃y. f x = INR y ∧ MEM y ys
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ last_x_assum drule_all
  \\ rpt strip_tac \\ gvs []
QED

Theorem mets_vcg_correct:
  ∀mets vcs.
    mets_vcg mets = INR vcs ∧ (EVERY (λ(vs,p). forall vs p) vcs) ⇒
    proved_methods (set mets)
Proof
  rpt strip_tac
  \\ gvs [mets_vcg_def, proved_methods_def]
  \\ rpt strip_tac
  \\ drule_all mem_result_mmap_inr
  \\ strip_tac
  \\ gvs [met_vcg_def, oneline bind_def, CaseEq "sum", CaseEq "option"]
  \\ drule stmt_vcg_correct \\ gvs []
  \\ simp [wrap_Old_list_eq]
  \\ disch_then $ irule_at (Pos hd)
  \\ gvs [EVERY_MEM]
  \\ simp [GSYM freevars_list_eq]
  \\ res_tac \\ fs []
QED
