(*
  Correctness proof for the Dafny compiler with all of its passes.
*)

open preamble
open dafny_semanticPrimitivesTheory
open dafny_freshenTheory
open dafny_freshenProofTheory
open dafny_to_cakemlTheory
open dafny_to_cakemlProofTheory
open dafny_compilerTheory
open mlstringTheory  (* isPrefix *)

val _ = new_theory "dafny_compilerProof";
val _ = set_grammar_ancestry
          ["dafny_semanticPrimitives", "dafny_freshen", "dafny_freshenProof",
           "dafny_to_cakeml", "dafny_to_cakemlProof", "dafny_compiler",
           "mlstring"];

(* TODO Upstream? *)
Triviality UNZIP_LENGTH:
  ∀xs ys zs. UNZIP xs = (ys, zs) ⇒ LENGTH ys = LENGTH zs
Proof
  Induct \\ gvs []
QED

(* TODO Upstream? *)
Triviality UNZIP_EQ_NIL:
  (UNZIP l = (xs, []) ⇔ l = [] ∧ xs = []) ∧
  (UNZIP l = ([], ys) ⇔ l = [] ∧ ys = [])
Proof
  Cases_on ‘l’ \\ gvs []
QED

(* TODO Upstream? *) (* by magnus *)
Theorem exists_mlstring:
  (∃x:mlstring. P x) ⇔ (∃s. P (strlit s))
Proof
  eq_tac \\ rw []
  >- (Cases_on ‘x’ \\ gvs [] \\ pop_assum $ irule_at Any)
  \\ pop_assum $ irule_at Any
QED

(* TODO Upstream? *)
Theorem isprefix_strcat:
  ∀s₁ s₂. isPrefix s₁ s₂ = ∃s₃. s₂ = s₁ ^ s₃
Proof
  rpt gen_tac
  \\ gvs [isprefix_thm, strcat_thm, isPREFIX_STRCAT, exists_mlstring,
          implode_def]
  \\ Cases_on ‘s₂’ \\ simp []
QED

(* TODO Move is_fresh properties to to separate file? *)

(* ** *)
(* TODO Already exists in freshenProof; make it Theorem *)
Triviality map_add_fresh_exists:
  ∀m cnt ns cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ⇒
    ∃m₁. m' = m₁ ++ m ∧ MAP FST m₁ = REVERSE ns
Proof
  Induct_on ‘ns’ \\ rpt strip_tac
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ last_x_assum drule_all \\ rpt strip_tac \\ gvs []
QED

(* TODO Already exists in freshenProof; make it Theorem *)
Triviality lookup_append_eq:
  ∀n m₁ m₀.
    MEM n (MAP FST m₁) ⇒ lookup (m₁ ++ m₀) n = lookup m₁ n
Proof
  rpt strip_tac
  \\ gvs [lookup_def, ALOOKUP_APPEND]
  \\ Cases_on ‘ALOOKUP m₁ n’
  \\ gvs [ALOOKUP_NONE]
QED

(* TODO Already exists in freshenProof; make it Theorem *)
Triviality freshen_rhs_exp_len_eq:
  ∀m cnt rhss cnt' rhss'.
    freshen_rhs_exps m cnt rhss = (cnt', rhss') ⇒
    LENGTH rhss' = LENGTH rhss
Proof
  Induct_on ‘rhss’ \\ rpt strip_tac
  \\ gvs [freshen_rhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ res_tac
QED

(* TODO Already exists in freshenProof; make it Theorem *)
Triviality freshen_lhs_exp_len_eq:
  ∀m cnt lhss cnt' lhss'.
    freshen_lhs_exps m cnt lhss = (cnt', lhss') ⇒
    LENGTH lhss' = LENGTH lhss
Proof
  Induct_on ‘lhss’ \\ rpt strip_tac
  \\ gvs [freshen_lhs_exps_def]
  \\ rpt (pairarg_tac \\ gvs[])
  \\ res_tac
QED

(* ** *)

Triviality map_add_fresh_every_is_fresh:
  ∀ns m cnt cnt' m'.
    map_add_fresh m cnt ns = (cnt', m') ∧
    ALL_DISTINCT ns ⇒
    EVERY (λn. is_fresh n) (MAP (lookup m') ns)
Proof
  Induct \\ simp []
  \\ qx_gen_tac ‘n’ \\ rpt strip_tac
  >-
   (drule map_add_fresh_exists
    \\ rpt strip_tac \\ gvs []
    \\ ‘MEM n (MAP FST m₁)’ by gvs []
    \\ drule lookup_append_eq \\ simp []
    \\ disch_then kall_tac
    \\ simp [lookup_def]
    \\ CASE_TAC
    >- (gvs [ALOOKUP_NONE])
    \\ simp [is_fresh_def, isprefix_strcat])
  \\ gvs [map_add_fresh_def, add_fresh_def]
  \\ last_assum irule
  \\ last_assum $ irule_at Any
QED

Triviality add_fresh_is_fresh:
  add_fresh m cnt v = (cnt', m') ⇒ is_fresh (lookup m' v)
Proof
  disch_tac \\ gvs [add_fresh_def, lookup_def, is_fresh_def, isprefix_strcat]
QED

Definition get_param_names_def[simp]:
  get_param_names (Method _ ins _ _ _ _ outs _ _) =
    MAP FST ins ++ MAP FST outs ∧
  get_param_names (Function _ ins _ _ _ _ _) = MAP FST ins
End

Triviality freshen_exp_is_fresh:
  (∀m cnt e cnt' e'.
     freshen_exp m cnt e = (cnt', e') ⇒ is_fresh_exp e') ∧
  (∀m cnt es cnt' es'.
     freshen_exps m cnt es = (cnt', es') ⇒
     EVERY (λe. is_fresh_exp e) es')
Proof
  ho_match_mp_tac freshen_exp_ind
  \\ rpt strip_tac
  >~ [‘Var v’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gvs [is_fresh_def, lookup_def]
    \\ CASE_TAC >- (simp [isprefix_thm])
    \\ simp [isprefix_strcat])
  >~ [‘Forall (v,ty) e’] >-
   (gvs [freshen_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac add_fresh_is_fresh)
  \\ gvs [freshen_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality freshen_lhs_exp_is_fresh:
  freshen_lhs_exp m cnt lhs = (cnt', lhs') ⇒ is_fresh_lhs_exp lhs'
Proof
  Cases_on ‘lhs’
  >~ [‘VarLhs var’] >-
   (rpt strip_tac
    \\ gvs [is_fresh_lhs_exp, freshen_lhs_exp_def, lookup_def, is_fresh_def]
    \\ CASE_TAC >- simp [isprefix_thm]
    \\ simp [isprefix_strcat])
  >~ [‘ArrSelLhs arr idx’] >-
   (rpt strip_tac
    \\ gvs [freshen_lhs_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp [])
QED

Triviality freshen_lhs_exps_is_fresh:
  ∀lhss m cnt cnt' lhss'.
    freshen_lhs_exps m cnt lhss = (cnt', lhss') ⇒
    EVERY (λe. is_fresh_lhs_exp e) lhss'
Proof
  Induct \\ simp [freshen_lhs_exps_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_lhs_exp_is_fresh \\ simp []
  \\ res_tac
QED

Triviality freshen_rhs_exp_is_fresh:
  freshen_rhs_exp m cnt rhs = (cnt', rhs') ⇒ is_fresh_rhs_exp rhs'
Proof
  Cases_on ‘rhs’
  >~ [‘ExpRhs e’] >-
   (simp [freshen_rhs_exp_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh))
  >~ [‘ArrAlloc len init’] >-
   (simp [freshen_rhs_exp_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp [])
QED

Triviality freshen_rhs_exps_is_fresh:
  ∀rhss m cnt cnt' rhss'.
    freshen_rhs_exps m cnt rhss = (cnt', rhss') ⇒
    EVERY (λe. is_fresh_rhs_exp e) rhss'
Proof
  Induct \\ simp [freshen_rhs_exps_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac freshen_rhs_exp_is_fresh \\ simp []
  \\ res_tac
QED

Triviality freshen_stmt_is_fresh:
  ∀stmt m cnt cnt' stmt'.
    freshen_stmt m cnt stmt = (cnt', stmt') ⇒ is_fresh_stmt stmt'
Proof
  Induct \\ rpt gen_tac
  >~ [‘MetCall lhss name args’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_lhs_exps_is_fresh \\ simp []
    \\ imp_res_tac (cj 2 freshen_exp_is_fresh))
  >~ [‘Dec local scope’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac add_fresh_is_fresh \\ simp []
    \\ res_tac)
  >~ [‘Then stmt₀ stmt₁’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ res_tac \\ simp [])
  >~ [‘If tst thn els’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac (cj 1 freshen_exp_is_fresh) \\ simp []
    \\ res_tac \\ simp [])
  >~ [‘Assign ass’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ EVERY (map imp_res_tac
               [freshen_rhs_exp_len_eq, freshen_lhs_exp_len_eq,
                freshen_rhs_exps_is_fresh, freshen_lhs_exps_is_fresh])
    \\ simp [MAP_ZIP])
  >~ [‘While grd invs decrs mods body’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ EVERY (map imp_res_tac (CONJUNCTS freshen_exp_is_fresh))
    \\ simp [] \\ res_tac)
  >~ [‘Print e ty’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_is_fresh)
  >~ [‘Assert e’] >-
   (simp [freshen_stmt_def]
    \\ rpt strip_tac
    \\ rpt (pairarg_tac \\ gvs [])
    \\ imp_res_tac freshen_exp_is_fresh)
  (* Return, Skip *)
  \\ simp [freshen_stmt_def]
QED

Triviality freshen_member_is_fresh:
  ALL_DISTINCT (get_param_names member) ⇒
  is_fresh_member (freshen_member member)
Proof
  disch_tac
  \\ namedCases_on ‘member’
       ["name ins reqs ens rds decrs outs mods body",
        "name ins res_t reqs rds decrs body"]
  \\ gvs [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ EVERY (map imp_res_tac
               ((CONJUNCTS freshen_exp_is_fresh) @
                [UNZIP_LENGTH, map_add_fresh_every_is_fresh,
                 freshen_stmt_is_fresh]))
  \\ gvs [MAP_ZIP, UNZIP_MAP, ALL_DISTINCT_APPEND]
QED

Triviality map_freshen_member_is_fresh:
  EVERY (λmember. ALL_DISTINCT (get_param_names member)) members ⇒
  EVERY is_fresh_member (MAP freshen_member members)
Proof
  Induct_on ‘members’ \\ simp []
  \\ rpt strip_tac
  \\ irule freshen_member_is_fresh \\ simp []
QED

(* *** *)

Triviality has_main_freshen:
  has_main (Program (MAP freshen_member members)) =
  has_main (Program members)
Proof
  Induct_on ‘members’ \\ simp []
  \\ qx_gen_tac ‘member’
  \\ gvs [has_main_def, get_member_def, get_member_aux_def]
  \\ Cases_on ‘member’ \\ simp [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac UNZIP_LENGTH
  \\ IF_CASES_TAC \\ gvs []
  \\ eq_tac
  \\ rpt strip_tac
  \\ gvs [ZIP_EQ_NIL, UNZIP_EQ_NIL]
QED

Definition valid_members_def:
  valid_members (Program members) =
  EVERY (λmember. ALL_DISTINCT (get_param_names member)) members
End

Theorem correct_compile:
  ∀dfy_ck prog s' r_dfy cml_decs env_cml (t: 'ffi cml_state).
    evaluate_program dfy_ck T prog = (s', r_dfy) ∧
    compile prog = INR cml_decs ∧
    has_main prog ∧ valid_members prog ∧ has_basic_cons env_cml ∧
    0 < dfy_ck ∧ t.clock = dfy_ck ∧ ExnStamp t.next_exn_stamp = ret_stamp ∧
    r_dfy ≠ Rstop (Serr Rtype_error) ⇒
    ∃ck t' m' r_cml.
      evaluate_decs (t with clock := t.clock + ck) env_cml cml_decs =
        (t', r_cml) ∧
      state_rel m' FEMPTY s' t' env_cml ∧ stmt_res_rel r_dfy r_cml
Proof
  rpt strip_tac
  \\ irule correct_from_program
  \\ fs [compile_def]
  \\ last_assum $ irule_at (Pos last)
  \\ irule_at (Pos last) correct_freshen_program \\ simp []
  \\ namedCases_on ‘prog’ ["members"]
  \\ simp [valid_prog_def, freshen_program_def, has_main_freshen]
  \\ irule_at (Pos hd) map_freshen_member_is_fresh
  \\ conj_tac >- (fs [valid_members_def])

  \\ cheat
QED


val _ = export_theory ();
