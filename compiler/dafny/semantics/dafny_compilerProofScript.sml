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

(* by magnus *)
Theorem exists_mlstring:
  (∃x:mlstring. P x) ⇔ (∃s. P (strlit s))
Proof
  eq_tac \\ rw []
  >- (Cases_on ‘x’ \\ gvs [] \\ pop_assum $ irule_at Any)
  \\ pop_assum $ irule_at Any
QED

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

Triviality lookup_append_eq:
  ∀n m₁ m₀.
    MEM n (MAP FST m₁) ⇒ lookup (m₁ ++ m₀) n = lookup m₁ n
Proof
  rpt strip_tac
  \\ gvs [lookup_def, ALOOKUP_APPEND]
  \\ Cases_on ‘ALOOKUP m₁ n’
  \\ gvs [ALOOKUP_NONE]
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

Triviality freshen_member_is_fresh:
  freshen_member member = fresh_member ⇒ is_fresh_member fresh_member
Proof
  disch_tac
  \\ Cases_on ‘member’
  \\ gvs [freshen_member_def]
  \\ rpt (pairarg_tac \\ gvs [])
  >-
   (imp_res_tac UNZIP_LENGTH
    \\ simp [MAP_ZIP]
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

Theorem correct_compile:
  ∀dfy_ck prog s' r_dfy cml_decs env_cml (t: 'ffi cml_state).
    evaluate_program dfy_ck T prog = (s', r_dfy) ∧
    compile prog = INR cml_decs ∧
    has_main prog ∧ has_basic_cons env_cml ∧
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

  \\ cheat
QED


val _ = export_theory ();
