(*
  Common lemmas that probably should be upstreamed.
*)

open preamble
open mlstringTheory

val _ = new_theory "daniel";

(* TODO Upstream? *)
Theorem UNZIP_LENGTH:
  ∀xs ys zs. UNZIP xs = (ys, zs) ⇒ LENGTH ys = LENGTH zs
Proof
  Induct \\ gvs []
QED

(* TODO Upstream? *)
Theorem UNZIP_EQ_NIL:
  (UNZIP l = (xs, []) ⇔ l = [] ∧ xs = []) ∧
  (UNZIP l = ([], ys) ⇔ l = [] ∧ ys = [])
Proof
  Cases_on ‘l’ \\ gvs []
QED

(* TODO Upstream? *) (* by Magnus *)
Theorem exists_mlstring:
  (∃x:mlstring. P x) ⇔ (∃s. P (strlit s))
Proof
  eq_tac \\ rw []
  >- (Cases_on ‘x’ \\ gvs [] \\ pop_assum $ irule_at Any)
  \\ pop_assum $ irule_at Any
QED

(* TODO Move to mlstring *)
Triviality isprefix_thm_aux:
  ∀ys xs zs.
    LENGTH ys ≤ LENGTH zs ⇒
    (isStringThere_aux (strlit (xs ++ ys)) (strlit (xs ++ zs))
       (LENGTH xs) (LENGTH xs) (LENGTH ys) ⇔
       ys ≼ zs)
Proof
  Induct \\ gvs [isStringThere_aux_def]
  \\ rpt strip_tac
  \\ Cases_on ‘zs’ \\ gvs []
  \\ rename [‘_ = h' ∧ _ ≼ zs’]
  \\ gvs [EL_APPEND]
  \\ last_x_assum $ qspecl_then [‘xs ++ [h]’, ‘zs’] mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
  \\ gvs [] \\ metis_tac []
QED

(* TODO Move to mlstring *)
Theorem isprefix_thm:
  isPrefix s₁ s₂ ⇔ explode s₁ ≼ explode s₂
Proof
  namedCases_on ‘s₁’ ["s"]
  \\ namedCases_on ‘s₂’ ["t"]
  \\ gvs [isPrefix_def]
  \\ Cases_on ‘LENGTH s ≤ LENGTH t’ \\ gvs []
  >- (qspecl_then [‘s’, ‘[]’, ‘t’] mp_tac isprefix_thm_aux \\ gvs [])
  \\ strip_tac \\ imp_res_tac IS_PREFIX_LENGTH
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

val _ = export_theory ();
