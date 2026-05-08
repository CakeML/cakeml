(*
  Mapping And-Inverter Graphs into CNF
*)
Theory aig_to_cnf
Ancestors
  misc mlstring aig cnf
Libs
  preamble

Definition new_live_def:
  new_live ([] : (('a,'i,'l) var # bool) list) l = (l:'a |-> unit) ∧
  new_live ((x,b) :: xs) l =
    case x of
    | Name n => new_live xs l |+ (n,())
    | Base _ => new_live xs l
End

Definition prune_def:
  prune ([]:('a,'i,'l) and list) (live :'a |-> unit) = [] ∧
  prune ((m,ts)::xs) live =
    case FLOOKUP live m of
    | NONE => (m,ts) :: prune xs live
    | _ =>
        let live' = live \\ m in
          (m,ts) :: prune xs (new_live ts live')
End

Definition prune_for_def:
  prune_for name ands = prune ands (FEMPTY |+ (name,()))
End

Theorem EVERY_EQ_EVERY[local]:
  EVERY (λx. P x = Q x) xs ⇒ (EVERY P xs = EVERY Q xs)
Proof
  Induct_on ‘xs’\\ fs []
QED

Theorem new_live_thm:
  ∀h1 live aa.
    MEM (Name aa,r) h1 ⇒
    FLOOKUP (new_live h1 live) aa = SOME ()
Proof
  Induct
  \\ fs [new_live_def,FORALL_PROD]
  \\ Cases \\ fs []
  \\ rw [] \\ rw [FLOOKUP_SIMP]
QED

Theorem new_live_pres[local]:
  ∀xs live name.
    FLOOKUP live name = SOME () ⇒
    FLOOKUP (new_live xs live) name = SOME ()
Proof
  Induct \\ simp [new_live_def, FORALL_PROD]
  \\ Cases \\ simp [new_live_def, FORALL_PROD]
  \\ rw [] \\ rw [FLOOKUP_SIMP]
QED

Theorem eval_circuit_prune:
  ∀ands name live x.
    FLOOKUP live name = SOME x ⇒
    eval_circuit (is,ls) ands name =
    eval_circuit (is,ls) (prune ands live) name
Proof
  Induct
  \\ fs [eval_circuit_def,prune_def]
  \\ PairCases \\ simp []
  \\ rw [prune_def]
  >-
   (simp [eval_circuit_def]
    \\ irule EVERY_EQ_EVERY
    \\ simp [EVERY_MEM]
    \\ Cases \\ Cases_on ‘q’
    \\ simp [eval_circuit_def]
    \\ rename [‘Name aa’]
    \\ strip_tac
    \\ first_x_assum $ qspecl_then [‘aa’,‘new_live h1 (live \\ h0)’] mp_tac
    \\ reverse impl_tac >- simp []
    \\ irule new_live_thm
    \\ simp [new_live_thm]
    \\ pop_assum $ irule_at Any)
  \\ CASE_TAC
  \\ simp [eval_circuit_def]
  \\ last_x_assum irule
  \\ irule new_live_pres
  \\ rw [] \\ fs [FLOOKUP_DEF]
QED

Theorem eval_circuit_prune_for:
  eval_circuit (is,ls) (prune_for name ands) name =
  eval_circuit (is,ls) ands name
Proof
  simp [Once EQ_SYM_EQ, prune_for_def]
  \\ irule eval_circuit_prune
  \\ simp [FLOOKUP_SIMP]
QED

Definition circuit_to_cnf_list_def:
  circuit_to_cnf_list (ands : ('a,'i,'l) and list) name =
    let ands = prune_for name ands in
      []
End

Definition circuit_to_cnf_def:
  circuit_to_cnf ands name =
    set (circuit_to_cnf_list ands name)
End

Theorem circuit_to_cnf_correct:
  satisfiable_cnf (circuit_to_cnf ands name) =
  ∃is ls. eval_circuit (is,ls) ands name
Proof
  cheat
QED

(*




*)

(*
  eval_bvar_def
  eval_circuit_def
*)

(*
  satisfies_literal_def
  satisfies_clause_def
  satisfies_def
  satisfiable_def
*)
