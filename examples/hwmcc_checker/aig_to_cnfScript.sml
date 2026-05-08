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

Definition negate_def:
  negate (Pos n) = Neg n ∧
  negate (Neg n) = Pos n
End

Definition imp_to_cnf_def:
  imp_to_cnf xs y = y :: MAP negate xs
End

Definition eq_every_to_cnf_def:
  eq_every_to_cnf x xs = (x::MAP negate xs)::MAP (λy. [y; negate x]) xs
End

Theorem eq_every_to_cnf_eq:
  eq_every_to_cnf x xs =
    imp_to_cnf xs x :: MAP (λy. imp_to_cnf [x] y) xs
Proof
  simp [imp_to_cnf_def, eq_every_to_cnf_def]
QED

Theorem satisfies_cnf_INSERT:
  satisfies_cnf w (x INSERT s) ⇔
  satisfies_clause w x ∧ satisfies_cnf w s
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, SF DNF_ss]
QED

Theorem satisfies_cnf_set:
  satisfies_cnf w (set xs) = EVERY (satisfies_clause w) xs
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, EVERY_MEM]
QED

Theorem satisfies_lit_negate:
  satisfies_lit w (negate y) = ~ satisfies_lit w y
Proof
  Cases_on ‘y’ \\ gvs [negate_def, satisfies_lit_def]
QED

Theorem satisfies_clause_imp_to_cnf:
  satisfies_clause w (imp_to_cnf xs y) ⇔
  (EVERY (satisfies_lit w) xs ⇒ satisfies_lit w y)
Proof
  fs [satisfies_clause_def, imp_to_cnf_def]
  \\ gvs [MEM_MAP,PULL_EXISTS, SF DNF_ss, satisfies_lit_negate]
  \\ Cases_on ‘satisfies_lit w y’ \\ simp []
  \\ fs [EXISTS_MEM]
QED

Theorem eq_every_to_cnf_thm:
  satisfies_cnf w (set (eq_every_to_cnf x xs)) =
  (satisfies_lit w x = EVERY (satisfies_lit w) xs)
Proof
  simp [eq_every_to_cnf_eq]
  \\ once_rewrite_tac [satisfies_cnf_INSERT]
  \\ simp [satisfies_cnf_set, EVERY_MAP]
  \\ simp [satisfies_clause_imp_to_cnf]
  \\ Cases_on ‘satisfies_lit w x’ \\ fs [SF ETA_ss]
QED

Definition not_TT_def:
  not_TT (Base Ff, T) = F ∧
  not_TT _ = T
End

Definition var_to_name_def:
  var_to_name (Name n) = 3 * n:num ∧
  var_to_name (Base (Input i)) = 3 * i + 1 ∧
  var_to_name (Base (Latch l)) = 3 * l + 2 ∧
  var_to_name _ = 0
End

Definition var_to_lit_def:
  var_to_lit (v,F) = Pos (var_to_name v) ∧
  var_to_lit (v,T) = Neg (var_to_name v)
End

Definition and_to_cnf_def:
  and_to_cnf n (ys : (num, num, num) aig$lit list) =
    if MEM (Base Ff, F) ys then
      [[Neg (3 * n:num)]]
    else
      eq_every_to_cnf (Pos (3 * n:num))
        (MAP var_to_lit (FILTER not_TT ys))
End

Definition to_cnf_def:
  to_cnf ([] : (num,num,num) and list) acc = (acc : num lit list list) ∧
  to_cnf ((n,ys)::xs) acc = to_cnf xs (and_to_cnf n ys ++ acc)
End

Definition direct_circuit_to_cnf_def:
  direct_circuit_to_cnf (ands : (num,num,num) and list) name =
    if NULL ands then [[]] else
      ([Pos (3 * name)] :: to_cnf ands []) : num lit list list
End

Definition circuit_to_cnf_def:
  circuit_to_cnf ands name =
    set (circuit_to_cnf_list ands name)
End

Definition get_is_def:
  get_is w n = w (3 * n + 1:num) : bool
End

Definition get_ls_def:
  get_ls w n = w (3 * n + 2:num) : bool
End

Definition eval_circuits_def:
  (eval_circuits (is,ls) [] w ⇔ T) ∧
  (eval_circuits (is,ls) ((k,ts)::rest) w ⇔
     (w (3 * k) = eval_circuit (is,ls) ((k,ts)::rest) k) ∧
     eval_circuits (is,ls) rest w)
End

Theorem to_cnf_acc:
  ∀ands acc. set (to_cnf ands acc) = set (to_cnf ands []) ∪ set acc
Proof
  Induct
  >- (once_rewrite_tac [to_cnf_def] \\ simp [])
  \\ PairCases
  \\ once_rewrite_tac [to_cnf_def]
  \\ pop_assum $ once_rewrite_tac o single
  \\ fs [AC UNION_ASSOC UNION_COMM]
QED

Theorem satisfies_cnf_UNION_IMP:
  satisfies_cnf w (x ∪ y) ⇒
  satisfies_cnf w x ∧ satisfies_cnf w y
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def]
QED

Theorem IMP_satisfies_cnf_UNION:
  satisfies_cnf w x ∧ satisfies_cnf w y ⇒
  satisfies_cnf w (x ∪ y)
Proof
  fs [satisfies_cnf_def, satisfies_fml_gen_def, SF DNF_ss]
QED

Theorem to_filter:
  ∀xs.
    EVERY (eval_lit (is,ls) ands) xs =
    EVERY (eval_lit (is,ls) ands) (FILTER not_TT xs)
Proof
  Induct \\ rw []
  \\ Cases_on ‘h’ \\ fs [not_TT_def]
  \\ Cases_on ‘q’ \\ fs [not_TT_def]
  \\ Cases_on ‘b’ \\ fs [not_TT_def]
  \\ Cases_on ‘r’ \\ fs [not_TT_def]
  \\ simp [eval_circuit_def]
QED

Definition closed_def:
  closed ([] :('a,'i,'l) and list) = T ∧
  closed ((n,ts)::rest) =
    (closed rest ∧
     ∀m b. MEM (Name m, b) ts ⇒ ALOOKUP rest m ≠ NONE)
End

Theorem eval_circuits_ALOOKUP:
  ∀ands a.
    eval_circuits (get_is w,get_ls w) ands w ∧
    ALOOKUP ands a ≠ NONE ⇒
    (w (3 * a) ⇔ eval_circuit (get_is w,get_ls w) ands a)
Proof
  Induct \\ simp [ALOOKUP_def]
  \\ PairCases \\ simp [ALOOKUP_def] \\ rw []
  \\ Cases_on ‘h0 = a’ \\ gvs [eval_circuits_def]
  \\ gvs [eval_circuit_def]
QED

Theorem satisfies_cnf_IMP:
  ∀ands w.
    satisfies_cnf w (set (to_cnf ands [])) ∧ closed ands ⇒
    eval_circuits (get_is w, get_ls w) ands w
Proof
  Induct
  \\ simp [eval_circuits_def]
  \\ PairCases \\ fs [closed_def]
  \\ simp [eval_circuits_def, to_cnf_def]
  \\ simp [Once to_cnf_acc]
  \\ rpt gen_tac
  \\ strip_tac
  \\ simp [eval_circuit_def]
  \\ dxrule satisfies_cnf_UNION_IMP \\ strip_tac
  \\ last_x_assum drule_all \\ strip_tac
  \\ simp []
  \\ fs [and_to_cnf_def]
  \\ Cases_on ‘MEM FF h1’ \\ fs []
  >-
   (gvs [satisfies_cnf_def, satisfies_fml_gen_def,
         satisfies_clause_def, satisfies_lit_def, EXISTS_MEM]
    \\ first_x_assum $ irule_at Any
    \\ gvs [eval_circuit_def])
  \\ fs [eq_every_to_cnf_thm, satisfies_lit_def, SF ETA_ss]
  \\ simp [Once to_filter]
  \\ simp [EVERY_MAP]
  \\ irule EVERY_EQ_EVERY
  \\ simp [EVERY_MEM, MEM_FILTER] \\ rw []
  \\ rename [‘not_TT z’]
  \\ PairCases_on ‘z’ \\ fs []
  \\ Cases_on ‘z1’ \\ fs []
  \\ Cases_on ‘z0’ \\ fs []
  \\ TRY (rename [‘Base b’] \\ Cases_on ‘b’ \\ fs [])
  \\ gvs [var_to_lit_def, satisfies_lit_def, var_to_name_def, not_TT_def]
  \\ gvs [eval_circuit_def, eval_bvar_def, get_is_def, get_ls_def]
  \\ last_x_assum drule
  \\ strip_tac
  \\ drule_all eval_circuits_ALOOKUP
  \\ rewrite_tac []
QED

Definition find_suffix_def:
  find_suffix n [] = NONE ∧
  find_suffix n ((k,xs)::rest) =
    if k = n then SOME ((k,xs)::rest) else find_suffix n rest
End

Definition cnf_witness_def:
  cnf_witness is ls ands n =
    if n MOD 3 = 1 then is (n DIV 3) else
    if n MOD 3 = 2 then ls (n DIV 3) else
      case find_suffix (n DIV 3) ands of
      | NONE => F
      | SOME rest => eval_circuit (is,ls) rest (n DIV 3)
End

Theorem find_suffix_fast_forward:
  ∀past.
    ALL_DISTINCT (MAP FST past ++ h0::rest) ⇒
    find_suffix h0 (past ++ (h0,h1)::ands) = SOME ((h0,h1)::ands)
Proof
  Induct \\ fs [find_suffix_def, FORALL_PROD]
QED

Theorem eval_circuit_drop:
  ∀l1 a.
    ~ MEM a (MAP FST l1) ⇒
    eval_circuit (is,ls) (l1 ++ l2) a =
    eval_circuit (is,ls) l2 a
Proof
  Induct \\ fs [eval_circuit_def, FORALL_PROD]
QED

Theorem eval_circuit_IMP_cnf_lemma:
  ∀ands past.
    closed ands ∧
    ALL_DISTINCT (MAP FST (past ++ ands)) ⇒
    satisfies_cnf (cnf_witness is ls (past ++ ands)) (set (to_cnf ands []))
Proof
  Induct \\ simp [Once to_cnf_def]
  >- simp [satisfies_cnf_def, satisfies_fml_gen_def]
  \\ PairCases \\ fs [closed_def]
  \\ strip_tac
  \\ simp [Once to_cnf_def]
  \\ simp [Once to_cnf_acc]
  \\ rpt strip_tac
  \\ irule IMP_satisfies_cnf_UNION
  \\ conj_tac
  >- (last_x_assum $ qspec_then ‘past ++ [(h0,h1)]’ mp_tac
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP])
  \\ fs [and_to_cnf_def] \\ rw []
  >-
   (gvs [satisfies_cnf_def, satisfies_fml_gen_def,
         satisfies_clause_def, satisfies_lit_def, EXISTS_MEM]
    \\ fs [cnf_witness_def]
    \\ drule find_suffix_fast_forward \\ fs [] \\ rw []
    \\ fs [eval_circuit_def]
    \\ simp [EXISTS_MEM]
    \\ first_x_assum $ irule_at Any
    \\ fs [eval_circuit_def])
  \\ fs [eq_every_to_cnf_thm, satisfies_lit_def, SF ETA_ss]
  \\ fs [cnf_witness_def]
  \\ drule find_suffix_fast_forward \\ fs [] \\ rw []
  \\ simp [eval_circuit_def, SF ETA_ss]
  \\ simp [Once to_filter]
  \\ simp [EVERY_MAP]
  \\ irule EVERY_EQ_EVERY
  \\ simp [EVERY_MEM, MEM_FILTER] \\ rw []
  \\ rename [‘not_TT z’]
  \\ PairCases_on ‘z’ \\ fs []
  \\ reverse $ Cases_on ‘z0’ \\ fs []
  >-
   (rename [‘Base b’] \\ Cases_on ‘b’ \\ fs []
    \\ Cases_on ‘z1’ \\ fs [not_TT_def]
    \\ simp [var_to_lit_def, var_to_name_def, eval_circuit_def,
             satisfies_lit_def, cnf_witness_def])
  \\ Cases_on ‘z1’
  \\ gvs [var_to_lit_def, satisfies_lit_def, var_to_name_def]
  \\ gvs [eval_circuit_def, eval_bvar_def, get_is_def, get_ls_def, cnf_witness_def]
  \\ res_tac
  \\ Cases_on ‘ALOOKUP ands a’ \\ fs []
  \\ dxrule ALOOKUP_MEM
  \\ simp [MEM_SPLIT]
  \\ strip_tac \\ gvs []
  \\ ‘ALL_DISTINCT (MAP FST (past ++ (h0,h1)::l1) ++ a :: MAP FST l2)’ by
    full_simp_tac std_ss [MAP_APPEND, MAP, GSYM APPEND_ASSOC, APPEND]
  \\ drule find_suffix_fast_forward
  \\ simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
  \\ rw []
  \\ irule eval_circuit_drop
  \\ fs [ALL_DISTINCT_APPEND]
  \\ metis_tac []
QED

Theorem eval_circuit_IMP_cnf:
  closed ands ∧ ALL_DISTINCT (MAP FST ands) ⇒
  satisfies_cnf (cnf_witness is ls ands) (set (to_cnf ands []))
Proof
  qspecl_then [‘ands’,‘[]’] mp_tac eval_circuit_IMP_cnf_lemma \\ fs []
QED

Theorem direct_circuit_to_cnf_correct:
  ALL_DISTINCT (MAP FST ands) ∧ closed ands ∧
  (~NULL ands ⇒ FST (HD ands) = name) ⇒
  (satisfiable_cnf (set (direct_circuit_to_cnf ands name)) =
   ∃is ls. eval_circuit (is,ls) ands name)
Proof
  rw [satisfiable_cnf_def] \\ eq_tac \\ strip_tac
  >-
   (qexists ‘get_is w’ \\ qexists ‘get_ls w’
    \\ fs [direct_circuit_to_cnf_def]
    \\ pop_assum mp_tac
    \\ Cases_on ‘NULL ands’
    >- (rw [] \\ gvs []
        \\ fs [satisfies_cnf_def, satisfies_fml_gen_def, satisfies_clause_def])
    \\ simp []
    \\ once_rewrite_tac [satisfies_cnf_INSERT]
    \\ rw [satisfies_clause_def, satisfies_lit_def]
    \\ drule_all satisfies_cnf_IMP
    \\ Cases_on ‘ands’ \\ gvs []
    \\ PairCases_on ‘h’
    \\ gvs [eval_circuits_def])
  \\ qexists ‘cnf_witness is ls ands’
  \\ simp [direct_circuit_to_cnf_def]
  \\ IF_CASES_TAC \\ simp [] >- gvs [NULL_EQ]
  \\ once_rewrite_tac [satisfies_cnf_INSERT]
  \\ conj_tac
  >-
   (simp [satisfies_clause_def, satisfies_lit_def]
    \\ simp [cnf_witness_def]
    \\ qsuff_tac ‘find_suffix name ands = SOME ands’ >- simp []
    \\ Cases_on ‘ands’ \\ gvs [] \\ PairCases_on ‘h’ \\ fs []
    \\ fs [find_suffix_def])
  \\ drule_all eval_circuit_IMP_cnf \\ simp []
QED
