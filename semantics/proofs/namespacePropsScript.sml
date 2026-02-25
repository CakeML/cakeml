(*
  Proofs about the namespace datatype.
*)
Theory namespaceProps
Ancestors
  ast namespace
Libs
  preamble

Theorem mk_id_11[simp]:
   !a b c d. mk_id a b = mk_id c d ⇔ (a = c) ∧ (b = d)
Proof
 Induct_on `a`
 >> Cases_on `c`
 >> rw [mk_id_def]
 >> metis_tac []
QED

Theorem id_to_mods_mk_id[simp]:
   !mn x. id_to_mods (mk_id mn x) = mn
Proof
 Induct_on `mn`
 >> rw [id_to_mods_def, mk_id_def]
QED

Theorem id_to_namemods_mk_id[simp]:
   !mn x. id_to_n (mk_id mn x) = x
Proof
 Induct_on `mn`
 >> rw [id_to_n_def, mk_id_def]
QED

Theorem mk_id_surj:
   !id. ?p n. id = mk_id p n
Proof
 Induct_on `id`
 >> rw []
 >> metis_tac [mk_id_def]
QED

Theorem mk_id_thm:
   !id. mk_id (id_to_mods id) (id_to_n id) = id
Proof
 Induct_on `id`
 >> rw [id_to_mods_def, id_to_n_def, mk_id_def]
QED

(* ----------- Monotonicity for ind rel ------------ *)

Theorem nsAll_mono[mono]:
   (!id x. P id x ⇒ Q id x) ⇒ nsAll P e ⇒ nsAll Q e
Proof
  rw [nsAll_def]
QED

Theorem nsSub_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
Proof
 Cases_on `e1`
 >> Cases_on `e2`
 >> simp [nsSub_def, nsLookup_def]
 >> rw []
 >> metis_tac []
QED

Theorem nsSub_mono2:
   (!x y z. nsLookup e1 x = SOME y ∧ nsLookup e2 x = SOME z ∧ R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2)
Proof
 Cases_on `e1`
 >> Cases_on `e2`
 >> simp [nsSub_def, nsLookup_def]
 >> rw []
 >> metis_tac []
QED

Theorem nsAll2_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2
Proof
 rw [nsAll2_def]
 >> irule nsSub_mono
 >> rw []
 >- metis_tac []
 >> qexists_tac `\x y z. R1 x z y`
 >> rw []
QED

(* ---------- Automatic simps involving empty envs -------------- *)

Theorem nsLookup_nsEmpty[simp]:
   !id. nsLookup nsEmpty id = NONE
Proof
 Cases
 >> rw [nsLookup_def, nsEmpty_def]
QED

Theorem nsLookupMod_nsEmpty[simp]:
   !x y. nsLookupMod nsEmpty (x::y) = NONE
Proof
 rw [nsLookupMod_def, nsEmpty_def]
QED

Theorem nsAppend_nsEmpty[simp]:
   !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env
Proof
 Cases
 >> rw [nsAppend_def, nsEmpty_def]
QED

Theorem alist_to_ns_nil[simp]:
   alist_to_ns [] = nsEmpty
Proof
 rw [alist_to_ns_def, nsEmpty_def]
QED

Theorem nsSub_nsEmpty[simp]:
   !r env. nsSub r nsEmpty env
Proof
 rw [nsSub_def]
 >> Induct_on `path`
 >> Cases_on `env`
 >> fs [nsLookupMod_def, nsEmpty_def]
QED

Theorem nsAll_nsEmpty[simp]:
   !f. nsAll f nsEmpty
Proof
 rw [nsEmpty_def, nsAll_def]
QED

Theorem nsAll2_nsEmpty[simp]:
   !f. nsAll2 f nsEmpty nsEmpty
Proof
 rw [nsEmpty_def, nsAll2_def]
QED

Theorem nsDom_nsEmpty[simp]:
   nsDom nsEmpty = {}
Proof
 rw [nsDom_def, nsEmpty_def, EXTENSION, GSPECIFICATION]
 >> pairarg_tac
 >> rw []
QED

Theorem nsDomMod_nsEmpty[simp]:
   nsDomMod nsEmpty = {[]}
Proof
  rw [nsDomMod_def, nsEmpty_def, EXTENSION, GSPECIFICATION] >>
  eq_tac
  >- (
    rw [] >>
    pairarg_tac >>
    fs [] >>
    Cases_on `n` >>
    fs [nsLookupMod_def])
  >- rw [EXISTS_PROD, nsLookupMod_def]
QED

Theorem nsMap_nsEmpty[simp]:
   !f. nsMap f nsEmpty = nsEmpty
Proof
 rw [nsMap_def, nsEmpty_def]
QED

Theorem nsBind_nsEmpty[simp]:
   !x y env. nsBind x y env ≠ nsEmpty
Proof
  rw [] >>
  Cases_on `env` >>
  rw [nsBind_def, nsEmpty_def]
QED

Theorem nsLookup_Bind_v_some:
   nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x
Proof
  Cases_on`k` \\ EVAL_TAC \\ simp[]
QED

(* ------------- Other simple automatic theorems --------- *)

Theorem alist_to_ns_cons[simp]:
   !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l)
Proof
 rw [alist_to_ns_def, nsBind_def]
QED

Theorem nsAppend_nsBind[simp]:
   !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2)
Proof
 Cases_on `e1`
 >> Cases_on `e2`
 >> rw [nsAppend_def, nsBind_def]
QED

Theorem nsAppend_alist_to_ns[simp]:
   !al1 al2. nsAppend (alist_to_ns al1) (alist_to_ns al2) = alist_to_ns (al1 ++ al2)
Proof
 rw [alist_to_ns_def, nsAppend_def]
QED

Theorem nsAppend_assoc[simp]:
   !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3
Proof
 rpt Cases
 >> rw [nsAppend_def]
QED

Theorem nsLookup_nsBind[simp]:
   (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
Proof
 rw []
 >> Cases_on `e`
 >> TRY (Cases_on `n`)
 >> rw [nsLookup_def, nsBind_def]
QED

Theorem nsAppend_nsSing[simp]:
   !n x e. nsAppend (nsSing n x) e = nsBind n x e
Proof
 rw [nsSing_def]
 >> Cases_on `e`
 >> simp [nsBind_def, nsAppend_def]
QED

Theorem nsLookup_nsSing[simp]:
   !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE
Proof
 rw [nsSing_def, nsLookup_def]
 >> Cases_on` id`
 >> fs [nsLookup_def]
QED

Theorem nsAll_nsSing[simp]:
   !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v
Proof
 rw [nsAll_def, nsSing_def]
 >> eq_tac
 >> rw [nsLookup_def]
 >> Cases_on `id`
 >> fs [nsLookup_def]
QED

Theorem nsAll2_nsSing[simp]:
   !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2
Proof
 rw [nsAll2_def, nsSub_def]
 >> eq_tac
 >- metis_tac []
 >> rw []
 >> rw []
 >> Cases_on `path`
 >> fs [nsSing_def, nsLookupMod_def]
QED

Theorem nsMap_nsSing[simp]:
   !f x v. nsMap f (nsSing x v) = nsSing x (f v)
Proof
  rw [nsSing_def, nsMap_def]
QED

Theorem nsLookupMod_nsSing[simp]:
   !n1 n2 v. nsLookupMod (nsSing n2 v) n1 = if n1 = [] then SOME (nsSing n2 v) else NONE
Proof
  rw [nsSing_def, nsLookupMod_def] >>
  Cases_on `n1` >>
  rw [nsLookupMod_def]
QED

Theorem nsBind_11[simp]:
   !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n'
Proof
  rw [] >>
  Cases_on `n` >>
  Cases_on `n'` >>
  fs [nsBind_def] >>
  metis_tac []
QED

Theorem nsDom_nsBind[simp]:
   !x y n. nsDom (nsBind x y n) = Short x INSERT nsDom n
Proof
  rw [] >>
  Cases_on `n` >>
  rw [nsBind_def, nsDom_def, EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  eq_tac >>
  rw [nsLookup_def] >>
  rw [nsLookup_def] >>
  Cases_on `x'` >>
  fs [nsLookup_def] >>
  metis_tac []
QED

Theorem nsDom_nsSing[simp]:
   !x y. nsDom (nsSing x y) = {Short x}
Proof
  rw [nsSing_def, nsDom_def, EXTENSION, GSPECIFICATION, LAMBDA_PROD, EXISTS_PROD]
QED

Theorem nsDomMod_nsBind[simp]:
   !x y n. nsDomMod (nsBind x y n) = nsDomMod n
Proof
  rw [] >>
  Cases_on `n` >>
  rw [nsBind_def, nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  eq_tac >>
  rw [nsLookupMod_def] >>
  Cases_on `x'` >>
  fs [nsLookupMod_def] >>
  metis_tac []
QED

Theorem nsDomMod_nsSing[simp]:
   !x y. nsDomMod (nsSing x y) = {[]}
Proof
  rw [nsSing_def, nsDomMod_def, EXTENSION, GSPECIFICATION, LAMBDA_PROD, EXISTS_PROD]
QED

Theorem nsLookupMod_alist_to_ns[simp]:
   !l x y. nsLookupMod (alist_to_ns l) (x::y) = NONE
Proof
  rw [alist_to_ns_def, nsLookupMod_def]
QED

Theorem alist_to_ns_11[simp]:
   !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2
Proof
  rw [alist_to_ns_def]
QED

(* -------------- nsLookup ------------------ *)

Theorem nsLookup_to_nsLookupMod:
   !n v t.
    nsLookup n v = SOME t
    ⇒
    ?m. nsLookupMod n (id_to_mods v) = SOME m ∧ nsLookup m (Short (id_to_n v)) = SOME t
Proof
  ho_match_mp_tac nsLookup_ind >>
  rw [id_to_n_def, nsLookup_def, nsLookupMod_def, id_to_mods_def] >>
  CASE_TAC >>
  fs []
QED

(* -------------- alist_to_ns --------------- *)

Theorem nsLookup_alist_to_ns_some:
   !l id v. nsLookup (alist_to_ns l) id = SOME v ⇔ ?x'. id = Short x' ∧ ALOOKUP l x' = SOME v
Proof
 Induct_on `l`
 >> fs [alist_to_ns_def, nsLookup_def]
 >> rw []
 >> Cases_on `id`
 >> fs [nsLookup_def]
QED

Theorem nsLookup_alist_to_ns_none:
   !l id. nsLookup (alist_to_ns l) id = NONE ⇔ !x'. id = Short x' ⇒ ALOOKUP l x' = NONE
Proof
 Induct_on `l`
 >> fs [alist_to_ns_def, nsLookup_def]
 >> rw []
 >> Cases_on `id`
 >> fs [nsLookup_def]
QED

Theorem nsDom_alist_to_ns[simp]:
   !l. nsDom (alist_to_ns l) = set (MAP (Short o FST) l)
Proof
  rw [nsDom_def, GSPECIFICATION, EXTENSION, EXISTS_PROD, MEM_MAP] >>
  eq_tac >>
  rw [nsLookup_alist_to_ns_some]
  >- metis_tac [ALOOKUP_MEM] >>
  Induct_on `l` >>
  rw [] >>
  rw [] >>
  PairCases_on `h` >>
  rw []
QED

(* -------------- nsLift --------------- *)

Theorem nsLookup_nsLift:
   !mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE
Proof
 rw [nsLift_def]
 >> CASE_TAC
 >> rw [nsLookup_def]
QED

Theorem nsLookupMod_nsLift:
   !mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE
Proof
 rw [nsLift_def]
 >> CASE_TAC
 >> rw [nsLookupMod_def]
QED

Theorem nsLookup_nsLift_append[simp]:
   !m ns ns' m' id n.
   nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns' (Short n) ∧
   nsLookup (nsAppend (nsLift m ns) ns') (Long m' id) =
     if m = m' then nsLookup ns id else nsLookup ns' (Long m' id)
Proof
 rpt strip_tac
 >> Cases_on `ns'`
 >> rw [nsAppend_def, nsLift_def, nsLookup_def]
QED

(* --------------- nsAppend ------------- *)

Theorem nsLookup_nsAppend_none:
   ∀e1 id e2.
    nsLookup (nsAppend e1 e2) id = NONE
    ⇔
    (nsLookup e1 id = NONE ∧
     (nsLookup e2 id = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ id_to_mods id = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
Proof
 ho_match_mp_tac nsLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [id_to_mods_def, nsLookupMod_def]
 >> eq_tac
 >> rw []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def]
   >> rfs [])
 >> rw [METIS_PROVE [] ``x ∨ y ⇔ ~x ⇒ y``]
 >> qexists_tac `[mn]`
 >> simp [nsLookupMod_def]
QED

Theorem nsLookup_nsAppend_some:
   ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE)
Proof
 ho_match_mp_tac nsLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [id_to_mods_def]
 >> eq_tac
 >> rw []
 >> fs []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def])
 >> first_x_assum (qspec_then `[mn]` mp_tac)
 >> simp [nsLookupMod_def]
QED

Theorem nsAppend_to_nsBindList:
   !l. nsAppend (alist_to_ns l) e = nsBindList l e
Proof
 Induct_on `l`
 >> fs [nsBindList_def, alist_to_ns_def]
 >> rw []
 >> pairarg_tac
 >> simp []
 >> Cases_on `e`
 >> fs [nsAppend_def]
 >> metis_tac [nsAppend_def, nsBind_def]
QED

Theorem nsLookupMod_nsAppend_none:
   !e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3))
Proof
 Induct_on `path`
 >> rw []
 >> Cases_on `e2`
 >> Cases_on `e1`
 >> fs [nsAppend_def, nsLookupMod_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []
 >> eq_tac
 >> rw []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def]
   >> rfs [])
 >> rw [METIS_PROVE [] ``x ∨ y ⇔ ~x ⇒ y``]
 >> qexists_tac `[h]`
 >> simp [nsLookupMod_def]
QED

Theorem nsLookupMod_nsAppend_some:
   !e1 e2 path.
    (nsLookupMod (nsAppend e1 e2) path = SOME x
     ⇔
     if path = [] then x = nsAppend e1 e2 else
     nsLookupMod e1 path = SOME x ∨
      (nsLookupMod e2 path = SOME x ∧
      !p1 p2. p1 ≠ [] ∧ path = p1++p2 ⇒ nsLookupMod e1 p1 = NONE))
Proof
 Induct_on `path`
 >> rw []
 >> Cases_on `e2`
 >> Cases_on `e1`
 >> fs [nsAppend_def, nsLookupMod_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs []
 >> eq_tac
 >> rw []
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def]
   >> rfs [])
 >- (
   Cases_on `p1`
   >> fs [nsLookupMod_def]
   >> rfs []) >>
 fs [nsLookupMod_def]
 >- (
   first_x_assum (qspecl_then [`[h]`, `[]`] mp_tac) >>
   rw [nsLookupMod_def])
 >- (
   first_x_assum (qspecl_then [`[h]`, `path`] mp_tac) >>
   rw [nsLookupMod_def])
QED

Theorem nsDom_nsAppend_alist[simp]:
   !x y. nsDom (nsAppend (alist_to_ns x) y) = set (MAP (Short o FST) x) ∪ nsDom y
Proof
  rw [nsDom_def, EXTENSION, GSPECIFICATION, LAMBDA_PROD, EXISTS_PROD, MAP_o] >>
  eq_tac >>
  rw [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, nsLookup_alist_to_ns_none] >>
  fs [MEM_MAP] >>
  rw [] >>
  imp_res_tac ALOOKUP_MEM
  >- metis_tac [PAIR_EQ, FST]
  >- (
    PairCases_on `y''` >>
    simp [METIS_PROVE [] ``(?x. P x ∨ Q x) ⇔ (?x. P x) ∨ (?x. Q x)``] >>
    disj1_tac >>
    Induct_on `x` >>
    rw [] >>
    rw [] >>
    PairCases_on `h` >>
    rw [])
  >- (
    Cases_on `x'` >>
    fs []
    >- (
      Cases_on `ALOOKUP x n` >>
      fs [ALOOKUP_NONE] >>
      rw [id_to_mods_def])
    >- (
      rw [id_to_mods_def, alist_to_ns_def] >>
      Cases_on `p1` >>
      fs [nsLookupMod_def]))
QED

(* -------------- nsAll ---------------- *)

Theorem eALL_T[simp]:
   !e. nsAll (\n x. T) e
Proof
 rw [nsAll_def]
QED

Theorem nsLookup_nsAll:
   !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v
Proof
 rw [nsAll_def]
QED

Theorem nsAll_nsAppend:
   !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2)
Proof
 simp [nsAll_def, PULL_FORALL]
 >> rpt gen_tac
 >> qspec_tac (`v`, `v`)
 >> qspec_tac (`e2`, `e2`)
 >> qspec_tac (`id`, `id`)
 >> qspec_tac (`e1`, `e1`)
 >> ho_match_mp_tac nsLookup_ind
 >> rw []
 >> Cases_on `e2`
 >> fs [nsAppend_def, nsLookup_def, ALOOKUP_APPEND]
 >> every_case_tac
 >> fs [GSYM PULL_FORALL]
 >- metis_tac [nsLookup_def]
 >- metis_tac [nsLookup_def]
 >> rw []
 >> rpt (first_x_assum (qspec_then `Long mn id` mp_tac))
 >> simp [nsLookup_def]
QED

Theorem nsAll_nsBind:
   !P x v e. P (Short x) v ∧ nsAll P e ⇒ nsAll P (nsBind x v e)
Proof
 rw [nsAll_def, nsBind_def]
 >> Cases_on `id = Short x`
 >> fs []
QED

Theorem nsAll_nsOptBind:
   !P x v e. (x = NONE ∨ ?n. x = SOME n ∧ P (Short n) v) ∧ nsAll P e ⇒ nsAll P (nsOptBind x v e)
Proof
 rw [nsAll_def, nsOptBind_def]
 >> every_case_tac
 >> fs []
 >> Cases_on `id`
 >> fs [nsLookup_def, nsBind_def]
 >> rename1 `nsLookup (nsBind n1 _ _) (Short n2)`
 >> Cases_on `n1 = n2`
 >> fs []
QED

Theorem nsAll_alist_to_ns:
   !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l)
Proof
 Induct_on `l`
 >> rw [nsAll_def, alist_to_ns_def]
 >> pairarg_tac
 >> fs []
 >> Cases_on `id`
 >> fs [nsLookup_def]
 >> every_case_tac
 >> fs [EVERY_MEM, LAMBDA_PROD, FORALL_PROD]
 >> rw []
 >> drule ALOOKUP_MEM
 >> metis_tac []
QED

Theorem nsAll_nsLift[simp]:
   !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e
Proof
 rw [nsAll_def, nsLookup_nsLift]
 >> eq_tac
 >> rw []
 >> every_case_tac
 >> fs []
QED

Theorem nsAll_nsAppend_left:
   !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1
Proof
  rw [nsAll_def] >>
  fs [nsLookup_nsAppend_some]
QED

(* -------------- nsSub ---------------- *)

Theorem nsSub_conj:
   !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2
Proof
 rw [nsSub_def]
 >> eq_tac
 >> rw []
 >> metis_tac [SOME_11]
QED

Theorem nsSub_refl:
   !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e
Proof
 rw [nsSub_def]
 >> metis_tac [nsLookup_nsAll]
QED

Theorem nsSub_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2)
Proof
 rw [nsBind_def, nsSub_def]
 >- (
   Cases_on `id = Short x`
   >> fs [])
 >> first_x_assum (qspec_then `path` mp_tac)
 >> Cases_on `path`
 >> fs [nsBind_def, nsLookupMod_def]
 >> Cases_on `e1`
 >> Cases_on `e2`
 >> fs [nsBind_def, nsLookupMod_def]
QED

Theorem nsSub_nsAppend2:
   !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2')
Proof
 rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Theorem nsSub_nsAppend_lift:
   !R mn e1 e1' e2 e2'.
    nsSub (\id. R (Long mn id)) e1 e1' ∧
    nsSub R e2 e2'
    ⇒
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2')
Proof
 rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none,
     nsLookupMod_nsLift, nsLookup_nsLift]
 >> rw [nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none,
     nsLookupMod_nsLift, nsLookup_nsLift]
 >> every_case_tac
 >> fs []
 >> rw []
 >> res_tac
 >> fs [id_to_mods_def]
 >> rw []
 >> every_case_tac
 >> fs []
 >- (
   rename1 `R (Long m id) _ _`
   >> first_x_assum (qspecl_then [`[m]`, `id_to_mods id`] mp_tac)
   >> simp [nsLookupMod_def])
 >- (
   disj2_tac
   >> qexists_tac `[h]`
   >> simp [nsLookupMod_def])
QED

Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End

Theorem alist_rel_restr_thm:
   !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2
Proof
 Induct_on `keys`
 >> rw [alist_rel_restr_def]
 >> every_case_tac
 >> fs []
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End

Theorem alistSub_cong:
   !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2')
Proof
  rw [alistSub_def]
  >> qspec_tac (`MAP FST l1`, `keys`)
  >> Induct
  >> rw [alist_rel_restr_def]
  >> every_case_tac
  >> metis_tac []
QED

val _ = DefnBase.export_cong "alistSub_cong";

Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
Termination
  wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0) (\x.0) (\x.0) env)`
 >> rw []
 >> Induct_on `e1M`
 >> rw [namespace_size_def]
 >> PairCases_on `h`
 >> fs [ALOOKUP_def]
 >> every_case_tac
 >> fs []
 >> rw [namespace_size_def,basicSizeTheory.pair_size_def]
End

Theorem nsLookup_FOLDR_nsLift:
   !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k)
Proof
 Induct_on `p`
 >> rw [mk_id_def, nsLookup_def, nsLift_def]
QED

Theorem nsLookup_FOLDR_nsLift_some:
   !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v)
Proof
 Induct_on `p`
 >> rw [nsLift_def]
 >> Cases_on `id`
 >> rw [nsLookup_def, mk_id_def]
 >> Cases_on `p`
 >> rw []
 >> eq_tac
 >> rw []
 >> rw []
 >> qexists_tac `id_to_mods i`
 >> qexists_tac `id_to_n i`
 >> rw [mk_id_thm]
QED

Theorem nsLookupMod_FOLDR_nsLift_none:
   !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE
Proof
 Induct_on `p1`
 >> rw [nsLift_def]
 >> Cases_on `p2`
 >> rw [nsLookupMod_def, mk_id_def]
QED

(*
Theorem nsSub_compute_thm_general:
   !p R e1 e2.
    nsSub R (FOLDR nsLift e1 (REVERSE p)) (FOLDR nsLift e2 (REVERSE p)) ⇔
    nsSub_compute p R e1 e2
Proof
 ho_match_mp_tac (theorem "nsSub_compute_ind")
 >> rw [nsSub_def, nsSub_compute_def, alistSub_def, alist_rel_restr_thm, nsLookup_def]
 >> eq_tac
 >> rw []
 >- (
   `?v1. ALOOKUP e1V k = SOME v1` by metis_tac [option_nchotomy, ALOOKUP_NONE]
   >> last_x_assum (qspec_then `mk_id (REVERSE p) k` mp_tac)
   >> simp [nsLookup_FOLDR_nsLift, nsLookup_def])
 >- (
   `?v1. ALOOKUP e1M k = SOME v1` by metis_tac [option_nchotomy, ALOOKUP_NONE]
   >> last_assum (qspec_then `REVERSE (k::p)` assume_tac)
   >> fs [nsLookupMod_FOLDR_nsLift_none, nsLookupMod_def]
   >> every_case_tac
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> simp []
   >> pop_assum kall_tac
   >> rw []
   >- (
     fs [nsLookup_FOLDR_nsLift_some]
     >> first_x_assum (qspec_then `mk_id (REVERSE p++[k]++p2) n` mp_tac)
     >> Cases_on `p=[]`
     >> simp [nsLookup_def, mk_id_def])
   >> fs []
   >> rw []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
     >> fs [nsLookupMod_def])
   >- (
     fs [nsLookupMod_FOLDR_nsLift_none]
     >> rw []
     >> fs []
     >> rw []
     >> last_x_assum (qspec_then `REVERSE p++[k]++p3` mp_tac)
     >> rw []
     >> fs [nsLookupMod_def]
     >> every_case_tac
     >> fs []
     >> rw []
     >> metis_tac [IS_PREFIX_APPEND3, APPEND_ASSOC]))
 >- (
   fs [nsLookup_FOLDR_nsLift_some]
   >> rw []
   >> fs [mk_id_def]
   >- (
     Cases_on `id`
     >> fs [nsLookup_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> metis_tac [mk_id_surj])
   >- (
     Cases_on `p2`
     >> fs [nsLookup_def, mk_id_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> first_x_assum drule
     >> rw []
     >> full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]))
 >- (
   fs [nsLookupMod_FOLDR_nsLift_none]
   >> rw []
   >> fs []
   >> rw []
   >> fs []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
      >> fs [nsLookupMod_def])
   >> CCONTR_TAC
   >> fs []
   >> `?x. nsLookupMod (Bind e1V e1M) p3 = SOME x` by metis_tac [option_nchotomy]
   >> fs []
   >> pop_assum mp_tac
   >> Cases_on `p3`
   >> fs [nsLookupMod_def]
   >> CASE_TAC
   >> rw []
   >> fs [MEM_MAP, PULL_EXISTS]
   >> drule ALOOKUP_MEM
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> fs []
   >> pop_assum kall_tac
   >> first_x_assum (qspec_then `REVERSE p ++ [h] ++ t` mp_tac)
   >> rw [])
QED

Theorem nsSub_compute_thm:
   !R e1 e2. nsSub R e1 e2 ⇔ nsSub_compute [] R e1 e2
Proof
 rw [GSYM nsSub_compute_thm_general]
QED
*)

(* -------------- nsAll2 ---------------- *)

Theorem nsAll2_conj:
   !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2
Proof
 rw [nsAll2_def, nsSub_conj]
 >> metis_tac []
QED

Theorem nsAll2_nsLookup1:
   !R e1 e2 n v1.
    nsLookup e1 n = SOME v1 ∧
    nsAll2 R e1 e2
    ⇒
    ?v2. nsLookup e2 n = SOME v2 ∧ R n v1 v2
Proof
 rw [nsSub_def, nsAll2_def]
QED

Theorem nsAll2_nsLookup2:
   !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2
Proof
 rw [nsSub_def, nsAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]
QED

Theorem nsAll2_nsLookup_none:
   !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE)
Proof
 rw [nsSub_def, nsAll2_def]
 >> metis_tac [NOT_SOME_NONE, option_nchotomy, SOME_11]
QED

Theorem nsAll2_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2)
Proof
 rw [nsAll2_def]
 >> irule nsSub_nsBind
 >> rw []
QED

Theorem nsAll2_nsBindList:
   !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)
Proof
 Induct_on `l1`
 >> rw [nsBindList_def]
 >> rw [nsBindList_def]
 >> pairarg_tac
 >> rw []
 >> pairarg_tac
 >> rw []
 >> fs [nsBindList_def]
 >> irule nsAll2_nsBind
 >> rw []
QED

Theorem nsAll2_nsAppend:
   !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2')
Proof
 rw [nsAll2_def, nsSub_def, nsLookup_nsAppend_some, nsLookupMod_nsAppend_none]
 >> metis_tac [NOT_SOME_NONE, SOME_11, option_nchotomy]
QED

Theorem nsAll2_alist_to_ns:
   !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2)
Proof
 Induct_on `l1`
 >> rw []
 >> pairarg_tac
 >> fs []
 >> pairarg_tac
 >> fs []
 >> rw []
 >> irule nsAll2_nsBind
 >> simp []
QED

Theorem nsAll2_nsLift[simp]:
   !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2
Proof
 rw [nsAll2_def, nsSub_def]
 >> eq_tac
 >> rw []
 >- (
   last_x_assum (qspec_then `Long mn id` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   last_x_assum (qspec_then `mn::path` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   first_x_assum (qspec_then `Long mn id` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >- (
   first_x_assum (qspec_then `mn::path` mp_tac)
   >> simp [nsLookup_nsLift, nsLookupMod_nsLift])
 >> pop_assum mp_tac
 >> simp [nsLookup_nsLift, nsLookupMod_nsLift]
 >> every_case_tac
 >> fs []
QED

(* -------------- nsMap --------------- *)

Theorem nsMap_alist_to_ns[simp]:
   !f l. nsMap f (alist_to_ns l) = alist_to_ns (MAP (\(k,v). (k, f v)) l)
Proof
 Induct_on `l`
 >> rw []
 >> rw [alist_to_ns_def, nsMap_def]
QED

Theorem nsMap_compose:
   ∀g e f. nsMap f (nsMap g e) = nsMap (f o g) e
Proof
  recInduct nsMap_ind
  \\ rw[nsMap_def, MAP_MAP_o, o_DEF, FORALL_PROD, EXISTS_PROD, LAMBDA_PROD, MAP_EQ_f]
  \\ metis_tac[]
QED

Theorem nsMap_I[simp]:
   ∀ns. nsMap I ns = ns
Proof
  `∀ns f. f = I ⇒ nsMap f ns = ns` suffices_by rw[]
  \\ CONV_TAC SWAP_FORALL_CONV
  \\ recInduct nsMap_ind
  \\ rw[nsMap_def, MAP_EQ_ID, UNCURRY, FORALL_PROD]
  \\ res_tac
QED

Theorem nsMap_nsAppend:
   !n1 n2 f. nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2)
Proof
  ho_match_mp_tac nsAppend_ind >>
  rw [nsAppend_def, nsMap_def]
QED

Theorem nsLookupMod_nsMap:
   !n x f. nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f) (nsLookupMod n x)
Proof
  ho_match_mp_tac nsLookupMod_ind >>
  rw [nsLookupMod_def, nsMap_def, ALOOKUP_MAP] >>
  every_case_tac >>
  rw [] >>
  fs []
QED

Theorem nsLookup_nsMap:
   !n x f. nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x)
Proof
  ho_match_mp_tac nsLookup_ind >>
  rw [nsLookup_def, nsMap_def, ALOOKUP_MAP] >>
  every_case_tac >>
  rw [] >>
  fs []
QED

Theorem nsAll_nsMap:
   !f n P. nsAll P (nsMap f n) ⇔ nsAll (\x y. P x (f y)) n
Proof
  rw [nsMap_def, nsAll_def, nsLookup_nsMap] >>
  metis_tac []
QED

Theorem nsLift_nsMap:
   !f n mn. nsLift mn (nsMap f n) = nsMap f (nsLift mn n)
Proof
  rw [nsLift_def, nsMap_def]
QED

Theorem nsSub_nsMap:
   !R f n1 n2.
    nsSub R (nsMap f n1) (nsMap f n2) ⇔ nsSub (\id x y. R id (f x) (f y)) n1 n2
Proof
  rw [nsSub_def, nsMap_def, nsLookup_nsMap, nsLookupMod_nsMap] >>
  eq_tac >>
  rw [] >>
  metis_tac []
QED

(* --------------- nsDom --------------- *)
Theorem nsLookup_nsDom:
   !x n. x ∈ nsDom n ⇔ ?v. nsLookup n x = SOME v
Proof
  rw [nsDom_def, GSPECIFICATION, EXISTS_PROD]
QED

Theorem nsDomMod_alist_to_ns[simp]:
   !l. nsDomMod (alist_to_ns l) = {[]}
Proof
  rw [nsDomMod_def, alist_to_ns_def, EXTENSION, GSPECIFICATION, EXISTS_PROD, UNCURRY] >>
  Cases_on `x` >>
  rw [nsLookupMod_def]
QED

Theorem lemma[local]:
  (?x. y = SOME x) ⇔ y ≠ NONE
Proof
  Cases_on `y` >>
  rw []
QED

Theorem nsDom_nsAppend_equal:
   !n1 n2 n3 n4.
    nsDom n1 = nsDom n3 ∧
    nsDom n2 = nsDom n4 ∧
    nsDomMod n1 = nsDomMod n3 ∧
    nsDomMod n2 = nsDomMod n4
    ⇒
    nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
    nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)
Proof
  rw [namespaceTheory.nsDom_def, namespaceTheory.nsDomMod_def,
      EXTENSION, GSPECIFICATION, EXISTS_PROD, nsLookup_nsAppend_some]
  >- metis_tac [NOT_SOME_NONE, option_nchotomy] >>
  fs [lemma, nsLookupMod_nsAppend_none]
  >- metis_tac [NOT_SOME_NONE, option_nchotomy]
QED

Theorem nsDom_nsLift:
   !mn n. nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n)
Proof
  rw [nsDom_def, EXTENSION, GSPECIFICATION, EXISTS_PROD, nsLookup_nsLift] >>
  Cases_on `x` >>
  rw [] >>
  metis_tac []
QED

Theorem nsDomMod_nsLift:
   !mn n. nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod n)
Proof
  rw [nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD, nsLookupMod_nsLift] >>
  Cases_on `x` >>
  rw [] >>
  metis_tac []
QED

Theorem nsDom_nsAppend_flat:
   !n1 n2.nsDomMod n1 = {[]} ⇒ nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2
Proof
  rw [nsDom_def, nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD,
      nsLookup_nsAppend_some] >>
  eq_tac >>
  rw []
  >- metis_tac []
  >- metis_tac []
  >- metis_tac [] >>
  Cases_on `nsLookup n1 x` >>
  rw [] >>
  Cases_on `x` >>
  fs [id_to_mods_def] >>
  Cases_on `p1` >>
  fs [] >>
  rw [] >>
  metis_tac [NOT_NIL_CONS, option_nchotomy]
QED

Theorem nsDomMod_nsAppend_flat:
   !n1 n2.nsDomMod n1 = {[]} ⇒ nsDomMod (nsAppend n1 n2) = nsDomMod n2
Proof
  rw [nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  eq_tac >>
  rw []
  >- (
    fs [nsLookupMod_nsAppend_some] >>
    Cases_on `x = []` >>
    fs [nsLookupMod_def] >>
    metis_tac [])
  >- (
    CCONTR_TAC >>
    fs [] >>
    `nsLookupMod (nsAppend n1 n2) x = NONE` by metis_tac [option_nchotomy] >>
    fs [nsLookupMod_nsAppend_none] >>
    fs [] >>
    metis_tac [option_nchotomy])
QED

