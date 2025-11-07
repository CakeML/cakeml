(*
  A concrete CNF representation as lists of integers that will be packed.
*)
Theory ccnf
Ancestors
  cnf mlvector
Libs
  preamble

(* In the concrete format, we consider assignments w: num -> bool
  In the standard formats, the special case of 0:num is ignored. *)

(* Each literal is represented as an integer in a list.
  The formula is still represented as a set.

  We'll first verify the algorithms on list, then transfer them to
  vectors (which we'll actually use).
*)
Type ilit = ``:int``;
Type cclause = ``:ilit list``;
Type vcclause = ``:ilit vector``;
Type cfml = ``:cclause set``;

Definition satisfies_ilit_def:
  satisfies_ilit w (i:ilit) =
  if i = 0 then F
  else if i > 0 then w (Num i)
  else ¬ w (Num (-i))
End

Definition satisfies_cclause_def:
  satisfies_cclause w ls ⇔
    ∃i. MEM i ls ∧ satisfies_ilit w i
End

Definition satisfies_vcclause_def:
  satisfies_vcclause w =
    satisfies_cclause w o toList
End

Definition satisfies_cfml_def:
  satisfies_cfml = satisfies_fml_gen satisfies_cclause
End

Definition satisfies_vcfml_def:
  satisfies_vcfml w =
  satisfies_cfml w o IMAGE toList
End

Theorem satsifies_cclause_SUBSET:
  satisfies_cclause w c ∧ set c ⊆ set d ⇒
  satisfies_cclause w d
Proof
  rw[satisfies_cclause_def,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem satisfies_cclause_CONS:
  satisfies_cclause w (x::xs) ⇔
  satisfies_ilit w x ∨
  satisfies_cclause w xs
Proof
  rw[satisfies_cclause_def]>>
  metis_tac[]
QED

Theorem satisfies_cclause_REVERSE:
  satisfies_cclause w (REVERSE cs) ⇔
  satisfies_cclause w cs
Proof
  rw[satisfies_cclause_def]
QED

Theorem satisfies_ilit_negate:
  satisfies_ilit w l ⇒
  ¬satisfies_ilit w (-l)
Proof
  rw[satisfies_ilit_def]>>
  `F` by intLib.ARITH_TAC
QED

(* Conversions *)
Definition to_ilit_def:
  to_ilit (l : num lit) =
  case l of
    Pos n => (&n):int
  | Neg n => -&n
End

Definition to_cclause_def:
  to_cclause (c:num clause) =
  (MAP to_ilit c):cclause
End

Theorem satisfies_ilit_to_ilit:
  lit_var l ≠ 0 ⇒
  (satisfies_ilit w (to_ilit l) ⇔
  satisfies_lit w l)
Proof
  rw[satisfies_ilit_def,satisfies_lit_def,to_ilit_def]>>
  TOP_CASE_TAC>>
  gvs[lit_var_def]>>
  `F` by intLib.ARITH_TAC
QED

Theorem satisfies_cclause_to_cclause:
  0 ∉ clause_vars c ⇒
  (satisfies_cclause w (to_cclause c) ⇔
  satisfies_clause w c)
Proof
  rw[satisfies_cclause_def,satisfies_clause_def,to_cclause_def,clause_vars_def]>>
  fs[MEM_MAP]>>
  metis_tac[satisfies_ilit_to_ilit]
QED

(* As a general pattern, we will traverse
  clauses from back-to-front to ease the related
  vector index computations*)
Definition all_assigned_def:
  (all_assigned dm [] = T) ∧
  (all_assigned dm (c::cs) =
    if c < 0
    then
      case FLOOKUP dm (Num (-c)) of
        SOME F => all_assigned dm cs
      | _ => F
    else
      case FLOOKUP dm (Num c) of
        SOME T => all_assigned dm cs
      | _ => F)
End

Definition all_assigned_vec_def:
  (all_assigned_vec dm v (i:num) =
  if i = 0 then T
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      case FLOOKUP dm (Num (-c)) of
        SOME F => all_assigned_vec dm v i1
      | _ => F
    else
      case FLOOKUP dm (Num c) of
        SOME T => all_assigned_vec dm v i1
      | _ => F
  )
End

Theorem all_assigned_vec:
  ∀dm v i ds.
  v = Vector ds ∧ i ≤ LENGTH ds ⇒
  all_assigned_vec dm v i =
  all_assigned dm (REVERSE (TAKE i ds))
Proof
  ho_match_mp_tac all_assigned_vec_ind>>rw[]>>
  simp[Once all_assigned_vec_def]>>
  Cases_on`i`
  >- simp[all_assigned_def]>>
  gvs[ADD1]>>
  DEP_REWRITE_TAC[TAKE_EL_SNOC]>>
  fs[REVERSE_SNOC,all_assigned_def,sub_def]>>
  rw[]>>gvs[]>>
  every_case_tac>>gvs[]>>
  metis_tac[]
QED

(*
  Part of the optimization for RUP,
  we take d to be a mapping num |-> bool option.
*)
Definition delete_literals_sing_def:
  (delete_literals_sing dm [] = SOME (T,dm)) ∧
  (delete_literals_sing dm ((c:int)::cs) =
  if c < 0
  then
    (let nc = Num (-c) in
    case FLOOKUP dm nc of
      NONE =>
        if all_assigned dm cs
        then SOME (F, dm |+ (nc,T))
        else NONE
    | SOME F => delete_literals_sing dm cs
    | _ => NONE)
  else
    let nc = Num c in
    case FLOOKUP dm nc of
      NONE =>
        if all_assigned dm cs
        then SOME (F, dm |+ (nc,F))
        else NONE
    | SOME T => delete_literals_sing dm cs
    | _ => NONE)
End

Definition delete_literals_sing_vec_def:
  (delete_literals_sing_vec dm v i =
  if i = 0 then SOME (T,dm)
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      (let nc = Num (-c) in
      case FLOOKUP dm nc of
        NONE =>
          if all_assigned_vec dm v i1
          then SOME (F, dm |+ (nc,T))
          else NONE
      | SOME F => delete_literals_sing_vec dm v i1
      | _ => NONE)
    else
      let nc = Num c in
      case FLOOKUP dm nc of
        NONE =>
          if all_assigned_vec dm v i1
          then SOME (F, dm |+ (nc,F))
          else NONE
      | SOME T => delete_literals_sing_vec dm v i1
      | _ => NONE)
End

Theorem delete_literals_sing_vec':
  ∀dm v i ds.
  v = Vector ds ∧ i ≤ LENGTH ds ⇒
  delete_literals_sing_vec dm v i =
  delete_literals_sing dm (REVERSE (TAKE i ds))
Proof
  ho_match_mp_tac delete_literals_sing_vec_ind>>rw[]>>
  simp[Once delete_literals_sing_vec_def]>>
  Cases_on`i`
  >- simp[Once delete_literals_sing_def]>>
  gvs[ADD1]>>
  DEP_REWRITE_TAC[TAKE_EL_SNOC]>>
  fs[REVERSE_SNOC,delete_literals_sing_def,sub_def]>>
  IF_CASES_TAC>>gvs[]>>
  DEP_REWRITE_TAC[all_assigned_vec]>>simp[]>>
  every_case_tac>>gvs[]
QED

Theorem delete_literals_sing_vec:
  i ≤ LENGTH ds ⇒
  delete_literals_sing_vec dm (Vector ds) i =
  delete_literals_sing dm (REVERSE (TAKE i ds))
Proof
  metis_tac[delete_literals_sing_vec']
QED

Definition is_rup_def:
  (is_rup fml dm [] = SOME (F,dm)) ∧
  (is_rup fml dm (i::is) =
  case lookup i fml of
    NONE => NONE
  | SOME c =>
  case delete_literals_sing dm (REVERSE c) of
    NONE => NONE
  | SOME (T,dm) => SOME (T,dm)
  | SOME (F,dm') => is_rup fml dm' is)
End

Definition is_rup_vec_def:
  (is_rup_vec fml dm [] = SOME (F,dm)) ∧
  (is_rup_vec fml dm (i::is) =
  case lookup i fml of
    NONE => NONE
  | SOME c =>
  case delete_literals_sing_vec dm c (length c) of
    NONE => NONE
  | SOME (T,dm) => SOME (T,dm)
  | SOME (F,dm') => is_rup_vec fml dm' is)
End

Theorem is_rup_vec:
  ∀is dm.
  is_rup_vec (map Vector fml) dm is =
  is_rup fml dm is
Proof
  Induct>>rw[is_rup_vec_def,is_rup_def]>>
  simp[lookup_map]>>
  rename1`lookup h fml`>>
  Cases_on`lookup h fml`>>
  simp[]>>
  DEP_REWRITE_TAC[delete_literals_sing_vec]>>
  simp[length_def]
QED

Theorem map_I:
  ∀t.
  sptree$map I t = t
Proof
  Induct>>rw[map_def]
QED

Theorem is_rup_vec':
  is_rup (map toList fml) dm is =
  is_rup_vec fml dm is
Proof
  rw[GSYM is_rup_vec]>>
  AP_THM_TAC>>
  AP_THM_TAC>>
  AP_TERM_TAC>>
  rw[map_map_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac`map f _`>>
  `f = I` by (
    simp[Abbr`f`,FUN_EQ_THM]>>
    Cases>>rw[mlvectorTheory.toList_thm])>>
  simp[map_I]
QED

Definition lit_map_def:
  lit_map d dm ⇔
  ∀n b.
    FLOOKUP dm n = SOME b ⇒
    if b then MEM (&n) d
    else MEM (-&n) d
End

Theorem NOT_NONE_SOME_EXISTS:
  x ≠ NONE ⇔ ?y. x = SOME y
Proof
  Cases_on`x`>>rw[]
QED

Theorem delete_literals_sing_SOME_T:
  ∀ls.
  lit_map d dm ∧
  satisfies_cclause w ls ∧
  delete_literals_sing dm ls = SOME (T,dm') ⇒
  satisfies_cclause w d
Proof
  Induct
  >-
    rw[delete_literals_sing_def,satisfies_cclause_def]>>
  rw[]>>
  gvs[delete_literals_sing_def,AllCaseEqs()]
  >- (
    fs[lit_map_def]>>
    first_x_assum drule>>
    fs[satisfies_cclause_CONS]>>
    `-&Num (-h) = h` by intLib.ARITH_TAC>>
    simp[satisfies_cclause_def]>>
    metis_tac[])
  >- (
    fs[lit_map_def]>>
    first_x_assum drule>>
    fs[satisfies_cclause_CONS]>>
    `&Num (h) = h` by intLib.ARITH_TAC>>
    simp[satisfies_cclause_def]>>
    metis_tac[])
QED

Theorem lit_map_cons:
  lit_map xs dm ∧
  Num (ABS x) = n ∧
  (b ⇔ x > 0)
  ⇒
  lit_map (x::xs) (dm |+ (n,b))
Proof
  rw[lit_map_def,FLOOKUP_UPDATE]>>
  gvs[AllCaseEqs()]>>rw[]
  >- (DISJ1_TAC>>intLib.ARITH_TAC)
  >- (DISJ1_TAC>>intLib.ARITH_TAC)>>
  first_x_assum drule>>simp[]
QED

Theorem lit_map_snoc:
  lit_map xs dm ∧
  Num (ABS x) = n ∧
  (b ⇔ x > 0)
  ⇒
  lit_map (xs++[x]) (dm |+ (n,b))
Proof
  rw[lit_map_def,FLOOKUP_UPDATE]>>
  gvs[AllCaseEqs()]>>rw[]
  >- (DISJ2_TAC>>intLib.ARITH_TAC)
  >- (DISJ2_TAC>>intLib.ARITH_TAC)>>
  first_x_assum drule>>simp[]
QED

Theorem FUPDATE_EQ:
  a = x ∧ b = y ⇒
  dm |+ (a,b) = dm |+ (x,y)
Proof
  rw[]
QED

Theorem lit_map_all_assigned:
  ∀cs.
  lit_map d dm ∧
  all_assigned dm cs ⇒
  set cs ⊆ set d
Proof
  Induct>>rw[all_assigned_def]>>
  gvs[AllCasePreds(),lit_map_def]>>
  first_x_assum drule>>gvs[]>>
  qmatch_goalsub_abbrev_tac`MEM hh d`>>
  `hh = h` by (unabbrev_all_tac >> intLib.ARITH_TAC)>>
  simp[]
QED

Theorem delete_literals_sing_SOME_F:
  ∀ls.
  lit_map d dm ∧
  delete_literals_sing dm ls = SOME (F,dm') ⇒
  ∃h.
  set ls DIFF set d ⊆ {h} ∧
  dm' = (dm |+ (Num (ABS h), h < 0))
Proof
  Induct
  >-
    rw[delete_literals_sing_def,satisfies_cclause_def]>>
  rpt strip_tac>>
  gvs[delete_literals_sing_def,AllCaseEqs()]
  >- (
    irule_at Any FUPDATE_EQ>>simp[]>>
    qexists_tac`h`>>simp[]>>
    drule_all lit_map_all_assigned>>
    rw[EXTENSION,SUBSET_DEF]
    >- intLib.ARITH_TAC
    >- metis_tac[]
    >- intLib.ARITH_TAC
    >- metis_tac[])
  >- (
    `MEM h d` by (
      fs[lit_map_def]>>first_x_assum drule>>
      simp[]>>
      `-&Num (-h) = h` by intLib.ARITH_TAC>>
      simp[])>>
    irule_at Any FUPDATE_EQ>>simp[]>>
    qexists_tac`h'`>>simp[])
  >- (
    irule_at Any FUPDATE_EQ>>simp[]>>
    qexists_tac`h`>>simp[]>>
    drule_all lit_map_all_assigned>>
    rw[EXTENSION,SUBSET_DEF]
    >- intLib.ARITH_TAC
    >- metis_tac[]
    >- intLib.ARITH_TAC
    >- metis_tac[])
  >- (
    `MEM h d` by (
      fs[lit_map_def]>>first_x_assum drule>>
      simp[]>>
      `&Num h = h` by intLib.ARITH_TAC>>
      simp[])>>
    irule_at Any FUPDATE_EQ>>simp[]>>
    qexists_tac`h'`>>simp[])
QED

Theorem is_rup_SOME_T:
  ∀is d dm.
  lit_map d dm ∧
  is_rup fml dm is = SOME (T,dm') ∧
  satisfies_cfml w (range fml) ⇒
  satisfies_cclause w d
Proof
  Induct>>rw[is_rup_def]>>
  gvs[AllCaseEqs()]>>
  fs[satisfies_cfml_def]>>
  drule_all satisfies_fml_gen_lookup>>
  strip_tac
  >-
    metis_tac[delete_literals_sing_SOME_T,satisfies_cclause_REVERSE]>>
  drule_all delete_literals_sing_SOME_F>>
  strip_tac>>
  first_x_assum $ drule_at Any>>
  gvs[]>>
  rename1`hh < 0` >>
  disch_then (qspec_then `-hh :: d` mp_tac)>>
  impl_tac >- (
    irule lit_map_cons>>simp[]>>
    intLib.ARITH_TAC)>>
  rw[]>>
  gvs[SUBSET_DEF,satisfies_cclause_def]>>
  drule satisfies_ilit_negate>>
  rw[]>>metis_tac[]
QED

Theorem is_rup_SOME_F:
  ∀is d dm.
  lit_map d dm ∧
  is_rup fml dm is = SOME (F,dm') ∧
  satisfies_cfml w (range fml) ∧
  ¬ satisfies_cclause w d ⇒
  ∃d'.
  lit_map d' dm' ∧
  ¬ satisfies_cclause w d'
Proof
  Induct>>rw[is_rup_def]
  >- metis_tac[]>>
  gvs[AllCaseEqs()]>>
  fs[satisfies_cfml_def]>>
  drule_all satisfies_fml_gen_lookup>>
  strip_tac>>
  drule_all delete_literals_sing_SOME_F>>
  strip_tac>>
  first_x_assum $ drule_at (Pos (el 2))>>
  gvs[]>>
  disch_then irule>>
  rename1`hh < 0` >>
  qexists_tac `-hh :: d`>>
  rw[]
  >- (
    gvs[SUBSET_DEF,satisfies_cclause_def]>>
    drule satisfies_ilit_negate>>
    rw[]>>metis_tac[])>>
  irule lit_map_cons>>simp[]>>
  intLib.ARITH_TAC
QED

Definition init_lit_map_def:
  (init_lit_map [] dm = dm) ∧
  (init_lit_map (d::ds) dm =
    init_lit_map ds (dm |+ (Num (ABS d), d > 0)))
End

Definition init_lit_map_vec_def:
  (init_lit_map_vec i v dm =
  if i = 0
  then dm
  else
    let i1 = i - 1 in
    let d = sub v i1 in
    init_lit_map_vec i1 v (dm |+ (Num (ABS d), d > 0)))
End

Theorem init_lit_map_lit_map:
  ∀cs d dm dm'.
  lit_map d dm ∧
  init_lit_map cs dm = dm' ⇒
  lit_map (d++cs) dm'
Proof
  Induct>>rw[init_lit_map_def]>>
  fs[]>>
  `d++h::cs = (d++[h])++cs` by fs[]>>
  pop_assum SUBST_ALL_TAC>>
  first_x_assum irule>>
  irule lit_map_snoc>>
  simp[]
QED

Theorem range_map:
  misc$range (map f fml) =
  IMAGE f (range fml)
Proof
  rw[miscTheory.range_def,EXTENSION,lookup_map]>>
  metis_tac[]
QED

Theorem is_rup_vec_SOME_T:
  lit_map (toList d) dm ∧
  is_rup_vec fml dm is = SOME (T,dm') ∧
  satisfies_vcfml w (range fml) ⇒
  satisfies_vcclause w d
Proof
  rw[]>>
  gvs[satisfies_vcfml_def,satisfies_vcclause_def]>>
  drule is_rup_SOME_T>>
  fs[GSYM range_map]>>
  disch_then $ drule_at Any>>
  simp[is_rup_vec']>>
  disch_then $ drule_at Any>>
  simp[]
QED

Theorem is_rup_vec_SOME_F:
  lit_map (toList d) dm ∧
  is_rup_vec fml dm is = SOME (F,dm') ∧
  satisfies_vcfml w (range fml) ∧
  ¬ satisfies_vcclause w d ⇒
  ∃d'.
  lit_map (toList d') dm' ∧
  ¬ satisfies_vcclause w d'
Proof
  rw[]>>
  gvs[satisfies_vcfml_def,satisfies_vcclause_def]>>
  drule is_rup_SOME_F>>
  fs[GSYM range_map]>>
  disch_then $ drule_at Any>>
  disch_then $ drule_at Any>>
  simp[is_rup_vec']>>
  disch_then $ drule_at Any>>
  rw[]>>
  metis_tac[toList_thm]
QED

