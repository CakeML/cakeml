(*
  A hash table from names to numbers: its hash function, its buckets and
  their relation to the name_to_num_state that specifies the numbering
*)
Theory name_table
Ancestors
  pbc pbc_normalise mlint
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*
  The hash. Base 97 with lazy reduction: h is reduced mod P only when it has
  reached P, so every step stays below 2^30 (lz97_bound) and the arithmetic
  is on small numbers. P = 11069489.
*)
Definition lz97_aux_def:
  lz97_aux s n i (h:num) =
  if smallnum_lt_str i n s then
    let r = if smallnum_lt h 11069489 then h else smallnum_mod h 11069489 in
    lz97_aux s n (smallnum_add_str i 1 s)
      (smallnum_add (smallnum_mul r 97) (ORD (strsub_unsafe s i)))
  else h
Termination
  WF_REL_TAC`measure (λ(s,n,i,h). n - i)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]
End

Definition lz97_def:
  lz97 s = lz97_aux s (strlen s) 0 0
End

(* One step of lz97 stays below 2^30 *)
Theorem lz97_step_bound:
  ∀h c. (if h < 11069489 then h else h MOD 11069489) * 97 + ORD c < 2 ** 30
Proof
  rpt gen_tac>>
  qabbrev_tac`r = if h < 11069489 then h else h MOD 11069489`>>
  `r < 11069489` by rw[Abbr`r`]>>
  `ORD c < 256` by simp[ORD_BOUND]>>
  simp[]
QED

Theorem lz97_aux_bound:
  ∀s n i h. h < 2 ** 30 ⇒ lz97_aux s n i h < 2 ** 30
Proof
  ho_match_mp_tac lz97_aux_ind>>
  rpt strip_tac>>
  simp[Once lz97_aux_def]>>
  IF_CASES_TAC>>
  fs[]>>
  first_x_assum irule>>
  qspecl_then [`h`,`strsub_unsafe s i`] assume_tac lz97_step_bound>>
  fs[smallnum_lt_def,smallnum_mod_def,smallnum_add_def,smallnum_mul_def]
QED

Theorem lz97_bound:
  lz97 s < 2 ** 30
Proof
  rewrite_tac[lz97_def]>>
  irule lz97_aux_bound>>
  simp[]
QED

(* A bucket: hash, name, number *)
Datatype:
  bucket = Bnil | Bnode num mlstring num bucket
End

(* The suffix of b starting at the node for name v, whose hash is h;
  Bnil when there is none *)
Definition bfind_def:
  bfind h v b =
  case b of
    Bnil => Bnil
  | Bnode h' v' n rest =>
    if smallnum_eq h h' ∧ v = v' then b else bfind h v rest
End

(* The bucket index of hash h in a table of m buckets *)
Definition bidx_def:
  bidx h m = smallnum_mod (h:num) m
End

(* Table sizes: the primes ≥ 1021·2^k; the largest is the last size *)
Definition tb_sizes_def:
  tb_sizes =
  [1021; 2053; 4091; 8171; 16339; 32687; 65353; 130693; 261379; 522757;
   1045507; 2091053; 4182019; 8364043; 16728071; 33456139:num]
End

Definition next_size_aux_def:
  (next_size_aux m [] = m) ∧
  (next_size_aux m (k::ks) = if m < k then k else next_size_aux m ks)
End

(* The size after m; m itself at the largest size *)
Definition next_size_def:
  next_size m = next_size_aux m tb_sizes
End

(*
  The model of the table: the list of its buckets
*)
Definition bucket_lookup_def:
  (bucket_lookup v Bnil = NONE) ∧
  (bucket_lookup v (Bnode h w n rest) =
    if v = w then SOME n else bucket_lookup v rest)
End

Definition bucket_alist_def:
  (bucket_alist Bnil = []) ∧
  (bucket_alist (Bnode h w n rest) = (w,n) :: bucket_alist rest)
End

(* All the names of the table, with their numbers *)
Definition tb_alist_def:
  tb_alist bs = FLAT (MAP bucket_alist bs)
End

(* Every node of bucket b stores the hash of its name and sits in bucket i of m *)
Definition bucket_ok_def:
  (bucket_ok m i Bnil ⇔ T) ∧
  (bucket_ok m i (Bnode h w n rest) ⇔
    h = lz97 w ∧ h MOD m = i ∧ bucket_ok m i rest)
End

Definition tb_lookup_def:
  tb_lookup bs v = bucket_lookup v (EL (lz97 v MOD LENGTH bs) bs)
End

Definition tb_insert_def:
  tb_insert bs v n =
  let i = lz97 v MOD LENGTH bs in
    LUPDATE (Bnode (lz97 v) v n (EL i bs)) i bs
End

(* Relinking the nodes of a bucket into the buckets bs2, as nt_grow does *)
Definition bucket_move_def:
  (bucket_move bs2 Bnil = bs2) ∧
  (bucket_move bs2 (Bnode h w n rest) =
    let j = h MOD LENGTH bs2 in
      bucket_move (LUPDATE (Bnode h w n (EL j bs2)) j bs2) rest)
End

Definition tb_grow_def:
  tb_grow bs m2 = FOLDL bucket_move (REPLICATE m2 Bnil) bs
End

(* The buckets bs hold exactly the names numbered by s, each once *)
Definition tb_rel_def:
  tb_rel bs s ⇔
    bs ≠ [] ∧ LENGTH bs < 2 ** 30 ∧
    (∀i. i < LENGTH bs ⇒ bucket_ok (LENGTH bs) i (EL i bs)) ∧
    ALL_DISTINCT (MAP FST (tb_alist bs)) ∧
    name_to_num_state_ok s ∧
    ∀v. lookup_index s v = tb_lookup bs v
End

(* The state the numbering starts from; n is the first number given *)
Definition nt_init_def:
  nt_init n = (init_state lz97 mlstring$compare) with next_num := n
End

Theorem bucket_lookup_ALOOKUP:
  ∀b v. bucket_lookup v b = ALOOKUP (bucket_alist b) v
Proof
  Induct>>
  rw[bucket_lookup_def,bucket_alist_def]
QED

Theorem bucket_ok_MEM:
  ∀b w n. bucket_ok m i b ∧ MEM (w,n) (bucket_alist b) ⇒ lz97 w MOD m = i
Proof
  Induct>>
  rw[bucket_ok_def,bucket_alist_def]>>
  metis_tac[]
QED

Theorem bfind_thm:
  bfind h v Bnil = Bnil ∧
  bfind h v (Bnode h' v' n rest) =
    if h = h' ∧ v = v' then Bnode h' v' n rest else bfind h v rest
Proof
  rw[Once bfind_def,smallnum_eq_def]>>
  simp[Once bfind_def,smallnum_eq_def]
QED

Theorem bfind_bucket_lookup:
  ∀b. bucket_ok m i b ⇒
  (bfind (lz97 v) v b = Bnil ⇔ bucket_lookup v b = NONE) ∧
  ∀h w n rest. bfind (lz97 v) v b = Bnode h w n rest ⇒
    bucket_lookup v b = SOME n
Proof
  Induct>>
  rw[bfind_thm,bucket_ok_def,bucket_lookup_def]
QED

Theorem FLAT_REPLICATE_NIL[local]:
  ∀k. FLAT (REPLICATE k []) = []
Proof
  Induct>>
  simp[]
QED

Theorem nt_init_ok:
  name_to_num_state_ok (nt_init n)
Proof
  simp[nt_init_def,name_to_num_state_ok_def,init_state_def,lookup_name_def,
       lookup_index_def,mlstringTheory.TotOrd_compare]
QED

Theorem tb_rel_init:
  0 < m ∧ m < 2 ** 30 ⇒ tb_rel (REPLICATE m Bnil) (nt_init n)
Proof
  rw[tb_rel_def,nt_init_ok]>>
  simp[nt_init_def,EL_REPLICATE,bucket_ok_def,tb_alist_def,map_replicate,
       tb_lookup_def,bucket_lookup_def,bucket_alist_def,FLAT_REPLICATE_NIL,
       lookup_index_def,init_state_def]
QED

Theorem tb_rel_bfind:
  tb_rel bs s ∧ h = lz97 v ⇒
  (lookup_index s v = NONE ⇔
    bfind h v (EL (h MOD LENGTH bs) bs) = Bnil) ∧
  ∀h' w n rest. bfind h v (EL (h MOD LENGTH bs) bs) = Bnode h' w n rest ⇒
    lookup_index s v = SOME n
Proof
  strip_tac>>
  gvs[tb_rel_def,tb_lookup_def]>>
  `lz97 v MOD LENGTH bs < LENGTH bs` by (Cases_on`bs`>>gvs[])>>
  first_x_assum drule>>
  strip_tac>>
  drule_then (qspec_then`v` strip_assume_tac) bfind_bucket_lookup>>
  rw[]
QED

Theorem name_to_num_state_ok_map_ok[local]:
  name_to_num_state_ok s ⇒
  TotOrd s.cmp_name ∧
  ∀h m. sptree$lookup h s.to_num = SOME m ⇒ map_ok m
Proof
  rw[name_to_num_state_ok_def]>>
  metis_tac[]
QED

(* Numbering a name already numbered changes nothing *)
Theorem lookup_index_SOME_name_to_num_var:
  lookup_index s v = SOME n ⇒ name_to_num_var v s = (n,s)
Proof
  rw[lookup_index_def,name_to_num_var_def,AllCaseEqs()]>>
  simp[]
QED

(* Numbering a new name changes the numbering at that name only *)
Theorem lookup_index_name_to_num_var:
  name_to_num_state_ok s ∧ lookup_index s v = NONE ∧
  name_to_num_var v s = (n,s') ⇒
  n = s.next_num ∧
  ∀w. lookup_index s' w = if w = v then SOME n else lookup_index s w
Proof
  strip_tac>>
  drule name_to_num_state_ok_map_ok>>
  strip_tac>>
  `map_ok (mlmap$empty s.cmp_name : ('a,num) map) ∧
   ∀w. mlmap$lookup (mlmap$empty s.cmp_name : ('a,num) map) w = NONE` by
    simp[mlmapTheory.empty_thm,mlmapTheory.lookup_thm]>>
  qpat_x_assum`name_to_num_var _ _ = _` mp_tac>>
  simp[name_to_num_var_def]>>
  Cases_on`sptree$lookup (s.hash_fun v) s.to_num`>>
  gvs[lookup_index_def]>>
  strip_tac>>
  gvs[]>>
  rw[sptreeTheory.lookup_insert,mk_map_def]>>
  res_tac>>
  fs[mlmapTheory.lookup_insert]
QED

(* Consing a node onto bucket i adds its pair to the table *)
Theorem tb_alist_LUPDATE_Bnode:
  ∀bs i h v n.
  i < LENGTH bs ⇒
  PERM (tb_alist (LUPDATE (Bnode h v n (EL i bs)) i bs))
    ((v,n) :: tb_alist bs)
Proof
  Induct>>
  rw[tb_alist_def]>>
  Cases_on`i`>>
  gvs[LUPDATE_def,bucket_alist_def]>>
  first_x_assum drule>>
  rw[GSYM tb_alist_def]>>
  rename1`bucket_alist b ++ _`>>
  irule PERM_TRANS>>
  qexists_tac`bucket_alist b ++ (v,n) :: tb_alist bs`>>
  simp[PERM_APPEND_IFF,PERM_FUN_APPEND_CONS]
QED

(* A name of the table is in the bucket of its hash *)
Theorem tb_alist_MEM:
  (∀i. i < LENGTH bs ⇒ bucket_ok (LENGTH bs) i (EL i bs)) ∧
  MEM (w,x) (tb_alist bs) ⇒
  MEM (w,x) (bucket_alist (EL (lz97 w MOD LENGTH bs) bs))
Proof
  rw[tb_alist_def,MEM_FLAT,MEM_MAP]>>
  rename1`MEM b bs`>>
  `∃j. j < LENGTH bs ∧ b = EL j bs` by metis_tac[MEM_EL]>>
  gvs[]>>
  `lz97 w MOD LENGTH bs = j` by metis_tac[bucket_ok_MEM]>>
  simp[]
QED

Theorem tb_rel_insert:
  tb_rel bs s ∧ lookup_index s v = NONE ∧
  name_to_num_var v s = (n,s') ⇒
  n = s.next_num ∧ s'.next_num = n + 1 ∧ tb_rel (tb_insert bs v n) s'
Proof
  strip_tac>>
  `name_to_num_state_ok s` by fs[tb_rel_def]>>
  `s'.next_num = s.next_num + 1` by (
    gvs[name_to_num_var_def,lookup_index_def,AllCaseEqs()])>>
  drule_all lookup_index_name_to_num_var>>
  strip_tac>>
  drule_all name_to_num_var_thm>>
  strip_tac>>
  gvs[tb_rel_def,tb_insert_def,tb_lookup_def]>>
  qabbrev_tac`i = lz97 v MOD LENGTH bs`>>
  `i < LENGTH bs` by (Cases_on`bs`>>gvs[Abbr`i`])>>
  rpt conj_tac
  >- rw[EL_LUPDATE,bucket_ok_def]
  >- (
    `PERM
       (MAP FST (tb_alist (LUPDATE (Bnode (lz97 v) v s.next_num (EL i bs)) i bs)))
       (MAP FST ((v,s.next_num) :: tb_alist bs))` by
      metis_tac[PERM_MAP,tb_alist_LUPDATE_Bnode]>>
    drule ALL_DISTINCT_PERM>>
    disch_then (rewrite_tac o single)>>
    simp[MEM_MAP,EXISTS_PROD]>>
    rpt strip_tac>>
    drule_all tb_alist_MEM>>
    gvs[bucket_lookup_ALOOKUP,ALOOKUP_NONE,MEM_MAP,Abbr`i`]>>
    metis_tac[FST])>>
  rw[EL_LUPDATE,bucket_lookup_def]>>
  gvs[]
QED

(* With every name in the bucket of its hash, lookup is in the whole table *)
Theorem tb_lookup_ALOOKUP:
  (∀i. i < LENGTH bs ⇒ bucket_ok (LENGTH bs) i (EL i bs)) ∧
  ALL_DISTINCT (MAP FST (tb_alist bs)) ∧ bs ≠ [] ⇒
  tb_lookup bs v = ALOOKUP (tb_alist bs) v
Proof
  strip_tac>>
  `lz97 v MOD LENGTH bs < LENGTH bs` by (Cases_on`bs`>>gvs[])>>
  simp[tb_lookup_def,bucket_lookup_ALOOKUP]>>
  Cases_on`ALOOKUP (bucket_alist (EL (lz97 v MOD LENGTH bs) bs)) v`
  >- (
    Cases_on`ALOOKUP (tb_alist bs) v`>>
    simp[]>>
    imp_res_tac ALOOKUP_MEM>>
    drule_all tb_alist_MEM>>
    gvs[ALOOKUP_NONE,MEM_MAP]>>
    metis_tac[FST])>>
  imp_res_tac ALOOKUP_MEM>>
  `MEM (v,x) (tb_alist bs)` by (
    simp[tb_alist_def,MEM_FLAT,MEM_MAP]>>
    metis_tac[MEM_EL])>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem LENGTH_bucket_move:
  ∀b bs2. LENGTH (bucket_move bs2 b) = LENGTH bs2
Proof
  Induct>>
  rw[bucket_move_def]
QED

Theorem bucket_move_thm:
  ∀b bs2 m0 i.
  bucket_ok m0 i b ∧ bs2 ≠ [] ∧
  (∀j. j < LENGTH bs2 ⇒ bucket_ok (LENGTH bs2) j (EL j bs2)) ⇒
  LENGTH (bucket_move bs2 b) = LENGTH bs2 ∧
  (∀j. j < LENGTH bs2 ⇒
    bucket_ok (LENGTH bs2) j (EL j (bucket_move bs2 b))) ∧
  PERM (tb_alist (bucket_move bs2 b)) (bucket_alist b ++ tb_alist bs2)
Proof
  Induct
  >- simp[bucket_move_def,bucket_alist_def]>>
  rpt gen_tac>>
  strip_tac>>
  rename1`bucket_ok m0 i (Bnode h w n rest)`>>
  gvs[bucket_ok_def,bucket_move_def,bucket_alist_def]>>
  qabbrev_tac`j = lz97 w MOD LENGTH bs2`>>
  `j < LENGTH bs2` by (Cases_on`bs2`>>gvs[Abbr`j`])>>
  last_x_assum
    (qspecl_then [`LUPDATE (Bnode (lz97 w) w n (EL j bs2)) j bs2`,`m0`,
                  `lz97 w MOD m0`] mp_tac)>>
  impl_tac
  >- rw[EL_LUPDATE,bucket_ok_def]>>
  strip_tac>>
  gvs[]>>
  irule PERM_TRANS>>
  qexists_tac`bucket_alist rest ++ tb_alist (LUPDATE (Bnode (lz97 w) w n (EL j bs2)) j bs2)`>>
  simp[]>>
  irule PERM_TRANS>>
  qexists_tac`bucket_alist rest ++ (w,n) :: tb_alist bs2`>>
  simp[PERM_APPEND_IFF,PERM_FUN_APPEND_CONS,tb_alist_LUPDATE_Bnode]
QED

Theorem FOLDL_bucket_move:
  ∀bs bs2.
  (∀b. MEM b bs ⇒ ∃m0 i. bucket_ok m0 i b) ∧ bs2 ≠ [] ∧
  (∀j. j < LENGTH bs2 ⇒ bucket_ok (LENGTH bs2) j (EL j bs2)) ⇒
  LENGTH (FOLDL bucket_move bs2 bs) = LENGTH bs2 ∧
  (∀j. j < LENGTH bs2 ⇒
    bucket_ok (LENGTH bs2) j (EL j (FOLDL bucket_move bs2 bs))) ∧
  PERM (tb_alist (FOLDL bucket_move bs2 bs)) (tb_alist bs ++ tb_alist bs2)
Proof
  Induct
  >- simp[tb_alist_def]>>
  rpt gen_tac>>
  strip_tac>>
  `∃m0 i. bucket_ok m0 i h` by metis_tac[MEM]>>
  drule_then (qspec_then`bs2` mp_tac) bucket_move_thm>>
  simp[]>>
  strip_tac>>
  first_x_assum (qspec_then`bucket_move bs2 h` mp_tac)>>
  impl_tac
  >- (
    rw[]>>
    strip_tac>>
    gvs[])>>
  strip_tac>>
  gvs[]>>
  irule PERM_TRANS>>
  qexists_tac`tb_alist bs ++ tb_alist (bucket_move bs2 h)`>>
  simp[tb_alist_def]>>
  irule PERM_TRANS>>
  qexists_tac`FLAT (MAP bucket_alist bs) ++ (bucket_alist h ++ FLAT (MAP bucket_alist bs2))`>>
  simp[PERM_APPEND_IFF,GSYM tb_alist_def]>>
  simp[tb_alist_def,PERM_APPEND,APPEND_ASSOC]
QED

Theorem tb_rel_grow:
  tb_rel bs s ∧ LENGTH bs ≤ m2 ∧ m2 < 2 ** 30 ⇒
  tb_rel (tb_grow bs m2) s
Proof
  strip_tac>>
  gvs[tb_rel_def,tb_grow_def]>>
  `0 < m2` by (Cases_on`bs`>>gvs[])>>
  qspecl_then [`bs`,`REPLICATE m2 Bnil`] mp_tac FOLDL_bucket_move>>
  impl_tac
  >- (
    simp[EL_REPLICATE,bucket_ok_def,REPLICATE_NIL]>>
    metis_tac[MEM_EL])>>
  simp[tb_alist_def,map_replicate,bucket_alist_def,FLAT_REPLICATE_NIL]>>
  simp[GSYM tb_alist_def]>>
  strip_tac>>
  qabbrev_tac`bs2 = FOLDL bucket_move (REPLICATE m2 Bnil) bs`>>
  `bs2 ≠ []` by (strip_tac>>gvs[])>>
  `ALL_DISTINCT (MAP FST (tb_alist bs2))` by
    metis_tac[ALL_DISTINCT_PERM,PERM_MAP]>>
  rw[]>>
  DEP_REWRITE_TAC[tb_lookup_ALOOKUP]>>
  simp[]>>
  `ALOOKUP (tb_alist bs) = ALOOKUP (tb_alist bs2)` suffices_by simp[]>>
  irule ALOOKUP_ALL_DISTINCT_PERM_same>>
  `PERM (tb_alist bs) (tb_alist bs2)` by simp[Once PERM_SYM]>>
  metis_tac[PERM_LIST_TO_SET,PERM_MAP]
QED

Theorem strsub_substring:
  a < n ∧ i + n ≤ strlen s ⇒
  strsub (substring s i n) a = strsub s (i + a)
Proof
  Cases_on`s`>>
  rw[mlstringTheory.strsub_def,mlstringTheory.substring_def,
     SEG_TAKE_DROP,EL_TAKE,EL_DROP]
QED

Theorem substring_substring:
  a + b ≤ n ∧ i + n ≤ strlen s ⇒
  substring (substring s i n) a b = substring s (i + a) b
Proof
  Cases_on`s`>>
  rw[mlstringTheory.substring_def,SEG_TAKE_DROP,TAKE_TAKE,DROP_DROP,DROP_TAKE]
QED

Theorem fromChars_range_unsafe_substring:
  ∀n p len s.
  n ≤ len ∧ p + len ≤ strlen s ⇒
  fromChars_range_unsafe 0 n (substring s p len) = fromChars_range_unsafe p n s
Proof
  Induct>>
  rw[fromChars_range_unsafe_def,strsub_substring]
QED

Theorem EL_explode_strsub:
  a < strlen t ⇒ EL a (explode t) = strsub t a
Proof
  Cases_on`t`>>
  simp[mlstringTheory.strsub_def]
QED

Theorem fromChars_substring_NONE:
  p ≤ q ∧ q < p + n ∧ p + n ≤ strlen s ∧ ¬isDigit (strsub s q) ⇒
  fromChars n (substring s p n) = NONE
Proof
  strip_tac>>
  `¬IS_SOME (fromChars n (substring s p n))` suffices_by
    (Cases_on`fromChars n (substring s p n)`>>simp[])>>
  DEP_REWRITE_TAC [mlintTheory.fromChars_IS_SOME_IFF]>>
  simp[mlstringTheory.strlen_substring,TAKE_LENGTH_ID_rwt,EXISTS_MEM,MEM_EL,
       PULL_EXISTS]>>
  qexists_tac`q - p`>>
  simp[EL_explode_strsub,strsub_substring,mlstringTheory.strlen_substring]
QED

Theorem fromChars_substring_SOME:
  (∀q. p ≤ q ∧ q < p + n ⇒ isDigit (strsub s q)) ∧ 0 < n ∧ p + n ≤ strlen s ⇒
  fromChars n (substring s p n) = SOME (fromChars_range_unsafe p n s)
Proof
  strip_tac>>
  DEP_REWRITE_TAC [mlintTheory.fromChars_eq_unsafe]>>
  simp[mlstringTheory.strlen_substring,mlintTheory.fromChars_range_unsafe_eq,
       fromChars_range_unsafe_substring,EVERY_EL,EL_explode_strsub,
       strsub_substring]
QED

Theorem fromChars_range_unsafe_snoc:
  p ≤ j ⇒
  fromChars_range_unsafe p (j + 1 - p) s =
  10 * fromChars_range_unsafe p (j - p) s + (ORD (strsub s j) − 48)
Proof
  strip_tac>>
  `j + 1 - p = SUC (j - p)` by decide_tac>>
  pop_assum SUBST1_TAC>>
  REWRITE_TAC[mlintTheory.fromChars_range_unsafe_def,
              mlintTheory.fromChar_unsafe_def]>>
  simp[]
QED

(*
  Reading the number of a name x<digits> in place. read_nat s i n is
  fromNatString (substring s i (n - i)) (read_nat_fromNatString).
*)
Definition read_digits_def:
  read_digits s i n (acc:num) =
  if smallnum_lt_str i n s then
    let c = ORD (strsub_unsafe s i) in
    if smallnum_le 48 c ∧ smallnum_le c 57 then
      read_digits s (smallnum_add_str i 1 s) n (acc * 10 + smallnum_sub c 48)
    else NONE
  else SOME acc
Termination
  WF_REL_TAC`measure (λ(s,i,n,acc). n - i)`>>
  rw[smallnum_lt_str_def,smallnum_add_str_def]
End

Definition read_nat_def:
  read_nat s i n =
  if smallnum_lt_str i n s then
    let c = strsub_unsafe s i in
    let i1 = smallnum_add_str i 1 s in
    if c = #"+" then
      (if smallnum_lt_str i1 n s then read_digits s i1 n 0 else NONE)
    else if c = #"~" ∨ c = #"-" then
      (if smallnum_lt_str i1 n s then
        case read_digits s i1 n 0 of
          SOME m => if m = 0 then SOME 0 else NONE
        | NONE => NONE
      else NONE)
    else read_digits s i n 0
  else NONE
End

(* acc holds the value of the digits read from p *)
Theorem read_digits_thm:
  ∀s i n acc p.
  i ≤ n ∧ n ≤ strlen s ∧ p ≤ i ∧ acc = fromChars_range_unsafe p (i - p) s ⇒
  read_digits s i n acc =
  if (∀q. i ≤ q ∧ q < n ⇒ isDigit (strsub s q))
  then SOME (fromChars_range_unsafe p (n - p) s)
  else NONE
Proof
  ho_match_mp_tac read_digits_ind>>
  rpt strip_tac>>
  simp[Once read_digits_def]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_le_def,
     smallnum_sub_def,mlstringTheory.strsub_unsafe_eq_strsub]>>
  reverse (Cases_on`i < n`)>>
  fs[]
  >- (
    `i = n` by decide_tac>>
    simp[])>>
  `(∀q. i ≤ q ∧ q < n ⇒ isDigit (strsub s q)) ⇔
   isDigit (strsub s i) ∧ ∀q. i + 1 ≤ q ∧ q < n ⇒ isDigit (strsub s q)` by (
    eq_tac>>
    rw[]>>
    Cases_on`q = i`>>
    gvs[])>>
  pop_assum SUBST1_TAC>>
  simp[isDigit_def]>>
  IF_CASES_TAC>>
  fs[]>>
  first_x_assum (qspec_then`p` mp_tac)>>
  simp[fromChars_range_unsafe_snoc,isDigit_def]
QED

(* On a non-empty suffix, read_digits from 0 is fromChars *)
Theorem read_digits_fromChars[local]:
  j < strlen s ⇒
  read_digits s j (strlen s) 0 =
  fromChars (strlen s - j) (substring s j (strlen s - j))
Proof
  strip_tac>>
  `read_digits s j (strlen s) 0 =
   if (∀q. j ≤ q ∧ q < strlen s ⇒ isDigit (strsub s q))
   then SOME (fromChars_range_unsafe j (strlen s - j) s)
   else NONE` by (
    irule read_digits_thm>>
    simp[fromChars_range_unsafe_def])>>
  pop_assum SUBST1_TAC>>
  IF_CASES_TAC
  >- (
    DEP_REWRITE_TAC[fromChars_substring_SOME]>>
    simp[])>>
  fs[]>>
  simp[Once EQ_SYM_EQ]>>
  irule fromChars_substring_NONE>>
  simp[]>>
  qexists_tac`q`>>
  simp[]
QED

Theorem read_nat_fromNatString:
  n = strlen s ∧ 1 ≤ n ⇒
  read_nat s 1 n = fromNatString (substring s 1 (n - 1))
Proof
  rw[]>>
  simp[read_nat_def,fromNatString_def,fromString_def,smallnum_lt_str_def,
       smallnum_add_str_def,mlstringTheory.strsub_unsafe_eq_strsub,
       mlstringTheory.strlen_substring]>>
  Cases_on`strlen s = 1`>>
  simp[]>>
  `strsub (substring s 1 (strlen s - 1)) 0 = strsub s 1` by
    simp[strsub_substring]>>
  `substring (substring s 1 (strlen s - 1)) 1 (strlen s - 2) =
   substring s 2 (strlen s - 2)` by
    simp[substring_substring]>>
  simp[]>>
  Cases_on`strlen s = 2`
  >- (
    simp[read_digits_fromChars,fromChars_def]>>
    rw[]>>
    Cases_on`fromChars 1 (substring s 1 1)`>>
    simp[])>>
  simp[read_digits_fromChars]>>
  Cases_on`strsub s 1 = #"+"`>>
  simp[]
  >- (
    Cases_on`fromChars (strlen s - 2) (substring s 2 (strlen s - 2))`>>
    simp[])>>
  Cases_on`strsub s 1 = #"~" ∨ strsub s 1 = #"-"`>>
  simp[]
  >- (
    Cases_on`fromChars (strlen s - 2) (substring s 2 (strlen s - 2))`>>
    simp[]>>
    rename1`SOME m`>>
    Cases_on`m`>>
    simp[])>>
  Cases_on`fromChars (strlen s - 1) (substring s 1 (strlen s - 1))`>>
  simp[]
QED

Definition x_initial_def:
  x_initial s ⇔ smallnum_lt_str 0 (strlen s) s ∧ strsub_unsafe s 0 = #"x"
End

Theorem x_initial_thm:
  x_initial s ⇔ 1 ≤ strlen s ∧ strsub s 0 = #"x"
Proof
  rw[x_initial_def,smallnum_lt_str_def,mlstringTheory.strsub_unsafe_eq_strsub]>>
  eq_tac>>
  rw[]
QED

(*
  Numbering one name. With no limit, every name is numbered by the table.
  With limit SOME l, as for the CNF frontend: a name x<n> with n ≤ l is
  the number n and is not stored, another name starting with x that is
  not x<n> is rejected, and every other name is numbered by the table.
*)
Definition res_var_def:
  res_var lim v s =
  case lim of
    NONE => SOME (name_to_num_var v s)
  | SOME l =>
    if 1 ≤ strlen v ∧ strsub v 0 = #"x" then
      case fromNatString (substring v 1 (strlen v - 1)) of
        NONE => NONE
      | SOME n => if n ≤ l then SOME (n,s) else SOME (name_to_num_var v s)
    else SOME (name_to_num_var v s)
End

Theorem res_var_NONE:
  res_var NONE v s = SOME (name_to_num_var v s)
Proof
  simp[res_var_def]
QED

(*
  Numbering the parts of a constraint, left to right
*)
Definition name_lit_def:
  (name_lit lim (Pos v) s =
    case res_var lim v s of
      NONE => NONE
    | SOME (n,s1) => SOME (Pos n,s1)) ∧
  (name_lit lim (Neg v) s =
    case res_var lim v s of
      NONE => NONE
    | SOME (n,s1) => SOME (Neg n,s1))
End

Definition name_lin_def:
  (name_lin lim [] s = SOME ([],s)) ∧
  (name_lin lim ((c,l)::xs) s =
    case name_lit lim l s of
      NONE => NONE
    | SOME (l1,s1) =>
      case name_lin lim xs s1 of
        NONE => NONE
      | SOME (xs1,s2) => SOME ((c:int,l1)::xs1,s2))
End

Definition name_lits_def:
  (name_lits lim [] s = SOME ([],s)) ∧
  (name_lits lim (l::ls) s =
    case name_lit lim l s of
      NONE => NONE
    | SOME (l1,s1) =>
      case name_lits lim ls s1 of
        NONE => NONE
      | SOME (ls1,s2) => SOME (l1::ls1,s2))
End

Definition name_pbhd_def:
  (name_pbhd lim (Fwd ls rel) s =
    case name_lits lim ls s of
      NONE => NONE
    | SOME (ls1,s1) => SOME (Fwd ls1 rel,s1)) ∧
  (name_pbhd lim (Bwd l op) s =
    case name_lit lim l s of
      NONE => NONE
    | SOME (l1,s1) => SOME (Bwd l1 op,s1)) ∧
  (name_pbhd lim (Iff l op) s =
    case name_lit lim l s of
      NONE => NONE
    | SOME (l1,s1) => SOME (Iff l1 op,s1))
End

Definition name_pbc_def:
  name_pbc lim ((p,l,i):mlstring pbc) s =
    case name_pbhd lim p s of
      NONE => NONE
    | SOME (p1,s1) =>
      case name_lin lim l s1 of
        NONE => NONE
      | SOME (l1,s2) => SOME ((p1,l1,i),s2)
End

Definition name_vars_def:
  (name_vars lim [] s = SOME ([],s)) ∧
  (name_vars lim (v::vs) s =
    case res_var lim v s of
      NONE => NONE
    | SOME (n,s1) =>
      case name_vars lim vs s1 of
        NONE => NONE
      | SOME (ns,s2) => SOME (n::ns,s2))
End

Definition name_assg_def:
  (name_assg lim [] s = SOME ([],s)) ∧
  (name_assg lim ((v,b:bool)::vs) s =
    case res_var lim v s of
      NONE => NONE
    | SOME (n,s1) =>
      case name_assg lim vs s1 of
        NONE => NONE
      | SOME (ns,s2) => SOME ((n,b)::ns,s2))
End

(* With no limit the numbering is name_to_num's *)
Theorem name_lit_NONE:
  name_lit NONE l s = SOME (name_to_num_lit l s)
Proof
  Cases_on`l`>>
  simp[name_lit_def,name_to_num_lit_def,res_var_def]>>
  Cases_on`name_to_num_var a s`>>
  simp[]
QED

Theorem name_lin_NONE_acc[local]:
  ∀xs s acc. ∃ys t.
    name_lin NONE xs s = SOME (ys,t) ∧
    name_to_num_lin_term xs s acc = (REVERSE acc ++ ys,t)
Proof
  Induct>>
  simp[name_lin_def,name_to_num_lin_term_def]>>
  PairCases>>
  rw[name_lin_def,name_to_num_lin_term_def,name_lit_NONE]>>
  pairarg_tac>>
  gvs[]>>
  first_x_assum (qspecl_then [`s1`,`(h0,l1)::acc`] strip_assume_tac)>>
  simp[]
QED

Theorem name_lin_NONE:
  ∀xs s. name_lin NONE xs s = SOME (name_to_num_lin_term xs s [])
Proof
  rpt gen_tac>>
  qspecl_then [`xs`,`s`,`[]`] strip_assume_tac name_lin_NONE_acc>>
  simp[]
QED

Theorem name_lits_NONE_acc[local]:
  ∀ls s acc. ∃ys t.
    name_lits NONE ls s = SOME (ys,t) ∧
    name_to_num_lits ls s acc = (REVERSE acc ++ ys,t)
Proof
  Induct>>
  rw[name_lits_def,name_to_num_lits_def,name_lit_NONE]>>
  pairarg_tac>>
  gvs[]>>
  first_x_assum (qspecl_then [`s1`,`l1::acc`] strip_assume_tac)>>
  simp[]
QED

Theorem name_pbhd_NONE:
  name_pbhd NONE p s = SOME (name_to_num_pbhd p s)
Proof
  Cases_on`p`>>
  simp[name_pbhd_def,name_to_num_pbhd_def,name_lit_NONE]
  >- (
    qspecl_then [`l`,`s`,`[]`] strip_assume_tac name_lits_NONE_acc>>
    simp[])>>
  pairarg_tac>>simp[]
QED

Theorem name_pbc_NONE:
  name_pbc NONE c s = SOME (name_to_num_pbc c s)
Proof
  PairCases_on`c`>>
  simp[name_pbc_def,name_to_num_pbc_def,name_pbhd_NONE,name_lin_NONE]>>
  rpt (pairarg_tac>>simp[])
QED

Theorem name_vars_NONE_acc[local]:
  ∀vs s acc. ∃ys t.
    name_vars NONE vs s = SOME (ys,t) ∧
    name_to_num_list vs s acc = (REVERSE acc ++ ys,t)
Proof
  Induct>>
  rw[name_vars_def,name_to_num_list_def,res_var_def]>>
  pairarg_tac>>
  gvs[]>>
  first_x_assum (qspecl_then [`s1`,`v1::acc`] strip_assume_tac)>>
  simp[]
QED

Theorem name_vars_NONE:
  ∀vs s. name_vars NONE vs s = SOME (name_to_num_list vs s [])
Proof
  rpt gen_tac>>
  qspecl_then [`vs`,`s`,`[]`] strip_assume_tac name_vars_NONE_acc>>
  simp[]
QED
