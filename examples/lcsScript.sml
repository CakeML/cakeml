(*
   Verification of longest common subsequence algorithms.
*)
open preamble;

val _ = new_theory "lcs";

(* Miscellaneous lemmas that may belong elsewhere *)

val sub_suc_0 = Q.prove(`x - SUC x = 0`,
  Induct_on `x` >> fs[SUB]);

val take_suc_length = Q.prove(`TAKE (SUC (LENGTH l)) l = l`,
  Induct_on `l` >> fs[])

val is_suffix_length = Q.prove(`IS_SUFFIX l1 l2 ==> LENGTH l1 >= LENGTH l2`,
  rpt strip_tac
  >> first_assum(assume_tac o MATCH_MP IS_SUFFIX_IS_SUBLIST)
  >> fs[IS_SUBLIST_APPEND]);

val is_suffix_take = Q.prove(`
  IS_SUFFIX l (h::r) ==>
  (TAKE (LENGTH l − LENGTH r) l = TAKE (LENGTH l − SUC(LENGTH r)) l ++ [h])`,
  fs[IS_SUFFIX_APPEND]
  >> rpt strip_tac
  >> fs[]
  >> fs[TAKE_APPEND, GSYM ADD1, take_suc_length, sub_suc_0]);

val is_suffix_drop = Q.prove(`
IS_SUFFIX l (h::r) ==> (DROP (LENGTH l − SUC(LENGTH r)) l = h::r)`,
  fs[IS_SUFFIX_APPEND]
  >> rpt strip_tac
  >> fs[]
  >> fs[GSYM ADD1]
  >> PURE_REWRITE_TAC [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
  >> fs[]);

val suc_ge = Q.prove(`(SUC x >= SUC y) = (x >= y)`, fs[]);

val take_singleton_one = Q.prove(`
  (TAKE n r = [e]) ==> (TAKE 1 r = [e])`,
  Cases_on `r` >> Cases_on `n` >> fs[]);

val sub_le_suc = Q.prove(`n ≥ SUC m ==> (n + SUC l − SUC m = n + l − m)`, fs[]);

val if_length_lemma = Q.prove(`TAKE (if LENGTH r <= 1 then 1 else LENGTH r) r = r`,
  Induct_on `r` >> rw[] >> Cases_on `r` >> fs[]);

(* The predicate
    lcs l1 l2 l3
   is true iff l1 is the longest common subsequence of l2 and l3. *)

val is_subsequence_def =
Define `(is_subsequence [] l = T) ∧
(is_subsequence (f::r) l =
 case l of
    | [] => F
    | f'::r' =>
      (((f = f') /\ is_subsequence r r') \/ is_subsequence (f::r) r'))`

val common_subsequence_def =
Define `common_subsequence s t u =
         (is_subsequence s t ∧ is_subsequence s u)`

val lcs_def =
Define `lcs s t u =
         (common_subsequence s t u ∧
          (∀s'. common_subsequence s' t u ⇒ LENGTH s' <= LENGTH s))`

(* Properties of lcs and its auxiliary functions *)

Theorem is_subsequence_nil:
    (is_subsequence l [] = (l = [])) /\ (is_subsequence [] l = T)
Proof
  Induct_on `l` >> fs[is_subsequence_def]
QED

Theorem is_subsequence_cons:
    is_subsequence (f::r) (h::r') =
  (((f = h) /\ is_subsequence r r') \/ is_subsequence (f::r) r')
Proof
  fs[Once is_subsequence_def]
QED

Theorem is_subsequence_single:
   is_subsequence s [h] = ((s = [h]) \/ (s = []))
Proof
  Cases_on `s`
  >> fs[is_subsequence_nil,is_subsequence_cons]
QED

Theorem is_subsequence_refl:
    is_subsequence l l = T
Proof
  Induct_on `l` >> fs[is_subsequence_nil,is_subsequence_cons]
QED

Theorem prefix_is_subsequence:
    ! s l s'.
  (is_subsequence (s ++ s') l ==> is_subsequence s l)
Proof
   ho_match_mp_tac (theorem "is_subsequence_ind")
    >> rpt strip_tac
    >- fs[is_subsequence_nil,is_subsequence_cons]
    >> Cases_on `l`
     >- fs[is_subsequence_nil]
     >> fs[is_subsequence_cons]
     >> rw[]
     >> metis_tac[]
QED

Theorem suffix_is_subsequence:
   ! s l s'.
  (is_subsequence (f::s) l ==> is_subsequence s l)
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
   >> rpt strip_tac
   >- fs[is_subsequence_nil,is_subsequence_cons]
   >> Cases_on `l`
    >- fs[is_subsequence_nil]
    >> fs[is_subsequence_cons]
QED

Theorem suffix_is_subsequence':
   !s l. is_subsequence (s' ++ s) l ==> is_subsequence s l
Proof
  Induct_on `s'`
  >> fs[] >> metis_tac[suffix_is_subsequence]
QED

Theorem cons_is_subsequence:
   is_subsequence s l ==> is_subsequence s (f::l)
Proof
  Induct_on `s`
   >> rw[is_subsequence_cons,is_subsequence_nil]
QED

Theorem is_subsequence_snoc:
    !s l f. is_subsequence (s ++ [f]) (l ++ [f]) = is_subsequence s l
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
   >- (Induct_on `l` >> fs[is_subsequence_nil,is_subsequence_cons])
  >> fs[is_subsequence_nil,is_subsequence_cons]
  >> Cases_on `l`
  >> rfs[is_subsequence_nil,is_subsequence_cons] >> metis_tac[]
QED

Theorem is_subsequence_snoc':
   !r r'. is_subsequence (r ++ [f]) (r' ++ [h]) =
   (((f = h) /\ is_subsequence r r') \/ is_subsequence (r ++ [f]) r')
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >> fs[is_subsequence_cons,is_subsequence_nil]
  >> Induct_on `r'` >> rpt strip_tac >> fs[is_subsequence_nil,is_subsequence_cons]
  >> metis_tac[]
QED

Theorem snoc_is_subsequence:
    !s l f. is_subsequence s l ==> is_subsequence s (l++[f])
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> rw[is_subsequence_snoc',is_subsequence_nil,SNOC_APPEND]
QED

Theorem is_subsequence_appendr:
    !l' s l. is_subsequence s l ==> is_subsequence s (l++l')
Proof
  Induct
  >> rpt strip_tac >> fs[]
  >> drule snoc_is_subsequence
  >> disch_then(qspec_then `h` assume_tac)
  >> first_x_assum drule
  >> FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC,GSYM CONS_APPEND]
QED

Theorem is_subsequence_appendl:
    !l' s l. is_subsequence s l ==> is_subsequence s (l'++l)
Proof
  Induct
  >> rpt strip_tac >> fs[]
  >> match_mp_tac cons_is_subsequence >> metis_tac[]
QED

Theorem is_subsequence_append:
   !l l' r r'. is_subsequence l l' /\ is_subsequence r r' ==> is_subsequence(l++r) (l'++r')
Proof
  ho_match_mp_tac (fetch "lcs" "is_subsequence_ind")
  >> rpt strip_tac
  >- (fs[is_subsequence_def] >> metis_tac[is_subsequence_appendl])
  >> Cases_on `l'`
  >- fs[is_subsequence_def]
  >> fs[is_subsequence_cons]
QED

Theorem is_subsequence_length:
    !l l'. is_subsequence l l' ==> LENGTH l <= LENGTH l'
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l'`
  >- fs[is_subsequence_nil]
  >> fs[is_subsequence_cons]
  >> metis_tac [suffix_is_subsequence]
QED

Theorem is_subsequence_cons':
    !s l f. is_subsequence s (f::l)
  ==> ((((s = []) \/ f ≠ HD s) /\ is_subsequence s l)
      \/ (((s ≠ []) /\ (f = HD s)) /\ is_subsequence (TL s) l))
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l`
  >- fs[is_subsequence_nil, Once is_subsequence_def]
  >- (Cases_on `f' = f`
     >> fs[is_subsequence_cons] >> rfs[]
     >> metis_tac [cons_is_subsequence])
QED

Theorem is_subsequence_snoc'':
    !s l f. is_subsequence s (l ++ [f])
  ==> ((((s = []) \/ f ≠ LAST s) /\ is_subsequence s l)
       \/ (((s ≠ []) /\ (f = LAST s)) /\ is_subsequence (FRONT s) l))
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l`
  >- fs[is_subsequence_nil, Once is_subsequence_def]
  >- (Cases_on `f' = f`
     >> fs[is_subsequence_snoc'] >> fs[is_subsequence_cons]
     >> rpt(first_x_assum(ASSUME_TAC o Q.SPEC `f'`))
     >> rfs[is_subsequence_nil] >> Cases_on `s` >> fs[is_subsequence_nil,is_subsequence_cons])
QED

Theorem common_subsequence_append:
   common_subsequence a b c /\ common_subsequence a' b' c' ==> common_subsequence(a++a') (b++b') (c++c')
Proof
  fs[common_subsequence_def,is_subsequence_append]
QED

Theorem common_subsequence_sym:
   common_subsequence u u u
Proof
  fs[common_subsequence_def,is_subsequence_refl]
QED

Theorem common_subsequence_sym:
   common_subsequence s u t = common_subsequence s t u
Proof
  fs[common_subsequence_def,EQ_IMP_THM]
QED

Theorem lcs_refl:
   lcs l l l
Proof
  fs[lcs_def,common_subsequence_def,is_subsequence_refl,is_subsequence_length]
QED

val is_subsequence_greater = Q.prove(
  `!l' l. is_subsequence l' l /\ LENGTH l ≤ LENGTH l'
  ==> l = l'`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
   >- fs[quantHeuristicsTheory.LIST_LENGTH_0]
   >> Cases_on `l`
    >> fs[is_subsequence_cons,is_subsequence_nil]
    >> rfs[]);

Theorem lcs_refl':
   lcs l' l l = (l = l')
Proof
  fs[lcs_def,common_subsequence_def,EQ_IMP_THM,is_subsequence_refl,is_subsequence_length]
  >> rpt strip_tac
  >> first_x_assum(assume_tac o Q.SPEC `l`)
  >> fs[is_subsequence_refl,is_subsequence_greater]
QED

Theorem lcs_sym:
   lcs l l' l'' = lcs l l'' l'
Proof
  metis_tac[lcs_def,common_subsequence_sym]
QED

val lcs_empty = Q.prove(`lcs [] l [] /\ lcs [] [] l`,
  fs[lcs_def,common_subsequence_def,is_subsequence_nil]);

Theorem lcs_empty':
   (lcs l l' [] = (l = [])) /\ (lcs l [] l' = (l = []))
Proof
  fs[lcs_def,common_subsequence_def,is_subsequence_nil,EQ_IMP_THM]
QED

Theorem common_subsequence_empty':
   (common_subsequence l l' [] = (l = [])) /\ (common_subsequence l [] l' = (l = []))
Proof
  fs[common_subsequence_def,is_subsequence_nil,EQ_IMP_THM]
QED

Theorem cons_lcs_optimal_substructure:
   lcs (f::l) (f::l') (f::l'') = lcs l l' l''
Proof
  fs[lcs_def,common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >> first_assum(ASSUME_TAC o Q.SPEC `f::s'`)
  >> fs[is_subsequence_cons]
  >> TRY(metis_tac[suffix_is_subsequence])
  >> rpt(first_x_assum(assume_tac o MATCH_MP is_subsequence_cons'))
  >> fs[]
   >- metis_tac[cons_is_subsequence, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]
   >- metis_tac[cons_is_subsequence, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]
   >- metis_tac[cons_is_subsequence, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]
   >- (`LENGTH(TL s') ≤ LENGTH l` by metis_tac[cons_is_subsequence, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]
       >> Cases_on `s'`
       >> fs[])
QED

Theorem cons_common_subsequence:
   common_subsequence (f::l) (f::l') (f::l'') = common_subsequence l l' l''
Proof
  fs[common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >> fs[is_subsequence_cons]
  >> metis_tac[suffix_is_subsequence]
QED

Theorem snoc_lcs_optimal_substructure:
   lcs (l ++ [f]) (l' ++ [f]) (l'' ++ [f]) = lcs l l' l''
Proof
  fs[lcs_def,common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >> first_assum(ASSUME_TAC o Q.SPEC `s' ++ [f]`)
  >> rpt(first_x_assum(assume_tac o MATCH_MP is_subsequence_snoc''))
  >> fs[is_subsequence_snoc,FRONT_APPEND]
  >> TRY(metis_tac[prefix_is_subsequence])
   >- (`LENGTH s' ≤ LENGTH l` by fs[] >> fs[])
   >- (`LENGTH(FRONT s') ≤ LENGTH l` by fs[] >> Cases_on `s'` >> fs[])
QED

Theorem cons_lcs_optimal_substructure_left:
   f ≠ f' /\ lcs l (f::l') l''
    /\ lcs l''' l' (f'::l'')
    /\ LENGTH l >= LENGTH l'''
   ==> lcs l (f::l') (f'::l'')
Proof
  fs[lcs_def,common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >- metis_tac[cons_is_subsequence]
  >> PAT_ASSUM ``is_subsequence s' (f'::l'')`` (assume_tac o MATCH_MP is_subsequence_cons')
  >> PAT_ASSUM ``is_subsequence s' (f::l')`` (assume_tac o MATCH_MP is_subsequence_cons')
  >> fs[is_subsequence_cons]
  >> Cases_on `s'`
  >> fs[is_subsequence_cons]
  >> `LENGTH(h::t) ≤ LENGTH l'''` by(first_assum match_mp_tac >> fs[is_subsequence_cons])
  >> fs[]
QED

Theorem snoc_lcs_optimal_substructure_left:
   f ≠ f' /\ lcs l (l' ++ [f]) l''
    /\ lcs l''' l' (l''++[f'])
    /\ LENGTH l >= LENGTH l'''
   ==> lcs l (l'++[f]) (l''++[f'])
Proof
  fs[lcs_def,common_subsequence_def, is_subsequence_snoc', EQ_IMP_THM]
  >> rpt strip_tac
  >- metis_tac[snoc_is_subsequence]
  >> PAT_ASSUM ``is_subsequence s' (l''++[f'])`` (assume_tac o MATCH_MP is_subsequence_snoc'')
  >> PAT_ASSUM ``is_subsequence s' (l'++[f])`` (assume_tac o MATCH_MP is_subsequence_snoc'')
  >> fs[is_subsequence_cons]
  >> FULL_STRUCT_CASES_TAC (Q.SPEC `s'` SNOC_CASES)
  >> fs[is_subsequence_snoc',SNOC_APPEND]
  >> `LENGTH(l''''++[x]) ≤ LENGTH l'''` by(first_assum match_mp_tac >> fs[is_subsequence_snoc'])
  >> fs[]
QED

Theorem cons_lcs_optimal_substructure_right:
    f ≠ f' /\ lcs l (f::l') l''
    /\ lcs l''' l' (f'::l'')
    /\ LENGTH l''' >= LENGTH l
  ==> lcs l''' (f::l') (f'::l'')
Proof
  metis_tac[cons_lcs_optimal_substructure_left,lcs_sym]
QED

Theorem snoc_lcs_optimal_substructure_right:
    f ≠ f' /\ lcs l (l'++[f]) l''
    /\ lcs l''' l' (l''++[f'])
    /\ LENGTH l''' >= LENGTH l
  ==> lcs l''' (l'++[f]) (l''++[f'])
Proof
  metis_tac[snoc_lcs_optimal_substructure_left,lcs_sym]
QED

Theorem lcs_length_left:
    (lcs xl yl zl /\ lcs xl' (yl ++ [y]) zl)
  ==> SUC(LENGTH xl) >= LENGTH xl'
Proof
  fs[lcs_def,common_subsequence_def] >> rpt strip_tac
  >> first_assum(assume_tac o MATCH_MP is_subsequence_snoc'')
  >> fs[]
   >- (`LENGTH xl' <= LENGTH xl` by metis_tac[] >> fs[])
   >> FULL_STRUCT_CASES_TAC (Q.SPEC `xl'` SNOC_CASES)
   >> fs[SNOC_APPEND]
   >> rpt(first_x_assum(assume_tac o MATCH_MP prefix_is_subsequence))
   >> `LENGTH l <= LENGTH xl` by metis_tac[] >> fs[]
QED

Theorem lcs_length_right:
    (lcs xl yl zl /\ lcs xl' (yl) (zl ++ [z]))
  ==> SUC(LENGTH xl) >= LENGTH xl'
Proof
  metis_tac[lcs_sym,lcs_length_left]
QED

Theorem lcs_length:
   !l l' r r'. lcs l r r' /\ lcs l' r r' ==> LENGTH l = LENGTH l'
Proof
  rpt strip_tac >> fs[lcs_def]
  >> metis_tac[EQ_LESS_EQ]
QED

Theorem is_subsequence_rev:
    !l r. is_subsequence (REVERSE l) (REVERSE r) = is_subsequence l r
Proof
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >> fs[is_subsequence_nil]
  >> Cases_on `r`
  >> fs[is_subsequence_nil,is_subsequence_snoc',is_subsequence_cons]
QED

Theorem is_subsequence_rev':
    !l r. is_subsequence l (REVERSE r) = is_subsequence (REVERSE l) r
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> strip_tac
   >- fs[is_subsequence_nil]
   >> rpt strip_tac
   >> Induct_on `r`
   >> fs[is_subsequence_nil,is_subsequence_cons,is_subsequence_snoc',SNOC_APPEND,REVERSE_APPEND]
QED

Theorem common_subsequence_rev:
   !l r s. common_subsequence (REVERSE l) (REVERSE r) (REVERSE s) = common_subsequence l r s
Proof
  rw[common_subsequence_def,is_subsequence_rev]
QED

Theorem common_subsequence_rev':
   !l r s. common_subsequence l (REVERSE r) (REVERSE s) = common_subsequence (REVERSE l) r s
Proof
  rw[common_subsequence_def,is_subsequence_rev']
QED

Theorem lcs_rev:
   !l r s. lcs (REVERSE l) (REVERSE r) (REVERSE s) = lcs l r s
Proof
  rw[common_subsequence_rev',lcs_def,EQ_IMP_THM]
  >> metis_tac[LENGTH_REVERSE,REVERSE_REVERSE]
QED

Theorem lcs_rev':
   !l r s. lcs l (REVERSE r) (REVERSE s) = lcs (REVERSE l) r s
Proof
  rw[common_subsequence_rev',lcs_def,EQ_IMP_THM]
  >> metis_tac[LENGTH_REVERSE,REVERSE_REVERSE]
QED

Theorem lcs_drop_ineq:
 (lcs (f::r) (h::l) l' /\ f ≠ h) ==> lcs (f::r) l l'
Proof
  rpt strip_tac
  >> fs[lcs_def,common_subsequence_def,Once is_subsequence_cons]
  >> metis_tac[cons_is_subsequence]
QED

Theorem common_subsequence_drop_ineq:
 (common_subsequence (f::r) (h::l) l' /\ f ≠ h) ==> common_subsequence (f::r) l l'
Proof
  rpt strip_tac
  >> fs[common_subsequence_def,Once is_subsequence_cons]
  >> metis_tac[cons_is_subsequence]
QED

Theorem lcs_split:
   lcs (f::r) l l' ==> ?ll lr. SPLITP ($= f) l = (ll,f::lr)
Proof
  Induct_on `l`
  >> rw[lcs_empty',SPLITP]
  >> fs[SPLITP]
  >> metis_tac[lcs_drop_ineq,SND]
QED

Theorem common_subsequence_split:
   common_subsequence (f::r) l l' ==> ?ll lr. SPLITP ($= f) l = (ll,f::lr)
Proof
  Induct_on `l`
  >> rw[common_subsequence_empty',SPLITP]
  >> fs[SPLITP]
  >> metis_tac[common_subsequence_drop_ineq,SND]
QED

Theorem lcs_split2:
   lcs (f::r) l l' ==> ?ll lr. SPLITP ($= f) l' = (ll,f::lr)
Proof
  metis_tac[lcs_split,lcs_sym]
QED

Theorem common_subsequence_split2:
   common_subsequence (f::r) l l' ==> ?ll lr. SPLITP ($= f) l' = (ll,f::lr)
Proof
  metis_tac[common_subsequence_split,common_subsequence_sym]
QED

Theorem lcs_split_lcs:
   lcs (f::r) l l' ==> lcs (f::r) (SND(SPLITP ($= f) l)) l'
Proof
  Induct_on `l`
  >> rw[lcs_empty',SPLITP]
  >> metis_tac[lcs_drop_ineq,SND]
QED

Theorem common_subsequence_split_css:
   common_subsequence (f::r) l l' ==> common_subsequence (f::r) (SND(SPLITP ($= f) l)) l'
Proof
  Induct_on `l`
  >> rw[common_subsequence_empty',SPLITP]
  >> metis_tac[common_subsequence_drop_ineq,SND]
QED

Theorem lcs_split_lcs2:
   lcs (f::r) l l' ==> lcs (f::r) l (SND(SPLITP ($= f) l'))
Proof
  metis_tac[lcs_split_lcs,lcs_sym]
QED

Theorem common_subsequence_split_css2:
   common_subsequence (f::r) l l' ==> common_subsequence (f::r) l (SND(SPLITP ($= f) l'))
Proof
  metis_tac[common_subsequence_split_css,common_subsequence_sym]
QED

Theorem split_lcs_optimal_substructure:
   lcs (f::r) l l' ==> lcs r (TL(SND(SPLITP ($= f) l))) (TL(SND(SPLITP ($= f) l')))
Proof
  rpt strip_tac >>
  drule lcs_split >> drule lcs_split2 >>
  pop_assum (assume_tac o MATCH_MP lcs_split_lcs2 o MATCH_MP lcs_split_lcs)
  >> rpt strip_tac
  >> fs[cons_lcs_optimal_substructure]
QED

Theorem split_common_subsequence:
   common_subsequence (f::r) l l' ==> common_subsequence r (TL(SND(SPLITP ($= f) l))) (TL(SND(SPLITP ($= f) l')))
Proof
  rpt strip_tac >>
  drule common_subsequence_split >> drule common_subsequence_split2 >>
  pop_assum (assume_tac o MATCH_MP common_subsequence_split_css2 o MATCH_MP common_subsequence_split_css)
  >> rpt strip_tac
  >> fs[cons_common_subsequence]
QED

Theorem lcs_max_length:
   !l t t'. lcs l t t' ==> 2 * LENGTH l <= LENGTH t + LENGTH t'
Proof
  rpt strip_tac >> fs[lcs_def,common_subsequence_def]
  >> drule is_subsequence_length >> qpat_x_assum `is_subsequence _ _` kall_tac
  >> drule is_subsequence_length >> fs[]
QED

(* A naive, exponential-time LCS algorithm that's easy to verify *)

val longest_def =
Define `longest l l' = if LENGTH l >= LENGTH l' then l else l'`

val naive_lcs_def =
Define
`(naive_lcs l [] = []) ∧
(naive_lcs [] l = []) ∧
(naive_lcs (f::r) (f'::r') =
 if f = f' then
   f::naive_lcs r r'
 else
   longest(naive_lcs (f::r) r') (naive_lcs r (f'::r')))`

(* Properties of the naive lcs algorithm *)

Theorem longest_tail:
   longest (l ++ [e]) (l' ++ [e]) = longest l l' ++ [e]
Proof
  rw[longest_def,GSYM ADD1] >> fs[]
QED

Theorem longest_cons:
   longest (e::l) (e::l') = e::longest l l'
Proof
  rw[longest_def,GSYM ADD1] >> fs[]
QED

Theorem naive_lcs_clauses:
  (naive_lcs l [] = []) ∧
(naive_lcs [] l = []) ∧
(naive_lcs (f::r) (f'::r') =
 if f = f' then
   f::naive_lcs r r'
 else
   longest(naive_lcs (f::r) r') (naive_lcs r (f'::r')))
Proof
  Cases_on `l` >> fs[naive_lcs_def]
QED

Theorem naive_lcs_tail:
    !prevh fullr h. naive_lcs (prevh ++ [h]) (fullr ++ [h]) = naive_lcs prevh fullr ++ [h]
Proof
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rpt strip_tac
   >- (fs[naive_lcs_clauses]
       >> Induct_on `prevh`
       >> rw[naive_lcs_clauses, longest_def])
   >- (rw[naive_lcs_clauses,longest_def]
       >> Induct_on `v3` (*TODO: generated name *)
       >> rw[naive_lcs_clauses,longest_def])
   >> rw[naive_lcs_clauses]
   >> fs[longest_tail]
QED

Theorem naive_lcs_length_bound:
    !l l'. LENGTH (naive_lcs l l') <= MIN (LENGTH l) (LENGTH l')
Proof
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rw[naive_lcs_clauses, MIN_DEF, longest_def]
QED

val naive_lcs_length = Q.prove(
  `!l l' h. LENGTH(naive_lcs l l') + 1 >= LENGTH(naive_lcs l (l' ++ [h]))`,
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rpt strip_tac
  >> fs[naive_lcs_clauses]
  >- (ASSUME_TAC(Q.SPECL [`l`,`[h]`] naive_lcs_length_bound)
      >> fs[])
  >> rw[longest_def] >> fs[GSYM ADD1, suc_ge]
  >> rpt(first_x_assum(assume_tac o Q.SPEC `h`))
  >> fs[]);

val naive_lcs_length' = Q.prove(
  `!l l' h. LENGTH(naive_lcs l l') + 1 >= LENGTH(naive_lcs (l ++ [h]) l')`,
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rpt strip_tac
  >> fs[naive_lcs_clauses]
  >> rw[]
  >- (ASSUME_TAC(Q.SPECL [`[h]`,`v3`] naive_lcs_length_bound)
      >> fs[longest_def])
  >> rw[longest_def] >> fs[GSYM ADD1, suc_ge]
  >> rpt(first_x_assum(assume_tac o Q.SPEC `h`))
  >> fs[]);

(* Main correctness theorem for the naive lcs algorithm *)

Theorem naive_lcs_correct:
   ∀l l'. lcs (naive_lcs l l') l l'
Proof
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rpt strip_tac
  (* Base cases *)
  >- fs[naive_lcs_def,lcs_def,common_subsequence_def,is_subsequence_nil]
  >- fs[naive_lcs_def,lcs_def,common_subsequence_def,is_subsequence_nil]
  (* Inductive step *)
  >> Cases_on `f = f'`
   >- fs[naive_lcs_def,cons_lcs_optimal_substructure]
   >> rw[naive_lcs_def, longest_def]
    >- metis_tac[cons_lcs_optimal_substructure_left]
    >> `LENGTH (naive_lcs l (f'::l')) ≥ (LENGTH (naive_lcs (f::l) l'))` by fs[]
    >> metis_tac[cons_lcs_optimal_substructure_right]
QED

(* A quadratic-time LCS algorithm in dynamic programming style *)

val longest'_def =
Define `longest' (l,n) (l',n') = if n:num >= n' then (l,n) else (l',n')`

val longest'_thm = Q.prove(
  `!l l'. longest' l l' = if SND l >= SND l' then l else l'`,
  Cases >> Cases >> fs[longest'_def]);

val dynamic_lcs_row_def = Define `
   (dynamic_lcs_row h [] previous_col previous_row ddl = [])
∧ (dynamic_lcs_row h (f::r) previous_col previous_row (diagonal,dl) =
    if f = h then
      (let current = longest' (f::diagonal,dl+1) (longest' (HD previous_row) previous_col) in
        current::dynamic_lcs_row h r current (TL previous_row) (HD previous_row))
    else
      (let current = longest' (HD previous_row) previous_col in
        current::dynamic_lcs_row h r current (TL previous_row) (HD previous_row))
   )`;

val dynamic_lcs_rows_def = Define `
  (dynamic_lcs_rows [] r previous_row =
   if previous_row = [] then [] else FST(LAST previous_row)) ∧
  (dynamic_lcs_rows (h::l) r previous_row =
   dynamic_lcs_rows l r (dynamic_lcs_row h r ([],0) previous_row ([],0)))
`;

val dynamic_lcs_def = Define `
  dynamic_lcs l r = REVERSE(dynamic_lcs_rows l r (REPLICATE (LENGTH r) ([],0)))`;

val dynamic_lcs_no_rev_def = Define `
  dynamic_lcs_no_rev l r = dynamic_lcs_rows l r (REPLICATE (LENGTH r) ([],0))`;

(* Verification of dynamic LCS algorithm *)

val dynamic_lcs_row_invariant_def = Define `
  dynamic_lcs_row_invariant h r previous_col previous_row diagonal prevh fullr =
  ((LENGTH r = LENGTH previous_row) ∧ (IS_SUFFIX fullr r) ∧
  (SND previous_col = LENGTH(FST previous_col)) ∧
  (SND diagonal = LENGTH(FST diagonal)) ∧
  (!n. 0 <= n /\ n < LENGTH previous_row ==> (lcs (REVERSE(FST((EL n previous_row)))) prevh (TAKE (SUC n + (LENGTH fullr - LENGTH r)) fullr))) ∧
  (!n. 0 <= n /\ n < LENGTH previous_row ==> (SND(EL n previous_row) = LENGTH(FST(EL n previous_row)))) ∧
   (lcs (REVERSE(FST diagonal)) prevh (TAKE (LENGTH fullr - LENGTH r) fullr)) ∧
   (lcs (REVERSE(FST previous_col)) (SNOC h prevh) (TAKE (LENGTH fullr - LENGTH r) fullr)))`;

val dynamic_lcs_rows_invariant_def = Define `
  dynamic_lcs_rows_invariant h r previous_row fullh =
  ((LENGTH r = LENGTH previous_row) ∧ (IS_SUFFIX fullh h) ∧
  (!n. 0 <= n /\ n < LENGTH previous_row ==> (lcs (REVERSE(FST(EL n previous_row))) (TAKE (LENGTH fullh - LENGTH h) fullh) (TAKE (SUC n) r))) ∧
  (!n. 0 <= n /\ n < LENGTH previous_row ==> (SND(EL n previous_row) = LENGTH(FST(EL n previous_row)))))`;

Theorem dynamic_lcs_row_invariant_pres1:
    dynamic_lcs_row_invariant h (h::r) previous_col previous_row (diagonal,dl) prevh fullr
  ==> dynamic_lcs_row_invariant h r (longest' (h::diagonal,dl+1)
                                             (longest' (HD previous_row) previous_col))
                                (TL previous_row) (HD previous_row) prevh fullr
Proof
 Cases_on `previous_col`
 >> rename1 `(previous_col,pcl)`
 >> fs[dynamic_lcs_row_invariant_def]
 >> rpt strip_tac
  >- (Cases_on `previous_row` >> fs[])
  >- metis_tac[IS_SUFFIX_CONS2_E]
  >- (fs[longest'_thm] >> every_case_tac
      >> fs[] >> first_x_assum(qspec_then `0` assume_tac)
      >> rfs[])
  >- (first_x_assum(qspec_then `0` assume_tac)
      >> rfs[])
  >- (last_x_assum(assume_tac o Q.SPEC `SUC n`)
      >> Cases_on `previous_row` >> fs[]
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC] >> every_case_tac
      >> Cases_on `n`
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[SUB,ADD_CLAUSES] >> rfs[])
  >- (first_x_assum(qspec_then `SUC n` assume_tac)
      >> Cases_on `previous_row` >> fs[])
  >- (last_x_assum(assume_tac o Q.SPEC `0`)
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> Cases_on `previous_row`
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC]
      >> every_case_tac
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[] >> rfs[])
  >- (rw[longest'_thm]
      >> PAT_ASSUM ``IS_SUFFIX fullr (h::r)`` (assume_tac o MATCH_MP is_suffix_take)
      >> fs[SNOC_APPEND,REVERSE_SNOC,snoc_lcs_optimal_substructure] >> rfs[]
       (* longest is from previous row *)
       >- (last_x_assum (assume_tac o Q.SPEC `0`)
           >> first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (h::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[] >> metis_tac[ADD1,lcs_length_right,LENGTH_REVERSE])
       (* longest is from previous column *)
       >- metis_tac[ADD1,lcs_length_left,LENGTH_REVERSE])
QED

Theorem dynamic_lcs_row_invariant_pres2:
    h ≠ f ∧ dynamic_lcs_row_invariant h (f::r) previous_col previous_row diagonal fullh fullr
  ==> dynamic_lcs_row_invariant h r (longest' (HD previous_row) previous_col) (TL previous_row)
                                (HD previous_row) fullh fullr
Proof
 fs[dynamic_lcs_row_invariant_def]
 >> rpt strip_tac
  >- (Cases_on `previous_row` >> fs[])
  >- metis_tac[IS_SUFFIX_CONS2_E]
  >- (first_x_assum(qspec_then `0` assume_tac)
      >> Cases_on `previous_row` >> fs[longest'_thm] >> rw[])
  >- (first_x_assum(qspec_then `0` assume_tac) >> fs[])
  >- (last_x_assum(assume_tac o Q.SPEC `SUC n`)
      >> Cases_on `previous_row` >> fs[]
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC] >> every_case_tac
      >> Cases_on `n`
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[SUB,ADD_CLAUSES] >> rfs[])
  >- (first_x_assum(qspec_then `SUC n` assume_tac) >>
      Cases_on `previous_row` >> rfs[])
  >- (last_x_assum(assume_tac o Q.SPEC `0`)
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> Cases_on `previous_row`
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC]
      >> every_case_tac
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[] >> rfs[])
  >- (rw[longest'_thm]
      >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_take)
      >> fs[SNOC_APPEND,snoc_lcs_optimal_substructure,REVERSE_SNOC] >> rfs[]
       (* longest is from previous row *)
       >- (MATCH_MP_TAC (Q.INST [`l`|->`REVERSE(FST (previous_col:'a list#num))`] snoc_lcs_optimal_substructure_right)
           >> rpt strip_tac >> fs[]
           >> last_x_assum (assume_tac o Q.SPEC `0`)
           >> first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[]) (*TODO: cleanup *)
       (* longest is from previous column *)
       >- (MATCH_MP_TAC (Q.INST [`l'''`|->`REVERSE(FST(HD (previous_row:('a list # num) list)))`] snoc_lcs_optimal_substructure_left)
           >> rpt strip_tac >> fs[]
           >> last_x_assum (assume_tac o Q.SPEC `0`)
           >> first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[]))
QED

Theorem dynamic_lcs_length:
    !h r previous_col previous_row diagonal.
  LENGTH(dynamic_lcs_row h r previous_col previous_row diagonal) = LENGTH r
Proof
  Induct_on `r` >> Cases_on `diagonal` >> rw[dynamic_lcs_row_def]
QED

Theorem dynamic_lcs_row_invariant_pres:
    !h r previous_col previous_row diagonal prevh fullr l n.
  (dynamic_lcs_row_invariant h r previous_col previous_row diagonal prevh fullr
    /\ (dynamic_lcs_row h r previous_col previous_row diagonal = l)
    /\ (0 <= n) /\ (n < LENGTH l))
  ==> (lcs (REVERSE (FST(EL n l))) (prevh ++ [h]) (TAKE (SUC n + (LENGTH fullr - (LENGTH l))) fullr))
Proof
   Induct_on `r`
 >> rpt strip_tac
 >> Cases_on `diagonal`
 >> rename1 `(diagonal,dl)`
 >- (fs[dynamic_lcs_row_def]
      >> metis_tac[LENGTH,prim_recTheory.NOT_LESS_0])
 >> `IS_SUFFIX fullr (h::r)` by fs[dynamic_lcs_row_invariant_def]
 >> first_assum(assume_tac o MATCH_MP is_suffix_length)
 >> first_assum(assume_tac o MATCH_MP is_suffix_take)
 >> Cases_on `n`
  (* 0 requires special treatment since it's outside the range of the inductive hypothesis *)
  >- (rw[dynamic_lcs_row_def]
      (* first element of r is a match *)
      >- (first_x_assum(ASSUME_TAC o MATCH_MP dynamic_lcs_row_invariant_pres1)
          >> fs[dynamic_lcs_row_invariant_def,SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> qpat_x_assum `LENGTH x = LENGTH y` (assume_tac o GSYM)
          >> fs[SUB_LEFT_SUC] >> rw[] >>
          `LENGTH fullr = SUC (LENGTH r)` by fs[] >> fs[])
      (* first element of r is NOT a match *)
      >- (`dynamic_lcs_row_invariant h' r
            (longest' (HD previous_row) previous_col)
            (TL previous_row) (HD previous_row) prevh fullr`
          by (MATCH_MP_TAC(GEN_ALL dynamic_lcs_row_invariant_pres2) >> metis_tac[])
          >> fs[dynamic_lcs_row_invariant_def,SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> qpat_x_assum `LENGTH x = LENGTH y` (assume_tac o GSYM) >> rfs[]
          >> fs[SUB_LEFT_SUC] >> rw[]
            >- (`LENGTH fullr = LENGTH previous_row` by fs[]
             >> fs[] >> rfs[]
             >> first_assum (assume_tac o MATCH_MP take_singleton_one) >> fs[])
            >- (qpat_x_assum `SUC(LENGTH x) = LENGTH y` (assume_tac o GSYM)
                >> fs[] >> rfs[])))
  (* SUC n -- inductive case *)
  >> rw[dynamic_lcs_row_def]
      (* first element of r is a match *)
      >- (first_x_assum(ASSUME_TAC o MATCH_MP dynamic_lcs_row_invariant_pres1)
          >> fs[SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> first_x_assum(assume_tac o Q.SPECL[`h`,
                                               `longest' (h::diagonal,SUC dl)
                                                 (longest' (HD previous_row) previous_col)`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[] >> metis_tac[sub_le_suc])
      (* first element of r is NOT a match *)
      >- (`dynamic_lcs_row_invariant h' r
            (longest' (HD previous_row) previous_col)
            (TL previous_row) (HD previous_row) prevh fullr`
            by (MATCH_MP_TAC (GEN_ALL dynamic_lcs_row_invariant_pres2)
                >> metis_tac[])
          >> fs[SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> first_x_assum(assume_tac o Q.SPECL[`h'`,
                                               `longest' (HD previous_row) previous_col`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[] >> metis_tac[sub_le_suc])
QED

Theorem dynamic_lcs_row_invariant_pres2:
    !h r previous_col previous_row diagonal prevh fullr l n.
  (dynamic_lcs_row_invariant h r previous_col previous_row diagonal prevh fullr
    /\ (dynamic_lcs_row h r previous_col previous_row diagonal = l)
    /\ (0 <= n) /\ (n < LENGTH l))
  ==> (SND (EL n l) = LENGTH (FST (EL n l)))
Proof
   Induct_on `r`
 >> rpt strip_tac
 >> Cases_on `diagonal`
 >> rename1 `(diagonal,dl)`
 >- (fs[dynamic_lcs_row_def]
      >> metis_tac[LENGTH,prim_recTheory.NOT_LESS_0])
 >> `IS_SUFFIX fullr (h::r)` by fs[dynamic_lcs_row_invariant_def]
 >> first_assum(assume_tac o MATCH_MP is_suffix_length)
 >> first_assum(assume_tac o MATCH_MP is_suffix_take)
 >> Cases_on `n`
  (* 0 requires special treatment since it's outside the range of the inductive hypothesis *)
  >- (rw[dynamic_lcs_row_def]
      (* first element of r is a match *)
      >- (first_x_assum(ASSUME_TAC o MATCH_MP dynamic_lcs_row_invariant_pres1)
          >> fs[dynamic_lcs_row_invariant_def,SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM])
      (* first element of r is NOT a match *)
      >- (`dynamic_lcs_row_invariant h' r
            (longest' (HD previous_row) previous_col)
            (TL previous_row) (HD previous_row) prevh fullr`
          by (MATCH_MP_TAC(GEN_ALL dynamic_lcs_row_invariant_pres2) >> metis_tac[])
          >> fs[dynamic_lcs_row_invariant_def,SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]))
  (* SUC n -- inductive case *)
  >> rw[dynamic_lcs_row_def]
      (* first element of r is a match *)
      >- (first_x_assum(ASSUME_TAC o MATCH_MP dynamic_lcs_row_invariant_pres1)
          >> fs[SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> first_x_assum(assume_tac o Q.SPECL[`h`,
                                               `longest' (h::diagonal,SUC dl)
                                                 (longest' (HD previous_row) previous_col)`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[])
      (* first element of r is NOT a match *)
      >- (`dynamic_lcs_row_invariant h' r
            (longest' (HD previous_row) previous_col)
            (TL previous_row) (HD previous_row) prevh fullr`
            by (MATCH_MP_TAC (GEN_ALL dynamic_lcs_row_invariant_pres2)
                >> metis_tac[])
          >> fs[SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> first_x_assum(assume_tac o Q.SPECL[`h'`,
                                               `longest' (HD previous_row) previous_col`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[])
QED

Theorem dynamic_lcs_rows_invariant_pres:
    dynamic_lcs_rows_invariant (h::l) r previous_row fullh
  ==> dynamic_lcs_rows_invariant l r (dynamic_lcs_row h r ([],0) previous_row ([],0)) fullh
Proof
  fs[dynamic_lcs_rows_invariant_def]
  >> rpt strip_tac
    >- fs[dynamic_lcs_length]
    >- metis_tac[IS_SUFFIX_CONS2_E]
    >- (first_assum(assume_tac o MATCH_MP is_suffix_take)
        >> fs[dynamic_lcs_length]
        >> `lcs (REVERSE (FST(EL n (dynamic_lcs_row h r ([],0) previous_row ([],0)))))
             (TAKE (LENGTH fullh − SUC (LENGTH l)) fullh ++ [h])
             (TAKE (SUC n + (LENGTH r -
                             (LENGTH (dynamic_lcs_row h r ([],0) previous_row ([],0)))))
                   r)` suffices_by fs[dynamic_lcs_length]
        >> MATCH_MP_TAC dynamic_lcs_row_invariant_pres
        >> Q.EXISTS_TAC `r` >> Q.EXISTS_TAC `([],0)`
        >> Q.EXISTS_TAC `previous_row` >> Q.EXISTS_TAC `([],0)`
        >> rpt strip_tac >> fs[dynamic_lcs_length]
        >> fs[dynamic_lcs_row_invariant_def]
        >> fs[lcs_def,common_subsequence_def,is_subsequence_nil])
    >- (first_assum(assume_tac o MATCH_MP is_suffix_take)
        >> fs[dynamic_lcs_length]
        >> MATCH_MP_TAC dynamic_lcs_row_invariant_pres2
        >> Q.EXISTS_TAC `h` >> Q.EXISTS_TAC `r`
        >> Q.EXISTS_TAC `([],0)` >> Q.EXISTS_TAC `previous_row`
        >> Q.EXISTS_TAC `([],0)`
        >> Q.EXISTS_TAC `(TAKE (LENGTH fullh − SUC (LENGTH l)) fullh)` >> Q.EXISTS_TAC `r`
        >> fs[] >> fs[dynamic_lcs_row_invariant_def,lcs_empty]
        >> fs[dynamic_lcs_length])
QED

Theorem dynamic_lcs_rows_correct:
    !l r previous_row fullh.
  dynamic_lcs_rows_invariant l r previous_row fullh
  ==> lcs (REVERSE (dynamic_lcs_rows l r previous_row)) fullh r
Proof
  Induct
  >> rpt strip_tac
    (* nil *)
    >- (fs[dynamic_lcs_rows_invariant_def]
        >> rw[dynamic_lcs_rows_def]
        >> last_x_assum(assume_tac o Q.SPEC `LENGTH r - 1`)
        >> rfs[quantHeuristicsTheory.LIST_LENGTH_0,lcs_empty]
        >> qpat_x_assum `LENGTH x = LENGTH y` (assume_tac o GSYM)
        >> `0 < LENGTH previous_row` by(Cases_on `previous_row` >> fs[])
        >> fs[LAST_EL,PRE_SUB1,SUB_LEFT_SUC,if_length_lemma])
    (* cons *)
    >> first_assum(assume_tac o MATCH_MP dynamic_lcs_rows_invariant_pres)
    >> first_x_assum(assume_tac o Q.SPECL [`r`,
                                           `dynamic_lcs_row h r ([],0) previous_row ([],0)`,
                                           `fullh`])
    >> fs[dynamic_lcs_rows_def]
QED

(* Main correctness theorem for dynamic LCS algorithm *)

Theorem dynamic_lcs_correct:
   lcs (dynamic_lcs l r) l r
Proof
  `dynamic_lcs_rows_invariant l r (REPLICATE (LENGTH r) ([],0)) l`
    by fs[dynamic_lcs_rows_invariant_def,LENGTH_REPLICATE,EL_REPLICATE,lcs_empty]
  >> fs[dynamic_lcs_def, dynamic_lcs_rows_correct]
QED

Theorem dynamic_lcs_no_rev_correct:
   lcs (REVERSE(dynamic_lcs_no_rev l r)) l r
Proof
  `dynamic_lcs_rows_invariant l r (REPLICATE (LENGTH r) ([],0)) l`
    by fs[dynamic_lcs_rows_invariant_def,LENGTH_REPLICATE,EL_REPLICATE,lcs_empty]
  >> fs[dynamic_lcs_no_rev_def, dynamic_lcs_rows_correct]
QED

Theorem dynamic_lcs_refl:
   dynamic_lcs l l = l
Proof
  metis_tac[dynamic_lcs_correct,lcs_refl']
QED

(* Further optimisation of the dynamic LCS algorithm: prune common
   prefixes and suffixes as a preprocessing step *)

val longest_common_prefix_def = Define `
  (longest_common_prefix [] l = []) /\
  (longest_common_prefix l [] = []) /\
  (longest_common_prefix (f::r) (f'::r') =
    if f = f' then f::longest_common_prefix r r' else [])`

Theorem longest_common_prefix_clauses:
    (longest_common_prefix [] l = []) /\
  (longest_common_prefix l [] = []) /\
  (longest_common_prefix (f::r) (f'::r') =
    if f = f' then f::longest_common_prefix r r' else [])
Proof
  Cases_on `l` >> fs[longest_common_prefix_def]
QED

val optimised_lcs_def = Define `
  optimised_lcs l r =
    let prefix = longest_common_prefix l r in
      let len = LENGTH prefix in
        let l = REVERSE(DROP len l) in
          let r = REVERSE(DROP len r) in
            let suffix = longest_common_prefix l r in
              let len = LENGTH suffix in
                let l = DROP len l in
                  let r = DROP len r in
                    prefix++dynamic_lcs_no_rev l r++REVERSE suffix`;

(* Verification of optimised LCS *)

val longest_common_suffix_def = Define `
  (longest_common_suffix [] l = []) /\
  (longest_common_suffix l [] = []) /\
  (longest_common_suffix (f::r) (f'::r') =
   if LENGTH r > LENGTH r' then
     longest_common_suffix r (f'::r')
   else if LENGTH r' > LENGTH r then
     longest_common_suffix (f::r) r'
   else let l = longest_common_suffix r r' in
     if f = f' /\ LENGTH l = LENGTH r then
       f::l
     else l)`

Theorem longest_common_suffix_clauses:
  !r r' f f'.
  (longest_common_suffix [] l = []) /\
  (longest_common_suffix l [] = []) /\
  (longest_common_suffix (r ++ [f]) (r' ++ [f']) =
    if f = f' then SNOC f (longest_common_suffix r r') else [])
Proof
  fs[longest_common_suffix_def,
     Q.prove(`longest_common_suffix l [] = []`, Cases_on `l` >> fs[longest_common_suffix_def])]
  >> ho_match_mp_tac (theorem "longest_common_suffix_ind")
  >> rpt strip_tac
  >> fs[longest_common_suffix_def]
  >- (Induct_on `r'` >> fs[longest_common_suffix_def,APPEND] >> Induct_on `v3` >> fs[longest_common_suffix_def])
  >- (Induct_on `v3` >> fs[longest_common_suffix_def] >> rw[] >> fs[] >> rfs[])
  >> rw[] >> fs[] >> rfs[]
QED

Theorem longest_common_prefix_LENGTH:
    !l r. LENGTH(longest_common_prefix l r) <= LENGTH l /\ LENGTH(longest_common_prefix l r) <= LENGTH r
Proof
  ho_match_mp_tac (fetch "lcs" "longest_common_prefix_ind")
  >> rpt strip_tac
  >> fs[longest_common_prefix_clauses]
  >> rw[]
QED

Theorem longest_common_suffix_LENGTH:
    !l r. LENGTH(longest_common_suffix l r) <= LENGTH l /\ LENGTH(longest_common_suffix l r) <= LENGTH r
Proof
  ho_match_mp_tac (fetch "lcs" "longest_common_suffix_ind")
  >> rpt strip_tac
  >> fs[longest_common_suffix_clauses]
  >> rw[]
  >> rw[longest_common_suffix_def]
QED

val longest_common_suffix_length_def = Define `
  (longest_common_suffix_length [] [] n = n) /\
  (longest_common_suffix_length (f::r) (f'::r') n =
     if f = f' then
       longest_common_suffix_length r r' (SUC n)
     else
       longest_common_suffix_length r r' 0)`

Theorem longest_common_suffix_length_le_length:
   !l r. LENGTH(longest_common_suffix l r) <= LENGTH r
Proof
  ho_match_mp_tac(fetch "-" "longest_common_suffix_ind")
  >> rpt strip_tac
  >> rw[longest_common_suffix_def]
  >> fs[]
QED

Theorem longest_common_suffix_length_thm:
   !l r n.
   LENGTH l = LENGTH r ==>
  longest_common_suffix_length l r n =
  if LENGTH(longest_common_suffix l r) = LENGTH r then
    n + LENGTH(longest_common_suffix l r)
  else
    LENGTH(longest_common_suffix l r)
Proof
  ho_match_mp_tac (fetch "-" "longest_common_suffix_ind")
  >> rpt strip_tac
  >> fs[longest_common_suffix_length_def,longest_common_suffix_def]
  >> rw[]
  >> qspecl_then [`l`,`r`] assume_tac longest_common_suffix_length_le_length
  >> fs[]
QED

Theorem longest_common_suffix_dropr:
   !l r. LENGTH r > LENGTH l ==>
         longest_common_suffix l (DROP (LENGTH r − LENGTH l) r) = longest_common_suffix l r
Proof
  ho_match_mp_tac (fetch "-" "longest_common_suffix_ind")
  >> rw[longest_common_suffix_def]
  >> fs[] >> fs[ADD1]
  >> Cases_on `LENGTH r > LENGTH l + 1`
  >> fs[]
  >> `LENGTH l +1 = LENGTH r` by fs[]
  >> fs[]
QED

Theorem longest_common_suffix_dropl:
   !l r. LENGTH l > LENGTH r ==>
         longest_common_suffix (DROP (LENGTH l − LENGTH r) l) r = longest_common_suffix l r
Proof
  ho_match_mp_tac (fetch "-" "longest_common_suffix_ind")
  >> rw[longest_common_suffix_def,ADD1,DROP_LENGTH_NIL]
  >> fs[] >> fs[ADD1,DROP_LENGTH_NIL]
  >> Cases_on `LENGTH l > LENGTH r + 1`
  >> fs[]
  >> `LENGTH r +1 = LENGTH l` by fs[]
  >> fs[]
QED

Theorem longest_common_suffix_length_if:
   !l r.
  (if LENGTH l = LENGTH r then
     longest_common_suffix_length l r 0
   else if LENGTH l < LENGTH r then
     longest_common_suffix_length l (DROP (LENGTH r - LENGTH l) r) 0
   else
     longest_common_suffix_length (DROP (LENGTH l - LENGTH r) l) r 0)
  =
    LENGTH(longest_common_suffix l r)
Proof
  rw[]
  >> fs[longest_common_suffix_length_thm,longest_common_suffix_dropl,longest_common_suffix_dropr]
QED

Theorem longest_prefix_is_prefix:
   !l r. IS_PREFIX l (longest_common_prefix l r) /\ IS_PREFIX r (longest_common_prefix l r)
Proof
  ho_match_mp_tac (theorem "longest_common_prefix_ind")
  >> rw[longest_common_prefix_def]
QED

Theorem longest_prefix_correct:
 !l r s. lcs (longest_common_prefix l r ++ s) l r = lcs s (DROP (LENGTH (longest_common_prefix l r)) l) (DROP (LENGTH (longest_common_prefix l r)) r)
Proof
  ho_match_mp_tac (theorem "longest_common_prefix_ind")
  >> rpt strip_tac
  >> rw[longest_common_prefix_clauses,cons_lcs_optimal_substructure]
QED

Theorem longest_common_prefix_reverse:
    !l r. longest_common_prefix (REVERSE l) (REVERSE r) = REVERSE(longest_common_suffix l r)
Proof
  ho_match_mp_tac (SNOC_INDUCT)
  >> strip_tac
  >- fs[longest_common_prefix_clauses,longest_common_suffix_clauses]
  >> ntac 3 strip_tac
  >> ho_match_mp_tac (SNOC_INDUCT)
  >> rpt strip_tac
  >> fs[longest_common_prefix_clauses,longest_common_suffix_clauses]
  >> rw[]
QED

Theorem longest_suffix_is_suffix:
   !l r. IS_SUFFIX l (longest_common_suffix l r) /\ IS_SUFFIX r (longest_common_suffix l r)
Proof
  rpt strip_tac >> fs[IS_SUFFIX_compute,GSYM longest_common_prefix_reverse]
  >> metis_tac[longest_prefix_is_prefix]
QED

Theorem longest_suffix_correct:
 !l r s. lcs (s ++ longest_common_suffix l r) l r = lcs s (REVERSE (DROP (LENGTH (longest_common_suffix l r)) (REVERSE l))) (REVERSE (DROP (LENGTH (longest_common_suffix l r)) (REVERSE r)))
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> strip_tac
  >- fs[longest_common_suffix_clauses]
  >> ntac 3 strip_tac
  >> ho_match_mp_tac SNOC_INDUCT
  >> rpt strip_tac
   >- (fs[SNOC_APPEND] >> fs[lcs_empty',longest_common_suffix_clauses])
   >> fs[SNOC_APPEND]
   >> fs[longest_common_suffix_clauses]
   >> rw[]
   >> fs[SNOC_APPEND,snoc_lcs_optimal_substructure,REVERSE_APPEND,
         Q.prove(`l - r - l = (0:num)`,intLib.COOPER_TAC),take_suc_length]
QED

Theorem longest_common_prefix_refl:
    !l r. longest_common_prefix l l = l
Proof
  Induct >> fs[longest_common_prefix_clauses]
QED

(* Main correctness theorem for optimised LCS algorithm *)

Theorem optimised_lcs_correct:
   lcs (optimised_lcs l r) l r
Proof
  fs[optimised_lcs_def,longest_prefix_correct]
  >> PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[longest_prefix_correct,longest_common_prefix_reverse,
        longest_suffix_correct,lcs_rev',dynamic_lcs_no_rev_correct]
QED

(* More properties of optimised LCS algorithm *)

Theorem optimised_lcs_refl:
   optimised_lcs l l = l
Proof
  metis_tac[optimised_lcs_correct,lcs_refl']
QED

val _ = export_theory ();
