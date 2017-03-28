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

val is_subsequence_nil = Q.store_thm("is_subsequence_nil",`
  (is_subsequence l [] = (l = [])) /\ (is_subsequence [] l = T)`,
  Induct_on `l` >> fs[is_subsequence_def]);

val is_subsequence_cons = Q.store_thm("is_subsequence_cons",`
  is_subsequence (f::r) (h::r') =
  (((f = h) /\ is_subsequence r r') \/ is_subsequence (f::r) r')`,
  fs[Once is_subsequence_def]);

val is_subsequence_single = Q.store_thm("is_subsequence_single",
  `is_subsequence s [h] = ((s = [h]) \/ (s = []))`,
  Cases_on `s`
  >> fs[is_subsequence_nil,is_subsequence_cons]);

val prefix_is_subsequence = Q.store_thm("prefix_is_subsequence",`
  ! s l s'.
  (is_subsequence (s ++ s') l ==> is_subsequence s l)`,
   ho_match_mp_tac (theorem "is_subsequence_ind")
    >> rpt strip_tac
    >- fs[is_subsequence_nil,is_subsequence_cons] 
    >> Cases_on `l`
     >- fs[is_subsequence_nil]
     >> fs[is_subsequence_cons]
     >> rw[]
     >> metis_tac[]);

val suffix_is_subsequence = Q.store_thm("suffix_is_subsequence",
  `! s l s'.
  (is_subsequence (f::s) l ==> is_subsequence s l)`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
   >> rpt strip_tac
   >- fs[is_subsequence_nil,is_subsequence_cons]
   >> Cases_on `l`
    >- fs[is_subsequence_nil]
    >> fs[is_subsequence_cons]);

val suffix_is_subsequence' = Q.store_thm("suffix_is_subsequence'",
  `!s l. is_subsequence (s' ++ s) l ==> is_subsequence s l`,
  Induct_on `s'`
  >> fs[] >> metis_tac[suffix_is_subsequence]);

val cons_is_subsequence = Q.store_thm("cons_is_subsequence",
  `is_subsequence s l ==> is_subsequence s (f::l)`,
  Induct_on `s`
   >> rw[is_subsequence_cons,is_subsequence_nil]);

val is_subsequence_snoc = Q.store_thm("is_subsequence_snoc",`
  !s l f. is_subsequence (s ++ [f]) (l ++ [f]) = is_subsequence s l`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
   >- (Induct_on `l` >> fs[is_subsequence_nil,is_subsequence_cons])
  >> fs[is_subsequence_nil,is_subsequence_cons]
  >> Cases_on `l`
  >> rfs[is_subsequence_nil,is_subsequence_cons] >> metis_tac[]);

val is_subsequence_snoc' = Q.store_thm("is_subsequence_snoc'",
  `!r r'. is_subsequence (r ++ [f]) (r' ++ [h]) =
   (((f = h) /\ is_subsequence r r') \/ is_subsequence (r ++ [f]) r')`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >> fs[is_subsequence_cons,is_subsequence_nil]
  >> Induct_on `r'` >> rpt strip_tac >> fs[is_subsequence_nil,is_subsequence_cons]
  >> metis_tac[]);

val snoc_is_subsequence = Q.store_thm("snoc_is_subsequence",`
  !s l f. is_subsequence s l ==> is_subsequence s (l++[f])`,
  ho_match_mp_tac SNOC_INDUCT
  >> rw[is_subsequence_snoc',is_subsequence_nil,SNOC_APPEND]);

val is_subsequence_length = Q.store_thm("is_subsequence_length",`
  !l l'. is_subsequence l l' ==> LENGTH l <= LENGTH l'`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l'`
  >- fs[is_subsequence_nil]
  >> fs[is_subsequence_cons]
  >> metis_tac [suffix_is_subsequence]);

val is_subsequence_cons' = Q.store_thm("is_subsequence_cons'",`
  !s l f. is_subsequence s (f::l)
  ==> ((((s = []) \/ f ≠ HD s) /\ is_subsequence s l)
      \/ (((s ≠ []) /\ (f = HD s)) /\ is_subsequence (TL s) l))`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l`
  >- fs[is_subsequence_nil, Once is_subsequence_def]
  >- (Cases_on `f' = f`
     >> fs[is_subsequence_cons] >> rfs[]
     >> metis_tac [cons_is_subsequence]));

val is_subsequence_snoc'' = Q.store_thm("is_subsequence_snoc'",`
  !s l f. is_subsequence s (l ++ [f])
  ==> ((((s = []) \/ f ≠ LAST s) /\ is_subsequence s l)
       \/ (((s ≠ []) /\ (f = LAST s)) /\ is_subsequence (FRONT s) l))`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >- fs[is_subsequence_nil]
  >> Cases_on `l`
  >- fs[is_subsequence_nil, Once is_subsequence_def]
  >- (Cases_on `f' = f`
     >> fs[is_subsequence_snoc'] >> fs[is_subsequence_cons]
     >> rpt(first_x_assum(ASSUME_TAC o Q.SPEC `f'`))
     >> rfs[is_subsequence_nil] >> Cases_on `s` >> fs[is_subsequence_nil,is_subsequence_cons]));

val common_subsequence_sym = Q.store_thm("common_subsequence_sym",
  `common_subsequence s u t = common_subsequence s t u`,
  fs[common_subsequence_def,EQ_IMP_THM])

val lcs_sym = Q.store_thm("lcs_sym",
  `lcs l l' l'' = lcs l l'' l'`,
  metis_tac[lcs_def,common_subsequence_sym]);

val lcs_empty = Q.prove(`lcs [] l [] /\ lcs [] [] l`,
  fs[lcs_def,common_subsequence_def,is_subsequence_nil]);

val lcs_empty' = Q.store_thm("lcs_empty'",
  `(lcs l l' [] = (l = [])) /\ (lcs l [] l' = (l = []))`,
  fs[lcs_def,common_subsequence_def,is_subsequence_nil,EQ_IMP_THM]);

val cons_lcs_optimal_substructure = Q.store_thm("cons_lcs_optimal_substructure",
  `lcs (f::l) (f::l') (f::l'') = lcs l l' l''`,
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
       >> fs[]));

val snoc_lcs_optimal_substructure = Q.store_thm("snoc_lcs_optimal_substructure",
  `lcs (l ++ [f]) (l' ++ [f]) (l'' ++ [f]) = lcs l l' l''`,
  fs[lcs_def,common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >> first_assum(ASSUME_TAC o Q.SPEC `s' ++ [f]`)
  >> rpt(first_x_assum(assume_tac o MATCH_MP is_subsequence_snoc''))
  >> fs[is_subsequence_snoc,FRONT_APPEND]
  >> TRY(metis_tac[prefix_is_subsequence])
   >- (`LENGTH s' ≤ LENGTH l` by fs[] >> fs[])
   >- (`LENGTH(FRONT s') ≤ LENGTH l` by fs[] >> Cases_on `s'` >> fs[]));

val cons_lcs_optimal_substructure_left = Q.store_thm(
  "cons_lcs_optimal_substructure_left",
  `f ≠ f' /\ lcs l (f::l') l''
    /\ lcs l''' l' (f'::l'')
    /\ LENGTH l >= LENGTH l'''
   ==> lcs l (f::l') (f'::l'')`,
  fs[lcs_def,common_subsequence_def, Once is_subsequence_def, EQ_IMP_THM]
  >> rpt strip_tac
  >- metis_tac[cons_is_subsequence]
  >> PAT_ASSUM ``is_subsequence s' (f'::l'')`` (assume_tac o MATCH_MP is_subsequence_cons')
  >> PAT_ASSUM ``is_subsequence s' (f::l')`` (assume_tac o MATCH_MP is_subsequence_cons')  
  >> fs[is_subsequence_cons]
  >> Cases_on `s'`
  >> fs[is_subsequence_cons]
  >> `LENGTH(h::t) ≤ LENGTH l'''` by(first_assum match_mp_tac >> fs[is_subsequence_cons])
  >> fs[]);

val snoc_lcs_optimal_substructure_left = Q.store_thm(
  "snoc_lcs_optimal_substructure_left",
  `f ≠ f' /\ lcs l (l' ++ [f]) l''
    /\ lcs l''' l' (l''++[f'])
    /\ LENGTH l >= LENGTH l'''
   ==> lcs l (l'++[f]) (l''++[f'])`,
  fs[lcs_def,common_subsequence_def, is_subsequence_snoc', EQ_IMP_THM]
  >> rpt strip_tac
  >- metis_tac[snoc_is_subsequence]
  >> PAT_ASSUM ``is_subsequence s' (l''++[f'])`` (assume_tac o MATCH_MP is_subsequence_snoc'')
  >> PAT_ASSUM ``is_subsequence s' (l'++[f])`` (assume_tac o MATCH_MP is_subsequence_snoc'')
  >> fs[is_subsequence_cons]
  >> FULL_STRUCT_CASES_TAC (Q.SPEC `s'` SNOC_CASES)
  >> fs[is_subsequence_snoc',SNOC_APPEND]
  >> `LENGTH(l''''++[x]) ≤ LENGTH l'''` by(first_assum match_mp_tac >> fs[is_subsequence_snoc'])
  >> fs[]);

val cons_lcs_optimal_substructure_right = Q.store_thm(
  "cons_lcs_optimal_substructure_right",`
  f ≠ f' /\ lcs l (f::l') l''
    /\ lcs l''' l' (f'::l'')
    /\ LENGTH l''' >= LENGTH l
  ==> lcs l''' (f::l') (f'::l'')`,
  metis_tac[cons_lcs_optimal_substructure_left,lcs_sym]);

val snoc_lcs_optimal_substructure_right = Q.store_thm(
  "snoc_lcs_optimal_substructure_right",`
  f ≠ f' /\ lcs l (l'++[f]) l''
    /\ lcs l''' l' (l''++[f'])
    /\ LENGTH l''' >= LENGTH l
  ==> lcs l''' (l'++[f]) (l''++[f'])`,
  metis_tac[snoc_lcs_optimal_substructure_left,lcs_sym]);

val lcs_length_left = Q.store_thm("lcs_length_left",`
  (lcs xl yl zl /\ lcs xl' (yl ++ [y]) zl)
  ==> SUC(LENGTH xl) >= LENGTH xl'`,
  fs[lcs_def,common_subsequence_def] >> rpt strip_tac
  >> first_assum(assume_tac o MATCH_MP is_subsequence_snoc'')
  >> fs[]
   >- (`LENGTH xl' <= LENGTH xl` by metis_tac[] >> fs[])
   >> FULL_STRUCT_CASES_TAC (Q.SPEC `xl'` SNOC_CASES)
   >> fs[SNOC_APPEND]
   >> rpt(first_x_assum(assume_tac o MATCH_MP prefix_is_subsequence))
   >> `LENGTH l <= LENGTH xl` by metis_tac[] >> fs[])

val lcs_length_right = Q.store_thm("lcs_length_right",`
  (lcs xl yl zl /\ lcs xl' (yl) (zl ++ [z]))
  ==> SUC(LENGTH xl) >= LENGTH xl'`,
  metis_tac[lcs_sym,lcs_length_left]);

val is_subsequence_rev = Q.store_thm("is_subsequence_rev",`
  !l r. is_subsequence (REVERSE l) (REVERSE r) = is_subsequence l r`,
  ho_match_mp_tac (theorem "is_subsequence_ind")
  >> rpt strip_tac
  >> fs[is_subsequence_nil]
  >> Cases_on `r`
  >> fs[is_subsequence_nil,is_subsequence_snoc',is_subsequence_cons]);

val is_subsequence_rev' = Q.store_thm("is_subsequence_rev",`
  !l r. is_subsequence l (REVERSE r) = is_subsequence (REVERSE l) r`,
  ho_match_mp_tac SNOC_INDUCT
  >> strip_tac
   >- fs[is_subsequence_nil]
   >> rpt strip_tac
   >> Induct_on `r`
   >> fs[is_subsequence_nil,is_subsequence_cons,is_subsequence_snoc',SNOC_APPEND,REVERSE_APPEND]);

val common_subsequence_rev = Q.store_thm("common_subsequence_rev",
  `!l r s. common_subsequence (REVERSE l) (REVERSE r) (REVERSE s) = common_subsequence l r s`,
  rw[common_subsequence_def,is_subsequence_rev]);

val common_subsequence_rev' = Q.store_thm("common_subsequence_rev",
  `!l r s. common_subsequence l (REVERSE r) (REVERSE s) = common_subsequence (REVERSE l) r s`,
  rw[common_subsequence_def,is_subsequence_rev']);

val lcs_rev = Q.store_thm("lcs_rev",
  `!l r s. lcs (REVERSE l) (REVERSE r) (REVERSE s) = lcs l r s`,
  rw[common_subsequence_rev',lcs_def,EQ_IMP_THM]
  >> metis_tac[LENGTH_REVERSE,REVERSE_REVERSE]);

val lcs_rev' = Q.store_thm("lcs_rev",
  `!l r s. lcs l (REVERSE r) (REVERSE s) = lcs (REVERSE l) r s`,
  rw[common_subsequence_rev',lcs_def,EQ_IMP_THM]
  >> metis_tac[LENGTH_REVERSE,REVERSE_REVERSE]);

val lcs_drop_ineq = Q.store_thm("lcs_drop_ineq",
`(lcs (f::r) (h::l) l' /\ f ≠ h) ==> lcs (f::r) l l'`,
  rpt strip_tac
  >> fs[lcs_def,common_subsequence_def,Once is_subsequence_cons]
  >> metis_tac[cons_is_subsequence]);

val lcs_split = Q.store_thm("lcs_split",
  `lcs (f::r) l l' ==> ?ll lr. SPLITP ($= f) l = (ll,f::lr)`,
  Induct_on `l`
  >> rw[lcs_empty',SPLITP]
  >> fs[SPLITP]
  >> metis_tac[lcs_drop_ineq,SND]);

val lcs_split2 = Q.store_thm("lcs_split2",
  `lcs (f::r) l l' ==> ?ll lr. SPLITP ($= f) l' = (ll,f::lr)`,
  metis_tac[lcs_split,lcs_sym]);

val lcs_split_lcs = Q.store_thm("lcs_split_lcs",
  `lcs (f::r) l l' ==> lcs (f::r) (SND(SPLITP ($= f) l)) l'`,
  Induct_on `l`
  >> rw[lcs_empty',SPLITP]
  >> metis_tac[lcs_drop_ineq,SND]);

val lcs_split_lcs2 = Q.store_thm("lcs_split_split_lcs2",
  `lcs (f::r) l l' ==> lcs (f::r) l (SND(SPLITP ($= f) l'))`,
  metis_tac[lcs_split_lcs,lcs_sym]);

val split_lcs_optimal_substructure = Q.store_thm("split_lcs_optimal_substructure",
  `lcs (f::r) l l' ==> lcs r (TL(SND(SPLITP ($= f) l))) (TL(SND(SPLITP ($= f) l')))`,
  rpt strip_tac >>
  drule lcs_split >> drule lcs_split2 >>      
  pop_assum (assume_tac o MATCH_MP lcs_split_lcs2 o MATCH_MP lcs_split_lcs)
  >> rpt strip_tac
  >> fs[cons_lcs_optimal_substructure]);

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

val longest_tail = Q.store_thm("longest_tail",
  `longest (l ++ [e]) (l' ++ [e]) = longest l l' ++ [e]`,
  rw[longest_def,GSYM ADD1] >> fs[])

val longest_cons = Q.store_thm("longest_cons",
  `longest (e::l) (e::l') = e::longest l l'`,
  rw[longest_def,GSYM ADD1] >> fs[])

val naive_lcs_clauses = Q.store_thm("naive_lcs_clauses",`
(naive_lcs l [] = []) ∧
(naive_lcs [] l = []) ∧
(naive_lcs (f::r) (f'::r') =
 if f = f' then
   f::naive_lcs r r'
 else
   longest(naive_lcs (f::r) r') (naive_lcs r (f'::r')))`,
  Cases_on `l` >> fs[naive_lcs_def]);

val naive_lcs_tail = Q.store_thm("naive_lcs_tail",`
  !prevh fullr h. naive_lcs (prevh ++ [h]) (fullr ++ [h]) = naive_lcs prevh fullr ++ [h]`,
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rpt strip_tac
   >- (fs[naive_lcs_clauses]
       >> Induct_on `prevh`
       >> rw[naive_lcs_clauses, longest_def])
   >- (rw[naive_lcs_clauses,longest_def]
       >> Induct_on `v3` (*TODO: generated name *)
       >> rw[naive_lcs_clauses,longest_def])
   >> rw[naive_lcs_clauses]
   >> fs[longest_tail]);

val naive_lcs_length_bound = Q.store_thm("naive_lcs_length_bound",`
  !l l'. LENGTH (naive_lcs l l') <= MIN (LENGTH l) (LENGTH l')`,
  ho_match_mp_tac (theorem "naive_lcs_ind")
  >> rw[naive_lcs_clauses, MIN_DEF, longest_def]);

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

val naive_lcs_correct = Q.store_thm("naive_lcs_correct",
  `∀l l'. lcs (naive_lcs l l') l l'`,
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
    >> metis_tac[cons_lcs_optimal_substructure_right]);

(* A quadratic-time LCS algorithm in dynamic programming style *)

val dynamic_lcs_row_def = Define `
   (dynamic_lcs_row h [] previous_col previous_row diagonal = [])
∧ (dynamic_lcs_row h (f::r) previous_col previous_row diagonal =
    if f = h then
      (let current = longest (SNOC f diagonal) (longest (HD previous_row) previous_col) in
        current::dynamic_lcs_row h r current (TL previous_row) (HD previous_row))
    else
      (let current = longest (HD previous_row) previous_col in
        current::dynamic_lcs_row h r current (TL previous_row) (HD previous_row))
   )`;

val dynamic_lcs_rows_def = Define `
  (dynamic_lcs_rows [] r previous_row = if previous_row = [] then [] else LAST previous_row) ∧
  (dynamic_lcs_rows (h::l) r previous_row =
   dynamic_lcs_rows l r (dynamic_lcs_row h r [] previous_row []))
`;

val dynamic_lcs_def = Define `
  dynamic_lcs l r = dynamic_lcs_rows l r (REPLICATE (LENGTH r) [])`;

(* Verification of dynamic LCS algorithm *)

val dynamic_lcs_row_invariant_def = Define `
  dynamic_lcs_row_invariant h r previous_col previous_row diagonal prevh fullr =
  ((LENGTH r = LENGTH previous_row) ∧ (IS_SUFFIX fullr r) ∧
   (!n. 0 <= n /\ n < LENGTH previous_row ==> (lcs (EL n previous_row) prevh (TAKE (SUC n + (LENGTH fullr - LENGTH r)) fullr))) ∧
   (lcs diagonal prevh (TAKE (LENGTH fullr - LENGTH r) fullr)) ∧
   (lcs previous_col (SNOC h prevh) (TAKE (LENGTH fullr - LENGTH r) fullr)))`;

val dynamic_lcs_rows_invariant_def = Define `
  dynamic_lcs_rows_invariant h r previous_row fullh =
  ((LENGTH r = LENGTH previous_row) ∧ (IS_SUFFIX fullh h) ∧
   (!n. 0 <= n /\ n < LENGTH previous_row ==> (lcs (EL n previous_row) (TAKE (LENGTH fullh - LENGTH h) fullh) (TAKE (SUC n) r))))`;

val dynamic_lcs_row_invariant_pres1 = Q.store_thm("dynamic_lcs_row_invariant_pres1",`
  dynamic_lcs_row_invariant h (h::r) previous_col previous_row diagonal prevh fullr
  ==> dynamic_lcs_row_invariant h r (longest (SNOC h diagonal)
                                             (longest (HD previous_row) previous_col))
                                (TL previous_row) (HD previous_row) prevh fullr`,
 fs[dynamic_lcs_row_invariant_def]
 >> rpt strip_tac
  >- (Cases_on `previous_row` >> fs[])
  >- metis_tac[IS_SUFFIX_CONS2_E]
  >- (first_x_assum(assume_tac o Q.SPEC `SUC n`)
      >> Cases_on `previous_row` >> fs[]
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC] >> every_case_tac
      >> Cases_on `n`
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[SUB,ADD_CLAUSES] >> rfs[])
  >- (first_x_assum(assume_tac o Q.SPEC `0`)
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> Cases_on `previous_row`
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC]
      >> every_case_tac
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[] >> rfs[])
  >- (rw[longest_def]
      >> PAT_ASSUM ``IS_SUFFIX fullr (h::r)`` (assume_tac o MATCH_MP is_suffix_take)
      >> fs[SNOC_APPEND,snoc_lcs_optimal_substructure] >> rfs[]
       (* longest is from previous row *)
       >- (first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (h::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[] >> metis_tac[lcs_length_right])
       (* longest is from previous column *)
       >- metis_tac[lcs_length_left]));
      
val dynamic_lcs_row_invariant_pres2 = Q.store_thm("dynamic_lcs_row_invariant_pres2",`
  h ≠ f ∧ dynamic_lcs_row_invariant h (f::r) previous_col previous_row diagonal fullh fullr
  ==> dynamic_lcs_row_invariant h r (longest (HD previous_row) previous_col) (TL previous_row)
                                (HD previous_row) fullh fullr`,
 fs[dynamic_lcs_row_invariant_def]
 >> rpt strip_tac
  >- (Cases_on `previous_row` >> fs[])
  >- metis_tac[IS_SUFFIX_CONS2_E]
  >- (first_x_assum(assume_tac o Q.SPEC `SUC n`)
      >> Cases_on `previous_row` >> fs[]
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC] >> every_case_tac
      >> Cases_on `n`
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[SUB,ADD_CLAUSES] >> rfs[])
  >- (first_x_assum(assume_tac o Q.SPEC `0`)
      >> first_x_assum(assume_tac o MATCH_MP is_suffix_length)
      >> Cases_on `previous_row`
      >> fs[ADD_CLAUSES,SUB_LEFT_SUC]
      >> every_case_tac
      >> TRY(`LENGTH fullr = SUC(LENGTH t)` by(fs[]>>NO_TAC))
      >> fs[] >> rfs[])
  >- (rw[longest_def]
      >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_take)
      >> fs[SNOC_APPEND,snoc_lcs_optimal_substructure] >> rfs[]
       (* longest is from previous row *)
       >- (MATCH_MP_TAC (Q.INST [`l`|->`previous_col`] snoc_lcs_optimal_substructure_right)
           >> rpt strip_tac >> fs[]                       
           >> first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[]) (*TODO: cleanup *)
       (* longest is from previous column *)
       >- (MATCH_MP_TAC (Q.INST [`l'''`|->`HD previous_row`] snoc_lcs_optimal_substructure_left)
           >> rpt strip_tac >> fs[]                       
           >> first_x_assum (assume_tac o Q.SPEC `0`)
           >> rfs[] >> fs[Q.SPEC `1` ADD_SYM] >> fs[TAKE_SUM]
           >> PAT_ASSUM ``IS_SUFFIX fullr (f::r)`` (assume_tac o MATCH_MP is_suffix_drop)
           >> rfs[] >> fs[])));

val dynamic_lcs_length = Q.store_thm("dynamic_lcs_length",`
  !h r previous_col previous_row diagonal.
  LENGTH(dynamic_lcs_row h r previous_col previous_row diagonal) = LENGTH r`,
  Induct_on `r` >> rw[dynamic_lcs_row_def]);

val dynamic_lcs_row_invariant_pres = Q.store_thm("dynamic_lcs_row_invariant_pres",`
  !h r previous_col previous_row diagonal prevh fullr l n.
  (dynamic_lcs_row_invariant h r previous_col previous_row diagonal prevh fullr
    /\ (dynamic_lcs_row h r previous_col previous_row diagonal = l)
    /\ (0 <= n) /\ (n < LENGTH l))
  ==> (lcs (EL n l) (prevh ++ [h]) (TAKE (SUC n + (LENGTH fullr - (LENGTH l))) fullr))`,
   Induct_on `r`
 >> rpt strip_tac
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
            (longest (HD previous_row) previous_col) 
            (TL previous_row) (HD previous_row) prevh fullr`
            by (MATCH_MP_TAC (Q.INST [`h`|->`h'`,`f`|->`h`]dynamic_lcs_row_invariant_pres2)
                >> fs[])
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
                                               `longest (diagonal ++ [h])
                                                 (longest (HD previous_row) previous_col)`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[] >> metis_tac[sub_le_suc])
      (* first element of r is NOT a match *)
      >- (`dynamic_lcs_row_invariant h' r
            (longest (HD previous_row) previous_col) 
            (TL previous_row) (HD previous_row) prevh fullr`
            by (MATCH_MP_TAC (Q.INST [`h`|->`h'`,`f`|->`h`]dynamic_lcs_row_invariant_pres2)
                >> fs[])
          >> fs[SNOC_APPEND,GSYM ADD1,
                dynamic_lcs_length,Q.SPEC `1` ADD_SYM]
          >> first_x_assum(assume_tac o Q.SPECL[`h'`,
                                               `longest (HD previous_row) previous_col`,
                                               `TL previous_row`, `HD previous_row`, `prevh`,
                                               `fullr`,`n'`])
          >> rfs[] >> metis_tac[sub_le_suc]));

val dynamic_lcs_rows_invariant_pres = Q.store_thm("dynamic_lcs_rows_invariant_pres",`
  dynamic_lcs_rows_invariant (h::l) r previous_row fullh
  ==> dynamic_lcs_rows_invariant l r (dynamic_lcs_row h r [] previous_row []) fullh`,
  fs[dynamic_lcs_rows_invariant_def]
  >> rpt strip_tac
    >- fs[dynamic_lcs_length]
    >- metis_tac[IS_SUFFIX_CONS2_E]
    >> first_assum(assume_tac o MATCH_MP is_suffix_take)
     >> fs[dynamic_lcs_length]
     >> `lcs (EL n (dynamic_lcs_row h r [] previous_row []))
          (TAKE (LENGTH fullh − SUC (LENGTH l)) fullh ++ [h])
          (TAKE (SUC n + (LENGTH r -
                          (LENGTH (dynamic_lcs_row h r [] previous_row []))))
                r)` suffices_by fs[dynamic_lcs_length]
     >> MATCH_MP_TAC dynamic_lcs_row_invariant_pres
     >> Q.EXISTS_TAC `r` >> Q.EXISTS_TAC `[]`
     >> Q.EXISTS_TAC `previous_row` >> Q.EXISTS_TAC `[]`
     >> rpt strip_tac >> fs[dynamic_lcs_length]
     >> fs[dynamic_lcs_row_invariant_def]
     >> fs[lcs_def,common_subsequence_def,is_subsequence_nil]);

val dynamic_lcs_rows_correct = Q.store_thm("dynamic_lcs_rows_correct",`
  !l r previous_row fullh.
  dynamic_lcs_rows_invariant l r previous_row fullh
  ==> lcs (dynamic_lcs_rows l r previous_row) fullh r`,
  Induct
  >> rpt strip_tac
    (* nil *)
    >- (fs[dynamic_lcs_rows_invariant_def]
        >> rw[dynamic_lcs_rows_def]
        >> first_x_assum(assume_tac o Q.SPEC `LENGTH r - 1`)
        >> rfs[quantHeuristicsTheory.LIST_LENGTH_0,lcs_empty]
        >> qpat_x_assum `LENGTH x = LENGTH y` (assume_tac o GSYM)
        >> `0 < LENGTH previous_row` by(Cases_on `previous_row` >> fs[])
        >> fs[LAST_EL,PRE_SUB1,SUB_LEFT_SUC,if_length_lemma])
    (* cons *)
    >> first_assum(assume_tac o MATCH_MP dynamic_lcs_rows_invariant_pres)
    >> first_x_assum(assume_tac o Q.SPECL [`r`,
                                           `dynamic_lcs_row h r [] previous_row []`,
                                           `fullh`])
    >> fs[dynamic_lcs_rows_def]);

(* Main correctness theorem for dynamic LCS algorithm *)

val dynamic_lcs_correct = Q.store_thm("dynamic_lcs_correct",
  `lcs (dynamic_lcs l r) l r`,
  `dynamic_lcs_rows_invariant l r (REPLICATE (LENGTH r) []) l`
    by fs[dynamic_lcs_rows_invariant_def,LENGTH_REPLICATE,EL_REPLICATE,lcs_empty]
  >> fs[dynamic_lcs_def, dynamic_lcs_rows_correct]);

(* Further optimisation of the dynamic LCS algorithm: prune common
   prefixes and suffixes as a preprocessing step *)

val longest_common_prefix_def = Define `
  (longest_common_prefix [] l = []) /\
  (longest_common_prefix l [] = []) /\
  (longest_common_prefix (f::r) (f'::r') =
    if f = f' then f::longest_common_prefix r r' else [])`

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
                    prefix++REVERSE(dynamic_lcs l r)++REVERSE suffix`;

(* Verification of optimised LCS *)

val longest_common_prefix_clauses = Q.store_thm("longest_common_prefix_clauses",`
  (longest_common_prefix [] l = []) /\
  (longest_common_prefix l [] = []) /\
  (longest_common_prefix (f::r) (f'::r') =
    if f = f' then f::longest_common_prefix r r' else [])`,
  Cases_on `l` >> fs[longest_common_prefix_def]);

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

val longest_common_suffix_clauses = Q.store_thm("longest_common_suffix_clauses",`!r r' f f'.
  (longest_common_suffix [] l = []) /\
  (longest_common_suffix l [] = []) /\
  (longest_common_suffix (r ++ [f]) (r' ++ [f']) =
    if f = f' then SNOC f (longest_common_suffix r r') else [])`,
  fs[longest_common_suffix_def,
     Q.prove(`longest_common_suffix l [] = []`, Cases_on `l` >> fs[longest_common_suffix_def])]
  >> ho_match_mp_tac (theorem "longest_common_suffix_ind")
  >> rpt strip_tac
  >> fs[longest_common_suffix_def]
  >- (Induct_on `r'` >> fs[longest_common_suffix_def,APPEND] >> Induct_on `v3` >> fs[longest_common_suffix_def])
  >- (Induct_on `v3` >> fs[longest_common_suffix_def] >> rw[] >> fs[] >> rfs[])
  >> rw[] >> fs[] >> rfs[]);

val longest_prefix_is_prefix = Q.store_thm("longest_prefix_is_prefix",
  `!l r. IS_PREFIX l (longest_common_prefix l r) /\ IS_PREFIX r (longest_common_prefix l r)`,
  ho_match_mp_tac (theorem "longest_common_prefix_ind")
  >> rw[longest_common_prefix_def]);

val longest_prefix_correct = Q.store_thm("longest_prefix_correct",
`!l r s. lcs (longest_common_prefix l r ++ s) l r = lcs s (DROP (LENGTH (longest_common_prefix l r)) l) (DROP (LENGTH (longest_common_prefix l r)) r)`,
  ho_match_mp_tac (theorem "longest_common_prefix_ind")
  >> rpt strip_tac
  >> rw[longest_common_prefix_clauses,cons_lcs_optimal_substructure]);

val longest_suffix_correct = Q.store_thm("longest_prefix_correct",
`!l r s. lcs (s ++ longest_common_suffix l r) l r = lcs s (REVERSE (DROP (LENGTH (longest_common_suffix l r)) (REVERSE l))) (REVERSE (DROP (LENGTH (longest_common_suffix l r)) (REVERSE r)))`,
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
         Q.prove(`l - r - l = (0:num)`,intLib.COOPER_TAC),take_suc_length]);

val longest_common_prefix_reverse = Q.store_thm("longest_common_prefix_reverse",`
  !l r. longest_common_prefix (REVERSE l) (REVERSE r) = REVERSE(longest_common_suffix l r)`,
  ho_match_mp_tac (SNOC_INDUCT)
  >> strip_tac
  >- fs[longest_common_prefix_clauses,longest_common_suffix_clauses]
  >> ntac 3 strip_tac
  >> ho_match_mp_tac (SNOC_INDUCT)
  >> rpt strip_tac
  >> fs[longest_common_prefix_clauses,longest_common_suffix_clauses]
  >> rw[]);

(* Main correctness theorem for optimised LCS algorithm *)

val optimised_lcs_correct = Q.store_thm("optimised_lcs_correct",
  `lcs (optimised_lcs l r) l r`,
  fs[optimised_lcs_def,longest_prefix_correct]
  >> PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> fs[longest_prefix_correct,longest_common_prefix_reverse,
        longest_suffix_correct,lcs_rev,dynamic_lcs_correct]);

val _ = export_theory ();
