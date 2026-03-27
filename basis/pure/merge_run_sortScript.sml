(*
  Verified run-finding (natural) merge sort.

  This is a bottom-up adaptive merge sort that:
  1. Finds natural ascending/descending runs in the input
  2. Merges adjacent pairs of runs, prioritising merges of similar-sized lists.

  Proven to be a permutation, to sort and to be stable.
*)

Theory merge_run_sort
Ancestors
  pred_set arithmetic list rich_list option pair relation sorting mergesort

Libs
  BasicProvers permLib

val every_case_tac = BasicProvers.EVERY_CASE_TAC;

(* ======== Section 1: find_run and its helpers ======== *)

Definition find_run_desc_def:
  find_run_desc R prev [] acc = (prev::acc, []) /\
  find_run_desc R prev (h::t) acc =
    if ~ R prev h then find_run_desc R h t (prev::acc)
    else (prev::acc, h::t)
End

Definition find_run_asc_def:
  find_run_asc R prev [] acc = (REVERSE (prev::acc), []) /\
  find_run_asc R prev (h::t) acc =
    if R prev h
    then find_run_asc R h t (prev::acc)
    else (REVERSE (prev::acc), h::t)
End

Definition find_run_def:
  find_run R [] = ([], []) /\
  find_run R [x] = ([x], []) /\
  find_run R (a::b::rest) =
    if ~ R a b then find_run_desc R b rest [a]
    else find_run_asc R b rest [a]
End

(* -- Helper -- *)

Theorem PERM_cons_REVERSE[local]:
  !x l. PERM (x::l) (REVERSE l ++ [x])
Proof
  rpt gen_tac
  \\ once_rewrite_tac [GSYM REVERSE_DEF]
  \\ rw [PERM_REVERSE]
QED

(* -- find_run_desc lemmas -- *)

Theorem find_run_desc_perm:
  !R prev tl acc run rest.
    find_run_desc R prev tl acc = (run, rest) ==>
    PERM (run ++ rest) (REVERSE acc ++ [prev] ++ tl)
Proof
  Induct_on `tl`
  \\ simp [Once find_run_desc_def]
  >- rw [PERM_cons_REVERSE]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ gvs []
  >- (
    first_x_assum drule
    \\ simp []
    \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
  )
  >- (
    ONCE_REWRITE_TAC [GSYM APPEND]
    \\ rewrite_tac [APPEND_ASSOC]
    \\ irule PERM_CONG
    \\ simp []
    \\ irule PERM_TRANS
    \\ irule_at Any PERM_REVERSE
    \\ rewrite_tac [REVERSE_DEF]
    \\ simp []
  )
QED

Theorem find_run_desc_length:
  !R prev tl acc run rest.
    find_run_desc R prev tl acc = (run, rest) ==>
    LENGTH rest <= LENGTH tl
Proof
  Induct_on `tl`
  \\ simp [Once find_run_desc_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ Q.PAT_X_ASSUM `!R prev acc run rest. _`
      (mp_tac o Q.SPECL [`R`, `h`, `prev::acc`, `run`, `rest`])
  \\ simp []
QED

Theorem sorted_cons_lemma[local]:
  SORTED R xs /\ (xs <> [] ==> R x (HD xs)) ==> SORTED R (x :: xs)
Proof
  Cases_on `xs` \\ fs [SORTED_DEF]
QED

Theorem find_run_desc_strict_sorted:
  !R prev tl acc run rest.
    find_run_desc R prev tl acc = (run, rest) /\
    transitive R /\
    SORTED (\x y. ~ R y x) acc /\ (acc <> [] ==> ~ R (HD acc) prev) ==>
    SORTED (\x y. ~ R y x) run
Proof
  Induct_on `tl`
  \\ simp [Once find_run_desc_def]
  \\ simp [sorted_cons_lemma]
  \\ rw []
  \\ simp [sorted_cons_lemma]
  \\ first_x_assum (drule_then irule)
  \\ simp [sorted_cons_lemma]
  \\ fs [total_def]
  \\ metis_tac []
QED

Theorem find_run_desc_sorted:
  !R prev tl acc run rest.
    find_run_desc R prev tl acc = (run, rest) /\
    transitive R /\ total R /\
    SORTED (\x y. ~ R y x) acc /\ (acc <> [] ==> ~ R (HD acc) prev) ==>
    SORTED R run
Proof
  rw []
  \\ irule SORTED_weaken
  \\ drule_then (irule_at Any) find_run_desc_strict_sorted
  \\ fs [total_def]
  \\ metis_tac []
QED

Theorem mem_sorted_append[local]:
  !R l1 l2 x y.
    transitive R /\ SORTED R (l1 ++ l2) /\ MEM x l1 /\ MEM y l2 ==> R x y
Proof
  Induct_on `l1` \\ rw []
  \\ imp_res_tac SORTED_EQ
  >- (first_x_assum irule \\ simp [MEM_APPEND])
  \\ first_x_assum irule \\ fs [SORTED_EQ]
  \\ qexists_tac `l2` \\ simp []
QED

(* -- find_run_asc lemmas -- *)

Theorem find_run_asc_partition:
  !R prev tl acc run rest.
    find_run_asc R prev tl acc = (run, rest) ==>
    run ++ rest = REVERSE acc ++ [prev] ++ tl
Proof
  Induct_on `tl`
  \\ simp [Once find_run_asc_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ Q.PAT_X_ASSUM `!R prev acc run rest. _`
      (mp_tac o Q.SPECL [`R`, `h`, `prev::acc`, `run`, `rest`])
  \\ simp [Once REVERSE_DEF]
QED

Theorem find_run_asc_length:
  !R prev tl acc run rest.
    find_run_asc R prev tl acc = (run, rest) ==>
    LENGTH rest <= LENGTH tl
Proof
  Induct_on `tl`
  \\ simp [Once find_run_asc_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ TRY (
    Q.PAT_X_ASSUM `!R prev acc run rest. _`
      (mp_tac o Q.SPECL [`R`, `h`, `prev::acc`, `run`, `rest`])
    \\ simp [] \\ NO_TAC)
QED

Theorem find_run_asc_sorted:
  !R prev tl acc run rest.
    transitive R /\ total R /\
    SORTED R (REVERSE (prev::acc)) /\
    find_run_asc R prev tl acc = (run, rest) ==>
    SORTED R run
Proof
  Induct_on `tl`
  \\ simp [Once find_run_asc_def]
  \\ rpt gen_tac \\ strip_tac
  \\ every_case_tac \\ gvs []
  \\ Q.PAT_X_ASSUM `!R prev acc run rest. _`
      (mp_tac o Q.SPECL [`R`, `h`, `prev::acc`, `run`, `rest`])
  \\ impl_tac
  >- (
    rw [] \\ once_rewrite_tac [REVERSE_DEF] \\ rw []
    \\ irule SORTED_APPEND_IMP
    \\ fs [SORTED_DEF]
    \\ `R prev h` by metis_tac [relationTheory.total_def]
    \\ `!x. MEM x acc ==> R x prev` by
         metis_tac [mem_sorted_append, MEM_REVERSE, MEM]
    \\ rw [] \\ metis_tac [relationTheory.transitive_def]
  )
  \\ simp []
QED

(* -- find_run lemmas -- *)

Theorem find_run_perm:
  !R l run rest.
    find_run R l = (run, rest) ==> PERM (run ++ rest) l
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `l` \\ gvs [Once find_run_def]
  \\ Cases_on `t` \\ gvs [Once find_run_def]
  \\ every_case_tac \\ gvs []
  >- (imp_res_tac find_run_desc_perm
      \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ fs [])
  \\ imp_res_tac find_run_asc_partition
  \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND] \\ fs []
QED

Theorem find_run_length:
  !R l run rest.
    find_run R l = (run, rest) /\ l <> [] ==> LENGTH rest < LENGTH l
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `l` \\ gvs []
  \\ Cases_on `t` \\ gvs [Once find_run_def]
  \\ every_case_tac \\ gvs []
  \\ imp_res_tac find_run_desc_length
  \\ imp_res_tac find_run_asc_length
  \\ fs []
QED

Theorem find_run_sorted:
  !R l run rest.
    total R /\ transitive R /\ find_run R l = (run, rest) ==> SORTED R run
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `l` \\ gvs [Once find_run_def, SORTED_DEF]
  \\ Cases_on `t` \\ gvs [Once find_run_def, SORTED_DEF]
  \\ every_case_tac \\ gvs []
  >- (match_mp_tac find_run_desc_sorted
      \\ qexists_tac `h'` \\ qexists_tac `t'`
      \\ qexists_tac `[h]` \\ qexists_tac `rest`
      \\ simp [SORTED_DEF])
  \\ match_mp_tac find_run_asc_sorted
  \\ qexists_tac `h'` \\ qexists_tac `t'`
  \\ qexists_tac `[h]` \\ qexists_tac `rest`
  \\ simp [SORTED_DEF]
  \\ metis_tac [relationTheory.total_def]
QED

(* An alternative (used in the monadic variant). *)

Definition count_while_2_def:
  count_while_2 P [] = 0n /\
  count_while_2 P [x] = 1 /\
  count_while_2 P (x :: y :: zs) = if P x y
    then count_while_2 P (y :: zs) + 1
    else 1
End

Theorem find_run_asc_eq_count:
  !R x xs acc.
  find_run_asc R x xs acc =
  let n = count_while_2 R (x :: xs)
  in (REVERSE acc ++ TAKE n (x :: xs), DROP n (x :: xs))
Proof
  Induct_on `xs`
  \\ simp [find_run_asc_def, count_while_2_def]
  \\ rw []
QED

Theorem find_run_desc_eq_count:
  !R x xs acc.
  find_run_desc R x xs acc =
  let n = count_while_2 (\x y. ~ R x y) (x :: xs)
  in (REVERSE (TAKE n (x :: xs)) ++ acc, DROP n (x :: xs))
Proof
  Induct_on `xs`
  \\ simp [find_run_desc_def, count_while_2_def]
  \\ rw []
QED

Theorem find_run_eq_count:
  find_run R (x :: y :: zs) =
  let n = count_while_2 (\x' y'. R x' y' = R x y) (y :: zs) in
  ((if R x y then I else REVERSE) (x :: TAKE n (y :: zs)), DROP n (y :: zs))
Proof
  simp [find_run_def, find_run_asc_eq_count, find_run_desc_eq_count]
  \\ rw [] \\ fs []
  \\ srw_tac [ETA_ss] []
QED

Theorem count_while_2_length:
  ! R xs.
  count_while_2 R xs <= LENGTH xs /\
  (0 < LENGTH xs ==> 0 < count_while_2 R xs)
Proof
  recInduct count_while_2_ind
  \\ rw [count_while_2_def]
QED

Theorem find_run_length_fst:
  ! R xs.
  LENGTH (FST (find_run R xs)) <= LENGTH xs
Proof
  rw []
  \\ Cases_on `TL xs` \\ Cases_on `xs` \\ fs []
  \\ simp [find_run_eq_count]
  \\ simp [find_run_def]
  \\ rw [LENGTH_TAKE_EQ]
QED

Theorem find_run_length_eq_sub:
  LENGTH (SND (find_run R xs)) = LENGTH xs - LENGTH (FST (find_run R xs))
Proof
  Cases_on `TL xs` \\ Cases_on `xs` \\ fs []
  \\ simp [find_run_eq_count]
  \\ simp [find_run_def]
  \\ rw [LENGTH_TAKE_EQ]
QED

(* ======== Section 2: find_runs (depends on find_run_length) ======== *)

Definition find_runs_def:
  find_runs R [] = [] /\
  find_runs R l =
    let (run, rest) = find_run R l in
      run :: find_runs R rest
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
  \\ metis_tac [find_run_length, listTheory.NOT_NIL_CONS, PAIR_EQ]
End

Theorem find_runs_perm:
  !R l. PERM l (FLAT (find_runs R l))
Proof
  ho_match_mp_tac find_runs_ind
  \\ rw [Once find_runs_def]
  \\ Cases_on `find_run R (v2::v3)` \\ gvs []
  \\ imp_res_tac find_run_perm
  \\ TRY (irule PERM_TRANS
          \\ qexists_tac `q ++ r`
          \\ conj_tac >- metis_tac [PERM_SYM]
          \\ irule PERM_CONG \\ simp [] \\ NO_TAC)
  \\ simp [Once find_runs_def]
QED

Theorem find_runs_every_sorted:
  !R l.
    total R /\ transitive R ==>
    EVERY (SORTED R) (find_runs R l)
Proof
  ho_match_mp_tac find_runs_ind
  \\ rw [Once find_runs_def]
  \\ Cases_on `find_run R (v2::v3)` \\ gvs []
  >- simp [Once find_runs_def]
  \\ metis_tac [find_run_sorted]
QED

(* ======== Section 3: merging into sized runs ======== *)

Definition merge_sizes_def:
  merge_sizes do_merge R [] sz_run = [sz_run] /\
  merge_sizes do_merge R (sz_run2 :: acc) sz_run = (
    if do_merge (FST sz_run) (FST sz_run2)
    then merge_sizes do_merge R acc
        (let (sz, run) = sz_run; (sz2, run2) = sz_run2
            in (sz + sz2, merge R run2 run))
    else sz_run :: sz_run2 :: acc
  )
End

(*
Definition merge_sizes_def:
  merge_sizes R acc run = (case acc of
    [] => [(LENGTH run, run)]
  | (x :: xs) => let
    l = LENGTH run;
    (l2, run2) = x in
    if l * 2 < l2
    then (l, run) :: x :: xs
    else (l + l2, merge R run2 run) :: xs
  )
End
*)

(* When merging in a new run, of length l, perform two kinds of merge.
   Firstly, merge smaller existing runs until their length reaches l.
   Secondly, merge in this run repeatedly unless there would be an
   "unbalanced" merge with a much longer run. This will preserve the invariant
   that the run lengths are at least exponential, and avoid unbalanced merges
   where possible. *)
Definition merge_in_run_def:
  merge_in_run R xs run =
    let l = LENGTH run in
    if l = 0 then xs
    else let ys = (case xs of (t1 :: t2 :: ts) => if FST t2 < l
        then merge_sizes (\sz sz2. sz2 < l) R (t2 :: ts) t1
        else xs
      | _ => xs) in
    merge_sizes (\sz sz2. ~ (sz * 2 < sz2)) R ys (l, run)
End

Definition first_pass_def:
  first_pass R xs = FOLDL (merge_in_run R) [] (find_runs R xs)
End

Theorem merge_sizes_perm[local]:
  !xs run. PERM (FLAT (MAP SND (merge_sizes f R xs run)))
    (FLAT (MAP SND xs) ++ SND run)
Proof
  Induct
  \\ rw [merge_sizes_def]
  \\ rpt (pairarg_tac \\ fs [])
  >- (
    irule PERM_TRANS
    \\ first_x_assum (irule_at Any)
    \\ simp []
    \\ REWRITE_TAC [GSYM APPEND_ASSOC, sortingTheory.PERM_TO_APPEND_SIMPS]
    \\ ONCE_REWRITE_TAC [PERM_SYM]
    \\ irule PERM_TRANS \\ irule_at (Pat `PERM _ (merge _ _ _)`) merge_perm
    \\ simp [PERM_APPEND]
  )
  \\ metis_tac [PERM_APPEND, APPEND_ASSOC]
QED

Theorem merge_in_run_perm:
  !run acc. PERM (FLAT (MAP SND (merge_in_run R acc run)))
    (FLAT (MAP SND acc) ++ run)
Proof
  rw [merge_in_run_def]
  \\ irule PERM_TRANS \\ irule_at Any merge_sizes_perm
  \\ simp []
  \\ irule PERM_CONG
  \\ simp []
  \\ every_case_tac \\ simp []
  \\ irule PERM_TRANS \\ irule_at Any merge_sizes_perm
  \\ simp []
  \\ irule PERM_TRANS \\ irule_at Any PERM_APPEND
  \\ simp []
QED

Theorem FOLDL_merge_in_run_perm[local]:
  !rs acc. PERM (FLAT (MAP SND (FOLDL (merge_in_run R) acc rs)))
    (FLAT (MAP SND acc ++ rs))
Proof
  Induct
  \\ rw []
  \\ irule PERM_TRANS \\ pop_assum (irule_at Any)
  \\ simp []
  \\ irule PERM_CONG
  \\ simp []
  \\ irule merge_in_run_perm
QED

Theorem first_pass_perm:
  !R xs. PERM (FLAT (MAP SND (first_pass R xs))) xs
Proof
  rw [first_pass_def]
  \\ irule PERM_TRANS \\ irule_at Any FOLDL_merge_in_run_perm
  \\ simp []
  \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ irule find_runs_perm
QED

Theorem merge_sizes_every_sorted[local]:
  !sz_run acc.
    total R /\ transitive R /\
    EVERY (SORTED R) (MAP SND acc) /\ SORTED R (SND sz_run) ==>
    EVERY (SORTED R) (MAP SND (merge_sizes f R acc sz_run))
Proof
  Induct_on `acc`
  \\ rw [merge_sizes_def]
  \\ first_x_assum irule
  \\ simp []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [merge_sorted]
QED

Theorem merge_in_run_every_sorted[local]:
  !run acc.
    total R /\ transitive R /\
    EVERY (SORTED R) (MAP SND acc) /\ SORTED R run ==>
    EVERY (SORTED R) (MAP SND (merge_in_run R acc run))
Proof
  rw [merge_in_run_def]
  \\ every_case_tac \\ fs []
  \\ simp [merge_sizes_every_sorted]
QED

Theorem FOLDL_merge_in_run_every_sorted[local]:
  !rs acc.
    total R /\ transitive R /\
    EVERY (SORTED R) (MAP SND acc) /\ EVERY (SORTED R) rs ==>
    EVERY (SORTED R) (MAP SND (FOLDL (merge_in_run R) acc rs))
Proof
  Induct
  \\ rw []
  \\ first_x_assum irule
  \\ simp [merge_in_run_every_sorted]
QED

Theorem first_pass_every_sorted:
  !R xs.
    total R /\ transitive R ==>
    EVERY (SORTED R) (MAP SND (first_pass R xs))
Proof
  rw [first_pass_def]
  \\ irule FOLDL_merge_in_run_every_sorted
  \\ simp [find_runs_every_sorted]
QED

Theorem merge_sizes_neq_nil[local]:
  !acc sz_run. merge_sizes f R acc sz_run <> []
Proof
  Induct
  \\ rw [merge_sizes_def]
QED

Theorem merge_sizes_eq_cons_lemma[local]:
  !acc sz_run.
  merge_sizes f R acc sz_run = hd :: tl ==>
  ?n. tl = DROP n acc /\
  (tl <> [] ==> ~ f (FST hd) (FST (HD tl)))
Proof
  Induct
  \\ rw [merge_sizes_def]
  >- (
    first_x_assum drule
    \\ rw []
    \\ qexists_tac `n + 1`
    \\ simp []
  )
  >- (
    qexists_tac `0`
    \\ simp []
  )
QED

Theorem merge_length[local]:
  LENGTH (merge R xs ys) = LENGTH xs + LENGTH ys
Proof
  qspecl_then [`R`, `xs`, `ys`] mp_tac merge_perm
  \\ rw []
  \\ imp_res_tac PERM_LENGTH
  \\ fs []
QED

Theorem merge_sizes_eq_length_inv:
  ! acc sz_run.
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) acc /\
  FST sz_run = LENGTH (SND sz_run) /\ ~ NULL (SND sz_run) ==>
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) (merge_sizes f R acc sz_run)
Proof
  Induct_on `acc`
  \\ simp [merge_sizes_def, FORALL_PROD]
  \\ rw []
  \\ first_x_assum irule
  \\ fs [merge_length, GSYM rich_listTheory.LENGTH_NOT_NULL]
QED

Theorem merge_in_run_eq_length_inv:
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) acc ==>
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) (merge_in_run R acc r)
Proof
  rw [merge_in_run_def]
  \\ Cases_on `HD acc` \\ Cases_on `acc`
  \\ fs [merge_sizes_def, merge_empty, GSYM NULL_EQ]
  \\ irule merge_sizes_eq_length_inv
  \\ simp []
  \\ every_case_tac \\ fs []
  \\ irule merge_sizes_eq_length_inv
  \\ simp []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [merge_length, GSYM rich_listTheory.LENGTH_NOT_NULL]
QED

Theorem SORTED_DROP_IMP[local]:
  !n xs. SORTED R xs ==> SORTED R (DROP n xs)
Proof
  Induct
  \\ simp []
  \\ Cases \\ simp []
  \\ metis_tac [SORTED_TL]
QED

Theorem SORTED_merge_sizes_lemma[local]:
  SORTED R2 acc /\ (!sz r sz2 r2. ~ f sz sz2 ==> R2 (sz, r) (sz2, r2)) ==>
  SORTED R2 (merge_sizes f R acc sz_run)
Proof
  rw []
  \\ subgoal `!t t2. ~ f (FST t) (FST t2) ==> R2 t t2`
  >- simp [FORALL_PROD]
  \\ Cases_on `merge_sizes f R acc sz_run` \\ simp []
  \\ drule merge_sizes_eq_cons_lemma
  \\ rw []
  \\ irule sorted_cons_lemma
  \\ fs [SORTED_DROP_IMP]
QED

Theorem neq_nil_IMP:
  x <> [] ==> (?y ys. x = y :: ys)
Proof
  Cases_on `x` \\ simp []
QED

(* The interesting case of the size invariant proof. The existing
   sizes go up in at-least-exponential strides, and are to be merged.
   The initial two are less than 'n'. The first may already have been
   merged, so it is merely less than the second. Merging continues until
   'n' is passed, and we need to know it does not overshoot so far that
   it would not itself be merged in the next pass. *)
Theorem merge_sizes_hd_lim[local]:
  !xs sz_run.
  merge_sizes (\sz sz2. sz2 < n) R xs sz_run = hd :: tl /\
  tl <> [] /\ FST sz_run < 2 * n /\
  SORTED (\sz sz2. sz * 2 < sz2) (MAP FST xs) /\
  (xs <> [] ==> FST sz_run < FST (HD xs)) ==>
  FST hd < 2 * n
Proof
  Induct
  \\ simp [merge_sizes_def]
  \\ rw []
  \\ imp_res_tac SORTED_TL
  \\ simp []
  \\ first_x_assum (drule_then irule)
  \\ simp []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ imp_res_tac neq_nil_IMP \\ fs []
QED

(* Not strictly needed for the verification of this variant. *)
Theorem merge_in_run_size_invariant:
  SORTED (\sz sz2. sz * 2 < sz2) (MAP FST acc) /\
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) acc ==>
  SORTED (\sz sz2. sz * 2 < sz2) (MAP FST (merge_in_run R acc r_add))
Proof
  strip_tac
  \\ rw [merge_in_run_def]
  \\ fs [sorted_map]
  \\ Cases_on `HD acc` \\ Cases_on `acc`
  \\ simp [merge_sizes_def, merge_empty]
  \\ fs []
  \\ imp_res_tac SORTED_TL
  \\ rw [] \\ fs []
  \\ every_case_tac \\ fs []
  \\ simp [SORTED_merge_sizes_lemma, sorted_map]
  (* The tricky case that remains is the one where the invariant
     might not hold at the head of the intermediate constructed list. *)
  \\ rpt (pairarg_tac \\ fs [])
  \\ qmatch_asmsub_rename_tac `EVERY _ xs`
  \\ qmatch_goalsub_abbrev_tac `SORTED _ (merge_sizes _ _ merge1 _)`
  \\ Cases_on `merge1`
  \\ fs [merge_sizes_neq_nil]
  \\ imp_res_tac merge_sizes_eq_cons_lemma
  \\ imp_res_tac SORTED_TL
  \\ rw [merge_sizes_def]
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ simp [SORTED_merge_sizes_lemma, SORTED_DROP_IMP]
  )
  >- (
    irule sorted_cons_lemma
    \\ simp [SORTED_DROP_IMP]
    \\ rw []
    \\ gs []
    \\ drule merge_sizes_hd_lim
    \\ simp [sorted_map]
    \\ rw []
    \\ imp_res_tac neq_nil_IMP \\ fs []
  )
QED

(* Not strictly needed for the verification of this variant. *)
Theorem FOLDL_merge_in_run_size_invariant:
  !rs acc.
  SORTED (\sz sz2. sz * 2 < sz2) (MAP FST acc) /\
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs) acc ==>
  SORTED (\sz sz2. sz * 2 < sz2)
    (MAP FST (FOLDL (merge_in_run R) acc rs)) /\
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs)
    (FOLDL (merge_in_run R) acc rs)
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac
  \\ strip_tac
  \\ fs []
  \\ first_x_assum irule
  \\ simp [merge_in_run_eq_length_inv,
          SIMP_RULE arith_ss [] merge_in_run_size_invariant]
QED

Theorem first_pass_size_invariant:
  SORTED (\sz sz2. sz * 2 < sz2)
    (MAP FST (first_pass R xs)) /\
  EVERY (\(sz, xs). sz = LENGTH xs /\ ~ NULL xs)
    (first_pass R xs)
Proof
  REWRITE_TAC [first_pass_def]
  \\ irule FOLDL_merge_in_run_size_invariant
  \\ simp []
QED

(* ======== Section 4: merge_run_sort (top-level) ======== *)

Definition merge_run_sort_def:
  merge_run_sort R xs = FLAT (MAP SND (merge_sizes (\_ _. T) R
        (first_pass R xs) (0, [])))
End

(*
Theorem PERM_FLAT_MAP_REVERSE:
  !xs. PERM (FLAT (MAP REVERSE xs)) (FLAT xs)
Proof
  Induct \\ simp []
  \\ simp [PERM_CONG]
QED
*)

Theorem merge_run_sort_perm:
  !R l. PERM l (merge_run_sort R l)
Proof
  rw [merge_run_sort_def]
  \\ ONCE_REWRITE_TAC [PERM_SYM]
  \\ irule PERM_TRANS \\ irule_at Any merge_sizes_perm
  \\ simp [first_pass_perm]
QED

Theorem SORTED_FLAT_1_lemma[local]:
  LENGTH xs <= 1 /\ EVERY (SORTED R) xs ==>
  SORTED R (FLAT xs)
Proof
  Cases_on `TL xs` \\ Cases_on `xs` \\ fs [ADD1]
QED

Theorem merge_sizes_T_length[local]:
  !acc sz_run. (!sz sz2. f sz sz2) ==>
  LENGTH (merge_sizes f R acc sz_run) <= 1
Proof
  Induct
  \\ simp [merge_sizes_def]
QED

Theorem merge_run_sort_sorted:
  !R l. total R /\ transitive R ==> SORTED R (merge_run_sort R l)
Proof
  rw [merge_run_sort_def]
  \\ irule SORTED_FLAT_1_lemma
  \\ simp [merge_sizes_every_sorted, first_pass_every_sorted]
  \\ simp [merge_sizes_T_length]
QED

Theorem merge_run_sort_SORTS:
  !R. total R /\ transitive R ==> SORTS merge_run_sort R
Proof
  rw [SORTS_DEF] \\ metis_tac [merge_run_sort_perm, merge_run_sort_sorted]
QED

(* ======== Section 5: Stability ======== *)

(* Stability for find_run_asc is easy. For find_run_desc, which reverses,
   this will be OK because each strictly descending run can have at most
   one element that satisfies the special predicate p. *)

Theorem find_run_asc_append_eq[local]:
  !R prev tl acc run rest.
    find_run_asc R prev tl acc = (run, rest) ==>
      REVERSE acc ++ [prev] ++ tl = run ++ rest
Proof
  Induct_on `tl`
  \\ simp [Once find_run_asc_def]
  \\ rw []
  \\ simp []
  \\ res_tac
  \\ fs []
QED

Theorem find_run_desc_append_eq[local]:
  !R prev tl acc run rest.
    find_run_desc R prev tl acc = (run, rest) ==>
      REVERSE acc ++ [prev] ++ tl = REVERSE run ++ rest
Proof
  Induct_on `tl`
  \\ simp [Once find_run_desc_def]
  \\ rw []
  \\ simp []
  \\ res_tac
  \\ fs []
QED

Theorem find_run_append_eq[local]:
  !R xs run rest.
    find_run R xs = (run, rest) ==>
      run ++ rest = xs \/ REVERSE run ++ rest = xs
Proof
  recInduct find_run_ind
  \\ simp [find_run_def]
  \\ rw []
  \\ imp_res_tac find_run_desc_append_eq
  \\ imp_res_tac find_run_asc_append_eq
  \\ fs []
QED

Theorem stable_refl[local] = stable_def |> Q.SPECL [`R`, `xs`, `xs`]
  |> REWRITE_RULE []

Theorem not_R_transitive[local]:
  transitive R /\ total R ==>
  transitive (\x y. ~ R y x)
Proof
  simp [transitive_def, total_def]
  \\ metis_tac []
QED

Theorem strict_desc_stable_reverse_lemma[local]:
  !xs.
    transitive R /\ total R /\ SORTED (\x y. ~ R y x) xs /\
    (!x y. p x /\ p y ==> R x y) ==>
    FILTER p (REVERSE xs) = FILTER p xs
Proof
  Induct
  \\ rw []
  \\ imp_res_tac SORTED_TL
  \\ simp [FILTER_APPEND]
  \\ Cases_on `FILTER p xs = []`
  \\ fs [FILTER_NEQ_NIL]
  \\ gs [SORTED_EQ, not_R_transitive]
  \\ metis_tac []
QED

Theorem find_run_stable:
  !R l run rest.
    transitive R /\ total R /\
    find_run R l = (run, rest) ==>
    stable R l (run ++ rest)
Proof
  recInduct find_run_ind
  \\ simp [find_run_def]
  \\ rw [stable_refl]
  \\ imp_res_tac find_run_desc_append_eq
  \\ imp_res_tac find_run_asc_append_eq
  \\ fs [stable_refl]
  \\ irule stable_cong
  \\ rw [stable_def]
  \\ drule_then irule strict_desc_stable_reverse_lemma
  \\ simp []
  \\ drule_then irule find_run_desc_strict_sorted
  \\ simp []
QED

Theorem find_runs_stable:
  !R l.
    transitive R /\ total R ==>
    stable R l (FLAT (find_runs R l))
Proof
  ho_match_mp_tac find_runs_ind
  \\ rw [Once find_runs_def]
  >- simp [Once find_runs_def, stable_def]
  \\ Cases_on `find_run R (v2::v3)` \\ gvs []
  \\ irule stable_trans
  \\ qexists_tac `q ++ FLAT (find_runs R r)`
  \\ conj_tac
  >- (irule stable_trans
      \\ qexists_tac `q ++ r`
      \\ conj_tac >- metis_tac [find_run_stable]
      \\ irule stable_cong \\ rw [stable_def])
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ irule stable_cong \\ rw [stable_def]
QED

Theorem merge_sizes_stable[local]:
  !acc sz_run. transitive R /\ EVERY (SORTED R) (MAP SND acc) ==>
  stable R (FLAT (REVERSE (MAP SND acc)) ++ SND sz_run)
    (FLAT (REVERSE (MAP SND (merge_sizes f R acc sz_run))))
Proof
  Induct
  \\ rw [merge_sizes_def, stable_refl]
  \\ irule stable_trans
  \\ first_x_assum (irule_at Any)
  \\ rpt (pairarg_tac \\ fs [])
  \\ REWRITE_TAC [GSYM APPEND_ASSOC]
  \\ irule stable_cong
  \\ simp [stable_refl, merge_stable]
QED

Theorem merge_in_run_stable[local]:
  !acc sz_run. transitive R /\ total R /\ EVERY (SORTED R) (MAP SND acc) ==>
  stable R (FLAT (REVERSE (MAP SND acc)) ++ r)
    (FLAT (REVERSE (MAP SND (merge_in_run R acc r))))
Proof
  rw [merge_in_run_def, stable_refl]
  \\ irule stable_trans
  \\ irule_at (Pat `stable _ _ (FLAT _)`) merge_sizes_stable
  \\ simp []
  \\ every_case_tac \\ simp [stable_refl]
  \\ fs [merge_sizes_every_sorted]
  \\ irule stable_cong
  \\ simp [stable_refl]
  \\ irule stable_trans
  \\ irule_at (Pat `stable _ _ (FLAT _)`) merge_sizes_stable
  \\ simp [stable_refl]
QED

Theorem FOLDL_merge_in_run_stable[local]:
  !rs acc. total R /\ transitive R /\
  EVERY (SORTED R) (MAP SND acc) /\ EVERY (SORTED R) rs ==>
  stable R (FLAT (REVERSE (MAP SND acc) ++ rs))
    (FLAT (REVERSE (MAP SND (FOLDL (merge_in_run R) acc rs))))
Proof
  Induct
  \\ simp [stable_refl]
  \\ rw []
  \\ irule stable_trans
  \\ first_x_assum (irule_at Any)
  \\ simp [merge_in_run_every_sorted]
  \\ irule stable_cong
  \\ simp [stable_refl, merge_in_run_stable]
QED

Theorem first_pass_stable:
  !R rs.
    total R /\ transitive R ==>
    stable R rs (FLAT (REVERSE (MAP SND (first_pass R rs))))
Proof
  rw [first_pass_def]
  \\ irule stable_trans
  \\ irule_at Any FOLDL_merge_in_run_stable
  \\ simp [find_runs_every_sorted, find_runs_stable]
QED

Theorem stable_FLAT_1_lemma[local]:
  stable R l (FLAT (REVERSE xs)) /\ LENGTH xs <= 1 ==>
  stable R l (FLAT xs)
Proof
  Cases_on `TL xs` \\ Cases_on `xs` \\ fs []
QED

Theorem merge_run_sort_stable:
  !R l. total R /\ transitive R ==> stable R l (merge_run_sort R l)
Proof
  rw [merge_run_sort_def]
  \\ irule stable_FLAT_1_lemma
  \\ simp [merge_sizes_T_length]
  \\ irule stable_trans
  \\ irule_at Any (merge_sizes_stable)
  \\ simp [MAP_REVERSE, first_pass_every_sorted, first_pass_stable]
QED

Theorem merge_run_sort_STABLE_SORT:
  !R. transitive R /\ total R ==> STABLE merge_run_sort R
Proof
  rw [STABLE_DEF]
  \\ metis_tac [merge_run_sort_SORTS, merge_run_sort_stable, stable_def]
QED

