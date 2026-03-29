(*
  Monadic variants of the merge-run-sort functions, and proofs of equivalence.
*)

Theory merge_run_sort_monadic
Ancestors
  merge_run_sort ml_monadBase mergesort
Libs
  preamble ml_monadBaseLib

(* Part 1: Setup of types and infrastructure. *)

(* The data type of the state. *)
Datatype:
  merge_run_state = <|
                 main_array : ( 'a ) list;
                 copy_array : ( 'a ) list;
                 sz_array : num list;
                |>
End

(* Equivalent to unit, but we need to construct a type so that the translation
   can construct a new exception type. *)
Datatype:
  heap_list_subscript_exn = MR_Subscript
End

(* Setup to use monad translator constants and monad syntax. *)
val acc_fun_defs = define_monad_access_funs ``: 'a merge_run_state``

val mr_manip_funs = define_MRarray_manip_funs acc_fun_defs
        ``MR_Subscript`` ``MR_Subscript``

val _ = ParseExtras.temp_tight_equality ();
val _ = monadsyntax.temp_add_monadsyntax ();

Overload "monad_bind"[local] = ``st_ex_bind``
Overload "monad_unitbind"[local] = ``st_ex_ignore_bind``
Overload "monad_ignore_bind"[local] = ``st_ex_ignore_bind``
Overload "return"[local] = ``st_ex_return``

(* Part 2: Definition of sort functions with runs held in an array. *)

Definition merge_runs_def:
  merge_runs R xi xlen yi ylen base = if xi >= xlen
    then (* no more xs, ys are in correct place *)
      return ()
    else if yi >= ylen
    then do (* no more ys, copy xs to correct place *)
      x <- copy_array_sub xi;
      update_main_array (base + yi + xi) x;
      merge_runs R (xi + 1) xlen yi ylen base
    od
    else do
      x <- copy_array_sub xi;
      y <- main_array_sub (base + xlen + yi);
      b <- return (R x y);
      update_main_array (base + yi + xi) (if b then x else y);
      merge_runs R (xi + (if b then 1 else 0)) xlen
          (yi + (if b then 0 else 1)) ylen base
    od
Termination
  WF_REL_TAC `measure (\(R, xi, xlen, yi, ylen, base). (xlen - xi) + (ylen - yi))`
End

Definition copy_to_copy_def:
  copy_to_copy base xi xlen = if xi >= xlen
    then return ()
    else do
      x <- main_array_sub (base + xi);
      update_copy_array xi x;
      copy_to_copy base (xi + 1) xlen
    od
Termination
  WF_REL_TAC `measure (\(base, xi, xlen). (xlen - xi))`
End

Definition do_merge_array_def:
  do_merge_array R ri arri = do
    xsz <- sz_array_sub (ri + 1);
    ysz <- sz_array_sub ri;
    update_sz_array (ri + 1) (xsz + ysz);
    base <- return (arri - (xsz + ysz));
    copy_to_copy base 0 xsz;
    merge_runs R 0 xsz 0 ysz base
  od
End

Definition merge_sizes_gen_array_def:
  merge_sizes_gen_array R f ri rlen arri =
    if ri + 1 >= rlen
    then return ri
    else do
      sz <- sz_array_sub ri;
      sz2 <- sz_array_sub (ri + 1);
      if f sz sz2
      then do
        do_merge_array R ri arri;
        merge_sizes_gen_array R f (ri + 1) rlen arri
      od
      else return ri
    od
Termination
  WF_REL_TAC `measure (\(R, f, ri, rlen, arri). (rlen - ri))`
End

Definition merge_smaller_array_def:
  merge_smaller_array R n ri rlen arri =
    if ri + 1 >= rlen
    then return ri
    else do
      sz2 <- sz_array_sub (ri + 1);
      if sz2 < n
      then do
        do_merge_array R ri arri;
        merge_smaller_array R n (ri + 1) rlen arri
      od
      else return ri
    od
Termination
  WF_REL_TAC `measure (\(R, n, ri, rlen, arri). (rlen - ri))`
End

Definition merge_similar_array_def:
  merge_similar_array R ri rlen arri =
    if ri + 1 >= rlen
    then return ri
    else do
      sz <- sz_array_sub ri;
      sz2 <- sz_array_sub (ri + 1);
      if sz * 2 < sz2
      then return ri
      else do
        do_merge_array R ri arri;
        merge_similar_array R (ri + 1) rlen arri
      od
    od
Termination
  WF_REL_TAC `measure (\(R, ri, rlen, arri). (rlen - ri))`
End

Definition merge_every_array_def:
  merge_every_array R ri rlen arri =
    if ri + 1 >= rlen
    then return ri
    else do
      do_merge_array R ri arri;
      merge_every_array R (ri + 1) rlen arri
    od
Termination
  WF_REL_TAC `measure (\(R, ri, rlen, arri). (rlen - ri))`
End

Definition merge_in_run_array_def:
  merge_in_run_array R ri rlen arri l = do
    ri2 <- if ri + 1 < rlen
    then do
      l2 <- sz_array_sub (ri + 1);
      if l2 < l then merge_smaller_array R l ri rlen arri
        else return ri
    od else return ri;
    ri3 <- return (ri2 - 1);
    update_sz_array ri3 l;
    merge_similar_array R ri3 rlen (arri + l)
  od
End

Definition find_known_run_array_def:
  find_known_run_array R x b n i arrlen = if i >= arrlen then return n
  else do
    y <- main_array_sub i;
    if R x y = b
    then find_known_run_array R y b (n + 1n) (i + 1n) arrlen
    else return n
  od
Termination
  WF_REL_TAC `measure (\(R, x, b, n, i, arrlen). arrlen - i)`
End

Definition reverse_run_def:
  reverse_run i l = if l < 2
  then return ()
  else let l2 = l - 2 in do
    x <- main_array_sub i;
    j <- return (i + l2 + 1);
    y <- main_array_sub j;
    update_main_array i y;
    update_main_array j x;
    reverse_run (i + 1) l2
  od
End

Definition find_run_array_def:
  find_run_array R i arrlen = if i + 1 >= arrlen
  then return (arrlen - i)
  else do
    x <- main_array_sub i;
    y <- main_array_sub (i + 1);
    b <- return (R x y);
    l <- find_known_run_array R y b 2 (i + 2) arrlen;
    if ~ b
    then reverse_run i l
    else return ();
    return l
  od
End

Definition first_pass_array_def:
  first_pass_array R ri rlen i arrlen =
  if i >= arrlen
  then return ri
  else do
    l <- find_run_array R i arrlen;
    ri2 <- merge_in_run_array R ri rlen i l;
    first_pass_array R ri2 rlen (i + (if l = 0 then 1n else l)) arrlen
  od
Termination
  WF_REL_TAC `measure (\(R, ri, rlen, i, arrlen). arrlen - i)`
End

(* Top-level of the monadic worker. Needs to be wrapped in a "run" function
   that sets up the array and fetches the final list again. *)
Definition merge_run_sort_monadic_def:
  merge_run_sort_monadic R rlen arrlen = do
    ri <- first_pass_array R rlen rlen 0 arrlen;
    merge_every_array R ri rlen arrlen;
    return ()
  od
End

(* Compute an overapproximation of the base-2 logarithm of v *)
Definition above_log2_def:
  above_log2 i v n = if n = 0n \/ v <= n
    then i
    else above_log2 (i + 1n) v (n * 2)
Termination
  WF_REL_TAC `measure (\(i, v, n). (v - n))`
End

Definition copy_into_array_def:
  copy_into_array i [] = return ()
  /\
  copy_into_array i (x :: xs) = do
    update_main_array i x;
    copy_into_array (i + 1) xs
  od
End

Definition copy_from_array_def:
  copy_from_array i acc = if i = 0
  then return acc
  else let j = i - 1 in do
    x <- main_array_sub j;
    copy_from_array j (x :: acc)
  od
End

Definition merge_run_sort_worker_def:
  merge_run_sort_worker R x xs = do
    l <- return (LENGTH xs);
    sz_log <- return (above_log2 0 (l + 1) 1 + 2);
    alloc_main_array l x;
    alloc_copy_array l x;
    alloc_sz_array sz_log 0;
    copy_into_array 0 xs;
    merge_run_sort_monadic R sz_log l;
    copy_from_array l [];
  od
End

(* Get straight to the key proof. Can we show that do_merge_array is merge
   and that merge_smaller_array is merge_sizes? *)

Definition mk_st_def:
  mk_st xs sz_junk junk copy =
    (<|
        sz_array := sz_junk ++ (MAP LENGTH xs);
        main_array := FLAT (REVERSE xs) ++ junk;
        copy_array := copy
    |>)
End

Theorem return_bind_eq[local]:
  st_ex_bind (return v) f = f v
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def, FUN_EQ_THM]
QED

Theorem st_ex_ignore_bind_simp[local]:
  st_ex_ignore_bind f g = st_ex_bind f (\_. g)
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_ignore_bind_def]
QED

Theorem bind_success_eqI:
  m st = (M_success v, st2) /\ f v st2 = rhs ==>
  st_ex_bind m f st = rhs
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem copy_array_sub_eq[local]:
  i < LENGTH c ==>
  st_ex_bind (copy_array_sub i) f
    (mk_st xs szj j c) =
  f (EL i c) (mk_st xs szj j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "copy_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def]
QED

Theorem update_copy_array_eq[local]:
  i < LENGTH c ==>
  st_ex_bind (update_copy_array i x) f (mk_st xss szj j c) =
  f () (mk_st xss szj j (LUPDATE x i c))
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "update_copy_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def]
QED

Theorem main_array_sub_hd_app_cons_eq[local]:
  i = LENGTH xs + SUM (MAP LENGTH pre) ==>
  st_ex_bind (main_array_sub i) f
    (mk_st ((xs ++ y :: ys) :: pre) szj j c) =
  f y (mk_st ((xs ++ y :: ys) :: pre) szj j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "main_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LENGTH_FLAT, MAP_REVERSE, SUM_REVERSE,
        EL_APPEND1, EL_APPEND2]
QED

Theorem main_array_sub_extra_EL[local]:
  SUM (MAP LENGTH pre) <= i /\ i < LENGTH ys + SUM (MAP LENGTH pre) ==>
  st_ex_bind (main_array_sub i) f
    (mk_st pre szj ys c) =
  f (EL (i - SUM (MAP LENGTH pre)) ys) (mk_st pre szj ys c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "main_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LENGTH_FLAT, MAP_REVERSE, SUM_REVERSE,
        EL_APPEND1, EL_APPEND2]
QED

Theorem main_array_sub_extra[local]:
  !xs. i = LENGTH xs + SUM (MAP LENGTH pre) ==>
  st_ex_bind (main_array_sub i) f
    (mk_st pre szj (xs ++ y :: ys) c) =
  f y (mk_st pre szj (xs ++ y :: ys) c)
Proof
  simp [main_array_sub_extra_EL, EL_APPEND2]
QED

Theorem update_main_array_hd_app_cons_eq[local]:
  i = LENGTH xs + SUM (MAP LENGTH pre) ==>
  st_ex_bind (update_main_array i x) f
    (mk_st ((xs ++ y :: ys) :: pre) szj j c) =
  f () (mk_st ((xs ++ x :: ys) :: pre) szj j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "update_main_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LENGTH_FLAT, MAP_REVERSE, SUM_REVERSE,
        LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_DEF]
QED

Theorem update_main_array_extra_LUPDATE[local]:
  SUM (MAP LENGTH pre) <= i /\ i < LENGTH ys + SUM (MAP LENGTH pre) ==>
  st_ex_bind (update_main_array i x) f
    (mk_st pre szj ys c) =
  f () (mk_st pre szj (LUPDATE x (i - SUM (MAP LENGTH pre)) ys) c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "update_main_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LENGTH_FLAT, MAP_REVERSE, SUM_REVERSE,
        LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_DEF]
QED

Definition mk_st_eq_def:
  mk_st_eq xs szs j cxs st = (st = mk_st xs szs j cxs)
End

val mk_st_unfold = qpat_x_assum `mk_st_eq _ _ _ _ _`
    (assume_tac o REWRITE_RULE [mk_st_eq_def])
  \\ full_simp_tac bool_ss []

Theorem mk_st_eqI[local]:
  xs = xs2 /\ szs = szs2 /\ j = j2 /\ cxs = cxs2 ==>
  mk_st_eq xs szs j cxs (mk_st xs2 szs2 j2 cxs2)
Proof
  simp [mk_st_eq_def]
QED

Theorem mk_st_eq_mk_stI[local] =
  REWRITE_RULE [mk_st_eq_def] mk_st_eqI

Theorem merge_runs_empty_ys_eq_lemma:
  ! xs xi csp sp fin st.
  xi + LENGTH xs = xlen /\
  base = SUM (MAP LENGTH pre) /\ LENGTH sp = LENGTH xs /\
  xi = LENGTH csp /\ LENGTH fin = ylen + xi /\
  mk_st_eq ((fin ++ sp) :: pre) szj j (csp ++ xs ++ j2) st ==>
  merge_runs R xi xlen ylen ylen base st =
    (M_success (), (mk_st ((fin ++ xs) :: pre) szj j
        (csp ++ xs ++ j2)))
Proof
  Induct
  \\ ONCE_REWRITE_TAC [merge_runs_def]
  \\ rw [st_ex_ignore_bind_simp]
  \\ mk_st_unfold
  >- (
    simp [merge_empty, ml_monadBaseTheory.st_ex_return_def]
  )
  >- (
    simp [copy_array_sub_eq, EL_APPEND1, EL_APPEND2]
    \\ Cases_on `sp` \\ fs []
    \\ simp [update_main_array_hd_app_cons_eq]
    \\ first_x_assum (qspec_then `spc ++ [x]` (assume_tac o Q.GENL [`spc`, `x`]))
    \\ fs []
    \\ irule EQ_TRANS
    \\ first_x_assum (irule_at Any)
    \\ simp []
    \\ irule_at Any mk_st_eqI
    \\ irule_at Any mk_st_eq_mk_stI
    \\ simp []
  )
QED

Theorem merge_runs_eq:
  ! R xs ys xi yi csp sp fin st.
  xi + LENGTH xs = xlen /\ yi + LENGTH ys = ylen /\
  base = SUM (MAP LENGTH pre) /\ LENGTH sp = LENGTH xs /\
  LENGTH csp = xi /\ LENGTH fin = xi + yi /\
  mk_st_eq ((fin ++ sp ++ ys) :: pre) szj j (csp ++ xs ++ j2) st ==>
  merge_runs R xi xlen yi ylen base st =
    (M_success (), (mk_st ((fin ++ merge R xs ys) :: pre) szj j
        (csp ++ xs ++ j2)))
Proof
  recInduct merge_ind
  \\ rw []
  \\ mk_st_unfold
  >- (
    ONCE_REWRITE_TAC [merge_runs_def]
    \\ simp [merge_empty, ml_monadBaseTheory.st_ex_return_def]
  )
  >- (
    simp [SIMP_RULE bool_ss [mk_st_eq_def] merge_runs_empty_ys_eq_lemma]
    \\ simp [merge_empty]
  )
  >- (
    ONCE_REWRITE_TAC [merge_runs_def]
    \\ simp [merge_empty, ml_monadBaseTheory.st_ex_return_def]
  )
  >- (
    ONCE_REWRITE_TAC [merge_runs_def]
    \\ simp [copy_array_sub_eq, EL_APPEND1, EL_APPEND2]
    \\ simp [st_ex_ignore_bind_simp, return_bind_eq]
    \\ simp [main_array_sub_hd_app_cons_eq]
    \\ Cases_on `sp` \\ fs []
    \\ REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
    \\ simp [update_main_array_hd_app_cons_eq]
    \\ TOP_CASE_TAC \\ fs []
    >- (
      first_x_assum (qspec_then `spc_z ++ [x_z]`
        (assume_tac o Q.GENL [`spc_z`, `x_z`]))
      \\ fs []
      \\ irule EQ_TRANS \\ first_x_assum (irule_at Any)
      \\ simp []
      \\ irule_at Any mk_st_eqI
      \\ irule_at Any mk_st_eq_mk_stI
      \\ simp [merge_def]
    )
    >- (
      irule EQ_TRANS \\ first_x_assum (irule_at Any)
      \\ simp []
      \\ irule_at Any mk_st_eqI
      \\ irule_at Any mk_st_eq_mk_stI
      \\ simp [merge_def]
    )
  )
QED

Theorem copy_to_copy_eq:
  ! xs xi copied j2 st.
  xi + LENGTH xs = xlen /\
  base = SUM (MAP LENGTH pre) /\
  LENGTH copied = xi /\
  LENGTH xs <= LENGTH j2 /\
  mk_st_eq ((copied ++ xs ++ oth) :: pre) szj j (copied ++ j2) st ==>
  copy_to_copy base xi xlen st =
    (M_success (), (mk_st ((copied ++ xs ++ oth) :: pre) szj j
        (copied ++ xs ++ DROP (LENGTH xs) j2)))
Proof
  Induct
  \\ rw []
  \\ ONCE_REWRITE_TAC [copy_to_copy_def]
  \\ rw []
  \\ mk_st_unfold
  >- (
    simp [ml_monadBaseTheory.st_ex_return_def]
  )
  >- (
    simp [st_ex_ignore_bind_simp, return_bind_eq]
    \\ REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
    \\ simp [main_array_sub_hd_app_cons_eq]
    \\ simp [update_copy_array_eq]
    \\ Cases_on `j2` \\ fs []
    \\ first_x_assum (qspec_then `spc ++ [x]` (assume_tac o Q.GENL [`spc`, `x`]))
    \\ fs []
    \\ irule EQ_TRANS \\ first_x_assum (irule_at Any)
    \\ simp []
    \\ irule_at Any mk_st_eqI
    \\ irule_at Any mk_st_eq_mk_stI
    \\ simp []
  )
QED

Theorem sz_array_sub_bind_eq:
  LENGTH szj <= i /\ i - LENGTH szj < LENGTH xss ==>
  st_ex_bind (sz_array_sub i) f (mk_st xss szj j c) =
  f (LENGTH (EL (i - LENGTH szj) xss)) (mk_st xss szj j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "sz_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, EL_APPEND2, EL_MAP]
QED

Theorem update_sz_array_append_eq:
  i = LENGTH szj + 1 /\ n = LENGTH xs + LENGTH ys ==>
  update_sz_array i n (mk_st (ys :: xs :: pre) szj j c) =
    (M_success (), mk_st ((xs ++ ys) :: pre) (szj ++ [LENGTH ys]) j c)
Proof
  rw []
  \\ simp [fetch "-" "update_sz_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_DEF]
QED

Theorem update_sz_array_append_bind_eq:
  i = LENGTH szj + 1 /\ n = LENGTH xs + LENGTH ys ==>
  st_ex_bind (update_sz_array i n) f (mk_st (ys :: xs :: pre) szj j c) =
    f () (mk_st ((xs ++ ys) :: pre) (szj ++ [LENGTH ys]) j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [update_sz_array_append_eq]
QED

Theorem update_sz_array_extend_eq:
  i + 1 = LENGTH szj /\ n = LENGTH xs ==>
  update_sz_array i n (mk_st xss szj (xs ++ j) c) =
    (M_success (), mk_st (xs :: xss) (TAKE i szj) j c)
Proof
  rw []
  \\ simp [fetch "-" "update_sz_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_DEF]
  \\ irule LIST_EQ
  \\ simp [EL_APPEND, EL_LUPDATE]
  \\ rw []
  \\ simp [EL_TAKE]
QED

Theorem update_sz_array_extend_bind_eq:
  i + 1 = LENGTH szj /\ n = LENGTH xs ==>
  st_ex_bind (update_sz_array i n) f (mk_st xss szj (xs ++ j) c) =
    f () (mk_st (xs :: xss) (TAKE i szj) j c)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [update_sz_array_extend_eq]
QED

Theorem do_merge_array_eq:
  ri = LENGTH szj /\
  arri = LENGTH xs + LENGTH ys + SUM (MAP LENGTH pre) /\
  LENGTH xs <= LENGTH c ==>
  do_merge_array R ri arri (mk_st (ys :: xs :: pre) szj j c) =
    (M_success (), (mk_st (merge R xs ys :: pre) (szj ++ [LENGTH ys]) j
        (xs ++ DROP (LENGTH xs) c)))
Proof
  rw [do_merge_array_def]
  \\ simp [st_ex_ignore_bind_simp, return_bind_eq]
  \\ simp [sz_array_sub_bind_eq]
  \\ simp [update_sz_array_append_bind_eq]
  \\ irule bind_success_eqI
  \\ irule_at Any copy_to_copy_eq
  \\ irule_at Any mk_st_eqI
  \\ csimp [APPEND_11_LENGTH]
  \\ irule EQ_TRANS
  \\ irule_at Any merge_runs_eq
  \\ irule_at Any mk_st_eqI
  \\ csimp [APPEND_11_LENGTH]
QED

Definition add_lengths_def:
  add_lengths xss = MAP (\xs. (LENGTH xs, xs)) xss
End

Theorem add_lengths_simps[local]:
  add_lengths [] = [] /\
  add_lengths (xs :: xss) = (LENGTH xs, xs) :: add_lengths xss /\
  MAP SND (add_lengths xss) = xss /\
  LENGTH (add_lengths xss) = LENGTH xss
Proof
  simp [add_lengths_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem add_lengths_MAP_SND_eq[local]:
  EVERY (\(sz, xs). sz = LENGTH xs) xss ==>
  add_lengths (MAP SND xss) = xss
Proof
  rw [add_lengths_def, MAP_MAP_o]
  \\ irule EQ_TRANS
  \\ irule_at Any MAP_CONG
  \\ simp []
  \\ qexists_tac `I`
  \\ fs [EVERY_MEM, FORALL_PROD]
QED

Definition is_eq_def:
  is_eq x y = (x = y)
End

Theorem is_eq_bind_successD:
  is_eq (st_ex_bind f g st) r ==>
  (?r'. is_eq (f st) r' /\
    (!x s. r' = (M_success x, s) ==> is_eq (g x s) r))
Proof
  rw [is_eq_def]
  \\ simp [bind_success_eqI]
QED

Theorem is_eq_bind_success_real_eqD:
  is_eq (st_ex_bind f g st) r ==>
  (!x s. f st = (M_success x, s) ==> is_eq (g x s) r)
Proof
  rw [is_eq_def]
  \\ simp [bind_success_eqI]
QED

Theorem merge_length[local]:
  LENGTH (merge R xs ys) = LENGTH xs + LENGTH ys
Proof
  qspecl_then [`R`, `xs`, `ys`] mp_tac merge_perm
  \\ rw []
  \\ imp_res_tac PERM_LENGTH
  \\ fs []
QED

Theorem merge_sizes_gen_array_eq:
  ! R f ri rlen arri xs xss szj j c r.
  is_eq (merge_sizes_gen_array R f ri rlen arri
    (mk_st (xs :: xss) szj j c)) r /\
  ri = LENGTH szj /\ ri + LENGTH xss + 1 = rlen /\
  arri = LENGTH xs + SUM (MAP LENGTH xss) /\
  arri <= LENGTH c ==>
  ?szj2 c2.
  let ys = merge_sizes f R (add_lengths xss) (LENGTH xs, xs)
  in
  r = (M_success (rlen - LENGTH ys), mk_st (MAP SND ys) (szj ++ szj2) j c2) /\
  LENGTH szj + LENGTH szj2 + LENGTH ys = rlen /\ LENGTH c2 = LENGTH c
Proof
  recInduct merge_sizes_gen_array_ind
  \\ rpt gen_tac \\ disch_tac
  \\ ONCE_REWRITE_TAC [merge_sizes_gen_array_def]
  \\ rw []
  >- (
    Cases_on `xss` \\ fs []
    \\ fs [is_eq_def, ml_monadBaseTheory.st_ex_return_def]
    \\ rw [merge_sizes_def, add_lengths_simps]
    \\ irule_at Any mk_st_eq_mk_stI
    \\ simp []
  )
  >- (
    Cases_on `xss` \\ fs []
    \\ fs [st_ex_ignore_bind_simp, return_bind_eq]
    \\ fs [sz_array_sub_bind_eq]
    \\ simp [merge_sizes_def, add_lengths_simps]
    \\ rw [] \\ fs []
    >- (
      dxrule is_eq_bind_success_real_eqD
      \\ simp [do_merge_array_eq]
      \\ rw []
      \\ first_x_assum (drule_then drule)
      \\ simp [merge_length]
      \\ rw []
      \\ irule_at Any mk_st_eq_mk_stI
      \\ simp []
    )
    >- (
      fs [is_eq_def, ml_monadBaseTheory.st_ex_return_def]
      \\ rw []
      \\ irule_at Any mk_st_eq_mk_stI
      \\ simp [merge_sizes_def, add_lengths_simps]
    )
  )
QED

Theorem merge_smaller_array_eq:
  ! R n ri rlen arri.
  merge_smaller_array R n ri rlen arri =
  merge_sizes_gen_array R (\sz sz2. sz2 < n) ri rlen arri
Proof
  recInduct merge_smaller_array_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [merge_smaller_array_def]
  \\ ONCE_REWRITE_TAC [merge_sizes_gen_array_def]
  \\ rw []
  \\ rw [FUN_EQ_THM]
  \\ simp [st_ex_bind_def |> Q.ISPEC `sz_array_sub i`]
  \\ every_case_tac
  \\ fs [fetch "-" "sz_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ res_tac
  \\ simp []
QED

Theorem merge_similar_array_eq:
  ! R ri rlen arri.
  merge_similar_array R ri rlen arri =
  merge_sizes_gen_array R (\sz sz2. ~ (sz * 2 < sz2)) ri rlen arri
Proof
  recInduct merge_similar_array_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [merge_similar_array_def]
  \\ ONCE_REWRITE_TAC [merge_sizes_gen_array_def]
  \\ rw [FUN_EQ_THM]
  \\ simp [st_ex_bind_def |> Q.ISPEC `sz_array_sub i`]
  \\ every_case_tac
QED

Theorem merge_every_array_eq:
  ! R ri rlen arri.
  merge_every_array R ri rlen arri =
  merge_sizes_gen_array R (\sz sz2. T) ri rlen arri
Proof
  recInduct merge_every_array_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [merge_every_array_def]
  \\ ONCE_REWRITE_TAC [merge_sizes_gen_array_def]
  \\ rw [FUN_EQ_THM]
  \\ simp [st_ex_bind_def |> Q.ISPEC `sz_array_sub i`]
  \\ every_case_tac
  \\ fs [fetch "-" "sz_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [do_merge_array_def]
  \\ simp [st_ex_ignore_bind_simp, st_ex_bind_def]
  \\ every_case_tac
  \\ fs [fetch "-" "sz_array_sub_def", ml_monadBaseTheory.monad_eqs]
QED

Overload mk_st_ret_xs[local] =
  ``\xss szj j c rlen. (M_success (rlen - LENGTH xss),
        mk_st xss szj j c)``

Theorem merge_sizes_same_length:
  !xss sz_run.
  SUM (MAP LENGTH (MAP SND (merge_sizes f R xss sz_run))) =
    LENGTH (SND sz_run) + SUM (MAP LENGTH (MAP SND xss))
Proof
  Induct
  \\ simp [merge_sizes_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs[])
  \\ simp [merge_length]
QED

Theorem merge_in_run_array_eq:
  is_eq (merge_in_run_array R ri rlen arri l
    (mk_st xss szj (xs ++ j) c)) r /\
  ri = LENGTH szj /\ ri + LENGTH xss = rlen /\
  arri = SUM (MAP LENGTH xss) /\
  arri + LENGTH xs <= LENGTH c /\ l = LENGTH xs /\
  EVERY ($~ o NULL) xss /\
  0 < ri /\ 0 < l
  ==>
  ?szj2 c2.
  r = mk_st_ret_xs (MAP SND (merge_in_run R (add_lengths xss) xs))
      szj2 j c2 rlen /\
  LENGTH szj2 + LENGTH (merge_in_run R (add_lengths xss) xs) = rlen /\
  LENGTH c2 = LENGTH c
Proof
  rpt strip_tac
  \\ fs [merge_in_run_array_def, merge_in_run_def]
  \\ Cases_on `xs = []` \\ fs []
  \\ qmatch_goalsub_abbrev_tac `merge_sizes _ _ merge_smaller_step`
  \\ subgoal `SUM (MAP LENGTH (MAP SND merge_smaller_step)) =
            SUM (MAP LENGTH xss) /\
        add_lengths (MAP SND merge_smaller_step) = merge_smaller_step`
  >- (
    fs [markerTheory.Abbrev_def]
    \\ Cases_on `TL xss` \\ Cases_on `xss` \\ fs [add_lengths_simps]
    \\ rw [] \\ fs [add_lengths_simps]
    \\ simp [merge_sizes_same_length, add_lengths_simps]
    \\ irule add_lengths_MAP_SND_eq
    \\ irule MONO_EVERY
    \\ irule_at Any (merge_sizes_eq_length_inv)
    \\ simp [FORALL_PROD]
    \\ simp [add_lengths_def, EVERY_MAP]
    \\ fs [combinTheory.o_DEF]
  )
  \\ dxrule is_eq_bind_successD
  \\ strip_tac
  \\ subgoal `?szj3 c3. r' = mk_st_ret_xs (MAP SND merge_smaller_step)
        szj3 (xs ++ j) c3 rlen /\
        LENGTH szj3 + LENGTH merge_smaller_step = rlen /\
        0 < LENGTH szj3 /\ LENGTH c3 = LENGTH c`
  >- (
    Cases_on `LENGTH xss < 2 \/ LENGTH (EL 1 xss) >= LENGTH xs`
    >- (
      Cases_on `TL xss` \\ Cases_on `xss` \\ fs []
      \\ fs [markerTheory.Abbrev_def]
      \\ gs [add_lengths_simps, is_eq_def, ml_monadBaseTheory.st_ex_return_def]
      \\ rw []
      \\ simp [sz_array_sub_bind_eq]
      \\ irule_at Any mk_st_eq_mk_stI
      \\ simp []
    )
    \\ Cases_on `TL xss` \\ Cases_on `xss` \\ fs []
    \\ fs [markerTheory.Abbrev_def]
    \\ gs [add_lengths_simps, sz_array_sub_bind_eq]
    \\ fs [merge_smaller_array_eq]
    \\ dxrule merge_sizes_gen_array_eq
    \\ rw []
    \\ irule_at Any mk_st_eq_mk_stI
    \\ gs [add_lengths_simps]
  )
  \\ fs []
  \\ qpat_x_assum `is_eq _ (M_success _, _)` kall_tac
  \\ qpat_x_assum `is_eq _ _` mp_tac
  \\ simp [st_ex_ignore_bind_simp, return_bind_eq]
  \\ simp [update_sz_array_extend_bind_eq]
  \\ simp [merge_similar_array_eq]
  \\ disch_tac \\ dxrule merge_sizes_gen_array_eq
  \\ simp [add_lengths_simps]
  \\ rw []
  \\ irule_at Any mk_st_eq_mk_stI
  \\ gs [add_lengths_simps]
QED

Theorem find_known_run_array_eq:
  ! R x b n i arrlen xs xss szj ys c st.
  n = LENGTH xs /\ i = LENGTH xs + SUM (MAP LENGTH xss) /\
  i + LENGTH ys = arrlen /\
  mk_st_eq xss szj (REVERSE xs ++ ys) c st ==>
  find_known_run_array R x b n i arrlen st =
    (M_success (n + count_while_2 (\x y. R x y = b) (x :: ys) - 1),
        mk_st xss szj (REVERSE xs ++ ys) c)
Proof
  recInduct find_known_run_array_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [find_known_run_array_def]
  \\ mk_st_unfold
  \\ Cases_on `ys` \\ fs []
  >- (
    simp [ml_monadBaseTheory.st_ex_return_def]
    \\ simp [count_while_2_def]
  )
  >- (
    simp [main_array_sub_extra]
    \\ TOP_CASE_TAC
    >- (
      first_x_assum drule
      \\ disch_then (qspec_then `z :: zs` (mp_tac o Q.GENL [`z`, `zs`]))
      \\ simp [ADD1]
      \\ disch_tac
      \\ irule EQ_TRANS
      \\ pop_assum (irule_at Any)
      \\ simp []
      \\ irule_at Any mk_st_eqI
      \\ simp [count_while_2_def]
      \\ REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
    )
    >- (
      simp [ml_monadBaseTheory.st_ex_return_def]
      \\ simp [count_while_2_def]
    )
  )
QED

Theorem find_known_run_array_eq_2[local] =
  find_known_run_array_eq |> SPEC_ALL |> Q.GEN `xs`
    |> Q.SPEC `[x; y]` |> GEN_ALL

Theorem reverse_run_eq:
  !i l xs ys st.
  i = SUM (MAP LENGTH xss) + LENGTH xs /\
  l <= LENGTH ys /\
  mk_st_eq xss szj (xs ++ ys) c st ==>
  reverse_run i l st =
    (M_success (), mk_st xss szj (xs ++ REVERSE (TAKE l ys) ++ DROP l ys) c)
Proof
  recInduct reverse_run_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [reverse_run_def]
  \\ mk_st_unfold
  \\ rw []
  >- (
    simp [ml_monadBaseTheory.st_ex_return_def]
    \\ irule mk_st_eq_mk_stI
    \\ simp []
    \\ subgoal `REVERSE (TAKE l ys) = TAKE l ys` \\ simp []
    \\ Cases_on `TL ys` \\ Cases_on `ys` \\ fs []
    \\ rw [TAKE_def]
  )
  >- (
    qspecl_then [`ys`, `l - 1`] mp_tac LESS_LENGTH
    \\ rw []
    \\ simp [main_array_sub_extra_EL, return_bind_eq, EL_APPEND2, EL_APPEND1]
    \\ simp [TAKE_APPEND1, DROP_APPEND2, TAKE_LENGTH_TOO_LONG, REVERSE_APPEND]
    \\ Cases_on `ys1` \\ fs []
    \\ simp [st_ex_ignore_bind_simp]
    \\ simp [update_main_array_extra_LUPDATE, LUPDATE_APPEND1,
        LUPDATE_APPEND2, LUPDATE_DEF]
    \\ first_x_assum (qspec_then `zs ++ [z]` (mp_tac o Q.GENL [`z`, `zs`]))
    \\ rw [ADD1]
    \\ irule EQ_TRANS \\ first_x_assum (irule_at Any)
    \\ simp []
    \\ irule_at Any mk_st_eqI
    \\ irule_at Any mk_st_eq_mk_stI
    \\ simp [DROP_APPEND1, TAKE_APPEND1, TAKE_LENGTH_TOO_LONG]
  )
QED

Theorem count_while_2_length_trans[local]:
  LENGTH xs <= n ==>
  count_while_2 R xs <= n
Proof
  metis_tac [count_while_2_length, LE_TRANS]
QED

Theorem find_run_array_eq:
  i = SUM (MAP LENGTH xss) /\
  i + LENGTH ys = arrlen /\
  mk_st_eq xss szj ys c st ==>
  find_run_array R i arrlen st =
    (M_success (LENGTH (FST (find_run R ys))),
        mk_st xss szj (FST (find_run R ys) ++ SND (find_run R ys)) c)
Proof
  rw [find_run_array_def]
  \\ mk_st_unfold
  >- (
    simp [ml_monadBaseTheory.st_ex_return_def]
    \\ Cases_on `TL ys` \\ Cases_on `ys` \\ fs [ADD1]
    \\ simp [find_run_def]
  )
  \\ Cases_on `TL ys` \\ Cases_on `ys` \\ fs [ADD1]
  \\ simp [main_array_sub_extra |> Q.SPEC `[]` |> SIMP_RULE list_ss [],
        main_array_sub_extra |> Q.SPEC `[x]` |> SIMP_RULE list_ss []]
  \\ simp [st_ex_ignore_bind_simp, return_bind_eq]
  \\ irule bind_success_eqI
  \\ irule_at Any find_known_run_array_eq_2
  \\ simp []
  \\ irule_at Any mk_st_eqI
  \\ simp []
  \\ rw []
  >- (
    irule bind_success_eqI
    \\ irule_at Any reverse_run_eq
    \\ simp [ml_monadBaseTheory.st_ex_return_def]
    \\ irule_at Any mk_st_eqI
    \\ simp []
    \\ simp [find_run_eq_count, ADD1, LENGTH_TAKE_EQ]
    \\ csimp []
    \\ simp [count_while_2_length_trans]
  )
  >- (
    simp [return_bind_eq]
    \\ simp [ml_monadBaseTheory.st_ex_return_def]
    \\ simp [find_run_eq_count, ADD1, LENGTH_TAKE_EQ]
    \\ simp [count_while_2_length_trans]
  )
QED

Theorem FST_find_run_neq_nil[local]:
  xs <> [] ==> FST (find_run R xs) <> []
Proof
  Cases_on `TL xs` \\ Cases_on `xs` \\ fs []
  \\ simp [find_run_eq_count]
  \\ simp [find_run_def]
  \\ rw []
QED

Theorem merge_in_run_total_length:
  SUM (MAP (LENGTH o SND) (merge_in_run R xs r)) =
  SUM (MAP (LENGTH o SND) xs) + LENGTH r
Proof
  qspecl_then [`R`, `r`, `xs`] mp_tac (GEN_ALL merge_in_run_perm)
  \\ rw []
  \\ imp_res_tac PERM_LENGTH
  \\ fs [LENGTH_FLAT, MAP_MAP_o]
QED

Theorem merge_in_run_MAP_SND_invs[local]:
  EVERY ($¬ ∘ NULL) xss /\ SORTED (\a b. 2 * LENGTH a < LENGTH b) xss ==>
  EVERY ($¬ ∘ NULL) (MAP SND (merge_in_run R (add_lengths xss) r)) /\
  SORTED (\a b. 2 * LENGTH a < LENGTH b)
    (MAP SND (merge_in_run R (add_lengths xss) r))
Proof
  strip_tac
  \\ qspecl_then [`r`, `add_lengths xss`, `R`] mp_tac
    (GEN_ALL merge_in_run_eq_length_inv)
  \\ impl_tac
  >- (
    fs [add_lengths_def, EVERY_MAP, FORALL_PROD, o_DEF]
  )
  \\ rw []
  >- (
    fs [EVERY_MEM, MEM_MAP, FORALL_PROD, EXISTS_PROD]
  )
  >- (
    simp [sorted_map]
    \\ irule SORTED_weaken
    \\ irule_at Any (REWRITE_RULE [sorted_map] merge_in_run_size_invariant)
    \\ simp [FORALL_PROD, EVERY_MAP, add_lengths_def, sorted_map, inv_image_def]
    \\ fs [o_DEF]
    \\ rw []
    \\ fs [EVERY_MEM, FORALL_PROD, add_lengths_def]
    \\ res_tac
    \\ simp []
  )
QED

Theorem find_runs_neq_nil_def[local]:
  xs <> [] ==>
  find_runs R xs = FST (find_run R xs) :: find_runs R (SND (find_run R xs))
Proof
  Cases_on `xs`
  \\ simp [find_runs_def]
  \\ pairarg_tac \\ simp []
QED

Theorem size_invariant_imp_sum_ineq:
  SORTED (λa b. 2 * LENGTH a < LENGTH b) xss /\
  xss <> [] /\ HD xss <> [] ==>
  2 ** (LENGTH xss - 1) <= SUM (MAP LENGTH xss)
Proof
  rw []
  \\ subgoal `!n. n < LENGTH xss ==> LENGTH (EL n xss) >= (2 ** n) * LENGTH (HD xss)`
  >- (
    Induct
    \\ rw []
    \\ fs []
    \\ imp_res_tac SORTED_EL_SUC
    \\ fs [EXP]
  )
  \\ qspec_then `xss` mp_tac SNOC_CASES
  \\ first_x_assum (qspec_then `LENGTH xss - 1` mp_tac)
  \\ Cases_on `HD xss`
  \\ rw []
  \\ fs [MAP_SNOC, SUM_SNOC, EL_LENGTH_SNOC, ADD1]
QED

Theorem first_pass_array_eq:
  ! R ri rlen i_param arrlen i xss szj ys c r.
  is_eq (first_pass_array R ri rlen i arrlen (mk_st xss szj ys c)) r /\
  is_eq ri (LENGTH szj) /\ is_eq (ri + LENGTH xss) rlen /\
  is_eq i (SUM (MAP LENGTH xss)) /\
  is_eq i_param i /\
  is_eq (i + LENGTH ys) arrlen /\
  LENGTH c = arrlen /\
  EVERY ($~ o NULL) xss /\
  SORTED (\a b. LENGTH a * 2 < LENGTH b) xss /\
  arrlen < 2 ** (rlen - 1)
  ==>
  ?szj2 c2.
  r = mk_st_ret_xs (MAP SND (FOLDL (merge_in_run R) (add_lengths xss) (find_runs R ys)))
      szj2 [] c2 rlen /\
  LENGTH szj2 + LENGTH (FOLDL (merge_in_run R) (add_lengths xss) (find_runs R ys)) = rlen /\
  LENGTH c2 = arrlen
Proof
  recInduct first_pass_array_ind
  \\ rpt gen_tac \\ disch_tac
  \\ ONCE_REWRITE_TAC [first_pass_array_def]
  \\ rw [] \\ fs []
  >- (
    fs [is_eq_def, ml_monadBaseTheory.st_ex_return_def]
    \\ rw []
    \\ Cases_on `ys` \\ fs []
    \\ simp [find_runs_def, add_lengths_simps]
    \\ irule_at Any mk_st_eq_mk_stI
    \\ simp []
  )
  \\ dxrule is_eq_bind_success_real_eqD
  \\ rpt (qpat_x_assum `is_eq _ _` (assume_tac o REWRITE_RULE [is_eq_def]))
  \\ dep_rewrite.DEP_REWRITE_TAC [find_run_array_eq]
  \\ simp [mk_st_eqI]
  \\ strip_tac
  \\ dxrule is_eq_bind_successD
  \\ strip_tac
  \\ dxrule merge_in_run_array_eq
  \\ simp [LENGTH_NOT_NULL, NULL_EQ, FST_find_run_neq_nil]
  \\ Cases_on `ys = []` \\ fs []
  \\ impl_tac
  >- (
    qspecl_then [`R`, `ys`] mp_tac find_run_length_fst
    \\ rw [FST_find_run_neq_nil]
    \\ CCONTR_TAC \\ fs []
    \\ gs []
    \\ imp_res_tac size_invariant_imp_sum_ineq
    \\ Cases_on `xss` \\ fs []
    \\ gs [NULL_EQ]
  )
  \\ strip_tac
  \\ simp [find_runs_neq_nil_def]
  \\ fs []
  \\ first_x_assum drule
  \\ simp [is_eq_def, FST_find_run_neq_nil]
  \\ disch_then (qspec_then `LENGTH (FST (find_run R ys))` mp_tac)
  \\ simp [FST_find_run_neq_nil]
  \\ impl_tac
  >- (
    simp [merge_in_run_total_length, MAP_MAP_o]
    \\ simp [GSYM MAP_MAP_o, add_lengths_simps]
    \\ simp [merge_in_run_MAP_SND_invs]
    \\ qspecl_then [`R`, `ys`] mp_tac find_run_length_fst
    \\ simp [find_run_length_eq_sub]
  )
  \\ rw []
  \\ simp [add_lengths_simps, add_lengths_MAP_SND_eq]
  \\ dep_rewrite.DEP_REWRITE_TAC [add_lengths_MAP_SND_eq]
  \\ conj_asm1_tac
  >- (
    irule MONO_EVERY
    \\ irule_at Any merge_in_run_eq_length_inv
    \\ simp [FORALL_PROD]
    \\ simp [add_lengths_def, EVERY_MAP]
    \\ fs [o_DEF]
  )
  \\ irule_at Any mk_st_eq_mk_stI
  \\ fs [add_lengths_MAP_SND_eq]
QED

Theorem merge_sizes_T_eq_sing[local]:
  !xss sz_run. ?x. merge_sizes (\_ _. T) R xss sz_run = [x]
Proof
  Induct
  \\ simp [merge_sizes_def]
QED

Theorem merge_run_sort_monadic_eq:
  arrlen = LENGTH ys /\ rlen = LENGTH szj /\ LENGTH c = arrlen /\
  ys <> [] /\ LENGTH ys < 2 ** (LENGTH szj − 1) ==>
  ?szj2 c2.
  merge_run_sort_monadic R rlen arrlen
    (mk_st [] szj ys c) =
    (M_success (), mk_st [merge_run_sort R ys] szj2 [] c2)
Proof
  rw []
  \\ qmatch_goalsub_abbrev_tac `res = (_, _)`
  \\ subgoal `?r. is_eq res r`
  >- (
    simp [is_eq_def]
  )
  \\ first_assum (simp o single o REWRITE_RULE [is_eq_def])
  \\ gs [markerTheory.Abbrev_def]
  \\ fs [merge_run_sort_monadic_def]
  \\ dxrule is_eq_bind_successD
  \\ rw []
  \\ dxrule first_pass_array_eq
  \\ simp [is_eq_def]
  \\ rw []
  \\ fs [st_ex_ignore_bind_simp, merge_every_array_eq]
  \\ dxrule is_eq_bind_successD
  \\ rw []
  \\ fs [add_lengths_simps]
  \\ qspecl_then [`ys`, `R`] mp_tac (GEN_ALL first_pass_size_invariant)
  \\ Cases_on `first_pass R ys`
  >- (
    qspecl_then [`R`, `ys`] mp_tac first_pass_perm
    \\ simp [first_pass_def]
  )
  \\ fs [first_pass_def]
  \\ rw []
  \\ dxrule merge_sizes_gen_array_eq
  \\ simp []
  \\ impl_tac
  >- (
    qspecl_then [`R`, `ys`] mp_tac first_pass_perm
    \\ rw [first_pass_def]
    \\ drule PERM_LENGTH
    \\ simp [LENGTH_FLAT]
  )
  \\ rw []
  \\ fs [is_eq_def, ml_monadBaseTheory.st_ex_return_def]
  \\ rw []
  \\ irule_at Any mk_st_eq_mk_stI
  \\ simp [merge_run_sort_def, first_pass_def, merge_sizes_def]
  \\ dep_rewrite.DEP_REWRITE_TAC [add_lengths_MAP_SND_eq]
  \\ simp [merge_empty]
  \\ pairarg_tac \\ fs []
  \\ csimp []
  \\ drule_at_then Any (irule_at Any) MONO_EVERY
  \\ simp [FORALL_PROD, merge_sizes_T_eq_sing]
QED

Theorem copy_into_array_eq:
  !xs i ys.
  i + LENGTH xs = LENGTH ys ==>
  copy_into_array i xs (mk_st [] szj ys c) =
    (M_success (), mk_st [] szj (TAKE i ys ++ xs) c)
Proof
  Induct
  \\ simp [copy_into_array_def, ml_monadBaseTheory.st_ex_return_def]
  \\ simp [st_ex_ignore_bind_simp]
  \\ rw []
  \\ fs [ADD1]
  \\ qspecl_then [`ys`, `i`] mp_tac LESS_LENGTH
  \\ rw []
  \\ fs []
  \\ simp [update_main_array_extra_LUPDATE, LUPDATE_APPEND1,
        LUPDATE_APPEND2, LUPDATE_DEF, TAKE_APPEND1, TAKE_APPEND2]
  \\ irule mk_st_eq_mk_stI
  \\ simp []
QED

Theorem copy_from_array_eq:
  !i xs ys.
  i <= LENGTH st.main_array ==>
  copy_from_array i xs st =
    (M_success (TAKE i st.main_array ++ xs), st)
Proof
  recInduct copy_from_array_ind
  \\ rw []
  \\ ONCE_REWRITE_TAC [copy_from_array_def]
  \\ rw []
  \\ simp [ml_monadBaseTheory.st_ex_return_def]
  \\ simp [fetch "-" "main_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ Cases_on `i` \\ fs []
  \\ simp [ADD1, TAKE_EL_SNOC]
QED

Theorem above_log2_is_above_ind[local]:
  ! i v n. n = 2 EXP i ==> v <= 2 ** (above_log2 i v n)
Proof
  recInduct above_log2_ind
  \\ rw [] \\ fs []
  \\ ONCE_REWRITE_TAC [above_log2_def]
  \\ rw [] \\ fs [EXP_ADD]
QED

Theorem merge_run_sort_worker_eq:
  xs <> [] ==>
  ?szj2 c2.
  merge_run_sort_worker R x xs st =
    (M_success (merge_run_sort R xs), mk_st [merge_run_sort R xs] szj2 [] c2)
Proof
  rw [merge_run_sort_worker_def]
  \\ simp [st_ex_ignore_bind_simp, return_bind_eq]
  \\ simp [fetch "-" "alloc_main_array_def", fetch "-" "alloc_sz_array_def",
        fetch "-" "alloc_copy_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [GSYM (mk_st_def |> Q.SPEC `[]` |> SIMP_RULE (srw_ss ()) [])]
  \\ simp [copy_into_array_eq]
  \\ qmatch_goalsub_abbrev_tac
        `merge_run_sort_monadic R rlen arrlen (mk_st _ szj _ c)`
  \\ qspec_then `xs` mp_tac (Q.GEN `ys` merge_run_sort_monadic_eq)
  \\ fs [markerTheory.Abbrev_def]
  \\ impl_tac
  >- (
    qspecl_then [`0`, `LENGTH xs + 1`, `1`] assume_tac above_log2_is_above_ind
    \\ fs [REWRITE_RULE [ADD1] EXP]
  )
  \\ rw []
  \\ subgoal `LENGTH xs = LENGTH (merge_run_sort R xs)`
  >- (
    irule PERM_LENGTH
    \\ irule merge_run_sort_perm
  )
  \\ simp [copy_from_array_eq, mk_st_def]
QED


