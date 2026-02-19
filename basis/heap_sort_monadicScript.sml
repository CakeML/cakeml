(*
  Using the monadic translator to translate heap sorting functions.

  Bit of an experiment, may move to ListProg if useful.
*)

Theory heap_sort_monadic
Ancestors
  heap_sort_in_fun ml_translator ml_monad_translator
Libs
  preamble ml_translatorLib ml_monad_translator_interfaceLib

(* Part 1. Translator Setup. *)

(* Set up translator to not check subtractions never underflow. *)
val _ = ml_translatorLib.use_sub_check true;

val _ = set_up_monadic_translator ();

(* The type variable used as parameter to the state type. It seems very
   important that this is used consistently. Strangely `'a` seems to work (for
   the current code) though it created problems in a previous iteration. *)
val tvar = ``: 'state``;

(* Create the data type to handle the references *)
Datatype:
  state_refs = <|
                 heap_array : ( ^tvar ) list;
                 sz_array : num list;
                |>
End

(* Data type for the exceptions. Seems to be standard. *)
Datatype:
  state_exn = Fail string | Subscript
End

val state_type = ``: ( ^tvar ) state_refs``;

val config = local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("heap_array", listSyntax.mk_list ([], tvar), ``Subscript``, ``Subscript``),
                ("sz_array", ``[] : num list``, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

val run_init_state_def = define_run state_type [] "init_state";

(* It seems important to turn this on last, or something turns it off again? *)
val _ = ParseExtras.tight_equality();

(* Part 2. Definition of heap-list sort via "suffix encoded" balanced trees.
   Every heap/tree is of power-of-two-minus-one size, with the largest element
   at the end, and two equal-sized smaller trees before it. *)

(* Positions of the left child in a suffix encoded balanced tree
   of height ht. *)
Definition sfx_heap_left_def:
  sfx_heap_left i ht = (i - (2 EXP (ht - 1)))
End

(* Insert a value into a balanced suffix heap of height ht, replacing the
   current top element which is at index i. *)
Definition insert_into_sfx_heap_def:
  insert_into_sfx_heap R i ht x = if ht <= 1
  then update_heap_array i x
  else do
    l <- return (sfx_heap_left i ht);
    r <- return (i - 1);
    lx <- heap_array_sub l;
    rx <- heap_array_sub r;
    if R lx x /\ R rx x
    then update_heap_array i x
    else if R lx rx
    then do
      update_heap_array i rx;
      insert_into_sfx_heap R r (ht - 1) x
    od
    else do
      update_heap_array i lx;
      insert_into_sfx_heap R l (ht - 1) x
    od
  od
End

(* Insert a value into a sequence of balanced suffix heaps, heights stored
   in positions [0 ..< j] of the sz_array. Replace the top elements of the
   final heap, which is at index i.  *)
Definition insert_into_sfx_heap_list_def:
  insert_into_sfx_heap_list R i j x =
  if j <= 1 then do
    ht <- sz_array_sub (j - 1);
    insert_into_sfx_heap R i ht x
  od
  else do
    ht <- sz_array_sub (j - 1);
    i2 <- return ((i + 1) - (2 EXP ht));
    t2x <- heap_array_sub i2;
    cond1 <- return (~ R t2x x);
    cond <- if cond1 /\ (1 < ht)
      then do
        l <- return (sfx_heap_left i ht);
        r <- return (i - 1);
        lx <- heap_array_sub l;
        rx <- heap_array_sub r;
        return (~ R t2x lx /\ ~ R t2x rx)
      od
      else return cond1;
    if cond
    then do
      update_heap_array i t2x;
      insert_into_sfx_heap_list R i2 (j - 1) x
    od
    else insert_into_sfx_heap R i ht x
  od
End

(* Expand the total size of a sequence of balanced suffix heaps from i to
   i + 1 total elements, starting with j total heaps. *)
Definition add_to_sfx_heaps_step1_def:
  add_to_sfx_heaps_step1 i j = do
    merge <- if j <= 1
      then return F
      else do
        n1 <- sz_array_sub (j - 1);
        n2 <- sz_array_sub (j - 2);
        return (n1 = n2);
      od;
    if merge
    then do
      n <- sz_array_sub (j - 2);
      update_sz_array (j - 2) (n + 1);
      return (j - 1);
    od
    else do
      update_sz_array j 1;
      return (j + 1);
    od
  od
End

(* Expand from i to i + 1 elements, set the new element, and preserve the heap
   invariants. *)
Definition add_to_sfx_heaps_def:
  add_to_sfx_heaps R i j x = do
    j' <- add_to_sfx_heaps_step1 i j;
    insert_into_sfx_heap_list R i j' x;
    return j'
  od
End

(* Extend a list of suffix heaps by a list of values. *)
Definition add_all_to_sfx_heaps_def:
  (add_all_to_sfx_heaps R i j [] = return (i, j)) /\
  (add_all_to_sfx_heaps R i j (x :: xs) = do
    j <- add_to_sfx_heaps R i j x;
    add_all_to_sfx_heaps R (i + 1) j xs;
  od)
End

(* Take an intact heap in the correct position and add it to the heap sequence,
   i.e. ensure its top element is the overall top element. *)
Definition reinsert_tree_def:
  reinsert_tree R i j ht =
  do
    update_sz_array j ht;
    x <- heap_array_sub (i - 1);
    upd <- if 0 < j then do
      i2 <- return (i - (2 EXP ht));
      t2x <- heap_array_sub i2;
      return (~ (R t2x x))
    od else return F;
    if upd
    then insert_into_sfx_heap_list R (i - 1) (j + 1) x
    else return ();
  od
End

(* Reduce a sequence of suffix-encoded heaps to a list. *)
Definition sfx_trees_to_list_def:
  sfx_trees_to_list R i j acc =
  if i = 0 then return acc
  else do
    ht <- sz_array_sub (j - 1);
    x <- heap_array_sub (i - 1);
    if ht <= 1 then sfx_trees_to_list R (i - 1) (j - 1) (x :: acc)
    else do
      l <- return (sfx_heap_left i ht);
      reinsert_tree R l (j - 1) (ht - 1);
      reinsert_tree R (i - 1) j (ht - 1);
      sfx_trees_to_list R (i - 1) (j + 1) (x :: acc)
    od
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

Definition sort_via_sfx_trees_worker_def:
  sort_via_sfx_trees_worker R x xs = do
      sz <- return (LENGTH xs);
      alloc_heap_array (sz + 1) x;
      sz_log <- return (above_log2 0 (sz + 1) 1);
      alloc_sz_array (sz_log + 5) 0;
      (i, j) <- add_all_to_sfx_heaps R 0 0 xs;
      sfx_trees_to_list R i j []
  od
End

Definition sort_via_sfx_trees_run_worker_def:
  sort_via_sfx_trees_run_worker R x xs =
  run_init_state (sort_via_sfx_trees_worker R x xs)
    (init_state [] [])
End

Definition sort_via_sfx_trees_def:
  sort_via_sfx_trees R xs = (case xs of [] => []
    | x :: _ => (case sort_via_sfx_trees_run_worker R x xs of
        M_success ys => ys
      | _ => [])
  )
End

(* Part 3. Proof that this monadic encoding computes the same as the pure heap
   list sort implementation. *)

Definition bs_tree_to_list_def:
  (bs_tree_to_list 0 t = []) /\
  (bs_tree_to_list (SUC ht) t =
     bs_tree_to_list ht (case t of Node _ l r => l | _ => t) ++
     bs_tree_to_list ht (case t of Node _ l r => r | _ => t) ++
     [case t of Node x l r => x]
  )
End

Theorem bs_tree_to_list_tree_rec[local]:
  (i = 0 ==> bs_tree_to_list i Empty_Tree = []) /\
  (0 < i ==> bs_tree_to_list i (Node x l r) =
    bs_tree_to_list (i - 1) l ++
    bs_tree_to_list (i - 1) r ++
    [x])
Proof
  Cases_on `i` \\ simp [bs_tree_to_list_def]
QED

Definition two_exp_min_1_def:
  two_exp_min_1 i = (2n EXP i) - 1
End

Theorem two_exp_min_1_less_rec:
  0 < i ==> two_exp_min_1 i = two_exp_min_1 (i - 1) + two_exp_min_1 (i - 1) + 1
Proof
  Cases_on `i`
  \\ fs [two_exp_min_1_def, EXP]
  \\ rw [SUB_RIGHT_ADD]
QED

Theorem two_exp_min_1_rec:
  two_exp_min_1 0 = 0 /\
  two_exp_min_1 (SUC i) = two_exp_min_1 i + two_exp_min_1 i + 1
Proof
  simp [two_exp_min_1_less_rec] \\ simp [two_exp_min_1_def]
QED

Theorem to_two_exp_min_1:
  (2n EXP i) = (two_exp_min_1 i + 1)
Proof
  rw [two_exp_min_1_def, SUB_RIGHT_ADD]
QED

Theorem sfx_heap_left_two_exp_min_1:
  sfx_heap_left n ht = n - (two_exp_min_1 (ht - 1)) - 1
Proof
  simp [sfx_heap_left_def, to_two_exp_min_1]
QED

Theorem LENGTH_bs_tree_to_list:
  ! i t. LENGTH (bs_tree_to_list i t) = two_exp_min_1 i
Proof
  Induct
  \\ simp [bs_tree_to_list_def, two_exp_min_1_rec]
QED

Definition tree_balanced_height_def:
  (tree_balanced_height i Empty_Tree = (i = 0n)) /\
  (tree_balanced_height i (Node x l r) = (
    (i > 0) /\ tree_balanced_height (i - 1) l /\
        tree_balanced_height (i - 1) r)
  )
End

Theorem tree_balanced_height_0:
  (tree_balanced_height 0 t = (t = Empty_Tree))
Proof
  Cases_on `t` \\ simp [tree_balanced_height_def]
QED

Theorem tree_balanced_height_pos:
  0 < ht ==> tree_balanced_height ht t =
    (?x l r. t = Node x l r /\ tree_balanced_height (ht - 1) l /\
        tree_balanced_height (ht - 1) r)
Proof
  Cases_on `t` \\ simp [tree_balanced_height_def]
QED

Definition bs_tree_list_to_list_def:
  bs_tree_list_to_list ts =
    FLAT (MAP (\(t, i). bs_tree_to_list i t) (REVERSE ts))
End

Theorem bs_tree_list_to_list_rec:
  bs_tree_list_to_list (t_i :: ts) = (
    bs_tree_list_to_list ts ++ bs_tree_to_list (SND t_i) (FST t_i)
  ) /\
  bs_tree_list_to_list [] = []
Proof
  simp [bs_tree_list_to_list_def]
  \\ rpt (pairarg_tac \\ fs[])
QED

Theorem st_ex_ignore_bind_simp[local]:
  st_ex_ignore_bind f g = st_ex_bind f (\_. g)
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_ignore_bind_def]
QED

Theorem monad_simps[local] = LIST_CONJ
    [fetch "-" "update_heap_array_def", fetch "-" "heap_array_sub_def",
        ml_monadBaseTheory.monad_eqs, st_ex_ignore_bind_simp,
         fetch "-" "update_sz_array_def", fetch "-" "sz_array_sub_def"]

Theorem tree_len_simps_no_less[local] = LIST_CONJ
    [tree_balanced_height_def, tree_balanced_height_0,
        two_exp_min_1_rec,
        LENGTH_bs_tree_to_list, bs_tree_to_list_def,
        bs_tree_to_list_tree_rec, bs_tree_list_to_list_rec]

Theorem tree_len_simps[local] = LIST_CONJ [tree_len_simps_no_less,
        two_exp_min_1_less_rec]

Theorem TAKE_DROP_eq_imp[local]:
  !xs i j. TAKE i (DROP j xs) = ys ==>
  i <= LENGTH ys ==>
  ys = [] \/ (?xs_pre xs_post. xs = xs_pre ++ ys ++ xs_post /\
    j = LENGTH xs_pre /\ i = LENGTH ys)
Proof
  Cases_on `ys = []` \\ simp []
  \\ rw []
  \\ qexists_tac `TAKE j xs`
  \\ qexists_tac `DROP (i + j) xs`
  \\ fs [GSYM TAKE_SUM]
  \\ fs [LENGTH_TAKE_EQ]
QED

Theorem TAKE_DROP_last_eq_imp[local]:
  TAKE l (DROP ((i + 1) - l) xs) = ys /\
  i + 1 <= LENGTH xs /\ l <= i + 1 /\
  l <= LENGTH ys /\ 0 < l ==>
  ?xs_pre xs_post. xs = xs_pre ++ ys ++ xs_post /\
    l = LENGTH ys /\ i = LENGTH xs_pre + (LENGTH ys - 1)
Proof
  rpt strip_tac
  \\ dxrule TAKE_DROP_eq_imp
  \\ Cases_on `ys = []` \\ fs []
  \\ rw []
  \\ irule_at Any EQ_REFL
  \\ simp []
QED

Theorem insert_into_sfx_heap_eq:
  ! t R i ht x st.
  TAKE (two_exp_min_1 ht) (DROP ((i + 1) - two_exp_min_1 ht) st.heap_array) =
    bs_tree_to_list ht t /\
  i + 1 <= LENGTH st.heap_array /\
  two_exp_min_1 ht <= i + 1 /\
  ht > 0 /\
  tree_balanced_height ht t ==>
  (insert_into_sfx_heap R i ht x st =
  (M_success (), st with <| heap_array := TAKE ((i + 1) - two_exp_min_1 ht) st.heap_array
    ++ bs_tree_to_list ht (insert_tree_inv R t x) ++ DROP (i + 1) st.heap_array |>))
Proof
  Induct
  \\ simp [tree_len_simps]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ rpt strip_tac
  \\ dxrule TAKE_DROP_last_eq_imp
  \\ simp [tree_len_simps]
  \\ rw [] \\ fs []
  \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
  >- (
    Cases_on `ht = 1` \\ fs [tree_len_simps]
    \\ fs [insert_tree_inv_def, tree_len_simps]
    \\ simp [monad_simps, LUPDATE_APPEND, LUPDATE_DEF]
  )
  >- (
    fs [tree_balanced_height_pos]
    \\ simp [monad_simps, tree_len_simps, sfx_heap_left_two_exp_min_1]
    \\ simp [EL_APPEND, tree_len_simps, LEFT_ADD_DISTRIB]
    \\ rpt TOP_CASE_TAC \\ simp [ml_monadBaseTheory.monad_eqs]
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ simp [insert_tree_inv_def, tree_len_simps]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
      \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
    )
  )
QED

Theorem EL_APPEND_PLUS[local]:
  EL (LENGTH xs + n) (xs ++ ys) = EL n ys
Proof
  simp [EL_APPEND]
QED

Theorem two_exp_min_1_pos[local]:
  (0 < two_exp_min_1 r) = (0 < r)
Proof
  Cases_on `r` \\ simp [two_exp_min_1_rec]
QED

Theorem insert_into_sfx_heap_list_eq:
  ! j ts R i x st.
  TAKE (LENGTH (bs_tree_list_to_list ts))
    (DROP ((i + 1) - (LENGTH (bs_tree_list_to_list ts))) st.heap_array) =
    bs_tree_list_to_list ts /\
  i + 1 <= LENGTH st.heap_array /\
  LENGTH (bs_tree_list_to_list ts) <= i + 1 /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j <= LENGTH st.sz_array ==>
  0 < j /\ EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_into_sfx_heap_list R i j x st =
  (M_success (), st with <| heap_array := TAKE ((i + 1) - LENGTH (bs_tree_list_to_list ts)) st.heap_array
    ++ bs_tree_list_to_list (insert_trees_inv R ts x) ++ DROP (i + 1) st.heap_array |>)
Proof
  Induct
  \\ simp []
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_list_def]
  \\ rpt strip_tac
  \\ dxrule TAKE_DROP_last_eq_imp
  \\ fs [tree_len_simps]
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ gs [tree_len_simps]
  \\ simp [insert_trees_inv_def]
  \\ rw []
  >- (
    Cases_on `t` \\ fs []
    \\ Cases_on `j` \\ fs []
    \\ qpat_x_assum `TAKE _ _ = _` (assume_tac o Q.AP_TERM `\x. (EL 0 x, LENGTH x)`)
    \\ gs [HD_TAKE]
    \\ simp [monad_simps]
    \\ drule_at (Pat `tree_balanced_height _ _`) insert_into_sfx_heap_eq
    \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
  )
  >- (
    gs [tree_len_simps, two_exp_min_1_pos]
    \\ first_x_assum (qspec_then `t` assume_tac)
    \\ qpat_x_assum `TAKE _ _ = _` (assume_tac o Q.AP_TERM `\x. (TAKE j x, EL j x, LENGTH x)`)
    \\ Cases_on `j` \\ fs []
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [ADD1, EL_TAKE, EL_APPEND, TAKE_TAKE]
    \\ gs [tree_balanced_height_pos]
    \\ simp [monad_simps, tree_len_simps]
    \\ full_simp_tac bool_ss [to_two_exp_min_1]
    \\ full_simp_tac bool_ss [GSYM ADD_ASSOC, GSYM APPEND_ASSOC, EL_APPEND_PLUS]
    \\ full_simp_tac bool_ss [to_two_exp_min_1]
    \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2]
    \\ TOP_CASE_TAC
    >- (
      simp [monad_simps]
      \\ simp [tree_len_simps, sfx_heap_left_two_exp_min_1, LEFT_ADD_DISTRIB]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2]
      \\ gs [tree_balanced_height_pos]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2]
      \\ rw []
      >- (
        simp [monad_simps]
        \\ simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
        \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2, LUPDATE_APPEND, LUPDATE_DEF]
      )
      >- (
        irule EQ_TRANS \\ irule_at Any insert_into_sfx_heap_eq
        \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2, LUPDATE_APPEND, LUPDATE_DEF]
        \\ irule_at Any EQ_REFL
        \\ simp [tree_len_simps]
      )
    )
    >- (
      simp [monad_simps]
      \\ simp [tree_len_simps, sfx_heap_left_two_exp_min_1, LEFT_ADD_DISTRIB]
      \\ TOP_CASE_TAC \\ fs []
      >- (
        Cases_on `r = 1` \\ fs []
        \\ fs [tree_len_simps]
        \\ simp [monad_simps]
        \\ fs [tree_len_simps]
        \\ simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
        \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2, LUPDATE_APPEND, LUPDATE_DEF]
        \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
      )
      >- (
        irule EQ_TRANS \\ irule_at Any insert_into_sfx_heap_eq
        \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2,
                EL_APPEND1, EL_APPEND2, LUPDATE_APPEND, LUPDATE_DEF]
        \\ irule_at Any EQ_REFL
        \\ simp [tree_len_simps]
      )
    )
  )
QED

Theorem MAP_SND_insert_trees_inv[local]:
  !ts. MAP SND (insert_trees_inv R ts x) = MAP SND ts
Proof
  Induct \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ rpt (TOP_CASE_TAC \\ simp [])
  \\ simp []
QED

Theorem MAP_LENGTH_insert_trees_inv[local]:
  MAP (LENGTH o (\(t, n). bs_tree_to_list n t))
            (insert_trees_inv R ts x) =
    MAP (LENGTH o (\(t, n). bs_tree_to_list n t)) ts
Proof
  qspec_then `ts` (mp_tac o Q.AP_TERM `MAP two_exp_min_1`) MAP_SND_insert_trees_inv
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY, tree_len_simps]
QED

Theorem LENGTH_insert_trees_inv[local] =
  Q.AP_TERM `LENGTH` (SPEC_ALL MAP_LENGTH_insert_trees_inv)
    |> REWRITE_RULE [LENGTH_MAP]

Theorem LENGTH_list_of_insert_trees[local]:
  LENGTH (bs_tree_list_to_list (insert_trees_inv R ts x)) =
  LENGTH (bs_tree_list_to_list ts)
Proof
  simp [bs_tree_list_to_list_def, LENGTH_FLAT, MAP_MAP_o, MAP_REVERSE]
  \\ simp [MAP_LENGTH_insert_trees_inv]
QED

Theorem TAKE_EQ_GENLIST:
  !n xs. TAKE n xs = GENLIST (\i. EL i xs) (MIN n (LENGTH xs))
Proof
  Induct \\ rw []
  \\ Cases_on `xs` \\ fs []
  \\ irule EQ_SYM
  \\ simp [llistTheory.GENLIST_EQ_CONS]
  \\ simp [o_DEF, MIN_DEF]
  \\ rw []
QED

Theorem add_to_sfx_heaps_step1_eq:
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  TAKE i st.heap_array = bs_tree_list_to_list ts /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  i + 1 < LENGTH st.heap_array /\
  j + 1 < LENGTH st.sz_array ==>
  ?st'.
  (let ts2 = add_trees_step1 ts (EL i st.heap_array);
        xs = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  add_to_sfx_heaps_step1 i j st = (M_success l2, st') /\
  TAKE (i + 1) st'.heap_array = xs /\
  TAKE l2 st'.sz_array = MAP SND (REVERSE ts2) /\
  LENGTH st'.sz_array = LENGTH st.sz_array /\
  LENGTH st'.heap_array = LENGTH st.heap_array
  )
Proof
  rw []
  \\ simp [add_to_sfx_heaps_step1_def, add_trees_step1_def]
  \\ Cases_on `ts` \\ fs []
  >- (
    simp [monad_simps]
    \\ fs [tree_len_simps]
    \\ fs [Q.SPEC `1` TAKE_EQ_GENLIST, MIN_DEF, EL_LUPDATE, HD_LUPDATE]
  )
  \\ Cases_on `t` \\ fs []
  >- (
    simp [monad_simps]
    \\ fs [tree_len_simps]
    \\ fs [Q.SPEC `2` TAKE_EQ_GENLIST, Q.SPEC `1` TAKE_EQ_GENLIST, MIN_DEF, EL_LUPDATE, HD_LUPDATE]
    \\ fs [TAKE_SUM]
  )
  \\ rpt (TOP_CASE_TAC \\ fs [])
  >- (
    simp [monad_simps]
    \\ fs [ADD1, TAKE_SUM, EL_DROP, EL_LUPDATE]
    \\ gs [Q.SPEC `2` TAKE_EQ_GENLIST, Q.SPEC `1` TAKE_EQ_GENLIST, MIN_DEF, HD_DROP, EL_DROP]
    \\ simp [monad_simps]
    \\ fs [tree_len_simps_no_less, HD_DROP, EL_LUPDATE]
    \\ irule EQ_TRANS
    \\ first_x_assum (irule_at Any)
    \\ irule listTheory.LIST_EQ
    \\ simp [EL_TAKE, EL_LUPDATE]
  )
  >- (
    simp [monad_simps]
    \\ fs [ADD1, TAKE_SUM, EL_DROP, EL_LUPDATE]
    \\ gs [Q.SPEC `2` TAKE_EQ_GENLIST, Q.SPEC `1` TAKE_EQ_GENLIST, MIN_DEF, HD_DROP, EL_DROP]
    \\ simp [monad_simps]
    \\ fs [tree_len_simps_no_less, HD_DROP, EL_LUPDATE]
    \\ qpat_x_assum `_ = MAP _ (REVERSE _)` (assume_tac o GSYM)
    \\ irule listTheory.LIST_EQ
    \\ rw [EL_TAKE, EL_APPEND]
    \\ simp [EL_LUPDATE, EL_DROP]
    \\ rw []
    \\ Cases_on `x = LENGTH t'` \\ fs []
    \\ Cases_on `x = LENGTH t' + 1` \\ fs []
  )
QED

Theorem LENGTH_add_tree_step1_facts[local]:
  0 < LENGTH (add_trees_step1 ts x) /\
  LENGTH (bs_tree_list_to_list (add_trees_step1 ts x)) =
    LENGTH (bs_tree_list_to_list ts) + 1 /\
  LENGTH (add_trees_step1 ts x) <= LENGTH ts + 1 /\
  (MAP SND (add_trees_step1 ts x) = MAP SND (add_trees_step1 ts y)) = T /\
  (LENGTH (add_trees_step1 ts x) = LENGTH (add_trees_step1 ts y)) = T
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_len_simps])
QED

Theorem inv_add_tree_step1[local]:
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (add_trees_step1 ts x)
  ) /\
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
    SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) ==>
    SORTED ($<=) (TAKE 2 (MAP SND (add_trees_step1 ts x))) /\
    SORTED ($<) (MAP SND (DROP 1 (add_trees_step1 ts x)))
  )
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_len_simps])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fs []
  \\ imp_res_tac SORTED_TL \\ fs []
  \\ Cases_on `t'` \\ fs []
QED

Theorem insert_trees_adj_with_inv[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_trees_inv R ((Node x_dc l r, n) :: ts) x =
      insert_trees_inv R ((Node y_dc l r, n) :: ts) x
Proof
  simp [insert_trees_inv_def]
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw [] \\ fs [tree_len_simps]
  \\ simp [insert_tree_inv_def]
QED

Theorem insert_trees_adj_add_trees_with_inv[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_trees_inv R (add_trees_step1 ts x_dc) x =
      insert_trees_inv R (add_trees_step1 ts y_dc) x
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_len_simps])
  \\ rw []
  \\ irule insert_trees_adj_with_inv
  \\ simp []
QED

Theorem add_to_sfx_heaps_eq:
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  TAKE i st.heap_array = bs_tree_list_to_list ts /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  i + 1 < LENGTH st.heap_array /\
  j + 1 < LENGTH st.sz_array ==>
  ?st'.
  (let ts2 = add_trees R ts x; xs = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  add_to_sfx_heaps R i j x st = (M_success l2, st') /\
  TAKE (i + 1) st'.heap_array = xs /\
  TAKE l2 st'.sz_array = MAP SND (REVERSE ts2) /\
  LENGTH st'.sz_array = LENGTH st.sz_array /\
  LENGTH st'.heap_array = LENGTH st.heap_array
  )
Proof
  simp [add_to_sfx_heaps_def, add_trees_def]
  \\ rpt strip_tac
  \\ mp_tac add_to_sfx_heaps_step1_eq
  \\ rpt strip_tac
  \\ gs [monad_simps]
  \\ irule_at Any insert_into_sfx_heap_list_eq
  \\ qexists_tac `add_trees_step1 ts (EL i st.heap_array)`
  \\ fs [tree_len_simps_no_less, LENGTH_insert_trees_inv]
  \\ fs [LENGTH_add_tree_step1_facts, inv_add_tree_step1, LENGTH_list_of_insert_trees]
  \\ rpt conj_tac
  >- (
    irule LESS_EQ_TRANS
    \\ MAP_FIRST (irule_at Any) (CONJUNCTS LENGTH_add_tree_step1_facts)
    \\ simp []
  )
  >- (
    simp [TAKE_APPEND1, LENGTH_add_tree_step1_facts, LENGTH_list_of_insert_trees,
        TAKE_LENGTH_TOO_LONG]
    \\ AP_TERM_TAC
    \\ irule insert_trees_adj_add_trees_with_inv
    \\ simp []
  )
  >- (
    simp [MAP_REVERSE, MAP_SND_insert_trees_inv]
    \\ irule (Q.prove (`a = b /\ TAKE b xs = zs/\ zs = ys ==> TAKE a xs = ys`, simp []))
    \\ first_x_assum (irule_at Any)
    \\ simp [MAP_REVERSE, LENGTH_add_tree_step1_facts]
  )
QED

Theorem LENGTH_to_list_add_trees[local]:
  LENGTH (bs_tree_list_to_list (add_trees R ts x)) =
    LENGTH (bs_tree_list_to_list ts) + 1
Proof
  simp [add_trees_def, LENGTH_list_of_insert_trees, LENGTH_add_tree_step1_facts]
QED

Theorem insert_tree_inv_balance_inv[local]:
  !t ht. tree_balanced_height ht t ==>
  tree_balanced_height ht (insert_tree_inv R t x)
Proof
  Induct \\ simp [insert_tree_inv_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_len_simps])
QED

Theorem insert_trees_inv_balance_inv[local]:
  !ts x. EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (insert_trees_inv R ts x)
Proof
  Induct \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ rpt (TOP_CASE_TAC \\ fs [tree_len_simps, insert_tree_inv_balance_inv])
QED

Theorem inv_add_trees[local]:
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (add_trees R ts x)
  ) /\
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
    SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) ==>
    SORTED ($<=) (TAKE 2 (MAP SND (add_trees R ts x))) /\
    SORTED ($<) (MAP SND (DROP 1 (add_trees R ts x)))
  )
Proof
  simp [add_trees_def, MAP_SND_insert_trees_inv, MAP_DROP]
  \\ simp [GSYM MAP_DROP, inv_add_tree_step1, insert_trees_inv_balance_inv]
QED

Theorem sum_lengths_greater_equal_exp[local]:
  ! ts n. EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED $< (MAP SND ts) /\
  ts <> [] /\ n <= SND (HD ts) /\ 1 <= n ==>
  ((2 EXP (LENGTH ts + (n - 1))) - 1) <= LENGTH (bs_tree_list_to_list ts)
Proof
  Induct \\ rw []
  \\ fs [tree_len_simps]
  \\ pairarg_tac \\ fs []
  \\ first_x_assum (qspec_then `SUC n` mp_tac)
  \\ imp_res_tac SORTED_TL
  \\ simp [tree_len_simps, EXP]
  \\ Cases_on `ts` \\ fs []
  >- (
    simp [tree_len_simps]
    \\ simp [two_exp_min_1_def, LEFT_SUB_DISTRIB]
    \\ simp [GSYM EXP, ADD1]
    \\ rw [SUB_RIGHT_ADD]
  )
  >- (
    rw []
    \\ gs [ADD1]
  )
QED

Theorem inv_trees_less_via_exp[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED $< (DROP 1 (MAP SND ts)) /\
  LENGTH (bs_tree_list_to_list ts) < 2 ** lg /\
  lg + i + 2 <= bd ==>
  LENGTH ts + i < bd
Proof
  rw []
  \\ fs [GSYM MAP_DROP]
  \\ drule_at (Pat `SORTED _ _`) sum_lengths_greater_equal_exp
  \\ simp [EVERY_DROP]
  \\ disch_then (qspec_then `1` mp_tac)
  \\ Cases_on `LENGTH ts <= 1` \\ fs []
  \\ impl_tac
  >- (
    fs [HD_DROP, EVERY_EL, UNCURRY]
    \\ first_x_assum (qspec_then `1` mp_tac)
    \\ simp []
  )
  \\ disch_tac
  \\ subgoal `2n ** (LENGTH ts - 1) < 2 ** lg`
  >- (
    drule_then irule LESS_EQ_LESS_TRANS
    \\ Cases_on `ts` \\ fs [tree_len_simps]
    \\ pairarg_tac \\ fs []
    \\ gs [tree_len_simps]
  )
  \\ fs []
QED

Theorem add_all_to_sfx_heaps_eq:
  !xs i j ts st. EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  TAKE i st.heap_array = bs_tree_list_to_list ts /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  i + LENGTH xs < LENGTH st.heap_array /\
  lg + 3 <= LENGTH st.sz_array /\
  i + LENGTH xs < 2 EXP lg ==>
  ?st'.
  (let ts2 = build_trees R ts xs; ys = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  add_all_to_sfx_heaps R i j xs st = (M_success (LENGTH ys, l2), st') /\
  TAKE (LENGTH ys) st'.heap_array = ys /\
  TAKE l2 st'.sz_array = MAP SND (REVERSE ts2) /\
  LENGTH st'.sz_array = LENGTH st.sz_array /\
  LENGTH st'.heap_array = LENGTH st.heap_array
  )
Proof
  Induct
  \\ rw [add_all_to_sfx_heaps_def, build_trees_def]
  \\ simp [monad_simps]
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac `add_to_sfx_heaps _ i j  x`
  \\ mp_tac add_to_sfx_heaps_eq
  \\ simp []
  \\ impl_tac
  >- (
    fs [markerTheory.Abbrev_def]
    \\ irule inv_trees_less_via_exp
    \\ simp [GSYM MAP_DROP]
    \\ qexists_tac `lg` \\ simp []
  )
  \\ rw []
  \\ last_x_assum (drule_at (Pat `_ = MAP _ _`))
  \\ gs [markerTheory.Abbrev_def, LENGTH_to_list_add_trees]
  \\ simp [inv_add_trees]
QED

Theorem TAKE_LUPDATE_CASES[local]:
  !xs i j. TAKE i (LUPDATE x j xs) = (if j < i then LUPDATE x j (TAKE i xs) else TAKE i xs)
Proof
  Induct \\ fs []
  \\ simp [LUPDATE_DEF]
  \\ rw []
  \\ fs []
  \\ Cases_on `i` \\ fs []
QED

Theorem reinsert_tree_eq:
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  TAKE i st.heap_array = bs_tree_list_to_list ts ++ bs_tree_to_list ht t /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts ++ bs_tree_to_list ht t) /\
  i < LENGTH st.heap_array /\
  j + 1 < LENGTH st.sz_array /\
  0 < ht /\ tree_balanced_height ht t ==>
  ?st'.
  (let ts2 = extend_trees R ts t ht; ys = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  reinsert_tree R i j ht st = (M_success (), st') /\
  TAKE (LENGTH ys) st'.heap_array = ys /\
  DROP (LENGTH ys) st'.heap_array = DROP (LENGTH ys) st.heap_array /\
  TAKE l2 st'.sz_array = MAP SND (REVERSE ts2) /\
  LENGTH st'.sz_array = LENGTH st.sz_array /\
  LENGTH st'.heap_array = LENGTH st.heap_array
  )
Proof
  rw [reinsert_tree_def]
  \\ simp [monad_simps]
  \\ qmatch_goalsub_abbrev_tac `(if C then check else return F) st_upd`
  \\ subgoal `(if C then check else return F) st_upd =
    (M_success (case (t, ts) of (Node x _ _, ((Node y _ _, _) :: _)) => ~ R y x | _ => F), st_upd)`
  >- (
    fs [markerTheory.Abbrev_def]
    \\ gs [tree_balanced_height_pos]
    \\ gs [TAKE_SUM, tree_len_simps, listTheory.APPEND_11_LENGTH,
            Q.SPECL [`two_exp_min_1 i`, `two_exp_min_1 i`] TAKE_SUM |> REWRITE_RULE [GSYM TIMES2]]
    \\ Cases_on `ts` \\ fs [monad_simps]
    \\ pairarg_tac \\ fs []
    \\ gs [tree_balanced_height_pos, tree_len_simps]
    \\ gs [TAKE_SUM, tree_len_simps, listTheory.APPEND_11_LENGTH,
            Q.SPECL [`two_exp_min_1 i`, `two_exp_min_1 i`] TAKE_SUM |> REWRITE_RULE [GSYM TIMES2]]
    \\ fs [EL_DROP, tree_len_simps, LEFT_ADD_DISTRIB, to_two_exp_min_1]
  )
  >- (
    fs []
    \\ qmatch_goalsub_abbrev_tac `(if C2 then _ else return _)`
    \\ subgoal `extend_trees R ts t ht = (if C2 then insert_trees_inv R ((t,ht) :: ts)
            (case t of Node x _ _ => x) else (t, ht) :: ts)`
    >- (
        fs [markerTheory.Abbrev_def]
        \\ simp [extend_trees_def]
        \\ gs [tree_balanced_height_pos]
        \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    )
    \\ rw []
    >- (
      irule_at Any insert_into_sfx_heap_list_eq
      \\ qexists_tac `(t, ht) :: ts`
      \\ fs [tree_len_simps, markerTheory.Abbrev_def, TAKE_SUM, EL_LUPDATE]
      \\ fs [tree_len_simps, LENGTH_list_of_insert_trees, LENGTH_insert_trees_inv,
            TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
      \\ simp [MAP_REVERSE, MAP_SND_insert_trees_inv]
      \\ simp [ADD1, TAKE_SUM, EL_LUPDATE]
      \\ simp [TAKE_LUPDATE_CASES, MAP_REVERSE]
      \\ gs [tree_balanced_height_pos]
      \\ gs [TAKE_SUM, tree_len_simps, listTheory.APPEND_11_LENGTH,
            Q.SPECL [`two_exp_min_1 i`, `two_exp_min_1 i`] TAKE_SUM |> REWRITE_RULE [GSYM TIMES2]]
      \\ fs [EL_DROP]
    )
    >- (
      simp [monad_simps]
      \\ fs [markerTheory.Abbrev_def, tree_len_simps]
      \\ simp [ADD1, TAKE_SUM, EL_LUPDATE]
      \\ simp [TAKE_LUPDATE_CASES, MAP_REVERSE]
    )
  )
QED

Theorem LENGTH_extend_trees_facts[local]:
  tree_balanced_height ht t /\ 0 < ht ==>
  LENGTH (extend_trees R ts t ht) = LENGTH ts + 1
  /\
  MAP SND (extend_trees R ts t ht) = ht :: MAP SND ts
  /\
  LENGTH (bs_tree_list_to_list (extend_trees R ts t ht)) =
  LENGTH (bs_tree_list_to_list ts) + LENGTH (bs_tree_to_list ht t) /\
  (EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) (extend_trees R ts t ht)
  )
Proof
  rw [extend_trees_def]
  \\ fs [tree_len_simps, tree_balanced_height_pos]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ simp [LENGTH_insert_trees_inv, MAP_SND_insert_trees_inv,
        LENGTH_list_of_insert_trees, tree_len_simps, insert_trees_inv_balance_inv]
QED

Theorem TAKE_2_times_two_exp[local] =
    Q.SPECL [`two_exp_min_1 i`, `two_exp_min_1 i`] TAKE_SUM |> REWRITE_RULE [GSYM TIMES2]

Theorem sfx_trees_to_list_eq:
  !i j acc ts st. EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  TAKE i st.heap_array = bs_tree_list_to_list ts /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  i < LENGTH st.heap_array /\
  lg + 4 <= LENGTH st.sz_array /\
  i < 2 EXP lg ==>
  ?st'. sfx_trees_to_list R i j acc st = (M_success (pull_trees R ts acc), st')
Proof
  Induct
  \\ ONCE_REWRITE_TAC [sfx_trees_to_list_def]
  >- (
    rw []
    \\ Cases_on `ts` \\ fs []
    \\ simp [monad_simps, pull_trees_def]
    \\ rpt (pairarg_tac \\ fs []) \\ gs [tree_len_simps, tree_balanced_height_pos]
  )
  \\ rw []
  \\ simp [monad_simps]
  \\ drule inv_trees_less_via_exp
  \\ simp [GSYM MAP_DROP]
  \\ disch_then (qspecl_then [`lg`, `2`, `LENGTH st.sz_array`] mp_tac)
  \\ rw []
  >- (
    Cases_on `ts` \\ fs [tree_len_simps]
    \\ pairarg_tac \\ fs []
    \\ gs [tree_len_simps, tree_balanced_height_pos]
    \\ gs [ADD1, TAKE_SUM]
    \\ Cases_on `n = 1` \\ fs [tree_len_simps]
    \\ simp [pull_trees_def, extend_trees_def]
    \\ fs [HD_DROP]
    \\ first_x_assum irule
    \\ simp []
    \\ Cases_on `t` \\ fs []
    \\ imp_res_tac SORTED_TL
    \\ simp []
    \\ qmatch_goalsub_abbrev_tac `TAKE 1 tl_ts`
    \\ Cases_on `tl_ts` \\ fs []
  )
  >- (
    simp [monad_simps, sfx_heap_left_two_exp_min_1]
    \\ qabbrev_tac `ts_case = ts`
    \\ Cases_on `ts_case` \\ fs [tree_len_simps_no_less]
    \\ qabbrev_tac `orig_ts = ts`
    \\ pairarg_tac \\ fs []
    \\ gs [tree_len_simps_no_less, tree_balanced_height_pos]
    \\ gs [ADD1, TAKE_SUM, tree_len_simps_no_less, APPEND_11_LENGTH, TAKE_2_times_two_exp]
    \\ qmatch_goalsub_abbrev_tac `reinsert_tree _ i_l j_l ht_l _`
    \\ qspecl_then [`i_l`, `j_l`, `ht_l`, `st`, `TL orig_ts`, `l`]
        mp_tac (Q.GENL [`i`, `j`, `ht`, `st`, `ts`, `t`] reinsert_tree_eq)
    \\ qspec_then `n` assume_tac (GEN_ALL two_exp_min_1_less_rec)
    \\ gs [markerTheory.Abbrev_def, tree_len_simps_no_less, LEFT_ADD_DISTRIB]
    \\ gs [ADD1, TAKE_SUM, tree_len_simps_no_less, APPEND_11_LENGTH, TAKE_2_times_two_exp]
    \\ strip_tac
    \\ simp []
    \\ qspecl_then [`i`, `j_l + 1`, `ht_l`, `st'`, `extend_trees R (TL orig_ts) l ht_l`, `r`]
        mp_tac (Q.GENL [`i`, `j`, `ht`, `st`, `ts`, `t`] reinsert_tree_eq)
    \\ gs [tree_len_simps_no_less, LEFT_ADD_DISTRIB, LENGTH_extend_trees_facts, MAP_REVERSE]
    \\ full_simp_tac bool_ss [ADD_ASSOC]
    \\ gs [ADD1, TAKE_SUM, tree_len_simps_no_less, APPEND_11_LENGTH, TAKE_2_times_two_exp]
    \\ fs [DROP_DROP]
    \\ strip_tac
    \\ simp [pull_trees_def]
    \\ qmatch_goalsub_abbrev_tac `pull_trees _ next_ts next_acc`
    \\ first_x_assum (qspecl_then [`next_acc`, `next_ts`] mp_tac)
    \\ fs [markerTheory.Abbrev_def, EL_DROP, tree_len_simps,
            LENGTH_extend_trees_facts, LEFT_ADD_DISTRIB]
    \\ disch_then irule
    \\ gs [ADD1, TAKE_SUM, tree_len_simps_no_less, APPEND_11_LENGTH, TAKE_2_times_two_exp]
    \\ simp [EL_DROP, MAP_DROP, LENGTH_extend_trees_facts]
    \\ gs [tree_len_simps, TAKE_SUM, EL_DROP, TAKE_2_times_two_exp]
    \\ qmatch_goalsub_abbrev_tac `SORTED _ (_ :: tl_ts)`
    \\ Cases_on `tl_ts` \\ fs []
  )
QED

Theorem above_log2_is_above_ind[local]:
  ! i v n. n = 2 EXP i ==> v <= 2 ** (above_log2 i v n)
Proof
  recInduct above_log2_ind
  \\ rw [] \\ fs []
  \\ ONCE_REWRITE_TAC [above_log2_def]
  \\ rw [] \\ fs [EXP_ADD]
QED

Theorem build_trees_facts[local]:
  !xs ts.
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  LENGTH (bs_tree_list_to_list (build_trees R ts xs)) =
    LENGTH (bs_tree_list_to_list ts) + LENGTH xs /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) (build_trees R ts xs) /\
  (SORTED $< (MAP SND (DROP 1 ts)) /\ SORTED $<= (TAKE 2 (MAP SND ts)) ==>
    SORTED $< (MAP SND (DROP 1 (build_trees R ts xs))) /\
    SORTED $<= (TAKE 2 (MAP SND (build_trees R ts xs))))
Proof
  Induct \\ simp [tree_len_simps, build_trees_def]
  \\ rw []
  \\ simp [inv_add_trees, LENGTH_to_list_add_trees]
  \\ fs [IMP_CONJ_THM, FORALL_AND_THM]
QED

Theorem sort_via_sfx_trees_eq:
  sort_via_sfx_trees R xs = another_heap_sort R xs
Proof
  simp [sort_via_sfx_trees_def, another_heap_sort_def]
  \\ TOP_CASE_TAC \\ simp []
  >- (
    simp [build_trees_def, pull_trees_def]
  )
  >- (
    simp [sort_via_sfx_trees_run_worker_def, run_init_state_def,
            ml_monadBaseTheory.run_def, sort_via_sfx_trees_worker_def]
    \\ simp [ml_monadBaseTheory.exc_case_eq, pairTheory.FST_EQ_EQUIV]
    \\ DISJ1_TAC
    \\ simp [fetch "-" "alloc_heap_array_def", fetch "-" "alloc_sz_array_def", monad_simps]
    \\ qmatch_goalsub_abbrev_tac `add_all_to_sfx_heaps _ _ _ xs st`
    \\ qspecl_then [`above_log2 0 (LENGTH xs + 1) 1`, `xs`, `0`, `0`, `[]`, `st`]
         mp_tac (add_all_to_sfx_heaps_eq |> Q.GEN `lg`)
    \\ fs [tree_len_simps, markerTheory.Abbrev_def]
    \\ qspecl_then [`0`, `LENGTH xs + 1`, `1`] assume_tac above_log2_is_above_ind
    \\ gs [LESS_LESS_EQ_TRANS]
    \\ strip_tac
    \\ simp []
    \\ irule sfx_trees_to_list_eq
    \\ simp [build_trees_facts, tree_len_simps]
    \\ irule_at Any (Q.prove (`(x + 1n) + 4 = y ==> x + 4 <= y`, simp []))
    \\ simp []
  )
QED

(* Part 4: translation of the sfx variants. *)

fun fix_state_type thm = let
    val types_in_thm = thm |> concl |> all_atoms
      |> HOLset.listItems |> map type_of
      |> map (fn t => fst (strip_fun t) @ [snd (strip_fun t)])
      |> List.concat
    val state_matching_types = types_in_thm
      |> filter (can (match_type state_type))
      |> HOLset.fromList Type.compare |> HOLset.listItems
    val substs = map (fn t => match_type t state_type) state_matching_types
  in case substs of
    [] => thm
  | [s] => INST_TYPE s thm
  | _ => failwith "fix_state_type: multiple!"
  end

Definition comp_exp_def:
  comp_exp m x 0 = x /\
  comp_exp (m : num) x (SUC i) = comp_exp m (x * m) i
End

Theorem comp_exp_eq_ind[local]:
  !i x. comp_exp m x i = x * (m EXP i)
Proof
  Induct \\ simp [comp_exp_def, EXP]
QED

Theorem use_comp_exp:
  (m EXP i) = comp_exp m 1 i
Proof
  simp [comp_exp_eq_ind]
QED

val comp_exp_v_thm = comp_exp_def |> translate;

val sfx_heap_left_v_thm = sfx_heap_left_def
  |> REWRITE_RULE [use_comp_exp] |> translate;

val insert_into_sfx_heap_v_thm = insert_into_sfx_heap_def
  |> fix_state_type |> m_translate;

val insert_into_sfx_heap_list_v_thm = insert_into_sfx_heap_list_def
  |> REWRITE_RULE [use_comp_exp]
  |> fix_state_type |> m_translate;

Theorem bind_assoc[local]:
  st_ex_bind (st_ex_bind f g) h = do
    x <- f;
    y <- g x;
    h y
  od
Proof
  rw [ml_monadBaseTheory.st_ex_bind_def, FUN_EQ_THM]
  \\ rpt (TOP_CASE_TAC \\ fs [])
QED

val add_to_sfx_heaps_v_thm = add_to_sfx_heaps_def
  |> SIMP_RULE bool_ss [add_to_sfx_heaps_step1_def, bind_assoc]
  |> fix_state_type |> m_translate;

val add_all_to_sfx_heaps_v_thm = add_all_to_sfx_heaps_def
  |> fix_state_type |> m_translate;

val reinsert_tree_v_thm = reinsert_tree_def
  |> REWRITE_RULE [use_comp_exp]
  |> fix_state_type |> m_translate;

val sfx_trees_to_list_v_thm = sfx_trees_to_list_def
  |> fix_state_type |> m_translate;

val length_v_thm = LENGTH |> translate;

val above_log2_v_thm = above_log2_def |> translate;

val sort_via_sfx_trees_worker_v_thm = sort_via_sfx_trees_worker_def
  |> fix_state_type |> m_translate;

val sort_via_sfx_trees_run_worker_v_thm = sort_via_sfx_trees_run_worker_def
  |> fix_state_type |> m_translate_run;

val sort_via_sfx_trees_v_thm = sort_via_sfx_trees_def |> translate;


(* An alternative proof of equivalence. *)

Definition monad_prop_def:
  monad_prop s m Q = (case m s of (M_success v, s') => Q v s' | _ => F)
End

Theorem monad_prop_bind:
  monad_prop s f P /\ (! x s'. P x s' ==> monad_prop s' (g x) Q) ==>
  monad_prop s (st_ex_bind f g) Q
Proof
  simp [monad_prop_def, ml_monadBaseTheory.st_ex_bind_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
QED

Theorem monad_prop_exI:
  (? x s'. m s = (M_success x, s') /\ Q x s') ==>
  monad_prop s m Q
Proof
  rw [monad_prop_def] \\ simp []
QED

Theorem monad_prop_postcond_imp:
  monad_prop s m P /\ (!x s'. P x s' ==> Q x s') ==>
  monad_prop s m Q
Proof
  rw [monad_prop_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
QED

Theorem monad_prop_return:
  Q x s ==> monad_prop s (return x) Q
Proof
  simp [ml_monadBaseTheory.st_ex_return_def, monad_prop_def]
QED

Theorem return_bind_eq:
  st_ex_bind (return v) f = f v
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def, FUN_EQ_THM]
QED

Definition array_eqs_def:
  array_eqs bg arr = (FINITE_BAG bg /\ BAG_ALL_DISTINCT (BAG_IMAGE FST bg) /\
    (!i x. BAG_IN (i, x) bg ==> i < LENGTH arr /\ EL i arr = x))
End

Theorem array_eqs_insert:
  array_eqs (BAG_INSERT (i, x) bg) arr =
    (array_eqs bg arr /\ i < LENGTH arr /\ EL i arr = x /\ (~ BAG_IN i (BAG_IMAGE FST bg)))
Proof
  simp [array_eqs_def]
  \\ EQ_TAC \\ rw [] \\ fs []
  \\ gs [BAG_ALL_DISTINCT_THM, BAG_IMAGE_FINITE_INSERT]
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ res_tac \\ fs []
QED

Theorem array_eqs_LUPDATE:
  array_eqs bg arr /\ (~ BAG_IN i (BAG_IMAGE FST bg)) ==>
  array_eqs bg (LUPDATE x i arr)
Proof
  rw [array_eqs_def]
  \\ rw [EL_LUPDATE]
  \\ gs [bagTheory.BAG_IN_FINITE_BAG_IMAGE]
  \\ metis_tac []
QED

Theorem heap_array_sub_prop:
  i < LENGTH s.heap_array ==>
  monad_prop s (heap_array_sub i)
    (\rv s'. rv = EL i s.heap_array /\ s' = s)
Proof
  rw []
  \\ irule monad_prop_exI
  \\ simp [monad_simps]
QED

Theorem update_heap_array_prop:
  i < LENGTH s.heap_array ==>
  monad_prop s (update_heap_array i x)
    (\rv s'. s' = (s with <| heap_array := LUPDATE x i s.heap_array |>))
Proof
  rw []
  \\ irule monad_prop_exI
  \\ simp [monad_simps]
QED

Definition list_mappings_from_def:
  list_mappings_from xs i = LIST_TO_BAG (MAPi (\j x. (i + j, x)) xs)
End

Theorem list_mappings_from_append:
  list_mappings_from (xs ++ ys) i =
    BAG_UNION (list_mappings_from xs i) (list_mappings_from ys (i + LENGTH xs))
Proof
  simp [list_mappings_from_def, MAPi_APPEND, LIST_TO_BAG_APPEND, o_DEF]
QED

Theorem list_mappings_from_bases:
  list_mappings_from [x] i = {|(i, x)|} /\
  list_mappings_from [] j = {||}
Proof
  simp [list_mappings_from_def]
QED

Theorem insert_into_sfx_heap_eq:

  ! t R i ht x st.
  array_eqs (BAG_UNION others
    (list_mappings_from (bs_tree_to_list ht t) ((i + 1) - two_exp_min_1 ht))) st.heap_array ==>
  i + 1 <= LENGTH st.heap_array /\
  two_exp_min_1 ht <= i + 1 /\
  ht > 0 /\
  tree_balanced_height ht t ==>
  monad_prop st (insert_into_sfx_heap R i ht x)
    (\_ st'. ?arr'. st' = st with <| heap_array := arr' |> /\
        LENGTH arr' = LENGTH st.heap_array /\
        array_eqs (BAG_UNION others
            (list_mappings_from (bs_tree_to_list ht (insert_tree_inv R t x))
                ((i + 1) - two_exp_min_1 ht))) arr')
Proof

  Induct
  \\ simp [tree_len_simps]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ rpt strip_tac
  \\ rw [] \\ fs []
  >- (
    Cases_on `ht = 1` \\ fs [tree_len_simps]
    \\ fs [insert_tree_inv_def, tree_len_simps]
    \\ fs [list_mappings_from_bases, BAG_UNION_INSERT, array_eqs_insert]
    \\ irule monad_prop_postcond_imp \\ irule_at Any update_heap_array_prop
    \\ simp []
    \\ irule_at Any EQ_REFL
    \\ simp [array_eqs_LUPDATE, EL_LUPDATE]
  )
  >- (

    fs [tree_balanced_height_pos]
    \\ simp [return_bind_eq]
    \\ fs [tree_len_simps, sfx_heap_left_two_exp_min_1]
    \\ fs [list_mappings_from_bases, list_mappings_from_append,
            BAG_UNION_INSERT, array_eqs_insert]
    \\ irule monad_prop_bind \\ irule_at Any heap_array_sub_prop \\ rw []
    \\ irule monad_prop_bind \\ irule_at Any heap_array_sub_prop
    \\ fs [list_mappings_from_bases, list_mappings_from_append,
            BAG_UNION_INSERT, array_eqs_insert]

    \\ irule monad_prop_bind \\ irule_at Any heap_array_sub_prop


    \\ simp [EL_APPEND, tree_len_simps, LEFT_ADD_DISTRIB]
    \\ rpt TOP_CASE_TAC \\ simp [ml_monadBaseTheory.monad_eqs]
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ simp [insert_tree_inv_def, tree_len_simps]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
      \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
    )
  )
QED


Theorem test:
  3 < LENGTH st.heap_array ==>
  monad_prop st
    do
      x <- heap_array_sub 1;
      y <- heap_array_sub 2;
      z <- heap_array_sub 3;
      return (x + y + z)
    od (\rv st. T)
 
Proof

  rw []
  \\ irule monad_prop_bind \\ irule_at Any heap_array_sub_prop \\ rw []
  \\ simp []
  \\ irule monad_prop_bind \\ irule_at Any heap_array_sub_prop \\ simp []

  conj_tac




Theorem broken:
  (! s i. monad_postcond s (get i) (\rv s'. rv = get_pure s i /\ s' = s))
  ==>
  ?Q. monad_postcond s' (get k) Q /\ (Conds Q)
Proof
  strip_tac
  >> pop_assum (irule_at Any)
  >> cheat
QED

Theorem works:
  (! s i. monad_postcond s (get i) (\rv s'. rv = get_pure s i /\ s' = s))
  ==>
  ?Q. monad_postcond s (get k) Q /\ (Conds Q)
Proof  
  strip_tac
  >> pop_assum (irule_at Any)
  >> cheat
QED

Theorem works:

  (! s i. monad_postcond s (get i) (\rv s'. rv = get_pure s i /\ s' = s))
  ==>
  ?Q. monad_postcond s' (get k) Q /\ (Conds Q)


  strip_tac
  >> pop_assum (irule_at Any)


Theorem

  ∃P. Q P /\ monad_prop s' (heap_array_sub 2) P

\\ irule_at Any heap_array_sub_prop

Theorem works:
  Q /\ (!x. R f x (\y. y = x))
  ==>
  R f z (\y. y = z) /\ Q
Proof
  strip_tac
  >> pop_assum (irule_at Any)
  >> simp []
QED

Theorem fails:
  Q /\ (!x. R f x (\y. y = x))
  ==>
  R f y (\z. z = y) /\ Q

Proof
  strip_tac
  >> pop_assum (qspec_then `y` (irule_at Any))

  >> simp []
QED






Definition result_prop_def:
  result_prop x Q = Q x
End

Theorem result_prop_LET:
  result_prop v P /\ (!x. P x ==> result_prop (f x) Q) ==>
  result_prop (LET f v) Q
Proof
  simp [result_prop_def]
QED

Theorem result_tup_eq_fst:
  result_prop (x, y) (\t. FST t = x)
Proof
  simp [result_prop_def]
QED

Theorem works:
  result_prop (let x = (1n, T); y = (2n, F); z = (3n, ()) in FST x + FST y + FST z) (\n. n > 5)
Proof
  irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ fs []
  \\ simp [result_prop_def]
QED

Theorem works:
  result_prop (let x = (1n, T); y = (2n, F); z = (3n, ()) in FST x + FST y + FST z) (\n. n > 5)
Proof
  irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ irule result_prop_LET \\ irule_at Any result_tup_eq_fst \\ rpt strip_tac \\ simp_tac bool_ss []
  \\ fs []
  \\ simp [result_prop_def]
QED


(* Another alternative proof, via array->fun->tree directed equivalence. *)


Definition extract_tree_def:
  extract_tree 0 i arr = Empty_Tree /\
  extract_tree (SUC ht) i arr = Node (EL (i + (two_exp_min_1 (SUC ht) - 1)) arr)
    (extract_tree ht i arr) (extract_tree ht (i + two_exp_min_1 ht) arr)
End

Theorem extract_tree_less_rec[local]:
  0 < ht ==> extract_tree ht i arr = Node (EL (i + (two_exp_min_1 ht - 1)) arr)
    (extract_tree (ht - 1) i arr) (extract_tree (ht - 1) (i + two_exp_min_1 (ht - 1)) arr)
Proof
  Cases_on `ht` \\ simp [extract_tree_def]
QED

Definition update_range_def:
  update_range i j f xs = TAKE i xs ++ GENLIST f j ++ DROP (i + j) xs
End

Theorem EL_update_range:
  k < LENGTH xs ==>
  EL k (update_range i j f xs) = (if k < i \/ k >= i + j
    then EL k xs else f (k - i))
Proof
  simp [update_range_def]
  \\ rw []
  \\ simp [EL_APPEND, LENGTH_TAKE_EQ]
  \\ rw []
  \\ fs [EL_TAKE, EL_DROP]
QED

Theorem insert_into_sfx_heap_eq:

  ! t R i ht x st.
  t = extract_tree ht (i - two_exp_min_1 ht) st.heap_array /\
  i + 1 <= LENGTH st.heap_array /\
  two_exp_min_1 ht <= i + 1 /\
  ht > 0 ==>
  ? arr upd_f.
  arr = update_range ((i + 1) - two_exp_min_1 ht) (two_exp_min_1 ht) upd_f st.heap_array /\
  insert_into_sfx_heap R i ht x st = (M_success (), st with <| heap_array := arr |>) /\
  extract_tree ht ((i + 1) - two_exp_min_1 ht) arr =
    insert_tree_inv R t x

Proof

  Induct
  \\ csimp [extract_tree_less_rec]
  \\ rw []
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ subgoal `?base. i = base + (two_exp_min_1 ht - 1)`
  >- (
    qexists_tac `(i + 1) - (two_exp_min_1 ht)`
    \\ fs [two_exp_min_1_less_rec, two_exp_min_1_pos]
  )
  \\ rw [] \\ fs []
  >- (
    Cases_on `ht = 1` \\ fs [extract_tree_def]
    \\ fs [two_exp_min_1_rec, two_exp_min_1_less_rec]
    \\ simp [monad_simps, fetch "-" "state_refs_component_equality"]
    \\ simp [insert_tree_inv_def]
    \\ simp [EL_update_range]
    (* this is somewhat annoying *)

    \\ cheat
  )

  >- (
    fs [two_exp_min_1_less_rec, sfx_heap_left_two_exp_min_1]
    \\ simp [monad_simps]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ simp [extract_tree_less_rec, two_exp_min_1_less_rec]
    \\ rw [] \\ fs []

    \\ simp [monad_simps, tree_len_simps, sfx_heap_left_two_exp_min_1]
    \\ simp [EL_APPEND, tree_len_simps, LEFT_ADD_DISTRIB]
    \\ rpt TOP_CASE_TAC \\ simp [ml_monadBaseTheory.monad_eqs]
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ simp [insert_tree_inv_def, tree_len_simps]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
      \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
    )
    >- (
      simp [tree_len_simps, LUPDATE_APPEND, LUPDATE_DEF]
      \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
      \\ simp [tree_len_simps]
      \\ simp [tree_len_simps, TAKE_APPEND2, TAKE_APPEND1, DROP_APPEND1, DROP_APPEND2]
    )
  )
QED


