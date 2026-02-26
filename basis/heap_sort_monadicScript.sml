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
  add_to_sfx_heaps_step1 j = do
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
    j' <- add_to_sfx_heaps_step1 j;
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

Theorem LAST_bs_tree_to_list[local]:
  0 < ht ==> LAST (bs_tree_to_list ht t) = (
    case t of Node x _ _ => x)
Proof
  Cases_on `ht` \\ simp [bs_tree_to_list_def, two_exp_min_1_rec]
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

Theorem tree_balanced_height_eq_0[local]:
  ht = 0 ==> (tree_balanced_height ht t = (t = Empty_Tree))
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
  \\ REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [sfx_trees_to_list_def]
  >- (
    rw []
    \\ Cases_on `ts` \\ fs []
    \\ simp [monad_simps, pull_trees_def]
    \\ rpt (pairarg_tac \\ fs []) \\ gs [tree_len_simps, tree_balanced_height_pos]
  )
  \\ rw []

  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs [bs_tree_list_to_list_rec]
  \\ simp [sz_array_sub_bind_eq, ADD1]
  \\ gs [tree_balanced_height_pos, bs_tree_to_list_tree_rec, ADD1]
  \\ gs [

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




(* Yet another attempt at equivalence. *)


Definition mk_st_def:
  mk_st hps szs =
    (<|
        sz_array := REVERSE (FST szs) ++ SND szs;
        heap_array := bs_tree_list_to_list (FST hps) ++ SND hps
    |> : 'a state_refs)
End

Definition encode_heap_list_def:
  encode_heap_list heaps szs =
    (<|
        sz_array := REVERSE szs;
        heap_array := bs_tree_list_to_list heaps;
    |> : 'a state_refs)
End

Definition is_last_ix_def:
  is_last_ix szs i = (SUM (MAP two_exp_min_1 szs) = i + 1)
End

Theorem is_last_ix_eq_min_1:
  is_last_ix szs i ==> i = SUM (MAP two_exp_min_1 szs) - 1
Proof
  simp [is_last_ix_def]
QED

Theorem encode_heap_list_ix_EL: 
  !k. is_last_ix (DROP k hps) i /\ EL k hps = (hp, n) /\ 0 < n ==>
  EL i (encode_heap_list hps ovs oss).heap_array =
    (case hp of Node x _ _ => x) /\
  i < LENGTH (encode_heap_list hps ovs oss).heap_array
Proof
  gen_tac \\ disch_tac
  \\ Cases_on `~ (k < LENGTH hps)`
  >- (
    fs [is_last_ix_def, DROP_LENGTH_TOO_LONG, bs_tree_list_to_list_rec]
  )
  \\ fs []
  \\ dxrule LESS_LENGTH
  \\ strip_tac
  \\ fs [DROP_APPEND1, DROP_LENGTH_TOO_LONG, EL_APPEND]
  \\ fs [is_last_ix_def, encode_heap_list_def, bs_tree_list_to_list_def]
  \\ subgoal `i = LENGTH (bs_tree_list_to_list ys2) + (LENGTH (bs_tree_to_list n hp) - 1)`
  \\ Cases_on `n` \\ fs []
  \\ fs [REVERSE_APPEND, bs_tree_to_list_def, bs_tree_list_to_list_def]
  \\ simp [EL_APPEND]
QED

Theorem LENGTH_bs_tree_list_to_list_eq_SUM[local]:
  LENGTH (bs_tree_list_to_list ts) = SUM (MAP two_exp_min_1 (MAP SND ts))
Proof
  simp [bs_tree_list_to_list_def, LENGTH_FLAT, MAP_MAP_o, o_DEF]
  \\ simp [UNCURRY, LENGTH_bs_tree_to_list, MAP_REVERSE, SUM_REVERSE]
QED

Theorem update_heap_array_bind:

  0 < n /\ is_last_ix (n :: MAP SND hps) i ==>
  f () (mk_st (((case hp of Node _ l r => Node x l r), n) :: hps, oths) szs) = rhs ==>
  st_ex_bind (update_heap_array i x) f (mk_st ((hp, n) :: hps, oths) szs) = rhs

Proof

  rw []
  \\ simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ imp_res_tac is_last_ix_eq_min_1
  \\ TOP_CASE_TAC
  \\ fs [ml_monadBaseTheory.monad_eqs, fetch "-" "update_heap_array_def"]
  \\ fs [mk_st_def, LENGTH_bs_tree_list_to_list_eq_SUM, is_last_ix_def]
  \\ simp [bs_tree_list_to_list_rec, LUPDATE_APPEND, LENGTH_bs_tree_list_to_list_eq_SUM]
  \\ Cases_on `n` \\ fs [two_exp_min_1_rec]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ Cases_on `hp` \\ simp [bs_tree_to_list_def]

  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC

  \\ simp [bs_tree_list_to_list_rec, bs_tree_to_list_def]
  \\ simp [LUPDATE_APPEND, LENGTH_bs_tree_list_to_list_eq_SUM, LENGTH_bs_tree_to_list]
  \\ fs [two_exp_min_1_rec]

print_match [] ``LENGTH (bs_tree_list_to_list _)``

  rw []
  \\ drule encode_heap_list_ix_EL
  \\ simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ disch_then (qspecl_then [`ovs`, `oss`] assume_tac)
  \\ Cases_on `heap_array_sub i (encode_heap_list hps ovs oss)`
  \\ fs [ml_monadBaseTheory.monad_eqs, fetch "-" "heap_array_sub_def"]
  \\ fs []
QED



Theorem heap_array_sub_encode_bind:
  ! k.
  is_last_ix base_hps i /\ hps = base_hps ++ [(hp, n)] ++ oths /\ 0 < n /\
  f (case hp of (Node x _ _) => x) (encode_heap_list hps szs) = rhs ==>

  st_ex_bind (heap_array_sub i) f (mk_st ( hps szs) = rhs

Proof

  rw []
  \\ drule encode_heap_list_ix_EL
  \\ simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ disch_then (qspecl_then [`ovs`, `oss`] assume_tac)
  \\ Cases_on `heap_array_sub i (encode_heap_list hps ovs oss)`
  \\ fs [ml_monadBaseTheory.monad_eqs, fetch "-" "heap_array_sub_def"]
  \\ fs []
QED

Theorem bind_return_eq:
  st_ex_bind m return = m
Proof
  cheat
QED

Theorem update_heap_array_bind:
  !f. 0 < n /\ is_last_ix (n :: MAP SND hps) i ==>
  f () (mk_st (((case hp of Node _ l r => Node x l r), n) :: hps, oths) szs) = rhs ==>
  st_ex_bind (update_heap_array i x) f (mk_st ((hp, n) :: hps, oths) szs) = rhs
Proof
  cheat
QED

Theorem update_heap_array_mk_st_eq:
  is_last_ix (n :: MAP SND hps) i ==>
  update_heap_array i x (mk_st ((Node x_dc l r, n) :: hps, oths) szs) =
        (M_success (), mk_st ((Node x l r, n) :: hps, oths) szs)
Proof
  cheat
QED

Theorem bind_success_eqI:
  m st = (M_success v, st2) /\ f v st2 = rhs ==>
  st_ex_bind m f st = rhs
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem bind_success_rdonly_eqI =
  Q.INST [`st2` |-> `st`] bind_success_eqI

Theorem heap_array_sub_left:
  is_last_ix (ht :: MAP SND hps) i /\ 1 < ht ==>
  st_ex_bind (heap_array_sub (sfx_heap_left i ht)) f
    (mk_st ((Node x (Node lx ll lr) r, ht) :: hps, oths) szs) =
  f lx (mk_st ((Node x (Node lx ll lr) r, ht) :: hps, oths) szs)
Proof
  cheat
QED

Theorem heap_array_sub_right:
  is_last_ix (ht :: MAP SND hps) i /\ 1 < ht ==>
  st_ex_bind (heap_array_sub (i - 1)) f
    (mk_st ((Node x l (Node rx rl rr), ht) :: hps, oths) szs) =
  f rx (mk_st ((Node x l (Node rx rl rr), ht) :: hps, oths) szs)
Proof
  cheat
QED

Theorem heap_array_sub_curr:
  is_last_ix (ht :: MAP SND hps) i /\ 0 < ht ==>
  st_ex_bind (heap_array_sub i) f
    (mk_st ((Node x l r, ht) :: hps, oths) szs) =
  f x (mk_st ((Node x l r, ht) :: hps, oths) szs)
Proof
  cheat
QED

Theorem heap_array_sub_prev:
  is_last_ix (ht :: MAP SND hps) i /\ 0 < LENGTH hps /\
    EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) hps ==>
  st_ex_bind (heap_array_sub (i - two_exp_min_1 ht)) f
    (mk_st ((t, ht) :: hps, oths) szs) =
  f (case hps of (Node x _ _, _) :: _ => x) (mk_st ((t, ht) :: hps, oths) szs)
Proof
  cheat
QED

Theorem mk_st_node_split_r:
  0 < ht ==>
  mk_st ((Node x l r, ht) :: hps, oths) szs =
  mk_st ((r, ht - 1) :: (l, ht - 1) :: hps, x :: oths) szs
Proof
  cheat
QED

Theorem mk_st_node_split_l:
  0 < ht ==>
  mk_st ((Node x l r, ht) :: hps, oths) szs =
  mk_st ((l, ht - 1) :: hps, bs_tree_to_list (ht - 1) r ++ x :: oths) szs
Proof
  cheat
QED

Theorem mk_st_move_others:
  mk_st ((t, ht) :: hps, oths) szs_pair =
  mk_st (hps, bs_tree_to_list ht t ++ oths) szs_pair /\
  mk_st hps_pair (n :: szs, sz_oths) =
  mk_st hps_pair (szs, n :: sz_oths)
Proof
  cheat
QED

Theorem is_last_ix_imps:
  is_last_ix (ht :: hts) i ==>
  (1 < ht ==> is_last_ix (ht - 1 :: hts) (sfx_heap_left i ht)) /\
  (1 < ht ==> is_last_ix (ht - 1 :: ht - 1 :: hts) (i - 1)) /\
  (0 < ht /\ 0 < LENGTH hts ==> is_last_ix hts (i - two_exp_min_1 ht))
Proof
  cheat
QED

Theorem sz_array_sub_bind_eq:
  i < LENGTH szs ==>
  st_ex_bind (sz_array_sub i) f (mk_st hps (szs, oths)) =
  f (EL (LENGTH szs - (i + 1)) szs) (mk_st hps (szs, oths))
Proof
  cheat
QED

Theorem update_sz_array_eq:
  i < LENGTH szs ==>
  update_sz_array i x (mk_st hps (szs, oths)) =
    (M_success (), mk_st hps (LUPDATE x (LENGTH szs - (i + 1)) szs, oths))
Proof
  cheat
QED

Theorem insert_into_sfx_heap_eq:
  ! ht hps oths t R i x st.
  is_last_ix (ht :: MAP SND hps) i /\ ht > 0 /\
  tree_balanced_height ht t ==>
  insert_into_sfx_heap R i ht x (mk_st ((t, ht) :: hps, oths) szs) =
    (M_success (), (mk_st ((insert_tree_inv R t x, ht) :: hps, oths) szs))
Proof
  Induct
  \\ simp [ADD1]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ simp [tree_balanced_height_pos]
  \\ rw []
  >- (
    Cases_on `ht` \\ fs [tree_balanced_height_0]
    \\ simp [insert_tree_inv_def, update_heap_array_mk_st_eq]
  )
  >- (
    simp [return_bind_eq]
    \\ gs [tree_balanced_height_pos]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ drule_then assume_tac is_last_ix_imps
    \\ gs []
    \\ simp [heap_array_sub_left, heap_array_sub_right]
    \\ rpt TOP_CASE_TAC
    \\ simp [update_heap_array_mk_st_eq, st_ex_ignore_bind_simp]
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ irule bind_success_eqI
      \\ simp [update_heap_array_mk_st_eq]
      \\ simp [Once mk_st_node_split_r]
      \\ simp [mk_st_node_split_r]
    )
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ irule bind_success_eqI
      \\ simp [update_heap_array_mk_st_eq]
      \\ simp [Once mk_st_node_split_l]
      \\ simp [mk_st_node_split_l]
    )
  )
QED

Theorem insert_into_sfx_heap_list_eq:
  ! j ts R i x oths szs.
  j = LENGTH ts /\
  is_last_ix (MAP SND ts) i /\
  0 < j /\ EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_into_sfx_heap_list R i j x (mk_st (ts, oths) (MAP SND ts, szs)) =
    (M_success (), mk_st (insert_trees_inv R ts x, oths) (MAP SND ts, szs))
Proof
  Induct
  \\ simp []
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_list_def]
  \\ rpt strip_tac
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ gs [ADD1, TAKE_SUM]
  \\ simp [insert_trees_inv_def]
  \\ rw []
  >- (
    Cases_on `t` \\ fs []
    \\ simp [sz_array_sub_bind_eq, return_bind_eq]
    \\ simp [insert_into_sfx_heap_eq]
  )
  \\ simp [sz_array_sub_bind_eq, return_bind_eq]
  \\ simp [ADD1]
  \\ simp [to_two_exp_min_1, heap_array_sub_prev]
  \\ irule bind_success_rdonly_eqI
  \\ qexists_tac `case t of ((Node t2x _ _, _) :: _) =>
        ~ R t2x x /\ ~ (case q of Node _ (Node lx _ _) _ => R t2x lx | _ => F) /\
        ~ (case q of Node _ _ (Node rx _ _) => R t2x rx | _ => F) | _ => F`
  \\ conj_tac
  >- (
    Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ rw []
    >- (
      gs [tree_balanced_height_pos]
      \\ simp [heap_array_sub_left, heap_array_sub_right]
      \\ simp [ml_monadBaseTheory.monad_eqs]
    )
    >- (
      simp [ml_monadBaseTheory.monad_eqs]
      \\ gs [tree_balanced_height_pos, tree_balanced_height_eq_0]
    )
  )
  \\ simp []
  \\ TOP_CASE_TAC
  >- (
    gs [tree_balanced_height_pos]
    \\ simp [st_ex_ignore_bind_simp]
    \\ irule bind_success_eqI
    \\ simp [update_heap_array_mk_st_eq]
    \\ simp [mk_st_move_others]
    \\ drule_then assume_tac is_last_ix_imps
    \\ gs []
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [tree_balanced_height_pos]
    \\ simp [insert_trees_inv_def, mk_st_move_others]
  )
  >- (
    simp [insert_into_sfx_heap_eq]
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [tree_balanced_height_pos]
  )
QED

Theorem add_to_sfx_heaps_step1_eq:
  j = LENGTH ts /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < LENGTH oth_szs ==>
  ? oth_szs2.
  let ts2 = add_trees_step1 ts x in
  add_to_sfx_heaps_step1 j (mk_st (ts, x :: oths) (MAP SND ts, oth_szs)) =
        (M_success (LENGTH ts2), mk_st (ts2, oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  rw []
  \\ simp [add_to_sfx_heaps_step1_def, add_trees_step1_def]
  \\ irule_at Any bind_success_rdonly_eqI
  \\ qexists_tac `case ts of (_, n1) :: (_, n2) :: _ => n1 = n2 | _ => F`
  \\ simp [GSYM PULL_EXISTS]
  \\ conj_tac
  >- (
    every_case_tac \\ fs []
    \\ simp [sz_array_sub_bind_eq, ADD1]
    \\ simp [ml_monadBaseTheory.monad_eqs]
  )
  \\ TOP_CASE_TAC
  >- (
    every_case_tac \\ fs []
    \\ simp [sz_array_sub_bind_eq, ADD1, st_ex_ignore_bind_simp]
    \\ irule_at Any bind_success_eqI
    \\ simp [update_sz_array_eq, ml_monadBaseTheory.monad_eqs]
    \\ simp [ADD1, LUPDATE_DEF]
    \\ simp [mk_st_node_split_r, mk_st_move_others]
    \\ irule_at Any EQ_REFL
    \\ simp []
  )
  >- (
    simp [st_ex_ignore_bind_simp]
    \\ irule_at Any bind_success_eqI
    \\ Cases_on `oth_szs` \\ fs []
    \\ simp [GSYM mk_st_move_others]
    \\ simp [update_sz_array_eq, ml_monadBaseTheory.monad_eqs]
    \\ simp [ADD1, LUPDATE_DEF]
    \\ every_case_tac \\ fs []
    \\ simp [mk_st_move_others, bs_tree_to_list_tree_rec]
    \\ REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
    \\ irule_at Any EQ_REFL
    \\ simp []
  )
QED

Theorem add_to_sfx_heaps_eq:
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < LENGTH oth_szs /\ 0 < LENGTH oths ==>
  let ts2 = add_trees R ts x in
  ? oth_szs2.
  add_to_sfx_heaps R i j x (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
    (M_success (LENGTH ts2), mk_st (ts2, TL oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  rpt strip_tac
  \\ qspecl_then [`HD oths`, `TL oths`] mp_tac (Q.GENL [`x`, `oths`] add_to_sfx_heaps_step1_eq)
  \\ Cases_on `oths` \\ fs []
  \\ rw []
  \\ simp [add_to_sfx_heaps_def, add_trees_def]
  \\ irule_at Any bind_success_eqI
  \\ simp [st_ex_ignore_bind_simp]
  \\ irule_at Any bind_success_eqI
  \\ simp [ml_monadBaseTheory.monad_eqs, LENGTH_insert_trees_inv]
  \\ dep_rewrite.DEP_REWRITE_TAC [insert_into_sfx_heap_list_eq]
  \\ simp [LENGTH_add_tree_step1_facts, inv_add_tree_step1, is_last_ix_def,
        GSYM LENGTH_bs_tree_list_to_list_eq_SUM]
  \\ simp [MAP_SND_insert_trees_inv]
  \\ irule_at Any (Q.prove (`a = b /\ c = d ==> mk_st a c = mk_st b d`, simp []))
  \\ simp []
  \\ metis_tac [insert_trees_adj_add_trees_with_inv, LENGTH_add_tree_step1_facts]
QED

Theorem add_all_to_sfx_heaps_eq:
  !xs i j ts oths oth_szs.
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  lg + 3 <= LENGTH ts + LENGTH oth_szs /\
  i + LENGTH xs < 2 EXP lg ==>
  LENGTH xs <= LENGTH oths ==>
  let ts2 = build_trees R ts xs in
  ? oth_szs2.
  add_all_to_sfx_heaps R i j xs (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
        (M_success (LENGTH (bs_tree_list_to_list ts2), LENGTH ts2),
            mk_st (ts2, DROP (LENGTH xs) oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  Induct
  \\ simp [add_all_to_sfx_heaps_def, build_trees_def]
  >- (
    simp [ml_monadBaseTheory.monad_eqs]
    \\ metis_tac []
  )
  \\ rpt strip_tac
  \\ irule_at Any bind_success_eqI
  \\ qmatch_goalsub_abbrev_tac `add_to_sfx_heaps R i j x`
  \\ mp_tac add_to_sfx_heaps_eq
  \\ fs [markerTheory.Abbrev_def]
  \\ impl_keep_tac
  >- (
    (* exponential argument that there is space in szs array *)
    drule inv_trees_less_via_exp
    \\ disch_then (qspecl_then [`lg`, `1`] mp_tac)
    \\ simp [GSYM MAP_DROP]
    \\ disch_then dxrule
    \\ simp []
  )
  \\ rw [] \\ simp []
  \\ qmatch_goalsub_abbrev_tac `mk_st (ts2, _)`
  \\ first_x_assum (qspecl_then [`ts2`, `TL oths`, `oth_szs2`] mp_tac)
  \\ fs [markerTheory.Abbrev_def]
  \\ simp [LENGTH_to_list_add_trees, inv_add_trees]
  \\ rw [] \\ simp []
  \\ Cases_on `oths` \\ fs []
  \\ irule_at Any EQ_REFL
  \\ simp []
QED

Theorem reinsert_tree_eq:
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ((t, ht) :: ts)) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  0 < ht /\ tree_balanced_height ht t ==>
  reinsert_tree R i j ht (mk_st ((t, ht) :: ts, oths) (dc :: MAP SND ts, oth_szs)) =
    (let ts2 = extend_trees R ts t ht in
        (M_success (), mk_st (ts2, oths) (MAP SND ts2, oth_szs)))
Proof
  simp [reinsert_tree_def, extend_trees_def]
  \\ rw []
  \\ gs [tree_balanced_height_pos]
  \\ qmatch_goalsub_abbrev_tac `mk_st (COND tree_cond _ _, _)`
  \\ simp [st_ex_ignore_bind_simp]
  \\ irule_at Any bind_success_eqI
  \\ simp [update_sz_array_eq]
  \\ dep_rewrite.DEP_REWRITE_TAC [heap_array_sub_curr]
  \\ conj_asm1_tac
  >- (
    fs [markerTheory.Abbrev_def]
    \\ simp [is_last_ix_def, LENGTH_bs_tree_list_to_list_eq_SUM]
    \\ fs [two_exp_min_1_less_rec]
  )
  \\ irule_at Any bind_success_rdonly_eqI
  \\ qexists_tac `~ tree_cond`
  \\ conj_tac
  >- (
    rw []
    \\ simp [return_bind_eq, to_two_exp_min_1]
    \\ simp [heap_array_sub_prev |> Q.GEN `i` |> Q.SPEC `i - 1`
        |> SIMP_RULE (srw_ss ()) [GSYM SUB_PLUS, ADD_COMM]]
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ every_case_tac \\ fs [markerTheory.Abbrev_def]
    \\ gs [tree_balanced_height_pos]
  )
  \\ rw []
  >- (
    simp [ADD1, LUPDATE_DEF]
    \\ qmatch_goalsub_abbrev_tac `mk_st (tt :: ts, _)`
    \\ qspecl_then [`j`, `tt :: ts`] (mp_tac o Q.GEN `j`) insert_into_sfx_heap_list_eq
    \\ fs [markerTheory.Abbrev_def, tree_balanced_height_def, ADD1]
    \\ simp [MAP_SND_insert_trees_inv]
  )
  \\ simp [ml_monadBaseTheory.monad_eqs]
  \\ simp [ADD1, LUPDATE_DEF]
QED

Theorem sfx_trees_to_list_eq:
  !i j acc ts oths oth_szs.
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  LENGTH ts = j /\ LENGTH (bs_tree_list_to_list ts) = i /\
  lg + 4 <= LENGTH ts + LENGTH oth_szs /\
  i < 2 EXP lg ==>
  ?st'. sfx_trees_to_list R i j acc (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
    (M_success (pull_trees R ts acc), st')
Proof
  Induct
  \\ REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [sfx_trees_to_list_def]
  >- (
    rw []
    \\ Cases_on `ts` \\ fs []
    \\ simp [monad_simps, pull_trees_def]
    \\ rpt (pairarg_tac \\ fs []) \\ gs [tree_len_simps, tree_balanced_height_pos]
  )
  \\ rw []
  \\ subgoal `is_last_ix (MAP SND ts) i`
  >- (
    fs [is_last_ix_def, ADD1]
    \\ fs [LENGTH_bs_tree_list_to_list_eq_SUM]
  )
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs [bs_tree_list_to_list_rec]
  \\ simp [sz_array_sub_bind_eq, ADD1]
  \\ gs [tree_balanced_height_pos, bs_tree_to_list_tree_rec, ADD1]
  \\ simp [heap_array_sub_curr]
(*
  \\ drule inv_trees_less_via_exp
  \\ simp [GSYM MAP_DROP]
  \\ disch_then (qspecl_then [`lg`, `2`] mp_tac)
*)
  \\ subgoal `SORTED $<= (TAKE 2 (MAP SND t)) ∧ SORTED $< (DROP 1 (MAP SND t))`
  >- (
    Cases_on `TL t` \\ Cases_on `t` \\ fs []
  )
  \\ rw []
  >- (
    gs [tree_balanced_height_eq_0]
    \\ simp [mk_st_move_others, bs_tree_to_list_tree_rec, pull_trees_def,
            extend_trees_def]
    \\ first_x_assum irule
    \\ fs [bs_tree_to_list_tree_rec, MAP_DROP]
  )
  >- (
    simp [st_ex_ignore_bind_simp, return_bind_eq]
    \\ simp [mk_st_node_split_l]
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ dep_rewrite.DEP_REWRITE_TAC [reinsert_tree_eq]
    \\ qpat_x_assum `_ = _ + 1n` (assume_tac o GSYM)
    \\ simp [MAP_DROP, sfx_heap_left_def, bs_tree_list_to_list_rec,
            LENGTH_bs_tree_to_list, to_two_exp_min_1]
    \\ Cases_on `oth_szs`
    >- (
      (* log/exp proof there is still a spare sz slot *)
      gs []
      \\ drule inv_trees_less_via_exp
      \\ disch_then (qspecl_then [`lg`, `2`] mp_tac)
      \\ simp []
      \\ disch_then drule
      \\ simp []
    )
    \\ simp [GSYM mk_st_move_others]
    \\ dep_rewrite.DEP_REWRITE_TAC [reinsert_tree_eq]
    \\ simp [LENGTH_extend_trees_facts, MAP_DROP, bs_tree_list_to_list_rec]
    \\ conj_tac
    >- (
      Cases_on `t` \\ fs []
    )
    \\ qmatch_goalsub_abbrev_tac `sfx_trees_to_list _ _ _ acc2 (mk_st (ts, oths2) (_, oth_szs2))`
    \\ first_x_assum (qspecl_then [`acc2`, `ts`, `oths2`, `oth_szs2`] mp_tac)
    \\ fs [markerTheory.Abbrev_def, LENGTH_extend_trees_facts, ADD1, MAP_DROP]
    \\ impl_tac
    >- (
      Cases_on `t` \\ fs []
    )
    \\ rw [] \\ simp []
    \\ simp [pull_trees_def]
  )
QED

Theorem sort_via_sfx_trees_eq:
  sort_via_sfx_trees R xs = another_heap_sort R xs
Proof
  simp [sort_via_sfx_trees_def, another_heap_sort_def]
  \\ Cases_on `xs`
  >- (
    simp [build_trees_def, pull_trees_def]
  )
  \\ simp [sort_via_sfx_trees_run_worker_def]
  \\ simp [run_init_state_def, ml_monadBaseTheory.run_def, sort_via_sfx_trees_worker_def]
  \\ simp [ml_monadBaseTheory.exc_case_eq, pairTheory.FST_EQ_EQUIV]
  \\ DISJ1_TAC
  \\ simp [fetch "-" "alloc_heap_array_def", fetch "-" "alloc_sz_array_def", monad_simps]
  \\ qmatch_goalsub_abbrev_tac `add_all_to_sfx_heaps _ _ _ xs st`
  \\ qspecl_then [`above_log2 0 (LENGTH xs + 1) 1`, `xs`,
            `0`, `0`, `[]`, `st.heap_array`, `st.sz_array`]
        mp_tac (add_all_to_sfx_heaps_eq |> Q.GEN `lg`)
  \\ qspecl_then [`0`, `LENGTH xs + 1`, `1`] assume_tac above_log2_is_above_ind
  \\ gs [markerTheory.Abbrev_def, bs_tree_list_to_list_rec, ADD1]
  \\ simp [mk_st_def |> Q.SPEC `([], x)`, bs_tree_list_to_list_rec]
  \\ rw [] \\ simp []
  \\ dep_rewrite.DEP_REWRITE_TAC [sfx_trees_to_list_eq |> Q.GEN `lg`]
  \\ simp [build_trees_facts]
  \\ simp [ADD1, bs_tree_list_to_list_rec]
  \\ drule_at_then Any (irule_at Any) LESS_LESS_EQ_TRANS
  \\ simp []
QED

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

Definition array_chunks_end_in_def:
  array_chunks_end_in xs arr = (
    EVERY (\(i, zs). LENGTH zs - 1 <= i) xs /\
    let ys = FLAT (MAP (\(i, zs).
        MAPi (\j z. ((i - (LENGTH zs - 1)) + j, z)) zs) xs) in
    ALL_DISTINCT (MAP FST ys) /\
    EVERY (\(j, z). j < LENGTH arr /\ EL j arr = z) ys
  )
End

Theorem array_chunks_end_in_append[local]:
  array_chunks_end_in (xs ++ ys) = array_chunks_end_in (ys ++ xs)
Proof
  simp [array_chunks_end_in_def, FUN_EQ_THM, ALL_DISTINCT_APPEND', DISJOINT_SYM]
  \\ rw [] \\ EQ_TAC \\ rw [] \\ simp []
QED

Theorem array_chunks_end_in_rotate[local]:
  array_chunks_end_in (x :: xs) = array_chunks_end_in (xs ++ [x])
Proof
  simp [Once array_chunks_end_in_append]
QED

Theorem array_chunks_end_in_null[local]:
  array_chunks_end_in ((i, []) :: xs) = array_chunks_end_in xs
Proof
  simp [array_chunks_end_in_def, FUN_EQ_THM]
QED

Theorem list_to_bag_flat_eq:
  !xs ys. LIST_TO_BAG xs = LIST_TO_BAG ys ==>
  LIST_TO_BAG (FLAT xs) = LIST_TO_BAG (FLAT ys)
Proof
  Induct
  >- (
    Cases \\ simp []
  )
  >- (
    rw []
    \\ first_assum (mp_tac o Q.AP_TERM `BAG_IN h`)
    \\ rw [IN_LIST_TO_BAG]
    \\ fs [MEM_SPLIT]
    \\ fs [LIST_TO_BAG_APPEND]
    \\ fsrw_tac [bagSimps.BAG_AC_ss] [BAG_INSERT_UNION]
    \\ simp_tac bool_ss [GSYM LIST_TO_BAG_APPEND, GSYM FLAT_APPEND]
    \\ first_x_assum irule
    \\ simp [LIST_TO_BAG_APPEND]
  )
QED

Theorem array_chunks_end_in_bag_eq:
  ! xs ys zs. LIST_TO_BAG xs = LIST_TO_BAG ys ==>
  array_chunks_end_in xs = array_chunks_end_in ys
Proof
  rw []
  \\ simp [array_chunks_end_in_def, FUN_EQ_THM]
  \\ simp [EVERY_FLAT]
  \\ rw [GSYM EVERY_LIST_TO_BAG, LIST_TO_BAG_MAP]
  \\ rpt (irule AND_CONG \\ rw [])
  \\ simp [GSYM containerTheory.LIST_TO_BAG_DISTINCT]
  \\ simp [LIST_TO_BAG_MAP]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ irule list_to_bag_flat_eq
  \\ simp [LIST_TO_BAG_MAP]
QED

Theorem array_chunks_end_in_chunk_append[local]:
  array_chunks_end_in ((i, xs ++ ys) :: zs) arr = (
    (LENGTH xs + LENGTH ys) - 1 <= i /\
    array_chunks_end_in ((i - LENGTH ys, xs) :: (i, ys) :: zs) arr
  )
Proof
  simp [array_chunks_end_in_def]
  \\ Cases_on `xs = []` \\ csimp []
  \\ Cases_on `ys = []` \\ csimp []
  >- (
    EQ_TAC \\ rw [] \\ fs []
  )
  \\ simp [MAPi_APPEND, o_DEF, GSYM CONJ_ASSOC]
  \\ Cases_on `LENGTH xs` \\ fs []
  \\ Cases_on `LENGTH ys` \\ fs []
  \\ csimp [ADD1]
QED

Theorem array_chunks_end_in_chunk_append_fun[local]:
  (LENGTH xs + LENGTH ys) - 1 <= i ==>
  array_chunks_end_in ((i, xs ++ ys) :: zs) = (
    array_chunks_end_in ((i - LENGTH ys, xs) :: (i, ys) :: zs)
  )
Proof
  simp [FUN_EQ_THM, array_chunks_end_in_chunk_append]
QED

Theorem array_chunks_end_in_EL[local]:
  array_chunks_end_in ((i, [x]) :: zs) arr ==>
    i < LENGTH arr /\ EL i arr = x
Proof
  rw [array_chunks_end_in_def]
QED

Theorem array_chunks_end_in_EL_each_LAST[local]:
  array_chunks_end_in xs arr ==>
  EVERY (\(i, xs). 0 < LENGTH xs ==> i < LENGTH arr /\ EL i arr = LAST xs) xs
Proof
  rw [array_chunks_end_in_def]
  \\ rw [EVERY_MEM]
  \\ pairarg_tac \\ fs []
  \\ fs [MEM_SPLIT] \\ fs []
  \\ disch_tac
  \\ qpat_x_assum `EVERY _ (MAPi _ _)` mp_tac
  \\ simp [EVERY_EL]
  \\ disch_then (qspec_then `LENGTH xs' - 1` mp_tac)
  \\ imp_res_tac LENGTH_NOT_NULL
  \\ fs [NULL_EQ, LAST_EL, PRE_SUB1]
QED

Theorem array_chunks_end_in_LUPDATE[local]:
  array_chunks_end_in ((i, [x]) :: zs) arr ==>
  array_chunks_end_in ((i, [y]) :: zs) (LUPDATE y i arr)
Proof
  rw [array_chunks_end_in_def, EL_LUPDATE]
  \\ fs [EVERY_FLAT, EVERY_MAP]
  \\ subgoal `!f g. EVERY f zs /\ (EVERY f zs = EVERY g zs) ==> EVERY g zs`
  \\ csimp []
  \\ pop_assum (drule_then irule)
  \\ irule EVERY_CONG
  \\ simp [FORALL_PROD] \\ rw []
  \\ irule EVERY_CONG
  \\ simp [MEM_MAPi, PULL_EXISTS]
  \\ rw []
  \\ dxrule (hd (RES_CANON MEM_SPLIT))
  \\ rw [] \\ fs []
  \\ fs [MEM_MAPi]
QED

Theorem array_chunks_end_in_tree_split[local]:
  0 < ht ==> (
  array_chunks_end_in ((i, bs_tree_to_list ht (Node x l r)) :: xs) arr <=>
  (2 * two_exp_min_1 (ht - 1) <= i) /\
  array_chunks_end_in (
        (i - (two_exp_min_1 (ht - 1) + 1), bs_tree_to_list (ht - 1) l) ::
        (i - 1, bs_tree_to_list (ht - 1) r) :: (i, [x]) :: xs) arr
  )
Proof
  csimp [bs_tree_to_list_tree_rec]
  \\ simp [array_chunks_end_in_chunk_append]
  \\ rw [] \\ EQ_TAC \\ rw []
  \\ fs [LENGTH_bs_tree_to_list]
QED

Theorem array_chunks_end_in_tree_split_fun[local]:
  0 < ht /\ (2 * two_exp_min_1 (ht - 1) <= i) ==> (
  array_chunks_end_in ((i, bs_tree_to_list ht (Node x l r)) :: xs) =
  array_chunks_end_in (
        (i - (two_exp_min_1 (ht - 1) + 1), bs_tree_to_list (ht - 1) l) ::
        (i - 1, bs_tree_to_list (ht - 1) r) :: (i, [x]) :: xs)
  )
Proof
  simp [FUN_EQ_THM, array_chunks_end_in_tree_split]
QED

Theorem array_chunks_end_in_bag_eq[local]:
  array_chunks_end_in xs arr /\ LIST_TO_BAG xs = LIST_TO_BAG ys ==>
  array_chunks_end_in ys arr

Proof

  cheat

QED

Theorem array_chunks_end_in_bag_eq_LUPDATE[local]:
  array_chunks_end_in xs arr /\
  MEM (i, [z]) xs /\
  LIST_TO_BAG ys = ((LIST_TO_BAG xs - {|(i, [z])|}) + {|(i, [y])|}) ==>
  array_chunks_end_in ys (LUPDATE y i arr)

Proof

  cheat

QED

Theorem EQ_REFL_OR[local]:
  x = x \/ P
Proof
  simp []
QED

val rotate_
           (CHANGED_TAC (REWRITE_TAC [array_chunks_end_in_rotate]) \\ simp [APPEND])


Definition eq_array_def:
  eq_array p p' P = (?arr. p = (FST p',
    (SND p' : 'a state_refs) with <| heap_array := arr |>) /\ P arr)
End

Theorem eq_array_sub:
  i < LENGTH (acc s) ==>
  eq_array (st_ex_bind (Marray_sub acc exn i) f s) (M_success v, s') P =
  eq_array (f (EL i (acc s)) s) (M_success v, s') P
Proof
  simp [eq_array_def, monad_simps]
QED

fun dest_list_apps t = let
    open listSyntax
    fun f xs yss [] = (xs, yss)
      | f xs yss (t :: ts) = if is_cons t
        then f (fst (dest_cons t) :: xs) yss (snd (dest_cons t) :: ts)
        else if is_append t
        then f xs yss (fst (dest_append t) :: snd (dest_append t) :: ts)
        else f xs (t :: yss) ts
  in f [] [] [t] end

fun chunks_conv pred t = let
    val (f, xs) = strip_comb t
    val _ = same_const ``array_chunks_end_in`` f orelse
        failwith "not array_chunks_end_in"
    val _ = (length xs = 2) orelse failwith "not enough args"
    val (chk_vs, oths) = dest_list_apps (hd xs)
    val el_typ = listSyntax.dest_list_type (type_of (hd xs))
    val (pick, reject) = partition pred chk_vs
    val base = if null oths then listSyntax.mk_list ([], el_typ)
        else foldr listSyntax.mk_append (last oths) (butlast oths)
    val rhs_chks = foldr listSyntax.mk_cons base (pick @ reject)
    val eq = mk_eq (t, list_mk_comb (f, [rhs_chks, last xs]))

fun pred t = can (match_term ``(_, [_])``) t


Theorem insert_into_sfx_heap_eq:

  ! t R i ht x st.
  array_chunks_end_in ((i, bs_tree_to_list ht t) :: others) st.heap_array /\
  i + 1 <= LENGTH st.heap_array /\
  two_exp_min_1 ht <= i + 1 /\
  ht > 0 /\
  tree_balanced_height ht t ==>
  eq_array (insert_into_sfx_heap R i ht x st)
    (M_success (), st)
    (array_chunks_end_in ((i, bs_tree_to_list ht (insert_tree_inv R t x)) :: others))

Proof

  Induct
  \\ simp [tree_balanced_height_def]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ rw []
  >- (
    Cases_on `ht = 1` \\ fs [tree_balanced_height_0]
    \\ simp [monad_simps, eq_array_def]
    \\ irule_at Any EQ_REFL
    \\ fs [array_chunks_end_in_tree_split, bs_tree_to_list_def,
            insert_tree_inv_def, array_chunks_end_in_null]
    \\ drule_then irule array_chunks_end_in_LUPDATE
  )
  >- (

    (* split array chunks once *)
    gs [array_chunks_end_in_tree_split]
    (* then expand the tree further to get top node vals *)
    \\ gs [tree_balanced_height_pos]
    (* continue *)
    \\ simp [sfx_heap_left_def, to_two_exp_min_1]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ simp [monad_simps, return_bind_eq, eq_array_sub]
    \\ imp_res_tac array_chunks_end_in_EL_each_LAST
    \\ gs [LENGTH_bs_tree_to_list, LAST_bs_tree_to_list, two_exp_min_1_pos]
    \\ rpt TOP_CASE_TAC \\ simp [ml_monadBaseTheory.monad_eqs]
    >- (
      simp [eq_array_def, monad_simps]
      \\ irule_at Any EQ_REFL
      \\ simp [Once array_chunks_end_in_tree_split]
      \\ drule_then (irule_at Any) array_chunks_end_in_bag_eq_LUPDATE
      \\ simp []
      \\ fsrw_tac [simpLib.ac_ss [(DISJ_ASSOC, DISJ_COMM)]] []
      \\ irule_at Any EQ_REFL_OR
      \\ simp [BAG_INSERT_commutes, BAG_UNION_INSERT]
    )
    >- (
      irule_at Any array_chunks_end_in_bag_eq
      \\ ONCE_REWRITE_TAC [CONJ_COMM]
      \\ ONCE_REWRITE_TAC [CONJ_ASSOC]
      \\ first_x_assum (irule_at Any)




Theorem insert_into_sfx_heap_eq:

  ! ht i st t others.
  array_chunks_end_in ((i, bs_tree_to_list ht t) :: others) st.heap_array /\
  i + 1 <= LENGTH st.heap_array /\
  two_exp_min_1 ht <= i + 1 /\
  ht > 0 /\
  tree_balanced_height ht t ==>
  ? arr'.
  insert_into_sfx_heap R i ht x st = (M_success (), st with <| heap_array := arr' |>) /\
  array_chunks_end_in ((i, bs_tree_to_list ht (insert_tree_inv R t x)) :: others) arr'

Proof

  Induct
  \\ simp [tree_balanced_height_def, ADD1]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ rw []
  >- (
    Cases_on `ht` \\ fs [tree_balanced_height_pos, tree_balanced_height_0]
    \\ simp [monad_simps]
    \\ irule_at Any EQ_REFL
    \\ fs [array_chunks_end_in_tree_split, bs_tree_to_list_def,
            insert_tree_inv_def, array_chunks_end_in_null]
    \\ drule_then irule array_chunks_end_in_LUPDATE
  )
  >- (

    (* unfold tree once *)
    fs [Once tree_balanced_height_pos]
    (* split array chunks once *)
    \\ gs [array_chunks_end_in_tree_split]
    (* then expand the tree further to get top node vals *)
    \\ gs [tree_balanced_height_pos]
    \\ simp [sfx_heap_left_def, to_two_exp_min_1]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ simp [monad_simps]
    \\ imp_res_tac array_chunks_end_in_EL_each_LAST
    \\ gs [LENGTH_bs_tree_to_list, LAST_bs_tree_to_list, two_exp_min_1_pos]
    \\ rpt TOP_CASE_TAC \\ simp []

    >- (
      simp [monad_simps]
      \\ irule_at Any EQ_REFL
      \\ simp [Once array_chunks_end_in_tree_split_fun]

      \\ qpat_x_assum `array_chunks_end_in _ _` mp_tac


      \\ drule_then (irule_at Any) array_chunks_end_in_bag_eq_LUPDATE
      \\ simp []
      \\ fsrw_tac [simpLib.ac_ss [(DISJ_ASSOC, DISJ_COMM)]] []
      \\ irule_at Any EQ_REFL_OR
      \\ simp [BAG_INSERT_commutes, BAG_UNION_INSERT]
    )
    >- (

      ONCE_REWRITE_TAC [ml_monadBaseTheory.monad_eqs]
      \\ simp [PULL_EXISTS]

      qmatch_goalsub_abbrev_tac `insert_into_sfx_heap _ i2 _ _ st2`
      \\ first_x_assum (qspecl_then [`i2`, `st2`] mp_tac)
      \\ dxrule (hd (RES_CANON array_chunks_end_in_rotate))
      \\ rw []
      \\ first_x_assum drule

      irule_at Any array_chunks_end_in_bag_eq
      \\ ONCE_REWRITE_TAC [CONJ_COMM]
      \\ ONCE_REWRITE_TAC [CONJ_ASSOC]
      \\ first_x_assum (irule_at Any)

      \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []



      \\ rpt (irule array_chunks_end_in_LUPDATE ORELSE
           (CHANGED_TAC (REWRITE_TAC [array_chunks_end_in_rotate]) \\ simp [APPEND])
        )
      \\ REWRITE_TAC [GSYM APPEND_ASSOC]
      \\ ONCE_REWRITE_TAC [array_chunks_end_in_append]
      \\ simp []
      \\ first_assum (irule_at Any)
    )

REWRITE_TAC [array_chunks_end_in_rotate])
      \\



Theorem monad_eq_helper[local]:
  (?s'. mv = (M_success x, s') /\ (SND mv = s' ==> s = s' /\ Q)) ==>
  mv = (M_success x, s) /\ Q
Proof
  rw [] \\ fs []
QED

Definition monad_eq_array_prop_def:
  monad_eq_array_prop mv x s P =
    (case mv of (M_success x', (s' : 'a state_refs)) =>
        x' = x /\ (?arr. s' = (s with <| heap_array := arr |>) /\ P arr)
      | _ => F)
End

Theorem monad_eq_array_prop_array_upd[local]:
  monad_eq_array_prop mv x (heap_array_fupd f s) P =
  monad_eq_array_prop mv x s P
Proof
  simp [monad_eq_array_prop_def]
QED

Theorem monad_eq_array_prop_eraseI:
  (case mv of (M_success x', s') =>
    x' = x /\ (s' with <| heap_array := [] |>) = (s with <| heap_array := [] |>) /\
    P s'.heap_array
  | _ => F) ==>
  monad_eq_array_prop mv x s P
Proof
  simp [monad_eq_array_prop_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ simp [fetch "-" "state_refs_component_equality"]
QED

Theorem monad_eq_array_prop_exI:
  (?s'. mv = (M_success x', s') /\
    x' = x /\ (s' with <| heap_array := [] |>) = (s with <| heap_array := [] |>) /\
    P s'.heap_array) ==>
  monad_eq_array_prop mv x s P
Proof
  rw [] \\ irule monad_eq_array_prop_eraseI
  \\ simp []
QED

Theorem monad_eq_array_prop_bindI:
  monad_eq_array_prop (m (st : 'a state_refs)) y (bd_st : 'a state_refs) Q /\
  (! upd_st arr. Q upd_st.heap_array /\ bd_st = (upd_st with <| heap_array := arr |>) ==>
    monad_eq_array_prop (f y upd_st) x st' P)
  ==>
  monad_eq_array_prop (st_ex_bind m f st) x st' P
Proof
  rw [] \\ irule monad_eq_array_prop_exI
  \\ simp [monad_simps]
  \\ Cases_on `FST (m st)` \\ Cases_on `m st` \\ fs [monad_eq_array_prop_def]
  \\ rw []
  \\ first_x_assum (qspecl_then [`bd_st with heap_array := arr`, `bd_st.heap_array`] mp_tac)
  \\ rpt (TOP_CASE_TAC \\ fs [])
  \\ simp [fetch "-" "state_refs_component_equality"]
QED

Theorem monad_eq_array_prop_bindI_rdonly:
  monad_eq_array_prop (m st) y st ((=) st.heap_array) /\
  monad_eq_array_prop (f y st) x st' P
  ==>
  monad_eq_array_prop (st_ex_bind m f st) x st' P
Proof
  rw [] \\ irule monad_eq_array_prop_bindI
  \\ last_assum (irule_at Any)
  \\ rw []
  \\ fs []
  \\ subgoal `(upd_st with heap_array := upd_st.heap_array) = upd_st`
  \\ fs []
  \\ simp [fetch "-" "state_refs_component_equality"]
QED

Theorem heap_array_sub_bind_eq:
  i < LENGTH st.heap_array ==>
  st_ex_bind (heap_array_sub i) f st =
  f (EL i st.heap_array) st
Proof
  rw []
  \\ fs [ml_monadBaseTheory.st_ex_bind_def]
  \\ simp [ml_monadBaseTheory.exc_case_eq, pair_case_eq]
  \\ simp [monad_simps]
QED

Theorem sz_array_sub_bind_eq:
  i < LENGTH st.sz_array ==>
  st_ex_bind (sz_array_sub i) f st =
  f (EL i st.sz_array) st
Proof
  rw []
  \\ fs [ml_monadBaseTheory.st_ex_bind_def]
  \\ simp [ml_monadBaseTheory.exc_case_eq, pair_case_eq]
  \\ simp [monad_simps]
QED

Theorem update_sz_array_prop:
  i < LENGTH st.sz_array ==>
  monad_eq_array_prop (update_sz_array i x st) ()
    (st with <| sz_array := LUPDATE x i st.sz_array |>)
    ((=) st.heap_array)
Proof
  rw [] \\ irule monad_eq_array_prop_exI
  \\ simp [monad_simps]
QED

Theorem update_heap_array_prop:
  array_chunks_end_in ((i, [prev_x]) :: others) st.heap_array ==>
  monad_eq_array_prop (update_heap_array i x st) () st
    (array_chunks_end_in ((i, [x]) :: others))
Proof
  rw [] \\ irule monad_eq_array_prop_exI
  \\ simp [monad_simps]
  \\ imp_res_tac array_chunks_end_in_EL_each_LAST
  \\ fs []
  \\ drule_then irule array_chunks_end_in_LUPDATE
QED

Theorem monad_eq_array_prop_postcondI:
  monad_eq_array_prop mv x s P /\ (!arr. P arr ==> Q arr) ==>
  monad_eq_array_prop mv x s Q
Proof
  rw [monad_eq_array_prop_def]
  \\ EVERY_CASE_TAC \\ fs []
  \\ irule_at Any EQ_REFL \\ simp []
QED

Theorem array_chunks_end_in_bag_eq_IMP[local]:
  array_chunks_end_in xs arr /\
  LIST_TO_BAG xs = LIST_TO_BAG ys ==>
  array_chunks_end_in ys arr
Proof
  metis_tac [array_chunks_end_in_bag_eq]
QED

val chunks_const = ``array_chunks_end_in``

fun chunk_select_conv pat tm = let
    val (f, xs) = strip_comb tm
    val _ = same_const chunks_const f orelse
        failwith "not array_chunks_end_in"
    val _ = not (null xs) orelse failwith "array_chunks_end_in no args"
    val cs = hd xs
    val ts = find_terms (fn t => listSyntax.is_cons t
        andalso can (match_term pat) (rand (rator t))) cs
    val _ = not (null ts) orelse failwith ("no chunk matches")
    val cs2 = Term.subst [hd ts |-> rand (hd ts)] cs
    val cs3 = listSyntax.mk_cons (rand (rator (hd ts)), cs2)
    val rhs = list_mk_comb (f, cs3 :: tl xs)
    val _ = not (aconv tm rhs) orelse failwith "chunk_select_conv: done"
    val eq = mk_eq (tm, list_mk_comb (f, cs3 :: tl xs))
  in prove (eq, TRY AP_THM_TAC
      \\ irule array_chunks_end_in_bag_eq
      \\ fsrw_tac [bagSimps.BAG_AC_ss] [BAG_INSERT_UNION])
  end

fun chunk_select_tac pat = POP_ASSUM_LIST (fn asms => let
    fun do_conv asm = if can (find_term (same_const chunks_const)) (concl asm)
      then let
        val asm2 = CONV_RULE (ONCE_DEPTH_CONV (chunk_select_conv pat)) asm
      in (asm2, aconv (concl asm2) (concl asm)) end
      else (asm, true)
    val conv_asms = map do_conv asms
    val (no_upd, upd) = partition snd conv_asms
  in MAP_EVERY (ASSUME_TAC o fst) (rev (upd @ no_upd))
    >> CONV_TAC (ONCE_DEPTH_CONV (chunk_select_conv pat)) end)

fun select_chunk_goal pat = CONV_TAC (DEPTH_CONV (chunk_select_conv pat))

fun select_chunk_asm pat = qpat_x_assum `array_chunks_end_in _ _`
    (assume_tac o CONV_RULE (chunk_select_conv pat))

(* chunks ends variant *)
Theorem insert_into_sfx_heap_eq:
  ! ht i st t others.
  array_chunks_end_in ((i, bs_tree_to_list ht t) :: others) st.heap_array /\
  ht > 0 /\
  tree_balanced_height ht t ==>
  monad_eq_array_prop (insert_into_sfx_heap R i ht x st) () st
      (array_chunks_end_in ((i, bs_tree_to_list ht (insert_tree_inv R t x)) :: others))
Proof
  Induct
  \\ simp [tree_balanced_height_def, ADD1]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ rw []
  >- (
    Cases_on `ht` \\ fs [tree_balanced_height_pos, tree_balanced_height_0]
    \\ irule monad_eq_array_prop_exI
    \\ simp [monad_simps]
    \\ imp_res_tac array_chunks_end_in_EL_each_LAST
    \\ fs [LENGTH_bs_tree_to_list, two_exp_min_1_pos]
    \\ fs [array_chunks_end_in_tree_split, bs_tree_to_list_def,
            insert_tree_inv_def, array_chunks_end_in_null]
    \\ drule_then irule array_chunks_end_in_LUPDATE
  )
  >- (
    (* unfold tree once *)
    fs [Once tree_balanced_height_pos]
    (* split array chunks once *)
    \\ gs [array_chunks_end_in_tree_split]
    (* then expand the tree further to get top node vals *)
    \\ gs [tree_balanced_height_pos]
    \\ simp [sfx_heap_left_def, to_two_exp_min_1]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ imp_res_tac array_chunks_end_in_EL_each_LAST
    \\ gs [LENGTH_bs_tree_to_list, LAST_bs_tree_to_list, two_exp_min_1_pos]
    \\ simp [return_bind_eq, heap_array_sub_bind_eq]
    \\ rpt TOP_CASE_TAC \\ simp []
    >- (
      simp [Once array_chunks_end_in_tree_split_fun]
      \\ chunk_select_tac ``(_, [_])``
      \\ drule_then irule update_heap_array_prop
    )
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ simp [Once array_chunks_end_in_tree_split_fun]
      \\ chunk_select_tac ``(_, [_])``
      \\ irule monad_eq_array_prop_bindI
      \\ dxrule_then (irule_at Any) update_heap_array_prop
      \\ rw []
      \\ chunk_select_tac ``(_ - 1n, _)``
      \\ first_x_assum dxrule
      \\ simp [monad_eq_array_prop_array_upd]
    )
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ simp [Once array_chunks_end_in_tree_split_fun]
      \\ chunk_select_tac ``(_, [_])``
      \\ irule monad_eq_array_prop_bindI
      \\ dxrule_then (irule_at Any) update_heap_array_prop
      \\ rw []
      \\ chunk_select_tac ``(_ - (_ + 1n), _)``
      \\ first_x_assum dxrule
      \\ simp [monad_eq_array_prop_array_upd]
    )
  )
QED

Definition bs_tree_list_chunks_def:
  bs_tree_list_chunks i [] = [] /\
  bs_tree_list_chunks i ((t, ht) :: ts) =
    ((i, bs_tree_to_list ht t) :: bs_tree_list_chunks (i - two_exp_min_1 ht) ts)
End

Theorem insert_into_sfx_heap_list_eq:
  ! j ts R i x others st.
  array_chunks_end_in ((i, bs_tree_list_to_list ts) :: others) st.heap_array /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j <= LENGTH st.sz_array ==>
  0 < j /\ EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  monad_eq_array_prop (insert_into_sfx_heap_list R i j x st) () st
      (array_chunks_end_in ((i, bs_tree_list_to_list (insert_trees_inv R ts x)) :: others))
Proof
  Induct
  \\ simp []
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_list_def]
  \\ rpt strip_tac
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ gs [ADD1, TAKE_SUM]
  \\ simp [insert_trees_inv_def]
  \\ rw []
  >- (
    Cases_on `j` \\ fs []
    \\ gs [tree_balanced_height_pos, bs_tree_list_to_list_rec]
    \\ simp [sz_array_sub_bind_eq]
    \\ irule insert_into_sfx_heap_eq
    \\ simp [tree_balanced_height_pos]
  )
  >- (
    gs [bs_tree_list_to_list_rec, tree_balanced_height_pos, ADD1,
        array_chunks_end_in_chunk_append]
    \\ simp [sz_array_sub_bind_eq, return_bind_eq]
    \\ imp_res_tac array_chunks_end_in_EL_each_LAST
    \\ gs [EL_TAKE, EL_APPEND, array_chunks_end_in_tree_split,
         LENGTH_bs_tree_to_list, two_exp_min_1_pos, APPEND]
    \\ simp [to_two_exp_min_1]
    \\ qpat_x_assum `0 < LENGTH (bs_tree_list_to_list _) ==> _` mp_tac
    \\ impl_keep_tac
    >- (
      Cases_on `HD t` \\ Cases_on `t` \\ fs []
      \\ gs [bs_tree_list_to_list_rec, tree_balanced_height_pos]
      \\ simp [bs_tree_to_list_tree_rec]
    )
    \\ rw []
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [tree_balanced_height_pos]
    \\ simp [heap_array_sub_bind_eq]
    \\ irule monad_eq_array_prop_bindI_rdonly
    \\ qmatch_goalsub_abbrev_tac `bs_tree_list_to_list (COND tree_conds _ _)`
    \\ qexists_tac `tree_conds`
    \\ conj_tac
    >- (
      Cases_on `j` \\ fs [ADD1, TAKE_SUM]
      \\ fs [markerTheory.Abbrev_def, bs_tree_list_to_list_rec,
            bs_tree_to_list_tree_rec]
      \\ reverse (rw [])
      >- (
        gs []
        \\ irule monad_eq_array_prop_exI
        \\ simp [ml_monadBaseTheory.monad_eqs]
        \\ gs [tree_balanced_height_eq_0]
      )
      >- (
        gs [tree_balanced_height_pos]
        \\ fs [array_chunks_end_in_chunk_append]
        \\ chunk_select_tac ``(_, _ ++ _)``
        \\ fs [array_chunks_end_in_chunk_append]
        \\ simp [sfx_heap_left_def, to_two_exp_min_1]
        \\ imp_res_tac array_chunks_end_in_EL_each_LAST
        \\ gs [LENGTH_bs_tree_to_list, two_exp_min_1_pos]
        \\ simp [heap_array_sub_bind_eq, LAST_bs_tree_to_list]
        \\ irule monad_eq_array_prop_exI
        \\ simp [ml_monadBaseTheory.monad_eqs]
      )
    )
    >- (
      qpat_x_assum `Abbrev _` (K all_tac)
      \\ rw []
      >- (
        fs [st_ex_ignore_bind_simp, bs_tree_to_list_tree_rec]
        \\ chunk_select_tac ``(_, _ ++ _)``
        \\ fs [array_chunks_end_in_chunk_append]
        \\ chunk_select_tac ``(_, [_])``
        \\ irule monad_eq_array_prop_bindI
        \\ dxrule_then (irule_at Any) update_heap_array_prop
        \\ rw []
        \\ simp [bs_tree_list_to_list_rec]
        \\ dep_rewrite.DEP_REWRITE_TAC [array_chunks_end_in_chunk_append_fun]
        \\ fs [LENGTH_bs_tree_to_list, LENGTH_list_of_insert_trees]
        \\ simp [monad_eq_array_prop_array_upd]
        \\ first_x_assum irule
        \\ simp [tree_balanced_height_def]
        \\ chunk_select_tac ``(_, bs_tree_to_list _ (Node _ _ _))``
        \\ simp [array_chunks_end_in_tree_split]
        \\ chunk_select_tac ``(_, [_])``
        \\ gs [bs_tree_list_to_list_rec, bs_tree_to_list_tree_rec]
      )
      >- (
        ONCE_REWRITE_TAC [bs_tree_list_to_list_rec]
        \\ simp [array_chunks_end_in_chunk_append_fun, LENGTH_bs_tree_to_list]
        \\ chunk_select_tac ``(_, bs_tree_to_list _ _)``
        \\ irule insert_into_sfx_heap_eq
        \\ simp [tree_balanced_height_def]
      )
    )
  )
QED

Theorem add_to_sfx_heaps_step1_eq:
  array_chunks_end_in ((i, [x]) :: (i - 1, bs_tree_list_to_list ts) :: others) st.heap_array /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < i /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ j + 1 < LENGTH st.sz_array ==>
  let ts2 = add_trees_step1 ts x;
        xs = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  monad_eq_array_prop (add_to_sfx_heaps_step1 i j st) l2
      (st with <| sz_array := MAP SND (REVERSE ts2) ++ DROP l2 st.sz_array |>)
      (array_chunks_end_in ((i, bs_tree_list_to_list ts2) :: others))
Proof
  rw []
  \\ simp [add_to_sfx_heaps_step1_def, add_trees_step1_def]
  \\ irule monad_eq_array_prop_bindI_rdonly
  \\ qexists_tac `case ts of (_, n1) :: (_, n2) :: _ => n1 = n2 | _ => F`
  \\ conj_tac
  >- (
    Cases_on `ts` \\ fs []
    \\ simp [monad_eq_array_prop_exI, ml_monadBaseTheory.monad_eqs]
    \\ fs [ADD1, TAKE_SUM]
    \\ Cases_on `t` \\ fs []
    \\ simp [monad_eq_array_prop_exI, ml_monadBaseTheory.monad_eqs]
    \\ fs [ADD1, TAKE_SUM]
    \\ simp [sz_array_sub_bind_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ simp [monad_eq_array_prop_exI, ml_monadBaseTheory.monad_eqs]
  )
  \\ rw []
  >- (
    (* merge case *)
    rpt (TOP_CASE_TAC \\ fs [ADD1, TAKE_SUM])
    \\ simp [sz_array_sub_bind_eq, st_ex_ignore_bind_simp]
    \\ irule monad_eq_array_prop_bindI
    \\ irule_at Any update_sz_array_prop
    \\ rw []
    \\ simp [monad_eq_array_prop_array_upd]
    \\ qspec_then `st.sz_array` mp_tac LESS_LENGTH
    \\ disch_then (qspec_then `LENGTH t'` mp_tac)
    \\ rw []
    \\ fs [EL_APPEND, TAKE_APPEND1, LUPDATE_APPEND, LUPDATE_def]
    \\ rw []
    \\ gs [TAKE_LENGTH_TOO_LONG, DROP_APPEND2, monad_eq_array_prop_array_upd]
    \\ irule monad_eq_array_prop_exI
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ fs [bs_tree_list_to_list_rec, bs_tree_to_list_tree_rec]
    \\ ONCE_REWRITE_TAC [array_chunks_end_in_chunk_append]
    \\ fs []
    \\ chunk_select_tac ``(_ - 1n, _)``
    \\ simp []
    \\ fs [array_chunks_end_in_chunk_append]
    \\ gs [LENGTH_bs_tree_to_list, two_exp_min_1_less_rec]
  )
  >- (
    (* no merge case *)
    simp [st_ex_ignore_bind_simp]
    \\ qmatch_goalsub_abbrev_tac `bs_tree_list_to_list upd_trees`
    \\ subgoal `upd_trees = (Node x Empty_Tree Empty_Tree, 1) :: ts`
    >- (
      every_case_tac \\ fs []
    )
    \\ simp []
    \\ irule monad_eq_array_prop_bindI
    \\ irule_at Any update_sz_array_prop
    \\ rw []
    \\ fs [ADD1]
    \\ qspec_then `st.sz_array` mp_tac LESS_LENGTH
    \\ disch_then (qspec_then `LENGTH ts` mp_tac)
    \\ rw []
    \\ fs [LUPDATE_APPEND, LUPDATE_DEF, TAKE_APPEND1]
    \\ gs [TAKE_LENGTH_TOO_LONG, DROP_APPEND2, monad_eq_array_prop_array_upd]
    \\ irule monad_eq_array_prop_exI
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ simp [bs_tree_list_to_list_rec, bs_tree_to_list_tree_rec]
    \\ chunk_select_tac ``(_ - 1n, _)``
    \\ simp [array_chunks_end_in_chunk_append]
    \\ fs [array_chunks_end_in_def]
  )
QED

Theorem add_to_sfx_heaps_eq:
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < i /\
  array_chunks_end_in ((i, [x]) :: (i - 1, bs_tree_list_to_list ts) :: others) st.heap_array /\
  TAKE j st.sz_array = MAP SND (REVERSE ts) /\
  j = LENGTH ts /\ j + 1 < LENGTH st.sz_array ==>
  (let ts2 = add_trees R ts x; xs = bs_tree_list_to_list ts2; l2 = LENGTH ts2 in
  monad_eq_array_prop (add_to_sfx_heaps R i j x st) l2
      (st with <| sz_array := MAP SND (REVERSE ts2) ++ DROP l2 st.sz_array |>)
      (array_chunks_end_in ((i, bs_tree_list_to_list ts2) :: others))
  )

Proof

  simp [add_to_sfx_heaps_def, add_trees_def, st_ex_ignore_bind_simp]
  \\ rpt strip_tac
  \\ irule monad_eq_array_prop_bindI
  \\ dxrule_then (irule_at Any) (SIMP_RULE bool_ss [LET_THM] add_to_sfx_heaps_step1_eq)
  \\ fs []
  \\ rw []
  \\ irule monad_eq_array_prop_bindI
  \\ dxrule_then (irule_at Any) insert_into_sfx_heap_list_eq
  \\ simp [LENGTH_add_tree_step1_facts]

  \\ 
  \\ simp [



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


