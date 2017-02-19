open preamble;
open semanticPrimitivesTheory;
open ml_translatorTheory ml_translatorLib ml_progLib;
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib;
open basisFunctionsLib;
open mlarrayProgTheory;

val _ = new_theory "quicksortProg";

val _ = translation_extends"mlarrayProg";

val hd_seg = Q.store_thm ("hd_seg",
  `!len start l.
    0 < len ∧
    start < LENGTH l
    ⇒
    HD (SEG len start l) = EL start l`,
  Induct_on `start` >>
  rw []
  >- (
    Cases_on `len` >>
    fs [SEG] >>
    Cases_on `l` >>
    fs [SEG]) >>
  Cases_on `len` >>
  fs [EL, SEG] >>
  Cases_on `l` >>
  fs [EL, SEG]);

val tl_seg = Q.store_thm ("tl_seg",
  `!len start l.
    0 < len ∧
    start < LENGTH l
    ⇒
    TL (SEG len start l) = SEG (len - 1) (start + 1) l`,
  Induct_on `start` >>
  rw []
  >- (
    Cases_on `len` >>
    fs [SEG] >>
    Cases_on `l` >>
    fs [SEG] >>
    `1 = SUC 0` by decide_tac >>
    Cases_on `n` >>
    ASM_REWRITE_TAC [SEG]) >>
  Cases_on `len` >>
  fs [EL, SEG] >>
  Cases_on `l` >>
  fs [EL, SEG, GSYM ADD1] >>
  Cases_on `n` >>
  simp [SEG]);

val el_seg = Q.store_thm ("el_seg",
  `!n len start l.
    len + start ≤ LENGTH l ∧
    n < len
    ⇒
    EL n (SEG len start l) = EL (n+start) l`,
  Induct_on `n` >>
  rw [hd_seg, EL, tl_seg, ADD1]);

val list_rel_seg = Q.store_thm ("list_rel_seg",
  `!r start len l1 l2.
    start + len ≤ LENGTH l1 ∧
    LIST_REL r l1 l2
    ⇒
    LIST_REL r (SEG len start l1) (SEG len start l2)`,
  rw [LIST_REL_EL_EQN, el_seg, LENGTH_SEG]);

(* Split a list into the part before lower, the part between lower and upper,
 * inclusive, and the part after upper. Need lower < upper and upper < LENGTH l
 * *)
val split_list_def = Define `
  split_list lower upper l =
    (SEG lower 0 l,
     SEG (upper - lower + 1) lower l,
     SEG (LENGTH l - upper - 1) (upper + 1) l)`;

val split_list_same = Q.store_thm ("split_list_same",
  `!idx l.
    idx < LENGTH l ⇒
    split_list idx idx l =
      (SEG idx 0 l, [EL idx l], SEG (LENGTH l - idx - 1) (idx + 1) l)`,
  rw [split_list_def] >>
  drule EL_SEG >>
  rw [] >>
  `LENGTH (SEG 1 idx l) = 1`
  by (
    irule LENGTH_SEG >>
    decide_tac) >>
  Cases_on `SEG 1 idx l` >>
  fs [] >>
  Cases_on `t` >>
  fs []);

val split_list_append = Q.store_thm ("split_list_append",
  `!lower upper l l1 l2 l3.
    lower ≤ upper ∧ upper < LENGTH l ∧
    split_list lower upper l = (l1, l2, l3)
    ⇒
    l1 ++ l2 ++ l3 = l`,
 rw [split_list_def] >>
 cheat);

val split_list_combine = Q.store_thm ("split_list_append2",
  `!l l1 l2 l3.
    LENGTH l2 ≠ 0 ⇒
    split_list (LENGTH l1) (LENGTH l1 + LENGTH l2 - 1) (l1++l2++l3) = (l1, l2, l3)`,
  rw [split_list_def]
  >- (
    Induct_on `l1` >>
    fs [SEG])
  >- (
    Induct_on `l1` >>
    fs [SEG] >>
    Induct_on `l2` >>
    fs [SEG] >>
    Induct_on `l2` >>
    fs [SEG])
  >- (
    `LENGTH (l1 ++ l2) ≤ LENGTH l1 + LENGTH l2` by rw [] >>
    drule SEG_APPEND2 >>
    `LENGTH l3 ≤ LENGTH l3` by rw [] >>
    disch_then drule >>
    simp [] >>
    rw [] >>
    rpt (pop_assum kall_tac) >>
    Induct_on `l3` >>
    rw [SEG]));

val split_list_length = Q.store_thm ("split_list_length",
  `!lower upper l l1 l2 l3.
    lower ≤ upper ∧ upper < LENGTH l ∧
    split_list lower upper l = (l1, l2, l3)
    ⇒
    LENGTH l1 = lower ∧
    LENGTH l2 = upper - lower + 1 ∧
    LENGTH l3 = LENGTH l - upper - 1`,
  rw [split_list_def] >>
  rw [LENGTH_SEG]);

fun basis_st () = get_ml_prog_state ()

val partition = process_topdecs `
fun partition cmp a pivot lower upper =
let
  fun scan_lower lower =
  let
    val lower = lower + 1
  in
    if cmp (Array.sub a lower) pivot then
      scan_lower lower
    else
      lower
  end

  fun scan_upper upper =
  let
    val upper = upper - 1
  in
    if cmp pivot (Array.sub a upper) then
      scan_upper upper
    else
      upper
  end

  fun part_loop lower upper =
  let
    val lower = scan_lower lower
    val upper = scan_upper upper
  in
    if lower < upper then
      let
        val v = Array.sub a lower
      in
        (Array.update a lower (Array.sub a upper);
         Array.update a upper v;
         part_loop lower upper)
      end
    else
      upper
  end
in
  part_loop (lower - 1) (upper + 1)
end;
`;
val partition_st = ml_progLib.add_prog partition pick_name (basis_st ());

val partition_pred_def = Define `
  partition_pred a cmp pivot lower p_v elem_vs part1 part2 ⇔
    (* Neither part is empty *)
    part1 ≠ [] ∧ part2 ≠ [] ∧
    (* The returned index points to the end of the first partition *)
    INT (&(lower + LENGTH part1) - 1) p_v ∧
    (* The partition permutes the original array *)
    PERM elem_vs (part1 ++ part2) ∧
    ∃elems1 elems2.
      (* The elements of the first part aren't greater than the pivot *)
      LIST_REL a elems1 part1 ∧
      EVERY (\e. ¬cmp pivot e) elems1 ∧
      (* The elements of the second part aren't less than the pivot *)
      LIST_REL a elems2 part2 ∧
      EVERY (\e. ¬cmp e pivot) elems2`;

val partition_spec = Q.store_thm ("partition_spec",

  `!a ffi_p cmp cmp_v arr_v elems elem_vs pivot pivot_v lower lower_v upper upper_v
    elem_vs1 elem_vs2 elem_vs3.
    (* The comparison function is a strict partial order over a *)
    transitive cmp ∧
    (!x y. cmp x y ⇒ ~cmp y x) ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    (* The elements of the array have "semantic type" a *)
    LIST_REL a elems elem_vs ∧
    (* The pivot element has semantic type a *)
    a pivot pivot_v ∧
    (* The indices must point to array elements, with lower before upper *)
    INT (&lower) lower_v ∧ INT (&upper) upper_v ∧
    lower < upper ∧ upper < LENGTH elem_vs ∧
    (* The pivot must be in the array elements between lower (inclusive) and
     * upper (exclusive). This ensures that neither side of the partition is
     * empty. *)
    (elem_vs1, elem_vs2, elem_vs3) = split_list lower upper elem_vs ∧
    MEM pivot_v (FRONT elem_vs2)
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "partition" partition_st)
      (* The arguments *)
      [cmp_v; arr_v; pivot_v; lower_v; upper_v]
      (* The array argument is in the heap with contents elem_vs *)
      (ARRAY arr_v elem_vs)
      (* The partition function returns with a index p_v into the array *)
      (POSTv p_v. SEP_EXISTS part1 part2.
        (* The array is still in the heap, with elements that form a partition,
         * of the part between lower and upper. Elements outside the lower-upper
         * range are left unchanged. *)
        ARRAY arr_v (elem_vs1 ++ part1 ++ part2 ++ elem_vs3) *
        &(partition_pred a cmp pivot lower p_v elem_vs2 part1 part2))`,

  xcf "partition" partition_st >>
  xfun_spec `scan_lower`
    `!i i_v.
      (* scan_lower takes an integer i, where i+1 indexes into the array *)
      INT i i_v ∧ -1 ≤ i ∧ i + 1 < &(LENGTH elems) ∧
      (* There is an array index after i where the element is not less than the
       * pivot. This ensures termination before hitting the end of the array. *)
      (?x:num. i < (&x) ∧ x < LENGTH elems ∧ ¬cmp (EL x elems) pivot) ∧
      (* The elements of the array have semantic type a *)
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_lower
        [i_v]
        (* The array argument is in the heap with contents elem_vs *)
        (ARRAY arr_v elem_vs)
        (* The scan terminates with an resulting index j *)
        (POSTv (j_v:v).
          (* The array argument is still in the heap unchanged *)
          (ARRAY arr_v elem_vs) *
          &(∃j:num.
             (* The index increased, and did not run off the end *)
             INT (&j) j_v ∧ i < (&j) ∧ j < LENGTH elems ∧
             (* The result index j points to an element not smaller than the
              * pivot *)
             ¬cmp (EL j elems) pivot ∧
             (* There is nothing bigger than the pivot between where the scan
              * started and finished *)
             !k:num. i < (&k) ∧ k < j ⇒ ¬cmp pivot (EL k elems)))`
  >- (
    (* Prove that scan lower has the above invariant *)
    gen_tac >>
    Induct_on `Num(&(LENGTH elems) - i)` >>
    rw []
    >- (
      `i = &LENGTH elems` by intLib.ARITH_TAC >>
      fs []) >>
    (* Start to run through the loop body.
     * It was slightly confusing to have to do this manually, because the
     * default xapp tactic wanted to use the spec, which we don't want to
     * do until the recursive call. *)
    last_x_assum xapp_spec >>
    (* It was confusing, and then annoying to have to manually keep adding the
     * frame *)
    xlet `POSTv j_v. ARRAY arr_v elem_vs * &(?j. INT j j_v ∧ j = i + 1)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def]) >>
    `?n:num. i+1 = &n`
    by (
      `i + 1 = 0 ∨ 0 < i + 1` by intLib.ARITH_TAC >>
      rw [] >>
      qexists_tac `Num (i+1)` >>
      intLib.ARITH_TAC) >>
    xlet `POSTv x_v. ARRAY arr_v elem_vs * &(a (EL (Num (i+1)) elems) x_v)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `n` >>
      fs [NUM_def, LIST_REL_EL_EQN]) >>
    xlet `POSTv b_v. ARRAY arr_v elem_vs * &(BOOL (cmp (EL (Num (i + 1)) elems) pivot) b_v)`
    >- (
      xapp >>
      xsimpl >>
      rw [BOOL_def] >>
      metis_tac []) >>
    xif
    >- (
      (* Set up the invariant for the recursive call.
       * This was really confusing, because the default tactics without doing
       * this first did reasonable looking things, but that led to unprovable
       * goals  *)
      first_x_assum (qspecl_then [`elems`, `i+1`] mp_tac) >>
      impl_keep_tac
      >- intLib.ARITH_TAC >>
      fs [] >>
      disch_then xapp_spec >> (* Use the invariant for the recursive call *)
      xsimpl >>
      simp [GSYM PULL_EXISTS] >>
      rw []
      >- (
        qexists_tac `x` >>
        rw [] >>
        `i + 1 ≠ &x` suffices_by intLib.ARITH_TAC >>
        CCONTR_TAC >>
        fs [])
      >- (
        `&LENGTH elems ≠ i + 1 + 1` suffices_by intLib.ARITH_TAC >>
        CCONTR_TAC >>
        fs [] >>
        `i + 1 = &x` by intLib.ARITH_TAC >>
        fs [])
      >- (
        qexists_tac `j` >>
        rw []
        >- intLib.ARITH_TAC >>
        `i + 1 = &k ∨ i + 1 < &k` by intLib.ARITH_TAC >>
        rw [] >>
        fs [] >>
        rfs []))
    >- (
      xvar >>
      xsimpl >>
      qexists_tac `n` >>
      fs [] >>
      rw []
      >- intLib.ARITH_TAC >>
      `i+1 < &n` by intLib.ARITH_TAC >>
      rfs [])) >>
  xfun_spec `scan_upper`
    (* Similar to the scan_lower invariant, except that i-1 indexes the array,
     * and we scan down passing over elements bigger thatn the pivot *)
    `!i i_v.
      INT i i_v ∧ 0 ≤ i - 1 ∧ i ≤ &(LENGTH elems) ∧
      (?x:num. (&x) < i ∧ ¬cmp pivot (EL x elems)) ∧
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_upper
        [i_v]
        (ARRAY arr_v elem_vs)
        (POSTv (j_v:v).
          (ARRAY arr_v elem_vs) *
          &(∃j:num.
             INT (&j) j_v ∧ (&j) < i ∧ 0 ≤ j ∧
             ¬cmp pivot (EL j elems) ∧
             !k:num. (&k) < i ∧ j < k ⇒ ¬cmp (EL k elems) pivot))`
  >- (
    (* Prove that scan upper has the above invariant. Similar to the scan lower
     * proof above *)
    gen_tac >>
    Induct_on `Num i` >>
    rw []
    >- (
      `i = 0` by intLib.ARITH_TAC >>
      fs []) >>
    last_x_assum xapp_spec >>
    xlet `POSTv j_v. ARRAY arr_v elem_vs * &(?j. INT j j_v ∧ j = i - 1)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def]) >>
    `?n:num. i-1 = &n`
    by (
      `i - 1 = 0 ∨ 0 < i - 1` by intLib.ARITH_TAC >>
      rw [] >>
      qexists_tac `Num (i-1)` >>
      intLib.ARITH_TAC) >>
    xlet `POSTv x_v. ARRAY arr_v elem_vs * &(a (EL (Num (i-1)) elems) x_v)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `n` >>
      fs [NUM_def, LIST_REL_EL_EQN] >>
      `n < LENGTH elem_vs` by intLib.ARITH_TAC >>
      rw []) >>
    xlet `POSTv b_v. ARRAY arr_v elem_vs * &(BOOL (cmp pivot (EL (Num (i - 1)) elems)) b_v)`
    >- (
      xapp >>
      xsimpl >>
      rw [BOOL_def] >>
      metis_tac []) >>
    xif
    >- (
      first_x_assum (qspecl_then [`i-1`] mp_tac) >>
      impl_keep_tac
      >- intLib.ARITH_TAC >>
      fs [] >>
      disch_then xapp_spec >>
      xsimpl >>
      simp [GSYM PULL_EXISTS] >>
      rw []
      >- (
        qexists_tac `x` >>
        rw [] >>
        `i - 1 ≠ &x` suffices_by intLib.ARITH_TAC >>
        CCONTR_TAC >>
        fs [])
      >- intLib.ARITH_TAC
      >- (
        Cases_on `n` >>
        fs [] >>
        rfs [] >>
        intLib.ARITH_TAC)
      >- (
        qexists_tac `j` >>
        rw []
        >- intLib.ARITH_TAC >>
        `i - 1 = &k ∨ &k < i - 1` by intLib.ARITH_TAC >>
        rw [] >>
        fs [] >>
        rfs []))
    >- (
      xvar >>
      xsimpl >>
      qexists_tac `n` >>
      fs [] >>
      rw []
      >- intLib.ARITH_TAC >>
      `i ≤ &k` by intLib.ARITH_TAC >>
      fs [] >>
      CCONTR_TAC >>
      intLib.ARITH_TAC)) >>
  cheat);

  (*
  xfun_spec `part_loop`
    `∀lower lower_v upper upper_v elem_vs.
      INT lower lower_v ∧ INT upper upper_v ∧
      lower < upper ∧ -1 ≤ lower ∧ upper ≤ &(LENGTH elem_vs) ∧
      (?stop_v1. MEM stop_v1 (SEG (Num (upper-lower)) (Num (lower + 1)) elem_vs)) ∧
      (?stop_v2. MEM stop_v2 (SEG (Num (upper-lower)) (Num (lower + 1)) elem_vs)) ∧
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "partition" partition_st)
      [lower_v; upper_v]
      (ARRAY arr_v elem_vs)
      (POSTv p_v. SEP_EXISTS elem_vs1 elem_vs2.
        ARRAY arr_v (elem_vs1++elem_vs2) *
        &(∃elems1 elems2.
            elem_vs1 ≠ [] ∧ elem_vs2 ≠ [] ∧
            INT (&LENGTH elem_vs1 - 1) p_v ∧
            PERM elem_vs (elem_vs1 ++ elem_vs2) ∧
            LIST_REL a elems1 elem_vs1 ∧
            LIST_REL a elems2 elem_vs2 ∧
            EVERY (\e. ¬cmp pivot e) elems1 ∧
            EVERY (\e. ¬cmp e pivot) elems2))`,

  *)

val quicksort = process_topdecs `
fun quicksort cmp a =
let
  fun quicksort_help lower upper =
    if lower = upper then
      ()
    else
      let
        val p = partition cmp a (Array.sub a lower) lower upper
      in
        (quicksort_help lower p;
         quicksort_help (p + 1) upper)
      end
in
  let val l = Array.length a in
    if l = 0 then () else quicksort_help 0 (l - 1)
  end
end;
`;
val quicksort_st = ml_progLib.add_prog quicksort pick_name partition_st;

val quicksort_spec = Q.store_thm ("quicksort_spec",
  `!ffi_p cmp cmp_v arr_v elem_vs elems.
    (* The comparison function is a strict partial order over a *)
    transitive cmp ∧
    (!x y. cmp x y ⇒ ~cmp y x) ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    (* The elements of the array are all of "semantic type" a *)
    LIST_REL a elems elem_vs
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "quicksort" quicksort_st)
      [cmp_v; arr_v]
      (* The array argument is in the heap with contents elem_vs *)
      (ARRAY arr_v elem_vs)
      (* Quicksort terminates *)
      (POSTv u.
        SEP_EXISTS elem_vs'.
          (* The array argument is in the heap with contents elem_vs *)
          ARRAY arr_v elem_vs' *
          (* Those contents permute the original contents *)
          &(PERM elem_vs' elem_vs) *
          (* The new contents all have semantic type a and are sorted *)
          &(?elems'.
              LIST_REL a elems' elem_vs' ∧
              (* We use "not greater than" as equivalent to "less or equal" *)
              SORTED (\x y. ¬(cmp y x)) elems'))`,
  xcf "quicksort" quicksort_st >>
  (* The loop invariant for the main loop. Note that we have to quantify over
   * what's in the array because it changes on the recursive calls. *)
  xfun_spec `quicksort_help`
    `!lower upper lower_v upper_v perm_elems perm_elem_vs elem_vs1 elem_vs2 elem_vs3.
      (* The array has elements of type a *)
      LIST_REL a perm_elems perm_elem_vs ∧
      (* The indices must point to array elements, with lower before upper *)
      INT (&lower) lower_v ∧ INT (&upper) upper_v ∧
      lower ≤ upper ∧ upper < LENGTH perm_elem_vs ∧
      (* We split the elements into those before lower, those we are sorting
       * and those after upper *)
      (elem_vs1, elem_vs2, elem_vs3) = split_list lower upper perm_elem_vs
      ⇒
      app ffi_p quicksort_help
        [lower_v; upper_v]
        (ARRAY arr_v perm_elem_vs)
        (* The loop terminates and has sorted the sub-array between lower and
         * upper *)
        (POSTv u.
          SEP_EXISTS sorted_vs.
            ARRAY arr_v (elem_vs1 ++ sorted_vs ++ elem_vs3) *
            &(PERM sorted_vs elem_vs2) *
            &(?sorted.
                LIST_REL a sorted sorted_vs ∧
                SORTED (\x y. ¬(cmp y x)) sorted))`
  >- (
    (* Prove the loop invariant, by induction on how big the segment to sort is *)
    ntac 2 gen_tac >>
    completeInduct_on `upper - lower` >>
    rw [] >>
    `lower = upper ∨ lower < upper` by decide_tac
    >- (
      (* A single element segment array *)
      fs [] >>
      xapp >>
      rw [] >>
      xlet `POSTv b_v. &(BOOL T b_v) * ARRAY arr_v perm_elem_vs`
      >- (
        xapp >>
        xsimpl >>
        fs [BOOL_def, INT_def]) >>
      xif >>
      qexists_tac `T` >>
      rw [] >>
      xret >>
      xsimpl >>
      `elem_vs1 ++ elem_vs2 ++ elem_vs3 = perm_elem_vs`
      by (
        irule split_list_append >>
        qexists_tac `lower` >>
        qexists_tac `lower` >>
        rw []) >>
      drule split_list_same >>
      rw [] >>
      fs [] >>
      qexists_tac `[EL lower perm_elems]` >>
      rw [] >>
      fs [LIST_REL_EL_EQN] >>
      metis_tac []) >>
    (* Get the code of the loop *)
    last_x_assum irule >>
    xlet `POSTv b_v. &(BOOL F b_v) * ARRAY arr_v perm_elem_vs`
    >- (
      xapp >>
      xsimpl >>
      fs [BOOL_def, INT_def]) >>
    xif >>
    qexists_tac `F` >>
    rw [] >>
    (* Get the pivot *)
    xlet `POSTv pivot_v. ARRAY arr_v perm_elem_vs * &(pivot_v = EL lower perm_elem_vs)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `lower` >>
      fs [NUM_def, INT_def]) >>
    (* The post-condition of partition *)
    xlet
      `POSTv p_v. SEP_EXISTS pivot part1 part2.
        (* The array is still in the heap, with elements that form a partition,
         * of the part between lower and upper. Elements outside the lower-upper
         * range are left unchanged. *)
        ARRAY arr_v (elem_vs1 ++ part1 ++ part2 ++ elem_vs3) *
        &(partition_pred a cmp pivot lower p_v elem_vs2 part1 part2)`
    >- (
      (* Show that we meet partition's assumptions *)
      xapp >>
      xsimpl >>
      MAP_EVERY qexists_tac [`EL lower perm_elems`, `lower`, `elem_vs3`, `elem_vs2`,
                             `elem_vs1`, `cmp`, `a`, `upper`, `perm_elems`] >>
      simp [] >>
      fs [LIST_REL_EL_EQN] >>
      rw [MEM_EL]
      >- (
        (* The pivot is in the right part of the array *)
        qexists_tac `0` >>
        `LENGTH elem_vs2 = upper - lower + 1 ∧
         LENGTH elem_vs1 = lower ∧
         perm_elem_vs = elem_vs1++elem_vs2++elem_vs3`
        by (
          `lower ≤ upper` by decide_tac >>
          metis_tac [split_list_length, split_list_append]) >>
        simp [] >>
        `elem_vs2 ≠ []`
        by (
          Cases_on `elem_vs2` >>
          fs []) >>
        rw [LENGTH_FRONT]
        >- decide_tac >>
        Cases_on `elem_vs2` >>
        fs [] >>
        Cases_on `t` >>
        fs [] >>
        simp [EL_APPEND_EQN])
      >- metis_tac []) >>
    fs [partition_pred_def] >>
    `LENGTH elem_vs2 = upper - lower + 1 ∧
     LENGTH elem_vs1 = lower ∧
     LENGTH elem_vs3 = LENGTH perm_elem_vs - upper - 1 ∧
     perm_elem_vs = elem_vs1++elem_vs2++elem_vs3`
    by (
      `lower ≤ upper` by decide_tac >>
      metis_tac [split_list_length, split_list_append]) >>
    drule PERM_LENGTH >>
    rw [] >>
    fs [GSYM LENGTH_NIL] >>
    (* The first recursive call sorts the lower partition *)
    xlet
      `POSTv u.
         SEP_EXISTS sorted_vs1.
           ARRAY arr_v (elem_vs1 ++ sorted_vs1 ++ part2 ++ elem_vs3) *
           &(PERM sorted_vs1 part1) *
           &(?sorted1.
               LIST_REL a sorted1 sorted_vs1 ∧
               SORTED (\x y. ¬(cmp y x)) sorted1)`
    >- (
      first_x_assum (qspec_then `LENGTH part1 - 1` mp_tac) >>
      impl_keep_tac
      >- decide_tac >>
      disch_then (qspecl_then [`LENGTH elem_vs1+LENGTH part1 − 1`, `LENGTH elem_vs1`] mp_tac) >>
      impl_keep_tac
      >- decide_tac >>
      disch_then xapp_spec >>
      xsimpl >>
      MAP_EVERY qexists_tac [`part2++elem_vs3`, `part1`, `elem_vs1`] >>
      rw [GSYM PULL_EXISTS]
      >- metis_tac [APPEND_ASSOC, split_list_combine]
      >- simp [int_arithTheory.INT_NUM_SUB]
      >- cheat) >>
    xlet `POSTv upper_v2. ARRAY arr_v (elem_vs1++sorted_vs1++part2++elem_vs3) *
              &(INT (&(LENGTH elem_vs1 + LENGTH part1)) upper_v2)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def]) >>
    (* The second recursive call sorts the upper partition, and that should
     * leave the whole list between lower and upper sorted. *)
    first_x_assum (qspec_then `LENGTH part2 - 1` mp_tac) >>
    impl_keep_tac
    >- decide_tac >>
    disch_then (qspecl_then [`upper`, `LENGTH part1+LENGTH elem_vs1`] mp_tac) >>
    impl_keep_tac
    >- decide_tac >>
    (* Don't do this, because we need to establish the post condition of the
     * recursive call, and then show that it implies the post conditioon of the
     * function overall, even thought there isn't any more computation to do.
      disch_then xapp_spec >>*)
    disch_then (qspecl_then [`upper_v2`, `upper_v`, `XXX`,
           `elem_vs1 ++ sorted_vs1++part2 ++ elem_vs3`, `elem_vs1++sorted_vs1`,
           `part2`, `elem_vs3`] mp_tac) >>
    simp [] >>
    impl_tac
    >- (
      rw [] >>
      cheat) >>
    disch_then xapp_spec >>
    xsimpl >>
    rw []
    >- (
      `PERM (part1++part2) (sorted_vs1++x)`
      suffices_by metis_tac [PERM_SYM, PERM_TRANS] >>
      metis_tac [PERM_SYM, PERM_CONG])
    >- (
      qexists_tac `sorted1 ++ sorted` >>
      rw []
      >- metis_tac [EVERY2_APPEND, LIST_REL_LENGTH] >>
      rw [SORTED_APPEND_IFF] >>
      CCONTR_TAC >>
      fs [] >>
      cheat)) >>
  (* Make the initial call to the sorting loop, unless the array is empty *)
  xlet `POSTv len_v. ARRAY arr_v elem_vs * &INT (&LENGTH elem_vs) len_v`
  >- (
    xapp >>
    xsimpl >>
    simp [NUM_def, INT_def]) >>
  xlet `POSTv b_v. ARRAY arr_v elem_vs * &BOOL (LENGTH elem_vs = 0) b_v`
  >- (
    xapp >>
    xsimpl >>
    fs [NUM_def, BOOL_def, INT_def]) >>
  xif
  >- (
    xret >>
    xsimpl >>
    fs [LENGTH_NIL]) >>
  xlet `POSTv len_v1. ARRAY arr_v elem_vs * &INT (&(LENGTH elem_vs - 1)) len_v1`
  >- (
    xapp >>
    xsimpl >>
    fs [INT_def, int_arithTheory.INT_NUM_SUB]) >>
  first_x_assum xapp_spec >>
  xsimpl >>
  MAP_EVERY qexists_tac [`[]`, `elem_vs`, `[]`, `LENGTH elem_vs - 1`, `elems`] >>
  rw [] >>
  qpat_abbrev_tac `l = split_list _ _ _` >>
  PairCases_on `l` >>
  rw [] >>
  `0 ≤ LENGTH elem_vs -1 ∧ LENGTH elem_vs - 1 < LENGTH elem_vs` by decide_tac >>
  `l0++l1++l2 = elem_vs` by metis_tac [split_list_append] >>
  `LENGTH elem_vs - (LENGTH elem_vs - 1) - 1 = 0` by decide_tac >>
  `LENGTH l0 = 0 ∧ LENGTH l2 = 0` by metis_tac [split_list_length] >>
  fs [LENGTH_NIL]);

val my_cmp = process_topdecs `
fun my_cmp (x1,y1) (x2,y2) =
  (log := log + 1;
   !x1 < !x2);
`;
val my_cmp_st = ml_progLib.add_prog my_cmp pick_name quicksort_st;

val example_sort = process_topdecs `
val sorted =
  quicksort my_cmp
  (fromList [(ref 0, 1), (ref 1, 2), (ref 0, 3), (ref 2, 4), (ref 1, 5)])
`;
val example_sort_st = ml_progLib.add_prog my_cmp pick_name my_cmp_st;


val example_sorted_correct = Q.store_thm ("example_sorted_correct",
  

val _ = export_theory ();

