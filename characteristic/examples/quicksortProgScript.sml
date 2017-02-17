open preamble;
open semanticPrimitivesTheory;
open ml_translatorTheory ml_translatorLib ml_progLib;
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib;
open basisFunctionsLib;
open mlarrayProgTheory;

val _ = new_theory "quicksortProg";

val _ = translation_extends"mlarrayProg";

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

(*

val partition_spec = Q.store_thm ("partition_spec",

  `!a ffi_p cmp cmp_v arr_v elem_vs pivot pivot_v lower lower_v upper upper_v.
    (* Partition takes two integers, and a comparison function of "semantic
     * type" a -> a -> bool *)
    INT lower lower_v ∧ INT upper upper_v ∧ (a --> a --> BOOL) cmp cmp_v ∧
    (* It also takes a pivot of semantic type a *)
    a pivot pivot_v ∧
    (* The integers must point to array elements, with lower before upper *)
    lower < upper ∧ 0 ≤ lower ∧ upper < &(LENGTH elem_vs) ∧
    (* The pivot must be in the array elements, other than at the last element.
     * This ensures that neither side of the partition is empty. *)
    MEM pivot_v (FRONT elem_vs) ∧
    (* The comparison function is a strict partial order *)
    transitive cmp ∧ (!x y. cmp x y ⇒ ~cmp y x)
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "partition" partition_st)
      [cmp_v; arr_v; pivot_v; lower_v; upper_v]
      (* The array argument is in the heap with contents elem_vs *)
      (ARRAY arr_v elem_vs)
      (* The partition function returns with a index p_v into the array *)
      (POSTv p_v. SEP_EXISTS elem_vs1 elem_vs2.
        (* The array is still in the heap, with elements that form a partition *)
        ARRAY arr_v (elem_vs1++elem_vs2) *
        &((* Neither part is empty *)
          elem_vs1 ≠ [] ∧ elem_vs2 ≠ [] ∧
          (* The returned index points to the end of the first partition *)
          INT (&LENGTH elem_vs1 - 1) p_v ∧
          (* The partition permutes the original array *)
          PERM elem_vs (elem_vs1 ++ elem_vs2)) *
        &(∃elems1 elems2.
           (* The elements of the first part aren't greater than the pivot *)
            LIST_REL a elems1 elem_vs1 ∧
            EVERY (\e. ¬cmp pivot e) elems1 ∧
            (* The elements of the second part aren't less than the pivot *)
            LIST_REL a elems2 elem_vs2 ∧
            EVERY (\e. ¬cmp e pivot) elems2))`,

  xcf "partition" partition_st >>
  xfun_spec `scan_lower`
    `!i elems i_v.
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
    ntac 2 gen_tac >>
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
    `!i i_v elems.
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
      qexists_tac `elems` >>
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
        val p = partition cmp a (sub a lower) lower upper
      in
        (quicksort_help lower p;
         quicksort_help (p + 1) upper)
      end
in
  quicksort_help 0 (Array.length a - 1)
end;
`;
val quicksort_st = ml_progLib.add_prog quicksort pick_name partition_st;

(*
val quicksort_spec = Q.store_thm ("quicksort_spec",
  `!ffi_p cmp cmp_v arr_v elem_vs elems.
    LIST_REL a elems elem_vs ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    transitive cmp
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "quicksort" quicksort_st)
      [cmp_v; arr_v]
      (ARRAY arr_v elem_vs)
      (POSTv u.
        SEP_EXISTS elem_vs'.
          ARRAY arr_v elem_vs' *
          &(PERM elem_vs' elem_vs) *
          &(?elems'.
              LIST_REL a elems' elem_vs' ∧
              SORTED (\x y. ¬(cmp y x)) elems'))`,

  xcf "quicksort" quicksort_st >>
  xfun_spec `quicksort_help`
    `!lower upper lower_v upper_v elems elem_vs.
      INT (&lower) lower_v ∧ INT (&upper) upper_v ∧
      lower ≤ upper ∧ upper < LENGTH elem_vs ∧
      LIST_REL a elems elem_vs
      ⇒
      app ffi_p quicksort_help
        [lower_v; upper_v]
        (ARRAY arr_v elem_vs)
        (POSTv u.
          SEP_EXISTS elem_vs'.
            ARRAY arr_v (SEG lower 0 elem_vs ++
                         elem_vs' ++
                         SEG (LENGTH elem_vs - upper + 1) (upper + 1) elem_vs) *
            &(PERM elem_vs' (SEG (upper - lower + 1) lower elem_vs)) *
            &(?elems'.
                LIST_REL a elems' elem_vs' ∧
                SORTED (\x y. ¬(cmp y x)) elems'))`

  >- (
    ntac 2 gen_tac >>
    completeInduct_on `upper - lower` >>
    rw [] >>
    `lower = upper ∨ lower < upper` by decide_tac
    >- (
      fs [] >>
      xapp >>
      rw [] >>
      xlet `POSTv b_v. &(BOOL T b_v) * ARRAY arr_v elem_vs'`
      >- (
        xapp >>
        xsimpl >>
        fs [BOOL_def, INT_def]) >>
      xif >>
      qexists_tac `T` >>
      rw [] >>
      xret >>
      xsimpl >>
      qexists_tac `(SEG 1 lower elem_vs')` >>
      rw []
      >- (
        qexists_tac `SEG 1 lower elems'` >>
        rw []
        >- cheat >>
        cheat) >>
      cheat) >>
    first_x_assum irule >>
    xlet `POSTv b_v. &(BOOL F b_v) * ARRAY arr_v elem_vs'`
    >- (
      xapp >>
      xsimpl >>
      fs [BOOL_def, INT_def]) >>
    xif >>
    qexists_tac `F` >>
    rw [] >>
    xlet `POSTv pivot_v. ARRAY arr_v elem_vs' * &(MEM pivot_v elem_vs')`
    >- cheat >>
    xlet `(POSTv p_v. SEP_EXISTS elem_vs1 elem_vs2.
             ARRAY arr_v (elem_vs1++elem_vs2) *
             &(∃elems1 elems2.
                 PERM elem_vs (elem_vs1 ++ elem_vs2) ∧
                 LIST_REL a elems1 elem_vs1 ∧
                 LIST_REL a elems2 elem_vs2 ∧
                 EVERY (\e. ¬cmp pivot e) elems1 ∧
                 EVERY (\e. ¬cmp e pivot) elems2))`
    >- (
      xapp >>
      xsimpl >>

      *)

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

