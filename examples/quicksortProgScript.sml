(*
  In-place quick sort on a polymorphic array.
*)
open preamble semanticPrimitivesTheory
open ml_translatorTheory ml_translatorLib ml_progLib cfLib basisFunctionsLib
open basisProgTheory ArrayProofTheory

val _ = new_theory "quicksortProg";

val _ = translation_extends"basisProg";

(* TODO: move *)

val list_rel_perm_help = Q.prove (
  `!l1 l2.
    PERM l1 l2
    ⇒
    !l3 l4.
      LIST_REL r (MAP FST l1) (MAP SND l1)
      ⇒
      LIST_REL r (MAP FST l2) (MAP SND l2)`,
  ho_match_mp_tac PERM_IND >>
  rw []);

Theorem list_rel_perm:
   !r l1 l2 l3 l4.
    LENGTH l3 = LENGTH l4 ∧
    LIST_REL r l1 l2 ∧
    PERM (ZIP (l1,l2)) (ZIP (l3,l4))
    ⇒
    LIST_REL r l3 l4
Proof
  rw [] >>
  drule list_rel_perm_help >>
  imp_res_tac LIST_REL_LENGTH >>
  rw [MAP_ZIP]
QED

val split_list = Q.prove (
  `!l x. x < LENGTH l ⇒ ?l1 l2. x = LENGTH l1 ∧ l = l1++[EL x l]++l2`,
  induct_on `l` >>
  rw [] >>
  Cases_on `x` >>
  fs [] >>
  metis_tac [APPEND, LENGTH]);

val split_list2 = Q.prove (
  `!l1 l2 l3 l4.
    LENGTH l1 < LENGTH l3 ∧ l1++l2 = l3++l4
    ⇒
    ?l1'. l3 = l1++l1'`,
  induct_on `l1` >>
  rw [] >>
  Cases_on `l3` >>
  fs [] >>
  metis_tac []);

val perm_swap_help = Q.prove (
  `!l x y.
    x < LENGTH l ∧ y < LENGTH l ∧ y < x
    ⇒
    PERM l (LUPDATE (EL x l) y (LUPDATE (EL y l) x l))`,
  rw [] >>
  `?l1 l2. LENGTH l1 = x ∧ l = l1++[EL x l]++l2`
  by metis_tac [split_list] >>
  qabbrev_tac `ex = EL x l` >>
  rw [lupdate_append2] >>
  pop_assum kall_tac >>
  qabbrev_tac `l' = l1 ++ [EL y (l1 ++ [ex] ++ l2)] ++ l2` >>
  `y < LENGTH l'` by fs [Abbr `l'`] >>
  `?l1' l2'. LENGTH l1' = y ∧ l' = l1'++[EL y l']++l2'`
  by metis_tac [split_list] >>
  qabbrev_tac `ey = EL y l'` >>
  rw [lupdate_append2] >>
  pop_assum kall_tac >>
  fs [markerTheory.Abbrev_def] >>
  simp [PERM_alt] >>
  rw [] >>
  `?l1''. l1 = l1'++l1''` by metis_tac [split_list2, APPEND_ASSOC] >>
  rw [] >>
  fs [FILTER_APPEND, EL_APPEND_EQN] >>
  Cases_on `l1''` >>
  fs [] >>
  rw [FILTER_APPEND]);

Theorem perm_swap:
   !l x y.
    x < LENGTH l ∧ y < LENGTH l
    ⇒
    PERM l (LUPDATE (EL x l) y (LUPDATE (EL y l) x l))
Proof
  rw [] >>
  `x < y ∨ y < x ∨ x = y` by decide_tac >>
  rw [] >>
  metis_tac [perm_swap_help, LUPDATE_commutes , PERM_REFL, LUPDATE_SAME]
QED

Theorem lupdate_zip:
   !l1 l2 x y n.
    LENGTH l1 = LENGTH l2 ∧ n < LENGTH l1 ⇒
    LUPDATE (x,y) n (ZIP (l1,l2)) =
    ZIP (LUPDATE x n l1, LUPDATE y n l2)
Proof
  induct_on `n` >>
  rw [] >>
  Cases_on `l1` >>
  Cases_on `l2` >>
  fs [LUPDATE_def]
QED

val el_append_length1 = Q.prove (
  `!n l1 l2. EL (n + LENGTH l1) (l1 ++ l2) = EL n l2`,
  Induct_on `l1` >>
  rw [EL_CONS] >>
  `PRE (n + SUC (LENGTH l1)) = n + LENGTH l1` by decide_tac >>
  metis_tac []);

Theorem front_zip:
   !l1 l2.
    l1 ≠ [] ∧ LENGTH l1 = LENGTH l2 ⇒
    FRONT (ZIP (l1,l2)) = ZIP (FRONT l1, FRONT l2)
Proof
  Induct_on `l1` >>
  rw [] >>
  Cases_on `l2` >>
  fs [] >>
  Cases_on `l1` >>
  Cases_on `t` >>
  fs [] >>
  first_x_assum (qspec_then `h'''::t''` mp_tac) >>
  rw []
QED

val strict_weak_order_def = Define `
  strict_weak_order r ⇔
    transitive r ∧
    (!x y. r x y ⇒ ~r y x) ∧
    transitive (\x y. ~r x y ∧ ¬r y x)`;

Theorem strict_weak_order_alt:
   strict_weak_order r ⇔
    (!x y. r x y ⇒ ~r y x) ∧
    transitive (\x y. ~r y x)
Proof
  rw [strict_weak_order_def, transitive_def] >>
  metis_tac []
QED

Theorem sing_length1:
   !l. LENGTH l = 1 ⇔ ?x. l = [x]
Proof
  Cases >>
  rw [LENGTH_NIL]
QED

Theorem length_gt1:
   !l. LENGTH l > 1 ⇒ ?x y z. l = x::y::z
Proof
  Cases >>
  rw [] >>
  Cases_on `t` >>
  fs []
QED

(* -- *)

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
val _ = append_prog partition;

val partition_pred_def = Define `
  partition_pred cmp offset p_v pivot elems elem_vs part1 part2 ⇔
    (* Neither part is empty *)
    part1 ≠ [] ∧ part2 ≠ [] ∧
    (* The returned index points to the end of the first partition *)
    INT (&(offset + LENGTH part1 - 1)) p_v ∧
    (* The partitions permute the array. Note that we need to
     * get the corresponding permutation on the shallowly embedded side
     * too. That's what the ZIP is for, to uniquely determine elems1 and elems2. *)
    ∃elems1 elems2.
      LENGTH elems1 = LENGTH part1 ∧
      LENGTH elems2 = LENGTH part2 ∧
      PERM (ZIP (elems,elem_vs)) (ZIP (elems1++elems2,part1++part2)) ∧
      (* The elements of the first part aren't greater than the pivot *)
      EVERY (\e. ¬cmp pivot e) elems1 ∧
      (* The elements of the second part aren't less than the pivot *)
      EVERY (\e. ¬cmp e pivot) elems2`;

val perm_helper = Q.prove(
  `!a b c. PERM b c ∧ PERM a b ⇒ PERM a c`,
  metis_tac [PERM_SYM, PERM_TRANS]);

Theorem partition_spec:
   !a ffi_p cmp cmp_v arr_v pivot pivot_v lower_v upper_v elem_vs1 elem_vs2 elem_vs3 elems2.
    strict_weak_order cmp ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    (* We split the array into 3 parts. The second must have elements of type
     * a and be non-empty. *)
    LIST_REL a elems2 elem_vs2 ∧
    elem_vs2 ≠ [] ∧
    (* The lower index must point to the beginning of elem_vs2, and the upper
     * to its end *)
    INT (&LENGTH elem_vs1) lower_v ∧
    INT (&(LENGTH elem_vs1 + LENGTH elem_vs2 - 1)) upper_v ∧
    (* The pivot must be in the middle part, but not at the end. This ensures
     * that neither side of the partition is empty. Use the ZIP to get the
     * shallowly embedded version of the pivot at the same time. *)
    MEM (pivot,pivot_v) (FRONT (ZIP (elems2,elem_vs2)))
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "partition" (basis_st()))
      (* The arguments *)
      [cmp_v; arr_v; pivot_v; lower_v; upper_v]
      (* The array argument is in the heap with contents of the 3 parts *)
      (ARRAY arr_v (elem_vs1 ++ elem_vs2 ++ elem_vs3))
      (* The partition function returns with a index p_v into the array *)
      (POSTv p_v. SEP_EXISTS part1 part2.
        (* The array is still in the heap, with the middle part partitioned. *)
        ARRAY arr_v (elem_vs1 ++ part1 ++ part2 ++ elem_vs3) *
        &(partition_pred cmp (LENGTH elem_vs1) p_v pivot elems2 elem_vs2 part1 part2))
Proof
  xcf "partition" (basis_st()) >>
  qmatch_assum_abbrev_tac `INT (&lower) lower_v` >>
  qmatch_assum_abbrev_tac `INT (&upper) upper_v` >>
  `a pivot pivot_v`
  by (
    Cases_on `elems2` >>
    Cases_on `elem_vs2` >>
    fs [] >>
    drule MEM_FRONT >>
    rw [] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH >>
    fs [MEM_ZIP] >>
    metis_tac [LIST_REL_EL_EQN]) >>
  xfun_spec `scan_lower`
    (* We split the array into 3 pieces. We work on the middle one. *)
    `!i elems i_v elem_vs ignore1 ignore2.
      (* scan_lower takes an integer i, where i+1 indexes into the middle
       * section. *)
      INT (&LENGTH ignore1 + i) i_v ∧ -1 ≤ i ∧ i + 1 < &(LENGTH elems) ∧
      (* There is an array index after i where the element is not less than the
       * pivot. This ensures termination before hitting the end of the middle
       * array piece. *)
      (?x:num. i < (&x) ∧ x < LENGTH elems ∧ ¬cmp (EL x elems) pivot) ∧
      (* The elements of the array have semantic type a *)
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_lower
        [i_v]
        (* The array argument is in the heap with contents elem_vs *)
        (ARRAY arr_v (ignore1++elem_vs++ignore2))
        (* The scan terminates with an resulting index j *)
        (POSTv (j_v:v).
          (* The array argument is still in the heap unchanged *)
          (ARRAY arr_v (ignore1++elem_vs++ignore2)) *
          &(∃j:num.
             (* The index increased, and did not run off the end *)
             INT (&(LENGTH ignore1 + j)) j_v ∧ i < (&j) ∧ j < LENGTH elems ∧
             (* The result index j points to an element not smaller than the
              * pivot *)
             ¬cmp (EL j elems) pivot ∧
             (* Everything is smaller than the pivot between where the scan
              * started and finished *)
             !k:num. i < (&k) ∧ k < j ⇒ cmp (EL k elems) pivot))`
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
    xlet `POSTv j_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
            &(?j. INT (&LENGTH ignore1 + j) j_v ∧ j = i + 1)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def] >>
      intLib.ARITH_TAC) >>
    `?n:num. i+1 = &n`
    by (
      `i + 1 = 0 ∨ 0 < i + 1` by intLib.ARITH_TAC >>
      rw [] >>
      qexists_tac `Num (i+1)` >>
      intLib.ARITH_TAC) >>
    xlet `POSTv x_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
            &(a (EL (Num (i+1)) elems) x_v)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `LENGTH ignore1 + n` >>
      fs [NUM_def, LIST_REL_EL_EQN, integerTheory.INT_ADD] >>
      simp [EL_APPEND_EQN]) >>
    xlet `POSTv b_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
              &(BOOL (cmp (EL (Num (i + 1)) elems) pivot) b_v)`
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
      rw [] >>
      MAP_EVERY qexists_tac [`ignore2`, `ignore1`, `elem_vs`] >>
      simp [] >>
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
        rfs [strict_weak_order_def] >>
        metis_tac []))
    >- (
      xvar >>
      xsimpl >>
      qexists_tac `n` >>
      fs [] >>
      rw []
      >- metis_tac [integerTheory.INT_ADD, integerTheory.INT_ADD_SYM]
      >- intLib.ARITH_TAC >>
      `i+1 < &n` by intLib.ARITH_TAC >>
      rfs [])) >>
  xfun_spec `scan_upper`
    (* Similar to the scan_lower invariant, except that i-1 indexes the array,
     * and we scan down passing over elements bigger thatn the pivot *)
    `!i elems i_v elem_vs ignore1 ignore2.
      INT (&LENGTH ignore1 + i) i_v ∧ 0 ≤ i - 1 ∧ i ≤ &(LENGTH elems) ∧
      (?x:num. (&x) < i ∧ ¬cmp pivot (EL x elems)) ∧
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_upper
        [i_v]
        (ARRAY arr_v (ignore1++elem_vs++ignore2))
        (POSTv (j_v:v).
          (ARRAY arr_v (ignore1++elem_vs++ignore2)) *
          &(∃j:num.
             INT (&(LENGTH ignore1 + j)) j_v ∧ (&j) < i ∧ 0 ≤ j ∧
             ¬cmp pivot (EL j elems) ∧
             !k:num. (&k) < i ∧ j < k ⇒ cmp pivot (EL k elems)))`
  >- (
    (* Prove that scan upper has the above invariant. Similar to the scan lower
     * proof above *)
    ntac 2 gen_tac >>
    Induct_on `Num i` >>
    rw []
    >- (
      `i = 0` by intLib.ARITH_TAC >>
      fs []) >>
    last_x_assum xapp_spec >>
    xlet `POSTv j_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
             &(?j. INT (&LENGTH ignore1 + j) j_v ∧ j = i - 1)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def] >>
      intLib.ARITH_TAC) >>
    `?n:num. i-1 = &n`
    by (
      `i - 1 = 0 ∨ 0 < i - 1` by intLib.ARITH_TAC >>
      rw [] >>
      qexists_tac `Num (i-1)` >>
      intLib.ARITH_TAC) >>
    xlet `POSTv x_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
              &(a (EL (Num (i-1)) elems) x_v)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `LENGTH ignore1 + n` >>
      fs [NUM_def, LIST_REL_EL_EQN] >>
      `n < LENGTH elem_vs` by intLib.ARITH_TAC >>
      rw [GSYM integerTheory.INT_ADD, EL_APPEND_EQN] >>
      metis_tac [integerTheory.INT_ADD_SYM]) >>
    xlet `POSTv b_v. ARRAY arr_v (ignore1++elem_vs++ignore2) *
             &(BOOL (cmp pivot (EL (Num (i - 1)) elems)) b_v)`
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
      rw [] >>
      MAP_EVERY qexists_tac [`ignore2`, `ignore1`, `elem_vs`] >>
      rw []
      >- (
        qexists_tac `x` >>
        simp [] >>
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
        rfs [strict_weak_order_def]))
    >- (
      xvar >>
      xsimpl >>
      qexists_tac `n` >>
      fs [] >>
      rw []
      >- metis_tac [integerTheory.INT_ADD, integerTheory.INT_ADD_SYM]
      >- intLib.ARITH_TAC >>
      `i ≤ &k` by intLib.ARITH_TAC >>
      fs [] >>
      CCONTR_TAC >>
      intLib.ARITH_TAC)) >>
  (* Don't know why the previous xfun_spec expanded ARRAY_def. Probably a CFBUG *)
  `(SEP_EXISTS loc.
     (λs.
        ∃v.
          v ⊆ s ∧ s ⊆ v ∧ arr_v = Loc loc ∧
          v ⊆ {Mem loc (Varray (elem_vs1 ++ elem_vs2 ++ elem_vs3))} ∧
          Mem loc (Varray (elem_vs1 ++ elem_vs2 ++ elem_vs3)) ∈ v))
    =
    ARRAY arr_v (elem_vs1++elem_vs2++elem_vs3)`
   by (
     rw [cfHeapsBaseTheory.ARRAY_def, SEP_EXISTS_THM, STAR_def,
         EXTENSION, SUBSET_DEF, DISJOINT_DEF, SPLIT_def, IN_DEF,
         one_def, cfHeapsBaseTheory.cell_def, cfHeapsBaseTheory.REF_def] >>
     simp [PULL_EXISTS, PULL_FORALL, cond_def, EQ_IMP_THM] >>
     rw []
     >- (
       qexists_tac `loc` >>
       qexists_tac `{}` >>
       simp [] >>
       metis_tac [])
     >- (
       qexists_tac `loc'` >>
       qexists_tac `v'` >>
       rw [] >>
       first_x_assum (qspecl_then [`x''`, `x''`, `x''`] mp_tac) >>
       simp [] >>
       rw [] >>
       fs [])) >>
  simp [] >>
  xfun_spec `part_loop`
   (* Partition the part of the array, middle_vs, between two pointers. The
    * pointers point to before and after the part to be partitioned, even if
    * that makes them out of bounds. Also, when part_loop is first called, the
    * pivot will be in middle_vs, but on subsequent iterations it might not be,
    * so we have to separate out the previously partitioned parts, lower_part
    * and upper_part and remember that they contain values that will stop the
    * traversal in case a pointer runs off of middle_vs. Lastly, on the first
    * iteration, if the pointers cross, and the upper part is empty, the we are
    * putting all of the elements in the lower part. We need to know that there
    * is a lower blocker before the last element of the middle to stop this
    * situation. But on subsequent iterations, there might not be such a
    * blocker. However, by then the upper part is not empty. *)
   `!middle_vs l_v u_v ignore1 lower_part upper_part ignore2 elems1 elems2 elems3.
    (* The already partitioned parts, and the middle part. *)
    LIST_REL a elems1 lower_part ∧
    LIST_REL a elems2 middle_vs ∧
    LIST_REL a elems3 upper_part ∧
    (* The lower pointer points to the last element of lower_part *)
    INT (&(LENGTH (ignore1 ++ lower_part)) - 1) l_v ∧
    (* The upper pointer points to the first element of upper_part *)
    INT (&LENGTH (ignore1 ++ lower_part ++ middle_vs)) u_v ∧
    EVERY (\e. ¬cmp pivot e) elems1 ∧
    EVERY (\e. ¬cmp e pivot) elems3 ∧
    (* There is an element in the middle and upper that will stop scan lower *)
    EXISTS (\e. ¬cmp e pivot) (elems2 ++ elems3) ∧
    (* There is an element in the lower and middle that will stop scan upper *)
    EXISTS (\e. ¬cmp pivot e) (elems1 ++ elems2) ∧
    (* We need at least two elements to get two non-empty partitions *)
    1 < LENGTH (lower_part ++ middle_vs ++ upper_part) ∧
    (* If the upper part is empty, there is a blocker for the lower part to
     * prevent the pointers crossing on the first iteration and giving an empty
     * partition. *)
    (upper_part = [] ⇒ elems2 ≠ [] ∧ EXISTS (\e. ¬cmp e pivot) (FRONT elems2))
    ⇒
    app (ffi_p:'ffi ffi_proj) part_loop
      [l_v; u_v]
      (ARRAY arr_v (ignore1 ++ lower_part ++ middle_vs ++ upper_part ++ ignore2))
      (* The array has new lower and upper partitions with no more in the middle *)
      (POSTv p_v. SEP_EXISTS lower_part' upper_part'.
        ARRAY arr_v (ignore1 ++ lower_part' ++ upper_part' ++ ignore2) *
        &(partition_pred cmp (LENGTH ignore1)
            p_v pivot (elems1++elems2++elems3)
            (lower_part++middle_vs++upper_part)
            lower_part' upper_part'))`
  >- (
    gen_tac >>
    completeInduct_on `LENGTH middle_vs` >>
    gen_tac >>
    strip_tac >>
    rpt gen_tac >>
    qpat_abbrev_tac `upper_stop = elem1++elems2'` >>
    qpat_abbrev_tac `lower_stop = elem2'++elems3` >>
    rw [] >>
    last_x_assum xapp_spec >>
    (* scan lower's postcondition, we instantiate i to -1 and elems to
     * elems2'++elems3, since we might need an element of elems3 to stop the
     * traversal *)
    xlet
      `POSTv (new_lower_v:v).
        (ARRAY arr_v (ignore1++lower_part++middle_vs++upper_part++ignore2)) *
        &(∃new_lower:num.
           INT (&(LENGTH ignore1 + LENGTH lower_part + new_lower)) new_lower_v ∧
           0 ≤ new_lower ∧
           new_lower < LENGTH (elems2'++elems3) ∧
           ¬cmp (EL new_lower (elems2'++elems3)) pivot ∧
           !k:num. k < new_lower ⇒ cmp (EL k (elems2'++elems3)) pivot)`
    >- (
      xapp >>
      xsimpl >>
      fs [EXISTS_MEM, MEM_EL] >>
      MAP_EVERY qexists_tac [`ignore2`, `ignore1++lower_part`,
             `-1`, `elems2'++elems3`,
             `middle_vs++upper_part`, `n'`] >>
      simp [] >>
      rw []
      >- metis_tac [LENGTH_APPEND]
      >- (
        `!x:int. x + -1 = x - 1` by intLib.ARITH_TAC >>
        simp [])
      >- (
        unabbrev_all_tac >>
        fs [])
      >- (
        unabbrev_all_tac >>
        fs [] >>
        metis_tac [EVERY2_APPEND])) >>
    (* scan uppers's postcondition, we instantiate i to LENGTH lower_part +
     * LENGTH middle_v and elems to elems1++elems2', since we might need an
     * element of elems1 to stop the traversal *)
    xlet
      `POSTv (new_upper_v:v).
        (ARRAY arr_v (ignore1++lower_part++middle_vs++upper_part++ignore2)) *
        &(∃new_upper:num.
           INT (&(LENGTH ignore1 + new_upper)) new_upper_v ∧
           new_upper < LENGTH (elems1++elems2') ∧
           ¬cmp pivot (EL new_upper (elems1++elems2')) ∧
           !k:num.
             (&k) < LENGTH (elems1++elems2') ∧ new_upper < k ⇒
             cmp pivot (EL k (elems1++elems2')))`
    >- (
      xapp >>
      xsimpl >>
      fs [EXISTS_MEM, MEM_EL] >>
      MAP_EVERY qexists_tac [`upper_part++ignore2`, `ignore1`,
             `&LENGTH (lower_part++middle_vs)`, `elems1++elems2'`,
             `lower_part++middle_vs`, `n''`] >>
      simp [] >>
      rw []
      >- metis_tac [LENGTH_APPEND, LIST_REL_LENGTH]
      >- fs [integerTheory.INT_ADD]
      >- metis_tac [LIST_REL_LENGTH, LESS_EQ_REFL]
      >- (
        unabbrev_all_tac >>
        fs [] >>
        imp_res_tac LIST_REL_LENGTH >>
        intLib.ARITH_TAC)
      >- (
        unabbrev_all_tac >>
        fs [] >>
        metis_tac [EVERY2_APPEND])
      >- (
        qexists_tac `j` >>
        rw []
        >- (
          imp_res_tac LIST_REL_LENGTH >>
          fs [])
        >- (
          unabbrev_all_tac >>
          fs [] >>
          first_x_assum match_mp_tac >>
          rw [] >>
          metis_tac [LIST_REL_LENGTH]))) >>
    xlet `POSTv b_v.
             ARRAY arr_v (ignore1 ++ lower_part ++ middle_vs ++ upper_part ++ ignore2) *
             &(BOOL (LENGTH lower_part + new_lower < new_upper) b_v)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, BOOL_def]) >>
    `lower_stop ≠ [] ∧ upper_stop ≠ []` by metis_tac [EXISTS_DEF] >>
    xif
    (* The pointers haven't crossed yet, loop *)
    >- (
      imp_res_tac LIST_REL_LENGTH >>
      `new_lower < LENGTH elems2'` by intLib.ARITH_TAC >>
      xlet `POSTv x1_v.
             (ARRAY arr_v (ignore1 ++ lower_part ++ middle_vs ++ upper_part ++ ignore2)) *
             &(x1_v = EL new_lower middle_vs ∧ a (EL new_lower elems2') x1_v)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `LENGTH ignore1 + LENGTH lower_part + new_lower` >>
        imp_res_tac LIST_REL_LENGTH >>
        rw [] >>
        fs [INT_def, NUM_def, EL_APPEND_EQN, Abbr`lower_stop`, LIST_REL_EL_EQN]) >>
      xlet `POSTv x2_v.
             (ARRAY arr_v (ignore1 ++ lower_part ++ middle_vs ++ upper_part ++ ignore2)) *
             &(x2_v = EL (new_upper - LENGTH lower_part) middle_vs ∧
               a (EL (new_upper - LENGTH lower_part) elems2') x2_v)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `LENGTH ignore1 + new_upper` >>
        imp_res_tac LIST_REL_LENGTH >>
        rw [] >>
        fs [INT_def, NUM_def, EL_APPEND_EQN, Abbr`upper_stop`, LIST_REL_EL_EQN]) >>
      xlet
        `POSTv u_v.
           ARRAY arr_v
             (ignore1 ++ lower_part ++
              LUPDATE x2_v new_lower middle_vs ++
              upper_part ++ ignore2)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `new_lower + (LENGTH ignore1 + LENGTH lower_part)` >>
        simp [NUM_def] >>
        simp [LIST_EQ_REWRITE, EL_LUPDATE, EL_APPEND_EQN] >>
        rw [] >>
        fs []) >>
      xlet
        `POSTv u_v.
           ARRAY arr_v
             (ignore1 ++ lower_part ++
              LUPDATE x1_v (new_upper - LENGTH lower_part)
                (LUPDATE x2_v new_lower middle_vs) ++
              upper_part ++ ignore2)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `new_upper + LENGTH ignore1` >>
        simp [NUM_def] >>
        simp [LIST_EQ_REWRITE, EL_LUPDATE, EL_APPEND_EQN] >>
        rw [] >>
        fs []) >>
      imp_res_tac LIST_REL_LENGTH >>
      qabbrev_tac `new_middle_size = new_upper - LENGTH lower_part - new_lower - 1` >>
      `new_middle_size  < LENGTH middle_vs`
      by (
        unabbrev_all_tac >>
        intLib.ARITH_TAC) >>
      last_x_assum drule >>
      disch_then (qspec_then `TAKE new_middle_size (DROP (new_lower + 1) middle_vs)` mp_tac) >>
      `new_middle_size ≤ LENGTH (DROP (new_lower + 1) middle_vs)`
      by (
        simp [LENGTH_DROP] >>
        unabbrev_all_tac >>
        intLib.ARITH_TAC) >>
      simp [LENGTH_TAKE] >>
      disch_then xapp_spec >>
      xsimpl >>
      MAP_EVERY qexists_tac
        [`LUPDATE x1_v 0 (DROP (new_upper - LENGTH lower_part) middle_vs) ++ upper_part`,
         `lower_part ++ LUPDATE x2_v new_lower (TAKE (new_lower + 1) middle_vs)`,
         `ignore2`,
         `ignore1`,
         `LUPDATE (EL new_lower elems2') 0 (DROP (new_upper - LENGTH lower_part) elems2') ++ elems3`,
         `TAKE new_middle_size (DROP (new_lower + 1) elems2')`,
         `elems1 ++ LUPDATE (EL (new_upper − LENGTH lower_part) elems2') new_lower
                            (TAKE (new_lower + 1) elems2')`] >>
      unabbrev_all_tac >>
      simp [GSYM CONJ_ASSOC] >>
      conj_tac
      (* If the upper partition is empty, there is a good blocker. Here, the
       * upper partition cannot be empty *)
      >- (
        rw [] >>
        drule DROP_EMPTY >>
        rw []) >>
      conj_tac
      (* The pivot is not less than the new lower partition *)
      >- (
        simp [EVERY_EL] >>
        rw [EL_TAKE, EL_LUPDATE]
        >- fs [EL_APPEND_EQN] >>
        `n < new_lower` by decide_tac >>
        `cmp (EL n elems2') pivot` suffices_by metis_tac [strict_weak_order_def] >>
        fs [EL_APPEND_EQN]) >>
      conj_tac
      (* The new upper partition is not less than the pivot *)
      >- (
        simp [EVERY_EL] >>
        rw [EL_DROP, EL_LUPDATE]
        >- fs [EL_APPEND_EQN] >>
        `cmp pivot (EL (n + new_upper − LENGTH lower_part) elems2')`
        suffices_by metis_tac [strict_weak_order_def] >>
        fs [EL_APPEND_EQN]) >>
      conj_tac
      (* We got the lower index value right in the above exists_tac *)
      >- simp [integerTheory.INT_SUB] >>
      conj_tac
      (* There is a stopping element in the new lower partition, plus new
       * middle. The one we just swapped in will do. *)
      >- (
        simp [EXISTS_MEM, MEM_LUPDATE, GSYM DISJ_ASSOC] >>
        disj2_tac >>
        disj1_tac >>
        qexists_tac `EL new_upper (elems1 ++ elems2')` >>
        simp [EL_APPEND_EQN]) >>
      conj_tac
      (* There is a stopping element in the new upper partition, plus new
       * middle. The one we just swapped in will do. *)
      >- (
        simp [EXISTS_MEM, MEM_LUPDATE] >>
        disj2_tac >>
        disj1_tac >>
        qexists_tac `EL new_lower (elems2' ++ elems3)` >>
        simp [EL_APPEND_EQN]) >>
      conj_tac
      (* The new lower partitions are related by a, essentially book keeping *)
      >- metis_tac [EVERY2_APPEND_suff, EVERY2_LUPDATE_same, EVERY2_TAKE] >>
      conj_tac
      (* The new middle partition is related by a, essentially book keeping *)
      >- metis_tac [EVERY2_APPEND_suff, EVERY2_TAKE, EVERY2_DROP] >>
      conj_tac
      (* The new upper partitions are related by a, essentially book keeping *)
      >- metis_tac [EVERY2_APPEND_suff, EVERY2_LUPDATE_same, EVERY2_DROP] >>
      conj_asm1_tac
      (* The ARRAY pre/post conditions line up *)
      >- (
        simp [EL_LUPDATE, LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, EL_DROP] >>
        rw [] >>
        fs [prim_recTheory.LESS_REFL]) >>
      (* We still have a partition *)
      pop_assum (assume_tac o GSYM) >>
      rw [partition_pred_def] >>
      MAP_EVERY qexists_tac [`x`, `x'`] >>
      rw [] >>
      MAP_EVERY qexists_tac [`elems1'`, `elems2''`] >>
      simp [] >>
      (* Permutation *)
      qpat_x_assum `PERM _ _` mp_tac >>
      `LUPDATE (EL (new_upper − LENGTH lower_part) elems2') new_lower (TAKE (new_lower + 1) elems2') ++
       TAKE (new_upper − (new_lower + (LENGTH lower_part + 1)))
         (DROP (new_lower + 1) elems2') ++
       LUPDATE (EL new_lower elems2') 0 (DROP (new_upper − LENGTH lower_part) elems2') =
       LUPDATE (EL new_lower elems2') (new_upper − LENGTH lower_part)
         (LUPDATE (EL (new_upper − LENGTH lower_part) elems2') new_lower elems2')`
      by (
        simp [EL_LUPDATE, LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, EL_DROP] >>
        rw [] >>
        fs [prim_recTheory.LESS_REFL]) >>
      ASM_REWRITE_TAC [METIS_PROVE [APPEND_ASSOC] ``!a b c d e:'a list. a++b++c++d++e=a++(b++c++d)++e``] >>
      rw [] >>
      drule perm_helper >>
      disch_then irule >>
      simp [GSYM ZIP_APPEND, PERM_APPEND_IFF, GSYM lupdate_zip] >>
      simp [GSYM EL_ZIP] >>
      irule perm_swap >> conj_tac
      >- metis_tac [LENGTH_ZIP] >>
      simp [LENGTH_ZIP])
    (* The pointers have crossed, stop *)
    >- (
      xvar >>
      xsimpl >>
      imp_res_tac LIST_REL_LENGTH >>
      fs [] >>
      `new_upper + 1 ≤ LENGTH (lower_part++middle_vs)`
      by (
        fs [] >>
        intLib.ARITH_TAC) >>
      (* new_upper indexes from the start of lower_part, and we include the
       * element that new_upper points to in the lower partition *)
      qexists_tac `TAKE (new_upper + 1) (lower_part++middle_vs)` >>
      qexists_tac `DROP (new_upper + 1) (lower_part++middle_vs++upper_part)` >>
      simp [partition_pred_def, GSYM CONJ_ASSOC] >>
      conj_tac
      (* The lower partition is non-empty *)
      >- metis_tac [APPEND_eq_NIL, LIST_REL_LENGTH, LENGTH_NIL] >>
      conj_tac
      (* The upper partition is non-empty *)
      >- (
        simp [DROP_NIL, DECIDE ``!a:num b. ¬(a ≥ b) ⇔ a < b``] >>
        fs [DECIDE ``!a b:num. ¬(a < b) ⇔ b ≤ a``] >>
        Cases_on `upper_part ≠ []` >>
        simp [] >>
        fs []
        >- full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL] >>
        fs [] >>
        `new_lower + 1 ≠ LENGTH middle_vs` suffices_by intLib.ARITH_TAC >>
        `?n. n < LENGTH elems2' - 1 ∧ ~cmp (EL n elems2') pivot`
        by (
          fs [EXISTS_MEM, MEM_EL] >>
          `~NULL elems2'` by rw [GSYM LENGTH_NOT_NULL] >>
          rw [] >>
          drule EL_FRONT >>
          rw [] >>
          metis_tac [LENGTH_FRONT, PRE_SUB1]) >>
        CCONTR_TAC >>
        fs [] >>
        `n < new_lower` by intLib.ARITH_TAC >>
        metis_tac []) >>
      conj_asm2_tac
      >- (
        pop_assum (assume_tac o GSYM) >>
        qexists_tac `TAKE (new_upper + 1) (elems1++elems2'++elems3)` >>
        qexists_tac `DROP (new_upper + 1) (elems1++elems2'++elems3)` >>
        simp [] >>
        rw []
        (* The pivot is not less than any of the elements in the first partition *)
        >- (
          fs [EVERY_EL] >>
          rw [EL_TAKE, Abbr `upper_stop`] >>
          rw [EL_APPEND_EQN] >>
          (* Because the pointers crossed *)
          `n - LENGTH lower_part ≤ new_lower` by intLib.ARITH_TAC >>
          pop_assum mp_tac >>
          REWRITE_TAC [LESS_OR_EQ] >>
          strip_tac
          >- (
            first_x_assum drule >>
            simp [Abbr `lower_stop`, EL_APPEND_EQN] >>
            metis_tac [strict_weak_order_def]) >>
          `n = new_upper` by intLib.ARITH_TAC >>
          var_eq_tac >>
          fs [Abbr`lower_stop`, EL_APPEND_EQN])
        (* The elements of the second partition are not less than the pivot *)
        >- (
          fs [EVERY_EL] >>
          rw [EL_DROP, Abbr `lower_stop`, Abbr `upper_stop`] >>
          rw [EL_APPEND_EQN] >>
          first_x_assum (qspec_then `n + (new_upper + 1)` mp_tac) >>
          simp [EL_APPEND_EQN] >>
          first_x_assum (qspec_then `n + (new_upper + 1)` mp_tac) >>
          simp [EL_APPEND_EQN] >>
          metis_tac [strict_weak_order_def]))
      >- (
        `TAKE (new_upper + 1) (lower_part ++ middle_vs ++ upper_part) =
         TAKE (new_upper + 1) (lower_part ++ middle_vs)`
        by rw [TAKE_APPEND] >>
        metis_tac [TAKE_DROP]))) >>
  simp [] >>
  xlet `POSTv i1_v.
          ARRAY arr_v (elem_vs1 ++ elem_vs2 ++ elem_vs3) *
          &NUM (lower + LENGTH elem_vs2) i1_v`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `&upper` >>
    rw [] >>
    UNABBREV_ALL_TAC >>
    fs [INT_def, NUM_def, int_arithTheory.INT_NUM_SUB] >>
    rw [] >>
    fs [LENGTH_NIL]) >>
  xlet `POSTv i2_v.
          ARRAY arr_v (elem_vs1 ++ elem_vs2 ++ elem_vs3) *
          &INT (&lower - 1) i2_v`
  >- (
    xapp >>
    xsimpl >>
    fs [NUM_def, INT_def]) >>
  xapp >>
  xsimpl >>
  `1 < LENGTH elem_vs2`
  by (
    Cases_on `elem_vs2` >>
    fs [] >>
    Cases_on `t` >>
    fs [] >>
    rfs []) >>
  imp_res_tac LIST_REL_LENGTH >>
  `elems2 ≠ []` by metis_tac [LENGTH_NIL] >>
  `MEM pivot (FRONT elems2)`
  by (
    fs [front_zip] >>
    qpat_x_assum `MEM _ (ZIP _)` mp_tac >>
    simp [MEM_ZIP, LENGTH_FRONT, MEM_EL, EL_FRONT, NULL_DEF] >>
    rw [] >>
    fs [LIST_REL_EL_EQN] >>
    metis_tac []) >>
  `MEM pivot elems2`
  by (
    Cases_on `elems2` >>
    fs [MEM_FRONT]) >>
  MAP_EVERY qexists_tac [`[]`, `elem_vs2`, `[]`, `elem_vs3`, `elem_vs1`, `[]`, `elems2`, `[]`] >>
  rw []
  >- (
    simp [EXISTS_MEM] >>
    qexists_tac `pivot` >>
    rw [] >>
    metis_tac [strict_weak_order_def])
  >- (
    simp [EXISTS_MEM] >>
    qexists_tac `pivot` >>
    rw [] >>
    metis_tac [strict_weak_order_def])
  >- (
    simp [EXISTS_MEM] >>
    qexists_tac `pivot` >>
    rw [] >>
    metis_tac [strict_weak_order_def])
  >- fs [INT_def, NUM_def]
  >- metis_tac []
QED

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
val _ = append_prog quicksort;

val eq_int_v_thm =
  MATCH_MP
    (DISCH_ALL mlbasicsProgTheory.eq_v_thm)
    (ml_translatorTheory.EqualityType_NUM_BOOL |> CONJUNCT2 |> CONJUNCT1)

Theorem quicksort_spec:
   !ffi_p cmp cmp_v arr_v elem_vs elems.
    strict_weak_order cmp ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    (* The elements of the array are all of "semantic type" a *)
    LIST_REL a elems elem_vs
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "quicksort" (basis_st()))
      [cmp_v; arr_v]
      (* The array argument is in the heap with contents elem_vs *)
      (ARRAY arr_v elem_vs)
      (* Quicksort terminates *)
      (POSTv u.
        SEP_EXISTS elem_vs'.
          (* The array argument is in the heap with contents elem_vs *)
          ARRAY arr_v elem_vs' *
          (* Those contents permute the original contents. Note that we need to
           * get the corresponding permutation on the shallowly embedded side
           * too. That's what the ZIP is for, to uniquely determine elems'. *)
          &(?elems'.
              LIST_REL a elems' elem_vs' ∧
              PERM (ZIP (elems',elem_vs')) (ZIP (elems,elem_vs)) ∧
              (* We use "not greater than" as equivalent to "less or equal" *)
              SORTED (\x y. ¬(cmp y x)) elems'))
Proof
  xcf "quicksort" (basis_st()) >>
  (* The loop invariant for the main loop. Note that we have to quantify over
   * what's in the array because it changes on the recursive calls. *)
  xfun_spec `quicksort_help`
    `!elem_vs2 elems2 lower_v upper_v elems1 elems3 elem_vs1 elem_vs3.
      (* We split the array into 3 parts. The second must have elements of type
       * a and be non-empty. *)
      LIST_REL a elems2 elem_vs2 ∧
      elem_vs2 ≠ [] ∧
      (* The lower index must point to the beginning of elem_vs2, and the upper
       * to its end *)
      INT (&LENGTH elem_vs1) lower_v ∧
      INT (&(LENGTH elem_vs1 + LENGTH elem_vs2 - 1)) upper_v
      ⇒
      app ffi_p quicksort_help
        [lower_v; upper_v]
        (ARRAY arr_v (elem_vs1 ++ elem_vs2 ++ elem_vs3))
        (* The loop terminates and has sorted the sub-array between lower and
         * upper *)
        (POSTv u.
          SEP_EXISTS sorted sorted_vs.
            ARRAY arr_v (elem_vs1 ++ sorted_vs ++ elem_vs3) *
            &(LENGTH sorted = LENGTH sorted_vs ∧
              PERM (ZIP (sorted, sorted_vs)) (ZIP (elems2, elem_vs2)) ∧
              SORTED (\x y. ¬(cmp y x)) sorted))`
  >- (
    (* Prove the loop invariant, by induction on how big the segment to sort is *)
    gen_tac >>
    completeInduct_on `LENGTH elem_vs2` >>
    rw [] >>
    `LENGTH elem_vs2 = 1 ∨ LENGTH elem_vs2 > 1`
    by full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL]
    >- (
      (* A single element segment array *)
      `LENGTH elems2 = 1` by metis_tac [LIST_REL_LENGTH] >>
      full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL] >>
      xapp >>
      rw [] >>
      xlet_auto
      >- (
        xsimpl >>
        fs [BOOL_def, INT_def]) >>
      xif >>
      qexists_tac `T` >>
      rw [] >>
      xret >>
      xsimpl >>
      qexists_tac `elems2` >>
      fs [sing_length1]) >>
    (* Get the code of the loop *)
    last_x_assum irule >>
    xlet_auto >- xsimpl >>
    xif >>
    qexists_tac `F` >>
    rw [] >>
    (* Get the pivot *)
    xlet_auto >- xsimpl >>
    qabbrev_tac `pivot = HD elems2` >>
    (* The post-condition of partition *)
    xlet
      `POSTv p_v. SEP_EXISTS part1 part2.
        ARRAY arr_v (elem_vs1 ++ part1 ++ part2 ++ elem_vs3) *
        &(partition_pred cmp (LENGTH elem_vs1) p_v pivot elems2 elem_vs2 part1 part2)`
    >- (
      (* Show that we meet partition's assumptions *)
      xapp >>
      xsimpl >> conj_tac
      >- (
        UNABBREV_ALL_TAC >>
        `LENGTH elems2 > 1` by metis_tac [LIST_REL_LENGTH] >>
        imp_res_tac length_gt1 >>
        simp [FRONT_DEF] >>
        fs [] >>
        REWRITE_TAC [GSYM APPEND_ASSOC] >>
        simp [EL_LENGTH_APPEND])
      >- metis_tac []) >>
    fs [partition_pred_def] >>
    (* The first recursive call sorts the lower partition *)
    xlet
      `POSTv u.
         SEP_EXISTS sorted_vs1.
           ARRAY arr_v (elem_vs1 ++ sorted_vs1 ++ part2 ++ elem_vs3) *
           &(?sorted1.
               LENGTH sorted1 = LENGTH sorted_vs1 ∧
               PERM (ZIP (sorted1,sorted_vs1)) (ZIP (elems1,part1)) ∧
               SORTED (\x y. ¬(cmp y x)) sorted1)`
    >- (
      first_x_assum (qspec_then `LENGTH part1` mp_tac) >>
      impl_keep_tac
      >- (
        `LENGTH elem_vs2 = LENGTH (part1 ++ part2)`
        by metis_tac [LENGTH_ZIP, PERM_LENGTH, LENGTH_APPEND, LIST_REL_LENGTH] >>
        full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,LENGTH_APPEND]) >>
      disch_then (qspec_then `part1` mp_tac) >>
      simp [] >>
      disch_then xapp_spec >>
      xsimpl >>
      `LIST_REL a (elems1++elems2') (part1++part2)`
      by metis_tac [list_rel_perm, LIST_REL_LENGTH, LENGTH_APPEND] >>
      drule LIST_REL_APPEND_IMP >>
      simp [] >>
      strip_tac >>
      MAP_EVERY qexists_tac [`elems1`, `part2++elem_vs3`, `elem_vs1`] >>
      rw [] >>
      metis_tac []) >>
    xlet_auto >- xsimpl >>
    (* The second recursive call sorts the upper partition, and that should
     * leave the whole list between lower and upper sorted. *)
    first_x_assum (qspec_then `LENGTH part2` mp_tac) >>
    impl_keep_tac
    >- (
      `LENGTH elem_vs2 = LENGTH (part1 ++ part2)`
      by metis_tac [LENGTH_ZIP, PERM_LENGTH, LENGTH_APPEND, LIST_REL_LENGTH] >>
      full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL,LENGTH_APPEND]) >>
    disch_then (qspecl_then [`part2`] mp_tac) >>
    simp [] >>
    disch_then xapp_spec >>
    xsimpl >>
    `LIST_REL a (elems1++elems2') (part1++part2)`
    by metis_tac [list_rel_perm, LIST_REL_LENGTH, LENGTH_APPEND] >>
    drule LIST_REL_APPEND_IMP >>
    simp [] >>
    strip_tac >>
    MAP_EVERY qexists_tac [`elems2'`, `elem_vs3`, `elem_vs1++sorted_vs1`] >>
    `LENGTH part1 = LENGTH sorted_vs1`
    by metis_tac [PERM_LENGTH, LENGTH_ZIP] >>
    rw []
    >- (
      fs [NUM_def] >>
      `LENGTH sorted_vs1 ≠ 0` by metis_tac [LENGTH_NIL] >>
      `LENGTH sorted_vs1 - 1 + 1 = LENGTH sorted_vs1` by intLib.ARITH_TAC >>
      fs [])
    >- metis_tac [ADD_COMM, PERM_LENGTH, LIST_REL_LENGTH, LENGTH_ZIP, LENGTH_APPEND] >>
    qexists_tac `sorted1++x` >>
    rw []
    >- (
      irule PERM_TRANS >>
      metis_tac [PERM_CONG, ZIP_APPEND, PERM_SYM]) >>
    simp [SORTED_APPEND_IFF] >>
    CCONTR_TAC >>
    fs [] >>
    (* The two sorted partitions are sorted once appended *)
    fs [EVERY_MEM] >>
    `MEM (HD x) x` by (Cases_on `x` >> fs []) >>
    `MEM (LAST sorted1) sorted1` by (Cases_on `sorted1` >> metis_tac [MEM_LAST]) >>
    `~cmp (HD x) pivot` by metis_tac [PERM_ZIP, MEM_PERM] >>
    `~cmp pivot (LAST sorted1)` by metis_tac [PERM_ZIP, MEM_PERM] >>
    fs [strict_weak_order_def, transitive_def] >>
    metis_tac []) >>
  (* Make the initial call to the sorting loop, unless the array is empty *)
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xif
  >- (
    xret >>
    xsimpl >>
    fs [LENGTH_NIL]) >>
  xlet_auto >- xsimpl >>
  first_x_assum xapp_spec >>
  xsimpl >>
  MAP_EVERY qexists_tac [`elems`, `[]`, `elem_vs`] >>
  rw []
  >- (
    fs [INT_def] >>
    `LENGTH elem_vs ≠ 0` by simp [] >>
    simp [int_arithTheory.INT_NUM_SUB]) >>
  qexists_tac `x` >>
  rw [] >>
  irule list_rel_perm >>
  rw [] >>
  metis_tac [PERM_SYM]
QED

val _ = export_theory ();
