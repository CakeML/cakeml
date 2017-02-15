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
    if cmp (sub a lower) pivot then
      scan_lower lower
    else
      lower
  end

  fun scan_upper upper =
  let
    val upper = upper - 1
  in
    if cmp pivot (sub a upper) then
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
        val v = sub a lower
      in
        (update a lower (sub a upper);
        update a upper v;
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
    INT lower lower_v ∧ INT upper upper_v ∧ lower < upper ∧ 0 ≤ lower ∧
    upper < &(LENGTH elem_vs) ∧
    MEM pivot_v elem_vs ∧
    a pivot pivot_v ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    transitive cmp
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "partition" partition_st)
      [cmp_v; arr_v; pivot_v; lower_v; upper_v]
      (ARRAY arr_v elem_vs)
      (POSTv p_v. SEP_EXISTS elem_vs1 elem_vs2.
        ARRAY arr_v (elem_vs1++elem_vs2) *
        &(∃elems1 elems2.
            PERM elem_vs (elem_vs1 ++ elem_vs2) ∧
            LIST_REL a elems1 elem_vs1 ∧
            LIST_REL a elems2 elem_vs2 ∧
            EVERY (\e. ¬cmp pivot e) elems1 ∧
            EVERY (\e. ¬cmp e pivot) elems2))`,

  xcf "partition" partition_st >>
  xfun_spec `scan_lower`
    `!i elems i_v.
      INT i i_v ∧ -1 ≤ i ∧ i < &(LENGTH elems) ∧
      (?x:num. i ≤ (&x) ∧ x < LENGTH elems ∧ ¬cmp (EL x elems) pivot) ∧
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_lower
        [i_v]
        (ARRAY arr_v elem_vs)
        (POSTv (j_v:v).
          &(∃j:num.
             INT (&j) j_v ∧ i < (&j) ∧ j < LENGTH elems ∧
             ¬cmp (EL j elems) pivot ∧
             !k:num. i < (&k) ∧ k < j ⇒ ¬cmp pivot (EL k elems)))`

  >- (
    rpt gen_tac >>
    Induct_on `Num(&(LENGTH elems) - i)` >>
    rw [] >>
    >- cheat
    xapp >>
    rw []

    xlet `POSTv j_v. &(?j. INT j j_v ∧ j = i + 1)`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def]) >>
    xlet `POSTv x_v. &(∃idx. (&idx) = i + 1 ∧ a (EL idx elems) x_v)`
    >- cheat >>
    xlet `POSTv b_v. &(BOOL (cmp (EL idx elems) pivot) b_v)`
    >- (
      xapp >>
      metis_tac []) >>
    xif
    >- (
      xapp



  xfun_spec `scan_upper`
    `!i_v i arr_v elem_vs elems.
      INT i i_v ∧ 0 ≤ i ∧ i ≤ &(LENGTH elems) ∧
      (?x:num. (&x) ≤ i ∧ x < LENGTH elems ∧ ¬cmp pivot (EL x elems)) ∧
      LIST_REL a elems elem_vs
      ⇒
      app (ffi_p:'ffi ffi_proj) scan_upper
        [i_v]
        (ARRAY arr_v elem_vs)
        (POSTv (j_v:v).
          &(∃j:num.
             INT (&j) j_v ∧ (&j) < i ∧ 0 ≤ j ∧
             ¬cmp pivot (EL j elems) ∧
             !k:num. (&k) < i ∧ j < k ⇒ ¬cmp (EL k elems) pivot))`
  >- cheat
  xfun_spec `par_loop`

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
  quicksort_help 0 (length a - 1)
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


val _ = export_theory ();

