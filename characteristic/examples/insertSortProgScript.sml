open preamble;
open semanticPrimitivesTheory;
open ml_translatorTheory ml_translatorLib ml_progLib;
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib;
open basisFunctionsLib;

open mlarrayProgTheory;

val _ = new_theory "insertSortProg";

val _ = translation_extends"mlarrayProg";

fun basis_st () = get_ml_prog_state ()

val insertsort = process_topdecs `
fun insertsort cmp a =
let
  fun outer_loop prefix =
    if prefix < Array.length a - 1 then
      let val c = Array.sub a (prefix + 1)
          fun inner_loop i =
            if i >= 0 andalso c < Array.sub a i then
              (Array.update a (i+1) (Array.sub a i);
               inner_loop (i - 1))
            else
              Array.update a (i+1) c
      in
      (inner_loop prefix;
       outer_loop (prefix+1))
      end
    else
      ()
in
  if Array.length a = 0 then () else outer_loop 0
end;
`;
val insertsort_st = ml_progLib.add_prog insertsort pick_name (basis_st());

val insertsort_spec = Q.store_thm ("insertquicksort_spec",
  `!ffi_p cmp cmp_v arr_v elem_vs elems.
    LIST_REL a elems elem_vs ∧
    (a --> a --> BOOL) cmp cmp_v
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "insertsort" insertsort_st)
      [cmp_v; arr_v]
      (ARRAY arr_v elem_vs)
      (POSTv u.
        SEP_EXISTS elem_vs'.
          ARRAY arr_v elem_vs' *
          &(?elems'.
              PERM (ZIP (elems', elem_vs')) (ZIP (elems, elem_vs)) ∧
              SORTED (\x y. ¬(cmp y x)) elems'))`,

  xcf "insertsort" insertsort_st >>
  xfun_spec `outer_loop`
    `!elems1 elems2 elems_vs1 elems_vs2 prefix_v.
      elem_vs1 ≠ [] ∧
      LIST_REL a elems1 elem_vs1 ∧
      LIST_REL a elems2 elem_vs2 ∧
      INT (&(LENGTH elem_vs1 - 1)) prefix_v ∧
      SORTED (\x y. ¬(cmp y x)) elems1
      ⇒
      app (ffi_p:'ffi ffi_proj) outer_loop
        [prefix_v]
        (ARRAY arr_v (elem_vs1++elem_vs2))
        (POSTv u.
          SEP_EXISTS elem_vs'.
            ARRAY arr_v elem_vs' *
            &(?elems'.
                PERM (ZIP (elems', elem_vs')) (ZIP (elems1++elems2, elem_vs1++elem_vs2)) ∧
                SORTED (\x y. ¬(cmp y x)) elems'))`
  >- (
    rw [] >>
    xapp >>
    xlet `POSTv len_v.
            ARRAY arr_v (elem_vs1 ++ elem_vs2) *
            &INT (&LENGTH (elem_vs1++elem_vs2)) len_v`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, NUM_def]) >>
    xlet `POSTv x.
            ARRAY arr_v (elem_vs1 ++ elem_vs2) *
            &INT (&(LENGTH (elem_vs1++elem_vs2)-1)) x`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, NUM_def, GSYM LENGTH_NIL] >>
      cheat) >>
    xlet `POSTv b_v.
            ARRAY arr_v (elem_vs1 ++ elem_vs2) *
            &BOOL (LENGTH elem_vs1 - 1 < LENGTH (elem_vs1++elem_vs2)-1) b_v`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, NUM_def, BOOL_def, GSYM LENGTH_NIL] >>
      intLib.ARITH_TAC) >>
    xif
    >- (
      xlet
        `POSTv pre1_v.
          ARRAY arr_v (elem_vs1 ++ elem_vs2) *
          &INT (&(LENGTH elem_vs1)) pre1_v`
      >- (
        xapp >>
        xsimpl >>
        fs [INT_def, GSYM LENGTH_NIL] >>
        cheat) >>
      xlet `POSTv cc_v. ARRAY arr_v (elem_vs1 ++ elem_vs2) * &(cc_v = HD elem_vs2)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `LENGTH elem_vs1` >>
        simp [EL_APPEND2] >>
        fs [INT_def, NUM_def]) >>
      xfun_spec `inner_loop`
        `!elems1 elems2 elems_vs1 elems_vs2 i_v c cc_v.
          elem_vs1 ≠ [] ∧
          LIST_REL a elems1 elem_vs1 ∧
          a c cc_v ∧
          INT (&(LENGTH elem_vs1 - 1)) i_v ∧
          SORTED (\x y. ¬(cmp y x)) elems1
          ⇒
          app (ffi_p:'ffi ffi_proj) inner_loop
            [i_v]
            (ARRAY arr_v (elem_vs1++[cc_v]++elem_vs2))
            (POSTv u.
              SEP_EXISTS elem_vs'.
                ARRAY arr_v (elem_vs' ++ elem_vs2) *
                &(?elems'.
                    PERM (ZIP (elems', elem_vs')) (ZIP (elems1++[c], elem_vs1)) ∧
                    SORTED (\x y. ¬(cmp y x)) elems'))`
      >- (
        rw [] >>
        xapp >>
        xlet `POSTv b_v2. ARRAY arr_v (elem_vs1 ++ [cc_v'] ++ elem_vs2) *
              &BOOL (&LENGTH elem_vs1 > 0) b_v2`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def, BOOL_def, GSYM LENGTH_NIL] >>
          cheat) >>
        



val _ = export_theory ();
