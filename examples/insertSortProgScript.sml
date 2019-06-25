(*
  In-place insertion sort on a polymorphic array.
*)
open preamble semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib cfLib
     basisFunctionsLib ArrayProofTheory

val _ = new_theory "insertSortProg";

val _ = translation_extends"ArrayProg";

fun basis_st () = get_ml_prog_state ()

val insertsort = process_topdecs `
fun insertsort cmp a =
let
  fun outer_loop prefix =
    if prefix < Array.length a - 1 then
      let val c = Array.sub a (prefix + 1)
          fun inner_loop i =
            if i >= 0 then
              let val ai = Array.sub a i in
              if cmp c ai then
                (Array.update a (i+1) ai;
                 inner_loop (i - 1))
              else
                Array.update a (i + 1) c
              end
            else
              Array.update a (i + 1) c
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
val insertsort_st = ml_progLib.add_prog insertsort ml_progLib.pick_name (basis_st());

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

Theorem list_rel_front:
   !r l1 l2.
    l1 ≠ [] ∧ l2 ≠ [] ⇒
    (LIST_REL r l1 l2
     ⇔
     LIST_REL r (FRONT l1) (FRONT l2) ∧ r (LAST l1) (LAST l2))
Proof
  Induct_on `l1` >>
  rw [] >>
  Cases_on `l2` >>
  fs [FRONT_DEF, LAST_DEF] >>
  rw [] >>
  metis_tac []
QED

Theorem zip_append_sing:
   !l1 l2 x y.
    LENGTH l1 = LENGTH l2
    ⇒
    ZIP (l1,l2) ++ [(x, y)] = ZIP (l1++[x], l2++[y])
Proof
  rw [] >>
  `[(x,y)] = ZIP ([x], [y])` by rw [] >>
  metis_tac [ZIP_APPEND, LENGTH]
QED

val arith = Q.prove (
  `!x:num. x ≠ 0 ⇒ &(x-1) = &x - 1:int`,
  rw [int_arithTheory.INT_NUM_SUB]);

val eq_num_v_thm =
  MATCH_MP
    (DISCH_ALL mlbasicsProgTheory.eq_v_thm)
    (ml_translatorTheory.EqualityType_NUM_BOOL |> CONJUNCT1)

Theorem insertsort_spec:
   !ffi_p cmp cmp_v arr_v elem_vs elems.
    LIST_REL a elems elem_vs ∧
    (a --> a --> BOOL) cmp cmp_v ∧
    (!x y. cmp x y ⇒ ~cmp y x)
    ⇒
    app (ffi_p:'ffi ffi_proj) ^(fetch_v "insertsort" insertsort_st)
      [cmp_v; arr_v]
      (ARRAY arr_v elem_vs)
      (POSTv u.
        SEP_EXISTS elem_vs'.
          ARRAY arr_v elem_vs' *
          &(?elems'.
              PERM (ZIP (elems', elem_vs')) (ZIP (elems, elem_vs)) ∧
              SORTED (\x y. ¬(cmp y x)) elems'))
Proof
  xcf "insertsort" insertsort_st >>
  xfun_spec `outer_loop`
    `!elem_vs2 elems1 elems2 elem_vs1 prefix_v.
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
                LENGTH elems' = LENGTH elem_vs' ∧
                PERM (ZIP (elems', elem_vs')) (ZIP (elems1++elems2, elem_vs1++elem_vs2)) ∧
                SORTED (\x y. ¬(cmp y x)) elems'))`
  >- (
    gen_tac >>
    Induct_on `LENGTH elem_vs2` >>
    rw []
    >- ( (* Base case: we've come to the end of the array *)
      xapp >>
      xlet `POSTv len_v.
            ARRAY arr_v (elem_vs1) *
            &INT (&LENGTH (elem_vs1)) len_v`
      >- (
        xapp >>
        xsimpl >>
        fs [INT_def, NUM_def]) >>
      xlet `POSTv x.
              ARRAY arr_v elem_vs1 *
              &INT (&(LENGTH elem_vs1-1)) x`
      >- (
        xapp >>
        xsimpl >>
        fs [INT_def, NUM_def, arith]) >>
      xlet `POSTv b_v. ARRAY arr_v elem_vs1 * &BOOL F b_v`
      >- (
        xapp >>
        xsimpl >>
        fs [INT_def, NUM_def, BOOL_def]) >>
      xif >>
      qexists_tac `F` >>
      rw [] >>
      xret >>
      xsimpl >>
      fs [] >>
      qexists_tac `elems1` >>
      rw [] >>
      metis_tac [LIST_REL_LENGTH]) >>
    (* Start going through the loop *)
    last_x_assum xapp_spec >>
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
      fs [INT_def, NUM_def, arith]) >>
    xlet `POSTv b_v. ARRAY arr_v (elem_vs1 ++ elem_vs2) * &BOOL T b_v`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, NUM_def, BOOL_def] >>
      Cases_on`LENGTH elem_vs1` \\ fs[]) >>
    xif >>
    qexists_tac `T` >>
    rw [] >>
    xlet
      `POSTv pre1_v.
        ARRAY arr_v (elem_vs1 ++ elem_vs2) *
        &INT (&(LENGTH elem_vs1)) pre1_v`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def, arith]) >>
    xlet `POSTv cc_v. ARRAY arr_v (elem_vs1 ++ elem_vs2) * &(cc_v = HD elem_vs2)`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `LENGTH elem_vs1` >>
      simp [EL_APPEND2] >>
      fs [INT_def, NUM_def]) >>
    xfun_spec `inner_loop`
      `!sorted_vs1 sorted1 sorted2 sorted_vs2 i_v junk.
        LIST_REL a sorted1 sorted_vs1 ∧
        LIST_REL a sorted2 sorted_vs2 ∧
        INT (&(LENGTH sorted_vs1) - 1) i_v ∧
        EVERY (cmp (HD elems2)) sorted2 ∧
        SORTED (\x y. ¬(cmp y x)) (sorted1++sorted2)
        ⇒
        app (ffi_p:'ffi ffi_proj) inner_loop
          [i_v]
          (ARRAY arr_v (sorted_vs1++[junk]++sorted_vs2++TL elem_vs2))
          (POSTv u.
            SEP_EXISTS sorted_vs'.
              ARRAY arr_v (sorted_vs' ++ sorted_vs2 ++ TL elem_vs2) *
              &(?sorted'.
                  LENGTH sorted' = LENGTH sorted_vs' ∧
                  PERM (ZIP (sorted', sorted_vs'))
                       (ZIP (sorted1++[HD elems2], sorted_vs1++[cc_v])) ∧
                  SORTED (\x y. ¬(cmp y x)) (sorted'++sorted2)))`
    >- (
      gen_tac >>
      Induct_on `LENGTH sorted_vs1` >>
      rw [] >>
      last_x_assum xapp_spec
      >- ( (* Base case, we've run off the array  *)
        xlet `POSTv b_v2. ARRAY arr_v (junk :: sorted_vs2 ++ TL elem_vs2) * &BOOL F b_v2`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def, NUM_def]) >>
        xif >>
        qexists_tac `F` >>
        fs [] >>
        xlet `POSTv i1_v. ARRAY arr_v (junk :: sorted_vs2 ++ TL elem_vs2) * &INT 0 i1_v`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def]) >>
        xapp >>
        xsimpl >>
        qexists_tac `0` >>
        simp [] >>
        fs [INT_def, NUM_def] >>
        rw [] >>
        qexists_tac `[HD elem_vs2]` >>
        simp [LUPDATE_def] >>
        qexists_tac `[HD elems2]` >>
        simp [] >>
        Cases_on `sorted2` >>
        simp [SORTED_DEF] >>
        fs []) >>
      (* We haven't hit the end *)
      xlet `POSTv b_v2. ARRAY arr_v (sorted_vs1 ++ [junk] ++ sorted_vs2 ++ TL elem_vs2) * &BOOL T b_v2`
      >- (
        xapp >>
        xsimpl >>
        fs [INT_def, NUM_def, BOOL_def] >>
        intLib.ARITH_TAC) >>
      xif >>
      qexists_tac `T` >>
      rw [] >>
      xlet `POSTv ai_v. ARRAY arr_v (sorted_vs1 ++ [junk] ++ sorted_vs2 ++ TL elem_vs2) *
               &(ai_v = LAST sorted_vs1)`
      >- (
        xapp >>
        xsimpl >>
        qexists_tac `&(LENGTH sorted_vs1 - 1)` >>
        simp [] >>
        qpat_x_assum`_ = LENGTH sorted_vs1`(assume_tac o SYM) \\ fs[] >>
        fs[EL_APPEND1, NUM_def, INT_def, ADD1, arith, LAST_EL, PRE_SUB1] >>
        conj_tac >- intLib.COOPER_TAC >>
        Q.ISPEC_THEN`sorted_vs1`mp_tac LAST_EL >> simp[PRE_SUB1] >>
        impl_tac >- (strip_tac \\ fs[]) \\ simp[]) >>
      xlet `POSTv b_v3. ARRAY arr_v (sorted_vs1 ++ [junk] ++ sorted_vs2 ++ TL elem_vs2) *
              &BOOL (cmp (HD elems2) (LAST sorted1)) b_v3`
      >- (
        xapp >>
        xsimpl >>
        MAP_EVERY qexists_tac [`LAST sorted1`, `HD elems2`, `cmp`, `a`] >>
        simp [] >>
        fs [LIST_REL_EL_EQN] >>
        rw [] >>
        `0 < LENGTH elems2 ∧ LENGTH sorted_vs1 ≠ 0 ∧ PRE (LENGTH sorted1) < LENGTH sorted_vs1` by decide_tac >>
        metis_tac [EL, LAST_EL, LENGTH_NIL]) >>
      xif
      >- ( (* The item to insert is too small. Keep going *)
        xlet `POSTv i1_v. ARRAY arr_v (sorted_vs1 ++ [junk] ++ sorted_vs2 ++ TL elem_vs2) *
                &INT (&LENGTH sorted_vs1) i1_v`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def, arith]) >>
        xlet `POSTv u_v. ARRAY arr_v (sorted_vs1 ++ [LAST sorted_vs1] ++ sorted_vs2 ++ TL elem_vs2)`
        >- (
          xapp >>
          xsimpl >>
          qexists_tac `LENGTH sorted_vs1` >>
          fs [NUM_def, INT_def] >>
          metis_tac [lupdate_append2, APPEND_ASSOC]) >>
        xlet `POSTv i2_v. ARRAY arr_v (sorted_vs1 ++ [LAST sorted_vs1] ++ sorted_vs2 ++ TL elem_vs2) *
                &INT (&LENGTH sorted_vs1 − 2) i2_v`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def] >>
          intLib.ARITH_TAC) >>
        (* Prepare inductive hyp *)
        `LENGTH sorted_vs1 ≠ 0` by decide_tac >>
        first_x_assum (qspec_then `FRONT sorted_vs1` mp_tac) >>
        impl_keep_tac
        >- (
          fs [LENGTH_NIL] >>
          simp [LENGTH_FRONT]) >>
        disch_then (qspecl_then [`FRONT sorted1`, `LAST sorted1::sorted2`,
                                 `LAST sorted_vs1::sorted_vs2`, `i2_v`, `LAST sorted_vs1`] mp_tac) >>
        simp [] >>
        fs [] >>
        impl_tac
        >- (
          `sorted1 ≠ []` by metis_tac [LENGTH_NIL, LIST_REL_LENGTH] >>
          fs [list_rel_front, LENGTH_NIL] >>
          fs [INT_def, LENGTH_FRONT, PRE_SUB1] >>
          rw [] >> fs [ arith]
          >- intLib.ARITH_TAC >>
          metis_tac [LENGTH_NIL, APPEND_FRONT_LAST, APPEND, APPEND_ASSOC]) >>
        disch_then xapp_spec >>
        xsimpl >>
        rw []
        >- metis_tac [LENGTH_NIL, APPEND_FRONT_LAST] >>
        qexists_tac `sorted'++[LAST sorted1]` >>
        rw []
        >- (
          imp_res_tac LIST_REL_LENGTH >>
          simp [GSYM ZIP_APPEND] >>
          `PERM (ZIP (sorted',x') ++ [(LAST sorted1,LAST sorted_vs1)])
                (ZIP (FRONT sorted1 ++ [HD elems2], FRONT sorted_vs1 ++ [HD elem_vs2]) ++
                 [(LAST sorted1,LAST sorted_vs1)])`
          by metis_tac [PERM_APPEND_IFF] >>
          pop_assum mp_tac >>
          simp [zip_append_sing] >>
          rw [] >>
          irule PERM_TRANS >>
          qexists_tac `ZIP (FRONT sorted1 ++ [HD elems2], FRONT sorted_vs1 ++ [HD elem_vs2]) ++ [(LAST sorted1,LAST sorted_vs1)]` >>
          `sorted_vs1 ≠ [] ∧ sorted1 ≠ []` by metis_tac [LENGTH_NIL] >>
          simp [GSYM ZIP_APPEND, LENGTH_FRONT] >>
          irule PERM_TRANS >>
          qexists_tac `ZIP (FRONT sorted1,FRONT sorted_vs1) ++ [(LAST sorted1,LAST sorted_vs1)] ++ [(HD elems2,HD elem_vs2)]` >>
          rw []
          >-  metis_tac [PERM_APPEND, PERM_APPEND_IFF, APPEND_ASSOC] >>
          simp [zip_append_sing, LENGTH_FRONT, ZIP_APPEND, APPEND_FRONT_LAST])
        >- metis_tac [APPEND, APPEND_ASSOC])
      >- ( (* We found the item's spot *)
        xlet `POSTv i1_v. ARRAY arr_v (sorted_vs1 ++ [junk] ++ sorted_vs2 ++ TL elem_vs2) *
                &INT (&LENGTH sorted_vs1) i1_v`
        >- (
          xapp >>
          xsimpl >>
          fs [INT_def]) >>
        xapp >>
        xsimpl >>
        qexists_tac `LENGTH sorted_vs1` >>
        simp [] >>
        fs [INT_def, NUM_def] >>
        rw [] >>
        qexists_tac `sorted_vs1++[HD elem_vs2]` >>
        rw []
        >- (
          qexists_tac `sorted1++[HD elems2]` >>
          imp_res_tac LIST_REL_LENGTH >>
          fs [SORTED_APPEND_IFF]
          >- metis_tac [LENGTH_NIL, DECIDE ``SUC v ≠ 0``] >>
          Cases_on `sorted2` >>
          simp [] >>
          `elems2 ≠ []` by metis_tac [LENGTH_NIL, DECIDE ``SUC v ≠ 0``] >>
          Cases_on `elems2` >>
          fs []) >>
        metis_tac [lupdate_append2, APPEND_ASSOC])) >>
    (* Call the inner loop from the outer loop *)
    xlet `POSTv u.
          SEP_EXISTS sorted_vs'.
            ARRAY arr_v (sorted_vs' ++ TL elem_vs2) *
            &(?sorted'.
                LENGTH sorted' = LENGTH sorted_vs' ∧
                PERM (ZIP (sorted', sorted_vs'))
                     (ZIP (elems1++[HD elems2], elem_vs1++[cc_v])) ∧
                SORTED (\x y. ¬(cmp y x)) sorted')`
    >- (
      xapp >>
      xsimpl >>
      MAP_EVERY qexists_tac [`[]`, `elem_vs1`, `[]`, `elems1`, `HD elem_vs2`] >>
      fs [INT_def] >>
      simp [arith] >>
      Cases_on `elem_vs2` >>
      fs []) >>
    xlet `POSTv p1_v. ARRAY arr_v (sorted_vs' ++ TL elem_vs2) *
            &INT (&LENGTH elem_vs1)  p1_v`
    >- (
      xapp >>
      xsimpl >>
      fs [INT_def] >>
      simp [arith]) >>
    (* Call the outer loop recursively *)
    xapp >>
    xsimpl >>
    MAP_EVERY qexists_tac [`TL elems2`, `sorted'`, `TL elem_vs2`, `sorted_vs'`] >>
    simp [] >>
    imp_res_tac LIST_REL_LENGTH >>
    drule PERM_LENGTH >>
    simp [] >>
    strip_tac >>
    `LENGTH sorted_vs' ≠ 0` by decide_tac >>
    fs [LENGTH_NIL] >>
    rw [LENGTH_TL]
    >- (
      irule list_rel_perm >>
      simp [] >>
      ONCE_REWRITE_TAC [PERM_SYM] >>
      qexists_tac `elems1 ++ [HD elems2]` >>
      qexists_tac `elem_vs1 ++ [HD elem_vs2]` >>
      simp [] >>
      Cases_on `elems2` >>
      Cases_on `elem_vs2` >>
      fs [])
    >- (
      Cases_on `elems2` >>
      Cases_on `elem_vs2` >>
      fs []) >>
    qexists_tac `elems'` >>
    rw [] >>
    irule PERM_TRANS >>
    qexists_tac `ZIP (sorted' ++ TL elems2,sorted_vs' ++ TL elem_vs2)` >>
    simp [] >>
    `PERM (ZIP (sorted',sorted_vs') ++ ZIP (TL elems2, TL elem_vs2))
          (ZIP (elems1 ++ [HD elems2],elem_vs1 ++ [HD elem_vs2]) ++ ZIP (TL elems2, TL elem_vs2))`
    by simp [PERM_APPEND_IFF] >>
    pop_assum mp_tac >>
    simp [ZIP_APPEND, LENGTH_TL] >>
    Cases_on `elems2` >>
    Cases_on `elem_vs2` >>
    fs [] >>
    metis_tac [APPEND, APPEND_ASSOC]) >>
  (* The initial stuff *)
  xlet `POSTv l_v. ARRAY arr_v elem_vs * &INT (&LENGTH elem_vs) l_v`
  >- (
    xapp >>
    xsimpl >>
    fs [NUM_def, INT_def]) >>
  xlet `POSTv b_v. ARRAY arr_v elem_vs * &BOOL (LENGTH elem_vs = 0) b_v`
  >- (
    xapp_spec eq_num_v_thm >>
    xsimpl >>
    fs [INT_def, NUM_def]) >>
  xif
  >- (
    xret >>
    xsimpl >>
    qexists_tac `elems` >>
    rw [] >>
    Cases_on `elems` >>
    fs [] >>
    rfs [])
  >- (
    xapp >>
    xsimpl >>
    MAP_EVERY qexists_tac [`TL elems`, `[HD elems]`, `TL elem_vs`, `[HD elem_vs]`] >>
    simp [] >>
    Cases_on `elems` >>
    Cases_on `elem_vs` >>
    fs [] >>
    rw [] >>
    qexists_tac `elems'` >>
    simp [])
QED

val _ = export_theory ();
