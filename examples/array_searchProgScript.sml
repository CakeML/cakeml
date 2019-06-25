(*
  An example based on searching an array.
*)
open preamble semanticPrimitivesTheory
open ml_translatorTheory ml_translatorLib ml_progLib cfLib basisFunctionsLib
open basisProgTheory quicksortProgTheory ArrayProofTheory

val _ = new_theory "array_searchProg";

val _ = translation_extends "basisProg";

fun basis_st () = get_ml_prog_state ()

(**********)

val linear_search = process_topdecs `
fun linear_search array value =
    let
        fun search_aux start =
            if start = (Array.length array) then
                None
            else
                if (Array.sub array start = value) then
                    Some start
                else
                    search_aux (start + 1)
    in
        search_aux 0
    end;
`;
val _ = append_prog linear_search;

Theorem EL_HD_DROP:
     ∀ n l . n < LENGTH l ⇒ EL n l = HD (DROP n l)
Proof
    Induct >> rw[] >> Cases_on `l` >> fs[]
QED

Theorem linear_search_spec:
    ∀ a ffi_p value value_v elems elem_vs arr_v .
        EqualityType a ∧
        (a) value value_v ∧
        LIST_REL (a) elems elem_vs
    ⇒
        app (ffi_p : 'ffi ffi_proj) ^(fetch_v "linear_search" (basis_st()))
        [arr_v; value_v] (* the arguments *)
        (ARRAY arr_v elem_vs) (* array is in heap with contents elem_vs *)
        (POSTv ret_v .
            (ARRAY arr_v elem_vs) (* array still in heap *) *
            SEP_EXISTS ret .
              &(
                OPTION_TYPE NUM ret ret_v ∧
                (MEM value elems ⇒ ∃ n . ret = SOME n ∧ EL n elems = value) ∧
                (* if value present, it is found *)
                (¬MEM value elems ⇒ ret = NONE) (* if value not present, NONE *)
              )
        )
Proof
    xcf "linear_search" (basis_st()) >>
    reverse (xfun_spec `search_aux`
        `∀ sublist sublist_vs offset offset_v .
            sublist = DROP offset elems ∧
            NUM offset offset_v ∧
            LENGTH elems ≥ offset
        ⇒
            app ffi_p search_aux [offset_v]
            (ARRAY arr_v elem_vs)
            (POSTv opt_v .
                (ARRAY arr_v elem_vs) *
                 SEP_EXISTS opt . &(
                    OPTION_TYPE NUM opt opt_v ∧
                    (MEM value sublist ⇒
                        ∃ index . opt = SOME index ∧ EL index elems = value ∧
                        offset ≤ index) ∧
                    (¬(MEM value sublist) ⇒ opt = NONE)
                )
            )`)
    >- (last_x_assum xapp_spec >>
        xsimpl >> qexists_tac `elem_vs` >> fs[])
    >>
        (*
        let a = Array.length array in
        let b = (start == a) in
        if b then NONE else
            let c = Array.sub array start in
            let d = (c == value) in
            if d then (SOME start) else
                let e = (start + 1) in
                search_aux e
        *)
        gen_tac >> Induct_on `sublist` >> rw[] >>
        `(∀ x y z . a x y ∧ a x z ⇒ y = z) ∧
         (∀ x y z . a x z ∧ a y z ⇒ x = y)` by (
          rw[] >- imp_res_tac EQTYPE_UNICITY_R
          >- imp_res_tac EQTYPE_UNICITY_L)
        >- ( (* base case - empty sublist *)
            last_x_assum xapp_spec >>
            `LENGTH elems ≤ offset` by (
                qspecl_then [`elems`, `offset`] mp_tac DROP_NIL >>
                rw[EQ_IMP_THM]) >>
            imp_res_tac EQ_LESS_EQ >>
            imp_res_tac LIST_REL_LENGTH >>
            fs[] >> rfs[] >> rw[] >> fs[] >>
            xlet_auto (* a *)
                >- xsimpl
                >> `nv = offset_v` by (
                    imp_res_tac LIST_REL_LENGTH >>
                    fs[NUM_def, INT_def])
            >> rveq >> xlet_auto (* b *)
                >- xsimpl
            >> xif >> fs[BOOL_def] >>
               xcon >>
               xsimpl >>
               fs[std_preludeTheory.OPTION_TYPE_def]
            )
        >>
            last_x_assum xapp_spec >>
            xlet_auto (* a *)
                >- xsimpl
                >> imp_res_tac LIST_REL_LENGTH  >> rveq
            >> xlet_auto (* b *)
                >- xsimpl
                >> `offset ≠ LENGTH elem_vs` by (
                        CCONTR_TAC >> fs[] >> rveq >>
                        `DROP (LENGTH elem_vs) elems = []` by
                            metis_tac[DROP_LENGTH_NIL] >> fs[]) >>
                   fs[] >>
                   xif >> fs[BOOL_def]
            >> xlet_auto (* c *)
                >- xsimpl
            >> xlet `POSTv bd . ARRAY arr_v elem_vs *
                    &(BOOL (v = value_v) bd)` (* d *)
                >- (xapp >> xsimpl >> qexists_tac `value` >>
                    qexists_tac `EL offset elems` >>
                    qexists_tac `a` >>
                    fs[] >> imp_res_tac LIST_REL_EL_EQN >> rw[] >>
                    fs[BOOL_def] >>
                    `a (EL offset elems) (EL offset elem_vs)` by fs[] >>
                    EQ_TAC >>
                    rw[] >> fs[] >>
                    metis_tac[])
            >> rveq >> xif
                >- (fs[] >> rveq >> xcon >> xsimpl >>
                    qexists_tac `SOME offset` >> fs[] >>
                    fs[std_preludeTheory.OPTION_TYPE_def] >>
                    `value = EL offset elems` by (
                        first_x_assum match_mp_tac >>
                        qexists_tac `EL offset elem_vs` >>
                        fs[LIST_REL_EL_EQN]) >>
                    rveq >> fs[] >>
                    DISJ1_TAC >>
                    qsuff_tac `EL 0 (DROP offset elems) = h`
                        >- fs[EL_DROP] >>
                    `DROP offset elems = h::sublist` by fs[] >> fs[])
            >> fs[] >>
               `EL offset elems = h` by (
                    `h = EL 0 (DROP offset elems)` by (fs[] >>
                        `DROP offset elems = h::sublist` by fs[] >> fs[]) >>
                    fs[] >> match_mp_tac EL_HD_DROP >> fs[]) >>
                imp_res_tac LIST_REL_EL_EQN >>
            xlet_auto
                >- xsimpl
            >> last_x_assum xapp_spec >>
               xsimpl >>
               qexists_tac `offset + 1` >> fs[] >>
               rw[]
               >- metis_tac[DROP_EQ_CONS_IMP_DROP_SUC, ADD1]
               >> qexists_tac `x` >> fs[] >>
                  `value ≠ EL offset elems` by (
                        CCONTR_TAC >> fs[] >>
                        `a (EL offset elems) (EL offset elem_vs)` by fs[] >>
                        metis_tac[]) >>
                  fs[] >>
                  `sublist = DROP (offset + 1) elems`
                    by metis_tac[DROP_EQ_CONS_IMP_DROP_SUC, ADD1] >>
                  fs[] >> rveq >> rw[] >> fs[]
QED

(**********)

val binary_search = process_topdecs `
fun binary_search cmp array value =
    let
        fun search_aux start finish =
            if start >= finish then None else
                let val mid = (finish + start) div 2
                in
                    if value = (Array.sub array mid) then
                        Some mid
                    else if cmp value (Array.sub array mid) then
                        search_aux start mid
                    else
                        search_aux (mid + 1) finish
                end;
    in
        search_aux 0 (Array.length array)
    end;
`;

val _ = append_prog binary_search;

Theorem drop_take_partition:
     ∀ l n m . n ≤ m ∧ m ≤ LENGTH l ⇒
        TAKE n l ++ DROP n (TAKE m l) ++ DROP m l = l
Proof
    Induct_on `l` >> rw[] >> fs[TAKE_def] >> Cases_on `n = 0` >> fs[] >>
    fs[DROP_def] >> Cases_on `m = 0` >> fs[]
QED

Theorem drop_take:
     ∀ l n m . n ≤ m ∧ m ≤ LENGTH l ⇒
        DROP n (TAKE m l) = TAKE (m - n) (DROP n l)
Proof
    Induct_on `l` >> rw[] >> fs[TAKE_def] >>
    Cases_on `m = 0` >> fs[] >> fs[DROP_def] >> Cases_on `n = 0` >> fs[]
QED

Theorem strict_weak_order_NOT_MEM:
     ∀ h t cmp e . strict_weak_order cmp ∧
               SORTED (λ x y . cmp x y) (h::t) ∧
               cmp e h
    ⇒ ¬ MEM e (h::t)
Proof
    Induct_on `t` >> rw[]
    >- (fs[strict_weak_order_def] >> metis_tac[])
    >- (fs[strict_weak_order_def] >> metis_tac[])
    >- (fs[SORTED_DEF] >>
        `cmp e h` by (fs[strict_weak_order_def] >> metis_tac[transitive_def]) >>
        fs[strict_weak_order_def] >> metis_tac[])
    >- (qsuff_tac `¬MEM e (h::t)` >- fs[MEM] >>
        first_x_assum match_mp_tac >>
        qexists_tac `cmp` >> fs[] >>
        rw[] >- imp_res_tac SORTED_TL >>
        fs[SORTED_DEF] >>
        fs[strict_weak_order_def] >> metis_tac[transitive_def])
QED

Theorem strict_weak_order_cmp_TAKE:
     ∀ cmp e l mid .
        strict_weak_order cmp ∧
        MEM e l ∧ cmp e (EL mid l) ∧
        SORTED (λ x y . cmp x y) l
      ⇒ MEM e (TAKE mid l)
Proof
    Induct_on `l` >> rw[] >> fs[TAKE_def] >>
    Cases_on `mid = 0` >> fs[]
    >- (fs[strict_weak_order_def] >> metis_tac[])
    >- (drule strict_weak_order_NOT_MEM >> rpt(disch_then drule) >> fs[])
    >- (Cases_on `e = h` >> fs[] >> first_x_assum match_mp_tac >>
        qexists_tac `cmp` >> fs[] >> Cases_on `mid` >> fs[] >>
        metis_tac[SORTED_TL])
QED

Theorem strict_weak_order_cmp_EL:
     ∀ l e n cmp .
        n < LENGTH (e::l) ∧ strict_weak_order cmp ∧
        ¬cmp e (EL n (e::l)) ∧ SORTED (λ x y . cmp x y) (e::l)
      ⇒ n = 0
Proof
    Induct_on `l` >> rw[] >> `cmp e h` by fs[SORTED_DEF] >>
    Cases_on `n` >> fs[] >>
    first_x_assum (qspecl_then [`e`, `n'`, `cmp`] mp_tac) >>
    fs[] >> Cases_on `n' = 0` >> fs[] >> Cases_on `n'` >> fs[] >>
    Cases_on `l` >> fs[SORTED_DEF] >> fs[strict_weak_order_def] >>
    metis_tac[transitive_def]
QED

Theorem strict_weak_order_cmp_DROP:
     ∀ cmp e l mid .
        strict_weak_order cmp ∧ mid < LENGTH l ∧
        MEM e l ∧ ¬cmp e (EL mid l) ∧ EL mid l ≠ e ∧
        SORTED (λ x y . cmp x y) l
      ⇒ MEM e (DROP (mid + 1) l)
Proof
    Induct_on `l` >> rw[] >> fs[DROP_def] >>
    Cases_on `mid = 0` >> fs[]
    >- (imp_res_tac strict_weak_order_cmp_EL >> fs[])
    >- (Cases_on `mid` >> fs[ADD1] >>
        first_x_assum match_mp_tac >> qexists_tac `cmp` >> fs[] >>
        metis_tac[SORTED_TL])
QED

Theorem sorted_drop:
     ∀ l n f . SORTED f l ⇒ SORTED f (DROP n l)
Proof
    Induct >> rw[] >> fs[DROP_def] >> Cases_on `n = 0` >> fs[] >>
    first_x_assum match_mp_tac >> metis_tac[SORTED_TL]
QED

Theorem sorted_take:
     ∀ l n f . SORTED f l ⇒ SORTED f (TAKE n l)
Proof
    Induct >> rw[] >> fs[TAKE_def] >> Cases_on `n` >> fs[] >>
    Cases_on `l` >> fs[TAKE, SORTED_DEF] >> Cases_on `n'` >> fs[] >>
    fs[SORTED_DEF] >> first_x_assum (qspecl_then [`n + 1`, `f`] mp_tac) >> rw[]
QED

Theorem mem_take_impl:
     ∀ l n m v . n ≤ m ⇒
        MEM v (TAKE n l) ⇒ MEM v (TAKE m l)
Proof
    Induct >> rw[] >> fs[TAKE_def] >>
    Cases_on `m = 0` >> fs[] >> rfs[] >>
    Cases_on `n = 0` >> fs[] >>
    Cases_on `v = h` >> fs[] >>
    first_x_assum (qspecl_then [`n - 1`, `m - 1`, `v`] mp_tac) >> fs[]
QED

Theorem mem_drop_impl:
     ∀ l n m v . n ≤ m
    ⇒ MEM v (DROP m l) ⇒ MEM v (DROP n l)
Proof
    Induct >> rw[] >> fs[DROP_def] >>
    Cases_on `m = 0` >> fs[] >>
    Cases_on `n = 0` >> fs[]
    >- (
        Cases_on `v = h` >> fs[] >>
        first_x_assum (qspecl_then [`0`, `m - 1`, `v`] mp_tac) >> fs[])
    >- (first_x_assum (qspecl_then [`n - 1`, `m - 1`, `v`] mp_tac) >> fs[])
QED

Theorem binary_search_spec:
    ∀ a ffi_p cmp cmp_v value value_v elems elem_vs arr_v .
        strict_weak_order cmp ∧
        EqualityType a ∧
        (a --> a --> BOOL) cmp cmp_v ∧
        (a) value value_v ∧
        LIST_REL (a) elems elem_vs ∧
        SORTED (λ x y . cmp x y) elems (* list is sorted *)
    ⇒
        app (ffi_p : 'ffi ffi_proj) ^(fetch_v "binary_search" (basis_st()))
        [cmp_v; arr_v; value_v] (* the arguments *)
        (ARRAY arr_v elem_vs) (* array is in heap with contents elem_vs *)
        (POSTv u_v .
            (ARRAY arr_v elem_vs) *
            &(∃ u .
                OPTION_TYPE NUM u u_v ∧
                (MEM value elems ⇒ ∃ n . u = SOME n ∧ EL n elems = value) ∧
                (* if value present, it is found *)
                (¬MEM value elems ⇒ u = NONE) (* if value not present, NONE *)
             )
        )
Proof
    xcf "binary_search" (basis_st()) >>
    reverse (xfun_spec `search_aux`
        `∀ sublist sublist_vs start finish start_v finish_v .
            sublist = DROP start (TAKE finish elems) ∧
            LIST_REL a sublist sublist_vs ∧
            finish ≥ start ∧
            LENGTH elems ≥ finish ∧
            NUM start start_v ∧
            NUM finish finish_v
        ⇒
            app ffi_p search_aux [start_v; finish_v]
            (ARRAY arr_v elem_vs)
            (POSTv u_v .
                (ARRAY arr_v elem_vs) *
                &(∃ u .
                    OPTION_TYPE NUM u u_v ∧
                    (MEM value sublist ⇒
                        ∃ n . u = SOME n ∧ EL n elems = value ∧
                              start ≤ n ∧ n ≤ finish) ∧
                    (¬(MEM value sublist) ⇒ u = NONE)
                 )
            )`
        )
        >- (
            xlet_auto
                >- xsimpl >>
            xapp >>
            xsimpl >>
            qexists_tac `LENGTH elems` >>
            qexists_tac `elem_vs` >>
            fs[] >>
            imp_res_tac LIST_REL_LENGTH >> fs[] >>
            rw[] >>
            qexists_tac `u` >> fs[] >>
            rw[] >>
            fs[]
            )
        >>  gen_tac >>
            completeInduct_on `LENGTH sublist` >> rw[] >>
            `(∀ x y z . a x y ∧ a x z ⇒ y = z) ∧
            (∀ x y z . a x z ∧ a y z ⇒ x = y) ∧
            (∀ x y u v . a x y ∧ a u v ∧ y ≠ v ⇒ x ≠ u)` by (
              rw[]
              >- imp_res_tac EQTYPE_UNICITY_R
              >- imp_res_tac EQTYPE_UNICITY_L
              >- (CCONTR_TAC >> fs[] >> imp_res_tac EQTYPE_UNICITY_R)
            ) >>
            `LENGTH (DROP start (TAKE finish elems)) = finish - start` by
                fs[LENGTH_DROP, LENGTH_TAKE] >>
            imp_res_tac LIST_REL_LENGTH >>
            Cases_on `finish - start` >> rw[] >> fs[]
            >- (imp_res_tac EQ_LESS_EQ >>
                fs[] >> rw[] >> rfs[] >> rveq >>
                imp_res_tac EQ_LESS_EQ >>
                fs[] >> rw[] >> rfs[] >> rveq >>
                `start_v = finish_v` by fs[NUM_def, INT_def] >>
                rveq >> fs[] >>
                last_x_assum xapp_spec >>
                xlet_auto
                    >- xsimpl >>
                xif >>
                fs[BOOL_def] >>
                xcon >> xsimpl >>
                fs[std_preludeTheory.OPTION_TYPE_def])
            >>
                (*
                    let a = (start ≥ finish) in
                    if a then NONE else
                        let b = start + finish in
                        let mid = b div 2 in
                        let c = Array.sub array mid in
                        let d = (value = c) in
                        if d then (SOME mid) else
                            let e = Array.sub array mid in  - NB e = c
                            let f = cmp value e in
                            if f then (search_aux start mid) else
                                let g = mid + 1 in
                                (search_aux (mid + 1) finish)
                *)
                `finish > start` by fs[] >> fs[ADD1] >>
                last_x_assum xapp_spec >>
                xlet_auto (* a *)
                    >- xsimpl >>
                xif >> fs[BOOL_def] >>
                xlet_auto (* b *)
                    >- xsimpl >>
                xlet_auto (* mid = (finish + start) DIV 2*)
                    >- xsimpl >>
                xlet_auto (* c *)
                    >- (xsimpl >> fs[DIV_LT_X]) >>
                Cases_on `value_v = v` >> fs[]
                >- (rveq >> xlet_auto (* d *)
                        >- xsimpl >>
                    xif >> fs[BOOL_def] >>
                    xcon >>
                    xsimpl >>
                    qexists_tac `SOME ((finish + start) DIV 2)` >>
                    fs[std_preludeTheory.OPTION_TYPE_def] >>
                    fs[X_LE_DIV, DIV_LE_X] >>
                    rw[]
                    >- (fs[LIST_REL_EL_EQN] >>
                        res_tac >>
                        first_x_assum match_mp_tac >>
                        qexists_tac `EL ((finish + start) DIV 2) elem_vs` >>
                        fs[] >> first_x_assum match_mp_tac >> fs[DIV_LT_X])
                    >>  fs[MEM_EL] >>
                        qexists_tac `(finish + start) DIV 2 - start` >>
                        fs[DIV_LT_X] >>
                        `((finish + start) DIV 2) <
                            LENGTH (TAKE finish elems)` by fs[DIV_LT_X] >>
                        fs[EL_DROP] >>
                        fs[EL_TAKE] >>
                        first_x_assum match_mp_tac >>
                        qexists_tac `EL ((finish + start) DIV 2) elem_vs` >>
                        fs[] >>
                        `start ≤ ((finish + start) DIV 2)` by fs[X_LE_DIV] >>
                        imp_res_tac LIST_REL_EL_EQN >> fs[]) >>
                xlet `POSTv bv . ARRAY arr_v elem_vs * &BOOL F bv` (* d *)
                    >- (xapp >> xsimpl >>
                        qexists_tac `EL ((finish + start) DIV 2) elems` >>
                        qexists_tac `value` >> qexists_tac `a` >> fs[] >>
                        imp_res_tac LIST_REL_EL_EQN >> fs[] >> rw[]
                        >- (last_x_assum match_mp_tac >> fs[DIV_LT_X])
                        >>  fs[BOOL_def] >>
                            fs[LIST_REL_EL_EQN] >>
                            qpat_x_assum `∀ y u v . ¬ a u y ∨ _`
                                (qspecl_then [`value_v`, `value`,
                                `EL ((finish + start) DIV 2) elem_vs`]
                            mp_tac) >>
                            fs[] >>
                            rw[] >>
                            `a (EL ((finish + start) DIV 2) elems)
                               (EL ((finish + start) DIV 2) elem_vs)` by (
                               first_assum match_mp_tac >>
                               fs[DIV_LT_X]) >>
                            metis_tac[]) >>
                xif >> fs[BOOL_def] >>
                xlet_auto (* e *)
                    >- (xsimpl >> fs[DIV_LT_X]) >>
                `v = v'` by fs[] >> rveq >> rw[] >>
                xlet `POSTv fv . ARRAY arr_v elem_vs * &(
                    BOOL (cmp value (EL ((finish + start) DIV 2) elems)) fv)`
                    >- (xapp >> xsimpl >>
                        qexists_tac `EL ((finish + start) DIV 2) elems` >>
                        qexists_tac `value` >> qexists_tac `cmp` >>
                        qexists_tac `a` >> fs[] >>
                        imp_res_tac LIST_REL_EL_EQN >>
                        last_x_assum match_mp_tac >>
                        fs[DIV_LT_X]) >>
                qabbrev_tac `mid = (finish + start) DIV 2` >> fs[] >>
                qabbrev_tac `sublist = DROP start (TAKE finish elems)` >>
                xif
                >- ( (* LOWER CASE - value in left half of sublist *)
                    qabbrev_tac `rec_len = mid - start` >>
                    first_x_assum (qspec_then `rec_len` mp_tac) >>
                    strip_tac >> fs[] >>
                    `rec_len < n + 1` by
                        (UNABBREV_TAC "rec_len" >> fs[] >>
                         UNABBREV_TAC "mid" >> fs[DIV_LT_X]) >>
                    fs[] >>
                    first_x_assum (qspec_then `TAKE rec_len sublist` mp_tac) >>
                    strip_tac >> fs[] >>
                    `rec_len = LENGTH (TAKE rec_len sublist)` by (
                        qsuff_tac `rec_len ≤ LENGTH sublist`
                            >- fs[LENGTH_TAKE] >>
                        UNABBREV_TAC "rec_len" >>
                        fs[DIV_LE_X] >> imp_res_tac LIST_REL_LENGTH >> fs[]) >>
                    fs[] >>
                    first_x_assum (qspecl_then
                      [`TAKE rec_len sublist_vs`, `start`, `mid`] mp_tac) >>
                    strip_tac >> fs[] >> last_x_assum xapp_spec >>
                    xsimpl >> fs[] >> UNABBREV_TAC "rec_len" >>
                    imp_res_tac LIST_REL_LENGTH >> rw[]
                    >- (`elems =
                        (TAKE start elems)++sublist++(DROP finish elems)` by (
                            UNABBREV_TAC "sublist" >> fs[] >>
                            (qspecl_then [`elems`, `start`, `finish`]
                                mp_tac) drop_take_partition >>
                            impl_tac >> fs[]) >>
                        UNABBREV_TAC "sublist" >> fs[] >>
                        `DROP start (TAKE mid elems) =
                            TAKE (mid - start) (DROP start elems)` by (
                            match_mp_tac drop_take >>
                            UNABBREV_TAC "mid" >> fs[X_LE_DIV, DIV_LE_X]) >>
                        `DROP start (TAKE finish elems) =
                            TAKE (finish - start) (DROP start elems)` by (
                            match_mp_tac drop_take >>
                            UNABBREV_TAC "mid" >> fs[X_LE_DIV, DIV_LE_X]) >>
                        fs[TAKE_TAKE])
                    >- (UNABBREV_TAC "mid" >> fs[] >> fs[GREATER_EQ, X_LE_DIV])
                    >-  fs[EVERY2_TAKE]
                    >- (
                        qexists_tac `u` >> fs[] >> rw[] >>
                        `DROP start (TAKE mid elems) =
                            TAKE (mid - start) (DROP start elems)` by (
                            match_mp_tac drop_take >>
                            UNABBREV_TAC "mid" >> fs[X_LE_DIV, DIV_LE_X]) >>
                        `DROP start (TAKE finish elems) =
                            TAKE (finish - start) (DROP start elems)` by (
                            match_mp_tac drop_take >>
                            UNABBREV_TAC "mid" >> fs[X_LE_DIV, DIV_LE_X])
                        >- (qsuff_tac
                                `MEM value (DROP start (TAKE mid elems))` >>
                            rw[] >> fs[] >>
                            UNABBREV_TAC "sublist" >>
                            fs[] >>
                            drule strict_weak_order_cmp_TAKE >>
                            disch_then match_mp_tac >>
                            rw[] >> fs[]
                            >- ((qspecl_then [`finish - start`,
                                 `DROP start elems`] mp_tac) MEM_TAKE >>
                                 impl_tac >> fs[] >> rw[] >>
                                 metis_tac[])
                            >- (fs[EL_DROP] >>
                                `start ≤ mid` by (
                                    UNABBREV_TAC "mid" >> fs[X_LE_DIV]) >>
                                metis_tac[SUB_ADD])
                            >- fs[sorted_drop])
                        >- (first_x_assum match_mp_tac >> fs[] >>
                            UNABBREV_TAC "sublist" >> fs[] >>
                            fs[] >>
                            (qspecl_then [`DROP start elems`,
                             `mid - start`, `finish - start`, `value`]
                             mp_tac) mem_take_impl >>
                            strip_tac >> rfs[])
                        )
                )
                >- ( (* UPPER CASE - value in right half of sublist *)
                    xlet_auto (* g *)
                        >- xsimpl >>
                    qabbrev_tac `rec_len = finish - (mid + 1)` >>
                    first_x_assum (qspec_then `rec_len` mp_tac) >>
                    strip_tac >> fs[] >>
                    `rec_len < n + 1` by (
                        UNABBREV_TAC "rec_len" >>
                        fs[] >>
                        qsuff_tac `start < mid + 1` >- fs[] >>
                        UNABBREV_TAC "mid" >>
                        fs[GSYM LE_LT1, X_LE_DIV]) >>
                    fs[] >>
                    first_x_assum (qspec_then
                        `DROP (mid - start + 1) sublist` mp_tac) >>
                    strip_tac >> fs[] >>
                    `rec_len = LENGTH sublist - (mid - start + 1)` by (
                        UNABBREV_TAC "rec_len" >> fs[] >>
                        imp_res_tac LIST_REL_LENGTH >> fs[]) >>
                    fs[] >>
                    first_x_assum (qspecl_then
                        [`DROP (mid - start + 1) sublist_vs`,
                         `mid + 1`, `finish`] mp_tac) >>
                    strip_tac >> fs[] >>
                    last_x_assum xapp_spec >>
                    xsimpl >>
                    fs[] >>
                    imp_res_tac LIST_REL_LENGTH >>
                    rw[]
                    >- (
                        UNABBREV_TAC "sublist" >> fs[] >>
                        `(mid - start + 1) + start = mid + 1` by (
                            `∀ m s . m ≥ s ⇒ m - s + 1 + s = m + 1n` by (
                                Induct >> fs[]) >>
                            first_x_assum match_mp_tac >>
                            UNABBREV_TAC "mid" >>
                            fs[GREATER_EQ, X_LE_DIV]
                        ) >>
                        (qspecl_then [`mid - start + 1`, `start`,
                            `TAKE finish elems`] mp_tac) DROP_DROP >>
                        rw[] >>
                        `mid + 1 ≤ finish` by (
                            UNABBREV_TAC "mid" >> fs[LE_LT1, DIV_LT_X]) >>
                        fs[])
                    >- (qsuff_tac `mid < finish` >> fs[] >>
                        UNABBREV_TAC "mid" >> fs[] >>
                        fs[DIV_LT_X])
                    >-  fs[EVERY2_DROP]
                    >- (
                        qexists_tac `u` >> fs[] >>
                        rw[]
                        >- (
                            qsuff_tac `MEM value
                                (DROP (mid + 1) (TAKE finish elems))` >>
                            rw[] >> fs[]
                            >- (UNABBREV_TAC "mid" >>
                                fs[LE_LT1] >> fs[DIV_LT_X]) >>
                            UNABBREV_TAC "sublist" >> fs[] >>
                            match_mp_tac strict_weak_order_cmp_DROP >>
                            qexists_tac `cmp` >> fs[] >>
                            `mid < finish` by (
                                UNABBREV_TAC "mid" >> fs[DIV_LT_X]) >>
                            fs[EL_TAKE] >>
                            fs[sorted_take] >>
                            reverse(rw[])
                            >- (fs[LIST_REL_EL_EQN] >>
                                first_x_assum (qspecl_then
                                [`value_v`, `EL mid elems`, `EL mid elem_vs`]
                                    mp_tac) >> fs[] >>
                                strip_tac >> metis_tac[]) >>
                            (qspecl_then [`start`, `TAKE finish elems`]
                                mp_tac) MEM_DROP >>
                            impl_tac >> fs[LENGTH_TAKE] >>
                            rw[] >> metis_tac[]
                        )
                        >- (first_x_assum match_mp_tac >> fs[] >>
                            (qspecl_then [`TAKE finish elems`, `start`,
                                `mid + 1`, `value` ] mp_tac) mem_drop_impl >>
                            strip_tac >> fs[] >>
                            UNABBREV_TAC "sublist" >> rfs[] >>
                            first_x_assum match_mp_tac >>
                            UNABBREV_TAC "mid" >>
                            qsuff_tac `start ≤ (finish + start) DIV 2` >>
                            fs[] >> fs[X_LE_DIV])
                        )
                    )
QED

val _ = export_theory ();
