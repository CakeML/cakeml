(*
 An example showing how to use the monadic translator to translate polymorphic
 monadic array quicksort, including exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "poly_array_sortProg"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
(* TODO still some problems with type variables - if 'a not used below,
   some translations fail *)

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| arr : 'a list |>
End

val state_type = ``:'state state_refs``;

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("arr", ``[] : 'state list``, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;


(*******************************************************************************

    TODO MOVE TO ml_monadBaseTheory

*******************************************************************************)

Theorem Msub_Success:
  ∀ l n e x . (Msub e n l = Success x) ⇔ n < LENGTH l ∧ (x = EL n l)
Proof
  Induct >>
  simp[Once ml_monadBaseTheory.Msub_def] >>
  rw[]
  >- (EQ_TAC >> rw[]) >>
  Cases_on `n` >> fs[] >>
  EQ_TAC >> rw[]
QED

Theorem Mupdate_Success:
  ∀ l n x e res . (Mupdate e x n l = Success res)
  ⇔ (n < LENGTH l ∧ (res = LUPDATE x n l))
Proof
  rw[] >>
  EQ_TAC >>
  rw[]
  >- (
    CCONTR_TAC >>
    fs[NOT_LESS] >>
    qspecl_then [`l`,`n`,`x`,`e`] assume_tac
      ml_monadBaseTheory.Mupdate_exn_eq  >>
    fs[]
    )
  >- (
    Cases_on `n < LENGTH l` >> fs[ml_monadBaseTheory.Mupdate_exn_eq] >>
    fs[ml_monadBaseTheory.Mupdate_eq]
  )
  >- (
    fs[ml_monadBaseTheory.Mupdate_eq]
    )
QED


(*******************************************************************************

    PRELIMINARIES

*******************************************************************************)

(* borrowed from examples/quicksortProg *)
val strict_weak_order_def = Define `
  strict_weak_order r ⇔
    transitive r ∧
    (∀ x y. r x y ⇒ ¬ r y x) ∧
    transitive (λ x y. ¬ r x y ∧ ¬ r y x)`;

(* borrowed from examples/quicksortProg *)
Theorem strict_weak_order_alt:
  ∀ r . strict_weak_order r ⇔
    (∀ x y. r x y ⇒ ¬ r y x) ∧
    transitive (λ x y. ¬ r y x)
Proof
  rw [strict_weak_order_def, transitive_def] >>
  metis_tac []
QED

Theorem strict_weak_order_irreflexive:
  ∀ r . strict_weak_order r ⇒ irreflexive r
Proof
  rw[irreflexive_def] >>
  fs[strict_weak_order_def] >>
  metis_tac[]
QED

Theorem TAKE_LUPDATE_LAST:
  ∀ n l new . n < LENGTH l ⇒
    (TAKE (n + 1) (LUPDATE new n l) = TAKE n l ++ [new])
Proof
  Induct >> rw[] >>
  Cases_on `l` >> fs[LUPDATE_def, ADD1]
QED

Theorem PERM_SWAP_FIRST_LAST:
  ∀ middle a b . PERM ([a] ++ middle ++ [b]) ([b] ++ middle ++ [a])
Proof
  Induct >> rw[PERM_SWAP_AT_FRONT] >>
  qsuff_tac `PERM (h::a::(middle ++ [b])) (h::b::(middle ++ [a]))`
  >- (
    strip_tac >>
    metis_tac[PERM_SYM, PERM_FUN_SWAP_AT_FRONT]
  ) >>
  match_mp_tac PERM_MONO >>
  first_x_assum (qspecl_then [`a`,`b`] assume_tac) >> fs[]
QED

(* borrowed from examples/array_searchProg *)
Theorem drop_take:
    ∀ l n m . n ≤ m ∧ m ≤ LENGTH l ⇒
        (DROP n (TAKE m l) = TAKE (m - n) (DROP n l))
Proof
  Induct_on `l` >> rw[] >> fs[TAKE_def] >>
  Cases_on `m = 0` >> fs[] >> fs[DROP_def] >> Cases_on `n = 0` >> fs[]
QED

Theorem PERM_LUPDATE_SWAP:
  ∀ l1 l2 n1 n2 .
    n1 < LENGTH l1 ∧ n2 < LENGTH l1 ∧ n1 ≤ n2 ⇒
    (PERM l1 l2 ⇔ PERM (LUPDATE (EL n1 l1) n2 (LUPDATE (EL n2 l1) n1 l1)) l2)
Proof
  rw[] >>
  Cases_on `n1 = n2` >>
  rveq >> fs[LUPDATE_SAME] >>
  `∃ left middle right .
    (l1 = (left ++ [EL n1 l1] ++ middle ++ [EL n2 l1] ++ right)) ∧
    (LENGTH left = n1) ∧
    (LENGTH middle = n2 - n1 - 1) ∧
    (LENGTH right = LENGTH l1 - n2 - 1)` by (
      qexists_tac `TAKE n1 l1` >>
      qexists_tac `DROP (n1 + 1) (TAKE n2 l1)` >>
      qexists_tac `DROP (n2 + 1) l1` >>
      fs[] >>
      `[EL n2 l1] ++ DROP (n2 + 1) l1 = DROP n2 l1` by fs[DROP_EL_CONS] >>
      `TAKE n1 l1 ++ [EL n1 l1] = TAKE (n1 + 1) l1` by fs[TAKE_EL_SNOC] >>
      simp[drop_take] >>
      simp[GSYM TAKE_SUM] >>
      qsuff_tac `l1 = TAKE n2 l1 ++ DROP n2 l1`
      >- (strip_tac >> metis_tac[APPEND_ASSOC]) >> fs[]) >>
  rw[] >> fs[] >>
  rename1 `l1 = _ ++ [a] ++ _ ++ [b] ++ _` >>
  `LUPDATE b (LENGTH left) l1 =
    left ++ [b] ++ middle ++ [b] ++ right` by (
      rveq >> simp[] >>
      qspecl_then [`left`,
        `[a] ++ middle ++ [b] ++ right`,
        `LENGTH left`, `b`] assume_tac LUPDATE_APPEND2 >>
      fs[LUPDATE_def]
  ) >>
  rveq >> fs[] >>
  `LENGTH (left ++ [b] ++ middle) ≤ n2` by fs[] >>
  drule LUPDATE_APPEND2 >>
  disch_then (
    qspecl_then [`[b] ++ right`, `a`] assume_tac) >>
  fs[LUPDATE_def] >>
  qsuff_tac `PERM
    (left ++ [a] ++ middle ++ [b] ++ right) (left ++ [b] ++ middle ++ a::right)`
  >- (
    strip_tac >> EQ_TAC >> rw[] >>
    metis_tac[PERM_SYM, PERM_TRANS]
    ) >>
  assume_tac (GSYM PERM_APPEND_IFF |> REWRITE_RULE [EQ_IMP_THM]) >>
  first_x_assum mp_tac >> strip_tac >>
  first_x_assum (
    qspecl_then [`right`,
    `left ++ [a] ++ middle ++ [b]`,
    `left ++ [b] ++ middle ++ [a]`
    ] mp_tac) >> strip_tac >>
  first_x_assum kall_tac >>
  first_x_assum mp_tac >>
  reverse(impl_tac)
  >- (
    strip_tac >>
    match_mp_tac PERM_TRANS >>
    asm_exists_tac >> simp[] >>
    `∀ l1 l2 . (l1 = l2) ⇒ PERM l1 l2` by simp[PERM_REFL] >>
    simp[]
    ) >>
  first_x_assum (
    qspecl_then [`left`,
      `[a] ++ middle ++ [b]`,
      `[b] ++ middle ++ [a]`
  ] mp_tac) >> strip_tac >>
  first_x_assum kall_tac >>
  first_x_assum mp_tac >>
  impl_tac >> simp[] >>
  qspecl_then [`middle`,`a`,`b`] mp_tac PERM_SWAP_FIRST_LAST >>
  simp[]
QED

Theorem LAST_TAKE:
  ∀ l n . n < LENGTH l ∧ n ≠ 0 ⇒
    (LAST (TAKE n l) = EL (n - 1) l)
Proof
  Induct >- rw[] >>
  strip_tac >>
  Induct >> rw[] >>
  fs[LAST_DEF] >>
  Cases_on `n` >> fs[ADD1] >>
  Cases_on `l` >> fs[]
QED

Theorem PERM_narrow_lemma:
  ∀ n m l l' .
    n ≤ m ∧ m ≤ LENGTH l ∧
    (∀ k . k < n ⇒ (EL k l = EL k l')) ∧
    (∀ k . k ≥ m ∧ k < LENGTH l ⇒ (EL k l = EL k l')) ∧
    PERM l l'
  ⇒ PERM (DROP n (TAKE m l)) (DROP n (TAKE m l'))
Proof
  rw[] >>
  `(l  = TAKE n (TAKE m l ) ++ (DROP n (TAKE m l )) ++ DROP m l ) ∧
   (l' = TAKE n (TAKE m l') ++ (DROP n (TAKE m l')) ++ DROP m l')` by
    fs[TAKE_DROP] >>
  `(TAKE n (TAKE m l) = TAKE n (TAKE m l')) ∧
   (DROP m l = DROP m l')` by (
    imp_res_tac PERM_LENGTH >>
    rw[LIST_EQ_REWRITE, EL_TAKE, EL_DROP]
   ) >>
  metis_tac[PERM_APPEND_IFF]
QED

Theorem PERM_narrow_EL:
∀ n m l l' .
    n ≤ m ∧ m ≤ LENGTH l ∧
    (∀ k . k < n ⇒ (EL k l = EL k l')) ∧
    (∀ k . k ≥ m ∧ k < LENGTH l ⇒ (EL k l = EL k l')) ∧
    PERM l l'
  ⇒ (∀ k . k ≥ n ∧ k < m ⇒ ∃ k' . k' ≥ n ∧ k' < m ∧ (EL k l = EL k' l'))
Proof
  rw[] >>
  imp_res_tac PERM_LENGTH >>
  qspecl_then [`n`,`m`,`l`,`l'`] assume_tac PERM_narrow_lemma >>
  rfs[] >>
  imp_res_tac MEM_PERM >>
  ntac 5 (first_x_assum kall_tac) >>
  fs[MEM_EL] >>
  first_x_assum (qspec_then `EL k l` assume_tac) >>
  fs[EQ_IMP_THM] >>
  first_x_assum kall_tac >>
  qpat_x_assum `_ ⇒ ∃ n' . n' < LENGTH (TAKE m l') - n ∧ _` mp_tac >>
  reverse(impl_tac)
  >- (
    rw[] >>
    `n' + n < LENGTH (TAKE m l')` by fs[] >>
    `n' + n < m` by fs[] >>
    fs[EL_DROP, EL_TAKE] >>
    qexists_tac `n + n'` >> fs[]
    ) >>
  qexists_tac `k - n` >> fs[EL_DROP, EL_TAKE]
QED

(*******************************************************************************

    SCAN_UPPER / SCAN_LOWER

*******************************************************************************)

val scan_lower_def = mtDefine "scan_lower" `
  scan_lower (cmp : 'a -> 'a -> bool) pivot lb = do
    elem <- arr_sub lb;
    if cmp elem pivot then
      (scan_lower cmp pivot (lb + 1))
    else (return lb)
  od
`
(
  fs[fetch "-" "arr_sub_def"] >>
  fs[ml_monadBaseTheory.Marray_sub_def] >>
  WF_REL_TAC `measure (λ (_,_,lb,s) . LENGTH (s.arr) - lb)` >>
  rw[] >>
  imp_res_tac Msub_Success >>
  DECIDE_TAC
)


val scan_upper_def = Define `
  scan_upper (cmp : 'a -> 'a -> bool) pivot ub =
    if ub = 0n then return ub else do
    elem <- arr_sub (ub - 1);
    if cmp pivot elem then
      scan_upper cmp pivot (ub - 1)
    else return (ub - 1)
  od
`

Theorem scan_lower_index:
  ∀ cmp pivot lb s new_lb s' .
    (scan_lower cmp pivot lb s = (Success new_lb, s'))
  ⇒ lb < LENGTH s.arr ∧ lb ≤ new_lb ∧ new_lb < LENGTH s.arr
Proof
  recInduct (theorem "scan_lower_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once scan_lower_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def] >>
  EVERY_CASE_TAC >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[ml_monadBaseTheory.st_ex_return_def] >>
  imp_res_tac Msub_Success >>
  rw[] >> fs[]
QED

Theorem scan_lower_state:
  ∀ cmp pivot lb s new_lb s' .
    (scan_lower cmp pivot lb s = (Success new_lb, s'))
  ⇒ (s = s') ∧ ¬ cmp (EL new_lb s.arr) pivot ∧
    (∀ index . lb ≤ index ∧ index < new_lb ⇒ cmp (EL index s.arr) pivot)
Proof
  recInduct (theorem "scan_lower_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once scan_lower_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def] >>
  EVERY_CASE_TAC >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[ml_monadBaseTheory.st_ex_return_def] >>
  rw[] >> fs[] >>
  rveq >>
  imp_res_tac Msub_Success >>
  fs[] >>
  imp_res_tac scan_lower_index >>
  rveq >>
  Cases_on `index = lb` >> fs[]
QED

Theorem scan_upper_index:
  ∀ cmp pivot ub s new_ub s' .
    (scan_upper cmp pivot ub s = (Success new_ub, s'))
  ⇒ (new_ub < ub ∨ ((new_ub = 0) ∧ (ub = 0))) ∧ new_ub ≤ LENGTH s.arr
Proof
  recInduct (theorem "scan_upper_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once scan_upper_def] >>
  fs[fetch "-" "raise_Subscript_def"] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def] >>
  EVERY_CASE_TAC >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def]
  >- (
    rveq >> strip_tac >>
    first_x_assum drule >>
    disch_then drule >>
    DECIDE_TAC
    )
  >- (
    rw[] >>
    rveq >>
    imp_res_tac Msub_Success >>
    rveq >>
    fs[]
  )
QED

Theorem scan_upper_state:
  ∀ cmp pivot ub s new_ub s'.
    (scan_upper cmp pivot ub s = (Success new_ub, s'))
  ⇒ (s = s') ∧ (new_ub ≠ 0 ⇒ ¬ cmp pivot (EL new_ub s.arr)) ∧
    (∀ index . new_ub < index ∧ index < ub ⇒ cmp pivot (EL index s.arr))
Proof
  recInduct (theorem "scan_upper_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once scan_upper_def] >>
  fs[fetch "-" "raise_Subscript_def"] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def] >>
  EVERY_CASE_TAC >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  imp_res_tac Msub_Success >>
  strip_tac >>
  rveq >> fs[] >>
  first_x_assum drule >>
  disch_then drule >>
  fs[] >>
  rw[] >>
  fs[] >>
  imp_res_tac scan_upper_index >>
  rveq >>
  Cases_on `new_ub + 1 = ub` >> fs[] >>
  Cases_on `index = ub - 1` >> fs[]
QED


(*******************************************************************************

    PARTITION

*******************************************************************************)

val partition_helper_def = mtDefine "partition_helper" `
  partition_helper (cmp : 'a -> 'a -> bool) pivot lb ub =
    if ub ≤ lb then return ub else do
    new_lb <- scan_lower cmp pivot lb;
    new_ub <- scan_upper cmp pivot ub;
    if new_lb < new_ub then (do
      low_elem <- arr_sub new_lb;
      high_elem <- arr_sub new_ub;
      update_arr new_lb high_elem;
      update_arr new_ub low_elem;
      partition_helper cmp pivot new_lb new_ub
    od)
    else
      (return new_ub)
  od
`
(
  WF_REL_TAC `measure ( λ (_,_,lb,ub,_) . ub - lb)` >>
  rw[] >>
  fs[NOT_LESS_EQUAL] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  imp_res_tac Msub_Success >>
  rveq >> fs[] >>
  imp_res_tac scan_lower_index >>
  reverse (imp_res_tac scan_upper_index) >>
  fs[prim_recTheory.NOT_LESS_0]
)

(* TODO fix s5 / s6 problem - can get away with it for now,
   but probably not in general... *)
(*
val partition_helper_def = tDefine "partition_helper" `
  partition_helper (cmp : 'a -> 'a -> bool) pivot lb ub s =
    if ub ≤ lb then (return ub s) else (
      monad_bind (scan_lower cmp pivot lb)
      (λ new_lb s1 .
        monad_bind (scan_upper cmp pivot ub)
        (λ new_ub s2 .
          if new_lb < new_ub then (
            monad_bind (arr_sub new_lb)
            (λ low_elem s3.
              monad_bind (arr_sub new_ub)
              (λ high_elem s4 .
                monad_ignore_bind (update_arr new_lb high_elem)
                ( λ s5 .
                  monad_ignore_bind (update_arr new_ub low_elem)
                  (λ s6 . partition_helper cmp pivot new_lb new_ub s5)
                s5)
              s4)
            s3 )
          s2 ) else (return new_ub s2)
        )
      s1 )
    ) s
`
*)

Theorem partition_helper_index:
  ∀ cmp pivot lb ub s result s'.
    strict_weak_order cmp ∧
    ub ≤ LENGTH s.arr ∧ lb < ub ∧
    (∃ index . index ≥ lb ∧ index < ub ∧ ¬ cmp pivot (EL index s.arr)) ∧
    (partition_helper cmp pivot lb ub s = (Success result, s'))
  ⇒ result ≥ lb ∧ result < ub ∧
    ¬ (cmp pivot (EL result s'.arr))
Proof
  recInduct (theorem "partition_helper_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  once_rewrite_tac [partition_helper_def] >>
  strip_tac >> fs[] >>
  fs[ml_monadBaseTheory.st_ex_return_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def] >>
  fs[ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  qpat_x_assum `(if _ then _ else _) _ = (Success _, _)` mp_tac >>
  IF_CASES_TAC >> fs[] >>
  ntac 4 (reverse (FULL_CASE_TAC >> rveq >> fs[])) >>
  rename1 `scan_upper _ _ _ _ = (Success new_ub, _)` >>
  rename1 `scan_lower _ _ _ _ = (Success new_lb, _)` >>
  fs[NOT_LESS_EQUAL] >>
  imp_res_tac scan_lower_index >> imp_res_tac scan_upper_index >> fs[] >>
  imp_res_tac scan_lower_state >> fs[] >>
  drule scan_upper_state >>
  strip_tac >> fs[] >>
  rveq >> fs[] >>
  reverse(FULL_CASE_TAC >> rveq >> fs[])
  >- (
    strip_tac >>
    rveq >> fs[] >>
    fs[NOT_LESS] >>
    rw[]
    >- (Cases_on `new_ub < index` >> fs[] >> res_tac) >>
    Cases_on `new_ub = 0` >> fs[] >>
    first_x_assum (qspec_then `index` mp_tac) >>
    strip_tac >>
    rfs[] >>
    rveq >> fs[]
    ) >>
  ntac 4 (reverse(FULL_CASE_TAC >> rveq >> fs[])) >>
  first_x_assum (qspec_then `<| arr := a'3' |>` mp_tac) >>
  strip_tac >> fs[] >> rfs[] >>
  strip_tac >> fs[] >>
  fs[Msub_Success, Mupdate_Success] >>
  rveq >> fs[] >> rfs[] >>
  Cases_on `new_ub = 0` >> fs[] >>
  fs[EL_LUPDATE] >>
  qpat_x_assum `(∃ index . _) ⇒ _` mp_tac >>
  impl_tac >> fs[] >>
  qexists_tac `new_lb` >> fs[]
QED

Theorem partition_helper_result:
  ∀ cmp pivot lb ub s result s' .
    strict_weak_order cmp ∧
    ub ≤ LENGTH s.arr ∧
    (partition_helper cmp pivot lb ub s = (Success result, s'))
  ⇒ (∀ k . k > result ∧ k < ub ⇒ ¬ cmp (EL k s'.arr) pivot) ∧
    (∀ k . k ≥ lb ∧ k < result ⇒ cmp (EL k s'.arr) pivot) ∧
    (∀ k . k < lb ∨ k ≥ ub ⇒ (EL k s'.arr = EL k s.arr)) ∧
    (PERM s.arr s'.arr)
Proof
  recInduct (theorem "partition_helper_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  once_rewrite_tac [partition_helper_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  strip_tac >>
  EVERY_CASE_TAC >> fs[]
  >- (
    first_x_assum drule >>
    rpt (disch_then drule) >>
    fs[] >> strip_tac >>
    rveq >> fs[] >>
    first_x_assum (qspec_then `<| arr := a'6' |>` mp_tac) >>
    fs[] >> strip_tac >>
    rename1 `scan_upper _ _ _ _ = (Success new_ub, _)` >>
    rename1 `scan_lower _ _ _ _ = (Success new_lb, _)` >>
    rename1 `Msub _ new_ub _ = Success nub_elem` >>
    rename1 `Msub _ new_lb _ = Success nlb_elem` >>
    Cases_on `new_ub = 0` >> fs[] >>
    imp_res_tac scan_upper_state >> rveq >> fs[] >>
    imp_res_tac scan_lower_state >> rveq >> fs[] >>
    imp_res_tac (Mupdate_Success |> INST_TYPE [beta |-> ``:state_exn``]) >>
    rveq >> fs[] >>
    imp_res_tac scan_upper_index >> fs[] >>
    imp_res_tac scan_lower_index >> fs[] >>
    rw[] >> fs[EL_LUPDATE]
    >- (
      Cases_on `k < new_ub` >> fs[NOT_LESS] >>
      IF_CASES_TAC >> fs[] >>
      fs[Msub_Success] >>
      fs[strict_weak_order_def]
      )
    >- (
      Cases_on `k < new_lb` >> fs[] >>
      fs[EL_LUPDATE]
      )
    >- (
      fs[Msub_Success] >>
      rveq >> fs[] >>
      Cases_on `new_lb = new_ub` >> fs[] >>
      Cases_on `new_ub ≥ new_lb` >> fs[] >>
      qspecl_then [`r.arr`, `s'.arr`, `new_lb`, `new_ub`]
        assume_tac PERM_LUPDATE_SWAP >>
      fs[]
      )
  ) >>
  rveq >> fs[NOT_LESS] >>
  first_x_assum drule >>
  strip_tac >>
  rfs[] >>
  rename1 `scan_upper _ _ _ _ = (Success new_ub, _)` >>
  rename1 `scan_lower _ _ _ _ = (Success new_lb, _)` >>
  imp_res_tac scan_upper_state >> rveq >> fs[] >>
  imp_res_tac scan_lower_state >> rveq >> fs[] >>
  imp_res_tac scan_upper_index >> fs[] >>
  imp_res_tac scan_lower_index >> fs[] >>
  fs[strict_weak_order_def]
QED

Theorem partition_helper_range_shrink_upper:
 ∀ cmp pivot lb ub s result s'.
    strict_weak_order cmp ∧
    ub ≤ LENGTH s.arr ∧ lb < ub ∧
    (∃ index . index ≥ lb ∧ index < ub - 1 ∧ (EL index s.arr = pivot)) ∧
    (partition_helper cmp pivot lb ub s = (Success result, s'))
  ⇒ (result ≥ lb ∧ result < ub - 1)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `partition_helper _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac [partition_helper_def] >>
  fs[ml_monadBaseTheory.st_ex_return_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def] >>
  fs[ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  EVERY_CASE_TAC >> fs[] >>
  rename1 `scan_upper _ _ _ _ = (Success new_ub, _)` >>
  rename1 `scan_lower _ _ _ _ = (Success new_lb, _)`
  >- (
    strip_tac >>
    fs[Msub_Success, Mupdate_Success] >> rveq >>
    drule partition_helper_index >> fs[] >>
    disch_then (qspecl_then [`EL index s.arr`, `new_lb`, `new_ub`] mp_tac) >>
    fs[] >>
    disch_then (
      qspecl_then [`<| arr := LUPDATE (EL new_lb r'.arr) new_ub
                      (LUPDATE (EL new_ub r'.arr) new_lb r'.arr) |>`] mp_tac) >>
    strip_tac >> rfs[] >>
    drule scan_upper_state >>
    strip_tac >> rveq >> fs[] >>
    imp_res_tac scan_upper_index >> fs[] >>
    fs[EL_LUPDATE] >>
    imp_res_tac scan_lower_index >>
    imp_res_tac scan_lower_state >> fs[] >>
    qsuff_tac `result ≥ new_lb ∧ result < new_ub ∧
                  ¬cmp (EL index r.arr) (EL result s'.arr)` >> fs[] >>
    first_x_assum match_mp_tac >>
    Cases_on `new_ub = 0` >> fs[] >>
    qexists_tac `new_lb` >> fs[] >>
    imp_res_tac scan_upper_index
    ) >>
  fs[NOT_LESS] >> strip_tac >>
  rveq >> fs[] >>
  imp_res_tac scan_upper_index >> imp_res_tac scan_lower_index >> fs[] >>
  imp_res_tac scan_lower_state >> fs[] >> rveq >>
  drule scan_upper_state >>
  strip_tac >> rveq >> fs[] >>
  Cases_on `new_ub = 0` >> fs[]
  >- (
    first_x_assum (qspec_then `index` assume_tac) >> rfs[] >>
    Cases_on `index = 0` >> fs[] >>
    imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]
    ) >>
  Cases_on `new_lb = new_ub` >> fs[] >>
  first_x_assum (qspec_then `index` assume_tac) >> rfs[] >>
  first_x_assum (qspec_then `index` assume_tac) >> rfs[] >>
  imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]
QED


(*******************************************************************************

    ARRAY SETTERS AND GETTERS

*******************************************************************************)

val array_set_aux_def = Define `
  (array_set_aux _ [] = return ()) ∧
  (array_set_aux n (x::xs) = do
    update_arr n x;
    array_set_aux (n + 1n) xs
  od)
`;

val array_set_def = Define `
  array_set l = array_set_aux 0n l
`;

Theorem array_set_aux_Success:
  ∀ l n s . (LENGTH (DROP n s.arr) = LENGTH l)
  ⇒ ∃ result . (array_set_aux n l s = (Success (), result)) ∧
    (DROP n result.arr = l) ∧
    (TAKE n s.arr = TAKE n result.arr) ∧
    (LENGTH s.arr = LENGTH result.arr)
Proof
  Induct >>
  rw[] >>
  simp[Once array_set_aux_def] >>
  fs[ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
  >- fs[DROP_LENGTH_TOO_LONG] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  fs[ADD1] >> rveq >>
  qspecl_then [`s.arr`,`n`,`h`,`Subscript`] assume_tac
    (Mupdate_Success |> INST_TYPE [beta |-> ``:state_exn``]) >> fs[] >>
  first_x_assum (qspec_then `LUPDATE h n s.arr` mp_tac) >> strip_tac >> fs[] >>
  fs[EQ_IMP_THM] >>
  first_x_assum (qspecl_then [
    `n + 1`, `<| arr := LUPDATE h n s.arr |>`] mp_tac) >>
  fs[] >> strip_tac >> rfs[] >>
  `n < LENGTH s.arr` by fs[] >>
  fs[TAKE_LUPDATE_LAST, TAKE_SUM, TAKE1_DROP, DROP_EL_CONS]
QED

Theorem array_set_Success:
  ∀ l s . (LENGTH l = LENGTH s.arr)
  ⇒ ∃ s' . (array_set l s = (Success (), s')) ∧ (s'.arr = l)
Proof
  rw[] >>
  fs[array_set_def] >>
  qspecl_then [`l`,`0n`,`s`] assume_tac array_set_aux_Success >>
  fs[] >>
  metis_tac[]
QED

val array_get_aux_def = tDefine "array_get_aux" `
  array_get_aux length n =
    if n ≥ length then return [] else do
      rest <- array_get_aux length (n + 1);
      elem <- arr_sub n;
      return (elem :: rest)
    od
`
(
  WF_REL_TAC `measure (λ (length, n) . length - n)`
)

val array_get_def = Define `
  array_get () = do
    len <- arr_length;
    array_get_aux len 0n
  od
`

Theorem array_get_aux_Success:
  ∀ length n s . (LENGTH s.arr = length)
  ⇒ ∃ result . (array_get_aux length n s = (Success result, s)) ∧
    (result = DROP n s.arr)
Proof
  recInduct (theorem "array_get_aux_ind") >>
  rw[] >>
  simp[Once array_get_aux_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  IF_CASES_TAC >> fs[]
  >- (qspecl_then [`s.arr`, `n`] assume_tac DROP_LENGTH_TOO_LONG >> fs[]) >>
  first_x_assum (qspec_then `s` mp_tac) >> strip_tac >> fs[] >>
  fs[NOT_GREATER_EQ, ADD1, LE_LT1] >>
  imp_res_tac (Msub_Success |> INST_TYPE [beta |-> ``:state_exn``]) >>
  fs[] >>
  fs[DROP_EL_CONS]
QED

Theorem array_get_Success:
  ∀ s . array_get () s = (Success s.arr, s)
Proof
  simp[Once array_get_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def] >>
  fs[fetch "-" "arr_length_def", ml_monadBaseTheory.Marray_length_def] >>
  rw[] >>
  qspecl_then [`LENGTH s.arr`,`0n`,`s`] assume_tac array_get_aux_Success >>
  rw[]
QED


(*******************************************************************************

    QUICKSORT

*******************************************************************************)

val quicksort_aux_def = mtDefine "quicksort_aux" `
  quicksort_aux cmp lower upper =
    if lower ≥ upper then return ()
    else do
      pivot <- arr_sub lower;
      part_index <- partition_helper cmp pivot lower (upper + 1);
      if part_index ≥ lower ∧ part_index < upper then do
        quicksort_aux cmp lower part_index;
        quicksort_aux cmp (part_index + 1) upper
      od
      else return ()
    od
`
(
  WF_REL_TAC `measure (λ (_, lower, upper, _) . upper - lower)`
)

Theorem quicksort_aux_result:
  ∀ cmp lower upper s result s' .
    upper ≥ lower ∧
    strict_weak_order cmp ∧ upper < LENGTH s.arr ∧
    (∃index. index ≥ lower ∧ index < upper + 1 ∧
      ¬cmp (EL lower s.arr) (EL index s.arr)) ∧
    (quicksort_aux cmp lower upper s = (Success result, s'))
  ⇒ PERM s.arr s'.arr ∧
    (∀ k . k < lower ⇒ (EL k s.arr = EL k s'.arr)) ∧
    (∀ k . k > upper ∧ k < LENGTH s.arr ⇒ (EL k s.arr = EL k s'.arr)) ∧
    SORTED (λ x y . ¬ cmp y x) (DROP lower (TAKE (upper + 1) s'.arr))
Proof
  recInduct (theorem "quicksort_aux_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once quicksort_aux_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  EVERY_CASE_TAC >> fs[]
  >- (
      rw[] >>
      `upper = lower` by fs[] >>
      rveq >> fs[] >>
      `DROP lower (TAKE (lower + 1) s.arr) = TAKE 1 (DROP lower s.arr)`
        by fs[drop_take] >>
      rveq >> fs[TAKE1_DROP]
    )
  >- (
    strip_tac >> fs[] >>
    rename1 `partition_helper _ _ _ _ _ = (Success part_index, part_state)` >>
    rename1 `quicksort_aux _ lower _ _ = (_, lsort_state)` >>
    rename1 `quicksort_aux _ _ upper _ = (_, final_state)` >>
    fs[Msub_Success] >>
    rveq >> fs[] >>
    `upper + 1 ≤ LENGTH s.arr` by fs[] >>
    drule partition_helper_result >>
    fs[] >>
    rpt (disch_then drule) >>
    fs[] >>
    strip_tac >>
    last_x_assum (qspec_then `part_state` assume_tac) >>
    rfs[] >>
    imp_res_tac PERM_LENGTH >> fs[] >> rfs[] >>
    fs[LE_LT1] >> rfs[] >>
    (* TODO clean this up - need to discharge existential hyp on assumption *)
    `PERM part_state.arr lsort_state.arr ∧
         (∀k. k < lower ⇒ (EL k s.arr = EL k lsort_state.arr)) ∧
         (∀k.
              k > part_index ∧ k < LENGTH part_state.arr ⇒
              (EL k part_state.arr = EL k lsort_state.arr)) ∧
         SORTED (λx y. ¬cmp y x)
           (DROP lower (TAKE (part_index + 1) lsort_state.arr))` by (
        first_x_assum match_mp_tac >> qexists_tac `lower` >>
        imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]
      ) >> rfs [] >>
    imp_res_tac PERM_LENGTH >> fs[] >>
    `PERM lsort_state.arr final_state.arr ∧
         (∀k.
              k < part_index + 1 ⇒
              (EL k lsort_state.arr = EL k final_state.arr)) ∧
         (∀k.
              k > upper ∧ k < LENGTH lsort_state.arr ⇒
              (EL k lsort_state.arr = EL k final_state.arr)) ∧
         SORTED (λx y. ¬cmp y x)
           (DROP (part_index + 1) (TAKE (upper + 1) final_state.arr))` by (
        first_x_assum match_mp_tac >> qexists_tac `part_index + 1` >>
        imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]
      ) >> fs[] >>
    rw[]
    >- (imp_res_tac PERM_TRANS >> fs[])
    >- (
      fs[GREATER_EQ, LE_LT1] >>
      `EL k lsort_state.arr = EL k final_state.arr` by fs[] >>
      `EL k part_state.arr = EL k lsort_state.arr` by fs[] >>
      `EL k part_state.arr = EL k s.arr` by
        (first_x_assum match_mp_tac >> fs[]) >>
      fs[]
      )
    >- (
      `upper + 1 ≤ LENGTH s.arr` by fs[] >>
      drule partition_helper_index >>
      disch_then drule >>
      disch_then (qspecl_then [`EL lower s.arr`, `lower`] assume_tac) >>
      rfs[] >>
      `¬cmp (EL lower s.arr) (EL part_index part_state.arr)` by (
        first_x_assum match_mp_tac >> qexists_tac `lower` >>
        imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]) >>
      fs[] >> rw[] >>
      imp_res_tac PERM_LENGTH >> rw[] >>
      `DROP lower (TAKE (part_index + 1) final_state.arr) =
        TAKE (part_index + 1 - lower) (DROP lower final_state.arr)` by (
        match_mp_tac drop_take >> fs[]) >>
      rveq >>
      `DROP lower (TAKE (part_index + 1) lsort_state.arr) =
        DROP lower (TAKE (part_index + 1) final_state.arr)` by (
          match_mp_tac LIST_EQ >>
          fs[] >> rw[] >>
          fs[EL_DROP, EL_TAKE]
        ) >>
        rveq >> fs[] >>
      `DROP lower (TAKE (upper + 1) final_state.arr) =
        DROP lower (TAKE (part_index + 1) final_state.arr) ++
          DROP (part_index + 1) (TAKE (upper + 1) final_state.arr)` by (
          fs[drop_take] >>
          `DROP (part_index + 1) final_state.arr =
            DROP (part_index + 1 - lower) (DROP lower final_state.arr)`
              by fs[DROP_DROP] >>
          rveq >> fs[] >>
          fs[GSYM TAKE_SUM]) >>
      rw[] >>
      fs[SORTED_APPEND_IFF] >>
      Cases_on `DROP lower final_state.arr = []` >> fs[] >>
      Cases_on
        `DROP (part_index + 1) (TAKE (upper + 1) final_state.arr) = []` >>
      fs[HD_DROP, LAST_TAKE, EL_TAKE, EL_DROP] >>
      (* TODO HOL simplification hangs without removing kall_tac below *)
      ntac 5 (first_x_assum kall_tac) >>
      rpt (qpat_x_assum `SORTED _ _` kall_tac) >>
      rpt (qpat_x_assum `quicksort_aux _ _ _ _ = _` kall_tac) >>
      qpat_x_assum `partition_helper _ _ _ _ _ = _` kall_tac >>
      `EL part_index final_state.arr = EL part_index lsort_state.arr` by fs[] >>
      qsuff_tac
        `¬ cmp (EL (part_index + 1) final_state.arr) (EL lower s.arr) ∧
         ¬ cmp (EL lower s.arr) (EL part_index lsort_state.arr)`
      >- (
        strip_tac >>
        imp_res_tac strict_weak_order_alt >>
        first_x_assum mp_tac >> once_rewrite_tac [transitive_def] >>
        strip_tac >>
        metis_tac[]
        ) >>
      reverse (strip_tac)
      >- (
        (* TODO as above, kall_tac needed *)
        qpat_x_assum
          `∀ k . _ ∧ k < LENGTH final_state.arr ⇒ _` kall_tac >>
        first_x_assum kall_tac >>
        qspecl_then [
          `lower`,
          `part_index + 1`,
          `lsort_state.arr`,
          `part_state.arr`
        ] mp_tac PERM_narrow_EL >>
        strip_tac >>
        rfs[GREATER_EQ, LE_LT1] >>
        `PERM lsort_state.arr part_state.arr`
          by metis_tac[PERM_TRANS, PERM_SYM] >>
        fs[] >>
        first_x_assum (qspec_then `part_index` assume_tac) >>
        rfs[] >>
        Cases_on `k' = part_index` >> fs[] >>
        fs[strict_weak_order_def]
        )
      >- (
        first_x_assum kall_tac >>
        qspecl_then [
          `part_index + 1`,
          `upper + 1`,
          `final_state.arr`,
          `lsort_state.arr`
        ] mp_tac PERM_narrow_EL >>
        strip_tac >>
        rfs[] >>
        `PERM final_state.arr lsort_state.arr`
          by metis_tac[PERM_TRANS, PERM_SYM] >>
        fs[] >>
        first_x_assum (qspec_then `part_index + 1` assume_tac) >>
        rfs[] >>
        `EL k' lsort_state.arr = EL k' part_state.arr` by fs[] >>
        qsuff_tac `¬ cmp (EL k' part_state.arr) (EL lower s.arr)`
        >- (strip_tac >> metis_tac[]) >>
        first_x_assum match_mp_tac >>
        fs[]
        )
      )
    )
  >>
    strip_tac >>
    rveq >> fs[Msub_Success] >>
    rveq >> fs[NOT_GREATER_EQ, LE_LT1, ADD1, NOT_LESS] >>
    rename1 `partition_helper _ _ _ _ _ = (Success part_index, _)` >>
    `upper + 1 ≤ LENGTH s.arr` by fs[] >>
    `lower < upper + 1` by fs[] >>
    drule partition_helper_index >>
    rpt (disch_then drule) >>
    disch_then (qspec_then `EL lower s.arr` assume_tac) >>
    rfs[]
    >- (
      first_x_assum (qspec_then `index` assume_tac) >>
      rfs[]
      )
    >- (
      res_tac >>
      `part_index = upper` by fs[] >>
      rveq >>
      fs[] >>
      `part_index + 1 ≤ LENGTH s.arr` by fs[] >>
      drule partition_helper_range_shrink_upper >>
      disch_then (qspecl_then
        [`EL lower s.arr`, `lower`, `part_index + 1`, `s`] assume_tac) >>
      rfs[] >>
      fs[NOT_GREATER_EQ, ADD1, LE_LT1, NOT_LESS] >>
      first_x_assum (qspec_then `lower` assume_tac) >>
      fs[]
      )
QED

val quicksort_def = Define `
  (quicksort cmp [] = return []) ∧
  (quicksort cmp (x::xs) = do
    alloc_arr (LENGTH (x::xs)) x;
    array_set (x::xs);
    quicksort_aux cmp 0n (LENGTH (x::xs) - 1n);
    array_get ()
  od)
`;

Theorem quicksort_result:
  ∀ l l' cmp s s' .
    strict_weak_order cmp ∧
    (quicksort cmp l s = (Success l', s'))
  ⇒ PERM l l' ∧ SORTED (λ x y . ¬ cmp y x) l'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `l` >> fs[quicksort_def] >>
  fs[ml_monadBaseTheory.st_ex_return_def] >>
  fs[ml_monadBaseTheory.st_ex_ignore_bind_def]
  >- (rveq >> fs[SORTED_DEF]) >>
  EVERY_CASE_TAC >> fs[ADD1] >>
  fs[fetch "-" "alloc_arr_def", ml_monadBaseTheory.Marray_alloc_def] >>
  rveq >> fs[] >>
  qspecl_then [`h::t`,`<| arr:= REPLICATE (LENGTH t + 1) h |>`]
    assume_tac array_set_Success >>
  fs[LENGTH_REPLICATE] >>
  fs[] >> rveq >>
  `LENGTH t ≥ 0` by fs[] >>
  drule quicksort_aux_result >>
  disch_then drule >>
  rename1 `quicksort_aux _ _ _ set_state = (_, sorted_state)` >>
  disch_then (qspec_then `set_state` assume_tac) >>
  rfs[] >>
  qspec_then `sorted_state` assume_tac array_get_Success >>
  fs[] >> rveq >>
  qpat_x_assum `_ ⇒ _` mp_tac >>
  impl_tac
  >- (
    qexists_tac `0` >>
    imp_res_tac strict_weak_order_irreflexive >> fs[irreflexive_def]
    ) >>
  rw[] >>
  imp_res_tac PERM_LENGTH >>
  fs[ADD1]
QED


(*******************************************************************************

    RUN QUICKSORT / QSORT

*******************************************************************************)

val run_init_state_def = define_run state_type [] "init_state";

val run_quicksort_def = Define `
  run_quicksort cmp l =
    run_init_state (quicksort l cmp) (init_state [])
`;

val qsort_def = Define `
  qsort cmp l = case run_quicksort l cmp of Success result => result
`;


(*******************************************************************************

    PROOF OF SUCCESS

*******************************************************************************)

Theorem scan_lower_Success:
  ∀ cmp pivot lb s .
    strict_weak_order cmp ∧ lb < LENGTH s.arr ∧
    (∃ index . index ≥ lb ∧ index < LENGTH s.arr ∧ (EL index s.arr = pivot))
  ⇒ ∃ result s' . (scan_lower cmp pivot lb s = (Success result, s'))
Proof
  recInduct (theorem "scan_lower_ind") >>
  rw[] >>
  simp[Once scan_lower_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def] >>
  EVERY_CASE_TAC >> fs[]
  >- (
      fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
      rveq >>
      Cases_on `index = lb` >> fs[]
      >- (
        imp_res_tac Msub_Success >>
        imp_res_tac strict_weak_order_irreflexive >>
        rveq >>
        fs[irreflexive_def]
        ) >>
      first_x_assum match_mp_tac >>
      fs[] >>
      qexists_tac `index` >> fs[]
    )
  >- (
    fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
    rveq >>
    `lb < LENGTH r.arr` by fs[] >>
    imp_res_tac (Msub_Success |> INST_TYPE [beta |-> ``:state_exn``]) >>
    fs[]
    )
QED

Theorem scan_upper_Success:
  ∀ cmp pivot ub s .
    ub ≤ LENGTH s.arr
  ⇒ ∃ result s' . (scan_upper cmp pivot ub s = (Success result, s'))
Proof
  recInduct (theorem "scan_upper_ind") >>
  rw[] >>
  simp[Once scan_upper_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  EVERY_CASE_TAC >> fs[]
  >- (
    first_x_assum drule >>
    strip_tac >>
    first_x_assum match_mp_tac >>
    fs[]
    )
  >- (
      `ub - 1 < LENGTH s.arr` by fs[] >>
      imp_res_tac
        (ml_monadBaseTheory.Msub_eq |> INST_TYPE [beta |-> ``:state_exn``]) >>
      fs[]
    )
QED

Theorem partition_helper_Success:
  ∀ cmp pivot lb ub s .
    strict_weak_order cmp ∧
    ub ≤ LENGTH s.arr ∧
    (∃ index . index ≥ lb ∧ index < LENGTH s.arr ∧ (EL index s.arr = pivot))
  ⇒ ∃ result s' . partition_helper cmp pivot lb ub s = (Success result, s')
Proof
  recInduct (theorem "partition_helper_ind") >>
  rw[] >>
  simp[Once partition_helper_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  IF_CASES_TAC >> fs[NOT_LEQ, ADD1] >>
  qspecl_then [`cmp`,`EL index s.arr`,`lb`,`s`] assume_tac scan_lower_Success >>
  rfs[] >> first_x_assum imp_res_tac >> rfs[] >>
  imp_res_tac scan_lower_state >> rveq >> fs[] >>
  qspecl_then [`cmp`,`EL index s.arr`,`ub`,`s`] assume_tac scan_upper_Success >>
  rfs[] >>
  imp_res_tac scan_upper_state >> rveq >> fs[] >>
  rename1 `scan_lower _ _ _ _ = (Success new_lb, _)` >>
  rename1 `scan_upper _ _ _ _ = (Success new_ub, _)` >>
  imp_res_tac scan_lower_index >>
  imp_res_tac scan_upper_index >> fs[] >>
  Cases_on `new_ub = 0` >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  `new_lb < LENGTH s.arr` by fs[] >>
  `new_ub < LENGTH s.arr` by fs[] >>
  imp_res_tac (Msub_Success |> INST_TYPE [beta |-> ``:state_exn``]) >> fs[] >>
  ntac 3 (first_x_assum (qspec_then `Subscript` mp_tac) >> strip_tac >> fs[]) >>
  qspecl_then [`s.arr`,`new_lb`,`EL new_ub s.arr`,`Subscript`] assume_tac
    (Mupdate_Success |> INST_TYPE [beta |-> ``:state_exn``]) >> fs[] >>
  first_x_assum (qspec_then `LUPDATE (EL new_ub s.arr) new_lb s.arr` mp_tac) >>
  fs[] >> strip_tac >> fs[] >>
  qspecl_then [`LUPDATE (EL new_ub s.arr) new_lb s.arr`,
               `new_ub`,`EL new_lb s.arr`,`Subscript`] assume_tac
    (Mupdate_Success |> INST_TYPE [beta |-> ``:state_exn``]) >> fs[] >>
  first_x_assum (qspec_then
    `LUPDATE (EL new_lb s.arr) new_ub (LUPDATE (EL new_ub s.arr) new_lb s.arr)`
      mp_tac) >>
  fs[] >> strip_tac >> fs[] >>
  first_x_assum match_mp_tac >>
  fs[] >>
  Cases_on `new_lb = index` >> fs[]
  >- (
    rveq >>
    qexists_tac `new_ub` >> fs[EL_LUPDATE]
    ) >>
  Cases_on `new_ub = index` >> fs[]
  >- (
    rveq >>
    qexists_tac `new_lb` >> fs[EL_LUPDATE]
    ) >>
  qexists_tac `index` >> fs[EL_LUPDATE] >>
  last_x_assum (qspec_then `index` mp_tac) >>
  Cases_on `index < new_lb` >> fs[] >>
  metis_tac[strict_weak_order_irreflexive, irreflexive_def]
QED

Theorem partition_helper_state_LENGTH:
  ∀ cmp pivot lb ub s result s'.
    (partition_helper cmp pivot lb ub s = (Success result, s'))
  ⇒ (LENGTH s'.arr = LENGTH s.arr)
Proof
  recInduct (theorem "partition_helper_ind") >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once partition_helper_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  fs[fetch "-" "update_arr_def", ml_monadBaseTheory.Marray_update_def] >>
  EVERY_CASE_TAC >> fs[] >>
  imp_res_tac scan_lower_state >>
  imp_res_tac scan_upper_state >> rveq >> fs[] >>
  rw[] >>
  first_x_assum drule >>
  rpt (disch_then drule) >>
  rw[] >>
  first_x_assum drule >>
  fs[] >> rw[] >>
  imp_res_tac Mupdate_Success >>
  fs[LUPDATE_LENGTH]
QED

Theorem quicksort_aux_Success:
  ∀ cmp lower upper s .
    strict_weak_order cmp ∧
    upper < LENGTH s.arr
  ⇒ ∃ result s' . (quicksort_aux cmp lower upper s = (Success result, s')) ∧
    (LENGTH s'.arr = LENGTH s.arr)
Proof
  recInduct (theorem "quicksort_aux_ind") >>
  rw[] >>
  simp[Once quicksort_aux_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "arr_sub_def", ml_monadBaseTheory.Marray_sub_def] >>
  IF_CASES_TAC >> fs[NOT_GREATER_EQ, ADD1, LE_LT1] >>
  `lower < LENGTH s.arr` by fs[] >>
  imp_res_tac (Msub_Success |> INST_TYPE [beta |-> ``:state_exn``]) >> fs[] >>
  ntac 2 (first_x_assum (qspec_then `Subscript` mp_tac) >> strip_tac >> fs[]) >>
  qspecl_then [`cmp`,`EL lower s.arr`,`lower`,`upper + 1`,`s`]
    assume_tac partition_helper_Success >> rfs[] >>
  (* TODO why do we have to manually state the below? *)
  `∃ result s' . partition_helper cmp (EL lower s.arr) lower (upper + 1) s =
    (Success result, s')` by
      (first_x_assum match_mp_tac >> qexists_tac `lower` >> fs[]) >>
  fs[] >>
  reverse (IF_CASES_TAC) >> fs[]
  >- metis_tac[partition_helper_state_LENGTH]
  >- metis_tac[partition_helper_state_LENGTH]
  >>
  `∃ s . (quicksort_aux cmp lower result s' = (Success (), s)) ∧
    (LENGTH s.arr = LENGTH s'.arr)` by (
      first_x_assum match_mp_tac >>
      imp_res_tac partition_helper_state_LENGTH >>
      DECIDE_TAC) >>
  fs[] >>
  qsuff_tac `upper < LENGTH s'.arr`
  >- (
    rw[] >> fs[] >>
    metis_tac[partition_helper_state_LENGTH]
    ) >>
  imp_res_tac partition_helper_state_LENGTH >>
  DECIDE_TAC
QED


Theorem quicksort_Success:
  ∀ cmp l s .
    strict_weak_order cmp
  ⇒ ∃ l' s' . quicksort cmp l s = (Success l', s')
Proof
  rw[] >> Cases_on `l` >> simp[quicksort_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  fs[fetch "-" "alloc_arr_def", ml_monadBaseTheory.Marray_alloc_def] >>
  qspecl_then [`h::t`, `<|arr := h::REPLICATE (LENGTH t) h|>`]
    assume_tac array_set_Success >> fs[] >>
  qspecl_then [`cmp`,`0n`,`LENGTH t`,`s'`] assume_tac quicksort_aux_Success >>
  rfs[] >>
  metis_tac[array_get_Success]
QED

Theorem run_quicksort_Success:
  ∀ cmp l . strict_weak_order cmp
  ⇒ ∃ l' .
    (run_quicksort l cmp = (Success l')) ∧
    PERM l l' ∧ SORTED (λ x y . ¬ cmp y x) l'
Proof
  fs[run_quicksort_def, fetch "-" "run_init_state_def"] >>
  fs[ml_monadBaseTheory.run_def] >> rw[] >>
  qspecl_then [`cmp`,`l`,`state_refs []`] assume_tac quicksort_Success >>
  rfs[] >>
  drule quicksort_result >>
  disch_then drule >>
  fs[]
QED


(*******************************************************************************

    TRANSLATIONS

*******************************************************************************)

val scan_lower_v_thm = m_translate scan_lower_def;
val scan_upper_v_thm = m_translate scan_upper_def;

val partition_helper_v_thm = m_translate partition_helper_def;

val quicksort_aux_v_thm = m_translate quicksort_aux_def;

val array_get_aux_v_thm = m_translate array_get_aux_def;
val array_get_v_thm = m_translate array_get_def;

val array_set_aux_v_thm = m_translate array_set_aux_def;
val array_set_v_thm = m_translate array_set_def;

val LENGTH_v_thm = translate LENGTH;
val quicksort_v_thm = m_translate quicksort_def;

val run_quicksort_v_thm = m_translate_run run_quicksort_def;

val qsort_v_thm = translate qsort_def;

val qsort_v_precond = Q.prove(
  `∀ cmp l . strict_weak_order cmp ⇒ qsort_side cmp l`,
  rw[fetch "-" "qsort_side_def"] >>
  metis_tac[run_quicksort_Success]
)

(* TODO update precondition doesn't seem to work here
val _ = qsort_v_precond |> update_precondition
*)
val qsort_v_thm = qsort_v_thm |> DISCH_ALL |>
                  REWRITE_RULE [ml_translatorTheory.PRECONDITION_def] |>
                  (fn th => HO_MATCH_MP th
                    (qsort_v_precond |> SPEC_ALL |> UNDISCH_ALL)) |>
                  DISCH_ALL

val _ = save_thm("qsort_v_thm", qsort_v_thm)


(*******************************************************************************

    FINAL THEOREM

*******************************************************************************)

Theorem qsort_thm:
  ∀ cmp l l' . strict_weak_order cmp ∧ (qsort cmp l = l')
  ⇒ PERM l l' ∧ SORTED (λ x y . ¬ cmp y x) l'
Proof
  rw[] >>
  fs[qsort_def] >>
  qspecl_then [`cmp`,`l`] assume_tac run_quicksort_Success >>
  rfs[]
QED


(******************************************************************************)

val _ = export_theory ();
