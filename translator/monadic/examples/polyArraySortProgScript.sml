(*
 An example showing how to use the monadic translator to translate polymorphic
 monadic array quicksort, including exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "polyArraySortProg"

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
(* TODO still some problems with type variables - if 'a not used below,
   some translations fail *)

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| arr : 'a list |>`;

val state_type = ``:'state state_refs``;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

val config =  local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("arr", ``[] : 'state list``, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;


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

val array_set_aux_v_thm = m_translate array_set_aux_def;
val array_set_v_thm = m_translate array_set_def;

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
val array_get_aux_v_thm = m_translate array_get_aux_def;
val array_get_v_thm = m_translate array_get_def;


(*******************************************************************************

    SCAN_UPPER / SCAN_LOWER

*******************************************************************************)

(* TODO move to ml_monadBaseTheory *)
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

val scan_lower_v_thm = m_translate scan_lower_def;

val scan_lower_v_thm_precond =
  let val goal = first is_forall (hyp scan_lower_v_thm)
      val imps = List.filter (fn t => not (aconv t goal)) (hyp scan_lower_v_thm)
      val conj_imps = list_mk_conj imps
  in mk_imp(conj_imps, goal) end

val scan_lower_v_thm_precond_thm = Q.prove(
  `^(scan_lower_v_thm_precond)`,
  strip_tac >>
  ho_match_mp_tac (theorem "scan_lower_ind") >>
  rpt strip_tac >>
  match_mp_tac
    (theorem "scan_lower_helper_0" |> UNDISCH |> UNDISCH |> UNDISCH) >>
  rpt strip_tac >>
  last_x_assum match_mp_tac >>
  fs[fetch "-" "arr_sub_def"] >>
  fs[fetch "ml_monadBase" "Marray_sub_def"]
);
val _ = UNDISCH_ALL scan_lower_v_thm_precond_thm |> update_local_precondition;

val scan_upper_def = Define `
  scan_upper (cmp : 'a -> 'a -> bool) pivot ub =
    if ub = 0n then return ub else do
    elem <- arr_sub (ub - 1);
    if cmp pivot elem then
      scan_upper cmp pivot (ub - 1)
    else return (ub - 1)
  od
`
val scan_upper_v_thm = m_translate scan_upper_def;

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


val partition_helper_v_thm = m_translate partition_helper_def;

val partition_helper_v_thm_precond =
  let val goal = first is_forall (hyp partition_helper_v_thm)
      val imps = List.filter (fn t => not (aconv t goal))
                  (hyp partition_helper_v_thm)
      val conj_imps = list_mk_conj imps
  in mk_imp(conj_imps, goal) end

val partition_helper_v_thm_precond_thm = Q.prove(
  `^(partition_helper_v_thm_precond)`,
  strip_tac >>
  ho_match_mp_tac (theorem "partition_helper_ind") >>
  rpt strip_tac >>
  match_mp_tac
    (theorem "partition_helper_helper_0" |> UNDISCH |> UNDISCH |> UNDISCH |>
      UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH) >>
  rpt strip_tac >>
  last_x_assum match_mp_tac >>
  fs[FST_EQ_EQUIV] >>
  imp_res_tac SND_EQ_EQUIV >>
  fs[]
);

val _ = UNDISCH_ALL partition_helper_v_thm_precond_thm |>
        update_local_precondition;

(* TODO prove something like this to remove condition checks in later functions
Theorem partition_helper_index:
  ∀ cmp pivot lb ub s p s' .
    ub > lb ∧ (partition_helper cmp pivot lb ub s = (Success p, s'))
  ⇒ p ≥ lb
Proof
  recInduct (theorem "partition_helper_ind") >>
  rw[] >>
  qpat_x_assum `partition_helper _ _ _ _ _ = _` mp_tac >>
  simp[Once partition_helper_def] >>
  fs[ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  EVERY_CASE_TAC >> fs[]
    >- (
      rw[] >>
      imp_res_tac scan_lower_index >>
      qsuff_tac `p >= a'` >- fs[] >>
      qpat_x_assum `partition_helper _ _ _ _ _ = _ ` mp_tac >>
      first_assum match_mp_tac >>
      fs[]
      )
    >- (
      fs[ml_monadBaseTheory.st_ex_return_def] >>
      rw[] >>
      fs[NOT_LESS] >>
      imp_res_tac scan_lower_index >>
      imp_res_tac scan_upper_index >> fs[prim_recTheory.NOT_LESS_0]
      metis_tac[]
      )
QED
*)

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

val quicksort_aux_v_thm = m_translate quicksort_aux_def;

val quicksort_aux_v_thm_precond =
  let val goal = first is_forall (hyp quicksort_aux_v_thm)
      val imps = List.filter (fn t => not (aconv t goal))
                  (hyp quicksort_aux_v_thm)
      val conj_imps = list_mk_conj imps
  in mk_imp(conj_imps, goal) end

val quicksort_aux_v_thm_precond_thm = Q.prove(
  `^(quicksort_aux_v_thm_precond)`,
  strip_tac >>
  ho_match_mp_tac (theorem "quicksort_aux_ind") >>
  rpt strip_tac >>
  match_mp_tac
    (theorem "quicksort_aux_helper_0" |> UNDISCH |> UNDISCH |> UNDISCH |>
      UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH |> UNDISCH |>
      UNDISCH |> UNDISCH |> UNDISCH) >>
  rpt strip_tac >>
  last_x_assum match_mp_tac >>
  fs[FST_EQ_EQUIV] >>
  imp_res_tac SND_EQ_EQUIV >>
  fs[]
);

val _ = UNDISCH_ALL quicksort_aux_v_thm_precond_thm |>
        update_local_precondition;


val quicksort_def = Define `
  (quicksort cmp [] = return []) ∧
  (quicksort cmp (x::xs) = do
    alloc_arr (LENGTH (x::xs)) x;
    array_set (x::xs);
    quicksort_aux cmp 0n (LENGTH (x::xs) - 1n);
    array_get ()
  od)
`;

val LENGTH_v_thm = translate LENGTH;
val quicksort_v_thm = m_translate quicksort_def;


(*******************************************************************************

    RUN QUICKSORT

*******************************************************************************)

val run_init_state_def = define_run state_type [] "init_state";

val run_quicksort_def = Define `
  run_quicksort cmp l =
    run_init_state (quicksort l cmp) (init_state [])
`;

val run_quicksort_v_thm = m_translate_run run_quicksort_def;


(******************************************************************************)

val _ = export_theory ();
