(*
  Using the monadic translator to translate heap sorting functions.

  Bit of an experiment, may move to ListProg if useful.
*)
Theory heap_sort_monadic
Ancestors
  heap_sort_in_fun ml_translator ml_monad_translator
Libs
  preamble ml_monad_translator_interfaceLib


val _ = set_up_monadic_translator ();

(* Create the data type to handle the references *)
Datatype:
  state_refs = <|
                 heap_array : 'a list;
                |>
End

(* Data type for the exceptions. Seems to be standard. *)
Datatype:
  state_exn = Fail string | Subscript
End

val state_type = ``:'el state_refs``;

val config = local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("heap_array", ``[] : 'el list``, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

Definition heap_insert_larger_monadic_def:
  heap_insert_larger_monadic R sz i x = (if (i = 0n) \/ i * 2 > sz
    then (if i = 0 then return ()
        else update_heap_array (i - 1) x)
    else do
      y <- heap_array_sub ((i * 2) - 1);
      z <- if (i * 2) + 1 > sz
      then return y
      else heap_array_sub (i * 2);
      if ((i * 2) + 1) <= sz /\ R z x /\ R z y
      then do
        update_heap_array (i - 1) z;
        heap_insert_larger_monadic R sz ((i * 2) + 1) x
      od
      else if (i * 2) <= sz /\ R y x /\ (((i * 2) + 1) <= sz ==> R y z)
      then do
        update_heap_array (i - 1) y;
        heap_insert_larger_monadic R sz (i * 2) x
      od
      else update_heap_array (i - 1) x
    od)
Termination
  qexists_tac `measure (\(_, sz, i, _). sz - i)`
  \\ simp []
End

Theorem st_ex_bind_split[local]:
  (st_ex_bind f g st = (res, st')) <=>
  ?r s. (f st = (r, s)) /\ (case r of M_success x => (g x s) = (res, st')
    | M_failure y => (res, st') = (M_failure y, s))
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ Cases_on `f st`
  \\ simp []
  \\ Cases_on `FST (f st)`
  \\ gs []
  \\ metis_tac []
QED

Theorem st_ex_ignore_bind_simp[local]:
  st_ex_ignore_bind f g = st_ex_bind f (\_. g)
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_ignore_bind_def]
QED

Definition st_embed_def:
  (st_embed sz hp : 'a state_refs) =
    <| heap_array := GENLIST (hp o ((+) 1)) sz |>
End

Theorem LENGTH_st_embed[local]:
  LENGTH (st_embed sz hp).heap_array = sz
Proof
  simp [st_embed_def]
QED

Theorem update_heap_array_st_embed[local]:
  i < sz ==>
  (update_heap_array i x (st_embed sz hp) =
        (M_success (), st_embed sz (hp⦇i + 1 ↦ x⦈)))
Proof
  simp [fetch "-" "update_heap_array_def"]
  \\ simp [ml_monadBaseTheory.monad_eqs]
  \\ simp [st_embed_def, LUPDATE_GENLIST]
  \\ simp [combinTheory.UPDATE_def, combinTheory.o_DEF]
QED

Theorem heap_array_sub_st_embed[local]:
  i < sz ==>
  (heap_array_sub i (st_embed sz hp) =
    (M_success (hp (i + 1)), (st_embed sz hp)))
Proof
  simp [fetch "-" "heap_array_sub_def"]
  \\ simp [ml_monadBaseTheory.monad_eqs, st_embed_def]
QED

Theorem monad_simps[local] = LIST_CONJ [
    ml_monadBaseTheory.st_ex_bind_def |> Q.ISPEC `update_heap_array i x`,
    update_heap_array_st_embed,
    ml_monadBaseTheory.st_ex_bind_def |> Q.ISPEC `heap_array_sub i`,
    heap_array_sub_st_embed,
    ml_monadBaseTheory.monad_eqs,
    st_ex_ignore_bind_simp]

Theorem heap_insert_larger_monadic_eq:
  0 < i /\ i <= sz /\ sz <= arr_sz ==>
  (heap_insert_larger_monadic R sz i x (st_embed arr_sz hp) =
    (M_success (), st_embed arr_sz (heap_insert_larger R sz i x hp)))
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `(\i. sz - i) i`
  \\ rw []
  \\ ONCE_REWRITE_TAC [heap_insert_larger_monadic_def]
  \\ ONCE_REWRITE_TAC [heap_insert_larger_def]
  \\ rw [] \\ fs []
  \\ simp [monad_simps]
  \\ rw [] \\ fs []
  \\ simp [monad_simps]
QED

Definition heap_pop_monadic_def:
  heap_pop_monadic R sz_dec = (do
    bot_el <- heap_array_sub 0;
    top_el <- heap_array_sub sz_dec;
    heap_insert_larger_monadic R sz_dec 1 top_el;
    return bot_el
  od)
End

(* The heap_pop_monadic version of sz is one less than the
   functional one (the size after the pop), to avoid a translation
   side-condition. *)
Theorem heap_pop_monadic_eq:
  sz < arr_sz ==>
  (heap_pop_monadic R sz (st_embed arr_sz hp) =
    (M_success (FST (heap_pop R (sz + 1) hp)), st_embed arr_sz (SND (heap_pop R (sz + 1) hp))))
Proof
  simp [heap_pop_def, heap_pop_monadic_def]
  \\ rw [] \\ fs []
  \\ simp [monad_simps, heap_insert_larger_monadic_eq]
  \\ Cases_on `sz = 0`
  >- (
    (* Works by coincidence for the base case. *)
    ONCE_REWRITE_TAC [heap_insert_larger_monadic_def]
    \\ ONCE_REWRITE_TAC [heap_insert_larger_def]
    \\ simp [monad_simps]
  )
  \\ simp [heap_insert_larger_monadic_eq]
QED

Definition heap_insert_smaller_monadic_def:
  heap_insert_smaller_monadic R sz i x = (if (i <= 1n)
    then update_heap_array (i - 1) x
    else do
      y <- heap_array_sub ((i DIV 2) - 1);
      if R x y
      then do
        update_heap_array (i - 1) y;
        heap_insert_smaller_monadic R sz (i DIV 2) x
      od
      else update_heap_array (i - 1) x
    od)
End

Theorem heap_insert_smaller_monadic_eq:
  0 < i /\ i <= sz /\ sz <= arr_sz ==>
  (heap_insert_smaller_monadic R sz i x (st_embed arr_sz hp) =
    (M_success (), st_embed arr_sz (heap_insert_smaller R sz i x hp)))
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `I i`
  \\ rw []
  \\ ONCE_REWRITE_TAC [heap_insert_smaller_monadic_def]
  \\ ONCE_REWRITE_TAC [heap_insert_smaller_def]
  \\ rw [] \\ fs []
  \\ subgoal `i DIV 2 < i`
  \\ simp [monad_simps, dividesTheory.DIV_POS]
  \\ rw [] \\ fs []
  \\ gs [monad_simps, SUB_ADD, X_LE_DIV, dividesTheory.DIV_POS]
QED

Definition heap_add_monadic_def:
  heap_add_monadic R sz x = (do
    el <- if 0 < sz
      then heap_array_sub (((sz + 1) DIV 2) - 1)
      else return x;
    update_heap_array sz el;
    heap_insert_smaller_monadic R (sz + 1) (sz + 1) x
  od)
End

Theorem heap_add_monadic_eq:
  sz + 1 <= arr_sz ==>
  (heap_add_monadic R sz x (st_embed arr_sz hp) =
    (M_success (), st_embed arr_sz (heap_add R sz hp x)))
Proof
  simp [heap_add_monadic_def, heap_add_def]
  \\ subgoal `0 < sz ==> (sz + 1) DIV 2 <= sz`
  >- (
    qspec_then `sz` assume_tac arithmeticTheory.ODD_OR_EVEN
    \\ fs []
  )
  \\ rw []
  \\ simp [monad_simps, heap_insert_smaller_monadic_eq]
  \\ simp [SUB_ADD, X_LE_DIV]
  \\ gs []
  \\ ONCE_REWRITE_TAC [heap_insert_smaller_def]
  \\ simp []
QED

Definition heap_add_all_monadic_def:
  (heap_add_all_monadic R sz [] = return sz) /\
  (heap_add_all_monadic R sz (x :: xs) = do
    heap_add_monadic R sz x;
    heap_add_all_monadic R (sz + 1) xs
  od)
End

Theorem heap_add_all_monadic_eq:
  sz + LENGTH xs <= arr_sz ==>
  (heap_add_all_monadic R sz xs (st_embed arr_sz hp) =
    (M_success (sz + LENGTH xs), st_embed arr_sz (heap_add_all R sz xs hp)))
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `sz`
  \\ Induct_on `xs`
  \\ ONCE_REWRITE_TAC [heap_add_all_monadic_def]
  \\ ONCE_REWRITE_TAC [heap_add_all_def]
  \\ simp [monad_simps, heap_add_monadic_eq]
QED

(* Leads to an exception.

Defn.Hol_defn "monad_fun"
 ` (monad_fun sz xs = if sz = 0 then return xs
    else st_ex_bind (return ARB)
      (\el. monad_fun (sz - 1) (el :: xs))
   )
 `

This exception blocks heap_pop_all_monadic from being
defined with an if/then/else on the RHS. Unfortunately
the 0/SUC version doesn't want to translate.

*)

Definition heap_pop_all_monadic_def:
  (heap_pop_all_monadic R 0 xs = return xs) /\
  (heap_pop_all_monadic R (SUC next_sz) xs =
    do
      el <- heap_pop_monadic R next_sz;
      heap_pop_all_monadic R next_sz (el :: xs)
    od)
End

Theorem heap_pop_all_monadic_eq:
  sz <= arr_sz ==>
  ?hp2. (heap_pop_all_monadic R sz xs (st_embed arr_sz hp) =
    (M_success (heap_pop_all R sz xs hp), hp2))
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `xs`
  \\ Induct_on `sz`
  \\ ONCE_REWRITE_TAC [heap_pop_all_monadic_def]
  \\ ONCE_REWRITE_TAC [heap_pop_all_def]
  \\ simp [monad_simps, heap_pop_monadic_eq]
  \\ rw []
  \\ pairarg_tac \\ fs []
  \\ fs [arithmeticTheory.ADD1]
  \\ simp [heap_pop_monadic_eq]
QED

val run_state_monad_def = 
  define_run ``: 'a state_refs`` [] "state_monad"

Definition heap_sort_via_monad_def:
  heap_sort_via_monad R xs = (case xs of
    [] => []
  | (x :: _) => (case run_state_monad (do
      sz <- return (LENGTH xs);
      R2 <- return (\x y. R y x);
      alloc_heap_array sz x;
      heap_add_all_monadic R2 0 xs;
      heap_pop_all_monadic R2 sz [];
    od) (state_monad [])
    of (M_success ys) => ys
      | _ => []
  ))
End

Theorem alloc_heap_array_eq[local]:
  alloc_heap_array n v st = (M_success (), st_embed n (K v))
Proof
  simp [fetch "-" "alloc_heap_array_def"]
  \\ simp [ml_monadBaseTheory.monad_eqs]
  \\ simp [st_embed_def, REPLICATE_GENLIST]
  \\ simp [fetch "-" "state_refs_component_equality"]
QED

Theorem heap_sort_eq:
  heap_sort R xs = heap_list_sort$heap_sort R xs
Proof
  simp [heap_sort_def, heap_list_sortTheory.heap_sort_def]
  \\ Cases_on `xs` \\ simp []
  \\ simp [run_state_monad_def, ml_monadBaseTheory.run_def]
  \\ simp [ml_monadBaseTheory.exc_case_eq, pairTheory.FST_EQ_EQUIV]
  \\ simp [monad_simps, alloc_heap_array_eq]
  \\ simp [heap_add_all_monadic_eq, heap_pop_all_monadic_eq]
QED

(* Attempt translation of these functions. *)


(* Works if the diverging "metis" call is interrupted ??? *)

val heap_insert_larger_v_thm = heap_insert_larger_monadic_def
  |> m_translate;

(* Works if arithmetic is tweaked to avoid "_ - 1" *)

val heap_pop_v_thm = heap_pop_monadic_def
  |> m_translate;

(* Doesn't work, and other issues prevent definition another way. *)

val heap_pop_all_v_thm = heap_pop_all_monadic_def
  |> m_translate;


