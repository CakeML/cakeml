(*
  Definitions for the state-and-exception monad that is supported by the
  proof-producing monadic translator.
*)

open preamble semanticPrimitivesTheory packLib

val _ = new_theory "ml_monadBase";

val _ = hide "state";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Datatype `
  exc = M_success 'a | M_failure 'b`;

Type M = ``:'a -> ('b, 'c) exc # 'a``

Definition liftM_def:
  (liftM read (write:('a->'a)->'d->'d) (op: ('a,'b,'c) M)) : ('d,'b,'c) M =
    (λstate. let (ret,new) = op (read state) in
               (ret, write (K new) state))
End

(* Definitions using monadic syntax *)
val _ = ParseExtras.temp_loose_equality ();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val _ = monadsyntax.temp_add_monadsyntax ();

Definition st_ex_bind_def:
  (st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
    λs.
      dtcase x s of
        (M_success y,s) => f y s
      | (M_failure x,s) => (M_failure x,s)
End

Definition st_ex_ignore_bind_def:
  (st_ex_ignore_bind : (α, β, γ) M -> (α, δ, γ) M -> (α, δ, γ) M) x f =
    λ s .
      dtcase x s of
        (M_success y, s) => f s
      | (M_failure x, s) => (M_failure x, s)
End


(*
 * Congruence theorems for st_ex_bind / st_ex_ignore_bind.
 * Used by TFL rewriters when deriving termination conditions.
 * Ensures that intermediate values of the monad bind (y, s'')
 * are captured.
 *)

Theorem st_ex_ignore_bind_CONG:
  ∀ x s x' s' f f'.
    (x = x') ∧ (s = s') ∧
    (∀ y s''. (x' s' = (M_success y, s'')) ⇒ (f s'' = f' s''))
  ⇒ (st_ex_ignore_bind x f s =
      st_ex_ignore_bind x' f' s')
Proof
  rw[st_ex_ignore_bind_def] >>
  Cases_on `x s` >>
  rw[] >>
  Cases_on `q` >> fs[]
QED
DefnBase.export_cong "st_ex_ignore_bind_CONG";

Theorem st_ex_bind_CONG:
  ∀ x s x' s' f f'.
    (x = x') ∧ (s = s') ∧
    (∀ y s''. (x' s' = (M_success y, s'')) ⇒ (f y s'' = f' y s''))
  ⇒ (st_ex_bind x f s = st_ex_bind x' f' s')
Proof
  rw[st_ex_bind_def] >>
  Cases_on `x s` >>
  rw[] >>
  Cases_on `q` >> fs[]
QED
DefnBase.export_cong "st_ex_bind_CONG";


Definition st_ex_return_def:
  (st_ex_return (*: α -> (β, α, γ) M*)) x =
    λs. (M_success x, s)
End

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``st_ex_ignore_bind``
Overload monad_ignore_bind[local] = ``st_ex_ignore_bind``
Overload return[local] = ``st_ex_return``

val _ = add_infix ("otherwise", 400, HOLgrammars.RIGHT);

Definition otherwise_def:
  x otherwise y =
    λs. dtcase ((x : ('a, 'b, 'c) M) s) of
          (M_success y, s) => (M_success y, s)
        | (M_failure e, s) => (y : ('a, 'b, 'c) M) s
End

Definition can_def:
  can f x = (do f x ; return T od
             otherwise return F)
End

(* Dynamic allocation of references *)
val _ = Datatype `
  store_ref = StoreRef num`;

(* Arrays *)

(* Msub *)
Definition Msub_def:
  Msub e (n : num) l =
    dtcase l of
      [] => M_failure e
    | x::l' => if n = 0 then M_success x else Msub e (n-1) l'
End

Theorem Msub_eq:
   !l n e. n < LENGTH l ==> (Msub e n l = M_success (EL n l))
Proof
  Induct
  \\ rw[Once Msub_def]
  \\ Cases_on `n`
  \\ fs[]
QED

Theorem Msub_exn_eq:
   !l n e. n >= LENGTH l ==> (Msub e n l = M_failure e)
Proof
  Induct
  \\ rw[Once Msub_def]
  \\ Cases_on `n`
  \\ fs[]
QED

(* Mupdate *)
Definition Mupdate_def:
  Mupdate e x (n : num) l =
    dtcase l of
      [] => M_failure e
    | x'::l' =>
        if n = 0 then
          M_success (x::l')
        else
          (dtcase Mupdate e x (n-1) l' of
             M_success l'' => M_success (x'::l'')
           | other => other)
End

Theorem Mupdate_eq:
   !l n x e. n < LENGTH l ==> (Mupdate e x n l = M_success (LUPDATE x n l))
Proof
  Induct
  \\ rw[Once Mupdate_def, LUPDATE_def]
  \\ Cases_on `n`
  \\ fs[LUPDATE_def]
QED

Theorem Mupdate_exn_eq:
   !l n x e. n >= LENGTH l ==> (Mupdate e x n l = M_failure e)
Proof
  Induct
  \\ rw[Once Mupdate_def, LUPDATE_def]
  \\ Cases_on `n`
  \\ fs[LUPDATE_def]
QED

(* Array resize *)
Definition array_resize_def:
  array_resize (n : num) x a =
    if n = 0 then
      []
    else
      dtcase a of
        [] => x::array_resize (n-1) x a
      | x'::a' => x'::array_resize (n-1) x a'
End

Theorem array_resize_eq:
   !a n x. array_resize n x a = TAKE n a ++ REPLICATE (n - LENGTH a) x
Proof
  Induct \\ Induct_on `n` \\ rw [Once array_resize_def]
QED

(* User functions *)
Definition Marray_length_def:
  Marray_length get_arr =
    \s. (M_success (LENGTH (get_arr s)), s)
End

Definition Marray_sub_def:
  Marray_sub get_arr e n =
    \s. (Msub e n (get_arr s), s)
End

Definition Marray_update_def:
  Marray_update get_arr set_arr e n x =
    \s. dtcase Mupdate e x n (get_arr s) of
          M_success a => (M_success(), set_arr a s)
        | M_failure e => (M_failure e, s)
End

Definition Marray_alloc_def:
  Marray_alloc set_arr n x =
    \s. (M_success (), set_arr (REPLICATE n x) s)
End

Definition Marray_resize_def:
  Marray_resize get_arr set_arr n x =
    \s. (M_success (), set_arr (array_resize n x (get_arr s)) s)
End

(* Dynamic allocated references *)
Definition Mref_def:
  Mref cons x = \s. (M_success (StoreRef (LENGTH s)), cons x::s)
End

Definition dref_def:
  dref n = \s. EL (LENGTH s - n - 1) s
End

Definition Mdref_aux_def:
  Mdref_aux e (n:num) =
    \s. dtcase s of
          [] => M_failure e
        | x::s => if n = 0 then M_success x else Mdref_aux e (n-1) s
End

Definition Mdref_def:
  Mdref e (StoreRef n) =
    \s. (Mdref_aux e (LENGTH s - n - 1) s, s)
End

Definition Mpop_ref_def:
  Mpop_ref e =
    \(r, s). dtcase s of
               x::s => (r, s)
             | [] => (M_failure e, s)
End

Definition Mref_assign_aux_def:
  Mref_assign_aux e (n:num) x =
    \s. dtcase s of
          x'::s =>
            if n = 0 then
              M_success (x::s)
            else
              (dtcase Mref_assign_aux e (n-1) x s of
                 M_success s => M_success (x'::s)
               | other => other)
        | [] => M_failure e
End

Definition Mref_assign_def:
  Mref_assign e (StoreRef n) x =
    \s. dtcase Mref_assign_aux e (LENGTH s - n - 1) x s of
          M_success s => (M_success (), s)
        | M_failure e => (M_failure e, s)
End

Definition ref_assign_def:
  ref_assign n x = \s. LUPDATE x (LENGTH s - n - 1) s
End

Theorem dref_cons_state:
   n < LENGTH state ==> (dref n (x::state) = dref n state)
Proof
  rw[Once dref_def]
  \\ fs[SUC_ONE_ADD]
  \\ Cases_on `LENGTH state - n` >-(fs[])
  \\ rw[]
  \\ rw[Once dref_def]
  \\ `LENGTH state - (n + 1) = LENGTH state - n - 1` by numLib.DECIDE_TAC
  \\ POP_ASSUM(fn x => rw[x])
QED

Theorem dref_first:
   dref (LENGTH s) (r::s) = r
Proof
  fs[Once dref_def, SUC_ONE_ADD]
QED

Theorem Mdref_eq:
   !state n.
     n < LENGTH state
     ==>
     (Mdref e (StoreRef n) state = (M_success(dref n state), state))
Proof
  Induct
  \\ rw[Once Mdref_def, Once Mdref_aux_def]
  >-(rw[Once dref_def]
     \\ fs[]
     \\ `n = LENGTH state` by fs[SUC_ONE_ADD]
     \\ rw[SUC_ONE_ADD])
  \\ fs[SUC_ONE_ADD]
  \\ `Mdref_aux e (LENGTH state - (n + 1)) state =
      FST(Mdref e (StoreRef n) state)`
      by (last_x_assum(fn x => ALL_TAC) \\ rw[Once Mdref_def])
  \\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
  \\ rw[]
  \\ rw[dref_cons_state]
QED

Theorem Mref_assign_aux_eq:
   !state e n x.
     n < LENGTH state
     ==>
     (Mref_assign_aux e (LENGTH state - n - 1) x state =
      M_success (ref_assign n x state))
Proof
  Induct
  \\ rw[Once Mref_assign_aux_def, Once ref_assign_def]
  >-(rw[SUC_ONE_ADD]
     >> Cases_on `LENGTH state - n` >-(rw[LUPDATE_def])
     >> rw[LUPDATE_def]
     >> irule FALSITY
     >> fs[])
  \\ fs[SUC_ONE_ADD]
  \\ Cases_on `LENGTH state - n` >-(fs[])
  \\ rw[Once ref_assign_def]
  \\ rw[LUPDATE_def]
  \\ `LENGTH state - (n + 1) = n'` by fs[SUC_ONE_ADD]
  \\ rw[]
QED

Theorem Mref_assign_eq:
   !state e n x.
     n < LENGTH state
     ==>
     (Mref_assign e (StoreRef n) x state = (M_success(), ref_assign n x state))
Proof
  rw[Once Mref_assign_def]
  \\ IMP_RES_TAC Mref_assign_aux_eq
  \\ fs[]
QED

Definition ref_bind_def:
  ref_bind create f pop =
    \s. dtcase create s of
          (M_success x, s) => pop (f x s)
        | (M_failure x, s) => (M_failure x, s)
End

(* TODO: use that *)
Definition Mget_ref_def:
  Mget_ref get_var = \s. (M_success (get_var s), s)
End

Definition Mset_ref_def:
  Mset_ref set_var x = \s. (M_success (), set_var x s)
End

val _ = ParseExtras.temp_tight_equality ();

(* Rules to deal with the monads *)
val st_ex_return_success = Q.prove(
  `!v st r st'.
     st_ex_return v st = (r, st')
     <=>
     r = M_success v ∧ st' = st`,
  rw [st_ex_return_def] \\ metis_tac[]);

val st_ex_bind_success = Q.prove (
  `!f g st st' v.
     st_ex_bind f g st = (M_success v, st')
     <=>
     ?v' st''.
       f st = (M_success v', st'') /\
       g v' st'' = (M_success v, st')`,
  rw [st_ex_bind_def] >>
  cases_on `f st` >>
  rw [] >>
  cases_on `q` >>
  rw []);

val otherwise_success = Q.prove(
  `(x otherwise y) s = (M_success v, s')
   <=>
   x s = (M_success v, s') \/
   ?e s''. x s = (M_failure e, s'') /\ y s'' = (M_success v, s')`,
  fs[otherwise_def]
  \\ EQ_TAC
  >> DISCH_TAC
  >> Cases_on `x s`
  >> Cases_on `q`
  >> fs[]);

val otherwise_failure = Q.prove(
  `(x otherwise y) s = (M_failure e, s')
   <=>
   ?e' s''. x s = (M_failure e', s'') /\ y s'' = (M_failure e, s')`,
  fs[otherwise_def]
  \\ EQ_TAC
  >> DISCH_TAC
  >> Cases_on `x s`
  >> Cases_on `q`
  >> fs[]);

val otherwise_eq = Q.prove(
  `(x otherwise y) s = (r, s')
   <=>
   (?v. ((x s = (M_success v, s') /\ r = M_success v) \/
         (?e s''. x s = (M_failure e, s'') /\
                  y s'' = (M_success v, s') /\
                  r = M_success v))) \/
   (?e e' s''. x s = (M_failure e', s'') /\
               y s'' = (M_failure e, s') /\
               r = M_failure e)`,
  Cases_on `x s`
  \\ Cases_on `r`
  \\ fs[otherwise_success, otherwise_failure]
  \\ rw[]
  \\ metis_tac[]);

val can_success = Q.prove(
  `can f x s = (M_failure e, s') <=> F`,
  rw[can_def, otherwise_def, st_ex_ignore_bind_def]
  \\ Cases_on `f x s`
  \\ Cases_on `q`
  \\ fs[st_ex_return_def]
);

val Marray_length_success = Q.prove(
  `!get_arr s r s'.
     Marray_length get_arr s = (r, s')
     <=>
     r = M_success (LENGTH (get_arr s)) /\
     s' = s`,
  rw[Marray_length_def] \\ metis_tac[]);

val Marray_sub_success = Q.prove(
  `!get_arr e n s v s'.
     Marray_sub get_arr e n s = (M_success v, s')
     <=>
     n < LENGTH (get_arr s) /\ v = EL n (get_arr s) /\ s' = s`,
  rw[Marray_sub_def]
  \\ EQ_TAC
  >> simp[GSYM AND_IMP_INTRO]
  >> rpt DISCH_TAC
  >> Cases_on `n < LENGTH (get_arr s)`
  >> rw[]
  \\ fs [Msub_eq, Msub_exn_eq]);

val Marray_sub_failure = Q.prove(
  `!get_arr e n s e' s'.
     Marray_sub get_arr e n s = (M_failure e', s')
     <=>
     n >= LENGTH (get_arr s) /\ e' = e /\ s' = s`,
  rw[Marray_sub_def]
  \\ EQ_TAC
  >> simp[GSYM AND_IMP_INTRO]
  >> rpt DISCH_TAC
  >> Cases_on `n < LENGTH (get_arr s)`
  >> rw[]
  \\ fs [Msub_eq, Msub_exn_eq]);

val Marray_sub_eq = Q.prove(
  `Marray_sub get_arr e n s = (r, s')
   <=>
   (n < LENGTH (get_arr s) /\ s' = s /\ r = M_success (EL n (get_arr s))) \/
   (n >= LENGTH (get_arr s) /\ s' = s /\ r = M_failure e)`,
  Cases_on `r`
  >> fs[Marray_sub_success, Marray_sub_failure]
  >> metis_tac[]);

val Marray_update_success = Q.prove(
  `!get_arr set_arr e n x s s'.
     Marray_update get_arr set_arr e n x s = (M_success v, s')
     <=>
     n < LENGTH (get_arr s) /\
     v = () /\
     s' = set_arr (LUPDATE x n (get_arr s)) s`,
  rw[Marray_update_def]
  \\ EQ_TAC
  >> simp[GSYM AND_IMP_INTRO]
  >> rpt DISCH_TAC
  >> Cases_on `n < LENGTH (get_arr s)`
  \\ fs [Mupdate_eq, Mupdate_exn_eq]);

val Marray_update_failure = Q.prove(
  `!get_arr set_arr e e' n x s s'.
     Marray_update get_arr set_arr e n x s = (M_failure e', s')
     <=>
     n >= LENGTH (get_arr s) /\
     e' = e /\
     s' = s`,
  rw[Marray_update_def]
  \\ EQ_TAC
  >> simp[GSYM AND_IMP_INTRO]
  >> rpt DISCH_TAC
  >> Cases_on `n < LENGTH (get_arr s)` \\ fs []
  \\ fs [Mupdate_eq, Mupdate_exn_eq]);

val Marray_update_eq = Q.prove(
  `Marray_update get_arr set_arr e n x s = (r, s')
   <=>
   (n < LENGTH (get_arr s) /\
    s' = set_arr (LUPDATE x n (get_arr s)) s /\
    r = M_success ()) \/
   (n >= LENGTH (get_arr s) /\
    s' = s /\
    r = M_failure e)`,
  Cases_on `r`
  >> Cases_on `n < LENGTH (get_arr s)`
  >> fs[Marray_update_success, Marray_update_failure]
  >> metis_tac[]);

val Marray_alloc_success = Q.prove(
  `Marray_alloc set_arr n x s = (r, s')
   <=>
   r = M_success () /\
   s' = set_arr (REPLICATE n x) s`,
  rw[Marray_alloc_def]
  \\ EQ_TAC
  >> simp[GSYM AND_IMP_INTRO]);

val monad_eqs = LIST_CONJ
  [ st_ex_return_success, st_ex_bind_success, otherwise_eq, can_success,
    Marray_length_success, Marray_sub_eq, Marray_update_eq,
    Marray_alloc_success ];
val _ = save_thm ("monad_eqs", monad_eqs);

(* Run *)
Definition run_def:
  run (x : ('a, 'b, 'c) M) state = FST (x state)
End


val _ = export_theory ();
