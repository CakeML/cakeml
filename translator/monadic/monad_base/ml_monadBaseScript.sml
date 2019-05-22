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
  exc = Success 'a | Failure 'b`;

val _ = type_abbrev ("M", ``:'a -> ('b, 'c) exc # 'a``);

val liftM_def = Define `
  (liftM read (write:('a->'a)->'d->'d) (op: ('a,'b,'c) M)) : ('d,'b,'c) M =
    (λstate. let (ret,new) = op (read state) in
               (ret, write (K new) state))`;

(* Definitions using monadic syntax *)
val _ = ParseExtras.temp_loose_equality ();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val _ = monadsyntax.temp_add_monadsyntax ();

val st_ex_bind_def = Define `
  (st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
    λs.
      dtcase x s of
        (Success y,s) => f y s
      | (Failure x,s) => (Failure x,s)`;

val st_ex_ignore_bind_def = Define `
  (st_ex_ignore_bind : (α, β, γ) M -> (α, δ, γ) M -> (α, δ, γ) M) x f =
    λ s .
      dtcase x s of
        (Success y, s) => f s
      | (Failure x, s) => (Failure x, s)`;


(*
 * Congruence theorems for st_ex_bind / st_ex_ignore_bind.
 * Used by TFL rewriters when deriving termination conditions.
 * Ensures that intermediate values of the monad bind (y, s'')
 * are captured.
 *)

Theorem st_ex_ignore_bind_CONG:
  ∀ x s x' s' f f'.
    (x = x') ∧ (s = s') ∧
    (∀ y s''. (x' s' = (Success y, s'')) ⇒ (f s'' = f' s''))
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
    (∀ y s''. (x' s' = (Success y, s'')) ⇒ (f y s'' = f' y s''))
  ⇒ (st_ex_bind x f s = st_ex_bind x' f' s')
Proof
  rw[st_ex_bind_def] >>
  Cases_on `x s` >>
  rw[] >>
  Cases_on `q` >> fs[]
QED
DefnBase.export_cong "st_ex_bind_CONG";


val st_ex_return_def = Define `
  (st_ex_return (*: α -> (β, α, γ) M*)) x =
    λs. (Success x, s)`;

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``st_ex_ignore_bind``);
val _ = temp_overload_on ("monad_ignore_bind", ``st_ex_ignore_bind``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = add_infix ("otherwise", 400, HOLgrammars.RIGHT);

val otherwise_def = Define `
  x otherwise y =
    λs. dtcase ((x : ('a, 'b, 'c) M) s) of
          (Success y, s) => (Success y, s)
        | (Failure e, s) => (y : ('a, 'b, 'c) M) s`;

val can_def = Define `
  can f x = (do f x ; return T od
             otherwise return F)`;

(* Dynamic allocation of references *)
val _ = Datatype `
  store_ref = StoreRef num`;

(* Arrays *)

(* Msub *)
val Msub_def = Define `
  Msub e (n : num) l =
    dtcase l of
      [] => Failure e
    | x::l' => if n = 0 then Success x else Msub e (n-1) l'`;

Theorem Msub_eq:
   !l n e. n < LENGTH l ==> (Msub e n l = Success (EL n l))
Proof
  Induct
  \\ rw[Once Msub_def]
  \\ Cases_on `n`
  \\ fs[]
QED

Theorem Msub_exn_eq:
   !l n e. n >= LENGTH l ==> (Msub e n l = Failure e)
Proof
  Induct
  \\ rw[Once Msub_def]
  \\ Cases_on `n`
  \\ fs[]
QED

(* Mupdate *)
val Mupdate_def = Define `
  Mupdate e x (n : num) l =
    dtcase l of
      [] => Failure e
    | x'::l' =>
        if n = 0 then
          Success (x::l')
        else
          (dtcase Mupdate e x (n-1) l' of
             Success l'' => Success (x'::l'')
           | other => other)`;

Theorem Mupdate_eq:
   !l n x e. n < LENGTH l ==> (Mupdate e x n l = Success (LUPDATE x n l))
Proof
  Induct
  \\ rw[Once Mupdate_def, LUPDATE_def]
  \\ Cases_on `n`
  \\ fs[LUPDATE_def]
QED

Theorem Mupdate_exn_eq:
   !l n x e. n >= LENGTH l ==> (Mupdate e x n l = Failure e)
Proof
  Induct
  \\ rw[Once Mupdate_def, LUPDATE_def]
  \\ Cases_on `n`
  \\ fs[LUPDATE_def]
QED

(* Array resize *)
val array_resize_def = Define `
  array_resize (n : num) x a =
    if n = 0 then
      []
    else
      dtcase a of
        [] => x::array_resize (n-1) x a
      | x'::a' => x'::array_resize (n-1) x a'`;

Theorem array_resize_eq:
   !a n x. array_resize n x a = TAKE n a ++ REPLICATE (n - LENGTH a) x
Proof
  Induct \\ Induct_on `n` \\ rw [Once array_resize_def]
QED

(* User functions *)
val Marray_length_def = Define `
  Marray_length get_arr =
    \s. (Success (LENGTH (get_arr s)), s)`;

val Marray_sub_def = Define `
  Marray_sub get_arr e n =
    \s. (Msub e n (get_arr s), s)`;

val Marray_update_def = Define `
  Marray_update get_arr set_arr e n x =
    \s. dtcase Mupdate e x n (get_arr s) of
          Success a => (Success(), set_arr a s)
        | Failure e => (Failure e, s)`;

val Marray_alloc_def = Define `
  Marray_alloc set_arr n x =
    \s. (Success (), set_arr (REPLICATE n x) s)`;

val Marray_resize_def = Define `
  Marray_resize get_arr set_arr n x =
    \s. (Success (), set_arr (array_resize n x (get_arr s)) s)`;

(* Dynamic allocated references *)
val Mref_def = Define `
  Mref cons x = \s. (Success (StoreRef (LENGTH s)), cons x::s)`;

val dref_def = Define `
  dref n = \s. EL (LENGTH s - n - 1) s`;

val Mdref_aux_def = Define `
  Mdref_aux e (n:num) =
    \s. dtcase s of
          [] => Failure e
        | x::s => if n = 0 then Success x else Mdref_aux e (n-1) s`;

val Mdref_def = Define `
  Mdref e (StoreRef n) =
    \s. (Mdref_aux e (LENGTH s - n - 1) s, s)`;

val Mpop_ref_def = Define `
  Mpop_ref e =
    \(r, s). dtcase s of
               x::s => (r, s)
             | [] => (Failure e, s)`;

val Mref_assign_aux_def = Define `
  Mref_assign_aux e (n:num) x =
    \s. dtcase s of
          x'::s =>
            if n = 0 then
              Success (x::s)
            else
              (dtcase Mref_assign_aux e (n-1) x s of
                 Success s => Success (x'::s)
               | other => other)
        | [] => Failure e`;

val Mref_assign_def = Define `
  Mref_assign e (StoreRef n) x =
    \s. dtcase Mref_assign_aux e (LENGTH s - n - 1) x s of
          Success s => (Success (), s)
        | Failure e => (Failure e, s)`;

val ref_assign_def = Define `
  ref_assign n x = \s. LUPDATE x (LENGTH s - n - 1) s`;

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
     (Mdref e (StoreRef n) state = (Success(dref n state), state))
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
      Success (ref_assign n x state))
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
     (Mref_assign e (StoreRef n) x state = (Success(), ref_assign n x state))
Proof
  rw[Once Mref_assign_def]
  \\ IMP_RES_TAC Mref_assign_aux_eq
  \\ fs[]
QED

val ref_bind_def = Define `
  ref_bind create f pop =
    \s. dtcase create s of
          (Success x, s) => pop (f x s)
        | (Failure x, s) => (Failure x, s)`;

(* TODO: use that *)
val Mget_ref_def = Define `
  Mget_ref get_var = \s. (Success (get_var s), s)`;

val Mset_ref_def = Define `
  Mset_ref set_var x = \s. (Success (), set_var x s)`;

val _ = ParseExtras.temp_tight_equality ();

(* Rules to deal with the monads *)
val st_ex_return_success = Q.prove(
  `!v st r st'.
     st_ex_return v st = (r, st')
     <=>
     r = Success v ∧ st' = st`,
  rw [st_ex_return_def] \\ metis_tac[]);

val st_ex_bind_success = Q.prove (
  `!f g st st' v.
     st_ex_bind f g st = (Success v, st')
     <=>
     ?v' st''.
       f st = (Success v', st'') /\
       g v' st'' = (Success v, st')`,
  rw [st_ex_bind_def] >>
  cases_on `f st` >>
  rw [] >>
  cases_on `q` >>
  rw []);

val otherwise_success = Q.prove(
  `(x otherwise y) s = (Success v, s')
   <=>
   x s = (Success v, s') \/
   ?e s''. x s = (Failure e, s'') /\ y s'' = (Success v, s')`,
  fs[otherwise_def]
  \\ EQ_TAC
  >> DISCH_TAC
  >> Cases_on `x s`
  >> Cases_on `q`
  >> fs[]);

val otherwise_failure = Q.prove(
  `(x otherwise y) s = (Failure e, s')
   <=>
   ?e' s''. x s = (Failure e', s'') /\ y s'' = (Failure e, s')`,
  fs[otherwise_def]
  \\ EQ_TAC
  >> DISCH_TAC
  >> Cases_on `x s`
  >> Cases_on `q`
  >> fs[]);

val otherwise_eq = Q.prove(
  `(x otherwise y) s = (r, s')
   <=>
   (?v. ((x s = (Success v, s') /\ r = Success v) \/
         (?e s''. x s = (Failure e, s'') /\
                  y s'' = (Success v, s') /\
                  r = Success v))) \/
   (?e e' s''. x s = (Failure e', s'') /\
               y s'' = (Failure e, s') /\
               r = Failure e)`,
  Cases_on `x s`
  \\ Cases_on `r`
  \\ fs[otherwise_success, otherwise_failure]
  \\ rw[]
  \\ metis_tac[]);

val can_success = Q.prove(
  `can f x s = (Failure e, s') <=> F`,
  rw[can_def, otherwise_def, st_ex_ignore_bind_def]
  \\ Cases_on `f x s`
  \\ Cases_on `q`
  \\ fs[st_ex_return_def]
);

val Marray_length_success = Q.prove(
  `!get_arr s r s'.
     Marray_length get_arr s = (r, s')
     <=>
     r = Success (LENGTH (get_arr s)) /\
     s' = s`,
  rw[Marray_length_def] \\ metis_tac[]);

val Marray_sub_success = Q.prove(
  `!get_arr e n s v s'.
     Marray_sub get_arr e n s = (Success v, s')
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
     Marray_sub get_arr e n s = (Failure e', s')
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
   (n < LENGTH (get_arr s) /\ s' = s /\ r = Success (EL n (get_arr s))) \/
   (n >= LENGTH (get_arr s) /\ s' = s /\ r = Failure e)`,
  Cases_on `r`
  >> fs[Marray_sub_success, Marray_sub_failure]
  >> metis_tac[]);

val Marray_update_success = Q.prove(
  `!get_arr set_arr e n x s s'.
     Marray_update get_arr set_arr e n x s = (Success v, s')
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
     Marray_update get_arr set_arr e n x s = (Failure e', s')
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
    r = Success ()) \/
   (n >= LENGTH (get_arr s) /\
    s' = s /\
    r = Failure e)`,
  Cases_on `r`
  >> Cases_on `n < LENGTH (get_arr s)`
  >> fs[Marray_update_success, Marray_update_failure]
  >> metis_tac[]);

val Marray_alloc_success = Q.prove(
  `Marray_alloc set_arr n x s = (r, s')
   <=>
   r = Success () /\
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
val run_def = Define `
  run (x : ('a, 'b, 'c) M) state = FST (x state)`;

(* Terms used by the ml_monadBaseLib *)
val Marray_length_const = ``Marray_length:(α -> β list) -> (α, num, γ) M``
val Marray_sub_const = ``Marray_sub:(α -> β list) -> γ -> num -> (α, β, γ) M``
val Marray_update_const =
  ``Marray_update:(α -> β list) ->
    (β list -> α -> α) -> γ -> num -> β -> (α, unit, γ) M``
val Marray_alloc_const =
  ``Marray_alloc:(α list -> β -> γ) -> num -> α -> β -> (unit, δ) exc # γ``
val parsed_terms = save_thm("parsed_terms",
  pack_list (pack_pair pack_string pack_term)
    [
     ("K", ``K : 'a -> 'b -> 'a``),
     ("FST", ``FST : 'a # 'b -> 'a``),
     ("SND", ``SND : 'a # 'b -> 'b``),
     ("REPLICATE", ``REPLICATE : num -> 'a -> 'a list``),
     ("unit", ``()``),
     ("Failure", ``Failure : 'a -> ('b, 'a) exc``),
     ("Success", ``Success : 'a -> ('a, 'b) exc``),
     ("Marray_length", Marray_length_const),
     ("Marray_sub", Marray_sub_const),
     ("Marray_update", Marray_update_const),
     ("Marray_alloc", Marray_alloc_const),
     ("run", ``run``)
    ]);

(* Types used by the ml_monadBaseLib *)
val parsed_types = save_thm("parsed_types",
  pack_list (pack_pair pack_string pack_type)
    [
      ("exc",``:('a, 'b) exc``),
      ("pair", ``:'a # 'b``),
      ("num", ``:num``),
      ("M", ``:('a, 'b, 'c) M``)
    ]);

val _ = export_theory ();

