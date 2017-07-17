open preamble semanticPrimitivesTheory

val _ = new_theory "ml_monadBase";

val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = hide "state";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Datatype `
  exc = Success 'a | Failure 'b`;

val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val st_ex_bind_def = Define `
(st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    dtcase x s of
      (Success y,s) => f y s
    | (Failure x,s) => (Failure x,s)`;

val st_ex_return_def = Define `
(st_ex_return (*: α -> (β, α, γ) M*)) x =
  λs. (Success x, s)`;

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = add_infix("otherwise",400,HOLgrammars.RIGHT)

val otherwise_def = Define `
  x otherwise y = \state.
     dtcase ((x : ('a, 'b, 'c) M) state) of
      (Success y, state) => (Success y, state)
    | (Failure e, state) => (y : ('a, 'b, 'c) M) state`;

val _ = Define `
  can f x = (do f x ; return T od
             otherwise return F)`;

(* TODO: Move that inside the proper lib *)
(* fun define_raise_handle raise_name handle_name excn =
  let
      val _ = if is_const excn then () else (failwith "define_raise_handle")
      val [exc_cons_type, exc_type] = type_of excn |> dest_type |> snd

      val raise_def = case raise_name of
	SOME raise_name => let
        val raise_type = ``:'d -> ('a, 'b, 'c) M``
	val raise_type = Type.type_subst [``:'c`` |-> exc_type, ``:'d`` |-> exc_cons_type] raise_type
	val raise_var = mk_var(raise_name, raise_type) in
        SOME (Define `^raise_var t = \state. (Failure (^excn t), state)`) end
        | NONE => NONE

      val handle_def = case handle_name of
      SOME handle_name => let      
      val handle_type = ``:('a, 'b, 'c) M -> ('d -> ('a, 'b, 'c) M) -> ('a, 'b, 'c) M``
      val handle_type = Type.type_subst [``:'c`` |-> exc_type, ``:'d`` |-> exc_cons_type] handle_type
      val handle_var = mk_var(handle_name, handle_type) in
      SOME (Define
        `^handle_var x f = \state. dtcase (x state) of
          | (Failure (^excn t), state) => f t state
          | other => other`) end
      | NONE => NONE 
  in
      (raise_def, handle_def)
  end
  handle HOL_ERR _ => failwith "define_raise_handle"; *)

(* Dynamic allocation of references *)
val _ = Hol_datatype `
store_ref = StoreRef of num`;

(* Arrays *)

(* Msub *)
val Msub_def = Define `
Msub e (n : num) l = case l of [] => Failure e
| x::l' => if n = 0 then Success x else Msub e (n-1) l'`;

val Msub_eq = Q.store_thm("Msub_eq",
`!l n e. n < LENGTH l ==> (Msub e n l = Success (EL n l))`,
Induct
\\ rw[]
\\ rw[Once Msub_def]
\\ Cases_on `n`
\\ fs[]);

val Msub_exn_eq = Q.store_thm("Msub_exn_eq",
`!l n e. n >= LENGTH l ==> (Msub e n l = Failure e)`,
Induct
\\ rw[]
\\ rw[Once Msub_def]
\\ Cases_on `n`
\\ fs[]);

(* Mupdate *)
val Mupdate_def = Define `
Mupdate e x (n : num) l = case l of [] => Failure e
| x'::l' => if n = 0 then Success (x::l')
	    else (case Mupdate e x (n-1) l' of Success l'' => Success (x'::l'')
					  | other => other)`;

val Mupdate_eq = Q.store_thm("Mupdate_eq",
`!l n x e. n < LENGTH l ==> (Mupdate e x n l = Success(LUPDATE x n l))`,
Induct
\\ rw[Once Mupdate_def, LUPDATE_def]
\\ Cases_on `n`
\\ fs[LUPDATE_def]);

val Mupdate_exn_eq = Q.store_thm("Mupdate_exn_eq",
`!l n x e. n >= LENGTH l ==> (Mupdate e x n l = Failure e)`,
Induct
\\ rw[Once Mupdate_def, LUPDATE_def]
\\ Cases_on `n`
\\ fs[LUPDATE_def]);

(* Array allocation *)
val replicate_def = Define `
replicate (n : num) x = if n = 0 then [] else x::(replicate (n-1) x)`;

val replicate_eq = Q.store_thm("replicate_eq",
`replicate = REPLICATE`,
irule EQ_EXT
\\ Induct
\\ irule EQ_EXT
\\ rw[Once replicate_def]);

(* Array resize *)
val array_resize_def = Define `
array_resize (n : num) x a =
if n = 0 then []
else case a of [] => x::(array_resize (n-1) x a)
	     | x'::a' => x'::(array_resize (n-1) x a')`;

val array_resize_eq = Q.store_thm("array_resize_eq",
`!a n x. array_resize n x a = (TAKE n a) ++ (REPLICATE (n - LENGTH a) x)`,
Induct
>-(Induct >> rw[Once array_resize_def])
\\ STRIP_TAC
\\ Induct
\\ rw[Once array_resize_def]);

(* User functions *)
val Marray_length_def = Define `
Marray_length get_arr () = \state. (Success(LENGTH (get_arr state)), state)`;

val Marray_sub_def = Define `
Marray_sub get_arr e n = \state. (Msub e n (get_arr state), state)`;

val Marray_update_def = Define `
Marray_update get_arr set_arr e n x =
\state. case Mupdate e x n (get_arr state) of
Success a => (Success(), set_arr a state)
| Failure e => (Failure e, state)`;

val Marray_alloc_def = Define `
Marray_alloc set_arr n x =
\state. (Success(), set_arr (replicate n x) state)`;

val Marray_resize_def = Define `
Marray_resize get_arr set_arr n x =
\state. (Success(), set_arr (array_resize n x (get_arr state)) state)`;

(* Dynamic allocated references *)
val Mref_def = Define `
Mref cons x = \state. (Success (StoreRef(LENGTH state)), (cons x)::state)`;

val dref_def = Define `
dref n = \state. EL (LENGTH state - n - 1) state`;

val Mdref_aux_def = Define `
Mdref_aux e (n:num) = \state.
case state of
[] => Failure e
| x::state' => if n = 0 then Success x else Mdref_aux e (n-1) state'`;

val Mdref_def = Define `
Mdref e (StoreRef n) = \state. (Mdref_aux e (LENGTH state - n - 1) state, state)`;

val Mpop_ref_def = Define `
Mpop_ref e = \(r, state). case state of
x::state' => (r, state')
| [] => (Failure e, state)`;

val Mref_assign_aux_def = Define `
Mref_assign_aux e (n:num) x = \state.
case state of
x'::state => if n = 0 then Success (x::state)
	     else (case Mref_assign_aux e (n-1) x state of Success state' => Success (x'::state')
							| other => other)
| [] => Failure e`

val Mref_assign_def = Define `
Mref_assign e (StoreRef n) x =
\state. case Mref_assign_aux e (LENGTH state - n - 1) x state of
Success state => (Success(), state)
| Failure e => (Failure e, state)`;

val ref_assign_def = Define `
ref_assign n x = \state. LUPDATE x (LENGTH state - n - 1) state`;

val dref_const_state_eq = Q.store_thm("dref_cons_state",
`n < LENGTH state ==> (dref n (x::state) = dref n state)`,
rw[Once dref_def]
\\ fs[SUC_ONE_ADD]
\\ Cases_on `LENGTH state - n` >-(fs[])
\\ rw[]
\\ rw[Once dref_def]
\\ `LENGTH state - (n + 1) = LENGTH state - n - 1` by numLib.DECIDE_TAC
\\ POP_ASSUM(fn x => rw[x]));

val dref_first = Q.store_thm("dref_first",
`dref (LENGTH s) (r::s) = r`,
fs[Once dref_def, SUC_ONE_ADD]);

val Mdref_eq = Q.store_thm("Mdref_eq",
`!state n. n < LENGTH state ==> (Mdref e (StoreRef n) state = (Success(dref n state), state))`,
Induct
>-(rw[Once Mdref_def, Once Mdref_aux_def])
\\ rw[Once Mdref_def, Once Mdref_aux_def]
>-(rw[Once dref_def]
   \\ fs[]
   \\ `n = LENGTH state` by fs[SUC_ONE_ADD]
   \\ rw[SUC_ONE_ADD])
\\ fs[SUC_ONE_ADD]
\\ `Mdref_aux e (LENGTH state - (n + 1)) state = FST(Mdref e (StoreRef n) state)`
   by (last_x_assum(fn x => ALL_TAC) \\ rw[Once Mdref_def])
\\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
\\ rw[]
\\ rw[dref_const_state_eq]);

val Mref_assign_aux_eq = Q.store_thm("Mref_assign_aux_eq",
`!state e n x. n < LENGTH state ==>
(Mref_assign_aux e (LENGTH state - n - 1) x state = Success (ref_assign n x state))`,
Induct
>-(rw[Once Mref_assign_aux_def, Once ref_assign_def])
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
\\ rw[]);

val Mref_assign_eq = Q.store_thm("Mref_assign_eq",
`!state e n x. n < LENGTH state ==>
(Mref_assign e (StoreRef n) x state = (Success(), ref_assign n x state))`,
rw[Once Mref_assign_def]
\\ IMP_RES_TAC Mref_assign_aux_eq
\\ fs[]);

val ref_bind_def = Define `
ref_bind create f pop = \s.
case create s of
(Success x, s) => pop(f x s)
| (Failure x, s) => (Failure x, s)`;

(* TODO: use that *)
val Mget_ref_def = Define `
Mget_ref get_var = \state. (Success (get_var state), state)`;

val Mset_ref_def = Define `
Mset_ref set_var x = \state. (Success (), set_var x state)`;

val _ = export_theory ();
