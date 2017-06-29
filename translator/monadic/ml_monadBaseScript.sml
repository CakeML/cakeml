open preamble

val _ = new_theory "ml_monadBase";
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

(* COPY/PASTE from inferScript.sml *)
(*  The inferencer uses a state monad internally to keep track of unifications at the expressions level *)

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
(* End of COPY/PASTE from inferScript.sml *)

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
fun define_raise_handle raise_name handle_name excn =
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
  handle HOL_ERR _ => failwith "define_raise_handle";

val _ = export_theory ();
