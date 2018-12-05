(*
  Bind various built-in functions to function names that the parser
  expects, e.g. the parser generates a call to a function called "+"
  when it parses 1+2.
*)
open preamble
     semanticPrimitivesTheory ml_translatorTheory
     ml_translatorLib ml_progLib cfLib basisFunctionsLib
     StringProgTheory

val _ = new_theory "mlbasicsProg"

val _ = translation_extends"StringProg"

val mk_binop_def = Define `
  mk_binop name prim = Dlet unknown_loc (Pvar name)
    (Fun "x" (Fun "y" (App prim [Var (Short "x"); Var (Short "y")])))`;

val mk_unop_def = Define `
  mk_unop name prim = Dlet unknown_loc (Pvar name)
    (Fun "x" (App prim [Var (Short "x")]))`;

(* no longer necessary
(* list, bool, and option come from the primitive types in
 * semantics/primTypesTheory *)
val _ = append_prog
  ``[Tdec (Dtabbrev unknown_loc [] "int" (Tapp [] TC_int));
     Tdec (Dtabbrev unknown_loc [] "unit" (Tapp [] TC_tup));
     Tdec (Dtabbrev unknown_loc [] "string" (Tapp [] TC_string));
     Tdec (Dtabbrev unknown_loc ["'a"] "ref" (Tapp [Tvar "'a"] TC_ref));
     Tdec (Dtabbrev unknown_loc ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector));
     Tdec (Dtabbrev unknown_loc ["'a"] "array" (Tapp [Tvar "'a"] TC_array));
     Tdec (Dtabbrev unknown_loc [] "exn" (Tapp [] TC_exn));
     Tdec (Dtabbrev unknown_loc [] "word" (Tapp [] TC_word64));
     Tdec (Dtabbrev unknown_loc [] "char" (Tapp [] TC_char))]``
*)

val _ = trans "+" `(+):int->int->int`
val _ = trans "-" `(-):int->int->int`
val _ = trans "*" `int_mul`
val _ = trans "div" `(/):int->int->int`
val _ = trans "mod" `(%):int->int->int`
val _ = trans "<" `(<):int->int->bool`
val _ = trans ">" `(>):int->int->bool`
val _ = trans "<=" `(<=):int->int->bool`
val _ = trans ">=" `(>=):int->int->bool`
val _ = trans "~" `\i. - (i:int)`
val _ = trans "@" `(++):'a list -> 'a list -> 'a list`


(* other basics that parser targets -- CF verified *)

val _ = trans "=" `\x1 x2. x1 = x2:'a`
val _ = trans "not" `\x. ~x:bool`
val _ = trans "<>" `\x1 x2. x1 <> (x2:'a)`
val _ = trans "^" `mlstring$strcat`

val _ = append_prog
  ``[mk_binop ":=" Opassign;
     mk_unop "!" Opderef;
     mk_unop "ref" Opref]``

fun prove_ref_spec op_name =
  xcf op_name (get_ml_prog_state()) \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

Theorem ref_spec
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" (get_ml_prog_state ())) [xv]
          emp (POSTv rv. rv ~~> xv)`
  (prove_ref_spec "op ref");

Theorem deref_spec
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" (get_ml_prog_state ())) [rv]
          (rv ~~> xv) (POSTv yv. cond (xv = yv) * rv ~~> xv)`
  (prove_ref_spec "op !");

Theorem assign_spec
  `!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" (get_ml_prog_state ())) [rv; yv]
       (rv ~~> xv) (POSTv v. cond (UNIT_TYPE () v) * rv ~~> yv)`
  (prove_ref_spec "op :=");

val _ = export_theory ()
