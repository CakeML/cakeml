open preamble
     ml_translatorTheory ml_translatorLib semanticPrimitivesTheory basisFunctionsLib 
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib mlstringProgTheory

val _ = new_theory "mlbasicsProg"

val _ = translation_extends"mlstringProg"

val mk_binop_def = Define `
  mk_binop name prim = Dlet (Pvar name)
    (Fun "x" (Fun "y" (App prim [Var (Short "x"); Var (Short "y")])))`;

val mk_unop_def = Define `
  mk_unop name prim = Dlet (Pvar name)
    (Fun "x" (App prim [Var (Short "x")]))`;

val _ = append_prog
  ``[Tdec (Dtabbrev [] "int" (Tapp [] TC_int));
     Tdec (Dtabbrev [] "unit" (Tapp [] TC_tup));
     Tdec (Dtabbrev ["'a"] "ref" (Tapp [Tvar "'a"] TC_ref));
     Tdec (Dtabbrev [] "exn" (Tapp [] TC_exn));
     Tdec (Dtabbrev [] "word" (Tapp [] TC_word8));
     Tdec (Dtabbrev [] "char" (Tapp [] TC_char))]``


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


(* other basics that parser targets -- CF verified *)

val _ = trans "=" `\x1 x2. x1 = x2:'a`
val _ = trans "not" `\x. ~x:bool`
val _ = trans "<>" `\x1 x2. x1 <> (x2:'a)`

val _ = append_prog
  ``[Tdec (mk_binop ":=" Opassign);
     Tdec (mk_unop "!" Opderef);
     Tdec (mk_unop "ref" Opref)]``

fun prove_ref_spec op_name =
  xcf op_name (get_ml_prog_state()) \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

val ref_spec = Q.store_thm ("ref_spec",
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" (get_ml_prog_state ())) [xv]
          emp (POSTv rv. rv ~~> xv)`,
  prove_ref_spec "op ref");

val deref_spec = Q.store_thm ("deref_spec",
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" (get_ml_prog_state ())) [rv]
          (rv ~~> xv) (POSTv yv. cond (xv = yv) * rv ~~> xv)`,
  prove_ref_spec "op !");

val assign_spec = Q.store_thm ("assign_spec",
  `!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" (get_ml_prog_state ())) [rv; yv]
       (rv ~~> xv) (POSTv v. cond (UNIT_TYPE () v) * rv ~~> yv)`,
  prove_ref_spec "op :=");


val _ = export_theory ()
