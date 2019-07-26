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

val _ = trans "+" intSyntax.plus_tm;
val _ = trans "-" intSyntax.minus_tm;
val _ = trans "*" intSyntax.mult_tm;
val _ = trans "div" intSyntax.div_tm;
val _ = trans "mod" intSyntax.mod_tm;
val _ = trans "<" intSyntax.less_tm;
val _ = trans ">" intSyntax.great_tm;
val _ = trans "<=" intSyntax.leq_tm;
val _ = trans ">=" intSyntax.geq_tm;
val _ = trans "~" ``\i. - (i:int)``;
val _ = trans "@" listSyntax.append_tm;


(* other basics that parser targets -- CF verified *)

val _ = trans "=" ``\x1 x2. x1 = x2:'a``;
val _ = trans "not" ``\x. ~x:bool``;
val _ = trans "<>" ``\x1 x2. x1 <> (x2:'a)``;
val _ = trans "^" mlstringSyntax.strcat_tm;

val _ = append_prog
  ``[mk_binop ":=" Opassign;
     mk_unop "!" Opderef
  (* mk_unop "ref" Opref *)]``

fun prove_ref_spec op_name =
  xcf op_name (get_ml_prog_state()) \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

(*
Theorem ref_spec:
   !xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" (get_ml_prog_state ())) [xv]
          emp (POSTv rv. rv ~~> xv)
Proof
  prove_ref_spec "op ref"
QED
*)

Theorem deref_spec:
   !xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" (get_ml_prog_state ())) [rv]
          (rv ~~> xv) (POSTv yv. cond (xv = yv) * rv ~~> xv)
Proof
  prove_ref_spec "op !"
QED

Theorem assign_spec:
   !rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" (get_ml_prog_state ())) [rv; yv]
       (rv ~~> xv) (POSTv v. cond (UNIT_TYPE () v) * rv ~~> yv)
Proof
  prove_ref_spec "op :="
QED

val bool_toString_def = Define `
  bool_toString b = if b then strlit "True" else strlit"False"`;

val _ = ml_prog_update (open_module "Bool");
val _ = (next_ml_names := ["toString"]);
val _ = translate bool_toString_def;
val _ = (next_ml_names := ["compare"]);
val _ = translate comparisonTheory.bool_cmp_def;
val _ = ml_prog_update (close_module NONE);

val pair_toString_def = Define `
  pair_toString f1 f2 (x,y) =
    concat [strlit"(";
            f1 x;
            strlit", ";
            f2 y;
            strlit")"]`;

val _ = ml_prog_update (open_module "Pair");
val _ = (next_ml_names := ["map"]);
val _ = translate pairTheory.PAIR_MAP_THM;
val _ = (next_ml_names := ["toString"]);
val _ = translate pair_toString_def;
val _ = (next_ml_names := ["compare"]);
val _ = translate comparisonTheory.pair_cmp_def;
val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
