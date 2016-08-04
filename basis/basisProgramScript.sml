open preamble
open ml_translatorTheory ml_translatorLib semanticPrimitivesTheory
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib

val _ = new_theory "basisProgram"

(* setup *)

fun trans names def = let
  val _ = (next_ml_names := names)
  in translate def end

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_prog tm pick_name) end

fun append_dec tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_dec tm pick_name) end

fun append_decs tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  val tms = fst (listSyntax.dest_list tm)
  in (map append_dec tms; ()) end

fun basis_st () = get_ml_prog_state ()

val _ = Define `
  mk_binop name prim = Dlet (Pvar name)
    (Fun "x" (Fun "y" (App prim [Var (Short "x"); Var (Short "y")])))`;

val _ = Define `
  mk_unop name prim = Dlet (Pvar name)
    (Fun "x" (App prim [Var (Short "x")]))`;


(* basic type abbreviations *)

val _ = append_prog
  ``[Tdec (Dtabbrev [] "int" (Tapp [] TC_int));
     Tdec (Dtabbrev [] "string" (Tapp [] TC_string));
     Tdec (Dtabbrev [] "unit" (Tapp [] TC_tup));
     Tdec (Dtabbrev ["'a"] "ref" (Tapp [Tvar "'a"] TC_ref));
     Tdec (Dtabbrev [] "exn" (Tapp [] TC_exn));
     Tdec (Dtabbrev [] "word" (Tapp [] TC_word8));
     Tdec (Dtabbrev ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector));
     Tdec (Dtabbrev ["'a"] "array" (Tapp [Tvar "'a"] TC_array));
     Tdec (Dtabbrev [] "char" (Tapp [] TC_char))]``


(* the parser targets the following for int arith ops -- translated *)

val _ = trans ["+"] (Define `plus i1 i2 = i1 + i2:int`);
val _ = trans ["-"] (Define `minus i1 i2 = i1 - i2:int`);
val _ = trans ["*"] (Define `times i1 i2 = i1 * i2:int`);
val _ = trans ["div"] (Define `div i1 i2 = i1 / i2:int`);
val _ = trans ["mod"] (Define `mod i1 i2 = i1 % i2:int`);
val _ = trans ["<"] (Define `lt i1 i2 = (i1 < (i2:int))`);
val _ = trans [">"] (Define `gt i1 i2 = (i1 > (i2:int))`);
val _ = trans ["<="] (Define `le i1 i2 = (i1 <= (i2:int))`);
val _ = trans [">="] (Define `ge i1 i2 = (i1 >= (i2:int))`);
val _ = trans ["~"] (Define `uminus i = 0-(i:int)`);


(* other basics that parser targets -- CF verified *)

val _ = trans ["="] (Define `eq x1 x2 = (x1 = (x2:'a))`);

val _ = append_prog
  ``[Tdec (Dlet (Pvar "not") (Fun "x" (If (Var (Short"x"))
          (Con (SOME (Short "false")) []) (Con (SOME (Short "true")) []))));
     Tdec (mk_binop ":=" Opassign);
     Tdec (mk_unop "!" Opderef);
     Tdec (mk_unop "ref" Opref)]``

fun prove_ref_spec op_name =
  xcf op_name (basis_st ()) \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

val ref_spec = store_thm ("ref_spec",
  ``!xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" (basis_st())) [xv]
          emp (\rv. rv ~~> xv)``,
  prove_ref_spec "op ref");

val deref_spec = store_thm ("deref_spec",
  ``!xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" (basis_st())) [rv]
          (rv ~~> xv) (\yv. cond (xv = yv) * rv ~~> xv)``,
  prove_ref_spec "op !");

val assign_spec = store_thm ("assign_spec",
  ``!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" (basis_st())) [rv; yv]
       (rv ~~> xv) (\v. cond (UNIT_TYPE () v) * rv ~~> yv)``,
  prove_ref_spec "op :=");


(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev [] "word" (Tapp [] TC_word8)``;
val _ = trans [] (Define `FromInt i = (n2w i):word8`);
val _ = trans [] (Define `toInt w = w2n (w:word8)`);

val _ = ml_prog_update (close_module NONE);


(* Word8Array module -- CF verified *)

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs
   ``[Dtabbrev [] "array" (Tapp [] TC_word8array);
      Dtabbrev [] "elem" (Tapp [] TC_word8);
      mk_binop "array" Aw8alloc;
      mk_binop "sub" Aw8sub;
      mk_unop "length" Aw8length;
      Dlet (Pvar "update") (Fun "x" (Fun "y" (Fun "z"
        (App Aw8update [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``

val _ = ml_prog_update (close_module NONE);

fun prove_array_spec op_name =
  xcf op_name (basis_st()) \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

val w8array_alloc_spec = store_thm ("w8array_alloc_spec",
  ``!n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" (basis_st())) [nv; wv]
       emp (\v. W8ARRAY v (REPLICATE n w))``,
  prove_array_spec "Word8Array.array");

val w8array_sub_spec = store_thm ("w8array_sub_spec",
  ``!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" (basis_st())) [av; nv]
       (W8ARRAY av a) (\v. cond (WORD (EL n a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.sub");

val w8array_length_spec = store_thm ("w8array_length_spec",
  ``!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" (basis_st())) [av]
       (W8ARRAY av a) (\v. cond (NUM (LENGTH a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.length");

val w8array_update_spec = store_thm ("w8array_update_spec",
  ``!a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" (basis_st()))
       [av; nv; wv]
       (W8ARRAY av a)
       (\v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))``,
  prove_array_spec "Word8Array.update");


(* Vector module -- translated *)

val _ = ml_prog_update (open_module "Vector");

val _ = append_dec ``Dtabbrev ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector)``;
val _ = trans [] (Define `fromList l = Vector l`);
val _ = trans ["length"] (Define `vec_length l = length l`);
val _ = trans ["sub"] (Define `vec_sub l = sub l`);

val _ = ml_prog_update (close_module NONE);


(* Array module -- CF verified *)

val _ = ml_prog_update (open_module "Array");

val _ = append_decs
   ``[Dtabbrev ["'a"] "array" (Tapp [Tvar "'a"] TC_array);
      mk_binop "array" Aalloc;
      mk_binop "sub" Asub;
      mk_unop "length" Alength;
      Dlet (Pvar "update")
       (Fun "x" (Fun "y" (Fun "z"
         (App Aupdate [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``

val _ = ml_prog_update (close_module NONE);

val array_alloc_spec = store_thm ("array_alloc_spec",
  ``!n nv v.
     NUM n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.array" (basis_st())) [nv; v]
       emp (\av. ARRAY av (REPLICATE n v))``,
  prove_array_spec "Array.array");

val array_sub_spec = store_thm ("array_sub_spec",
  ``!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.sub" (basis_st())) [av; nv]
       (ARRAY av a) (\v. cond (v = EL n a) * ARRAY av a)``,
  prove_array_spec "Array.sub");

val array_length_spec = store_thm ("array_length_spec",
  ``!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Array.length" (basis_st())) [av]
       (ARRAY av a)
       (\v. cond (NUM (LENGTH a) v) * ARRAY av a)``,
  prove_array_spec "Array.length");

val array_update_spec = store_thm ("array_update_spec",
  ``!a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.update" (basis_st()))
       [av; nv; v]
       (ARRAY av a)
       (\uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))``,
  prove_array_spec "Array.update");


(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val _ = append_dec ``Dtabbrev [] "char" (Tapp [] TC_char)``;
val _ = trans [] (Define `ord c = ORD c`);
val _ = trans [] (Define `chr c = CHR c`);
val _ = trans ["<"] (Define `lt c1 c2 = (c1 < (c2:char))`);
val _ = trans [">"] (Define `gt c1 c2 = (c1 > (c2:char))`);
val _ = trans ["<="] (Define `le c1 c2 = (c1 <= (c2:char))`);
val _ = trans [">="] (Define `ge c1 c2 = (c1 >= (c2:char))`);

val _ = ml_prog_update (close_module NONE);


(* String module -- translated *)

val _ = ml_prog_update (open_module "String");

val _ = append_dec ``Dtabbrev [] "string" (Tapp [] TC_string)``;
val _ = trans ["explode"] (Define `str_explode s = explode s`);
val _ = trans ["implode"] (Define `str_implode s = implode s`);
val _ = trans ["size"] (Define `str_size s = strlen (s:mlstring)`);

val _ = ml_prog_update (close_module NONE);


(* TODO: add a few modules for basic I/O once CF supports FFI *)


(* definition of basis program *)

val basis_prog = get_ml_prog_state () |> remove_snocs
  |> get_thm |> concl |> rator |> rator |> rator |> rand

val basis_def = Define `basis = ^basis_prog`;

val _ = export_theory ()
