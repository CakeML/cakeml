open preamble
open ml_translatorTheory ml_translatorLib semanticPrimitivesTheory
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib

val _ = new_theory "basisProgram"

(* setup *)

fun get_module_prefix () = let
  val mod_tm = ml_progLib.get_thm (get_ml_prog_state ())
               |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none mod_tm then "" else
       stringSyntax.fromHOLstring (mod_tm |> rand |> rator |> rand) ^ "_"
  end

fun trans ml_name q = let
  val rhs = Term q
  val prefix = get_module_prefix ()
  val tm = mk_eq(mk_var(prefix ^ pick_name ml_name,type_of rhs),rhs)
  val def = Define `^tm`
  val _ = (next_ml_names := [ml_name])
  val v_thm = translate (def |> SIMP_RULE std_ss [FUN_EQ_THM])
  val v_thm = v_thm |> REWRITE_RULE [def]
                    |> CONV_RULE (DEPTH_CONV ETA_CONV)
  val v_name = v_thm |> concl |> rand |> dest_const |> fst
  (* evaluate precondition *)
  val pat = PRECONDITION_def |> SPEC_ALL |> GSYM |> concl |> rand
  fun PRECOND_CONV c tm =
    if can (match_term pat) tm then RAND_CONV c tm else NO_CONV tm
  val v_thm = v_thm |> DISCH_ALL
                    |> CONV_RULE (ONCE_DEPTH_CONV (PRECOND_CONV EVAL))
                    |> UNDISCH_ALL
  val _ = save_thm(v_name ^ "_thm",v_thm)
  in v_thm end

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
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`

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
val _ = trans "fromList" `Vector`
val _ = trans "length" `length`
val _ = trans "sub" `sub`

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
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`
val _ = trans "<" `string$char_lt`
val _ = trans ">" `string$char_gt`
val _ = trans "<=" `string$char_le`
val _ = trans ">=" `string$char_ge`

val _ = ml_prog_update (close_module NONE);


(* String module -- translated *)

val _ = ml_prog_update (open_module "String");

val _ = append_dec ``Dtabbrev [] "string" (Tapp [] TC_string)``;
val _ = trans "explode" `explode`
val _ = trans "implode" `implode`
val _ = trans "size" `strlen`

val _ = ml_prog_update (close_module NONE);


(* CharIO -- CF verified *)

(*

  val print = bytarray [0w];
  val print = fn c =>
    val _ = print[0] := (n2w (ord c))
    in FFI 0 print end

*)

val _ = ml_prog_update (open_module "CharIO");

fun derive_eval_thm v_name e = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val lemma = goal
    |> (NCONV 50 (SIMP_CONV (srw_ss()) [Once bigStepTheory.evaluate_cases,
            PULL_EXISTS,do_app_def,store_alloc_def,LET_THM]) THENC EVAL)
  val v_thm = prove(mk_imp(lemma |> concl |> rand,goal),fs [lemma])
                 |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
  val v_tm = v_thm |> concl |> rand |> rand |> rand
  val v_def = define_abbrev true v_name v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "print_loc" e) "print" [])

val Apps_def = tDefine "Apps" `
  (Apps [x;y] = App Opapp [x;y]) /\
  (Apps [] = ARB) /\
  (Apps xs = App Opapp [Apps (FRONT xs); LAST xs])`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_FRONT]);

val e =
  ``Let (SOME "c") (App Opapp [Var (Long "Char" "ord"); Var (Short "c")])
     (Let (SOME "c") (App Opapp [Var (Long "Word8" "fromInt"); Var (Short "c")])
       (Let (SOME "c") (Apps [Var (Long "Word8Array" "update"); Var (Short "print");  Lit (IntLit 0); Var (Short "c")])
         (Let (SOME "_") (App (FFI 0) [Var (Short "print")])
           (Var (Short "c")))))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"print"`` ``"c"`` e "print_v")

val _ = ml_prog_update (close_module NONE);

val stdout_fun_def = Define `
  stdout_fun = (\_ bytes s. case (bytes,s) of
                    | ([w],Str output) => SOME ([w],Str (output ++ [CHR (w2n w)]))
                    | _ => NONE)`

val STDOUT_def = Define `
  STDOUT output = IO (Str output) stdout_fun [0]`

val CHAR_IO_def = Define `
  CHAR_IO = SEP_EXISTS w. W8ARRAY print_loc [w]`;

val print_spec = store_thm ("print_spec",
  ``!a av n nv v.
     CHAR c cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.print" (basis_st()))
       [cv]
       (CHAR_IO * STDOUT output)
       (\uv. cond (UNIT_TYPE () uv) * CHAR_IO * STDOUT (output ++ [c]))``,
  xcf "CharIO.print" (basis_st())
  \\ fs [CHAR_IO_def] \\ xpull
  \\ xlet `\xv. W8ARRAY print_loc [w] * STDOUT output * & (NUM (ORD c) xv)`
  THEN1 (xapp \\ xsimpl \\ metis_tac [])
  \\ xlet `\wv. W8ARRAY print_loc [w] * STDOUT output *
                & (WORD (n2w (ORD c):word8) wv)`
  THEN1 (xapp \\ xsimpl \\ metis_tac [])
  \\ xlet `\zv. STDOUT output * W8ARRAY print_loc [n2w (ORD c)] * & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [CHAR_IO_def,EVAL ``print_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC \\ fs [])
  \\ xlet `\_. STDOUT (output ++ [c]) * W8ARRAY print_loc [n2w (ORD c)]`
  THEN1
   (xffi
    \\ fs [EVAL ``print_loc``, STDOUT_def]
    \\ `MEM 0 [0n]` by EVAL_TAC \\ instantiate
    \\ qexists_tac `[n2w (ORD c)]` \\ xsimpl
    \\ qexists_tac `emp` \\ xsimpl
    \\ qexists_tac `Str output` \\ fs []
    \\ qexists_tac `Str (output ++ [c])` \\ fs []
    \\ qexists_tac `stdout_fun` \\ xsimpl
    \\ EVAL_TAC \\ fs [ORD_BOUND,CHR_ORD])
  \\ xret \\ xsimpl);

(* definition of basis program *)

val basis_st = get_ml_prog_state ();

val basis_prog_state = save_thm("basis_prog_state",
  ml_progLib.pack_ml_prog_state basis_st);

val basis_prog = basis_st |> remove_snocs
  |> get_thm |> concl |> rator |> rator |> rator |> rand

val basis_def = Define `basis = ^basis_prog`;

val _ = export_theory ()
