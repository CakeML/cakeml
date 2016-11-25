open preamble
     ml_translatorTheory ml_translatorLib semanticPrimitivesTheory
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib

val _ = new_theory "basisProg"

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

val _ = Datatype `order = LESS | EQUAL | GREATER`;

val _ = register_type ``:order``;

val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;

(* new stuff *)
(*################################################################################*)

(* List module -- Translated *)

(* TODO: move this module into its own theory and check the translator to allow
names that save_thm can't handle, see if translation is being module specific
and if next_ml_names is working as intended *)


val _ = ml_prog_update (open_module "List");

val _ = append_dec ``Dtabbrev ["'a"] "list" (Tapp [Tvar "'a"] (TC_name (Short "list")))``;

(*--------------------------------------------------------------------------------*)

val result = translate NULL_DEF;

(*--------------------------------------------------------------------------------*)

val result = translate LENGTH;

(*--------------------------------------------------------------------------------*)

(*This could be needed to be changed to an infix @ if HOL doesn't do it *)
val result = translate APPEND;

(*--------------------------------------------------------------------------------*)

show_assums := true;
(*This has a precondition and I don't know what is wanted with pattern matching,
  list empty exception*)
val result = translate HD;
val hd_side_def = definition"hd_side_def"

(*--------------------------------------------------------------------------------*)

(*This has a precondition and I don't know what is wanted with pattern matching, 
  list empty exception*)
val result = translate TL;

(*--------------------------------------------------------------------------------*)

(*Pre-conditions needs to raise an exception with the list is empty *)
val result = translate LAST_DEF;

(*--------------------------------------------------------------------------------*)

val getItem_def = Define`
  getItem l = case l of
    [] => NONE
    | (h::t) => SOME(h, t)`; 

val result = translate getItem_def;

(*--------------------------------------------------------------------------------*)

val nth_def = Define`
  nth (l, i) = EL i l`;
(*EL has a precondition because TL and HD have preconditions, subscript exception *)
val result = translate EL;
val result = translate nth_def;

(*--------------------------------------------------------------------------------*)

(*subscript exception *)
val take_def = Define`
  take (l, i) = TAKE i l`;
(*see if this is correct *)
val result = next_ml_names := ["TAKE_HOL"];
val result = translate TAKE_def;
val result = translate take_def;

(*--------------------------------------------------------------------------------*)

val drop_def = Define`
  drop (l, i) = DROP i l`;
val result = next_ml_names := ["DROP_HOL"];
val result = translate DROP_def;
val result = translate drop_def;

(*--------------------------------------------------------------------------------*)

(*
val rev_def = Define`
  rev l = REVERSE l`;
*)
val result = next_ml_names := ["rev_def"];
val result = translate REVERSE_DEF;
(* val result = translate rev_def; *)

(*--------------------------------------------------------------------------------*)

val result = next_ml_names := ["concat_def"];
val result = translate FLAT;

(*--------------------------------------------------------------------------------*)

val revAppend_def = Define`
  revAppend (l1, l2) = REV l1 l2`;
val result = translate REV_DEF;
val result = translate revAppend_def;

(*--------------------------------------------------------------------------------*)

(*What do we do with app?? *)

(*--------------------------------------------------------------------------------*)

val result = translate MAP;

(*--------------------------------------------------------------------------------*)

val mapPartial_def = Define`
  mapPartial f l = case l of
    [] => []
    | (h::t) => if f h = NONE then h::(mapPartial f t)
      else mapPartial f t`;
val result = translate mapPartial_def;   

(*--------------------------------------------------------------------------------*)

val find_def = Define`
  find f l = case l of
    [] => NONE
    | (h::t) => if f h = NONE then find f t
      else h`;
val result = translate find_def;

(*--------------------------------------------------------------------------------*)

val filter_def = Define`
  filter f l = case l of
    [] => []
    | (h::t) => if f h then h::(filter f t)
      else filter f t`;
val result = translate filter_def; 

(*--------------------------------------------------------------------------------*)

val partition_aux_def = Define`
  partition_aux f l (pos, neg) = case l of
    [] => (pos, neg)
    | (h::t) => if f h then partition_aux f t ((h::pos), neg)
      else partition_aux f t (pos, (h::neg))`;

val partition_def = Define`
  partition f l = partition_aux f l ([], [])`;

val result = translate partition_aux_def;
val result = translate partition_def;

(*--------------------------------------------------------------------------------*)

val result = translate FOLDL;

(*--------------------------------------------------------------------------------*)

val result = translate FOLDR;

(*--------------------------------------------------------------------------------*)

val result = translate EXISTS_DEF;

(*--------------------------------------------------------------------------------*)

val result = next_ml_names := ["all_def"];
val result = translate EVERY_DEF;

(*--------------------------------------------------------------------------------*)

val tabulate_def = Define`
  tabulate (n, f) = GENLIST f n`;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
val result = translate tabulate_def;

(*--------------------------------------------------------------------------------*)

(* TODO: Check the functionality of this function *)
val collate_def = Define`
  collate f (l1, l2) = case l1 of
    [] => (case l2 of
      [] => EQUAL
      | (h2::t2) => GREATER)
    | (h1::t1) => (case l2 of
      [] => LESS
      | (h2::t2) => if f h1 h2 = EQUAL then collate f (t1, t2)
        else f h1 h2)`;
val result = translate collate_def;

(*--------------------------------------------------------------------------------*)
val _ = ml_prog_update (close_module NONE);

(* end new stuff *)
(*################################################################################*)


(* Vector module -- translated *)
(* TODO: move this module into its own theory and check the translator to allow
names that save_thm can't handle *)

val _ = ml_prog_update (open_module "Vector");

(* TODO: maxLen will probably need to be a CakeML primitive (if we want it at all) *)

val _ = append_dec ``Dtabbrev ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector)``;
val _ = trans "fromList" `Vector`
val _ = trans "length" `length`
val _ = trans "sub" `sub`

(* new stuff *)

(*--------------------------------------------------------------------------------*)


val tabulate_def = Define`
  tabulate n f = Vector (GENLIST f n)`;
(* val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX; *)
val result = translate tabulate_def;


(*--------------------------------------------------------------------------------*)


val toList_aux_def = tDefine "toList_aux"`
  toList_aux vec n =  
  if length(vec) <= n
    then [] 
  else sub vec n::toList_aux vec (n + 1)`
(wf_rel_tac `measure (\(vec, n). length(vec) - n)`)

val toList_aux_ind = theorem"toList_aux_ind";

val toList_def = Define`toList vec = toList_aux vec 0`;

val result = translate toList_aux_def;

val toList_aux_side_def = theorem"tolist_aux_side_def"

val toList_aux_side_thm = Q.prove(`∀vec n. tolist_aux_side vec n`,
  ho_match_mp_tac toList_aux_ind
  \\ metis_tac[GREATER_EQ,NOT_LESS_EQUAL,toList_aux_side_def])
  |> update_precondition

val result = translate toList_def; 

val toList_aux_thm = Q.prove (
  `!vec n. toList_aux vec n = case vec of Vector vs => DROP n vs`,
  ho_match_mp_tac toList_aux_ind \\
  rw [] \\
  ONCE_REWRITE_TAC [toList_aux_def] \\
  IF_CASES_TAC THEN1
    (Cases_on `vec` \\
    fs [length_def, DROP_NIL]) \\
  fs [] \\
  Cases_on `vec` \\ 
  fs [sub_def, length_def, DROP_EL_CONS] 
);

val toList_thm = Q.store_thm (
  "toList_thm",
  `!ls. toList (Vector ls) = ls`,
  rw [toList_def, toList_aux_thm]  
)


(*--------------------------------------------------------------------------------*)


val update_def = Define`
  update vec i x = Vector (LUPDATE x i (toList(vec)))`;
val result = translate LUPDATE_def;
val result = translate update_def;

val update_thm = Q.store_thm (
  "update_thm",
  `!vec i x. sub (update vec i x) i = if i < length vec then x 
    else sub vec i`,
  Cases \\
  rw [update_def, toList_thm, EL_LUPDATE, length_def, sub_def]
); 


(* Definition of update which would be more efficient if tabulate was efficient
val update_aux_def = Define`
  update_aux vec i x n = 
    if n = i then x 
    else sub vec n`;

val update_def = Define`
  update vec i x = tabulate (length vec) (update_aux vec i x)`;

val result = translate update_aux_def;
val update_aux_side_def = definition"update_aux_side_def"
val result = translate update_def; 


val update_side_def = definition"update_side_def"
val update_aux_side_thm = Q.prove(`∀vec n i x. update_aux_side vec n i x`,
  \\ metis_tac[update_aux_side_def]
  |> update_precondition
*)


(*--------------------------------------------------------------------------------*)


(*
val concat_aux_def = tDefine "concat_aux"`
  concat_aux l = 
  if LENGTH l <= n
    then []
  else toList (EL n l)::concat_aux l (n + 1)`
(wf_rel_tac `measure (\(l, n). LENGTH l - n)`)
  

val concat_def = Define`
  concat l = Vector (FLAT (concat_aux l 0))`;
*)

(*TODO prove concat works *)
val concat_def = Define`
  concat l = Vector (FLAT (MAP toList l))`;

(* 
val result = translate APPEND;
val next_ml_names = ["concat"];
val result = translate FLAT; 
val result = translate MAP;
*)
val result = translate concat_def;


(*--------------------------------------------------------------------------------*)


(*TODO deal with app/appi *)
(*  
  val app_aux_def = tDefine "app_aux"`
  app_aux f vec n = if length vec <= n then ()
      else app_aux f (update vec n (f (sub vec n))) (n + 1)`
  (
    wf_rel_tac `measure (\(f, vec, n). length(vec) - n)` \\
    Cases_on `vec` \\
    rw [length_def, update_def, sub_def, toList_thm]
  )

  val app_def = Define`
    app f vec = app_aux f vec 0`; 



  val appi_aux_def = xDefine "app_aux"`
    appi_aux f vec n = if length vec <= n then vec
      else appi_aux f (update vec n (f n (sub vec n))) (n + 1)`
  (
    wf_rel_tac `measure (\(f, vec, n). length(vec) - n)` \\
    Cases_on `vec` \\
    rw [length_def, update_def, sub_def, toList_thm]
  )

  val appi_def = Define`
    appi f vec = appi_aux f vec 0`;

*)


(*--------------------------------------------------------------------------------*)


val map_def = Define`
  map vec f = tabulate (length vec) (\n. f (sub vec n))`; 

val mapi_def = Define`
  mapi vec f = tabulate (length vec) (\n. f n (sub vec n))`; 

val map_proof_def = Define`
  map_proof vec f = fromList (MAP f (toList vec))`;

(*TODO find a way to implement mapi using the list MAP function *)

show_assums := true;

(* map is already defined in the translator for strings check if this still works *)
(*TODO fix map side condition if need be*)
val result = translate map_def;
val map_1_side_def = definition"map_1_side_def";
val result = translate mapi_def;


(*--------------------------------------------------------------------------------*)

val _ = ml_prog_update (close_module NONE);

(*################################################################################*)
(*end new stuff*)

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

val ref_spec = Q.store_thm ("ref_spec",
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" (basis_st())) [xv]
          emp (POSTv rv. rv ~~> xv)`,
  prove_ref_spec "op ref");

val deref_spec = Q.store_thm ("deref_spec",
  `!xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" (basis_st())) [rv]
          (rv ~~> xv) (POSTv yv. cond (xv = yv) * rv ~~> xv)`,
  prove_ref_spec "op !");

val assign_spec = Q.store_thm ("assign_spec",
  `!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" (basis_st())) [rv; yv]
       (rv ~~> xv) (POSTv v. cond (UNIT_TYPE () v) * rv ~~> yv)`,
  prove_ref_spec "op :=");


(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`
val _ = trans "andb" `word_and:word8->word8->word8`;

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

val w8array_alloc_spec = Q.store_thm ("w8array_alloc_spec",
  `!n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" (basis_st())) [nv; wv]
       emp (POSTv v. W8ARRAY v (REPLICATE n w))`,
  prove_array_spec "Word8Array.array");

val w8array_sub_spec = Q.store_thm ("w8array_sub_spec",
  `!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" (basis_st())) [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)`,
  prove_array_spec "Word8Array.sub");

val w8array_length_spec = Q.store_thm ("w8array_length_spec",
  `!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" (basis_st())) [av]
       (W8ARRAY av a) (POSTv v. cond (NUM (LENGTH a) v) * W8ARRAY av a)`,
  prove_array_spec "Word8Array.length");

val w8array_update_spec = Q.store_thm ("w8array_update_spec",
  `!a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" (basis_st()))
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))`,
  prove_array_spec "Word8Array.update");

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

val array_alloc_spec = Q.store_thm ("array_alloc_spec",
  `!n nv v.
     NUM n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.array" (basis_st())) [nv; v]
       emp (POSTv av. ARRAY av (REPLICATE n v))`,
  prove_array_spec "Array.array");

val array_sub_spec = Q.store_thm ("array_sub_spec",
  `!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.sub" (basis_st())) [av; nv]
       (ARRAY av a) (POSTv v. cond (v = EL n a) * ARRAY av a)`,
  prove_array_spec "Array.sub");

val array_length_spec = Q.store_thm ("array_length_spec",
  `!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Array.length" (basis_st())) [av]
       (ARRAY av a)
       (POSTv v. cond (NUM (LENGTH a) v) * ARRAY av a)`,
  prove_array_spec "Array.length");

val array_update_spec = Q.store_thm ("array_update_spec",
  `!a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.update" (basis_st()))
       [av; nv; v]
       (ARRAY av a)
       (POSTv uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))`,
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

val print_spec = Q.store_thm ("print_spec",
  `!a av n nv v.
     CHAR c cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.print" (basis_st()))
       [cv]
       (CHAR_IO * STDOUT output)
       (POSTv uv. cond (UNIT_TYPE () uv) * CHAR_IO * STDOUT (output ++ [c]))`,
  xcf "CharIO.print" (basis_st())
  \\ fs [CHAR_IO_def] \\ xpull
  \\ xlet `POSTv xv. W8ARRAY print_loc [w] * STDOUT output * & (NUM (ORD c) xv)`
  THEN1 (xapp \\ xsimpl \\ metis_tac [])
  \\ xlet `POSTv wv. W8ARRAY print_loc [w] * STDOUT output *
                     & (WORD (n2w (ORD c):word8) wv)`
  THEN1 (xapp \\ xsimpl \\ metis_tac [])
  \\ xlet `POSTv zv. STDOUT output * W8ARRAY print_loc [n2w (ORD c)] * & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [CHAR_IO_def,EVAL ``print_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC \\ fs [])
  \\ xlet `POSTv _. STDOUT (output ++ [c]) * W8ARRAY print_loc [n2w (ORD c)]`
  THEN1
   (xffi
    \\ fs [EVAL ``print_loc``, STDOUT_def]
    \\ `MEM 0 [0n]` by EVAL_TAC \\ instantiate \\ xsimpl
    \\ EVAL_TAC \\ fs [ORD_BOUND, CHR_ORD])
  \\ xret \\ xsimpl);

(* definition of basis program *)

val basis_st = get_ml_prog_state ();

val basis_prog_state = save_thm("basis_prog_state",
  ml_progLib.pack_ml_prog_state basis_st);

val basis_prog = basis_st |> remove_snocs
  |> get_thm |> concl |> rator |> rator |> rator |> rand

val basis_def = Define `basis = ^basis_prog`;

val _ = export_theory ()
