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

(*new stuff*)
(*################################################################################*)

(* Option module -- Translated *)

val _ = ml_prog_update (open_module "Option");

val _ = append_dec ``Dtabbrev ["'a"] "option" (Tapp [Tvar "'a"] (TC_name (Short "option")))``;

val result = translate IS_SOME_DEF;

val getOpt_def = Define`
  getOpt opt a = case opt of
    (SOME v) => v
    | NONE => a`;

val result = translate getOpt_def;

val result = translate IS_SOME_DEF;  


(*precondition/option exception if it is not in the form (SOME x) *)
val result = next_ml_names := ["valOf_def"];
val result = translate THE_DEF;

val filter_def  = Define`
  filter f a = if f a then SOME(a) else NONE`;
val result = translate filter_def;

val result = next_ml_names := ["join_def"];
val result = translate OPTION_JOIN_DEF; 

(*app still missing *)

val result = next_ml_names := ["map_def"];
val result = translate OPTION_MAP_DEF;

val mapPartial_def = Define`
  mapPartial f opt = OPTION_BIND opt f`;
val result = translate (OPTION_BIND_def |> REWRITE_RULE[GSYM mapPartial_def]);

(*val compose_def = Define`
  compose f g a = ((OPTION_MAP f) o g) a`;
val result = translate (OPTION_MAP_DEF |> REWRITE_RULE[GSYM compose_def]);
*)

val compose_def = Define`
  compose f g a = case g a of 
    (SOME v) => SOME(f v)
    | NONE => NONE`;
val result = translate compose_def;

val composePartial_def = Define`
  composePartial f g a = case g a of
    (SOME v) => f v
    | NONE => NONE`;
val result = translate composePartial_def;

val _ = ml_prog_update (close_module NONE);

(*################################################################################*)
(*End new stuff *)

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
(*This has a precondition, list empty exception*)
val result = translate HD;

(*--------------------------------------------------------------------------------*)

(*This has a precondition, list empty exception*)
val result = translate TL;

(*--------------------------------------------------------------------------------*)

(*Pre-conditions needs to raise an exception with the list is empty *)

val result = translate LAST_DEF;
val last_side_def = theorem"last_side_def"


(*--------------------------------------------------------------------------------*)

val getItem_def = Define`
  getItem l = case l of
    [] => NONE
    | (h::t) => SOME(h, t)`; 

val result = translate getItem_def;

(*--------------------------------------------------------------------------------*)

val nth_def = Define`
  nth l i = EL i l`;
val result = translate (EL |> REWRITE_RULE[GSYM nth_def]);
(*EL has a precondition because TL and HD have preconditions, subscript exception *)

(*--------------------------------------------------------------------------------*)

(*subscript exception *)
val take_def = Define`
  take l i = TAKE i l`;
val result = translate (TAKE_def |> REWRITE_RULE[GSYM take_def]);

(*--------------------------------------------------------------------------------*)

val drop_def = Define`
  drop l i = DROP i l`;
val result = translate (DROP_def |> REWRITE_RULE[GSYM drop_def]);

(*--------------------------------------------------------------------------------*)

val result = next_ml_names := ["rev_def"];
val result = translate REVERSE_DEF;

(*--------------------------------------------------------------------------------*)

val result = next_ml_names := ["concat_def"];
val result = translate FLAT;

(*--------------------------------------------------------------------------------*)

val result = translate REV_DEF;

(*--------------------------------------------------------------------------------*)

(*List.app needs to be decided upon *)

(*--------------------------------------------------------------------------------*)

val result = translate MAP;

(*--------------------------------------------------------------------------------*)

val mapPartial_def = Define`
  mapPartial f l = case l of
    [] => []
    | (h::t) => case (f h) of     
      NONE => mapPartial f t
      | (SOME x) => x::(mapPartial f t)`;

val result = translate mapPartial_def;   

val mapPartial_thm = Q.store_thm (
  "mapPartial_thm",
  `!f l. mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  Induct_on `l` THEN1
  rw [mapPartial_def] \\
  rw [mapPartial_def] \\
  Cases_on `f h` THEN1
    fs [IS_SOME_DEF]\\
    rw [THE_DEF] \\
  Cases_on `f h` THEN1
    rw [] \\
    fs [IS_SOME_DEF]
)



(*--------------------------------------------------------------------------------*)


(*note that I didn't just translate find because it uses a method which stores indexes
 and values and then has to peel the value from a pair *)
val find_def = Define`
  find f l = case l of
    [] => NONE
    | (h::t) => if f h then SOME(h)
      else find f t`;
val result = translate find_def;


val index_find_thm = Q.prove (
  `!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)`,
  Induct_on `l` THEN1
  rw [INDEX_FIND_def] \\
  Cases_on `f h` \\
  EVAL_TAC \\
  rw [] \\
  EVAL_TAC \\
  rw [] 
);


"find_thm",
  `!f l. find f l = FIND f l`,
  Induct_on `l` \\
  rw [find_def, FIND_def, INDEX_FIND_def] \\
  rw [find_def, FIND_def] \\
  rw [INDEX_FIND_def] \\
  EVAL_TAC \\
  rw [index_find_thm]
)





(*--------------------------------------------------------------------------------*)

val result = translate FILTER;

(*--------------------------------------------------------------------------------*)

(*check if pos and neg should be curried *)
val partition_aux_def = Define`
  partition_aux f l (pos, neg) = case l of
    [] => (REVERSE pos, REVERSE neg)
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

(* raise exception for n < 0 *)
val tabulate_def = Define`
  tabulate n f = GENLIST f n`;
val result = translate SNOC;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
val result = translate (GENLIST |> REWRITE_RULE[GSYM tabulate_def]);

(*--------------------------------------------------------------------------------*)

(*This function has been curried to be different to SML *)
val collate_def = Define`
  collate f l1 l2 = case l1 of
    [] => (case l2 of
      [] => EQUAL
      | (h2::t2) => GREATER)
    | (h1::t1) => (case l2 of
      [] => LESS
      | (h2::t2) => if f h1 h2 = EQUAL then collate f t1 t2
        else f h1 h2)`;
val result = translate collate_def;


(*--------------------------------------------------------------------------------*)
val zip_def = Define`
  zip l1 l2 = 
    case l1 of
      (h1::t1) => (case l2 of
        [] => []
        | (h2::t2) => (h1, h2)::(zip t1 t2))
      | [] => []`; 

val result = translate zip_def;

(*--------------------------------------------------------------------------------*)

val butLast_def = Define`
  butLast  l = case l of
      [] => [] (*this is to stop exceptions*)
      | (h::t) => 
        if t = [] 
          then []
        else h::(butLast t)`;

val result = translate butLast_def;

(*--------------------------------------------------------------------------------*)

(*Haskell Functions*)
val scanl_def = Define`
  scanl f q l = q::(case l of
      [] => []
      | (h::t) => scanl f (f q h) t)`;

val result = translate scanl_def;

(*--------------------------------------------------------------------------------*)

(*this is a reasonably poor implementation *)
val scanr_def = Define`
  scanr_def f q l = REVERSE (scanl f q (REVERSE l))`;

val result = translate scanr_def;
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

val concat_def = Define`
  concat l = Vector (FLAT (MAP toList l))`;

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

val map_thm = Q.store_thm (
  "map_thm",
  `!vec f. map vec f = fromList (MAP f (toList vec))`,
  Cases \\
  rw [map_def, toList_thm, length_def, sub_def, tabulate_def, fromList_def, 
    GENLIST_EL_MAP]
);  

show_assums := true;

val result = translate map_def;
val map_1_side_def = definition"map_1_side_def";
val result = translate mapi_def;

(*--------------------------------------------------------------------------------*)

val foldli_aux_def = tDefine "foldli_aux"`
  foldli_aux f e vec (max: num) n = 
    if max <= n 
      then e
    else foldli_aux f (f n e (sub vec n)) vec max (n + 1)`
(wf_rel_tac `measure (\(f, e, vec, max, n). max - n)`);

val foldli_def = Define`
  foldli f e vec = foldli_aux f e vec (length vec) 0`; 

val result = translate foldli_aux_def;
val result = translate foldli_def;


val foldl_aux_def = tDefine "foldl_aux"`
  foldl_aux f e vec (max: num) n = 
    if max <= n
      then e
    else foldl_aux f (f e (sub vec n)) vec max (n + 1)`
(wf_rel_tac `measure (\(f, e, vec, max, n). max - n)`);

val foldl_def = Define`
  foldl f e vec = foldl_aux f e vec (length vec) 0`;

val result = translate foldl_aux_def;
val result = translate foldl_def;


val foldl_thm = Q.store_thm (
  "foldl_thm",
  `!f e vec. foldl f e vec = fromList (FOLDL f e (toList vec))`,
  Cases \\
  rw [map_def, toList_thm, length_def, sub_def, tabulate_def, fromList_def, 
    GENLIST_EL_MAP]
); 
 
`!f e vec. foldl f e vec = FOLDL f e (toList vec)`
Cases \\
rw [toList_def, toList_aux_thm]
Cases




(*--------------------------------------------------------------------------------*)

val foldri_aux_def = tDefine "foldri_aux"`
  foldri_aux f e vec (n: num) = 
    if n = 0 
      then f e 0
    else foldri_aux f (f n e (sub vec n)) vec (n - 1)`
(wf_rel_tac `measure (\(f, e, vec, n). n)`);

val foldri_def = Define`
  foldri f e vec = foldri_aux f e vec ((length vec) - 1)`; 

val result = translate foldri_aux_def;
val result = translate foldri_def;


val foldr_aux_def = tDefine "foldr_aux"`
  foldr_aux f e vec (n: num) = 
    if n = 0
      then e
    else foldr_aux f (f e (sub vec n)) vec (n - 1)`
(wf_rel_tac `measure (\(f, e, vec, n). n)`);

val foldr_def = Define`
  foldl f e vec = foldr_aux f e vec ((length vec) - 1)`;

val result = translate foldr_aux_def;
val result = translate foldr_def;


(*--------------------------------------------------------------------------------*)

val findi_aux_def = tDefine "findi_aux"`
  findi_aux f vec max n =
    if max <= n 
      then NONE
    else if f n (sub vec n)
      then SOME(sub vec n)
    else findi_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val findi_def = Define `
  findi f vec = findi_aux f vec (length vec) 0`;

val result = translate findi_aux_def;
val result = translate findi_def;


val find_aux_def = tDefine "find_aux"`
  find_aux f vec max n =
    if max <= n 
      then NONE
    else if f (sub vec n)
      then SOME(sub vec n)
    else find_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val find_def = Define `
  find f vec = find_aux f vec (length vec) 0`;

val result = translate find_aux_def;
val result = translate find_def;


(*--------------------------------------------------------------------------------*)

val exists_aux_def = tDefine "exists_aux"`
  exists_aux f vec max n =
    if max <= n
      then F
    else if f (sub vec n)
      then T
    else exists_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val exists_def = Define`
  exists f vec = exists_aux f vec (length vec) 0`;

val result = translate exists_aux_def;
val result = translate exists_def;

(*--------------------------------------------------------------------------------*)

val all_aux_def = tDefine "all_aux"`
  all_aux f vec max n =
    if max <= n
      then T
    else if f (sub vec n)
      then all_aux f vec max (n + 1)
    else F`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val all_def = Define`
  all f vec = all_aux f vec (length vec) 0`;

val result = translate all_aux_def;
val result = translate all_def;


(*--------------------------------------------------------------------------------*)

val collate_aux_def = tDefine "collate_aux"`
  collate_aux f vec1 vec2 max ord n =
    if max <= n
      then ord
    else if f (sub vec1 n) (sub vec2 n) = EQUAL
      then collate_aux f vec1 vec2 max ord (n + 1)
    else
      f (sub vec1 n) (sub vec2 n)`
(wf_rel_tac `measure (\(f, vec1, vec2, max, ord, n). max - n)`);

val collate_def = Define`
  collate f vec1 vec2 =
  if (length vec1) < (length vec2)
    then collate_aux f vec1 vec2 (length vec1) GREATER 0
  else if (length vec2) < (length vec1)
    then collate_aux f vec1 vec2 (length vec2) LESS 0
  else collate_aux f vec1 vec2 (length vec2) EQUAL 0`;

val result = translate collate_aux_def;
val result = translate collate_def;


val _ = ml_prog_update (close_module NONE);

(*################################################################################*)
(*end new stuff*)




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


(*################################################################################*)
(* String module -- translated *)

val _ = ml_prog_update (open_module "String");

val _ = append_dec ``Dtabbrev [] "string" (Tapp [] TC_string)``;
val _ = trans "explode" `explode`
val _ = trans "implode" `implode`
val _ = trans "size" `strlen`

(*new stuff*)
(*--------------------------------------------------------------------------------*)
val sub_def = Define`
  sub s n =  EL n (explode s)`;

(*EL is not translated in list - its translation is moved to nth *)
val result = translate EL;
val result = translate sub_def;

(*--------------------------------------------------------------------------------*)

val extract_aux_def = tDefine "extract_aux"`
    extract_aux s n max =
    if max <= n
      then []
    else (sub s n)::(extract_aux s (n + 1) max)`
(wf_rel_tac `measure (\(s, n, max). max - n)`)

(*should raise subscript exceptions, THE means there is an option dependency*)
val extract_def = Define`
  extract s i opt = case opt of
    (SOME x) => implode (extract_aux s i (THE opt))
    | NONE => implode (extract_aux s i (strlen s))`;

val substring_def = Define`
  substring s i j = implode (extract_aux s i j)`;

(*extract_aux has a pre-condition because sub has a precondition *)
val result = translate extract_aux_def;
val result = translate extract_def;
val result = translate substring_def;

(*--------------------------------------------------------------------------------*)


val strcat_def = Define`
  strcat s1 s2 = implode((explode s1) ++ (explode s2))`
(*This infix code is from the previous stringml stuff *)
val _ = Parse.add_infix("^",480,Parse.LEFT)
val _ = Parse.overload_on("^",``λx y. strcat x y``)


val result = translate strcat_def;

(*--------------------------------------------------------------------------------*)

(*at the moment the only way of putting strings together is turning them to lists *)
val stringListToChars_def = Define`
  stringListToChars l = case l of 
    [] => []
    | ([]::t) => stringListToChars t
    | ((hh::ht)::t) => hh::stringListToChars(ht::t)`;

fun stringListToChars l = case l of
    [] => []
    | ([]::t) => stringListToChars t
    | ((hh::ht)::t) => hh::stringListToChars(ht::t);


(*a more memory efficient implementation *)
val concat_def = Define`
  concat l = implode (stringListToChars l)` ;
(*
val concat_def = Define`
  concat l = implode (FLAT (MAP explode l))`;
*)
val result = translate stringListToChars_def;
val result = translate concat_def;
 
(*--------------------------------------------------------------------------------*)

(*NEED TO PROVE TERMINATION*)
(*may be a bit complex to attempt to save memory (passing around a lot)*)
val concatWith_aux_def = Define`
  concatWith_aux l s ss bool =  
  if bool then
    case l of
      [] => []
      | []::[] => []
      | ([]::t) => concatWith_aux t s s F
      | ((hh::ht)::t) => hh::(concatWith_aux (ht::t) s ss T)
  else 
    case ss of
      [] => concatWith_aux l s ss T
      | (h::t) => h::(concatWith_aux l s t F) `;
(wf_rel_tac `measure (\(l, s, ss, bool). (LENGTH l) + (LENGTH ss) + (LENGTH (EL 0 l))`)


fun concatWith_aux l s ss bool =  
  if bool then
    case l of
         [] => []
      |  []::[] => []
      | ([]::t) => concatWith_aux t s ss false
      | ((hh::ht)::t) => hh::(concatWith_aux (ht::t) s ss true)
  else 
    case ss of
      [] => concatWith_aux l s s true
      | (h::t) => h::(concatWith_aux l s t false);

val concatWith_def = Define`
    concatWith s l = implode (concatWith_aux l s s T)`; 


(*--------------------------------------------------------------------------------*)

val str_def = Define`
  str (c: char) = [c]`; 

translate str_def;

(*--------------------------------------------------------------------------------*)

(*not transferred accross because explode is currently a primitive *)
val explode_aux_def = tDefine "explode_aux"`
  explode_aux s max n = 
    if max <= n then []
    else (sub s n)::(explode_aux s max (n + 1))`
(wf_rel_tac `measure (\(s, max, n). max - n)`);

val explode_def = Define`
  explode s = explode_aux s (strlen s) 0`;

translate explode_aux_def;
translate explode_def;


(*--------------------------------------------------------------------------------*)

(*NOTE: MAP for strings is like APP for other types *)
  
val translate_aux_def = tDefine "translate_aux"`
  translate_aux f s max n = 
    if max <= n then []
    else f (sub s n)::(translate_aux f s max (n + 1))`
(wf_rel_tac `measure (\(f, s, max, n). max - n)`);


val translate_def = Define`
  translate f s = implode (translate_aux f s (strlen s) 0)`;

(*these have pre-conditions because sub has a precondition *)
val result = translate translate_aux_def;
val result = translate translate_def;

(*--------------------------------------------------------------------------------*)


(*Check the functionality *)
val tokens_aux_def = tDefine "tokens_aux"`
  tokens_aux f s ss max n = 
  if max <= n 
    then []
  else if (f (sub s n) /\ ~(ss = []))
    then ss::(tokens_aux f s [] max (n + 1))
  else if f (sub s n) 
    then tokens_aux f s ss max (n + 1)
  else tokens_aux f s ((sub s n)::ss) max (n + 1)`
(wf_rel_tac `measure (\(f, s, ss, max, n). max - n)`);

val tokens_def = Define `
  tokens f s = tokens_aux f s [] (strlen s) 0`;

fun tokens_aux (f : char -> bool) s ss max n = 
  if max <= n 
    then []
  else if (f (String.sub s n)) andalso not(ss = [])
    then ss::(tokens_aux f s [] max (n + 1))
  else if f (String.sub s n) 
    then tokens_aux f s ss max (n + 1)
  else tokens_aux f s ((String.sub s n)::ss) max (n + 1)



(*these have pre-conditions because sub has a precondition *)
val result = translate tokens_aux_def;
val result = translate tokens_def;

(*--------------------------------------------------------------------------------*)

val fields_aux_def = tDefine "fields_aux"`
  fields_aux f s ss max n = 
  if max <= n 
    then []
  else if f (sub s n)
    then ss::(fields_aux f s [] max (n + 1))
  else fields_aux f s ((sub s n)::ss) max (n + 1)`
(wf_rel_tac `measure (\(f, s, ss, max, n). max - n)`);

val fields_def = Define`
  fields f s = fields_aux f s [] (strlen s) 0`;

(*these have pre-conditions because sub has a precondition *)
val result = translate fields_aux_def;
val result = translate tokens_def;


(*--------------------------------------------------------------------------------*)

(*this could be one less iteration if the check is for n + 1 *)
val isStringThere_aux_def = tDefine "isPrefix_aux"`
  isStringThere_aux s1 s2 max n = 
  if max <= n 
    then T
  else if (sub s1 n) = (sub s2 n)
    then isStringThere_aux s1 s2 max (n + 1)
  else F`
(wf_rel_tac `measure (\(s1, s2, max, n). max - n)`);

val isPrefix_def = Define`
  isPrefix s1 s2 = isStringThere_aux s1 s2 (strlen s1) 0`;

val isSuffix_def = Define`
  isSuffix s1 s2 = isStringThere_aux s1 s2 (strlen s2) ((strlen s2) - (strlen s1))`;

val isSubstring_aux_def = tDefine "isSubstring_aux"`
  isSubstring_aux s1 s2 len1 max n = 
    if max <= n
      then F
    else if isStringThere_aux s1 s2 (n + len1) n
      then T
    else isSubstring_aux s1 s2 len1 max (n + 1)` 
(wf_rel_tac `measure (\(s1, s2, len1, max, n). max - n)`);

val isSubstring_def = Define`
  isSubstring s1 s2 = isSubstring_aux s1 s2 (strlen s1) ((strlen s2) - (strlen s1)) 0`;

(* what is going on with is string there *) 
val result = translate isStringThere_aux_def;
 
(*--------------------------------------------------------------------------------*)

val compare_aux_def = tDefine "compare_aux"`
  compare_aux (s1 : mlstring) s2 max ord n = 
    if max <= n
      then ord
    else if (sub s1 n) > (sub s2 n) 
      then GREATER
    else if (sub s1 n) < (sub s2 n)
      then LESS
    else compare_aux s1 s2 max ord (n + 1)` 
(wf_rel_tac `measure (\(s1, s2, max, ord, n). max - n)`);

val compare_def = Define`
  compare_def s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 (strlen s1) GREATER 0
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 (strlen s2) LESS 0
  else compare_aux s1 s2 (strlen s2) EQUAL 0`; 

(*Pre conditions from sub *)
val result = translate compare_aux_def;
val result = translate compare_def;

(*--------------------------------------------------------------------------------*)

val collate_aux_def = tDefine "collate_aux"`
  collate_aux f (s1 : mlstring) s2 max ord n = 
    if max <= n 
      then ord
    else if f (sub s1 n) (sub s2 n) = EQUAL
      then collate_aux f s1 s2 max ord (n + 1)
    else
      f (sub s1 n) (sub s2 n)`
(wf_rel_tac `measure (\(f, s1, s2, max, ord, n). max - n)`);

val collate_def = Define`
  collate f s1 s2 = 
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 (strlen s1) GREATER 0
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 (strlen s2) LESS 0
  else collate_aux f s1 s2 (strlen s2) EQUAL 0`;

(*Pre conditions from sub *) 
val result = translate collate_aux_def;
val result = translate collate_def;

(*--------------------------------------------------------------------------------*)



val _ = ml_prog_update (close_module NONE);

(*end new stuff *)

(*################################################################################*)



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
