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

val tl_def = Define`
  (tl [] = []) /\ 
  (tl (h::t) = t)`;

val result = translate tl_def;
val result = next_ml_names := ["tl_hol_def"];
val result = translate TL;

(*--------------------------------------------------------------------------------*)

(*Pre-conditions needs to raise an exception with the list is empty *)

val result = translate LAST_DEF;


(*--------------------------------------------------------------------------------*)

val getItem_def = Define`
  (getItem [] = NONE) /\ 
  (getItem (h::t) = SOME(h, t))`; 

val result = translate getItem_def;

(*--------------------------------------------------------------------------------*)

val nth_def = Define`
  nth l i = EL i l`;
val result = translate (EL |> REWRITE_RULE[GSYM nth_def]);
(*EL has a precondition because TL and HD have preconditions, subscript exception *)

(*--------------------------------------------------------------------------------*)

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


val list_mapi_def = Define `
  (list_mapi f (n: num) [] = []) /\
  (list_mapi f n (h::t) = (f n h)::(list_mapi f (n + 1) t))`


val MAPI_thm_gen = Q.prove (
  `!f l x. MAPi (\a. f (a + x)) l = list_mapi f x l`,
  Induct_on `l` \\ rw [MAPi_def, list_mapi_def] \\
  rw [o_DEF, ADD1] \\
  fs [] \\
  pop_assum (fn th => rw[GSYM th] ) \\
  rw[AC ADD_ASSOC ADD_COMM] \\
  match_mp_tac MAPi_CONG \\ rw[]
);


val MAPI_thm =
  MAPI_thm_gen |> Q.SPECL[`f`,`l`,`0`]
  |> SIMP_RULE (srw_ss()++ETA_ss) [] ;

val result = translate list_mapi_def;
val result = translate MAPI_thm;

(*--------------------------------------------------------------------------------*)

val mapPartial_def = Define`
  (mapPartial f [] = []) /\ 
  (mapPartial f (h::t) = case (f h) of
    NONE => mapPartial f t 
    |(SOME x) => x::mapPartial f t)`;

val result = translate mapPartial_def;   

val mapPartial_thm = Q.store_thm (
  "mapPartial_thm",
  `!f l. mapPartial f l = MAP THE (FILTER IS_SOME (MAP f l))`,
  Induct_on `l` \\ rw [mapPartial_def] \\ Cases_on `f h` \\ rw [THE_DEF] \\ fs [IS_SOME_DEF]
)

(*--------------------------------------------------------------------------------*)

val index_find_thm = Q.prove (
  `!x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)`,
  Induct_on`l` \\ rw[INDEX_FIND_def]
);

val FIND_thm = Q.store_thm(
  "FIND_thm",
  `(FIND f [] = NONE) ∧
   (∀h t. FIND f (h::t) = if f h then SOME h else FIND f t)`,
  rw[FIND_def,INDEX_FIND_def,index_find_thm]
);

val res = translate FIND_thm;

(*--------------------------------------------------------------------------------*)

val result = translate FILTER;

(*--------------------------------------------------------------------------------*)

val partition_aux_def = Define`
  (partition_aux f [] pos neg = 
    (REVERSE pos, REVERSE neg)) /\
    (partition_aux f (h::t) pos neg = if f h then partition_aux f t (h::pos) neg
      else partition_aux f t pos (h::neg))`;

val partition_def = Define`
  partition (f : 'a -> bool) l = partition_aux f l [] []`;

val partition_aux_thm = Q.prove(
  `!f l l1 l2. partition_aux f l l1 l2 = (REVERSE l1++(FILTER f l), REVERSE l2++(FILTER ($~ o f) l))`,
  Induct_on `l` \\
  rw [partition_aux_def] \\
  rw [partition_aux_def]
); 

val partition_pos_thm = Q.store_thm(
  "partition_pos_thm",
  `!f l. FST (partition f l) = FILTER f l`,
  rw [partition_def, FILTER, partition_aux_thm]
);

val partition_neg_thm = Q.store_thm(
  "partition_neg_thm",
  `!f l. SND (partition f l) = FILTER ($~ o f) l`,
  rw [partition_def, FILTER, partition_aux_thm]
);


val result = translate partition_aux_def;
val result = translate partition_def;


(*--------------------------------------------------------------------------------*)

val result = translate FOLDL;

val foldli_aux_def = Define`
  (foldli_aux f e n [] = e) /\
  (foldli_aux f e n (h::t) = foldli_aux f (f n e h) (SUC n) t)`;

val foldli_def = Define`
  foldli f e l = foldli_aux f e 0 l`;

val foldli_aux_thm = Q.prove (
  `!l f e n.  foldli_aux f e n l = FOLDRi (\n' e h. f (LENGTH l + n - (SUC n')) h e) e (REVERSE l)`,
  Induct_on `l` \\
  rw [foldli_aux_def] \\
  rw [FOLDRi_APPEND] \\
  rw [ADD1]
);

val foldli_thm = Q.store_thm (
  "foldli_thm",
  `!f e l. foldli f e l = FOLDRi (\n e h. f (LENGTH l - (SUC n)) h e) e (REVERSE l)`,
  rw [foldli_def, foldli_aux_thm]
);


val result = translate foldli_aux_def;
val result = translate foldli_def;

(*--------------------------------------------------------------------------------*)

val result = translate FOLDR;
val result = translate (FOLDRi_def |> REWRITE_RULE[o_DEF]);


(*--------------------------------------------------------------------------------*)

val result = translate EXISTS_DEF;

(*--------------------------------------------------------------------------------*)

val result = next_ml_names := ["all_def"];
val result = translate EVERY_DEF;

(*--------------------------------------------------------------------------------*)

val tabulate_def = Define`
  tabulate n f = GENLIST f n`;
val result = translate SNOC;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
val result = translate (GENLIST |> REWRITE_RULE[GSYM tabulate_def]);

(*--------------------------------------------------------------------------------*)

val collate_def = Define`
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)`;

val collate_ind = theorem"collate_ind";

val collate_equal_thm = Q.store_thm (
  "collate_equal_thm",
  `!l. (!x. MEM x l ==> f x x = EQUAL) ==> collate f l l = EQUAL`,
  Induct_on `l` \\ rw [collate_def] \\ rw [collate_def]
);

val collate_short_thm = Q.store_thm (
  "collate_short_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l1 ≼ l2) ==>
        collate f l1 l2 = LESS`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);

val collate_long_thm = Q.store_thm (
  "collate_long_thm",
  `!f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l2 ≼ l1) ==>
        collate f l1 l2 = GREATER`,
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
);


val cpn_to_reln_def = Define`
  cpn_to_reln f x1 x2 = (f x1 x2 = LESS)`; 
  

    

(* this statement isn't true - collate f l1 l2 has no bearing on the values of h1 and h2*)
val collate_cpn_reln_thm = Q.store_thm (
  "collate_cpn_reln_thm",
  `!f l1 l2. (!x1 x2. f x1 x2 = EQUAL <=> 
    (x1 = x2)) ==> cpn_to_reln (collate f) l1 l2 = LLEX (cpn_to_reln f) l1 l2`, 
  ho_match_mp_tac collate_ind \\ 
  rw [collate_def, cpn_to_reln_def, LLEX_def] \\
  `EQUAL ≠ LESS` by fs[] \\
  first_assum (qspecl_then [`h1`, `h1`] (fn th => assume_tac (GSYM th))) \\
  `(h1 = h1) = T` by DECIDE_TAC \\
  rw[]
);
 
 
(*--------------------------------------------------------------------------------*)

val zip_def = Define`
  (zip [] [] = []) /\ 
  (zip [] (h::t) = []) /\
  (zip (h::t) [] = []) /\
  (zip (h1::t1) (h2::t2) = (h1, h2)::(zip t1 t2))`; 

val zip_ind = theorem"zip_ind";

val zip_thm = Q.store_thm("zip_thm",
  `!l1 l2. ((LENGTH l1) = (LENGTH l2)) ==> ((zip l1 l2) = (ZIP (l1, l2)))`,
  ho_match_mp_tac zip_ind \\ rw[zip_def,ZIP]);

val result = translate zip_def;


val _ = ml_prog_update (close_module NONE);

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


(*--------------------------------------------------------------------------------*)


val tabulate_def = Define`
  tabulate n f = Vector (GENLIST f n)`;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
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


val update_side_def = definition "update_side_def"
val update_aux_side_thm = Q.prove(`∀vec n i x. update_aux_side vec n i x`,
  \\ metis_tac[update_aux_side_def])
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


(* These functions have preconditions that don't propagate through the translator to be solvable *)
(* can make map more efficient by combining toList and map into one *)

val map_proof_def = Define`
  map_proof vec f = tabulate (length vec) (\n. f (sub vec n))`; 

val mapi_proof_def = Define`
  mapi_proof vec f = tabulate (length vec) (\n. f n (sub vec n))`; 

val map_def = Define`
  map vec f = fromList (MAP f (toList vec))`;

val mapi_def = Define`
  mapi vec f = fromList (MAPi f (toList vec))`;

val result = translate map_def;
val result = translate mapi_def;


(*--------------------------------------------------------------------------------*)


val less_than_length_thm = Q.prove (
  `!xs n. n < LENGTH xs ==> ?ys z zs. xs = ys ++ z::zs /\ LENGTH ys = n`,
  rw[] \\
  qexists_tac`TAKE n xs` \\
  rw[] \\
  qexists_tac`HD (DROP n xs)` \\
  qexists_tac`TL (DROP n xs)` \\
  Cases_on`DROP n xs` \\ fs[]
  >- fs[DROP_NIL] \\
  metis_tac[TAKE_DROP,APPEND_ASSOC,CONS_APPEND]
); 


(*--------------------------------------------------------------------------------*)


(*This needs to be proven once the modules are separated *)
val foldli_aux_def = Define`
  (foldli_aux f e vec n 0 = e) /\
  (foldli_aux f e vec n (SUC len) = foldli_aux f (f n e (sub vec n)) vec (n + 1) len)`;

val foldli_def = Define`
  foldli f e vec = foldli_aux f e vec 0 (length vec)`;


val foldli_aux_def = Define`
  `!f e vec n len. foldli_aux f e vec n len = list$foldli_aux f e vec n len`

val result = translate foldli_aux_def;
val foldli_aux_side_def = theorem"foldli_aux_side_def"
val result = translate foldli_def;
val foldli_side_def = definition"foldli_side_def";

val foldli_aux_side_thm = Q.prove(  
  `!f e vec n len. n + len = length (vec) ==> foldli_aux_side f e vec n len`, 
  Induct_on`len` \\ rw[Once foldli_aux_side_def]
);

val foldli_side_thm = Q.prove(
  `foldli_side f e vec`,
  rw[foldli_side_def,foldli_aux_side_thm]) |> update_precondition;

(*----------------------------------------------------------------------------------*)


val foldl_aux_def = Define`
  (foldl_aux f e vec n 0 = e) /\
  (foldl_aux f e vec n (SUC len) = foldl_aux f (f e (sub vec n)) vec (n + 1) len)`; 

val foldl_def = Define`
  foldl f e vec = foldl_aux f e vec 0 (length vec)`;

val foldl_aux_thm = Q.prove (
  `!f e vec x len. (x + len = length vec) ==>
    foldl_aux f e vec x len = FOLDL f e (DROP x (toList vec))`,
  Induct_on `len` \\ Cases_on `vec` \\
  rw [foldl_aux_def, DROP_LENGTH_TOO_LONG, length_def, toList_thm] \\ 
  rw [length_def, sub_def, toList_thm] \\
  `x < LENGTH l` by decide_tac \\
  drule less_than_length_thm \\
  rw [] \\
  rw [] \\
  `LENGTH ys + 1 = LENGTH (ys ++ [z])` by (fs [] \\ NO_TAC) \\ ASM_REWRITE_TAC [DROP_LENGTH_APPEND]\\
  simp_tac std_ss [GSYM APPEND_ASSOC, APPEND, EL_LENGTH_APPEND, NULL, HD,
        FOLDL,  DROP_LENGTH_APPEND]
);

val foldl_thm = Q.store_thm (
  "foldl_thm",
  `!f e vec. foldl f e vec = FOLDL f e (toList vec)`,
  rw [foldl_aux_thm, foldl_def]
);

val result = translate foldl_aux_def;
val foldl_aux_side_def = theorem"foldl_aux_side_def"
val result = translate foldl_def;
val foldl_side_def = definition"foldl_side_def";

val foldl_aux_side_thm = Q.prove(
  `!f e vec n len. n + len = length vec ==> foldl_aux_side f e vec n len`,
  Induct_on `len` \\ rw [Once foldl_aux_side_def]
);

val foldl_side_thm = Q.prove(
  `!f e vec. foldl_side f e vec`,
  rw [foldl_side_def, foldl_aux_side_thm]) |> update_precondition;

(*----------------------------------------------------------------------------------*)

val foldri_aux_def = Define`
  (foldri_aux f e vec 0 = e) /\
  (foldri_aux f e vec (SUC len) = foldri_aux f (f len (sub vec len) e) vec len)`;

val foldri_def = Define`
  foldri f e vec = foldri_aux f e vec (length vec)`;

val take_el_thm = Q.prove(
  `!n l. n < LENGTH l ==> TAKE 1 (DROP n l) = [EL n l]`,
  Induct_on `l` \\ rw[] \\
  Cases_on `n` \\ rw[EL_restricted]
);

val foldri_aux_thm = Q.prove (
  `!f e vec len. len <= length vec ==>
    foldri_aux f e vec len = FOLDRi f e (TAKE len (toList vec))`,
  Induct_on `len` \\ rw[foldri_aux_def] \\
  Cases_on `vec` \\ fs[length_def, toList_thm, sub_def] \\
  rw [ADD1, TAKE_SUM, take_el_thm, FOLDRi_APPEND] 
);

val foldri_thm = Q.store_thm (
  "foldri_thm",
  `!f e vec. foldri f e vec = FOLDRi f e (toList vec)`, 
  Cases_on `vec` \\
  rw [foldri_aux_thm, foldri_def, toList_thm, length_def]
);

val result = translate foldri_aux_def;
val foldri_aux_side_def = theorem"foldri_aux_side_def";
val result = translate foldri_def;
val foldri_side_def = definition"foldri_side_def";

val foldri_aux_side_thm = Q.prove(
  `!f e vec len. len <= length vec ==> foldri_aux_side f e vec len`,
  Induct_on `len` \\ rw [Once foldri_aux_side_def]
);

val foldri_side_thm = Q.prove(
  `!f e vec. foldri_side f e vec`,
  rw [foldri_side_def, foldri_aux_side_thm] ) |> update_precondition


(*----------------------------------------------------------------------------------*)

val foldr_aux_def = Define`
  (foldr_aux f e vec 0 = e) /\
  (foldr_aux f e vec (SUC len) = foldr_aux f (f (sub vec len) e) vec len)`;

val foldr_def = Define`
  foldr f e vec = foldr_aux f e vec (length vec)`;

val foldr_aux_thm = Q.prove (
  `!f e vec len. len <= length vec ==>
    foldr_aux f e vec len = FOLDR f e (TAKE len (toList vec))`,
  Induct_on `len` \\ rw[foldr_aux_def] \\
  Cases_on `vec` \\ fs[length_def, toList_thm, sub_def] \\
  rw [ADD1, TAKE_SUM, take_el_thm, FOLDR_APPEND]
);

val foldr_thm = Q.store_thm (
  "foldr_thm",
  `!f e vec. foldr f e vec = FOLDR f e (toList vec)`,
  Cases_on `vec` \\
  rw[foldr_def, foldr_aux_thm, length_def, toList_thm]
);

val result = translate foldr_aux_def;
val foldr_aux_side_def = theorem"foldr_aux_side_def";
val result = translate foldr_def;
val foldr_side_def = definition"foldr_side_def";

val foldr_aux_side_thm = Q.prove(
  `!f e vec len. len <= length vec ==> foldr_aux_side f e vec len`,
  Induct_on `len` \\ rw[Once foldr_aux_side_def]
);

val foldr_side_thm = Q.prove(
  `!f e vec. foldr_side f e vec`,
  rw [foldr_side_def, foldr_aux_side_thm] ) |> update_precondition

(*--------------------------------------------------------------------------------*)


(*Think of a good function to mimic findi functionality *)

val findi_aux_def = Define`
  (findi_aux f vec n 0 = NONE) /\
  (findi_aux f vec n (SUC len) = 
  if f n (sub vec n) 
    then SOME(n, (sub vec n))
  else findi_aux f vec (n + 1) len)`;

val findi_def = Define`
  findi f vec = findi_aux f vec 0 (length vec)`;


val findi_aux_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> (?x. ((MEM x (toList vec) ) /\ 
    (f (THE (INDEX_OF x (toList vec))) x ) /\ (SND (THE (findi_aux f vec n len)) = x))) \/ 
    (!y. (MEM y (toList vec)) ==> ~(f (THE (INDEX_OF y (toList vec))) y))`
    Cases_on `vec` \\ rw [toList_thm, length_def, sub_def, findi_aux_def, INDEX_OF_def]
    rw [] 
);

val result = translate findi_aux_def;
val findi_aux_side_def = theorem"findi_aux_side_def"
val result = translate findi_def;
val findi_side_def = definition"findi_side_def"

val findi_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> findi_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once findi_aux_side_def]
);

val findi_side_thm = Q.prove (
  `!f vec. findi_side f vec`,
  rw [findi_side_def, findi_aux_side_thm] ) |> update_precondition

(*--------------------------------------------------------------------------------*)

val find_aux_def = Define`
  (find_aux f vec n 0 = NONE) /\
  (find_aux f vec n (SUC len) = 
  if f (sub vec n) 
    then SOME(sub vec n)
  else find_aux f vec (n + 1) len)`;

val find_def = Define `
  find f vec = find_aux f vec 0 (length vec)`;


val find_aux_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> find_aux f vec n len = FIND f (DROP n (toList vec))`,
  Induct_on `len` \\ Cases_on `vec` \\ rw [find_aux_def, sub_def, length_def, 
  toList_thm, FIND_def, INDEX_FIND_def] \\
  rw[DROP_LENGTH_NIL, INDEX_FIND_def] THEN1
  (qexists_tac`(0, EL n l)` \\ rw [DROP_EL_CONS, INDEX_FIND_def]) \\
  rw [DROP_EL_CONS, INDEX_FIND_def, index_find_thm]
);
 
val find_thm = Q.store_thm (
  "find_thm",
  `!f vec. find f vec = FIND f (toList vec)`,
  rw [find_aux_thm, find_def] 
);

val result = translate find_aux_def;
val find_aux_side_def = theorem"find_aux_side_def"
val result = translate find_def;
val find_side_def = definition"find_side_def"

val find_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> find_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once find_aux_side_def]
);

val find_side_thm = Q.prove (
  `!f vec. find_side f vec`,
  rw [find_side_def, find_aux_side_thm]) |> update_precondition

(*--------------------------------------------------------------------------------*)

val exists_aux_def = Define`
  (exists_aux f vec n 0 = F) /\
  (exists_aux f vec n (SUC len) = 
    if f (sub vec n)
      then T
    else exists_aux f vec (n + 1) len)`;

val exists_def = Define`
  exists f vec = exists_aux f vec 0 (length vec)`;

val exists_aux_thm = Q.prove(
  `!f vec n len. n + len = length (vec) ==> exists_aux f vec n len = EXISTS f (DROP n (toList vec))`,
  Induct_on `len` \\ Cases_on `vec` \\ rw[toList_thm, length_def, sub_def, exists_aux_def] THEN1
  rw [DROP_LENGTH_NIL, EVERY_DEF] \\
  rw [DROP_EL_CONS]
);

val exists_thm = Q.store_thm (
  "exists_thm",
  `!f vec. exists f vec = EXISTS f (toList vec)`,
  Cases_on `vec` \\
  rw [exists_def, exists_aux_thm]
);

val result = translate exists_aux_def;
val exists_aux_side_def = theorem"exists_aux_side_def";
val result = translate exists_def;
val exists_side_def = definition"exists_side_def";

val exists_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> exists_aux_side f vec n len`,
  Induct_on `len` \\ rw [Once exists_aux_side_def]
);

val exists_side_thm = Q.prove (
  `!f vec. exists_side f vec`,
  rw [exists_side_def, exists_aux_side_thm]) |> update_precondition

(*--------------------------------------------------------------------------------*)

val all_aux_def = Define`
  (all_aux f vec n 0 = T) /\
  (all_aux f vec n (SUC len) = 
    if f (sub vec n) 
      then all_aux f vec (n + 1) len
    else F)`;

val all_def = Define`
  all f vec = all_aux f vec 0 (length vec)`;      

val all_aux_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> all_aux f vec n len = EVERY f (DROP n (toList vec))`,
  Induct_on `len` \\ Cases_on `vec` \\ rw[toList_thm, length_def, sub_def, all_aux_def] THEN1
  rw [DROP_LENGTH_NIL] \\
  rw [DROP_EL_CONS] 
);

val all_thm = Q.store_thm (
  "all_thm",
  `!f vec. all f vec = EVERY f (toList vec)`,
  Cases_on `vec` \\ rw[all_def, all_aux_thm]
);

val result = translate all_aux_def;
val all_aux_side_def = theorem"all_aux_side_def";
val result = translate all_def;
val all_side_def = definition"all_side_def";

val all_aux_side_thm = Q.prove (
  `!f vec n len. n + len = length vec ==> all_aux_side f vec n len`,
  Induct_on `len` \\ rw[Once all_aux_side_def]
);

val all_side_thm = Q.prove (
  `!f vec. all_side f vec`,
  rw [all_side_def, all_aux_side_thm]) |> update_precondition

(*--------------------------------------------------------------------------------*)

(*collate needs to be proven in a different file so it can use the list collate *)
val collate_aux_def = Define`
  (collate_aux f vec1 vec2 n ord 0 = ord) /\
  (collate_aux f vec1 vec2 n ord (SUC len) = 
    if f (sub vec1 n) (sub vec2 n) = EQUAL
      then collate_aux f vec1 vec2 (n + 1) ord len
    else f (sub vec1 n) (sub vec2 n))`;

val collate_def = Define`
  collate f vec1 vec2 =
  if (length vec1) < (length vec2)
    then collate_aux f vec1 vec2 0 GREATER (length vec1)
  else if (length vec2) < (length vec1)
    then collate_aux f vec1 vec2 0 LESS (length vec2)
  else collate_aux f vec1 vec2 0 EQUAL (length vec2)`;

val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val result = translate collate_def;
val collate_side_def = definition"collate_side_def";

val collate_aux_side_thm = Q.prove (
  `!f vec1 vec2 n ord len. n + len = 
    (if length vec1 < length vec2 
      then length vec1
    else length vec2) ==>
        collate_aux_side f vec1 vec2 n ord len`,
  Induct_on `len` \\ rw[Once collate_aux_side_def]
);

val collate_side_thm = Q.prove (
  `!f vec1 vec2. collate_side f vec1 vec2`,
  rw[collate_side_def, collate_aux_side_thm] ) |> update_precondition

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

clear_overloads_on"STRING";
clear_overloads_on"STRCAT";
clear_overloads_on"STRLEN";
(*--------------------------------------------------------------------------------*)

val sub_def = Define`
  sub s n =  EL n (explode s)`;
(*EL is not translated in list - its translation is moved to nth *)
val result = translate EL;
val result = translate sub_def;

(*--------------------------------------------------------------------------------*)

val extract_aux_def = Define`
  (extract_aux s n 0 = []) /\
  (extract_aux s n (SUC len) = (sub s n):: extract_aux s (n + 1) len)`;

val extract_def = Define`
  extract s i opt = 
    if strlen s <= i
      then implode []
    else case opt of
      (SOME x) => implode (extract_aux s i (MIN (strlen s - i) x))
      | NONE => implode (extract_aux s i ((strlen s) - i))`;


val substring_def = Define`
  substring s i j = implode (extract_aux s i j)`;

val extract_aux_thm = Q.prove (
  `!s n len. n + len <= strlen s ==> extract_aux s n len = SEG len n (explode s)`,
  Cases_on `s` \\ Induct_on `len` >-
  rw[extract_aux_def, SEG] \\
  fs [extract_aux_def, sub_def, strlen_def, explode_def] \\ 
  rw [EL_SEG, SEG_TAKE_BUTFISTN] \\
  rw [TAKE_SUM, take_el_thm, DROP_DROP, DROP_EL_CONS]
); 

(*This proves that the functions are the same for values where SEG is defined*)
val extract_thm = Q.store_thm (
  "extract_thm",
  `!s i opt. i < strlen s ==> extract s i opt = (case opt of 
    (SOME x) => implode (SEG (MIN (strlen s - i) x) i (explode s))
    | NONE => implode (SEG ((strlen s) - i) i (explode s)))`,
    Cases_on `opt` >- rw [extract_def, extract_aux_thm, implode_def, strlen_def, MIN_DEF] \\
    rw [extract_def] \\ AP_TERM_TAC ORELSE AP_THM_TAC \\ rw[MIN_DEF] \\ rw [extract_aux_thm]
);
    
 
(*extract_aux has a pre-condition because it can call sub on indexes out of the range*)
val result = translate MIN_DEF;
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

(*this is inefficient while strcat is inefficient *)
val concat_def = Define`
  (concat [] = implode []) /\
  (concat (h::t) = strcat h (concat t))`;

val concat_thm = Q.store_thm (
  "concat_thm",
  `!l. concat l = implode (FLAT (MAP explode l))`,
  Induct_on `l` \\ rw [concat_def] \\ Cases_on `h` \\
  rw [strcat_def, implode_def, explode_def]
); 
  
val result = translate concat_def;
 
(*--------------------------------------------------------------------------------*)

(*This is inefficient while strcat is inefficient *)
val concatWith_aux_def = Define`
  (concatWith_aux s [] bool = implode []) /\
  (concatWith_aux s (h::t) T = strcat h (concatWith_aux s t F)) /\
  (concatWith_aux s (h::t) F = strcat s (concatWith_aux s t T))`;

val concatWith_def = Define`
  concatWith s l = concatWith_aux s l T`;
 
val result = translate concatWith_aux_def;

val result = translate concatWith_def;
(*--------------------------------------------------------------------------------*)

val str_def = Define`
  str (c: char) = implode [c]`; 

val result = translate str_def;

(*--------------------------------------------------------------------------------*)

val explode_aux_def = Define`
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n+1) len))`;
val _ = export_rewrites["explode_aux_def"];

val explode_aux_thm = Q.store_thm("explode_aux_thm",
  `∀max n ls.
    n + max = LENGTH ls ⇒
    explode_aux (strlit ls) n max = DROP n ls`,
  Induct \\ rw[] \\ fs[LENGTH_NIL_SYM,DROP_LENGTH_TOO_LONG]
  \\ match_mp_tac (GSYM rich_listTheory.DROP_EL_CONS)
  \\ simp[]);

val explode_def = Define`
  explode s = explode_aux s 0 (strlen s)`;

val explode_thm = Q.store_thm("explode_thm[simp]",
  `explode (strlit ls) = ls`,
  rw[explode_def,SIMP_RULE std_ss [] explode_aux_thm]);

translate explode_aux_def;
translate explode_def;


(*--------------------------------------------------------------------------------*)

val translate_aux_def = Define`
  (translate_aux f s n 0 = []) /\
  (translate_aux f s n (SUC len) = f (sub s n)::translate_aux f s (n + 1) len)`;

val translate_def = Define`
  translate f s = implode (translate_aux f s 0 (strlen s))`;

val translate_aux_thm = Q.prove (
  `!f s n len. n + len = strlen s ==> translate_aux f s n len = MAP f (DROP n (explode s))`,
  Cases_on `s` \\ Induct_on `len` \\ rw [translate_aux_def, strlen_def, explode_def] >-
  rw [DROP_LENGTH_NIL] \\
  rw [sub_def, DROP_EL_CONS]
);

val translate_thm = Q.store_thm (
  "translate_thm",
  `!f s. translate f s = implode (MAP f (explode s))`,
  rw [translate_def, translate_aux_thm]
);

(*these have pre-conditions because sub has a precondition *)
val result = translate translate_aux_def;
val translate_aux_side_def = theorem"translate_aux_side_def";
val result = translate translate_def;
val translate_side_def = definition"translate_side_def";

val translate_aux_side_thm = Q.prove (
  `!f s n len. n + len = strlen s ==> translate_aux_side f s n len`,
  Induct_on `len` \\ rw[Once translate_aux_side_def]
);

val translate_side_thm = Q.prove (
  `!f s. translate_side f s`,
  rw [translate_side_def, translate_aux_side_thm] ) |> update_precondition  

(*--------------------------------------------------------------------------------*)

val tokens_aux_def = Define`
  (tokens_aux f s ss n 0 = []) /\
  (tokens_aux f s [] n (SUC len) = 
    if f (sub s n) 
      then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [sub s n] (n + 1) len) /\
  (tokens_aux f s (h::t) n (SUC len) = 
    if f (sub s n)
      then (implode (h::t))::(tokens_aux f s [] (n + 1) len)
    else tokens_aux f s (sub s n::(h::t)) (n + 1) len)`;

val tokens_def = Define `
  tokens f s = tokens_aux f s [] 0 (strlen s)`;

(*Number of tokens, members of the flat of the tokens list *)

val result = translate tokens_aux_def;
val tokens_aux_side_def = theorem"tokens_aux_side_def";
val result = translate tokens_def;
val tokens_side_def = definition"tokens_side_def";

val tokens_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> tokens_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once tokens_aux_side_def]
);

val tokens_side_thm = Q.prove (
  `!f s. tokens_side f s`,
  rw [tokens_side_def, tokens_aux_side_thm] ) |> update_precondition

(*--------------------------------------------------------------------------------*)

val fields_aux_def = Define`
  (fields_aux f s ss n 0 = []) /\
  (fields_aux f s ss n (SUC len) = 
    if f (sub s n)
      then implode ss::(fields_aux f s [] (n + 1) len)
    else fields_aux f s (sub s n::ss) (n + 1) len)`;

val fields_def = Define`
  fields f s = fields_aux f s [] 0 (strlen s)`;

val fields_aux_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==>
    ?c. f c ==> (concatWith (str c) (fields_aux f s ss n len) = implode (DROP n (explode s)))`
  Induct_on `len` \\  Cases_on `s`
  rw [fields_aux_def, concatWith_def, concatWith_aux_def, strlen_def, DROP_LENGTH_NIL]
  

val fields_thm = Q.store_thm (
  "fields_thm",
  `!f s. ?c. (f c) /\ concatWith (str c) (fields f s) = s`
  rw [concatWith_def, fields_def] 

val result = translate fields_aux_def;
val fields_aux_side_def = theorem"fields_aux_side_def";
val result = translate fields_def;
val fields_side_def = definition"fields_side_def";

val fields_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> fields_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once fields_aux_side_def]
);

val fields_side_thm = Q.prove (
  `!f s. fields_side f s`,
  rw [fields_side_def, fields_aux_side_thm] ) |> update_precondition

(*--------------------------------------------------------------------------------*)

val isStringThere_aux_def = Define`
  (isStringThere_aux s1 s2 n 0 = T) /\
  (isStringThere_aux s1 s2 n (SUC len) = 
    if sub s1 n = sub s2 n
      then isStringThere_aux s1 s2 (n + 1) len
    else F)`;

val isPrefix_def = Define`
  isPrefix s1 s2 = 
    if strlen s1 <= strlen s2 
      then isStringThere_aux s1 s2 (strlen s1) 0
    else F`;

val isSuffix_def = Define`
  isSuffix s1 s2 = 
    if strlen s1 <= strlen s2
      then isStringThere_aux s1 s2 (strlen s2 - strlen s1) (strlen s1)
    else F`;

val isSubstring_aux_def = Define`
  (isSubstring_aux s1 s2 lens1 n 0 = F) /\
  (isSubstring_aux s1 s2 lens1 n (SUC len) =
    if (isStringThere_aux s1 s2 n lens1) 
      then T
    else isSubstring_aux s1 s2 lens1 (n + 1) len)`;

val isSubstring_def = Define`
  isSubstring s1 s2 = 
  if strlen s1 <= strlen s2
    then isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2) - (strlen s1))
  else F`;

val result = translate isStringThere_aux_def;
val isStringThere_aux_side_def = theorem"isstringthere_aux_side_def";

val isStringThere_aux_side_thm = Q.prove (
  `!s1 s2 n len. n + len <= strlen s2 ==> isstringthere_aux_side s1 s2 n len`,
  Induct_on `len` \\ rw [Once isStringThere_aux_side_def]
);

val result = translate isPrefix_def;
val isPrefix_side_def = definition"isprefix_side_def";
val isPrefix_thm = Q.prove (
  `!s1 s2. isprefix_side s1 s2`,
  rw[isPrefix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val result = translate isSuffix_def;
val isSuffix_side_def = definition"issuffix_side_def";
val isSuffix_thm = Q.prove (
  `!s1 s2. issuffix_side s1 s2`,
  rw[isSuffix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val result = translate isSubstring_aux_def;
val isSubstring_aux_side_def = theorem"issubstring_aux_side_def";
val isSubstring_aux_side_thm = Q.prove (
  `!s1 s2 lens1 n len. (n + len = strlen s2 - strlen s1) /\ (lens1 = strlen s1) ==> 
    issubstring_aux_side s1 s2 lens1 n len`,
  Induct_on `len` \\ rw [Once isSubstring_aux_side_def, isStringThere_aux_side_thm]
);
val result = translate isSubstring_def;
val isSubstring_side_def = definition"issubstring_side_def";
val isSubstring_side_thm = Q.prove (
  `!s1 s2. issubstring_side s1 s2`,
  rw [isSubstring_side_def, isSubstring_aux_side_thm] ) |> update_precondition

(*--------------------------------------------------------------------------------*)

val compare_aux_def = Define`
  (compare_aux (s1: mlstring) s2 ord n 0 = ord) /\
  (compare_aux s1 s2 ord n (SUC len) = 
    if sub s2 n < sub s1 n
      then GREATER
    else if sub s1 n < sub s2 n
      then LESS
    else compare_aux s1 s2 ord (n + 1) len)`;

val compare_def = Define`
  compare_def s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)`; 

(*Pre conditions from sub *)
val result = translate compare_aux_def;
val compare_aux_side_def = theorem"compare_aux_side_def";
val result = translate compare_def;
val compare_side_def = definition"compare_side_def";

val compare_aux_side_thm = Q.prove (
  `!s1 s2 ord n len. (n + len = 
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len`,
  cheat );
  Induct_on `len` \\ rw [Once compare_aux_side_def]
);

val compare_side_thm = Q.prove (
  `!s1 s2. compare_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition
(*--------------------------------------------------------------------------------*)

val collate_aux_def = Define`
  (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
  (collate_aux f s1 s2 ord n (SUC len) = 
    if f (sub s1 n) (sub s2 n) = EQUAL
      then collate_aux f s1 s2 ord (n + 1) len
    else f (sub s1 n) (sub s2 n))`;

val collate_def = Define`
  collate f s1 s2 = 
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)`;

(*Pre conditions from sub*) 
val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val result = translate collate_def;
val collate_side_def = definition"collate_side_def";

val collate_aux_side_thm = Q.prove (
  `!f s1 s2 ord n len. (n + len = 
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> collate_aux_side f s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once collate_aux_side_def]
);

val collate_side_thm = Q.prove (
  `!f s1 s2. collate_side f s1 s2`,
  rw [collate_side_def, collate_aux_side_thm] ) |> update_precondition

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
