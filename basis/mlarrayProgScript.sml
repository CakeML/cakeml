open preamble
     ml_translatorTheory ml_translatorLib semanticPrimitivesTheory basisFunctionsLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib
     mlbasicsProgTheory mlw8arrayProgTheory

val _ = new_theory"mlarrayProg"

val _ = translation_extends"mlw8arrayProg"

fun array_st () = get_ml_prog_state ()


val () = ml_prog_update (open_module "Array");

val () = append_decs
   ``[Dtabbrev ["'a"] "array" (Tapp [Tvar "'a"] TC_array);
      mk_binop "array" Aalloc;
      mk_binop "sub" Asub;
      mk_unop "length" Alength;
      Dlet (Pvar "update")
       (Fun "x" (Fun "y" (Fun "z"
         (App Aupdate [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``;

val array_fromList = process_topdecs
  `fun fromList l =
    let val arr = array (List.length l) 0
      fun f l i =
       case l of
          [] => arr
        | (h::t) => (update arr i h; f t (i + 1))
    in f l 0 end`;


val fromList_st = ml_progLib.add_prog array_fromList pick_name (array_st());
(* val () = append_decs array_fromList; *)

val array_tabulate = process_topdecs
  `fun tabulate n f =
    let val arr = array n 0
      fun u x =
        if x = n then arr
        else (update arr x (f x); u (x + 1))
    in
      u 0
    end`;

val tabulate_st = ml_progLib.add_prog array_tabulate pick_name (array_st ());
(* val () = append_decs array_tabulate; *)

(*val array_vector = process_topdecs
  `fun vector arr = Vector.tabulate (length arr) (fn i => sub arr i)`*)

val array_copy = process_topdecs
  `fun copy_aux src dst di max n =
    if n = max
      then ()
    else (update dst (di + n) (sub src n); copy_aux src dst di (n + 1))

  fun copy src dst di =
    copy_aux src dst di (length src) 0`

val copy_st = ml_progLib.add_prog array_copy pick_name (array_st ())
(* val () = append_decs array_copy; *)

val array_copyVec = process_topdecs
  `fun copyVec_aux src dst di max n =
    if n = max
        then ()
    else (update dst (di + n) (Vector.sub src n); copy_aux src dst di max (n + 1))

  fun copy src dst di =
    copyVec_aux src dst di (Vector.length src) 0`

val copyVec_st = ml_progLib.add_prog array_copyVec pick_name (array_st())
(*val () = append_decs array_copyVec; *)

val array_app = process_topdecs
  `fun app_aux f arr max n =
    if n = max
      then ()
    else (f (sub arr n); app_aux f arr max (n + 1))

  fun app f arr =
    app_aux f arr (length arr) 0`

val app_st = ml_progLib.add_prog array_app pick_name (array_st ())
(*val () = append_decs array_app; *)

val array_appi = process_topdecs
  `fun appi_aux f arr max n =
    if n = max
      then ()
    else (f n (sub arr n); app_aux f arr max (n + 1))

  fun appi f arr =
    appi_aux f arr (length arr) 0`

val appi_st = ml_progLib.add_prog array_appi pick_name (array_st ())
(*val () = append_decs array_appi;*)

val array_modify = process_topdecs
  `fun modify_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f (sub arr n)); modify_aux f arr max (n + 1))

  fun modify f arr =
    modify_aux f arr (length arr) 0`

val modify_st = ml_progLib.add_prog array_modify pick_name (array_st ())
(*val () = append_decs array_modify; *)

val array_modifyi = process_topdecs
  `fun modifyi_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f (sub arr n)); modify_aux f arr max (n + 1))

  fun modifyi f arr =
    modifyi_aux f arr (length arr) 0`

val modifyi_st = ml_progLib.add_prog array_modify pick_name (array_st ())
(*val () = append_decs array_modify;*)


val array_foldli = process_topdecs
  `fun foldli_aux f init arr max n =
    if n = max
      then init
    else foldli_aux f (f n init (sub arr n)) arr max (n + 1)

  fun foldli f init arr =
    foldli_aux f init arr (length arr) 0`

val foldli_st = ml_progLib.add_prog array_foldli pick_name (array_st ())
(*val () = append_decs array_foldli; *)

val array_foldl = process_topdecs
  `fun foldl_aux f init arr max n =
    if n = max
      then init
    else foldl_aux f (f init (sub arr n)) arr max (n + 1)

  fun foldl f init arr =
    foldl_aux f init arr (length arr) 0`

val foldl_st = ml_progLib.add_prog array_foldl pick_name (array_st ())
(* val () = append_decs array_foldl; *)

val array_foldri = process_topdecs
  `fun foldri_aux f init arr n =
    if n = 0
      then init
    else foldri_aux f (f (n - 1) init (sub arr (n - 1))) arr (n - 1)

  fun foldri f init arr =
    foldri_aux f init arr (length arr)`

val foldri_st = ml_progLib.add_prog array_foldri pick_name (array_st ())
(*val () = append_decs array_foldri;*)


val array_foldr = process_topdecs
  `fun foldr_aux f init arr n =
    if n = 0
      then init
    else foldr_aux f (f init (sub arr (n - 1))) arr (n - 1)

  fun foldr f init arr =
    foldr_aux f init arr (length arr)`

val foldr_st = ml_progLib.add_prog array_foldr pick_name (array_st ())
(*val () = append_decs array_foldr;*)


val array_find = process_topdecs
  `fun find_aux f arr max n =
    if n = max
      then NONE
    else (if f (sub arr n)
        then SOME(sub arr n)
      else find_aux f arr max (n + 1))

  fun find f arr =
    find_aux f arr (length arr) 0`

val find_st = ml_progLib.add_prog array_find pick_name (array_st ())
(*val () = append_decs array_find;*)

val array_findi = process_topdecs
  `fun findi_aux f arr max n =
    if n = max
      then NONE
    else (if f n (sub arr n)
        then SOME((n, sub arr n))
      else find_aux f arr max (n + 1))

  fun findi f arr =
    findi_aux f arr (length arr) 0`

val findi_st = ml_progLib.add_prog array_findi pick_name (array_st ())
(*val () = append_decs array_findi;*)

val array_exists = process_topdecs
  `fun exists_aux f arr max n =
    if n = max
      then false
    else (if f (sub arr n)
      then T
    else exists_aux f arr max (n + 1))

  fun exists f arr =
    exists_aux f arr (length arr) 0`

val exists_st = ml_progLib.add_prog array_exists pick_name (array_st ())
(*val () = append_decs array_exists; *)


val array_all = process_topdecs
  `fun all_aux f arr max n =
    if n = max
      then T
    else (if f (sub arr n)
      then all_aux f arr max (n + 1)
    else F)

  fun all f arr =
    all_aux f arr (length arr) 0`

val all_st = ml_progLib.add_prog array_all pick_name (array_st ())
(* val () = append_decs array_all; *)


val array_collate = process_topdecs
  `fun collate_aux f a1 a2 max ord n =
    if n = max
      then ord
    else (if f (sub a1 n) (sub a2 n) = Equal
        then collate_aux f a1 a2 max ord (n + 1)
      else f (sub a1 n) (sub a2 n))

  fun collate f a1 a2 =
    if (length a1) < (length a2)
      then collate_aux f a1 a2 (length a1) LESS 0
    else if (length a2) < (length a1)
      then collate_aux f a1 a2 (length a2) GREATER 0
    else collate_aux f a1 a2 (length a2) EQUAL 0`

val collate_st = ml_progLib.add_prog array_collate pick_name (array_st ())
(* val () = append_decs array_collate; *)


val _ = ml_prog_update (close_module NONE);

fun prove_array_spec op_name =
  xcf op_name (array_st()) \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

val array_alloc_spec = Q.store_thm ("array_alloc_spec",
  `!n nv v.
     NUM n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.array" (array_st())) [nv; v]
       emp (POSTv av. ARRAY av (REPLICATE n v))`,
  prove_array_spec "Array.array");

val array_sub_spec = Q.store_thm ("array_sub_spec",
  `!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.sub" (array_st())) [av; nv]
       (ARRAY av a) (POSTv v. cond (v = EL n a) * ARRAY av a)`,
  prove_array_spec "Array.sub");

val array_length_spec = Q.store_thm ("array_length_spec",
  `!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Array.length" (array_st())) [av]
       (ARRAY av a)
       (POSTv v. cond (NUM (LENGTH a) v) * ARRAY av a)`,
  prove_array_spec "Array.length");

val array_update_spec = Q.store_thm ("array_update_spec",
  `!a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.update" (array_st()))
       [av; nv; v]
       (ARRAY av a)
       (POSTv uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))`,
  prove_array_spec "Array.update");



val array_fromList_spec = Q.store_thm("array_fromList_spec",
  `!l lv a A.
    LIST_TYPE A l lv /\ v_to_list lv = SOME a ==>
    app (p:'ffi ffi_proj) ^(fetch_v "fromList" fromList_st) [lv]
      emp (POSTv av. ARRAY av a)`,
    xcf "fromList" fromList_st \\
    xlet `POSTv v. & NUM (LENGTH l) v` >-
    (xapp \\ metis_tac[]) \\
    xlet `POSTv ar. ARRAY ar (REPLICATE (LENGTH l) (Litv(IntLit 0)))` >-
    (xapp \\ xsimpl) \\
    xfun_spec `f`
      `!ls lsv i iv a l_pre rest.
        NUM i iv /\ LENGTH l_pre = i /\
        LIST_TYPE A ls lsv /\ v_to_list lsv = SOME a /\ LENGTH ls = LENGTH rest
      ==>
      app p f [lsv; iv]
      (ARRAY ar (l_pre ++ rest))
      (POSTv ret. & (ret = ar) * ARRAY ar (l_pre ++ a))` >- (
        Induct >- (
          rw[LIST_TYPE_def] \\
          first_x_assum match_mp_tac \\
          xmatch \\ xret \\
          fs [LENGTH_NIL_SYM] \\
          fs [terminationTheory.v_to_list_def] \\
          xsimpl) \\
        rw[LIST_TYPE_def] \\
        fs[terminationTheory.v_to_list_def] \\
        qpat_x_assum`_ = SOME _`mp_tac \\ CASE_TAC \\ rw[] \\
        last_x_assum match_mp_tac \\
        xmatch \\
        Cases_on `rest` \\ fs[] \\
        qmatch_assum_rename_tac`A h hv` \\
        xlet `POSTv u. ARRAY ar (l_pre ++ hv::t)` >- (
          xapp \\
          instantiate \\
          xsimpl ) \\
        xlet `POSTv iv. ARRAY ar (l_pre ++ hv::t) * & NUM (LENGTH l_pre + 1) iv`
        >- (
          xapp \\
          xsimpl \\
          qexists_tac `&(LENGTH l_pre)` \\
          fs [NUM_def, plus_def, integerTheory.INT_ADD]
          ) \\
        once_rewrite_tac[CONS_APPEND] \\
        rewrite_tac[APPEND_ASSOC] \\
        xapp \\ xsimpl ) \\
      xapp \\
      instantiate \\
      simp[LENGTH_NIL_SYM,PULL_EXISTS] \\
      instantiate \\
      xsimpl \\
      simp[LENGTH_REPLICATE]);

(*
val eq_v_thm = fetch "-" "eq_v_thm"
val eq_num_v_thm = save_thm("eq_num_v_thm",
        MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1))

val tabulate = prefix ^"tabulate";
val array_tabulate_spec = Q.store_thm ("array_tabulate_spec",
  `!n nv f fv A.
    NUM n nv /\ (NUM --> A) f fv ==>
    app (p:'ffi ffi_proj) ^(fetch_v tabulate tabulate_st) [nv; fv]
    emp (POSTv av. ARRAY av (GENLIST f n))`,
    xcf "tabulate" tabulate_st \\
    xlet `POSTv av. ARRAY av (REPLICATE n (Litv(IntLit 0)))` >- (
      xapp \\ rw []) \\
    xfun_spec `u`
      `!x xv l_pre rest.
        NUM x xv /\ LENGTH l_pre = x /\ LENGTH l_pre + LENGTH rest = n ==>
          app p u [xv]
        (ARRAY av (l_pre ++ rest))
        (POSTv ret. & (ret = av) * ARRAY av (l_pre ++ (GENLIST (\i. f (x + i)) (n - x))))`
    >- (
     Induct >- (
        rw []  \\ first_x_assum match_mp_tac \\
        fsrw_tac[ETA_ss][LENGTH_NIL] \\
        xlet `POSTv bv. & BOOL (xv=nv) bv * ARRAY av rest`
        >- (
          xapp \\ rw[BOOL_def] \\ xsimpl \\
          instantiate \\
          metis_tac[EqualityType_NUM_BOOL,EqualityType_def])
        \\ xif
        >- (xret \\ xsimpl \\ fs[NUM_def,INT_def,LENGTH_NIL_SYM] )
        \\ xlet `POSTv v. ARRAY av rest * & A (f 0) v`
        >- (
          xapp \\ xsimpl  \\ instantiate)
        \\ xlet `POSTv u. ARRAY av (LUPDATE v 0 rest)`
        >- (xapp \\ xsimpl \\ instantiate \\
        `!a b. NUM a nv /\ NUM b xv /\ xv <> nv ==> a <> b` by fs[]

DB.find "NUM _ _ ="
    fs [GSYM NUM_def, INT_def, LENGTH_NIL_SYM, ]
      rw [] \\ first_x_assum match_mp_tac ) \\
      xapp \\
      rw [LENGTH_NIL_SYM] \\
      xsimpl \\
      rw [LENGTH_REPLICATE, ETA_AX]
);


val copy_aux = prefix ^"copy_aux";
val array_copy_aux_spec = Q.store_thm("array_copy_aux_spec",
  `!src srcv bfr afr mid dstv di div n nv max maxv.
      NUM di div /\ NUM n nv /\ NUM max maxv /\ LENGTH src = LENGTH mid
       /\  di = LENGTH bfr /\ n <= max /\ max = LENGTH src
      ==> app (p:'ffi ffi_proj) ^(fetch_v copy_aux copy_st) [srcv; dstv; div; maxv; nv]
      (ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr))
    (POSTv uv. ARRAY srcv src * ARRAY dstv (bfr ++ TAKE n mid ++ DROP n src ++ afr))`,
      xcf copy_aux copy_st \\
      Induct_on `n` \\ rw[] >- (
        xlet `POSTv bool. & BOOL (n = max) bool * ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr)` >- (
          cheat )
        xif >- (
          cheat
          (*xcon \\
          `n = 0` by fs[NUM_def, INT_def]
          `LENGTH mid = LENGTH src` by DECIDE_TAC \\
          `DROP (LENGTH mid) src = []` by fs [DROP_LENGTH_NIL] \\
          xsimpl *))
        xlet `POSTv v. &(v = EL n src) * ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr)` >- (
          xapp \\
          xsimpl \\
          qexists_tac `n` \\
          rw[] )
        xlet `POSTv v. & NUM (di + n) v * ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr)` >- (
          xapp \\
          xsimpl \\
          fs [NUM_def] \\
          instantiate \\
          rw [std_preludeTheory.plus_def, integerTheory.INT_ADD])
        xlet `POSTv u. ARRAY srcv src * ARRAY dstv (LUPDATE (EL n src) (di + n) (bfr ++ mid ++ afr))` >- (
          xapp \\
          xsimpl \\
          instantiate)
        xlet `POSTv v. & NUM (n + 1) v * ARRAY srcv src * ARRAY dstv (LUPDATE (EL n src) (di + n) (bfr ++ mid ++ afr))` >- (
          xapp \\
          xsimpl \\
          fs [NUM_def] \\
          instantiate \\
          rw [std_preludeTheory.plus_def, integerTheory.INT_ADD])
        xapp




val modify_aux = prefix ^"modify_aux"
val array_modify_aux_spec = Q.store_thm("array_modify_aux_spec",
  `!f fv a av max maxv n nv A A'.
    NUM max maxv /\ max = LENGTH a /\ NUM n nv /\ (A --> A') f fv /\ n <= max
    ==> app (p:'ffi ffi_proj) ^(fetch_v modify_aux modify_st) [fv; av; maxv; nv]
    (ARRAY av a) (POSTv uv. ARRAY av (TAKE n a ++ MAP f (DROP n a)))`
    xcf modify_aux modify_st \\
    xlet `POSTv bool. & (BOOL (n = max) bool) * ARRAY av a` >- (
      cheat
    )
    xif >- (
      xcon \\ rw [DROP_LENGTH_NIL] \\
      xsimpl
    rw [cfHeapsBaseTheory.ARRAY_def]
*)
val _ = export_theory ()
