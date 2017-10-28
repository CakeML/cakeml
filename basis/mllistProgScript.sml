open preamble ml_translatorLib ml_progLib cfLib std_preludeTheory
open mllistTheory ml_translatorTheory mloptionProgTheory

(*this library depends on nothing*)
val _ = new_theory"mllistProg"

val _ = translation_extends "mloptionProg"

val _ = ml_prog_update (open_module "List");


val _ = ml_prog_update (add_dec ``Dtabbrev unknown_loc ["'a"] "list" (Tapp [Tvar "'a"] (TC_name (Short "list")))`` I);

val result = translate LENGTH;
(* val result = save_thm("length_v_thm",translate LENGTH); *)

val result = next_ml_names := ["revAppend"]
val res = translate REV_DEF;
val result = next_ml_names := ["rev"];
val res = translate REVERSE_REV;
val append_v_thm = translate APPEND;
val _ = save_thm("append_v_thm",append_v_thm);

val result = translate HD;
val hd_side_def = Q.prove(
  `!xs. hd_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "hd_side_def"])
  |> update_precondition;

val result = translate tl_def;
val result = next_ml_names := ["TL_hol"];
val result = translate TL;
val tl_1_side_def = Q.prove(
  `!xs. tl_1_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "tl_1_side_def"])
  |> update_precondition;


val result = translate LAST_DEF;


val result = translate getItem_def;


val result = translate (EL |> REWRITE_RULE[GSYM nth_def]);
val nth_side_def = theorem"nth_side_def";

val result = translate (TAKE_def |> REWRITE_RULE[GSYM take_def]);


val result = translate (DROP_def |> REWRITE_RULE[GSYM drop_def]);


val result = next_ml_names := ["concat"];
val result = translate FLAT;


val result = next_ml_names := ["map","mapi_aux","mapi","mapPartial"];
val result = translate MAP;
val result = translate mllistTheory.mapi_def;
val result = translate MAPI_thm;


val result = translate mapPartial_def;


val app = process_topdecs`
  fun app f ls = case ls of [] => ()
    | (x::xs) => (f x; app f xs)`;
val _ = ml_prog_update(ml_progLib.add_prog app pick_name)

val st = get_ml_prog_state();

val app_spec = Q.prove(
  `∀l start lv A.
   LIST_TYPE A l lv /\
   (!n xv. n < LENGTH l ∧ A (EL n l) xv ==> app p fv [xv] (eff (start+n)) (POSTv v. &UNIT_TYPE () v * (eff (start+n+1))))
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "app" st) [fv; lv] (eff start)
     (POSTv v. &UNIT_TYPE () v * (eff (start + (LENGTH l))))`,
  Induct \\ rw[LIST_TYPE_def]
  >- ( xcf "app" st \\ xmatch \\ xcon \\ xsimpl )
  \\ xcf "app" st
  \\ xmatch
  \\ xlet`POSTv v. &UNIT_TYPE () v * eff (start+1)`
  >- (
    xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"]))
    \\ qexists_tac`0` \\ xsimpl )
  \\ first_x_assum drule
  \\ disch_then(qspec_then`start+1`mp_tac)
  \\ simp[ADD1]
  \\ impl_tac
  >- (
    rw[]
    \\ first_x_assum(qspec_then`n+1`mp_tac)
    \\ simp[EL_CONS,PRE_SUB1] )
  \\ strip_tac \\ xapp)
|> CONV_RULE SWAP_FORALL_CONV
|> Q.SPEC`0` |> SIMP_RULE(srw_ss())[]
|> Q.GENL[`eff`,`fv`]
|> curry save_thm "app_spec";

val result = translate FIND_thm;


val result = translate FILTER;


val result = translate partition_aux_def;
val result = translate mllistTheory.partition_def;


val result = translate FOLDL;
val result = translate foldli_aux_def;
val result = translate foldli_def;


val result = translate FOLDR;
val result = translate (FOLDRi_def |> REWRITE_RULE[o_DEF]);


val result = translate EXISTS_DEF;


val result = next_ml_names := ["all"];
val result = translate EVERY_DEF;


val result = translate SNOC;
val result = translate GENLIST_AUX;
val result = translate GENLIST_GENLIST_AUX;
val result = translate tabulate_aux_def;
val result = translate tabulate_def;

val st = get_ml_prog_state()

(* TODO: using p:'b ffi_proj makes xapp fail in hard to trace ways
      - ultimately it's because app_of_Arrow_rule is not robust when ffi_ty is either 'a or 'b
*)
val tabulate_aux_inv_spec = Q.store_thm("tabulate_aux_inv_spec",
  `∀f fv A heap_inv n m nv mv acc accv ls.
    NUM n nv /\ NUM m mv /\ LIST_TYPE A acc accv /\
    ls = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m - n) /\
    (!i iv. NUM i iv /\ n <= i /\ i < m ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate_aux" st) [nv;mv;fv;accv] heap_inv
      (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  ntac 6 gen_tac
  \\ Induct_on`m-n`
  >- (
    rw[]
    \\ xcf "tabulate_aux" st
    \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
      >-(xopb \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
    \\ xif \\ asm_exists_tac \\ simp[]
    \\ xapp
    \\ instantiate \\ xsimpl
    \\ `m - n = 0` by simp[] \\ simp[])
  \\ rw[]
  \\ xcf "tabulate_aux" st
  \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
    >-(xopb \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
  \\ xif \\ asm_exists_tac \\ simp[]
  \\ Cases_on`m` \\ fs[]
  \\ rename1`SUC v = SUC m - n`
  \\ `v = m - n` by decide_tac
  \\ qpat_x_assum`SUC v = _`(assume_tac o SYM)
  \\ rw[] \\ fs[GENLIST_CONS,FUNPOW_SUC_PLUS]
  \\ xlet `POSTv v. &(A (f n) v) * heap_inv`
  >- ( xapp \\ xsimpl )
  \\ xlet `POSTv nv. &NUM (n+1) nv * heap_inv`
  >-( xopn \\  xsimpl \\ fs[NUM_def,INT_def] \\ intLib.COOPER_TAC)
  \\ xlet `POSTv av. &LIST_TYPE A (f n::acc) av * heap_inv`
  >-( xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp
  \\ xsimpl
  \\ map_every qexists_tac[`n+1`,`SUC m`]
  \\ instantiate
  \\ simp[o_DEF,ADD1]
  \\ once_rewrite_tac[CONS_APPEND]
  \\ simp[]);

val tabulate_inv_spec = Q.store_thm("tabulate_inv_spec",
  `!f fv A heap_inv n nv ls.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  xcf "tabulate" st \\
  xlet`POSTv v. &LIST_TYPE A [] v * heap_inv`
  >- (xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp
  \\ xsimpl
  \\ instantiate
  \\ simp[FUNPOW_SUC_PLUS,o_DEF,ETA_AX]);

val result = translate collate_def;

val result = translate ZIP_def;

val result = translate MEMBER_def;

(*Extra translations from std_preludeLib.sml *)
val res = translate LENGTH_AUX_def;
(*val res = translate LENGTH_AUX_THM;*)
val result = translate SUM;
val result = translate UNZIP;
val result = translate PAD_RIGHT;
val result = translate PAD_LEFT;
val result = translate (ALL_DISTINCT |> REWRITE_RULE [MEMBER_INTRO]);
val result = translate isPREFIX;
val result = translate FRONT_DEF;
val result = translate (splitAtPki_def |> REWRITE_RULE [SUC_LEMMA])


val front_side_def = Q.prove(
  `!xs. front_side xs = ~(xs = [])`,
  Induct THEN ONCE_REWRITE_TAC [fetch "-" "front_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

val last_side_def = Q.prove(
  `!xs. last_side xs = ~(xs = [])`,
  Induct THEN ONCE_REWRITE_TAC [fetch "-" "last_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;


val nth_side_def = Q.prove(
  `!n xs. nth_side xs n = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "nth_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

val _ =  ml_prog_update (close_module NONE);

(* sorting -- included here because it depends on List functions like append  *)

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

(* finite maps -- similarly *)

val FMAP_EQ_ALIST_def = Define `
  FMAP_EQ_ALIST f l <=> (ALOOKUP l = FLOOKUP f)`;

val FMAP_TYPE_def = Define `
  FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) (f:'a|->'b) =
    \v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ FMAP_EQ_ALIST f l`;

val _ = add_type_inv ``FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool)``
                     ``:('a # 'b) list``;

val ALOOKUP_eval = translate ALOOKUP_def;

val Eval_FLOOKUP = Q.prove(
  `!v. ((LIST_TYPE (PAIR_TYPE (b:'b -> v -> bool) (a:'a -> v -> bool)) -->
          b --> OPTION_TYPE a) ALOOKUP) v ==>
        ((FMAP_TYPE b a --> b --> OPTION_TYPE a) FLOOKUP) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS,FMAP_EQ_ALIST_def] THEN METIS_TAC [])
  |> (fn th => MATCH_MP th ALOOKUP_eval)
  |> add_user_proved_v_thm;

val AUPDATE_def = Define `AUPDATE l (x:'a,y:'b) = (x,y)::l`;
val AUPDATE_eval = translate AUPDATE_def;

val FMAP_EQ_ALIST_UPDATE = Q.prove(
  `FMAP_EQ_ALIST f l ==> FMAP_EQ_ALIST (FUPDATE f (x,y)) (AUPDATE l (x,y))`,
  SIMP_TAC (srw_ss()) [FMAP_EQ_ALIST_def,AUPDATE_def,ALOOKUP_def,FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FAPPLY_FUPDATE_THM]
  THEN METIS_TAC []);

val Eval_FUPDATE = Q.prove(
  `!v. ((LIST_TYPE (PAIR_TYPE a b) -->
          PAIR_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) -->
          LIST_TYPE (PAIR_TYPE a b)) AUPDATE) v ==>
        ((FMAP_TYPE a b --> PAIR_TYPE a b --> FMAP_TYPE a b) FUPDATE) v`,
  rw[Arrow_def,AppReturns_def,FMAP_TYPE_def] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs`strip_assume_tac o MATCH_MP th)) \\
  METIS_TAC[FMAP_EQ_ALIST_UPDATE,PAIR,APPEND_ASSOC] (* this also works above, but slower *))
  |> (fn th => MATCH_MP th AUPDATE_eval)
  |> add_user_proved_v_thm;

val NIL_eval = hol2deep ``[]:('a # 'b) list``

val Eval_FEMPTY = Q.prove(
  `!v. (LIST_TYPE (PAIR_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool)) []) v ==>
        ((FMAP_TYPE a b) FEMPTY) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS,FMAP_EQ_ALIST_def] THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `[]`
  THEN FULL_SIMP_TAC (srw_ss()) [ALOOKUP_def,FUN_EQ_THM,
         finite_mapTheory.FLOOKUP_DEF])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN NIL_eval)
  |> add_eval_thm;

val AEVERY_AUX_def = Define `
  (AEVERY_AUX aux P [] = T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) =
     if MEMBER x aux then AEVERY_AUX aux P xs else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)`;
val AEVERY_def = Define `AEVERY = AEVERY_AUX []`;
val _ = translate AEVERY_AUX_def;
val AEVERY_eval = translate AEVERY_def;

val AEVERY_AUX_THM = Q.prove(
  `!l aux P. AEVERY_AUX aux P l <=>
              !x y. (ALOOKUP l x = SOME y) /\ ~(MEM x aux) ==> P (x,y)`,
  Induct
  THEN FULL_SIMP_TAC std_ss [ALOOKUP_def,AEVERY_AUX_def,FORALL_PROD,
    MEM,GSYM MEMBER_INTRO] THEN REPEAT STRIP_TAC
  THEN SRW_TAC [] [] THEN METIS_TAC [SOME_11]);

val AEVERY_THM = Q.prove(
  `AEVERY P l <=> !x y. (ALOOKUP l x = SOME y) ==> P (x,y)`,
  SIMP_TAC (srw_ss()) [AEVERY_def,AEVERY_AUX_THM]);

val AEVERY_EQ_FEVERY = Q.prove(
  `FMAP_EQ_ALIST f l ==> (AEVERY P l <=> FEVERY P f)`,
  FULL_SIMP_TAC std_ss [FMAP_EQ_ALIST_def,FEVERY_DEF,AEVERY_THM]
  THEN FULL_SIMP_TAC std_ss [FLOOKUP_DEF]);

val Eval_FEVERY = Q.prove(
  `!v. (((PAIR_TYPE (a:'a->v->bool) (b:'b->v->bool) --> BOOL) -->
         LIST_TYPE (PAIR_TYPE a b) --> BOOL) AEVERY) v ==>
        (((PAIR_TYPE (a:'a->v->bool) (b:'b->v->bool) --> BOOL) -->
         FMAP_TYPE a b --> BOOL) FEVERY) v`,
  rw[Arrow_def,AppReturns_def,FMAP_TYPE_def,PULL_EXISTS,BOOL_def] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs`strip_assume_tac o MATCH_MP th)) \\
  fs [] \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ fs[] \\
  METIS_TAC[AEVERY_EQ_FEVERY,Boolv_11])
  |> (fn th => MATCH_MP th AEVERY_eval)
  |> add_user_proved_v_thm;

val AMAP_def = Define `
  (AMAP f [] = []) /\
  (AMAP f ((x:'a,y:'b)::xs) = (x,(f y):'c) :: AMAP f xs)`;
val AMAP_eval = translate AMAP_def;

val ALOOKUP_AMAP = Q.prove(
  `!l. ALOOKUP (AMAP f l) a =
        case ALOOKUP l a of NONE => NONE | SOME x => SOME (f x)`,
  Induct THEN SIMP_TAC std_ss [AMAP_def,ALOOKUP_def,FORALL_PROD]
  THEN SRW_TAC [] []);

val FMAP_EQ_ALIST_o_f = Q.prove(
  `FMAP_EQ_ALIST m l ==> FMAP_EQ_ALIST (x o_f m) (AMAP x l)`,
  SIMP_TAC std_ss [FMAP_EQ_ALIST_def,FUN_EQ_THM,FLOOKUP_DEF,
    o_f_DEF,ALOOKUP_AMAP] THEN REPEAT STRIP_TAC THEN SRW_TAC [] []);

val Eval_o_f = Q.prove(
  `!v. (((b --> c) --> LIST_TYPE (PAIR_TYPE (a:'a->v->bool) (b:'b->v->bool)) -->
          LIST_TYPE (PAIR_TYPE a (c:'c->v->bool))) AMAP) v ==>
        (((b --> c) --> FMAP_TYPE a b --> FMAP_TYPE a c) $o_f) v`,
  rw[Arrow_def,AppReturns_def,FMAP_TYPE_def,PULL_EXISTS] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs`strip_assume_tac o MATCH_MP th)) \\
  fs [] \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ fs[] \\
  METIS_TAC[FMAP_EQ_ALIST_o_f])
  |> (fn th => MATCH_MP th AMAP_eval)
  |> add_user_proved_v_thm;

val append_eval = let
  val th = fetch "-" "append_v_thm"
  val inv = ``x ++ (y:('a # 'b) list)``
            |> repeat rator |> hol2deep |> concl |> rand
  val pat = th |> concl |> rator
  val (ii,ss) = match_term pat inv
  val th = INST ii (INST_TYPE ss th)
  in th end

val Eval_FUNION = Q.prove(
  `!v. (LIST_TYPE (PAIR_TYPE a b) --> LIST_TYPE (PAIR_TYPE a b) -->
         LIST_TYPE (PAIR_TYPE a b)) APPEND v ==>
        (FMAP_TYPE a b --> FMAP_TYPE a b --> FMAP_TYPE a b) $FUNION v`,
  rw[Arrow_def,AppReturns_def,FMAP_TYPE_def,FMAP_EQ_ALIST_def,PULL_EXISTS] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs`strip_assume_tac o MATCH_MP th)) \\
  fs [] \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ fs[] \\ rw[] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs''`strip_assume_tac o MATCH_MP th)) \\
  fs [] \\ first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ fs[] \\
  first_assum(part_match_exists_tac (hd o strip_conj) o concl) \\ fs[] \\
  FULL_SIMP_TAC std_ss [ALOOKUP_APPEND,FUN_EQ_THM]
  THEN FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FUNION_DEF,IN_UNION]
  THEN REPEAT STRIP_TAC THEN SRW_TAC [] [] THEN FULL_SIMP_TAC std_ss [])
  |> (fn th => MATCH_MP th append_eval)
  |> add_user_proved_v_thm;

val ADEL_def = Define `
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)`
val ADEL_eval = translate ADEL_def;

val ALOOKUP_ADEL = Q.prove(
  `!l a x. ALOOKUP (ADEL l a) x = if x = a then NONE else ALOOKUP l x`,
  Induct THEN SRW_TAC [] [ALOOKUP_def,ADEL_def] THEN Cases_on `h`
  THEN SRW_TAC [] [ALOOKUP_def,ADEL_def]);

val FMAP_EQ_ALIST_ADEL = Q.prove(
  `!x l. FMAP_EQ_ALIST x l ==>
          FMAP_EQ_ALIST (x \\ a) (ADEL l a)`,
  FULL_SIMP_TAC std_ss [FMAP_EQ_ALIST_def,ALOOKUP_def,fmap_domsub,FUN_EQ_THM]
  THEN REPEAT STRIP_TAC THEN SRW_TAC [] [ALOOKUP_ADEL,FLOOKUP_DEF,DRESTRICT_DEF]
  THEN FULL_SIMP_TAC std_ss []);

val Eval_fmap_domsub = Q.prove(
  `!v. ((LIST_TYPE (PAIR_TYPE a b) --> a -->
          LIST_TYPE (PAIR_TYPE a b)) ADEL) v ==>
        ((FMAP_TYPE a b --> a --> FMAP_TYPE a b) $\\) v`,
  rw[Arrow_def,AppReturns_def,FMAP_TYPE_def,PULL_EXISTS] \\
  first_x_assum(fn th => first_x_assum (qspec_then`refs`strip_assume_tac o MATCH_MP th)) \\
  METIS_TAC[FMAP_EQ_ALIST_ADEL])
  |> (fn th => MATCH_MP th ADEL_eval)
  |> add_user_proved_v_thm;

val _ = export_theory()
