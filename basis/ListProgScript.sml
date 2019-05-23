(*
  Module about the built-in list tyoe.
*)
open preamble ml_translatorLib ml_progLib cfLib std_preludeTheory
open mllistTheory ml_translatorTheory OptionProgTheory
open basisFunctionsLib

val _ = new_theory"ListProg"

val _ = translation_extends "OptionProg"

val _ = ml_prog_update (open_module "List");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a"] "list" (Atapp [Atvar "'a"] (Short "list"))`` I);

val r = translate NULL;

val _ = ml_prog_update open_local_block;
val res = translate LENGTH_AUX_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["length"]
val res = translate LENGTH_AUX_THM;

val _ = ml_prog_update open_local_block;
val res = translate REV_DEF;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["rev"];
val res = translate REVERSE_REV;

(* New list-append translation *)
val append_v_thm = trans "@" listSyntax.append_tm;
val _ = save_thm("append_v_thm",append_v_thm);

(* Old list-append translation *)
(*val append_v_thm = translate APPEND;*)
(*val _ = save_thm("append_v_thm",append_v_thm);*)

val result = translate HD;
val hd_side_def = Q.prove(
  `!xs. hd_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "hd_side_def"])
  |> update_precondition;

val result = translate TL_DEF;

val result = translate LAST_DEF;

val _ = next_ml_names := ["getItem"];
val result = translate getItem_def;

val result = translate (EL |> REWRITE_RULE[GSYM nth_def]);
val nth_side_def = theorem"nth_side_def";

val result = translate (TAKE_def |> REWRITE_RULE[GSYM take_def]);
val result = translate (DROP_def |> REWRITE_RULE[GSYM drop_def]);

val _ = next_ml_names := ["takeUntil","dropUntil"];
val result = translate takeUntil_def;
val result = translate dropUntil_def;

val _ = next_ml_names := ["cmp"];
val result = translate list_compare_def;

val result = next_ml_names := ["concat"];
val result = translate FLAT;

(* the let is introduced to produce slight better code (smaller stack frames) *)
val MAP_let = prove(
  ``MAP f xs =
    case xs of
    | [] => []
    | (y::ys) => let z = f y in z :: MAP f ys``,
  Cases_on `xs` \\ fs []);

Theorem MAP_ind:
   ∀P. (∀f xs. (∀y ys z. xs = y::ys ∧ z = f y ⇒ P f ys) ⇒ P f xs) ⇒
       ∀f xs. P f xs
Proof
  ntac 2 strip_tac \\ Induct_on `xs` \\ fs []
QED

val _ = add_preferred_thy "-"; (* so that the translator finds MAP_ind above *)

val result = next_ml_names := ["map"]
val result = translate MAP_let;

val _ = ml_prog_update open_local_block;
val result = translate mllistTheory.mapi_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["mapi","mapPartial"];
val result = translate MAPI_thm;
val result = translate mapPartial_def;

val app = process_topdecs`
  fun app f ls = case ls of [] => ()
    | (x::xs) => (f x; app f xs)`;
val _ = ml_prog_update(ml_progLib.add_prog app pick_name)

val result = translate FIND_thm;

val result = translate FILTER;

val _ = ml_prog_update open_local_block;
val result = translate partition_aux_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["partition"];
val result = translate mllistTheory.partition_def;

val result = translate FOLDL;

val _ = ml_prog_update open_local_block;
val result = translate foldli_aux_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["foldi"];
val result = translate foldli_def;

val result = translate FOLDR;
val result = translate (FOLDRi_def |> REWRITE_RULE[o_DEF]);

val result = translate EXISTS_DEF;

val result = next_ml_names := ["all"];
val result = translate EVERY_DEF;

val result = translate SNOC;

val _ = ml_prog_update open_local_block;
val result = translate GENLIST_AUX;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["genlist"];
val result = translate GENLIST_GENLIST_AUX;

val result = next_ml_names := ["tabulate"];
val result = translate tabulate_aux_def;

val tabulate_aux_inv_spec =
  let
    val st = get_ml_prog_state();
  in
  Q.store_thm("tabulate_aux_inv_spec",
  `∀f fv A heap_inv n m nv mv acc accv ls.
    NUM n nv /\ NUM m mv /\ LIST_TYPE A acc accv /\
    ls = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m - n) /\
    (!i iv. NUM i iv /\ n <= i /\ i < m ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate" st) [nv;mv;fv;accv] heap_inv
      (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  ntac 6 gen_tac
  \\ Induct_on`m-n`
  >- (
    rw[]
    \\ xcf "tabulate" st
    \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
      >-(xopb \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
    \\ xif \\ asm_exists_tac \\ simp[]
    \\ xapp
    \\ instantiate \\ xsimpl
    \\ `m - n = 0` by simp[] \\ simp[])
  \\ rw[]
  \\ xcf "tabulate" st
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
  \\ simp[]) end;

val result = next_ml_names := ["tabulate"];
val result = translate tabulate_def;

val tabulate_inv_spec =
  let
    val st = get_ml_prog_state();
  in
  Q.store_thm("tabulate_inv_spec",
  `!f fv A heap_inv n nv ls.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  xcf "tabulate" st \\
  xlet`POSTv v. &LIST_TYPE A [] v * heap_inv`
  >- (xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp_spec tabulate_aux_inv_spec
  \\ xsimpl
  \\ instantiate
  \\ simp[FUNPOW_SUC_PLUS,o_DEF,ETA_AX]) end;

val result = translate collate_def;

val result = translate ZIP_def;

val result = translate MEMBER_def;

val result = translate SUM;
val result = translate UNZIP;
val result = translate PAD_RIGHT;
val result = translate PAD_LEFT;
val result = translate (ALL_DISTINCT |> REWRITE_RULE [MEMBER_INTRO]);
val _ = next_ml_names := ["isPrefix"];
val result = translate isPREFIX;
val result = translate FRONT_DEF;
val _ = next_ml_names := ["splitAtPki"];
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

val _ = next_ml_names := ["update"];
val result = translate LUPDATE_def;

val _ = (next_ml_names := ["compare"]);
val _ = translate mllistTheory.list_compare_def;

val _ = ml_prog_update open_local_block;
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["sort"];
val res = translate sortingTheory.QSORT_DEF;

val _ =  ml_prog_update close_local_blocks;
val _ =  ml_prog_update (close_module NONE);

(* finite maps -- depend on lists *)

val _ = ml_prog_update (open_module "Alist");

val FMAP_EQ_ALIST_def = Define `
  FMAP_EQ_ALIST f l <=> (ALOOKUP l = FLOOKUP f)`;

val FMAP_TYPE_def = Define `
  FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) (f:'a|->'b) =
    \v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ FMAP_EQ_ALIST f l`;

val _ = add_type_inv ``FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool)``
                     ``:('a # 'b) list``;

val _ = next_ml_names := ["lookup"];
val ALOOKUP_eval = translate ALOOKUP_def;

val Eval_FLOOKUP = Q.prove(
  `!v. ((LIST_TYPE (PAIR_TYPE (b:'b -> v -> bool) (a:'a -> v -> bool)) -->
          b --> OPTION_TYPE a) ALOOKUP) v ==>
        ((FMAP_TYPE b a --> b --> OPTION_TYPE a) FLOOKUP) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS,FMAP_EQ_ALIST_def] THEN METIS_TAC [])
  |> (fn th => MATCH_MP th ALOOKUP_eval)
  |> add_user_proved_v_thm;

val _ = next_ml_names := ["update"];
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
val _ = next_ml_names := ["every","every"];
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

val _ = next_ml_names := ["map"];
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

(* TODO: quick fix on account of hol2deep not accepting ``$++`` *)
val append_eval =
  let
    val th  = fetch "-" "append_v_thm"
    val pat = th |> concl |> rator
    val inv = ``(LIST_TYPE (PAIR_TYPE a b) -->
                 LIST_TYPE (PAIR_TYPE a b) -->
                 LIST_TYPE (PAIR_TYPE a b))
                 ((++) : ('a # 'b) list -> ('a # 'b) list -> ('a # 'b) list)``
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

val _ = next_ml_names := ["delete"];
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

val _ =  ml_prog_update (close_module NONE);

val _ = export_theory()
