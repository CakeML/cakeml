(*
  Module about the built-in list tyoe.
*)
Theory ListProg
Ancestors
  mergesort std_prelude mllist ml_translator OptionProg
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "OptionProg"

val _ = ml_prog_update (open_module "List");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [«'a»] «list» (Atapp [Atvar «'a»] (Short «list»))`` I);

val r = translate NULL;

val _ = ml_prog_update open_local_block;
val res = translate LENGTH_AUX_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["length"]
val res = translate LENGTH_AUX_THM;

val _ = ml_prog_update open_local_block;
val res = translate REV_DEF;
val res = translate map_rev'_def;
val res = translate filter_rev'_def;
val res = translate flat_rev'_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["rev"];
val res = translate REVERSE_REV;
val result = next_ml_names := ["mapRev"];
val res = translate map_rev_def;
val result = next_ml_names := ["filterRev"];
val res = translate filter_rev_def;
val result = next_ml_names := ["flatRev"];
val res = translate flat_rev_def;

(* New list-append translation *)
val append_v_thm = trans "@" listSyntax.append_tm;
Theorem append_v_thm[allow_rebind] =
  append_v_thm

(* Old list-append translation *)
(* val append_v_thm = translate APPEND; *)
(* Theorem append_v_thm = append_v_thm *)

val result = translate HD;
val hd_side_def = Q.prove(
  `!xs. hd_side xs = ~(xs = [])`,
  Cases THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "hd_side_def"])
  |> update_precondition;

val result = translate TL_DEF;

val result = translate LAST_DEF;

val _ = next_ml_names := ["getItem"];
val result = translate mllistTheory.getItem_def;

Theorem nth_thm[local]:
  mllist$nth l 0 = HD l ∧
  mllist$nth l (SUC n) = mllist$nth (TL l) n
Proof
  gvs [mllistTheory.nth_def,listTheory.EL]
QED

val result = translate nth_thm;
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
Theorem MAP_let[local]:
    MAP f xs =
    case xs of
    | [] => []
    | (y::ys) => let z = f y in z :: MAP f ys
Proof
  Cases_on `xs` \\ fs []
QED

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

Quote add_cakeml:
  fun app f ls = case ls of [] => ()
    | (x::xs) => (f x; app f xs)
End

val result = translate FIND_thm;

val result = translate FILTER;

val _ = ml_prog_update open_local_block;
val result = translate partition_aux_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["partition"];
val result = translate mllistTheory.partition_def;

val result = translate foldl_def;

val _ = ml_prog_update open_local_block;
val result = translate foldli_aux_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["foldli"];
val result = translate foldli_def;

val result = translate FOLDR;
val result = next_ml_names := ["foldri"];
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

local
  val st = get_ml_prog_state();
in
Theorem tabulate_aux_inv_spec:
  ∀f fv A heap_inv n m nv mv acc accv ls.
    NUM n nv /\ NUM m mv /\ LIST_TYPE A acc accv /\
    ls = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m - n) /\
    (!i iv. NUM i iv /\ n <= i /\ i < m ==>
            app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate" st) [nv;mv;fv;accv] heap_inv
      (POSTv lv. &LIST_TYPE A ls lv * heap_inv)
Proof
  ntac 6 gen_tac
  \\ Induct_on`m-n`
  >- (
    rw[]
    \\ xcf "tabulate" st \\ simp []
    \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
    >- (xint_cmp \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
    \\ xif \\ gvs[]
    \\ xapp
    \\ instantiate \\ xsimpl
    \\ `m - n = 0` by simp[] \\ simp[])
  \\ rw[]
  \\ xcf "tabulate" st \\ simp []
  \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
  >- (xint_cmp \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
  \\ xif \\ gvs []
  \\ Cases_on`m` \\ fs[]
  \\ rename1`SUC v = SUC m - n`
  \\ `v = m - n` by decide_tac
  \\ qpat_x_assum`SUC v = _`(assume_tac o SYM)
  \\ rw[] \\ fs[GENLIST_CONS,FUNPOW_SUC_PLUS]
  \\ xlet `POSTv v. &(A (f n) v) * heap_inv`
  >- ( xapp \\ xsimpl )
  \\ xlet `POSTv nv. &NUM (n+1) nv * heap_inv`
  >-( xarith \\  xsimpl \\ fs[NUM_def,INT_def] \\ intLib.COOPER_TAC)
  \\ xlet `POSTv av. &LIST_TYPE A (f n::acc) av * heap_inv`
  >-( xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp
  \\ xsimpl
  \\ map_every qexists_tac[`n+1`,`SUC m`]
  \\ instantiate
  \\ simp[o_DEF,ADD1]
  \\ once_rewrite_tac[CONS_APPEND]
  \\ simp[]
QED
end

val result = next_ml_names := ["tabulate"];
val result = translate tabulate_def;

local
  val st = get_ml_prog_state();
in
Theorem tabulate_inv_spec:
  !f fv A heap_inv n nv ls.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)
Proof
  rpt strip_tac
  \\ xcf "tabulate" st
  \\ xlet`POSTv v. &LIST_TYPE A [] v * heap_inv`
  >- (xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp_spec tabulate_aux_inv_spec
  \\ xsimpl
  \\ instantiate
  \\ simp[FUNPOW_SUC_PLUS,o_DEF,ETA_AX]
QED
end

val result = translate collate_def;

Theorem ZIP_ind:
  ∀P. (∀v. (∀x4 x3 x2 x1. v = (x4::x3,x2::x1) ⇒ P (x3,x1)) ⇒ P v) ⇒ ∀v. P v
Proof
  simp [FORALL_PROD] \\ ntac 2 strip_tac \\ Induct \\ rw []
QED

Theorem ZIP_eq:
  ZIP x =
    case x of
    | (x::xs,y::ys) => (x,y) :: ZIP (xs,ys)
    | _ => []
Proof
  PairCases_on ‘x’ \\ fs [ZIP_def]
  \\ Cases_on ‘x0’ \\ Cases_on ‘x1’ \\ fs [ZIP_def]
QED

val result = translate ZIP_eq;

val result = translate MEMBER_def;

val result = translate SUM;

Theorem UNZIP_eq:
  !xs.
    UNZIP xs =
      case xs of
        [] => ([], [])
      | (y,z)::xs =>
          let (ys,zs) = UNZIP xs in
            (y::ys, z::zs)
Proof
  Induct \\ simp [ELIM_UNCURRY, FORALL_PROD]
QED

Theorem UNZIP_ind:
  ∀P. (∀v. (∀x4 x3. v = x4::x3 ⇒ ∀x2 x1. x4 = (x2,x1) ⇒ P x3) ⇒ P v) ⇒ ∀v. P v
Proof
  simp [FORALL_PROD]
  \\ gen_tac \\ strip_tac
  \\ Induct \\ rw []
QED

val result = translate UNZIP_eq;

val result = translate (PAD_RIGHT |> REWRITE_RULE [GSYM sub_check_def]);
val result = translate (PAD_LEFT |> REWRITE_RULE [GSYM sub_check_def]);
val result = translate (ALL_DISTINCT |> REWRITE_RULE [MEMBER_INTRO]);
val _ = next_ml_names := ["isPrefix"];
val result = translate isPREFIX;
val result = translate FRONT_DEF;

val _ = next_ml_names := ["splitAtPki"];
val result = translate (splitAtPki_def |> REWRITE_RULE [SUC_LEMMA])

Theorem SPLITP_alt[local]:
  SPLITP P [] = ([],[]) ∧
  SPLITP P (x::l) =
  if P x then ([],x::l) else
    let (l',l'') = SPLITP P l in
      (x::l',l'')
Proof
  rw[rich_listTheory.SPLITP,pairTheory.ELIM_UNCURRY]
QED
val _ = next_ml_names := ["split"];
val result = translate SPLITP_alt

val last_side_def = Q.prove(
  `!xs. last_side xs = ~(xs = [])`,
  Induct THEN ONCE_REWRITE_TAC [fetch "-" "last_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

val nth_side_def = Q.prove(
  `!n xs. nth_side xs n = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "nth_side_def"]
  THEN fs[CONTAINER_def])
  |> update_precondition;

Theorem LUPDATE_ind:
  ∀P. (∀e n. P e n []) ∧ (∀e n x xs. (∀e n. P e n xs) ⇒ P e n (x::xs)) ⇒ ∀e n xs. P e n xs
Proof
  ntac 2 strip_tac \\ Induct_on ‘xs’ \\ fs []
QED

Theorem LUPDATE_eq:
  LUPDATE e n xs =
    case xs of
    | [] => []
    | y::ys => if n = 0 then e :: ys else y :: LUPDATE e (n-1) ys
Proof
  Cases_on ‘xs’ \\ fs [LUPDATE_DEF,PRE_SUB1]
QED

val _ = next_ml_names := ["update"];
val result = translate LUPDATE_eq;

val _ = (next_ml_names := ["compare"]);
val _ = translate mllistTheory.list_compare_def;

val _ = ml_prog_update open_local_block;

val result = translate sort2_tail_def;
val result = translate sort3_tail_def;
val result = translate REV_DEF;
val result = translate merge_tail_def;
val result = translate DIV2_def;
val result = translate DROP_def;
val result = translate_no_ind mergesortN_tail_def;

Theorem mergesortn_tail_ind[local]:
  mergesortn_tail_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "mergesortn_tail_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, DIV2_def]
QED

val result = mergesortn_tail_ind |> update_precondition;

Theorem mergesortn_tail_side[local]:
  !w x y z. mergesortn_tail_side w x y z
Proof
  completeInduct_on `y`
  \\ once_rewrite_tac[(fetch "-" "mergesortn_tail_side_def")]
  \\ rpt gen_tac \\ rename1 `SUC x1`
  \\ rw[DIV2_def]
     >- (
        first_x_assum match_mp_tac
        \\ fs[]
        \\ qspecl_then [`2`,`SUC x1`] assume_tac dividesTheory.DIV_POS
        \\ gvs[]
      )
     >- (
        qspecl_then [`SUC x1`, `2`] assume_tac arithmeticTheory.DIV_LESS
        \\ `0 < SUC x1` by fs[]
        \\ `SUC x1 DIV 2 < SUC x1` suffices_by rw[]
        \\ first_x_assum match_mp_tac
        \\ fs[]
      )
QED

val result = mergesortn_tail_side |> update_precondition;
val result = translate mergesort_tail_def

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["sort"];

val result = translate sort_def;

val _ =  ml_prog_update close_local_blocks;
val _ =  ml_prog_update (close_module NONE);

(* finite maps -- depend on lists *)

val _ = ml_prog_update (open_module "Alist");

Definition FMAP_EQ_ALIST_def:
  FMAP_EQ_ALIST f l <=> (ALOOKUP l = FLOOKUP f)
End

Definition FMAP_TYPE_def:
  FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) (f:'a|->'b) =
    \v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ FMAP_EQ_ALIST f l
End

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
Definition AUPDATE_def:
  AUPDATE l (x:'a,y:'b) = (x,y)::l
End
val AUPDATE_eval = translate AUPDATE_def;

Theorem FMAP_EQ_ALIST_UPDATE[local]:
  FMAP_EQ_ALIST f l ==> FMAP_EQ_ALIST (FUPDATE f (x,y)) (AUPDATE l (x,y))
Proof
  SIMP_TAC (srw_ss()) [FMAP_EQ_ALIST_def,AUPDATE_def,ALOOKUP_def,FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FAPPLY_FUPDATE_THM]
  THEN METIS_TAC []
QED

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

Definition AEVERY_AUX_def:
  (AEVERY_AUX aux P [] = T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) =
     if MEMBER x aux then AEVERY_AUX aux P xs else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)
End
Definition AEVERY_def:
  AEVERY = AEVERY_AUX []
End
val _ = next_ml_names := ["every","every"];
val _ = translate AEVERY_AUX_def;
val AEVERY_eval = translate AEVERY_def;

Theorem AEVERY_AUX_THM[local]:
  !l aux P. AEVERY_AUX aux P l <=>
              !x y. (ALOOKUP l x = SOME y) /\ ~(MEM x aux) ==> P (x,y)
Proof
  Induct
  THEN FULL_SIMP_TAC std_ss [ALOOKUP_def,AEVERY_AUX_def,FORALL_PROD,
    MEM,GSYM MEMBER_INTRO] THEN REPEAT STRIP_TAC
  THEN SRW_TAC [] [] THEN METIS_TAC [SOME_11]
QED

Theorem AEVERY_THM[local]:
  AEVERY P l <=> !x y. (ALOOKUP l x = SOME y) ==> P (x,y)
Proof
  SIMP_TAC (srw_ss()) [AEVERY_def,AEVERY_AUX_THM]
QED

Theorem AEVERY_EQ_FEVERY[local]:
  FMAP_EQ_ALIST f l ==> (AEVERY P l <=> FEVERY P f)
Proof
  FULL_SIMP_TAC std_ss [FMAP_EQ_ALIST_def,FEVERY_DEF,AEVERY_THM]
  THEN FULL_SIMP_TAC std_ss [FLOOKUP_DEF]
QED

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
Definition AMAP_def:
  (AMAP f [] = []) /\
  (AMAP f ((x:'a,y:'b)::xs) = (x,(f y):'c) :: AMAP f xs)
End
val AMAP_eval = translate AMAP_def;

Theorem ALOOKUP_AMAP[local]:
  !l. ALOOKUP (AMAP f l) a =
        case ALOOKUP l a of NONE => NONE | SOME x => SOME (f x)
Proof
  Induct THEN SIMP_TAC std_ss [AMAP_def,ALOOKUP_def,FORALL_PROD]
  THEN SRW_TAC [] []
QED

Theorem FMAP_EQ_ALIST_o_f[local]:
  FMAP_EQ_ALIST m l ==> FMAP_EQ_ALIST (x o_f m) (AMAP x l)
Proof
  SIMP_TAC std_ss [FMAP_EQ_ALIST_def,FUN_EQ_THM,FLOOKUP_DEF,
    o_f_DEF,ALOOKUP_AMAP] THEN REPEAT STRIP_TAC THEN SRW_TAC [] []
QED

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
Definition ADEL_def:
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)
End
val ADEL_eval = translate ADEL_def;

Theorem ALOOKUP_ADEL[local]:
  !l a x. ALOOKUP (ADEL l a) x = if x = a then NONE else ALOOKUP l x
Proof
  Induct THEN SRW_TAC [] [ALOOKUP_def,ADEL_def] THEN Cases_on `h`
  THEN SRW_TAC [] [ALOOKUP_def,ADEL_def]
QED

Theorem FMAP_EQ_ALIST_ADEL[local]:
  !x l. FMAP_EQ_ALIST x l ==>
          FMAP_EQ_ALIST (x \\ a) (ADEL l a)
Proof
  FULL_SIMP_TAC std_ss [FMAP_EQ_ALIST_def,ALOOKUP_def,fmap_domsub,FUN_EQ_THM]
  THEN REPEAT STRIP_TAC THEN SRW_TAC [] [ALOOKUP_ADEL,FLOOKUP_DEF,DRESTRICT_DEF]
  THEN FULL_SIMP_TAC std_ss []
QED

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
