(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)
open HolKernel bossLib boolLib boolSimps lcsymtacs Parse libTheory
open optionTheory combinTheory dep_rewrite listTheory pred_setTheory finite_mapTheory alistTheory rich_listTheory llistTheory arithmeticTheory pairTheory sortingTheory relationTheory totoTheory comparisonTheory bitTheory sptreeTheory wordsTheory wordsLib set_sepTheory indexedListsTheory stringTheory ASCIInumbersLib machine_ieeeTheory

(* Misc. lemmas (without any compiler constants) *)
val _ = new_theory "misc"
val _ = ParseExtras.tight_equality()

(* Note: This globally hides constants over the reals that gets imported through machine_ieeeTheory *)

val _ = remove_ovl_mapping "exp" {Name="exp", Thy="transc"}
val _ = remove_ovl_mapping "max" {Name="max", Thy="real"}
val _ = remove_ovl_mapping "min" {Name="min", Thy="real"}
val _ = remove_ovl_mapping "pos" {Name="pos", Thy="real"}
val _ = remove_ovl_mapping "abs" {Name="abs", Thy="real"}
val _ = remove_ovl_mapping "inf" {Name="inf", Thy="real"}
val _ = remove_ovl_mapping "lim" {Name="lim", Thy="seq"}
val _ = remove_ovl_mapping "ln" {Name="ln", Thy="transc"}

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))
val rveq = rpt BasicProvers.VAR_EQ_TAC
(* -- *)

(* TODO: move/categorize *)

val _ = numLib.prefer_num();

val IMP_IMP = save_thm("IMP_IMP",METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``);

val SUBSET_IMP = Q.store_thm("SUBSET_IMP",
  `s SUBSET t ==> (x IN s ==> x IN t)`,
  fs[pred_setTheory.SUBSET_DEF]);

val safeTL_def = Define`safeTL [] = [] ∧ safeTL (h::t) = t`

val revdroprev = Q.store_thm("revdroprev",
  `∀l n.
     n ≤ LENGTH l ⇒ (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l)`,
  ho_match_mp_tac listTheory.SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `n ≤ SUC (LENGTH l)` >>
  `n = 0 ∨ ∃m. n = SUC m` by (Cases_on `n` >> simp[]) >> simp[]
  >- simp[TAKE_APPEND2] >>
  simp[TAKE_APPEND1] >>
  `LENGTH l + 1 - SUC m = LENGTH l - m`
     suffices_by (disch_then SUBST_ALL_TAC >> simp[]) >>
  simp[]);

val revtakerev = Q.store_thm("revtakerev",
  `∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l`,
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]);

val times_add_o = Q.store_thm("times_add_o",
  `(λn:num. k * n + x) = ($+ x) o ($* k)`,
  rw[FUN_EQ_THM]);

val SORTED_inv_image_LESS_PLUS = Q.store_thm("SORTED_inv_image_LESS_PLUS",
  `SORTED (inv_image $< (arithmetic$+ k)) = SORTED $<`,
  simp[FUN_EQ_THM]
  \\ Induct
  \\ Q.ISPEC_THEN`$+ k`(fn th => simp[MATCH_MP SORTED_EQ th])
      (MATCH_MP transitive_inv_image transitive_LESS)
  \\ simp[MATCH_MP SORTED_EQ transitive_LESS]);

val SORTED_GENLIST_TIMES = Q.store_thm("SORTED_GENLIST_TIMES",
  `0 < k ⇒ ∀n. SORTED prim_rec$< (GENLIST ($* k) n)`,
  strip_tac
  \\ Induct \\ simp[GENLIST,SNOC_APPEND]
  \\ match_mp_tac SORTED_APPEND
  \\ simp[MEM_GENLIST,PULL_EXISTS]);

val read_bytearray_def = Define `
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))`

val read_bytearray_LENGTH = Q.store_thm("read_bytearray_LENGTH",
  `!n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)`,
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac);

val shift_seq_def = Define `
  shift_seq k s = \i. s (i + k:num)`;

val SUM_SET_IN_LT = Q.store_thm("SUM_SET_IN_LT",
  `!s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s`,
  metis_tac[SUM_SET_IN_LE,LESS_LESS_EQ_TRANS]);

val BIJ_support = Q.store_thm("BIJ_support",
  `∀f s' s. BIJ f s' s' ∧ s' ⊆ s ∧ (∀x. x ∉ s' ⇒ f x = x) ⇒ BIJ f s s`,
  rw[BIJ_IFF_INV,SUBSET_DEF]
  >- metis_tac[]
  \\ qexists_tac`λx. if x ∈ s' then g x else x`
  \\ rw[] \\ metis_tac[]);

val CARD_IMAGE_ID_BIJ = Q.store_thm("CARD_IMAGE_ID_BIJ",
  `∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s`,
  rw[]
  \\ `SURJ f s s` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
  \\ `IMAGE f s ⊆ s` by metis_tac[SUBSET_DEF,IN_IMAGE]
  \\ metis_tac[SUBSET_EQ_CARD,IMAGE_FINITE]);

val CARD_IMAGE_EQ_BIJ = Q.store_thm("CARD_IMAGE_EQ_BIJ",
  `∀s. FINITE s ⇒ CARD (IMAGE f s) = CARD s ⇒ BIJ f s (IMAGE f s)`,
  rw[]
  \\ `SURJ f s (IMAGE f s)` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]);

val ALOOKUP_MAP_gen = Q.store_thm("ALOOKUP_MAP_gen",
  `∀f al x.
    ALOOKUP (MAP (λ(x,y). (x,f x y)) al) x =
    OPTION_MAP (f x) (ALOOKUP al x)`,
  gen_tac >> Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][]);

val map_fromAList = Q.store_thm("map_fromAList",
  `map f (fromAList ls) = fromAList (MAP (λ(k,v). (k, f v)) ls)`,
  Induct_on`ls` >> simp[fromAList_def] >>
  Cases >> simp[fromAList_def] >>
  simp[wf_fromAList,map_insert])

val _ = overload_on ("LLOOKUP", “λl n. oEL n l”)
val LLOOKUP_def      = save_thm("LLOOKUP_def", listTheory.oEL_def);
val LLOOKUP_EQ_EL    = save_thm("LLOOKUP_EQ_EL", listTheory.oEL_EQ_EL);
val LLOOKUP_THM      = save_thm("LLOOKUP_THM", listTheory.oEL_THM);
val LLOOOKUP_DROP    = save_thm("LLOOKUP_DROP", listTheory.oEL_DROP);
val LLOOKUP_TAKE_IMP = save_thm("LLOOKUP_TAKE_IMP", listTheory.oEL_TAKE_E);
val LLOOKUP_LUPDATE  = save_thm("LLOOKUP_LUPDATE", listTheory.oEL_LUPDATE);

val _ = Datatype `
  app_list = List ('a list) | Append app_list app_list | Nil`

val append_aux_def = Define `
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))`;

val append_def = Define `
  append l = append_aux l []`;

val append_aux_thm = Q.store_thm("append_aux_thm",
  `!l xs. append_aux l xs = append_aux l [] ++ xs`,
  Induct \\ metis_tac [APPEND,APPEND_ASSOC,append_aux_def]);

val append_thm = Q.store_thm("append_thm[simp]",
  `append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []`,
  fs [append_def,append_aux_def]
  \\ once_rewrite_tac [append_aux_thm] \\ fs []);

val SmartAppend_def = Define`
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)`;
val _ = export_rewrites["SmartAppend_def"];

val SmartAppend_thm = Q.store_thm("SmartAppend_thm",
  `∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2`,
  Cases \\ Cases \\ rw[]);

val append_SmartAppend = Q.store_thm("append_SmartAppend[simp]",
  `append (SmartAppend l1 l2) = append l1 ++ append l2`,
  rw[append_def,SmartAppend_thm,append_aux_def]
  \\ rw[Once append_aux_thm]);

val GENLIST_eq_MAP = Q.store_thm("GENLIST_eq_MAP",
  `GENLIST f n = MAP g ls ⇔
   LENGTH ls = n ∧ ∀m. m < n ⇒ f m = g (EL m ls)`,
  srw_tac[][LIST_EQ_REWRITE,EQ_IMP_THM,EL_MAP])

val GENLIST_ID = Q.store_thm("GENLIST_ID",
  `!x. GENLIST (\i. EL i x) (LENGTH x) = x`,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ full_simp_tac(srw_ss())[] \\ simp_tac std_ss [GENLIST,GSYM ADD1]
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,rich_listTheory.EL_LENGTH_APPEND]
  \\ rpt strip_tac \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp_tac std_ss [Once (GSYM th)])
  \\ full_simp_tac(srw_ss())[GENLIST_FUN_EQ] \\ srw_tac[][]
  \\ match_mp_tac (GSYM rich_listTheory.EL_APPEND1) \\ full_simp_tac(srw_ss())[]);

val ZIP_GENLIST1 = Q.store_thm("ZIP_GENLIST1",
  `∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n`,
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]);

val MAP3_def = Define`
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)`;
val _ = export_rewrites["MAP3_def"];

val MAP3_ind = theorem"MAP3_ind";

val LENGTH_MAP3 = Q.store_thm("LENGTH_MAP3[simp]",
  `∀f l1 l2 l3. LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3 ⇒ LENGTH (MAP3 f l1 l2 l3) = LENGTH l3`,
  ho_match_mp_tac MAP3_ind \\ rw[]);

val EL_MAP3 = Q.store_thm("EL_MAP3",
  `∀f l1 l2 l3 n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ n < LENGTH l3 ⇒
    EL n (MAP3 f l1 l2 l3) = f (EL n l1) (EL n l2) (EL n l3)`,
  ho_match_mp_tac MAP3_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]);

val MAP_REVERSE_STEP = Q.store_thm("MAP_REVERSE_STEP",
  `∀x f. x ≠ [] ⇒ MAP f (REVERSE x) = f (LAST x) :: MAP f (REVERSE (FRONT x))`,
  recInduct SNOC_INDUCT
  \\ rw [FRONT_APPEND]);

val LENGTH_TAKE_EQ_MIN = Q.store_thm("LENGTH_TAKE_EQ_MIN",
  `!n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)`,
  simp[LENGTH_TAKE_EQ] \\ full_simp_tac(srw_ss())[MIN_DEF] \\ decide_tac);

val hd_drop = Q.store_thm ("hd_drop",
  `!n l. n < LENGTH l ⇒ HD (DROP n l) = EL n l`,
  Induct_on `l` >>
  srw_tac[][DROP_def] >>
  `n - 1 < LENGTH l` by decide_tac >>
  res_tac >>
  `0 < n` by decide_tac >>
  srw_tac[][EL_CONS] >>
  `n - 1 = PRE n` by decide_tac >>
  srw_tac[][]);

val INJ_EXTEND = Q.store_thm("INJ_EXTEND",
  `INJ b s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) b) (x INSERT s) (y INSERT t)`,
  full_simp_tac(srw_ss())[INJ_DEF,combinTheory.APPLY_UPDATE_THM] \\ METIS_TAC []);

val MEM_LIST_REL = Q.store_thm("MEM_LIST_REL",
  `!xs ys P x. LIST_REL P xs ys /\ MEM x xs ==> ?y. MEM y ys /\ P x y`,
  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]);

val LIST_REL_MEM = Q.store_thm("LIST_REL_MEM",
  `!xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys`,
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]);

val LIST_REL_GENLIST_I = Q.store_thm("LIST_REL_GENLIST_I",
  `!xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)`,
  simp[LIST_REL_EL_EQN]);

val LIST_REL_lookup_fromList = Q.store_thm("LIST_REL_lookup_fromList",
  `LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args`,
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]);

val LIST_REL_SNOC = Q.store_thm("LIST_REL_SNOC",
  `(LIST_REL R (SNOC x xs) yys ⇔
      ∃y ys. yys = SNOC y ys ∧ LIST_REL R xs ys ∧ R x y) ∧
   (LIST_REL R xxs (SNOC y ys) ⇔
      ∃x xs. xxs = SNOC x xs ∧ LIST_REL R xs ys ∧ R x y)`,
  simp[EQ_IMP_THM, PULL_EXISTS, SNOC_APPEND] >> rpt strip_tac
  >- (imp_res_tac LIST_REL_SPLIT1 >> fs[])
  >- (imp_res_tac LIST_REL_SPLIT2 >> fs[]));

val LIST_REL_FRONT_LAST = Q.store_thm("LIST_REL_FRONT_LAST",
  `l1 <> [] /\ l2 <> [] ==>
    (LIST_REL A l1 l2 <=>
     LIST_REL A (FRONT l1) (FRONT l2) /\ A (LAST l1) (LAST l2))`,
  map_every
    (fn q => Q.ISPEC_THEN q FULL_STRUCT_CASES_TAC SNOC_CASES >>
             fs[LIST_REL_SNOC])
    [`l1`,`l2`]);

val LIST_REL_APPEND_EQ = Q.store_thm("LIST_REL_APPEND_EQ",
  `LENGTH x1 = LENGTH x2 ⇒
   (LIST_REL R (x1 ++ y1) (x2 ++ y2) <=> LIST_REL R x1 x2 /\ LIST_REL R y1 y2)`,
  metis_tac[LIST_REL_APPEND_IMP, EVERY2_LENGTH, EVERY2_APPEND_suff]);

val lookup_fromList_outside = Q.store_thm("lookup_fromList_outside",
  `!k. LENGTH args <= k ==> (lookup k (fromList args) = NONE)`,
  SIMP_TAC std_ss [lookup_fromList] \\ DECIDE_TAC);

val lemmas = Q.prove(
  `(2 + 2 * n - 1 = 2 * n + 1:num) /\
    (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'':num) /\
    (2 * m = 2 * n <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)`,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  THEN1 DECIDE_TAC
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 2 = n MOD 2)``)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 2:num``)]
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[MOD_EQ_0,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

val IN_domain = Q.store_thm("IN_domain",
  `!n x t1 t2.
      (n IN domain LN <=> F) /\
      (n IN domain (LS x) <=> (n = 0)) /\
      (n IN domain (BN t1 t2) <=>
         n <> 0 /\ (if EVEN n then ((n-1) DIV 2) IN domain t1
                              else ((n-1) DIV 2) IN domain t2)) /\
      (n IN domain (BS t1 x t2) <=>
         n = 0 \/ (if EVEN n then ((n-1) DIV 2) IN domain t1
                             else ((n-1) DIV 2) IN domain t2))`,
  full_simp_tac(srw_ss())[domain_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `n = 0` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `EVEN n` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM ODD_EVEN]
  \\ IMP_RES_TAC EVEN_ODD_EXISTS
  \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[lemmas]
  \\ Cases_on `m` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[lemmas])

val map_map_K = Q.store_thm("map_map_K",
  `!t. map (K a) (map (K a) t) = map (K a) t`,
  Induct \\ full_simp_tac(srw_ss())[map_def]);

val lookup_map_K = Q.store_thm("lookup_map_K",
  `!t n. lookup n (map (K x) t) = if n IN domain t then SOME x else NONE`,
  Induct \\ full_simp_tac(srw_ss())[IN_domain,map_def,lookup_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = 0` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `EVEN n` \\ full_simp_tac(srw_ss())[]);

val lookup_any_def = Define `
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m`;

val alist_insert_def = Define `
  (alist_insert [] xs t = t) /\
  (alist_insert vs [] t = t) /\
  (alist_insert (v::vs) (x::xs) t = insert v x (alist_insert vs xs t))`

val lookup_alist_insert = Q.store_thm("lookup_alist_insert",
  `!x y t z. LENGTH x = LENGTH y ==>
    (lookup z (alist_insert x y t) =
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)`,
    ho_match_mp_tac (fetch "-" "alist_insert_ind")>>
    srw_tac[][]>-
      (full_simp_tac(srw_ss())[LENGTH,alist_insert_def]) >>
    Cases_on`z=x`>>
      srw_tac[][lookup_def,alist_insert_def]>>
    full_simp_tac(srw_ss())[lookup_insert])

val domain_alist_insert = Q.store_thm("domain_alist_insert",
  `!a b locs. LENGTH a = LENGTH b ==>
    domain (alist_insert a b locs) = domain locs UNION set a`,
  Induct_on`a`>>Cases_on`b`>>full_simp_tac(srw_ss())[alist_insert_def]>>srw_tac[][]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM])

val fromList2_def = Define `
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)`

val EVEN_fromList2_lemma = Q.prove(
  `!l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x`,
  Induct \\ full_simp_tac(srw_ss())[FOLDL] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC);

val EVEN_fromList2 = Q.store_thm("EVEN_fromList2",
  `!l n. n IN domain (fromList2 l) ==> EVEN n`,
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ full_simp_tac(srw_ss())[]);

val SUBMAP_FDOM_SUBSET = Q.store_thm("SUBMAP_FDOM_SUBSET",
  `f1 ⊑ f2 ⇒ FDOM f1 ⊆ FDOM f2`,
  srw_tac[][SUBMAP_DEF,SUBSET_DEF])

val SUBMAP_FRANGE_SUBSET = Q.store_thm("SUBMAP_FRANGE_SUBSET",
  `f1 ⊑ f2 ⇒ FRANGE f1 ⊆ FRANGE f2`,
  srw_tac[][SUBMAP_DEF,SUBSET_DEF,IN_FRANGE] >> metis_tac[])

val FDIFF_def = Define `
  FDIFF f1 s = DRESTRICT f1 (COMPL s)`;

val FDOM_FDIFF = Q.store_thm("FDOM_FDIFF",
  `x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN f2)`,
  full_simp_tac(srw_ss())[FDIFF_def,DRESTRICT_DEF]);

val INJ_FAPPLY_FUPDATE = Q.store_thm("INJ_FAPPLY_FUPDATE",
  `INJ ($' f) (FDOM f) (FRANGE f) ∧
   s = k INSERT FDOM f ∧ v ∉ FRANGE f ∧
   t = v INSERT FRANGE f
  ⇒
   INJ ($' (f |+ (k,v))) s t`,
  srw_tac[][INJ_DEF,FAPPLY_FUPDATE_THM] >> srw_tac[][] >>
  pop_assum mp_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[IN_FRANGE] >>
  METIS_TAC[])

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]
  |> curry save_thm "NUM_NOT_IN_FDOM";

val EXISTS_NOT_IN_FDOM_LEMMA = Q.prove(
  `?x. ~(x IN FDOM (refs:num|->'a))`,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NOTIN_FDOM = Q.store_thm("LEAST_NOTIN_FDOM",
  `(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs`,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ full_simp_tac(srw_ss())[]);

val LEAST_LESS_EQ = Q.store_thm("LEAST_LESS_EQ",
  `(LEAST x. y ≤ x) = y`,
  numLib.LEAST_ELIM_TAC \\ rw[]
  >- (qexists_tac`y` \\ simp[])
  \\ fs[LESS_OR_EQ] \\ res_tac \\ fs[]);

val list_to_num_set_def = Define `
  (list_to_num_set [] = LN) /\
  (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))`;

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

val domain_list_to_num_set = Q.store_thm("domain_list_to_num_set",
  `!xs. x IN domain (list_to_num_set xs) <=> MEM x xs`,
  Induct \\ full_simp_tac(srw_ss())[list_to_num_set_def]);

val domain_list_insert = Q.store_thm("domain_list_insert",
  `!xs x t.
      x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t`,
  Induct \\ full_simp_tac(srw_ss())[list_insert_def] \\ METIS_TAC []);

val domain_FOLDR_delete = Q.store_thm("domain_FOLDR_delete",
  `∀ls live. domain (FOLDR delete live ls) =
  (domain live) DIFF (set ls)`,
  Induct>>
  full_simp_tac(srw_ss())[DIFF_INSERT,EXTENSION]>>
  metis_tac[])

val lookup_list_to_num_set = Q.store_thm("lookup_list_to_num_set",
  `!xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME () else NONE`,
  Induct \\ srw_tac [] [list_to_num_set_def,lookup_def,lookup_insert] \\ full_simp_tac(srw_ss())[]);

val OPTION_BIND_SOME = Q.store_thm("OPTION_BIND_SOME",
  `∀f. OPTION_BIND f SOME = f`,
  Cases >> simp[])

val take1 = Q.store_thm ("take1",
  `!l. l ≠ [] ⇒ TAKE 1 l = [EL 0 l]`,
  Induct_on `l` >> srw_tac[][]);

val take1_drop = Q.store_thm (
  "take1_drop",
  `!n l. n < LENGTH l ==> (TAKE 1 (DROP n l) = [EL n l])`,
  Induct_on `l` \\ rw[] \\
  Cases_on `n` \\ rw[EL_restricted]
);

val SPLIT_LIST = Q.store_thm("SPLIT_LIST",
  `!xs.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)`,
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ full_simp_tac(srw_ss())[DIV_LE_X] \\ DECIDE_TAC);

val EXISTS_ZIP = Q.store_thm ("EXISTS_ZIP",
  `!l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)`,
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []);

val EVERY_ZIP = Q.store_thm ("EVERY_ZIP",
  `!l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)`,
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []);

val ZIP_MAP_FST_SND_EQ = Q.store_thm("ZIP_MAP_FST_SND_EQ",
  `∀ls. ZIP (MAP FST ls,MAP SND ls) = ls`,
  Induct>>full_simp_tac(srw_ss())[])

val zlookup_def = Define `
  zlookup m k = case lookup k m of NONE => 0n | SOME k => k`;

val tlookup_def = Define `
  tlookup m k = case lookup k m of NONE => k | SOME k => k`;

val tlookup_id = Q.store_thm("tlookup_id",
  `x ∉ domain names
   ⇒ tlookup names x = x`,
  rw[tlookup_def]
  \\ fs[domain_lookup] \\ CASE_TAC \\ fs[]);

val tlookup_bij_suff = Q.store_thm("tlookup_bij_suff",
  `set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV`,
  strip_tac
  \\ match_mp_tac BIJ_support
  \\ qexists_tac`domain names`
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[tlookup_def]
    \\ CASE_TAC \\ fs[domain_lookup])
  \\ `set (toList names) = IMAGE (tlookup names) (domain names)`
  by (
    pop_assum kall_tac
    \\ simp[EXTENSION,tlookup_def,MEM_toList,domain_lookup]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (qexists_tac`k` \\ fs[])
    \\ metis_tac[] )
  \\ match_mp_tac (MP_CANON CARD_IMAGE_ID_BIJ)
  \\ fs[] \\ rw[] \\ fs[EXTENSION]
  \\ metis_tac[]);

val tlookup_bij_iff = Q.store_thm("tlookup_bij_iff",
  `BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names`,
  rw[EQ_IMP_THM,tlookup_bij_suff]
  \\ fs[BIJ_IFF_INV]
  \\ rw[EXTENSION,domain_lookup,MEM_toList]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`k=x` >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ `tlookup names x = x`
    by (
      simp[tlookup_def]
      \\ CASE_TAC \\ fs[] )
    \\ `tlookup names k = x`
    by ( simp[tlookup_def] )
    \\ metis_tac[] )
  \\ Cases_on`x=v` >- metis_tac[]
  \\ spose_not_then strip_assume_tac
  \\ `tlookup names x = v`
  by ( simp[tlookup_def] )
  \\ `∀k. tlookup names k ≠ x`
  by (
    rw[tlookup_def]
    \\ CASE_TAC \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[])
  \\ metis_tac[] )

val any_el_def = Define `
  (any_el n [] d = d) /\
  (any_el n (x::xs) d = if n = 0 then x else any_el (n-1:num) xs d)`

val list_max_def = Define `
  (list_max [] = 0:num) /\
  (list_max (x::xs) =
     let m = list_max xs in
       if m < x then x else m)`

val list_max_max = Q.store_thm("list_max_max",
  `∀ls.  EVERY (λx. x ≤ list_max ls) ls`,
  Induct>>full_simp_tac(srw_ss())[list_max_def,LET_THM]>>srw_tac[][]>>full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>
  res_tac >> decide_tac);

val list_max_intro = Q.store_thm("list_max_intro",`
  ∀ls.
  P 0 ∧ EVERY P ls ⇒ P (list_max ls)`,
  Induct>>full_simp_tac(srw_ss())[list_max_def]>>srw_tac[][]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]);

val list_inter_def = Define `
  list_inter xs ys = FILTER (\y. MEM y xs) ys`;

val max3_def = Define`
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)`
val _ = export_rewrites["max3_def"];

val SING_HD = Q.store_thm("SING_HD",
  `(([HD xs] = xs) <=> (LENGTH xs = 1)) /\
    ((xs = [HD xs]) <=> (LENGTH xs = 1))`,
  Cases_on `xs` \\ full_simp_tac(srw_ss())[LENGTH_NIL] \\ METIS_TAC []);

val ALOOKUP_SNOC = Q.store_thm("ALOOKUP_SNOC",
  `∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE`,
  Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][])

val ALOOKUP_GENLIST = Q.store_thm("ALOOKUP_GENLIST",
  `∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE`,
  gen_tac >> Induct >> simp[GENLIST] >> srw_tac[][] >> full_simp_tac(srw_ss())[ALOOKUP_SNOC] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][])

val ALOOKUP_ZIP_FAIL = Q.store_thm("ALOOKUP_ZIP_FAIL",
  `∀A B x.
  LENGTH A = LENGTH B ⇒
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)`,
  srw_tac[][]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  full_simp_tac(srw_ss())[MAP_ZIP])

val anub_def = Define`
  (anub [] acc = []) ∧
  (anub ((k,v)::ls) acc =
   if MEM k acc then anub ls acc else
   (k,v)::(anub ls (k::acc)))`

val anub_ind = theorem"anub_ind"

val EVERY_anub_imp = Q.store_thm("EVERY_anub_imp",
  `∀ls acc x y.
      EVERY P (anub ((x,y)::ls) acc) ∧ x ∉ set acc
      ⇒
      P (x,y) ∧ EVERY P (anub ls (x::acc))`,
  ho_match_mp_tac anub_ind >> srw_tac[][anub_def] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD])

val ALOOKUP_anub = Q.store_thm("ALOOKUP_anub",
  `ALOOKUP (anub ls acc) k =
    if MEM k acc then ALOOKUP (anub ls acc) k
    else ALOOKUP ls k`,
  qid_spec_tac`acc` >>
  Induct_on`ls` >>
  srw_tac[][anub_def] >>
  Cases_on`h`>>srw_tac[][anub_def]>>full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`acc`mp_tac) >>
    srw_tac[][] ) >>
  first_x_assum(qspec_then`q::acc`mp_tac) >>
  srw_tac[][])

val anub_eq_nil = Q.store_thm("anub_eq_nil",
  `anub x y = [] ⇔ EVERY (combin$C MEM y) (MAP FST x)`,
  qid_spec_tac`y` >>
  Induct_on`x`>>srw_tac[][anub_def]>>
  Cases_on`h`>>srw_tac[][anub_def])

val EVERY_anub_suff = Q.store_thm("EVERY_anub_suff",
  `∀ls acc.
    (∀x. ¬MEM x acc ⇒ case ALOOKUP ls x of SOME v => P (x,v) | NONE => T)
    ⇒ EVERY P (anub ls acc)`,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >- (
    first_x_assum(match_mp_tac) >>
    srw_tac[][] >>
    res_tac >>
    pop_assum mp_tac >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] )
  >- (
    res_tac >> full_simp_tac(srw_ss())[] ) >>
  first_x_assum match_mp_tac >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  `q ≠ x` by full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[])

val anub_notin_acc = Q.store_thm("anub_notin_acc",
  `∀ls acc. MEM x acc ⇒ ¬MEM x (MAP FST (anub ls acc))`,
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >>
  metis_tac[])

val anub_tl_anub = Q.store_thm("anub_tl_anub",
  `∀x y h t. anub x y = h::t ⇒ ∃a b. t = anub a b ∧ set a ⊆ set x ∧ set b ⊆ set ((FST h)::y)`,
  Induct >> srw_tac[][anub_def] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[anub_def] >>
  pop_assum mp_tac  >> srw_tac[][] >>
  res_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac[MEM] )

val anub_all_distinct_keys = Q.store_thm("anub_all_distinct_keys",
  `∀ls acc.
    ALL_DISTINCT acc ⇒
    ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)`,
  Induct>>srw_tac[][anub_def]>>PairCases_on`h`>>full_simp_tac(srw_ss())[anub_def]>>
  srw_tac[][]>>
  `ALL_DISTINCT (h0::acc)` by full_simp_tac(srw_ss())[ALL_DISTINCT]>>res_tac>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND]>>
  metis_tac[])

val MEM_anub_ALOOKUP = Q.store_thm("MEM_anub_ALOOKUP",
  `MEM (k,v) (anub ls []) ⇒
    ALOOKUP ls k = SOME v`,
  srw_tac[][]>>
  Q.ISPECL_THEN[`ls`,`[]`] assume_tac anub_all_distinct_keys>>
  Q.ISPECL_THEN [`ls`,`k`,`[]`] assume_tac (GEN_ALL ALOOKUP_anub)>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM])

val FEMPTY_FUPDATE_EQ = Q.store_thm("FEMPTY_FUPDATE_EQ",
  `∀x y. (FEMPTY |+ x = FEMPTY |+ y) ⇔ (x = y)`,
  Cases >> Cases >> srw_tac[][fmap_eq_flookup,FDOM_FUPDATE,FLOOKUP_UPDATE] >>
  Cases_on`q=q'`>>srw_tac[][] >- (
    srw_tac[][EQ_IMP_THM] >>
    pop_assum(qspec_then`q`mp_tac) >> srw_tac[][] ) >>
  qexists_tac`q`>>srw_tac[][])

val FUPDATE_LIST_EQ_FEMPTY = Q.store_thm("FUPDATE_LIST_EQ_FEMPTY",
  `∀fm ls. fm |++ ls = FEMPTY ⇔ fm = FEMPTY ∧ ls = []`,
  srw_tac[][EQ_IMP_THM,FUPDATE_LIST_THM] >>
  full_simp_tac(srw_ss())[GSYM fmap_EQ_THM,FDOM_FUPDATE_LIST])

val IS_SOME_EXISTS = Q.store_thm("IS_SOME_EXISTS",
  `∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x`,
  Cases >> simp[])

val _ = type_abbrev("num_set",``:unit spt``);
val _ = type_abbrev("num_map",``:'a spt``);

val toAList_domain = Q.store_thm("toAList_domain",`
  ∀x. MEM x (MAP FST (toAList t)) ⇔ x ∈ domain t`,
  full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup])

val domain_nat_set_from_list = Q.store_thm("domain_nat_set_from_list",
  `∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls`,
  Induct >> simp[sptreeTheory.domain_insert] >>
  srw_tac[][EXTENSION] >> metis_tac[])
val _ = export_rewrites["domain_nat_set_from_list"]

val wf_nat_set_from_list = Q.store_thm("wf_nat_set_from_list",
  `∀ls ns. wf ns ⇒ wf (FOLDL (λs n. insert n z s) ns ls)`,
  Induct >> simp[] >> srw_tac[][sptreeTheory.wf_insert])

val BIT_11 = Q.store_thm("BIT_11",
  `∀n m. (BIT n = BIT m) ⇔ (n = m)`,
  simp[EQ_IMP_THM] >>
  Induct >> simp[BIT0_ODD,FUN_EQ_THM] >- (
    Cases >> simp[] >>
    qexists_tac`1` >> simp[GSYM BIT_DIV2,BIT_ZERO] ) >>
  simp[GSYM BIT_DIV2] >>
  Cases >> simp[GSYM BIT_DIV2] >- (
    qexists_tac`1` >>
    simp[BIT_ZERO] >>
    simp[BIT_def,BITS_THM] ) >>
  srw_tac[][] >>
  first_x_assum MATCH_MP_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  first_x_assum(qspec_then`x*2`mp_tac) >>
  simp[arithmeticTheory.MULT_DIV])

val BIT_11_2 = Q.store_thm("BIT_11_2",
  `∀n m. (∀z. (z < 2 ** (MAX n m)) ⇒ (BIT n z ⇔ BIT m z)) ⇔ (n = m)`,
  simp[Once EQ_IMP_THM] >>
  Induct >- (
    simp[] >>
    Cases >> simp[] >>
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  Cases >> simp[] >- (
    qexists_tac`2 ** SUC n - 1` >>
    simp[BIT_EXP_SUB1] ) >>
  strip_tac >>
  first_x_assum MATCH_MP_TAC >>
  qx_gen_tac`z` >>
  first_x_assum(qspec_then`z*2`mp_tac) >>
  simp[GSYM BIT_DIV2,arithmeticTheory.MULT_DIV] >>
  srw_tac[][] >> first_x_assum MATCH_MP_TAC >>
  full_simp_tac(srw_ss())[arithmeticTheory.MAX_DEF] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  simp[arithmeticTheory.EXP])

val binary_induct = Q.store_thm("binary_induct",
  `∀P. P (0:num) ∧ (∀n. P n ⇒ P (2*n) ∧ P (2*n+1)) ⇒ ∀n. P n`,
  gen_tac >> strip_tac >>
  completeInduct_on`n` >>
  Cases_on`n=0`>>simp[]>>
  `n DIV 2 < n ∧ ((n = 2 * (n DIV 2)) ∨ (n = 2 * (n DIV 2) + 1))` by (
    simp[DIV_MULT_THM2] >>
    `n MOD 2 < 2` by (
      MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
      simp[] ) >>
    simp[] ) >>
  metis_tac[])

val BIT_TIMES2 = Q.store_thm("BIT_TIMES2",
  `BIT z (2 * n) ⇔ 0 < z ∧ BIT (PRE z) n`,
  Cases_on`z`>>simp[]>-(
    simp[BIT0_ODD] >>
    simp[arithmeticTheory.ODD_EVEN] >>
    simp[arithmeticTheory.EVEN_DOUBLE] ) >>
  qmatch_rename_tac`BIT (SUC z) (2 * n) ⇔ BIT z n` >>
  qspecl_then[`z`,`n`,`1`]mp_tac BIT_SHIFT_THM >>
  simp[arithmeticTheory.ADD1])

val BIT_TIMES2_1 = Q.store_thm("BIT_TIMES2_1",
  `∀n z. BIT z (2 * n + 1) ⇔ (z=0) ∨ BIT z (2 * n)`,
  Induct >> simp_tac std_ss [] >- (
    simp_tac std_ss [BIT_ZERO] >>
    Cases_on`z`>>simp_tac std_ss [BIT0_ODD] >>
    simp_tac arith_ss [GSYM BIT_DIV2,BIT_ZERO] ) >>
  Cases >> simp_tac std_ss [BIT0_ODD] >- (
    simp_tac std_ss [arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  simp_tac std_ss [GSYM BIT_DIV2] >>
  qspec_then`2`mp_tac arithmeticTheory.ADD_DIV_RWT >>
  simp[] >>
  disch_then(qspecl_then[`2 * SUC n`,`1`]mp_tac) >>
  simp_tac std_ss [] >>
  simp_tac std_ss [arithmeticTheory.MOD_EQ_0_DIVISOR] >>
  metis_tac[] )

val LOG2_TIMES2 = Q.store_thm("LOG2_TIMES2",
  `0 < n ⇒ (LOG2 (2 * n) = SUC (LOG2 n))`,
  srw_tac[][LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1])

val LOG2_TIMES2_1 = Q.store_thm("LOG2_TIMES2_1",
  `∀n. 0 < n ⇒ (LOG2 (2 * n + 1) = LOG2 (2 * n))`,
  srw_tac[][LOG2_def] >>
  MATCH_MP_TAC logrootTheory.LOG_UNIQUE >>
  simp[GSYM LOG2_def,LOG2_TIMES2] >>
  simp[arithmeticTheory.EXP] >>
  conj_tac >- (
    MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac`2*n` >> simp[] >>
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`2 ** LOG2 n ≤ X` >- srw_tac[][] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] ) >>
  simp[GSYM arithmeticTheory.ADD1] >>
  match_mp_tac arithmeticTheory.LESS_NOT_SUC >>
  `4:num = 2 * 2` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[Once (GSYM arithmeticTheory.MULT_ASSOC)] >>
  simp[] >>
  conj_asm1_tac >- (
    qspec_then`n`mp_tac logrootTheory.LOG_MOD >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`n = X` >>
    qsuff_tac`X < 2 * 2 ** LOG2 n` >- srw_tac[][] >>
    qunabbrev_tac`X` >>
    simp[LOG2_def] >>
    qmatch_abbrev_tac`(a:num) + b < 2 * a` >>
    qsuff_tac`n MOD a < a` >- simp[] >>
    MATCH_MP_TAC arithmeticTheory.MOD_LESS >>
    simp[Abbr`a`] ) >>
  qmatch_abbrev_tac`X ≠ Y` >>
  qsuff_tac`EVEN X ∧ ODD Y` >- metis_tac[arithmeticTheory.EVEN_ODD] >>
  conj_tac >- (
    simp[Abbr`X`,arithmeticTheory.EVEN_EXISTS] >>
    qexists_tac`2 * 2 ** LOG2 n` >>
    simp[] ) >>
  simp[Abbr`Y`,arithmeticTheory.ODD_EXISTS] >>
  metis_tac[])

val C_BIT_11 = Q.store_thm("C_BIT_11",
  `∀n m. (∀z. (z ≤ LOG2 (MAX n m)) ⇒ (BIT z n ⇔ BIT z m)) ⇔ (n = m)`,
  simp_tac std_ss [Once EQ_IMP_THM] >>
  ho_match_mp_tac binary_induct >>
  simp_tac std_ss [] >>
  conj_tac >- (
    Cases >> simp_tac arith_ss [] >>
    qexists_tac`LOG2 (SUC n)` >>
    simp_tac arith_ss [BIT_LOG2,BIT_ZERO] ) >>
  gen_tac >> strip_tac >>
  simp_tac std_ss [BIT_TIMES2,BIT_TIMES2_1] >>
  srw_tac[][] >- (
    Cases_on`n=0`>>full_simp_tac std_ss []>-(
      Cases_on`m=0`>>full_simp_tac std_ss []>>
      first_x_assum(qspec_then`LOG2 m`mp_tac)>>simp_tac std_ss [BIT_ZERO] >>
      full_simp_tac std_ss [BIT_LOG2]) >>
    `¬ODD m` by (
      simp_tac std_ss [SYM BIT0_ODD] >>
      first_x_assum(qspec_then`0`mp_tac) >>
      simp_tac std_ss [] ) >>
    full_simp_tac std_ss [arithmeticTheory.ODD_EVEN] >>
    full_simp_tac std_ss [arithmeticTheory.EVEN_EXISTS] >>
    simp_tac std_ss [arithmeticTheory.EQ_MULT_LCANCEL] >>
    first_x_assum MATCH_MP_TAC >>
    srw_tac[][] >>
    first_x_assum(qspec_then`SUC z`mp_tac) >>
    impl_tac >- (
      full_simp_tac std_ss [arithmeticTheory.MAX_DEF] >>
      srw_tac[][] >> full_simp_tac arith_ss [LOG2_TIMES2] ) >>
    simp_tac std_ss [BIT_TIMES2] ) >>
  Cases_on`n=0`>>full_simp_tac std_ss []>-(
    full_simp_tac std_ss [BIT_ZERO] >>
    Cases_on`m=0`>>full_simp_tac std_ss [BIT_ZERO] >>
    Cases_on`m=1`>>full_simp_tac std_ss []>>
    first_x_assum(qspec_then`LOG2 m`mp_tac) >>
    full_simp_tac std_ss [arithmeticTheory.MAX_DEF,BIT_LOG2] >>
    spose_not_then strip_assume_tac >>
    qspec_then`m`mp_tac logrootTheory.LOG_MOD >>
    full_simp_tac arith_ss [GSYM LOG2_def] ) >>
  `ODD m` by (
    simp_tac std_ss [SYM BIT0_ODD] >>
    first_x_assum(qspec_then`0`mp_tac) >>
    simp_tac std_ss [] ) >>
  full_simp_tac std_ss [arithmeticTheory.ODD_EXISTS,arithmeticTheory.ADD1] >>
  simp_tac std_ss [arithmeticTheory.EQ_MULT_LCANCEL] >>
  first_x_assum MATCH_MP_TAC >>
  srw_tac[][] >>
  first_x_assum(qspec_then`SUC z`mp_tac) >>
  impl_tac >- (
    full_simp_tac std_ss [arithmeticTheory.MAX_DEF] >>
    srw_tac[][] >> full_simp_tac arith_ss [LOG2_TIMES2_1,LOG2_TIMES2] ) >>
  full_simp_tac arith_ss [BIT_TIMES2_1,BIT_TIMES2])

val BIT_num_from_bin_list_leading = Q.store_thm("BIT_num_from_bin_list_leading",
  `∀l x. EVERY ($> 2) l ∧ LENGTH l ≤ x ⇒ ¬BIT x (num_from_bin_list l)`,
  simp[numposrepTheory.num_from_bin_list_def] >>
  srw_tac[][] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH l` >>
  simp[numposrepTheory.l2n_lt] )

val word_bit_test = Q.store_thm("word_bit_test",
  `word_bit n w <=> ((w && n2w (2 ** n)) <> 0w:'a word)`,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
    [wordsTheory.word_index, DECIDE ``0n < d ==> (n <= d - 1) = (n < d)``])

val least_from_def = Define`
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P`

val LEAST_thm = Q.store_thm("LEAST_thm",
  `$LEAST P = least_from P 0`,
  srw_tac[][least_from_def,ETA_AX])

val least_from_thm = Q.store_thm("least_from_thm",
  `least_from P n = if P n then n else least_from P (n+1)`,
  srw_tac[][least_from_def] >>
  numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- metis_tac[] >>
    qmatch_rename_tac`a = b` >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] ))

val FILTER_F = Q.store_thm("FILTER_F",
  `∀ls. FILTER (λx. F) ls = []`,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

val OPTREL_SOME = Q.store_thm("OPTREL_SOME",
  `(!R x y. OPTREL R (SOME x) y <=> (?z. y = SOME z /\ R x z)) /\
    (!R x y. OPTREL R x (SOME y) <=> (?z. x = SOME z /\ R z y))`,
    srw_tac[][optionTheory.OPTREL_def])

val LIST_REL_O = Q.store_thm("LIST_REL_O",
  `∀R1 R2 l1 l2.
     LIST_REL (R1 O R2) l1 l2 ⇔ ∃l3. LIST_REL R2 l1 l3 ∧ LIST_REL R1 l3 l2`,
  rpt gen_tac >>
  simp[EVERY2_EVERY,EVERY_MEM,EQ_IMP_THM,GSYM AND_IMP_INTRO,MEM_ZIP,PULL_EXISTS,
       O_DEF] >>
  srw_tac[][] >- (
    full_simp_tac(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >>
    qexists_tac`GENLIST f (LENGTH l2)` >>
    simp[MEM_ZIP,PULL_EXISTS] ) >>
  metis_tac[])

val OPTREL_O_lemma = Q.prove(
  `∀R1 R2 l1 l2. OPTREL (R1 O R2) l1 l2 ⇔ ∃l3. OPTREL R2 l1 l3 ∧ OPTREL R1 l3 l2`,
  srw_tac[][optionTheory.OPTREL_def,EQ_IMP_THM,O_DEF,PULL_EXISTS] >> metis_tac[])

val OPTREL_O = Q.store_thm("OPTREL_O",
  `∀R1 R2. OPTREL (R1 O R2) = OPTREL R1 O OPTREL R2`,
  srw_tac[][FUN_EQ_THM,OPTREL_O_lemma,O_DEF])

val FUNPOW_mono = Q.store_thm("FUNPOW_mono",
  `(∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y`,
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> srw_tac[][])

val FUNPOW_SUC_PLUS = Q.store_thm("FUNPOW_SUC_PLUS",
  `∀n a. FUNPOW SUC n = (+) n`, Induct \\ simp[FUNPOW,FUN_EQ_THM]);

val OPTREL_trans = Q.store_thm("OPTREL_trans",
  `∀R x y z. (∀a b c. (x = SOME a) ∧ (y = SOME b) ∧ (z = SOME c) ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z`,
  srw_tac[][optionTheory.OPTREL_def])

val UPDATE_LIST_def = Define`
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))`
val _ = Parse.add_infix("=++",500,Parse.LEFT)
val _ = Parse.overload_on("=++",``UPDATE_LIST``)

val UPDATE_LIST_THM = Q.store_thm("UPDATE_LIST_THM",
  `∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)`,
  srw_tac[][UPDATE_LIST_def,pairTheory.UNCURRY])

val APPLY_UPDATE_LIST_ALOOKUP = Q.store_thm("APPLY_UPDATE_LIST_ALOOKUP",
  `∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y`,
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  srw_tac[][] >> BasicProvers.CASE_TAC)

val IS_SUFFIX_CONS = Q.store_thm("IS_SUFFIX_CONS",
  `∀l1 l2 a. IS_SUFFIX l1 l2 ⇒ IS_SUFFIX (a::l1) l2`,
  srw_tac[][rich_listTheory.IS_SUFFIX_APPEND] >>
  qexists_tac`a::l` >>srw_tac[][])

val INFINITE_INJ_NOT_SURJ = Q.store_thm("INFINITE_INJ_NOT_SURJ",
  `∀s. INFINITE s ⇔ (s ≠ ∅) ∧ (∃f. INJ f s s ∧ ¬SURJ f s s)`,
  srw_tac[][EQ_IMP_THM] >- (
    PROVE_TAC[INFINITE_INHAB,MEMBER_NOT_EMPTY] )
  >- (
    full_simp_tac(srw_ss())[infinite_num_inj] >>
    qexists_tac`λx. if ∃n. x = f n then f (SUC (LEAST n. x = f n)) else x` >>
    conj_asm1_tac >- (
      full_simp_tac(srw_ss())[INJ_IFF] >>
      conj_asm1_tac >- srw_tac[][] >>
      srw_tac[][] >- (
        numLib.LEAST_ELIM_TAC >>
        conj_tac >- PROVE_TAC[] >>
        srw_tac[][] ) >>
      numLib.LEAST_ELIM_TAC >>
      srw_tac[][] >>
      metis_tac[] ) >>
    full_simp_tac(srw_ss())[SURJ_DEF,INJ_IFF] >>
    qexists_tac`f 0` >>
    simp[] >>
    srw_tac[][] >>
    metis_tac[]) >>
  full_simp_tac(srw_ss())[SURJ_DEF] >- (full_simp_tac(srw_ss())[INJ_IFF] >> metis_tac[]) >>
  simp[infinite_num_inj] >>
  qexists_tac`λn. FUNPOW f n x` >>
  simp[INJ_IFF] >>
  conj_asm1_tac >- (
    Induct >>
    simp[arithmeticTheory.FUNPOW_SUC] >>
    full_simp_tac(srw_ss())[INJ_IFF] ) >>
  Induct >> simp[] >- (
    Cases >> simp[arithmeticTheory.FUNPOW_SUC] >>
    metis_tac[] ) >>
  Cases >> simp[arithmeticTheory.FUNPOW_SUC] >> full_simp_tac(srw_ss())[INJ_IFF] >>
  metis_tac[] )

val find_index_def = Define`
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))`

val INDEX_FIND_CONS_EQ_SOME = store_thm("INDEX_FIND_CONS_EQ_SOME",
  ``(INDEX_FIND n f (x::xs) = SOME y) <=>
    (f x /\ (y = (n,x))) \/
    (~f x /\ (INDEX_FIND (n+1) f xs = SOME y))``,
  fs [INDEX_FIND_def] \\ rw [] \\ Cases_on `y` \\ fs [ADD1] \\ metis_tac []);

val find_index_INDEX_FIND = Q.store_thm("find_index_INDEX_FIND",
  `∀y xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ($= y) xs)`,
  Induct_on`xs` \\ rw[find_index_def]
  \\ rw[Once INDEX_FIND_def,ADD1]);

val find_index_INDEX_OF = Q.store_thm("find_index_INDEX_OF",
  `find_index y xs 0 = INDEX_OF y xs`,
  rw[INDEX_OF_def,find_index_INDEX_FIND])

val find_index_NOT_MEM = Q.store_thm("find_index_NOT_MEM",
  `∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)`,
  Induct >> srw_tac[][find_index_def])

val find_index_MEM = Q.store_thm("find_index_MEM",
  `!ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)`,
  Induct >> srw_tac[][find_index_def] >- (
    qexists_tac`0`>>srw_tac[][] ) >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  srw_tac[][]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1])

val find_index_LEAST_EL = Q.store_thm("find_index_LEAST_EL",
  `∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE`,
  Induct >- srw_tac[][find_index_def] >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>full_simp_tac(srw_ss())[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> srw_tac[][]) >>
    Cases >> srw_tac[][] >>
    first_x_assum (qspec_then`0`mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  srw_tac[][] >>
  Cases_on`n`>>full_simp_tac(srw_ss())[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  srw_tac[][] >>
  qmatch_rename_tac`m = n` >>
  Cases_on`m < n` >- (res_tac >> full_simp_tac(srw_ss())[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> full_simp_tac(srw_ss())[GSYM ADD1] ) >>
  DECIDE_TAC )

val find_index_LESS_LENGTH = Q.store_thm(
"find_index_LESS_LENGTH",
`∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)`,
Induct >> srw_tac[][find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val ALOOKUP_find_index_NONE = Q.store_thm("ALOOKUP_find_index_NONE",
  `(ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)`,
  srw_tac[][ALOOKUP_FAILS] >> srw_tac[][GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD])

val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >> srw_tac[][find_index_def] >-
    (qexists_tac`0`>>simp[]) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]
val ALOOKUP_find_index_SOME = Q.store_thm("ALOOKUP_find_index_SOME",
  `(ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))`,
  srw_tac[][] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> full_simp_tac(srw_ss())[EL_MAP])

val find_index_ALL_DISTINCT_EL = Q.store_thm(
"find_index_ALL_DISTINCT_EL",
`∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))`,
Induct >- srw_tac[][] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_ALL_DISTINCT_EL_eq = Q.store_thm("find_index_ALL_DISTINCT_EL_eq",
  `∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)`,
  srw_tac[][EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    full_simp_tac(srw_ss())[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    full_simp_tac(srw_ss())[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL])

val find_index_APPEND_same = Q.store_thm("find_index_APPEND_same",
  `!l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)`,
  Induct >> srw_tac[][find_index_def])

val find_index_ALL_DISTINCT_REVERSE = Q.store_thm("find_index_ALL_DISTINCT_REVERSE",
  `∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))`,
  srw_tac[][] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by srw_tac[][ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >> srw_tac[][] >>
  qmatch_assum_rename_tac`z < LENGTH ls` >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1])

val THE_find_index_suff = Q.store_thm("THE_find_index_suff",
  `∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))`,
  srw_tac[][] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val find_index_APPEND1 = Q.store_thm("find_index_APPEND1",
  `∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)`,
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  srw_tac[][] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[])

val find_index_APPEND2 = Q.store_thm("find_index_APPEND2",
  `∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)`,
  Induct >> simp[find_index_def] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1])

val find_index_is_MEM = Q.store_thm("find_index_is_MEM",
  `∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls`,
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE])

val find_index_MAP_inj = Q.store_thm("find_index_MAP_inj",
  `∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)`,
  Induct >- simp[find_index_def] >>
  srw_tac[][] >> srw_tac[][find_index_def] >>
  metis_tac[])

val find_index_shift_0 = Q.store_thm("find_index_shift_0",
  `∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)`,
  Induct >> simp_tac(srw_ss())[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x` >- (
    BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  first_assum(qspecl_then[`x`,`k+1`]mp_tac) >>
  first_x_assum(qspecl_then[`x`,`1`]mp_tac) >>
  srw_tac[][] >>
  Cases_on`find_index x ls 0`>>srw_tac[][] >>
  simp[])

val find_index_shift = Q.store_thm("find_index_shift",
  `∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)`,
  Induct >> simp[find_index_def] >> srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][])

val find_index_APPEND = Q.store_thm("find_index_APPEND",
  `∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x`,
  Induct >> simp[find_index_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1])

val find_index_in_FILTER_ZIP_EQ = Q.store_thm("find_index_in_FILTER_ZIP_EQ",
  `∀P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) ∧
      (FILTER (P o FST) (ZIP(l1,v1)) = l2) ∧
      (find_index x l1 n1 = SOME (n1+j1)) ∧
      (find_index x (MAP FST l2) n2 = SOME (n2+j2)) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      (EL j1 (ZIP(l1,v1)) = EL j2 l2)`,
  gen_tac >> Induct >> simp[find_index_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    full_simp_tac(srw_ss())[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][] >>
    Cases_on`v1`>>fsrw_tac[ARITH_ss][find_index_def]) >>
  strip_tac >>
  Cases_on`v1`>>full_simp_tac(srw_ss())[] >>
  Cases_on`P h`>>full_simp_tac(srw_ss())[find_index_def] >- (
    rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`n2+1`,`t`]mp_tac) >> simp[] >>
    Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`j2=0`>>fsrw_tac[ARITH_ss][]>>
    disch_then(qspecl_then[`PRE j1`,`PRE j2`]mp_tac) >>
    simp[rich_listTheory.EL_CONS] ) >>
  first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`n2`,`t`]mp_tac) >> simp[] >>
  imp_res_tac find_index_LESS_LENGTH >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
  disch_then(qspec_then`PRE j1`mp_tac) >>
  simp[rich_listTheory.EL_CONS] )

val ALL_DISTINCT_PERM_ALOOKUP_ZIP = Q.store_thm("ALL_DISTINCT_PERM_ALOOKUP_ZIP",
  `∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))`,
  srw_tac[][EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1` >>
    imp_res_tac PERM_LENGTH >> full_simp_tac(srw_ss())[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ (x = EL m l2)` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    srw_tac[][ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1` >>
  imp_res_tac PERM_LENGTH >>
  full_simp_tac(srw_ss())[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  full_simp_tac(srw_ss())[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  impl_tac >- simp[] >>
  disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  qexists_tac`m` >>
  simp[EL_MAP] >>
  Cases_on`EL m l1`>>simp[ALOOKUP_APPEND] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    metis_tac[MEM_EL] ) >>
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF])

val PERM_ZIP = Q.store_thm("PERM_ZIP",
  `∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. (l1 = ZIP(a,b)) ∧ (l2 = ZIP(c,d)) ∧ (LENGTH a = LENGTH b) ∧ (LENGTH c = LENGTH d) ⇒
    PERM a c ∧ PERM b d`,
  ho_match_mp_tac PERM_IND >>
  conj_tac >- (
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] ) >>
  conj_tac >- (
    Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    metis_tac[PERM_MONO]) >>
  conj_tac >- (
    ntac 2 Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LENGTH a = LENGTH b` >>
    pop_assum mp_tac >>
    qmatch_assum_rename_tac`LENGTH c = LENGTH d` >>
    strip_tac >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`b`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`c`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`d`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  assume_tac (GSYM ZIP_MAP_FST_SND_EQ)>>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS])

val PERM_BIJ = Q.store_thm("PERM_BIJ",
  `∀l1 l2. PERM l1 l2 ⇒ ∃f. (BIJ f (count(LENGTH l1)) (count(LENGTH l1)) ∧ (l2 = GENLIST (λi. EL (f i) l1) (LENGTH l1)))`,
  ho_match_mp_tac PERM_IND >> simp[BIJ_EMPTY] >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(f i)` >>
    simp[EL_CONS,PRE_SUB1] >>
    full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
    conj_tac >- ( Cases >> simp[] ) >>
    qexists_tac`λi. case i of 0 => 0 | SUC i => SUC(g i)` >>
    conj_tac >- ( Cases >> simp[] ) >>
    conj_tac >- ( Cases >> simp[] ) >>
    ( Cases >> simp[] )) >>
  conj_tac >- (
    simp[GENLIST_CONS] >>
    srw_tac[][combinTheory.o_DEF] >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(f n))` >>
    simp[PRE_SUB1,EL_CONS] >>
    REWRITE_TAC[ONE] >> simp[] >>
    full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    qexists_tac`λi. case i of 0 => 1 | SUC 0 => 0 | SUC(SUC n) => SUC(SUC(g n))` >>
    simp[] >>
    conj_tac >- (Cases >> simp[]>> Cases_on`n`>>simp[]) >>
    conj_tac >- (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[]) >>
    (Cases >> simp[]>> TRY(Cases_on`n`)>>simp[] >> REWRITE_TAC[ONE]>>simp[])) >>
  ntac 2 (srw_tac[][LENGTH_GENLIST]) >>
  simp[LIST_EQ_REWRITE,EL_GENLIST] >>
  full_simp_tac(srw_ss())[LENGTH_GENLIST] >>
  qexists_tac`f o f'` >>
  simp[combinTheory.o_DEF] >>
  full_simp_tac(srw_ss())[BIJ_IFF_INV] >>
  qexists_tac`g' o g` >>
  simp[combinTheory.o_DEF] )

val PERM_EVERY = Q.store_thm("PERM_EVERY",
`∀ls ls'.
  PERM ls ls' ⇒
  (EVERY P ls ⇔ EVERY P ls')`,
  ho_match_mp_tac PERM_STRONG_IND>>srw_tac[][]>>metis_tac[])

val RTC_RINTER = Q.store_thm("RTC_RINTER",
  `!R1 R2 x y. RTC (R1 RINTER R2) x y ⇒ ((RTC R1) RINTER (RTC R2)) x y`,
  ntac 2 gen_tac >>
  match_mp_tac RTC_INDUCT >>
  simp[RINTER] >>
  metis_tac[RTC_CASES1] )

val RTC_invariant = Q.store_thm("RTC_invariant",
  `!R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y`,
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER])

val RTC_RSUBSET = Q.store_thm("RTC_RSUBSET",
  `!R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)`,
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1])

val PERM_PART = Q.store_thm("PERM_PART",
  `∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)`,
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> srw_tac[][] >- (
    first_x_assum(qspecl_then[`h::l1`,`l2`,`p`,`q`]mp_tac) >>
    simp[] >>
    REWRITE_TAC[Once CONS_APPEND] >>
    strip_tac >>
    REWRITE_TAC[Once CONS_APPEND] >>
    full_simp_tac std_ss [APPEND_ASSOC] >>
    metis_tac[PERM_REWR,PERM_APPEND] ) >>
  first_x_assum(qspecl_then[`l1`,`h::l2`,`p`,`q`]mp_tac) >>
  simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >>
  strip_tac >>
  REWRITE_TAC[Once CONS_APPEND] >>
  full_simp_tac std_ss [APPEND_ASSOC] >>
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC] )

val PERM_PARTITION = Q.store_thm("PERM_PARTITION",
  `∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)`,
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL])

val transitive_LESS = Q.store_thm("transitive_LESS",
  `transitive ($< : (num->num->bool))`,
  srw_tac[][relationTheory.transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = Q.store_thm("OPTION_EVERY_cong",
  `!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)`,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = Q.store_thm("OPTION_EVERY_mono",
  `(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op`,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val option_case_NONE_F = Q.store_thm("option_case_NONE_F",
  `(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)`,
  Cases_on`X`>>srw_tac[][])

val IS_PREFIX_THM = Q.store_thm("IS_PREFIX_THM",
 `!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)`,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val EVERY2_RC_same = Q.store_thm("EVERY2_RC_same",
  `EVERY2 (RC R) l l`,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]

val FOLDL_invariant = Q.store_thm("FOLDL_invariant",
  `!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)`,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val FOLDL_invariant_rest = Q.store_thm("FOLDL_invariant_rest",
  `∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)`,
  ntac 2 gen_tac >>
  Induct >> srw_tac[][] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> srw_tac[][])

val between_def = Define`
  between x y z ⇔ x:num ≤ z ∧ z < y`

val SUC_LEAST = Q.store_thm("SUC_LEAST",
  `!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))`,
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC)

val fmap_linv_def = Define`
  fmap_linv f1 f2 ⇔ (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`

val fmap_linv_unique = Q.store_thm("fmap_linv_unique",
  `!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)`,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = Q.store_thm("INJ_has_fmap_linv",
  `INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g`,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = Q.store_thm("has_fmap_linv_inj",
  `(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))`,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = Q.store_thm("fmap_linv_FAPPLY",
  `fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)`,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val o_f_cong = Q.store_thm("o_f_cong",
  `!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')`,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

val plus_compose = Q.store_thm("plus_compose",
  `!n:num m. $+ n o $+ m = $+ (n + m)`,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

(* TODO: move elsewhere? export as rewrite? *)
val IN_option_rwt = Q.store_thm(
"IN_option_rwt",
`(x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)`,
Cases_on `opt` >> srw_tac[][EQ_IMP_THM])

val IN_option_rwt2 = Q.store_thm(
"IN_option_rwt2",
`x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y`,
Cases_on `opt` >> srw_tac[][])

(* Re-expressing folds *)

val FOLDR_CONS_triple = Q.store_thm(
"FOLDR_CONS_triple",
`!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a`,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_CONS_5tup = Q.store_thm(
"FOLDR_CONS_5tup",
`!f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a`,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_transitive_property = Q.store_thm(
"FOLDR_transitive_property",
`!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)`,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

(* Re-expressing curried lambdas *)

val FST_triple = Q.store_thm(
"FST_triple",
`(λ(n,ns,b). n) = FST`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val FST_5tup = Q.store_thm(
"FST_5tup",
`(λ(n,ns,b,x,y). n) = FST`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = Q.store_thm(
"SND_triple",
`(λ(n,ns,b). f ns b) = UNCURRY f o SND`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = Q.store_thm(
"FST_pair",
`(λ(n,v). n) = FST`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = Q.store_thm(
"SND_pair",
`(λ(n,v). v) = SND`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = Q.store_thm(
"SND_FST_pair",
`(λ((n,m),c).m) = SND o FST`,
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY])

val MAP_ZIP_SND_triple = Q.store_thm(
"MAP_ZIP_SND_triple",
`(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)`,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

(* Specialisations to identity function *)

val INJ_I = Q.store_thm(
"INJ_I",
`∀s t. INJ I s t ⇔ s ⊆ t`,
SRW_TAC[][INJ_DEF,SUBSET_DEF])


val MAP_EQ_ID = Q.store_thm(
"MAP_EQ_ID",
`!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))`,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* Specialisations to FEMPTY *)

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = Q.store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
`FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)`,
Cases_on `x IN s` >>
srw_tac[][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(* FUPDATE_LIST stuff *)

(* Misc. *)

val LESS_1 = Q.store_thm(
"LESS_1",
`x < 1 ⇔ (x = 0:num)`,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]



  (* --------- SO additions --------- *)

val map_fst = Q.store_thm ("map_fst",
`!l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l`,
Induct_on `l` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]);

val map_some_eq = Q.store_thm ("map_some_eq",
`!l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)`,
 Induct_on `l1` >>
 srw_tac[][] >>
 Cases_on `l2` >>
 srw_tac[][]);

val map_some_eq_append = Q.store_thm ("map_some_eq_append",
`!l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)`,
metis_tac [map_some_eq, MAP_APPEND]);

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];


(* list misc *)

val LASTN_LEMMA = Q.store_thm("LASTN_LEMMA",
  `(LASTN (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LASTN (LENGTH xs + 1) (x::xs) = x::xs)`,
  MP_TAC (Q.SPEC `x::y::xs` LASTN_LENGTH_ID)
  \\ MP_TAC (Q.SPEC `x::xs` LASTN_LENGTH_ID) \\ full_simp_tac(srw_ss())[ADD1]);

val LASTN_TL = save_thm("LASTN_TL",
  LASTN_CONS |> Q.SPECL[`n+1`,`xs`]
  |> C MP (DECIDE``n < LENGTH xs ⇒ n + 1 ≤ LENGTH xs`` |> UNDISCH)
  |> SPEC_ALL |> DISCH_ALL);

val LASTN_LENGTH_LESS_EQ = Q.store_thm("LASTN_LENGTH_LESS_EQ",
  `!xs n. LENGTH xs <= n ==> LASTN n xs = xs`,
  full_simp_tac(srw_ss())[LASTN_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [listTheory.TAKE_LENGTH_TOO_LONG] \\ full_simp_tac(srw_ss())[]);

val LASTN_ALT = Q.store_thm("LASTN_ALT",
  `(LASTN n [] = []) /\
    (LASTN n (x::xs) = if LENGTH (x::xs) <= n then x::xs else LASTN n xs)`,
  srw_tac[][] THEN1 (full_simp_tac(srw_ss())[LASTN_def])
  THEN1 (match_mp_tac LASTN_LENGTH_LESS_EQ \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[LASTN_def] \\ REPEAT STRIP_TAC
  \\ `n <= LENGTH (REVERSE xs)` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ full_simp_tac(srw_ss())[]);

val LENGTH_LASTN_LESS = Q.store_thm("LENGTH_LASTN_LESS",
  `!xs n. LENGTH (LASTN n xs) <= LENGTH xs`,
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `n` assume_tac)
  \\ decide_tac);

val MAP_EQ_MAP_IMP = Q.store_thm("MAP_EQ_MAP_IMP",
  `!xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)`,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP] \\ METIS_TAC []);
(*
NB: this is weaker:
val MAP_EQ_MAP_IMP = save_thm("MAP_EQ_MAP_IMP",
  INJ_MAP_EQ |> SIMP_RULE (srw_ss()) [INJ_DEF]);
*)

val LENGTH_EQ_FILTER_FILTER = Q.store_thm("LENGTH_EQ_FILTER_FILTER",
  `!xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))`,
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]);

val LIST_REL_MAP_FILTER_NEQ = Q.store_thm("LIST_REL_MAP_FILTER_NEQ",
  `∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))`,
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND])

(* move into HOL? *)

val bytes_in_word_def = Define `
  bytes_in_word = n2w (dimindex (:'a) DIV 8):'a word`;

val word_list_def = Define `
  (word_list a [] = emp) /\
  (word_list a (x::xs) = set_sep$one (a,x) * word_list (a + bytes_in_word) xs)`;

val word_list_exists_def = Define `
  word_list_exists a n =
    SEP_EXISTS xs. word_list a xs * cond (LENGTH xs = n)`;

val lookup_vars_def = Define `
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)`

val isHexDigit_HEX = Q.store_thm("isHexDigit_HEX",
  `∀n. n < 16 ⇒ isHexDigit (HEX n) ∧ (isAlpha (HEX n) ⇒ isUpper (HEX n))`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC);

val EVERY_isHexDigit_num_to_hex_string = Q.store_thm("EVERY_isHexDigit_num_to_hex_string",
  `∀n. EVERY (λc. isHexDigit c ∧ (isAlpha c ⇒ isUpper c)) (num_to_hex_string n)`,
  rw[ASCIInumbersTheory.num_to_hex_string_def,ASCIInumbersTheory.n2s_def]
  \\ rw[rich_listTheory.EVERY_REVERSE,listTheory.EVERY_MAP]
  \\ simp[EVERY_MEM]
  \\ gen_tac\\ strip_tac
  \\ match_mp_tac isHexDigit_HEX
  \\ qspecl_then[`16`,`n`]mp_tac numposrepTheory.n2l_BOUND
  \\ rw[EVERY_MEM]
  \\ res_tac
  \\ decide_tac);

val isHexDigit_isPrint = Q.store_thm("isHexDigit_isPrint",
  `∀x. isHexDigit x ⇒ isPrint x`,
  EVAL_TAC \\ rw[]);

val num_to_hex_string_length_1 = Q.store_thm("num_to_hex_string_length_1",
  `∀x. x < 16 ⇒ (LENGTH (num_to_hex_string x) = 1)`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC);

val num_to_hex_string_length_2 = Q.store_thm("num_to_hex_string_length_2",
  `∀x. 16 ≤ x ∧ x < 256 ⇒ (LENGTH (num_to_hex_string x) = 2)`,
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV (RAND_CONV EVAL))
  \\ strip_tac \\ var_eq_tac \\ pop_assum mp_tac
  \\ EVAL_TAC);

val num_from_hex_string_length_2 = Q.store_thm("num_from_hex_string_length_2",
  `num_from_hex_string [d1;d2] < 256`,
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`UNHEX d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`UNHEX d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac);

val num_from_hex_string_leading_0 = Q.store_thm("num_from_hex_string_leading_0",
  `∀ls. ls ≠ [] ⇒ (num_from_hex_string (#"0" :: ls) = num_from_hex_string ls)`,
  simp[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def]
  \\ ho_match_mp_tac SNOC_INDUCT \\ simp[]
  \\ simp[REVERSE_SNOC]
  \\ simp[numposrepTheory.l2n_def]
  \\ rw[]
  \\ Cases_on`ls` \\ fs[numposrepTheory.l2n_def]
  \\ EVAL_TAC);

val num_from_hex_string_length_2_less_16 = Q.store_thm("num_from_hex_string_length_2_less_16",
  `∀h1 h2. isHexDigit h1 ⇒ num_from_hex_string [h1;h2] < 16 ⇒ h1 = #"0"`,
  rw[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ Cases_on`UNHEX h1 MOD 16` \\ fs[]
  \\ fs[MOD_EQ_0_DIVISOR]
  \\ fs[stringTheory.isHexDigit_def]
  \\ Cases_on`h1` \\ fs[]
  >- (
    `MEM (n - 48) (COUNT_LIST (58 - 48))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def])
  >- (
    `MEM (n - 97) (COUNT_LIST (103 - 97))` by simp[MEM_COUNT_LIST]
    \\ pop_assum mp_tac
    \\ CONV_TAC(LAND_CONV EVAL)
    \\ strip_tac
    \\ rfs[SUB_RIGHT_EQ]
    \\ fs[ASCIInumbersTheory.UNHEX_def]
    \\ `n = 97` by decide_tac
    \\ fs[ASCIInumbersTheory.UNHEX_def] )
  \\ `MEM (n - 65) (COUNT_LIST (71 - 65))` by simp[MEM_COUNT_LIST]
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac
  \\ rfs[SUB_RIGHT_EQ]
  \\ fs[ASCIInumbersTheory.UNHEX_def]
  \\ `n = 65` by decide_tac
  \\ fs[ASCIInumbersTheory.UNHEX_def] )

val num_from_hex_string_num_to_hex_string = Q.store_thm("num_from_hex_string_num_to_hex_string[simp]",
  `num_from_hex_string (num_to_hex_string n) = n`,
  ASCIInumbersTheory.num_hex_string
  |> SIMP_RULE std_ss [combinTheory.o_DEF,FUN_EQ_THM]
  |> MATCH_ACCEPT_TAC)

val MAPi_ID = Q.store_thm("MAPi_ID[simp]",
  `MAPi (\x y. y) = I`,
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]);

val enumerate_def = Define`
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)`

val LENGTH_enumerate = Q.store_thm("LENGTH_enumerate",`
  ∀xs k. LENGTH (enumerate k xs) = LENGTH xs`,
  Induct>>fs[enumerate_def])

val EL_enumerate = Q.store_thm("EL_enumerate",`
  ∀xs n k.
  n < LENGTH xs ⇒
  EL n (enumerate k xs) = (n+k,EL n xs)`,
  Induct>>fs[enumerate_def]>>rw[]>>
  Cases_on`n`>>fs[])

val MAP_enumerate_MAPi = Q.store_thm("MAP_enumerate_MAPi",`
  ∀f xs.
  MAP f (enumerate 0 xs) = MAPi (λn e. f (n,e)) xs`,
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate])

val MAPi_enumerate_MAP = Q.store_thm("MAPi_enumerate_MAP",`
  ∀f xs.
  MAPi f xs = MAP (λi,e. f i e) (enumerate 0 xs)`,
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate])

val MEM_enumerate = Q.store_thm("MEM_enumerate",`
  ∀xs i e.
  i < LENGTH xs ⇒
  (MEM (i,e) (enumerate 0 xs) ⇔ EL i xs = e)`,
  fs[MEM_EL]>>rw[]>>eq_tac>>rw[LENGTH_enumerate]>>
  imp_res_tac EL_enumerate>>fs[]>>
  qexists_tac`i`>>fs[])

val MEM_enumerate_IMP = Q.store_thm("MEM_enumerate_IMP",`
  ∀xs i e.
  MEM (i,e) (enumerate 0 xs) ⇒ MEM e xs`,
  fs[MEM_EL,LENGTH_enumerate]>>rw[]>>imp_res_tac EL_enumerate>>
  qexists_tac`n`>>fs[])

val SNOC_REPLICATE = Q.store_thm("SNOC_REPLICATE",
  `!n x. SNOC x (REPLICATE n x) = REPLICATE (SUC n) x`,
  Induct \\ fs [REPLICATE]);

val REVERSE_REPLICATE = Q.store_thm("REVERSE_REPLICATE",
  `!n x. REVERSE (REPLICATE n x) = REPLICATE n x`,
  Induct \\ fs [REPLICATE] \\ fs [GSYM REPLICATE,GSYM SNOC_REPLICATE]);

val SUM_REPLICATE = Q.store_thm("SUM_REPLICATE",
  `!n k. SUM (REPLICATE n k) = n * k`,
  Induct \\ full_simp_tac(srw_ss())[REPLICATE,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]);

val LENGTH_FLAT_REPLICATE = Q.store_thm("LENGTH_FLAT_REPLICATE",
  `∀n. LENGTH (FLAT (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val SUM_MAP_LENGTH_REPLICATE = Q.store_thm("SUM_MAP_LENGTH_REPLICATE",
  `∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val FLAT_REPLICATE_NIL = Q.store_thm("FLAT_REPLICATE_NIL",
  `!n. FLAT (REPLICATE n []) = []`,
  Induct \\ fs [REPLICATE]);

(* n.b. used in hol-reflection *)

val FDOM_FLOOKUP = Q.store_thm("FDOM_FLOOKUP",
  `x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v`,
  rw[FLOOKUP_DEF])

val FLAT_MAP_SING = Q.store_thm("FLAT_MAP_SING",
  `∀ls. FLAT (MAP (λx. [f x]) ls) = MAP f ls`,
  Induct \\ simp[]);

val FLAT_MAP_NIL = Q.store_thm("FLAT_MAP_NIL",
  `FLAT (MAP (λx. []) ls) = []`,
  rw[FLAT_EQ_NIL,EVERY_MAP]);

val UPDATE_LIST_NOT_MEM = Q.store_thm("UPDATE_LIST_NOT_MEM",
  `∀ls f x. ¬MEM x(MAP FST ls) ⇒ (f =++ ls) x = f x`,
  Induct >> simp[UPDATE_LIST_THM,combinTheory.APPLY_UPDATE_THM])

val MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same = Q.store_thm("MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same",
  `∀ks vs f. LENGTH ks = LENGTH vs ∧ ALL_DISTINCT ks ⇒ (MAP (f =++ ZIP (ks,vs)) ks = vs)`,
  Induct >> simp[LENGTH_NIL_SYM] >>
  gen_tac >> Cases >> simp[UPDATE_LIST_THM] >>
  simp[UPDATE_LIST_NOT_MEM,MAP_ZIP,combinTheory.APPLY_UPDATE_THM])

val MULT_LE_EXP = Q.store_thm("MULT_LE_EXP",
  `∀a:num b. a ≠ 1 ⇒ a * b ≤ a ** b`,
  Induct_on`b` >> simp[arithmeticTheory.MULT,arithmeticTheory.EXP] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`SUC n`mp_tac) >>
  simp[arithmeticTheory.MULT] >>
  Cases_on`b=0` >- (
    simp[arithmeticTheory.EXP] ) >>
  `SUC b ≤ b + b * n` suffices_by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  Cases_on`b * n` >> simp[] >>
  fs[arithmeticTheory.MULT_EQ_0] >> fs[])

val domain_rrestrict_subset = Q.store_thm("domain_rrestrict_subset",
  `domain (rrestrict r s) ⊆ domain r ∩ s`,
  rw[set_relationTheory.domain_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

val range_rrestrict_subset = Q.store_thm("range_rrestrict_subset",
  `range (rrestrict r s) ⊆ range r ∩ s`,
  rw[set_relationTheory.range_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[])

val PERM_MAP_BIJ = Q.store_thm("PERM_MAP_BIJ",
  `∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))`,
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP])

val bool_case_eq = Q.store_thm("bool_case_eq",
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.store_thm("pair_case_eq",
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val lookup_fromList2 = Q.store_thm("lookup_fromList2",
  `!l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE`,
  recInduct SNOC_INDUCT \\ srw_tac[][]
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  \\ full_simp_tac(srw_ss())[fromList2_def,FOLDL_SNOC]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[GSYM fromList2_def,FOLDL_SNOC]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_fromList,DIV_LT_X]
  \\ `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ full_simp_tac(srw_ss())[FOLDL]
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM DIV_LT_X,EL_SNOC]
  \\ full_simp_tac(srw_ss())[MULT_DIV,SNOC_APPEND,EL_LENGTH_APPEND,EVEN_MOD2,MOD_EQ_0]
  \\ TRY decide_tac
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `n = LENGTH l * 2 + 1` by decide_tac
  \\ full_simp_tac(srw_ss())[MOD_TIMES]);

val domain_fromList2 = Q.store_thm("domain_fromList2",
  `∀q. domain(fromList2 q) = set(GENLIST (λx. 2n*x) (LENGTH q))`,
  rw[EXTENSION,domain_lookup,lookup_fromList2,MEM_GENLIST,
     lookup_fromList,EVEN_EXISTS]
  \\ rw[EQ_IMP_THM] \\ rename1`2 * m`
  \\ qspecl_then[`2`,`m`]mp_tac MULT_DIV \\ simp[]);

val UNCURRY_eq_pair = Q.store_thm("UNCURRY_eq_pair",
  `UNCURRY f v = z ⇔ ∃a b. v = (a,b) ∧ f a b = z`,
  Cases_on`v`\\ rw[UNCURRY]);

val OLEAST_SOME_IMP = Q.store_thm("OLEAST_SOME_IMP",
  `$OLEAST P = SOME i ⇒ P i ∧ (∀n. n < i ⇒ ¬P n)`,
  simp[whileTheory.OLEAST_def]
  \\ metis_tac[whileTheory.LEAST_EXISTS_IMP]);

val EXP2_EVEN = Q.store_thm("EXP2_EVEN",
  `∀n. EVEN (2 ** n) ⇔ n ≠ 0`,
  Induct >> simp[EXP,EVEN_DOUBLE]);

val FST_UNZIP_MAPi = Q.store_thm(
  "FST_UNZIP_MAPi",
  `∀l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`,
  Induct >> simp[]);

val SND_UNZIP_MAPi = Q.store_thm(
  "SND_UNZIP_MAPi",
  `∀l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`,
  Induct >> simp[]);

val ALL_DISTINCT_FLAT = Q.store_thm(
  "ALL_DISTINCT_FLAT",
  `∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))`,
  Induct >> dsimp[ALL_DISTINCT_APPEND, LT_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]);

val TAKE_EQ_NIL = Q.store_thm(
  "TAKE_EQ_NIL[simp]",
  `TAKE n l = [] <=> n = 0 ∨ l = []`,
  Q.ID_SPEC_TAC `l` THEN Induct_on `n` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  Cases THEN ASM_SIMP_TAC (srw_ss()) []);

val GSPEC_o = Q.store_thm(
  "GSPEC_o",
  `GSPEC f o g = { x | ∃y. (g x, T) = f y }`,
  simp[FUN_EQ_THM, GSPECIFICATION]);

val NULL_APPEND = Q.store_thm("NULL_APPEND[simp]",
  `NULL (l1 ++ l2) ⇔ NULL l1 ∧ NULL l2`,
  simp[NULL_LENGTH]);

val MAP_DROP = Q.store_thm("MAP_DROP",
  `∀l i. MAP f (DROP i l) = DROP i (MAP f l)`,
  Induct \\ simp[DROP_def] \\ rw[]);

val MAP_FRONT = Q.store_thm("MAP_FRONT",
  `∀ls. ls ≠ [] ⇒ MAP f (FRONT ls) = FRONT (MAP f ls)`,
  Induct \\ simp[] \\ Cases_on`ls`\\fs[])

val LAST_MAP = Q.store_thm("LAST_MAP",
  `∀ls. ls ≠ [] ⇒ LAST (MAP f ls) = f (LAST ls)`,
  Induct \\ simp[] \\ Cases_on`ls`\\fs[])

val splitAtPki_push = Q.store_thm("splitAtPki_push",
  `f (splitAtPki P k l) = splitAtPki P (λl r. f (k l r)) l`,
  rw[splitAtPki_EQN]
  \\ BasicProvers.CASE_TAC \\ simp[]);

val splitAtPki_MAP = Q.store_thm("splitAtPki_MAP",
  `splitAtPki P k (MAP f l) = splitAtPki (λi x. P i (f x)) (λl r. k (MAP f l) (MAP f r)) l`,
  rw[splitAtPki_EQN,MAP_TAKE,MAP_DROP]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ rw[EQ_IMP_THM] \\ rfs[EL_MAP]);

val splitAtPki_change_predicate = Q.store_thm("splitAtPki_change_predicate",
  `(∀i. i < LENGTH l ⇒ P1 i (EL i l) = P2 i (EL i l)) ⇒
   splitAtPki P1 k l = splitAtPki P2 k l`,
  rw[splitAtPki_EQN]
  \\ rpt(AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ metis_tac[]);

val o_PAIR_MAP = Q.store_thm("o_PAIR_MAP",
  `FST o (f ## g) = f o FST ∧
   SND o (f ## g) = g o SND`,
  simp[FUN_EQ_THM]);

val any_el_ALT = Q.store_thm(
  "any_el_ALT",
  `∀l n d. any_el n l d = if n < LENGTH l then EL n l else d`,
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[] \\ rfs[]);

val MOD_MINUS = Q.store_thm("MOD_MINUS",
  `0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k) MOD k`,
  strip_tac
  \\ mp_tac (wordsTheory.MOD_COMPLEMENT |> Q.SPECL [`k`,`p`,`n MOD (p * k)`])
  \\ impl_tac THEN1 (fs [MOD_LESS,ZERO_LESS_MULT])
  \\ fs [MOD_MULT_MOD]);

val option_fold_def = Define `
  (option_fold f x NONE = x) ∧
  (option_fold f x (SOME y) = f y x)`;

val SPLITP_JOIN = Q.store_thm("SPLITP_JOIN",
  `!ls l r.
    (SPLITP P ls = (l, r)) ==>
    (ls = l ++ r)`,
    Induct \\ rw[SPLITP] \\
    Cases_on `SPLITP P ls`
    \\ rw[FST, SND]
);


val SPLITP_IMP = Q.store_thm("SPLITP_IMP",
  `∀P ls l r.
    (SPLITP P ls = (l,r)) ==>
    EVERY ($~ o P) l /\ (~NULL r ==> P (HD r))`,
  Induct_on`ls`
  \\ rw[SPLITP]
  \\ rw[] \\ fs[]
  \\ Cases_on`SPLITP P ls` \\ fs[]);

val SPLITP_NIL_IMP = Q.store_thm("SPLITP_NIL_IMP",
  `∀ls r. (SPLITP P ls = ([],r)) ==> (r = ls) /\ ((ls <> "") ==> (P (HD ls)))`,
  Induct \\ rw[SPLITP]);


val SPLITP_NIL_SND_EQ = Q.store_thm("SPLIT_NIL_SND_EQ",
  `!ls r. (SPLITP P ls = (r, [])) ==> (r = ls)`,
    rw[] \\ imp_res_tac SPLITP_JOIN \\ fs[]);

val SPLITP_NIL_SND_EVERY = Q.store_thm("SPLITP_NIL_SND_EVERY",
  `!ls r. (SPLITP P ls = (r, [])) <=> (r = ls) /\ (EVERY ($~ o P) ls)`,
  rw[] \\ EQ_TAC
    >-(rw[] \\ imp_res_tac SPLITP_IMP \\ imp_res_tac SPLITP_JOIN \\ fs[])
  \\ rw[] \\ Induct_on `ls` \\ rw[SPLITP]
);

val SPLITP_CONS_IMP = Q.store_thm("SPLITP_CONS_IMP",
  `∀ls l' r. (SPLITP P ls = (l', r)) /\ (r <> []) ==> (EXISTS P ls)`,
  rw[] \\ imp_res_tac SPLITP_IMP \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on `r` \\ rfs[NULL_EQ, EXISTS_DEF, HD]);


val LAST_CONS_alt = Q.store_thm("LAST_CONS_alt",
  `P x ==> ((ls <> [] ==> P (LAST ls)) <=> (P (LAST (CONS x ls))))`,
  Cases_on`ls` \\ rw[]);

val SPLITP_APPEND = Q.store_thm("SPLITP_APPEND",
  `!l1 l2.
   SPLITP P (l1 ++ l2) =
    if EXISTS P l1 then
      (FST (SPLITP P l1), SND (SPLITP P l1) ++ l2)
    else
      (l1 ++ FST(SPLITP P l2), SND (SPLITP P l2))`,
  Induct \\ rw[SPLITP] \\ fs[]);


val SPLITP_LENGTH = Q.store_thm("SPLITP_LENGTH",
  `!l.
    LENGTH l = (LENGTH (FST (SPLITP P l)) + LENGTH (SND (SPLITP P l)))`,
    Induct \\ rw[SPLITP, LENGTH]
);


val TOKENS_APPEND = Q.store_thm("TOKENS_APPEND",
  `∀P l1 x l2.
    P x ==>
    (TOKENS P (l1 ++ x::l2) = TOKENS P l1 ++ TOKENS P l2)`,
  ho_match_mp_tac TOKENS_ind
  \\ rw[TOKENS_def] >- (fs[SPLITP])
  \\ pairarg_tac  \\ fs[]
  \\ pairarg_tac  \\ fs[]
  \\ fs[NULL_EQ, SPLITP]
  \\ Cases_on `P h` \\ full_simp_tac bool_ss []
  \\ rw[]
  \\ fs[TL]
  \\ Cases_on `EXISTS P t` \\ rw[SPLITP_APPEND, SPLITP]
  \\ fs[NOT_EXISTS] \\ imp_res_tac (GSYM SPLITP_NIL_SND_EVERY) \\ rw[]
  \\ fs[NOT_EXISTS] \\ imp_res_tac (GSYM SPLITP_NIL_SND_EVERY) \\ rw[]);


val TOKENS_NIL = Q.store_thm("TOKENS_NIL",
  `!ls. (TOKENS f ls = []) <=> EVERY f ls`,
  Induct \\ rw[TOKENS_def]  \\ pairarg_tac  \\ fs[NULL_EQ, SPLITP]
  \\ every_case_tac \\ fs[] \\ rw[]);


val TOKENS_START = Q.store_thm("TOKENS_START",
  `!l a.
      TOKENS (\x. x = a) (a::l) = TOKENS (\x. x = a) l`,
    gen_tac \\ Induct_on `l` \\ rw[TOKENS_def] \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[]
    >-(imp_res_tac SPLITP_NIL_IMP \\ fs[] \\ rw[TOKENS_def])
    >-(fs[SPLITP])
    >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[]
      \\ imp_res_tac SPLITP_NIL_IMP \\ fs[]
      \\ simp[TOKENS_def] \\ rw[NULL_EQ])
    >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP])
);

val TOKENS_END = Q.store_thm("TOKENS_END",
  `!l a.
      TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l`,
    rw[]
    \\ `TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l ++ TOKENS (\x. x = a) ""` by fs[TOKENS_APPEND]
    \\ fs[TOKENS_def] \\ rw[]
);


val TOKENS_LENGTH_END  = Q.store_thm("TOKENS_LENGTH_END",
  `!l a.
      LENGTH (TOKENS (\x. x = a) (l ++ [a])) = LENGTH (TOKENS (\x. x = a) l)`,
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_END]
);

val TOKENS_LENGTH_START = Q.store_thm("TOKENS_LENGTH_START",
  `!l a.
      LENGTH (TOKENS (\x. x = a) (a::l)) = LENGTH (TOKENS (\x. x= a) l)`,
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_START]
);


val DROP_EMPTY = Q.store_thm("DROP_EMPTY",
  `!ls n. (DROP n ls = []) ==> (n >= LENGTH ls)`,
    Induct \\ rw[DROP]
    \\ Cases_on `n > LENGTH ls` \\ fs[]
    \\ `n < LENGTH (h::ls)` by fs[]
    \\ fs[DROP_EL_CONS]);

val FRONT_APPEND' = Q.prove(
  `!l h a b t. l = h ++ [a; b] ++ t ==>
      FRONT l = h ++ FRONT([a; b] ++ t)`,
      Induct \\ rw[FRONT_DEF, FRONT_APPEND]
      >-(rw[LIST_EQ_REWRITE])
      \\ Cases_on `h'` \\ fs[FRONT_APPEND, FRONT_DEF]
);


val EVERY_NOT_IMP = Q.prove(
  `!ls a. (EVERY ($~ o (\x. x = a)) ls) ==> (LIST_ELEM_COUNT a ls = 0)`,
    Induct \\ rw[LIST_ELEM_COUNT_DEF] \\ fs[LIST_ELEM_COUNT_DEF]
);

val LIST_ELEM_COUNT_CONS = Q.prove(
  `!h t a. LIST_ELEM_COUNT a (h::t) = LIST_ELEM_COUNT a [h] + LIST_ELEM_COUNT a t`,
    simp_tac std_ss [Once CONS_APPEND, LIST_ELEM_COUNT_THM]
);

val FRONT_COUNT_IMP = Q.prove(
  `!l1 l2 a. l1 <> [] /\ FRONT l1 = l2 ==> (LIST_ELEM_COUNT a l2 = LIST_ELEM_COUNT a l1) \/ (LIST_ELEM_COUNT a l2 + 1 = LIST_ELEM_COUNT a l1)`,
    gen_tac \\ Induct_on `l1` \\ gen_tac \\ Cases_on `l2` \\ rw[FRONT_DEF]
    >-(Cases_on `h = a` \\ rw[LIST_ELEM_COUNT_DEF])
    \\ rw[LIST_ELEM_COUNT_DEF] \\ fs[LIST_ELEM_COUNT_DEF]
    \\ Cases_on `LENGTH (FILTER (\x. x = a) l1)`
    \\ first_x_assum (qspecl_then [`a`] mp_tac) \\ rw[] \\ rfs[]
);

val CONCAT_WITH_aux_def = Define`
    (CONCAT_WITH_aux [] l fl = REVERSE fl ++ FLAT l) /\
    (CONCAT_WITH_aux (h::t) [] fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ((h1::t1)::ls) fl = CONCAT_WITH_aux (h::t) (t1::ls) (h1::fl)) /\
    (CONCAT_WITH_aux (h::t) ([]::[]) fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ([]::(h'::t')) fl = CONCAT_WITH_aux (h::t) (h'::t') (REVERSE(h::t) ++ fl))`

val CONCAT_WITH_AUX_ind = theorem"CONCAT_WITH_aux_ind";

val CONCAT_WITH_def = Define`
    CONCAT_WITH s l = CONCAT_WITH_aux s l [] `

val OPT_MMAP_MAP_o = Q.store_thm("OPT_MMAP_MAP_o",
  `!ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls`,
  Induct \\ rw[OPT_MMAP_def]);

val OPT_MMAP_SOME = Q.store_thm("OPT_MMAP_SOME[simp]",
  `OPT_MMAP SOME ls = SOME ls`,
  Induct_on`ls` \\ rw[OPT_MMAP_def]);

val OPT_MMAP_CONG = Q.store_thm("OPT_MMAP_CONG[defncong]",
  `!l1 l2 f f'.
     (l1 = l2) /\
     (!x. MEM x l2 ==> (f x = f' x))
     ==> (OPT_MMAP f l1 = OPT_MMAP f' l2)`,
  Induct \\ rw[OPT_MMAP_def] \\ rw[OPT_MMAP_def] \\
  Cases_on`f' h` \\ rw[] \\ fs[] \\ metis_tac[]);

val IMP_OPT_MMAP_EQ = Q.store_thm("IMP_OPT_MMAP_EQ",
  `!l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2 l2)`,
  Induct \\ rw[OPT_MMAP_def] \\ Cases_on`l2` \\ fs[OPT_MMAP_def] \\
  Cases_on`f2 h'` \\ fs[] \\ metis_tac[]);

val DISJOINT_set_simp = Q.store_thm("DISJOINT_set_simp",
  `DISJOINT (set []) s /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)`,
  fs [DISJOINT_DEF,EXTENSION] \\ metis_tac []);

val ALOOKUP_EXISTS_IFF = Q.store_thm(
  "ALOOKUP_EXISTS_IFF",
  `(∃v. ALOOKUP alist k = SOME v) ⇔ (∃v. MEM (k,v) alist)`,
  Induct_on `alist` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]);

val LUPDATE_commutes = Q.store_thm(
  "LUPDATE_commutes",
  `∀m n e1 e2 l.
    m ≠ n ⇒
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)`,
  Induct_on `l` >> simp[LUPDATE_def] >>
  Cases_on `m` >> simp[LUPDATE_def] >> rpt strip_tac >>
  rename[`LUPDATE _ nn (_ :: _)`] >>
  Cases_on `nn` >> fs[LUPDATE_def]);

val ALIST_FUPDKEY_def = Define`
  (ALIST_FUPDKEY k f [] = []) ∧
  (ALIST_FUPDKEY k f ((k',v)::rest) =
     if k = k' then (k,f v)::rest
     else (k',v) :: ALIST_FUPDKEY k f rest)
`;

val ALIST_FUPDKEY_ind = theorem"ALIST_FUPDKEY_ind";

val ALIST_FUPDKEY_ALOOKUP = Q.store_thm(
  "ALIST_FUPDKEY_ALOOKUP",
  `ALOOKUP (ALIST_FUPDKEY k2 f al) k1 =
     case ALOOKUP al k1 of
         NONE => NONE
       | SOME v => if k1 = k2 then SOME (f v) else SOME v`,
  Induct_on `al` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >> rw[]
  >- (Cases_on `ALOOKUP al k1` >> simp[]) >>
  simp[]);

val MAP_FST_ALIST_FUPDKEY = Q.store_thm(
  "MAP_FST_ALIST_FUPDKEY[simp]",
  `MAP FST (ALIST_FUPDKEY f k alist) = MAP FST alist`,
  Induct_on `alist` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >> rw[]);

val ALIST_FUPDKEY_unchanged = Q.store_thm(
  "ALIST_FUPDKEY_unchanged",
  `∀k f alist.
   (∀v. ALOOKUP alist k = SOME v ⇒ f v = v)
   ==> ALIST_FUPDKEY k f alist = alist`,
  ho_match_mp_tac ALIST_FUPDKEY_ind
  \\ rw[ALIST_FUPDKEY_def]);

val ALIST_FUPDKEY_o = Q.store_thm(
  "ALIST_FUPDKEY_o",
  `ALIST_FUPDKEY k f1 (ALIST_FUPDKEY k f2 al) = ALIST_FUPDKEY k (f1 o f2) al`,
  Induct_on `al` >> simp[ALIST_FUPDKEY_def, FORALL_PROD] >>
  rw[ALIST_FUPDKEY_def]);

val ALIST_FUPDKEY_eq = Q.store_thm("ALIST_FUPDKEY_eq",
  `∀k f1 l f2.
   (∀v. ALOOKUP l k = SOME v ⇒ f1 v = f2 v) ⇒
   ALIST_FUPDKEY k f1 l = ALIST_FUPDKEY k f2 l`,
  ho_match_mp_tac ALIST_FUPDKEY_ind \\ rw[ALIST_FUPDKEY_def]);

val FILTER_EL_EQ = Q.store_thm("FILTER_EL_EQ",
  `∀l1 l2. LENGTH l1 = LENGTH l2 ∧
   (∀n. n < LENGTH l1 ∧ (P (EL n l1) ∨ P (EL n l2)) ⇒ (EL n l1 = EL n l2))
   ⇒
   FILTER P l1 = FILTER P l2`,
  Induct \\ rw[] \\ Cases_on`l2` \\ fs[]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac (srw_ss())[] \\ simp[]
  \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[]);

val LENGTH_ALIST_FUPDKEY = Q.store_thm("LENGTH_ALIST_FUPDKEY[simp]",
  `∀ls. LENGTH (ALIST_FUPDKEY k f ls) = LENGTH ls`,
  Induct \\ simp[ALIST_FUPDKEY_def]
  \\ Cases \\ rw[ALIST_FUPDKEY_def]);

val FST_EL_ALIST_FUPDKEY = Q.store_thm("FST_EL_ALIST_FUPDKEY",
  `∀n. n < LENGTH ls ⇒ FST (EL n (ALIST_FUPDKEY k f ls)) = FST (EL n ls)`,
  Induct_on`ls` \\ simp[]
  \\ Cases \\ rw[ALIST_FUPDKEY_def]
  \\ Cases_on`n` \\ fs[]);

val EL_ALIST_FUPDKEY_unchanged = Q.store_thm("EL_ALIST_FUPDKEY_unchanged",
  `∀n. n < LENGTH ls ∧ FST (EL n ls) ≠ k ⇒ EL n (ALIST_FUPDKEY k f ls) = EL n ls`,
  Induct_on`ls` \\ simp[]
  \\ Cases \\ simp[ALIST_FUPDKEY_def]
  \\ Cases \\ simp[]
  \\ IF_CASES_TAC \\ rveq \\ rw[]);

val A_DELKEY_def = Define`
  A_DELKEY k alist = FILTER (λp. FST p <> k) alist
`;

val MEM_DELKEY = Q.store_thm(
  "MEM_DELKEY[simp]",
  `∀al. MEM (k1,v) (A_DELKEY k2 al) ⇔ k1 ≠ k2 ∧ MEM (k1,v) al`,
  Induct >> simp[A_DELKEY_def, FORALL_PROD] >> rw[MEM_FILTER] >>
  metis_tac[]);

val ALOOKUP_ADELKEY = Q.store_thm(
  "ALOOKUP_ADELKEY",
  `∀al. ALOOKUP (A_DELKEY k1 al) k2 = if k1 = k2 then NONE else ALOOKUP al k2`,
  simp[A_DELKEY_def] >> Induct >> simp[FORALL_PROD] >> rw[] >> simp[]);

val A_DELKEY_ALIST_FUPDKEY = Q.store_thm("A_DELKEY_ALIST_FUPDKEY[simp]",
  `∀fd f ls. A_DELKEY fd (ALIST_FUPDKEY fd f ls) = A_DELKEY fd ls`,
  ho_match_mp_tac ALIST_FUPDKEY_ind
  \\ rw[ALIST_FUPDKEY_def,A_DELKEY_def]);

val A_DELKEY_I = Q.store_thm("A_DELKEY_I",
  `∀x ls. (A_DELKEY x ls = ls ⇔ ¬MEM x (MAP FST ls))`,
  Induct_on`ls`
  \\ rw[A_DELKEY_def,FILTER_EQ_ID,MEM_MAP,EVERY_MEM]
  >- metis_tac[]
  \\ rw[EQ_IMP_THM]
  >- (
    `LENGTH (h::ls) ≤ LENGTH ls` by metis_tac[LENGTH_FILTER_LEQ]
    \\ fs[] )
  \\ first_x_assum(qspec_then`h`mp_tac)
  \\ simp[]);

val findi_APPEND = Q.store_thm(
  "findi_APPEND",
  `∀l1 l2 x.
      findi x (l1 ++ l2) =
        let n0 = findi x l1
        in
          if n0 = LENGTH l1 then n0 + findi x l2
          else n0`,
  Induct >> simp[findi_def] >> rw[] >> fs[]);

val NOT_MEM_findi_IFF = Q.store_thm(
  "NOT_MEM_findi_IFF",
  `¬MEM e l ⇔ findi e l = LENGTH l`,
  Induct_on `l` >> simp[findi_def, bool_case_eq, ADD1] >> metis_tac[]);

val NOT_MEM_findi = save_thm( (* more useful as conditional rewrite *)
  "NOT_MEM_findi",
  NOT_MEM_findi_IFF |> EQ_IMP_RULE |> #1);

val ORD_eq_0 = Q.store_thm(
  "ORD_eq_0",
  `(ORD c = 0 ⇔ c = CHR 0) ∧ (0 = ORD c ⇔ c = CHR 0)`,
  metis_tac[char_BIJ, ORD_CHR, EVAL ``0n < 256``]);

val HD_LUPDATE = Q.store_thm(
  "HD_LUPDATE",
  `0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l`,
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]);

val w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]
         |> curry save_thm "w2n_lt_256"

val CHR_w2n_n2w_ORD = Q.store_thm("CHR_w2n_n2w_ORD",
  `(CHR o w2n o (n2w:num->word8) o ORD) = I`,
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
);

val n2w_ORD_CHR_w2n = Q.store_thm("n2w_ORD_CHR_w2n",
  `((n2w:num->word8) o ORD o CHR o w2n) = I`,
  rw[w2n_lt_256, o_DEF, ORD_BOUND, ORD_CHR, FUN_EQ_THM]
);

val MAP_CHR_w2n_11 = Q.store_thm("MAP_CHR_w2n_11",
  `!ws1 ws2:word8 list.
      MAP (CHR ∘ w2n) ws1 = MAP (CHR ∘ w2n) ws2 <=> ws1 = ws2`,
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `ws2` \\ fs [] \\ metis_tac [CHR_11,w2n_lt_256,w2n_11]);

val MAP_K_REPLICATE = Q.store_thm("MAP_K_REPLICATE",
  `MAP (K x) ls = REPLICATE (LENGTH ls) x`,
  Induct_on`ls` \\ rw[REPLICATE]);

val shift_left_def = Define`
  shift_left (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_left (a << 32) (n - 32)
  else if n > 16 then shift_left (a << 16) (n - 16)
  else if n > 8 then shift_left (a << 8) (n - 8)
  else shift_left (a << 1) (n - 1)`

val shift_left_rwt = Q.store_thm("shift_left_rwt",
  `!a n. a << n = shift_left a n`,
  completeInduct_on `n`
  \\ rw [Once shift_left_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val shift_right_def = Define`
  shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_right (a >>> 32) (n - 32)
  else if n > 16 then shift_right (a >>> 16) (n - 16)
  else if n > 8 then shift_right (a >>> 8) (n - 8)
  else shift_right (a >>> 1) (n - 1)`

val shift_right_rwt = Q.store_thm("shift_right_rwt",
  `!a n. a >>> n = shift_right a n`,
  completeInduct_on `n`
  \\ rw [Once shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val arith_shift_right_def = Define`
  arith_shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) /\ ~word_msb a then 0w
  else if (a = -1w) \/ n > dimindex(:'a) /\ word_msb a then -1w
  else if n > 32 then arith_shift_right (a >> 32) (n - 32)
  else if n > 16 then arith_shift_right (a >> 16) (n - 16)
  else if n > 8 then arith_shift_right (a >> 8) (n - 8)
  else arith_shift_right (a >> 1) (n - 1)`

val arith_shift_right_rwt = Q.store_thm("arith_shift_right_rwt",
  `!a n. a >> n = arith_shift_right a n`,
  completeInduct_on `n`
  \\ rw [Once arith_shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX])

val any_word64_ror_def = Define `
  any_word64_ror (w:word64) (n:num) =
    if 64 <= n then any_word64_ror w (n - 64) else
    if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
    if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
    if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
    if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
    if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
    if 1 <= n then word_ror w 1 else w`

val word_ror_eq_any_word64_ror = Q.store_thm("word_ror_eq_any_word64_ror",
  `!a n. word_ror a n = any_word64_ror a n`,
  completeInduct_on `n`
  \\ rw [Once any_word64_ror_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX]
  THEN1 fs [fcpTheory.CART_EQ,wordsTheory.word_ror_def,arithmeticTheory.SUB_MOD]
  \\ `n = 1 \/ n = 0` by fs [] \\ fs []);

val TL_DROP_SUC = Q.store_thm("TL_DROP_SUC",
  `∀x ls. x < LENGTH ls ⇒ TL (DROP x ls) = DROP (SUC x) ls`,
  Induct \\ rw[] \\ Cases_on`ls` \\ fs[]);

val LENGTH_FIELDS = Q.store_thm("LENGTH_FIELDS",
  `∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[] \\ fs[] \\ rw[ADD1]
  \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_NIL_IMP
  \\ imp_res_tac SPLITP_NIL_SND_EVERY
  \\ imp_res_tac SPLITP_IMP
  \\ fs[NULL_EQ]
  \\ fs[SPLITP] \\ rfs[] \\ rw[]
  >- (`FILTER P t = []` by (simp[FILTER_EQ_NIL] \\ fs[EVERY_MEM])
      \\ simp[])
  \\ first_x_assum(qspec_then`LENGTH t`mp_tac) \\ simp[]
  \\ disch_then(qspec_then`t`mp_tac)
  \\ Cases_on`t` \\ rw[FIELDS_def]
  \\ fs[SPLITP] \\ rfs[]
  \\ rfs[NULL_EQ]);

val FIELDS_NEQ_NIL = Q.store_thm("FIELDS_NEQ_NIL[simp]",
  `FIELDS P ls ≠ []`,
  disch_then(assume_tac o Q.AP_TERM`LENGTH`)
  \\ fs[LENGTH_FIELDS]);

val CONCAT_FIELDS = Q.store_thm("CONCAT_FIELDS",
  `∀ls. CONCAT (FIELDS P ls) = FILTER ($~ o P) ls`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ simp[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ fs[Once SPLITP]
  \\ Cases_on`P h` \\ fs[] \\ rveq \\ simp[]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`NULL r` \\ fs[NULL_EQ]
  >- (
    imp_res_tac SPLITP_NIL_SND_EVERY
    \\ fs[FILTER_EQ_ID] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ simp[FILTER_APPEND]
  \\ fs[GSYM FILTER_EQ_ID]
  \\ Cases_on`r` \\ fs[] );

val FIELDS_next = Q.store_thm("FIELDS_next",
  `∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c)`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ imp_res_tac SPLITP_NIL_IMP \\ fs[]
  \\ imp_res_tac SPLITP_IMP \\ fs[]
  \\ imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[]
  \\ rfs[PULL_FORALL,NULL_EQ]
  \\ fs[SPLITP]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ fs[SPLITP]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`SPLITP P q` \\ fs[]
  \\ rw[]
  \\ `FIELDS P t = q::FIELDS P (TL r)`
  by (
    Cases_on`t` \\ fs[]
    \\ rw[FIELDS_def,NULL_EQ] )
  \\ first_x_assum(qspecl_then[`t`,`q`,`FIELDS P (TL r)`]mp_tac)
  \\ simp[] );

val FIELDS_full = Q.store_thm("FIELDS_full",
  `∀P ls l1 l2.
   FIELDS P ls = l1::l2 ∧ LENGTH ls ≤ LENGTH l1 ⇒
   l1 = ls ∧ l2 = []`,
  ntac 2 gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ simp_tac(srw_ss()++LET_ss)[FIELDS_def]
  \\ pairarg_tac \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
  \\ strip_tac
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY )
  \\ simp_tac(srw_ss())[]
  \\ strip_tac \\ rveq
  \\ Q.ISPEC_THEN`h::t`mp_tac SPLITP_LENGTH
  \\ last_x_assum kall_tac
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ `LENGTH r = 0` by decide_tac
  \\ fs[LENGTH_NIL]);

val FLAT_MAP_TOKENS_FIELDS = Q.store_thm("FLAT_MAP_TOKENS_FIELDS",
  `∀P' ls P.
    (∀x. P' x ⇒ P x) ⇒
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls`,
  Induct_on`FIELDS P' ls` \\ rw[] \\
  qpat_x_assum`_ = FIELDS _ _`(assume_tac o SYM) \\
  imp_res_tac FIELDS_next \\
  Cases_on`LENGTH ls ≤ LENGTH h` >- (
    imp_res_tac FIELDS_full \\ fs[] ) \\
  fs[] \\ rw[] \\
  fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] \\
  `h ++ [c] ++ l  = h ++ (c::l)` by simp[] \\ pop_assum SUBST_ALL_TAC \\
  asm_simp_tac std_ss [TOKENS_APPEND]);

val the_nil_eq_cons = Q.store_thm("the_nil_eq_cons",
  `(the [] x = y::z) ⇔ x = SOME (y ::z)`,
  Cases_on`x` \\ EVAL_TAC);

val splitlines_def = Define`
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines`;

val splitlines_next = Q.store_thm("splitlines_next",
  `splitlines ls = ln::lns ⇒
   splitlines (DROP (SUC (LENGTH ln)) ls) = lns ∧
   ln ≼ ls ∧ (LENGTH ln < LENGTH ls ⇒ ln ++ "\n" ≼ ls)`,
  simp[splitlines_def]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ Cases_on`LENGTH h < LENGTH ls`
  >- (
    imp_res_tac FIELDS_next
    \\ strip_tac
    \\ `ln = h`
    by (
      pop_assum mp_tac \\ rw[]
      \\ fs[FRONT_DEF] )
    \\ fs[]
    \\ fs[LAST_DEF,NULL_EQ]
    \\ Cases_on`t = []` \\ fs[]
    \\ fs[FRONT_DEF]
    \\ IF_CASES_TAC \\ fs[]
    \\ fs[IS_PREFIX_APPEND])
  \\ fs[NOT_LESS]
  \\ imp_res_tac FIELDS_full \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac \\ rveq \\ fs[]
  \\ simp[DROP_LENGTH_TOO_LONG,FIELDS_def]);

val splitlines_nil = save_thm("splitlines_nil[simp]",
  EVAL``splitlines ""``);

val splitlines_eq_nil = Q.store_thm("splitlines_eq_nil[simp]",
  `splitlines ls = [] ⇔ (ls = [])`,
  rw[EQ_IMP_THM]
  \\ fs[splitlines_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]);

val splitlines_CONS_FST_SPLITP = Q.store_thm("splitlines_CONS_FST_SPLITP",
  `splitlines ls = ln::lns ⇒ FST (SPLITP ($= #"\n") ls) = ln`,
  rw[splitlines_def]
  \\ Cases_on`ls` \\ fs[FIELDS_def]
  \\ TRY pairarg_tac \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ fs[NULL_EQ]
  \\ qmatch_assum_abbrev_tac`FRONT (x::y) = _`
  \\ Cases_on`y` \\ fs[]);

val DIV_EQ_0 = Q.store_thm("DIV_EQ_0",
  `1 < b ==> ((n DIV b = 0) = (n < b))`,
  metis_tac[numposrepTheory.DIV_0_IMP_LT,LESS_DIV_EQ_ZERO]);

val n2l_DIV_MOD = Q.store_thm("n2l_DIV_MOD",
  `!b n k. 1 < b /\ 0 < k /\ b ** k <= n ==>
   (n2l b (n MOD (b ** k)) ++ REPLICATE (k - LENGTH (n2l b (n MOD (b ** k)))) 0 ++
    n2l b (n DIV (b ** k)) = n2l b n)`,
  ho_match_mp_tac numposrepTheory.n2l_ind
  \\ rw[]
  \\ Cases_on`b < 2` \\ fs[]
  \\ Cases_on`n < b` \\ fs[]
  >- ( `b <= b ** k` by ( Cases_on`k` \\ fs[EXP] ) \\ fs[] )
  \\ Cases_on`k` \\ fs[EXP]
  \\ fs[GSYM DIV_DIV_DIV_MULT]
  \\ fs[DIV_MOD_MOD_DIV]
  \\ rw[Once numposrepTheory.n2l_def,SimpRHS]
  \\ qmatch_assum_rename_tac`b * b ** k <= n`
  \\ Cases_on`k=0` \\ fs[EXP]
  >- (
    rw[Once numposrepTheory.n2l_def,REPLICATE_NIL] \\
    rw[numposrepTheory.LENGTH_n2l])
  \\ simp[Once numposrepTheory.n2l_def]
  \\ simp[MOD_MULT_MOD]
  \\ fs[numposrepTheory.LENGTH_n2l]
  \\ first_x_assum(qspec_then`k`mp_tac)
  \\ impl_tac >- simp[X_LE_DIV]
  \\ disch_then(assume_tac o SYM) \\ simp[]
  \\ rfs[DIV_EQ_0]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- simp[logrootTheory.LOG_DIV,ADD1]
  \\ IF_CASES_TAC \\ fs[]
  >- (
    `0 < b ** k` by simp[] \\
    `0 < b * b ** k` by simp[LESS_MULT2] \\
    fs[MOD_EQ_0_DIVISOR,ZERO_DIV,Once numposrepTheory.n2l_def]
    \\ Cases_on`k` \\ fs[REPLICATE]
    \\ metis_tac[MULT_ASSOC] )
  \\ conj_asm1_tac
  >- (
    qspecl_then[`b ** k`,`b`]mp_tac MOD_MULT_MOD
    \\ simp[]
    \\ disch_then(qspec_then`n`mp_tac)
    \\ simp[LESS_MOD])
  \\ simp[]
  \\ `n MOD b DIV b = 0` by simp[DIV_EQ_0]
  \\ simp[Once numposrepTheory.n2l_def]
  \\ rewrite_tac[GSYM REPLICATE,ADD1]
  \\ `LOG b (n MOD b) = 0`
  by ( simp[logrootTheory.LOG_EQ_0] )
  \\ simp[]);

val irreflexive_inv_image = Q.store_thm("irreflexive_inv_image",
  `!R f. irreflexive R ==> irreflexive (inv_image R f)`,
  SIMP_TAC std_ss [irreflexive_def,inv_image_def])

val trichotomous_inv_image = Q.store_thm("trichotomous_inv_image",
  `!R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)`,
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[])

val MEM_REPLICATE_IMP = Q.store_thm("MEM_REPLICATE_IMP",
  `MEM x (REPLICATE n y) ==> x = y`,
  Induct_on`n` \\ rw[REPLICATE] \\ fs[]);

val plus_0_I = Q.store_thm("plus_0_I[simp]",
  `$+ 0n = I`, rw[FUN_EQ_THM]);

val OPTION_MAP_I = Q.store_thm("OPTION_MAP_I[simp]",
  `OPTION_MAP I x = x`,
  Cases_on`x` \\ rw[]);

val OPTION_MAP_INJ = Q.store_thm("OPTION_MAP_INJ",
  `(∀x y. f x = f y ⇒ x = y)
   ⇒ ∀o1 o2.
     OPTION_MAP f o1 = OPTION_MAP f o2 ⇒ o1 = o2`,
  strip_tac \\ Cases \\ Cases \\ simp[]);

val TAKE_FLAT_REPLICATE_LEQ = Q.store_thm("TAKE_FLAT_REPLICATE_LEQ",
  `∀j k ls len.
    len = LENGTH ls ∧ k ≤ j ⇒
    TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)`,
  Induct \\ simp[REPLICATE]
  \\ Cases \\ simp[REPLICATE]
  \\ simp[TAKE_APPEND2] \\ rw[] \\ fs[]
  \\ simp[MULT_SUC]);

val MOD_2EXP_0_EVEN = Q.store_thm("MOD_2EXP_0_EVEN",
  `∀x y. 0 < x ∧ MOD_2EXP x y = 0 ⇒ EVEN y`,
  rw[EVEN_MOD2,bitTheory.MOD_2EXP_def,MOD_EQ_0_DIVISOR]
  \\ Cases_on`x` \\ fs[EXP]);

val ADD_MOD_EQ_LEMMA = Q.store_thm("ADD_MOD_EQ_LEMMA",
  `k MOD d = 0 /\ n < d ==> (k + n) MOD d = n`,
  rw [] \\ `0 < d` by decide_tac
  \\ fs [MOD_EQ_0_DIVISOR]
  \\ pop_assum kall_tac
  \\ drule MOD_MULT
  \\ fs []);

val list_subset_def = Define `
list_subset l1 l2 = EVERY (\x. MEM x l2) l1`;

val list_set_eq = Define `
list_set_eq l1 l2 ⇔ list_subset l1 l2 ∧ list_subset l2 l1`;

val BIJ_UPDATE = store_thm("BIJ_UPDATE",
  ``!f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);

val INJ_UPDATE = store_thm("INJ_UPDATE",
  ``INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);


(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

val (eventually_rules,eventually_ind,eventually_cases) = Hol_reln`
  (!ll. P ll ==> eventually P ll) /\
  (!h t. ¬P (h:::t) /\ eventually P t ==> eventually P (h:::t)) `;

val eventually_thm = store_thm(
  "eventually_thm",
  ``(eventually P [||] = P [||]) /\
    (eventually P (h:::t) = (P (h:::t) \/(¬ P (h:::t) /\ eventually P t)))``,
  CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [eventually_cases])) THEN
  SRW_TAC [][]);

val _ = export_rewrites ["eventually_thm"]

val (always_rules,always_coind,always_cases) = Hol_coreln`
  (!h t. (P (h ::: t) /\ always P t) ==> always P (h ::: t))`;

val always_thm = Q.store_thm("always_thm",
   `∀h t. (always P (h:::t) ==> P (h:::t) ∧ always P t)`,
   rw[] >> fs[Once always_cases]);

val _ = export_rewrites ["always_thm"]

val always_conj_l = Q.store_thm("always_conj_l",
  `!ll. ¬ LFINITE ll /\ (always (\x. P x /\ Q x) ll) ==> (always P ll)`,
  ho_match_mp_tac always_coind >>
  rw[] >> Cases_on`ll` >> fs[] >> imp_res_tac always_thm >> fs[]);

val always_eventually_ind = Q.store_thm("always_eventually_ind",
  `(!ll. (P ll \/ (¬ P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
   !ll. ll <> [||] ⇒  always(eventually P) ll ==> Q ll`,
   `(!ll. (P ll \/ (¬ P ll /\ Q (THE(LTL ll)))) ==> Q ll) ==>
     (!ll. eventually P ll ==> (Q ll))` by
     (strip_tac >> ho_match_mp_tac eventually_ind >> rw[]) >>
   rw[] >> Cases_on`ll` >> fs[] >> imp_res_tac always_thm >> res_tac);

val always_DROP = Q.store_thm("always_DROP",
  `!ll. ¬ LFINITE ll /\ always P ll ==> always P (THE(LDROP k ll))`,
  Induct_on`k` >> Cases_on`ll` >> fs[always_thm,LDROP] >>
  rw[] >> imp_res_tac always_thm >> fs[]);

val LDROP_1 = Q.store_thm("LDROP_1",
  `LDROP (1: num) (h:::t) = SOME t`,
  `LDROP (SUC 0) (h:::t) = SOME t` by fs[LDROP] >>
  metis_tac[arithmeticTheory.ONE]);

val LDROP_NONE_LFINITE = Q.store_thm("LDROP_NONE_LFINITE",
  `LDROP k l = NONE ⇒ LFINITE l`,
  metis_tac[NOT_LFINITE_DROP,NOT_SOME_NONE]);

val LDROP_LDROP = Q.store_thm("LDROP_LDROP",
  `!ll k1 k2. ¬ LFINITE ll ==>
    THE (LDROP k2 (THE (LDROP k1 ll))) =
    THE (LDROP k1 (THE (LDROP k2 ll)))`,
    rw[] >>
    `LDROP (k1+k2) ll = LDROP (k2 + k1) ll` by fs[] >>
    fs[LDROP_ADD] >>
    NTAC 2 (full_case_tac >- imp_res_tac LDROP_NONE_LFINITE) >> fs[])

val TAKE_TAKE_MIN = Q.store_thm("TAKE_TAKE_MIN",
  `!m n. TAKE n (TAKE m l) = TAKE (MIN n m) l`,
  Induct_on`l` >> rw[] >>
  Cases_on`m` >> Cases_on`n` >> fs[MIN_DEF] >> CASE_TAC >> fs[]);

val SPLITP_TAKE_DROP = Q.store_thm("SPLITP_TAKE_DROP",
 `!P i l. EVERY ($~ ∘ P) (TAKE i l) ==>
  P (EL i l) ==>
  SPLITP P l = (TAKE i l, DROP i l)`,
  Induct_on`l` >> rw[SPLITP] >> Cases_on`i` >> fs[] >>
  res_tac >> fs[FST,SND]);

val SND_SPLITP_DROP = Q.store_thm("SND_SPLITP_DROP",
 `!P n l. EVERY ($~ o P) (TAKE n l) ==>
   SND (SPLITP P (DROP n l)) = SND (SPLITP P l)`,
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >> fs[SPLITP]);

val FST_SPLITP_DROP = Q.store_thm("FST_SPLITP_DROP",
 `!P n l. EVERY ($~ o P) (TAKE n l) ==>
   FST (SPLITP P l) = (TAKE n l) ++ FST (SPLITP P (DROP n l))`,
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >>
 PURE_REWRITE_TAC[DROP_def,TAKE_def,APPEND] >> simp[] >>
 fs[SPLITP]);

(* computes the next position for which P holds *)
val Lnext_def = tDefine "Lnext" `
  Lnext P ll = if eventually P ll then
                        if P ll then 0
                        else SUC(Lnext P (THE (LTL ll)))
                     else ARB`
 (exists_tac``\(P,ll') (P',ll).
    ((P = P') /\ eventually P ll /\ eventually P ll' /\
    (LTL ll = SOME ll') /\ ¬ P ll)`` >>
    reverse(rw[relationTheory.WF_DEF,eventually_thm])
  >-(Cases_on`ll` >> fs[])
  >-(Cases_on`ll` >> fs[]) >>
  Cases_on`w` >> rename[`B(P, ll)`] >> rename[`B(P, ll)`] >>
  reverse(Cases_on`eventually P ll`)
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  rpt(LAST_X_ASSUM MP_TAC) >> qid_spec_tac `ll` >>
  HO_MATCH_MP_TAC eventually_ind >> rw[]
  >-(qexists_tac`(P,ll)` >> rw[] >> pairarg_tac >> fs[] >> res_tac >> rfs[]) >>
  Cases_on`B(P,ll)` >-(metis_tac[]) >>
  qexists_tac`(P,h:::ll)` >> fs[] >> rw[] >> pairarg_tac >> fs[]);

val Lnext_pos_def = Define`
  Lnext_pos (ll :num llist) = Lnext (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0) ll`

val OPTION_CHOICE_EQUALS_OPTION = Q.store_thm("OPTION_CHOICE_EQUALS_OPTION",
  `!(x:'a option) y z. (OPTION_CHOICE x y = SOME z) <=>
                       ((x = SOME z) \/ ((x = NONE) /\ (y = SOME z)))`,
 rw[] \\ Cases_on `x` \\ Cases_on `y` \\ fs[]);

val _ =  save_thm("option_eq_some",
    LIST_CONJ [
    OPTION_IGNORE_BIND_EQUALS_OPTION,
    OPTION_BIND_EQUALS_OPTION,
    OPTION_CHOICE_EQUALS_OPTION]);

val SUM_MAP_K = Q.store_thm("SUM_MAP_K",
  `∀f ls c. (∀x. f x = c) ⇒ SUM (MAP f ls) = LENGTH ls * c`,
  rw[] \\ Induct_on`ls` \\ rw[MULT_SUC]);

val LAST_FLAT = Q.store_thm("LAST_FLAT",
  `∀ls. ~NULL (FLAT ls) ==> (LAST (FLAT ls) = LAST (LAST (FILTER ($~ o NULL) ls)))`,
  ho_match_mp_tac SNOC_INDUCT \\ rw[]
  \\ fs[FLAT_SNOC,FILTER_SNOC]
  \\ Cases_on`x` \\ fs[]);

val TOKENS_FRONT = Q.store_thm("TOKENS_FRONT",
  `¬NULL ls ∧ P (LAST ls) ⇒
   TOKENS P (FRONT ls) = TOKENS P ls`,
  Induct_on`ls` \\ rw[]
  \\ Cases_on`ls` \\ fs[]
  >- rw[TOKENS_def,SPLITP]
  \\ rw[TOKENS_def]
  \\ pairarg_tac
  \\ simp[Once SPLITP]
  \\ CASE_TAC \\ fs[NULL_EQ]
  >- (
    imp_res_tac SPLITP_NIL_IMP
    \\ fs[] )
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`l` \\ fs[] \\ rveq
  \\ imp_res_tac SPLITP_IMP
  \\ CASE_TAC \\ fs[]
  \\ qmatch_goalsub_rename_tac`SPLITP P (x::xs)`
  \\ `∃y ys. x::xs = SNOC y ys` by metis_tac[SNOC_CASES,list_distinct]
  \\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC] \\ rveq
  \\ qmatch_goalsub_rename_tac`SPLITP P (SNOC y (w ++ z))`
  \\ Cases_on`NULL z` \\ fs[NULL_EQ]
  >- (
    simp[SPLITP_APPEND]
    \\ full_simp_tac std_ss [GSYM NOT_EXISTS]
    \\ simp[SPLITP,TOKENS_def] )
  \\ Cases_on`z` \\ fs[]
  \\ simp[SPLITP_APPEND]
  \\ full_simp_tac std_ss [GSYM NOT_EXISTS]
  \\ simp[SPLITP,TOKENS_def]
  \\ simp[TOKENS_APPEND,TOKENS_NIL]);

val TOKENS_unchanged = Q.store_thm("TOKENS_unchanged",
  `EVERY ($~ o P) ls ==> TOKENS P ls = if NULL ls then [] else [ls]`,
  Induct_on`ls` \\ rw[TOKENS_def] \\ fs[]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`r=[]` \\ fs[]
  >- ( imp_res_tac SPLITP_NIL_IMP \\ rveq \\ fs[TOKENS_NIL] )
  \\ rw[]
  >- (
    imp_res_tac SPLITP_NIL_IMP
    \\ rfs[] \\ rveq \\ fs[] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ fs[EVERY_MEM]
  \\ `MEM (HD r) (l ++ r)` by (Cases_on`r` \\ fs[])
  \\ Cases_on`MEM (HD r) l` \\ fs[] >- metis_tac[]
  \\ `MEM (HD r) (h::ls)` by metis_tac[MEM_APPEND]
  \\ fs[] \\ rw[] \\ metis_tac[]);

val TOKENS_FLAT_MAP_SNOC = Q.store_thm("TOKENS_FLAT_MAP_SNOC",
  `EVERY (EVERY ((<>) x)) ls ∧ EVERY ($~ o NULL) ls ==>
   TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls`,
  Induct_on`ls` \\ rw[TOKENS_NIL]
  \\ Q.ISPEC_THEN`x`(mp_tac o GSYM) CONS_APPEND
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ disch_then(rewrite_tac o mlibUseful.sing)
  \\ DEP_REWRITE_TAC[TOKENS_APPEND] \\ rw[]
  \\ DEP_REWRITE_TAC[TOKENS_unchanged]
  \\ fs[EVERY_MEM]);

(* insert a string (l1) at specified index (n) in a list (l2) *)
val insert_atI_def = Define`
  insert_atI l1 n l2 =
    TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2
`;

val insert_atI_NIL = Q.store_thm(
  "insert_atI_NIL",
  `∀n l.insert_atI [] n l = l`,
  simp[insert_atI_def]);

val insert_atI_CONS = Q.store_thm(
  "insert_atI_CONS",
  `∀n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (h::t) n l = LUPDATE h n (insert_atI t (n + 1) l)`,
  simp[insert_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]);

val LENGTH_insert_atI = Q.store_thm(
  "LENGTH_insert_atI",
  `p + LENGTH l1 <= LENGTH l2 ⇒ LENGTH (insert_atI l1 p l2) = LENGTH l2`,
  simp[insert_atI_def]);

val insert_atI_app = Q.store_thm("insert_atI_app",
  `∀n l c1 c2.  n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
     insert_atI (c1 ++ c2) n l =
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)`,
  Induct_on`c1` >> fs[insert_atI_NIL,insert_atI_CONS,LENGTH_insert_atI,ADD1]);

val insert_atI_end = Q.store_thm("insert_atI_end",
  `insert_atI l1 (LENGTH l2) l2 = l2 ++ l1`,
  simp[insert_atI_def,DROP_LENGTH_TOO_LONG]);

val insert_atI_insert_atI = Q.store_thm("insert_atI_insert_atI",
  `pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1 ++ c2) pos1 l`,
    rw[insert_atI_def,TAKE_SUM,TAKE_APPEND,LENGTH_TAKE_EQ,LENGTH_DROP,
       GSYM DROP_DROP_T,DROP_LENGTH_TOO_LONG,DROP_LENGTH_NIL_rwt]
    >> fs[DROP_LENGTH_NIL_rwt,LENGTH_TAKE,DROP_APPEND1,TAKE_APPEND,TAKE_TAKE,
       DROP_DROP_T,DROP_APPEND2,TAKE_LENGTH_TOO_LONG,TAKE_SUM,LENGTH_DROP]);

val LUPDATE_insert_commute = Q.store_thm(
  "LUPDATE_insert_commute",
  `∀ws pos1 pos2 a w.
     pos2 < pos1 ∧ pos1 + LENGTH ws <= LENGTH a ⇒
     insert_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insert_atI ws pos1 a)`,
  Induct >> simp[insert_atI_NIL,insert_atI_CONS, LUPDATE_commutes]);

val ALIST_FUPDKEY_comm = Q.store_thm("ALIST_FUPDKEY_comm",
 `!k1 k2 f1 f2 l. k1 <> k2 ==>
  ALIST_FUPDKEY k2 f2 (ALIST_FUPDKEY k1 f1 l) =
  ALIST_FUPDKEY k1 f1 (ALIST_FUPDKEY k2 f2 l)`,
  Induct_on`l` >> rw[] >> fs[ALIST_FUPDKEY_def] >>
  Cases_on`h`>> fs[ALIST_FUPDKEY_def] >>
  CASE_TAC >> fs[ALIST_FUPDKEY_def] >>
  CASE_TAC >> fs[ALIST_FUPDKEY_def]);

val A_DELKEY_ALIST_FUPDKEY_comm = Q.store_thm("A_DELKEY_ALIST_FUPDKEY_comm",
  `!ls f x y. x <> y ==>
  A_DELKEY x (ALIST_FUPDKEY y f ls) = (ALIST_FUPDKEY y f (A_DELKEY x ls))`,
  Induct >>  rw[A_DELKEY_def,ALIST_FUPDKEY_def] >>
  Cases_on`h` >> fs[ALIST_FUPDKEY_def] >> TRY CASE_TAC >> fs[A_DELKEY_def]);

val _ = export_theory()
