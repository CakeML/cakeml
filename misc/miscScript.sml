(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)

(* Misc. lemmas (without any compiler constants) *)
Theory misc
Ancestors
  alignment alist arithmetic blast[qualified] bitstring bag byte
  combin container list pred_set finite_map rich_list llist option
  pair sorting relation toto comparison bit sptree words set_sep
  indexedLists string machine_ieee integer_word address[qualified]
  path[qualified] res_quan[qualified] lprefix_lub[qualified]
Libs
  boolSimps mp_then dep_rewrite wordsLib BasicProvers
  ASCIInumbersLib bagLib[qualified] blastLib[qualified]

val _ = ParseExtras.tight_equality()

(* Total version of THE *)
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End

Definition opt_bind_def:
 opt_bind n v e =
   case n of
   | NONE => e
   | SOME n' => (n',v)::e
End

(* Note: This globally hides constants over the reals that gets imported through machine_ieeeTheory *)

val _ = remove_ovl_mapping "max" {Name="max", Thy="realax"}
val _ = remove_ovl_mapping "min" {Name="min", Thy="realax"}
val _ = remove_ovl_mapping "pos" {Name="pos", Thy="real"}
val _ = remove_ovl_mapping "abs" {Name="abs", Thy="realax"}
val _ = remove_ovl_mapping "inf" {Name="inf", Thy="real"}

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))
val rveq = rpt BasicProvers.VAR_EQ_TAC
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
(* -- *)

(* TODO: move/categorize *)

val _ = numLib.temp_prefer_num();

(* theorem behind impl_tac *)
Theorem IMP_IMP =
  METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``

(* used elsewhere in cakeml *)
Theorem SUBSET_IMP:
   s SUBSET t ==> (x IN s ==> x IN t)
Proof
  fs[pred_setTheory.SUBSET_DEF]
QED

Theorem DROP_NIL:
  ∀n xs. DROP n xs = [] ⇔ LENGTH xs ≤ n
Proof
  Induct \\ Cases_on ‘xs’ \\ fs [DROP_def]
QED

Theorem revdroprev:
   ∀l n.
     n ≤ LENGTH l ⇒ (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l)
Proof
  fs [GSYM BUTLASTN_def,BUTLASTN_TAKE]
QED

Theorem revtakerev:
   ∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l
Proof
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]
QED

Theorem times_add_o:
   (λn:num. k * n + x) = ($+ x) o ($* k)
Proof
  rw[FUN_EQ_THM]
QED

Theorem SORTED_inv_image_LESS_PLUS:
   SORTED (inv_image $< (arithmetic$+ k)) = SORTED $<
Proof
  simp[FUN_EQ_THM]
  \\ Induct
  \\ Q.ISPEC_THEN`$+ k`(fn th => simp[MATCH_MP SORTED_EQ th])
      (MATCH_MP transitive_inv_image transitive_LESS)
  \\ simp[MATCH_MP SORTED_EQ transitive_LESS]
QED

Theorem SORTED_GENLIST_TIMES:
   0 < k ⇒ ∀n. SORTED prim_rec$< (GENLIST ($* k) n)
Proof
  strip_tac
  \\ Induct \\ simp[GENLIST,SNOC_APPEND]
  \\ simp[MEM_GENLIST,PULL_EXISTS,SORTED_APPEND]
QED

(* this is
     read_bytearray a c gb = OPT_MMAP gb (GENLIST (λi. a + n2w i) c)
*)
Definition read_bytearray_def:
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))
End

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)
Theorem read_bytearray_LENGTH:
   !n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)
Proof
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac
QED

Definition shift_seq_def:
  shift_seq k s = \i. s (i + k:num)
End

(* TODO: Used once in all of CakeML: could probably be pushed back to use-site*)
Theorem SUM_SET_IN_LT:
   !s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s
Proof
  metis_tac[SUM_SET_IN_LE,LESS_LESS_EQ_TRANS]
QED

(* only used in proof of tlookup_bij_iff *)
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s
Proof
  rw[]
  \\ `SURJ f s s` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
  \\ `IMAGE f s ⊆ s` by metis_tac[SUBSET_DEF,IN_IMAGE]
  \\ metis_tac[SUBSET_EQ_CARD,IMAGE_FINITE]
QED

(* never used *)
Theorem CARD_IMAGE_EQ_BIJ:
   ∀s. FINITE s ⇒ CARD (IMAGE f s) = CARD s ⇒ BIJ f s (IMAGE f s)
Proof
  rw[]
  \\ `SURJ f s (IMAGE f s)` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
QED

(* used only in clos_callProof -
   HOL has DISJOINT_IMAGE:
     |- (!x y. f x = f y <=> x = y) ==>
        (DISJOINT (IMAGE f x) (IMAGE f y) <=> DISJOINT x y
*)
Theorem DISJOINT_IMAGE_SUC:
   DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y
Proof
  fs [IN_DISJOINT] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]
QED

(* disgusting and used only in clos_callProof *)
Theorem IMAGE_SUC_SUBSET_UNION:
   IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
    x SUBSET y UNION z
Proof
  fs [SUBSET_DEF] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]
QED

Overload LLOOKUP = “λl n. oEL n l”

Theorem LLOOKUP_def =
  listTheory.oEL_def
Theorem LLOOKUP_EQ_EL =
  listTheory.oEL_EQ_EL
Theorem LLOOKUP_THM =
  listTheory.oEL_THM
Theorem LLOOKUP_DROP =
  listTheory.oEL_DROP
Theorem LLOOKUP_TAKE_IMP =
  listTheory.oEL_TAKE_E
Theorem LLOOKUP_LUPDATE =
  listTheory.oEL_LUPDATE

(* app_list stuff should be in an app_list theory *)
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End

Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End

Definition append_def:
  append l = append_aux l []
End

Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs
Proof
  Induct \\ metis_tac [APPEND,APPEND_ASSOC,append_aux_def]
QED

Theorem append_thm[simp]:
   append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []
Proof
  fs [append_def,append_aux_def]
  \\ once_rewrite_tac [append_aux_thm] \\ fs []
QED

Definition SmartAppend_def[simp]:
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)
End

Theorem SmartAppend_thm:
   ∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2
Proof
  Cases \\ Cases \\ rw[]
QED

Theorem SmartAppend_Nil:
  SmartAppend l Nil = l ∧
  SmartAppend Nil l = l
Proof
  Cases_on ‘l’ \\ gvs [SmartAppend_def]
QED

Theorem append_SmartAppend[simp]:
   append (SmartAppend l1 l2) = append l1 ++ append l2
Proof
  rw[append_def,SmartAppend_thm,append_aux_def]
  \\ rw[Once append_aux_thm]
QED

(* instant derivation from LIST_EQ_REWRITE *)
Theorem GENLIST_eq_MAP:
   GENLIST f n = MAP g ls ⇔
   LENGTH ls = n ∧ ∀m. m < n ⇒ f m = g (EL m ls)
Proof
  srw_tac[][LIST_EQ_REWRITE,EQ_IMP_THM,EL_MAP]
QED

(* TODO - already in HOL as ZIP_GENLIST *)
Theorem ZIP_GENLIST1:
   ∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n
Proof
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]
QED

(* MAP3 never used *)
Definition MAP3_def[simp]:
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
End

val MAP3_ind = theorem"MAP3_ind";

Theorem LENGTH_MAP3[simp]:
   ∀f l1 l2 l3. LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3 ⇒ LENGTH (MAP3 f l1 l2 l3) = LENGTH l3
Proof
  ho_match_mp_tac MAP3_ind \\ rw[]
QED

Theorem EL_MAP3:
   ∀f l1 l2 l3 n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ n < LENGTH l3 ⇒
    EL n (MAP3 f l1 l2 l3) = f (EL n l1) (EL n l2) (EL n l3)
Proof
  ho_match_mp_tac MAP3_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]
QED

(* used once *)
Theorem MAP_REVERSE_STEP:
   ∀x f. x ≠ [] ⇒ MAP f (REVERSE x) = f (LAST x) :: MAP f (REVERSE (FRONT x))
Proof
  recInduct SNOC_INDUCT
  \\ rw [FRONT_APPEND]
QED

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)
Theorem LENGTH_TAKE_EQ_MIN:
   !n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)
Proof
  simp[LENGTH_TAKE_EQ] \\ full_simp_tac(srw_ss())[MIN_DEF] \\ decide_tac
QED

(* should be switched in orientation; looks like an attempt to get congruence
   rule *)
Theorem LIST_REL_MEM:
   !xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys
Proof
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]
QED

(* only used in theorem immediately below *)
Theorem LIST_REL_GENLIST_I:
   !xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)
Proof
  simp[LIST_REL_EL_EQN]
QED

(* only used in bvi_to_dataProof *)
Theorem LIST_REL_lookup_fromList:
   LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args
Proof
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]
QED

Theorem LIST_REL_lookup_fromList_MAP:
   LIST_REL (λv x. ∃z. lookup v (fromList args) = SOME z ∧ x = f z)
    (GENLIST I (LENGTH args)) (MAP f args)
Proof
  fs [LIST_REL_MAP2,LIST_REL_GENLIST_I,lookup_fromList]
QED

(* only used in examples/stackProg; oriented badly *)
Theorem LIST_REL_FRONT_LAST:
   l1 <> [] /\ l2 <> [] ==>
    (LIST_REL A l1 l2 <=>
     LIST_REL A (FRONT l1) (FRONT l2) /\ A (LAST l1) (LAST l2))
Proof
  map_every
    (fn q => Q.ISPEC_THEN q FULL_STRUCT_CASES_TAC SNOC_CASES >>
             fs[LIST_REL_SNOC])
    [`l1`,`l2`]
QED

Theorem lemmas[local]:
  (2 + 2 * n - 1 = 2 * n + 1:num) /\
    (2 + 2 * n' = 2 * n'' + 2 <=> n' = n'':num) /\
    (2 * m = 2 * n <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)
Proof
  intLib.ARITH_TAC
QED

Definition lookup_any_def:
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m
End

Definition fromList2_def:
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)
End

Theorem EVEN_fromList2_lemma[local]:
  !l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x
Proof
  Induct \\ full_simp_tac(srw_ss())[FOLDL] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC
QED

Theorem EVEN_fromList2:
   !l n. n IN domain (fromList2 l) ==> EVEN n
Proof
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ full_simp_tac(srw_ss())[]
QED

Theorem SUBMAP_mono_FUPDATE_LIST:
   ∀ls f g.
   DRESTRICT f (COMPL (set (MAP FST ls))) ⊑
   DRESTRICT g (COMPL (set (MAP FST ls)))
   ⇒ f |++ ls ⊑ g |++ ls
Proof
  Induct \\ rw[FUPDATE_LIST_THM, DRESTRICT_UNIV]
  \\ first_x_assum MATCH_MP_TAC
  \\ Cases_on`h`
  \\ fs[SUBMAP_FLOOKUP_EQN]
  \\ rw[] \\ fs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
  \\ rw[] \\ fs[]
  \\ METIS_TAC[]
QED

Theorem INJ_FAPPLY_FUPDATE:
   INJ ($' f) (FDOM f) (FRANGE f) ∧
   s = k INSERT FDOM f ∧ v ∉ FRANGE f ∧
   t = v INSERT FRANGE f
  ⇒
   INJ ($' (f |+ (k,v))) s t
Proof
  srw_tac[][INJ_DEF,FAPPLY_FUPDATE_THM] >> srw_tac[][] >>
  pop_assum mp_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[IN_FRANGE] >>
  METIS_TAC[]
QED

(* used in only one place: stack_to_labProof *)
Theorem BIJ_FLOOKUP_MAP_KEYS:
   BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)
Proof
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]
QED

Theorem SPLIT_LIST:
   !xs.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)
Proof
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ full_simp_tac(srw_ss())[DIV_LE_X] \\ DECIDE_TAC
QED

Theorem EXISTS_ZIP:
   !l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []
QED

Theorem EVERY_ZIP:
   !l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []
QED

Theorem every_zip_split:
   !l1 l2 P Q.
    LENGTH l1 = LENGTH l2 ⇒
    (EVERY (\(x,y). P x ∧ Q y) (ZIP (l1, l2)) ⇔ EVERY P l1 ∧ EVERY Q l2)
Proof
 Induct_on `l1`
 >> simp []
 >> Cases_on `l2`
 >> rw []
 >> metis_tac []
QED

Theorem every_shim:
 !l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw []
QED

Theorem every_shim2:
 !l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw [] >>
metis_tac []
QED

Theorem MEM_ZIP2:
    ∀l1 l2 x.
  MEM x (ZIP (l1,l2)) ⇒
  ∃n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ x = (EL n l1,EL n l2)
Proof
  Induct>>fs[ZIP_def]>>
  Cases_on`l2`>>fs[ZIP_def]>>
  rw[]
  >-
    (qexists_tac`0n`>>fs[])
  >>
    first_x_assum drule>>
    rw[]>>
    qexists_tac`SUC n`>>fs[]
QED

Theorem ZIP_MAP_FST_SND_EQ:
   ∀ls. ZIP (MAP FST ls,MAP SND ls) = ls
Proof
  Induct>>full_simp_tac(srw_ss())[]
QED

Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs
Proof
  Induct \\ fs [FORALL_PROD]
QED

Theorem EVERY_FST_SND:
   EVERY (λ(a,b). P a ∧ Q b) ls ⇔ EVERY P (MAP FST ls) ∧ EVERY Q (MAP SND ls)
Proof
  rw[EVERY_MEM,MEM_MAP,UNCURRY,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]
QED

Definition zlookup_def:
  zlookup m k = case lookup k m of NONE => 0n | SOME k => k
End

Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End

Theorem tlookup_id:
   x ∉ domain names
   ⇒ tlookup names x = x
Proof
  rw[tlookup_def]
  \\ fs[domain_lookup] \\ CASE_TAC \\ fs[]
QED

Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV
Proof
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
  \\ metis_tac[]
QED

Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names
Proof
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
  \\ metis_tac[]
QED

(* should be composition of oEL and as-yet-undefined "THE default" *)
Definition any_el_def:
  (any_el n [] d = d) /\
  (any_el n (x::xs) d = if n = 0 then x else any_el (n-1:num) xs d)
End

Definition update_resize_def:
  update_resize ls default v n =
    if n < LENGTH ls then
      LUPDATE v n ls
    else
      LUPDATE v n (ls ++ REPLICATE (n * 2 + 1 - LENGTH ls) default)
End

(*TODO upstream*)
Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys)
Proof
  Induct_on `xs` >> simp[AC MAX_COMM MAX_ASSOC]
QED

(*Or should it be MAX x (MAX_LIST xs)*)
Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x
Proof
  simp[SNOC_APPEND]
QED

Theorem MAX_LIST_intro:
  ∀ls.
  P 0 ∧ EVERY P ls ⇒ P (MAX_LIST ls)
Proof
  Induct>>rpt strip_tac >>
  full_simp_tac(srw_ss())[MAX_DEF,COND_RAND]
QED

Theorem MAX_LIST_max:
  ∀ls. EVERY (λx. x ≤ MAX_LIST ls) ls
Proof
  rw[EVERY_MEM] >> irule MAX_LIST_PROPERTY >> fs[]
QED

Theorem FOLDR_MAX_0_MAX_LIST:
  ∀ls. FOLDR MAX 0 ls = MAX_LIST ls
Proof
  Induct \\ rw[MAX_DEF]
QED

(* never used *)
Definition list_inter_def:
  list_inter xs ys = FILTER (\y. MEM y xs) ys
End

Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End

Theorem ALOOKUP_SNOC:
   ∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE
Proof
  Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][]
QED

Theorem ALOOKUP_GENLIST:
   ∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE
Proof
  gen_tac >> Induct >> simp[GENLIST] >> srw_tac[][] >> full_simp_tac(srw_ss())[ALOOKUP_SNOC] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][]
QED

Theorem ALOOKUP_ZIP_FAIL:
   ∀A B x.
  LENGTH A = LENGTH B ⇒
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)
Proof
  srw_tac[][]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  full_simp_tac(srw_ss())[MAP_ZIP]
QED

Theorem MEM_ALOOKUP:
   !xs x v.
      ALL_DISTINCT (MAP FST xs) ==>
      (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ eq_tac \\ rw [] \\ rfs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []
QED

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
Definition anub_def:
  (anub [] acc = []) ∧
  (anub ((k,v)::ls) acc =
   if MEM k acc then anub ls acc else
   (k,v)::(anub ls (k::acc)))
End

val anub_ind = theorem"anub_ind"

Theorem EVERY_anub_imp:
   ∀ls acc x y.
      EVERY P (anub ((x,y)::ls) acc) ∧ x ∉ set acc
      ⇒
      P (x,y) ∧ EVERY P (anub ls (x::acc))
Proof
  ho_match_mp_tac anub_ind >> srw_tac[][anub_def] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
QED

(* terrible rewrite *)
Theorem ALOOKUP_anub:
   ALOOKUP (anub ls acc) k =
    if MEM k acc then ALOOKUP (anub ls acc) k
    else ALOOKUP ls k
Proof
  qid_spec_tac`acc` >>
  Induct_on`ls` >>
  srw_tac[][anub_def] >>
  Cases_on`h`>>srw_tac[][anub_def]>>full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`acc`mp_tac) >>
    srw_tac[][] ) >>
  first_x_assum(qspec_then`q::acc`mp_tac) >>
  srw_tac[][]
QED

Theorem anub_eq_nil:
   anub x y = [] ⇔ EVERY (combin$C MEM y) (MAP FST x)
Proof
  qid_spec_tac`y` >>
  Induct_on`x`>>srw_tac[][anub_def]>>
  Cases_on`h`>>srw_tac[][anub_def]
QED

Theorem EVERY_anub_suff:
   ∀ls acc.
    (∀x. ¬MEM x acc ⇒ case ALOOKUP ls x of SOME v => P (x,v) | NONE => T)
    ⇒ EVERY P (anub ls acc)
Proof
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
  `q ≠ x` by full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
QED

Theorem anub_notin_acc:
   ∀ls acc. MEM x acc ⇒ ¬MEM x (MAP FST (anub ls acc))
Proof
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >>
  metis_tac[]
QED

Theorem anub_tl_anub:
   ∀x y h t. anub x y = h::t ⇒ ∃a b. t = anub a b ∧ set a ⊆ set x ∧ set b ⊆ set ((FST h)::y)
Proof
  Induct >> srw_tac[][anub_def] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[anub_def] >>
  pop_assum mp_tac  >> srw_tac[][] >>
  res_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac[MEM]
QED

Theorem anub_all_distinct_keys:
   ∀ls acc.
    ALL_DISTINCT acc ⇒
    ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)
Proof
  Induct>>srw_tac[][anub_def]>>PairCases_on`h`>>full_simp_tac(srw_ss())[anub_def]>>
  srw_tac[][]>>
  `ALL_DISTINCT (h0::acc)` by full_simp_tac(srw_ss())[ALL_DISTINCT]>>res_tac>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND]>>
  metis_tac[]
QED

Theorem MEM_anub_ALOOKUP:
   MEM (k,v) (anub ls []) ⇒
    ALOOKUP ls k = SOME v
Proof
  srw_tac[][]>>
  Q.ISPECL_THEN[`ls`,`[]`] assume_tac anub_all_distinct_keys>>
  Q.ISPECL_THEN [`ls`,`k`,`[]`] assume_tac (GEN_ALL ALOOKUP_anub)>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM]
QED

Type num_set = ``:unit spt``
Type num_map = ``:'a spt``

Theorem toAList_domain:
    ∀x. MEM x (MAP FST (toAList t)) ⇔ x ∈ domain t
Proof
  full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup]
QED

Theorem domain_nat_set_from_list[simp]:
   ∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls
Proof
  Induct >> simp[sptreeTheory.domain_insert] >>
  srw_tac[][EXTENSION] >> metis_tac[]
QED

Theorem wf_nat_set_from_list:
   ∀ls ns. wf ns ⇒ wf (FOLDL (λs n. insert n z s) ns ls)
Proof
  Induct >> simp[] >> srw_tac[][sptreeTheory.wf_insert]
QED

Theorem BIT_11:
   ∀n m. (BIT n = BIT m) ⇔ (n = m)
Proof
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
  simp[arithmeticTheory.MULT_DIV]
QED

Theorem BIT_11_2:
   ∀n m. (∀z. (z < 2 ** (MAX n m)) ⇒ (BIT n z ⇔ BIT m z)) ⇔ (n = m)
Proof
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
  simp[arithmeticTheory.EXP]
QED

(* only used below in proof of theorem that is in turn used just twice *)
Theorem LOG2_TIMES2:
   0 < n ⇒ (LOG2 (2 * n) = SUC (LOG2 n))
Proof
  srw_tac[][LOG2_def] >>
  qspecl_then[`1`,`2`,`n`]mp_tac logrootTheory.LOG_EXP >>
  simp[arithmeticTheory.ADD1]
QED

(* only used below in proof of theorem that is in turn used just twice *)
Theorem LOG2_TIMES2_1:
   ∀n. 0 < n ⇒ (LOG2 (2 * n + 1) = LOG2 (2 * n))
Proof
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
  metis_tac[]
QED

(* used only twice, both times in candle/set-theory *)
Theorem C_BIT_11:
   ∀n m. (∀z. (z ≤ LOG2 (MAX n m)) ⇒ (BIT z n ⇔ BIT z m)) ⇔ (n = m)
Proof
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
  full_simp_tac arith_ss [BIT_TIMES2_1,BIT_TIMES2]
QED

Theorem BIT_num_from_bin_list_leading:
   ∀l x. EVERY ($> 2) l ∧ LENGTH l ≤ x ⇒ ¬BIT x (num_from_bin_list l)
Proof
  simp[numposrepTheory.num_from_bin_list_def] >>
  srw_tac[][] >>
  MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
  MATCH_MP_TAC arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** LENGTH (REVERSE l)` >>
  simp[numposrepTheory.l2n_lt]
QED

Definition least_from_def:
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P
End

Theorem LEAST_thm:
   $LEAST P = least_from P 0
Proof
  srw_tac[][least_from_def,ETA_AX]
QED

Theorem least_from_thm:
   least_from P n = if P n then n else least_from P (n+1)
Proof
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
    full_simp_tac(srw_ss())[] )
QED

Theorem FUNPOW_mono:
   (∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y
Proof
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> srw_tac[][]
QED

Theorem FUNPOW_SUC_PLUS:
   ∀n a. FUNPOW SUC n = (+) n
Proof
Induct \\ simp[FUNPOW,FUN_EQ_THM]
QED

(* used just once; better as
     transitive R ==> transitive (OPTREL R)
   or that with transitive expanded out *)
Theorem OPTREL_trans:
   ∀R x y z. (∀a b c. (x = SOME a) ∧ (y = SOME b) ∧ (z = SOME c) ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z
Proof
  srw_tac[][optionTheory.OPTREL_def]
QED

Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
val _ = Parse.add_infix("=++",500,Parse.LEFT)

Overload "=++" = ``UPDATE_LIST``

Theorem UPDATE_LIST_THM:
   ∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)
Proof
  srw_tac[][UPDATE_LIST_def,pairTheory.UNCURRY]
QED

Theorem APPLY_UPDATE_LIST_ALOOKUP:
   ∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y
Proof
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  srw_tac[][] >> BasicProvers.CASE_TAC
QED

(* should be using indexedLists$findi, or INDEX_OF *)
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End

Theorem INDEX_FIND_CONS_EQ_SOME:
   (INDEX_FIND n f (x::xs) = SOME y) <=>
    (f x /\ (y = (n,x))) \/
    (~f x /\ (INDEX_FIND (n+1) f xs = SOME y))
Proof
  fs [INDEX_FIND_def] \\ rw [] \\ Cases_on `y` \\ fs [ADD1] \\ metis_tac []
QED

Theorem find_index_INDEX_FIND:
   ∀y xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ($= y) xs)
Proof
  Induct_on`xs` \\ rw[find_index_def]
  \\ rw[Once INDEX_FIND_def,ADD1]
QED

Theorem find_index_INDEX_OF:
   find_index y xs 0 = INDEX_OF y xs
Proof
  rw[INDEX_OF_def,find_index_INDEX_FIND]
QED

Theorem find_index_NOT_MEM:
   ∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)
Proof
  Induct >> srw_tac[][find_index_def]>>
  metis_tac[]
QED

Theorem find_index_MEM:
   !ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)
Proof
  Induct >> srw_tac[][find_index_def] >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  srw_tac[][]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1]
QED

Theorem find_index_LEAST_EL:
   ∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE
Proof
  Induct >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>full_simp_tac(srw_ss())[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> srw_tac[][]) >>
    Cases >> srw_tac[][] >>
    qexists_tac`0` >>simp[])>>
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
  DECIDE_TAC
QED

Theorem find_index_LESS_LENGTH:
 ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)
Proof
Induct >> srw_tac[][find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1]
QED

Theorem ALOOKUP_find_index_NONE:
   (ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)
Proof
  srw_tac[][ALOOKUP_FAILS] >>
  srw_tac[][GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD]
QED

val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >>
  srw_tac[][find_index_def] >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]

Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))
Proof
  srw_tac[][] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> full_simp_tac(srw_ss())[EL_MAP]
QED

Theorem find_index_ALL_DISTINCT_EL[simp]:
 ∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))
Proof
Induct >- srw_tac[][] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL]
QED

Theorem find_index_ALL_DISTINCT_EL_eq:
   ∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)
Proof
  srw_tac[][EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    full_simp_tac(srw_ss())[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    full_simp_tac(srw_ss())[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL]
QED

Theorem find_index_APPEND_same:
   !l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)
Proof
  Induct >> srw_tac[][find_index_def]
QED

Theorem find_index_ALL_DISTINCT_REVERSE:
   ∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))
Proof
  srw_tac[][] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by srw_tac[][ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >> srw_tac[][] >>
  qmatch_assum_rename_tac`z < LENGTH ls` >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1]
QED

Theorem THE_find_index_suff:
   ∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))
Proof
  srw_tac[][] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][]
QED

Theorem find_index_APPEND1:
   ∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)
Proof
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  srw_tac[][] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[]
QED

Theorem find_index_APPEND2:
   ∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)
Proof
  Induct >> simp[find_index_def] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1]
QED

Theorem find_index_is_MEM:
   ∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls
Proof
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE]
QED

Theorem find_index_MAP_inj:
   ∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)
Proof
  Induct >- simp[find_index_def] >>
  srw_tac[][] >> srw_tac[][find_index_def] >>
  metis_tac[]
QED

Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)
Proof
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
  simp[]
QED

Theorem find_index_shift:
   ∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)
Proof
  Induct >> simp[find_index_def] >> srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][]
QED

Theorem find_index_APPEND:
   ∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x
Proof
  Induct >> simp[find_index_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1]
QED

Theorem find_index_in_FILTER_ZIP_EQ:
   ∀P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) ∧
      (FILTER (P o FST) (ZIP(l1,v1)) = l2) ∧
      (find_index x l1 n1 = SOME (n1+j1)) ∧
      (find_index x (MAP FST l2) n2 = SOME (n2+j2)) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      (EL j1 (ZIP(l1,v1)) = EL j2 l2)
Proof
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
  simp[rich_listTheory.EL_CONS]
QED

Theorem ALL_DISTINCT_PERM_ALOOKUP_ZIP:
   ∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))
Proof
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
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF]
QED

(* surely better with UNZIP rather than ZIP: i.e., UNZIP l1 = (a,b)...  *)
Theorem PERM_ZIP:
   ∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. (l1 = ZIP(a,b)) ∧ (l2 = ZIP(c,d)) ∧ (LENGTH a = LENGTH b) ∧ (LENGTH c = LENGTH d) ⇒
    PERM a c ∧ PERM b d
Proof
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
  metis_tac[PERM_TRANS]
QED

(* never used *)
Theorem RTC_invariant:
   !R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER]
QED

(* never used *)
Theorem RTC_RSUBSET:
   !R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)
Proof
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1]
QED

Theorem PERM_PART:
   ∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)
Proof
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
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC]
QED

Theorem PERM_PARTITION:
   ∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)
Proof
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL]
QED

Theorem option_case_NONE_F:
   (case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)
Proof
  Cases_on`X`>>srw_tac[][]
QED

Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
Proof
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] )
QED

Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l
Proof
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF]
QED

(* used twice, and only in source_to_flatProof *)
Theorem FOLDL_invariant:
   !P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)
Proof
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][]
QED

(* never used *)
Theorem FOLDL_invariant_rest:
   ∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)
Proof
  ntac 2 gen_tac >>
  Induct >> srw_tac[][] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> srw_tac[][]
QED

Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End

Theorem IN_between:
   x ∈ between y z ⇔ y ≤ x ∧ x < z
Proof
  rw[IN_DEF] \\ EVAL_TAC
QED

(* never used *)
Theorem SUC_LEAST:
   !x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))
Proof
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
  DECIDE_TAC
QED

(* never used *)
Definition fmap_linv_def:
  fmap_linv f1 f2 ⇔ (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))
End

(* never used *)
Theorem fmap_linv_unique:
   !f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)
Proof
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[]
QED

(* never used *)
Theorem INJ_has_fmap_linv:
   INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g
Proof
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF]
QED

(* never used *)
Theorem has_fmap_linv_inj:
   (?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))
Proof
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] )
QED

(* never used *)
Theorem fmap_linv_FAPPLY:
   fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)
Proof
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF]
QED

(* TODO - candidate for move to HOL *)
Theorem plus_compose:
   !n:num m. $+ n o $+ m = $+ (n + m)
Proof
  SRW_TAC[ARITH_ss][FUN_EQ_THM]
QED

(* TODO: move elsewhere? export as rewrite? *)
(* never used *)
Theorem IN_option_rwt:
 (x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)
Proof
Cases_on `opt` >> srw_tac[][EQ_IMP_THM]
QED

(* never used *)
Theorem IN_option_rwt2:
 x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y
Proof
Cases_on `opt` >> srw_tac[][]
QED

(* Re-expressing folds *)

(* only used in flat_elimProof *)
Theorem FOLDR_CONS_triple:
 !f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a
Proof
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][]
QED

(* never used *)
Theorem FOLDR_CONS_5tup:
 !f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a
Proof
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][]
QED

(* never used *)
Theorem FOLDR_transitive_property:
 !P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)
Proof
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][]
QED

(* Re-expressing curried lambdas *)

Theorem FST_triple:
 (λ(n,ns,b). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem FST_5tup:
 (λ(n,ns,b,x,y). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_triple:
 (λ(n,ns,b). f ns b) = UNCURRY f o SND
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

Theorem FST_pair:
 (λ(n,v). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_pair:
 (λ(n,v). v) = SND
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_FST_pair:
 (λ((n,m),c).m) = SND o FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem MAP_ZIP_SND_triple:
 (LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)
Proof
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC)
QED

(* Specialisations to identity function *)

Theorem I_PERMUTES[simp]:
   I PERMUTES s
Proof
rw[BIJ_DEF, INJ_DEF, SURJ_DEF]
QED

(* never used *)
Theorem INJ_I:
 ∀s t. INJ I s t ⇔ s ⊆ t
Proof
SRW_TAC[][INJ_DEF,SUBSET_DEF]
QED


Theorem MAP_EQ_ID:
 !f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))
Proof
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM]
QED

(* Specialisations to FEMPTY *)

Theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]:
 FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)
Proof
Cases_on `x IN s` >>
srw_tac[][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY]
QED

(* FUPDATE_LIST stuff *)

(* Misc. *)

Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num)
Proof
DECIDE_TAC
QED



  (* --------- SO additions --------- *)

Theorem map_fst:
 !l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l
Proof
Induct_on `l` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]
QED

(* use INJ_MAP_EQ_IFF and INJ_DEF *)
Theorem map_some_eq:
 !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)
Proof
 Induct_on `l1` >>
 srw_tac[][] >>
 Cases_on `l2` >>
 srw_tac[][]
QED

(* never used *)
Theorem map_some_eq_append:
 !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
Proof
metis_tac [map_some_eq, MAP_APPEND]
QED

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];


(* list misc *)

Theorem LASTN_LEMMA:
   (LASTN (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LASTN (LENGTH xs + 1) (x::xs) = x::xs)
Proof
  MP_TAC (Q.SPEC `x::y::xs` LASTN_LENGTH_ID)
  \\ MP_TAC (Q.SPEC `x::xs` LASTN_LENGTH_ID) \\ full_simp_tac(srw_ss())[ADD1]
QED

Theorem LASTN_TL =
  LASTN_CONS |> Q.SPECL[`n+1`,`xs`]
  |> C MP (DECIDE``n < LENGTH xs ⇒ n + 1 ≤ LENGTH xs`` |> UNDISCH)
  |> SPEC_ALL |> DISCH_ALL

Theorem LASTN_LENGTH_LESS_EQ:
   !xs n. LENGTH xs <= n ==> LASTN n xs = xs
Proof
  full_simp_tac(srw_ss())[LASTN_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [listTheory.TAKE_LENGTH_TOO_LONG] \\ full_simp_tac(srw_ss())[]
QED

Theorem LASTN_ALT:
   (LASTN n [] = []) /\
    (LASTN n (x::xs) = if LENGTH (x::xs) <= n then x::xs else LASTN n xs)
Proof
  srw_tac[][] THEN1 (full_simp_tac(srw_ss())[LASTN_def])
  THEN1 (match_mp_tac LASTN_LENGTH_LESS_EQ \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[LASTN_def] \\ REPEAT STRIP_TAC
  \\ `n <= LENGTH (REVERSE xs)` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ full_simp_tac(srw_ss())[]
QED

Theorem LENGTH_LASTN_LESS:
   !xs n. LENGTH (LASTN n xs) <= LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `n` assume_tac)
  \\ decide_tac
QED

Theorem MAP_EQ_MAP_IMP:
   !xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)
Proof
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP] \\ METIS_TAC []
QED
(*
NB: this is weaker:
Theorem MAP_EQ_MAP_IMP =
  INJ_MAP_EQ |> SIMP_RULE (srw_ss()) [INJ_DEF]
*)

Theorem INJ_MAP_EQ_2:
   ∀f l1 l2.
   (∀x y. x ∈ set l1 ∧ y ∈ set l2 ∧ f x = f y ⇒ x = y) ∧
   MAP f l1 = MAP f l2 ⇒
   l1 = l2
Proof
  gen_tac \\ Induct \\ rw[]
  \\ Cases_on`l2` \\ pop_assum mp_tac \\ rw[]
QED

Theorem LENGTH_EQ_FILTER_FILTER:
   !xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))
Proof
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]
QED

Theorem LIST_REL_MAP_FILTER_NEQ:
   ∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))
Proof
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND]
QED

(* move into HOL? *)

Definition word_list_def:
  (word_list a [] = emp) /\
  (word_list a (x::xs) = set_sep$one (a,x) * word_list (a + bytes_in_word) xs)
End

Definition word_list_exists_def:
  word_list_exists a n =
    SEP_EXISTS xs. word_list a xs * cond (LENGTH xs = n)
End

(* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End

Theorem EVERY_lookup_vars:
   ∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'
Proof
  Induct >> simp[lookup_vars_def, CaseEq"option", CaseEq"bool", PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]
QED

Theorem EVERY_LAST:
   !P l. l ≠ [] /\ EVERY P l ==> P (LAST l)
Proof
  rw [LAST_EL, EVERY_EL, NOT_NIL_EQ_LENGTH_NOT_0]
QED

(* TODO - candidate for move to HOL *)
Theorem num_to_hex_string_length_1:
   ∀x. x < 16 ⇒ (LENGTH (num_to_hex_string x) = 1)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC
QED

(* TODO - candidate for move to HOL *)
Theorem num_to_hex_string_length_2:
   ∀x. 16 ≤ x ∧ x < 256 ⇒ (LENGTH (num_to_hex_string x) = 2)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV (RAND_CONV EVAL))
  \\ strip_tac \\ var_eq_tac \\ pop_assum mp_tac
  \\ EVAL_TAC
QED

Theorem num_from_hex_string_length_2:
   num_from_hex_string [d1;d2] < 256
Proof
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`UNHEX d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`UNHEX d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac
QED

Theorem num_from_hex_string_leading_0:
   ∀ls. ls ≠ [] ⇒ (num_from_hex_string (#"0" :: ls) = num_from_hex_string ls)
Proof
  simp[ASCIInumbersTheory.num_from_hex_string_def,ASCIInumbersTheory.s2n_def]
  \\ ho_match_mp_tac SNOC_INDUCT \\ simp[]
  \\ simp[REVERSE_SNOC]
  \\ simp[numposrepTheory.l2n_def]
  \\ rw[]
  \\ Cases_on`ls` \\ fs[numposrepTheory.l2n_def]
  \\ EVAL_TAC
QED

Theorem num_from_hex_string_length_2_less_16:
   ∀h1 h2. isHexDigit h1 ⇒ num_from_hex_string [h1;h2] < 16 ⇒ h1 = #"0"
Proof
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
  \\ fs[ASCIInumbersTheory.UNHEX_def]
QED

Theorem num_from_hex_string_num_to_hex_string[simp]:
   num_from_hex_string (num_to_hex_string n) = n
Proof
  ASCIInumbersTheory.num_hex_string
  |> SIMP_RULE std_ss [combinTheory.o_DEF,FUN_EQ_THM]
  |> MATCH_ACCEPT_TAC
QED

Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I
Proof
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]
QED

(* TODO - candidate for move to HOL - though
     enumerate i0 l = MAPi (λx i. (i + i0, x)) l
*)
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)
End

(* TODO - candidate for move to HOL *)
Theorem LENGTH_enumerate:
    ∀xs k. LENGTH (enumerate k xs) = LENGTH xs
Proof
  Induct>>fs[enumerate_def]
QED

Theorem EL_enumerate:
    ∀xs n k.
  n < LENGTH xs ⇒
  EL n (enumerate k xs) = (n+k,EL n xs)
Proof
  Induct>>fs[enumerate_def]>>rw[]>>
  Cases_on`n`>>fs[]
QED

Theorem MAP_enumerate_MAPi:
    ∀f xs.
  MAP f (enumerate 0 xs) = MAPi (λn e. f (n,e)) xs
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MAPi_enumerate_MAP:
    ∀f xs.
  MAPi f xs = MAP (λi,e. f i e) (enumerate 0 xs)
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MEM_enumerate:
    ∀xs i e.
  i < LENGTH xs ⇒
  (MEM (i,e) (enumerate 0 xs) ⇔ EL i xs = e)
Proof
  fs[MEM_EL]>>rw[]>>eq_tac>>rw[LENGTH_enumerate]>>
  imp_res_tac EL_enumerate>>fs[]>>
  qexists_tac`i`>>fs[]
QED

Theorem MEM_enumerate_IMP:
  ∀ls k.
  MEM (i,e) (enumerate k ls) ⇒ MEM e ls
Proof
  Induct_on`ls`>>fs[enumerate_def]>>rw[]>>
  metis_tac[]
QED

Theorem MAP_FST_enumerate:
  MAP FST (enumerate k ls) = GENLIST ($+ k) (LENGTH ls)
Proof
  rw[LIST_EQ_REWRITE,LENGTH_enumerate]>>
  simp[EL_MAP,LENGTH_enumerate,EL_enumerate]
QED

Theorem ALL_DISTINCT_MAP_FST_enumerate:
  ALL_DISTINCT (MAP FST (enumerate k ls))
Proof
  simp[MAP_FST_enumerate,ALL_DISTINCT_GENLIST]
QED

Theorem ALOOKUP_enumerate:
  ∀ls k x.
  ALOOKUP (enumerate k ls) x =
  if k ≤ x ∧ x < LENGTH ls + k then SOME (EL (x-k) ls) else NONE
Proof
  Induct>>rw[enumerate_def]>>
  `x-k = SUC(x-(k+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem SUM_MAP_LENGTH_REPLICATE:
   ∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls
Proof
  Induct >> simp[REPLICATE,MULT]
QED

Theorem SUM_MAP_COUNT_LIST:
   !n k. SUM (MAP ($+ k) (COUNT_LIST n)) = (n * (2 * k + n - 1)) DIV 2
Proof
  Induct \\ rw [COUNT_LIST_def]
  \\ `!xs. MAP SUC xs = MAP ($+ 1) xs` by (Induct \\ rw [])
  \\ pop_assum (qspec_then `COUNT_LIST n` SUBST1_TAC)
  \\ pop_assum (qspec_then `k + 1` mp_tac)
  \\ simp [MAP_MAP_o, o_DEF]
  \\ `$+ (k + 1) = \x. k + (x + 1)` by fs [FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC \\ rw [ADD1]
  \\ fs [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  \\ metis_tac [ADD_DIV_ADD_DIV, MULT_COMM, DECIDE ``0n < 2``]
QED

Theorem SUM_REPLICATE:
   ∀n m. SUM (REPLICATE n m) = n * m
Proof
  Induct \\ simp[REPLICATE,ADD1]
QED

Theorem SUM_MAP_BOUND:
    (∀x. f x ≤ c) ⇒ (SUM (MAP f ls) ≤ LENGTH ls * c)
Proof
  rw[]>> Induct_on`ls` >>rw[MULT_SUC]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  DECIDE_TAC
QED

Theorem SUM_MOD:
    k > 0 ⇒
  (SUM ls MOD k = (SUM (MAP (λn. n MOD k) ls)) MOD k)
Proof
  Induct_on`ls`>>rw[]>>
  DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS]>>fs[]
QED

Theorem MOD_SUB_LEMMA:
   n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0
Proof
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ once_rewrite_tac[GSYM MOD_PLUS]
  \\ fs[]
QED

Theorem FLAT_REPLICATE_NIL:
   !n. FLAT (REPLICATE n []) = []
Proof
  Induct \\ fs [REPLICATE]
QED

Theorem MEM_REPLICATE_EQ:
   !n x y. MEM x (REPLICATE n y) <=> x = y /\ n <> 0
Proof
  Induct \\ fs [REPLICATE] \\ rw [] \\ eq_tac \\ rw []
QED

(* n.b. used in hol-reflection *)

Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
Proof
  rw[FLOOKUP_DEF]
QED

Theorem FLAT_MAP_SING:
   ∀ls. FLAT (MAP (λx. [f x]) ls) = MAP f ls
Proof
  Induct \\ simp[]
QED

Theorem FLAT_MAP_NIL:
   FLAT (MAP (λx. []) ls) = []
Proof
  rw[FLAT_EQ_NIL,EVERY_MAP]
QED

Theorem UPDATE_LIST_NOT_MEM:
   ∀ls f x. ¬MEM x(MAP FST ls) ⇒ (f =++ ls) x = f x
Proof
  Induct >> simp[UPDATE_LIST_THM,combinTheory.APPLY_UPDATE_THM]
QED

Theorem MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same:
   ∀ks vs f. LENGTH ks = LENGTH vs ∧ ALL_DISTINCT ks ⇒ (MAP (f =++ ZIP (ks,vs)) ks = vs)
Proof
  Induct >> simp[LENGTH_NIL_SYM] >>
  gen_tac >> Cases >> simp[UPDATE_LIST_THM] >>
  simp[UPDATE_LIST_NOT_MEM,MAP_ZIP,combinTheory.APPLY_UPDATE_THM]
QED

Theorem flookup_update_list_none:
 !x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (ALOOKUP l x = NONE))
Proof
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []
QED

Theorem flookup_update_list_some:
 !x m l y.
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((ALOOKUP (REVERSE l) x = SOME y) ∨
   ((ALOOKUP l x = NONE) ∧ (FLOOKUP m x = SOME y)))
Proof
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []
QED

Theorem MULT_LE_EXP:
   ∀a:num b. a ≠ 1 ⇒ a * b ≤ a ** b
Proof
  Induct_on`b` >> simp[arithmeticTheory.MULT,arithmeticTheory.EXP] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`SUC n`mp_tac) >>
  simp[arithmeticTheory.MULT] >>
  Cases_on`b=0` >- (
    simp[arithmeticTheory.EXP] ) >>
  `SUC b ≤ b + b * n` suffices_by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  Cases_on`b * n` >> simp[] >>
  fs[arithmeticTheory.MULT_EQ_0] >> fs[]
QED

Theorem domain_rrestrict_subset:
   domain (rrestrict r s) ⊆ domain r ∩ s
Proof
  rw[set_relationTheory.domain_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[]
QED

Theorem range_rrestrict_subset:
   range (rrestrict r s) ⊆ range r ∩ s
Proof
  rw[set_relationTheory.range_def,
     set_relationTheory.rrestrict_def,
     SUBSET_DEF] >> metis_tac[]
QED

Theorem PERM_MAP_BIJ:
   ∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))
Proof
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP]
QED

Theorem lookup_fromList2:
   !l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE
Proof
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
  \\ full_simp_tac(srw_ss())[MOD_TIMES]
QED

Theorem domain_fromList2:
   ∀q. domain(fromList2 q) = set(GENLIST (λx. 2n*x) (LENGTH q))
Proof
  rw[EXTENSION,domain_lookup,lookup_fromList2,MEM_GENLIST,
     lookup_fromList,EVEN_EXISTS, PULL_EXISTS, SF CONJ_ss] \\
  metis_tac[]
QED

Theorem UNCURRY_eq_pair:
   UNCURRY f v = z ⇔ ∃a b. v = (a,b) ∧ f a b = z
Proof
  Cases_on`v`\\ rw[UNCURRY]
QED

Theorem OLEAST_SOME_IMP:
   $OLEAST P = SOME i ⇒ P i ∧ (∀n. n < i ⇒ ¬P n)
Proof
  simp[WhileTheory.OLEAST_def]
  \\ metis_tac[WhileTheory.LEAST_EXISTS_IMP]
QED

Theorem EXP2_EVEN:
   ∀n. EVEN (2 ** n) ⇔ n ≠ 0
Proof
  Induct >> simp[EXP,EVEN_DOUBLE]
QED

Theorem FST_UNZIP_MAPi:
   ∀l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l
Proof
  Induct >> simp[]
QED

Theorem SND_UNZIP_MAPi:
   ∀l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l
Proof
  Induct >> simp[]
QED

Theorem ALL_DISTINCT_FLAT:
   ∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))
Proof
  Induct >> dsimp[ALL_DISTINCT_APPEND, LT_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]
QED

Theorem ALL_DISTINCT_FLAT_EVERY:
   ∀ls. ALL_DISTINCT (FLAT ls) ⇒ EVERY ALL_DISTINCT ls
Proof
  Induct \\ simp[ALL_DISTINCT_APPEND]
QED

Theorem ALL_DISTINCT_APPEND_APPEND_IMP:
   ALL_DISTINCT (xs ++ ys ++ zs) ==>
    ALL_DISTINCT (xs ++ ys) /\ ALL_DISTINCT (xs ++ zs) /\ ALL_DISTINCT (ys ++ zs)
Proof
  fs [ALL_DISTINCT_APPEND]
QED

Theorem GSPEC_o:
   GSPEC f o g = { x | ∃y. (g x, T) = f y }
Proof
  simp[FUN_EQ_THM, GSPECIFICATION]
QED


(* TODO - candidate for move to HOL *)
Theorem o_PAIR_MAP:
   FST o (f ## g) = f o FST ∧
   SND o (f ## g) = g o SND
Proof
  simp[FUN_EQ_THM]
QED

Theorem any_el_ALT:
   ∀l n d. any_el n l d = if n < LENGTH l then EL n l else d
Proof
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[] \\ rfs[]
QED

Theorem MOD_MINUS:
   0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k) MOD k
Proof
  strip_tac
  \\ mp_tac (wordsTheory.MOD_COMPLEMENT |> Q.SPECL [`k`,`p`,`n MOD (p * k)`])
  \\ impl_tac THEN1 (fs [MOD_LESS,ZERO_LESS_MULT])
  \\ fs [MOD_MULT_MOD]
QED

Definition option_fold_def:
  (option_fold f x NONE = x) ∧
  (option_fold f x (SOME y) = f y x)
End

Theorem SPLITP_CONS_IMP:
   ∀ls l' r. (SPLITP P ls = (l', r)) /\ (r <> []) ==> (EXISTS P ls)
Proof
  rw[] \\ imp_res_tac SPLITP_IMP \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on `r` \\ rfs[NULL_EQ, EXISTS_DEF, HD]
QED


Theorem LAST_CONS_alt:
   P x ==> ((ls <> [] ==> P (LAST ls)) <=> (P (LAST (CONS x ls))))
Proof
  Cases_on`ls` \\ rw[]
QED

Theorem EL_CONS_IF:
  EL n (x :: xs) = (if n = 0 then x else EL (PRE n) xs)
Proof    Cases_on `n` \\ fs []
QED

Theorem EVERY_TOKENS:
   ∀P ls. EVERY (EVERY ($~ o P)) (TOKENS P ls)
Proof
  recInduct TOKENS_ind
  \\ rw[TOKENS_def]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ IF_CASES_TAC \\ fs[]
  \\ imp_res_tac SPLITP_IMP
QED

Theorem TOKENS_START:
  !l a. TOKENS (\x. x = a) (a::l) = TOKENS (\x. x = a) l
Proof
  gen_tac \\ Induct_on `l` \\ rw[TOKENS_def] \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[]
  >-(imp_res_tac SPLITP_NIL_FST_IMP \\ fs[] \\ rw[TOKENS_def])
  >-(fs[SPLITP])
  >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[]
    \\ imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP \\ rfs[]
    \\ simp[TOKENS_def] \\ rw[NULL_EQ])
  >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP])
QED

Theorem TOKENS_END:
   !l a.
      TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l
Proof
    rw[]
    \\ `TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l ++ TOKENS (\x. x = a) ""` by fs[TOKENS_APPEND]
    \\ fs[TOKENS_def] \\ rw[]
QED


Theorem TOKENS_LENGTH_END:
   !l a.
      LENGTH (TOKENS (\x. x = a) (l ++ [a])) = LENGTH (TOKENS (\x. x = a) l)
Proof
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_END]
QED

Theorem TOKENS_LENGTH_START:
   !l a.
      LENGTH (TOKENS (\x. x = a) (a::l)) = LENGTH (TOKENS (\x. x= a) l)
Proof
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_START]
QED


Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
Proof
    Induct \\ rw[DROP]
    \\ Cases_on `n > LENGTH ls` \\ fs[]
    \\ `n < LENGTH (h::ls)` by fs[]
    \\ fs[DROP_EL_CONS]
QED

Theorem FRONT_APPEND'[local]:
  !l h a b t. l = h ++ [a; b] ++ t ==>
      FRONT l = h ++ FRONT([a; b] ++ t)
Proof
  Induct \\ rw[FRONT_DEF, FRONT_APPEND]
      >-(rw[LIST_EQ_REWRITE])
      \\ Cases_on `h'` \\ fs[FRONT_APPEND, FRONT_DEF]
QED


Theorem EVERY_NOT_IMP[local]:
  !ls a. (EVERY ($~ o (\x. x = a)) ls) ==> (LIST_ELEM_COUNT a ls = 0)
Proof
  Induct \\ rw[LIST_ELEM_COUNT_DEF] \\ fs[LIST_ELEM_COUNT_DEF]
QED

Theorem LIST_ELEM_COUNT_CONS[local]:
  !h t a. LIST_ELEM_COUNT a (h::t) = LIST_ELEM_COUNT a [h] + LIST_ELEM_COUNT a t
Proof
  simp_tac std_ss [Once CONS_APPEND, LIST_ELEM_COUNT_THM]
QED

Theorem FRONT_COUNT_IMP[local]:
  !l1 l2 a. l1 <> [] /\ FRONT l1 = l2 ==> (LIST_ELEM_COUNT a l2 = LIST_ELEM_COUNT a l1) \/ (LIST_ELEM_COUNT a l2 + 1 = LIST_ELEM_COUNT a l1)
Proof
  gen_tac \\ Induct_on `l1` \\ gen_tac \\ Cases_on `l2` \\ rw[FRONT_DEF]
    >-(Cases_on `h = a` \\ rw[LIST_ELEM_COUNT_DEF])
    \\ rw[LIST_ELEM_COUNT_DEF] \\ fs[LIST_ELEM_COUNT_DEF]
    \\ Cases_on `LENGTH (FILTER (\x. x = a) l1)`
    \\ first_x_assum (qspecl_then [`a`] mp_tac) \\ rw[] \\ rfs[]
QED

Definition CONCAT_WITH_aux_def:
    (CONCAT_WITH_aux [] l fl = REVERSE fl ++ FLAT l) /\
    (CONCAT_WITH_aux (h::t) [] fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ((h1::t1)::ls) fl = CONCAT_WITH_aux (h::t) (t1::ls) (h1::fl)) /\
    (CONCAT_WITH_aux (h::t) ([]::[]) fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ([]::(h'::t')) fl = CONCAT_WITH_aux (h::t) (h'::t') (REVERSE(h::t) ++ fl))
End

val CONCAT_WITH_AUX_ind = theorem"CONCAT_WITH_aux_ind";

Definition CONCAT_WITH_def:
    CONCAT_WITH s l = CONCAT_WITH_aux s l []
End

Theorem OPT_MMAP_MAP_o:
   !ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls
Proof
  Induct \\ rw[OPT_MMAP_def]
QED

Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_def]
QED

Theorem OPT_MMAP_CONG[defncong]:
   !l1 l2 f f'.
     (l1 = l2) /\
     (!x. MEM x l2 ==> (f x = f' x))
     ==> (OPT_MMAP f l1 = OPT_MMAP f' l2)
Proof
  Induct \\ rw[OPT_MMAP_def] \\ rw[OPT_MMAP_def] \\
  Cases_on`f' h` \\ rw[] \\ fs[] \\ metis_tac[]
QED

Theorem IMP_OPT_MMAP_EQ:
   !l1 l2. (MAP f1 l1 = MAP f2 l2) ==> (OPT_MMAP f1 l1 = OPT_MMAP f2 l2)
Proof
  Induct \\ rw[OPT_MMAP_def] \\ Cases_on`l2` \\ fs[OPT_MMAP_def] \\
  Cases_on`f2 h'` \\ fs[] \\ metis_tac[]
QED

Theorem DISJOINT_set_simp:
   DISJOINT (set []) s /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)
Proof
  fs [DISJOINT_DEF,EXTENSION] \\ metis_tac []
QED

Theorem DISJOINT_INTER:
   DISJOINT b c ⇒ DISJOINT (a ∩ b) (a ∩ c)
Proof
  rw[IN_DISJOINT] \\ metis_tac[]
QED

Theorem ALOOKUP_EXISTS_IFF:
   (∃v. ALOOKUP alist k = SOME v) ⇔ (∃v. MEM (k,v) alist)
Proof
  Induct_on `alist` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem LUPDATE_commutes:
   ∀m n e1 e2 l.
    m ≠ n ⇒
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)
Proof
  Induct_on `l` >> simp[LUPDATE_def] >>
  Cases_on `m` >> simp[LUPDATE_def] >> rpt strip_tac >>
  rename[`LUPDATE _ nn (_ :: _)`] >>
  Cases_on `nn` >> fs[LUPDATE_def]
QED

Theorem LUPDATE_APPEND:
   !xs n ys x.
      LUPDATE x n (xs ++ ys) =
      if n < LENGTH xs then LUPDATE x n xs ++ ys
                       else xs ++ LUPDATE x (n - LENGTH xs) ys
Proof
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LUPDATE_def] \\ rw [] \\ fs []
QED

Theorem FILTER_EL_EQ:
   ∀l1 l2. LENGTH l1 = LENGTH l2 ∧
   (∀n. n < LENGTH l1 ∧ (P (EL n l1) ∨ P (EL n l2)) ⇒ (EL n l1 = EL n l2))
   ⇒
   FILTER P l1 = FILTER P l2
Proof
  Induct \\ rw[] \\ Cases_on`l2` \\ fs[]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac (srw_ss())[] \\ simp[]
  \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[]
QED

Theorem FST_EL_AFUPDKEY:
   ∀n. n < LENGTH ls ⇒ FST (EL n (AFUPDKEY k f ls)) = FST (EL n ls)
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ rw[AFUPDKEY_def]
  \\ Cases_on`n` \\ fs[]
QED

Theorem EL_AFUPDKEY_unchanged:
   ∀n. n < LENGTH ls ∧ FST (EL n ls) ≠ k ⇒ EL n (AFUPDKEY k f ls) = EL n ls
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ simp[AFUPDKEY_def]
  \\ Cases \\ simp[]
  \\ IF_CASES_TAC \\ rveq \\ rw[]
QED

Theorem findi_APPEND:
   ∀l1 l2 x.
      findi x (l1 ++ l2) =
        let n0 = findi x l1
        in
          if n0 = LENGTH l1 then n0 + findi x l2
          else n0
Proof
  Induct >> simp[findi_def] >> rw[] >> fs[]
QED

Theorem NOT_MEM_findi_IFF:
   ¬MEM e l ⇔ findi e l = LENGTH l
Proof
  Induct_on `l` >> simp[findi_def, bool_case_eq, ADD1] >> metis_tac[]
QED

Theorem NOT_MEM_findi =
  NOT_MEM_findi_IFF |> EQ_IMP_RULE |> #1

Theorem ORD_eq_0:
   (ORD c = 0 ⇔ c = CHR 0) ∧ (0 = ORD c ⇔ c = CHR 0)
Proof
  metis_tac[char_BIJ, ORD_CHR, EVAL ``0n < 256``]
QED

Theorem HD_LUPDATE:
   0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l
Proof
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]
QED

Theorem DROP_LUPDATE:
   !n x m l. n ≤ m ⇒ DROP n (LUPDATE x m l) = LUPDATE x (m - n) (DROP n l)
Proof
  rw [LIST_EQ_REWRITE, EL_DROP, EL_LUPDATE] >>
  rw [] >>
  fs []
QED

Theorem w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]

Theorem CHR_w2n_n2w_ORD:
   (CHR o w2n o (n2w:num->word8) o ORD) = I
Proof
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
QED

Theorem n2w_ORD_CHR_w2n:
   ((n2w:num->word8) o ORD o CHR o w2n) = I
Proof
  rw[w2n_lt_256, o_DEF, ORD_BOUND, ORD_CHR, FUN_EQ_THM]
QED

Theorem CHR_w2n_n2w_ORD_simp[simp]:
   !c. CHR(w2n((n2w:num->word8)(ORD c))) = c
Proof
  metis_tac[CHR_w2n_n2w_ORD,o_THM,I_THM]
QED

Theorem n2w_ORD_CHR_w2n_simp[simp]:
   !w. n2w(ORD(CHR(w2n w))) = (w:word8)
Proof
  metis_tac[n2w_ORD_CHR_w2n,o_THM,I_THM]
QED

Theorem MAP_CHR_w2n_11:
   !ws1 ws2:word8 list.
      MAP (CHR ∘ w2n) ws1 = MAP (CHR ∘ w2n) ws2 <=> ws1 = ws2
Proof
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `ws2` \\ fs [] \\ metis_tac [CHR_11,w2n_lt_256,w2n_11]
QED

Theorem MAP_K_REPLICATE:
   MAP (K x) ls = REPLICATE (LENGTH ls) x
Proof
  Induct_on`ls` \\ rw[REPLICATE]
QED

Definition shift_left_def:
  shift_left (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_left (a << 32) (n - 32)
  else if n > 16 then shift_left (a << 16) (n - 16)
  else if n > 8 then shift_left (a << 8) (n - 8)
  else shift_left (a << 1) (n - 1)
End

Theorem shift_left_rwt:
   !a n. a << n = shift_left a n
Proof
  completeInduct_on `n`
  \\ rw [Once shift_left_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs []
QED

Definition shift_right_def:
  shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_right (a >>> 32) (n - 32)
  else if n > 16 then shift_right (a >>> 16) (n - 16)
  else if n > 8 then shift_right (a >>> 8) (n - 8)
  else shift_right (a >>> 1) (n - 1)
End

Theorem shift_right_rwt:
   !a n. a >>> n = shift_right a n
Proof
  completeInduct_on `n`
  \\ rw [Once shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs []
QED

Definition arith_shift_right_def:
  arith_shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) /\ ~word_msb a then 0w
  else if (a = -1w) \/ n > dimindex(:'a) /\ word_msb a then -1w
  else if n > 32 then arith_shift_right (a >> 32) (n - 32)
  else if n > 16 then arith_shift_right (a >> 16) (n - 16)
  else if n > 8 then arith_shift_right (a >> 8) (n - 8)
  else arith_shift_right (a >> 1) (n - 1)
End

Theorem arith_shift_right_rwt:
   !a n. a >> n = arith_shift_right a n
Proof
  completeInduct_on `n`
  \\ rw [Once arith_shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX]
QED

Definition any_word64_ror_def:
  any_word64_ror (w:word64) (n:num) =
    if 64 <= n then any_word64_ror w (n - 64) else
    if 32 <= n then any_word64_ror (word_ror w 32) (n - 32) else
    if 16 <= n then any_word64_ror (word_ror w 16) (n - 16) else
    if 8 <= n then any_word64_ror (word_ror w 8) (n - 8) else
    if 4 <= n then any_word64_ror (word_ror w 4) (n - 4) else
    if 2 <= n then any_word64_ror (word_ror w 2) (n - 2) else
    if 1 <= n then word_ror w 1 else w
End

Theorem word_ror_eq_any_word64_ror:
   !a n. word_ror a n = any_word64_ror a n
Proof
  completeInduct_on `n`
  \\ rw [Once any_word64_ror_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX]
  THEN1 fs [fcpTheory.CART_EQ,wordsTheory.word_ror_def,arithmeticTheory.SUB_MOD]
  \\ `n = 1 \/ n = 0` by fs [] \\ fs []
QED

Theorem TL_DROP_SUC:
   ∀x ls. x < LENGTH ls ⇒ TL (DROP x ls) = DROP (SUC x) ls
Proof
  Induct \\ rw[] \\ Cases_on`ls` \\ fs[]
QED

Theorem DROP_IMP_LESS_LENGTH:
   !xs n y ys. DROP n xs = y::ys ==> n < LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ decide_tac
QED

Theorem DROP_EQ_CONS_IMP_DROP_SUC:
   !xs n y ys. DROP n xs = y::ys ==> DROP (SUC n) xs = ys
Proof
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ `n - 1 + 1 = n` by decide_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem DROP_IMP_EL:
   !xs n h t. DROP n xs = h::t ==> (EL n xs = h)
Proof
  Induct \\ fs [DROP_def] \\ Cases_on `n` \\ fs []
QED

Theorem LENGTH_FIELDS:
   ∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[] \\ fs[] \\ rw[ADD1]
  \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_NIL_FST_IMP
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
  \\ rfs[NULL_EQ]
QED

Theorem FIELDS_NEQ_NIL[simp]:
   FIELDS P ls ≠ []
Proof
  disch_then(assume_tac o Q.AP_TERM`LENGTH`)
  \\ fs[LENGTH_FIELDS]
QED

Theorem CONCAT_FIELDS:
   ∀ls. CONCAT (FIELDS P ls) = FILTER ($~ o P) ls
Proof
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
  \\ Cases_on`r` \\ fs[]
QED

Theorem FIELDS_next:
   ∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c)
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ imp_res_tac SPLITP_NIL_FST_IMP \\ fs[]
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
  \\ simp[]
QED

Theorem FIELDS_full:
   ∀P ls l1 l2.
   FIELDS P ls = l1::l2 ∧ LENGTH ls ≤ LENGTH l1 ⇒
   l1 = ls ∧ l2 = []
Proof
  ntac 2 gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ simp_tac(srw_ss()++LET_ss)[FIELDS_def]
  \\ pairarg_tac \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
  \\ strip_tac
  \\ IF_CASES_TAC
  >-
   (simp_tac(srw_ss())[]
    \\ Cases_on ‘l1 = ""’ \\simp[])
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY )
  \\ simp_tac(srw_ss())[]
  \\ strip_tac \\ rveq
  \\ qspec_then`h::t`mp_tac(GSYM SPLITP_LENGTH)
  \\ last_x_assum kall_tac
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ `LENGTH r = 0` by decide_tac
  \\ fs[LENGTH_NIL]
QED

Theorem FLAT_MAP_TOKENS_FIELDS:
   ∀P' ls P.
    (∀x. P' x ⇒ P x) ⇒
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls
Proof
  Induct_on`FIELDS P' ls` \\ rw[] \\
  qpat_x_assum`_ = FIELDS _ _`(assume_tac o SYM) \\
  imp_res_tac FIELDS_next \\
  Cases_on`LENGTH ls ≤ LENGTH h` >- (
    imp_res_tac FIELDS_full \\ fs[] ) \\
  fs[] \\ rw[] \\
  fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] \\
  `h ++ [c] ++ l  = h ++ (c::l)` by simp[] \\ pop_assum SUBST_ALL_TAC \\
  asm_simp_tac std_ss [TOKENS_APPEND]
QED

Theorem the_nil_eq_cons:
   (the [] x = y::z) ⇔ x = SOME (y ::z)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Definition splitlines_def:
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines
End

Theorem splitlines_next:
   splitlines ls = ln::lns ⇒
   splitlines (DROP (SUC (LENGTH ln)) ls) = lns ∧
   ln ≼ ls ∧ (LENGTH ln < LENGTH ls ⇒ ln ++ "\n" ≼ ls)
Proof
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
  \\ simp[DROP_LENGTH_TOO_LONG,FIELDS_def]
QED

Theorem splitlines_nil[simp] = EVAL“splitlines ""”

Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = [])
Proof
  rw[EQ_IMP_THM]
  \\ fs[splitlines_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]
QED

Theorem splitlines_CONS_FST_SPLITP:
   splitlines ls = ln::lns ⇒ FST (SPLITP ($= #"\n") ls) = ln
Proof
  rw[splitlines_def]
  \\ Cases_on`ls` \\ fs[FIELDS_def]
  \\ TRY pairarg_tac \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ fs[NULL_EQ, FIELDS_def]
  \\ qmatch_assum_abbrev_tac`FRONT (x::y) = _`
  \\ Cases_on`y` \\ fs[]
QED

Theorem n2l_DIV_MOD:
   !b n k. 1 < b /\ 0 < k /\ b ** k <= n ==>
   (n2l b (n MOD (b ** k)) ++ REPLICATE (k - LENGTH (n2l b (n MOD (b ** k)))) 0 ++
    n2l b (n DIV (b ** k)) = n2l b n)
Proof
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
  \\ simp[]
QED

Theorem irreflexive_inv_image:
   !R f. irreflexive R ==> irreflexive (inv_image R f)
Proof
  SIMP_TAC std_ss [irreflexive_def,inv_image_def]
QED

Theorem trichotomous_inv_image:
   !R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)
Proof
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[]
QED

Theorem MEM_REPLICATE_IMP:
   MEM x (REPLICATE n y) ==> x = y
Proof
  Induct_on`n` \\ rw[REPLICATE] \\ fs[]
QED

Theorem plus_0_I[simp]:
   $+ 0n = I
Proof
rw[FUN_EQ_THM]
QED

(* used once *)
Theorem SUM_COUNT_LIST =
  SUM_MAP_COUNT_LIST |> Q.SPECL [`n`,`0`] |> SIMP_RULE (srw_ss()) []

Theorem OPTION_MAP_I[simp]:
   OPTION_MAP I x = x
Proof
  Cases_on`x` \\ rw[]
QED

(* should be made an iff in conclusion *)
Theorem OPTION_MAP_INJ:
   (∀x y. f x = f y ⇒ x = y)
   ⇒ ∀o1 o2.
     OPTION_MAP f o1 = OPTION_MAP f o2 ⇒ o1 = o2
Proof
  strip_tac \\ Cases \\ Cases \\ simp[]
QED

Theorem the_OPTION_MAP:
     !f d opt.
    f d = d ==>
    the d (OPTION_MAP f opt) = f (the d opt)
Proof
    rw [] >> Cases_on `opt` >> rw [the_def]
QED

Theorem TAKE_FLAT_REPLICATE_LEQ:
   ∀j k ls len.
    len = LENGTH ls ∧ k ≤ j ⇒
    TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)
Proof
  Induct \\ simp[REPLICATE]
  \\ Cases \\ simp[REPLICATE]
  \\ simp[TAKE_APPEND2] \\ rw[] \\ fs[]
  \\ simp[MULT_SUC]
QED

Theorem MOD_2EXP_0_EVEN:
   ∀x y. 0 < x ∧ MOD_2EXP x y = 0 ⇒ EVEN y
Proof
  rw[EVEN_MOD2,bitTheory.MOD_2EXP_def,MOD_EQ_0_DIVISOR]
  \\ Cases_on`x` \\ fs[EXP]
QED

Theorem ADD_MOD_EQ_LEMMA:
   k MOD d = 0 /\ n < d ==> (k + n) MOD d = n
Proof
  rw [] \\ `0 < d` by decide_tac
  \\ fs [MOD_EQ_0_DIVISOR]
  \\ pop_assum kall_tac
  \\ drule MOD_MULT
  \\ fs []
QED

(* should be set l1 ⊆ set l2 *)
Definition list_subset_def:
  list_subset l1 l2 = EVERY (\x. MEM x l2) l1
End

Definition list_set_eq_def:
  list_set_eq l1 l2 ⇔ list_subset l1 l2 ∧ list_subset l2 l1
End

Theorem list_subset_LENGTH:
    !l1 l2.ALL_DISTINCT l1 ∧
  list_subset l1 l2 ⇒
  LENGTH l1 ≤ LENGTH l2
Proof
  fs[list_subset_def,EVERY_MEM]>>
  Induct>>rw[]>>
  first_x_assum(qspec_then`FILTER ($~ o $= h) l2` assume_tac)>>
  rfs[MEM_FILTER]>>
  `LENGTH (FILTER ($~ o $= h) l2) < LENGTH l2` by
    (match_mp_tac LENGTH_FILTER_LESS>>
    fs[EXISTS_MEM])>>
  fs[]
QED

Theorem BIJ_UPDATE:
   !f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)
Proof
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []
QED

Theorem INJ_UPDATE:
   INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)
Proof
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []
QED

(* TODO: candidate for move to HOL;
         subspt_domain exists already but is specialised to unit *)
Theorem subspt_domain_SUBSET:
   subspt t1 t2 ==> domain t1 SUBSET domain t2
Proof
  fs [subspt_def,SUBSET_DEF]
QED

(* Some temporal logic definitions based on lazy lists *)
(* move into llistTheory? *)

Theorem SPLITP_TAKE_DROP:
  !P i l. EVERY ($~ ∘ P) (TAKE i l) ==>
  P (EL i l) ==>
  SPLITP P l = (TAKE i l, DROP i l)
Proof
  Induct_on`l` >> rw[SPLITP] >> Cases_on`i` >> fs[] >>
  res_tac >> fs[FST,SND]
QED

Theorem SND_SPLITP_DROP:
  !P n l. EVERY ($~ o P) (TAKE n l) ==>
   SND (SPLITP P (DROP n l)) = SND (SPLITP P l)
Proof
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >> fs[SPLITP]
QED

Theorem FST_SPLITP_DROP:
  !P n l. EVERY ($~ o P) (TAKE n l) ==>
   FST (SPLITP P l) = (TAKE n l) ++ FST (SPLITP P (DROP n l))
Proof
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >>
 PURE_REWRITE_TAC[DROP_def,TAKE_def,APPEND] >> simp[] >>
 fs[SPLITP]
QED

Theorem TAKE_DROP_SUBLIST:
   ll ≼ (DROP n ls) ∧ n < LENGTH ls ∧ (nlll = n + LENGTH ll) ⇒
   (TAKE n ls ++ ll ++ DROP nlll ls = ls)
Proof
  rw[IS_PREFIX_APPEND, LIST_EQ_REWRITE, LENGTH_TAKE_EQ, EL_APPEND_EQN, EL_DROP]
  \\ rw[] \\ fs[EL_TAKE]
  \\ fs[NOT_LESS, LESS_EQ_EXISTS]
QED

(* computes the next position for which P holds *)
Definition Lnext_def:
  Lnext P ll = if eventually P ll then
                        if P ll then 0
                        else SUC(Lnext P (THE (LTL ll)))
                     else ARB
Termination
  exists_tac``\(P,ll') (P',ll).
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
  qexists_tac`(P,h:::ll)` >> fs[] >> rw[] >> pairarg_tac >> fs[]
End

Definition Lnext_pos_def:
  Lnext_pos (ll :num llist) = Lnext (λll. ∃k. LHD ll = SOME k ∧ k ≠ 0) ll
End

Theorem OPTION_CHOICE_EQUALS_OPTION:
   !(x:'a option) y z. (OPTION_CHOICE x y = SOME z) <=>
                       ((x = SOME z) \/ ((x = NONE) /\ (y = SOME z)))
Proof
 rw[] \\ Cases_on `x` \\ Cases_on `y` \\ fs[]
QED

Theorem option_eq_some =
  LIST_CONJ [
    OPTION_IGNORE_BIND_EQUALS_OPTION,
    OPTION_BIND_EQUALS_OPTION,
    OPTION_CHOICE_EQUALS_OPTION]

Theorem ALL_DISTINCT_alist_to_fmap_REVERSE:
   ALL_DISTINCT (MAP FST ls) ⇒ alist_to_fmap (REVERSE ls) = alist_to_fmap ls
Proof
  Induct_on`ls` \\ simp[FORALL_PROD] \\ rw[] \\ rw[FUNION_FUPDATE_2]
QED

Theorem FUPDATE_LIST_alist_to_fmap:
 ∀ls fm. fm |++ ls = alist_to_fmap (REVERSE ls) ⊌ fm
Proof
 metis_tac [FUNION_alist_to_fmap, REVERSE_REVERSE]
QED

Theorem DISTINCT_FUPDATE_LIST_UNION:
   ALL_DISTINCT (MAP FST ls) /\
   DISJOINT (FDOM f) (set(MAP FST ls)) ==>
   f |++ ls = FUNION f (alist_to_fmap ls)
Proof
  rw[FUPDATE_LIST_alist_to_fmap,ALL_DISTINCT_alist_to_fmap_REVERSE]
  \\ match_mp_tac FUNION_COMM \\ rw[DISJOINT_SYM]
QED

Theorem fevery_to_drestrict:
 !P m s.
  FEVERY P m ⇒ FEVERY P (DRESTRICT m s)
Proof
 rw [FEVERY_ALL_FLOOKUP,FLOOKUP_DRESTRICT]
QED

Theorem SUM_MAP_K:
   ∀f ls c. (∀x. f x = c) ⇒ SUM (MAP f ls) = LENGTH ls * c
Proof
  rw[] \\ Induct_on`ls` \\ rw[MULT_SUC]
QED

Theorem LAST_FLAT:
   ∀ls. ~NULL (FLAT ls) ==> (LAST (FLAT ls) = LAST (LAST (FILTER ($~ o NULL) ls)))
Proof
  ho_match_mp_tac SNOC_INDUCT \\ rw[]
  \\ fs[FLAT_SNOC,FILTER_SNOC]
  \\ Cases_on`x` \\ fs[]
QED

Theorem TOKENS_unchanged:
  EVERY ($~ o P) ls ==> TOKENS P ls = if NULL ls then [] else [ls]
Proof
  Induct_on`ls` \\ rw[TOKENS_def] \\ fs[]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`r=[]` \\ fs[]
  >- ( imp_res_tac SPLITP_NIL_FST_IMP \\ rveq \\ fs[TOKENS_NIL] )
  \\ rw[]
  >- (
    imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP
    \\ rfs[] \\ rveq \\ fs[] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ fs[EVERY_MEM]
  \\ `MEM (HD r) (l ++ r)` by (Cases_on`r` \\ fs[])
  \\ Cases_on`MEM (HD r) l` \\ fs[] >- metis_tac[]
  \\ `MEM (HD r) (h::ls)` by metis_tac[MEM_APPEND]
  \\ fs[] \\ rw[] \\ metis_tac[]
QED

Theorem TOKENS_FLAT_MAP_SNOC:
   EVERY (EVERY ((<>) x)) ls ∧ EVERY ($~ o NULL) ls ==>
   TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls
Proof
  Induct_on`ls` \\ rw[TOKENS_NIL]
  \\ rewrite_tac[GSYM APPEND_ASSOC,SNOC_APPEND,APPEND]
  \\ DEP_REWRITE_TAC[TOKENS_APPEND] \\ rw[]
  \\ DEP_REWRITE_TAC[TOKENS_unchanged]
  \\ fs[EVERY_MEM]
QED

(* insert a string (l1) at specified index (n) in a list (l2) *)
Definition insert_atI_def:
  insert_atI l1 n l2 =
    TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2
End

Theorem insert_atI_NIL:
   ∀n l.insert_atI [] n l = l
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_CONS:
   ∀n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (h::t) n l = LUPDATE h n (insert_atI t (n + 1) l)
Proof
  simp[insert_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]
QED

Theorem LENGTH_insert_atI:
   p + LENGTH l1 <= LENGTH l2 ⇒ LENGTH (insert_atI l1 p l2) = LENGTH l2
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_app:
   ∀n l c1 c2.  n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
     insert_atI (c1 ++ c2) n l =
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)
Proof
  Induct_on`c1` >> fs[insert_atI_NIL,insert_atI_CONS,LENGTH_insert_atI,ADD1]
QED

Theorem insert_atI_end:
   insert_atI l1 (LENGTH l2) l2 = l2 ++ l1
Proof
  simp[insert_atI_def,DROP_LENGTH_TOO_LONG]
QED

Theorem insert_atI_insert_atI:
   pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1 ++ c2) pos1 l
Proof
    rw[insert_atI_def,TAKE_SUM,TAKE_APPEND,LENGTH_TAKE_EQ,LENGTH_DROP,
       GSYM DROP_DROP_T,DROP_LENGTH_TOO_LONG,DROP_LENGTH_NIL_rwt]
    >> fs[DROP_LENGTH_NIL_rwt,LENGTH_TAKE,DROP_APPEND1,TAKE_APPEND,TAKE_TAKE,
       DROP_DROP_T,DROP_APPEND2,TAKE_LENGTH_TOO_LONG,TAKE_SUM,LENGTH_DROP]
QED

Theorem LUPDATE_insert_commute:
   ∀ws pos1 pos2 a w.
     pos2 < pos1 ∧ pos1 + LENGTH ws <= LENGTH a ⇒
     insert_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insert_atI ws pos1 a)
Proof
  Induct >> simp[insert_atI_NIL,insert_atI_CONS, LUPDATE_commutes]
QED

Theorem LESS_EQ_LENGTH:
   !xs k. k <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = k)
Proof
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss []
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]
QED

Theorem LESS_LENGTH:
   !xs k. k < LENGTH xs ==>
           ?ys1 y ys2. (xs = ys1 ++ y::ys2) /\ (LENGTH ys1 = k)
Proof
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss [CONS_11]
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]
QED

Theorem IN_EVEN =
  SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``

Theorem FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM:
   FOLDL OPTION_CHOICE x ls = SOME y ⇒ MEM (SOME y) (x::ls)
Proof
  qid_spec_tac`x` \\ Induct_on`ls` \\ rw[] \\
  res_tac \\ fs[] \\ Cases_on`x` \\ fs[]
QED

Theorem BAG_ALL_DISTINCT_FOLDR_BAG_UNION:
   ∀ls b0.
   BAG_ALL_DISTINCT (FOLDR BAG_UNION b0 ls) ⇔
   BAG_ALL_DISTINCT b0 ∧
   (∀n. n < LENGTH ls ⇒
        BAG_DISJOINT (EL n ls) b0 ∧ BAG_ALL_DISTINCT (EL n ls) ∧
        (∀m. m < n ⇒ BAG_DISJOINT (EL n ls) (EL m ls)))
Proof
  Induct \\ rw[]
  \\ rw[BAG_ALL_DISTINCT_BAG_UNION]
  \\ simp[Once FORALL_NUM, SimpRHS]
  \\ Cases_on`BAG_ALL_DISTINCT h` \\ simp[]
  \\ Cases_on`BAG_ALL_DISTINCT b0` \\ simp[]
  \\ simp[BAG_DISJOINT_FOLDR_BAG_UNION, EVERY_MEM, MEM_EL, PULL_EXISTS]
  \\ CONV_TAC(PATH_CONV"rrrarrr"(HO_REWR_CONV FORALL_NUM))
  \\ simp[]
  \\ rw[EQ_IMP_THM] \\ fs[]
  \\ metis_tac[BAG_DISJOINT_SYM]
QED

(* TODO - candidate for move to HOL *)
(* N.B.: there is a different is_subsequence defined in lcsTheory; these should be merged *)
Definition is_subseq_def:
  (is_subseq ls [] ⇔ T) ∧
  (is_subseq [] (x::xs) ⇔ F) ∧
  (is_subseq (y::ys) (x::xs) ⇔
   (x = y ∧ is_subseq ys xs) ∨
   (is_subseq ys (x::xs)))
End

(* TODO - candidate for move to HOL *)
val is_subseq_ind = theorem"is_subseq_ind";

(* TODO - candidate for move to HOL *)
Theorem is_subseq_refl[simp]:
   ∀ls. is_subseq ls ls
Proof
Induct \\ rw[is_subseq_def]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_nil[simp]:
   is_subseq [] ls ⇔ ls = []
Proof
  Cases_on`ls` \\ rw[is_subseq_def]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_cons:
   ∀l1 l2 x. is_subseq l1 l2 ⇒ is_subseq (x::l1) l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_snoc:
   ∀l1 l2 x. is_subseq l1 l2 ⇒ is_subseq (SNOC x l1) l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def] \\ fs[]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_append1:
   ∀l3 l1 l2. is_subseq l1 l2 ⇒ is_subseq (l3 ++ l1) l2
Proof
  Induct
  \\ rw[is_subseq_def] \\ fs[]
  \\ metis_tac[is_subseq_cons]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_append2:
   ∀l4 l1 l2. is_subseq l1 l2 ⇒ is_subseq (l1 ++ l4) l2
Proof
  ho_match_mp_tac SNOC_INDUCT
  \\ rw[is_subseq_def] \\ fs[]
  \\ metis_tac[is_subseq_snoc, SNOC_APPEND, APPEND_ASSOC]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_IS_SUBLIST:
   is_subseq l1 l2 ∧ IS_SUBLIST l3 l1 ⇒ is_subseq l3 l2
Proof
  rw[IS_SUBLIST_APPEND]
  \\ metis_tac[is_subseq_append1, is_subseq_append2]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_MEM:
   ∀l1 l2 x. is_subseq l1 l2 ∧ MEM x l2 ⇒ MEM x l1
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ metis_tac[]
QED

(* TODO - candidate for move to HOL *)
Theorem IS_PREFIX_is_subseq:
   ∀l1 l2. IS_PREFIX l1 l2 ⇒ is_subseq l1 l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ fs[IS_PREFIX_NIL]
QED

(* TODO - candidate for move to HOL *)
Theorem IS_SUBLIST_is_subseq:
   ∀l1 l2. IS_SUBLIST l1 l2 ⇒ is_subseq l1 l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def, IS_SUBLIST]
  \\ simp[IS_PREFIX_is_subseq]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_ALL_DISTINCT:
   ∀l1 l2. ALL_DISTINCT l1 ∧ is_subseq l1 l2 ⇒ ALL_DISTINCT l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def] \\ fs[] \\ rfs[]
  \\ metis_tac[is_subseq_MEM]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_append_suff:
   ∀l1 l3 l2 l4.
   is_subseq l1 l3 ∧ is_subseq l2 l4 ⇒
   is_subseq (l1 ++ l2) (l3 ++ l4)
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ metis_tac[is_subseq_append1]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_FLAT_suff:
   ∀ls1 ls2. LIST_REL is_subseq ls1 ls2 ⇒ is_subseq (FLAT ls1) (FLAT ls2)
Proof
  ho_match_mp_tac LIST_REL_ind
  \\ rw[is_subseq_append_suff]
QED

Theorem LIST_REL_IMP_LAST:
   !P xs ys.
      LIST_REL P xs ys /\ (xs <> [] \/ ys <> []) ==> P (LAST xs) (LAST ys)
Proof
  rpt gen_tac
  \\ Cases_on `xs = []` \\ fs [] \\ Cases_on `ys = []` \\ fs []
  \\ `?x1 x2. xs = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ `?y1 y2. ys = SNOC y1 y2` by metis_tac [SNOC_CASES]
  \\ asm_rewrite_tac [LAST_SNOC] \\ fs [LIST_REL_SNOC]
QED

Definition make_even_def:
  make_even n = if EVEN n then n else n+1
End

Theorem EVEN_make_even[simp]:
   EVEN (make_even x)
Proof
  rw[make_even_def, EVEN_ADD]
QED

Theorem ALOOKUP_MAP_FST_INJ_SOME:
   ∀ls x y.
    ALOOKUP ls x = SOME y ∧ (∀x'. IS_SOME (ALOOKUP ls x') ∧ f x' = f x ⇒ x = x') ⇒
    ALOOKUP (MAP (f ## g) ls) (f x) = SOME (g y)
Proof
  Induct \\ simp[]
  \\ Cases \\ rw[]
  >- metis_tac[IS_SOME_EXISTS]
  \\ first_x_assum irule
  \\ rw[]
  \\ first_x_assum irule
  \\ rw[]
QED

Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w
Proof
EVAL_TAC
QED

Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w
Proof
EVAL_TAC
QED

Theorem v2w_sing:
   v2w [b] = if b then 1w else 0w
Proof
  Cases_on `b` \\ EVAL_TAC
QED

Theorem FOLDR_FUNPOW:
   FOLDR (λx. f) x ls = FUNPOW f (LENGTH ls) x
Proof
  qid_spec_tac`x`
  \\ Induct_on`ls`
  \\ rw[FUNPOW_SUC]
QED

Theorem FUNPOW_refl_trans_chain:
   transitive P ∧ reflexive P ⇒
   ∀n x.  (∀j. j < n ⇒ P (FUNPOW f j x) (f (FUNPOW f j x))) ⇒
     P x (FUNPOW f n x)
Proof
  strip_tac
  \\ Induct
  \\ rw[]
  >- fs[reflexive_def]
  \\ rw[]
  \\ fs[transitive_def]
  \\ last_x_assum irule
  \\ simp[FUNPOW_SUC]
  \\ qexists_tac`FUNPOW f n x`
  \\ simp[]
QED

Theorem byte_align_extract:
   byte_align (x:word32) = (((31 >< 2) x):word30) @@ (0w:word2)
Proof
  rw[alignmentTheory.byte_align_def]
  \\ rw[alignmentTheory.align_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem byte_align_IN_IMP_IN_range:
   byte_align a ∈ dm ∧
   (dm = { w | low <=+ w ∧ w <+ hi }) ∧
   byte_aligned low ∧ byte_aligned hi ⇒
   a ∈ dm
Proof
  rw[] \\ fs[]
  >- (
    `byte_align a <=+ a` suffices_by metis_tac[WORD_LOWER_EQ_TRANS]
    \\ simp[alignmentTheory.byte_align_def]
    \\ simp[align_ls] )
  \\ Cases_on`byte_aligned a`
    >- metis_tac[alignmentTheory.byte_aligned_def,
                 alignmentTheory.aligned_def,
                 alignmentTheory.byte_align_def]
  \\ match_mp_tac (GEN_ALL aligned_between)
  \\ fs[alignmentTheory.byte_aligned_def]
  \\ asm_exists_tac
  \\ fs[alignmentTheory.byte_align_def]
QED

Theorem MULT_DIV_MULT_LEMMA:
   !m l k. 0 < m /\ 0 < l ==> (m * k) DIV (l * m) = k DIV l
Proof
  rw [] \\ qsuff_tac `k * m DIV (m * l) = k DIV l` THEN1 fs []
  \\ simp [GSYM DIV_DIV_DIV_MULT] \\ simp [MULT_DIV]
QED

Theorem IMP_MULT_DIV_LESS:
   m <> 0 /\ d < k ==> m * (d DIV m) < k
Proof
  strip_tac \\ `0 < m` by decide_tac
  \\ drule DIVISION
  \\ disch_then (qspec_then `d` assume_tac)
  \\ decide_tac
QED

Theorem DIV_LESS_DIV:
   n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k
Proof
  strip_tac
  \\ drule DIVISION \\ disch_then (qspec_then `n` (strip_assume_tac o GSYM))
  \\ drule DIVISION \\ disch_then (qspec_then `m` (strip_assume_tac o GSYM))
  \\ rfs [] \\ metis_tac [LT_MULT_LCANCEL]
QED

Theorem toPath_fromList:
   (toPath (x, fromList []) = stopped_at x) ∧
   (toPath (x, fromList ((y,z)::t)) = pcons x y (toPath (z, fromList t)))
Proof
  conj_tac >- EVAL_TAC
  \\ rw[pathTheory.pcons_def, pathTheory.first_def, pathTheory.path_rep_bijections_thm]
QED

Definition steps_def:
  (steps f x [] = []) ∧
  (steps f x (j::js) =
   let y = f x j in
   let tr = steps f y js in
     ((j,y)::tr))
End

Definition steps_rel_def:
  (steps_rel R x [] ⇔ T) ∧
  (steps_rel R x ((j,y)::tr) ⇔
    R x j y ∧
    steps_rel R y tr)
End

val steps_rel_ind = theorem"steps_rel_ind";

Theorem steps_rel_okpath:
   ∀R x tr.
    steps_rel R x tr ⇔ okpath R (toPath (x,fromList tr))
Proof
  recInduct steps_rel_ind
  \\ rewrite_tac[toPath_fromList]
  \\ rw[steps_rel_def, pathTheory.first_def, pathTheory.path_rep_bijections_thm]
QED

Theorem steps_rel_LRC:
    ∀R x tr.
     steps_rel R x tr ⇒
     LRC (λx y. ∃i. R x i y)
       (FRONT(x::(MAP SND tr))) x (LAST (x::(MAP SND tr)))
Proof
  recInduct steps_rel_ind
  \\ rw[steps_rel_def]
  \\ rw[LRC_def, PULL_EXISTS]
  \\ asm_exists_tac \\ rw[]
QED

Theorem LAST_MAP_SND_steps_FOLDL:
   ∀f x ls. LAST (x::(MAP SND (steps f x ls))) = FOLDL f x ls
Proof
  Induct_on`ls` \\ rw[steps_def]
QED

Definition all_words_def:
  (all_words base 0 = ∅) /\
  (all_words base (SUC n) = base INSERT (all_words (base + 1w) n))
End

Theorem IN_all_words:
   x ∈ all_words base n ⇔ (∃i. i < n ∧ x = base + n2w i)
Proof
  qid_spec_tac`base`
  \\ Induct_on`n`
  \\ rw[all_words_def, ADD1]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  >- ( qexists_tac`i + 1` \\ simp[GSYM word_add_n2w] )
  \\ Cases_on`i` \\ fs[ADD1]
  \\ disj2_tac
  \\ simp[GSYM word_add_n2w]
  \\ asm_exists_tac \\ simp[]
QED

Theorem read_bytearray_IMP_mem_SOME:
   ∀p n m ba.
   (read_bytearray p n m = SOME ba) ⇒
   ∀k. k ∈ all_words p n ⇒ IS_SOME (m k)
Proof
  Induct_on `n`
  \\ rw[read_bytearray_def,all_words_def]
  \\ fs[CaseEq"option"]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp []
QED

Theorem read_bytearray_no_wrap:
   ∀ptr len.
   IS_SOME (read_bytearray ptr len (m:'a word -> 'b option)) ∧
   (∀x. IS_SOME (m x) ⇒ w2n x < dimword(:'a) - 1) ∧
   w2n ptr < dimword (:'a)
   ⇒
   w2n ptr + len < dimword(:'a)
Proof
  Induct_on`len`
  \\ rw[read_bytearray_def]
  \\ fs[CaseEq"option", IS_SOME_EXISTS, PULL_EXISTS]
  \\ Cases_on`ptr` \\ fs[word_add_n2w, ADD1]
  \\ res_tac \\ fs[] \\ rfs[]
QED

Definition asm_write_bytearray_def:
  (asm_write_bytearray a [] (m:'a word -> word8) = m) /\
  (asm_write_bytearray a (x::xs) m = (a =+ x) (asm_write_bytearray (a+1w) xs m))
End

Theorem mem_eq_imp_asm_write_bytearray_eq:
   ∀a bs.
    (m1 k = m2 k) ⇒
    (asm_write_bytearray a bs m1 k = asm_write_bytearray a bs m2 k)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def]
  \\ rw[APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_unchanged:
   ∀a bs m z. (x <+ a ∨ a + n2w (LENGTH bs) <=+ x) ∧
    (w2n a + LENGTH bs < dimword(:'a)) ∧ (z = m x)
  ⇒ (asm_write_bytearray (a:'a word) bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ TRY (
    Cases_on`a` \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
    \\ NO_TAC )
  \\ first_x_assum match_mp_tac
  \\ Cases_on`a`
  \\ Cases_on`x`
  \\ fs[word_ls_n2w,word_lo_n2w,word_add_n2w]
QED

Theorem asm_write_bytearray_id:
   ∀a bs m.
    (∀j. j < LENGTH bs ⇒ (m (a + n2w j) = EL j bs))
  ⇒ (asm_write_bytearray (a:'a word) bs m x = m x)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum match_mp_tac
  \\ rw[]
  \\ first_x_assum(qspec_then`SUC j`mp_tac)
  \\ rw[]
  \\ fs[ADD1, GSYM word_add_n2w]
QED

Theorem asm_write_bytearray_unchanged_alt:
   ∀a bs m z.
      (z = m x) /\ ~(x IN { a + n2w k | k < LENGTH bs }) ==>
      (asm_write_bytearray a bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  THEN1 (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
  \\ first_x_assum match_mp_tac \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then `k + 1` mp_tac)
  \\ fs [GSYM word_add_n2w,ADD1]
QED

Theorem asm_write_bytearray_unchanged_all_words:
   ∀a bs m z x.
    ~(x ∈ all_words a (LENGTH bs)) ∧ (z = m x) ⇒
    (asm_write_bytearray (a:'a word) bs m x = z)
Proof
  Induct_on`bs`
  \\ rw[all_words_def,asm_write_bytearray_def,APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_append:
   ∀a l1 l2 m.
   w2n a + LENGTH l1 + LENGTH l2 < dimword (:'a) ⇒
   (asm_write_bytearray (a:'a word) (l1 ++ l2) m =
    asm_write_bytearray (a + n2w (LENGTH l1)) l2 (asm_write_bytearray a l1 m))
Proof
  Induct_on`l1` \\ rw[asm_write_bytearray_def]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
  \\ rw[]
  >- (
    irule (GSYM asm_write_bytearray_unchanged)
    \\ simp[APPLY_UPDATE_THM]
    \\ Cases_on`a` \\ simp[word_lo_n2w,word_add_n2w,word_ls_n2w]
    \\ fs[] )
  \\ fs[ADD1,GSYM word_add_n2w]
  \\ first_x_assum (qspec_then`a+1w`mp_tac)
  \\ simp[]
  \\ Cases_on`a` \\ fs[word_add_n2w]
  \\ disch_then drule
  \\ rw[]
  \\ irule mem_eq_imp_asm_write_bytearray_eq
  \\ simp[APPLY_UPDATE_THM]
QED

Theorem asm_write_bytearray_EL:
   ∀a bs m x. x < LENGTH bs ∧ LENGTH bs < dimword(:'a) ⇒
   (asm_write_bytearray (a:'a word) bs m (a + n2w x) = EL x bs)
Proof
  Induct_on`bs`
  \\ rw[asm_write_bytearray_def,APPLY_UPDATE_THM]
  \\ Cases_on`x` \\ fs[]
  >- ( fs[addressTheory.WORD_EQ_ADD_CANCEL] )
  \\ first_x_assum drule
  \\ simp[ADD1,GSYM word_add_n2w]
  \\ metis_tac[WORD_ADD_ASSOC,WORD_ADD_COMM]
QED

(* TODO: move to sptTheory *)

Definition eq_shape_def:
  eq_shape LN LN = T /\
  eq_shape (LS _) (LS _) = T /\
  eq_shape (BN t1 t2) (BN u1 u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape (BS t1 _ t2) (BS u1 _ u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape _ _ = F
End

Theorem spt_eq:
   !t1 t2.
      t1 = t2 <=>
      (eq_shape t1 t2 /\ (!k v. lookup k t1 = SOME v ==> lookup k t2 = SOME v))
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,lookup_def]
  THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ rw [] \\ rw [] \\ fs []
  \\ first_assum (qspec_then `0` mp_tac)
  \\ first_assum (qspec_then `k * 2 + 1` mp_tac)
  \\ first_x_assum (qspec_then `k * 2 + 1 + 1` mp_tac)
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT,EVEN_ADD]
  \\ fs [GSYM ADD1,EVEN,EVEN_DOUBLE]
QED

Theorem eq_shape_map:
   !t1 t2 f. eq_shape (map f t1) t2 <=> eq_shape t1 t2
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,map_def]
QED

Theorem eq_shape_IMP_domain:
   !t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2
Proof
  ho_match_mp_tac (fetch "-" "eq_shape_ind")
  \\ rw [] \\ fs [eq_shape_def]
QED

Definition copy_shape_def:
  copy_shape LN LN = LN /\
  copy_shape LN (LS y) = LN /\
  copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN t2) /\
  copy_shape LN (BS t1 y t2) = LN /\
  copy_shape (LS x) LN = LS x /\
  copy_shape (LS x) (LS y) = LS x /\
  copy_shape (LS x) (BN t1 t2) = LS x /\
  copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x (copy_shape LN t2) /\
  copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN else BN u1 u2) /\
  copy_shape (BN u1 u2) (LS y) = BN u1 u2 /\
  copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1) (copy_shape u2 t2) /\
  copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2 /\
  copy_shape (BS u1 x u2) LN = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (LS y) =
     (if domain (BN u1 u2) = {} then LS x else BS u1 x u2) /\
  copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (BS t1 y t2) = BS (copy_shape u1 t1) x (copy_shape u2 t2)
End

Theorem eq_shape_copy_shape[local]:
    !s. domain s = {} ==> eq_shape (copy_shape LN s) s
Proof
  Induct \\ fs [copy_shape_def,eq_shape_def]
QED

Theorem num_lemma[local]:
    (!n. 0 <> 2 * n + 2 /\ 0 <> 2 * n + 1:num) /\
    (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
    (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
    (!n m. 2 * n + 2 <> 2 * m + 1n)
Proof
  rw [] \\ fs [] \\ Cases_on `m = n` \\ fs []
QED

Theorem shape_eq_copy_shape:
   !t1 t2. domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,copy_shape_def]
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac)
  \\ TRY (match_mp_tac eq_shape_copy_shape) \\ fs []
  \\ rw [] \\ pop_assum mp_tac
  \\ rewrite_tac [DE_MORGAN_THM] \\ strip_tac
  \\ fs [eq_shape_def] \\ fs [EXTENSION]
  \\ TRY (first_assum (qspec_then `0` mp_tac) \\ simp_tac std_ss [])
  \\ rw [] \\ first_assum (qspec_then `2 * x + 2` mp_tac)
  \\ first_x_assum (qspec_then `2 * x + 1` mp_tac)
  \\ fs [num_lemma]
QED

Theorem lookup_copy_shape_LN[local]:
    !s n. lookup n (copy_shape LN s) = NONE
Proof
  Induct \\ fs [copy_shape_def,lookup_def] \\ rw [] \\ fs []
QED

Theorem domain_EMPTY_lookup[local]:
    domain t = EMPTY ==> !x. lookup x t = NONE
Proof
  fs [domain_lookup,EXTENSION] \\ rw []
  \\ pop_assum (qspec_then `x` mp_tac)
  \\ Cases_on `lookup x t` \\ fs []
QED

Theorem lookup_copy_shape:
   !t1 t2 n. lookup n (copy_shape t1 t2) = lookup n t1
Proof
  Induct \\ Cases_on `t2` \\ fs [copy_shape_def,lookup_def] \\ rw []
  \\ fs [lookup_def,lookup_copy_shape_LN,domain_EMPTY_lookup]
QED

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

Theorem lookup_zero:
   ∀ n t x. (lookup n t = SOME x) ==> (size t <> 0)
Proof
   recInduct lookup_ind
   \\ rw[lookup_def]
QED

Theorem empty_sub:
     isEmpty(difference a b) ∧ (subspt b a) ==> (domain a = domain b)
Proof
    fs[subspt_def] >>
    rw[] >>
    imp_res_tac difference_sub >>
    metis_tac[GSYM SUBSET_DEF, SUBSET_ANTISYM]
QED

Theorem subspt_delete:
     ∀ a b x . subspt a b ⇒ subspt (delete x a) b
Proof
    rw[subspt_def, lookup_delete]
QED

Theorem inter_union_empty:
     ∀ a b c . isEmpty (inter (union a b) c)
  ⇔ isEmpty (inter a c) ∧ isEmpty (inter b c)
Proof
    rw[] >> EQ_TAC >> rw[] >>
    `wf (inter (union a b) c) ∧ wf (inter a c)` by metis_tac[wf_inter] >>
    fs[domain_empty] >> fs[EXTENSION] >> rw[] >>
    pop_assum (qspec_then `x` mp_tac) >> fs[domain_lookup] >>
    rw[] >> fs[lookup_inter, lookup_union] >>
    TRY(first_x_assum (qspec_then `x` mp_tac)) >> rw[] >>
    fs[lookup_inter, lookup_union] >> BasicProvers.EVERY_CASE_TAC >> fs[]
QED

Theorem inter_insert_empty:
     ∀ n t1 t2 . isEmpty (inter (insert n () t1) t2)
  ⇒ n ∉ domain t2 ∧ isEmpty(inter t1 t2)
Proof
    rw[] >>
    `∀ k . lookup k (inter (insert n () t1) t2) = NONE` by fs[lookup_def]
    >- (fs[domain_lookup] >> rw[] >> fs[lookup_inter] >>
        pop_assum (qspec_then `n` mp_tac) >>
        rw[] >> fs[] >> BasicProvers.EVERY_CASE_TAC >> fs[])
    >- (`wf (inter t1 t2)` by metis_tac[wf_inter] >> fs[domain_empty] >>
        fs[EXTENSION] >> rw[] >>
        pop_assum (qspec_then `x` mp_tac) >> rw[] >>
        first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
        fs[domain_lookup, lookup_inter, lookup_insert] >>
        Cases_on `x = n` >> fs[] >>
        Cases_on `lookup n t2` >> fs[] >> CASE_TAC)
QED

Theorem fromList2_value:
     ∀ e l t n . MEM e l ⇔  ∃ n . lookup n (fromList2 l) = SOME e
Proof
    rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >>
        rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
QED

(* The range is the set of values taken on by an sptree.
  Not sure if these are worth moving. *)
Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End

Theorem range_delete:
  range (delete h v) ⊆ range v
Proof
  simp[range_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem range_insert:
  n ∉ domain fml ⇒
  range (insert n l fml) = l INSERT range fml
Proof
  rw[range_def,EXTENSION,lookup_insert,domain_lookup]>>
  metis_tac[SOME_11]
QED

Theorem range_insert_2:
  C ∈ range (insert n l fml) ⇒ C ∈ range fml ∨ C = l
Proof
  fs[range_def,lookup_insert]>>
  rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem range_insert_SUBSET:
  range (insert n l fml) ⊆ l INSERT range fml
Proof
  rw[SUBSET_DEF]>>
  metis_tac[range_insert_2]
QED

(* END TODO *)

Theorem TWOxDIV2:
   2 * x DIV 2 = x
Proof
  ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
QED

Theorem alist_insert_REVERSE:
   ∀xs ys s.
   ALL_DISTINCT xs ∧ LENGTH xs = LENGTH ys ⇒
   alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s
Proof
  Induct \\ simp[alist_insert_def]
  \\ gen_tac \\ Cases \\ simp[alist_insert_def]
  \\ simp[alist_insert_append,alist_insert_def]
  \\ rw[] \\ simp[alist_insert_pull_insert]
QED

Theorem alist_insert_ALL_DISTINCT:
    ∀xs ys t ls.
  ALL_DISTINCT xs ∧
  LENGTH xs = LENGTH ys ∧
  PERM (ZIP (xs,ys)) ls ⇒
  alist_insert xs ys t = alist_insert (MAP FST ls) (MAP SND ls) t
Proof
  ho_match_mp_tac alist_insert_ind>>rw[]>>
  fs[LENGTH_NIL_SYM]>>rveq>>fs[ZIP]>>
  simp[alist_insert_def]>>
  fs[PERM_CONS_EQ_APPEND]>>
  simp[alist_insert_append,alist_insert_def]>>
  `¬MEM xs (MAP FST M)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac PERM_MEM_EQ>>
    fs[FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
    res_tac>>
    imp_res_tac MEM_ZIP>>
    fs[EL_MEM])>>
  simp[alist_insert_pull_insert]>>
  simp[GSYM alist_insert_append]>>
  metis_tac[MAP_APPEND]
QED

Theorem n2w_lt:
   (0w:'a word) < n2w a ∧ (0w:'a word) < n2w b ∧
   a < dimword (:'a) ∧ b < dimword (:'a)
   ⇒
   ((n2w a:'a word) < (n2w b:'a word) ⇔ a < b)
Proof
  simp[word_lt_n2w]
QED

Theorem n2w_le:
   (0w:'a word) < n2w a ∧ (0w:'a word) < n2w b ∧
   a < dimword (:'a) ∧ b < dimword (:'a)
   ⇒
   ((n2w a:'a word) ≤ (n2w b:'a word) ⇔ a ≤ b)
Proof
  srw_tac[][WORD_LESS_OR_EQ,LESS_OR_EQ]
  \\ metis_tac[n2w_lt]
QED

Theorem word_lt_0w:
   2 * n < dimword (:'a) ⇒ ((0w:'a word) < n2w n ⇔ 0 < n)
Proof
  simp[WORD_LT]
  \\ Cases_on`0 < n` \\ simp[]
  \\ simp[word_msb_n2w_numeric]
  \\ simp[NOT_LESS_EQUAL]
  \\ simp[wordsTheory.INT_MIN_def]
  \\ simp[dimword_def]
  \\ Cases_on`dimindex(:'a)`\\simp[]
  \\ simp[EXP]
QED

Theorem word_sub_lt:
   0w < n ∧ 0w < m ∧ n ≤ m ⇒ m - n < m
Proof
  rpt strip_tac
  \\ Cases_on`m`>>Cases_on`n`
  \\ qpat_x_assum`_ ≤ _`mp_tac
  \\ asm_simp_tac std_ss [n2w_le]
  \\ simp_tac std_ss [GSYM n2w_sub]
  \\ strip_tac
  \\ qmatch_assum_rename_tac`a:num ≤ b`
  \\ Cases_on`a=b`>-full_simp_tac(srw_ss())[]
  \\ `a < b` by simp[]
  \\ `0 < a` by (Cases_on`a`\\full_simp_tac(srw_ss())[]\\metis_tac[WORD_LESS_REFL])
  \\ `b - a < b` by simp[]
  \\ Cases_on`0w < n2w (b - a)`
  >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[n2w_lt]
    \\ simp[])
  \\ full_simp_tac(srw_ss())[word_lt_n2w,LET_THM]
QED

(* see #521 *)

Definition bytes_in_memory_def:
  (bytes_in_memory a [] m dm <=> T) /\
  (bytes_in_memory a ((x:word8)::xs) m dm <=>
     (m a = x) /\ a IN dm /\ bytes_in_memory (a + 1w) xs m dm)
End

Theorem bytes_in_memory_APPEND:
   !l1 l2 pc mem mem_domain.
      bytes_in_memory pc (l1 ++ l2) mem mem_domain <=>
      bytes_in_memory pc l1 mem mem_domain /\
      bytes_in_memory (pc + n2w (LENGTH l1)) l2 mem mem_domain
Proof
  Induct
  THEN ASM_SIMP_TAC list_ss
         [bytes_in_memory_def, wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w,
          GSYM wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD1]
  THEN DECIDE_TAC
QED

Theorem bytes_in_memory_change_domain:
   ∀a bs m md1 md2.
    bytes_in_memory a bs m md1 ∧
   (∀n. n < LENGTH bs ∧ a + n2w n ∈ md1 ⇒ a + n2w n ∈ md2)
  ⇒ bytes_in_memory a bs m md2
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]
QED

Theorem bytes_in_memory_change_mem:
   ∀a bs m1 m2 md.
    bytes_in_memory a bs m1 md ∧
   (∀n. n < LENGTH bs ⇒ (m1 (a + n2w n) = m2 (a + n2w n)))
  ⇒ bytes_in_memory a bs m2 md
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]
QED

Theorem bytes_in_memory_EL:
   ∀a bs m md k. bytes_in_memory a bs m md ∧ k < LENGTH bs ⇒ (m (a + n2w k) = EL k bs)
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[ADD1, GSYM word_add_n2w]
QED

Theorem bytes_in_memory_in_domain:
   ∀a bs m md k. bytes_in_memory a bs m md ∧ k < LENGTH bs ⇒ ((a + n2w k) ∈ md)
Proof
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[ADD1, GSYM word_add_n2w]
QED

Definition bytes_in_mem_def:
  (bytes_in_mem a [] m md k <=> T) /\
  (bytes_in_mem a (b::bs) m md k <=>
     a IN md /\ ~(a IN k) /\ (m a = b) /\
     bytes_in_mem (a+1w) bs m md k)
End

Theorem bytes_in_mem_IMP:
   !xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm
Proof
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,bytes_in_memory_def]
QED

Theorem fun2set_disjoint_union:
      DISJOINT d1 d2 ∧
  p (fun2set (m,d1)) ∧
   q (fun2set (m,d2))
   ⇒ (p * q) (fun2set (m,d1 ∪ d2))
Proof
  rw[set_sepTheory.fun2set_def,set_sepTheory.STAR_def,set_sepTheory.SPLIT_def]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ simp[EXTENSION]
  \\ conj_tac >- metis_tac[]
  \\ fs[IN_DISJOINT,FORALL_PROD]
QED

Theorem WORD_LS_IMP:
   a <=+ b ==>
    ?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)
Proof
  Cases_on `a` \\ Cases_on `b` \\ fs [WORD_LS]
  \\ fs [markerTheory.Abbrev_def]
  \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ rw [] THEN1
   (rewrite_tac [GSYM word_sub_def]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_SUB])
  \\ Cases_on `w` \\ fs [WORD_LO,word_add_n2w]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename1 `k < m:num` \\ qexists_tac `k - n` \\ fs []
QED

Theorem size_fromAList: (* TODO: move to HOL *)
  !xs. ALL_DISTINCT (MAP FST xs) ==> size (fromAList xs) = LENGTH xs
Proof
  Induct THEN1 (fs [] \\ EVAL_TAC)
  \\ fs [FORALL_PROD]
  \\ fs [fromAList_def,size_insert,domain_lookup,lookup_fromAList,ADD1] \\ rw []
  \\ imp_res_tac ALOOKUP_MEM \\ fs []
  \\ fs [MEM_MAP,EXISTS_PROD] \\ metis_tac []
QED

Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  `SORTED $< (MAP FST (toSortedAList t))` by
    simp[SORTED_toSortedAList]>>
  pop_assum mp_tac>>
  match_mp_tac SORTED_ALL_DISTINCT>>
  simp[irreflexive_def]
QED


Definition good_dimindex_def:
  good_dimindex (:'a) ⇔ dimindex (:'a) = 32 ∨ dimindex (:'a) = 64
End

Theorem good_dimindex_get_byte_set_byte:
  good_dimindex (:'a) ==>
    (get_byte a (set_byte (a:'a word) b w be) be = b)
Proof
  strip_tac \\
  match_mp_tac get_byte_set_byte \\
  fs[good_dimindex_def]
QED

Theorem byte_index_LESS_IMP[local]:
  (dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
    byte_index (a:'a word) be < byte_index (a':'a word) be /\ i < 8 ==>
    byte_index a be + i < byte_index a' be /\
    byte_index a be <= i + byte_index a' be /\
    byte_index a be + 8 <= i + byte_index a' be /\
    i + byte_index a' be < byte_index a be + dimindex (:α)
Proof
  fs [byte_index_def,LET_DEF] \\ Cases_on `be` \\ fs []
  \\ rpt strip_tac \\ rfs [] \\ fs []
  \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ decide_tac
QED

Theorem NOT_w2w_bit[local]:
  8 <= i /\ i < dimindex (:'b) ==> ~((w2w:word8->'b word) w ' i)
Proof
  rpt strip_tac \\ rfs [w2w] \\ decide_tac
QED

val LESS4 = DECIDE ``n < 4 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``
val LESS8 = DECIDE ``n < 8 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                               (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``

Theorem DIV_EQ_DIV_IMP[local]:
  0 < d /\ n <> n' /\ (n DIV d * d = n' DIV d * d) ==> n MOD d <> n' MOD d
Proof
  rpt strip_tac \\ Q.PAT_X_ASSUM `n <> n'` mp_tac \\ fs []
  \\ MP_TAC (Q.SPEC `d` DIVISION) \\ fs []
  \\ rpt strip_tac \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs []
QED

Theorem get_byte_set_byte_diff:
   good_dimindex (:'a) /\ a <> a' /\ (byte_align a = byte_align a') ==>
    (get_byte a (set_byte (a':'a word) b w be) be = get_byte a w be)
Proof
  fs [get_byte_def,set_byte_def,LET_DEF] \\ rpt strip_tac
  \\ `byte_index a be <> byte_index a' be` by
   (fs [good_dimindex_def]
    THENL
     [`w2n a MOD 4 < 4 /\ w2n a' MOD 4 < 4` by fs []
      \\ `w2n a MOD 4 <> w2n a' MOD 4` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 4 * 4 + n MOD 4) < dimword (:'a) /\
            (n' DIV 4 * 4 + n' MOD 4) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<4:num``])
        \\ `(n DIV 4 * 4) < dimword (:'a) /\
            (n' DIV 4 * 4) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs []),
      `w2n a MOD 8 < 8 /\ w2n a' MOD 8 < 8` by fs []
      \\ `w2n a MOD 8 <> w2n a' MOD 8` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 8 * 8 + n MOD 8) < dimword (:'a) /\
            (n' DIV 8 * 8 + n' MOD 8) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<8:num``])
        \\ `(n DIV 8 * 8) < dimword (:'a) /\
            (n' DIV 8 * 8) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs [])]
    \\ full_simp_tac bool_ss [LESS4,LESS8] \\ fs [] \\ rfs []
    \\ fs [byte_index_def,LET_DEF] \\ rw [])
  \\ fs [fcpTheory.CART_EQ,w2w,good_dimindex_def] \\ rpt strip_tac
  \\ `i' < dimindex (:'a)` by decide_tac
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i' + byte_index a be < dimindex (:'a)` by
   (fs [byte_index_def,LET_DEF] \\ rw []
    \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ decide_tac)
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ fs [DECIDE ``m <> n <=> m < n \/ n < m:num``]
  \\ Cases_on `w ' (i' + byte_index a be)` \\ fs []
  \\ imp_res_tac byte_index_LESS_IMP
  \\ fs [w2w] \\ TRY (match_mp_tac NOT_w2w_bit)
  \\ fs [] \\ decide_tac
QED

(* helpful theorems for _size *)
Theorem list_size_pair_size_MAP_FST_SND:
  list_size (pair_size f g) ls =
  list_size f (MAP FST ls) +
  list_size g (MAP SND ls)
Proof
  Induct_on`ls`>>simp[]>>
  Cases>>rw[]
QED

Theorem MEM_list_size:
  MEM x ls ⇒
  f x ≤ list_size f ls
Proof
  Induct_on`ls`>>simp[]>>
  rw[]>>gvs[]
QED
