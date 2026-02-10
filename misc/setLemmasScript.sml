(*
   General-purpose set and finite map lemmas (INJ, BIJ, SURJ, SUBSET,
   DISJOINT, IMAGE, FUPDATE_LIST, FLOOKUP, FDOM, etc.)
   used throughout the CakeML development.
*)
Theory setLemmas
Ancestors
  listLemmas pred_set finite_map
  list arithmetic pair
Libs
  boolSimps mp_then dep_rewrite BasicProvers

val _ = numLib.temp_prefer_num();

(* TODO: Used once in all of CakeML: could probably be pushed back to use-site*)
Theorem SUM_SET_IN_LT:
   !s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s
Proof
  metis_tac[SUM_SET_IN_LE,LESS_LESS_EQ_TRANS]
QED

(* only used in proof of tlookup_bij_iff *)
Theorem CARD_IMAGE_ID_BIJ:
   !s. FINITE s ==> (!x. x IN s ==> f x IN s) /\ CARD (IMAGE f s) = CARD s ==> BIJ f s s
Proof
  rw[]
  \\ `SURJ f s s` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
  \\ `IMAGE f s SUBSET s` by metis_tac[SUBSET_DEF,IN_IMAGE]
  \\ metis_tac[SUBSET_EQ_CARD,IMAGE_FINITE]
QED

(* never used *)
Theorem CARD_IMAGE_EQ_BIJ:
   !s. FINITE s ==> CARD (IMAGE f s) = CARD s ==> BIJ f s (IMAGE f s)
Proof
  rw[]
  \\ `SURJ f s (IMAGE f s)` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
QED

Theorem DISJOINT_IMAGE_SUC:
   DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y
Proof
  fs [IN_DISJOINT] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]
QED

(* used only in clos_callProof *)
Theorem IMAGE_SUC_SUBSET_UNION:
   IMAGE SUC x SUBSET IMAGE SUC y UNION IMAGE SUC z <=>
    x SUBSET y UNION z
Proof
  fs [SUBSET_DEF] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]
QED

Theorem SUBMAP_mono_FUPDATE_LIST:
   !ls f g.
   DRESTRICT f (COMPL (set (MAP FST ls))) SUBMAP
   DRESTRICT g (COMPL (set (MAP FST ls)))
   ==> f |++ ls SUBMAP g |++ ls
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
   INJ ($' f) (FDOM f) (FRANGE f) /\
   s = k INSERT FDOM f /\ v NOTIN FRANGE f /\
   t = v INSERT FRANGE f
  ==>
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

(* never used *)
Definition fmap_linv_def:
  fmap_linv f1 f2 <=> (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))
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

Theorem I_PERMUTES[simp]:
   I PERMUTES s
Proof
rw[BIJ_DEF, INJ_DEF, SURJ_DEF]
QED

(* never used *)
Theorem INJ_I:
 !s t. INJ I s t <=> s SUBSET t
Proof
SRW_TAC[][INJ_DEF,SUBSET_DEF]
QED

Theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]:
 FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)
Proof
Cases_on `x IN s` >>
srw_tac[][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY]
QED

Theorem DISJOINT_set_simp:
   DISJOINT (set []) s /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)
Proof
  fs [DISJOINT_DEF,EXTENSION] \\ metis_tac []
QED

Theorem DISJOINT_INTER:
   DISJOINT b c ==> DISJOINT (a INTER b) (a INTER c)
Proof
  rw[IN_DISJOINT] \\ metis_tac[]
QED

(* --- SUBSET / INJ lemmas --- *)

Theorem SUBSET_OF_INSERT:
  !s x. s SUBSET x INSERT s
Proof
  srw_tac[][SUBSET_DEF]
QED

Theorem INJ_UNION:
  !f A B.
  INJ f (A UNION B) UNIV ==>
  INJ f A UNIV /\
  INJ f B UNIV
Proof
  srw_tac[][]>>
  metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_UNION]
QED

Theorem INJ_less:
  INJ f s' UNIV /\ s SUBSET s'
  ==>
  INJ f s UNIV
Proof
  metis_tac[INJ_DEF,SUBSET_DEF]
QED

Theorem INJ_IMP_IMAGE_DIFF:
  INJ f (s UNION t) UNIV ==>
  IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t)
Proof
  rw[EXTENSION,EQ_IMP_THM]>> TRY (metis_tac[])>>
  fs[INJ_DEF]>>
  metis_tac[]
QED

Theorem INJ_IMP_IMAGE_DIFF_single:
  INJ f (s UNION {n}) UNIV ==>
  (IMAGE f s) DIFF {f n} = IMAGE f (s DIFF {n})
Proof
  rw[]>>
  `{f n} = IMAGE f {n}` by fs[]>>
  fs[INJ_IMP_IMAGE_DIFF]
QED

Theorem INJ_ALL_DISTINCT_MAP:
  !ls.
  ALL_DISTINCT (MAP f ls) ==>
  INJ f (set ls) UNIV
Proof
  Induct>>full_simp_tac(srw_ss())[INJ_DEF]>>srw_tac[][]>>
  metis_tac[MEM_MAP]
QED
