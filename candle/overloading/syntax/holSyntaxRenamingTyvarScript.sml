(*
 * Properties of RenamingTheory for our syntax
 *)
Theory holSyntaxRenamingTyvar
Ancestors
  toto comparison ternaryComparisons mlstring holSyntaxLib
  holSyntax holSyntaxExtra holSyntaxRenaming
Libs
  preamble

(* overloads for set operations on lists *)

val _ = Parse.add_infix("∩", 401, Parse.NONASSOC)
Overload "∩" = ``λs t. list_inter s t``
val _ = Parse.add_infix("\\", 401, Parse.NONASSOC)
Overload "\\" = ``λs t. list_complement s t``
val _ = Parse.add_infix("∪", 401, Parse.NONASSOC)
Overload "∪" = ``λs t. LIST_UNION s t``
val _ = Parse.add_infix("⊆", 401, Parse.NONASSOC)
Overload "⊆" = ``λs t. list_subset s t``

(* general properties of pairs *)

Theorem MEM_MAP_SWAP':
  !x s. MEM x (MAP SWAP s) = MEM (SWAP x) s
Proof
  rw[MEM_MAP,EQ_IMP_THM]
  >- fs[SWAP_def]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[SWAP_def]
QED

Theorem MEM_MAP_SWAP:
  !x s. MEM (SWAP x) (MAP SWAP s) = MEM x s
Proof
  Cases >> rename1`(x,y)`
  >> qspec_then `(y,x)` assume_tac MEM_MAP_SWAP'
  >> fs[SWAP_def]
QED

Theorem EVERY_MEM_SWAP_eq[local]:
  !s. EVERY (λx. MEM (SWAP x) s) s ⇔  set (MAP SWAP s) = set s
Proof
  rw[EQ_IMP_THM,EVERY_MEM,pred_setTheory.EXTENSION,FORALL_AND_THM]
  >- fs[MEM_MAP]
  >- fs[MEM_MAP_SWAP']
  >> fs[MEM_MAP_SWAP']
QED

Theorem SWAP_EQ_FST_SND:
  !x. SWAP x = x ⇔  FST x = SND x
Proof
  Cases >> rw[EQ_IMP_THM]
  >> fs[SWAP_def]
QED

Theorem SWAP_eq:
  SWAP = λ(x,y). (y,x)
Proof
  fs[FUN_EQ_THM,SWAP_def,ELIM_UNCURRY]
QED

Theorem MAP_INVOL:
  !f xs ys. INVOL f ==> (MAP f xs = ys) = (xs = MAP f ys)
Proof
  rw[INVOL_DEF,EQ_IMP_THM]
  >> TRY (qpat_x_assum `MAP _ = _` (assume_tac o GSYM))
  >> fs[MAP_MAP_o]
QED

Theorem SWAP_SWAP_INVOL:
  SWAP o SWAP = I
Proof
  rw[FUN_EQ_THM,SWAP_def]
QED

val MAP_SWAP = REWRITE_RULE[INVOL_DEF,SWAP_SWAP_INVOL]
  (SPEC ``SWAP:'a#'a->'a#'a`` (INST_TYPE [alpha |-> ``:'a#'a``] MAP_INVOL))

Theorem MEM_APPEND_SND_lemma:
  !a b c d x y.
    a ++ [x] ++ b = c ++ [y] ++ d
    ∧ ¬MEM (SND x) (MAP SND a) ∧ ¬MEM (SND y) (MAP SND c)
    ∧ SND x = SND y
    ==> a = c
Proof
  rw[]
  >> imp_res_tac (CONTRAPOS (SPEC_ALL (Q.ISPEC `SND` MEM_MAP_f)))
  >> qspecl_then [`a`,`[x]++b`,`c`,`[y]++d`]
      assume_tac (INST_TYPE [alpha |-> ``:'a#'b``] (REWRITE_RULE[IS_PREFIX_APPEND] APPEND_EQ_APPEND_IS_PREFIX))
  >> rfs[] >> rveq >> fs[]
  >> Cases_on `l`
  >> rfs[] >> rveq >> fs[]
QED

Theorem MEM_APPEND_FST_lemma:
  !a b c d x y.
    a ++ [x] ++ b = c ++ [y] ++ d
    ∧ ¬MEM (FST x) (MAP FST a) ∧ ¬MEM (FST y) (MAP FST c)
    ∧ FST x = FST y
    ==> a = c
Proof
  rw[]
  >> imp_res_tac (CONTRAPOS (SPEC_ALL (Q.ISPEC `FST` MEM_MAP_f)))
  >> qspecl_then [`a`,`[x]++b`,`c`,`[y]++d`]
      assume_tac (INST_TYPE [alpha |-> ``:'a#'b``] (REWRITE_RULE[IS_PREFIX_APPEND] APPEND_EQ_APPEND_IS_PREFIX))
  >> rfs[] >> rveq >> fs[]
  >> Cases_on `l`
  >> rfs[] >> rveq >> fs[]
QED

Theorem ALOOKUP_MEM_eq:
  !s x y. (ALOOKUP s x = SOME y)
  = ?pfx sfx. s = pfx ++ [(x,y)] ++ sfx /\ ~MEM x (MAP FST pfx)
Proof
  Induct >- fs[ALOOKUP_def]
  >> rw[EQ_IMP_THM]
  >> rename1`h::s`
  >> Cases_on `h`
  >> fs[ALOOKUP_def]
  >> FULL_CASE_TAC
  >> fs[]
  >- (
    qexists_tac `[]`
    >> fs[]
  )
  >- (
    res_tac
    >> qexists_tac `(q,r)::pfx`
    >> fs[]
  )
  >- (
    qmatch_asmsub_rename_tac `pfx ++ [_] ++ sfx`
    >> Cases_on `pfx`
    >> fs[MEM_MAP]
    >> qmatch_assum_rename_tac`(_,_)=h`
    >> first_x_assum (qspec_then `h` assume_tac)
    >> rveq
    >> fs[]
  )
  >- (
    qmatch_asmsub_rename_tac `pfx ++ [_] ++ sfx`
    >> Cases_on `pfx` >> fs[]
    >> ONCE_REWRITE_TAC[CONJ_COMM]
    >> asm_exists_tac
    >> fs[]
  )
QED

Theorem MEM_ALOOKUP_INJ:
   !f g xs x v. (!x y. f x = f y ==> x = y) /\ (!x y. g x = g y ==> x = y)
   ==> (ALOOKUP (MAP (f ## g) xs) (f x) = SOME (g v))
     = (ALOOKUP xs x = SOME v)
Proof
  NTAC 2 strip_tac
  >> Induct
  >> rw[PAIR_MAP]
  >- (
    Cases_on `h`
    >> fs[EQ_IMP_THM,ALOOKUP_def]
  )
  >> Cases_on `h`
  >> fs[ALOOKUP_def]
  >> FULL_CASE_TAC
  >> rw[]
QED

Theorem MEM_SPLIT_APPEND_FST_first:
  !s x. MEM x (MAP FST s) ==>
  ?pfx sfx q. s = pfx ++ [(x,q)] ++ sfx /\ ~MEM x (MAP FST pfx)
Proof
  rpt strip_tac
  >> pop_assum (assume_tac o PURE_ONCE_REWRITE_RULE [MEM_SPLIT_APPEND_first])
  >> fs[]
  >> rename1 `pfx ++ [x] ++ sfx`
  >> qexists_tac `TAKE (LENGTH pfx) s`
  >> qexists_tac `DROP (SUC (LENGTH pfx)) s`
  >> qexists_tac `EL (LENGTH pfx) (MAP SND s)`
  >> ONCE_REWRITE_TAC[GSYM ZIP_MAP_FST_SND_EQ]
  >> fs[MAP_APPEND,MAP_ZIP,MAP_TAKE]
  >> NTAC 2 (ONCE_REWRITE_TAC[GSYM APPEND_ASSOC])
  >> REWRITE_TAC[TAKE_LENGTH_APPEND,GEN_ALL MAP_DROP]
  >> qspec_then `LENGTH pfx` assume_tac LESS_EQ_SUC_REFL
  >> fs[DROP_APPEND2,ADD1]
  >> `LENGTH pfx < LENGTH (MAP SND s)` by (
    fs[LENGTH_MAP]
    >> ONCE_REWRITE_TAC[Q.ISPEC `FST` (CONV_RULE SWAP_FORALL_CONV (GSYM LENGTH_MAP))]
    >> ASM_REWRITE_TAC[]
    >> fs[]
  )
  >> imp_res_tac (GSYM TAKE1_DROP)
  >> ASM_REWRITE_TAC[GSYM TAKE_SUM]
  >> fs[TAKE_DROP]
QED

Theorem MEM_Tyvar_MAP_Tyvar:
  !l x. MEM (Tyvar x) (MAP Tyvar l) = MEM x l
Proof
  match_mp_tac MEM_f_MAP_f_INJ
  >> fs[]
QED

(* properties of set functions for lists (e.g. list_inter, LIST_UNION) *)

Theorem NULL_list_inter_INJ:
  !f l1 l2.  (!x y. f x = f y ==> x = y) ==>
  NULL (list_inter (MAP f l1) (MAP f l2)) = NULL (list_inter l1 l2)
Proof
  rw[NULL_FILTER,list_inter_def,EQ_IMP_THM]
  >- (
    dxrule MEM_MAP_f
    >> CCONTR_TAC
    >> fs[]
    >> imp_res_tac MEM_MAP_f
    >> imp_res_tac MEM_f_MAP_f_INJ
    >> rpt (first_x_assum (qspec_then `f` assume_tac))
    >> res_tac
  )
  >> CCONTR_TAC
  >> fs[MEM_MAP]
  >> rveq
  >> res_tac
  >> fs[]
QED

Theorem NULL_list_inter_MAP_Tyvar:
  !l1 l2. NULL (list_inter (MAP Tyvar l1) (MAP Tyvar l2)) = NULL (list_inter l1 l2)
Proof
  rw[NULL_list_inter_INJ]
QED

Theorem list_subset_id:
  !l. list_subset l l
Proof
  fs[list_subset_def,EVERY_MEM]
QED

Theorem list_complement_MAP_Tyvar:
  !a b. MAP Tyvar (list_complement a b) = (list_complement (MAP Tyvar a) (MAP Tyvar b))
Proof
  rw[]
  >> match_mp_tac list_complement_MAP_INJ
  >> fs[]
QED

Theorem LIST_INSERT_MAP_Tyvar:
  !a b. MAP Tyvar (LIST_INSERT a b) = (LIST_INSERT (Tyvar a) (MAP Tyvar b))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[LIST_INSERT_def]
  >> assume_tac (Q.ISPEC `Tyvar` MEM_f_MAP_f_INJ)
  >> fs[]
QED

Theorem LIST_UNION_MAP_Tyvar:
  !a b. MAP Tyvar (LIST_UNION a b) = LIST_UNION (MAP Tyvar a) (MAP Tyvar b)
Proof
  Induct
  >> rw[LIST_UNION_def]
  >> fs[LIST_INSERT_MAP_Tyvar,GSYM LIST_UNION_def]
QED

Theorem list_inter_LIST_UNION_NULL:
  !a b c. NULL (list_inter a (LIST_UNION b c))
  = (NULL (list_inter a b) /\ NULL (list_inter a c))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> rw[EQ_IMP_THM]
  >> fs[]
QED

Theorem MEM_LIST_UNION:
  !x a b. MEM x (LIST_UNION a b) = (MEM x a \/ MEM x b)
Proof
  fs[set_LIST_UNION]
QED

(* TODO put somewhere else *)
Theorem UNION_DIFF_EQ:
  !s t. ((s:'a -> bool) ∪ (t DIFF s)) = (s ∪ t)
Proof
  rw[pred_setTheory.EXTENSION,EQ_IMP_THM] >> fs[]
QED

Theorem CARD_LIST_TO_SET_ALL_DISTINCT_eq =
  CONJ
    (SPEC ``ls:'a list`` CARD_LIST_TO_SET_ALL_DISTINCT)
    (SPEC ``ls:'a list`` ALL_DISTINCT_CARD_LIST_TO_SET)
  |> REWRITE_RULE[GSYM EQ_IMP_THM]
  |> GEN_ALL

Theorem ALL_DISTINCT_set_eq:
  !A B. ALL_DISTINCT A
  ∧ LENGTH A = LENGTH B
  ∧ set A = set B
  ⇒ ALL_DISTINCT B
Proof
  rpt strip_tac
  >> fs[GSYM CARD_LIST_TO_SET_ALL_DISTINCT_eq,EQ_SYM_EQ]
QED

(* non-trivial permutations *)
Definition rename_bij_def:
  rename_bij s =
    (set (MAP FST s) = set (MAP SND s)
    ∧ EVERY (UNCURRY $<>) s
    ∧ ALL_DISTINCT (MAP SND s))
End

Theorem rename_bij_ALL_DISTINCT_FST:
  !s. rename_bij s⇒ ALL_DISTINCT (MAP FST s)
Proof
  rw[rename_bij_def]
  >> drule_then match_mp_tac ALL_DISTINCT_set_eq
  >> fs[]
QED

Theorem rename_bij_SWAP_IMP:
  !s. rename_bij s ⇒ rename_bij (MAP SWAP s)
Proof
  rpt strip_tac
  >> drule_then assume_tac rename_bij_ALL_DISTINCT_FST
  >> fs[FST_SND_SWAP,MAP_MAP_o,EVERY_MAP,rename_bij_def]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> match_mp_tac (Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC)
  >> fs[SWAP_def,ELIM_UNCURRY]
QED

Theorem rename_bij_def_imps =
  Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM] rename_bij_def
  |> CONJUNCT1

Theorem rename_bij_MEM_REV_ASSOCD:
  !s x. MEM x s ∧ rename_bij s
  ⇒ REV_ASSOCD (SND x) s (SND x) = FST x
Proof
  rw[]
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> drule_then strip_assume_tac MEM_SPLIT_APPEND_SND_first
  >> rveq
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> dxrule_then (REWRITE_TAC o single) REV_ASSOCD_drop_prefix
  >> qpat_x_assum `MEM _ (MAP _ _)` kall_tac
  >> dxrule_then assume_tac (List.nth(CONJUNCTS rename_bij_def_imps,2))
  >> rw[REV_ASSOCD_def]
  >> fs[ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM]
  >> TRY (dxrule (Q.ISPEC `SND` MEM_MAP_f)) >> fs[]
  >> qmatch_goalsub_abbrev_tac `FST x` >> Cases_on `x` >> fs[]
QED

Theorem rename_bij_NOT_MEM_REV_ASSOCD:
  !s. rename_bij s ⇒
  !y. ¬MEM y (MAP SND s) ⇔ REV_ASSOCD y s y = y
Proof
  rw[EQ_IMP_THM]
  >- (dxrule REV_ASSOCD_NOT_MEM_drop >> fs[])
  >> CCONTR_TAC >> fs[MEM_MAP]
  >> drule_all_then assume_tac rename_bij_MEM_REV_ASSOCD
  >> fs[rename_bij_def,EVERY_MEM]
  >> res_tac >> fs[ELIM_UNCURRY]
QED

Theorem rename_bij_SWAP_id:
  !s t. rename_bij s ⇒
  REV_ASSOCD (REV_ASSOCD t s t) (MAP SWAP s) (REV_ASSOCD t s t) = t
Proof
  rw[]
  >> Cases_on `MEM t (MAP SND s)`
  >- (
    fs[MEM_MAP]
    >> drule_all_then strip_assume_tac rename_bij_MEM_REV_ASSOCD
    >> ASM_REWRITE_TAC[]
    >> ONCE_REWRITE_TAC[GSYM FST_SND_SWAP]
    >> full_simp_tac(bool_ss)[o_DEF]
    >> match_mp_tac rename_bij_MEM_REV_ASSOCD
    >> fs[rename_bij_SWAP_IMP,MEM_MAP_SWAP]
  )
  >> drule_then (drule_then (rw o single))
    (Ho_Rewrite.REWRITE_RULE[IMP_CONJ_THM,EQ_IMP_THM,FORALL_AND_THM,pred_setTheory.EXTENSION]
    rename_bij_NOT_MEM_REV_ASSOCD |> CONJUNCT1)
  >> `~MEM t (MAP SND (MAP SWAP s))` by fs[rename_bij_def,FST_SND_SWAP,MAP_MAP_o]
  >> dxrule_then assume_tac rename_bij_SWAP_IMP
  >> drule_then (fs o single) rename_bij_NOT_MEM_REV_ASSOCD
QED

Theorem rename_bij_SWAP_id':
  !s t. rename_bij s ⇒
  REV_ASSOCD (REV_ASSOCD t (MAP SWAP s) t) s (REV_ASSOCD t (MAP SWAP s) t) = t
Proof
  rpt strip_tac
  >> dxrule_then assume_tac rename_bij_SWAP_IMP
  >> dxrule rename_bij_SWAP_id
  >> fs[MAP_MAP_o,SWAP_SWAP_INVOL]
QED

Theorem rename_bij_inj_MEM[local]:
  !s x x'. rename_bij s
  /\ REV_ASSOCD x s x = REV_ASSOCD x' s x'
  /\ MEM x (MAP SND s)
  ==> x = x'
Proof
  rw[MEM_MAP]
  >> drule_all_then strip_assume_tac rename_bij_MEM_REV_ASSOCD
  >> Cases_on `MEM x' (MAP SND s)`
  >- (
    fs[MEM_MAP]
    >> drule_all_then strip_assume_tac rename_bij_MEM_REV_ASSOCD
    >> rgs[]
    >> drule_then strip_assume_tac rename_bij_ALL_DISTINCT_FST
    >> dxrule_then match_mp_tac ALL_DISTINCT_FST_MEMs
    >> rename[`SND yy`]
    >> PairCases_on `yy`
    >> rgs[]
    >> rename[`SND yy'`]
    >> PairCases_on `yy'`
    >> rgs[]
    >> rpt $ goal_assum drule
  )
  >> drule $ cj 2 rename_bij_def_imps
  >> rw[EVERY_MEM]
  >> first_x_assum drule
  >> drule_then imp_res_tac rename_bij_NOT_MEM_REV_ASSOCD
  >> imp_res_tac $
  Ho_Rewrite.REWRITE_RULE[SET_EQ_SUBSET,SUBSET_DEF] $
  cj 1 rename_bij_def_imps
  >> first_x_assum $ drule_at Concl
  >> imp_res_tac $ Q.ISPEC `FST` MEM_MAP_f
  >> rgs[]
QED

Theorem rename_bij_inj_NOT_MEM[local]:
  !s x x'. rename_bij s
  /\ REV_ASSOCD x s x = REV_ASSOCD x' s x'
  /\ ~MEM x' (MAP SND s)
  ==> x = x'
Proof
  rw[]
  >> Cases_on `MEM x (MAP SND s)`
  >- (drule_all rename_bij_inj_MEM >> fs[])
  >> drule_then imp_res_tac rename_bij_NOT_MEM_REV_ASSOCD
  >> fs[]
QED

Theorem rename_bij_inj:
  !s x x'. rename_bij s
  /\ REV_ASSOCD x s x = REV_ASSOCD x' s x'
  ==> x = x'
Proof
  rw[]
  >> Cases_on `MEM x (MAP SND s)`
  >> metis_tac[rename_bij_inj_MEM,rename_bij_inj_NOT_MEM]
QED

(* TODO move *)
Theorem INSERT_DELETE':
  x ∉ A ∧ x INSERT A = B ⇒ A = B DELETE x
Proof
  rw[pred_setTheory.EXTENSION,DISJ_IMP_THM,FORALL_AND_THM,EQ_IMP_THM,DISJ_EQ_IMP]
QED

Theorem set_SWAP_EVEN:
  !s. set (MAP SWAP s) = set s ∧ EVERY (UNCURRY $<>) s
  ∧ ALL_DISTINCT s
  ⇒ EVEN (LENGTH s)
Proof
  gen_tac >> completeInduct_on `LENGTH s`
  >> Cases >> rw[]
  >> `h ≠ SWAP h` by (
    ONCE_REWRITE_TAC[GSYM PAIR]
    >> fs[SWAP_def,ELIM_UNCURRY]
  )
  >> `MEM (SWAP h) t` by (
    fs[ELIM_UNCURRY,DISJ_IMP_THM,FORALL_AND_THM,EQ_IMP_THM,pred_setTheory.EXTENSION]
  )
  >> pop_assum (strip_assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> fs[ALL_DISTINCT_APPEND,FORALL_AND_THM,DISJ_IMP_THM]
  >> fs[PULL_FORALL]
  >> first_x_assum (qspec_then `l1 ++ l2` mp_tac)
  >> fs[ALL_DISTINCT_APPEND,SIMP_RULE(srw_ss())[FUN_EQ_THM] SWAP_SWAP_INVOL]
  >> impl_tac
  >- (
    `~MEM (SWAP h) (MAP SWAP l1) ∧ ~MEM (SWAP h) (MAP SWAP l2)` by (
      fs[MEM_MAP_SWAP]
    )
    >> `~MEM h (MAP SWAP l1) ∧ ~MEM h (MAP SWAP l2)` by (
      fs[MEM_MAP_SWAP']
    )
    >> dxrule (ONCE_REWRITE_RULE[CONJ_COMM] INSERT_DELETE')
    >> rw[UNION_DELETE,DELETE_INSERT,DELETE_NON_ELEMENT_RWT,Once EQ_SYM_EQ]
    >> dxrule (ONCE_REWRITE_RULE[CONJ_COMM] INSERT_DELETE')
    >> rw[UNION_DELETE,DELETE_INSERT,DELETE_NON_ELEMENT_RWT,Once EQ_SYM_EQ]
  )
  >> qmatch_goalsub_abbrev_tac `EVEN a ⇒ EVEN b`
  >> `b = SUC(SUC(a))` by (unabbrev_all_tac >> fs[])
  >> fs[Abbr`b`,EVEN]
QED

Definition var_renaming_def:
  var_renaming s =
    (rename_bij s ∧ EVERY (λ(x,y). ∃a. y = Tyvar a) s)
End

Theorem var_renaming_eq:
  !s. var_renaming s =
    (rename_bij s ∧ EVERY (λx. ∃a b. x = (Tyvar a,Tyvar b)) s)
Proof
  fs[EQ_IMP_THM,var_renaming_def,FORALL_AND_THM,GSYM AND_IMP_INTRO]
  >> conj_tac
  >- (
    rw[EVERY_MEM,rename_bij_def,ELIM_UNCURRY]
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> last_x_assum ((dxrule_then assume_tac) o CONJUNCT1 o Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM,pred_setTheory.EXTENSION])
    >> fs[MEM_MAP]
    >> qpat_x_assum `!x. _ ⇒ ?x. _` imp_res_tac
    >> ONCE_REWRITE_TAC[GSYM PAIR]
    >> fs[Excl"PAIR"]
  )
  >> ntac 2 strip_tac
  >> match_mp_tac (Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC)
  >> fs[ELIM_UNCURRY,PULL_EXISTS]
QED

Theorem var_renaming_nil:
  var_renaming []
Proof
  fs[rename_bij_def,var_renaming_def]
QED

Theorem var_renaming_SWAP_IMP:
  !s. var_renaming s ⇒ var_renaming (MAP SWAP s)
Proof
  rw[var_renaming_eq,rename_bij_SWAP_IMP,EVERY_MAP]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> match_mp_tac (Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC)
  >> Cases
  >> rw[SWAP_def,ELIM_UNCURRY]
QED

Theorem var_renaming_SWAP_eq:
  !s. var_renaming (MAP SWAP s) = var_renaming s
Proof
  rw[EQ_IMP_THM,var_renaming_SWAP_IMP]
  >> imp_res_tac var_renaming_SWAP_IMP
  >> fs[MAP_MAP_o,SWAP_def,o_DEF]
QED

Theorem var_renaming_MEM_TYPE_SUBST:
  !s x y. MEM (x,Tyvar y) s ∧ var_renaming s
  ⇒ TYPE_SUBST s (Tyvar y) = x
Proof
  rw[var_renaming_def]
  >> drule_all rename_bij_MEM_REV_ASSOCD
  >> fs[]
QED

Theorem var_renaming_MEM_REV_ASSOCD =
  REWRITE_RULE[TYPE_SUBST_def]var_renaming_MEM_TYPE_SUBST

Theorem var_renaming_NOT_MEM_TYPE_SUBST:
  !s. var_renaming s ⇒
  !y. ¬MEM (Tyvar y) (MAP SND s) ⇔ TYPE_SUBST s (Tyvar y) = Tyvar y
Proof
  fs[var_renaming_def,rename_bij_NOT_MEM_REV_ASSOCD]
QED

Theorem var_renaming_NOT_MEM_REV_ASSOCD_IMP =
  Ho_Rewrite.REWRITE_RULE
    [FORALL_AND_THM,IMP_CONJ_THM,AND_IMP_INTRO,EQ_IMP_THM,TYPE_SUBST_def]
    var_renaming_NOT_MEM_TYPE_SUBST
  |> CONJUNCT1 |> Ho_Rewrite.REWRITE_RULE[PULL_FORALL,AND_IMP_INTRO]

Theorem var_renaming_SWAP_id:
  !s t. var_renaming s ⇒
  TYPE_SUBST (MAP SWAP s) (TYPE_SUBST s t) = t
Proof
  rw[TYPE_SUBST_compose]
  >> CONV_TAC (RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL]))
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> REWRITE_TAC[GSYM TYPE_SUBST_compose]
  >> Cases_on `MEM (Tyvar x) (MAP SND s)`
  >- (
    fs[MEM_MAP] >> PairCases_on `y` >> fs[] >> rveq
    >> `?y. y0 = Tyvar y` by (fs[EVERY_MEM,var_renaming_eq] >> res_tac >> fs[])
    >> VAR_EQ_TAC
    >> drule_all_then strip_assume_tac var_renaming_MEM_REV_ASSOCD
    >> ASM_REWRITE_TAC[]
    >> fs[Once (GSYM MEM_MAP_SWAP),SWAP_def]
    >> drule var_renaming_MEM_REV_ASSOCD
    >> fs[var_renaming_SWAP_IMP]
  )
  >> drule_then (fs o single) var_renaming_NOT_MEM_REV_ASSOCD_IMP
  >> `~MEM (Tyvar x) (MAP SND (MAP SWAP s))` by (
    fs[var_renaming_def,rename_bij_def]
    >> last_x_assum (mp_tac o CONJUNCT1 o Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM,pred_setTheory.EXTENSION])
    >> disch_then (dxrule o ONCE_REWRITE_RULE[MONO_NOT_EQ])
    >> fs[FST_SND_SWAP,MAP_MAP_o]
  )
  >> dxrule_then assume_tac var_renaming_SWAP_IMP
  >> drule_then (fs o single) var_renaming_NOT_MEM_REV_ASSOCD_IMP
QED

Theorem var_renaming_SWAP_id':
  !s t. var_renaming s ⇒
  TYPE_SUBST s (TYPE_SUBST (MAP SWAP s) t) = t
Proof
  rpt strip_tac
  >> dxrule_then assume_tac var_renaming_SWAP_IMP
  >> dxrule var_renaming_SWAP_id
  >> fs[MAP_MAP_o,SWAP_SWAP_INVOL]
QED

Theorem var_renaming_TYPE_SUBST_SWAP_eq:
  !s t t'. var_renaming s ⇒
  (TYPE_SUBST s t' = t <=> t' = TYPE_SUBST (MAP SWAP s) t)
Proof
  fs[EQ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM,var_renaming_SWAP_id,var_renaming_SWAP_id']
QED

Theorem var_renaming_Tyvar_imp:
  (!s x. var_renaming s ∧
  MEM x (MAP FST s) ⇒ ∃a. x = Tyvar a)
  /\ (!s x. var_renaming s ∧
  MEM x (MAP SND s) ⇒ ∃a. x = Tyvar a)
  /\ (!s x. var_renaming s ∧
  MEM x s ⇒ ∃a b. x = (Tyvar a,Tyvar b))
Proof
  rw[var_renaming_eq,MEM_MAP,EVERY_MEM]
  >> first_x_assum (drule_then strip_assume_tac)
  >> fs[]
QED

Theorem var_renaming_TYPE_SUBST_Tyvar:
  !s m x. var_renaming s
  /\ TYPE_SUBST s (Tyvar m) = x
  ==> ?b. x = Tyvar b
Proof
  rw[]
  >> Cases_on `MEM (Tyvar m) $ MAP SND s`
  >- (
    fs[MEM_MAP]
    >> rename[`MEM y _`]
    >> PairCases_on `y`
    >> fs[]
    >> rveq
    >> drule_all var_renaming_MEM_REV_ASSOCD
    >> drule_all_then strip_assume_tac $ cj 3 var_renaming_Tyvar_imp
    >> fs[]
  )
  >> fs[var_renaming_NOT_MEM_REV_ASSOCD_IMP]
QED

Theorem var_renaming_inj:
  !s x x'. var_renaming s
  /\ TYPE_SUBST s x = TYPE_SUBST s x'
  ==> x = x'
Proof
  gen_tac
  >> ho_match_mp_tac type_ind
  >> fs[]
  >> rw[]
  >- (
    drule_then (qspec_then `m` assume_tac) var_renaming_TYPE_SUBST_Tyvar
    >> Cases_on `x'`
    >> rgs[var_renaming_def]
    >> drule_then (qspecl_then [`Tyvar m`,`Tyvar m'`] mp_tac) rename_bij_inj
    >> fs[]
  )
  >> Cases_on `x'`
  >- (
    drule_then (qspec_then `m'` assume_tac) var_renaming_TYPE_SUBST_Tyvar
    >> rgs[var_renaming_def]
  )
  >> rgs[MAP_EQ_EVERY2,EVERY_MEM,LIST_REL_EL_EQN]
  >> match_mp_tac LIST_EQ
  >> rw[]
  >> first_x_assum $ drule_then assume_tac
  >> rename[`x < LENGTH _`]
  >> `MEM (EL x l) l` by fs[EL_MEM]
  >> first_x_assum $ drule_then assume_tac
  >> rw[]
QED

Theorem var_renaming_MEM_ineq:
  !s x. var_renaming s ∧ MEM x s ⇒ FST x ≠ SND x
Proof
  rw[var_renaming_def,rename_bij_def,EVERY_MEM,ELIM_UNCURRY]
QED

Theorem var_renaming_MAP_FST_SND:
  !s. var_renaming s
  ⇒ set (MAP FST s) = set (MAP SND s)
Proof
  fs[rename_bij_def,var_renaming_def]
QED

(* TODO remove unused theorem *)
Theorem var_renaming_compose_set[local]:
  !r s. var_renaming r ∧ var_renaming s⇒
  set (MAP FST (MAP (TYPE_SUBST s ## I) r))
  = ({ FST x | MEM x s ∧ MEM (SND x) (MAP FST r) }
      ∪ (set (MAP FST r) DIFF set (MAP SND s)))
Proof
  rw[pred_setTheory.EXTENSION,EQ_IMP_THM,PAIR_MAP_o,o_DEF,MAP_MAP_o]
  >- (
    qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
    >> fs[var_renaming_eq,EVERY_MEM]
    >> rename1`MEM y r`
    >> Cases_on `MEM (FST y) (MAP SND s)`
    >- (
      qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
      >> res_tac
      >> rveq >> fs[] >> rveq
      >> drule var_renaming_MEM_REV_ASSOCD
      >> rw[var_renaming_eq,EVERY_MEM]
      >> disj1_tac
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
      >> fs[]
    )
    >> res_tac
    >> VAR_EQ_TAC
    >> fs[]
    >> drule (ONCE_REWRITE_RULE[CONJ_COMM] var_renaming_NOT_MEM_REV_ASSOCD_IMP)
    >> rw[var_renaming_eq,EVERY_MEM]
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> fs[]
  )
  >- (
    qpat_x_assum `MEM _ (MAP FST _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
    >> drule (ONCE_REWRITE_RULE[CONJ_COMM]var_renaming_MEM_TYPE_SUBST)
    >> fs[var_renaming_eq,EVERY_MEM]
    >> res_tac
    >> rveq >> fs[] >> rveq
    >> disch_then (drule_then assume_tac)
    >> fs[MEM_MAP]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> qpat_x_assum `MEM _ (MAP FST _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
  >> drule var_renaming_NOT_MEM_REV_ASSOCD_IMP
  >> fs[var_renaming_eq,EVERY_MEM]
  >> res_tac
  >> rveq >> fs[] >> rveq
  >> disch_then (drule_then assume_tac)
  >> fs[MEM_MAP]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

(* TODO remove unused theorem *)
Theorem var_renaming_compose_props[local]:
  ∀r s. var_renaming s ∧ var_renaming r
  ⇒ let s = MAP (TYPE_SUBST s ## I) r ++ s
  in
    (set (MAP FST s) = set (MAP SND s)
    ∧ EVERY (λ(x,y). ∃a. y = Tyvar a) s)
Proof
  REWRITE_TAC[LET_THM]
  >> BETA_TAC
  >> reverse (rpt strip_tac)
  >- (
    fs[var_renaming_def,EVERY_MAP]
    >> qpat_x_assum `EVERY _ r` mp_tac
    >> match_mp_tac (Ho_Rewrite.REWRITE_RULE[PULL_FORALL] EVERY_MONOTONIC)
    >> fs[ELIM_UNCURRY]
  )
  >> drule var_renaming_compose_set
  >> disch_then (last_assum o mp_then Any mp_tac)
  >> fs[var_renaming_def,EVERY_MAP]
  >> fs[rename_bij_def,MAP_MAP_o,o_DEF,PAIR_MAP_THM,ETA_THM]
  >> rw[]
  >> qmatch_goalsub_abbrev_tac `((C ∪ _) ∪ _) = (A ∪ B)`
  >> `C ⊆ B` by (
    unabbrev_all_tac
    >> qpat_x_assum `set (MAP FST s) = _` (fs o single o GSYM)
    >> fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP_f]
  )
  >> fs[UNION_DIFF_EQ,UNION_IDEMPOT,AC UNION_ASSOC UNION_COMM,SUBSET_UNION_ABSORPTION]
QED

Theorem var_renaming_compose_set_FST_FILTER[local]:
  !r s.  var_renaming s ∧ var_renaming r
  ⇒ set (MAP FST (FILTER (λ(x,y). x ≠ y) (MAP (TYPE_SUBST s ## I) r)))
  = ({ FST x | ∃a. MEM x s ∧ MEM (SND x,a) r ∧ a ≠ FST x}
      ∪ (set (MAP FST r) DIFF set (MAP SND s)))
Proof
  rw[pred_setTheory.EXTENSION,EQ_IMP_THM,PAIR_MAP_o,o_DEF,MAP_MAP_o]
  >- (
    qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP,FILTER_MAP,o_DEF,MEM_FILTER,ELIM_UNCURRY])
    >> fs[var_renaming_eq,EVERY_MEM]
    >> rename1`MEM y' r`
    >> Cases_on `MEM (FST y') (MAP SND s)`
    >- (
      qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
      >> res_tac
      >> gvs[]
      >> drule var_renaming_MEM_REV_ASSOCD
      >> rw[var_renaming_eq,EVERY_MEM,PULL_EXISTS]
      >> disj1_tac
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[]
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[]
    )
    >> res_tac
    >> VAR_EQ_TAC
    >> fs[]
    >> drule (ONCE_REWRITE_RULE[CONJ_COMM] var_renaming_NOT_MEM_REV_ASSOCD_IMP)
    >> rw[var_renaming_eq,EVERY_MEM]
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> fs[]
  )
  >- (
    drule (ONCE_REWRITE_RULE[CONJ_COMM]var_renaming_MEM_TYPE_SUBST)
    >> qpat_x_assum `var_renaming r` (fn x =>
      drule (ONCE_REWRITE_RULE[CONJ_COMM]var_renaming_MEM_TYPE_SUBST)
      >> assume_tac x
    )
    >> fs[var_renaming_eq,EVERY_MEM]
    >> res_tac
    >> gvs[]
    >> rpt (disch_then (drule_then assume_tac))
    >> rw[MEM_MAP,MEM_FILTER,FILTER_MAP,o_DEF,PULL_EXISTS,ELIM_UNCURRY]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> qpat_x_assum `MEM _ (MAP FST _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
  >> qpat_x_assum `var_renaming s` assume_tac
  >> drule var_renaming_NOT_MEM_REV_ASSOCD_IMP
  >> fs[var_renaming_eq,EVERY_MEM]
  >> res_tac
  >> gvs[]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (el 2 (CONJUNCTS rename_bij_def_imps)))
  >> disch_then (drule_then assume_tac)
  >> rw[MEM_MAP,MEM_FILTER,FILTER_MAP,o_DEF,PULL_EXISTS,ELIM_UNCURRY]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[ELIM_UNCURRY]
QED

Theorem var_renaming_compose_set_SND_FILTER[local]:
  !r s.  var_renaming s ∧ var_renaming r
  ⇒ set (MAP SND (FILTER (λ(x,y). x ≠ y) (MAP (TYPE_SUBST s ## I) r)))
  = { SND x | MEM x r ∧ ¬MEM (SWAP x) s}
Proof
  rw[pred_setTheory.EXTENSION,EQ_IMP_THM,PAIR_MAP_o,o_DEF,MAP_MAP_o,SWAP_def]
  >- (
    qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP,FILTER_MAP,o_DEF,MEM_FILTER,ELIM_UNCURRY])
    >> gvs[ELIM_UNCURRY]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> rename1`MEM y' r`
    >> Cases_on `MEM (FST y') (MAP SND s)`
    >- (
      CCONTR_TAC
      >> qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP])
      >> qpat_x_assum `var_renaming s` assume_tac
      >> drule (ONCE_REWRITE_RULE[CONJ_COMM]var_renaming_MEM_REV_ASSOCD)
      >> fs[var_renaming_eq,EVERY_MEM]
      >> res_tac
      >> gvs[]
      >> goal_assum imp_res_tac
    )
    >> qpat_x_assum `var_renaming s` assume_tac
    >> drule var_renaming_NOT_MEM_REV_ASSOCD_IMP
    >> fs[var_renaming_eq,EVERY_MEM]
    >> res_tac
    >> gvs[]
    >> disch_then (drule_then assume_tac)
    >> CCONTR_TAC
    >> fs[]
    >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
    >> fs[]
  )
  >> rw[MEM_MAP,MEM_FILTER,FILTER_MAP,o_DEF,PULL_EXISTS,ELIM_UNCURRY]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> rename1`MEM x' r`
  >> Cases_on `MEM (FST x') (MAP SND s)`
  >- (
    CCONTR_TAC
    >> qpat_x_assum `var_renaming s` assume_tac
    >> drule (ONCE_REWRITE_RULE[CONJ_COMM]var_renaming_MEM_REV_ASSOCD)
    >> fs[var_renaming_eq,EVERY_MEM,MEM_MAP]
    >> res_tac
    >> gvs[]
    >> goal_assum imp_res_tac
    >> fs[rename_bij_def,EVERY_MEM]
  )
  >> qpat_x_assum `var_renaming s` assume_tac
  >> drule var_renaming_NOT_MEM_REV_ASSOCD_IMP
  >> fs[var_renaming_eq,EVERY_MEM]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (el 2 (CONJUNCTS rename_bij_def_imps)))
  >> res_tac
  >> gvs[ELIM_UNCURRY]
QED

Theorem var_renaming_clean_tysubst_eq:
  !s. var_renaming s ⇒ clean_tysubst s = s
Proof
  rw[rename_bij_def,var_renaming_def]
  >> match_mp_tac clean_tysubst_id
  >> fs[LAMBDA_PROD]
QED

(*
 The claim needs clean_tysubst.
 Counterexample: r = (a x)(b c), s = (b x), s o r = (a b c x)
 *)
Theorem var_renaming_compose:
  ∀r s. var_renaming s ∧ var_renaming r
  ⇒ var_renaming (clean_tysubst (MAP (TYPE_SUBST s ## I) r ++ s))
Proof
  rpt strip_tac
  >> reverse $ rw[var_renaming_def,rename_bij_def,clean_tysubst_prop]
  >- (
    qmatch_goalsub_abbrev_tac `EVERY _`
    >> qmatch_goalsub_abbrev_tac `clean_tysubst sor`
    >> qspec_then `sor` mp_tac $ cj 2 clean_tysubst_prop
    >> fs[ELIM_UNCURRY]
  )
  >> qmatch_goalsub_abbrev_tac`sr ++ s`
  >> rw[clean_tysubst_APPEND,FORALL_AND_THM,var_renaming_clean_tysubst_eq]
  >> `MAP SND sr = MAP SND r` by  (
    fs[Abbr`sr`,MAP_MAP_o,o_DEF]
    >> SIMP_TAC(std_ss ++ ETA_ss)[]
  )
  >> `ALL_DISTINCT (MAP SND sr)` by fs[var_renaming_def,rename_bij_def]
  >> dxrule clean_tysubst_FILTER_eq
  >> impl_tac
  >- (
    qabbrev_tac `P = λx. ?a. x = Tyvar a`
    >> qmatch_goalsub_abbrev_tac `EVERY P'`
    >> `P' = P o SND` by fs[Abbr`P`,Abbr`P'`,o_DEF]
    >> VAR_EQ_TAC
    >> REWRITE_TAC[GSYM EVERY_MAP,o_DEF]
    >> fs[Abbr`P`,var_renaming_def]
    >> fs[LAMBDA_PROD,EVERY_MAP]
  )
  >> disch_then (REWRITE_TAC o single)
  >> qabbrev_tac `P = λx. ~MEM x (MAP SND r)`
  >> qmatch_goalsub_abbrev_tac `FILTER P' s`
  >> `P' = P o SND` by fs[Abbr`P`,Abbr`P'`,o_DEF]
  >> VAR_EQ_TAC
  >> qpat_x_assum `_ = P o SND` kall_tac
  >> rw[var_renaming_compose_set_SND_FILTER,var_renaming_compose_set_FST_FILTER,Abbr`sr`]
  >> qpat_x_assum `_ = _` kall_tac
  >> rw[ELIM_UNCURRY,SWAP_def,EQ_IMP_THM,pred_setTheory.EXTENSION]
  >> rw[DISJ_EQ_IMP,PULL_FORALL]
  >> fs[FORALL_AND_THM,AND_IMP_INTRO]
  >- (
    fs[MEM_FILTER,GSYM FILTER_MAP,Abbr`P`]
    >> reverse conj_tac
    >- (
      imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
      >> fs[var_renaming_def]
      >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT1 rename_bij_def_imps))
      >> fs[EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
    )
    >> CCONTR_TAC
    >> fs[MEM_MAP,EVERY_MEM,var_renaming_def]
    >> first_x_assum (drule_all_then assume_tac)
    >> imp_res_tac rename_bij_ALL_DISTINCT_FST
    >> rpt (dxrule_then (dxrule_then assume_tac) ALL_DISTINCT_FST_MEMs)
    >> rename1`MEM x' s` >> PairCases_on`x'`
    >> rename1`MEM y r` >> PairCases_on`y`
    >> gvs[]
    >> metis_tac[]
  )
  >- (
    fs[var_renaming_def]
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT1 rename_bij_def_imps))
    >> fs[EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
    >> first_x_assum (dxrule_then (strip_assume_tac o REWRITE_RULE[MEM_MAP]))
    >> first_x_assum ((dxrule_then assume_tac) o ONCE_REWRITE_RULE[MONO_NOT_EQ])
    >> qpat_x_assum `!x. _ ∧ _ ⇒ _` imp_res_tac
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> rfs[]
  )
  >- (
    fs[MEM_FILTER,GSYM FILTER_MAP,Abbr`P`]
    >> qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[Once MEM_MAP,MEM_FILTER,o_DEF])
    >> gvs[ELIM_UNCURRY]
    >> reverse conj_tac
    >- (
      imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
      >> fs[var_renaming_def]
      >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT1 rename_bij_def_imps))
      >> fs[EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
    )
    >> goal_assum (strip_assume_tac o REWRITE_RULE[MEM_MAP])
    >> rename1`MEM y' r` >> PairCases_on`y'`
    >> rename1`MEM y s` >> PairCases_on`y`
    >> gvs[]
    >> qpat_x_assum `!x. _` imp_res_tac
    >> qpat_x_assum `var_renaming s` (strip_assume_tac o REWRITE_RULE[var_renaming_def])
    >> dxrule_then assume_tac rename_bij_ALL_DISTINCT_FST
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> fs[]
    >> dxrule_then (dxrule_then imp_res_tac) ALL_DISTINCT_FST_MEMs
    >> metis_tac[rename_bij_def,var_renaming_eq,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
  )
  >- (
    rw[Once MEM_MAP,MEM_FILTER,GSYM FILTER_MAP,Abbr`P`]
    >> `?a. MEM (SND x',a) s` by (
      qpat_x_assum `_ ⇒ _` mp_tac
      >> impl_tac
      >- (
        qpat_x_assum `var_renaming r` mp_tac
        >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
        >> rw[var_renaming_def,rename_bij_def,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
      )
      >> qpat_x_assum `var_renaming s` (strip_assume_tac o Ho_Rewrite.REWRITE_RULE[var_renaming_def,rename_bij_def,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM])
      >> strip_tac
      >> first_x_assum (drule_then (strip_assume_tac o REWRITE_RULE[MEM_MAP]))
      >> rename1`MEM y s` >> PairCases_on `y`
      >> fs[] >> goal_assum drule
    )
    >> goal_assum imp_res_tac
    >> qpat_x_assum `!x. _` imp_res_tac
    >> fs[]
    >> qpat_x_assum `var_renaming r` (strip_assume_tac o Ho_Rewrite.REWRITE_RULE[var_renaming_def,rename_bij_def,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM])
    >> first_x_assum (drule_then (strip_assume_tac o REWRITE_RULE[MEM_MAP]))
    >> rename1`MEM y r` >> PairCases_on `y`
    >> gvs[]
    >> first_x_assum (drule_then assume_tac)
    >> rename1`MEM x' r` >> PairCases_on `x'`
    >> gvs[]
    >> dxrule_then (dxrule_then imp_res_tac) ALL_DISTINCT_SND_MEMs
    >> fs[]
  )
  >> qpat_x_assum `MEM _ (MAP _ _)` (strip_assume_tac o REWRITE_RULE[GSYM FILTER_MAP,MEM_FILTER])
  >> rw[Once MEM_MAP,MEM_FILTER,GSYM FILTER_MAP,Abbr`P`]
  >> fs[ELIM_UNCURRY]
  >> qpat_x_assum `var_renaming s` (strip_assume_tac o Ho_Rewrite.REWRITE_RULE[var_renaming_def,rename_bij_def,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM])
  >> first_x_assum (drule_then (strip_assume_tac o REWRITE_RULE[MEM_MAP]))
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> goal_assum (strip_assume_tac o REWRITE_RULE[MEM_MAP])
  >> rfs[]
  >> rename1`MEM y' r` >> PairCases_on `y'`
  >> gvs[]
  >> qpat_x_assum `!x y. _` imp_res_tac
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[var_renaming_def,rename_bij_def,EQ_IMP_THM,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM]
  >> first_x_assum (drule_then (strip_assume_tac o REWRITE_RULE[MEM_MAP]))
  >> rename1`MEM yy r` >> PairCases_on `yy`
  >> gvs[]
  >> first_x_assum (drule_then assume_tac)
  >> gvs[]
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[]
QED

Theorem var_renaming_SWAP_inv:
  !s t. var_renaming s ∧ set (MAP SWAP s) = set s
    ⇒ TYPE_SUBST (MAP SWAP s) t = TYPE_SUBST s t
Proof
  rw[TYPE_SUBST_tyvars]
  >> Cases_on `MEM (Tyvar x) (MAP SND s)`
  >- (
    fs[MEM_MAP] >> rename1 `MEM y _` >> PairCases_on `y` >> fs[] >> rveq
    >> drule_all var_renaming_MEM_TYPE_SUBST
    >> dxrule_then assume_tac var_renaming_SWAP_IMP
    >> drule (ONCE_REWRITE_RULE[CONJ_COMM] var_renaming_MEM_TYPE_SUBST)
    >> fs[pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM,EQ_IMP_THM,MAP_MAP_o,FST_SND_SWAP]
  )
  >> `¬MEM (Tyvar x) (MAP SND (MAP SWAP s))` by (
    fs[var_renaming_eq,rename_bij_def,pred_setTheory.EXTENSION,FORALL_AND_THM,IMP_CONJ_THM,EQ_IMP_THM,MAP_MAP_o,FST_SND_SWAP]
    >> first_x_assum (match_mp_tac o ONCE_REWRITE_RULE[MONO_NOT_EQ])
    >> asm_rewrite_tac[]
  )
  >> imp_res_tac REV_ASSOCD_NOT_MEM_drop >> fs[]
QED

Theorem var_renaming_SWAP_inverse:
  !s x y. var_renaming s ∧ set (MAP SWAP s) = set s
    ∧ TYPE_SUBST s (Tyvar x) = (Tyvar y)
    ==> TYPE_SUBST s (Tyvar y) = (Tyvar x)
Proof
  rpt strip_tac
  >> qpat_x_assum `TYPE_SUBST _ _ = _` (REWRITE_TAC o single o GSYM)
  >> drule var_renaming_SWAP_id'
  >> drule_all_then (Ho_Rewrite.REWRITE_TAC o single) var_renaming_SWAP_inv
  >> fs[]
QED

Theorem var_renaming_SWAP_inverse':
  !s x. var_renaming s ∧ set (MAP SWAP s) = set s
    ==> TYPE_SUBST s (TYPE_SUBST s (Tyvar x)) = (Tyvar x)
Proof
  rpt strip_tac
  >> drule var_renaming_SWAP_id'
  >> drule_all_then (Ho_Rewrite.REWRITE_TAC o single) var_renaming_SWAP_inv
  >> fs[]
QED

Theorem FST_SND_SUBSET:
  !s. ALL_DISTINCT (MAP SND s) /\ ALL_DISTINCT (MAP FST s)
    ==>
    (set (MAP SND s) SUBSET set (MAP FST s)  ==> set (MAP FST s) SUBSET set (MAP SND s))
    /\ (set (MAP FST s) SUBSET set (MAP SND s) ==> (set (MAP SND s)) SUBSET set (MAP FST s))
Proof
  rw[]
  >> drule_at Any (Ho_Rewrite.REWRITE_RULE[PULL_FORALL,AND_IMP_INTRO] SUBSET_EQ_CARD)
  >> fs[GSYM SUBSET_ANTISYM_EQ,ALL_DISTINCT_CARD_LIST_TO_SET]
QED

Theorem ALL_DISTINCT_MEM_LENGTH_FILTER:
  !s y. MEM y s /\ ALL_DISTINCT s
  ==> LENGTH (FILTER (λx. x <> y) s) = PRE (LENGTH s)
Proof
  Induct >> rw[] >> fs[]
  >- fs[MEM_SPLIT]
  >> qmatch_goalsub_abbrev_tac `FILTER f`
  >> `EVERY f s` by fs[EVERY_MEM,Abbr`f`]
  >> fs[GSYM FILTER_EQ_ID]
QED

Theorem LNTH_SOME_MONO:
  !n m ll x. LNTH n ll = SOME x /\ m <= n ==> IS_SOME (LNTH m ll)
Proof
  rw[]
  >> qpat_x_assum `_ = SOME _` mp_tac
  >> rw[Once MONO_NOT_EQ]
  >> drule_then drule LNTH_NONE_MONO
  >> fs[]
QED

Theorem LNTH_IS_SOME_MONO:
  !n m ll. IS_SOME (LNTH n ll) /\ m <= n ==> IS_SOME (LNTH m ll)
Proof
  fs[Once IS_SOME_EXISTS,PULL_EXISTS]
  >> ACCEPT_TAC LNTH_SOME_MONO
QED

Theorem LUNFOLD_f_iter_index_shift:
  !n f x. IS_SOME (f x) ==>
  LNTH (SUC n) (LUNFOLD (OPTION_MAP (λx. (x,x)) o f) x)
    = LNTH n (LUNFOLD (OPTION_MAP (λx. (x,x)) o f) (THE (f x)))
Proof
  Induct
  >- (
    rw[OPTION_MAP_COMPOSE,IS_SOME_EXISTS]
    >> FULL_CASE_TAC
    >> gvs[]
  )
  >> rpt strip_tac
  >> rgs[IS_SOME_EXISTS]
QED

Theorem LUNFOLD_f_iter:
  !n f x. let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o f) x in
  IS_SOME (LNTH n ll) ==> LNTH (SUC n) ll = f (THE (LNTH n ll))
Proof
  Induct
  >- fs[OPTION_MAP_EQ_SOME,IS_SOME_EXISTS,PULL_EXISTS,OPTION_MAP_COMPOSE,o_DEF]
  >> full_simp_tac(bool_ss++LET_ss)[]
  >> REWRITE_TAC[IS_SOME_EXISTS]
  >> rpt strip_tac
  >> ONCE_REWRITE_TAC[LNTH_LUNFOLD]
  >> FULL_CASE_TAC
  >- (
    drule LNTH_SOME_MONO
    >> disch_then (qspec_then `0` (assume_tac o SIMP_RULE(std_ss)[LNTH_LUNFOLD,OPTION_MAP_COMPOSE]))
    >> fs[OPTION_MAP_EQ_SOME,IS_SOME_EXISTS]
  )
  >> fs[Excl"LUNFOLD",Excl"LNTH_THM",Excl"LNTH",Excl"LNTH_LUNFOLD"]
  >> first_x_assum match_mp_tac
  >> drule (Ho_Rewrite.REWRITE_RULE[PULL_EXISTS,IS_SOME_EXISTS] LUNFOLD_f_iter_index_shift)
  >> disch_then (qspec_then `n` assume_tac)
  >> rw[IS_SOME_EXISTS,Once EQ_SYM_EQ]
  >> rfs[Excl"LUNFOLD",Excl"LNTH_THM",Excl"LNTH",Excl"LNTH_LUNFOLD"]
  >> goal_assum drule
QED

Theorem LUNFOLD_f_iter_inj:
  !k n f x. let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o f) x in
  (!x y. IS_SOME (f x) /\ (f x = f y) ==> x = y)
  /\ LNTH (n + k) ll = LNTH n ll /\ IS_SOME (LNTH (n + k) ll)
  /\ 0 < k
  ==> THE (LNTH (PRE k) ll) = x
Proof
  gen_tac >> Induct
  >- (
    full_simp_tac(bool_ss++LET_ss)[]
    >> rpt strip_tac
    >> drule_then (qspec_then `PRE k` assume_tac) LNTH_IS_SOME_MONO
    >> rfs[]
    >> drule_then assume_tac (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter)
    >> drule_then (qspec_then `0` (mp_tac o REWRITE_RULE[IS_SOME_EXISTS])) LNTH_IS_SOME_MONO
    >> `SUC (PRE k) = k` by fs[]
    >> pop_assum (full_simp_tac (bool_ss) o single)
    >> rw[]
    >> fs[IS_SOME_EXISTS,PULL_EXISTS,Excl"LUNFOLD",Excl"LNTH_THM",Excl"LNTH",Excl"LNTH_LUNFOLD"]
  )
  >> full_simp_tac(bool_ss++LET_ss)[]
  >> rpt strip_tac
  >> last_x_assum match_mp_tac
  >> asm_rewrite_tac[]
  >> reverse conj_asm2_tac
  >- (
    match_mp_tac LNTH_IS_SOME_MONO
    >> goal_assum (drule_at Any)
    >> fs[]
  )
  >> qmatch_goalsub_abbrev_tac `A = B`
  >> `IS_SOME B` by (
    unabbrev_all_tac
    >> match_mp_tac LNTH_IS_SOME_MONO
    >> goal_assum (drule_at Any)
    >> fs[]
  )
  >> `(A = B) <=> (THE A = THE B)` by fs[IS_SOME_EXISTS]
  >> pop_assum (REWRITE_TAC o single)
  >> unabbrev_all_tac
  >> first_x_assum match_mp_tac
  >> imp_res_tac (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter)
  >> rgs[GSYM SUC_ADD_SYM,IS_SOME_EXISTS,PULL_EXISTS,Excl"LUNFOLD",Excl"LNTH_THM",Excl"LNTH",Excl"LNTH_LUNFOLD"]
QED

Theorem every_LTAKE_EVERY:
  !P ll k l. every P ll /\ LTAKE k ll = SOME l ==> EVERY P l
Proof
  rw[GSYM every_fromList_EVERY]
  >> match_mp_tac every_LAPPEND1
  >> (rename o single) `LTAKE k ll`
  >> Cases_on `LFINITE ll`
  >> imp_res_tac LTAKE_DROP
  >> first_x_assum (qspec_then `k` mp_tac)
  >> TRY (
    impl_tac >>
    drule_then assume_tac (Ho_Rewrite.REWRITE_RULE[IS_SOME_EXISTS,PULL_EXISTS] IS_SOME_LTAKE_less_opt_LLENGTH)
    >> gvs[LFINITE_LLENGTH,less_opt_def]
  )
  >> strip_tac
  >> qmatch_asmsub_abbrev_tac `LAPPEND _ l2`
  >> qexists_tac `l2`
  >> gvs[]
QED

Theorem ALOOKUP_bij_LNTH_SUC_LNTH_SOME[local]:
  !s n. ALL_DISTINCT (MAP SND s) /\ ALL_DISTINCT (MAP FST s) /\ EVERY (UNCURRY $<>) s
    ==> let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                  (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))
        in IS_SOME (LNTH (SUC n) ll) ==> IS_SOME (LNTH n ll)
Proof
  gen_tac
  >> SIMP_TAC (bool_ss++LET_ss) []
  >> qmatch_goalsub_abbrev_tac `LNTH _ ll`
  >> rw[]
  >> match_mp_tac LNTH_SOME_MONO
  >> fs[IS_SOME_EXISTS]
  >> goal_assum (drule_at Any) >> fs[]
QED

Theorem ALOOKUP_bij_every[local]:
    !s. ALL_DISTINCT (MAP SND s)
    /\ ALL_DISTINCT (MAP FST s)
    /\ EVERY (UNCURRY $<>) s
    ==> every (λx. MEM x (MAP SND s))
          (LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
            (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s))))
Proof
  rw[]
  >> REWRITE_TAC[every_LNTH] >> Cases
  >- (
    rw[PULL_EXISTS,GSYM MEM_ALOOKUP,MEM_MAP]
    >> goal_assum (drule_at Any)
    >> fs[]
  )
  >> rpt strip_tac
  >> drule_all ALOOKUP_bij_LNTH_SUC_LNTH_SOME
  >> SIMP_TAC (bool_ss++LET_ss) []
  >> disch_then (imp_res_tac o (CONV_RULE (DEPTH_CONV (LAND_CONV (REWR_CONV IS_SOME_EXISTS)))))
  >> drule_then assume_tac (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter)
  >> map_every qmatch_asmsub_abbrev_tac [`LNTH _ ll`,`LUNFOLD f _`]
  >> rfs[]
  >> qpat_x_assum `SOME _ = ALOOKUP _ _` (assume_tac o GSYM)
  >> rgs[GSYM MEM_ALOOKUP]
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[]
QED

Theorem ALOOKUP_bij_LNTH_SUC_MEM_LNTH[local]:
  !s n. let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))
      in ALL_DISTINCT (MAP SND s) /\ ALL_DISTINCT (MAP FST s) /\ EVERY (UNCURRY $<>) s
        /\ IS_SOME (LNTH (SUC n) ll)
        ==> MEM (THE (LNTH n ll)) (MAP FST s) /\ MEM (THE (LNTH n ll)) (MAP SND s)
Proof
  gen_tac
  >> SIMP_TAC (bool_ss++LET_ss) []
  >> qmatch_goalsub_abbrev_tac `LNTH _ ll`
  >> rw[]
  >- (
    drule_all ALOOKUP_bij_LNTH_SUC_LNTH_SOME
    >> SIMP_TAC (bool_ss++LET_ss) []
    >> qunabbrev_tac `ll`
    >> disch_then (drule_then assume_tac)
    >> drule_then assume_tac (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter)
    >> CCONTR_TAC
    >> fs[GSYM ALOOKUP_NONE]
  )
  >> drule_all_then (match_mp_tac o SIMP_RULE std_ss [every_LNTH]) ALOOKUP_bij_every
  >> qunabbrev_tac `ll`
  >> drule_all_then (dxrule o SIMP_RULE(bool_ss++LET_ss)[]) ALOOKUP_bij_LNTH_SUC_LNTH_SOME
  >> rw[IS_SOME_EXISTS]
  >> fs[] >> goal_assum drule
QED

Theorem ALOOKUP_bij_distinct[local]:
 !s n k. ALL_DISTINCT (MAP SND s)
    /\ ALL_DISTINCT (MAP FST s)
    /\ EVERY (UNCURRY $<>) s
    /\ set (MAP SND s) <> set (MAP FST s)
    /\ (let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                  (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))
    in IS_SOME (LNTH n ll) /\ 0 < k /\ LNTH (n + k) ll = LNTH n ll)
    ==> F
Proof
  rpt strip_tac
  >> FULL_SIMP_TAC (bool_ss++LET_ss) []
  >> drule_at Any (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter_inj)
  >> disch_then (drule_at Any)
  >> map_every qmatch_asmsub_abbrev_tac [`LNTH _ ll`,`LUNFOLD f _`]
  >> impl_tac
  >- (
    fs[]
    >> rw[IS_SOME_EXISTS]
    >> rfs[]
    >> qpat_x_assum `SOME _ = ALOOKUP _ _` (assume_tac o GSYM)
    >> rfs[GSYM MEM_ALOOKUP]
    >> drule_then match_mp_tac ALL_DISTINCT_SND_MEMs
    >> rpt (goal_assum (drule_at Any))
  )
  >> drule_then (qspec_then `PRE k` mp_tac) (SIMP_RULE(bool_ss++LET_ss)[] ALOOKUP_bij_LNTH_SUC_LNTH_SOME)
  >> drule_then (qspec_then `PRE k` mp_tac) (SIMP_RULE(bool_ss++LET_ss)[] ALOOKUP_bij_LNTH_SUC_MEM_LNTH)
  >> `SUC (PRE k) = k` by fs[]
  >> pop_assum (CONV_TAC o DEPTH_CONV o REWR_CONV)
  >> rpt strip_tac
  >> qpat_x_assum `LNTH (_ + _) _ = LNTH _ _` (assume_tac o GSYM)
  >> fs[]
  >> drule_then (qspec_then `k` assume_tac) LNTH_IS_SOME_MONO
  >> qmatch_asmsub_abbrev_tac `HD ls`
  >> `~NULL ls` by (
    unabbrev_all_tac
    >> fs[NULL_FILTER,GSYM SUBSET_DEF,GSYM SUBSET_ANTISYM_EQ]
    >> drule FST_SND_SUBSET
    >> asm_rewrite_tac[]
  )
  >> `MEM (HD ls) ls` by (Cases_on `ls` >> fs[])
  >> qunabbrev_tac `ls`
  >> rgs[MEM_FILTER]
QED

Theorem ALOOKUP_bij_LFINITE[local]:
 !s. ALL_DISTINCT (MAP SND s)
    /\ ALL_DISTINCT (MAP FST s)
    /\ EVERY (UNCURRY $<>) s
    /\ set (MAP SND s) <> set (MAP FST s)
    ==> LFINITE (LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                  (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s))))
Proof
  rpt strip_tac
  >> drule_all_then assume_tac ALOOKUP_bij_every
  >> CCONTR_TAC
  >> map_every qmatch_asmsub_abbrev_tac [`LFINITE ll`,`LUNFOLD f _`]
  >> drule_then match_mp_tac (CONV_RULE (DEPTH_CONV (REWR_CONV LET_THM)) ALOOKUP_bij_distinct)
  >> qpat_x_assum `~LFINITE _` (qspec_then `SUC (LENGTH s)` strip_assume_tac
      o SIMP_RULE std_ss [LFINITE,GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS])
  >> drule_then (strip_assume_tac o GSYM) LTAKE_LENGTH
  >> fs[GSYM PULL_EXISTS]
  >> spose_not_then assume_tac
  >> `ALL_DISTINCT x` by (
    ntac 3 $ pop_assum mp_tac >> rpt $ pop_assum kall_tac
    >> REWRITE_TAC[EL_ALL_DISTINCT_EL_EQ,EQ_IMP_THM]
    >> rpt strip_tac >> rfs[]
    >> drule_then imp_res_tac LTAKE_LNTH_EL
    >> rw[Once EQ_LESS_EQ,LESS_OR_EQ,DISJ_EQ_IMP]
    >> fs[NOT_LESS,LESS_OR_EQ]
    >> drule_then strip_assume_tac LESS_ADD
    >> qpat_x_assum `!n. _ ==> _` $ imp_res_tac o REWRITE_RULE[IS_SOME_EXISTS]
    >> gvs[]
    >> res_tac >> fs[]
  )
  >> drule_all_then assume_tac every_LTAKE_EVERY
  >> qspecl_then [`set (MAP SND s)`,`set x`] assume_tac $ Ho_Rewrite.REWRITE_RULE[PULL_FORALL] CARD_SUBSET
  >> rfs[EVERY_MEM,SUBSET_DEF,ALL_DISTINCT_CARD_LIST_TO_SET]
QED

Theorem ALOOKUP_bij_IS_SOME_llast[local]:
 !s. ALL_DISTINCT (MAP SND s)
    /\ ALL_DISTINCT (MAP FST s)
    /\ EVERY (UNCURRY $<>) s
    /\ set (MAP SND s) <> set (MAP FST s)
    ==> let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                  (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))
        in IS_SOME (LNTH (PRE (THE (LLENGTH ll))) ll)
Proof
  rw[]
  >> drule_all_then assume_tac ALOOKUP_bij_LFINITE
  >> map_every qmatch_goalsub_abbrev_tac [`LUNFOLD f _`,`LNTH _ ll`]
  >> drule_then (qspec_then `THE (LLENGTH ll)` (strip_assume_tac o SIMP_RULE std_ss [])) LFINITE_TAKE
  >> qmatch_goalsub_abbrev_tac `LNTH n`
  >> drule_then (qspec_then `n` mp_tac) LTAKE_LNTH_EL
  >> qunabbrev_tac `n`
  >> Cases_on `THE (LLENGTH ll)`
  >- (
    qmatch_asmsub_abbrev_tac `HD ls`
    >> `~NULL ls` by (
      unabbrev_all_tac
      >> fs[NULL_FILTER,GSYM SUBSET_DEF,GSYM SUBSET_ANTISYM_EQ]
      >> drule FST_SND_SUBSET
      >> asm_rewrite_tac[]
    )
    >> `MEM (HD ls) ls` by (Cases_on `ls` >> fs[])
    >> `IS_SOME (f (HD ls))` by (
      map_every qunabbrev_tac [`ls`,`f`]
      >> fs[MEM_FILTER,IS_SOME_EXISTS,MEM_MAP,GSYM MEM_ALOOKUP]
      >> rename1 `MEM y' s` >> PairCases_on `y'`
      >> fs[]
      >> goal_assum drule
    )
    >> fs[Abbr`ll`,IS_SOME_EXISTS]
  )
  >> fs[]
QED

Theorem LFINITE_LNTH_LLENGTH_NONE:
  !ll. LFINITE ll ==> LNTH (THE (LLENGTH ll)) ll = NONE
Proof
  rw[LFINITE_LLENGTH]
  >> drule_then match_mp_tac LNTH_LLENGTH_NONE
  >> fs[]
QED

Theorem LFINITE_LNTH_IS_SOME:
  !ll n. LFINITE ll /\ n < THE (LLENGTH ll) ==> IS_SOME (LNTH n ll)
Proof
  rw[]
  >> dxrule_then (qspec_then `SUC n` assume_tac) LFINITE_TAKE
  >> rfs[IS_SOME_EXISTS]
  >> dxrule LTAKE_LNTH_EL
  >> fs[prim_recTheory.LESS_THM,AND_IMP_INTRO]
QED

Theorem ALOOKUP_bij_LLENGTH:
 !s. ALL_DISTINCT (MAP SND s)
    /\ ALL_DISTINCT (MAP FST s)
    /\ EVERY (UNCURRY $<>) s
    /\ set (MAP SND s) <> set (MAP FST s)
    ==> let ll = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s))
                  (HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))
        in IS_SOME (LLENGTH ll) /\ 0 < THE (LLENGTH ll)
Proof
  gen_tac
  >> fs[]
  >> disch_then strip_assume_tac
  >> drule_all_then assume_tac ALOOKUP_bij_LFINITE
  >> map_every qmatch_goalsub_abbrev_tac [`LUNFOLD f _`,`LLENGTH ll`]
  >> drule_all_then assume_tac ALOOKUP_bij_IS_SOME_llast
  >> drule_then assume_tac LFINITE_LNTH_LLENGTH_NONE
  >> rfs[LFINITE_LLENGTH,IS_SOME_EXISTS]
  >> CCONTR_TAC
  >> rgs[]
QED

Definition ALOOKUP_bij_def:
  ALOOKUP_bij s =
    if ~ALL_DISTINCT (MAP SND s)
      \/ ~ALL_DISTINCT (MAP FST s)
      \/ EXISTS (UNCURRY $=) s
    then []
    else if set (MAP SND s) = set (MAP FST s)
    then s
    else
      let f = LUNFOLD (OPTION_MAP (λx. (x,x)) o (ALOOKUP s)) ;
        a = HD (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s))
      in
        ALOOKUP_bij (SNOC (THE (LNTH (PRE (THE (LLENGTH (f a)))) (f a)),a) s)
Termination
  fs[SNOC_APPEND,o_UNCURRY_R]
  >> WF_REL_TAC `measure (λs. LENGTH (FILTER (λx. ~MEM x (MAP SND s)) (MAP FST s)))`
  >> fs[LENGTH_APPEND,FILTER_APPEND,Excl"LENGTH_MAP"]
  >> gen_tac
  >> disch_then strip_assume_tac
  >> map_every qmatch_goalsub_abbrev_tac [`HD ls`,`LUNFOLD f`,`LLENGTH ll`]
  >> fs[GSYM FILTER_FILTER,Once FILTER_COMM]
  >> `~NULL ls` by (
    unabbrev_all_tac
    >> fs[NULL_FILTER,GSYM SUBSET_DEF,GSYM SUBSET_ANTISYM_EQ]
    >> drule FST_SND_SUBSET
    >> asm_rewrite_tac[]
  )
  >> `MEM (HD ls) ls` by (Cases_on `ls` >> fs[])
  >> drule ALL_DISTINCT_MEM_LENGTH_FILTER
  >> impl_tac
  >- fs[Abbr`ls`,FILTER_ALL_DISTINCT]
  >> disch_then (reverse o rw o single)
  >- (Cases_on `LENGTH ls` >> fs[])
  >> drule_all_then assume_tac ALOOKUP_bij_IS_SOME_llast
  >> drule_all_then assume_tac ALOOKUP_bij_every
  >> fs[every_LNTH,IS_SOME_EXISTS]
  >> qmatch_assum_abbrev_tac `~MEM (THE llast) _`
  >> first_x_assum (drule_then assume_tac)
  >> rgs[Abbr`f`,o_DEF]
End

Theorem SUBSET_UNION_DISJ[local]:
  (!a b (c:'a set). a ⊆ b ∪ c /\ (a ∩ b) = EMPTY ==> a ⊆ c)
  /\ (!a b (c:'a set). a ⊆ b ∪ c /\ (a ∩ c) = EMPTY ==> a ⊆ b)
Proof
  conj_asm1_tac
  >- rw[SUBSET_DEF,pred_setTheory.EXTENSION,DISJ_EQ_IMP]
  >> metis_tac[UNION_COMM]
QED

Theorem ALOOKUP_bij_prop:
  !s. ALL_DISTINCT (MAP FST s) /\ ALL_DISTINCT (MAP SND s) /\ EVERY (UNCURRY $<>) s
  ==>
  ALL_DISTINCT (MAP FST (ALOOKUP_bij s))
  /\ ALL_DISTINCT (MAP SND (ALOOKUP_bij s)) /\ EVERY ($~ o UNCURRY $=) (ALOOKUP_bij s)
  /\ set (MAP FST (ALOOKUP_bij s)) = set (MAP SND (ALOOKUP_bij s))
  /\ ?e. ALOOKUP_bij s = s ++ e /\ set (MAP FST e) ⊆ set (MAP SND s) /\ set (MAP SND e) ⊆ set (MAP FST s)
Proof
  ho_match_mp_tac ALOOKUP_bij_ind
  >> gen_tac
  >> SIMP_TAC (bool_ss ++ LET_ss) [NOT_EXISTS]
  >> rpt (disch_then strip_assume_tac)
  >> map_every qmatch_asmsub_abbrev_tac [`HD ls`,`LUNFOLD f`,`LLENGTH ll`]
  >> ONCE_REWRITE_TAC[ALOOKUP_bij_def]
  >> TOP_CASE_TAC
  >- (
    rfs[]
    >> qpat_x_assum `EXISTS _ _` mp_tac
    >> rw[Once MONO_NOT_EQ,ELIM_UNCURRY,o_DEF]
    >> rw[Once LAMBDA_PROD]
  )
  >> pop_assum kall_tac
  >> TOP_CASE_TAC
  >- (rw[o_DEF,ELIM_UNCURRY] >> rw[Once LAMBDA_PROD])
  >> qpat_x_assum `_ ==> _` mp_tac
  >> fs[]
  >> impl_tac
  >- fs[ELIM_UNCURRY,o_DEF]
  >> impl_tac
  >- (
    drule_all_then assume_tac ALOOKUP_bij_IS_SOME_llast
    >> drule_all_then assume_tac ALOOKUP_bij_every
    >> rfs[SNOC_APPEND,ALL_DISTINCT_APPEND]
    >> conj_asm1_tac
    >- (
      drule_all_then strip_assume_tac ALOOKUP_bij_LFINITE
      >> drule_then assume_tac LFINITE_LNTH_LLENGTH_NONE
      >> unabbrev_all_tac
      >> drule (SIMP_RULE(bool_ss++LET_ss)[] LUNFOLD_f_iter)
      >> map_every qmatch_asmsub_abbrev_tac [`HD ls`,`LUNFOLD f`,`LLENGTH ll`]
      >> rfs[IS_SOME_EXISTS]
      >> Cases_on `THE (LLENGTH ll)` >> fs[ALOOKUP_NONE]
    )
    >> `~NULL ls` by (
      unabbrev_all_tac
      >> fs[NULL_FILTER,GSYM SUBSET_DEF,GSYM SUBSET_ANTISYM_EQ]
      >> drule FST_SND_SUBSET
      >> asm_rewrite_tac[]
    )
    >> `MEM (HD ls) ls` by (Cases_on `ls` >> fs[])
    >> conj_asm1_tac
    >- fs[MEM_FILTER,Abbr`ls`]
    >> `MEM (HD ls) (MAP FST s)` by fs[MEM_FILTER,Abbr`ls`]
    >> CCONTR_TAC
    >> fs[]
  )
  >> `~NULL s` by (CCONTR_TAC >> fs[NULL_EQ])
  >> `~NULL ls` by (
    qunabbrev_tac `ls`
    >> fs[NULL_FILTER,GSYM SUBSET_DEF,GSYM SUBSET_ANTISYM_EQ]
    >> drule FST_SND_SUBSET
    >> asm_rewrite_tac[]
  )
  >> `MEM (HD ls) ls` by (Cases_on `ls` >> fs[])
  >> drule_all_then assume_tac ALOOKUP_bij_LFINITE
  >> drule_all_then assume_tac ALOOKUP_bij_LLENGTH
  >> drule_all_then assume_tac ALOOKUP_bij_IS_SOME_llast
  >> drule_then (qspec_then `PRE (THE (LLENGTH ll))` assume_tac) LFINITE_LNTH_IS_SOME
  >> drule_all ALOOKUP_bij_every
  >> rfs[SNOC_APPEND,every_LNTH,LFINITE_LLENGTH]
  >> disch_then strip_assume_tac
  >> REWRITE_TAC[GSYM APPEND_ASSOC]
  >> disch_then strip_assume_tac
  >> goal_assum drule
(* >> fs[ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,GSYM CONJ_ASSOC] *)
  >> fs[GSYM CONJ_ASSOC]
  >> conj_asm1_tac
  >- (
    first_x_assum match_mp_tac
    >> rgs[IS_SOME_EXISTS]
    >> goal_assum drule
  )
  >> conj_asm1_tac
  >- (
    match_mp_tac $ cj 2 SUBSET_UNION_DISJ
    >> goal_assum drule
    >> fs[ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,pred_setTheory.EXTENSION]
    >> first_x_assum match_mp_tac
    >> fs[MEM_FILTER,Abbr`ls`]
  )
  >> conj_tac >- fs[MEM_FILTER,Abbr`ls`]
  >> match_mp_tac $ cj 2 SUBSET_UNION_DISJ
  >> goal_assum drule
  >> fs[ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,pred_setTheory.EXTENSION]
QED

(* less strict renaming *)

Definition renaming_compute_def:
  renaming_compute s = EVERY (λ(y,x). case x of
    | Tyvar a => (
      case (ALOOKUP (MAP SWAP s) (Tyvar a)) of
      | SOME (Tyvar b) => T
      | NONE => T
      | _ => F
    ) | _ => T) s
End

(* TODO: renaming_def in holSyntaxExtraScript.sml is too strong. Use this instead *)
Definition renaming_def:
  renaming s = !x pfx sfx.
    MAP SND s = pfx ++ [Tyvar x] ++ sfx /\ ~MEM (Tyvar x) pfx
    ==> ?a. ALOOKUP (MAP SWAP s) (Tyvar x) = SOME (Tyvar a)
End

Theorem renaming_imp:
  !s x. renaming s /\ MEM (Tyvar x) (MAP SND s)
  ==> ?pfx sfx q. s = pfx ++ [Tyvar q,Tyvar x] ++ sfx /\ ~MEM (Tyvar x) (MAP SND pfx)
Proof
  rw[renaming_def]
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> qmatch_assum_rename_tac `s = pfx ++ [(q,Tyvar x)] ++ sfx`
  >> first_x_assum (qspecl_then [`x`,`MAP SND pfx`,`MAP SND sfx`] assume_tac)
  >> rfs[MAP_APPEND,ALOOKUP_APPEND]
  >> ONCE_REWRITE_TAC[CONJ_COMM]
  >> asm_exists_tac
  >> `ALOOKUP (MAP SWAP pfx) (Tyvar x) = NONE` by (
    qpat_x_assum `~MEM _ _` mp_tac
    >> rpt(pop_assum kall_tac)
    >> rw[MEM_MAP,ALOOKUP_FAILS,SWAP_def]
    >> first_x_assum (qspec_then `y` assume_tac)
    >> fs[]
  )
  >> fs[SWAP_def]
QED

Theorem renaming_compute_eq:
  !s. renaming s = renaming_compute s
Proof
  rw[EQ_IMP_THM,renaming_compute_def,renaming_def,EVERY_MEM,ELIM_UNCURRY]
  >- (
    FULL_CASE_TAC
    >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
    >> imp_res_tac MEM_SPLIT_APPEND_SND_first
    >> rename1`Tyvar m`
    >> rename1`pfx ++ _ ++ sfx`
    >> first_x_assum (qspecl_then [`m`,`MAP SND pfx`,`MAP SND sfx`] assume_tac)
    >> rfs[MAP_APPEND]
  )
  >- (
    rename1`MAP SND s = pfx ++ _ ++ _`
    >> `LENGTH (pfx) < LENGTH s` by (
      REWRITE_TAC[Q.ISPEC `SND` (CONV_RULE SWAP_FORALL_CONV (GSYM LENGTH_MAP))]
      >> ASM_REWRITE_TAC[]
      >> fs[]
    )
    >> `MEM (EL (LENGTH pfx) s) s` by (
      fs[MEM_EL] >> asm_exists_tac >> fs[]
    )
    >> first_x_assum drule
    >> drule (INST_TYPE [alpha |-> ``:type#type``,beta|-> ``:type``] (GSYM EL_MAP))
    >> disch_then (REWRITE_TAC o single)
    >> ASM_REWRITE_TAC[]
    >> REWRITE_TAC[el_append3]
    >> FULL_CASE_TAC >> fs[]
    >> CASE_TAC
    >- (
      qpat_x_assum `_ = NONE` mp_tac
      >> fs[ALOOKUP_FAILS,MEM_MAP,SWAP_def]
      >> ONCE_REWRITE_TAC[CONJ_COMM]
      >> asm_exists_tac
      >> drule (INST_TYPE [alpha |-> ``:type#type``,beta|-> ``:type``] (GSYM EL_MAP))
      >> disch_then (REWRITE_TAC o single)
      >> ASM_REWRITE_TAC[]
      >> REWRITE_TAC[el_append3]
    )
    >> FULL_CASE_TAC
  )
QED

Theorem renaming_eq:
  !s. renaming s = !x. MEM (Tyvar x) (MAP SND s)
  ==> ?a. ALOOKUP (MAP SWAP s) (Tyvar x) = SOME (Tyvar a)
Proof
  rw[EQ_IMP_THM,renaming_compute_eq,renaming_compute_def,EVERY_MEM]
  >- (
    fs[MEM_MAP]
    >> first_x_assum drule
    >> pairarg_tac
    >> strip_tac
    >> rveq
    >> fs[]
    >> FULL_CASE_TAC >> fs[]
    >> FULL_CASE_TAC
    >- (
      fs[ALOOKUP_FAILS,MEM_MAP,SWAP_def]
      >> qmatch_assum_rename_tac `MEM (y',Tyvar m) s`
      >> first_x_assum (qspec_then `(y',Tyvar m)` assume_tac)
      >> fs[]
    )
    >> fs[]
    >> FULL_CASE_TAC
    >> fs[]
  )
  >> pairarg_tac
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[]
  >> FULL_CASE_TAC
  >> first_x_assum drule
  >> FULL_CASE_TAC
  >> rw[]
  >> fs[]
QED

Theorem renaming_imp':
  !e. EVERY (λ(x,y). (?m n. (x = Tyvar m) /\ (y = Tyvar n))) e
  ==> renaming e
Proof
  rw[EVERY_MEM,renaming_def,ALOOKUP_MEM_eq]
  >> `MEM (Tyvar x) (MAP SND e)` by fs[]
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> `MEM (q,Tyvar x) e` by fs[]
  >> last_x_assum imp_res_tac
  >> fs[ELIM_UNCURRY,SWAP_def]
  >> qexists_tac `m`
  >> qexists_tac `MAP SWAP pfx'`
  >> fs[MAP_MAP_o,FST_SND_SWAP]
  >> fs[]
QED

(* properties of renaming and clean_tysubst *)

Theorem list_subset_clean_tysubst:
  !r. list_subset (clean_tysubst r) r
Proof
  Induct
  >> fs[list_subset_set,clean_tysubst_def,SUBSET_DEF]
  >> rpt strip_tac
  >> qmatch_asmsub_rename_tac `h::r`
  >> Cases_on `h`
  >> qmatch_asmsub_rename_tac `(_,z)`
  >> Cases_on `z`
  >> fs[clean_tysubst_def,list_subset_set,SUBSET_DEF]
  >> FULL_CASE_TAC
  >> fs[MEM_FILTER]
QED

Theorem clean_tysubst_ALOOKUP:
  !r x. MEM x (clean_tysubst r)
  = (ALOOKUP (MAP SWAP r) (SND x) = SOME (FST x) /\ SND x <> FST x /\ !a b. (SND x <> Tyapp a b ))
Proof
  Induct
  >- fs[clean_tysubst_def,ALOOKUP_def]
  >> rw[EQ_IMP_THM]
  >- (
    Cases_on `h` >> Cases_on `r'`
    >> fs[SWAP_def,ALOOKUP_def,clean_tysubst_def]
    >> TRY (FULL_CASE_TAC)
    >> fs[MEM_FILTER]
    >- (
      FULL_CASE_TAC >> fs[MEM_FILTER,ELIM_UNCURRY]
      >> qpat_x_assum `_ = (_,_)` (assume_tac o CONV_RULE(LHS_CONV(PURE_ONCE_REWRITE_CONV[GSYM PAIR])))
      >> fs[]
    )
    >- (
      FULL_CASE_TAC >> fs[MEM_FILTER,ELIM_UNCURRY]
      >- ( first_x_assum (qspec_then `x` assume_tac) >> fs[])
      >- (
        qpat_x_assum `_ = (_,_)` (assume_tac o CONV_RULE(LHS_CONV(PURE_ONCE_REWRITE_CONV[GSYM PAIR])))
        >> fs[]
      )
      >- ( first_x_assum (qspec_then `x` assume_tac) >> fs[])
    )
    >- ( first_x_assum (qspec_then `x` assume_tac) >> rfs[] >> fs[])
    >- ( first_x_assum (qspec_then `x` assume_tac) >> fs[])
  )
  >- (
    Cases_on `h` >> Cases_on `r'`
    >> fs[SWAP_def,ALOOKUP_def,clean_tysubst_def]
    >> TRY (FULL_CASE_TAC)
    >> fs[MEM_FILTER]
    >> first_x_assum (qspec_then `x` assume_tac)
    >> fs[]
  )
  >- (
    Cases_on `h` >> Cases_on `r'`
    >> fs[SWAP_def,ALOOKUP_def,clean_tysubst_def]
    >> TRY (FULL_CASE_TAC)
    >> fs[MEM_FILTER]
    >> first_x_assum (qspec_then `x` assume_tac)
    >> fs[]
  )
  >- (
    Cases_on `h` >> Cases_on `r'`
    >> fs[SWAP_def,ALOOKUP_def,clean_tysubst_def]
    >> TRY (FULL_CASE_TAC)
    >> fs[MEM_FILTER]
    >> FULL_CASE_TAC
    >> CONV_TAC(LAND_CONV(PURE_ONCE_REWRITE_CONV[GSYM PAIR]))
    >> fs[ELIM_UNCURRY]
  )
QED

Theorem clean_tysubst_NOT_MEM:
   !pfx a sfx q. ¬MEM (Tyvar a) (MAP SND pfx)
   ==> ~MEM (q,Tyvar a) (clean_tysubst (pfx ++ [(Tyvar a,Tyvar a)] ++ sfx))
Proof
  Induct
  >> fs[clean_tysubst_def,MEM_FILTER]
  >> Cases
  >> Cases_on `r`
  >> fs[clean_tysubst_def]
  >> FULL_CASE_TAC
  >> rw[MEM_FILTER]
QED

(* rename apart two two argument lists *)

Definition ren_def:
  ren rs cs =
    MAP (Tyvar ## Tyvar) (rename_apart_by #"A" rs cs)
End

Theorem ren_ALL_DISTINCT:
  !r c. ALL_DISTINCT (MAP SND (ren r c))
  /\ ALL_DISTINCT (MAP FST (ren r c))
Proof
  fs[ren_def,MAP_MAP_o]
  >> fs[GSYM MAP_MAP_o]
  >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac `MAP FST rab`
  >> Q.ISPECL_THEN [`MAP FST rab`,`Tyvar`] assume_tac (GSYM ALL_DISTINCT_MAP_inj)
  >> Q.ISPECL_THEN [`MAP SND rab`,`Tyvar`] assume_tac (GSYM ALL_DISTINCT_MAP_inj)
  >> unabbrev_all_tac
  >> fs[rename_apart_by_ALL_DISTINCT]
QED

Theorem ren_MEM:
  !x y r c. MEM (Tyvar y,Tyvar x) (ren r c) ==> (~MEM y c /\ MEM x (list_inter c r))
Proof
  rw[ren_def,MAP_MAP_o,MEM_MAP,PAIR_MAP]
  >> imp_res_tac rename_apart_by_MEM
  >> fs[]
QED

Theorem ren_Tyvars:
  !r c. EVERY (λx. ?y1 y2. x = (Tyvar y1,Tyvar y2)) (ren r c)
Proof
  rw[EVERY_MEM,ren_def,MEM_MAP,PAIR_MAP]
QED

Theorem ren_strlen_FST:
  !r c. EVERY (λa. ?x. a = Tyvar x /\ MAX_LIST (MAP strlen (r++c)) < strlen x) (MAP FST (ren r c))
Proof
  rw[EVERY_MEM,MEM_MAP]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] ren_Tyvars)
  >> fs[ren_def,PAIR_MAP,MEM_MAP]
  >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST)
  >> fs[]
QED

Theorem ren_MEM_SND:
  !r c x. MEM x (list_inter r c) = MEM (Tyvar x) (MAP SND (ren r c))
Proof
  fs[ren_def,MAP_MAP_o]
  >> fs[GSYM MAP_MAP_o,MEM_Tyvar_MAP_Tyvar,rename_apart_by_MEM_SND]
QED

Theorem ren_MEM_SND1 = ONCE_REWRITE_RULE[list_inter_set_comm] ren_MEM_SND

Theorem ren_disj_dom_img:
  !r c. NULL (list_inter (MAP FST (ren r c)) (MAP SND (ren r c)))
Proof
  fs[ren_def,MAP_MAP_o]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_disj_dom_img]
QED

Theorem ren_diff:
  !r c. EVERY (UNCURRY $<>) (ren r c)
Proof
  rw[ren_def,rename_apart_by_diff,EVERY_MAP,ELIM_UNCURRY,EVERY_MEM,MEM_MAP]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_diff)
  >> fs[ELIM_UNCURRY]
QED

Theorem ren_disj_img_c:
  !r c. NULL (list_inter (MAP FST (ren r c)) (MAP Tyvar c))
Proof
  fs[ren_def,MAP_MAP_o]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_disj_img_c]
QED

Theorem ren_disj_dom_img2:
  !r c. NULL (list_inter (MAP ((TYPE_SUBST (ren r c)) o $Tyvar) r) (MAP Tyvar c))
Proof
  rw[NULL_FILTER,list_inter_def] >> rw[MEM_MAP]
  >> Cases_on `MEM y' r` >> gvs[MEM_MAP]
  >> reverse $ Cases_on `MEM (Tyvar y') (MAP SND (ren r c))`
  >- (
    drule_then assume_tac TYPE_SUBST_drop_all
    >> gvs[GSYM ren_MEM_SND1,list_inter_def,MEM_FILTER]
  )
  >> drule_then strip_assume_tac TYPE_SUBST_MEM_MAP_SND
  >> imp_res_tac $ Q.ISPEC `FST` MEM_MAP_f
  >> imp_res_tac $ Q.ISPEC `Tyvar` MEM_MAP_f
  >> imp_res_tac $ SIMP_RULE (srw_ss()) [list_inter_def,NULL_FILTER] ren_disj_img_c
  >> drule_then assume_tac $ SIMP_RULE (srw_ss()) [list_inter_def,NULL_FILTER] ren_disj_dom_img
  >> gs[REV_ASSOCD_def]
QED

Theorem ren_disj_img_r:
  !r c. NULL (list_inter (MAP FST (ren r c)) (MAP Tyvar r))
Proof
  fs[ren_def,MAP_MAP_o]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_disj_img_r]
QED

Theorem SWAP_PAIR_MAP_COMM:
  !f. SWAP o (f ## f) = (f ## f) o SWAP
Proof
  rw[FUN_EQ_THM,SWAP_def,PAIR_MAP]
QED

Theorem ren_ALOOKUP:
  !v x r c. MEM (v,x) (ren r c)
    = (ALOOKUP (MAP SWAP (ren r c)) x = SOME v)
Proof
  rw[ren_def,MAP_MAP_o,SWAP_PAIR_MAP_COMM,EQ_IMP_THM]
  >> fs[GSYM MAP_MAP_o]
  >- (
    Q.ISPECL_THEN [`Tyvar`,`Tyvar`] assume_tac MEM_ALOOKUP_INJ
    >> fs[MEM_MAP] >> rveq
    >> fs[rename_apart_by_ALOOKUP]
  )
  >> qmatch_asmsub_abbrev_tac `MAP SWAP rab`
  >> fs[ALOOKUP_MEM_eq,PAIR_MAP]
  >> imp_res_tac (GSYM (PURE_REWRITE_RULE[APPEND_ASSOC] (ONCE_REWRITE_RULE[CONS_APPEND] MEM_SPLIT)))
  >> fs[MAP_MAP_o,GSYM SWAP_PAIR_MAP_COMM]
  >> fs[GSYM MAP_MAP_o]
  >> qpat_x_assum `MEM _ (MAP _ _)` (assume_tac o ONCE_REWRITE_RULE[MEM_MAP])
  >> fs[SWAP_def]
QED

Theorem ren_ALOOKUP_NONE:
  !x r c. (!v. ~MEM (v,x) (ren r c))
    = (ALOOKUP (MAP SWAP (ren r c)) x = NONE)
Proof
  fs[EQ_IMP_THM]
  >> rpt strip_tac
  >> CCONTR_TAC
  >> fs[ren_ALOOKUP]
  >> qmatch_asmsub_abbrev_tac `ALOOKUP s x`
  >> Cases_on `ALOOKUP s x`
  >> fs[]
QED

Theorem ren_INJ1:
  !r c x k.
  TYPE_SUBST (ren r c) (Tyvar x) = k
  <=> MEM (k,Tyvar x) (ren r c) \/
  (~MEM (Tyvar x) (MAP SND (ren r c))  /\ k = Tyvar x)
Proof
  rw[TYPE_SUBST_def,REV_ASSOCD_ALOOKUP]
  >> FULL_CASE_TAC
  >> fs[GSYM ELIM_UNCURRY]
  >> fs[REWRITE_RULE[SWAP_eq] (GSYM ren_ALOOKUP),REWRITE_RULE[SWAP_eq] (GSYM ren_ALOOKUP_NONE)]
  >> rw[EQ_IMP_THM]
  >- (
    rw[MEM_MAP]
    >> CCONTR_TAC
    >> Cases_on `y`
    >> fs[]
    >> rveq
    >> first_x_assum (qspec_then `q` assume_tac)
    >> fs[]
  )
  >> fs[]
  >> fs[EQ_IMP_THM]
  >- (
    fs[MEM_SPLIT]
    >> rfs[APPEND_EQ_APPEND_MID]
    >> rveq
    >- (qspecl_then [`r`,`c`] assume_tac ren_ALL_DISTINCT >> rfs[ALL_DISTINCT_APPEND])
    >- fs[APPEND_EQ_SING]
    >- (qspecl_then [`r`,`c`] assume_tac ren_ALL_DISTINCT >> rfs[ALL_DISTINCT_APPEND])
  )
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> fs[]
QED

Theorem ren_INJ = GSYM (CONV_RULE (DEPTH_CONV BETA_CONV)
  (REWRITE_RULE[GSYM ren_MEM_SND,MEM_FILTER,list_inter_def] ren_INJ1))

Theorem ren_ID:
  !r c x. MEM x (list_complement c r) \/ MEM x (list_complement r c) ==>
  TYPE_SUBST (ren r c) (Tyvar x) = (Tyvar x)
Proof
  rw[MEM_FILTER,list_complement_def]
  >> `~MEM (Tyvar x) (MAP SND (ren r c))` by (
    fs[GSYM ren_MEM_SND,list_inter_def,MEM_FILTER]
  )
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_x_assum (qspec_then `[]` assume_tac)
  >> fs[REV_ASSOCD_def]
QED

Theorem ren_renaming:
  !r c. renaming (ren r c)
Proof
  rw[renaming_eq,MEM_MAP,GSYM ren_ALOOKUP]
  >> Cases_on `y`
  >> fs[ren_def,MEM_MAP] >> rveq
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem ren_list_complement:
   !r rc c. NULL (list_inter (MAP SND (ren (list_complement r rc) c)) (MAP Tyvar rc))
Proof
  fs[ren_def,MAP_MAP_o]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_list_complement]
QED

Theorem ren_LIST_UNION:
   (!r c1 c2. NULL (list_inter (MAP FST (ren r (LIST_UNION c1 c2))) (MAP Tyvar c1)))
   /\ !r c1 c2. NULL (list_inter (MAP FST (ren r (LIST_UNION c1 c2))) (MAP Tyvar c2))
Proof
  fs[ren_def,MAP_MAP_o]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_LIST_UNION]
QED

Theorem LR_TYPE_SUBST_FILTER_SND_tyvars:
  !p s. is_const_or_type p ==>
  LR_TYPE_SUBST (FILTER (λx. MEM (SND x) (MAP Tyvar (FV p))) s) p
  = LR_TYPE_SUBST s p
Proof
  rw[is_const_or_type_eq,LAMBDA_PROD,sum_case_def,LR_TYPE_SUBST_cases,tvars_def,FV_def]
  >> fs[MEM_MAP,LR_TYPE_SUBST_cases]
  >> qspecl_then [`ty`,`s`] assume_tac TYPE_SUBST_FILTER_SND_tyvars
  >> fs[tvars_def]
  >> qmatch_goalsub_abbrev_tac `TYPE_SUBST (FILTER f1 s) _ = TYPE_SUBST (FILTER f2 s) _`
  >> `f1 = f2` by (
    unabbrev_all_tac
    >> rw[FUN_EQ_THM,EQ_IMP_THM]
  )
  >> fs[]
QED

Theorem FV_renaming_comm:
  !x y r c. is_const_or_type x ==>
    MEM y (MAP (TYPE_SUBST (ren r c) o Tyvar) (FV x)) = MEM y (MAP Tyvar (FV (LR_TYPE_SUBST (ren r c) x)))
Proof
  rw[FV_def,is_const_or_type_eq,sum_case_def,MEM_MAP,LR_TYPE_SUBST_cases,tvars_def,tyvars_TYPE_SUBST,EQ_IMP_THM]
  >> qspecl_then [`r`,`c`] assume_tac ren_Tyvars
  >> fs[sum_case_def,tvars_def,EVERY_MEM]
  >> qmatch_goalsub_abbrev_tac `REV_ASSOCD _ s _`
  >> fs[sum_case_def,LR_TYPE_SUBST_cases,tyvars_def,tvars_def,tyvars_TYPE_SUBST]
  >> qmatch_asmsub_abbrev_tac `MEM z (tyvars ty)`
    ORELSE qmatch_goalsub_abbrev_tac `REV_ASSOCD (Tyvar z) s _`
  >> Cases_on `MEM (Tyvar z) (MAP SND s)`
  >> TRY (imp_res_tac MEM_SPLIT_APPEND_SND_first)
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_assum (qspec_then `[(q,Tyvar z)]++sfx` assume_tac)
  >> first_x_assum (qspec_then `[]` assume_tac)
  >> first_x_assum (qspec_then `(q,Tyvar z)` assume_tac)
  >> rveq
  >> fs[REV_ASSOCD_def]
  >> rveq
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[tyvars_def]
QED

Theorem TYPE_SUBST_FILTER_MEM1:
  !x tv l1 l2. MEM x tv ==>
  TYPE_SUBST (FILTER (λx. MEM (SND x) (MAP Tyvar (tv))) l1 ++ FILTER (λx. ~MEM (SND x) (MAP Tyvar (tv))) l2) (Tyvar x)
  = TYPE_SUBST l1 (Tyvar x)
Proof
  rw[]
  >> imp_res_tac (Q.ISPEC `Tyvar` MEM_MAP_f)
  >> qmatch_goalsub_abbrev_tac `REV_ASSOCD _ (fl1 ++ fl2) _`
  >> Cases_on `MEM (Tyvar x) (MAP SND l1)`
  >> TRY (imp_res_tac MEM_SPLIT_APPEND_SND_first)
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_assum (qspec_then `[]` assume_tac)
  >> first_x_assum (qspec_then `[(q,Tyvar x)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def]
  >- (
    qunabbrev_tac `fl1`
    >> qmatch_goalsub_abbrev_tac `FILTER f1 _`
    >> `~MEM (Tyvar x) (MAP SND (FILTER f1 pfx))` by (
      qunabbrev_tac `f1`
      >> fs[MAP_SND_FILTER,MEM_FILTER,MAP_APPEND]
    )
    >> dxrule TYPE_SUBST_drop_prefix
    >> disch_then (qspec_then `[(q,Tyvar x)]++FILTER f1 sfx ++ fl2` assume_tac)
    >> qunabbrev_tac `f1`
    >> fs[FILTER_APPEND,REV_ASSOCD_def]
  )
  >> `~MEM (Tyvar x) (MAP SND (fl1 ++ fl2))` by (
    qunabbrev_tac `fl1`
    >> qunabbrev_tac `fl2`
    >> fs[MAP_SND_FILTER,MEM_FILTER,MAP_APPEND]
  )
  >> drule TYPE_SUBST_drop_prefix
  >> disch_then (qspec_then `[]` assume_tac)
  >> fs[]
QED

Theorem TYPE_SUBST_FILTER_MEM2:
  !x tv l1 l2. ~MEM x tv ==>
  TYPE_SUBST (FILTER (λx. MEM (SND x) (MAP Tyvar tv)) l1
    ++ FILTER (λx. ~MEM (SND x) (MAP Tyvar tv)) l2) (Tyvar x)
  = TYPE_SUBST l2 (Tyvar x)
Proof
  rw[]
  >> imp_res_tac (Q.ISPEC `Tyvar` MEM_MAP_f)
  >> qmatch_goalsub_abbrev_tac `REV_ASSOCD _ (FILTER f1 l1 ++ FILTER f2 l2) _`
  >> `~MEM (Tyvar x) (MAP SND (FILTER f1 l1))` by (
    qunabbrev_tac `f1`
    >> fs[MAP_SND_FILTER,MEM_FILTER]
    >> fs[MEM_MAP]
  )
  >> dxrule TYPE_SUBST_drop_prefix
  >> disch_then (qspec_then `FILTER f2 l2` assume_tac)
  >> fs[]
  >> Cases_on `MEM (Tyvar x) (MAP SND l2)`
  >> TRY (imp_res_tac MEM_SPLIT_APPEND_SND_first)
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_assum (qspec_then `[]` assume_tac)
  >> first_x_assum (qspec_then `[(q,Tyvar x)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def]
  >- (
    `~MEM (Tyvar x) (MAP SND (FILTER f2 pfx))` by (
      qunabbrev_tac `f2`
      >> qunabbrev_tac `f1`
      >> fs[MAP_SND_FILTER,MEM_FILTER,MAP_APPEND]
    )
    >> dxrule TYPE_SUBST_drop_prefix
    >> disch_then (qspec_then `[(q,Tyvar x)]++FILTER f2 sfx` assume_tac)
    >> qunabbrev_tac `f2`
    >> qunabbrev_tac `f1`
    >> fs[FILTER_APPEND,REV_ASSOCD_def,MEM_MAP]
  )
  >> `~MEM (Tyvar x) (MAP SND (FILTER f2 l2))` by (
    qunabbrev_tac `f2`
    >> qunabbrev_tac `f1`
    >> fs[MAP_SND_FILTER,MEM_FILTER,MAP_APPEND]
  )
  >> drule TYPE_SUBST_drop_prefix
  >> disch_then (qspec_then `[]` assume_tac)
  >> fs[]
QED

Theorem ren_MEM_SND_compl_union =
      GEN_ALL (Q.SPECL [`list_complement (r:mlstring list) (s:mlstring list)`,`LIST_UNION (s:mlstring list) c`] ren_MEM_SND)

Theorem ren_ID_compl_union =
      GEN_ALL (Q.SPECL [`list_complement (r:mlstring list) (s:mlstring list)`,`LIST_UNION (s:mlstring list) c`] ren_ID)

Theorem ren_TYPE_SUBST_INJ1:
  !r c x y.
    MEM x (LIST_UNION r c) /\ MEM y (LIST_UNION r c)
    /\ ~MEM x (list_inter r c) /\ ~MEM y (list_inter r c)
    /\ TYPE_SUBST (ren r c) (Tyvar x) = TYPE_SUBST (ren r c) (Tyvar y)
    ==> x = y
Proof
  rw[]
  >> imp_res_tac (ONCE_REWRITE_RULE[MONO_NOT_EQ] (Ho_Rewrite.REWRITE_RULE[FORALL_AND_THM,EQ_IMP_THM] ren_MEM_SND))
  >> imp_res_tac TYPE_SUBST_drop_all
  >> fs[REV_ASSOCD_def]
QED

Theorem ren_TYPE_SUBST_INJ2:
  !r c x y. MEM x (list_inter r c) /\ MEM y (list_inter r c)
    /\ TYPE_SUBST (ren r c) (Tyvar x) = TYPE_SUBST (ren r c) (Tyvar y)
    ==> x = y
Proof
  rw[]
  >> imp_res_tac ren_MEM_SND
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_x_assum (qspec_then `[(q,Tyvar x)]++sfx` assume_tac)
  >> first_x_assum (qspec_then `[(q',Tyvar y)]++sfx'` assume_tac)
  >> `MEM (q,Tyvar x) (ren r c)` by fs[]
  >> `MEM (q',Tyvar y) (ren r c)` by rfs[]
  >> qspecl_then [`r`,`c`] assume_tac ren_Tyvars
  >> rpt (qpat_x_assum `ren r c = _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  >> fs[REV_ASSOCD_def,EVERY_MEM]
  >> qpat_x_assum `!x. MEM _ _ ==> _` imp_res_tac
  >> qspecl_then [`r`,`c`] assume_tac ren_ALL_DISTINCT
  >> Q.ISPECL_THEN [`q`,`Tyvar x`,`Tyvar y`,`ren r c`] mp_tac ALL_DISTINCT_FST_MEMs
  >> fs[]
  >> disch_then match_mp_tac
  >> rveq
  >> ASM_REWRITE_TAC[]
QED

Theorem ren_TYPE_SUBST_INJ3:
  !r c x y.
    MEM x (list_inter r c)
    /\ ~MEM y (list_inter r c) /\ MEM y (LIST_UNION r c)
    /\ TYPE_SUBST (ren r c) (Tyvar x) = TYPE_SUBST (ren r c) (Tyvar y)
    ==> x = y
Proof
  rw[]
  >> qspecl_then [`r`,`c`,`y`] assume_tac ren_ID
  >> imp_res_tac ren_MEM_SND
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_x_assum (qspec_then `[(q,Tyvar x)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def,DISJ_IMP_THM]
  >> qpat_x_assum `ren r c = _` mp_tac
  >> qspecl_then [`r`,`c`] (assume_tac o REWRITE_RULE[list_inter_def,NULL_FILTER]) ren_disj_img_c
  >> qspecl_then [`r`,`c`] (assume_tac o REWRITE_RULE[list_inter_def,NULL_FILTER]) ren_disj_img_r
  >> rpt (first_x_assum (qspec_then `Tyvar y` assume_tac))
  >> fs[MEM_Tyvar_MAP_Tyvar]
  >> fs[MEM_FILTER,list_inter_def,list_complement_def,MEM_LIST_UNION]
  >> rfs[]
  >> strip_tac
  >> fs[]
QED

Theorem ren_TYPE_SUBST_INJ:
  !r c x y.
    MEM x (LIST_UNION r c) /\ MEM y (LIST_UNION r c)
    /\ TYPE_SUBST (ren r c) (Tyvar x) = TYPE_SUBST (ren r c) (Tyvar y)
    ==> x = y
Proof
  rpt strip_tac
  >> qspecl_then [`r`,`c`,`x`,`y`] mp_tac ren_TYPE_SUBST_INJ1
  >> qspecl_then [`r`,`c`,`x`,`y`] mp_tac ren_TYPE_SUBST_INJ2
  >> qspecl_then [`r`,`c`,`x`,`y`] mp_tac ren_TYPE_SUBST_INJ3
  >> qspecl_then [`r`,`c`,`y`,`x`] mp_tac ren_TYPE_SUBST_INJ3
  >> ASM_REWRITE_TAC[]
  >> Cases_on `MEM x (list_inter r c)`
  >> Cases_on `MEM y (list_inter r c)`
  >> ASM_REWRITE_TAC[]
  >> fs[]
QED

Theorem list_complement_MAP_INJ1[local]:
  !f a b x. (!x y. (MEM x a \/ MEM x b) /\ (MEM y a \/ MEM y b) ==> f x = f y ==> x = y) ==>
  (MEM x (MAP f (list_complement a b))) = MEM x (list_complement (MAP f a) (MAP f b))
Proof
  rw[EQ_IMP_THM] >> rw[list_complement_def,EVERY_MEM]
  >> fs[MEM_MAP,MEM_FILTER,list_complement_def]
  >> rw[]
  >- metis_tac[]
  >- (goal_assum $ drule_at Any >> fs[])
  >> spose_not_then assume_tac
  >> rpt $ first_x_assum $ qspec_then `y` assume_tac
  >> fs[]
QED

Theorem ren_MEM_list_complement:
  !r s c x. let sigma = ren (list_complement r s) (LIST_UNION s c) in
  MEM (Tyvar x) (MAP (TYPE_SUBST sigma o Tyvar) (list_complement r s))
  = MEM (Tyvar x) (list_complement (MAP (TYPE_SUBST sigma o Tyvar) r) (MAP (TYPE_SUBST sigma o Tyvar) s))
Proof
  rw[]
  >> irule list_complement_MAP_INJ1
  >> rw[o_DEF]
  >> qspecl_then [`list_complement r s`,`LIST_UNION s c`] mp_tac ren_TYPE_SUBST_INJ
  >> disch_then irule
  >> rw[MEM_FILTER,list_inter_def,list_complement_def,MEM_LIST_UNION,DISJ_EQ_IMP]
QED

(* bijective version of ren *)

Definition renn_def:
  renn r c =
    ren r c ++ MAP SWAP (ren r c)
End

Theorem renn_ALL_DISTINCT:
  !r c. ALL_DISTINCT (MAP SND (renn r c))
  /\ ALL_DISTINCT (MAP FST (renn r c))
Proof
  rw[ALL_DISTINCT_APPEND,renn_def,ren_ALL_DISTINCT,MAP_MAP_o,FST_SND_SWAP]
  >> imp_res_tac (REWRITE_RULE[list_inter_def,NULL_FILTER] ren_disj_dom_img)
  >> imp_res_tac ((REWRITE_RULE[list_inter_def,NULL_FILTER] o ONCE_REWRITE_RULE[NULL_list_inter_COMM]) ren_disj_dom_img)
  >> fs[]
QED

Theorem renn_Tyvars:
  !r c. EVERY (λx. ?y1 y2. x = (Tyvar y1,Tyvar y2)) (renn r c)
Proof
  rw[SWAP_def,EVERY_MEM,ren_def,renn_def,MEM_MAP,PAIR_MAP]
QED

Theorem renn_diff:
  !r c. EVERY (UNCURRY $<>) (renn r c)
Proof
  rw[EVERY_MEM,MEM_APPEND,renn_def,MEM_MAP,SWAP_def]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] ren_diff)
  >> fs[ELIM_UNCURRY]
QED

Theorem renn_set_MAP_SWAP:
  !r c. set (MAP SWAP (renn r c)) = set (renn r c)
Proof
  rw[renn_def,SWAP_SWAP_INVOL,MAP_MAP_o,UNION_COMM]
QED

Theorem renn_MEM_MAP_SWAP:
  !r c x. MEM x (MAP SWAP (renn r c)) <=> MEM x (renn r c)
Proof
  fs[renn_set_MAP_SWAP]
QED

(* renn is a var_renaming *)
Theorem renn_var_renaming:
  var_renaming (renn r c)
Proof
  fs[var_renaming_eq,rename_bij_def,renn_ALL_DISTINCT,renn_diff,renn_Tyvars]
  >> fs[MEM_MAP_SWAP,EVERY_MEM,GSYM renn_MEM_MAP_SWAP]
  >> fs[renn_def,MAP_MAP_o,FST_SND_SWAP,UNION_COMM]
QED

Theorem renn_MEM:
  !r c x y. MEM (x,y) (renn r c) <=> MEM (y,x) (renn r c)
Proof
  rw[]
  >> CONV_TAC $ LAND_CONV $ ONCE_REWRITE_CONV $ single $ GSYM MEM_MAP_SWAP
  >> fs[SWAP_eq,renn_MEM_MAP_SWAP]
QED

Theorem renn_MAP_FST_SND:
  !r c x. MEM x (MAP FST (renn r c)) <=> MEM x (MAP SND (renn r c))
Proof
  ONCE_REWRITE_TAC[CONJUNCT1 (GSYM FST_SND_SWAP)]
  >> fs[GSYM MAP_MAP_o]
  >> CONV_TAC(ONCE_DEPTH_CONV(RHS_CONV(PURE_ONCE_REWRITE_CONV [MEM_MAP])))
  >> fs[renn_set_MAP_SWAP]
  >> fs[MEM_MAP]
QED

Theorem renn_bij:
  !r c x y. TYPE_SUBST (renn r c) (Tyvar x) = (Tyvar y)
  ==> TYPE_SUBST (renn r c) (Tyvar y) = (Tyvar x)
Proof
  rpt gen_tac
  >> rename1`renn r c`
  >> qspecl_then [`r`,`c`] assume_tac (GEN_ALL renn_var_renaming)
  >> drule var_renaming_SWAP_inverse
  >> ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO]
  >> disch_then match_mp_tac
  >> fs[renn_set_MAP_SWAP]
QED

Theorem renn_bij2:
  !r c x y z.
  TYPE_SUBST (renn r c) (Tyvar x) = (Tyvar z)
  /\ TYPE_SUBST (renn r c) (Tyvar y) = (Tyvar z)
  ==> x = y
Proof
  rpt strip_tac
  >> imp_res_tac renn_bij
  >> fs[]
QED

Theorem renn_Tyvars_TYPE_SUBST:
  !r c x. ?a. TYPE_SUBST (renn r c) (Tyvar x) = Tyvar a
Proof
  rw[]
  >> Cases_on `MEM (Tyvar x) (MAP SND (renn r c))`
  >- (
    imp_res_tac TYPE_SUBST_MEM_MAP_SND
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] renn_Tyvars)
    >> fs[]
  )
  >> imp_res_tac TYPE_SUBST_drop_all
  >> fs[]
QED

Theorem renn_bij3:
  !r c x y.
  TYPE_SUBST (renn r c) (Tyvar x)
  = TYPE_SUBST (renn r c) (Tyvar y)
  ==> x = y
Proof
  rpt strip_tac
  >> match_mp_tac renn_bij2
  >> qspecl_then [`r`,`c`,`x`] strip_assume_tac renn_Tyvars_TYPE_SUBST
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem renn_TYPE_SUBST_inverse:
  !r c x. TYPE_SUBST (renn r c) (TYPE_SUBST (renn r c) (Tyvar x)) = Tyvar x
Proof
  rpt gen_tac
  >> match_mp_tac var_renaming_SWAP_inverse'
  >> fs[renn_var_renaming,renn_set_MAP_SWAP]
QED

Theorem renn_LR_TYPE_SUBST_inverse:
  !r c x. is_const_or_type x ==> LR_TYPE_SUBST (renn r c) (LR_TYPE_SUBST (renn r c) x) = x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,TYPE_SUBST_compose]
  >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL]))
  >> rw[TYPE_SUBST_tyvars]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> fs[GSYM TYPE_SUBST_compose,renn_TYPE_SUBST_inverse]
QED

Theorem ren_Tyvars_TYPE_SUBST:
  !r c x. ?a. TYPE_SUBST (ren r c) (Tyvar x) = Tyvar a
Proof
  rw[]
  >> Cases_on `MEM (Tyvar x) (MAP SND (ren r c))`
  >- (
    imp_res_tac TYPE_SUBST_MEM_MAP_SND
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] ren_Tyvars)
    >> fs[]
    >> rveq
  )
  >> dxrule TYPE_SUBST_drop_all
  >> fs[]
QED

Theorem MEM_FV_LR_TYPE_SUBST_ren_imp:
  !x t.
  MEM x (FV (LR_TYPE_SUBST (ren r c) t)) /\ is_const_or_type t
  ==> ?y. MEM y (FV t) /\ TYPE_SUBST (ren r c) (Tyvar y) = Tyvar x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,FV_def,sum_case_def,tyvars_def,tvars_def,tyvars_TYPE_SUBST]
  >> qspecl_then [`r`,`c`,`x'`] assume_tac ren_Tyvars_TYPE_SUBST
  >> fs[tyvars_def]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[tyvars_def]
QED

Theorem MEM_FV_LR_TYPE_SUBST_renn_imp:
  !x t r c. MEM x (FV (LR_TYPE_SUBST (renn r c) t)) /\ is_const_or_type t
  ==> ?y. MEM y (FV t) /\ TYPE_SUBST (renn r c) (Tyvar y) = Tyvar x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,FV_def,sum_case_def,tyvars_def,tvars_def,tyvars_TYPE_SUBST]
  >> qspecl_then [`r`,`c`,`x'`] assume_tac renn_Tyvars_TYPE_SUBST
  >> fs[tyvars_def]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[tyvars_def]
QED

Theorem renn_MEM_SND:
  !r c x. MEM x (LIST_UNION r c) ==>
  MEM x (list_inter r c) = MEM (Tyvar x) (MAP SND (renn r c))
Proof
  fs[renn_def,ren_MEM_SND,MAP_MAP_o,FST_SND_SWAP]
  >> rw[EQ_IMP_THM]
  >> qspecl_then [`r`,`c`,`Tyvar x`] assume_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] ren_disj_img_r)
  >> qspecl_then [`r`,`c`,`Tyvar x`] assume_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] ren_disj_img_c)
  >> rfs[MEM_Tyvar_MAP_Tyvar]
QED

Theorem renn_MEM_SND_compl_union =
      GEN_ALL (Q.SPECL [`list_complement (r:mlstring list) (s:mlstring list)`,`LIST_UNION (s:mlstring list) c`] renn_MEM_SND)

Theorem renn_ID:
  !r c x. MEM x (list_complement r c) \/ MEM x (list_complement c r)
  ==> TYPE_SUBST (renn r c) (Tyvar x) = Tyvar x
Proof
  rw[MEM_FILTER,list_complement_def]
  >> `~MEM (Tyvar x) (MAP SND (renn r c))` by (
    fs[GSYM renn_MEM_SND,list_inter_def,MEM_FILTER]
  )
  >> imp_res_tac TYPE_SUBST_drop_all
  >> fs[]
QED

Theorem renn_ID_LR_TYPE_SUBST:
  !r s c t. is_const_or_type t
  /\ list_subset (FV t) s
  ==> LR_TYPE_SUBST (renn (list_complement r s) (LIST_UNION s c)) t = t
Proof
  rw[is_const_or_type_eq,FV_def]
  >> fs[sum_case_def,tyvars_def,tvars_def,LR_TYPE_SUBST_cases,list_subset_def,EVERY_MEM]
  >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL]))
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
  >> ONCE_REWRITE_TAC[EQ_SYM_EQ]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> match_mp_tac renn_ID
  >> fs[MEM_FILTER,list_inter_def,MEM_LIST_UNION,list_complement_def]
QED

Theorem renn_disj_dom_s:
  !r s c. NULL (list_inter (MAP SND (renn (list_complement r s) (LIST_UNION s c))) (MAP Tyvar s))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> pop_assum (assume_tac o REWRITE_RULE[MEM_MAP])
  >> fs[]
  >> rveq
  >> qspecl_then [`list_complement r s`,`LIST_UNION s c`,`y'`] mp_tac renn_MEM_SND
  >> fs[MEM_LIST_UNION,list_inter_def,MEM_FILTER,list_complement_def]
QED

Theorem renn_disj_dom_img2:
  !r s c. NULL (list_inter (MAP ((TYPE_SUBST (renn (list_complement r s) (LIST_UNION s c))) o $Tyvar) (list_complement r s)) (MAP Tyvar s))
Proof
  rw[NULL_FILTER,list_inter_def,GSYM MAP_MAP_o]
  >> rw[MEM_MAP]
  >> drule $ REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s
  >> disch_then $ qspecl_then [`r`,`c`] assume_tac
  >> fs[]
  >> imp_res_tac $ ONCE_REWRITE_RULE[MONO_NOT_EQ] $ Ho_Rewrite.REWRITE_RULE[FORALL_AND_THM,EQ_IMP_THM] renn_MAP_FST_SND
  >> spose_not_then assume_tac
  >> qmatch_asmsub_abbrev_tac `REV_ASSOCD _ sigma _`
  >> Cases_on `MEM (Tyvar y'') (MAP SND sigma)`
  >- (
    drule_then strip_assume_tac TYPE_SUBST_MEM_MAP_SND
    >> imp_res_tac $ Q.ISPEC `FST` MEM_MAP_f
    >> unabbrev_all_tac
    >> imp_res_tac renn_MAP_FST_SND
    >> imp_res_tac $ REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s
    >> gs[]
  )
  >> imp_res_tac TYPE_SUBST_drop_all
  >> gvs[MEM_Tyvar_MAP_Tyvar,list_complement_def,MEM_FILTER]
QED

Theorem renn_disj_dom_img3:
  !r c. NULL (list_inter (MAP ((TYPE_SUBST (renn r c)) o $Tyvar) (list_inter r c)) (MAP Tyvar c))
Proof
  rw[NULL_FILTER,list_inter_def,GSYM MAP_MAP_o,MEM_MAP]
  >> spose_not_then assume_tac
  >> fs[MEM_FILTER,renn_def]
  >> qspecl_then [`r`,`c`,`y''`] assume_tac ren_MEM_SND
  >> gvs[MEM_LIST_UNION,list_inter_def,MEM_FILTER,REWRITE_RULE[TYPE_SUBST_def] TYPE_SUBST_drop_suffix]
  >> fs[GSYM MEM_Tyvar_MAP_Tyvar]
  >> imp_res_tac $ REWRITE_RULE[NULL_FILTER,list_inter_def] ren_disj_dom_img2
  >> gs[MEM_Tyvar_MAP_Tyvar,MEM_MAP]
QED

Theorem renn_disj_dom_img4:
  !r c. NULL (list_inter (MAP ((TYPE_SUBST (renn r c)) o $Tyvar) r) (MAP Tyvar c))
Proof
  ONCE_REWRITE_TAC[NULL_list_inter_COMM]
  >> rw[NULL_FILTER,list_inter_def]
  >> pop_assum (assume_tac o REWRITE_RULE[MEM_MAP])
  >> mp_tac ((REWRITE_RULE[NULL_FILTER,list_inter_def] o ONCE_REWRITE_RULE[NULL_list_inter_COMM]) renn_disj_dom_img3)
  >> fs[Once EQ_SYM_EQ]
  >> Cases_on `MEM y' c`
  >- (
    disch_then match_mp_tac
    >> rw[MEM_MAP,MEM_FILTER]
    >> qexists_tac `r`
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> disch_then kall_tac
  >> qspecl_then [`r`,`c`,`y'`] assume_tac renn_MEM_SND
  >> rfs[MEM_FILTER,list_inter_def]
  >> imp_res_tac TYPE_SUBST_drop_all
  >> rfs[MEM_Tyvar_MAP_Tyvar]
QED

Theorem renn_compl_union_TYPE_SUBST_s:
  !r s c y x. let sigma = renn (list_complement r s) (LIST_UNION s c) in
  MEM y r /\ TYPE_SUBST sigma (Tyvar y) = Tyvar x
  /\ ~MEM x s
  ==> ~MEM (Tyvar x) (MAP ((TYPE_SUBST sigma) o Tyvar) s)
Proof
  rw[MEM_MAP]
  >> Cases_on `MEM y s`
  >- (
    qspecl_then [`s`,`r`,`c`,`y`] mp_tac renn_MEM_SND_compl_union
    >> rw[MEM_FILTER,MEM_LIST_UNION,list_inter_def,list_complement_def]
    >> fs[GSYM list_complement_def]
    >> imp_res_tac TYPE_SUBST_drop_all
    >> gvs[]
  )
  >> gvs[Excl"TYPE_SUBST_def",GSYM TYPE_SUBST_def]
  >> imp_res_tac renn_bij3
  >> gvs[]
QED

