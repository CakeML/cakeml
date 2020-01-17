(*
 Implementation of cyclicity check for function definitions
 *)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
     holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSyntaxRenamingTheory

val _ = new_theory"holSyntaxCyclicity"

val _ = Parse.temp_overload_on("is_instance",``λty0 ty. ∃i. ty = TYPE_SUBST i ty0``)
val _ = Parse.add_infix("#", 401, Parse.NONASSOC)
val _ = Parse.temp_overload_on("#", ``$orth_ty``)
val _ = Parse.temp_overload_on("#", ``$orth_ci``)

(* contraposition of an equivalence *)
fun ccontr_equiv(x) =
  let val (a,b) = EQ_IMP_RULE (SPEC_ALL x)
  in GEN_ALL (IMP_ANTISYM_RULE (CONTRAPOS b) (CONTRAPOS a)) end;

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
    >> imp_res_tac (INST_TYPE [alpha |-> ``:type#type``,beta|-> ``:type``] (GSYM EL_MAP))
    >> ASM_REWRITE_TAC[]
    >> REWRITE_TAC[el_append3]
    >> qpat_x_assum `!x. _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
    >> FULL_CASE_TAC >> fs[]
    >> CASE_TAC
    >- (
      qpat_x_assum `_ = NONE` mp_tac
      >> fs[ALOOKUP_FAILS,MEM_MAP,SWAP_def]
      >> ONCE_REWRITE_TAC[CONJ_COMM]
      >> asm_exists_tac
      >> unabbrev_all_tac
      >> ASM_REWRITE_TAC[]
      >> qpat_x_assum `!x. _` kall_tac
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

Theorem FST_SND_SWAP:
  FST o SWAP = SND
  /\ SND o SWAP = FST
Proof
  rw[FUN_EQ_THM,SWAP_def]
QED

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

Theorem clean_tysubst_MEM:
  !pfx q q' x sfx. ~MEM (Tyvar x) (MAP SND pfx) /\ Tyvar x <> q
  /\ MEM (q,Tyvar x) (clean_tysubst (pfx ++ [(q',Tyvar x)] ++ sfx))
  ==> q=q'
Proof
  Induct
  >> rw[clean_tysubst_def,MEM_FILTER]
  >> Cases_on `h`
  >> Cases_on `r`
  >> fs[clean_tysubst_def,MEM_FILTER]
  >> TRY (FULL_CASE_TAC)
  >> fs[MEM_FILTER]
  >> last_x_assum match_mp_tac
  >> asm_exists_tac
  >> fs[]
  >> asm_exists_tac
  >> fs[]
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

Theorem renaming_clean_tysubst_imp:
  !r. renaming r ==> renaming (clean_tysubst r)
Proof
  Cases
  >- fs[renaming_def,clean_tysubst_def]
  >> rename1 `h::_`
  >> Cases_on `h`
  >> rename1 `(_,r)::t`
  >> Cases_on `r`
  >> rw[renaming_def,clean_tysubst_def,ALOOKUP_MEM_eq]
  >> TRY (FULL_CASE_TAC >> fs[])
  (* (Tyvar m, Tyvar m) is head *)
  >- (
    qmatch_asmsub_abbrev_tac `FILTER f`
    >> `MEM (Tyvar x) (MAP SND (FILTER f (clean_tysubst t)))` by fs[]
    >> pop_assum (assume_tac o REWRITE_RULE[MAP_SND_FILTER_NEQ,MEM_FILTER,MEM_MAP,BETA_THM])
    >> fs[ELIM_UNCURRY]
    >> qmatch_assum_rename_tac `MEM y (clean_tysubst _)`
    >> Cases_on `y`
    >> imp_res_tac (REWRITE_RULE[list_subset_set,SUBSET_DEF] list_subset_clean_tysubst)
    >> dxrule (Q.ISPEC `SND` MEM_MAP_f)
    >> qunabbrev_tac `f`
    >> rw[]
    >> rveq
    >> dxrule MEM_SPLIT_APPEND_SND_first
    >> rw[]
    >> first_x_assum (qspecl_then [`x`,`Tyvar m::MAP SND pfx'`,`MAP SND sfx'`] assume_tac)
    >> rfs[SWAP_def]
    >> rveq
    >> fs[]
    >> rfs[]
    >> Q.ISPECL_THEN
      [`(Tyvar m,Tyvar m)::MAP SWAP pfx'`,`MAP SWAP sfx'`,`pfx''`,`sfx''`,`(Tyvar x,q')`,`(Tyvar x,Tyvar a)`]
      assume_tac (GSYM MEM_APPEND_FST_lemma)
    >> rfs[FST_SND_SWAP,MAP_MAP_o,SWAP_def]
    >> fs[]
    >> qmatch_asmsub_abbrev_tac `MAP SND (FILTER f (clean_tysubst s))`
    >> Q.ISPECL_THEN [`f`,`clean_tysubst s`] mp_tac MEM_FILTER
    >> qunabbrev_tac `f`
    >> disch_then imp_res_tac
    >> pop_assum (assume_tac o REWRITE_RULE[MEM_SPLIT,ELIM_UNCURRY])
    >> rfs[]
    >> qpat_x_assum `_ = _ ++ _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
    >> qexists_tac `a`
    >> qexists_tac `MAP SWAP l1`
    >> qexists_tac `MAP SWAP l2`
    >> fs[SWAP_SWAP_INVOL,FST_SND_SWAP,MAP_MAP_o,PAIR,SWAP_def]
    >> qmatch_asmsub_abbrev_tac `MAP SND (FILTER f (clean_tysubst s))`
    >> qspec_then `s` assume_tac (CONJUNCT1 clean_tysubst_prop)
    >> dxrule FILTER_ALL_DISTINCT
    >> disch_then (qspec_then `λx. x <> (Tyvar m)` mp_tac)
    >> rw[FILTER_MAP,o_DEF,ALL_DISTINCT_APPEND]
    >- (
      match_mp_tac clean_tysubst_MEM
      >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT2 clean_tysubst_prop))
      >> fs[ELIM_UNCURRY,markerTheory.Abbrev_def]
      >> asm_exists_tac >> fs[]
      >> asm_exists_tac >> fs[]
    )
    >> qspec_then `s` assume_tac (CONJUNCT1 clean_tysubst_prop)
    >> dxrule FILTER_ALL_DISTINCT
    >> disch_then (qspec_then `λx. x <> (Tyvar m)` mp_tac)
    >> fs[markerTheory.Abbrev_def]
    >> rveq
    >> qpat_x_assum `MAP SND (FILTER _ _) = _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
    >> rw[FILTER_MAP,o_DEF,ELIM_UNCURRY,ALL_DISTINCT_APPEND]
  )
  >- (
    qmatch_asmsub_abbrev_tac `FILTER f`
    >> `MEM (Tyvar x) (Tyvar m::MAP SND (FILTER f (clean_tysubst t)))` by (ASM_REWRITE_TAC[] >> fs[])
    >> Cases_on `m = x` >> fs[]
    >- (
      first_x_assum (qspecl_then [`x`,`[]`,`MAP SND t`] mp_tac)
      >> Q.ISPECL_THEN [`[(Tyvar m,q)]`] mp_tac APPEND_EQ_APPEND_IS_PREFIX
      >> rw[SWAP_def]
      >> qpat_x_assum `!x. _` imp_res_tac
      >> TRY (FULL_CASE_TAC) >> fs[]
      >- (
        qpat_x_assum `(_,_) = _` (assume_tac o GSYM)
        >> rveq
        >> qexists_tac `a`
        >> qexists_tac `[]`
        >> Cases_on `t`
        >> rfs[]
        >> rveq
        >> fs[]
        >> Cases_on `pfx'`
        >> fs[]
      )
      >> fs[IS_PREFIX_APPEND]
      >> qexists_tac `a`
      >> qexists_tac `[]`
      >> Cases_on `pfx'`
      >> fs[]
    )
    >> `MEM (Tyvar x) (MAP SND t)` by  (
        fs[MEM_MAP,MEM_FILTER]
        >> imp_res_tac (REWRITE_RULE[list_subset_set,SUBSET_DEF] list_subset_clean_tysubst)
        >> fs[AC CONJ_ASSOC CONJ_COMM]
        >> asm_exists_tac
        >> fs[]
      )
    >> qpat_x_assum `MEM _ (MAP SND (FILTER _ _))` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
    >> dxrule MEM_SPLIT_APPEND_SND_first
    >> rw[]
    >> first_x_assum (qspecl_then [`x`,`Tyvar m::MAP SND pfx'`,`MAP SND sfx'`] assume_tac)
    >> rfs[SWAP_def]
    >> Q.ISPECL_THEN [`(Tyvar m,q)::MAP SWAP pfx'`,`MAP SWAP sfx'`,`pfx''`,`sfx''`,`(Tyvar x,q')`,`(Tyvar x,Tyvar a)`] assume_tac (GSYM MEM_APPEND_FST_lemma)
    >> rfs[MAP_MAP_o,FST_SND_SWAP]
    >> rveq
    >> fs[]
    >> unabbrev_all_tac
    >> pop_assum (assume_tac o REWRITE_RULE[MEM_MAP,MEM_FILTER,ELIM_UNCURRY])
    >> fs[]
    >> Cases_on `y`
    >> rveq
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT2 clean_tysubst_prop))
    >> fs[ELIM_UNCURRY]
    >> rveq
    >> fs[]
    >> rveq
    >> qmatch_asmsub_abbrev_tac `clean_tysubst s`
    >> qpat_x_assum `MEM _ (clean_tysubst s)` (assume_tac o REWRITE_RULE[MEM_SPLIT])
    >> qspec_then `s` assume_tac (CONJUNCT1 clean_tysubst_prop)
    >> fs[]
    >> rfs[ALL_DISTINCT_APPEND]
    >> qmatch_asmsub_abbrev_tac `FILTER f`
    >> qexists_tac `a`
    >> qexists_tac `(Tyvar m,q)::MAP SWAP (FILTER f l1)`
    >> Q.ISPECL_THEN [`Tyvar a'`,`λx. x <> Tyvar m`,`MAP SND l1`] assume_tac (ccontr_equiv(MEM_FILTER))
    >> qunabbrev_tac `f`
    >> rfs[FILTER_APPEND,SWAP_def,MAP_MAP_o,FST_SND_SWAP,FILTER_MAP,o_DEF,LAMBDA_PROD,markerTheory.Abbrev_def]
    >> match_mp_tac clean_tysubst_MEM
    >> qexists_tac `pfx'`
    >> qexists_tac `a'`
    >> qexists_tac `sfx'`
    >> ASM_REWRITE_TAC[]
    >> fs[]
  )
  (* third top level subgoal *)
  >- (
    `MEM (Tyvar x) (MAP SND (clean_tysubst t))` by fs[]
    >> pop_assum (assume_tac o REWRITE_RULE[MEM_MAP])
    >> fs[]
    >> imp_res_tac (REWRITE_RULE[SUBSET_DEF,list_subset_set] list_subset_clean_tysubst)
    >> rename1 `SND y`
    >> Cases_on `y`
    >> fs[]
    >> rveq
    >> qpat_x_assum `MEM _ (clean_tysubst _)` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
    >> dxrule (Q.ISPEC `SND` MEM_MAP_f)
    >> rw[]
    >> dxrule MEM_SPLIT_APPEND_SND_first
    >> rw[]
    >> first_x_assum (qspecl_then [`x`,`Tyapp m l::MAP SND pfx'`,`MAP SND sfx'`] assume_tac)
    >> rfs[SWAP_def]
    >> Q.ISPECL_THEN [`(Tyapp m l,q)::MAP SWAP pfx'`,`MAP SWAP sfx'`,`pfx''`,`sfx''`,`(Tyvar x,q'')`,`(Tyvar x,Tyvar a)`] assume_tac (GSYM MEM_APPEND_FST_lemma)
    >> rfs[MAP_MAP_o,FST_SND_SWAP]
    >> rveq >> fs[MAP_MAP_o,FST_SND_SWAP,markerTheory.Abbrev_def]
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] (CONJUNCT2 clean_tysubst_prop))
    >> qmatch_asmsub_abbrev_tac `clean_tysubst s`
    >> qspec_then `s` assume_tac (CONJUNCT1 clean_tysubst_prop)
    >> unabbrev_all_tac
    >> fs[ELIM_UNCURRY]
    >> imp_res_tac clean_tysubst_MEM
    >> fs[ELIM_UNCURRY]
    >> qpat_x_assum `MEM (_,_) _` (assume_tac o REWRITE_RULE[MEM_SPLIT])
    >> qpat_x_assum `MAP SND (clean_tysubst _) = _` kall_tac
    >> rfs[ALL_DISTINCT_APPEND]
    >> qexists_tac `a`
    >> qexists_tac `MAP SWAP l1`
    >> fs[SWAP_def,MAP_MAP_o,FST_SND_SWAP,ALL_DISTINCT_APPEND]
  )
QED

Definition wf_pqs_def:
  wf_pqs = EVERY (UNCURRY $/\ o (is_const_or_type ## is_const_or_type))
End

(* Definition 5.3, Kunčar 2015
 * Solution to a sequence *)
Definition sol_seq_def:
  sol_seq rs pqs =
    (wf_pqs pqs
    /\ (LENGTH rs = LENGTH pqs
    /\ !i. SUC i < LENGTH rs ==>
    LR_TYPE_SUBST (EL i rs) (SND (EL i pqs))
    = LR_TYPE_SUBST (EL (SUC i) rs) (FST (EL (SUC i) pqs))))
End

Theorem LR_TYPE_SUBST_NIL:
  !x. is_const_or_type x ==> LR_TYPE_SUBST [] x = x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,TYPE_SUBST_NIL]
QED

(* most general solution to a sequence *)
Definition mg_sol_seq_def:
  mg_sol_seq rs pqs =
    (sol_seq rs pqs
    /\ !rs'. sol_seq rs' pqs ==>
    ?es. LENGTH es = LENGTH rs /\
    !i. i < LENGTH rs ==>
    LR_TYPE_SUBST (EL i es) (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))
    = LR_TYPE_SUBST (EL i rs') (FST (EL i pqs)))
End

Theorem FV_LR_TYPE_SUBST_mono:
  !x y s. is_const_or_type x /\ is_const_or_type y /\ set (FV x) ⊆ set (FV y)
  ==> set (FV (LR_TYPE_SUBST s x)) ⊆ set (FV (LR_TYPE_SUBST s y))
Proof
  rw[is_const_or_type_eq,FV_def,LR_TYPE_SUBST_cases]
  >> fs[LR_TYPE_SUBST_cases,tvars_def,tyvars_TYPE_SUBST_mono]
QED

(* Lemma 5.2, Kunčar 2015 *)
Theorem monotone_dep_seq_free_vars_SND_FST_same[local]:
  !pqs rs ctxt.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  ==>
    let fvset = λx y. set(FV (LR_TYPE_SUBST x y))
    in !i. i < LENGTH pqs ==>
      fvset (EL i rs) (SND (EL i pqs)) ⊆ fvset (EL i rs) (FST (EL i pqs))
Proof
  rw[monotone_def,PAIR_MAP,ELIM_UNCURRY,o_DEF]
  >> qmatch_abbrev_tac `set (FV (LR_TYPE_SUBST _ (_ (EL ipq pqs)))) SUBSET _`
  >> `MEM (EL ipq pqs) pqs` by (
    fs[MEM_EL] >> qexists_tac `ipq` >> fs[]
  )
  >> fs[EVERY_MEM]
  >> rpt (qpat_x_assum `!x. MEM _ pqs ==> _` drule)
  >> rw[]
  >> qpat_x_assum `!x y. dependency _ _ _ ==> _` dxrule
  >> rw[list_subset_set]
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
QED

Theorem LR_TYPE_SUBST_type_preserving:
  !t s. is_const_or_type t ==> is_const_or_type (LR_TYPE_SUBST s t)
Proof
  rw[is_const_or_type_eq] >> fs[LR_TYPE_SUBST_cases]
QED

Theorem sol_seq_is_const_or_type:
  !rs pqs i. sol_seq rs pqs /\ i < LENGTH pqs
  ==> is_const_or_type (FST (EL i pqs))
  /\ is_const_or_type (SND (EL i pqs))
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >> imp_res_tac EL_MEM
  >> res_tac
  >> fs[ELIM_UNCURRY]
QED

Theorem mg_sol_seq_is_const_or_type:
  !rs pqs i. mg_sol_seq rs pqs /\ i < LENGTH pqs
  ==> is_const_or_type (FST (EL i pqs))
  /\ is_const_or_type (SND (EL i pqs))
Proof
  fs[mg_sol_seq_def]
  >> rpt gen_tac
  >> rpt disch_tac
  >> match_mp_tac sol_seq_is_const_or_type
  >> fs[]
  >> asm_exists_tac
  >> fs[]
QED

(* Lemma 5.2, Kunčar 2015 *)
Theorem monotone_dep_seq_free_vars_FST_SND:
  !pqs rs ctxt.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  ==>
    let fvset = λx y. set(FV (LR_TYPE_SUBST x y))
    in !i j. i < j /\ j < LENGTH pqs ==>
    fvset (EL j rs) (FST (EL j pqs)) ⊆ fvset (EL i rs) (SND (EL i pqs))
Proof
  rw[]
  >> Induct_on `j`
  >> rw[]
  >> fs[RIGHT_CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) (SPEC_ALL sol_seq_def),EVERY_MEM,monotone_def]
  >> `MEM (EL j pqs) pqs` by (
    fs[MEM_EL] >> qexists_tac `j` >> fs[]
  )
  >> qpat_x_assum `!x. MEM _ pqs ==> _` drule
  >> rw[ELIM_UNCURRY]
  >> qpat_x_assum `!x y. dependency _ _ _ ==> _` dxrule
  >> rw[list_subset_set]
  >> qspecl_then [`SND (EL j pqs)`,`FST (EL j pqs)`] assume_tac FV_LR_TYPE_SUBST_mono
  >> fs[wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
  >> qpat_x_assum `!e. MEM e _ ==> _` imp_res_tac
  >> fs[]
  >> Cases_on `i < j` >> fs[]
  >- (
    match_mp_tac SUBSET_TRANS
    >> ONCE_REWRITE_TAC[CONJ_COMM]
    >> asm_exists_tac
    >> fs[]
  )
  >> Cases_on `i = j`
  >> fs[LESS_SUC_NOT]
QED

Theorem FV_LR_TYPE_SUBST_mono_FST_SND:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i < j /\ j < LENGTH pqs ==>
  set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (FST (EL j pqs)))))
  ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))))
Proof
  rw[]
  >> drule monotone_dep_seq_free_vars_FST_SND
  >> fs[]
  >> disch_then (drule_then drule)
  >> disch_then (qspecl_then [`i`,`j`] assume_tac)
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rw[]
  >> match_mp_tac LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> first_assum drule
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
QED


(* Lemma 5.2, Kunčar 2015 *)
Theorem monotone_dep_seq_free_vars_FST_FST:
  !pqs rs ctxt.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  ==>
    let fvset = λx y. set(FV (LR_TYPE_SUBST x y))
    in !i j. i <= j /\ j < LENGTH pqs ==>
    fvset (EL j rs) (FST (EL j pqs)) ⊆ fvset (EL i rs) (FST (EL i pqs))
Proof
  rw[LESS_OR_EQ]
  >> fs[SUBSET_REFL]
  >> imp_res_tac monotone_dep_seq_free_vars_FST_SND
  >> fs[]
  >> pop_assum imp_res_tac
  >> match_mp_tac SUBSET_TRANS
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> imp_res_tac monotone_dep_seq_free_vars_SND_FST_same
  >> fs[]
QED

Theorem FV_LR_TYPE_SUBST_mono_FST_FST:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs ==>
  set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (FST (EL j pqs)))))
  ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))))
Proof
  rw[]
  >> drule monotone_dep_seq_free_vars_FST_FST
  >> fs[]
  >> rpt (disch_then drule)
  >> strip_tac
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rw[]
  >> match_mp_tac LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> first_assum drule
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
QED

(* Lemma 5.2, Kunčar 2015 *)
Theorem monotone_dep_seq_free_vars_SND_SND:
  !pqs rs ctxt.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  ==>
    let fvset = λx y. set(FV (LR_TYPE_SUBST x y))
    in !i j. i <= j /\ j < LENGTH pqs ==>
    fvset (EL j rs) (SND (EL j pqs)) ⊆ fvset (EL i rs) (SND (EL i pqs))
Proof
  rw[LESS_OR_EQ]
  >> fs[SUBSET_REFL]
  >> imp_res_tac monotone_dep_seq_free_vars_SND_FST_same
  >> fs[]
  >> first_x_assum drule
  >> imp_res_tac monotone_dep_seq_free_vars_FST_SND
  >> strip_tac
  >> match_mp_tac SUBSET_TRANS
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem FV_LR_TYPE_SUBST_mono_SND_SND:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs ==>
  set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (SND (EL j pqs)))))
  ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))))
Proof
  rw[]
  >> drule monotone_dep_seq_free_vars_SND_SND
  >> fs[]
  >> rpt (disch_then drule)
  >> strip_tac
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rw[]
  >> match_mp_tac LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> first_assum drule
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
QED

Theorem monotone_dep_seq_free_vars_SND_FST:
  !pqs rs ctxt.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  ==>
    let fvset = λx y. set(FV (LR_TYPE_SUBST x y))
    in !i j. i <= j /\ j < LENGTH pqs ==>
      fvset (EL j rs) (SND (EL j pqs)) ⊆ fvset (EL i rs) (FST (EL i pqs))
Proof
  rw[]
  >> drule monotone_dep_seq_free_vars_SND_SND
  >> rpt (disch_then drule)
  >> drule monotone_dep_seq_free_vars_SND_FST_same
  >> rpt (disch_then drule)
  >> fs[]
  >> disch_then (qspec_then `i` assume_tac)
  >> disch_then (qspecl_then [`i`,`j`] assume_tac)
  >> match_mp_tac SUBSET_TRANS
  >> rfs[]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem FV_LR_TYPE_SUBST_mono_SND_FST:
  !pqs rs ctxt i j s.
  monotone (dependency ctxt)
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ sol_seq rs pqs
  /\ i <= j /\ j < LENGTH pqs ==>
  set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST  (EL j rs) (SND (EL j pqs)))))
  ⊆ set (FV (LR_TYPE_SUBST s (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))))
Proof
  rw[]
  >> drule monotone_dep_seq_free_vars_SND_FST
  >> fs[]
  >> rpt (disch_then drule)
  >> strip_tac
  >> match_mp_tac FV_LR_TYPE_SUBST_mono
  >> rw[]
  >> match_mp_tac LR_TYPE_SUBST_type_preserving
  >> drule_then assume_tac sol_seq_is_const_or_type
  >> fs[]
QED

Theorem mgu_TYPE_SUBST':
  !e e' t t'.
    TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
    ==> !x. MEM x (tyvars t) /\ MEM (Tyvar x) (MAP SND e)
    ==> ?a pfx. pfx ++ [(Tyvar a, Tyvar x)] ≼ e /\ ~MEM (Tyvar x) (MAP SND pfx)
Proof
  rw[subtype_at_eq]
  >> imp_res_tac (GSYM subtype_at_tyvars)
  >> qpat_x_assum `!x. _ = subtype_at t' _` (qspec_then `p` (assume_tac o GSYM))
  >> qpat_x_assum `!x. _ = _` (qspec_then `p` assume_tac)
  >> imp_res_tac subtype_at_TYPE_SUBST
  >> first_x_assum (fn x => fs[x])
  >> qpat_x_assum `subtype_at t _ = SOME _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def])
  >> drule subtype_at_TYPE_SUBST
  >> disch_then (fn x => fs[x,markerTheory.Abbrev_def])
  >> rpt(qpat_x_assum `subtype_at _ _ = _` kall_tac)
  >> dxrule MEM_SPLIT_APPEND_SND_first
  >> rw[]
  >> drule TYPE_SUBST_drop_prefix
  >> disch_then (qspec_then `[(q,Tyvar x)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def]
  >> qmatch_assum_rename_tac `TYPE_SUBST _ q = Tyvar _`
  >> Cases_on `q`
  >> fs[TYPE_SUBST_def,IS_PREFIX_APPEND]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem mgu_TYPE_SUBST:
  !e e' t t'.
    TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
    ==> renaming (FILTER (λx. MEM (SND x) (MAP Tyvar (tyvars t))) e)
Proof
  rpt strip_tac
  >> qspecl_then [`e`,`e'`,`t`,`t'`] assume_tac mgu_TYPE_SUBST'
  >> rfs[]
  >> rpt(qpat_x_assum `TYPE_SUBST _ _ = _` kall_tac)
  >> rw[REWRITE_RULE[ALOOKUP_MEM_eq,MAP_SWAP,MAP_APPEND] renaming_eq]
  >> pop_assum (mp_tac o REWRITE_RULE[MEM_MAP,FILTER_MAP,MEM_FILTER])
  >> rw[] >> Cases_on `y` >> fs[] >> rveq
  >> dxrule (Q.ISPEC `SND` MEM_MAP_f)
  >> last_x_assum drule
  >> rw[SWAP_def,IS_PREFIX_APPEND]
  >> fs[FILTER_APPEND]
  >> qmatch_goalsub_abbrev_tac `FILTER f`
  >> qexists_tac `a`
  >> qexists_tac `MAP SWAP (FILTER f pfx)`
  >> qexists_tac `MAP SWAP (FILTER f l)`
  >> CONJ_TAC
  >- (
    fs[MAP_MAP_o,SWAP_SWAP_INVOL,FST_SND_SWAP,MEM_FILTER]
    >> REWRITE_TAC[MEM_MAP]
    >> rw[]
  )
  >> fs[FST_SND_SWAP,MAP_MAP_o]
  >> qpat_x_assum `MEM _ (MAP SND _)` kall_tac
  >> unabbrev_all_tac
  >> fs[MAP_MAP_o,FST_SND_SWAP,MEM_MAP,MEM_FILTER]
  >> rw[]
  >> first_x_assum (qspec_then `y` assume_tac)
  >> fs[]
QED

Theorem mgu_TYPE_SUBST_pre:
  !e e' t t'.
    EVERY (λx. MEM (SND x) (MAP Tyvar (tyvars t))) e
    /\ TYPE_SUBST e t = t' /\ TYPE_SUBST e' t' = t
    ==> renaming e
Proof
  rpt strip_tac
  >> imp_res_tac mgu_TYPE_SUBST
  >> rfs[GSYM FILTER_EQ_ID]
QED

(* Lemma 5.4, Kunčar 2015 *)
Theorem mg_solution1:
  !rs rs' pqs.
    mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
    ==>
    !i. i < LENGTH rs ==>
    !x. MEM x (FV (FST (EL i pqs)))
    ==>
    ?e. renaming e /\
    TYPE_SUBST e (TYPE_SUBST (EL i rs') (Tyvar x))
    = TYPE_SUBST (EL i rs) (Tyvar x)
Proof
  rw[]
  >> `is_const_or_type (FST (EL i pqs))` by (
    fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
    >> `i < LENGTH pqs` by fs[]
    >> dxrule EL_MEM
    >> disch_tac
    >> qpat_x_assum `!x. MEM _ _ ==> _` imp_res_tac
  )
  >> rfs[is_const_or_type_eq]
  >> fs[tvars_def,mg_sol_seq_def]
  >> qpat_x_assum `!x. sol_seq _ _ ==> ?e. LENGTH _ = LENGTH rs' /\ _` (qspec_then `rs` assume_tac)
  >> qpat_x_assum `!x. sol_seq _ _ ==> ?e. LENGTH _ = LENGTH rs /\ _` (qspec_then `rs'` assume_tac)
  >> `LENGTH rs' = LENGTH rs` by fs[sol_seq_def]
  >> rfs[]
  >> NTAC 2 (first_x_assum (qspec_then `i` assume_tac))
  >> rfs[FV_def,tvars_def,LR_TYPE_SUBST_cases,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
  >> NTAC 2 (first_x_assum (qspec_then `x` mp_tac) >> disch_then imp_res_tac)
  >> qabbrev_tac `e' = (EL i es')`
  >> qabbrev_tac `r' = (EL i rs')`
  >> qabbrev_tac `e = (EL i es)`
  >> qabbrev_tac `r = (EL i rs)`
  >> qexists_tac `FILTER (λy. MEM (SND y) (MAP Tyvar (tyvars (TYPE_SUBST r' (Tyvar x))))) e'`
  >> rpt (
    qpat_x_assum `REV_ASSOCD _ _ _ = _ ` (assume_tac o REWRITE_RULE[GSYM TYPE_SUBST_compose] o ONCE_REWRITE_RULE[GSYM TYPE_SUBST_def])
  )
  >> CONJ_TAC
  (* renaming cases *)
  >> TRY (
    match_mp_tac mgu_TYPE_SUBST
    >> NTAC 2 (qpat_x_assum `TYPE_SUBST _ _ = TYPE_SUBST _ (TYPE_SUBST _ _)` (assume_tac o GSYM))
    >> NTAC 2 (goal_assum (first_assum o mp_then Any mp_tac))
  )
  >> REWRITE_TAC[GSYM TYPE_SUBST_def,GSYM TYPE_SUBST_compose]
  >> qpat_x_assum `TYPE_SUBST r' (Tyvar x) = TYPE_SUBST _ (TYPE_SUBST _ _) ` (assume_tac o GSYM)
  >> qspecl_then [`TYPE_SUBST r' (Tyvar x)`,`e'`] assume_tac TYPE_SUBST_FILTER_tyvars
  >> ASM_REWRITE_TAC[MEM_MAP,LAMBDA_PROD]
  >> qmatch_abbrev_tac `TYPE_SUBST (FILTER f1 _) _ = TYPE_SUBST (FILTER f2 _) _`
  >> `f1 = f2` by (
    unabbrev_all_tac
    >> rw[FUN_EQ_THM]
    >> pairarg_tac
    >> ASM_REWRITE_TAC[]
    >> rpt (pop_assum kall_tac)
    >> rw[EQ_IMP_THM]
  )
  >> rw[]
QED

(* TODO remove mg_solution1 and replace with mg_solution *)
(* Lemma 5.4, Kunčar 2015 *)
Theorem mg_solution:
  !rs rs' pqs.
    mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
    ==> !i. i < LENGTH rs ==>
    ?e. renaming e /\
    !x. MEM x (FV (FST (EL i pqs))) ==>
    TYPE_SUBST e (TYPE_SUBST (EL i rs') (Tyvar x))
    = TYPE_SUBST (EL i rs) (Tyvar x)
Proof
  rw[]
  >> `is_const_or_type (FST (EL i pqs))` by (
    fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY]
    >> `i < LENGTH pqs` by fs[]
    >> dxrule EL_MEM
    >> disch_tac
    >> qpat_x_assum `!x. MEM _ _ ==> _` imp_res_tac
  )
  >> rfs[is_const_or_type_eq]
  >> fs[FV_def,sum_case_def,tvars_def,mg_sol_seq_def]
  >> qpat_x_assum `!x. sol_seq _ _ ==> ?e. LENGTH _ = LENGTH rs' /\ _` (qspec_then `rs` mp_tac)
  >> qpat_x_assum `!x. sol_seq _ _ ==> ?e. LENGTH _ = LENGTH rs /\ _` (qspec_then `rs'` mp_tac)
  >> `LENGTH rs' = LENGTH rs` by fs[sol_seq_def]
  >> rw[]
  >> NTAC 2 (first_x_assum (qspec_then `i` assume_tac))
  >> rfs[FV_def,tvars_def,LR_TYPE_SUBST_cases]
  >> qabbrev_tac `e' = (EL i es')`
  >> qabbrev_tac `r' = (EL i rs')`
  >> qabbrev_tac `e = (EL i es)`
  >> qabbrev_tac `r = (EL i rs)`
  >> qexists_tac `FILTER (λy. MEM (SND y) (MAP Tyvar (tyvars (TYPE_SUBST r' ty)))) e'`
  >> CONJ_TAC
  (* renaming cases *)
  >> TRY (
    match_mp_tac mgu_TYPE_SUBST
    >> NTAC 2 (goal_assum (first_assum o mp_then Any mp_tac))
  )
  >> PURE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> REWRITE_TAC[TYPE_SUBST_compose]
  >> REWRITE_TAC[TYPE_SUBST_def]
  >> REWRITE_TAC[GSYM TYPE_SUBST_tyvars]
  >> PURE_REWRITE_TAC[GSYM TYPE_SUBST_def,GSYM TYPE_SUBST_compose]
  >> qpat_x_assum `_ = TYPE_SUBST r ty` (fn x => fs[GSYM x])
  >> rw[GSYM TYPE_SUBST_FILTER_tyvars2]
QED

Theorem LR_TYPE_SUBST_tyvars:
  !t s s'. is_const_or_type t ==>
  (LR_TYPE_SUBST s t = LR_TYPE_SUBST s' t)
  = !x. MEM x (FV t)
    ==> (TYPE_SUBST s (Tyvar x) = TYPE_SUBST s' (Tyvar x))
Proof
  rw[is_const_or_type_eq,EQ_IMP_THM,FV_def]
  >> fs[TYPE_SUBST_tyvars,LR_TYPE_SUBST_cases,sum_case_def,tvars_def]
QED

(* Lemma 5.4, Kunčar 2015 *)
Theorem mg_solutions:
  !rs rs' pqs. mg_sol_seq rs pqs /\ mg_sol_seq rs' pqs
  ==>
    ?es. LENGTH es = LENGTH pqs
    /\ EVERY renaming es
    /\ !i. i < LENGTH rs ==>
      LR_TYPE_SUBST (EL i es) (LR_TYPE_SUBST (EL i rs') (FST (EL i pqs)))
      = LR_TYPE_SUBST (EL i rs) (FST (EL i pqs))
Proof
  rw[]
  >> qspecl_then [`rs`,`rs'`,`pqs`] mp_tac mg_solution
  >> rw[]
  >> qabbrev_tac `P = λi e. renaming e
    /\ !x. MEM x (FV (FST (EL i pqs))) ==>
    TYPE_SUBST e (TYPE_SUBST (EL i rs') (Tyvar x))
    = TYPE_SUBST (EL i rs) (Tyvar x)`
  >> fs[]
  >> qabbrev_tac `f = λi. @e. P i e`
  >> `!i. i < LENGTH rs ==> P i (f i)` by (
    rw[]
    >> first_x_assum drule
    >> fs[GSYM SELECT_THM]
  )
  >> qexists_tac `MAP f (COUNT_LIST (LENGTH pqs))`
  >> rw[LENGTH_COUNT_LIST,EVERY_MAP,EVERY_MEM]
  >- (
    `LENGTH pqs = LENGTH rs` by fs[mg_sol_seq_def,sol_seq_def]
    >> rfs[MEM_COUNT_LIST]
    >> res_tac
    >> qunabbrev_tac `P`
    >> fs[]
  )
  >> `i < LENGTH pqs` by fs[mg_sol_seq_def,sol_seq_def]
  >> drule_then drule mg_sol_seq_is_const_or_type
  >> res_tac
  >> rw[el_map_count]
  >> qpat_x_assum `is_const_or_type (SND _)` kall_tac
  >> fs[is_const_or_type_eq,LR_TYPE_SUBST_tyvars,LR_TYPE_SUBST_compose]
  >> PURE_REWRITE_TAC[GSYM TYPE_SUBST_def,GSYM TYPE_SUBST_compose]
  >> qunabbrev_tac `P`
  >> fs[]
QED

(* Definition 5.5, Kunčar 2015 *)
Definition path_starting_at_def:
  path_starting_at ctxt k rs pqs =
  (
    wf_pqs pqs
    /\ k < LENGTH rs
    /\ LENGTH rs = LENGTH pqs
    /\ EVERY (UNCURRY (dependency ctxt)) (DROP k pqs)
    /\ (?e. renaming e /\ LR_TYPE_SUBST e (LR_TYPE_SUBST (EL k rs) (FST (EL k pqs))) = (FST (EL k pqs)))
    /\ sol_seq (TAKE k rs) (TAKE k pqs)
  )
End

Theorem MEM_DROP_TAKE:
  !xs l. l <= LENGTH xs ==> !x k. MEM x (DROP k (TAKE l xs)) ==> MEM x (DROP k xs)
Proof
  Induct
  >> fs[DROP_def,TAKE_def]
  >> rpt strip_tac
  >> FULL_CASE_TAC
  >> fs[DROP_def,TAKE_def,PULL_FORALL]
  >- (
    FULL_CASE_TAC
    >> fs[MEM]
    >> first_x_assum (qspecl_then [`l-1`,`x`,`0`] assume_tac)
    >> rfs[DROP_def]
  )
  >> FULL_CASE_TAC
  >> fs[DROP_def]
  >> first_x_assum (qspecl_then [`l-1`,`x`,`k-1`] assume_tac)
  >> rfs[DROP_def]
QED

Theorem path_starting_at_shorten:
  !k l rs pqs ctxt. k < l /\ l <= LENGTH pqs
  /\ path_starting_at ctxt k rs pqs ==>
  path_starting_at ctxt k (TAKE l rs) (TAKE l pqs)
Proof
  rw[path_starting_at_def,wf_pqs_def,EVERY_MEM,LENGTH_TAKE]
  >- (
    qpat_x_assum `!x. MEM _ pqs ==> _` match_mp_tac
    >> drule MEM_TAKE
    >> fs[]
  )
  >- (imp_res_tac MEM_DROP_TAKE >> fs[])
  >- (
    fs[EL_TAKE]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> fs[TAKE_TAKE]
QED

Theorem path_starting_at_0:
  !k rs pqs ctxt. path_starting_at ctxt k rs pqs ==>
  path_starting_at ctxt 0 (DROP k rs) (DROP k pqs)
Proof
  rw[path_starting_at_def,wf_pqs_def,HD_DROP,EVERY_MEM]
  >- (
    qpat_x_assum `!x. MEM _ pqs ==> _` match_mp_tac
    >> fs[EL_MEM,MEM_DROP]
  )
  >> rw[sol_seq_def,wf_pqs_def]
QED

Definition instance_LR_compute_def:
  (instance_LR_compute ((INR c1):type+term) (INR c2) =
    case (c1,c2) of
      | (Const m ty1,Const n ty2) => if (m = n)
        then instance_subst [(ty2,ty1)] [] [] else NONE
      | (_,_) => NONE)
  /\ (instance_LR_compute (INL ty1) (INL ty2) = instance_subst [(ty2,ty1)] [] [])
  /\ (instance_LR_compute _ _ = NONE)
End

Definition is_instance_LR_compute_def:
  is_instance_LR_compute x y = IS_SOME (instance_LR_compute x y)
End

Definition is_instance_LR_def:
  (is_instance_LR (INR c1) (INR c2) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ is_instance ty1 ty2)
  /\ (is_instance_LR (INL ty1) (INL ty2) = is_instance ty1 ty2)
  /\ (is_instance_LR _ _ = F)
End

Theorem is_instance_LR_equiv:
  is_instance_LR = is_instance_LR_compute
Proof
  fs[FUN_EQ_THM]
  >> rpt Cases
  >> REWRITE_TAC[is_instance_LR_def,instance_LR_compute_def,is_instance_LR_compute_def,instance_subst_completeness,option_CLAUSES]
  >> rpt (FULL_CASE_TAC)
  >> fs[option_CLAUSES]
QED

Theorem is_instance_LR_eq:
  !t t'. is_instance_LR t' t =
  (is_const_or_type t /\ is_const_or_type t'
  /\ ?s. LR_TYPE_SUBST s t' = t)
Proof
  rpt Cases
  >> fs[EQ_IMP_THM,is_const_or_type_eq,is_instance_LR_def,LR_TYPE_SUBST_cases,LR_TYPE_SUBST_sides]
  >> rpt strip_tac
  >> rveq
  >> fs[LR_TYPE_SUBST_cases]
  >- (qexists_tac `i` >> fs[])
  >- (qexists_tac `s` >> fs[])
  >- (
    qmatch_abbrev_tac `A \/ B`
    >> Cases_on `A`
    >> fs[]
    >> unabbrev_all_tac
    >> rw[LR_TYPE_SUBST_cases]
    >> rw[LR_TYPE_SUBST_cases]
  )
  >- (qexists_tac `i` >> fs[])
  >- (qexists_tac `s` >> fs[])
QED

(* Definition 5.6, Kunčar 2015 *)
Definition cyclic_dep_def:
  cyclic_dep ctxt =
  (?pqs rs.
    path_starting_at ctxt 0 rs pqs
    /\ is_instance_LR (FST (EL 0 pqs)) (LR_TYPE_SUBST (EL (LENGTH rs) rs) (SND (EL (LENGTH pqs) pqs))))
End

Definition has_common_instance_compute_def:
  (has_common_instance_compute ((INR c1):type+term) ((INR c2):type+term) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ IS_SOME (unify ty1 ty2))
  /\ (has_common_instance_compute (INL ty1) (INL ty2) = IS_SOME (unify ty1 ty2))
  /\ (has_common_instance_compute _ _ = F)
End

Definition has_common_instance_def:
  (has_common_instance (INR c1:type+term) (INR c2:type+term) =
    ?m ty1 ty2. c1 = Const m ty1 /\ c2 = Const m ty2 /\ ~(ty1 # ty2))
  /\ (has_common_instance (INL ty1) (INL ty2) = ~(ty1 # ty2))
  /\ (has_common_instance _ _ = F)
End

Theorem has_common_instance_equiv:
  !ty1 ty2. has_common_instance ty1 ty2 = has_common_instance_compute ty1 ty2
Proof
  rpt Cases
  >> REWRITE_TAC[has_common_instance_def,has_common_instance_compute_def,unify_complete]
QED

Theorem has_common_instance_is_instance_LR_equiv:
  !x y. is_const_or_type x /\ is_const_or_type y
  ==> has_common_instance x y = ?t. is_const_or_type t /\ is_instance_LR x t /\ is_instance_LR y t
Proof
  rw[EQ_IMP_THM,is_const_or_type_eq]
  >> fs[has_common_instance_def,is_instance_LR_def,orth_ty_def]
  >> rveq
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST s tt`
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance_LR (INR (Const c _)) _`
    >> qexists_tac `INR (Const c (TYPE_SUBST s tt))`
  )
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance_LR (INL ll) _`
    >> qexists_tac `INL (TYPE_SUBST s tt)`
  )
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance red _`
    >> qexists_tac `TYPE_SUBST s tt`
  )
  >> unabbrev_all_tac
  >> fs[is_instance_LR_def]
  >> rw[]
  >> TRY (
    qmatch_goalsub_abbrev_tac `is_instance ty _`
    >> qexists_tac `i` >> fs[]
  )
  >> (qexists_tac `i'` >> fs[])
QED

(* Definition 5.7, Kunčar 2015 *)
Definition composable_dep_def:
  composable_dep ctxt =
  !pqs rs p q. dependency ctxt p q
  /\ path_starting_at ctxt 0 rs pqs
  ==>
    is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
    \/
    is_instance_LR (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
    \/
    ~has_common_instance (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
End

Theorem LAST_DROP:
  !l k. ~NULL (DROP k l) ==> LAST (DROP k l) = LAST l
Proof
  Induct
  >- fs[LAST,DROP_NIL,NULL_EQ]
  >> strip_tac
  >> Cases
  >- fs[LAST,DROP_NIL,NULL_EQ]
  >> first_x_assum (qspec_then `n` assume_tac)
  >> rw[DROP,LAST_DEF,DROP_NIL,NULL_EQ]
QED

Theorem DROP_TAKE_NIL:
  !ls k. NULL (DROP k (TAKE k ls))
Proof
  Induct >> rw[DROP_def,TAKE_def]
QED

Theorem sol_seq_TAKE:
  !rs pqs k. sol_seq rs pqs /\
  k <= LENGTH rs ==> sol_seq (TAKE k rs) (TAKE k pqs)
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >- (
    qpat_x_assum `!x. MEM _ pqs ==> _` match_mp_tac
    >> `k <= LENGTH pqs` by fs[]
    >> imp_res_tac MEM_TAKE
  )
  >> `i < k` by fs[]
  >> fs[EL_TAKE]
QED

Theorem sol_seq_DROP:
  !rs pqs k. sol_seq rs pqs /\ k <= LENGTH rs
  ==> sol_seq (DROP k rs) (DROP k pqs)
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM]
  >- (
    last_x_assum match_mp_tac
    >> imp_res_tac MEM_DROP_IMP
  )
  >> `i + k < LENGTH pqs` by fs[]
  >> `(SUC i) + k < LENGTH pqs` by fs[]
  >> fs[EL_DROP,ADD_CLAUSES]
QED

Theorem LR_tyvars_SUBSET:
  !t t' x. is_const_or_type t /\ is_const_or_type t'
  /\ MEM x (FV t) /\ list_subset (FV t) (FV t')
  ==> MEM x (FV t')
Proof
  rw[is_const_or_type_eq,sum_case_def,list_subset_set,FV_def,SUBSET_DEF]
  >> fs[INL,INR]
QED

(* Comment to Definition 5.3, Kunčar 2015 *)
Theorem sol_mon_prop:
  !rs rs' pqs ctxt es.
  (sol_seq rs' pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ sol_seq rs pqs
  /\ LENGTH es = LENGTH rs
  /\ !i. i < LENGTH rs ==>
    LR_TYPE_SUBST (EL i es) (LR_TYPE_SUBST (EL i rs) (FST (EL i pqs)))
    = LR_TYPE_SUBST (EL i rs') (FST (EL i pqs)))
  ==>
    !i. i < LENGTH rs ==>
    LR_TYPE_SUBST (EL i es) (LR_TYPE_SUBST (EL i rs) (SND (EL i pqs)))
    = LR_TYPE_SUBST (EL i rs') (SND (EL i pqs))
Proof
  rw[sol_seq_def,wf_pqs_def,EVERY_MEM,ELIM_UNCURRY,monotone_def]
  >> imp_res_tac MEM_EL
  >> fs[]
  >> rpt (first_x_assum drule)
  >> rw[LR_TYPE_SUBST_compose,LR_TYPE_SUBST_tyvars]
  >> first_x_assum (drule_then assume_tac)
  >> qmatch_asmsub_abbrev_tac `MEM x (FV (SND elm))`
  >> qspecl_then [`SND elm`,`FST elm`,`x`] assume_tac LR_tyvars_SUBSET
  >> first_x_assum (qspec_then `i` assume_tac)
  >> rfs[LR_TYPE_SUBST_compose,LR_TYPE_SUBST_tyvars]
QED

(* Lemma 5.8, Kunčar 2015 *)
Theorem sol_ex_non_orth:
  !pqs rs rs' ctxt n k.
  sol_seq rs pqs
  /\ LENGTH rs = SUC n
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ composable_dep ctxt
  /\ monotone (dependency ctxt)
  /\ mg_sol_seq rs' (TAKE n pqs)
  /\ path_starting_at ctxt k rs' (TAKE n pqs)
  ==>
    is_instance_LR (LR_TYPE_SUBST (EL (PRE n) rs') (SND (EL (PRE n) pqs))) (FST (EL n pqs))
    \/
    is_instance_LR (FST (EL n pqs)) (LR_TYPE_SUBST (EL (PRE n) rs') (SND (EL (PRE n) pqs)))
Proof
  rw[EVERY_MEM,mg_sol_seq_def]
  >> `LENGTH rs' = n` by fs[mg_sol_seq_def,sol_seq_def,path_starting_at_def]
  >> `k <= n` by fs[mg_sol_seq_def,sol_seq_def,path_starting_at_def]
  >> first_x_assum (qspec_then `TAKE (LENGTH rs') rs` assume_tac)
  >> `~NULL rs' /\ LENGTH rs = LENGTH pqs /\ LENGTH rs' = n /\ n <= LENGTH pqs /\ n <= LENGTH rs /\ 0 < n` by (
    fs[mg_sol_seq_def,NULL_EQ,ADD1,sol_seq_def]
    >> CCONTR_TAC
    >> fs[sol_seq_def,path_starting_at_def]
    >> rveq >> fs[]
  )
  >> imp_res_tac sol_seq_TAKE
  >> fs[]
  >> imp_res_tac LENGTH_TAKE
  >> `n < LENGTH pqs` by fs[prim_recTheory.LESS_SUC_REFL]
  >> imp_res_tac MEM_EL
  >> fs[]
  >> qpat_assum `!x. MEM _ _ ==> _` (imp_res_tac o REWRITE_RULE[ELIM_UNCURRY])
  >> `EL (PRE n) (TAKE n pqs) = EL (PRE n) pqs /\ EL (PRE n) (TAKE n rs) = EL (PRE n) rs /\ LAST (DROP k (TAKE n rs)) = EL (PRE n) rs /\ LAST (DROP k (TAKE n pqs)) = EL (PRE n) pqs` by (
    `~NULL (DROP k (TAKE n rs)) /\ ~NULL (DROP k (TAKE n pqs))` by (
      CCONTR_TAC
      >> fs[DROP_NIL,DROP_TAKE_NIL,GREATER_EQ,NULL_EQ]
      >> rfs[]
      >> imp_res_tac (GSYM EQ_LESS_EQ)
      >> fs[path_starting_at_def,DROP_TAKE_NIL]
    )
    >> fs[LAST_DROP]
    >> `~NULL (TAKE n rs) /\ ~NULL(TAKE n pqs)` by (CCONTR_TAC >> fs[NULL_EQ,path_starting_at_def] >> rveq >> fs[])
    >> NTAC 2 (dxrule (REWRITE_RULE[GSYM NULL_EQ] LAST_EL))
    >> rw[]
    >> match_mp_tac EL_TAKE
    >> Cases_on `rs'`
    >> fs[prim_recTheory.PRE_DEF]
  )
  >> fs[ELIM_UNCURRY]
  >> imp_res_tac path_starting_at_0
  >> qpat_x_assum `composable_dep _` (dxrule o REWRITE_RULE[composable_dep_def])
  >> disch_then (drule_then assume_tac)
  >> `~NULL (DROP k rs')` by fs[NULL_EQ,path_starting_at_def,DROP_NIL]
  >> dxrule LAST_DROP
  >> dxrule (REWRITE_RULE[GSYM NULL_EQ] LAST_EL)
  >> rpt strip_tac
  >> rveq
  >> fs[]
  >> rfs[]
  >> `LENGTH rs' <= LENGTH pqs` by fs[]
  >> imp_res_tac MEM_TAKE
  >> qspecl_then [`rs'`,`TAKE (LENGTH rs') rs`,`TAKE (LENGTH rs') pqs`,`ctxt`,`es`] assume_tac sol_mon_prop
  >> rfs[sol_seq_TAKE,EVERY_MEM,MEM_TAKE,ELIM_UNCURRY]
  >> first_x_assum (qspec_then `PRE (LENGTH rs')` assume_tac)
  >> first_x_assum (qspec_then `PRE (LENGTH rs')` assume_tac)
  >> `PRE (LENGTH rs') < LENGTH rs'` by fs[prim_recTheory.LESS_SUC_REFL]
  >> fs[LR_TYPE_SUBST_tyvars,LR_TYPE_SUBST_compose,EL_TAKE]
  >> qpat_x_assum `sol_seq rs _` (assume_tac o REWRITE_RULE[sol_seq_def])
  >> fs[]
  >> first_x_assum (qspec_then `PRE (LENGTH rs')` assume_tac)
  >> `0 < LENGTH rs'` by fs[]
  >> imp_res_tac SUC_PRE
  >> fs[]
  >> rfs[]
  >> qmatch_asmsub_abbrev_tac `~has_common_instance fst snd`
  >> `is_const_or_type fst` by (
    unabbrev_all_tac
    >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM]
    >> `PRE (LENGTH rs') < LENGTH pqs` by fs[]
    >> imp_res_tac EL_MEM
    >> first_x_assum drule
    >> rw[ELIM_UNCURRY]
    >> imp_res_tac LR_TYPE_SUBST_type_preserving
    >> fs[]
  )
  >> `is_const_or_type snd` by (
    unabbrev_all_tac
    >> fs[sol_seq_def,wf_pqs_def,EVERY_MEM]
    >> `LENGTH rs' < LENGTH pqs` by fs[]
    >> imp_res_tac EL_MEM
    >> first_x_assum drule
    >> fs[ELIM_UNCURRY]
  )
  >> imp_res_tac LR_TYPE_SUBST_type_preserving
  >> fs[has_common_instance_is_instance_LR_equiv]
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST sfst fst = LR_TYPE_SUBST ssnd snd`
  >> qpat_x_assum `!x. _ \/ _ \/ _` (qspec_then `LR_TYPE_SUBST ssnd snd` assume_tac)
  >> rfs[is_instance_LR_eq,LR_TYPE_SUBST_type_preserving]
  >- (CCONTR_TAC >> fs[])
  >> qpat_x_assum `!x. LR_TYPE_SUBST _ snd <> LR_TYPE_SUBST ssnd snd` (qspec_then `ssnd` assume_tac)
  >> fs[]
QED

Theorem mg_sol_ext1[local]:
  !rs pqs p q s ctxt. (mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ LR_TYPE_SUBST s p = LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
  /\ wf_pqs [(p,q)]
  ==> sol_seq (rs++[s]) (pqs++[(p,q)])
Proof
  rw[mg_sol_seq_def,sol_seq_def]
  >> fs[wf_pqs_def,EVERY_APPEND]
  >> rpt strip_tac
  >> `i < LENGTH rs` by fs[]
  >> `i < LENGTH pqs` by fs[]
  >> NTAC 2 (dxrule EL_APPEND1)
  >> fs[]
  >> Cases_on `SUC i < LENGTH pqs`
  >- (
    `SUC i < LENGTH rs` by fs[]
    >> dxrule EL_APPEND1
    >> drule EL_APPEND1
    >> rw[]
  )
  >> rfs[NOT_LESS,GSYM ADD1,LESS_OR_EQ]
  >> `rs <> []` by (CCONTR_TAC >> fs[])
  >> `pqs <> []` by (CCONTR_TAC >> fs[])
  >> imp_res_tac LAST_EL
  >> imp_res_tac (REWRITE_RULE[LESS_OR_EQ] EL_APPEND2)
  >> fs[] >> rfs[]
QED

(* Lemma 5.9 *)
Theorem mg_sol_ext1:
  !rs pqs p q s ctxt. (mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ LR_TYPE_SUBST s p = LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
  /\ wf_pqs [(p,q)]
  ==> mg_sol_seq (rs++[s]) (pqs++[(p,q)])
Proof
  rw[]
  >> imp_res_tac mg_sol_ext1
  >> fs[mg_sol_seq_def]
  >> rpt strip_tac
  >> `LENGTH rs' = SUC (LENGTH rs)` by fs[sol_seq_def]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> qspecl_then [`rs'`,`pqs++[(p,q)]`,`LENGTH rs`] assume_tac sol_seq_TAKE
  >> rfs[TAKE_LENGTH_APPEND]
  >> `LENGTH rs <= LENGTH rs'` by fs[]
  >> first_x_assum (qspec_then `TAKE (LENGTH rs) rs'` assume_tac)
  >> rfs[]
  >> qspecl_then [`rs`,`TAKE (LENGTH rs) rs'`,`TAKE (LENGTH rs) pqs`,`ctxt`,`es`] assume_tac sol_mon_prop
  >> rfs[]
  >> qexists_tac `es++[LAST es]`
  >> rw[]
  >> Cases_on `i < LENGTH rs`
  >- (
    `i < LENGTH pqs` by fs[sol_seq_def]
    >> `i < LENGTH es` by fs[sol_seq_def]
    >> imp_res_tac EL_APPEND1
    >> `i < LENGTH rs'` by fs[sol_seq_def]
    >> rw[EL_TAKE]
  )
  >> rfs[NOT_LESS,GSYM ADD1,LESS_OR_EQ]
  >> `rs <> [] /\ pqs <> [] /\ es <> []` by (CCONTR_TAC >> fs[] >> rveq >> fs[sol_seq_def] >> rveq >> fs[])
  >> imp_res_tac LAST_EL
  >> `LENGTH rs <= i /\ LENGTH es <= i /\ LENGTH pqs <= i /\ LENGTH pqs = LENGTH rs` by fs[sol_seq_def]
  >> fs[EL_APPEND2]
  >> NTAC 2 (first_x_assum (qspec_then `PRE i` (assume_tac o GSYM)))
  >> rfs[]
  >> qpat_x_assum `LR_TYPE_SUBST _ (SND _) = LR_TYPE_SUBST _ (LR_TYPE_SUBST _ _)` (assume_tac o GSYM)
  >> `PRE i < i` by rfs[]
  >> fs[EL_TAKE]
  >> qpat_x_assum `sol_seq rs' (_ ++ _)` (assume_tac o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[sol_seq_def])
  >> first_x_assum (qspec_then `PRE i` assume_tac)
  >> rfs[]
  >> `SUC (PRE i) = i` by fs[]
  >> fs[]
  >> `PRE i < LENGTH pqs /\ LENGTH pqs <= i` by fs[]
  >> fs[EL_APPEND1,EL_APPEND2]
  >> `LENGTH pqs = i` by fs[]
  >> fs[]
QED

Definition ren_def:
  ren rs cs =
    MAP (Tyvar ## Tyvar) (rename_apart_by #"A" rs cs)
End


Theorem FST_SND_PAIR_MAP:
  !f g. FST o (f ## g) = f o FST
  /\ !f g. SND o (f ## g) = g o SND
Proof
  rw[SND_PAIR_MAP,FST_PAIR_MAP,FUN_EQ_THM,o_DEF]
QED

Theorem ren_ALL_DISTINCT:
  !r c. ALL_DISTINCT (MAP SND (ren r c))
  /\ ALL_DISTINCT (MAP FST (ren r c))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
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
  rw[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP,MEM_MAP,PAIR_MAP]
  >> Cases_on `y'`
  >> imp_res_tac rename_apart_by_MEM
  >> fs[]
QED

Theorem ren_Tyvars:
  !r c. EVERY (λx. ?y1 y2. x = (Tyvar y1,Tyvar y2)) (ren r c)
Proof
  rw[EVERY_MEM,ren_def,MEM_MAP,PAIR_MAP]
QED

Theorem ren_strlen_FST:
  !r c. EVERY (λa. ?x. a = Tyvar x /\ list_max (MAP strlen (r++c)) < strlen x) (MAP FST (ren r c))
Proof
  rw[EVERY_MEM,MEM_MAP]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] ren_Tyvars)
  >> fs[ren_def,PAIR_MAP,MEM_MAP]
  >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] rename_apart_by_strlen_FST)
  >> fs[]
QED

Theorem MEM_Tyvar_MAP_Tyvar:
  !l x. MEM (Tyvar x) (MAP Tyvar l) = MEM x l
Proof
  match_mp_tac MEM_f_MAP_f_INJ
  >> fs[]
QED

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

Theorem ren_MEM_SND:
  !r c x. MEM x (list_inter r c) = MEM (Tyvar x) (MAP SND (ren r c))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
  >> fs[GSYM MAP_MAP_o,MEM_Tyvar_MAP_Tyvar,rename_apart_by_MEM_SND]
QED

Theorem ren_MEM_SND1 = ONCE_REWRITE_RULE[list_inter_set_comm] ren_MEM_SND

Theorem ren_disj_dom_img:
  !r c. NULL (list_inter (MAP FST (ren r c)) (MAP SND (ren r c)))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
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
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_disj_img_c]
QED

Theorem ren_disj_dom_img2:
  !r c. NULL (list_inter (MAP ((TYPE_SUBST (ren r c)) o $Tyvar) r) (MAP Tyvar c))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> rw[MEM_MAP]
  >> Cases_on `MEM y' r`
  >> fs[MEM_MAP]
  >> rveq
  >> Cases_on `MEM (Tyvar y') (MAP SND (ren r c))`
  >- (
    qspecl_then [`r`,`c`] assume_tac ren_disj_dom_img
    >> fs[list_inter_def,NULL_FILTER]
    >> imp_res_tac MEM_SPLIT_APPEND_SND_first
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> first_x_assum (qspec_then `[(q,Tyvar y')]++sfx` assume_tac)
    >> `MEM q (MAP FST (ren r c))` by fs[]
    >> res_tac
    >> fs[REV_ASSOCD_def]
    >> qspecl_then [`r`,`c`] (assume_tac o REWRITE_RULE[list_inter_def,NULL_FILTER,Q.ISPECL [`c:mlstring list`,`Tyvar`] MEM_MAP]) ren_disj_img_c
    >> pop_assum imp_res_tac
    >> CCONTR_TAC
    >> fs[]
  )
  >> imp_res_tac TYPE_SUBST_drop_all
  >> fs[GSYM ren_MEM_SND1]
  >> fs[list_inter_def,MEM_FILTER]
  >> fs[]
  >> CCONTR_TAC
  >> fs[]
QED

Theorem ren_disj_img_r:
  !r c. NULL (list_inter (MAP FST (ren r c)) (MAP Tyvar r))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_disj_img_r]
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
    >> fs[MEM_MAP]
    >> Cases_on `y`
    >> fs[PAIR_MAP,rename_apart_by_ALOOKUP]
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

Theorem SWAP_eq:
  SWAP = λ(x,y). (y,x)
Proof
  fs[FUN_EQ_THM,SWAP_def,ELIM_UNCURRY]
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
  >> fs[ren_def,MEM_MAP,PAIR_MAP]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
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

Theorem ren_list_complement:
   !r rc c. NULL (list_inter (MAP SND (ren (list_complement r rc) c)) (MAP Tyvar rc))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_list_complement]
QED

Theorem ren_LIST_UNION:
   (!r c1 c2. NULL (list_inter (MAP FST (ren r (LIST_UNION c1 c2))) (MAP Tyvar c1)))
   /\ !r c1 c2. NULL (list_inter (MAP FST (ren r (LIST_UNION c1 c2))) (MAP Tyvar c2))
Proof
  fs[ren_def,MAP_MAP_o,FST_SND_PAIR_MAP]
  >> rw[GSYM MAP_MAP_o,NULL_list_inter_MAP_Tyvar,rename_apart_by_LIST_UNION]
QED

val _ = Parse.add_infix("∩", 401, Parse.NONASSOC)
val _ = Parse.overload_on("∩",``λs t. list_inter s t``)
val _ = Parse.add_infix("\\", 401, Parse.NONASSOC)
val _ = Parse.overload_on("\\",``λs t. list_complement s t``)
val _ = Parse.add_infix("∪", 401, Parse.NONASSOC)
val _ = Parse.overload_on("∪",``λs t. LIST_UNION s t``)
val _ = Parse.add_infix("⊆", 401, Parse.NONASSOC)
val _ = Parse.overload_on("⊆",``λs t. list_subset s t``)

Theorem list_subset_id:
  !l. list_subset l l
Proof
  fs[list_subset_def,EVERY_MEM]
QED

Theorem list_inter_LIST_UNION_NULL:
  !a b c. NULL (list_inter a (LIST_UNION b c))
  = (NULL (list_inter a b) /\ NULL (list_inter a c))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> rw[EQ_IMP_THM]
  >> fs[]
QED

Theorem LR_TYPE_SUBST_FILTER_tyvars:
  !p s. is_const_or_type p ==>
  LR_TYPE_SUBST (FILTER (λx. MEM (SND x) (MAP Tyvar (FV p))) s) p
  = LR_TYPE_SUBST s p
Proof
  rw[is_const_or_type_eq,LAMBDA_PROD,sum_case_def,LR_TYPE_SUBST_cases,tvars_def,FV_def]
  >> fs[MEM_MAP,LR_TYPE_SUBST_cases]
  >> qspecl_then [`ty`,`s`] assume_tac TYPE_SUBST_FILTER_tyvars
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

Theorem MEM_LIST_UNION:
  !x a b. MEM x (LIST_UNION a b) = (MEM x a \/ MEM x b)
Proof
  fs[set_LIST_UNION]
QED

Theorem ALL_DISTINCT_FST_MEMs:
  !x v w s. ALL_DISTINCT (MAP FST s)
  /\ MEM (x,v) s /\ MEM (x,w) s
  ==> v = w
Proof
  rw[]
  >> qpat_x_assum `MEM _ s` (assume_tac o REWRITE_RULE[MEM_SPLIT])
  >> fs[]
  >> `~MEM x (MAP FST l1) /\ ~MEM x (MAP FST l2)` by (
    imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> fs[ALL_DISTINCT_APPEND]
  )
  >> `~MEM (x,v) l1 /\ ~MEM (x,v) l2` by (
    CCONTR_TAC
    >> fs[]
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> fs[]
  )
  >> fs[]
QED

Theorem ALL_DISTINCT_SND_MEMs:
  !x v w s. ALL_DISTINCT (MAP SND s)
  /\ MEM (v,x) s /\ MEM (w,x) s
  ==> v = w
Proof
  ONCE_REWRITE_TAC[GSYM FST_SND_SWAP]
  >> rw[GSYM MAP_MAP_o]
  >> imp_res_tac (Q.ISPEC `SWAP` MEM_MAP_f)
  >> fs[SWAP_def]
  >> match_mp_tac ALL_DISTINCT_FST_MEMs
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem ren_TYPE_SUBST_INJ1:
  !r c x y.
    MEM x (LIST_UNION r c) /\ MEM y (LIST_UNION r c)
    /\ ~MEM x (list_inter r c) /\ ~MEM y (list_inter r c)
    /\ TYPE_SUBST (ren r c) (Tyvar x) = TYPE_SUBST (ren r c) (Tyvar y)
    ==> x = y
Proof
  rw[]
  >> imp_res_tac (ccontr_equiv ren_MEM_SND)
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
  >> fs[REV_ASSOCD_def]
  >> rpt (qpat_x_assum `ren r c = _` (assume_tac o ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]))
  >> fs[]
  >> qspecl_then [`r`,`c`] (assume_tac o REWRITE_RULE[list_inter_def,NULL_FILTER]) ren_disj_img_c
  >> qspecl_then [`r`,`c`] (assume_tac o REWRITE_RULE[list_inter_def,NULL_FILTER]) ren_disj_img_r
  >> rpt (first_x_assum (qspec_then `Tyvar y` assume_tac))
  >> rfs[MEM_Tyvar_MAP_Tyvar]
  >> fs[MEM_FILTER,list_inter_def,list_complement_def,MEM_LIST_UNION]
  >> rfs[markerTheory.Abbrev_def]
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

Theorem ren_MEM_list_complement:
  !r s c x. let sigma = ren (list_complement r s) (LIST_UNION s c) in
  MEM (Tyvar x) (MAP (TYPE_SUBST sigma o Tyvar) (list_complement r s))
  = MEM (Tyvar x) (list_complement (MAP (TYPE_SUBST sigma o Tyvar) r) (MAP (TYPE_SUBST sigma o Tyvar) s))
Proof
  rw[]
  >> match_mp_tac list_complement_MAP_INJ1
  >> rw[o_DEF]
  >> qspecl_then [`list_complement r s`,`LIST_UNION s c`] mp_tac ren_TYPE_SUBST_INJ
  >> disch_then match_mp_tac
  >> ASM_REWRITE_TAC[TYPE_SUBST_def]
  >> fs[MEM_FILTER,list_inter_def,list_complement_def,MEM_LIST_UNION]
  >> Cases_on `MEM x s`
  >> ASM_REWRITE_TAC[]
  >> Cases_on `MEM y s`
  >> ASM_REWRITE_TAC[]
QED

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

Theorem renn_set_MAP_SWAP:
  !r c. set (MAP SWAP (renn r c)) = set (renn r c)
Proof
  rw[renn_def,SWAP_SWAP_INVOL,MAP_MAP_o,UNION_COMM]
QED

Theorem renn_MEM:
  !r c x y. MEM (x,y) (renn r c) <=> MEM (y,x) (renn r c)
Proof
  rw[]
  >> qspecl_then [`SWAP`,`renn r c`] assume_tac
    (INST_TYPE [alpha |-> ``:type#type``,beta|-> ``:type#type``] MEM_f_MAP_f_INJ)
  >> fs[SWAP_eq,LAMBDA_PROD]
  >> fs[ELIM_UNCURRY,GSYM SWAP_eq]
  >> pop_assum (fn x => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV[GSYM x])))
  >> fs[renn_set_MAP_SWAP]
QED

Theorem renn_MEM_MAP_SWAP:
  !r c x. MEM x (MAP SWAP (renn r c)) <=> MEM x (renn r c)
Proof
  fs[renn_set_MAP_SWAP]
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
  rw[]
  >> Cases_on `MEM (Tyvar x) (MAP SND (renn r c))`
  >- (
    drule TYPE_SUBST_MEM_MAP_SND
    >> rw[]
    >> imp_res_tac renn_MEM
    >> drule (Q.ISPEC `SND` MEM_MAP_f)
    >> rw[]
    >> drule TYPE_SUBST_MEM_MAP_SND
    >> qspecl_then [`r`,`c`] (assume_tac o CONJUNCT1) renn_ALL_DISTINCT
    >> rw[]
    >> imp_res_tac ALL_DISTINCT_SND_MEMs
  )
  >> drule TYPE_SUBST_drop_all
  >> fs[]
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

Theorem renn_Tyvars:
  !r c. EVERY (λx. ?y1 y2. x = (Tyvar y1,Tyvar y2)) (renn r c)
Proof
  rw[SWAP_def,EVERY_MEM,ren_def,renn_def,MEM_MAP,PAIR_MAP]
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
  >> qspecl_then [`r`,`c`,`x`] assume_tac renn_Tyvars_TYPE_SUBST
  >> fs[]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem renn_diff:
  !r c. EVERY (UNCURRY $<>) (renn r c)
Proof
  rw[EVERY_MEM,MEM_APPEND,renn_def,MEM_MAP,SWAP_def]
  >> imp_res_tac (REWRITE_RULE[EVERY_MEM] ren_diff)
  >> fs[ELIM_UNCURRY]
QED

Theorem TYPE_SUBST_ren_Tyvar:
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

Theorem TYPE_SUBST_renn_Tyvar:
  !r c x. ?a. TYPE_SUBST (renn r c) (Tyvar x) = Tyvar a
Proof
  rw[]
  >> Cases_on `MEM (Tyvar x) (MAP SND (renn r c))`
  >- (
    imp_res_tac TYPE_SUBST_MEM_MAP_SND
    >> imp_res_tac (REWRITE_RULE[EVERY_MEM] renn_Tyvars)
    >> fs[]
    >> rveq
  )
  >> dxrule TYPE_SUBST_drop_all
  >> fs[]
QED

Theorem renn_TYPE_SUBST_bij:
  !r c x. TYPE_SUBST (renn r c) (TYPE_SUBST (renn r c) (Tyvar x)) = Tyvar x
Proof
  rw[]
  >> qspecl_then [`r`,`c`,`x`] assume_tac TYPE_SUBST_renn_Tyvar
  >> fs[]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> match_mp_tac renn_bij
  >> fs[]
QED

Theorem renn_LR_TYPE_SUBST_bij:
  !r c x. is_const_or_type x ==> LR_TYPE_SUBST (renn r c) (LR_TYPE_SUBST (renn r c) x) = x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,TYPE_SUBST_compose]
  >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL]))
  >> fs[TYPE_SUBST_tyvars]
  >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
  >> fs[GSYM TYPE_SUBST_compose,renn_TYPE_SUBST_bij]
QED

Theorem MEM_FV_LR_TYPE_SUBST_ren_imp:
  !x t.
  MEM x (FV (LR_TYPE_SUBST (ren r c) t)) /\ is_const_or_type t
  ==> ?y. MEM y (FV t) /\ TYPE_SUBST (ren r c) (Tyvar y) = Tyvar x
Proof
  rw[is_const_or_type_eq]
  >> fs[LR_TYPE_SUBST_cases,FV_def,sum_case_def,tyvars_def,tvars_def,tyvars_TYPE_SUBST]
  >> qspecl_then [`r`,`c`,`x'`] assume_tac TYPE_SUBST_ren_Tyvar
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
  >> qspecl_then [`r`,`c`,`x'`] assume_tac TYPE_SUBST_renn_Tyvar
  >> fs[tyvars_def]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[tyvars_def]
QED

Theorem sol_seq_TYPE_SUBST:
  !rs pqs s. sol_seq rs pqs
  ==> sol_seq (MAP (λx. MAP (TYPE_SUBST s ## I) x ++ s) rs) pqs
Proof
  rpt strip_tac
  >> imp_res_tac sol_seq_is_const_or_type
  >> fs[sol_seq_def]
  >> rw[]
  >> rfs[]
  >> qpat_x_assum `!x. _ ==> (_ = _)` drule
  >> `i < LENGTH rs /\ i < LENGTH pqs /\ SUC i < LENGTH rs` by fs[]
  >> fs[EL_MAP]
  >> res_tac
  >> rw[GSYM LR_TYPE_SUBST_compose]
QED

Theorem mg_sol_seq_TYPE_SUBST:
  !rs pqs r c. mg_sol_seq rs pqs
  ==> mg_sol_seq (MAP (λx. MAP (TYPE_SUBST (renn r c) ## I) x ++ (renn r c)) rs) pqs
Proof
  rw[mg_sol_seq_def,sol_seq_TYPE_SUBST]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> first_x_assum drule
  >> rw[]
  >> qmatch_goalsub_abbrev_tac `TYPE_SUBST sigma`
  >> qexists_tac `MAP (λx. MAP (TYPE_SUBST x ## I) sigma ++ x) es`
  >> rw[]
  >> first_x_assum drule
  >> drule sol_seq_is_const_or_type
  >> disch_then drule
  >> rw[]
  >> `i < LENGTH rs` by fs[]
  >> imp_res_tac LR_TYPE_SUBST_type_preserving
  >> rw[EL_MAP]
  >> qpat_x_assum `LR_TYPE_SUBST _ (LR_TYPE_SUBST _ _) = _` (assume_tac o GSYM)
  >> fs[GSYM LR_TYPE_SUBST_compose]
  >> rpt (first_x_assum (qspec_then `EL i rs` assume_tac))
  >> qunabbrev_tac `sigma`
  >> fs[renn_LR_TYPE_SUBST_bij]
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
  >> drule (REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s)
  >> disch_then (qspecl_then [`r`,`c`] assume_tac)
  >> CCONTR_TAC
  >> fs[]
  >> imp_res_tac (ccontr_equiv renn_MAP_FST_SND)
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST sigma`
  >> Cases_on `MEM (Tyvar y'') (MAP SND sigma)`
  >- (
    qunabbrev_tac `sigma`
    >> imp_res_tac TYPE_SUBST_MEM_MAP_SND
    >> imp_res_tac (Q.ISPEC `FST` MEM_MAP_f)
    >> imp_res_tac renn_MAP_FST_SND
    >> imp_res_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s)
    >> rfs[]
    >> fs[]
  )
  >> imp_res_tac TYPE_SUBST_drop_all
  >> rveq
  >> fs[MEM_Tyvar_MAP_Tyvar,list_complement_def,MEM_FILTER]
QED

Theorem renn_disj_dom_img3:
  !r c. NULL (list_inter (MAP ((TYPE_SUBST (renn r c)) o $Tyvar) (list_inter r c)) (MAP Tyvar c))
Proof
  rw[NULL_FILTER,list_inter_def,GSYM MAP_MAP_o,MEM_MAP]
  >> CCONTR_TAC
  >> fs[MEM_FILTER,renn_def]
  >> qspecl_then [`r`,`c`,`y''`] assume_tac ren_MEM_SND
  >> rfs[MEM_LIST_UNION,list_inter_def,MEM_FILTER]
  >> fs[REWRITE_RULE[TYPE_SUBST_def] TYPE_SUBST_drop_suffix]
  >> fs[GSYM MEM_Tyvar_MAP_Tyvar]
  >> qspecl_then [`r`,`c`,`Tyvar y'`] assume_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] ren_disj_dom_img2)
  >> rfs[MEM_Tyvar_MAP_Tyvar,MEM_MAP]
  >> qpat_x_assum `_ = REV_ASSOCD _ _ _` (assume_tac o GSYM)
  >> fs[]
  >> rfs[]
  >> first_x_assum (qspec_then `y''` (assume_tac o GSYM))
  >> Cases_on `y`
  >> fs[]
  >> rveq
  >> fs[]
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
    >> fs[]
    >> rveq
    >> fs[]
  )
  >> qmatch_goalsub_abbrev_tac `a \/ _`
  >> Cases_on `a`
  >> mp_tac renn_bij3
  >> fs[markerTheory.Abbrev_def]
  >> disch_then drule
  >> rw[]
  >> fs[]
QED

Theorem mg_sol_ext2[local]:
  !rs pqs p q s ctxt. (mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ p = LR_TYPE_SUBST (FILTER
    (λx. MEM (SND x) (MAP Tyvar (FV (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs)))))) s)
      (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs)))
  /\ wf_pqs [(p,q)])
  ==> ?r. mg_sol_seq ((MAP (λs. MAP (TYPE_SUBST r ## I) s ++ r) rs)++[[]]) (pqs++[(p,q)])
    /\ !x. MEM x (FV (LR_TYPE_SUBST (EL (PRE (LENGTH rs)) rs) (SND (EL (PRE (LENGTH pqs)) pqs))))
      ==> TYPE_SUBST r (Tyvar x) = TYPE_SUBST s (Tyvar x)
Proof
  rw[]
  >> qmatch_asmsub_abbrev_tac `wf_pqs [(p,_)]`
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST (FILTER f s) rn_qn`
  >> qabbrev_tac `r0_p0 = LR_TYPE_SUBST (EL 0 rs) (FST (EL 0 pqs))`
  >> qabbrev_tac `qn = SND (EL (PRE (LENGTH pqs)) pqs)`
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def,mg_sol_seq_def]
  >> qabbrev_tac `r = FV r0_p0`
  >> qabbrev_tac `t = FV rn_qn`
  >> qabbrev_tac `c = FV p`
  >> `sol_seq rs pqs` by fs[mg_sol_seq_def]
  >> dxrule mg_sol_seq_TYPE_SUBST
  >> disch_then (qspecl_then [`list_complement r t`,`LIST_UNION t c`] assume_tac)
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST sigma`
  >> `PRE (LENGTH pqs) < LENGTH pqs` by fs[sol_seq_def]
  >> drule_then drule mg_sol_seq_is_const_or_type
  >> rw[]
  >> `is_const_or_type rn_qn` by (
    imp_res_tac LR_TYPE_SUBST_type_preserving
    >> qunabbrev_tac `rn_qn`
    >> qunabbrev_tac `qn`
    >> fs[]
  )
  >> `is_const_or_type p` by fs[wf_pqs_def]
  >> rfs[]
  >> qmatch_asmsub_abbrev_tac `mg_sol_seq rt _`
  >> qspecl_then [`r`,`t`,`c`,`rn_qn`] assume_tac renn_ID_LR_TYPE_SUBST
  >> rfs[list_subset_def,EVERY_MEM]
  >> `sol_seq (MAP (λx. (MAP (TYPE_SUBST (FILTER f s) ## I) x) ++ (FILTER f s)) rt ++[[]]) (pqs++[(p,q)])` by (
    rw[sol_seq_def]
    >- fs[wf_pqs_def,mg_sol_seq_def,sol_seq_def]
    >- (qunabbrev_tac `rt` >> fs[])
    >> qmatch_goalsub_abbrev_tac `EL _ (MAP fs rt ++ _)`
    >> Cases_on `i = PRE (LENGTH rt)`
    >- (
      `LENGTH (MAP ss rt) <= SUC i /\ 0 < LENGTH rt` by fs[]
      >> fs[EL_APPEND2]
      >> `LENGTH rt = LENGTH pqs` by (qunabbrev_tac `rt` >> fs[])
      >> `i < LENGTH (MAP fs rt)` by fs[]
      >> fs[EL_APPEND1,EL_APPEND2,EL_MAP]
      >> `0 < LENGTH pqs` by fs[]
      >> fs[SUC_PRE,LR_TYPE_SUBST_NIL]
      >> qunabbrev_tac `rt`
      >> fs[EL_MAP]
      >> qunabbrev_tac `p`
      >> qpat_x_assum `LR_TYPE_SUBST _ rn_qn = rn_qn` (fn x => ONCE_REWRITE_TAC[GSYM x])
      >> qunabbrev_tac `fs`
      >> qunabbrev_tac `rn_qn`
      >> `rs <> []` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def])
      >> `pqs <> []` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def])
      >> fs[LR_TYPE_SUBST_compose]
      >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
      >> fs[MAP_MAP_o,MAP_EQ_f]
      >> fs[TYPE_SUBST_compose,o_DEF,PAIR_MAP]
    )
    (* i < PRE (LENGTH rt) *)
    >> fs[GSYM ADD1]
    >> `SUC i < LENGTH rt /\ i < LENGTH rt
      /\ i < LENGTH (MAP ss rt) /\ SUC i < LENGTH (MAP ss rt)
      /\ i < LENGTH pqs /\ SUC i < LENGTH pqs` by (unabbrev_all_tac >> fs[])
    >> fs[EL_APPEND1,EL_MAP]
    >> `sol_seq rt pqs` by (qunabbrev_tac `rt` >> fs[sol_seq_TYPE_SUBST,mg_sol_seq_def])
    >> rfs[sol_seq_def]
    >> qpat_x_assum `!x. _` imp_res_tac
    >> qmatch_goalsub_abbrev_tac `SND q_i`
    >> qmatch_goalsub_abbrev_tac `FST p_ip`
    >> `is_const_or_type (SND q_i) /\ is_const_or_type (FST p_ip)` by (
      qunabbrev_tac `q_i`
      >> qunabbrev_tac `p_ip`
      >> `SUC i < LENGTH pqs /\ i < LENGTH pqs` by fs[]
      >> imp_res_tac mg_sol_seq_is_const_or_type
      >> fs[]
    )
    >> qunabbrev_tac `fs`
    >> fs[GSYM LR_TYPE_SUBST_compose]
  )
  >> qexists_tac `MAP (TYPE_SUBST (FILTER f s) ## I) sigma ++ (FILTER f s)`
  >> qmatch_asmsub_abbrev_tac `sol_seq (f1 ++ [[]]) _`
  >> qmatch_goalsub_abbrev_tac `mg_sol_seq (f2 ++ [[]]) _`
  >> `f2 = f1` by (
    qunabbrev_tac `rt`
    >> qunabbrev_tac `f1`
    >> qunabbrev_tac `f2`
    >> fs[MAP_MAP_o,o_DEF,TYPE_SUBST_compose,ETA_THM,MAP_EQ_f]
    >> fs[TYPE_SUBST_compose,PAIR_MAP]
  )
  >> ONCE_REWRITE_TAC[CONJ_COMM]
  >> rw[]
  >- (
    qspecl_then [`rn_qn`,`s`] mp_tac LR_TYPE_SUBST_FILTER_tyvars
    >> qspec_then `rn_qn` mp_tac LR_TYPE_SUBST_NIL
    >> fs[]
    >> disch_then (fn x => qpat_x_assum `LR_TYPE_SUBST _ rn_qn = rn_qn` (mp_tac o (CONV_RULE (RHS_CONV (ONCE_REWRITE_CONV[GSYM x])))))
    >> fs[LR_TYPE_SUBST_tyvars]
    >> rpt (disch_then imp_res_tac)
    >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
    >> PURE_REWRITE_TAC[GSYM TYPE_SUBST_compose]
    >> fs[ETA_THM]
  )
  >> rw[mg_sol_seq_def]
  >> `sol_seq (TAKE (LENGTH pqs) rs') pqs` by (
    `LENGTH rs' = SUC(LENGTH pqs)` by fs[sol_seq_def]
    >> dxrule sol_seq_TAKE
    >> disch_then (qspec_then `LENGTH pqs` assume_tac)
    >> rfs[TAKE_APPEND1]
  )
  >> qmatch_asmsub_abbrev_tac `sol_seq rs'_front pqs`
  >> fs[mg_sol_seq_def]
  >> `LENGTH f1 = LENGTH rs` by (qunabbrev_tac `f1` >> fs[LENGTH_MAP])
  >> first_x_assum (qspec_then `rs'_front` mp_tac)
  >> rw[]
  >> qexists_tac `(MAP (λi.
        (FILTER (λx. MEM (SND x) (MAP Tyvar (FV p))) (LAST rs'))
        ++ (FILTER (λx. ~MEM (SND x) (MAP Tyvar (FV p))) (EL i es))
    ) (COUNT_LIST (LENGTH pqs))) ++ [LAST rs']`
  >> fs[LENGTH_COUNT_LIST]
  >> Induct_on `(LENGTH pqs) - i`
  >- (
    rw[LESS_OR_EQ]
    >> rfs[]
    >> `LENGTH (COUNT_LIST (LENGTH pqs)) <= (LENGTH pqs)` by fs[LENGTH_COUNT_LIST]
    >> fs[EL_APPEND2]
    >> `rs' <> []` by (CCONTR_TAC >> fs[sol_seq_def])
    >> `PRE (LENGTH rs') = LENGTH pqs` by fs[sol_seq_def]
    >> fs[LENGTH_COUNT_LIST,LR_TYPE_SUBST_NIL,LAST_EL]
  )
  >> rw[]
  >> `i < LENGTH pqs` by fs[]
  >> drule_then (drule_then assume_tac) sol_seq_is_const_or_type
  >> fs[GSYM ADD_EQ_SUB]
  >> drule_then (qspec_then `(EL i rt)` assume_tac) LR_TYPE_SUBST_type_preserving
  >> `i < LENGTH (COUNT_LIST (LENGTH pqs))` by fs[LENGTH_COUNT_LIST]
  >> fs[EL_APPEND1,EL_MAP,EL_COUNT_LIST,EL_TAKE]
  (* >> qmatch_asmsub_abbrev_tac `is_const_or_type rti_qi` *)
  >> first_x_assum (qspecl_then [`pqs`,`SUC i`] mp_tac)
  >> qunabbrev_tac `rs'_front`
  >> fs[Q.ISPEC `T` markerTheory.Abbrev_def]
  >> qpat_assum `sol_seq (_ ++ [[]]) _` ((qspec_then `i` mp_tac) o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[sol_seq_def])
  >> `LENGTH rs' = SUC (LENGTH pqs) /\ i < LENGTH f1` by fs[sol_seq_def]
  >> fs[EL_APPEND1]
  >> disch_then (fn x => fs[GSYM x])
  >> qpat_assum `sol_seq rs' _` ((qspec_then `i` mp_tac) o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[sol_seq_def])
  >> fs[EL_APPEND1]
  >> disch_then (fn x => fs[GSYM x])
  >> qspecl_then [`rt`,`(TAKE (LENGTH pqs) rs')`,`pqs`,`ctxt`,`es`] mp_tac sol_mon_prop
  >> fs[EL_TAKE,EVERY_MEM]
  >> disch_then (qspec_then `i` mp_tac)
  >> `LENGTH rt = LENGTH pqs` by fs[sol_seq_def]
  >> fs[EL_TAKE]
  >> disch_then (fn x => fs[GSYM x])
  >> `i < LENGTH rt` by fs[]
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST (eta_si)`
  (* >> `i < LENGTH nums` by (qunabbrev_tac `nums` >> fs[LENGTH_COUNT_LIST]) *)
  >> `i < LENGTH rs` by fs[]
  >> qunabbrev_tac `f1`
  >> qpat_x_assum `Abbrev(MAP _ _ = _)` kall_tac
  >> fs[EL_MAP]
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST (EL i es) rt_qi`
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST eta_si chaos`
  >> qabbrev_tac `qi = SND (EL i pqs)`
  >> `chaos = LR_TYPE_SUBST (FILTER f s) (LR_TYPE_SUBST (EL i rt) qi)` by (
    qunabbrev_tac `chaos`
    >> qunabbrev_tac `rt`
    >> fs[LR_TYPE_SUBST_compose,TYPE_SUBST_compose,EL_MAP,MAP_MAP_o,o_DEF,ETA_THM]
    >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    >> fs[FUN_EQ_THM,PAIR_MAP,TYPE_SUBST_compose]
  )
  >> qpat_x_assum `Abbrev_def (chaos = _)` kall_tac
  >> pop_assum (fn x => rw[x])
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST eta_i (LR_TYPE_SUBST _ _)`
  >> qabbrev_tac `p_i = FST (EL i pqs)`
  >> qabbrev_tac `rt_pi = LR_TYPE_SUBST (EL i rt) p_i`
  >> `LR_TYPE_SUBST (EL i es) rt_pi = LR_TYPE_SUBST eta_i (LR_TYPE_SUBST (FILTER f s) rt_pi)` by (
    `is_const_or_type rt_pi` by (
      qunabbrev_tac `rt_pi`
      >> match_mp_tac LR_TYPE_SUBST_type_preserving
      >> fs[]
    )
    >> rw[LR_TYPE_SUBST_compose,LR_TYPE_SUBST_tyvars]
    >> Cases_on `MEM x (FV rn_qn)`
    >- (
      qabbrev_tac `ri_pi = LR_TYPE_SUBST (EL i rs) p_i`
      >> `MEM x (FV ri_pi)` by (
        qspecl_then [`pqs`,`rs`,`ctxt`] mp_tac monotone_dep_seq_free_vars_SND_FST
        >> fs[EVERY_MEM]
        >> disch_then (qspecl_then [`i`,`PRE (LENGTH pqs)`] mp_tac)
        >> rfs[SUBSET_DEF]
      )
      >> qabbrev_tac `ri_qi = LR_TYPE_SUBST (EL i rs) qi`
      >> `MEM x (FV ri_qi)` by (
        qspecl_then [`pqs`,`rs`,`ctxt`] mp_tac monotone_dep_seq_free_vars_SND_SND
        >> fs[EVERY_MEM]
        >> disch_then (qspecl_then [`i`,`PRE (LENGTH pqs)`] mp_tac)
        >> rfs[SUBSET_DEF]
      )
      >> `MEM x (FV (rt_qi))` by (
        qunabbrev_tac `rt_qi`
        >> qunabbrev_tac `rt_pi`
        >> qunabbrev_tac `rt`
        >> qmatch_asmsub_abbrev_tac `EL i (MAP sigma_map rs)`
        >> rfs[EL_MAP]
        >> qunabbrev_tac `sigma_map`
        >> rfs[GSYM LR_TYPE_SUBST_compose]
        >> qspecl_then [`p_i`,`EL i rs`] assume_tac LR_TYPE_SUBST_type_preserving
        >> qspecl_then [`qi`,`EL i rs`] assume_tac LR_TYPE_SUBST_type_preserving
        >> qspecl_then [`x`,`ri_pi`,`list_complement r t`,`LIST_UNION t c`] mp_tac MEM_FV_LR_TYPE_SUBST_renn_imp
        >> qspecl_then [`r`,`t`,`c`,`Tyvar x`] mp_tac (REWRITE_RULE[NULL_FILTER,list_inter_def] renn_disj_dom_s)
        >> fs[]
        >> rfs[MEM_Tyvar_MAP_Tyvar]
        >> rw[]
        >> qunabbrev_tac `sigma`
        >> imp_res_tac (REWRITE_RULE[TYPE_SUBST_def] renn_bij)
        >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST sigma`
        >> qpat_x_assum `is_const_or_type ri_qi` (assume_tac o REWRITE_RULE[is_const_or_type_eq])
        >> fs[EL_MAP,LR_TYPE_SUBST_cases,FV_def,tyvars_def,tvars_def]
        >> rveq
        >> rfs[sum_case_def,tyvars_def,tvars_def,tyvars_TYPE_SUBST]
        >> qexists_tac `x`
        >> imp_res_tac TYPE_SUBST_drop_all
        >> fs[tyvars_def]
      )
      >> rfs[LR_TYPE_SUBST_compose]
      >> qpat_x_assum `LR_TYPE_SUBST _ rt_qi = LR_TYPE_SUBST _ rt_qi` mp_tac
      >> fs[LR_TYPE_SUBST_tyvars]
      >> disch_then drule
      >> disch_then (fn x => fs[GSYM x])
      >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
      >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_compose]
      >> qmatch_goalsub_abbrev_tac `TYPE_SUBST eta_si sx`
      >> `list_subset (tyvars sx) (FV p)` by (
        qunabbrev_tac `sx`
        >> qunabbrev_tac `c`
        >> qunabbrev_tac `p`
        >> fs[tyvars_TYPE_SUBST]
        >> qpat_x_assum `is_const_or_type rn_qn` (assume_tac o REWRITE_RULE[is_const_or_type_eq])
        >> fs[LR_TYPE_SUBST_cases,tyvars_def,tvars_def,FV_def,sum_case_def]
        >> rveq
        >> fs[sum_case_def,tyvars_def,tvars_def,list_subset_def,EVERY_MEM]
        >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
        >> strip_tac
        >> match_mp_tac (REWRITE_RULE[SUBSET_DEF] tyvars_TYPE_SUBST_mono)
        >> fs[tyvars_def]
      )
      >> rw[TYPE_SUBST_tyvars]
      >> qpat_x_assum `list_subset _ _` (imp_res_tac o REWRITE_RULE[list_subset_def,EVERY_MEM])
      >> fs[]
      >> Cases_on `LENGTH pqs <= SUC i`
      >- (
        rfs[LESS_OR_EQ]
        >> `LENGTH (COUNT_LIST (SUC i)) <= SUC i` by fs[LENGTH_COUNT_LIST]
        >> qunabbrev_tac `eta_i`
        >> qunabbrev_tac `eta_si`
        >> fs[EL_APPEND2,LENGTH_COUNT_LIST]
        >> qspecl_then [`x'`,`FV p`,`LAST rs'`,`EL i es`] mp_tac TYPE_SUBST_FILTER_MEM1
        >> fs[]
      )
      >> qunabbrev_tac `eta_i`
      >> qunabbrev_tac `eta_si`
      >> qmatch_goalsub_abbrev_tac `MAP eta_ (COUNT_LIST _)`
      >> `SUC i < LENGTH (MAP eta_ (COUNT_LIST (LENGTH pqs)))` by fs[LENGTH_COUNT_LIST]
      >> `SUC i < LENGTH pqs` by fs[]
      >> fs[EL_APPEND1,EL_COUNT_LIST,EL_MAP]
      >> qunabbrev_tac `eta_`
      >> qspecl_then [`x'`,`FV p`,`LAST rs'`] mp_tac TYPE_SUBST_FILTER_MEM1
      >> fs[]
    )
    >> `TYPE_SUBST (FILTER f s) (Tyvar x) = (Tyvar x)` by (
      qspecl_then [`x`,`FV rn_qn`,`s`,`[]`] mp_tac TYPE_SUBST_FILTER_MEM2
      >> fs[ETA_THM]
    )
    >> ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
    >> PURE_REWRITE_TAC[GSYM TYPE_SUBST_compose]
    >> ASM_REWRITE_TAC[]
    >> qunabbrev_tac `eta_i`
    >> match_mp_tac (GSYM TYPE_SUBST_FILTER_MEM2)
    >> `?y. MEM y r /\ TYPE_SUBST sigma (Tyvar y) = Tyvar x` by (
      qunabbrev_tac `rt_pi`
      >> qunabbrev_tac `rt`
      >> qmatch_asmsub_abbrev_tac `EL i (MAP sigma_map rs)`
      >> `i < LENGTH (MAP sigma_map rs)` by fs[]
      >> rfs[EL_MAP]
      >> qunabbrev_tac `sigma_map`
      >> rfs[GSYM LR_TYPE_SUBST_compose]
      >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST sigma ri_pi`
      >> `is_const_or_type ri_pi` by (
        qunabbrev_tac `ri_pi`
        >> match_mp_tac LR_TYPE_SUBST_type_preserving
        >> fs[]
      )
      >> qunabbrev_tac `sigma`
      >> drule MEM_FV_LR_TYPE_SUBST_renn_imp
      >> qmatch_asmsub_abbrev_tac `TYPE_SUBST sigma`
      >> rw[]
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> qunabbrev_tac `r`
      >> qunabbrev_tac `r0_p0`
      >> qunabbrev_tac `ri_pi`
      >> qunabbrev_tac `p_i`
      >> drule (REWRITE_RULE[EVERY_MEM,SUBSET_DEF] monotone_dep_seq_free_vars_FST_FST)
      >> disch_then (qspecl_then [`pqs`,`rs`] mp_tac)
      >> fs[]
      >> disch_then (qspecl_then [`0`,`i`] mp_tac)
      >> fs[]
    )
    >> qspecl_then [`list_complement r t`,`LIST_UNION t c`,`Tyvar x`] mp_tac ((REWRITE_RULE[NULL_FILTER,list_inter_def] o ONCE_REWRITE_RULE[NULL_list_inter_COMM]) renn_disj_dom_img4)
    >> fs[MEM_Tyvar_MAP_Tyvar,MEM_MAP,MEM_LIST_UNION,MEM_FILTER,list_complement_def]
    >> rfs[]
    >> disch_then match_mp_tac
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[GSYM list_complement_def]
    >> qspecl_then [`r`,`t`,`c`,`y`,`x`] assume_tac renn_compl_union_TYPE_SUBST_s
    >> rfs[]
    >> fs[MEM_MAP]
    >> first_x_assum (qspec_then `y` assume_tac)
    >> fs[]
    >> fs[]
  )
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST eta_i chaos`
  >> `chaos = LR_TYPE_SUBST (FILTER f s) rt_pi` by (
    qunabbrev_tac `chaos`
    >> qunabbrev_tac `rt`
    >> qunabbrev_tac `rt_pi`
    >> fs[LR_TYPE_SUBST_compose,TYPE_SUBST_compose,EL_MAP,MAP_MAP_o,o_DEF,ETA_THM]
    >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    >> fs[FUN_EQ_THM,PAIR_MAP,TYPE_SUBST_compose]
  )
  >> pop_assum (fn x => rw[x])
  >> qpat_x_assum `Abbrev_def (chaos = _)` kall_tac
  >> first_x_assum (qspec_then `i` mp_tac)
  >> fs[]
QED

(* Lemma 5.10 *)
Theorem mg_sol_ext2:
  !rs pqs p q s ctxt. (mg_sol_seq rs pqs
  /\ 0 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ p = LR_TYPE_SUBST s (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))))
  /\ wf_pqs [(p,q)]
  ==> ?r. mg_sol_seq ((MAP (λs. MAP (TYPE_SUBST r ## I) s ++ r) rs)++[[]]) (pqs++[(p,q)])
    /\ !x. MEM x (FV (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))))
      ==> TYPE_SUBST r (Tyvar x) = TYPE_SUBST s (Tyvar x)
Proof
  rw[]
  >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST s rn_qn`
  >> `LENGTH rs = LENGTH pqs` by fs[mg_sol_seq_def,sol_seq_def]
  >> `is_const_or_type rn_qn` by (
    unabbrev_all_tac
    >> `LENGTH rs = LENGTH pqs` by fs[mg_sol_seq_def,sol_seq_def]
    >> match_mp_tac LR_TYPE_SUBST_type_preserving
    >> `pqs <> []` by (fs[] >> fs[GSYM NOT_ZERO_LT_ZERO])
    >> dxrule LAST_EL
    >> disch_tac
    >> imp_res_tac MEM_EL
    >> rfs[mg_sol_seq_def,sol_seq_def,wf_pqs_def,EVERY_MEM]
    >> fs[ELIM_UNCURRY]
  )
  >> unabbrev_all_tac
  >> qmatch_goalsub_abbrev_tac `[p,q]`
  >> qspecl_then [`rs`,`pqs`,`p`,`q`,`s`,`ctxt`] mp_tac mg_sol_ext2
  >> `pqs <> []` by (CCONTR_TAC >> fs[])
  >> `rs <> []` by (CCONTR_TAC >> fs[])
  >> unabbrev_all_tac
  >> fs[GSYM LAST_EL]
  >> disch_then (mp_tac o REWRITE_RULE[GSYM LAST_EL])
  >> imp_res_tac LR_TYPE_SUBST_FILTER_tyvars
  >> fs[]
QED

(* Lemma 5.11, Kunčar 2015 *)
Theorem mg_sol_exists'[local]:
  !rs pqs r pq ctxt. (
  sol_seq (r::rs) (pq::pqs)
  /\ EVERY (UNCURRY (dependency ctxt)) (pq::pqs)
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt)
  ==> ?rs' k. mg_sol_seq rs' (pq::pqs)
    /\ path_starting_at ctxt k rs' (pq::pqs)
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> strip_tac
  >- (
    rw[]
    >> qexists_tac `[[]]`
    >> fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def,ELIM_UNCURRY]
    >> imp_res_tac LR_TYPE_SUBST_NIL
    >> qexists_tac `0`
    >> fs[path_starting_at_def,ELIM_UNCURRY,sol_seq_def,wf_pqs_def]
    >> rw[]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[renaming_def]
  )
  >> rw[SNOC_APPEND]
  >> Q.ISPEC_THEN `pqs` assume_tac (REWRITE_RULE[SNOC_APPEND] SNOC_CASES)
  >> fs[] >> rveq
  >- fs[sol_seq_def]
  >> `LENGTH rs = LENGTH l` by fs[sol_seq_def]
  >> qspecl_then [`r::rs++[x]`,`pq::l++[x']`,`LENGTH rs+1`] assume_tac sol_seq_TAKE
  >> fs[TAKE_APPEND1]
  >> rfs[TAKE_APPEND1]
  >> qpat_x_assum `!x. _` drule
  >> disch_then drule
  >> rw[]
  >> `LENGTH rs' = SUC (LENGTH l)` by fs[sol_seq_def,mg_sol_seq_def]
  >> qspecl_then [`pq::l++[x']`,`r::rs++[x]`,`rs'`,`ctxt`,`LENGTH rs'`,`k`] assume_tac sol_ex_non_orth
  >> rfs[TAKE_APPEND1,EL_APPEND1,EL_APPEND2,GSYM ADD1,is_instance_LR_eq]
  >> `wf_pqs [x']` by fs[sol_seq_def,wf_pqs_def]
  >> `rs' <> []` by (CCONTR_TAC >> fs[sol_seq_def,wf_pqs_def])
  >> dxrule LAST_EL
  >> disch_tac
  >- (
    qspecl_then [`rs'`,`pq::l`,`FST x'`,`SND x'`,`s`,`ctxt`] assume_tac mg_sol_ext2
    >> rfs[LAST_EL]
    >> fs[]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> qexists_tac `SUC (LENGTH l)`
    >> fs[path_starting_at_def]
    >> strip_tac
    >- fs[wf_pqs_def,EVERY_APPEND]
    >> strip_tac
    >- (
      fs[DROP_APPEND1]
      >> imp_res_tac EVERY_DROP
      >> fs[]
    )
    >> strip_tac
    >- (
      qexists_tac `[]`
      >> fs[renaming_def,EL_APPEND2,LR_TYPE_SUBST_NIL]
    )
    >> qmatch_goalsub_abbrev_tac `TAKE _ (l1 ++ l2)`
    >> Q.ISPECL_THEN [`l1`,`l2`] assume_tac TAKE_LENGTH_APPEND
    >> unabbrev_all_tac
    >> rfs[LENGTH_MAP]
    >> fs[TAKE_LENGTH_APPEND]
    >> rw[sol_seq_def,EL_MAP]
    >> `is_const_or_type (SND (EL i (pq::l))) /\ is_const_or_type (FST (EL i l))` by (
      fs[sol_seq_def]
      >> qpat_x_assum `wf_pqs (pq::l)` (assume_tac o REWRITE_RULE[wf_pqs_def])
      >> fs[EVERY_MEM,ELIM_UNCURRY]
      >> `i < LENGTH (pq::l)` by fs[]
      >> imp_res_tac EL_MEM
      >> fs[]
    )
    >> rw[GSYM LR_TYPE_SUBST_compose]
    >> qpat_x_assum `mg_sol_seq rs' _` (assume_tac o REWRITE_RULE[mg_sol_seq_def,sol_seq_def])
    >> fs[]
  )
  >> qspecl_then [`rs'`,`pq::l`,`FST x'`,`SND x'`,`s`,`ctxt`] assume_tac mg_sol_ext1
  >> rfs[LAST_EL]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> qexists_tac `k`
  >> fs[path_starting_at_def]
  >> strip_tac
  >- fs[wf_pqs_def,EVERY_APPEND]
  >> `k < LENGTH rs'` by fs[]
  >> strip_tac
  >- (
    ONCE_REWRITE_TAC[CONS_APPEND]
    >> PURE_REWRITE_TAC[APPEND_ASSOC]
    >> fs[EL_APPEND1,DROP_APPEND1,TAKE_APPEND1]
  )
  >> strip_tac
  >- (
    goal_assum (first_assum o mp_then Any mp_tac)
    >> ONCE_REWRITE_TAC[CONS_APPEND]
    >> PURE_REWRITE_TAC[APPEND_ASSOC]
    >> fs[EL_APPEND1,DROP_APPEND1,TAKE_APPEND1]
  )
  >> ONCE_REWRITE_TAC[CONS_APPEND]
  >> PURE_REWRITE_TAC[APPEND_ASSOC]
  >> fs[TAKE_APPEND1]
QED

(* Lemma 5.11, Kunčar 2015 *)
Theorem mg_sol_exists:
  !rs pqs ctxt. (
  0 < LENGTH rs
  /\ sol_seq rs pqs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt)
  ==> ?rs' k. mg_sol_seq rs' pqs
    /\ path_starting_at ctxt k rs' pqs
Proof
  rw[]
  >> `0 < LENGTH pqs` by fs[sol_seq_def]
  >> fs[GSYM NOT_NIL_EQ_LENGTH_NOT_0]
  >> drule (REWRITE_RULE[NULL_EQ] CONS)
  >> disch_then (fn x => PURE_ONCE_REWRITE_TAC[GSYM x] >> assume_tac x)
  >> ho_match_mp_tac mg_sol_exists'
  >> ASM_REWRITE_TAC[]
  >> qexists_tac `TL rs`
  >> qexists_tac `HD rs`
  >> fs[REWRITE_RULE[NULL_EQ] CONS]
QED

(* Definition 5.12 *)
Definition has_mg_sol_leq_def:
  has_mg_sol_leq pqs p =
  ?rs. mg_sol_seq rs pqs
    /\ is_instance_LR p (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs)))
    /\ is_const_or_type p
    /\ 0 < LENGTH rs
End

Definition has_mg_sol_geq_def:
  has_mg_sol_geq pqs p =
  ?rs. mg_sol_seq rs pqs
    /\ is_instance_LR (LR_TYPE_SUBST (LAST rs) (SND (LAST pqs))) p
    /\ is_const_or_type p
    /\ 0 < LENGTH rs
End

val _ = Parse.add_infix("≼", 401, Parse.NONASSOC)
val _ = Parse.overload_on("≼",``λpqs p. has_mg_sol_leq pqs p``)
val _ = Parse.add_infix("≽", 401, Parse.NONASSOC)
val _ = Parse.overload_on("≽",``λpqs p. has_mg_sol_geq pqs p``)

Theorem CONS_FRONT:
  !s. 1 < LENGTH s ==> HD s::TL (FRONT s) = FRONT s
Proof
  Induct
  >> rw[FRONT_DEF]
QED

Theorem EVERY_FRONT:
  !l P. ~NULL l /\ EVERY P l ==> EVERY P (FRONT l)
Proof
  Induct
  >> rw[FRONT_DEF,NULL_EQ]
QED

(* Corollary 5.13 *)
Theorem leq_geq_monotone_composable:
  !rs pqs ctxt.
  1 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ sol_seq rs pqs
  ==> has_mg_sol_leq (FRONT pqs) (FST (LAST pqs))
  \/ has_mg_sol_geq (FRONT pqs) (FST (LAST pqs))
Proof
  rw[]
  >> `LENGTH rs = LENGTH pqs` by fs[sol_seq_def]
  >> `1 < LENGTH pqs` by fs[]
  >> qspecl_then [`TL (FRONT rs)`,`TL (FRONT pqs)`,`HD rs`,`HD pqs`,`ctxt`] mp_tac mg_sol_exists'
  >> imp_res_tac CONS_FRONT
  >> ASM_REWRITE_TAC[]
  >> `~NULL pqs` by (CCONTR_TAC >> fs[NULL_EQ])
  >> `~NULL rs` by (CCONTR_TAC >> fs[NULL_EQ] >> rfs[])
  >> drule sol_seq_TAKE
  >> disch_then (qspec_then `PRE (LENGTH rs)` assume_tac)
  >> rfs[EVERY_FRONT,REWRITE_RULE[GSYM NULL_EQ] TAKE_PRE_LENGTH]
  >> rw[]
  >> qspecl_then [`pqs`,`rs`,`rs'`,`ctxt`,`PRE(LENGTH rs)`,`k`] mp_tac sol_ex_non_orth
  >> rw[REWRITE_RULE[GSYM NULL_EQ] TAKE_PRE_LENGTH,has_mg_sol_leq_def,has_mg_sol_geq_def]
  >- (
    DISJ2_TAC
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> imp_res_tac sol_seq_is_const_or_type
    >> `~NULL rs'` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def,NULL_EQ])
    >> `LENGTH rs' = PRE(LENGTH pqs)` by fs[mg_sol_seq_def,sol_seq_def,LENGTH_FRONT,NULL_EQ]
    >> `~NULL (FRONT pqs)` by (CCONTR_TAC >> Cases_on `pqs` >> fs[FRONT_CONS_EQ_NIL,NULL_EQ])
    >> `0 < PRE (LENGTH pqs)` by (CCONTR_TAC >> fs[])
    >> `PRE (LENGTH (FRONT pqs)) < LENGTH (FRONT pqs)` by (
      fs[REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
      >> fs[INV_PRE_LESS]
    )
    >> fs[REWRITE_RULE[GSYM NULL_EQ] LAST_EL,EL_FRONT,REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
  )
  >> DISJ1_TAC
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> imp_res_tac sol_seq_is_const_or_type
  >> `~NULL rs'` by (CCONTR_TAC >> fs[mg_sol_seq_def,sol_seq_def,NULL_EQ])
  >> `LENGTH rs' = PRE(LENGTH pqs)` by fs[mg_sol_seq_def,sol_seq_def,LENGTH_FRONT,NULL_EQ]
  >> `~NULL (FRONT pqs)` by (CCONTR_TAC >> Cases_on `pqs` >> fs[FRONT_CONS_EQ_NIL,NULL_EQ])
  >> `0 < PRE (LENGTH pqs)` by (CCONTR_TAC >> fs[])
  >> `PRE (LENGTH (FRONT pqs)) < LENGTH (FRONT pqs)` by (
    fs[REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
    >> fs[INV_PRE_LESS]
  )
  >> fs[REWRITE_RULE[GSYM NULL_EQ] LAST_EL,EL_FRONT,REWRITE_RULE[GSYM NULL_EQ]LENGTH_FRONT]
QED

Theorem leq_NOT_geq:
  !rs pqs ctxt.
  1 < LENGTH rs
  /\ EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ composable_dep ctxt
  /\ sol_seq rs pqs
  /\ ~has_mg_sol_leq (FRONT pqs) (FST (LAST pqs))
    ==> has_mg_sol_geq (FRONT pqs) (FST (LAST pqs))
Proof
  rw[EQ_IMP_THM]
  >> drule_then drule leq_geq_monotone_composable
  >> fs[]
QED

(* Definition 5.14 *)
Definition seq_asc_def:
  seq_asc pqs =
  (wf_pqs pqs /\ !i.
  0 < i /\ i < LENGTH pqs ==>
  has_mg_sol_leq (TAKE i pqs) (FST (EL i pqs)))
End

Theorem seq_asc_imp_mg_sol:
  !pqs. 1 < LENGTH pqs /\ seq_asc pqs
  ==> ?rs. mg_sol_seq rs (TAKE (PRE (LENGTH pqs)) pqs)
Proof
  rw[seq_asc_def,has_mg_sol_leq_def]
  >> `0 < PRE (LENGTH pqs)` by (Cases_on `pqs` >> fs[])
  >> first_x_assum (qspec_then `PRE (LENGTH pqs)` mp_tac)
  >> rw[]
  >> goal_assum (first_assum o mp_then Any mp_tac)
QED

(* Corollary 5.15 *)
Theorem seq_asc_mg_sol_path:
  !pqs ctxt n.
  EVERY (UNCURRY (dependency ctxt)) pqs
  /\ monotone (dependency ctxt)
  /\ seq_asc pqs
  /\ 0 < n /\ n < LENGTH pqs
  ==> ?rs. mg_sol_seq rs (TAKE n pqs)
  /\ path_starting_at ctxt 0 rs (TAKE n pqs)
Proof
  rw[seq_asc_def,has_mg_sol_leq_def]
  >> qpat_assum `!x. _` drule
  >> ASM_REWRITE_TAC[]
  >> strip_tac
  >> `LENGTH rs = n` by fs[mg_sol_seq_def,sol_seq_def]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> `!i. i <= n ==> mg_sol_seq (TAKE i rs) (TAKE i pqs)` by (
    Induct_on `n - i`
    >> rw[ADD_EQ_SUB]
    >- (
      imp_res_tac LESS_EQUAL_ANTISYM
      >> fs[]
      >> Q.ISPEC_THEN `rs` mp_tac TAKE_LENGTH_ID
      >> ASM_REWRITE_TAC[]
      >> fs[]
    )
    >> fs[ADD_EQ_SUB,LESS_OR_EQ]
    >> Cases_on `0 < i`
    >- (
      qpat_x_assum `!i. _ ==> ?rs. _` (qspec_then `i` mp_tac)
      >> `i <= LENGTH pqs` by fs[]
      >> drule_then drule EVERY_TAKE
      >> rw[is_instance_LR_eq,TAKE_LENGTH_ID]
      >> drule mg_sol_ext1
      >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST s (FST pq) = _`
      >> disch_then (qspecl_then [`FST pq`,`SND pq`,`s`,`ctxt`] mp_tac)
      >> `wf_pqs [pq]` by (
        fs[wf_pqs_def]
        >> `i < LENGTH (TAKE (LENGTH rs) pqs)` by fs[]
        >> qspec_then `rs` mp_tac mg_sol_seq_is_const_or_type
        >> disch_then (drule_then drule)
        >> `i < LENGTH rs` by fs[]
        >> fs[EL_TAKE,ELIM_UNCURRY]
      )
      >> ASM_REWRITE_TAC[]
      >> `TAKE i pqs ++ [pq] = TAKE (SUC i) pqs` by (
        fs[ADD1,TAKE_SUM,TAKE1_DROP]
      )
      >> first_x_assum (qspec_then `SUC i` mp_tac)
      >> rw[]
      >> rw[mg_sol_seq_def]
      >- (
        qpat_x_assum `mg_sol_seq (TAKE _ rs) (TAKE _ pqs)` (assume_tac o REWRITE_RULE[mg_sol_seq_def])
        >> fs[]
        >> drule sol_seq_TAKE
        >> fs[TAKE_TAKE]
      )
      >> qpat_x_assum `mg_sol_seq _ (TAKE i pqs)` (mp_tac o (REWRITE_RULE[mg_sol_seq_def]))
      >> strip_tac
      >> first_x_assum (qspec_then `rs''` mp_tac)
      >> rw[]
      >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST (EL _ rs''rs') (LR_TYPE_SUBST (EL _ rs') _)`
      >> qspecl_then [`rs'++[s]`,`TAKE (SUC i) rs`,`TAKE (SUC i) pqs`] assume_tac mg_solutions
      >> rfs[]
      >> qmatch_asmsub_abbrev_tac `LR_TYPE_SUBST (EL _ rs'rs) (LR_TYPE_SUBST (EL _ (TAKE _ rs)) _)`
      >> qexists_tac `MAP (λi. MAP (TYPE_SUBST (EL i rs''rs') ## I) (EL i rs'rs) ++ (EL i rs''rs')) (COUNT_LIST i)`
      >> rw[LENGTH_TAKE,LENGTH_COUNT_LIST,EL_TAKE]
      >> `i' < SUC i` by fs[]
      >> `i' < LENGTH rs'` by fs[sol_seq_def]
      >> NTAC 2 (first_x_assum (qspec_then `i'` mp_tac))
      >> rw[LENGTH_COUNT_LIST,el_map_count,EL_APPEND1,EL_TAKE,GSYM ADD1]
      >> rpt (qpat_x_assum `LR_TYPE_SUBST _ (LR_TYPE_SUBST _ _) = _` (assume_tac o GSYM))
      >> `i' < LENGTH pqs` by fs[sol_seq_def]
      >> drule sol_seq_is_const_or_type
      >> fs[LENGTH_TAKE]
      >> disch_then drule
      >> rw[EL_TAKE]
      >> qspec_then `FST (EL i' pqs)` assume_tac LR_TYPE_SUBST_type_preserving
      >> rfs[]
      >> rw[LR_TYPE_SUBST_compose]
    )
    >> fs[mg_sol_seq_def,sol_seq_def,wf_pqs_def]
  )
  >> rw[path_starting_at_def]
  >- fs[mg_sol_seq_def,sol_seq_def]
  >- (
    drule EVERY_TAKE
    >> disch_then match_mp_tac
    >> fs[]
  )
  >- (
    ONCE_REWRITE_TAC[GSYM EL]
    >> first_x_assum (qspec_then `1` mp_tac)
    >> fs[EL_TAKE]
    >> rw[]
    >> drule mg_sol_seq_is_const_or_type
    >> fs[LENGTH_TAKE]
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> rw[EL_TAKE]
    >> `mg_sol_seq [[]] (TAKE 1 pqs)` by (
      rw[mg_sol_seq_def]
      >- fs[sol_seq_def,mg_sol_seq_def]
      >- (
        ONCE_REWRITE_TAC[GSYM EL]
        >> fs[EL_TAKE,LR_TYPE_SUBST_NIL,sol_seq_def]
        >> rfs[LENGTH_TAKE]
        >> goal_assum (first_assum o mp_then Any mp_tac)
        >> fs[]
      )
    )
    >> qspecl_then [`[[]]`,`TAKE 1 rs`,`TAKE 1 pqs`] mp_tac mg_solutions
    >> fs[]
    >> ONCE_REWRITE_TAC[GSYM EL]
    >> rw[EL_TAKE,LR_TYPE_SUBST_NIL,EVERY_MEM]
    >> `0 < LENGTH es` by fs[]
    >> drule EL_MEM
    >> strip_tac
    >> qpat_x_assum `!x. MEM _ _ ==> _` imp_res_tac
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[EL]
  )
  >> fs[sol_seq_def,wf_pqs_def]
QED

(* Definition 5.14, for llists *)
Definition Lseq_asc_def:
  Lseq_asc pqs =
  !pre. 1 < LENGTH pre /\ LPREFIX (fromList pre) pqs
  ==> has_mg_sol_leq (FRONT pre) (FST (LAST pre))
End

Theorem every_LAPPEND:
  !P x y. every P (LAPPEND x y) ==> every P x
Proof
  strip_tac
  >> qspecl_then [`P`,`λx. ?y. every P (LAPPEND x y)`] assume_tac every_coind
  >> fs[PULL_EXISTS]
QED

Theorem LAPPEND_CONS:
  !x h t. LAPPEND x (h:::t) = LAPPEND (LAPPEND x [|h|]) t
Proof
  fs[LAPPEND_ASSOC]
QED

(* by Johannes *)
Theorem exists_thm_strong:
  exists P ll ⇔ ∃n a t l. LDROP n ll = SOME (a:::t) ∧ P a /\
                           LTAKE n ll = SOME l /\ EVERY ($~ o P) l
Proof
  simp[exists_LDROP,EQ_IMP_THM] >>
  reverse conj_tac >- metis_tac[] >>
  disch_then (strip_assume_tac o Ho_Rewrite.PURE_ONCE_REWRITE_RULE[whileTheory.LEAST_EXISTS]) >>
  rename1 `LDROP n` >>
  goal_assum drule >>
  rw[] >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`a`,`t`,`ll`,`n`] >>
  Induct >- rw[] >>
  Cases >>
  rw[] >>
  `~P h`
    by(first_x_assum(qspec_then `0` mp_tac) >>
       impl_tac >- simp[] >>
       disch_then(qspecl_then [`h`,`t`] mp_tac) >> simp[]) >>
  first_x_assum (drule_then drule) >>
  impl_tac >- (rw[] >> first_x_assum(qspec_then `SUC n'` mp_tac) >> rw[]) >>
  rw[PULL_EXISTS]
QED

(* by Johannes Åman Pohjola *)
val LFILTER_fromList = Q.prove(`
  !l. LFILTER f (fromList l) = fromList(FILTER f l)`,
  Induct >> rw[]);

(* by Johannes Åman Pohjola *)
Theorem LFILTER_EQ_CONS:
  LFILTER P ll = h:::t
  ==> ?l ll'. ll = LAPPEND (fromList l) (h:::ll') /\
              EVERY ($~ o P) l /\ P h /\
              LFILTER P ll' = t
Proof
  strip_tac >>
  `exists P ll` by(fs[Once LFILTER,CaseEq "bool"]) >>
  fs[exists_thm_strong] >>
  `ll = LAPPEND (fromList l) (a:::t')`
    by(reverse(Cases_on `LFINITE ll`)
       >- (drule_then (qspec_then `n` (fn thm => PURE_ONCE_REWRITE_TAC[GSYM thm])) (CONJUNCT1 LTAKE_DROP) >>
           simp[]) >>
       `n <= THE(LLENGTH ll)` by(fs[LFINITE_LLENGTH] >> metis_tac[LDROP_SOME_LLENGTH]) >>
       drule_all_then (fn thm => PURE_ONCE_REWRITE_TAC[GSYM thm]) (CONJUNCT2 LTAKE_DROP) >>
       simp[]) >>
  BasicProvers.VAR_EQ_TAC >>
  fs[LFINITE_fromList,LFILTER_APPEND,LFILTER_fromList] >>
  `FILTER P l = []` by(fs[listTheory.FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  fs[] >> rpt(BasicProvers.VAR_EQ_TAC) >>
  metis_tac[]
QED

(* by Johannes Åman Pohjola *)
Theorem every_LFILTER:
  !ll P. every P (LFILTER P ll)
Proof
  rpt strip_tac >>
  `!ll. (?ll'. ll = LFILTER P ll') ==> every P ll
  `
    by(ho_match_mp_tac every_coind >>
       rw[] >> first_x_assum(ASSUME_TAC o GSYM) >>
       drule_then strip_assume_tac LFILTER_EQ_CONS >>
       fs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem every_LAPPEND_SINGLETON:
  !P h x. LFINITE x /\ every P (LAPPEND x [|h|]) ==> P h
Proof
  fs[GSYM AND_IMP_INTRO]
  >> NTAC 2 strip_tac
  >> ho_match_mp_tac LFINITE_STRONG_INDUCTION
  >> fs[]
QED

Theorem every_LAPPEND2:
  !P x y. LFINITE x /\ every P (LAPPEND x y) ==> every P y
Proof
  NTAC 2 strip_tac
  >> qspecl_then [`P`,`λy. ?x. LFINITE x /\ every P (LAPPEND x y)`] assume_tac every_strong_coind
  >> fs[PULL_EXISTS]
  >> pop_assum match_mp_tac
  >> fs[Once LAPPEND_CONS]
  >> rw[]
  >> imp_res_tac every_LAPPEND
  >- (
    match_mp_tac every_LAPPEND_SINGLETON
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> rw[DISJ_EQ_IMP]
  >> first_x_assum (qspec_then `LAPPEND x [|h|]` assume_tac)
  >> rfs[LFINITE_APPEND,Once LAPPEND_CONS]
QED

Theorem every_every_LFILTER:
  !ll P Q. every Q ll ==> every Q (LFILTER P ll)
Proof
  rpt strip_tac
  >> `!ll. (?ll'. ll = LFILTER P ll' /\ every Q ll') ==> every Q ll` by (
    ho_match_mp_tac every_coind
    >> rw[] >> qpat_x_assum `_:::_ = _`(ASSUME_TAC o GSYM)
    >> drule_then strip_assume_tac LFILTER_EQ_CONS
    >> rveq
    >> rename1 `LAPPEND (fromList l) (h:::llll)`
    >> qspec_then `l` assume_tac LFINITE_fromList
    >> drule_all every_LAPPEND2
    >> rw[every_thm]
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> metis_tac[]
QED

Theorem every_LPREFIX:
  !pre s. LPREFIX pre s /\ every P s ==> every P pre
Proof
  rw[LPREFIX_APPEND]
  >> imp_res_tac every_LAPPEND
QED

Theorem every_fromList:
  !P ls. every P (fromList ls) ==> EVERY P ls
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> fs[]
QED

Theorem every_LPREFIX_EVERY:
  !pre s P. LPREFIX (fromList pre) s
  /\ every P s ==> EVERY P pre
Proof
  rw[]
  >> match_mp_tac every_fromList
  >> imp_res_tac every_LPREFIX
QED

Theorem every_LTAKE_EVERY:
  !i P s. every P s /\ ~LFINITE s
  ==>  EVERY P (THE (LTAKE i s))
Proof
  rw[]
  >> match_mp_tac every_fromList
  >> match_mp_tac every_LAPPEND
  >> imp_res_tac LTAKE_DROP
  >> qexists_tac `THE (LDROP i s)`
  >> fs[]
QED

Theorem every_LNTH:
  !P s i. every P s /\ ~LFINITE s
  ==> P (THE (LNTH i s))
Proof
  rw[]
  >> imp_res_tac infinite_lnth_some
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[every_def,exists_LNTH]
  >> first_x_assum (qspecl_then [`i`,`x`] assume_tac)
  >> rfs[]
QED

Theorem WOP_eq[local]:
  ∀P. (∃(n:num). P n) <=> ∃n. P n ∧ ∀m. m < n ⇒ ¬P m
Proof
  rw[EQ_IMP_THM,WOP]
  >> goal_assum (first_assum o mp_then Any mp_tac)
QED

Theorem NOT_LFINITE_LDROP:
  !ll k. ~LFINITE ll ==> ~LFINITE (THE (LDROP k ll))
Proof
  rw[LFINITE,infinite_lnth_some]
  >> first_assum (qspec_then `n+k` assume_tac)
  >> fs[]
  >> drule LNTH_LDROP
  >> first_x_assum (qspec_then `n` assume_tac)
  >> fs[LNTH_ADD]
QED

Theorem every_LNTH:
  !n e P is. every P is /\ LNTH n is = SOME e ==> P e
Proof
  rw[every_def,exists_LNTH]
  >> first_x_assum (qspecl_then [`n`,`e`] mp_tac)
  >> fs[]
QED

Theorem every_LDROP:
  !ll k P. ~LFINITE ll /\ every P ll ==> every P (THE (LDROP k ll))
Proof
  rw[]
  >> `every P (LAPPEND (fromList (THE (LTAKE k ll))) (THE (LDROP k ll)))` by (
    qspecl_then [`k`,`ll`] mp_tac (CONJUNCT1 LTAKE_DROP)
    >> fs[NOT_LFINITE_NO_LENGTH]
  )
  >> match_mp_tac every_LAPPEND2
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[LFINITE_fromList]
QED

Theorem EL_LTAKE_LDROP_LNTH:
  !s i j k. ~LFINITE s /\ i < j
  ==>
  EL i (THE (LTAKE j (THE (LDROP k s)))) = THE (LNTH (k+i) s)
Proof
  rpt strip_tac
  >> fs[LNTH_ADD]
  >> `IS_SOME (LDROP k s)` by (
    fs[IS_SOME_EXISTS]
    >> match_mp_tac NOT_LFINITE_DROP
    >> ASM_REWRITE_TAC[]
  )
  >> `IS_SOME (LTAKE j (THE (LDROP k s)))` by (
    fs[IS_SOME_EXISTS]
    >> match_mp_tac NOT_LFINITE_TAKE
    >> match_mp_tac NOT_LFINITE_DROP_LFINITE
    >> goal_assum (first_assum o mp_then Any mp_tac)
    >> fs[]
  )
  >> fs[IS_SOME_EXISTS]
  >> drule LTAKE_LNTH_EL
  >> disch_then imp_res_tac
  >> rfs[option_CLAUSES]
QED

Theorem FRONT_TAKE_PRE:
  !ls. ~NULL ls ==> FRONT ls = TAKE (PRE (LENGTH ls)) ls
Proof
  rw[NULL_EQ]
  >> qspecl_then [`PRE (LENGTH ls)`,`FRONT ls`] mp_tac TAKE_APPEND1
  >> drule LENGTH_FRONT
  >> disch_then (fn x => fs[GSYM x])
  >> disch_then (qspec_then `[LAST ls]` (mp_tac o GSYM))
  >> imp_res_tac APPEND_FRONT_LAST
  >> fs[]
QED

Theorem LPREFIX_TAKE_EL_LTAKE:
  !pre pqs l. LPREFIX (fromList pre) pqs
  /\ ~LFINITE pqs
  /\ l < LENGTH pre
  ==> THE (LTAKE l pqs) = TAKE l pre
  /\ THE (LNTH l pqs) = EL l pre
Proof
  rw[]
  >- (
    fs[LPREFIX_APPEND]
    >> qspec_then `pre` assume_tac LTAKE_fromList
    >> drule LTAKE_TAKE_LESS
    >> disch_then (qspec_then `l` mp_tac)
    >> qspecl_then [`l`] mp_tac LTAKE_LAPPEND1
    >> fs[IS_SOME_EXISTS]
  )
  >> imp_res_tac NOT_LFINITE_TAKE
  >> fs[LNTH_fromList,LNTH_LAPPEND,LPREFIX_APPEND]
QED

Theorem LPREFIX_FRONT_LAST_LTAKE:
  !pre pqs. LPREFIX (fromList pre) pqs
  /\ ~LFINITE pqs
  /\ 1 < LENGTH pre
  ==> THE (LTAKE (PRE (LENGTH pre)) pqs) = FRONT pre
  /\ THE (LNTH (PRE (LENGTH pre)) pqs) = LAST pre
Proof
  rpt gen_tac
  >> disch_tac
  >> `pre <> []` by (
    fs[NOT_NIL_EQ_LENGTH_NOT_0]
  )
  >> fs[LAST_EL,REWRITE_RULE[NULL_EQ] FRONT_TAKE_PRE]
  >> match_mp_tac LPREFIX_TAKE_EL_LTAKE
  >> fs[]
QED

Theorem LPREFIX_TAKE_LPREFIX:
  !pre pqs l. LPREFIX (fromList pre) pqs
  /\ ~LFINITE pqs
  ==> LPREFIX (fromList (TAKE l pre)) pqs
Proof
  rw[]
  >> fs[LPREFIX_APPEND]
  >> qspecl_then [`l`,`pre`] mp_tac TAKE_DROP
  >> disch_then (fn x => CONV_TAC (ONCE_DEPTH_CONV (LHS_CONV (PURE_ONCE_REWRITE_CONV[GSYM x]))))
  >> fs[GSYM LAPPEND_fromList]
  >> fs[LAPPEND_ASSOC]
  >> qmatch_goalsub_abbrev_tac `LAPPEND _ (LAPPEND a b)`
  >> qexists_tac `LAPPEND a b`
  >> fs[]
QED

Theorem LPREFIX_FRONT_LPREFIX:
  !pre pqs. LPREFIX (fromList pre) pqs
  /\ ~LFINITE pqs
  /\ 1 < LENGTH pre
  ==> LPREFIX (fromList (FRONT pre)) pqs
Proof
  rw[]
  >> `~NULL pre` by (
    fs[NULL_EQ,NOT_NIL_EQ_LENGTH_NOT_0]
  )
  >> fs[FRONT_TAKE_PRE]
  >> match_mp_tac LPREFIX_TAKE_LPREFIX
  >> fs[]
QED

Theorem IS_PREFIX_LENGTH:
  !z x y. IS_PREFIX z x /\ IS_PREFIX z y /\ LENGTH x = LENGTH y ==> x = y
Proof
  Induct
  >> rw[]
  >> Cases_on `x`
  >> Cases_on `y`
  >> fs[]
QED

Theorem NOT_LFINITE_LPREFIX_THE_LTAKE:
  !ll l. ~LFINITE ll ==> LPREFIX (fromList(THE (LTAKE l ll))) ll
Proof
  rw[LPREFIX_APPEND]
  >> drule (CONJUNCT1 LTAKE_DROP)
  >> disch_then (qspec_then `l` assume_tac)
  >> goal_assum (mp_tac o GSYM)
  >> goal_assum (first_assum o mp_then Any mp_tac)
QED

Theorem mg_sol_seq_DROP:
  !rs pqs i. mg_sol_seq rs pqs
  /\ i <= LENGTH rs
  ==> sol_seq (DROP i rs) (DROP i pqs)
Proof
  rw[]
  >> match_mp_tac sol_seq_DROP
  >> fs[mg_sol_seq_def]
QED

Theorem FRONT_LAST_TAKE_SUC:
  !ls i. i < LENGTH ls
  ==> FRONT (TAKE (SUC i) ls) = TAKE i ls /\ LAST (TAKE (SUC i) ls) = EL i ls
Proof
  rw[]
  >> `~NULL (TAKE (SUC i) ls)` by fs[NULL_EQ,NOT_NIL_EQ_LENGTH_NOT_0]
  >> imp_res_tac FRONT_TAKE_PRE
  >> imp_res_tac (REWRITE_RULE[GSYM NULL_EQ] LAST_EL)
  >> rfs[LENGTH_TAKE,TAKE_TAKE,EL_TAKE]
QED

Theorem every_LNTH_eq:
  !P ll. ~LFINITE ll /\ every P ll
  <=> !n. ?e. LNTH n ll = SOME e /\ P e
Proof
  rw[EQ_IMP_THM,every_def,exists_LNTH,DISJ_EQ_IMP,infinite_lnth_some]
  >> rpt (first_x_assum (qspec_then `n` assume_tac))
  >> fs[]
  >> qpat_x_assum `SOME _ = _` (assume_tac o GSYM)
  >> fs[]
QED

Theorem LNTH_LUNFOLD_index_shift:
  !i k. LNTH i (LUNFOLD (λn. SOME (n+1,n)) (SUC k))
  = LNTH (SUC i) (LUNFOLD (λn. SOME (n+1,n)) k)
Proof
  Induct
  >> fs[]
  >> first_x_assum (qspec_then `SUC k` assume_tac)
  >> fs[ADD1]
QED

Theorem LDROP_LUNFOLD_LGENLIST[local]:
  !i:num. THE (LDROP i (LGENLIST I NONE))
  = LUNFOLD (λn. SOME (n+1,n)) i
Proof
  Induct
  >- fs[LGENLIST_def]
  >> fs[ADD1,LDROP_ADD]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac NOT_LFINITE_DROP
  >> first_x_assum (qspec_then `i` mp_tac)
  >> rw[]
  >> fs[option_CLAUSES]
  >> CONV_TAC (LHS_CONV (PURE_ONCE_REWRITE_CONV[LUNFOLD]))
  >> fs[]
QED

Theorem LGENLIST_num:
  !i. LNTH i (LGENLIST I NONE) = SOME i
Proof
  rw[]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> fs[infinite_lnth_some]
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
  >> imp_res_tac LNTH_LDROP
  >> qspec_then `i` assume_tac LDROP_LUNFOLD_LGENLIST
  >> fs[option_CLAUSES]
QED

Theorem LNTH_LFILTER1[local]:
  !k ll e. ~LFINITE ll /\ LNTH k ll = SOME e /\ P e
  ==> ?n. LNTH n (LFILTER P ll) = SOME e
Proof
  rw[]
  >> drule (CONJUNCT1 LTAKE_DROP)
  >> disch_then (qspec_then `k` (fn x => ONCE_REWRITE_TAC[GSYM x]))
  >> fs[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList]
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 _`
  >> qexists_tac `THE (LLENGTH ll1)`
  >> imp_res_tac LNTH_LDROP
  >> fs[Abbr`ll1`,LNTH_LAPPEND]
  >> qmatch_asmsub_abbrev_tac `LHD ll1`
  >> Cases_on `ll1`
  >> fs[]
QED

Theorem LNTH_LFILTER:
  !k ll e. ~LFINITE ll /\ LNTH k ll = SOME e /\ P e
  ==> ?n. LNTH n (LFILTER P ll) = SOME e /\ n <= k
Proof
  rw[]
  >> drule (CONJUNCT1 LTAKE_DROP)
  >> disch_then (qspec_then `k` (fn x => ONCE_REWRITE_TAC[GSYM x]))
  >> fs[LFILTER_APPEND,LFINITE_fromList,LFILTER_fromList]
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 _`
  >> qexists_tac `THE (LLENGTH ll1)`
  >> imp_res_tac LNTH_LDROP
  >> fs[Abbr`ll1`,LNTH_LAPPEND]
  >> qmatch_asmsub_abbrev_tac `LHD ll1`
  >> Cases_on `ll1`
  >> fs[]
  >> qmatch_goalsub_abbrev_tac `FILTER P l`
  >> `k = LENGTH l` by (
    drule NOT_LFINITE_TAKE
    >> disch_then (qspec_then `k` assume_tac)
    >> fs[Abbr`l`,LLENGTH_fromList]
    >> imp_res_tac LTAKE_LENGTH
  )
  >> fs[LENGTH_FILTER_LEQ]
QED

Theorem LFILTER_num_pred:
  !P e. P e = (?n. LNTH n (LFILTER P (LGENLIST I NONE)) = SOME e)
Proof
  rw[EQ_IMP_THM]
  >> qspecl_then [`LGENLIST I NONE`,`P`] assume_tac every_LFILTER
  >> imp_res_tac every_LNTH
  >> qspec_then `e` assume_tac LGENLIST_num
  >> match_mp_tac LNTH_LFILTER1
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[LFINITE_LGENLIST]
QED

Theorem LENGTH_num:
  !i. LENGTH (THE (LTAKE i (LGENLIST I NONE))) = i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac NOT_LFINITE_TAKE
  >> rw[]
  >> first_x_assum (qspec_then `i` assume_tac)
  >> fs[]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem LTAKE_GENLIST_num:
  !i f. THE (LTAKE i (LGENLIST I NONE)) = GENLIST I i
Proof
  Induct
  >> rw[LTAKE_SNOC_LNTH,GENLIST]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac infinite_lnth_some
  >> imp_res_tac NOT_LFINITE_TAKE
  >> rpt (first_x_assum (qspec_then `i` assume_tac))
  >> fs[LGENLIST_num,option_CLAUSES]
QED

Theorem LDROP_GENLIST_NOT_SOME:
  !n i. LNTH (SUC n) (THE (LDROP i (LGENLIST I NONE))) <> SOME i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> rw[]
  >> qspec_then `i + SUC n` assume_tac LGENLIST_num
  >> imp_res_tac NOT_LFINITE_DROP
  >> qspecl_then [`i`,`SUC n`,`LGENLIST I NONE`] mp_tac LNTH_ADD
  >> rw[]
  >> fs[]
QED

Theorem LDROP_SUC_LGENLIST_NOT_SOME:
  !n i. LNTH n (THE (LDROP (SUC i) (LGENLIST I NONE))) <> SOME i
Proof
  `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> rw[]
  >> qspec_then `SUC i + n` assume_tac LGENLIST_num
  >> imp_res_tac NOT_LFINITE_DROP
  >> qspecl_then [`SUC i`,`n`,`LGENLIST I NONE`] mp_tac LNTH_ADD
  >> rw[]
  >> fs[]
QED

Theorem exists_every:
  !P ll. exists P ll = ~every ($~ o P) ll
Proof
  fs[every_def,NOT_CLAUSES,o_DEF,ETA_THM]
QED

Theorem every_LDROP:
  !P ll. every P ll <=> !n a t. LDROP n ll = SOME (a:::t) ==> P a
Proof
  rw[DISJ_EQ_IMP,every_def,exists_LDROP]
QED

Theorem NOT_LFINITE_LFILTER:
  !P ll. ~LFINITE (LFILTER P ll) ==> ~LFINITE ll
Proof
  Induct_on `THE(LLENGTH ll)`
  >> rpt gen_tac
  >> strip_tac
  >> gen_tac
  >> match_mp_tac MONO_NOT
  >- (
    rw[LFINITE_LLENGTH]
    >> fs[option_CLAUSES]
    >> rveq
    >> imp_res_tac LLENGTH_0
    >> fs[]
  )
  >> Cases_on `ll`
  >> fs[]
  >> rw[]
  >> imp_res_tac LFINITE_LLENGTH
  >> first_x_assum (qspec_then `t` assume_tac)
  >> rfs[option_CLAUSES]
  >> fs[]
QED

Theorem NOT_LFINITE_LENGTH:
  !ll k. ~LFINITE ll ==> LENGTH (THE (LTAKE k ll)) = k
Proof
  rw[]
  >> drule NOT_LFINITE_TAKE
  >> disch_then (qspec_then `k` assume_tac)
  >> fs[]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem LFINITE_LFILTER:
  !P ll. LFINITE ll ==> LFINITE (LFILTER P ll)
Proof
  rw[]
  >> CCONTR_TAC
  >> imp_res_tac NOT_LFINITE_LFILTER
QED

Theorem LLENGTH_LFILTER_LEQ:
  !P ll. LFINITE ll ==>
  THE(LLENGTH (LFILTER P ll)) <= THE (LLENGTH ll)
Proof
  Induct_on `THE(LLENGTH ll)`
  >- (
    rw[LFINITE_LLENGTH]
    >> fs[option_CLAUSES]
    >> rveq
    >> imp_res_tac LLENGTH_0
    >> fs[]
  )
  >> Cases_on `ll`
  >> fs[]
  >> rw[]
  >> drule LFINITE_LFILTER
  >> disch_then (qspec_then `P` assume_tac)
  >> imp_res_tac LFINITE_LLENGTH
  >> rw[]
  >> first_x_assum (qspec_then `t` assume_tac)
  >> rfs[option_CLAUSES]
  >> fs[]
  >> rw[]
  >> first_x_assum (qspec_then `P` mp_tac)
  >> fs[option_CLAUSES]
QED

Theorem LNTH_LFILTER_pred:
  !n P ll. LNTH n (LFILTER P ll) = SOME x ==> P x
Proof
  rw[]
  >> match_mp_tac every_LNTH
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[every_LFILTER]
QED

Theorem every_CONJ_eq:
  !P Q ll:'a llist. every P ll /\ every Q ll <=> every (λx. P x /\ Q x) ll
Proof
  rw[EQ_IMP_THM]
  >- (
    qspecl_then [`λx. P x /\ Q x`,`λx. every P x /\ every Q x`] assume_tac every_strong_coind
    >> fs[]
  )
  >- (
    qspecl_then [`P`,`λx. every (λx. P x /\ Q x) x`] assume_tac every_strong_coind
    >> fs[]
  )
  >- (
    qspecl_then [`Q`,`λx. every (λx. P x /\ Q x) x`] assume_tac every_strong_coind
    >> fs[]
  )
QED

Theorem every_F:
  !ll. every (λx. F) ll <=> ll = [||]
Proof
  rw[EQ_IMP_THM]
  >> Cases_on `ll`
  >> fs[]
QED

Theorem LFILTER_LFILTER:
  !P ll. LFILTER P (LFILTER P ll) = LFILTER P ll
Proof
  rw[]
  >> ONCE_REWRITE_TAC[LLIST_BISIMULATION0]
  >> qexists_tac `λx y. every P x /\ every P y /\ x = LFILTER P y`
  >> rw[every_LFILTER]
  >> Cases_on `ll4`
  >> fs[LFILTER_EQ_NIL]
QED

Theorem LNTH_LFILTER_LNTH:
  !n P ll e. LNTH n (LFILTER P ll) = SOME e
  ==> ?k. LNTH n (LFILTER P ll) = LNTH k ll /\ n <= k /\ P (THE (LNTH k ll))
Proof
  Induct
  >> rw[IS_SOME_EXISTS]
  >> imp_res_tac LNTH_LFILTER_pred
  >- (
    Cases_on `LFILTER P ll`
    >> fs[]
    >> imp_res_tac LFILTER_EQ_CONS
    >> qexists_tac `LENGTH l`
    >> rveq
    >> fs[LNTH_LAPPEND]
  )
  >> Cases_on `LFILTER P ll`
  >> fs[]
  >> imp_res_tac LFILTER_EQ_CONS
  >> first_x_assum (qspecl_then [`P`,`ll'`] mp_tac)
  >> rw[IS_SOME_EXISTS,LNTH_LAPPEND]
  >> qexists_tac `LENGTH l + SUC k`
  >> fs[]
QED

Theorem LNTH_FILTER_num_pred_position:
  !i n P. LNTH n (LFILTER P (LGENLIST I NONE)) = SOME i
  ==> n <= i
Proof
  rw[]
  >> `~LFINITE (LGENLIST I NONE)` by fs[LFINITE_LGENLIST]
  >> imp_res_tac LFILTER_num_pred
  >> qspec_then `SUC i` assume_tac LGENLIST_num
  >> qspec_then `i` assume_tac LGENLIST_num
  >> qpat_x_assum `LNTH n _ = _` mp_tac
  >> drule_all (CONJUNCT1 LTAKE_DROP)
  >> disch_then (qspec_then `SUC i` mp_tac)
  >> disch_then (fn x => ONCE_REWRITE_TAC[GSYM x])
  >> fs[LFILTER_APPEND,LFINITE_fromList,LNTH_LAPPEND,LFILTER_fromList]
  >> FULL_CASE_TAC
  >- (
    qmatch_asmsub_abbrev_tac `FILTER P l`
    >> qspecl_then [`P`,`l`] assume_tac LENGTH_FILTER_LEQ
    >> fs[Abbr`l`,LENGTH_num]
  )
  >> fs[NOT_LESS]
  >> rw[]
  >> imp_res_tac LNTH_LFILTER_LNTH
  >> fs[LDROP_SUC_LGENLIST_NOT_SOME]
QED

Theorem LNTH_LNTH_SUC_NOT_LFINITE:
  !n P ll e e'. ~LFINITE (LFILTER P ll)
  /\ LNTH n (LFILTER P ll) = SOME e
  /\ LNTH (SUC n) (LFILTER P ll) = SOME e'
  ==> ?ll1 ll2. LFILTER P ll = LAPPEND ll1 (e:::e':::ll2)
Proof
  rw[]
  >> imp_res_tac LNTH_LDROP
  >> qmatch_asmsub_abbrev_tac `LNTH _ FPL`
  >> qspecl_then [`n`,`FPL`] mp_tac (CONJUNCT1 LTAKE_DROP)
  >> fs[]
  >> disch_then (fn x => PURE_ONCE_REWRITE_TAC[GSYM x])
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 _`
  >> qexists_tac `ll1`
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 ll2`
  >> Cases_on `ll2`
  >> fs[]
  >> `t = THE (LDROP (SUC n) FPL)` by (
    fs[markerTheory.Abbrev_def,LDROP_SUC]
    >> drule NOT_LFINITE_DROP
    >> disch_then (qspec_then `n` assume_tac)
    >> fs[OPTION_BIND_def,option_CLAUSES]
    >> qpat_x_assum `_:::_ = _` (assume_tac o GSYM)
    >> rfs[option_CLAUSES]
  )
  >> Cases_on `t`
  >- (qpat_x_assum `[||] = _` (assume_tac o GSYM) >> fs[])
  >> qpat_x_assum `_:::_ = _` (assume_tac o GSYM)
  >> qexists_tac `t'`
  >> fs[]
QED

Theorem LNTH_LNTH_SUC_LFINITE:
  !n P ll e e'. LFINITE (LFILTER P ll)
  /\ SUC n <= THE (LLENGTH (LFILTER P ll))
  /\ LNTH n (LFILTER P ll) = SOME e
  /\ LNTH (SUC n) (LFILTER P ll) = SOME e'
  ==> ?ll1 ll2. LFILTER P ll = LAPPEND ll1 (e:::e':::ll2)
Proof
  rw[]
  >> imp_res_tac LNTH_LDROP
  >> qmatch_asmsub_abbrev_tac `LNTH _ FPL`
  >> qspecl_then [`n`,`FPL`] mp_tac (CONJUNCT2 LTAKE_DROP)
  >> fs[]
  >> disch_then (fn x => PURE_ONCE_REWRITE_TAC[GSYM x])
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 _`
  >> qexists_tac `ll1`
  >> qmatch_goalsub_abbrev_tac `LAPPEND ll1 ll2`
  >> Cases_on `ll2`
  >> fs[]
  >> `t = THE (LDROP (SUC n) FPL)` by (
    fs[markerTheory.Abbrev_def,LDROP_SUC]
    >> drule LFINITE_DROP
    >> disch_then (qspec_then `n` assume_tac)
    >> rfs[]
    >> qpat_x_assum `_:::_ = _` (assume_tac o GSYM)
    >> rfs[option_CLAUSES]
  )
  >> Cases_on `t`
  >- (qpat_x_assum `[||] = _` (assume_tac o GSYM) >> fs[])
  >> qpat_x_assum `_:::_ = _` (assume_tac o GSYM)
  >> qexists_tac `t'`
  >> fs[]
QED

Theorem LFINITE_LNTH_SOME:
  !n ll. n < THE (LLENGTH ll) /\ LFINITE ll
  ==> ?e. LNTH n ll = SOME e
Proof
  rw[]
  >> drule LFINITE_TAKE
  >> disch_then (qspec_then `SUC n` mp_tac)
  >> rw[]
  >> drule LTAKE_LNTH_EL
  >> disch_then (qspec_then `n` mp_tac)
  >> rw[]
QED


Definition infin_or_leq_def:
  infin_or_leq ll k P =
    (~LFINITE ll \/ (LFINITE ll /\ k <= THE (LLENGTH ll) /\ P))
End

Theorem infin_or_leq_eq:
  !ll k. infin_or_leq ll k T = (LFINITE ll ==> k <= THE (LLENGTH ll))
Proof
  rw[infin_or_leq_def,EQ_IMP_THM]
  >> fs[DISJ_EQ_IMP]
QED

Theorem not_infin_or_leq[simp]:
  !ll k. ~infin_or_leq ll (SUC k) T = (LFINITE ll /\ THE (LLENGTH ll) <= k)
Proof
  rw[infin_or_leq_def,EQ_IMP_THM,NOT_LESS]
QED

Theorem infin_or_leq_imp:
  !ll k l. infin_or_leq ll l T /\ k <= l ==> infin_or_leq ll k T
Proof
  rw[infin_or_leq_def]
  >> fs[]
QED

Theorem infin_or_leq_SUC_imp:
  !ll k l. infin_or_leq ll (SUC k) T ==> infin_or_leq ll k T
Proof
  rw[] >> imp_res_tac infin_or_leq_imp >> fs[]
QED

Theorem infin_or_leq_imp1:
  !ll k P Q. infin_or_leq ll k P /\ P ==> Q ==> infin_or_leq ll k Q
Proof
  rw[infin_or_leq_def] >> fs[]
QED

Theorem infin_or_leq_imp2:
  !ll k l. infin_or_leq ll l (k < l) ==> infin_or_leq ll k T
Proof
  rw[infin_or_leq_def] >> fs[]
QED

Theorem IS_SOME_LNTH_infin_or_leq:
  !k ll e. IS_SOME (LNTH k ll) ==> infin_or_leq ll (SUC k) T
Proof
  rw[]
  >> Cases_on `LFINITE ll`
  >> fs[infin_or_leq_def]
  >> imp_res_tac LFINITE_LLENGTH
  >> CCONTR_TAC
  >> rfs[NOT_LESS_EQUAL]
  >> fs[LNTH_LLENGTH_NONE]
QED

Theorem LNTH_SOME_infin_or_leq =
  REWRITE_RULE[IS_SOME_EXISTS] IS_SOME_LNTH_infin_or_leq;

Theorem IS_SOME_LTAKE_infin_or_leq:
  !k ll. IS_SOME (LTAKE k ll) ==> infin_or_leq ll k T
Proof
  rw[]
  >> Cases_on `LFINITE ll`
  >> fs[infin_or_leq_def]
  >> imp_res_tac LFINITE_LLENGTH
  >> CCONTR_TAC
  >> rfs[NOT_LESS_EQUAL]
  >> fs[LTAKE_LLENGTH_NONE]
QED

Theorem LTAKE_SOME_infin_or_leq =
  REWRITE_RULE[IS_SOME_EXISTS] IS_SOME_LTAKE_infin_or_leq;

Theorem LNTH_EL_LTAKE:
  !ll n k.
  infin_or_leq ll k T /\ n < k ==> LNTH n ll = SOME (EL n (THE (LTAKE k ll)))
Proof
  rw[infin_or_leq_def]
  >> match_mp_tac LTAKE_LNTH_EL
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >- (
    drule NOT_LFINITE_TAKE
    >> disch_then (qspec_then `k` mp_tac)
    >> rw[]
    >> fs[]
  )
  >> imp_res_tac LFINITE_TAKE
  >> fs[]
QED

Theorem EL_FILTER_EL:
  !ls m P. m < LENGTH (FILTER P ls)
  ==> ?i. EL m (FILTER P ls) = EL i ls /\ i < LENGTH ls
Proof
  rw[]
  >> imp_res_tac EL_MEM
  >> fs[MEM_FILTER,MEM_EL]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[]
QED

Theorem EL_FILTER_EL_unique:
  !(ls:num list) P m. m < LENGTH (FILTER P ls)
  /\ (!m n i:num j. m < n /\ n < LENGTH ls ==> EL m ls < EL n ls)
  ==> ?!i. EL m (FILTER P ls) = EL i ls /\ i < LENGTH ls
Proof
  rw[EXISTS_UNIQUE_DEF,EL_FILTER_EL]
  >> Cases_on `x < y`
  >- (
    first_x_assum drule
    >> fs[prim_recTheory.LESS_REFL,NOT_LESS]
  )
  >> Cases_on `y < x`
  >- (
    first_x_assum drule
    >> fs[prim_recTheory.LESS_REFL,NOT_LESS]
  )
  >> fs[NOT_LESS,LESS_OR_EQ]
QED

Theorem NOT_EQ_LESS:
  ~(x:num = y) <=> x < y \/ y < x
Proof
  fs[]
QED

Theorem DROP_FILTER_FILTER_DROP:
  !(ls:num list) k P. k <= LENGTH (FILTER P ls)
  ==> ?l. l <= LENGTH ls /\ DROP k (FILTER P ls) = FILTER P (DROP l ls)
Proof
  ho_match_mp_tac SNOC_INDUCT
  >> rw[SNOC_APPEND]
  >> Cases_on `k < LENGTH (FILTER P ls)`
  >- (
    last_x_assum (qspecl_then [`k`,`P`] mp_tac)
    >> rw[FILTER_APPEND,EXISTS_UNIQUE_DEF]
    >> qexists_tac `l`
    >> fs[DROP_APPEND1,FILTER_APPEND]
  )
  >> fs[NOT_LESS,FILTER_APPEND]
  >> Cases_on `k = LENGTH (FILTER P ls)`
  >- (
    qexists_tac `LENGTH ls`
    >> FULL_CASE_TAC
    >> fs[DROP_APPEND2,DROP_NIL]
  )
  >> qexists_tac `SUC (LENGTH ls)`
  >> FULL_CASE_TAC
  >> fs[DROP_APPEND2,DROP_NIL]
QED

Theorem LNTH_THE_DROP:
  !k l ll. infin_or_leq ll l T
  ==> LNTH k (THE (LDROP l ll)) = LNTH (k+l) ll
Proof
  rw[infin_or_leq_def]
  >> imp_res_tac LTAKE_DROP
  >> pop_assum mp_tac
  >> TRY (disch_then (qspec_then `l` mp_tac))
  >> disch_then (fn x => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV[GSYM x])))
  >> `IS_SOME(LTAKE l ll)` by (
    fs[IS_SOME_EXISTS,NOT_LFINITE_TAKE,LFINITE_TAKE]
  )
  >> fs[IS_SOME_EXISTS]
  >> imp_res_tac LTAKE_LENGTH
  >> fs[LNTH_LAPPEND]
QED

Theorem LTAKE_CONS:
  !k ll. infin_or_leq ll (SUC k) T
  ==> THE (LTAKE (SUC k) ll) = THE (LTAKE k ll) ++ [THE (LNTH k ll)]
  /\ IS_SOME (LTAKE (SUC k) ll)
  /\ IS_SOME (LTAKE k ll)
  /\ IS_SOME (LNTH k ll)
Proof
  rw[LTAKE_SNOC_LNTH,infin_or_leq_def]
  >> TRY (drule NOT_LFINITE_TAKE >> disch_then (qspec_then `SUC (SUC k)` assume_tac)
    >> drule NOT_LFINITE_TAKE >> disch_then (qspec_then `k` assume_tac))
  >> TRY (drule LFINITE_TAKE >> disch_then (qspec_then `k` assume_tac)
    >> drule LFINITE_TAKE >> disch_then (qspec_then `SUC k` assume_tac))
  >> rfs[]
  >> imp_res_tac LTAKE_LNTH_EL
  >> fs[]
QED

Theorem infin_or_leq_IS_SOME_LDROP:
  !ll k. infin_or_leq ll k T ==> IS_SOME (LDROP k ll)
Proof
  rw[infin_or_leq_def]
  >> fs[NOT_LFINITE_DROP,IS_SOME_EXISTS,LFINITE_DROP]
QED

Theorem LDROP_THE_LDROP_ADD:
  !ll l k. infin_or_leq ll (k + l) T
  ==> LDROP k (THE (LDROP l ll)) = LDROP (k + l) ll
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> rw[]
  >> first_assum (qspecl_then [`ll`,`1`] assume_tac)
  >> first_x_assum (qspecl_then [`ll`,`SUC k`] assume_tac)
  >> rfs[ADD1]
  >> pop_assum (fn x => ONCE_REWRITE_TAC[GSYM x])
  >> fs[GSYM ADD1]
  >> CONV_TAC(RHS_CONV (ONCE_REWRITE_CONV [CONJUNCT2 LDROP]))
  >> drule infin_or_leq_imp
  >> disch_then (qspec_then `SUC l` assume_tac)
  >> fs[LDROP1_THM]
  >> drule infin_or_leq_IS_SOME_LDROP
  >> rw[IS_SOME_EXISTS]
  >> fs[option_CLAUSES]
QED

Theorem infin_or_leq_IS_SOME_LNTH:
  !ll k l. infin_or_leq ll k (l < k) ==> IS_SOME(LNTH l ll)
Proof
  rw[infin_or_leq_def,IS_SOME_EXISTS,infinite_lnth_some]
  >> fs[]
  >> drule LFINITE_TAKE
  >> disch_then (qspec_then `THE (LLENGTH ll)` assume_tac)
  >> fs[]
  >> drule LTAKE_LNTH_EL
  >> disch_then (qspec_then `l` mp_tac)
  >> fs[]
QED

Theorem infin_or_leq_SUC_IS_SOME_LNTH:
  !ll k. infin_or_leq ll (SUC k) T ==> IS_SOME(LNTH k ll)
Proof
  rw[infin_or_leq_def,IS_SOME_EXISTS,infinite_lnth_some]
  >> fs[]
  >> drule LFINITE_TAKE
  >> disch_then imp_res_tac
  >> drule LTAKE_LNTH_EL
  >> disch_then (qspec_then `k` mp_tac)
  >> fs[]
QED

Theorem LDROP_CONS:
  !k ll. infin_or_leq ll (SUC k) T
  ==> THE (LDROP k ll) = LAPPEND [|THE (LNTH k ll)|] (THE (LDROP (SUC k) ll))
  /\ IS_SOME (LDROP (SUC k) ll)
  /\ IS_SOME (LDROP k ll)
  /\ IS_SOME (LNTH k ll)
Proof
  rw[]
  >> imp_res_tac LNTH_EL_LTAKE
  >> TRY (match_mp_tac infin_or_leq_SUC_IS_SOME_LNTH >> fs[infin_or_leq_imp])
  >> TRY (match_mp_tac infin_or_leq_IS_SOME_LDROP >> imp_res_tac infin_or_leq_imp >> fs[])
  >> ONCE_REWRITE_TAC[LLIST_BISIMULATION0]
  >> qexists_tac `λx y. (x = [||] /\ x = y) \/ LHD x = LHD y /\ LTL x = LTL y`
  >> rw[]
  >- (
    fs[LDROP_LDROP,LNTH_LDROP,ADD1]
    >> ONCE_REWRITE_TAC[GSYM LDROP1_THM]
    >> fs[LDROP_THE_LDROP_ADD]
    >> imp_res_tac infin_or_leq_IS_SOME_LDROP
    >> fs[IS_SOME_EXISTS]
  )
  >> rename1`LHD la = LHD lb`
  >> Cases_on `la`
  >> Cases_on `lb`
  >> fs[]
QED

Theorem infin_or_leq_IS_SOME_LTAKE:
  !ll k. infin_or_leq ll k T ==> IS_SOME(LTAKE k ll)
Proof
  rw[infin_or_leq_def,IS_SOME_EXISTS]
  >> fs[NOT_LFINITE_TAKE,LFINITE_TAKE]
QED

Theorem infin_or_leq_LNTH_EL_LTAKE:
  !ll n k. infin_or_leq ll k T /\ n < k ==> LNTH n ll = SOME (EL n (THE (LTAKE k ll)))
Proof
  rw[GSYM LESS_EQ] >> fs[LNTH_EL_LTAKE]
QED

Theorem NOT_infin_or_leq_LNTH_LLENGTH_NONE:
  !ll k. ~infin_or_leq ll (SUC k) T ==> LNTH k ll = NONE
Proof
  rw[]
  >> imp_res_tac LFINITE_LLENGTH
  >> fs[LNTH_LLENGTH_NONE]
QED

Theorem infin_or_leq_LENGTH_LTAKE_EQ:
  !ll k. infin_or_leq ll k T ==> LENGTH (THE (LTAKE k ll)) = k
Proof
  rw[infin_or_leq_def]
  >> fs[NOT_LFINITE_LENGTH]
  >> imp_res_tac LFINITE_LLENGTH
  >> imp_res_tac LTAKE_LLENGTH_SOME
  >> fs[]
  >> drule LTAKE_TAKE_LESS
  >> disch_then (qspec_then `k` assume_tac)
  >> rfs[]
  >> match_mp_tac LENGTH_TAKE
  >> imp_res_tac LTAKE_LENGTH
  >> fs[]
QED

Theorem LNTH_LFILTER_LNTH_NONE:
  !n P ll. LNTH n ll = NONE
  ==> ?k. k <= n /\ LNTH k (LFILTER P ll) = NONE
Proof
  rw[]
  >> imp_res_tac LFINITE_LNTH_NONE
  >> drule LLENGTH_LFILTER_LEQ
  >> drule LFINITE_LFILTER
  >> rpt (disch_then (qspec_then `P` assume_tac))
  >> imp_res_tac (GSYM (REWRITE_RULE[NOT_IS_SOME_EQ_NONE] (ccontr_equiv less_opt_LLENGTH_LNTH_SOME)))
  >> imp_res_tac LFINITE_LLENGTH
  >> fs[less_opt_def,NOT_LESS]
  >> qexists_tac `n'`
  >> fs[]
  >> match_mp_tac (GEN_ALL LNTH_LLENGTH_NONE)
  >> fs[]
QED

Theorem LNTH_SOME_MONO:
  ∀m n ll. IS_SOME (LNTH m ll) ∧ n ≤ m ⇒ IS_SOME (LNTH n ll)
Proof
  rw[]
  >> CCONTR_TAC
  >> fs[NOT_IS_SOME_EQ_NONE,quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
  >> imp_res_tac LNTH_NONE_MONO
QED

Theorem IS_SOME_IS_NONE_SUC_LLENGTH:
  !k ll. IS_SOME(LNTH k ll) /\ IS_NONE(LNTH (SUC k) ll)
  ==> LLENGTH ll = SOME (SUC k)
Proof
  rw[EQ_IMP_THM]
  >> imp_res_tac LFINITE_LNTH_NONE
  >> imp_res_tac LFINITE_LLENGTH
  >> Cases_on `SUC k = n`
  >> fs[NOT_EQ_LESS,GSYM LESS_EQ_IFF_LESS_SUC]
  >- (
    imp_res_tac LTAKE_LLENGTH_SOME
    >> imp_res_tac LTAKE_LENGTH
    >> imp_res_tac LTAKE_LNTH_EL
    >> fs[]
  )
  >> imp_res_tac LNTH_LLENGTH_NONE
  >> fs[]
QED

Theorem LFINITE_THE_DROP:
  !k ll. LFINITE ll /\ k <= THE (LLENGTH ll) ==> LFINITE (THE (LDROP k ll))
Proof
  rw[]
  >> imp_res_tac LFINITE_LLENGTH
  >> REWRITE_TAC[LFINITE_LLENGTH]
  >> drule_all_then strip_assume_tac LFINITE_DROP
  >> fs[]
  >> imp_res_tac LDROP_SOME_LLENGTH
  >> fs[]
QED

Theorem LFINITE_LFILTER_THE_LDROP:
  !ll P k. ~LFINITE ll /\ LFINITE (LFILTER P ll) ==> LFINITE (LFILTER P (THE (LDROP k ll)))
Proof
  rw[]
  >> qpat_x_assum `LFINITE _` mp_tac
  >> drule_then (qspec_then `k` mp_tac) (CONJUNCT1 LTAKE_DROP)
  >> disch_then (fn x => disch_then (assume_tac o ONCE_REWRITE_RULE[GSYM x]))
  >> qmatch_asmsub_abbrev_tac `LAPPEND (fromList l1) l2`
  >> qspec_then `l1` assume_tac LFINITE_fromList
  >> fs[LFILTER_APPEND,LFINITE_APPEND]
QED

Theorem infin_or_leq_LTAKE_DROP:
  !k ll. infin_or_leq ll k T
  ==> LAPPEND (fromList (THE (LTAKE k ll))) (THE (LDROP k ll)) = ll
Proof
  rw[infin_or_leq_def] >> fs[LTAKE_DROP]
QED

Theorem LFINITE_LENGTH_LTAKE_LEQ:
  !k ll. LFINITE ll /\ IS_SOME (LTAKE k ll)
  ==> LENGTH (THE (LTAKE k ll)) <= THE (LLENGTH ll)
Proof
  rw[IS_SOME_EXISTS]
  >> imp_res_tac LFINITE_HAS_LENGTH
  >> drule LTAKE_LENGTH
  >> disch_then (assume_tac o GSYM)
  >> CCONTR_TAC
  >> qspecl_then [`k`,`THE (LLENGTH ll)`,`ll`,`x`] assume_tac (GEN_ALL LTAKE_TAKE_LESS)
  >> rfs[NOT_LESS_EQUAL]
  >> fs[LTAKE_LLENGTH_NONE]
QED

Theorem infin_or_leq_LENGTH_LTAKE:
  !k ll. infin_or_leq ll k T ==> infin_or_leq ll (LENGTH (THE (LTAKE k ll))) T
Proof
  rw[]
  >> imp_res_tac infin_or_leq_IS_SOME_LTAKE
  >> fs[infin_or_leq_def,LFINITE_LENGTH_LTAKE_LEQ]
QED

Theorem infin_or_leq_LFILTER_imp:
  !ll l P. infin_or_leq (LFILTER P ll) l T ==> infin_or_leq ll l T
Proof
  rw[infin_or_leq_def]
  >> imp_res_tac NOT_LFINITE_LFILTER
  >> fs[]
  >> Cases_on `LFINITE ll` >> fs[]
  >> drule LLENGTH_LFILTER_LEQ
  >> disch_then (qspec_then `P` assume_tac)
  >> fs[]
QED

Theorem LTAKE_NULL_EQ_ZERO:
  !n ll. LTAKE n ll = SOME [] <=> n = 0
Proof
  Induct >> rw[] >> Cases_on `ll` >> fs[]
QED

Theorem IS_SOME_LNTH_LFILTER_P:
  !l P ll. IS_SOME (LNTH l (LFILTER P ll)) ==> P (THE (LNTH l (LFILTER P ll)))
Proof
  rw[IS_SOME_EXISTS]
  >> match_mp_tac every_LNTH
  >> fs[]
  >> goal_assum (first_assum o mp_then Any mp_tac)
  >> fs[every_LFILTER]
QED

val (llist_sorted_def,llist_sorted_coind,llist_sorted_rules) =
  Hol_coreln
    `(llist_sorted [||]) /\
     (!l:num ll.
      llist_sorted ll /\
      every ($<= l) ll ==>
      llist_sorted (l:::ll))
    `

Theorem LREPEAT_SORTED:
  llist_sorted(LREPEAT [x])
Proof
  ho_match_mp_tac (MP_CANON llist_sorted_coind) >>
  qexists_tac `λll. ll = LREPEAT [x]` >>
  rw[] >>
  rw[Once LREPEAT_thm] >>
  ho_match_mp_tac (MP_CANON every_coind) >>
  qexists_tac `λll. ll = LREPEAT [x]` >>
  fs[Once LREPEAT_thm]
QED

Theorem llist_sorted_LDROP:
  !k ll. llist_sorted ll /\ (LFINITE ll ==> k <= THE (LLENGTH ll))
  ==> llist_sorted (THE (LDROP k ll))
Proof
  Induct
  >> rw[]
  >> first_x_assum (qspec_then `THE (LDROP 1 ll)` mp_tac)
  >> `infin_or_leq ll (SUC k) T` by (fs[infin_or_leq_def] >> Cases_on `LFINITE ll` >> rw[])
  >> qspecl_then [`ll`,`1`,`k`] mp_tac LDROP_THE_LDROP_ADD
  >> rw[GSYM arithmeticTheory.ADD1]
  >> first_x_assum match_mp_tac
  >> qpat_x_assum `llist_sorted _` (assume_tac o ONCE_REWRITE_RULE[llist_sorted_rules])
  >> fs[]
  >> fs[CONJUNCT1 LFINITE_rules]
  >> strip_tac
  >> imp_res_tac LFINITE_LLENGTH
  >> fs[]
QED

Theorem LFINITE_LDROP_LAPPEND_snd:
  !l1 l2. LFINITE l1 ==> LDROP (THE (LLENGTH l1)) (LAPPEND l1 l2) = SOME l2
Proof
  fs[GSYM PULL_FORALL]
  >> ho_match_mp_tac LFINITE_STRONG_INDUCTION
  >> rw[LFINITE_LLENGTH]
  >> rfs[]
QED

Theorem llist_sorted_LAPPEND_snd:
  !l1 l2. llist_sorted (LAPPEND l1 l2) /\ LFINITE l1 ==> llist_sorted l2
Proof
  rw[]
  >> drule_then (qspec_then `THE (LLENGTH l1)` mp_tac) llist_sorted_LDROP
  >> fs[LFINITE_APPEND,LLENGTH_APPEND,LFINITE_LDROP_LAPPEND_snd]
QED

Theorem llist_sorted_LAPPEND_fst:
  !l1 l2. llist_sorted (LAPPEND l1 l2) ==> llist_sorted l1
Proof
  `!l1. (?l2. llist_sorted (LAPPEND l1 l2)) ==> llist_sorted l1` by (
    ho_match_mp_tac llist_sorted_coind
    >> Cases
    >> rw[]
    >> pop_assum (assume_tac o ONCE_REWRITE_RULE[llist_sorted_rules])
    >> fs[]
    >> imp_res_tac every_LAPPEND
    >> goal_assum (first_assum o mp_then Any mp_tac)
  )
  >> metis_tac[]
QED

Theorem llist_sorted_LFILTER:
  !ll P. llist_sorted ll ==> llist_sorted (LFILTER P ll)
Proof
  `!ll. (?ll' P. ll = LFILTER P ll' /\ llist_sorted ll') ==> llist_sorted ll` by (
    ho_match_mp_tac llist_sorted_coind
    >> rw[]
    >> rename1 `LFILTER P ll`
    >> Cases_on `LFILTER P ll`
    >> fs[]
    >> drule_then strip_assume_tac LFILTER_EQ_CONS
    >> rveq
    >> qspecl_then [`LAPPEND (fromList l) [|h|]`,`ll'`] assume_tac llist_sorted_LAPPEND_snd
    >> rfs[LAPPEND_ASSOC,LFINITE_APPEND,LFINITE_fromList]
    >> rw[]
    >- metis_tac[]
    >> drule llist_sorted_LAPPEND_snd
    >> fs[LFINITE_fromList]
    >> disch_then (assume_tac o ONCE_REWRITE_RULE[llist_sorted_rules])
    >> fs[every_every_LFILTER]
  )
  >> metis_tac[]
QED

Theorem LLnum_mono2_equiv:
  !ll. (!n i j:num. LNTH n ll = SOME i /\ LNTH (SUC n) ll = SOME j ==> i <= j)
  <=> !n m i j:num. LNTH n ll = SOME i /\ LNTH m ll = SOME j /\ n <= m ==> i <= j
Proof
  fs[EQ_IMP_THM]
  >> gen_tac
  >> conj_tac
  >> disch_tac
  >- (
    CONV_TAC SWAP_FORALL_CONV
    >> Induct
    >> rw[]
    >> fs[]
    >> Cases_on `n = SUC m`
    >> fs[NOT_EQ_LESS]
    >> qspecl_then [`SUC m`,`m`,`ll`] mp_tac (REWRITE_RULE[IS_SOME_EXISTS] LNTH_SOME_MONO)
    >> rw[]
    >> Cases_on `n = m`
    >> fs[NOT_EQ_LESS]
    >- (
      last_x_assum match_mp_tac
      >> goal_assum (first_assum o mp_then Any mp_tac)
      >> fs[]
    )
    >> first_x_assum (qspecl_then [`n`,`i`] assume_tac)
    >> first_x_assum (qspecl_then [`m`,`x`,`j`] assume_tac)
    >> rfs[]
  )
  >> rw[]
  >> first_x_assum (qspecl_then [`n`,`SUC n`] mp_tac)
  >> fs[]
QED

Theorem llist_sorted_LNTH[local]:
  !ll. llist_sorted ll ==>
  !n m i:num j. LNTH n ll = SOME i /\ LNTH m ll = SOME j /\ n <= m ==> i <= j
Proof
  ONCE_REWRITE_TAC[GSYM LLnum_mono2_equiv]
  >> rw[]
  >> imp_res_tac LNTH_SOME_infin_or_leq
  >> qspecl_then [`n`,`ll`] mp_tac llist_sorted_LDROP
  >> qspecl_then [`0`,`n`,`ll`] mp_tac LNTH_THE_DROP
  >> qspecl_then [`1`,`n`,`ll`] mp_tac LNTH_THE_DROP
  >> qspecl_then [`ll`,`n`] mp_tac infin_or_leq_IS_SOME_LDROP
  >> rw[infin_or_leq_SUC_imp,GSYM infin_or_leq_eq,GSYM arithmeticTheory.ADD1,IS_SOME_EXISTS]
  >> rename1 `LDROP n ll = SOME x`
  >> Cases_on `x`
  >- fs[LDROP_EQ_LNIL,infin_or_leq_def,LFINITE_LLENGTH]
  >> rename1 `LDROP n ll = SOME (h:::t)`
  >> Cases_on `t`
  >- (
    fs[infin_or_leq_def]
    >> fs[]
    >- (imp_res_tac NOT_LFINITE_DROP_LFINITE >> fs[LFINITE_THM])
    >> imp_res_tac LFINITE_DROP
    >> fs[LDROP_SUC]
    >> rpt (rveq >> fs[LTL_EQ_NONE])
  )
  >> rfs[]
  >> qpat_x_assum `llist_sorted (_:::_)` (assume_tac o ONCE_REWRITE_RULE[llist_sorted_rules])
  >> qpat_x_assum `LNTH 1 _ = _` (assume_tac o REWRITE_RULE[ONE,LNTH_THM])
  >> fs[]
QED

Theorem LNTH_llist_sorted[local]:
  !ll. (!n m i:num j. LNTH n ll = SOME i /\ LNTH m ll = SOME j /\ n <= m ==> i <= j)
  ==> llist_sorted ll
Proof
  ho_match_mp_tac llist_sorted_coind
  >> Cases
  >> rw[]
  >- (
    first_x_assum match_mp_tac
    >> rename1 `LNTH n t = SOME i`
    >> rename1 `LNTH m t = SOME j`
    >> qexists_tac `SUC n`
    >> qexists_tac `SUC m`
    >> fs[]
  )
  >> rw[every_def,exists_LNTH,DISJ_EQ_IMP]
  >> first_x_assum (qspecl_then [`0`,`SUC n`] match_mp_tac)
  >> fs[]
QED

Theorem llist_sorted_LNTH_eq:
  !ll. llist_sorted ll <=> 
  (!n m i:num j. LNTH n ll = SOME i /\ LNTH m ll = SOME j /\ n <= m ==> i <= j)
Proof
  metis_tac[EQ_IMP_THM,LNTH_llist_sorted,llist_sorted_LNTH]
QED

Theorem llist_sorted_LNTH_LFILTER:
  !ll P. llist_sorted ll ==> 
  !n m i:num j. LNTH n (LFILTER P ll) = SOME i /\ LNTH m (LFILTER P ll) = SOME j /\ n <= m ==> i <= j
Proof
  rpt gen_tac
  >> disch_tac
  >> ho_match_mp_tac llist_sorted_LNTH
  >> fs[llist_sorted_LFILTER]
QED

Theorem llist_sorted_LGENLIST:
  llist_sorted (LGENLIST I NONE)
Proof
  rw[llist_sorted_LNTH_eq,LGENLIST_num]
QED

Theorem LNTH_n_geq_num_pred:
  !n i P. LNTH n (LFILTER P (LGENLIST I NONE)) = SOME i ==> n <= i
Proof
  rw[]
  >> qspec_then `i` assume_tac LGENLIST_num
  >> imp_res_tac LNTH_LFILTER_LNTH
  >> fs[LGENLIST_num]
QED

val _ = export_theory();
