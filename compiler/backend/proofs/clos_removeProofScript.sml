open preamble closPropsTheory clos_relationTheory clos_removeTheory;

val _ = new_theory"clos_removeProof";

val _ = Parse.bring_to_front_overload"Let"{Name="Let",Thy="closLang"};

val FOLDL_acc = Q.prove(
  `∀l f m l0.
     FOLDL (λ(n,a) e. (n + 1n, f n e::a)) (m,l0) l =
       let (nr0, lr0) = FOLDL (λ(n,a) e. (n + 1, f (n + m) e::a)) (0,[]) l
       in (nr0 + m, lr0 ++ l0)`,
  Induct >- simp[] >> simp_tac (srw_ss()) [] >>
  pop_assum (fn th => simp[SimpLHS, Once th] >> simp[SimpRHS, Once th]) >>
  simp[UNCURRY]);

val MAPi_thm = Q.store_thm(
  "MAPi_thm[simp]",
  `MAPi f [] = [] ∧
   MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t`,
  simp[MAPi_def] >> simp[Once FOLDL_acc, SimpLHS] >> simp[UNCURRY, ADD1]);

val FOLDR_SUB = Q.prove(
  `∀l N.
     FST (FOLDR (λe (i,acc). (i - 1, f i acc e)) (N, a0) l) = N - LENGTH l`,
  Induct >> simp[UNCURRY]);

val FOLDR_SUB2 = Q.prove(
  `∀l N x a0. SND (FOLDR (λe (i,acc). (i - 1n, f i acc e)) (N - x, a0) l) =
              SND (FOLDR (λe (i,acc). (i - 1, f (i - x) acc e)) (N, a0) l)`,
  Induct >> simp[UNCURRY, FOLDR_SUB]);

val FOLDR_SUB_CONG = Q.prove(
  `∀l N a0. LENGTH l ≤ N ⇒ (∀n a e. 0 < n ⇒ f1 n a e = f2 n a e) ⇒
            FOLDR (λe (i,acc). (i - 1, f1 i acc e)) (N,a0) l =
            FOLDR (λe (i,acc). (i - 1, f2 i acc e)) (N,a0) l`,
  Induct >> simp[UNCURRY, FOLDR_SUB]);

val FOLDR_MAPi = Q.store_thm(
  "FOLDR_MAPi",
  `∀g. FOLDR f a (MAPi g l) =
       SND (FOLDR (λe (i,acc). (i - 1, f (g i e) acc))
                  (LENGTH l - 1, a) l)`,
  Induct_on `l` >> simp[] >> simp[UNCURRY, FOLDR_SUB, FOLDR_SUB2] >>
  simp[Cong FOLDR_SUB_CONG, ADD1]);

(* can't be used a general rewrite as it loops *)
val fv_CONS = Q.store_thm(
  "fv_CONS",
  `∀h. fv n (h::t) ⇔ fv n [h] ∨ fv n t`,
  Induct_on `t` >> simp[fv_def]);

val fv_APPEND = Q.store_thm(
  "fv_APPEND[simp]",
  `fv n (l1 ++ l2) ⇔ fv n l1 ∨ fv n l2`,
  Induct_on `l1` >> simp[fv_def] >> once_rewrite_tac[fv_CONS] >>
  simp[DISJ_ASSOC]);

val FOLDR_UNZIP = Q.store_thm(
  "FOLDR_UNZIP",
  `FOLDR (λ(x,l) (ts,frees). (x::ts, mk_Union l frees)) ([], A) l =
   let (ts, fvs) = UNZIP l in
     (ts, list_mk_Union (fvs ++ [A]))`,
  Induct_on `l` >> simp[db_varsTheory.list_mk_Union_def] >>
  qcase_tac `UNZIP ll` >> Cases_on `UNZIP ll` >> fs[FORALL_PROD]);

val FPAIR = Q.prove(
  `(λ(a,b). (f a, g b)) = f ## g`,
  simp[FUN_EQ_THM, FORALL_PROD]);

val LENGTH_MAPi = Q.store_thm(
  "LENGTH_MAPi[simp]",
  `∀f. LENGTH (MAPi f l) = LENGTH l`,
  Induct_on `l` >> simp[MAPi_thm]);

val FST_UNZIP_MAPi = Q.store_thm(
  "FST_UNZIP_MAPi",
  `∀l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l`,
  Induct >> simp[]);

val SND_UNZIP_MAPi = Q.store_thm(
  "SND_UNZIP_MAPi",
  `∀l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l`,
  Induct >> simp[]);

val lt_SUC = prove(
  ``x < SUC y ⇔ x = 0 ∨ ∃x0. x = SUC x0 ∧ x0 < y``,
  Cases_on `x` >> simp[]);

val MEM_MAPi = Q.store_thm(
  "MEM_MAPi",
  `∀l f e. MEM e (MAPi f l) ⇔ ∃n. n < LENGTH l ∧ e = f n (EL n l)`,
  Induct >> dsimp[lt_SUC]);

val fv_MAPi = Q.store_thm(
  "fv_MAPi",
  `∀l x f. fv x (MAPi f l) ⇔ ∃n. n < LENGTH l ∧ fv x [f n (EL n l)]`,
  Induct >> simp[fv_def] >> simp[Once fv_CONS, SimpLHS] >>
  dsimp[lt_SUC]);

val remove_fv = Q.store_thm("remove_fv",
  `∀xs cs l. remove xs = (cs, l) ⇒ ∀n. fv n cs ⇔ has_var n l`,
  ho_match_mp_tac remove_ind >> simp[remove_def, fv_def, UNCURRY] >>
  rpt strip_tac
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      qcase_tac `FST (remove(e'::es))` >> Cases_on `remove(e'::es)` >> fs[])
  >- (qcase_tac `FST (remove[E1])` >> Cases_on `remove [E1]` >> fs[] >>
      imp_res_tac remove_SING >> fs[] >>
      qcase_tac `FST (remove[E2])` >> Cases_on `remove[E2]` >> fs[] >> rw[] >>
      imp_res_tac remove_SING >> fs[] >> rw[] >>
      qcase_tac `FST (remove[E3])` >> Cases_on `remove[E3]` >> fs[] >> rw[] >>
      imp_res_tac remove_SING >> fs[])
  >- (qcase_tac `FST (remove[E1])` >> Cases_on `remove[E1]` >> fs[] >>
      simp[FOLDR_UNZIP, FPAIR, FST_UNZIP_MAPi, combinTheory.o_ABS_R,
           SND_UNZIP_MAPi] >>
      simp_tac (srw_ss() ++ COND_elim_ss)[] >>
      imp_res_tac remove_SING >> rw[] >> dsimp[fv_MAPi, EXISTS_MEM, MEM_MAPi] >>
      eq_tac >> dsimp[] >> qx_gen_tac `i` >>
      qcase_tac `i < LENGTH xs` >> Cases_on `i < LENGTH xs` >> simp[] >>
      `MEM (EL i xs) xs` by metis_tac[MEM_EL] >> rw[const_0_def, fv_def] >>
      Cases_on `remove [EL i xs]` >> fs[] >> imp_res_tac remove_SING >> rw[] >>
      fs[] >> metis_tac[FST,SND,HD])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[] >> qcase_tac `FST (remove xs)` >>
      Cases_on `remove xs` >> fs[])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove[e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[] >>
      simp[FOLDR_UNZIP, FPAIR, FST_UNZIP_MAPi, SND_UNZIP_MAPi,
           combinTheory.o_ABS_R, pairTheory.o_UNCURRY_R, EXISTS_MEM,
           MEM_MAPi] >> dsimp[] >>
      simp_tac (srw_ss() ++ COND_elim_ss) [] >>
      qcase_tac `has_var (n + LENGTH fns) res` >>
      Cases_on `has_var (n + LENGTH fns) res` >> simp[] >>
      eq_tac >> dsimp[] >> qx_gen_tac `i` >>
      `∃m ee. EL i fns = (m,ee)` by (Cases_on `EL i fns` >> simp[]) >>
      asm_simp_tac (srw_ss() ++ COND_elim_ss) [const_0_def, fv_def] >>
      Cases_on `remove[ee]` >> fs[] >> imp_res_tac remove_SING >> rw[] >>
      qexists_tac `i` >> simp[] >>
      `MEM (m,ee) fns` by metis_tac[MEM_EL] >>
      first_x_assum (qspecl_then [`m`, `ee`, `i`] mp_tac) >>
      simp[] >> strip_tac >> lfs[])
  >- (qcase_tac `FST (remove[e])` >> Cases_on `remove [e]` >> fs[] >>
      imp_res_tac remove_SING >> rw[] >>
      qcase_tac `FST (remove[e2])` >> Cases_on `remove [e2]` >> fs[] >>
      imp_res_tac remove_SING >> rw[])
)

val remove_correct = Q.store_thm("remove_correct",
  `∀es es' s.
    every_Fn_vs_NONE es ⇒
    remove es = (es',s) ⇒
    exp_rel (:'ffi) es es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  TRY (qcase_tac`Let` >>
       lfs[FOLDR_UNZIP, FPAIR, PAIR_MAP, FST_UNZIP_MAPi,
           SND_UNZIP_MAPi, combinTheory.o_ABS_R] >> rw[] >>
       simp_tac (srw_ss() ++ COND_elim_ss) [] >>
       simp[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
       qx_genl_tac [`i`, `env1`, `env2`, `s1`, `s2`] >>
       strip_tac >> simp[closSemTheory.evaluate_def] >> cheat) >>
  TRY ( qcase_tac`Letrec` >> cheat ) >>
  metis_tac[compat]);

val k_intro = Q.prove(`(λn. x) = K x`, simp[FUN_EQ_THM])

val code_locs_const_0 = Q.store_thm("code_locs_const_0[simp]",
  `code_locs [const_0] = []`,
  EVAL_TAC)

val code_locs_REPLICATE_const_0 = Q.store_thm("code_locs_REPLICATE_const_0[simp]",
  `code_locs (REPLICATE n const_0) = []`,
  Induct_on`n`>>rw[REPLICATE,code_locs_def]>>
  rw[code_locs_cons])

fun qccase q = qcase_tac q >> Cases_on q

val code_locs_MAPi = Q.store_thm(
  "code_locs_MAPi",
  `∀f. code_locs (MAPi f xs) = FLAT (MAPi (λn x. code_locs [f n x]) xs)`,
  Induct_on `xs` >> simp[code_locs_def] >>
  simp[Once closPropsTheory.code_locs_cons, SimpLHS] >>
  simp[combinTheory.o_DEF]);

val ALL_DISTINCT_FLAT = Q.store_thm(
  "ALL_DISTINCT_FLAT",
  `∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))`,
  Induct >> dsimp[ALL_DISTINCT_APPEND, lt_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]);

val EL_MAPi = Q.store_thm(
  "EL_MAPi",
  `∀l i f. i < LENGTH l ⇒ EL i (MAPi f l) = f i (EL i l)`,
  Induct >> dsimp[lt_SUC]);

val code_loc'_def = Define`
  code_loc' x = code_locs [x]
`;

val code_loc'_THM = save_thm(
  "code_loc'_THM[simp]",
  CONJ (code_locs_def |> SIMP_RULE (srw_ss()) [GSYM code_loc'_def, LET_THM])
       (code_locs_cons |> REWRITE_RULE [GSYM code_loc'_def]))

val code_locs_FLAT_MAP = Q.store_thm(
  "code_locs_FLAT_MAP",
  `code_locs xs = FLAT (MAP code_loc' xs)`,
  Induct_on `xs` >> simp[]);

val code_locs_MEM_SUBSET = Q.store_thm(
  "code_locs_MEM_SUBSET",
  `MEM x xs ⇒ set (code_loc' x) ⊆ set (code_locs xs)`,
  simp[SUBSET_DEF] >> Induct_on `xs` >> dsimp[] >> rpt strip_tac >>
  simp[Once code_locs_cons]);

val code_locs_FST_remove_sing = Q.store_thm(
  "code_locs_FST_remove_sing",
  `code_locs (FST (remove [e])) = code_loc' (HD (FST (remove [e])))`,
  Cases_on `remove [e]` >> imp_res_tac remove_SING >> simp[]);

val code_loc'_const_0 = Q.store_thm(
  "code_loc'_const_0[simp]",
  `code_loc' const_0 = []`,
  simp[const_0_def]);

val MAP_MAPi = Q.store_thm(
  "MAP_MAPi",
  `∀l f g. MAP f (MAPi g l) = MAPi ((o) ((o) f) g) l`,
  Induct >> simp[]);

val UNCURRY_SND = Q.store_thm(
  "UNCURRY_SND",
  `UNCURRY (λx y. f y) = f o SND`,
  simp[FUN_EQ_THM, FORALL_PROD]);

val remove_distinct_locs = Q.store_thm("remove_distinct_locs",
  `∀es.
    set (code_locs (FST (remove es))) ⊆ set (code_locs es) ∧
    (ALL_DISTINCT (code_locs es) ⇒ ALL_DISTINCT (code_locs (FST (remove es))))`,
  ho_match_mp_tac remove_ind >> simp[remove_def, code_locs_def] >>
  rpt conj_tac >> rpt gen_tac >> disch_then strip_assume_tac
  >- (qcase_tac `remove[x]` >> Cases_on `remove[x]` >> fs[] >>
      qcase_tac `remove (y::xs)` >> Cases_on `remove(y::xs)` >>
      fs[code_locs_append, ALL_DISTINCT_APPEND] >> fs[SUBSET_DEF] >>
      metis_tac[])
  >- ((* if *) qccase `remove[x1]` >> fs[] >>
      qccase `remove[x2]` >> fs[] >>
      qccase `remove[x3]` >> fs[] >> imp_res_tac remove_SING >>
      rw[code_locs_def, LET_THM, ALL_DISTINCT_APPEND] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- ((* let *) qccase `remove[body]` >> fs[] >>
      simp[FOLDR_UNZIP, ALL_DISTINCT_APPEND, FPAIR, FST_UNZIP_MAPi,
           combinTheory.o_ABS_R] >>
      simp[code_locs_MAPi, MEM_FLAT, MEM_MAPi, PULL_EXISTS, SUBSET_DEF] >>
      imp_res_tac remove_SING >> var_eq_tac >> fs[code_locs_FST_remove_sing] >>
      rw[]
      >- metis_tac[MEM_EL, SUBSET_DEF, code_locs_MEM_SUBSET]
      >- metis_tac[MEM_EL, SUBSET_DEF, code_locs_MEM_SUBSET]
      >- metis_tac[MEM_EL, SUBSET_DEF, code_locs_MEM_SUBSET]
      >- (simp[ALL_DISTINCT_FLAT, MEM_MAPi, EL_MAPi, PULL_EXISTS] >>
          lfs[code_locs_FLAT_MAP, ALL_DISTINCT_FLAT, MEM_MAP, PULL_EXISTS,
              EL_MAP, MEM_FLAT] >> conj_tac >- (rw[] >> metis_tac[MEM_EL]) >>
          rw[] >>
          qcase_tac `j < LENGTH xs` >> qcase_tac `i < j` >>
          `i < LENGTH xs` by simp[] >>
          `MEM (EL i xs) xs ∧ MEM (EL j xs) xs` by metis_tac[MEM_EL] >>
          metis_tac[SUBSET_DEF])
      >- (pop_assum mp_tac >> rw[] >>
          fs[code_locs_FLAT_MAP, MEM_FLAT, PULL_EXISTS, MEM_MAP] >>
          metis_tac[MEM_EL, SUBSET_DEF]))
  >- ((* raise *) qccase `remove[exn]` >> imp_res_tac remove_SING >>
      var_eq_tac >> fs[])
  >- ((* tick *) qccase `remove[tickc]` >> imp_res_tac remove_SING >>
      var_eq_tac >> fs[])
  >- ((* Op *) qccase `remove args` >> fs[])
  >- ((* App *) qccase `remove [f]` >> imp_res_tac remove_SING >>
      var_eq_tac >> fs[] >>
      qccase `remove args` >> fs[ALL_DISTINCT_APPEND, SUBSET_DEF] >>
      metis_tac[])
  >- ((* Fn *) qccase `remove[body]` >> imp_res_tac remove_SING >>
      var_eq_tac >> fs[ALL_DISTINCT_APPEND] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- ((* Letrec *) qccase `remove[body]` >> imp_res_tac remove_SING >>
      var_eq_tac >> fs[code_locs_FST_remove_sing] >>
      simp[FOLDR_UNZIP, ALL_DISTINCT_APPEND, FPAIR, FST_UNZIP_MAPi,
           combinTheory.o_ABS_R, pairTheory.o_UNCURRY_R, MAP_MAPi,
           code_locs_MAPi, MEM_FLAT, PULL_EXISTS, MEM_MAPi, DISJ_IMP_THM,
           ALL_DISTINCT_FLAT, EL_MAPi, SUBSET_DEF, MEM_GENLIST] >>
      simp_tac (srw_ss() ++ COND_elim_ss) [UNCURRY_SND] >> rpt strip_tac
      >- (simp[code_locs_FLAT_MAP, MEM_FLAT, MEM_MAP, PULL_EXISTS,
               EXISTS_PROD] >>
          qccase `EL ii fns` >> fs[] >> metis_tac[MEM_EL, SUBSET_DEF])
      >- (simp[code_locs_FLAT_MAP, MEM_FLAT, MEM_MAP, PULL_EXISTS,
               EXISTS_PROD] >>
          qccase `EL ii fns` >> fs[] >> metis_tac[MEM_EL, SUBSET_DEF])
      >- metis_tac[SUBSET_DEF]
      >- (lfs[code_locs_FLAT_MAP, MEM_FLAT, MEM_MAP, PULL_EXISTS,
              ALL_DISTINCT_FLAT, EL_MAP] >>
          qccase `EL ii fns` >> fs[] >> metis_tac[MEM_EL, SND])
      >- (qcase_tac `jj < LENGTH fns` >> qcase_tac `ii < jj` >>
          qccase `EL jj fns` >>
          lfs[code_locs_FLAT_MAP, ALL_DISTINCT_FLAT, EL_MAP] >>
          qccase `EL ii fns`  >> fs[] >>
          qcase_tac `EL jj fns = (jN, jfn)` >>
          qcase_tac `EL ii fns = (iN, ifn)` >>
          `MEM (jN,jfn) fns ∧ MEM (iN,ifn) fns`
            by metis_tac[MEM_EL, LESS_TRANS] >>
          fs[SUBSET_DEF] >> metis_tac[SND])
      >- (qcase_tac `jj < LENGTH fns` >> qcase_tac `ii < jj` >>
          qccase `EL jj fns` >>
          lfs[code_locs_FLAT_MAP, ALL_DISTINCT_FLAT, EL_MAP] >>
          qccase `EL ii fns`  >> fs[] >>
          qcase_tac `EL jj fns = (jN, jfn)` >>
          qcase_tac `EL ii fns = (iN, ifn)` >>
          `MEM (jN,jfn) fns ∧ MEM (iN,ifn) fns`
            by metis_tac[MEM_EL, LESS_TRANS] >>
          fs[SUBSET_DEF] >> metis_tac[SND])
      >- (first_x_assum irule >>
          simp[code_locs_FLAT_MAP, MEM_FLAT, PULL_EXISTS, MEM_MAP,
               EXISTS_PROD] >>
          qccase `EL i fns` >> fs[] >> metis_tac[MEM_EL, SUBSET_DEF])
      >- (first_x_assum irule >>
          simp[code_locs_FLAT_MAP, MEM_FLAT, PULL_EXISTS, MEM_MAP,
               EXISTS_PROD] >>
          qccase `EL i fns` >> fs[] >> metis_tac[MEM_EL, SUBSET_DEF])
      >- (fs[FORALL_AND_THM, code_locs_FLAT_MAP, MEM_FLAT, MEM_MAP,
             PULL_EXISTS] >>
          qccase `EL i fns` >> fs[] >>
          metis_tac[MEM_EL, SUBSET_DEF, SND])
      >- (fs[FORALL_AND_THM, code_locs_FLAT_MAP, MEM_FLAT, MEM_MAP,
             PULL_EXISTS] >>
          qccase `EL i fns` >> fs[] >>
          metis_tac[MEM_EL, SUBSET_DEF, SND])
      >- (fs[FORALL_AND_THM] >> metis_tac[SUBSET_DEF]))
  >- ((* handle *)
      qccase `remove [E1]` >> imp_res_tac remove_SING >> var_eq_tac >> fs[] >>
      qccase `remove [E2]` >> imp_res_tac remove_SING >> var_eq_tac >> fs[] >>
      fs[SUBSET_DEF, ALL_DISTINCT_APPEND] >> metis_tac[])
  >- ((* call *) qccase `remove args` >> fs[]))

val every_Fn_vs_NONE_const_0 = Q.store_thm("every_Fn_vs_NONE_const_0[simp]",
  `every_Fn_vs_NONE [const_0]`,
  EVAL_TAC)

val every_Fn_vs_NONE_remove = Q.store_thm("every_Fn_vs_NONE_remove",
  `∀es es' s.
   every_Fn_vs_NONE es ⇒
   remove es = (es',s) ⇒
   every_Fn_vs_NONE es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  every_case_tac >> fs[] >> rw[] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_REPLICATE,EVERY_MAP,UNCURRY] >>
  simp[GSYM every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  res_tac >>
  fs[Once every_Fn_vs_NONE_EVERY,EVERY_MAP,EVERY_MEM] >>
  metis_tac[remove_SING,HD,SND,PAIR]);

val every_Fn_SOME_const_0 = Q.store_thm("every_Fn_SOME_const_0[simp]",
  `every_Fn_SOME [const_0]`,
  EVAL_TAC)

val every_Fn_SOME_remove = Q.store_thm("every_Fn_SOME_remove",
  `∀es es' s.
   every_Fn_SOME es ⇒
   remove es = (es',s) ⇒
   every_Fn_SOME es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  every_case_tac >> fs[] >> rw[] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[] >>
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] >>
  simp[EVERY_REPLICATE,EVERY_MAP,UNCURRY] >>
  simp[GSYM every_Fn_SOME_EVERY] >>
  simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  res_tac >>
  fs[Once every_Fn_SOME_EVERY,EVERY_MAP,EVERY_MEM] >>
  metis_tac[remove_SING,HD,SND,PAIR]);

val _ = export_theory();
