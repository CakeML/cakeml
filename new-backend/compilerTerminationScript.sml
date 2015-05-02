open HolKernel boolLib boolSimps bossLib Defn pairTheory pred_setTheory listTheory finite_mapTheory state_transformerTheory lcsymtacs
open terminationTheory libTheory
open modLangTheory conLangTheory exhLangTheory patLangTheory;

val _ = new_theory "compilerTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val list_size_thm = store_thm(
"list_size_thm",
``∀f ls. list_size f ls = SUM (MAP f ls) + LENGTH ls``,
gen_tac >> Induct >> srw_tac[ARITH_ss][list_size_def])

(* termination proofs *)

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
  val _ = computeLib.add_persistent_funs [name^"_def"]
in (def,ind) end

val (exp_to_i1_def, exp_to_i1_ind) =
  tprove_no_defn ((exp_to_i1_def, exp_to_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);
val _ = register "exp_to_i1" (exp_to_i1_def,exp_to_i1_ind);

val (pmatch_i1_def, pmatch_i1_ind) =
  tprove_no_defn ((pmatch_i1_def, pmatch_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                        | INR (a,x,ps,y,z) => pats_size ps)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.pat_size_def]);
val _ = register "pmatch_i1" (pmatch_i1_def,pmatch_i1_ind);

val (do_eq_i1_def, do_eq_i1_ind) =
  tprove_no_defn ((do_eq_i1_def, do_eq_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i1_size x
                                        | INR (xs,ys) => v_i14_size xs)`);
val _ = register "do_eq_i1" (do_eq_i1_def,do_eq_i1_ind);

val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  WF_REL_TAC `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  Induct_on `ps` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" (pat_to_i2_def,pat_to_i2_ind);

val (exp_to_i2_def, exp_to_i2_ind) =
  tprove_no_defn ((exp_to_i2_def, exp_to_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,e) => exp_i1_size e
                                        | INR (INL (x,es)) => exp_i16_size es
                                        | INR (INR (INL (x,pes))) => exp_i13_size pes
                                        | INR (INR (INR (x,funs))) => exp_i11_size funs)`)
val _ = register "exp_to_i2" (exp_to_i2_def,exp_to_i2_ind);

val (pmatch_i2_def, pmatch_i2_ind) =
  tprove_no_defn ((pmatch_i2_def, pmatch_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_i2_size p
                                        | INR (a,x,ps,y,z) => pat_i21_size ps)` >>
  srw_tac [ARITH_ss] [pat_i2_size_def]);
val _ = register "pmatch_i2" (pmatch_i2_def,pmatch_i2_ind);

val (do_eq_i2_def, do_eq_i2_ind) =
  tprove_no_defn ((do_eq_i2_def, do_eq_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i2_size x
                                        | INR (xs,ys) => v_i23_size xs)`);
val _ = register "do_eq_i2" (do_eq_i2_def,do_eq_i2_ind);

val (is_unconditional_def, is_unconditional_ind) =
  tprove_no_defn((is_unconditional_def, is_unconditional_ind),
  WF_REL_TAC`measure pat_i2_size` >> gen_tac >>
  Induct >> simp[pat_i2_size_def] >>
  rw[] >> res_tac >> simp[pat_i2_size_def])
val _ = register "is_unconditional" (is_unconditional_def, is_unconditional_ind);

val (do_eq_exh_def, do_eq_exh_ind) =
  tprove_no_defn ((do_eq_exh_def, do_eq_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_exh_size x
                                        | INR (xs,ys) => v_exh3_size xs)`);
val _ = register "do_eq_exh" (do_eq_exh_def,do_eq_exh_ind);

val (pmatch_exh_def, pmatch_exh_ind) =
  tprove_no_defn ((pmatch_exh_def, pmatch_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,p,y,z) => pat_exh_size p
                                        | INR (x,ps,y,z) => pat_exh1_size ps)` >>
  srw_tac [ARITH_ss] [pat_exh_size_def]);
val _ = register "pmatch_exh" (pmatch_exh_def,pmatch_exh_ind);

val exp_i23_size_append = prove(
  ``∀p1 p2. exp_i23_size (p1++p2) = exp_i23_size p1 + exp_i23_size p2``,
  Induct >> simp[exp_i2_size_def])

val e2sz_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine"e2sz"`
  (e2sz (If_i2 e1 e2 e3) = e2sz e1 + e2sz e2 + e2sz e3 + 1) ∧
  (e2sz (Raise_i2 e) = e2sz e + 1) ∧
  (e2sz (Letrec_i2 funs e) = e2sz e + f2sz funs + 1) ∧
  (e2sz (Mat_i2 e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (Handle_i2 e pes) = e2sz e + p2sz pes + 4) ∧
  (e2sz (App_i2 op es) = l2sz es + 1) ∧
  (e2sz (Let_i2 x e1 e2) = e2sz e1 + e2sz e2 + 1) ∧
  (e2sz (Fun_i2 x e) = e2sz e + 1) ∧
  (e2sz (Con_i2 t es) = l2sz es + 1) ∧
  (e2sz _ = (0:num)) ∧
  (l2sz [] = 0) ∧
  (l2sz (e::es) = e2sz e + l2sz es + 1) ∧
  (p2sz [] = 0) ∧
  (p2sz ((p,e)::pes) = e2sz e + p2sz pes + 1) ∧
  (f2sz [] = 0) ∧
  (f2sz ((f,x,e)::funs) = e2sz e + f2sz funs + 1)`)
  (WF_REL_TAC`inv_image $< (\x. case x of
    | INL (e) => exp_i2_size e
    | INR (INL (es)) => exp_i26_size es
    | INR (INR (INL (pes))) => exp_i23_size pes
    | INR (INR (INR (funs))) => exp_i21_size funs)`)

val p2sz_append = prove(
  ``∀p1 p2. p2sz (p1++p2) = p2sz p1 + p2sz p2``,
  Induct >> simp[e2sz_def] >>
  Cases >> simp[e2sz_def])

val (exp_to_exh_def, exp_to_exh_ind) =
  tprove_no_defn ((exp_to_exh_def, exp_to_exh_ind),
  WF_REL_TAC `inv_image $< (\x. case x of
    | INL (_,e) => e2sz e
    | INR (INL (_,es)) => l2sz es
    | INR (INR (INL (_,pes))) => p2sz pes
    | INR (INR (INR (_,funs))) => f2sz funs)` >>
  simp[e2sz_def] >>
  rw[add_default_def] >>
  simp[p2sz_append,e2sz_def])
val _ = register "exp_to_exh" (exp_to_exh_def,exp_to_exh_ind);

val _ = map delete_const ["e2sz","p2sz","l2sz","f2sz","e2sz_UNION"]
val _ = delete_binding "e2sz_ind"

val (pat_to_exh_def, pat_to_exh_ind) =
  tprove_no_defn ((pat_to_exh_def, pat_to_exh_ind),
  WF_REL_TAC `measure pat_i2_size` >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  Induct_on `ps` >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  srw_tac [ARITH_ss] [pat_i2_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_exh" (pat_to_exh_def,pat_to_exh_ind);

val (exp_to_pat_def, exp_to_pat_ind) =
  tprove_no_defn ((exp_to_pat_def, exp_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,e) => exp_exh_size e
                                        | INR (INL (bvs,es)) => exp_exh6_size es
                                        | INR (INR (INL (bvs,funs))) => exp_exh1_size funs
                                        | INR (INR (INR (bvs,pes))) => exp_exh3_size pes)`);
val _ = register "exp_to_pat" (exp_to_pat_def,exp_to_pat_ind);

val (pat_to_pat_def, pat_to_pat_ind) =
  tprove_no_defn ((pat_to_pat_def, pat_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL p => pat_exh_size p
                                        | INR (n,ps) => pat_exh1_size ps)`);
val _ = register "pat_to_pat" (pat_to_pat_def,pat_to_pat_ind);

val (row_to_pat_def, row_to_pat_ind) =
  tprove_no_defn ((row_to_pat_def, row_to_pat_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,p) => pat_exh_size p
                                        | INR (bvs,n,k,ps) => pat_exh1_size ps)`);
val _ = register "row_to_pat" (row_to_pat_def,row_to_pat_ind);

val (Let_Els_pat_def, Let_Els_pat_ind) =
  tprove_no_defn ((Let_Els_pat_def, Let_Els_pat_ind),
  WF_REL_TAC `measure (FST o SND)`);
val _ = register "Let_Els_pat" (Let_Els_pat_def,Let_Els_pat_ind);

val (do_eq_pat_def, do_eq_pat_ind) =
  tprove_no_defn ((do_eq_pat_def, do_eq_pat_ind),
  WF_REL_TAC`inv_image $< (\x. case x of INL (v1,v2) => v_pat_size v1
                                       | INR (vs1,vs2) => v_pat1_size vs1)`);
val _ = register "do_eq_pat" (do_eq_pat_def,do_eq_pat_ind);

(* export rewrites *)
val _ = export_rewrites
  ["exp_to_pat_def"
  ,"patLang.fo_pat_def"
  ,"patLang.ground_pat_def"
  ,"patLang.pure_op_pat_def"]

val Bool_pat_eqns = save_thm("Bool_pat_eqns[simp]",
  [``Bool_pat T``,``Bool_pat F``]
  |> List.map (SIMP_CONV(std_ss)[Bool_pat_def])
  |> LIST_CONJ)

(* TODO: add missing *)
val _ = export_rewrites
["lib.the_def","lib.fapply_def"];

(* compilerLibExtra *)

open SatisfySimps arithmeticTheory miscTheory

val the_find_index_suff = store_thm("the_find_index_suff",
  ``∀P d x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (the d (find_index x ls n))``,
  rw[] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][])

val set_lunion = store_thm("set_lunion",
  ``∀l1 l2. set (lunion l1 l2) = set l1 ∪ set l2``,
  Induct >> simp[lunion_def] >> rw[EXTENSION] >> metis_tac[])
val _ = export_rewrites["set_lunion"]

val set_lshift = store_thm("set_lshift",
  ``∀ls n. set (lshift n ls) = { m-n | m | m ∈ set ls ∧ n ≤ m}``,
  Induct >> rw[lshift_def,EXTENSION,MEM_MAP,MEM_FILTER,EQ_IMP_THM] >>
  srw_tac[ARITH_ss,SATISFY_ss][] >> fsrw_tac[ARITH_ss][] >>
  TRY(qexists_tac`h`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`v`>>simp[]>>NO_TAC)>>
  TRY(qexists_tac`m`>>simp[]>>NO_TAC))
val _ = export_rewrites["set_lshift"]

val sLet_pat_thm = store_thm("sLet_pat_thm",
  ``sLet_pat e1 e2 =
    if e2 = Var_local_pat 0 then e1 else
    if ground_pat 0 e2 then
      if pure_pat e1 then e2 else Seq_pat e1 e2
    else Let_pat e1 e2``,
  Cases_on`e2`>>rw[sLet_pat_def]>>
  Cases_on`n`>>rw[sLet_pat_def])

(* constants that are just applications of higher-order operators *)

val funs_to_exh_MAP = store_thm("funs_to_exh_MAP",
  ``∀exh funs. funs_to_exh exh funs = MAP (λ(f,x,e). (f,x,exp_to_exh exh e)) funs``,
  Induct_on`funs` >> simp[exp_to_exh_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def])

val funs_to_i2_MAP = store_thm("funs_to_i2_MAP",
  ``∀g funs. funs_to_i2 g funs = MAP (λ(f,x,e). (f,x,exp_to_i2 g e)) funs``,
  Induct_on`funs` >> simp[exp_to_i2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i2_def])

val funs_to_i1_MAP = store_thm("funs_to_i1_MAP",
  ``∀menv env funs. funs_to_i1 menv env funs = MAP (λ(f,x,e). (f,x,exp_to_i1 menv (env \\ x) e)) funs``,
  Induct_on`funs` >> simp[exp_to_i1_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i1_def])

val _ = export_theory()
