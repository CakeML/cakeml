open HolKernel boolLib boolSimps bossLib lcsymtacs miscLib
open listTheory patLangTheory callLangTheory
val _ = new_theory"callLangProof"

val pComp_def = tDefine"pComp"`
  (pComp (Raise_pat e) =
    Raise (pComp e)) ∧
  (pComp (Handle_pat e1 e2) =
    Handle (pComp e1) (pComp e2)) ∧
  (pComp (Lit_pat (IntLit i)) =
    Op (Const i) []) ∧
  (pComp (Lit_pat (Word8 w)) =
    Op (Const (&w2n w)) []) ∧
  (pComp (Lit_pat (Char c)) =
    Op (Const (& ORD c)) []) ∧
  (pComp (Lit_pat (StrLit s)) =
    Op (Cons string_tag) (MAP (λc. Op (Const (& ORD c)) []) s)) ∧
  (pComp (Lit_pat (Bool b)) =
    Op (Cons (bool_to_tag b)) []) ∧
  (pComp (Lit_pat Unit) =
    Op (Cons unit_tag) []) ∧
  (pComp (Con_pat cn es) =
    Op (Cons (cn+block_tag)) (MAP pComp es)) ∧
  (pComp (Var_local_pat n) =
    Var n) ∧
  (pComp (Var_global_pat n) =
    Op (Global n) []) ∧
  (pComp (Fun_pat e) =
    Fn (pComp e)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Opapp)) es) =
    if LENGTH es ≠ 2 then Var 0 else
    App (pComp (EL 0 es)) (pComp (EL 1 es))) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Plus))) es) =
    Op Add (MAP pComp es)) ∧
  (* TODO: rest *)
  (pComp (App_pat (Op_pat (Init_global_var_i2 n)) es) =
    Op (SetGlobal n) (MAP pComp es)) ∧
  (pComp (App_pat (Tag_eq_pat n) es) =
    Op (TagEq n) (MAP pComp es)) ∧
  (pComp (App_pat (El_pat n) es) =
    Op (El n) (MAP pComp es)) ∧
  (pComp (If_pat e1 e2 e3) =
    If (pComp e1) (pComp e2) (pComp e3)) ∧
  (pComp (Let_pat e1 e2) =
    Let [pComp e1] (pComp e2)) ∧
  (pComp (Seq_pat e1 e2) =
    Let [pComp e1;pComp e2] (Var 1)) ∧
  (pComp (Letrec_pat es e) =
    Letrec (MAP pComp es) (pComp e)) ∧
  (pComp (Extend_global_pat n) =
   Let (REPLICATE n (Op AllocGlobal []))
     (Op (Cons unit_tag) []))`
    (WF_REL_TAC `measure exp_pat_size` >>
     simp[exp_pat_size_def] >>
     rpt conj_tac >> rpt gen_tac >>
     Induct_on`es` >> simp[exp_pat_size_def] >>
     rw[] >> res_tac >> fs[] >> simp[exp_pat_size_def] >>
     Cases_on`es`>>fs[LENGTH_NIL,exp_pat_size_def] >> simp[])
val _ = export_rewrites["pComp_def"]

val v_to_Cv_def = tDefine"v_to_Cv"`
  (v_to_Cv (Litv_pat (IntLit i)) = (Number i)) ∧
  (v_to_Cv (Litv_pat (Word8 w)) = (Number (&w2n w))) ∧
  (v_to_Cv (Litv_pat (Char c)) = (Number (& ORD c))) ∧
  (v_to_Cv (Litv_pat (StrLit s)) =
    (Block string_tag (MAP (Number o $& o ORD) s))) ∧
  (v_to_Cv (Litv_pat (Bool b)) = (Block (bool_to_tag b) [])) ∧
  (v_to_Cv (Litv_pat Unit) = (Block unit_tag [])) ∧
  (v_to_Cv (Loc_pat m) = (RefPtr m)) ∧
  (v_to_Cv (Conv_pat cn vs) = (Block (cn+block_tag) (MAP (v_to_Cv) vs))) ∧
  (v_to_Cv (Vectorv_pat vs) = (Block vector_tag (MAP (v_to_Cv) vs))) ∧
  (v_to_Cv (Closure_pat vs e) = (Closure (MAP (v_to_Cv) vs) (pComp e))) ∧
  (v_to_Cv (Recclosure_pat vs es k) = (Recclosure (MAP (v_to_Cv) vs) (MAP pComp es) k))`
    (WF_REL_TAC`measure (v_pat_size)` >> simp[v_pat_size_def] >>
     rpt conj_tac >> rpt gen_tac >>
     Induct_on`vs` >> simp[v_pat_size_def] >>
     rw[] >> res_tac >> fs[] >> simp[v_pat_size_def])
val _ = export_rewrites["v_to_Cv_def"]

val sv_to_Cref_def = Define`
  (sv_to_Cref (Refv v) = ValueArray [v_to_Cv v]) ∧
  (sv_to_Cref (Varray vs) = ValueArray (MAP v_to_Cv vs))`

val s_to_Cs_def = Define`
  s_to_Cs (((c,s),g):v_pat count_store_genv) =
    <| globals := MAP (OPTION_MAP v_to_Cv) g;
       refs := alist_to_fmap (GENLIST (λi. (i, sv_to_Cref (EL i s))) (LENGTH s));
       clock := c;
       code := FEMPTY;
       output := "" |>`

val res_to_Cres_def = Define`
  (res_to_Cres f (Rval v) = Result (f v)) ∧
  (res_to_Cres f (Rerr (Rraise v)) = Exception (v_to_Cv v)) ∧
  (res_to_Cres f (Rerr Rtimeout_error) = TimeOut) ∧
  (res_to_Cres f (Rerr Rtype_error) = Error)`
val _ = export_rewrites["res_to_Cres_def"]

(* TODO: copied from free_varsTheory *)

open boolSimps miscTheory evalPropsTheory pred_setTheory arithmeticTheory rich_listTheory semanticPrimitivesTheory pairTheory

val free_vars_pat_def = tDefine"free_vars_pat"`
  free_vars_pat (Raise_pat e) = free_vars_pat e ∧
  free_vars_pat (Handle_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Lit_pat _) = [] ∧
  free_vars_pat (Con_pat _ es) = free_vars_list_pat es ∧
  free_vars_pat (Var_local_pat n) = [n] ∧
  free_vars_pat (Var_global_pat _) = [] ∧
  free_vars_pat (Fun_pat e) = lshift 1 (free_vars_pat e) ∧
  free_vars_pat (App_pat _ es) = free_vars_list_pat es ∧
  free_vars_pat (If_pat e1 e2 e3) = lunion (free_vars_pat e1) (lunion (free_vars_pat e2) (free_vars_pat e3)) ∧
  free_vars_pat (Let_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Seq_pat e1 e2) = lunion (free_vars_pat e1) (free_vars_pat e2) ∧
  free_vars_pat (Letrec_pat es e) = lunion (free_vars_defs_pat (LENGTH es) es) (lshift (LENGTH es) (free_vars_pat e)) ∧
  free_vars_pat (Extend_global_pat _) = [] ∧
  free_vars_list_pat [] = [] ∧
  free_vars_list_pat (e::es) = lunion (free_vars_pat e) (free_vars_list_pat es) ∧
  free_vars_defs_pat _ [] = [] ∧
  free_vars_defs_pat n (e::es) = lunion (lshift (n+1) (free_vars_pat e)) (free_vars_defs_pat n es)`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_pat_size e
  | INR (INL es) => exp_pat1_size es
  | INR (INR (_,es)) => exp_pat1_size es)`)
val _ = export_rewrites["free_vars_pat_def"]

val free_vars_defs_pat_MAP = store_thm("free_vars_defs_pat_MAP",
  ``set (free_vars_defs_pat n es) = set (lshift (n+1) (free_vars_list_pat es))``,
  Induct_on`es`>>simp[] >> fs[EXTENSION] >>
  rw[EQ_IMP_THM] >> simp[] >> metis_tac[])

val free_vars_list_pat_MAP = store_thm("free_vars_list_pat_MAP",
  ``∀es. set (free_vars_list_pat es) = set (FLAT (MAP free_vars_pat es))``,
  Induct >> simp[])
val _ = export_rewrites["free_vars_defs_pat_MAP","free_vars_list_pat_MAP"]

val free_vars_pat_sIf = store_thm("free_vars_pat_sIf",
  ``∀e1 e2 e3. set (free_vars_pat (sIf_pat e1 e2 e3)) ⊆ set (free_vars_pat (If_pat e1 e2 e3))``,
  rw[sIf_pat_def] >>
  BasicProvers.CASE_TAC >> simp[SUBSET_DEF] >>
  BasicProvers.CASE_TAC >> simp[] >> rw[])

val free_vars_ground_pat = store_thm("free_vars_ground_pat",
  ``(∀e n. ground_pat n e ⇒ set (free_vars_pat e) ⊆ count n) ∧
    (∀es n. ground_list_pat n es ⇒ set (free_vars_list_pat es) ⊆ count n)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_pat``)) >>
  simp[] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  rw[] >> res_tac >>
  DECIDE_TAC)

val (closed_pat_rules,closed_pat_ind,closed_pat_cases) = Hol_reln`
(closed_pat (Litv_pat l)) ∧
(EVERY (closed_pat) vs ⇒ closed_pat (Conv_pat cn vs)) ∧
(EVERY (closed_pat) env ∧ set (free_vars_pat b) ⊆ count (LENGTH env + 1)
⇒ closed_pat (Closure_pat env b)) ∧
(EVERY (closed_pat) env ∧ d < LENGTH defs ∧
 EVERY (λe. set (free_vars_pat e) ⊆ count (LENGTH env + LENGTH defs + 1)) defs
⇒ closed_pat (Recclosure_pat env defs d)) ∧
(closed_pat (Loc_pat n)) ∧
(EVERY closed_pat vs ⇒ closed_pat (Vectorv_pat vs))`;

val closed_pat_lit_loc_conv = store_thm("closed_pat_lit_loc_conv",
  ``closed_pat (Litv_pat l) ∧ closed_pat (Loc_pat n) ∧
    (closed_pat (Conv_pat a bs) ⇔ EVERY closed_pat bs) ∧
    (closed_pat (Vectorv_pat bs) ⇔ EVERY closed_pat bs)``,
  rw[closed_pat_cases])
val _ = export_rewrites["closed_pat_lit_loc_conv"]

val csg_closed_pat_def = Define`
  csg_closed_pat csg ⇔
    EVERY (sv_every closed_pat) (SND(FST csg)) ∧
    EVERY (OPTION_EVERY closed_pat) (SND csg)`

val v_to_list_pat_closed = prove(
  ``∀v vs. v_to_list_pat v = SOME vs ⇒ closed_pat v ⇒ EVERY closed_pat vs``,
  ho_match_mp_tac v_to_list_pat_ind >>
  simp[v_to_list_pat_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val char_list_to_v_pat_closed = prove(
  ``∀ls. closed_pat (char_list_to_v_pat ls)``,
  Induct >> simp[char_list_to_v_pat_def])

val do_app_pat_cases = store_thm("do_app_pat_cases",
  ``do_app_pat s op vs = SOME x ⇒
    (∃z n1 n2. op = Op_pat (Op_i2 (Opn z)) ∧ vs = [Litv_pat (IntLit n1); Litv_pat (IntLit n2)]) ∨
    (∃z n1 n2. op = Op_pat (Op_i2 (Opb z)) ∧ vs = [Litv_pat (IntLit n1); Litv_pat (IntLit n2)]) ∨
    (∃v1 v2. op = Op_pat (Op_i2 Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = Op_pat (Op_i2 Opassign) ∧ vs = [Loc_pat lnum; v]) ∨
    (∃n. op = Op_pat (Op_i2 Opderef) ∧ vs = [Loc_pat n]) ∨
    (∃v. op = Op_pat (Op_i2 Opref) ∧ vs = [v]) ∨
    (∃idx v. op = Op_pat (Init_global_var_i2 idx) ∧ vs = [v]) ∨
    (∃n w. op = Op_pat (Op_i2 Aw8alloc) ∧ vs = [Litv_pat (IntLit n); Litv_pat (Word8 w)]) ∨
    (∃lnum i. op = Op_pat (Op_i2 Aw8sub) ∧ vs = [Loc_pat lnum; Litv_pat (IntLit i)]) ∨
    (∃n. op = Op_pat (Op_i2 Aw8length) ∧ vs = [Loc_pat n]) ∨
    (∃lnum i w. op = Op_pat (Op_i2 Aw8update) ∧ vs = [Loc_pat lnum; Litv_pat (IntLit i); Litv_pat (Word8 w)]) ∨
    (∃c. op = Op_pat (Op_i2 Ord) ∧ vs = [Litv_pat (Char c)]) ∨
    (∃n. op = Op_pat (Op_i2 Chr) ∧ vs = [Litv_pat (IntLit n)]) ∨
    (∃z c1 c2. op = Op_pat (Op_i2 (Chopb z)) ∧ vs = [Litv_pat (Char c1); Litv_pat (Char c2)]) ∨
    (∃v s. op = Op_pat (Op_i2 Explode) ∧ vs = [Litv_pat (StrLit s)]) ∨
    (∃v ls. op = Op_pat (Op_i2 Implode) ∧ vs = [v] ∧ (v_pat_to_char_list v = SOME ls)) ∨
    (∃s. op = Op_pat (Op_i2 Strlen) ∧ vs = [Litv_pat (StrLit s)]) ∨
    (∃v vs'. op = Op_pat (Op_i2 VfromList) ∧ vs = [v] ∧ (v_to_list_pat v = SOME vs')) ∨
    (∃vs' i. op = Op_pat (Op_i2 Vsub) ∧ vs = [Vectorv_pat vs'; Litv_pat (IntLit i)]) ∨
    (∃vs'. op = Op_pat (Op_i2 Vlength) ∧ vs = [Vectorv_pat vs']) ∨
    (∃v n. op = Op_pat (Op_i2 Aalloc) ∧ vs = [Litv_pat (IntLit n); v]) ∨
    (∃lnum i. op = Op_pat (Op_i2 Asub) ∧ vs = [Loc_pat lnum; Litv_pat (IntLit i)]) ∨
    (∃n. op = Op_pat (Op_i2 Alength) ∧ vs = [Loc_pat n]) ∨
    (∃lnum i v. op = Op_pat (Op_i2 Aupdate) ∧ vs = [Loc_pat lnum; Litv_pat (IntLit i); v]) ∨
    (∃n tag v. op = Tag_eq_pat n ∧ vs = [Conv_pat tag v]) ∨
    (∃n tag v. op = El_pat n ∧ vs = [Conv_pat tag v])``,
  PairCases_on`s`>>rw[do_app_pat_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[]);

val evaluate_pat_raise_rval = store_thm("evaluate_pat_raise_rval",
  ``∀ck env s e s' v. ¬evaluate_pat ck env s (Raise_pat e) (s', Rval v)``,
  rw[Once evaluate_pat_cases])
val _ = export_rewrites["evaluate_pat_raise_rval"]

val evaluate_pat_closed = store_thm("evaluate_pat_closed",
  ``(∀ck env s e res. evaluate_pat ck env s e res ⇒
       set (free_vars_pat e) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result closed_pat closed_pat (SND res)) ∧
    (∀ck env s es res. evaluate_list_pat ck env s es res ⇒
       set (free_vars_list_pat es) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result (EVERY closed_pat) closed_pat (SND res))``,
  ho_match_mp_tac evaluate_pat_ind >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >> fs[] >>
    fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
    Cases>>simp[ADD1] >> rw[] >>
    res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >- (
    simp[csg_closed_pat_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> first_x_assum(qspec_then`n`mp_tac) >> simp[] ) >>
  strip_tac >- (
    simp[Once closed_pat_cases,SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    Cases >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    strip_tac >> fs[] >>
    fs[do_opapp_pat_def] >>
    Cases_on`vs`>>fs[]>>Cases_on`t`>>fs[]>>
    Cases_on`t'`>>fs[]>>Cases_on`h`>>fs[]>>
    rpt BasicProvers.VAR_EQ_TAC >>
    rfs[csg_closed_pat_def,
        Q.SPEC`Closure_pat X Y`closed_pat_cases,
        Q.SPEC`Recclosure_pat X Y Z`closed_pat_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[ARITH_ss][ADD1] >>
    simp[build_rec_env_pat_def,EVERY_GENLIST] >>
    fsrw_tac[ARITH_ss][EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] >>
    simp[Once closed_pat_cases,EVERY_MEM,MEM_EL,PULL_EXISTS]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    strip_tac >> fs[] >>
    PairCases_on`s2` >>
    imp_res_tac do_app_pat_cases >>
    fs[do_app_pat_def] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    simp[prim_exn_pat_def] >>
    imp_res_tac v_to_list_pat_closed >>
    fs[store_assign_def,store_lookup_def,LET_THM,csg_closed_pat_def,UNCURRY,store_alloc_def] >>
    rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[prim_exn_pat_def] >>
    fs[EVERY_MEM] >>
    simp[REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS] >>
    TRY (
      fs[MEM_EL,PULL_EXISTS] >>
      last_x_assum(qspec_then`lnum`mp_tac) >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    TRY (
      fs[MEM_EL,PULL_EXISTS,EL_LUPDATE] >> rw[] >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_LUPDATE] >>
      rw[] >>
      last_x_assum(qspec_then`lnum`mp_tac) >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    simp[char_list_to_v_pat_closed] >>
    metis_tac[MEM_LUPDATE_E,sv_every_def,MEM_EL,OPTION_EVERY_def,NOT_LESS_EQUAL,GREATER_EQ] ) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> simp[do_if_pat_def] >>
    Cases_on`l`>>simp[] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1] >>
    Cases >> simp[ADD1] >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,build_rec_env_pat_def,EVERY_GENLIST] >>
    conj_tac >- (
      rw[] >>
      Cases_on`x < LENGTH funs`>>simp[] >>
      REWRITE_TAC[Once ADD_SYM] >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    simp[Once closed_pat_cases] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    rw[] >>
    fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_SYM] >>
    Cases_on`x < LENGTH funs + 1`>>simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[] ) >>
  simp[csg_closed_pat_def,EVERY_GENLIST])

(* -- *)

(* TODO: move? *)

val tEval_MAP_Op_Const = store_thm("tEval_MAP_Op_Const",
  ``∀f env s ls.
      tEval (MAP (λx. Op (Const (f x)) []) ls,env,s) =
      (Result (MAP (Number o f) ls),s)``,
  ntac 3 gen_tac >> Induct >>
  simp[tEval_def] >>
  simp[Once tEval_CONS] >>
  simp[tEval_def,tEvalOp_def])

val tEval_REPLICATE_Op_AllocGlobal = store_thm("tEval_REPLICATE_Op_AllocGlobal",
  ``∀n env s. tEval (REPLICATE n (Op AllocGlobal []),env,s) =
              (Result (GENLIST (K(Number 0)) n),s with globals := s.globals ++ GENLIST (K NONE) n)``,
  Induct >> simp[tEval_def,REPLICATE] >- (
    simp[call_state_component_equality] ) >>
  simp[Once tEval_CONS,tEval_def,tEvalOp_def,GENLIST_CONS] >>
  simp[call_state_component_equality])

val evaluate_list_pat_length = store_thm("evaluate_list_pat_length",
  ``∀ck env s es x vs.
    evaluate_list_pat ck env s es (x,Rval vs) ⇒
    (LENGTH vs = LENGTH es)``,
  Induct_on`es`>>simp[] >>
  simp[Once evaluate_pat_cases,PULL_EXISTS] >>
  rw[] >> res_tac)
(* -- *)

val pComp_correct = store_thm("pComp_correct",
  ``(∀ck env s e res. evaluate_pat ck env s e res ⇒
       ck ∧
       set (free_vars_pat e) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ∧
       SND res ≠ Rerr Rtype_error ⇒
       tEval ([pComp e],MAP v_to_Cv env,s_to_Cs s) =
         (res_to_Cres (λv. [v_to_Cv v]) (SND res), s_to_Cs (FST res))) ∧
    (∀ck env s es res. evaluate_list_pat ck env s es res ⇒
       ck ∧
       set (free_vars_list_pat es) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ∧
       SND res ≠ Rerr Rtype_error ⇒
       tEval (MAP pComp es,MAP v_to_Cv env,s_to_Cs s) =
         (res_to_Cres (MAP v_to_Cv) (SND res), s_to_Cs (FST res)))``,
  ho_match_mp_tac evaluate_pat_strongind >>
  strip_tac >- (
    Cases_on`l`>>
    rw[tEval_def,tEvalOp_def] >>
    simp[tEval_MAP_Op_Const,combinTheory.o_DEF] ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >>
    Cases_on`err`>>simp[] ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[] >> first_x_assum match_mp_tac >>
    imp_res_tac evaluate_pat_closed >> rfs[] >>
    fs[SUBSET_DEF,PULL_EXISTS] >>
    Cases >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    simp[tEval_def] >>
    Cases_on`err`>>simp[] ) >>
  strip_tac >- simp[tEval_def,ETA_AX,tEvalOp_def] >>
  strip_tac >- (
    Cases_on`err`>>
    simp[tEval_def,ETA_AX,tEvalOp_def] ) >>
  strip_tac >- simp[tEval_def,EL_MAP] >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def,tEvalOp_def] >>
    Cases_on`s`>>simp[s_to_Cs_def,get_global_def,EL_MAP] ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- simp[tEval_def,ETA_AX] >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[tEval_def] >>
    imp_res_tac evaluate_list_pat_length >>
    Cases_on`vs`>>fs[do_opapp_pat_def] >>
    Cases_on`t`>>fs[do_opapp_pat_def] >>
    Cases_on`t'`>>fs[do_opapp_pat_def] >>
    Cases_on`es`>>fs[]>>
    Cases_on`t`>>fs[LENGTH_NIL]>>
    fs[tEval_def] >>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    rw[] >>
    qpat_assum`X ⇒ Y`mp_tac >>
    discharge_hyps >- (
      imp_res_tac (CONJUNCT2 evaluate_pat_closed) >>
      fs[] >> rfs[] >>
      Cases_on`h`>>fs[] >>
      pop_assum mp_tac >> simp[Once closed_pat_cases] >>
      strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[csg_closed_pat_def,SUBSET_DEF,ADD1] >>
      fs[EVERY_MEM,PULL_EXISTS,build_rec_env_pat_def,MEM_GENLIST] >>
      simp[Once closed_pat_cases,EVERY_MEM,PULL_EXISTS,SUBSET_DEF] >>
      `MEM (EL n l0) l0` by metis_tac[MEM_EL] >>
      rw[] >> res_tac >> fs[] ) >>
    strip_tac >>
    Cases_on`h`>>fs[dest_closure_def,s_to_Cs_def,ETA_AX,dec_clock_def] >>
    rw[] >> fs[] >> rfs[EL_MAP] >> fs[build_rec_env_pat_def] >>
    fsrw_tac[ARITH_ss][] >>
    fs[MAP_GENLIST,combinTheory.o_DEF,ETA_AX] >>
    fsrw_tac[ETA_ss][] ) >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[tEval_def] >>
    imp_res_tac evaluate_list_pat_length >>
    Cases_on`vs`>>fs[do_opapp_pat_def] >>
    Cases_on`t`>>fs[do_opapp_pat_def] >>
    Cases_on`t'`>>fs[do_opapp_pat_def] >>
    Cases_on`es`>>fs[]>>
    Cases_on`t`>>fs[LENGTH_NIL]>>
    fs[tEval_def] >>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    rw[] >>
    Cases_on`h`>>fs[dest_closure_def,s_to_Cs_def,ETA_AX,dec_clock_def] >>
    rw[] >> rw[] >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[] >>
    cheat ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >>
    cheat ) >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[] >>
    Cases_on`v`>>fs[]>>rw[]>>fs[do_if_pat_def]>>
    Cases_on`l`>>fs[]>>
    Cases_on`b`>>fs[]>>rw[]>>
    imp_res_tac evaluate_pat_closed >>fs[]) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >>
    imp_res_tac evaluate_pat_closed >>fs[] >>
    Cases_on`err`>>fs[] ) >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >>
    qpat_assum`X ⇒ Y`mp_tac >>
    discharge_hyps >- (
      imp_res_tac evaluate_pat_closed >>fs[] >>
      fs[SUBSET_DEF,PULL_EXISTS] >>
      Cases >> rw[] >> res_tac >> fs[] >>
      fsrw_tac[ARITH_ss][]) >>
    simp[] ) >>
  strip_tac >- (
    simp[tEval_def] >> Cases_on`err`>>simp[] ) >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >> fs[] >>
    qpat_assum`X ⇒ Y`mp_tac >>
    discharge_hyps >- (
      imp_res_tac evaluate_pat_closed >>fs[] ) >>
    rw[] >>
    Cases_on`res`>>fs[]>>
    Cases_on`r`>>fs[]>>simp[]>>
    Cases_on`e''`>>simp[]) >>
  strip_tac >- (
    simp[tEval_def] >>
    Cases_on`err`>>simp[] ) >>
  strip_tac >- (
    simp[tEval_def] >>
    rw[] >> fs[] >>
    qpat_assum`X ⇒ Y`mp_tac >>
    discharge_hyps >- (
      imp_res_tac evaluate_pat_closed >>fs[] >>
      fs[SUBSET_DEF,build_rec_env_pat_def,EVERY_GENLIST,PULL_EXISTS] >>
      simp[Once closed_pat_cases,SUBSET_DEF,EVERY_MEM,PULL_EXISTS] >>
      fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      rw[] >> res_tac >> fs[] >> simp[] >>
      fs[EVERY_MEM] ) >>
    rw[build_rec_env_pat_def,build_recc_def,MAP_GENLIST,combinTheory.o_DEF,ETA_AX,MAP_MAP_o] >>
    fsrw_tac[ETA_ss][] ) >>
  strip_tac >- (
    simp[tEval_def] >>
    simp[tEval_REPLICATE_Op_AllocGlobal,tEvalOp_def] >>
    Cases_on`s`>>simp[s_to_Cs_def,MAP_GENLIST,combinTheory.o_DEF,combinTheory.K_DEF] ) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >>
    simp[Once tEval_CONS] >>
    imp_res_tac evaluate_pat_closed >> fs[] ) >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >> fs[] >>
    simp[Once tEval_CONS] >>
    Cases_on`err`>>fs[]) >>
  simp[tEval_def] >> rw[] >>
  simp[Once tEval_CONS] >>
  imp_res_tac evaluate_pat_closed >> fs[] >>
  Cases_on`err`>>fs[])

val _ = export_theory()
