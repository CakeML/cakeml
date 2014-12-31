open HolKernel boolLib boolSimps bossLib lcsymtacs miscLib intLib
open rich_listTheory listTheory alistTheory finite_mapTheory pred_setTheory stringTheory integerTheory arithmeticTheory
open patLangTheory callLangTheory
open astTheory semanticPrimitivesTheory
open terminationTheory free_varsTheory compilerTerminationTheory
val _ = new_theory"callLangProof"

(* TODO: move? *)
val ALOOKUP_SNOC = store_thm("ALOOKUP_SNOC",
  ``∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE``,
  Induct >> simp[] >>
  Cases >> simp[] >> rw[])

val ALOOKUP_GENLIST = store_thm("ALOOKUP_GENLIST",
  ``∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE``,
  gen_tac >> Induct >> simp[GENLIST] >> rw[] >> fs[ALOOKUP_SNOC] >>
  rw[] >> fsrw_tac[ARITH_ss][])

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

val bool_to_val_thm = store_thm("bool_to_val_thm",
  ``bool_to_val b = callLang$Block (if b then 1 else 0) []``,
  Cases_on`b`>>rw[bool_to_val_def])
val bool_to_tag_thm = store_thm("bool_to_tag_thm",
  ``bool_to_tag b = if b then 1 else 0``,
  Cases_on`b`>>rw[bytecodeTheory.bool_to_tag_def])
(* -- *)

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
    if LENGTH es ≠ 2 then Op Sub (MAP pComp es) else
    App (pComp (EL 0 es)) (pComp (EL 1 es))) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Plus))) es) =
    Op Add (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Minus))) es) =
    Op Sub (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Times))) es) =
    Op Mult (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Divide))) es) =
    Let (MAP pComp es)
      (If (Op Equal [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (div_tag+block_tag)) []))
          (Op Div [Var 0; Var 1]))) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opn Modulo))) es) =
    Let (MAP pComp es)
      (If (Op Equal [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (div_tag+block_tag)) []))
          (Op Mod [Var 0; Var 1]))) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opb Lt))) es) =
    Op Less (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opb Gt))) es) =
    Let (MAP pComp es)
      (Op Less [Var 1; Var 0])) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opb Leq))) es) =
    Let [Op Sub (MAP pComp es)]
      (Op Less [Var 0; Op (Const 1) []])) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Opb Geq))) es) =
    Let (MAP pComp es)
      (Op Less [Op Sub [Var 1; Var 0]; Op (Const 1) []])) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Chopb Lt))) es) =
    Op Less (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Chopb Gt))) es) =
    Let (MAP pComp es)
      (Op Less [Var 1; Var 0])) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Chopb Leq))) es) =
    Let [Op Sub (MAP pComp es)]
      (Op Less [Var 0; Op (Const 1) []])) ∧
  (pComp (App_pat (Op_pat (Op_i2 (Chopb Geq))) es) =
    Let (MAP pComp es)
      (Op Less [Op Sub [Var 1; Var 0]; Op (Const 1) []])) ∧
  (pComp (App_pat (Op_pat (Op_i2 Equality)) es) =
    Let [Op Equal (MAP pComp es)]
      (If (Op IsBlock [Var 0]) (Var 0)
          (Raise (Op (Cons (eq_tag+block_tag)) [])))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Opassign)) es) =
    Let (MAP pComp es)
      (Let [Op Update [Var 0; Op (Const 0) []; Var 1]]
         (Op (Cons unit_tag) []))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Opderef)) es) =
    Op Deref (MAP pComp es ++ [Op (Const 0) []])) ∧
  (pComp (App_pat (Op_pat (Op_i2 Opref)) es) =
    Op Ref (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Ord)) es) =
    if LENGTH es ≠ 1 then Op Sub (MAP pComp es) else pComp (HD es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Chr)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 0; Op (Const 0) []])
        (Raise (Op (Cons (chr_tag+block_tag)) []))
        (If (Op Less [Op (Const 255) []; Var 0])
          (Raise (Op (Cons (chr_tag+block_tag)) []))
          (Var 0)))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aw8alloc)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 0; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (Op RefByte [Var 0; Var 1]))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aw8sub)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (If (Op Less [Var 1; Op LengthByte [Var 0]])
              (Op DerefByte [Var 0; Var 1])
              (Raise (Op (Cons (subscript_tag + block_tag)) []))))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aw8length)) es) =
    Op LengthByte (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aw8update)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (If (Op Less [Var 1; Op LengthByte [Var 0]])
              (Let [Op UpdateByte [Var 0; Var 1; Var 2]]
                 (Op (Cons unit_tag) []))
              (Raise (Op (Cons (subscript_tag + block_tag)) []))))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Explode)) es) =
    Op ToList (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Implode)) es) =
    Op (FromList string_tag) (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Strlen)) es) =
    Op LengthBlock (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 VfromList)) es) =
    Op (FromList vector_tag) (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Vsub)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (If (Op Less [Var 1; Op LengthBlock [Var 0]])
              (Op El2 [Var 0; Var 1])
              (Raise (Op (Cons (subscript_tag + block_tag)) []))))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Vlength)) es) =
    Op LengthBlock (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aalloc)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 0; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (Op Ref2 [Var 0; Var 1]))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Asub)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (If (Op Less [Var 1; Op Length [Var 0]])
              (Op Deref [Var 0; Var 1])
              (Raise (Op (Cons (subscript_tag + block_tag)) []))))) ∧
  (pComp (App_pat (Op_pat (Op_i2 Alength)) es) =
    Op Length (MAP pComp es)) ∧
  (pComp (App_pat (Op_pat (Op_i2 Aupdate)) es) =
    Let (MAP pComp es)
      (If (Op Less [Var 1; Op (Const 0) []])
          (Raise (Op (Cons (subscript_tag + block_tag)) []))
          (If (Op Less [Var 1; Op Length [Var 0]])
              (Let [Op Update [Var 0; Var 1; Var 2]]
                 (Op (Cons unit_tag) []))
              (Raise (Op (Cons (subscript_tag + block_tag)) []))))) ∧
  (pComp (App_pat (Op_pat (Init_global_var_i2 n)) es) =
    Let [Op (SetGlobal n) (MAP pComp es)]
      (Op (Cons unit_tag) [])) ∧
  (pComp (App_pat (Tag_eq_pat n) es) =
    Op (TagEq (n+block_tag)) (MAP pComp es)) ∧
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
     Cases_on`es`>>fs[LENGTH_NIL,exp_pat_size_def] >> simp[] >>
     Cases_on`t`>>fs[exp_pat_size_def] >> rw[] >> simp[]>>
     Cases_on`t'`>>fs[exp_pat_size_def] >> rw[] >> simp[])
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
  (sv_to_Cref (Varray vs) = ValueArray (MAP v_to_Cv vs)) ∧
  (sv_to_Cref (W8array bs) = ByteArray bs)`

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

val do_eq_pat_call_equal = store_thm("do_eq_pat_call_equal",
  ``(∀v1 v2. do_eq_pat v1 v2 ≠ Eq_type_error ⇒
      (do_eq_pat v1 v2 = call_equal (v_to_Cv v1) (v_to_Cv v2))) ∧
    (∀vs1 vs2. do_eq_list_pat vs1 vs2 ≠ Eq_type_error ⇒
      (do_eq_list_pat vs1 vs2 = call_equal_list (MAP v_to_Cv vs1) (MAP v_to_Cv vs2)))``,
  ho_match_mp_tac do_eq_pat_ind >>
  simp[do_eq_pat_def,call_equal_def] >>
  conj_tac >- (
    Cases >> Cases >> simp[lit_same_type_def,call_equal_def,ORD_11,bool_to_tag_thm] >>
    TRY(rw[] >> pop_assum mp_tac >> rw[] >> NO_TAC) >>
    qid_spec_tac`s'` >>
    Induct_on`s` >> simp[LENGTH_NIL_SYM,call_equal_def] >> rw[] >>
    TRY (
      spose_not_then strip_assume_tac >> rw[] >> fs[] >> NO_TAC) >>
    Cases_on`s'`>>fs[call_equal_def,ORD_11] >> rw[]) >>
  conj_tac >- rw[ETA_AX] >>
  conj_tac >- rw[ETA_AX] >>
  rw[] >>
  Cases_on`v1`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  Cases_on`v2`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  fs[do_eq_pat_def,call_equal_def,lit_same_type_def,ORD_11,bool_to_tag_thm] >>
  rw[]>>fs[]>>rfs[ETA_AX]>>
  BasicProvers.CASE_TAC>>fs[]>>
  rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[])

val call_to_list_correct = store_thm("call_to_list_correct",
  ``∀ls. call_to_list (MAP (Number o $& o ORD) ls) =
         v_to_Cv (char_list_to_v_pat ls)``,
  Induct >> simp[call_to_list_def,char_list_to_v_pat_def])

val call_from_char_list_correct = store_thm("call_from_char_list_correct",
  ``∀v ls. (v_pat_to_char_list v = SOME ls) ⇒
           (call_from_list (v_to_Cv v) = SOME (MAP (Number o $& o ORD) ls))``,
  ho_match_mp_tac v_pat_to_char_list_ind >>
  simp[v_pat_to_char_list_def,call_from_list_def] >>
  rw[] >>
  Cases_on`v`>>fs[v_pat_to_char_list_def] >>
  Cases_on`l`>>fs[v_pat_to_char_list_def,call_from_list_def] >>
  rw[]>>fs[]>>
  Cases_on`h`>>fs[v_pat_to_char_list_def,call_from_list_def] >>
  Cases_on`l`>>fs[v_pat_to_char_list_def,call_from_list_def] >>
  Cases_on`t`>>fs[v_pat_to_char_list_def,call_from_list_def] >>
  Cases_on`t'`>>fs[v_pat_to_char_list_def,call_from_list_def] >>
  rw[]>>fs[]>>
  Cases_on`v_pat_to_char_list h`>>fs[]>> rw[])

val call_from_list_correct = store_thm("call_from_list_correct",
  ``∀v ls. (v_to_list_pat v = SOME ls) ⇒
           (call_from_list (v_to_Cv v) = SOME (MAP v_to_Cv ls))``,
  ho_match_mp_tac v_to_list_pat_ind >>
  simp[v_to_list_pat_def,call_from_list_def] >>
  rw[] >> Cases_on`v_to_list_pat v`>>fs[]>> rw[])

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
    simp[tEval_def] >> rw[] >>
    PairCases_on`s2` >>
    imp_res_tac do_app_pat_cases >>
    fs[do_app_pat_def] >> rw[] >- (
      Cases_on`z`>>fs[tEval_def,ETA_AX,tEvalOp_def] >>
      rw[opn_lookup_def,call_equal_def,bool_to_val_thm] >>
      TRY IF_CASES_TAC >> fs[] >> fsrw_tac[ARITH_ss][] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rw[prim_exn_pat_def,opn_lookup_def] )
    >- (
      Cases_on`z`>>fs[tEval_def,ETA_AX,tEvalOp_def,bool_to_tag_thm,opb_lookup_def,bool_to_val_thm] >>
      simp[] >> rw[] >> COOPER_TAC )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      Cases_on`do_eq_pat v1 v2 = Eq_type_error`>>fs[] >>
      imp_res_tac do_eq_pat_call_equal >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> rw[bool_to_tag_thm,bool_to_val_thm] >>
      fsrw_tac[ARITH_ss][prim_exn_pat_def])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      fs[store_assign_def,Once s_to_Cs_def] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_GENLIST] ) >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_GENLIST] >>
      Cases_on`EL lnum s21`>> fs[store_v_same_type_def,sv_to_Cref_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[s_to_Cs_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST,EL_LUPDATE] >>
      rw[] >> fs[sv_to_Cref_def] >>
      simp[LIST_EQ_REWRITE] >>
      REWRITE_TAC[GSYM EL] >>
      simp[EL_LUPDATE] )
    >- (
      simp[ETA_AX,tEval_def,tEvalOp_def] >>
      fs[store_lookup_def] >>
      imp_res_tac evaluate_list_pat_length >>
      Cases_on`es`>>fs[LENGTH_NIL] >>
      simp[Once tEval_CONS,tEval_def,tEvalOp_def] >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      rw[]>>fs[] >>
      Cases_on`EL n s21`>>fs[sv_to_Cref_def] >>
      rw[s_to_Cs_def] )
    >- (
      simp[ETA_AX,tEval_def,tEvalOp_def] >>
      fs[store_alloc_def,LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[s_to_Cs_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n)` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_APPEND2,sv_to_Cref_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,s_to_Cs_def,get_global_def,EL_MAP] >>
      Cases_on`EL idx s22`>>fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[s_to_Cs_def,LUPDATE_MAP] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_alloc_def,LET_THM] >>
      Cases_on`n<0`>>fs[prim_exn_pat_def] >- rw[] >>
      `0 ≤ n` by COOPER_TAC >>
      Q.ISPEC_THEN`w`mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_8] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[s_to_Cs_def] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,sv_to_Cref_def] >>
      metis_tac[INT_ABS_EQ_ID])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        rw[prim_exn_pat_def] ) >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[sv_to_Cref_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        rw[s_to_Cs_def,prim_exn_pat_def] ) >>
      simp[ALOOKUP_GENLIST,sv_to_Cref_def] >>
      rw[s_to_Cs_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      fs[store_lookup_def] >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`n < LENGTH s21`>>fs[]>>
      Cases_on`EL n s21`>>fs[sv_to_Cref_def] >>
      rw[s_to_Cs_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        rw[prim_exn_pat_def] ) >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[sv_to_Cref_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        rw[s_to_Cs_def,prim_exn_pat_def] ) >>
      simp[ALOOKUP_GENLIST,sv_to_Cref_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      Q.ISPEC_THEN`w`mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_8] >> strip_tac >>
      rw[s_to_Cs_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,sv_to_Cref_def])
    >- (
      imp_res_tac evaluate_list_pat_length >> fs[] )
    >- ( Cases_on`es`>>fs[LENGTH_NIL] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm,prim_exn_pat_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm,prim_exn_pat_def] >>
      Cases_on`n < 0` >> fs[] >>
      `255 < n` by COOPER_TAC >> simp[])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm,prim_exn_pat_def] >> fs[] >>
      `¬(255 < n)` by COOPER_TAC >> simp[] >>
      `ABS n = n` by COOPER_TAC >>
      `Num n < 256` by COOPER_TAC >>
      `0 ≤ n` by COOPER_TAC >>
      simp[ORD_CHR,INT_OF_NUM])
    >- (
      Cases_on`z`>>fs[tEval_def,ETA_AX,tEvalOp_def,bool_to_tag_thm,opb_lookup_def,bool_to_val_thm] >>
      simp[] >> rw[] >> COOPER_TAC )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      simp[call_to_list_correct,IMPLODE_EXPLODE_I])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      imp_res_tac call_from_char_list_correct >>
      simp[IMPLODE_EXPLODE_I])
    >- ( simp[tEval_def,ETA_AX,tEvalOp_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      imp_res_tac call_from_list_correct >>
      simp[])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      Cases_on`i < 0` >> fs[LET_THM] >- (
        rw[prim_exn_pat_def] ) >>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH vs' ⇔ ¬(Num i ≥ LENGTH vs')` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH vs'`>>fs[] >- (
        rw[s_to_Cs_def,prim_exn_pat_def] ) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[EL_MAP] )
    >- ( simp[tEval_def,ETA_AX,tEvalOp_def])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_alloc_def,LET_THM] >>
      Cases_on`n<0`>>fs[prim_exn_pat_def] >- rw[] >>
      `0 ≤ n` by COOPER_TAC >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[s_to_Cs_def] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,sv_to_Cref_def] >>
      simp[REPLICATE_GENLIST,MAP_GENLIST] >>
      metis_tac[INT_ABS_EQ_ID])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        rw[prim_exn_pat_def] ) >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[sv_to_Cref_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        rw[s_to_Cs_def,prim_exn_pat_def] ) >>
      simp[ALOOKUP_GENLIST,sv_to_Cref_def,EL_MAP] >>
      rw[s_to_Cs_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def] >>
      fs[store_lookup_def] >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`n < LENGTH s21`>>fs[]>>
      Cases_on`EL n s21`>>fs[sv_to_Cref_def] >>
      rw[s_to_Cs_def] )
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        rw[prim_exn_pat_def] ) >>
      simp[s_to_Cs_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[sv_to_Cref_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        rw[s_to_Cs_def,prim_exn_pat_def] ) >>
      simp[ALOOKUP_GENLIST,sv_to_Cref_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      rw[s_to_Cs_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,sv_to_Cref_def,LUPDATE_MAP])
    >- (
      simp[tEval_def,ETA_AX,tEvalOp_def,bool_to_val_thm,bool_to_tag_thm] )
    >- ( simp[tEval_def,ETA_AX,tEvalOp_def,EL_MAP] )) >>
  strip_tac >- simp[tEval_def] >>
  strip_tac >- (
    simp[tEval_def] >> rw[] >>
    Cases_on`op`>>simp[tEval_def,ETA_AX] >>
    TRY( Cases_on`err`>>fs[] >> NO_TAC) >>
    Cases_on`o'`>>simp[tEval_def,ETA_AX] >>
    TRY( Cases_on`err`>>fs[] >> NO_TAC) >>
    Cases_on`o''`>>simp[tEval_def,ETA_AX] >>
    rw[tEval_def] >>
    TRY( Cases_on`err`>>fs[] >> NO_TAC) >>
    TRY(Cases_on`o'`>>simp[tEval_def,ETA_AX] >>
        Cases_on`err`>>fs[] >> NO_TAC) >>
    TRY(
      CHANGED_TAC(REWRITE_TAC[GSYM SNOC_APPEND]) >>
      simp[Once tEval_SNOC] >>
      Cases_on`err`>>fs[] >> NO_TAC) >>
    Cases_on`es`>>fs[LENGTH_NIL] >>
    Cases_on`t`>>fs[LENGTH_NIL] >>
    TRY(CHANGED_TAC(fs[Once tEval_CONS]) >>
        BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[tEval_def]>>rw[]>>
        Cases_on`err`>>fs[]>>
        BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[tEval_def]>>
        NO_TAC) >>
    Cases_on`err`>>fs[]) >>
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
