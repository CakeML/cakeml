(**
 * The beginnings of a PEG parser for the Pancake language.
 *
 * We take significant inspiration from the Spark ADA development.
 *)
open HolKernel Parse boolLib bossLib stringLib numLib intLib;

open pegTheory pegexecTheory panLexerTheory;
open ASCIInumbersLib combinTheory;

val _ = new_theory "panPEG";

Datatype:
  pancakeNT = ProgNT | BlockNT | StmtNT | ExpNT
            | DecNT | AssignNT | StoreNT | StoreByteNT
            | IfNT | WhileNT | CallNT | RetNT | HandleNT
            | ExtCallNT | RaiseNT | ReturnNT
            | ArgListNT
            | EXorNT | EAndNT | EEqNT | ECmpNT
            | EShiftNT | EAddNT
            | EBaseNT
            | StructNT | LoadNT | LoadByteNT | LabelNT
            | ShapeNT | ShapeCombNT
            | EqOpsNT | CmpOpsNT | ShiftOpsNT | AddOpsNT
End

Definition mknt_def:
  mknt (ntsym : pancakeNT) = nt (INL ntsym) I
End

Definition mkleaf_def:
  mkleaf t = [Lf (TOK (FST t), SND t)]
End

Definition mknode_def:
  mknode x ts = Nd (INL x, ptree_list_loc ts) ts
End

(** Make a sub-parsetree with a single child *)
Definition mksubtree_def:
  mksubtree x ts = [mknode x ts]
End

(** Accept a token without storing it. *)
Definition consume_tok_def:
  consume_tok t = tok ((=) t) (λt. [])
End

(** Accept and store a token in the parse tree. *)
Definition keep_tok_def:
  keep_tok t = tok ((=) t) mkleaf
End

(** Similar functions for keyword tokens *)
Definition consume_kw_def:
  consume_kw k = consume_tok (KeywordT k)
End

Definition keep_kw_def:
  keep_kw k = keep_tok (KeywordT k)
End

Definition keep_ident_def:
  keep_ident = tok (λt. case t of
                       | IdentT _ => T
                       | _ => F) mkleaf
End

Definition keep_int_def:
  keep_int = tok (λt. case t of
                       | IntT _ => T
                       | _ => F) mkleaf
End

Definition keep_nat_def:
  keep_nat = tok (λt. case t of
                        IntT n => if n >= 0 then T else F
                      | _ => F) mkleaf
End

Definition extract_sum_def:
  extract_sum (INL x) = x ∧ extract_sum (INR x) = x
End

Definition choicel_def:
  choicel [] = not (empty []) [] ∧
  choicel (h::t) = choice h (choicel t) extract_sum
End

Definition pegf_def:
  pegf s f = seq s (empty []) (λl1 l2. f l1)
End

Definition seql_def:
  seql l f = pegf (FOLDR (λp acc. seq p acc (++)) (empty []) l) f
End

Definition try_def:
  try s = choicel [s; empty []]
End

Definition pancake_peg_def[nocompute]:
  pancake_peg = <|
    start := mknt ProgNT;
    anyEOF := "Didn't expect an EOF";
    tokFALSE := "Failed to see expected token";
    tokEOF := "Failed to see expected token; saw EOF instead";
    notFAIL := "Not combinator failed";
    rules := FEMPTY |++ [
        (INL ProgNT, rpt (choicel [mknt BlockNT;
                                   seql [mknt StmtNT;
                                         consume_tok SemiT] I])
                         (mksubtree ProgNT o FLAT));
        (INL BlockNT, choicel [mknt DecNT; mknt IfNT; mknt WhileNT]);
        (INL StmtNT, choicel [keep_kw SkipK;
                              mknt AssignNT; mknt StoreNT;
                              mknt StoreByteNT;
                              keep_kw BrK; keep_kw ContK;
                              mknt CallNT; mknt ExtCallNT;
                              mknt RaiseNT; mknt ReturnNT;
                              keep_kw TicK]);
        (INL DecNT,seql [consume_kw VarK; keep_ident;
                         consume_tok AssignT; mknt ExpNT;
                         consume_tok LCurT; mknt ProgNT;
                         consume_tok RCurT]
                         (mksubtree DecNT));
        (INL AssignNT, seql [keep_ident; consume_tok AssignT;
                             mknt ExpNT] (mksubtree AssignNT));
        (INL StoreNT, seql [consume_kw StoreK; mknt ExpNT;
                            consume_tok CommaT; mknt ExpNT]
                           (mksubtree StoreNT));
        (INL StoreByteNT, seql [consume_kw StoreBK; mknt ExpNT;
                                consume_tok CommaT; mknt ExpNT]
                               (mksubtree StoreByteNT));
        (INL IfNT, seql [consume_kw IfK; mknt ExpNT; consume_tok LCurT;
                         mknt ProgNT; consume_tok RCurT;
                         try (seql [consume_kw ElseK; consume_tok LCurT;
                                    mknt ProgNT; consume_tok RCurT] I)]
                        (mksubtree IfNT));
        (INL WhileNT, seql [consume_kw WhileK; mknt ExpNT;
                            consume_tok LCurT; mknt ProgNT;
                            consume_tok RCurT] (mksubtree WhileNT));
        (INL CallNT, seql [try (mknt RetNT); mknt ExpNT;
                           consume_tok LParT; try (mknt ArgListNT);
                           consume_tok RParT]
                          (mksubtree CallNT));
        (INL RetNT, seql [keep_ident; consume_tok AssignT;
                          try (mknt HandleNT)]
                          (mksubtree RetNT));
        (INL HandleNT, seql [consume_kw WithK; keep_ident;
                             consume_kw InK; keep_ident;
                             consume_tok DArrowT; mknt ProgNT;
                             consume_kw HandleK]
                            (mksubtree HandleNT));
        (INL ExtCallNT, seql [consume_tok HashT; keep_ident;
                              consume_tok LParT; keep_ident; keep_ident;
                              keep_ident; keep_ident; consume_tok RParT]
                             (mksubtree ExtCallNT));
        (INL RaiseNT, seql [consume_kw RaiseK; keep_ident; mknt ExpNT]
                           (mksubtree RaiseNT));
        (INL ReturnNT, seql [consume_kw RetK; mknt ExpNT]
                            (mksubtree ReturnNT));
        (INL ArgListNT, seql [mknt ExpNT;
                              rpt (seql [consume_tok CommaT;
                                         mknt ExpNT] I)
                                  FLAT]
                             (mksubtree ArgListNT));
        (INL ExpNT, seql [mknt EXorNT;
                          rpt (seql [keep_tok OrT; mknt EXorNT] I)
                              FLAT]
                         (mksubtree ExpNT));
        (INL EXorNT, seql [mknt EAndNT;
                           rpt (seql [keep_tok XorT; mknt EAndNT] I)
                               FLAT]
                          (mksubtree EXorNT));
        (INL EAndNT, seql [mknt EEqNT;
                           rpt (seql [keep_tok AndT; mknt EEqNT] I)
                               FLAT]
                          (mksubtree EAndNT));
        (INL EEqNT, seql [mknt ECmpNT;
                          try (seql [mknt EqOpsNT; mknt ECmpNT] I)]
                         (mksubtree EEqNT));
        (INL ECmpNT, seql [mknt EShiftNT;
                           try (seql [mknt CmpOpsNT; mknt EShiftNT] I)]
                          (mksubtree ECmpNT));
        (INL EShiftNT, seql [mknt EAddNT;
                             rpt (seql [mknt ShiftOpsNT; keep_nat] I)
                                 FLAT]
                            (mksubtree EShiftNT));
        (INL EAddNT, seql [mknt EBaseNT;
                           rpt (seql [mknt AddOpsNT; mknt EBaseNT] I)
                               FLAT]
                          (mksubtree EAddNT));
        (INL EBaseNT, seql [choicel [seql [consume_tok LParT;
                                           mknt ExpNT;
                                           consume_tok RParT] I;
                                     keep_int; keep_ident; mknt LabelNT;
                                     mknt StructNT; mknt LoadNT;
                                     mknt LoadByteNT; keep_kw BaseK];
                            rpt (seql [consume_tok DotT; keep_nat] I)
                                FLAT]
                           (mksubtree EBaseNT));
        (INL LabelNT, seql [consume_tok NotT; keep_ident]
                           (mksubtree LabelNT));
        (INL StructNT, seql [consume_tok LessT; mknt ArgListNT;
                             consume_tok GreaterT]
                            (mksubtree StructNT));
        (INL LoadNT, seql [consume_kw LdsK; mknt ShapeNT; mknt ExpNT]
                          (mksubtree LoadNT));
        (INL LoadByteNT, seql [consume_kw LdbK; mknt ExpNT]
                              (mksubtree LoadByteNT));
        (INL ShapeNT, choicel [keep_tok StarT;
                               seql [consume_tok LessT;
                                     mknt ShapeCombNT;
                                     consume_tok GreaterT] I]);
        (INL ShapeCombNT, seql [mknt ShapeNT;
                                rpt (seq (consume_tok CommaT)
                                     (mknt ShapeNT) (flip K)) FLAT]
                             (mksubtree ShapeCombNT));
        (INL EqOpsNT, choicel [keep_tok EqT; keep_tok NeqT]);
        (INL CmpOpsNT, choicel [keep_tok LessT; keep_tok GeqT]);
        (INL ShiftOpsNT, choicel [keep_tok LslT; keep_tok LsrT;
                                  keep_tok AsrT; keep_tok RorT]);
        (INL AddOpsNT, choicel [keep_tok PlusT; keep_tok MinusT])]
        |>
End

(** Compute pancake parser domain lookup function. *)
val FDOM_pancake_peg = save_thm(
  "FDOM_pancake_peg",
  SIMP_CONV (srw_ss()) [pancake_peg_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM pancake_peg.rules``);


val pancake_peg_nt_thm =
    pegexecTheory.peg_nt_thm
      |> Q.GEN ‘G’ |> Q.ISPEC `pancake_peg`
      |> SIMP_RULE (srw_ss()) [FDOM_pancake_peg]
      |> Q.GEN `n`;

fun mk_rule_app n =
  SIMP_CONV (srw_ss())
            [pancake_peg_def, finite_mapTheory.FUPDATE_LIST_THM,
             finite_mapTheory.FAPPLY_FUPDATE_THM]
            “pancake_peg.rules ' ^n”

val pancakeNTs =
  let
    fun inject x = “INL ^x : pancakeNT inf”
  in
    map inject $ TypeBase.constructors_of “:pancakeNT”
  end

val pancake_peg_applied = let
  val ths = map mk_rule_app pancakeNTs
in
  save_thm("pancake_peg_applied", LIST_CONJ ths);
  ths
end

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:pancakeNT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end

Theorem pancake_exec_thm[compute] =
  TypeBase.constructors_of ``:pancakeNT``
    |> map (fn t => Q.SPEC ‘INL ^t’ pancake_peg_nt_thm)
    |> map (SIMP_RULE bool_ss (pancake_peg_applied @ distinct_ths @
                               [sumTheory.INL_11]))
    |> LIST_CONJ;

val test1 = time EVAL
             “peg_exec pancake_peg (mknt ProgNT)
              [(IdentT "x",Locs (POSN 1 1) (POSN 1 2));
               (AssignT,Locs (POSN 1 4) (POSN 1 4));
               (IntT 1,Locs (POSN 1 6) (POSN 1 7));
               (SemiT,Locs (POSN 1 8) (POSN 1 8))]
              [] NONE [] done failed”

val prog =
  “pancake_lex "var x = 0 { var y = <1,2,3> { x = x + y.1; } }"”

Definition parse_def:
  parse s =
    case peg_exec pancake_peg (mknt ProgNT) s [] NONE [] done failed of
    | Result (Success [] [e] _) => SOME e
    | _ => NONE
End

(** Properties for proving well-formedness of the Pancake grammar. *)

val frange_image = Q.prove(
  ‘FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)’,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION]
  >> metis_tac[]);

val peg_range =
    SIMP_CONV (srw_ss())
              (FDOM_pancake_peg :: frange_image :: pancake_peg_applied)
              “FRANGE pancake_peg.rules”

val peg_start =
  SIMP_CONV (srw_ss()) [pancake_peg_def] “pancake_peg.start”

val wfpeg_rwts = wfpeg_cases
                   |> ISPEC “pancake_peg”
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [‘seq e1 e2 f’, ‘choice e1 e2 f’,
                                     ‘tok P f’, ‘any f’, ‘empty v’,
                                     ‘not e v’, ‘rpt e f’, ‘choicel []’,
                                     ‘choicel (h::t)’, ‘keep_tok t’,
                                     ‘consume_tok t’, ‘keep_kw k’,
                                     ‘consume_kw k’, ‘keep_int’,
                                     ‘keep_nat’, ‘keep_ident’,
                                     ‘pegf e f’])
                   |> map (CONV_RULE
                           (RAND_CONV (SIMP_CONV (srw_ss())
                                       [choicel_def, seql_def,
                                        keep_tok_def, consume_tok_def,
                                        keep_kw_def, consume_kw_def,
                                        keep_int_def, keep_nat_def,
                                        keep_ident_def, pegf_def])))

val wfpeg_mknt = wfpeg_cases
                  |> ISPEC “pancake_peg”
                  |> Q.SPEC ‘mknt n’
                  |> CONV_RULE (RAND_CONV
                                (SIMP_CONV (srw_ss()) [mknt_def]))

val peg0_rwts = peg0_cases
                  |> ISPEC “pancake_peg” |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [‘tok P f’, ‘choice e1 e2 f’,
                                        ‘seq e1 e2 f’, ‘keep_tok t’,
                                        ‘consume_tok t’, ‘keep_kw k’,
                                        ‘consume_kw k’, ‘empty v’,
                                        ‘not e v’, ‘rpt e f’])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [keep_tok_def, consume_tok_def,
                                                   keep_kw_def, consume_kw_def])))

val pegfail_t = ``pegfail``
val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end

val pegnt_case_ths =
  peg0_cases
    |> ISPEC “pancake_peg”
    |> CONJUNCTS
    |> map (Q.SPEC ‘mknt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [mknt_def])))

Theorem peg0_pegf[simp]:
  peg0 G (pegf s f) = peg0 G s
Proof
  simp[pegf_def]
QED

Theorem peg0_seql[simp]:
  (peg0 G (seql [] f) ⇔ T) ∧
  (peg0 G (seql (h::t) f) ⇔ peg0 G h ∧ peg0 G (seql t I))
Proof
  simp[seql_def]
QED

Theorem peg0_keep_tok[simp]:
  peg0 G (keep_tok t) = F
Proof
  simp[keep_tok_def]
QED

Theorem peg0_consume_tok[simp]:
  peg0 G (consume_tok t) = F
Proof
  simp[consume_tok_def]
QED

Theorem peg0_keep_kw[simp]:
  peg0 G (keep_kw k) = F
Proof
  simp[keep_kw_def,peg0_keep_tok]
QED

Theorem peg0_consume_kw[simp]:
  peg0 G (consume_kw k) = F
Proof
  simp[consume_kw_def,peg0_consume_tok]
QED

Theorem peg0_keep_int[simp]:
  peg0 G keep_int = F
Proof
  simp[keep_int_def]
QED

Theorem peg0_keep_nat[simp]:
  peg0 G keep_int = F
Proof
  simp[keep_nat_def]
QED

Theorem peg0_keep_ident[simp]:
  peg0 G keep_ident = F
Proof
  simp[keep_ident_def]
QED

Theorem peg0_choicel[simp]:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔
     peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

fun pegnt(t,acc) = let
  val th =
      Q.prove(‘¬peg0 pancake_peg (mknt ^t)’,
            simp pegnt_case_ths >>
            simp pancake_peg_applied >>
            simp[FDOM_pancake_peg] >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [mknt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val topo_nts = [“AddOpsNT”, “ShiftOpsNT”, “CmpOpsNT”,
                “EqOpsNT”, “ShapeNT”,
                “ShapeCombNT”, “LabelNT”, “LoadByteNT”,
                “LoadNT”, “StructNT”,
                “EBaseNT”, “EAddNT”, “EShiftNT”, “ECmpNT”,
                “EEqNT”, “EAndNT”, “EXorNT”,
                “ExpNT”, “ArgListNT”, “ReturnNT”,
                “RaiseNT”, “ExtCallNT”,
                “HandleNT”, “RetNT”, “CallNT”,
                “WhileNT”, “IfNT”, “StoreByteNT”,
                “StoreNT”, “AssignNT”, “DecNT”,
                “StmtNT”, “BlockNT”];

(** All non-terminals except the top-level
  * program nonterminal always consume input. *)
val npeg0_rwts = List.foldl pegnt [] topo_nts

fun wfnt(t,acc) = let
  val th =
    Q.prove(‘wfpeg pancake_peg (mknt ^t)’,
          SIMP_TAC (srw_ss())
                   (pancake_peg_applied @
                    [wfpeg_mknt, FDOM_pancake_peg, try_def,
                     seql_def, keep_tok_def, consume_tok_def,
                     keep_kw_def, consume_kw_def, keep_int_def,
                     keep_nat_def, keep_ident_def]) THEN
          simp(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

(** This time include the top-level program non-terminal which is
  * well-formed. *)
val pancake_wfpeg_thm = save_thm(
  "pancake_wfpeg_thm",
  LIST_CONJ (List.foldl wfnt [] (topo_nts @ [“ProgNT”])))

val subexprs_mknt = Q.prove(
  ‘subexprs (mknt n) = {mknt n}’,
  simp[subexprs_def, mknt_def]);

Theorem PEG_wellformed[simp]:
  wfG pancake_peg
Proof
  simp[wfG_def, Gexprs_def, subexprs_def,
       subexprs_mknt, peg_start, peg_range, DISJ_IMP_THM,FORALL_AND_THM,
       choicel_def, seql_def, pegf_def, keep_tok_def, consume_tok_def,
       keep_kw_def, consume_kw_def, keep_int_def, keep_nat_def,
       keep_ident_def, try_def] >>
  simp(pancake_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts)
QED

val _ = export_theory();
