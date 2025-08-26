(**
 * The beginnings of a PEG parser for the Pancake language.
 *)

(*
 * We take significant inspiration from the Spark ADA development.
 *)
Theory panPEG
Ancestors
  peg pegexec panLexer combin
Libs
  stringLib numLib intLib ASCIInumbersLib


Datatype:
  pancakeNT = TopDecListNT | FunNT | ProgNT | BlockNT | StmtNT | ExpNT
            | DecNT | GlobalDecNT | AssignNT | StoreNT | StoreByteNT | Store32NT
            | IfNT | WhileNT | CallNT | RetNT | HandleNT
            | ExtCallNT | RaiseNT | ReturnNT
            | DecCallNT | RetCallNT
            | ArgListNT | NotNT
            | ParamListNT
            | EBoolAndNT | EEqNT | ECmpNT
            | ELoadNT | ELoadByteNT | ELoad32NT
            | EXorNT | EOrNT | EAndNT
            | EShiftNT | EAddNT | EMulNT
            | EBaseNT | StructNT
            | ShapeNT | ShapeCombNT
            | EqOpsNT | CmpOpsNT | ShiftOpsNT | AddOpsNT | MulOpsNT
            | SharedLoadNT | SharedLoadByteNT | SharedLoad16NT | SharedLoad32NT
            | SharedStoreNT | SharedStoreByteNT | SharedStore16NT | SharedStore32NT
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

Definition keep_annot_def:
  keep_annot = tok (λt. case t of
                       | AnnotCommentT _ => T
                       | _ => F) mkleaf
End

Definition keep_ffi_ident_def:
  keep_ffi_ident = tok (λt. case t of
                       | ForeignIdent _ => T
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

(* like try, but stores given token without consumption on failure *)
Definition try_default_def:
  try_default s t = choicel [s; empty $ mkleaf (t, unknown_loc)]
End

(* add single Skip in place of empty Prog - will generate unnecessary Skips if used without caution *)
Definition try_ProgNT_def:
  try_ProgNT =
    choicel [
      seql [consume_tok RCurT; empty $ mkleaf (KeywordT SkipK, unknown_loc)] (mksubtree ProgNT);
      mknt ProgNT
    ]
End

Definition pancake_peg_def[nocompute]:
  pancake_peg = <|
    start := mknt TopDecListNT;
    anyEOF := "Didn't expect an EOF";
    tokFALSE := "Failed to see expected token";
    tokEOF := "Failed to see expected token; saw EOF instead";
    notFAIL := "Not combinator failed";
    rules := FEMPTY |++ [
        (INL TopDecListNT, choicel [not (any $ K $ mksubtree TopDecListNT []) $ mksubtree TopDecListNT [];
                                 seql [mknt FunNT; mknt TopDecListNT] (mksubtree TopDecListNT);
                                 seql [mknt GlobalDecNT; mknt TopDecListNT] (mksubtree TopDecListNT);
                                 seql [keep_annot; mknt TopDecListNT] (mksubtree TopDecListNT)]);
        (INL FunNT, seql [try_default (keep_kw ExportK) StaticT;
                          consume_kw FunK;
                          keep_ident;
                          consume_tok LParT;
                          choicel
                          [mknt ParamListNT;
                           empty $ mksubtree ParamListNT []
                          ];
                          consume_tok RParT;
                          consume_tok LCurT;
                          try_ProgNT]
                          (mksubtree FunNT));
        (INL ParamListNT, seql [mknt ShapeNT; keep_ident;
                                rpt (seql [consume_tok CommaT;
                                           mknt ShapeNT;
                                           keep_ident] I)
                                           FLAT]
                               (mksubtree ParamListNT));
        (INL ProgNT, choicel [seql [mknt BlockNT; mknt ProgNT] (mksubtree ProgNT);
                              seql [mknt DecCallNT; try_ProgNT] (mksubtree DecCallNT);
                              seql [mknt DecNT; try_ProgNT] (mksubtree DecNT);
                              seql [keep_annot; mknt ProgNT] (mksubtree ProgNT);
                              seql [mknt StmtNT; consume_tok SemiT; mknt ProgNT] (mksubtree ProgNT);
                              consume_tok RCurT
                             ]);
        (INL BlockNT, choicel [mknt IfNT;
                               mknt WhileNT]);
        (INL StmtNT, choicel [keep_kw SkipK;
                              mknt CallNT;
                              mknt AssignNT; mknt StoreNT;
                              mknt StoreByteNT;
                              mknt Store32NT;
                              mknt SharedLoadByteNT;
                              mknt SharedLoad16NT;
                              mknt SharedLoad32NT;
                              mknt SharedLoadNT;
                              mknt SharedStoreByteNT;
                              mknt SharedStore16NT;
                              mknt SharedStore32NT;
                              mknt SharedStoreNT;
                              keep_kw BrK; keep_kw ContK;
                              mknt ExtCallNT;
                              mknt RaiseNT; mknt RetCallNT; mknt ReturnNT;
                              keep_kw TicK;
                              seql [consume_tok LCurT; try_ProgNT] I
                              ]);
        (INL DecCallNT, seql [consume_kw VarK; mknt ShapeNT; keep_ident; consume_tok AssignT;
                              keep_ident;
                              consume_tok LParT; try (mknt ArgListNT);
                              consume_tok RParT;consume_tok SemiT]
                          (mksubtree DecCallNT));
        (INL DecNT,seql [consume_kw VarK; keep_ident;
                         consume_tok AssignT; mknt ExpNT;
                         consume_tok SemiT]
                         (mksubtree DecNT));
        (INL GlobalDecNT,seql [consume_kw VarK; mknt ShapeNT; keep_ident;
                         consume_tok AssignT; mknt ExpNT;
                         consume_tok SemiT]
                         (mksubtree GlobalDecNT));
        (INL AssignNT, seql [keep_ident; consume_tok AssignT;
                             mknt ExpNT] (mksubtree AssignNT));
        (INL StoreNT, seql [consume_kw StK; mknt ExpNT;
                            consume_tok CommaT; mknt ExpNT]
                           (mksubtree StoreNT));
        (INL StoreByteNT, seql [consume_kw St8K; mknt ExpNT;
                                consume_tok CommaT; mknt ExpNT]
                               (mksubtree StoreByteNT));
        (INL Store32NT, seql [consume_kw St32K; mknt ExpNT;
                                consume_tok CommaT; mknt ExpNT]
                               (mksubtree Store32NT));
        (INL IfNT, seql [consume_kw IfK; mknt ExpNT; consume_tok LCurT;
                         try_ProgNT;
                         try_default (seql [consume_kw ElseK; consume_tok LCurT;
                                    try_ProgNT] I) (KeywordT SkipK)]
                        (mksubtree IfNT));
        (INL WhileNT, seql [consume_kw WhileK; mknt ExpNT;
                            consume_tok LCurT; try_ProgNT] (mksubtree WhileNT));
        (INL CallNT, seql [try (choicel [keep_kw RetK; mknt RetNT]);
                           choicel [seql [consume_tok StarT; mknt ExpNT] I;
                                    keep_ident];
                           consume_tok LParT; try (mknt ArgListNT);
                           consume_tok RParT]
                          (mksubtree CallNT));
        (INL RetNT, seql [keep_ident; consume_tok AssignT;
                          try (mknt HandleNT)]
                          (mksubtree RetNT));
        (INL HandleNT, seql [consume_kw WithK; keep_ident;
                             consume_kw InK; keep_ident;
                             consume_tok DArrowT; consume_tok LCurT; try_ProgNT;
                             consume_kw HandleK]
                            (mksubtree HandleNT));
        (INL ExtCallNT, seql [keep_ffi_ident;
                              consume_tok LParT; mknt ExpNT;
                              consume_tok CommaT; mknt ExpNT;
                              consume_tok CommaT; mknt ExpNT;
                              consume_tok CommaT; mknt ExpNT;
                              consume_tok RParT]
                             (mksubtree ExtCallNT));
        (INL RaiseNT, seql [consume_kw RaiseK; keep_ident; mknt ExpNT]
                           (mksubtree RaiseNT));
        (INL RetCallNT, seql [consume_kw RetK;
                              choicel [seql [consume_tok StarT; mknt ExpNT] I;
                                       keep_ident];
                              consume_tok LParT; try (mknt ArgListNT);
                              consume_tok RParT]
                            (mksubtree RetCallNT));
        (INL ReturnNT, seql [consume_kw RetK; mknt ExpNT]
                            (mksubtree ReturnNT));
        (INL ArgListNT, seql [mknt ExpNT;
                              rpt (seql [consume_tok CommaT;
                                         mknt ExpNT] I)
                                  FLAT]
                             (mksubtree ArgListNT));
        (INL ExpNT, seql [mknt EBoolAndNT;
                          rpt (seql [consume_tok BoolOrT; mknt EBoolAndNT] I)
                              FLAT]
                         (mksubtree ExpNT));
        (INL EBoolAndNT, seql [mknt EEqNT;
                               rpt (seql [consume_tok BoolAndT; mknt EEqNT] I)
                                   FLAT]
                              (mksubtree EBoolAndNT));
        (INL EEqNT, seql [mknt ECmpNT;
                          try (seql [mknt EqOpsNT; mknt ECmpNT] I)]
                         (mksubtree EEqNT));
        (INL ECmpNT, seql [mknt ELoadNT;
                           try (seql [mknt CmpOpsNT; mknt ELoadNT] I)]
                          (mksubtree ECmpNT));
        (INL ELoadNT, choicel [seql [consume_kw LdsK; mknt ShapeNT; mknt ELoadByteNT]
                                (mksubtree ELoadNT);
                               mknt ELoadByteNT]);
        (INL ELoadByteNT, choicel [seql [consume_kw Ld8K; mknt ELoad32NT]
                                    (mksubtree ELoadByteNT);
                                   mknt ELoad32NT]);
        (INL ELoad32NT, choicel [seql [consume_kw Ld32K; mknt EOrNT]
                                    (mksubtree ELoad32NT);
                                   mknt EOrNT]);
        (INL EOrNT, seql [mknt EXorNT;
                          rpt (seql [keep_tok OrT; mknt EXorNT] I)
                              FLAT]
                         (mksubtree EOrNT));
        (INL EXorNT, seql [mknt EAndNT;
                           rpt (seql [keep_tok XorT; mknt EAndNT] I)
                               FLAT]
                          (mksubtree EXorNT));
        (INL EAndNT, seql [mknt EShiftNT;
                           rpt (seql [keep_tok AndT; mknt EShiftNT] I)
                               FLAT]
                          (mksubtree EAndNT));
        (INL EShiftNT, seql [mknt EAddNT;
                             rpt (seql [mknt ShiftOpsNT; keep_nat] I)
                                 FLAT]
                            (mksubtree EShiftNT));
        (INL EAddNT, seql [mknt EMulNT;
                           rpt (seql [mknt AddOpsNT; mknt EMulNT] I)
                               FLAT]
                          (mksubtree EAddNT));
        (INL EMulNT, seql [mknt EBaseNT;
                           rpt (seql [mknt MulOpsNT; mknt EBaseNT] I) FLAT]
                          (mksubtree EMulNT));
        (INL EBaseNT, seql [choicel [seql [consume_tok LParT;
                                           mknt ExpNT;
                                           consume_tok RParT] I;
                                     mknt NotNT;
                                     keep_kw TrueK; keep_kw FalseK;
                                     keep_int; keep_ident;
                                     mknt StructNT; keep_kw BaseK; keep_kw BiwK;
                                     keep_kw TopK;
                                     ];
                            rpt (seql [consume_tok DotT; keep_nat] I)
                                FLAT]
                           (mksubtree EBaseNT));
        (INL NotNT, seql [consume_tok NotT; mknt EBaseNT]
                           (mksubtree NotNT));
        (INL StructNT, seql [consume_tok LessT; mknt ArgListNT;
                             consume_tok GreaterT]
                            (mksubtree StructNT));
        (INL ShapeNT, choicel [keep_int;
                               seql [consume_tok LCurT;
                                     mknt ShapeCombNT;
                                     consume_tok RCurT] I
                              ]);
        (INL ShapeCombNT, seql [mknt ShapeNT;
                                rpt (seq (consume_tok CommaT)
                                     (mknt ShapeNT) (flip K)) FLAT]
                             (mksubtree ShapeCombNT));
        (INL EqOpsNT, choicel [keep_tok EqT; keep_tok NeqT]);
        (INL CmpOpsNT, choicel [keep_tok LessT; keep_tok GeqT; keep_tok GreaterT; keep_tok LeqT;
                                keep_tok LowerT; keep_tok HigherT; keep_tok HigheqT; keep_tok LoweqT]);
        (INL ShiftOpsNT, choicel [keep_tok LslT; keep_tok LsrT;
                                  keep_tok AsrT; keep_tok RorT]);
        (INL AddOpsNT, choicel [keep_tok PlusT; keep_tok MinusT]);
        (INL MulOpsNT, keep_tok StarT);
        (INL SharedLoadNT,seql [consume_tok NotT; consume_kw LdwK; keep_ident;
                                consume_tok CommaT; mknt ExpNT]
                               (mksubtree SharedLoadNT));
        (INL SharedLoadByteNT,seql [consume_tok NotT; consume_kw Ld8K; keep_ident;
                                    consume_tok CommaT; mknt ExpNT]
                                   (mksubtree SharedLoadByteNT));
        (INL SharedLoad16NT,seql [consume_tok NotT; consume_kw Ld16K; keep_ident;
                                    consume_tok CommaT; mknt ExpNT]
                                   (mksubtree SharedLoad16NT));
        (INL SharedLoad32NT,seql [consume_tok NotT; consume_kw Ld32K; keep_ident;
                                    consume_tok CommaT; mknt ExpNT]
                                   (mksubtree SharedLoad32NT));
        (INL SharedStoreNT,seql [consume_tok NotT; consume_kw StwK; mknt ExpNT;
                                 consume_tok CommaT; mknt ExpNT]
                                (mksubtree SharedStoreNT));
        (INL SharedStoreByteNT,seql [consume_tok NotT; consume_kw St8K; mknt ExpNT;
                                     consume_tok CommaT; mknt ExpNT]
                                    (mksubtree SharedStoreByteNT));
        (INL SharedStore16NT,seql [consume_tok NotT; consume_kw St16K; mknt ExpNT;
                                     consume_tok CommaT; mknt ExpNT]
                                    (mksubtree SharedStore16NT));
        (INL SharedStore32NT,seql [consume_tok NotT; consume_kw St32K; mknt ExpNT;
                                     consume_tok CommaT; mknt ExpNT]
                                    (mksubtree SharedStore32NT));
        ]
        |>
End

(** Compute pancake parser domain lookup function. *)
Theorem FDOM_pancake_peg =
  SIMP_CONV (srw_ss()) [pancake_peg_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM pancake_peg.rules``


val pancake_peg_nt_thm =
    pegexecTheory.peg_nt_thm
      |> Q.GEN ‘G’ |> Q.ISPEC `pancake_peg`
      |> SIMP_RULE (srw_ss()) [FDOM_pancake_peg]
      |> Q.GEN `n`;

fun mk_rule_app peg n =
  SIMP_CONV (srw_ss())
            [pancake_peg_def, finite_mapTheory.FUPDATE_LIST_THM,
             finite_mapTheory.FAPPLY_FUPDATE_THM]
            “(^peg).rules ' ^n”

val pancakeNTs =
  let
    fun inject x = “INL ^x : pancakeNT inf”
  in
    map inject $ TypeBase.constructors_of “:pancakeNT”
  end

val pancake_peg_applied = let
  val ths = map (mk_rule_app “pancake_peg”) pancakeNTs
in
  save_thm("pancake_peg_applied", LIST_CONJ ths);
  ths
end

val pancake_peg_applied' = let
  val ths = map (mk_rule_app “pancake_peg with start := mknt FunNT”) pancakeNTs
in
  save_thm("pancake_peg_applied'", LIST_CONJ ths);
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

Definition parse_statement_def:
  parse_statement s =
    case peg_exec pancake_peg (mknt ProgNT) s [] NONE [] done failed of
    | Result (Success [] [e] _) => SOME e
    | _ => NONE
End

Definition parse_def:
  parse s =
    case peg_exec pancake_peg (mknt TopDecListNT) s [] NONE [] done failed of
    | Result (Success [] [e] _) => INL e
    | Result (Success toks _ _) => INR [(«Parser could not consume all tokens», unknown_loc)]
    | Result (Failure loc msg) => INR [(implode msg, loc)]
    | Looped => INR [(«PEG execution looped during parsing», unknown_loc)]
    | _ => INR [(«Unknown error during parsing», unknown_loc)]
End

(** Properties for proving well-formedness of the Pancake grammar. *)

Triviality frange_image:
  FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)
Proof
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

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
                                     ‘keep_nat’,‘keep_ffi_ident’,
                                     ‘keep_ident’,‘keep_annot’,
                                     ‘pegf e f’])
                   |> map (CONV_RULE
                           (RAND_CONV (SIMP_CONV (srw_ss())
                                       [choicel_def, seql_def,
                                        keep_tok_def, consume_tok_def,
                                        keep_kw_def, consume_kw_def,
                                        keep_int_def, keep_nat_def,
                                        keep_ffi_ident_def,
                                        keep_ident_def, pegf_def])))

val wfpeg_rwts' = wfpeg_cases
                   |> ISPEC “pancake_peg with start := mknt FunNT”
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
                                        keep_ident_def, pegf_def, peg_accfupds])))

val wfpeg_mknt = wfpeg_cases
                  |> ISPEC “pancake_peg”
                  |> Q.SPEC ‘mknt n’
                  |> CONV_RULE (RAND_CONV
                                (SIMP_CONV (srw_ss()) [mknt_def]))

val wfpeg_mknt' = wfpeg_cases
                  |> ISPEC “pancake_peg with start := mknt FunNT”
                  |> Q.SPEC ‘mknt n’
                  |> CONV_RULE (RAND_CONV
                                (SIMP_CONV (srw_ss()) [mknt_def,peg_accfupds]))

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

val peg1_rwts = peg0_cases
                  |> ISPEC “pancake_peg with start := mknt FunNT” |> CONJUNCTS
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
                                                   keep_kw_def, consume_kw_def,
                                                   peg_accfupds])))

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

val peg1_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg1_rwts
end

val pegnt_case_ths =
  peg0_cases
    |> ISPEC “pancake_peg”
    |> CONJUNCTS
    |> map (Q.SPEC ‘mknt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [mknt_def])))

val pegnt_case_ths' =
  peg0_cases
    |> ISPEC “pancake_peg with start := mknt FunNT”
    |> CONJUNCTS
    |> map (Q.SPEC ‘mknt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [mknt_def,peg_accfupds])))

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

Theorem peg0_keep_ffi_ident[simp]:
  peg0 G keep_ffi_ident = F
Proof
  simp[keep_ffi_ident_def]
QED

Theorem peg0_choicel[simp]:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔
     peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof
  simp[choicel_def]
QED

fun pegnt pref peg (t,acc) = let
  val th =
      Q.prove(‘¬peg0 ^peg (mknt ^t)’,
            simp $ pegnt_case_ths @ pegnt_case_ths'>>
            simp $ pancake_peg_applied @ map (PURE_REWRITE_RULE [mknt_def]) pancake_peg_applied' >>
            simp[FDOM_pancake_peg] >>
            simp(peg0_rwts @ peg1_rwts @ acc) >>
            simp(mknt_def::peg1_rwts @ map (PURE_REWRITE_RULE [mknt_def]) acc))
  val nm = pref ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [mknt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val topo_nts = [“MulOpsNT”, “AddOpsNT”, “ShiftOpsNT”, “CmpOpsNT”,
                “EqOpsNT”, “ShapeNT”,
                “ShapeCombNT”, “NotNT”, “StructNT”,
                “EBaseNT”, “EMulNT”, “EAddNT”, “EShiftNT”, “EAndNT”, “EXorNT”, “EOrNT”,
                “ELoad32NT”, “ELoadByteNT”, “ELoadNT”, “ECmpNT”, “EEqNT”, “EBoolAndNT”,
                “ExpNT”, “ArgListNT”, “ReturnNT”,
                “RaiseNT”, “ExtCallNT”,
                “HandleNT”, “RetNT”, “RetCallNT”, “CallNT”,
                “WhileNT”, “IfNT”, “StoreByteNT”, “Store32NT”,
                “StoreNT”, “AssignNT”,
                “SharedLoadByteNT”, “SharedLoad16NT”, “SharedLoad32NT”, “SharedLoadNT”,
                “SharedStoreByteNT”, “SharedStore16NT”, “SharedStore32NT”, “SharedStoreNT”, “DecNT”,
                “DecCallNT”, “StmtNT”, “BlockNT”, “ParamListNT”, “GlobalDecNT”, “FunNT”
                ];

(*  “FunNT”, “TopDecListNT” *)

(** All non-terminals except the top-level
  * program nonterminal always consume input. *)
val npeg0_rwts = List.foldl (pegnt "peg0_" “pancake_peg”) [] topo_nts

val npeg1_rwts = List.foldl (pegnt "peg1_" “pancake_peg with start := mknt FunNT”) [] topo_nts

fun wfnt tm (t,acc) = let
  val th =
    Q.prove(‘wfpeg ^tm (mknt ^t)’,
          SIMP_TAC (srw_ss())
                   (pancake_peg_applied @
                    [wfpeg_mknt, wfpeg_mknt',
                     REWRITE_RULE [mknt_def] wfpeg_mknt',
                     FDOM_pancake_peg, try_def, try_default_def,
                     seql_def, keep_tok_def, consume_tok_def,
                     keep_kw_def, consume_kw_def, keep_int_def,
                     keep_nat_def, keep_ident_def, keep_ffi_ident_def,
                     keep_annot_def, peg_accfupds]) THEN
          simp(wfpeg_rwts @ wfpeg_rwts' @ npeg0_rwts @ npeg1_rwts @ peg0_rwts @ peg1_rwts @ acc
              ) THEN
          simp(mknt_def::wfpeg_rwts @ wfpeg_rwts' @ npeg0_rwts @ npeg1_rwts @ peg0_rwts @ peg1_rwts @ acc @
               map (PURE_REWRITE_RULE [mknt_def]) (acc @ wfpeg_rwts')
              ))
in
  th::acc
end;

(** This time include the top-level program non-terminal which is
  * well-formed. *)
Theorem pancake_wfpeg_thm =
  LIST_CONJ (List.foldl (wfnt “pancake_peg”) [] (topo_nts @ [“ProgNT”, “TopDecListNT”]))

Theorem pancake_wfpeg_FunNT_thm =
  LIST_CONJ (List.foldl (wfnt “pancake_peg with start := mknt FunNT”) [] (topo_nts @ [“ProgNT”]))

Triviality subexprs_mknt:
  subexprs (mknt n) = {mknt n}
Proof
  simp[subexprs_def, mknt_def]
QED

Theorem PEG_wellformed[simp]:
  wfG pancake_peg
Proof
  simp[wfG_def, Gexprs_def, subexprs_def,
       subexprs_mknt, peg_start, peg_range, DISJ_IMP_THM,FORALL_AND_THM,
       choicel_def, seql_def, pegf_def, keep_tok_def, consume_tok_def,
       keep_kw_def, consume_kw_def, keep_int_def, keep_nat_def,
       keep_ident_def, keep_annot_def, keep_ffi_ident_def, try_def,
       try_default_def, try_ProgNT_def] >>
  simp(pancake_wfpeg_thm :: wfpeg_rwts @ peg0_rwts @ npeg0_rwts)
QED

