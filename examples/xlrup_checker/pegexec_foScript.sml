(*
  First-order PEG exec instantiated to CakeML surface types:
    input: (token # locs) list
    values: mlptree list  (as in cmlPEG)
    errors: string
    rule keys: MMLnonT inf

  Semantic actions are defunctionalized via finite datatypes (sem_u, sem_b,
  ...) so the whole machine stays first-order
*)
Theory pegexec_cml_fo
(* val _ = loadPath := !loadPath @ ["~/cakeml/examples/xlrup_checker/.hol/objs"]; *)
Ancestors
  peg gram location rich_list arithmetic While list tokenUtils lexer_impl xlrup_parsing
Libs
  boolSimps cv_transLib

(* ----- defunctionalized semantics (extend with one constructor per cmlPEG combinator) -- *)

Datatype:
  sem_u =
    SemU_id
  | SemU_bindNT (MMLnonT inf)
End
val _ = hide "nt";
Definition eval_unary_def:
  (eval_unary SemU_id v = v) ∧
  (eval_unary (SemU_bindNT nt) v =
     [Nd (nt, ptree_list_loc v) v])
End

Datatype:
  sem_b =
    SemB_first
  | SemB_second
  | SemB_append
  | SemB_mklinfix (MMLnonT inf)
  | SemB_foldl_Eapp
  | SemB_foldl_DType
  | SemB_papp_ctor_rpt
  | SemB_ebase_paren_apply
  | SemB_bindNT0 (MMLnonT inf)
End

Definition mkNd_fo_def:
  mkNd_fo nt l = Nd (nt, ptree_list_loc l) l
End

(* Same cases as cmlPEGTheory.peg_EbaseParenFn (cannot depend on cmlPEG here). *)
Definition peg_Ebase_paren_fo_def:
  peg_Ebase_paren_fo l =
    case l of
      [lp; es; rp] => [mkNd_fo (mkNT nEbase) [lp; mkNd_fo (mkNT nEseq) [es]; rp]]
    | [lp; e; sep; es; rp] =>
      (case destLf sep of
         NONE => []
       | SOME t =>
         (case destTOK t of
            NONE => []
          | SOME t =>
            if t = CommaT then
              [
                mkNd_fo (mkNT nEbase) [
                  mkNd_fo (mkNT nEtuple) [lp; mkNd_fo (mkNT nElist2) [e; sep; es]; rp]
                ]
              ]
            else
              [mkNd_fo (mkNT nEbase) [lp; mkNd_fo (mkNT nEseq) [e; sep; es]; rp]]))
    | _ => []
End

Definition mk_linfix_fo_def:
  mk_linfix_fo tgt acc [] = acc ∧
  mk_linfix_fo tgt acc [t] = acc ∧
  mk_linfix_fo tgt acc (opt::t::rest) =
    mk_linfix_fo tgt (mkNd_fo tgt [acc; opt; t]) rest
End

Definition foldl_Eapp_aux_def:
  foldl_Eapp_aux acc [] = acc ∧
  foldl_Eapp_aux acc (x::xs) =
    foldl_Eapp_aux (mkNd_fo (mkNT nEapp) [acc;x]) xs
End

Definition foldl_DType_aux_def:
  foldl_DType_aux acc [] = acc ∧
  foldl_DType_aux acc (x::xs) =
    foldl_DType_aux (mkNd_fo (mkNT nDType) [acc;x]) xs
End

Definition foldl_Eapp_fo_def:
  foldl_Eapp_fo [] = [] ∧
  foldl_Eapp_fo (h::t) =
    [foldl_Eapp_aux (mkNd_fo (mkNT nEapp) [h]) t]
End

Definition foldl_DType_fo_def:
  foldl_DType_fo [] = [] ∧
  foldl_DType_fo (h::t) =
    [foldl_DType_aux (mkNd_fo (mkNT nDType) [h]) t]
End

Definition ptPapply0_fo_def:
  ptPapply0_fo c [] = [] ∧
  ptPapply0_fo c [pb_pt] = [mkNd_fo (mkNT nPapp) [c; pb_pt]] ∧
  ptPapply0_fo c (pb::pbs) = ptPapply0_fo (mkNd_fo (mkNT nPConApp) [c; pb]) pbs
End

Definition ptPapply_fo_def:
  ptPapply_fo [] = [] ∧
  ptPapply_fo [_] = [] ∧
  ptPapply_fo (c::rest) = ptPapply0_fo (mkNd_fo (mkNT nPConApp) [c]) rest
End

Definition eval_papp_ctor_rpt_fo_def:
  eval_papp_ctor_rpt_fo pts =
    if LENGTH pts = 1 then [mkNd_fo (mkNT nPapp) [mkNd_fo (mkNT nPbase) [HD pts]]]
    else if 1 < LENGTH pts then ptPapply_fo pts
    else []
End

Definition eval_binary_def:
  (eval_binary SemB_first v2 v1 = v2) ∧
  (eval_binary SemB_second v2 v1 = v1) ∧
  (eval_binary SemB_append v2 v1 = v2 ++ v1) ∧
  (eval_binary (SemB_mklinfix tgt) v2 v1 =
     case v2 of
       [] => []
     | h::_ => [mk_linfix_fo tgt (mkNd_fo tgt [h]) v1]) ∧
  (eval_binary SemB_foldl_Eapp v2 v1 = foldl_Eapp_fo (v2 ++ v1)) ∧
  (eval_binary SemB_foldl_DType v2 v1 = foldl_DType_fo (v2 ++ v1)) ∧
  (eval_binary SemB_papp_ctor_rpt v2 v1 = eval_papp_ctor_rpt_fo (v2 ++ v1)) ∧
  (eval_binary SemB_ebase_paren_apply v2 v1 = peg_Ebase_paren_fo v2) ∧
  (eval_binary (SemB_bindNT0 tgt) v2 v1 = [mkNd_fo tgt (v2 ++ v1)])
End


Definition eval_combine_def:
  eval_combine s =
    case s of
      INL x => x
    | INR y => y
End


Definition eval_fold_def:
  eval_fold  vs = FLAT vs
End

Datatype:
  token_alpha_check =
    TokenAlpha_nonempty
  | TokenAlpha_upper_initial
  | TokenAlpha_lower_initial_not_reserved
End

Definition eval_token_alpha_check_def:
  (eval_token_alpha_check TokenAlpha_nonempty s ⇔ s ≠ «») ∧
  (eval_token_alpha_check TokenAlpha_upper_initial s ⇔
     if s = «» then F else isUpper (strsub s 0)) ∧
  (eval_token_alpha_check TokenAlpha_lower_initial_not_reserved s ⇔
     if s = «» then F else ¬isUpper (strsub s 0) ∧
     s ≠ «before» ∧
     s <>  «div» ∧
     s <> «mod» /\
     s <> «o»)
End

Datatype:
  token_symbol_check =
    TokenSymbol_nonempty
  | TokenSymbol_valid_mult
  | TokenSymbol_valid_add
  | TokenSymbol_valid_rel
  | TokenSymbol_valid_list
  | TokenSymbol_valid_prefix
End

Definition in_set_def:
  in_set (x:'a) [] = F ∧
  in_set x (y::ys) = (x = y ∨ in_set x ys)
End

Definition validAddSym_alt_def:
  validAddSym_alt s =
    case s of
    | [] => F
    | c::t =>
        in_set c [#"+"; #"-"; #"\094"] ∨
        (t ≠ [] ∧ c = #"|")
End

Definition eval_token_symbol_check_def:
  (eval_token_symbol_check TokenSymbol_nonempty s ⇔ s ≠ «») ∧
  (eval_token_symbol_check TokenSymbol_valid_mult s ⇔ validMultSym (explode s)) ∧
  (eval_token_symbol_check TokenSymbol_valid_add s ⇔ validAddSym_alt (explode s)) ∧
  (eval_token_symbol_check TokenSymbol_valid_rel s ⇔ validRelSym (explode s)) ∧
  (eval_token_symbol_check TokenSymbol_valid_list s ⇔ validListSym (explode s)) ∧
  (eval_token_symbol_check TokenSymbol_valid_prefix s ⇔ validPrefixSym (explode s))
End

Datatype:
  token_longid_check =
    TokenLongid_tail_nonempty
  | TokenLongid_tail_nonempty_head_alpha_not_upper
  | TokenLongid_ctor_upper_initial
End

Definition eval_token_longid_check_def:
  (eval_token_longid_check TokenLongid_tail_nonempty (str,s) ⇔ s ≠ «») ∧
  (eval_token_longid_check TokenLongid_tail_nonempty_head_alpha_not_upper (str,s) ⇔
     s ≠ «» ∧ (isAlpha (strsub s 0) ⇒ ¬isUpper (strsub s 0))) ∧
  (eval_token_longid_check TokenLongid_ctor_upper_initial (str,s) ⇔
     s ≠ «» ∧ isAlpha (strsub s 0) ∧ isUpper (strsub s 0))
End

Definition eval_token_longid_check_alt_def:
  (eval_token_longid_check_alt TokenLongid_tail_nonempty (str,s) ⇔
     s ≠ «») ∧
  (eval_token_longid_check_alt
     TokenLongid_tail_nonempty_head_alpha_not_upper (str,s) ⇔
     if s = «» then F
     else isAlpha (strsub s 0) ⇒ ¬isUpper (strsub s 0)) ∧
  (eval_token_longid_check_alt TokenLongid_ctor_upper_initial (str,s) ⇔
     if s = «» then F
     else isAlpha (strsub s 0) ∧ isUpper (strsub s 0))
End

Datatype:
  token_check =
    TokenCheck_always
  | TokenCheck_never
  | TokenCheck_eq token
  | TokenCheck_isInt
  | TokenCheck_isString
  | TokenCheck_isChar
  | TokenCheck_isWord
  | TokenCheck_isFFI
  | TokenCheck_alpha token_alpha_check
  | TokenCheck_symbol token_symbol_check
  | TokenCheck_longid token_longid_check
  | TokenCheck_isTyvarT
  | TokenCheck_isAlphaSym
  | TokenCheck_isLongidT
  | TokenCheck_opid_longid_nonempty
  | TokenCheck_opid_symbol_nonempty
  | TokenCheck_opid_alpha_nonempty
End

Definition eval_token_check_def:
  eval_token_check token_check (t,l) =
  case token_check of
  | TokenCheck_always => T
  | TokenCheck_never  => F
  | TokenCheck_eq t0 => (t = t0)
  | TokenCheck_isInt => isInt t
  | TokenCheck_isString => isString t
  | TokenCheck_isChar => isCharT t
  | TokenCheck_isWord => isWordT t
  | TokenCheck_isFFI => IS_SOME (destFFIT t)
  | TokenCheck_alpha a =>
      (case destAlphaT t of
       | NONE => F
       | SOME s => eval_token_alpha_check a s)
  | TokenCheck_symbol p =>
      (case destSymbolT t of
       NONE => F
       | SOME s => eval_token_symbol_check p s)
  | TokenCheck_longid p =>
                      ( case destLongidT t of
                          NONE => F
                        | SOME ls => eval_token_longid_check_alt p ls)
  | TokenCheck_isTyvarT => isTyvarT t
  | TokenCheck_isAlphaSym  => isAlphaSym t
  | TokenCheck_isLongidT => isLongidT t
  | TokenCheck_opid_longid_nonempty =>
      (     case destLongidT t of NONE => F | SOME (_,s) =>  s ≠ «»)
  | TokenCheck_opid_symbol_nonempty =>
      (     case destSymbolT t of NONE => F | SOME s => s ≠ «»)
  | TokenCheck_opid_alpha_nonempty =>

     case destAlphaT t of NONE => F | SOME s => s ≠ «»
End

Datatype:
  tok_map =
    TokenMap_mktokLf
  | TokenMap_empty_list
  | TokenMap_bindNT (MMLnonT inf)
End

Definition eval_tok_map_def:
  eval_tok_map tm (t,l) = case tm of
                          | TokenMap_mktokLf => [Lf (TOK t, l)]
                          | TokenMap_empty_list =>  ([] : mlptree list)
                          | TokenMap_bindNT nnt => [Nd (nnt, l) [Lf (TOK t, l)]]
End

Overload EOF_fo[local] = “Locs EOFpt EOFpt”

Definition merge_err_option_def:
  merge_err_option eo ox =
    case (eo, ox) of
      (NONE, NONE) => NONE
    | (NONE, SOME x) => SOME x
    | (SOME x, NONE) => SOME x
    | (SOME _, SOME y) => SOME y
End

Datatype:
  pegsym_fo =
    Empty_fo (mlptree list)
  | Any_fo tok_map
  | Tok_fo token_check tok_map
  | Nt_fo (MMLnonT inf) sem_u
  | Seq_fo pegsym_fo pegsym_fo sem_b
  | Choice_fo pegsym_fo pegsym_fo
  | Rpt_fo pegsym_fo
  | Not_fo pegsym_fo (mlptree list)
  | Error_fo string
End

Datatype:
  kont_fo =
    Ksym_fo pegsym_fo kont_fo kont_fo
  | App1_plain_fo sem_u kont_fo
  | App1_cl_fo kont_fo
  | App1_cr_fo kont_fo
  | App2_fo sem_b kont_fo
  | DropErr_fo kont_fo
  | AddErr_fo locs string kont_fo
  | CmpErrs_fo kont_fo
  | CmpEO_fo ((locs # string) option) kont_fo
  | ReturnTo_fo ((token # locs) list) ((mlptree list) option list) kont_fo
  | RestoreEO_fo ((locs # string) option) kont_fo
  | Poplist_fo kont_fo
  | Listsym_fo pegsym_fo kont_fo
  | Done_fo
  | Failed_fo
End

Datatype:
  evalcase_fo =
    EV_fo pegsym_fo ((token # locs) list) ((mlptree list) option list)
          ((locs # string) option) ((locs # string) list) kont_fo kont_fo
  | AP_fo kont_fo ((token # locs) list) ((mlptree list) option list)
          ((locs # string) option) ((locs # string) list)
  | Result_fo (((token # locs) list, mlptree list, string) pegresult)
  | Looped_fo
End

Datatype:
  peg_fo =
    <| start : pegsym_fo ;
       anyEOF : string ;
       tokFALSE : string ;
       tokEOF : string ;
       notFAIL : string |>
End

Definition poplist_aux_def:
  poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t ∧
  poplist_aux acc (NONE::t) = (acc,t) ∧
  poplist_aux acc [] = (acc,[])
End

Definition poplistval_def:
  poplistval l =
    let (values,rest) = poplist_aux [] l in
      SOME (eval_fold values) :: rest
End

Definition sloc_pexec_def:
  sloc_pexec (i:(token # locs) list) =
    case i of
      [] => EOF_fo
    | (c,l)::t => l
End

(* Inline nonterminal dispatcher:
   put each grammar rule directly here instead of using a finite-map `rules`. *)
Definition nt_rule_fo_def:
  nt_rule_fo (INL nV) =
    SOME
      (Choice_fo
        (Tok_fo
          (TokenCheck_alpha TokenAlpha_lower_initial_not_reserved)
          (TokenMap_bindNT (INL nV)))
        (Seq_fo
          (Tok_fo
            (TokenCheck_symbol TokenSymbol_valid_prefix)
            TokenMap_mktokLf)
          (Empty_fo [])
          (SemB_bindNT0 (INL nV)))) ∧
  nt_rule_fo (INL nFQV) =
    SOME
      (Choice_fo
        (Nt_fo (INL nV) (SemU_bindNT (INL nFQV)))
        (Tok_fo
          (TokenCheck_longid TokenLongid_tail_nonempty_head_alpha_not_upper)
          (TokenMap_bindNT (INL nFQV)))) ∧
  nt_rule_fo (INL nEliteral) =
    SOME
      (Choice_fo
        (Tok_fo TokenCheck_isInt (TokenMap_bindNT (INL nEliteral)))
        (Choice_fo
          (Tok_fo TokenCheck_isString (TokenMap_bindNT (INL nEliteral)))
          (Choice_fo
            (Tok_fo TokenCheck_isChar (TokenMap_bindNT (INL nEliteral)))
            (Choice_fo
              (Tok_fo TokenCheck_isWord (TokenMap_bindNT (INL nEliteral)))
              (Tok_fo TokenCheck_isFFI (TokenMap_bindNT (INL nEliteral))))))) ∧
  nt_rule_fo (INL nEbase) =
    SOME
      (Choice_fo
        (Nt_fo (INL nEliteral) (SemU_bindNT (INL nEbase)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
            (Seq_fo
              (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
              (Empty_fo [])
              SemB_append)
            (SemB_bindNT0 (INL nEbase)))
          (Choice_fo
            (Seq_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nE) SemU_id)
                  (Choice_fo
                    (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
                    (Choice_fo
                      (Seq_fo
                        (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
                        (Seq_fo
                          (Nt_fo (INL nElist1) SemU_id)
                          (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
                          SemB_append)
                        SemB_append)
                      (Seq_fo
                        (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
                        (Seq_fo
                          (Nt_fo (INL nEseq) SemU_id)
                          (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
                          SemB_append)
                        SemB_append)))
                  SemB_append)
                SemB_append)
              (Empty_fo [])
              SemB_ebase_paren_apply)
            (Choice_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq LbrackT) TokenMap_mktokLf)
                (Seq_fo
                  (Choice_fo
                    (Nt_fo (INL nElist1) SemU_id)
                    (Empty_fo []))
                  (Seq_fo
                    (Tok_fo (TokenCheck_eq RbrackT) TokenMap_mktokLf)
                    (Empty_fo [])
                    SemB_append)
                  SemB_append)
                (SemB_bindNT0 (INL nEbase)))
              (Choice_fo
                (Seq_fo
                  (Tok_fo (TokenCheck_eq LetT) TokenMap_mktokLf)
                  (Seq_fo
                    (Nt_fo (INL nLetDecs) SemU_id)
                    (Seq_fo
                      (Tok_fo (TokenCheck_eq InT) TokenMap_mktokLf)
                      (Seq_fo
                        (Nt_fo (INL nEseq) SemU_id)
                        (Seq_fo
                          (Tok_fo (TokenCheck_eq EndT) TokenMap_mktokLf)
                          (Empty_fo [])
                          SemB_append)
                        SemB_append)
                      SemB_append)
                    SemB_append)
                  (SemB_bindNT0 (INL nEbase)))
                (Choice_fo
                  (Nt_fo (INL nFQV) (SemU_bindNT (INL nEbase)))
                  (Choice_fo
                    (Nt_fo (INL nConstructorName) (SemU_bindNT (INL nEbase)))
                    (Seq_fo
                      (Tok_fo (TokenCheck_eq OpT) TokenMap_mktokLf)
                      (Seq_fo
                        (Nt_fo (INL nOpID) SemU_id)
                        (Empty_fo [])
                        SemB_append)
                      (SemB_bindNT0 (INL nEbase)))))))))) ∧
  nt_rule_fo (INL nEapp) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEbase) SemU_id)
        (Rpt_fo (Nt_fo (INL nEbase) SemU_id))
        SemB_foldl_Eapp) ∧
  nt_rule_fo (INL nEmult) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEapp) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Nt_fo (INL nMultOps) SemU_id)
            (Nt_fo (INL nEapp) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nEmult))) ∧
  nt_rule_fo (INL nEadd) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEmult) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Nt_fo (INL nAddOps) SemU_id)
            (Nt_fo (INL nEmult) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nEadd))) ∧
  nt_rule_fo (INL nElistop) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEadd) SemU_id)
        (Choice_fo
          (Seq_fo
            (Nt_fo (INL nListOps) SemU_id)
            (Nt_fo (INL nElistop) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nElistop))) ∧
  nt_rule_fo (INL nErel) =
    SOME
      (Seq_fo
        (Nt_fo (INL nElistop) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Nt_fo (INL nRelOps) SemU_id)
            (Nt_fo (INL nElistop) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nErel))) ∧
  nt_rule_fo (INL nEcomp) =
    SOME
      (Seq_fo
        (Nt_fo (INL nErel) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Nt_fo (INL nCompOps) SemU_id)
            (Nt_fo (INL nErel) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nEcomp))) ∧
  nt_rule_fo (INL nEbefore) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEcomp) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq (AlphaT «before»)) TokenMap_mktokLf)
            (Nt_fo (INL nEcomp) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nEbefore))) ∧
  nt_rule_fo (INL nEtyped) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEbefore) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq ColonT) TokenMap_mktokLf)
            (Nt_fo (INL nType) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nEtyped))) ∧
  nt_rule_fo (INL nElogicAND) =
    SOME
      (Seq_fo
        (Nt_fo (INL nEtyped) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq AndalsoT) TokenMap_mktokLf)
            (Nt_fo (INL nEtyped) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nElogicAND))) ∧
  nt_rule_fo (INL nElogicOR) =
    SOME
      (Seq_fo
        (Nt_fo (INL nElogicAND) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq OrelseT) TokenMap_mktokLf)
            (Nt_fo (INL nElogicAND) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nElogicOR))) ∧
  nt_rule_fo (INL nEhandle) =
    SOME
      (Seq_fo
        (Nt_fo (INL nElogicOR) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq HandleT) TokenMap_mktokLf)
            (Nt_fo (INL nPEs) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nEhandle))) ∧
  nt_rule_fo (INL nE) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq RaiseT) TokenMap_mktokLf)
          (Seq_fo (Nt_fo (INL nE) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nE)))
        (Choice_fo
          (Nt_fo (INL nEhandle) (SemU_bindNT (INL nE)))
          (Choice_fo
            (Seq_fo
              (Tok_fo (TokenCheck_eq IfT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nE) SemU_id)
                (Seq_fo
                  (Tok_fo (TokenCheck_eq ThenT) TokenMap_mktokLf)
                  (Seq_fo
                    (Nt_fo (INL nE) SemU_id)
                    (Seq_fo
                      (Tok_fo (TokenCheck_eq ElseT) TokenMap_mktokLf)
                      (Seq_fo
                        (Nt_fo (INL nE) SemU_id)
                        (Empty_fo [])
                        SemB_append)
                      SemB_append)
                    SemB_append)
                  SemB_append)
                SemB_append)
              (SemB_bindNT0 (INL nE)))
            (Choice_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq FnT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nPattern) SemU_id)
                  (Seq_fo
                    (Tok_fo (TokenCheck_eq DarrowT) TokenMap_mktokLf)
                    (Seq_fo
                      (Nt_fo (INL nE) SemU_id)
                      (Empty_fo [])
                      SemB_append)
                    SemB_append)
                  SemB_append)
                (SemB_bindNT0 (INL nE)))
              (Seq_fo
                (Tok_fo (TokenCheck_eq CaseT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nE) SemU_id)
                  (Seq_fo
                    (Tok_fo (TokenCheck_eq OfT) TokenMap_mktokLf)
                    (Seq_fo
                      (Nt_fo (INL nPEs) SemU_id)
                      (Empty_fo [])
                      SemB_append)
                    SemB_append)
                  SemB_append)
                (SemB_bindNT0 (INL nE))))))) ∧
  nt_rule_fo (INL nTyvarN) =
    SOME
      (Seq_fo
        (Tok_fo TokenCheck_isTyvarT TokenMap_mktokLf)
        (Empty_fo [])
        (SemB_bindNT0 (INL nTyvarN))) ∧
  nt_rule_fo (INL nElist1) =
    SOME
      (Seq_fo
        (Nt_fo (INL nE) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
            (Nt_fo (INL nElist1) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nElist1))) ∧
  nt_rule_fo (INL nMultOps) =
    SOME
      (Seq_fo
        (Choice_fo
          (Tok_fo
            (TokenCheck_symbol TokenSymbol_valid_mult)
            TokenMap_mktokLf)
          (Choice_fo
            (Tok_fo (TokenCheck_eq StarT) TokenMap_mktokLf)
            (Choice_fo
              (Tok_fo (TokenCheck_eq (AlphaT «mod»)) TokenMap_mktokLf)
              (Tok_fo (TokenCheck_eq (AlphaT «div»)) TokenMap_mktokLf))))
        (Empty_fo [])
        (SemB_bindNT0 (INL nMultOps))) ∧
  nt_rule_fo (INL nAddOps) =
    SOME
      (Seq_fo
        (Tok_fo
          (TokenCheck_symbol TokenSymbol_valid_add)
          TokenMap_mktokLf)
        (Empty_fo [])
        (SemB_bindNT0 (INL nAddOps))) ∧
  nt_rule_fo (INL nRelOps) =
    SOME
      (Seq_fo
        (Choice_fo
          (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
          (Tok_fo
            (TokenCheck_symbol TokenSymbol_valid_rel)
            TokenMap_mktokLf))
        (Empty_fo [])
        (SemB_bindNT0 (INL nRelOps))) ∧
  nt_rule_fo (INL nListOps) =
    SOME
      (Seq_fo
        (Tok_fo
          (TokenCheck_symbol TokenSymbol_valid_list)
          TokenMap_mktokLf)
        (Empty_fo [])
        (SemB_bindNT0 (INL nListOps))) ∧
  nt_rule_fo (INL nCompOps) =
    SOME
      (Seq_fo
        (Choice_fo
          (Tok_fo (TokenCheck_eq (SymbolT «:=»)) TokenMap_mktokLf)
          (Tok_fo (TokenCheck_eq (AlphaT «o»)) TokenMap_mktokLf))
        (Empty_fo [])
        (SemB_bindNT0 (INL nCompOps))) ∧
  nt_rule_fo (INL nOpID) =
    SOME
      (Choice_fo
        (Tok_fo
          TokenCheck_opid_longid_nonempty
          (TokenMap_bindNT (INL nOpID)))
        (Choice_fo
          (Tok_fo
            TokenCheck_opid_symbol_nonempty
            (TokenMap_bindNT (INL nOpID)))
          (Choice_fo
            (Tok_fo
              TokenCheck_opid_alpha_nonempty
              (TokenMap_bindNT (INL nOpID)))
            (Choice_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq StarT) TokenMap_mktokLf)
                (Empty_fo [])
                (SemB_bindNT0 (INL nOpID)))
              (Seq_fo
                (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
                (Empty_fo [])
                (SemB_bindNT0 (INL nOpID))))))) ∧
  nt_rule_fo (INL nEseq) =
    SOME
      (Seq_fo
        (Nt_fo (INL nE) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
            (Nt_fo (INL nEseq) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nEseq))) ∧
  nt_rule_fo (INL nPEs) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPattern) SemU_id)
        (Seq_fo
          (Tok_fo (TokenCheck_eq DarrowT) TokenMap_mktokLf)
          (Seq_fo (Nt_fo (INL nPE) SemU_id) (Empty_fo []) SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nPEs))) ∧
  nt_rule_fo (INL nPE) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq IfT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nE) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq ThenT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nE) SemU_id)
                (Seq_fo
                  (Tok_fo (TokenCheck_eq ElseT) TokenMap_mktokLf)
                  (Seq_fo
                    (Nt_fo (INL nPE) SemU_id)
                    (Empty_fo [])
                    SemB_append)
                  SemB_append)
                SemB_append)
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nPE)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq CaseT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nE) SemU_id)
              (Seq_fo
                (Tok_fo (TokenCheck_eq OfT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nPEs) SemU_id)
                  (Empty_fo [])
                  SemB_append)
                SemB_append)
              SemB_append)
            (SemB_bindNT0 (INL nPE)))
          (Choice_fo
            (Seq_fo
              (Tok_fo (TokenCheck_eq FnT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nPattern) SemU_id)
                (Seq_fo
                  (Tok_fo (TokenCheck_eq DarrowT) TokenMap_mktokLf)
                  (Seq_fo
                    (Nt_fo (INL nE) SemU_id)
                    (Empty_fo [])
                    SemB_append)
                  SemB_append)
                SemB_append)
              (SemB_bindNT0 (INL nPE)))
            (Choice_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq RaiseT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nPE) SemU_id)
                  (Empty_fo [])
                  SemB_append)
                (SemB_bindNT0 (INL nPE)))
              (Seq_fo
                (Nt_fo (INL nElogicOR) SemU_id)
                (Seq_fo (Nt_fo (INL nPEsfx) SemU_id) (Empty_fo []) SemB_append)
                (SemB_bindNT0 (INL nPE))))))) ∧
  nt_rule_fo (INL nPEsfx) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq HandleT) TokenMap_mktokLf)
          (Seq_fo (Nt_fo (INL nPEs) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nPEsfx)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq BarT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nPEs) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nPEsfx)))
          (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nPEsfx))))) ∧
  nt_rule_fo (INL nAndFDecls) =
    SOME
      (Seq_fo
        (Nt_fo (INL nFDecl) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq AndT) TokenMap_mktokLf)
            (Nt_fo (INL nFDecl) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nAndFDecls))) ∧
  nt_rule_fo (INL nFDecl) =
    SOME
      (Seq_fo
        (Nt_fo (INL nV) SemU_id)
        (Seq_fo
          (Nt_fo (INL nPbaseList1) SemU_id)
          (Seq_fo
            (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nE) SemU_id) (Empty_fo []) SemB_append)
            SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nFDecl))) ∧
  nt_rule_fo (INL nPbaseList1) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPbase) SemU_id)
        (Choice_fo (Nt_fo (INL nPbaseList1) SemU_id) (Empty_fo []))
        (SemB_bindNT0 (INL nPbaseList1))) ∧
  nt_rule_fo (INL nType) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPType) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq ArrowT) TokenMap_mktokLf)
            (Nt_fo (INL nType) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nType))) ∧
  nt_rule_fo (INL nDType) =
    SOME
      (Seq_fo
        (Nt_fo (INL nTbase) SemU_id)
        (Rpt_fo (Nt_fo (INL nTyOp) SemU_id) )
        SemB_foldl_DType) ∧
  nt_rule_fo (INL nTbase) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nType) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nTbase)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nTypeList2) SemU_id)
              (Seq_fo
                (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nTyOp) SemU_id)
                  (Empty_fo [])
                  SemB_append)
                SemB_append)
              SemB_append)
            (SemB_bindNT0 (INL nTbase)))
          (Choice_fo
            (Tok_fo TokenCheck_isTyvarT (TokenMap_bindNT (INL nTbase)))
            (Nt_fo (INL nTyOp) (SemU_bindNT (INL nTbase)))))) ∧
  nt_rule_fo (INL nPTbase) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nType) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nPTbase)))
        (Choice_fo
          (Tok_fo TokenCheck_isTyvarT (TokenMap_bindNT (INL nPTbase)))
          (Nt_fo (INL nTyOp) (SemU_bindNT (INL nPTbase))))) ∧
  nt_rule_fo (INL nTypeList2) =
    SOME
      (Seq_fo
        (Nt_fo (INL nType) SemU_id)
        (Seq_fo
          (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
          (Seq_fo (Nt_fo (INL nTypeList1) SemU_id) (Empty_fo []) SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nTypeList2))) ∧
  nt_rule_fo (INL nTypeList1) =
    SOME
      (Seq_fo
        (Nt_fo (INL nType) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
            (Nt_fo (INL nTypeList1) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nTypeList1))) ∧
  nt_rule_fo (INL nTbaseList) =
    SOME
      (Seq_fo
        (Choice_fo
          (Seq_fo
            (Nt_fo (INL nPTbase) SemU_id)
            (Seq_fo (Nt_fo (INL nTbaseList) SemU_id) (Empty_fo []) SemB_append)
            SemB_append)
          (Empty_fo []))
        (Empty_fo [])
        (SemB_bindNT0 (INL nTbaseList))) ∧
  nt_rule_fo (INL nTyOp) =
    SOME
      (Seq_fo
        (Choice_fo
          (Nt_fo (INL nUQTyOp) SemU_id)
          (Tok_fo TokenCheck_isLongidT TokenMap_mktokLf))
        (Empty_fo [])
        (SemB_bindNT0 (INL nTyOp))) ∧
  nt_rule_fo (INL nUQTyOp) =
    SOME
      (Seq_fo
        (Tok_fo TokenCheck_isAlphaSym TokenMap_mktokLf)
        (Empty_fo [])
        (SemB_bindNT0 (INL nUQTyOp))) ∧
  nt_rule_fo (INL nPType) =
    SOME
      (Seq_fo
        (Nt_fo (INL nDType) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq StarT) TokenMap_mktokLf)
            (Nt_fo (INL nPType) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nPType))) ∧
  nt_rule_fo (INL nTypeName) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nUQTyOp) SemU_id)
          (Empty_fo [])
          (SemB_bindNT0 (INL nTypeName)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nTyVarList) SemU_id)
              (Seq_fo
                (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nUQTyOp) SemU_id)
                  (Empty_fo [])
                  SemB_append)
                SemB_append)
              SemB_append)
            (SemB_bindNT0 (INL nTypeName)))
          (Seq_fo
            (Tok_fo TokenCheck_isTyvarT TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nUQTyOp) SemU_id)
              (Empty_fo [])
              SemB_append)
            (SemB_bindNT0 (INL nTypeName))))) ∧
  nt_rule_fo (INL nTyVarList) =
    SOME
      (Seq_fo
        (Nt_fo (INL nTyvarN) SemU_id)
        (Rpt_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
            (Nt_fo (INL nTyvarN) SemU_id)
            SemB_append)
          )
        (SemB_mklinfix (INL nTyVarList))) ∧
  nt_rule_fo (INL nTypeDec) =
    SOME
      (Seq_fo
        (Tok_fo (TokenCheck_eq DatatypeT) TokenMap_mktokLf)
        (Seq_fo
          (Seq_fo
            (Nt_fo (INL nDtypeDecl) SemU_id)
            (Rpt_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq AndT) TokenMap_mktokLf)
                (Nt_fo (INL nDtypeDecl) SemU_id)
                SemB_append)
              )
            (SemB_mklinfix (INL nDtypeDecls)))
          (Empty_fo [])
          SemB_append)
        (SemB_bindNT0 (INL nTypeDec))) ∧
  nt_rule_fo (INL nDtypeDecl) =
    SOME
      (Seq_fo
        (Nt_fo (INL nTypeName) SemU_id)
        (Seq_fo
          (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nDconstructor) SemU_id)
            (Rpt_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq BarT) TokenMap_mktokLf)
                (Nt_fo (INL nDconstructor) SemU_id)
                SemB_append)
              )
            (SemB_mklinfix (INL nDtypeCons)))
          SemB_append)
        (SemB_bindNT0 (INL nDtypeDecl))) ∧
  nt_rule_fo (INL nDconstructor) =
    SOME
      (Seq_fo
        (Nt_fo (INL nUQConstructorName) SemU_id)
        (Seq_fo (Nt_fo (INL nTbaseList) SemU_id) (Empty_fo []) SemB_append)
        (SemB_bindNT0 (INL nDconstructor))) ∧
  nt_rule_fo (INL nUQConstructorName) =
    SOME
      (Tok_fo
        (TokenCheck_alpha TokenAlpha_upper_initial)
        (TokenMap_bindNT (INL nUQConstructorName))) ∧
  nt_rule_fo (INL nConstructorName) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nUQConstructorName) SemU_id)
          (Empty_fo [])
          (SemB_bindNT0 (INL nConstructorName)))
        (Tok_fo
          (TokenCheck_longid TokenLongid_ctor_upper_initial)
          (TokenMap_bindNT (INL nConstructorName)))) ∧
  nt_rule_fo (INL nPbase) =
    SOME
      (Seq_fo
        (Choice_fo
          (Nt_fo (INL nV) SemU_id)
          (Choice_fo
            (Nt_fo (INL nConstructorName) SemU_id)
            (Choice_fo
              (Tok_fo TokenCheck_isInt TokenMap_mktokLf)
              (Choice_fo
                (Tok_fo TokenCheck_isString TokenMap_mktokLf)
                (Choice_fo
                  (Tok_fo TokenCheck_isChar TokenMap_mktokLf)
                  (Choice_fo
                    (Nt_fo (INL nPtuple) SemU_id)
                    (Choice_fo
                      (Tok_fo (TokenCheck_eq UnderbarT) TokenMap_mktokLf)
                      (Choice_fo
                        (Seq_fo
                          (Tok_fo (TokenCheck_eq LbrackT) TokenMap_mktokLf)
                          (Seq_fo
                            (Choice_fo
                              (Nt_fo (INL nPatternList) SemU_id)
                              (Empty_fo []))
                            (Seq_fo
                              (Tok_fo (TokenCheck_eq RbrackT) TokenMap_mktokLf)
                              (Empty_fo [])
                              SemB_append)
                            SemB_append)
                          SemB_append)
                        (Seq_fo
                          (Tok_fo (TokenCheck_eq OpT) TokenMap_mktokLf)
                          (Seq_fo
                            (Nt_fo (INL nOpID) SemU_id)
                            (Empty_fo [])
                            SemB_append)
                          SemB_append)))))))))
        (Empty_fo [])
        (SemB_bindNT0 (INL nPbase))) ∧
  nt_rule_fo (INL nPapp) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nConstructorName) SemU_id)
          (Rpt_fo (Nt_fo (INL nPbase) SemU_id) )
          SemB_papp_ctor_rpt)
        (Nt_fo (INL nPbase) (SemU_bindNT (INL nPapp)))) ∧
  nt_rule_fo (INL nPcons) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPapp) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq (SymbolT «::»)) TokenMap_mktokLf)
            (Nt_fo (INL nPcons) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nPcons))) ∧
  nt_rule_fo (INL nPas) =
    SOME
      (Seq_fo
        (Choice_fo
          (Seq_fo
            (Nt_fo (INL nV) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq AsT) TokenMap_mktokLf)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          (Empty_fo []))
        (Seq_fo (Nt_fo (INL nPcons) SemU_id) (Empty_fo []) SemB_append)
        (SemB_bindNT0 (INL nPas))) ∧
  nt_rule_fo (INL nPattern) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPas) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq ColonT) TokenMap_mktokLf)
            (Nt_fo (INL nType) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nPattern))) ∧
  nt_rule_fo (INL nPatternList) =
    SOME
      (Seq_fo
        (Nt_fo (INL nPattern) SemU_id)
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq CommaT) TokenMap_mktokLf)
            (Nt_fo (INL nPatternList) SemU_id)
            SemB_append)
          (Empty_fo []))
        (SemB_bindNT0 (INL nPatternList))) ∧
  nt_rule_fo (INL nPtuple) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
          (Seq_fo
            (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
            (Empty_fo [])
            SemB_append)
          (SemB_bindNT0 (INL nPtuple)))
        (Seq_fo
          (Tok_fo (TokenCheck_eq LparT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nPatternList) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq RparT) TokenMap_mktokLf)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nPtuple)))) ∧
  nt_rule_fo (INL nLetDec) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq ValT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nPattern) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nE) SemU_id)
                (Empty_fo [])
                SemB_append)
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nLetDec)))
        (Seq_fo
          (Tok_fo (TokenCheck_eq FunT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nAndFDecls) SemU_id)
            (Empty_fo [])
            SemB_append)
          (SemB_bindNT0 (INL nLetDec)))) ∧
  nt_rule_fo (INL nLetDecs) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nLetDec) SemU_id)
          (Seq_fo (Nt_fo (INL nLetDecs) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nLetDecs)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nLetDecs) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nLetDecs)))
          (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nLetDecs))))) ∧
  nt_rule_fo (INL nDecl) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq ValT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nPattern) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nE) SemU_id)
                (Empty_fo [])
                SemB_append)
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nDecl)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq FunT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nAndFDecls) SemU_id)
              (Empty_fo [])
              SemB_append)
            (SemB_bindNT0 (INL nDecl)))
          (Choice_fo
            (Seq_fo
              (Tok_fo (TokenCheck_eq ExceptionT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nDconstructor) SemU_id)
                (Empty_fo [])
                SemB_append)
              (SemB_bindNT0 (INL nDecl)))
            (Choice_fo
              (Seq_fo
                (Tok_fo (TokenCheck_eq LocalT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nDecls) SemU_id)
                  (Seq_fo
                    (Tok_fo (TokenCheck_eq InT) TokenMap_mktokLf)
                    (Seq_fo
                      (Nt_fo (INL nDecls) SemU_id)
                      (Seq_fo
                        (Tok_fo (TokenCheck_eq EndT) TokenMap_mktokLf)
                        (Empty_fo [])
                        SemB_append)
                      SemB_append)
                    SemB_append)
                  SemB_append)
                (SemB_bindNT0 (INL nDecl)))
              (Choice_fo
                (Seq_fo
                  (Nt_fo (INL nTypeDec) SemU_id)
                  (Empty_fo [])
                  (SemB_bindNT0 (INL nDecl)))
                (Choice_fo
                  (Seq_fo
                    (Nt_fo (INL nTypeAbbrevDec) SemU_id)
                    (Empty_fo [])
                    (SemB_bindNT0 (INL nDecl)))
                  (Seq_fo
                    (Nt_fo (INL nStructure) SemU_id)
                    (Empty_fo [])
                    (SemB_bindNT0 (INL nDecl))))))))) ∧
  nt_rule_fo (INL nTypeAbbrevDec) =
    SOME
      (Seq_fo
        (Tok_fo (TokenCheck_eq TypeT) TokenMap_mktokLf)
        (Seq_fo
          (Nt_fo (INL nTypeName) SemU_id)
          (Seq_fo
            (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nType) SemU_id)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nTypeAbbrevDec))) ∧
  nt_rule_fo (INL nDecls) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nDecl) SemU_id)
          (Seq_fo (Nt_fo (INL nDecls) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nDecls)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nDecls) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nDecls)))
          (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nDecls))))) ∧
  nt_rule_fo (INL nOptTypEqn) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
          (Seq_fo (Nt_fo (INL nType) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nOptTypEqn)))
        (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nOptTypEqn)))) ∧
  nt_rule_fo (INL nSpecLine) =
    SOME
      (Choice_fo
        (Seq_fo
          (Tok_fo (TokenCheck_eq ValT) TokenMap_mktokLf)
          (Seq_fo
            (Nt_fo (INL nV) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq ColonT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nType) SemU_id)
                (Empty_fo [])
                SemB_append)
              SemB_append)
            SemB_append)
          (SemB_bindNT0 (INL nSpecLine)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq TypeT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nTypeName) SemU_id)
              (Seq_fo (Nt_fo (INL nOptTypEqn) SemU_id) (Empty_fo []) SemB_append)
              SemB_append)
            (SemB_bindNT0 (INL nSpecLine)))
          (Choice_fo
            (Seq_fo
              (Tok_fo (TokenCheck_eq ExceptionT) TokenMap_mktokLf)
              (Seq_fo
                (Nt_fo (INL nDconstructor) SemU_id)
                (Empty_fo [])
                SemB_append)
              (SemB_bindNT0 (INL nSpecLine)))
            (Seq_fo
              (Nt_fo (INL nTypeDec) SemU_id)
              (Empty_fo [])
              (SemB_bindNT0 (INL nSpecLine)))))) ∧
  nt_rule_fo (INL nSpecLineList) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nSpecLine) SemU_id)
          (Seq_fo (Nt_fo (INL nSpecLineList) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nSpecLineList)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nSpecLineList) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nSpecLineList)))
          (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nSpecLineList))))) ∧
  nt_rule_fo (INL nSignatureValue) =
    SOME
      (Seq_fo
        (Tok_fo (TokenCheck_eq SigT) TokenMap_mktokLf)
        (Seq_fo
          (Nt_fo (INL nSpecLineList) SemU_id)
          (Seq_fo
            (Tok_fo (TokenCheck_eq EndT) TokenMap_mktokLf)
            (Empty_fo [])
            SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nSignatureValue))) ∧
  nt_rule_fo (INL nOptionalSignatureAscription) =
    SOME
      (Seq_fo
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SealT) TokenMap_mktokLf)
            (Seq_fo
              (Nt_fo (INL nSignatureValue) SemU_id)
              (Empty_fo [])
              SemB_append)
            SemB_append)
          (Empty_fo []))
        (Empty_fo [])
        (SemB_bindNT0 (INL nOptionalSignatureAscription))) ∧
  nt_rule_fo (INL nStructName) =
    SOME
      (Tok_fo
        (TokenCheck_alpha TokenAlpha_nonempty)
        (TokenMap_bindNT (INL nStructName))) ∧
  nt_rule_fo (INL nStructure) =
    SOME
      (Seq_fo
        (Tok_fo (TokenCheck_eq StructureT) TokenMap_mktokLf)
        (Seq_fo
          (Nt_fo (INL nStructName) SemU_id)
          (Seq_fo
            (Nt_fo (INL nOptionalSignatureAscription) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq EqualsT) TokenMap_mktokLf)
              (Seq_fo
                (Tok_fo (TokenCheck_eq StructT) TokenMap_mktokLf)
                (Seq_fo
                  (Nt_fo (INL nDecls) SemU_id)
                  (Seq_fo
                    (Tok_fo (TokenCheck_eq EndT) TokenMap_mktokLf)
                    (Empty_fo [])
                    SemB_append)
                  SemB_append)
                SemB_append)
              SemB_append)
            SemB_append)
          SemB_append)
        (SemB_bindNT0 (INL nStructure))) ∧
  nt_rule_fo (INL nTopLevelDecs) =
    SOME
      (Choice_fo
        (Seq_fo
          (Seq_fo
            (Nt_fo (INL nE) SemU_id)
            (Seq_fo
              (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
              (Seq_fo (Nt_fo (INL nTopLevelDecs) SemU_id) (Empty_fo []) SemB_append)
              SemB_append)
            SemB_append)
          (Empty_fo [])
          (SemB_bindNT0 (INL nTopLevelDecs)))
        (Choice_fo
          (Seq_fo
            (Nt_fo (INL nDecl) SemU_id)
            (Seq_fo (Nt_fo (INL nNonETopLevelDecs) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nTopLevelDecs)))
          (Choice_fo
            (Seq_fo
              (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
              (Seq_fo (Nt_fo (INL nTopLevelDecs) SemU_id) (Empty_fo []) SemB_append)
              (SemB_bindNT0 (INL nTopLevelDecs)))
            (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nTopLevelDecs)))))) ∧
  nt_rule_fo (INL nNonETopLevelDecs) =
    SOME
      (Choice_fo
        (Seq_fo
          (Nt_fo (INL nDecl) SemU_id)
          (Seq_fo (Nt_fo (INL nNonETopLevelDecs) SemU_id) (Empty_fo []) SemB_append)
          (SemB_bindNT0 (INL nNonETopLevelDecs)))
        (Choice_fo
          (Seq_fo
            (Tok_fo (TokenCheck_eq SemicolonT) TokenMap_mktokLf)
            (Seq_fo (Nt_fo (INL nTopLevelDecs) SemU_id) (Empty_fo []) SemB_append)
            (SemB_bindNT0 (INL nNonETopLevelDecs)))
          (Seq_fo (Empty_fo []) (Empty_fo []) (SemB_bindNT0 (INL nNonETopLevelDecs))))) ∧
  nt_rule_fo _ =
    NONE
End

Definition corestep_fo_body_def:
  corestep_fo_body (anyE:string) (tokF:string) (tokE:string) (notF:string)
                   s =
  case s of
    EV_fo (Empty_fo v) i r eo errs k fk =>
      AP_fo k i (SOME v::r) eo errs
  | EV_fo (Any_fo m) i r eo errs k fk =>
      (case i of
         [] =>
           let err = (EOF_fo,anyE) in
             AP_fo fk i r (merge_err_option eo (SOME err)) (err::errs)
       | h::t =>
           AP_fo k t (SOME (eval_tok_map m h) :: r) eo errs)
  | EV_fo (Tok_fo p m) i r eo errs k fk =>
      (case i of
         [] =>
           let err = (EOF_fo,tokE) in
             AP_fo fk i r (merge_err_option eo (SOME err)) (err::errs)
       | h::t =>
           if eval_token_check p h then
             AP_fo k t (SOME (eval_tok_map m h)::r) eo errs
           else
             let err = (sloc_pexec i,tokF) in
               AP_fo fk i r (merge_err_option eo (SOME err)) (err::errs))
  | EV_fo (Nt_fo n u) i r eo errs k fk =>
      (case nt_rule_fo n of
         SOME sym =>
           EV_fo sym i r eo errs (App1_plain_fo u k) fk
       | NONE => Looped_fo)
  | EV_fo (Seq_fo e1 e2 b) i r eo errs k fk =>
      EV_fo e1 i r eo errs
         (RestoreEO_fo eo
          (Ksym_fo e2
           (App2_fo b k)
           (CmpEO_fo eo (ReturnTo_fo i r fk))))
         fk
  | EV_fo (Choice_fo e1 e2) i r eo errs k fk =>
      EV_fo e1 i r eo errs
         (App1_cl_fo k)
         (ReturnTo_fo i r
          (Ksym_fo e2
           (DropErr_fo (App1_cr_fo k))
           (CmpErrs_fo fk)))
  | EV_fo (Rpt_fo e) i r eo errs k fk =>
      EV_fo e i (NONE::r) eo errs
         (RestoreEO_fo eo (Listsym_fo e k))
       (Poplist_fo k)
  | EV_fo (Not_fo e v) i r eo errs k fk =>
      EV_fo e i r eo errs
         (RestoreEO_fo eo
            (ReturnTo_fo i r (AddErr_fo (sloc_pexec i) notF fk)))
         (RestoreEO_fo eo (ReturnTo_fo i (SOME v::r) (DropErr_fo k)))
  | EV_fo (Error_fo err) i r eo errs k fk =>
      let err = (sloc_pexec i,err) in
        AP_fo fk i r (merge_err_option eo (SOME err)) (err :: errs)
  | AP_fo Done_fo i [] _ _ => Looped_fo
  | AP_fo Done_fo i (NONE :: t) _ _ => Looped_fo
  | AP_fo Done_fo i (SOME rv :: _) eo _ =>
      Result_fo (Success i rv eo)
  | AP_fo Failed_fo i r eo [] =>
      (case eo of
       NONE => Looped_fo
      | SOME (l,e) => Result_fo (Failure l e))
  | AP_fo Failed_fo i r _ ((l,e)::_) => Result_fo (Failure l e)
    | AP_fo (DropErr_fo k) i r eo [] => AP_fo k i r eo []
  | AP_fo (DropErr_fo k) i r eo (_ :: t) => AP_fo k i r eo t
  | AP_fo (AddErr_fo l e k) i r eo errs =>
      AP_fo k i r (merge_err_option eo (SOME (l,e))) ((l,e)::errs)
  | AP_fo (CmpErrs_fo k) i r eo [] => AP_fo k i r eo []
  | AP_fo (CmpErrs_fo k) i r eo [e] => AP_fo k i r eo [e]
  | AP_fo (CmpErrs_fo k) i r eo ((l2,er2)::(l1,er1)::rest) =>
      AP_fo k i r eo ((l2,er2) :: rest)
    | AP_fo (CmpEO_fo eo1 k) i r eo2 [] =>
      AP_fo k i r (merge_err_option eo1 eo2) []
  | AP_fo (CmpEO_fo eo1 k) i r eo2 ((l,err)::rest) =>
      AP_fo k i r (merge_err_option eo1 (SOME (l,err))) ((l,err)::rest)
  | AP_fo (Ksym_fo e k fk) i r eo errs =>
      EV_fo e i r eo errs k fk
  | AP_fo (App1_plain_fo u k) i (SOME v :: r) eo errs =>
      AP_fo k i (SOME (eval_unary u v) :: r) eo errs
  | AP_fo (App1_cl_fo k) i (SOME v :: r) eo errs =>
      AP_fo k i (SOME (eval_combine (INL v)) :: r) eo errs
  | AP_fo (App1_cr_fo k) i (SOME v :: r) eo errs =>
      AP_fo k i (SOME (eval_combine(INR v)) :: r) eo errs
  | AP_fo (App1_plain_fo _ _) _ _ _ _ => Looped_fo
  | AP_fo (App1_cl_fo _) _ _ _ _ => Looped_fo
  | AP_fo (App1_cr_fo _) _ _ _ _ => Looped_fo
  | AP_fo (App2_fo b k) i (SOME v1 :: SOME v2 :: r) eo errs =>
      AP_fo k i (SOME (eval_binary b v2 v1) :: r) eo errs
  | AP_fo (App2_fo _ _) _ _ _ _ => Looped_fo
  | AP_fo (ReturnTo_fo i r k) i' r' eo errs => AP_fo k i r eo errs
  | AP_fo (RestoreEO_fo eo k) i r eo' errs => AP_fo k i r eo errs
  | AP_fo (Listsym_fo e k) i r eo errs =>
      EV_fo e i r eo errs
         (RestoreEO_fo eo (Listsym_fo e k))
         (Poplist_fo k)
  | AP_fo (Poplist_fo k) i r eo [] =>
      AP_fo k i (poplistval r) eo []
  | AP_fo (Poplist_fo k) i r eo (e :: errs) =>
      AP_fo k i (poplistval r) eo errs
  | Result_fo r => Result_fo r
  | Looped_fo => Looped_fo
End

(* Definition corestep_fo_def:
  corestep_fo s =
    corestep_fo_body "Didn't expect an EOF" "Failed to see expected token"  "Failed to see expected token; saw EOF instead" "Not combinator failed" s
End

Definition coreloop_fo_def[nocompute]:
  coreloop_fo G =
   OWHILE (λs. case s of Result_fo _ => F | _ => T)
          (corestep_fo G)
End *)

Definition run_peg_fo_def:
  run_peg_fo 0 anyE tokF tokE notF st = Looped_fo ∧
  run_peg_fo (SUC n) anyE tokF tokE notF st =
    case st of
      Result_fo r => Result_fo r
    | Looped_fo => Looped_fo
    | st' =>
        run_peg_fo n anyE tokF tokE notF
          (corestep_fo_body anyE tokF tokE notF st')
End

Definition peg_exec_fuel_fo_def:
  peg_exec_fuel_fo fuel e i r eo errs k fk =
    run_peg_fo fuel "Didn't expect an EOF" "Failed to see expected token"  "Failed to see expected token; saw EOF instead" "Not combinator failed"
      (EV_fo e i r eo errs k fk)
End

Definition peg_exec_core_fuel_def:
  peg_exec_core_fuel fuel i =
  peg_exec_fuel_fo fuel (Nt_fo (INL nTopLevelDecs) SemU_id) i [] NONE [] Done_fo Failed_fo
End

(* Definition peg_exec_fo_def[nocompute]: *)
(*   peg_exec_fo G e i r eo errs k fk = *)
(*     case coreloop_fo G (EV_fo e i r eo errs k fk) of *)
(*       SOME r => r *)
(*     | NONE => Looped_fo *)
(* End *)

(* Definition applykont_fo_def[nocompute]: *)
(*   applykont_fo G k i r eo errs = *)
(*     case coreloop_fo G (AP_fo k i r eo errs) of *)
(*       SOME r => r *)
(*     | NONE => Looped_fo *)
(* End *)

Definition map_ptree_loc_def:
  map_ptree_loc [] = [] /\
  map_ptree_loc (x::ts) = ptree_loc x::map_ptree_loc ts
End

Theorem map_ptree_loc_thm:
  MAP ptree_loc l = map_ptree_loc l
Proof
  Induct_on ‘l’ >> simp[map_ptree_loc_def]
QED

val _ = cv_trans locationTheory.unknown_loc_def;
val _ = cv_trans locationTheory.merge_locs_def;
val _ = cv_trans locationTheory.merge_list_locs_def;
val _ = cv_trans grammarTheory.ptree_loc_def;
val _ = cv_trans map_ptree_loc_def;
val _ = cv_trans ((grammarTheory.ptree_list_loc_def) |> REWRITE_RULE [map_ptree_loc_thm]);
val _ = cv_trans mkNd_fo_def;
val _ = cv_trans tokenUtilsTheory.destLf_def;
val _ = cv_trans tokenUtilsTheory.destTOK_def;
val _ = cv_trans peg_Ebase_paren_fo_def;
val _ = cv_trans mk_linfix_fo_def;
val _ = cv_trans foldl_Eapp_aux_def;

val _ = cv_trans foldl_DType_aux_def;
val _ = cv_trans foldl_Eapp_fo_def;
val _ = cv_trans foldl_DType_fo_def;

val _ = cv_trans ptPapply0_fo_def;
val _ = cv_trans ptPapply_fo_def;
val _ = cv_trans listTheory.LENGTH;
val _ = cv_trans_pre "HD_pre" listTheory.HD;
Theorem HD_pre_LENGTH_thm:
  HD_pre l ⇔ 0 < LENGTH l
Proof
  Cases_on ‘l’ >> simp[DB.fetch "-" "HD_pre_cases"]
QED



val _ = cv_trans_pre "epcrf_pre" eval_papp_ctor_rpt_fo_def;
Theorem epcrf_pre[cv_pre]:
  ∀pts. epcrf_pre pts
Proof
  simp[DB.fetch "-" "epcrf_pre_cases", HD_pre_LENGTH_thm]
QED

val _ = cv_trans listTheory.APPEND;
val _ = cv_trans eval_binary_def;
val _ = cv_trans eval_combine_def;
val _ = cv_trans listTheory.FLAT;
val _ = cv_trans eval_fold_def;

val _ = cv_trans eval_unary_def;
val _ = cv_trans stringTheory.isUpper_def;
val _ = cv_trans_pre "TL_pre" listTheory.TL;
val _ = cv_trans_pre "EL_pre" listTheory.EL;
val _ = cv_trans_pre "strsub_pre" mlstringTheory.strsub_def;
val etac_pre_res = cv_trans_pre "etac_pre" eval_token_alpha_check_def;


Theorem TL_pre_LENGTH_thm:
  TL_pre l ⇔ 0 < LENGTH l
Proof
  Cases_on ‘l’ >> simp[DB.fetch "-" "TL_pre_cases"]
QED
Theorem EL_pre_thm:
  ∀ i l. EL_pre i l ⇔ i < LENGTH l
Proof
  Induct_on ‘l’ >> simp[Once (DB.fetch "-" "EL_pre_cases")] >>
  simp[HD_pre_LENGTH_thm, TL_pre_LENGTH_thm]
  >> Cases_on ‘i’ >> simp[]
QED
Theorem strsub_pre_thm:
  strsub_pre s i ⇔ i < strlen s
Proof
  Cases_on ‘s’ >> simp[DB.fetch "-" "strsub_pre_cases", EL_pre_thm]
QED
Theorem etac_pre[cv_pre]:
  ∀v s. etac_pre v s
Proof
  Cases_on ‘s’ >> Cases_on ‘s'’ >> simp[Once etac_pre_res, strsub_pre_thm]
QED
val _ = cv_trans listTheory.isPREFIX;
val _ = cv_trans validMultSym_def;
val ea_pre_res = cv_trans_pre "ea_pre" mlstringTheory.explode_aux_def;
Theorem ea_pre_thm:
  ∀s i j. i+j ≤ strlen s ⇒  ea_pre s i j
Proof
       Induct_on ‘j’ >> simp[Once ea_pre_res, strsub_pre_thm]
QED
val _ = cv_trans mlstringTheory.strlen_def;
val explode_pre_res = cv_trans_pre "explode_pre" mlstringTheory.explode_def;
Theorem explode_pre[cv_pre]:
  ∀s . explode_pre s
Proof
  rw [explode_pre_res] >> irule ea_pre_thm >> simp[]
QED

val _ = cv_trans in_set_def;
val _ = cv_trans validAddSym_alt_def;
val _ = cv_trans validRelSym_def;
val _ = cv_trans validListSym_def;
val _ = cv_trans validPrefixSym_def;
val _ = cv_trans eval_token_symbol_check_def;
val _ = cv_trans stringTheory.isLower_def;
val _ = cv_trans stringTheory.isAlpha_def;

val etlca_pre_res =
  cv_trans_pre "etlca_pre" eval_token_longid_check_alt_def;

Theorem mlstring_nonempty_strlen:
  ∀ms. ms ≠ «» ⇔ 0 < strlen ms
Proof
  Cases >> simp[mlstringTheory.strlen_def] >>
  Cases_on ‘s’ >> simp[]
QED

Theorem etlca_pre[cv_pre]:
  ∀v p. etlca_pre v p
Proof
  Cases >> Cases >>
  rw[etlca_pre_res, strsub_pre_thm] >>
  fs[GSYM mlstring_nonempty_strlen]
QED
val _ = cv_trans tokenUtilsTheory.destLongidT_def;
val _ = cv_trans tokenUtilsTheory.destAlphaT_def;
val _ = cv_trans tokenUtilsTheory.destSymbolT_def;
val _ = cv_trans tokenUtilsTheory.destFFIT_def;
val _ = cv_trans tokenUtilsTheory.isInt_def;
val _ = cv_trans tokenUtilsTheory.isString_def;
val _ = cv_trans tokenUtilsTheory.isCharT_def;
val _ = cv_trans tokenUtilsTheory.isWordT_def;
val _ = cv_trans tokenUtilsTheory.isTyvarT_def;
val _ = cv_trans tokenUtilsTheory.isAlphaSym_def;
val _ = cv_trans tokenUtilsTheory.isLongidT_def;
val _ = cv_trans optionTheory.IS_SOME_DEF;

val _ = cv_trans eval_token_check_def;
val _ = cv_trans eval_tok_map_def;
val _ = cv_trans merge_err_option_def;
val _ = cv_trans poplist_aux_def;
val _ = cv_trans poplistval_def;
val _ = cv_trans sloc_pexec_def;
val _ = cv_trans nt_rule_fo_def;
val _ = cv_trans corestep_fo_body_def;

val _ = cv_trans run_peg_fo_def;
val _ = cv_trans peg_exec_fuel_fo_def;
val _ = cv_trans peg_exec_core_fuel_def;

(* EVAL ``eval_token_check TokenCheck_isInt (IntT 3, Locs (POSN 0 0) (POSN 0 0))``; *)
(* EVAL ``peg_exec_fuel_fo 500000 *)
(*         (Tok_fo TokenCheck_isInt (TokenMap_bindNT (INL nEliteral))) *)
(*         (lexer_fun "3") [] NONE [] Done_fo Failed_fo``; *)
(* EVAL ``peg_exec_fuel_fo 500000 (Nt_fo (INL nE) SemU_id) *)
(*         (lexer_fun "3") [] NONE [] Done_fo Failed_fo``; *)
(* EVAL ``peg_exec_fuel_fo 200000 (Nt_fo (INL nDecl) SemU_id) *)
(*         (lexer_fun "val x = 3") [] NONE [] Done_fo Failed_fo``; *)
val toks = EVAL “ lexer_fun "val x = 3+y;"” |> concl|> rhs;
toks;
(* cv_eval ``peg_exec_core_fuel 200000000 ^toks``; *)

val xlrupsraw = ``[
  strlit"8 d 0";
  strlit"x d 1 2 0";
  strlit"9 6 1 0 1 2 8 0";
  strlit"10 6 2 0 3 4 8 0";
  strlit"11 6 3 0 5 6 8 0";
  strlit"12 -6 4 0 1 5 7 3 0";
  strlit"x 1234 -6 4 0 1 5 7 3 0";
  strlit"o x 5 -1 1 2 3 0";
  strlit"12 d 1 5 3 0";
  strlit"13 -6 5 0 2 6 7 4 0";
  strlit"13 d 2 6 4 0";
  strlit"14 6 0 9 10 11 7 0";
  strlit"14 d 9 10 11 7 0";
  strlit"16 0 14 12 13 8 0";
  strlit"i cx 17 1 2 3 4 0 14 12 13 8 0";
  strlit"i x 17 0 14 12 13 8 0";
  strlit"o b 18 1 2 3 4 0 14 15 0 ";
  strlit"o b 18 1 2 3 4 0 14 0 ";
  strlit"i cb 17 1 2 3 4 0 14 u 12 13 8 0";
  strlit"b 18 1 2 3 4 0 14 15 0 12 13 8 0";
  strlit"b 18 1 2 3 4 0 14 0 12 13 8 0";
  strlit"b d 1 2 3 4 0";
  ]``;

val cv_xlrup_bench_single_short =
  time EVAL ``parse_xlrup (toks_fast (strlit"8 d 0"))``;

val cv_xlrup_bench_single_long =
  time EVAL ``parse_xlrup (toks_fast (strlit"12 -6 4 0 1 5 7 3 0"))``;

val cv_xlrup_bench_single_imp =
  time EVAL ``parse_xlrup (toks_fast (strlit"i cx 17 1 2 3 4 0 14 12 13 8 0"))``;

val cv_xlrup_bench_batch =
time EVAL ``parse_xlrups ^(xlrupsraw)``;
val _ = cv_trans listTheory.REVERSE_DEF;
val _ = cv_trans xlrup_parsingTheory.starts_with_def;
val _ = cv_trans integerTheory.INT_ABS;
val _ = cv_trans xlrup_parsingTheory.parse_until_c_zero_nn_def;

val _ = cv_trans xlrup_parsingTheory.parse_until_zero_def;
val _ = cv_trans xlrup_parsingTheory.parse_until_zero_nn_def;
val _ = cv_trans xlrup_parsingTheory.parse_u_rest_def;
val _ = cv_trans xlrup_parsingTheory.parse_id_u_rest_def;
val _ = cv_trans xlrup_parsingTheory.parse_xadd_xdel_def;
val _ = cv_trans xlrup_parsingTheory.parse_rest_def;
val _ = cv_trans xlrup_parsingTheory.parse_id_rest_def;

val _ = cv_trans xlrup_parsingTheory.parse_imply_def;
val _ = cv_trans cnf_extTheory.mk_lit_def;
val _ = cv_trans cnf_extTheory.parse_lits_aux_def;
val _ = cv_trans cnf_extTheory.parse_bnn_tail_def;
val _ = cv_trans xlrup_parsingTheory.parse_bnn_nomv_def;
val _ = cv_trans xlrup_parsingTheory.parse_xor_nomv_def;
val _ = cv_trans xlrup_parsingTheory.parse_orig_def;

Definition wrap_lst_def:
  wrap_lst lst = case lst of
    [] => []
  | h::hs => INR h :: wrap_lst hs
End

(* Definition parse_badd_tail_fo_def:
  parse_badd_tail_fo (tl:int list) = parse_bnn_tail ((wrap_lst tl ++ [INR 0]):(unit + int) list)
End *)
Theorem wrap_lst_nil[simp]:
  wrap_lst [] = []
Proof
  simp[wrap_lst_def]
QED

Theorem wrap_lst_cons[simp]:
  wrap_lst (h::hs) = INR h :: wrap_lst hs
Proof
  rw[Once wrap_lst_def]
QED

Theorem wrap_lst_thm:
  MAP INR tl = wrap_lst tl
Proof
  Induct_on ‘tl’ >> simp[MAP]
QED

val _ = cv_trans wrap_lst_def;
val _ = cv_trans ((xlrup_parsingTheory.parse_badd_tail_def) |> REWRITE_RULE [wrap_lst_thm]);


val _ = cv_trans xlrup_parsingTheory.split_hint_def;
val _ = cv_trans xlrup_parsingTheory.parse_badd_def;
val _ = cv_trans xlrup_parsingTheory.parse_badd_bdel_def;
val _ = cv_trans xlrup_parsingTheory.parse_rup_del_def;
val _ = cv_trans xlrup_parsingTheory.parse_xlrup_def;
Definition map_tokenize_def:
  map_tokenize l = case l of
    [] => []
  | h::hs => tokenize_fast h :: map_tokenize hs
End
Theorem map_tokenize_thm:
  MAP tokenize_fast l = map_tokenize l
Proof
   Induct_on ‘l’
  >- (
       once_rewrite_tac [map_tokenize_def]
       >> simp[MAP]
     )
  >> gen_tac
  >> once_rewrite_tac [map_tokenize_def]
  >> simp[MAP]
QED
val _ = cv_trans xlrup_parsingTheory.is_lowercase_def;
val _ = cv_trans mlstringTheory.strlen_def;
val _ = cv_trans mlintTheory.exp_for_dec_enc_def;
val _ = cv_trans mlintTheory.padLen_DEC_def;
val _ = cv_trans mlintTheory.fromChar_unsafe_def;
val fcru_pre_res = cv_trans_pre "fcru_pre" mlintTheory.fromChars_range_unsafe_def;
val fcru_pre_cases = DB.fetch "-" "fcru_pre_cases";

Theorem fcru_pre[cv_pre]:
  ∀l v str. l + v ≤ strlen str ⇒ fcru_pre l v str
Proof
  Induct_on ‘v’
  >- simp[fcru_pre_res]
  >> rpt gen_tac >> strip_tac
  >> rw[Once fcru_pre_res]
  >> rpt strip_tac
  >> fs[ADD1, strsub_pre_thm]
QED

(* val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE [mlintTheory.maxSmall_DEC_def, mlintTheory.padLen_DEC_eq]);

Theorem fromChars_unsafe_ind[local]:
  fromchars_unsafe_ind
Proof
  rewrite_tac [fetch "-" "fromchars_unsafe_ind_def"]
  \ rpt gen_tac
  \ rpt (disch_then strip_assume_tac)
  \ match_mp_tac (latest_ind ())
  \ rpt strip_tac
  \ last_x_assum match_mp_tac
  \ rpt strip_tac
  \ fs [FORALL_PROD]
  \ fs [mlintTheory.padLen_DEC_eq, ADD1]
QED *)

val _ = fromChars_unsafe_ind |> update_precondition;

val _ = cv_trans mlintTheory.maxSmall_DEC_def;

val _ = cv_trans xlrup_parsingTheory.fromString_unsafe_def;
val _ = cv_trans xlrup_parsingTheory.tokenize_fast_def;
val _ = cv_trans map_tokenize_def;
val _ = cv_trans ((xlrup_parsingTheory.toks_fast_def) |> REWRITE_RULE [map_tokenize_thm]);

val cv_xlrup_bench_single_short =
  time cv_eval ``parse_xlrup (toks_fast (strlit"8 d 0"))``;

val cv_xlrup_bench_single_long =
  time cv_eval ``parse_xlrup (toks_fast (strlit"12 -6 4 0 1 5 7 3 0"))``;

val cv_xlrup_bench_single_imp =
  time cv_eval ``parse_xlrup (toks_fast (strlit"i cx 17 1 2 3 4 0 14 12 13 8 0"))``;

val cv_xlrup_bench_batch =
  time cv_eval ``parse_xlrups ^(xlrupsraw)``;
