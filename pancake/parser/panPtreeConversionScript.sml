(**
 * Theory for translating the Pancake parse tree into the Pancake AST.
 *)

(*
 * We take some inspiration from the existing conversion theory
 * for CakeML.
 *
 * Created by Craig McLaughlin on 6/5/2022.
 *)

open HolKernel Parse boolLib bossLib stringLib numLib intLib;

open arithmeticTheory;
open preamble pegTheory pegexecTheory;
open grammarTheory;
open panLexerTheory panLangTheory panPEGTheory;
open ASCIInumbersLib combinTheory;
open helperLib;

val _ = new_theory "panPtreeConversion";

(** Set HOL to parse operations in following definition
  * for Option monad. *)
val _ = preamble.option_monadsyntax.temp_add_option_monadsyntax();

Overload lift[local] = ``option$OPTION_MAP``

(** Copied from tokenUtilsTheory: prevent a conflict between
  * panLexer$token and token$token. *)
Definition destLf_def[simp]:
  (destLf (Lf (x,_)) = SOME x) ∧ (destLf _ = NONE)
End

Definition destTOK_def[simp]:
  (destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)
End
(** End copy *)

(** Copied from cmlptreeconversion *)
Overload "'"[local] = ``λf a. OPTION_BIND a f``

Overload ptree_size[local] = ``parsetree_size (K 0) (K 0) (K 0)``;
Overload ptree1_size[local] = ``parsetree1_size (K 0) (K 0) (K 0)``;

Definition tokcheck_def:
  tokcheck pt expected =
    case (destTOK ' (destLf pt)) of
      SOME actual => actual = expected
    | NONE => F
End
(** End copy **)

Definition dest_annot_tok_def:
  dest_annot_tok pt = case (OPTION_BIND (destLf pt) destTOK) of
      SOME (AnnotCommentT c) => SOME c
    | _ => NONE
End

Definition kw_def:
  kw k = KeywordT k
End

Definition isNT_def:
  isNT nodeNT ntm ⇔ FST nodeNT = INL ntm
End

Definition argsNT_def:
  argsNT (Lf _) _ = NONE ∧
  argsNT (Nd nodeNT args) ntm =
    if FST nodeNT = INL ntm then SOME args else NONE
End

Definition conv_int_def:
  conv_int tree =
    case destTOK ' (destLf tree) of
      SOME (IntT n) => SOME n
    | _ => NONE
End

Definition conv_nat_def:
  conv_nat tree =
    case conv_int tree of
      SOME n => if n >= 0 then SOME (Num n) else NONE
    | _ => NONE
End

Definition conv_const_def:
  conv_const t = lift (panLang$Const o i2w) $ conv_int t
End

Definition conv_ident_def:
  conv_ident tree =
    case destTOK ' (destLf tree) of
      SOME (IdentT s) => SOME (strlit s)
    | _ => NONE
End

Definition conv_ffi_ident_def:
  conv_ffi_ident tree =
    case destTOK ' (destLf tree) of
      SOME (ForeignIdent s) => SOME (strlit s)
    | _ => NONE
End

Definition conv_var_def:
  conv_var t = lift Var (conv_ident t)
End

(** Collection of binop expression nodes, n >= 2 *)
Definition binaryExps_def:
  binaryExps = [EOrNT; EXorNT; EAndNT; EAddNT]
End

Definition panExps_def:
  panExps = [EMulNT]
End

(** Subtraction must apply to only two subexpressions.
  * See the pancake semantics script. *)
Definition isSubOp_def:
  isSubOp (Op Sub [e1;e2]) = T ∧
  isSubOp _ = F
End

(* Convert a binary operator into its AST representation. *)
Definition conv_binop_def:
  (conv_binop (Nd nodeNT args) =
     if isNT nodeNT AddOpsNT then
       case args of
         [leaf] => conv_binop leaf
       | _ => NONE
     else NONE) ∧
  conv_binop leaf =
   if tokcheck leaf PlusT then SOME Add
   else if tokcheck leaf MinusT then SOME Sub
   else if tokcheck leaf AndT then SOME And
   else if tokcheck leaf OrT then SOME Or
   else if tokcheck leaf XorT then SOME Xor
   else NONE
End

Definition conv_panop_def:
  (conv_panop (Nd nodeNT args) =
     if isNT nodeNT MulOpsNT then
       case args of
         [leaf] => conv_panop leaf
       | _ => NONE
     else NONE) ∧
  conv_panop leaf =
   if tokcheck leaf StarT then SOME Mul
   else NONE
End

Definition conv_shift_def:
  (conv_shift (Nd nodeNT args) =
   if isNT nodeNT ShiftOpsNT then
     case args of
       [leaf] => conv_shift leaf
     | _ => NONE
   else NONE) ∧
  conv_shift leaf =
  if tokcheck leaf LslT then SOME Lsl
  else if tokcheck leaf LsrT then SOME Lsr
  else if tokcheck leaf AsrT then SOME Asr
  else if tokcheck leaf RorT then SOME Ror
  else NONE
End

Definition conv_cmp_def:
  (conv_cmp (Nd nodeNT args) =
   if isNT nodeNT CmpOpsNT ∨ isNT nodeNT EqOpsNT then
     case args of
       [leaf] => conv_cmp leaf
     | _ => NONE
   else NONE) ∧
  conv_cmp leaf =
  if tokcheck leaf EqT then SOME(Equal,F)
  else if tokcheck leaf NeqT then SOME(NotEqual,F)
  else if tokcheck leaf LessT then SOME(Less,F)
  else if tokcheck leaf GeqT then SOME(NotLess,F)
  else if tokcheck leaf GreaterT then SOME(Less,T)
  else if tokcheck leaf LeqT then SOME(NotLess,T)
  else if tokcheck leaf LowerT then SOME(Lower,F)
  else if tokcheck leaf HigherT then SOME(Lower,T)
  else if tokcheck leaf HigheqT then SOME(NotLower,F)
  else if tokcheck leaf LoweqT then SOME(NotLower,T)
  else NONE
End

(** A single tree is smaller than the forest. *)
Definition conv_Shape_def:
  conv_Shape tree =
  case conv_int tree of
    SOME n =>
      if n < 1 then NONE
      else if n = 1 then SOME One
      else
        SOME $ Comb $ REPLICATE (Num n) One
  | NONE =>
      (case argsNT tree ShapeCombNT of
         SOME ts => lift Comb $ OPT_MMAP conv_Shape ts
       | _ => NONE)
Termination
  WF_REL_TAC ‘measure ptree_size’ >> rw[]
  >> Cases_on ‘tree’
  >> gvs[argsNT_def]
  >> drule MEM_list_size
  >> disch_then (qspec_then`ptree_size` assume_tac)
  >> simp[]
End

Definition conv_params_def:
  conv_params as =
  case as of
    (s::t::ps) =>
      (case (conv_Shape s) of
         SOME sh =>
           (case (conv_ident t) of
              SOME v => (lift (CONS (v, sh))) (conv_params ps)
            | _ => NONE)
       | _ => NONE)
  | [] => SOME []
  | _ => NONE
End

Definition conv_Shift_def:
  conv_Shift [] e = SOME e ∧
  conv_Shift [x] e = NONE ∧
  (conv_Shift (t1::t2::ts) e =
    do op <- conv_shift t1;
       n <- conv_nat t2;
       conv_Shift ts (Shift op e n)
    od)
End

(** Convert a expression parse tree into the corresponding AST.
  *
  * The definition is slightly complicated by the requirement that
  * subtraction must have exactly two children. All the other 'binop'
  * operations can have ≥ 2 arguments. See the Pancake semantics script
  * for precise details. *)
Definition conv_Exp_def:
  (conv_ArgList tree =
    case argsNT tree ArgListNT of
      SOME (t::ts) => OPT_MMAP conv_Exp (t::ts)
    | _ => NONE) ∧
  (conv_Exp (Nd nodeNT args) =
    if isNT nodeNT EBaseNT then
      case args of
        [] => NONE
      | [t] => conv_const t ++ conv_var t ++ conv_Exp t
      | t::ts => FOLDL (λe t. lift2 Field (conv_nat t) e) (conv_var t ++ conv_Exp t) ts
    else if isNT nodeNT LabelNT then
      case args of
        [t] => lift Label (conv_ident t)
      | _ => NONE
    else if isNT nodeNT FLabelNT then
      case args of
        [t] => lift Label (conv_ident t)
      | _ => NONE
    else if isNT nodeNT StructNT then
      case args of
        [ts] => do es <- conv_ArgList ts;
                   SOME $ Struct es
                od
      | _ => NONE
    else if isNT nodeNT NotNT then
      case args of
        [t] => lift (Cmp Equal (Const 0w)) (conv_Exp t)
      | _ => NONE
    else if isNT nodeNT ELoadByteNT then
      case args of
        [t] => lift LoadByte (conv_Exp t)
      | _ => NONE
    else if isNT nodeNT ELoad32NT then
      case args of
        [t] => lift Load32 (conv_Exp t)
      | _ => NONE
    else if isNT nodeNT ELoadNT then
      case args of
        [t1; t2] => do s <- conv_Shape t1;
                       e <- conv_Exp t2;
                       SOME $ Load s e
                    od
      | _ => NONE
    else if isNT nodeNT ECmpNT ∨ isNT nodeNT EEqNT then
      case args of
        [e] => conv_Exp e
      | [e1; op; e2] => do e1' <- conv_Exp e1;
                           (op',b) <- conv_cmp op;
                           e2' <- conv_Exp e2;
                           SOME $ if b then Cmp op' e2' e1'
                                  else Cmp op' e1' e2'
                        od
      | _ => NONE
    else if isNT nodeNT ExpNT then (* boolean or *)
      case args of
        [e] => conv_Exp e
      | e1::args' => do es  <- OPT_MMAP conv_Exp $ e1::args';
                        SOME $ Cmp NotEqual (Const 0w) $ Op Or es
                     od
      | _ => NONE
    else if isNT nodeNT EBoolAndNT then
      case args of
        [e] => conv_Exp e
      | e1::args' => do es  <- OPT_MMAP conv_Exp $ e1::args';
                        SOME $ Op And $ MAP (λe. Cmp NotEqual (Const 0w) e) es
                     od
      | _ => NONE
    else if isNT nodeNT EShiftNT then
      case args of
        (e::es) => conv_Shift es ' (conv_Exp e)
      | _ => NONE
    else if EXISTS (isNT nodeNT) binaryExps then
      case args of
        [] => NONE
      | (e::es) => conv_binaryExps es ' (conv_Exp e)
    else if EXISTS (isNT nodeNT) panExps then
      case args of
        [] => NONE
      | (e::es) => conv_panops es ' (conv_Exp e)
    else NONE) ∧
  (conv_Exp leaf = if tokcheck leaf (kw BaseK) then SOME BaseAddr
                   else if tokcheck leaf (kw BiwK) then SOME BytesInWord
                   else if tokcheck leaf (kw TrueK) then SOME $ Const 1w
                   else if tokcheck leaf (kw FalseK) then SOME $ Const 0w
                  else NONE) ∧
  conv_binaryExps [] e = SOME e ∧
  (conv_binaryExps (t1::t2::ts) res =
    do op <- conv_binop t1;
       e <- conv_Exp t2;
       case res of
         Op bop es => if bop ≠ op ∨ isSubOp res then
                        conv_binaryExps ts (Op op [res; e])
                      else conv_binaryExps ts (Op bop (APPEND es [e]))
       | e' => conv_binaryExps ts (Op op [e'; e])
    od) ∧
  conv_binaryExps _ _ = NONE ∧ (* Impossible: ruled out by grammar. *)
  conv_panops [] e = SOME e ∧
  (conv_panops (t1::t2::ts) res =
    do op <- conv_panop t1;
       e <- conv_Exp t2;
       case res of
         Panop bop es => conv_panops ts (Panop op [res; e])
       | e' => conv_panops ts (Panop op [e'; e])
    od) ∧
  conv_panops _ _ = NONE (* Impossible: ruled out by grammar. *)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INR (INL x) => ptree_size x
                           | INL x => ptree_size x
                           | INR (INR(INL x)) => list_size ptree_size (FST x)
                           | INR (INR(INR x)) => list_size ptree_size (FST x))’ >> rw[]
  >> simp[]
  >- (
    drule MEM_list_size
    >> disch_then (qspec_then `ptree_size` assume_tac)
    >> simp[])
  >- (
    drule MEM_list_size
    >> disch_then (qspec_then `ptree_size` assume_tac)
    >> simp[])
  >> Cases_on ‘tree’
  >> gvs[argsNT_def]
  >> drule MEM_list_size
  >> disch_then (qspec_then `ptree_size` assume_tac)
  >> simp[]
End

(** Handles all statements which cannot contain
  * Prog nodes as children. *)
Definition conv_NonRecStmt_def:
  (conv_NonRecStmt (Nd nodeNT args) =
    if isNT nodeNT AssignNT then
      case args of
        [dst; src] => lift2 Assign (conv_ident dst) (conv_Exp src)
      | _ => NONE
    else if isNT nodeNT StoreNT then
      case args of
        [dst; src] => lift2 Store (conv_Exp dst) (conv_Exp src)
      | _ => NONE
    else if isNT nodeNT StoreByteNT then
      case args of
        [dst; src] => lift2 StoreByte (conv_Exp dst) (conv_Exp src)
      | _ => NONE
    else if isNT nodeNT Store32NT then
      case args of
        [dst; src] => lift2 Store32 (conv_Exp dst) (conv_Exp src)
      | _ => NONE
    else if isNT nodeNT SharedLoadNT then
      case args of
        [v; e] => lift2 (ShMemLoad OpW) (conv_ident v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT SharedLoadByteNT then
      case args of
        [v; e] => lift2 (ShMemLoad Op8) (conv_ident v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT SharedLoad32NT then
      case args of
        [v; e] => lift2 (ShMemLoad Op32) (conv_ident v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT SharedStoreNT then
      case args of
        [v; e] => lift2 (ShMemStore OpW) (conv_Exp v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT SharedStoreByteNT then
      case args of
        [v; e] => lift2 (ShMemStore Op8) (conv_Exp v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT SharedStore32NT then
      case args of
        [v; e] => lift2 (ShMemStore Op32) (conv_Exp v) (conv_Exp e)
      | _ => NONE
    else if isNT nodeNT ExtCallNT then
      case args of
        [name; ptr; clen; array; alen] =>
          do name' <- conv_ffi_ident name;
             ptr' <- conv_Exp ptr;
             clen' <- conv_Exp clen;
             array' <- conv_Exp array;
             alen' <- conv_Exp alen;
             SOME $ ExtCall name' ptr' clen' array' alen'
          od
      | _ => NONE
    else if isNT nodeNT RaiseNT then
      case args of
        [id; e] => do eid <- conv_ident id;
                      e' <- conv_Exp e;
                      SOME $ Raise eid e'
                   od
      | _ => NONE
    else if isNT nodeNT ReturnNT then
      case args of
        [e] => lift Return $ conv_Exp e
      | _ => NONE
    else NONE) ∧
  conv_NonRecStmt leaf =
    if tokcheck leaf (kw SkipK) then SOME Skip
    else if tokcheck leaf (kw BrK) then SOME Break
    else if tokcheck leaf (kw ContK) then SOME Continue
    else if tokcheck leaf (kw TicK) then SOME Tick
    else (case dest_annot_tok leaf of
      | SOME c => SOME (Annot (strlit "@") (implode c))
      | NONE => NONE)
End

Definition butlast_def:
  (butlast [] = []) ∧
  (butlast (x::xs) = (if xs = [] then [] else x::(butlast xs)))
End

Theorem butlast_length:
  ∀xs. LENGTH (butlast xs) = LENGTH xs - 1
Proof
  Induct>>rw[]>>gs[butlast_def]>>
  Cases_on ‘xs’>>gs[]
QED

Theorem butlast_tl[simp]:
  ∀xs. butlast (TL xs) = TL (butlast xs)
Proof
  Induct>>rw[]>>gs[butlast_def]>>
  Cases_on ‘xs’>>gs[butlast_def]
QED

Theorem butlast_append[simp]:
  ∀xs ys. butlast (xs ++ ys) = (if ys = [] then butlast xs else xs ++ butlast ys)
Proof
  Induct>>rw[]>>gs[butlast_def]
QED

Theorem list_size_butlast:
  ∀xs f. list_size f (butlast xs) ≤ list_size f xs
Proof
  Induct>>rw[]>>gs[butlast_def]>>
  IF_CASES_TAC>>gs[list_size_def]
QED

Theorem list_size_MEM:
  ∀xs x. MEM x xs ⇒ f x ≤ list_size f xs
Proof
  Induct>>rw[]>>gs[list_size_def]>>
  last_x_assum (qspec_then ‘x’ assume_tac)>>
  gs[]
QED

Definition parsetree_locs_def:
  parsetree_locs tree = (case tree of
    | Nd (_, Locs p1 p2) _ => (p1, p2)
    | Lf (_, Locs p1 p2) => (p1, p2)
  )
End

Definition posn_string_def:
  posn_string (POSN lnum cnum) = (toString lnum ++ ":" ++ toString cnum) /\
  posn_string EOFpt = "EOF" /\
  posn_string UNKNOWNpt = "UNKNOWN"
End

Definition locs_comment_def:
  locs_comment (p1, p2) = implode ("(" ++ posn_string p1 ++ " " ++ posn_string p2 ++ ")")
End

Definition add_locs_annot_def:
  add_locs_annot ptree prog = panLang$Seq (Annot (strlit "location") (locs_comment (parsetree_locs ptree))) prog
End

val Nd = “Nd : (pancakeNT + num) # locs -> (token, pancakeNT, locs) parsetree list -> (token, pancakeNT, locs) parsetree”;

Definition conv_Dec_def:
  (conv_Dec (^Nd nodeNT args) =
   if isNT nodeNT DecNT then
     case args of
       [id; e] => do v <- conv_ident id;
                     e' <- conv_Exp e;
                     SOME (v,e')
                  od
     | _ => NONE
   else
     NONE) ∧
  conv_Dec _ = NONE
End

Definition conv_DecCall_def:
  (conv_DecCall (^Nd nodeNT args) =
   if isNT nodeNT DecCallNT then
     case args of
       s::i::e::ts =>
         do s' <- conv_Shape s;
            i' <- conv_ident i;
            e' <- conv_Exp e;
            args' <- (case ts of [] => SOME [] | args::_ => conv_ArgList args);
            SOME (s',i',e':'a exp,args': 'a exp list)
         od
     | _ => NONE
   else
     NONE) ∧
  conv_DecCall _ = NONE
End

Definition conv_Prog_def:
  (conv_Handle tree =
    case argsNT tree HandleNT of
    | SOME [eid; id; p] => do excp <- conv_ident eid;
                              var <- conv_ident id;
                              prog <- conv_Prog p;
                              SOME $ SOME (excp, var, prog)
                           od
    | _ => NONE) ∧
  (conv_Ret tree =
   if tokcheck tree (kw RetK) then
     SOME $ NONE
   else
     case argsNT tree RetNT of
     | SOME [id; t] => do var <- conv_ident id;
                          hdl <- conv_Handle t;
                          SOME $ SOME (SOME var, hdl)
                       od
     | SOME [id] => do var <- conv_ident id;
                       SOME $ SOME (SOME var, NONE)
                    od
     | _ => NONE) ∧
  (conv_Prog (Nd nodeNT args) =
     let nd = Nd nodeNT args in
     if isNT nodeNT DecNT then
       case args of
         [d; p] => do (v,e') <- conv_Dec d;
                      p' <- conv_Prog p;
                      SOME (add_locs_annot nd (Dec v e' p'))
                   od
       | _ => NONE
     else if isNT nodeNT IfNT then
       case args of
       | [e; p1; p2] => do e' <- conv_Exp e;
                           p1' <- conv_Prog p1;
                           p2' <- conv_Prog p2;
                           SOME (add_locs_annot nd (If e' p1' p2'))
                        od
       | _ => NONE
     else if isNT nodeNT WhileNT then
       case args of
         [e; p] => do e' <- conv_Exp e;
                      p' <- conv_Prog p;
                      SOME (add_locs_annot nd (While e' p'))
                   od
       | _ => NONE
     else if isNT nodeNT DecCallNT then
       case args of
         [dec; p] =>
           do (s',i',e',args') <- conv_DecCall dec;
               p' <- conv_Prog p;
               SOME $ add_locs_annot nd $ DecCall i' s' e' args' p'
           od
       | _ => NONE
     else if isNT nodeNT CallNT then
       case args of
         [] => NONE
       | r::ts =>
           (case conv_Ret r of
              SOME NONE =>
                (case ts of
                   [] => NONE
                 | r::ts =>
                     do e' <- conv_Exp r;
                        args' <- (case ts of [] => SOME []
                                          | args::_ => conv_ArgList args);
                        SOME $ add_locs_annot nd $ TailCall e' args'
                     od)
            | NONE =>
                (case conv_Handle r of
                   NONE =>
                     do e' <- conv_Exp r;
                        args' <- (case ts of [] => SOME []
                                          | args::_ => conv_ArgList args);
                        SOME $ add_locs_annot nd $ StandAloneCall NONE e' args'
                     od
                 | SOME h =>
                     (case ts of
                      | [] => NONE
                      | r::ts =>
                          do e' <- conv_Exp r;
                             args' <- (case ts of [] => SOME []
                                               | args::_ => conv_ArgList args);
                             SOME $ add_locs_annot nd $ StandAloneCall h e' args'
                          od))
            | SOME(SOME r') =>
                (case ts of
                   [] => NONE
                 | e::xs =>
                     do e' <- conv_Exp e;
                        args' <- (case xs of [] => SOME []
                                          | args::_ => conv_ArgList args);
                        SOME $ add_locs_annot nd $ panLang$Call (SOME r') e' args'
                     od))
     else if isNT nodeNT ProgNT then
       case args of
         t::ts => if ts ≠ []
                  then FOLDR (λt' p. lift2 Seq t' p) (conv_Prog (LAST ts))
                             (MAP conv_Prog (t::(butlast ts)))
                  else conv_Prog t
       | _ => NONE
     else OPTION_MAP (add_locs_annot nd) (conv_NonRecStmt (Nd nodeNT args))) ∧
  conv_Prog leaf = OPTION_MAP (add_locs_annot leaf) (conv_NonRecStmt leaf)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INR x => sum_CASE x ptree_size ptree_size
                           | INL x => ptree_size x)’
  >> rw[] >> gvs[argsNT_def]
  >- (
    drule MEM_list_size>>
    disch_then (qspec_then `ptree_size` assume_tac)>>
    ‘list_size ptree_size (butlast ts) ≤ list_size ptree_size ts’
      by irule list_size_butlast>>
    gs[])
  >- (
    ‘ptree_size (LAST ts) ≤ list_size ptree_size ts’
      by (irule list_size_MEM>>
          gs[LAST_EL, MEM_EL]>>
          qexists_tac ‘PRE (LENGTH ts)’>>gs[]>>
          Cases_on ‘ts’>>gs[])>>
    gs[])>>
  Cases_on ‘tree’ >> gvs[argsNT_def]
End

Definition conv_expos_def:
  conv_expos tree =
    case destTOK ' (destLf tree) of
      SOME (KeywordT ExportK) => SOME T
    | SOME (StaticT) => SOME F
    | _ => NONE
End

Definition conv_Fun_def:
  conv_Fun tree =
  case argsNT tree FunNT of
  | SOME [e;n;ps;c] =>
      (case (argsNT ps ParamListNT) of
         SOME args =>
           (do ps'  <- conv_params args;
               body <- conv_Prog c;
               n'   <- conv_ident n;
               e'   <- conv_expos e;
               SOME (n', e', ps', body)
            od)
       | _ => NONE)
  | _ => NONE
End

Definition conv_FunList_def:
  conv_FunList tree =
   case argsNT tree FunListNT of
     SOME [] => SOME []
   | SOME [f; tree'] =>
       (case dest_annot_tok f of
         NONE =>
           (case conv_Fun f of
            | SOME f =>
                (case conv_FunList tree' of
                  NONE => NONE
                 | SOME fs => SOME(f::fs))
            | NONE => NONE)
       | SOME _ => conv_FunList tree')
   | _ => NONE
Termination
  wf_rel_tac ‘measure $ ptree_size’ >>
  rw[] >>
  gvs[oneline argsNT_def,AllCaseEqs(),parsetree_size_def]
End

Definition parse_to_ast_def:
  parse_to_ast s =
    case parse_statement (pancake_lex s) of
      SOME e => conv_Prog e
    | _ => NONE
End

Definition parse_funs_to_ast_def:
  parse_funs_to_ast s =
    (case safe_pancake_lex s of
     | INL toks =>
        (case parse toks of
           | INL e =>
             (case conv_FunList e of
              | SOME funs => INL funs
              | NONE => INR [(«Parse tree conversion failed»,unknown_loc)])
           | INR err => INR err)
     | INR err => INR err)
End

val _ = export_theory();
