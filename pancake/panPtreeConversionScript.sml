(**
 * Theory for translating the Pancake parse tree into the Pancake AST.
 *
 * We take some inspiration from the existing conversion theory
 * for CakeML.
 *
 * Created by Craig McLaughlin on 6/5/2022.
 *)
open HolKernel Parse boolLib bossLib stringLib numLib intLib;

open arithmeticTheory;
open preamble pegTheory pegexecTheory;
open grammarTheory;
open panLexerTheory panLangTheory panPEGTheory
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

Definition conv_var_def:
  conv_var t = lift Var (conv_ident t)
End

(** Collection of binop expression nodes, n >= 2 *)
Definition binaryExps_def:
  binaryExps = [ExpNT; EXorNT; EAndNT; EAddNT]
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
   if tokcheck leaf EqT then SOME Equal
   else if tokcheck leaf NeqT then SOME NotEqual
   else if tokcheck leaf LessT then SOME Less
   else if tokcheck leaf GeqT then SOME NotLess
   else NONE
End

(** A single tree is smaller than the forest. *)
Theorem mem_ptree_thm:
  ∀a l. MEM a l ⇒ ptree_size a < ptree1_size l
Proof
  Induct_on ‘l’ >> rw[] >> simp[parsetree_size_def]
  >> first_x_assum drule >> simp[]
QED

Definition conv_Shape_def:
  (conv_Shape tree =
    case argsNT tree ShapeNT of
      SOME [t] => if tokcheck t panLexer$StarT then SOME One
                  else conv_ShapeComb t
    | _ => NONE) ∧
  (conv_ShapeComb tree =
     case argsNT tree ShapeCombNT of
       SOME ts => lift Comb $ OPT_MMAP conv_Shape ts
     | _ => NONE)
Termination
  WF_REL_TAC ‘measure (λx. sum_CASE x ptree_size ptree_size)’ >> rw[]
  >> Cases_on ‘tree’
  >> gvs[argsNT_def,parsetree_size_def]
  >> drule_then assume_tac mem_ptree_thm >> gvs[]
End

Definition conv_Shift_def:
  conv_Shift [] e = SOME e ∧
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
        [t] => conv_const t ++ conv_var t ++ conv_Exp t
      | t::ts => FOLDR (λt. lift2 Field (conv_nat t)) (conv_Exp t) ts
    else if isNT nodeNT LabelNT then
      case args of
        [t] => lift Label (conv_ident t)
      | _ => NONE
    else if isNT nodeNT StructNT then
      case args of
        [ts] => do es <- conv_ArgList ts;
                   SOME $ Struct es
                od
      | _ => NONE
    else if isNT nodeNT LoadByteNT then
      case args of
        [t] => lift LoadByte (conv_Exp t)
      | _ => NONE
    else if isNT nodeNT LoadNT then
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
                           op' <- conv_cmp op;
                           e2' <- conv_Exp e2;
                           SOME $ Cmp op' e1' e2'
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
    else NONE) ∧
  (conv_Exp leaf = if tokcheck leaf (kw BaseK) then SOME BaseAddr
                  else NONE) ∧
  conv_binaryExps [] e = SOME e ∧
  (conv_binaryExps (t1::t2::ts) res =
    do op <- conv_binop t1;
       e <- conv_Exp t2;
       case res of
         Op bop es => if bop ≠ op ∨ isSubOp res then
                        conv_binaryExps ts (Op bop [res; e])
                      else conv_binaryExps ts (Op bop (APPEND es [e]))
       | e' => conv_binaryExps ts (Op op [e'; e])
    od) ∧
  conv_binaryExps _ _ = NONE (* Impossible: ruled out by grammar. *)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INR (INR x) => ptree1_size (FST x)
                           | INR (INL x) => ptree_size x
                           | INL x => ptree_size x)’ >> rw[]
  >> Cases_on ‘tree’
  >> gvs[argsNT_def,parsetree_size_def]
  >> drule_then assume_tac mem_ptree_thm >> gvs[]
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
    else if isNT nodeNT ExtCallNT then
      case args of
        [name; ptr; clen; array; alen] =>
          do name' <- conv_ident name;
             ptr' <- conv_ident ptr;
             clen' <- conv_ident clen;
             array' <- conv_ident array;
             alen' <- conv_ident alen;
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
    else NONE
End

Definition conv_Prog_def:
  (conv_Handle tree =
    case argsNT tree HandleNT of
      SOME [eid; id; p] => do excp <- conv_ident eid;
                              var <- conv_ident id;
                              prog <- conv_Prog p;
                              SOME $ Handle excp var prog
                           od
    | _ => NONE) ∧

  (conv_Ret tree =
    case argsNT tree RetNT of
      SOME [id; t] => do var <- conv_ident id;
                         hdr' <- conv_Handle t;
                         SOME $ Ret var (SOME hdr')
                      od
    | SOME [id] => lift2 Ret (conv_ident id) (SOME NONE)
    | _ => NONE) ∧

  (conv_Prog (Nd nodeNT args) =
     if isNT nodeNT DecNT then
       case args of
         [id; e; p] => do v <- conv_ident id;
                          e' <- conv_Exp e;
                          p' <- conv_Prog p;
                          SOME (Dec v e' p')
                       od
       | _ => NONE
     else if isNT nodeNT IfNT then
       case args of
         [e; p] => do e' <- conv_Exp e;
                      p' <- conv_Prog p;
                      SOME (If e' p' Skip)
                   od
       | [e; p1; p2] => do e' <- conv_Exp e;
                           p1' <- conv_Prog p1;
                           p2' <- conv_Prog p2;
                           SOME (If e' p1' p2')
                        od
       | _ => NONE
     else if isNT nodeNT WhileNT then
       case args of
         [e; p] => do e' <- conv_Exp e;
                      p' <- conv_Prog p;
                      SOME (While e' p')
                   od
       | _ => NONE
     else if isNT nodeNT CallNT then
       case args of
         [r; e; args] => do r' <- conv_Ret r;
                            e' <- conv_Exp e;
                            args' <- conv_ArgList args ++ SOME [];
                            SOME $ Call r' e' args'
                         od
       | e::args => do e' <- conv_Exp e;
                       args' <- conv_ArgList (HD args) ++ SOME [];
                       SOME $ TailCall e' args'
                    od
       | _ => NONE
     else if isNT nodeNT ProgNT then
       case args of
         t::ts => FOLDR (λt p. lift2 Seq p (conv_Prog t))
                        (conv_Prog t) ts
       | _ => NONE
     else conv_NonRecStmt (Nd nodeNT args)) ∧
  conv_Prog leaf = conv_NonRecStmt leaf
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INR x => sum_CASE x ptree_size ptree_size
                           | INL x => ptree_size x)’
  >> rw[] >> Cases_on ‘tree’ >> gvs[argsNT_def,parsetree_size_def]
End

Definition parse_to_ast_def:
  parse_to_ast s =
    case parse (pancake_lex s) of
      SOME e => conv_Prog e
    | _ => NONE
End

(** Small test modelled after the minimal working example. *)
val src = ‘var a = @base {
 var b = 8 {
  var c = @base + 16 {
   var d = 1 {
     #out_morefun(a b c d);
     str @base, ic;
     return 0;
 }}}}’;

fun parse_pancake q =
  let
    val code = quote_to_strings q |> concat |> fromMLstring
  in
    EVAL “parse_to_ast ^code”
  end

val _ = export_theory();
