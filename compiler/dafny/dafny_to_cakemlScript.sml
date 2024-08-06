(*
  Definitions to convert Dafny's AST into CakeML's AST.
*)

open preamble
open result_monadTheory
open astTheory semanticPrimitivesTheory (* CakeML AST *)
open dafny_astTheory

open alistTheory
open mlintTheory

val _ = new_theory "dafny_to_cakeml";

(* TODO Check if we can reduce the number of generated cases *)

Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload None = “Con (SOME (Short "None")) []”
Overload Some = “λx. Con (SOME (Short "Some")) [x]”
Overload Unit = “Con NONE []”

(* Converts a HOL list of CakeML expressions into a CakeML list. *)
Definition cml_list_def:
  (cml_list [] = Con (SOME (Short "[]")) []) ∧
  (cml_list (x::rest) =
   Con (SOME (Short "::")) [x; cml_list rest])
End

Definition cml_fapp_aux_def:
  cml_fapp_aux fun_name [] = App Opapp [fun_name; Unit] ∧
  cml_fapp_aux fun_name (e::rest) =
  if rest = [] then (App Opapp [fun_name; e])
  else
    let inner_app = cml_fapp_aux fun_name rest in
      (App Opapp [inner_app; e])
End

Definition cml_fapp_def:
  cml_fapp fun_name args = cml_fapp_aux fun_name (REVERSE args)
End

(* Definitions to deal with (Early)Return in Dafny *)

(* TODO Since the generated program does not necessarily need to type-check,
 * it may be possible to use something like exception Result of 'a instead of
 * using a reference for the result *)
Definition result_name_def:
  result_name = "res_CML_ref"
End

Definition return_exn_name_def:
  return_exn_name = "Return_CML_con"
End

Definition return_dexn_def:
  return_dexn = Dexn unknown_loc return_exn_name []
End

Definition raise_return_def:
  raise_return = Raise (Con (SOME (Short return_exn_name)) [])
End

(* Definitions to deal with unlabeled break statements *)
Definition break_exn_name_def:
  break_exn_name = "Break_CML_con"
End

Definition break_dexn_def:
  break_dexn = Dexn unknown_loc break_exn_name []
End

Definition raise_break_def:
  raise_break = Raise (Con (SOME (Short break_exn_name)) [])
End

Definition add_break_handle_def:
  add_break_handle e = Handle e [Pcon (SOME (Short break_exn_name)) [], Unit]
End

(* Definitions to deal with labeled break statements *)

Definition labeled_break_exn_name_def:
  labeled_break_exn_name = "LabeledBreak_CML_con"
End

Definition labeled_break_dexn_def:
  labeled_break_dexn = Dexn unknown_loc labeled_break_exn_name
                            [Atapp [] (Short "string")]
End

Definition raise_labeled_break_def:
  raise_labeled_break lbl = Raise (Con (SOME (Short labeled_break_exn_name))
                                       [Lit (StrLit lbl)])
End

Definition add_labeled_break_handle_def:
  add_labeled_break_handle cur_lbl e =
  Handle e [Pcon (SOME (Short labeled_break_exn_name)) [Pvar "lbl"],
            (If (App Equality [Var (Short "lbl"); Lit (StrLit cur_lbl)])
                (Unit)
                (Raise (Con (SOME (Short labeled_break_exn_name))
                            [Var (Short "lbl")])))]
End

(* Definitions for Euclidean modulo and division
 * Based on HOL's definitions at https://hol-theorem-prover.org/trindemossen-1-helpdocs/help/src-sml/htmlsigs/integerTheory.html#EDIV_DEF-val *)
(* TODO Verify that this is correct according to the semantics of CakeML and
 * Dafny *)
(* TODO Place these definition into separate modules *)
Definition cml_abs_name_def:
  cml_abs_name = "abs_CML_fun"
End

(* fun cml_abs i = if i < 0 then ~i else i; *)
Definition cml_abs_def_def:
  cml_abs_def =
  Dletrec unknown_loc
          [(cml_abs_name,"i",
            (If
             (App (Opb Lt) [Var (Short "i"); Lit (IntLit 0)])
             (cml_fapp (Var (Short "~")) [Var (Short "i")])
             ((Var (Short "i")))))]
End

Definition cml_emod_name_def:
  cml_emod_name = "emod_CML_fun"
End

(* fun emod i j = i % (cml_abs j); *)
Definition cml_emod_def_def:
  cml_emod_def =
  Dletrec unknown_loc
          [(cml_emod_name, "i",
            (Fun "j" (App (Opn Modulo) [Var (Short "i");
                                        cml_fapp (Var (Short cml_abs_name)) [Var (Short "j")]])))]
End

Definition cml_ediv_name_def:
  cml_ediv_name = "ediv_CML_fun"
End

(* fun ediv i j = if 0 < j then i div j else ~(i div ~j); *)
Definition cml_ediv_def_def:
  cml_ediv_def =
  Dletrec unknown_loc
          [(cml_ediv_name, "i",
            (Fun "j"
                 (If
                  (App (Opb Lt) [Lit (IntLit 0); Var (Short "j")])
                  (App (Opn Divide) [Var (Short "i"); Var (Short "j")])
                  (cml_fapp (Var (Short "~"))
                            [App (Opn Divide)
                                 [Var (Short "i"); (cml_fapp (Var (Short "~"))
                                                             [Var (Short "j")])]]))))]
End

Definition cml_while_name_def:
  cml_while_name (lvl: int) = "CML_while_" ++ (explode (toString lvl))
End

(* TODO move this to dafny_ast? *)
Definition is_DeclareVar_def:
  is_DeclareVar s =
  case s of
  | DeclareVar _ _ _ => T
  | _ => F
End

(* TODO? Merge is_<Con> and dest_<Con> into one def returning an option *)
Definition is_Eq_def:
  is_Eq bop =
  case bop of
  | Eq _ _ => T
  | _ => F
End

Definition is_Seq_def:
  is_Seq typ =
  case typ of
  | Seq _ => T
  | _ => F
End

Definition dest_Seq_def:
  dest_Seq (Seq t) = return t ∧
  dest_Seq _ = fail "dest_Seq: Not a Seq"
End

(* TODO? Move to dafny_ast *)
Definition dest_Name_def:
  dest_Name (Name s) = s
End

Definition dest_Ident_def:
  dest_Ident (Ident n) = n
End

(* TODO move this to dafny_ast? *)
Definition dest_DeclareVar_def:
  dest_DeclareVar s =
  case s of
  | DeclareVar n t e_opt => return (n, t, e_opt)
  | _ => fail "dest_DeclareVar: Not a DeclareVar"
End

(* TODO move this to result_monad? *)
Definition dest_SOME_def:
  dest_SOME (SOME x) = return x ∧
  dest_SOME NONE = fail "dest_SOME: Not a SOME"
End

(* TODO? Move to dafny_ast *)
Definition dest_Method_def:
  dest_Method (Method isStatic hasBody overridingPath nam
                      typeParams params body outTypes outVars) =
  (isStatic, hasBody, overridingPath, nam, typeParams, params, body, outTypes, outVars)
End

Definition call_type_name_def:
  call_type_name (Name n) = Name (n ++ "_call_CML_name")
End

Definition from_string_def:
  from_string s =
  case (fromString (implode s)) of
  | SOME i =>
      return i
  | NONE =>
      fail ("Could not convert into int: " ++ s)
End

Definition cml_ref_ass_def:
  cml_ref_ass lhs rhs = (App Opassign [lhs; rhs])
End

Definition cml_ref_def:
  cml_ref n val_e in_e = (Let (SOME n) ((App Opref [val_e])) in_e)
End

(* TODO Find better way to generate internal names *)

Definition varN_from_formal_def:
  varN_from_formal (Formal n _ attrs) =
  if attrs ≠ [] then
    fail "param_from_formals: Attributes currently unsupported"
  else
    return (dest_Name n)
End

Definition internal_varN_from_formal_def:
  internal_varN_from_formal fo =
  do
    n <- varN_from_formal fo;
    return (n ++ "_CML_param")
  od
End

Definition internal_varN_from_ident_def:
  internal_varN_from_ident (Ident (Name n)) = (n ++ "_CML_out_ref")
End

Definition arb_value_def:
  arb_value (t: dafny_ast$type) =
  (case t of
   | Primitive Int => return (Lit (IntLit 0))
   | Primitive String => return (Lit (StrLit ""))
   | Primitive Bool => return False
   | Seq _ => return (cml_list [])
   | _ => fail "arb_value_def: Unsupported type")
End

Definition from_name_def:
  from_name n = Var (Short (dest_Name n))
End

Definition from_ident_def:
  from_ident (Ident n) = from_name n
End

(* It appears that function and methods in Dafny are both represented by the
 * same datatype, even though they are slightly different *)
Definition method_is_function_def:
  method_is_function (Method isStatic hasBody overridingPath nam
                             typeParams params body outTypes outVars) =
  (* Function has one outType and no outVars *)
  if LENGTH outTypes ≠ 1 ∨ outVars ≠ NONE then
    return F
  else if ¬isStatic then
    fail ("method_is_function: Did not expect function " ++ (dest_Name nam) ++
          " to be static")
  else if ¬hasBody then
    fail ("method_is_function: Function " ++ (dest_Name nam) ++
          " did not have a body, even though it must")
  else if overridingPath ≠ NONE then
    fail ("method_is_function: Did not expect function " ++ (dest_Name nam) ++
          " to have an overriding path")
  else if typeParams ≠ [] then
    fail ("method_is_function: Type parameters are currently unsupported (in "
          ++ (dest_Name nam) ++ ")")
  else
    return T
End

Definition method_is_method_def:
  method_is_method (Method isStatic hasBody overridingPath nam
                           typeParams params body outTypes outVars) =
  case outVars of
  | SOME outVars_list =>
      if LENGTH outTypes ≠ LENGTH outVars_list then
        fail ("method_is_method: Function " ++ (dest_Name nam) ++
              " did not have the same number of outTypes and outVars, even" ++
              " though it must")
      else if ¬isStatic then
        fail ("method_is_method: non-static methods are currently " ++
              "unsupported (in " ++ (dest_Name nam) ++ ")")
      else if ¬hasBody then
        fail ("method_is_method: Method " ++ (dest_Name nam) ++
              " did not have a body, even though it must")
      else if overridingPath ≠ NONE then
        fail ("method_is_method: Overriding path for methods are currently " ++
              "unsupported (in " ++ (dest_Name nam) ++ ")")
      else if typeParams ≠ [] then
        fail ("method_is_method: Type parameters are currently unsupported (in "
              ++ (dest_Name nam) ++ ")")
      else
        return T
  | NONE => return F
End

Definition from_literal_def:
  from_literal (l: dafny_ast$literal) =
   case l of
   | BoolLiteral T =>
       return True
   | BoolLiteral F =>
       return False
   | IntLiteral s (Primitive Int) =>
       do
         i <- from_string s;
         return (Lit (IntLit i))
       od
   | IntLiteral _ _ =>
       fail "IntLiteral _ _: Unclear how to handle"
   (* TODO Look into Rat module in basis *)
   | DecLiteral s1 s2 typ =>
       fail "DecLiteral s1 s2 typ: TODO"
   (* TODO String/Char support incomplete or incorrect - see
      to_dafny_astScript for more details *)
   | StringLiteral s verbatim =>
       return (Lit (StrLit s))
   | CharLiteral ch =>
       return (Lit (Char ch))
   | CharLiteralUTF16 n =>
       fail "CharLiteralUTF16 n: Unsupported"
   (* Encode a nullable type as ((a' ref) option) *)
   | Null typ =>
       return None
End

Definition call_type_env_def:
  call_type_env [] = return []  ∧
  call_type_env ((ClassItem_Method m)::rest) =
  do
    is_function <- method_is_function m;
    is_method <- method_is_method m;
    if is_function then
      do
        (_, _, _, nam, _, _, _, outTypes, _) <<- dest_Method m;
        type_env <- (call_type_env rest);
        return ((call_type_name nam, HD outTypes)::type_env)
      od
    else if is_method then
      (* call_type_name is only used in Expression_Call, and since methods
       * cannot be called in expressions, we do not add them to the (type)
       * environment *)
      call_type_env rest
    else
      fail "call_type_env: ClassItem_Method m was neither method nor function."
  od
End

Definition dafny_type_of_def:
  dafny_type_of (env: ((name, type) alist)) (e: dafny_ast$expression) =
  case e of
  | Literal (IntLiteral _ t) => return t
  | Literal (StringLiteral _ _) => return (Primitive String)
  | Expression_Ident n =>
       (case ALOOKUP env n of
       | SOME t => return t
       | NONE => fail ("dafny_type_of: Unknown Name " ++ (dest_Name n)))
  | SeqValue _ t =>
      return (Seq t)
  | SeqUpdate se idx v =>
      do
        se_t <- dafny_type_of env se;
        idx_t <- dafny_type_of env idx;
        v_t <- dafny_type_of env v;
        if se_t ≠ Seq v_t then
          fail "dafny_type_of (SeqUpdate): Unexpectedly, se_t <> Seq v_t"
        else if idx_t ≠ Primitive Int then
          fail "dafny_type_of (SeqUpdate): Unexpectedly, idx_t wasn't an int"
        else
          return se_t
      od
  | Ite cnd thn els =>
      do
        thn_t <- dafny_type_of env thn;
        els_t <- dafny_type_of env els;
        if (thn_t ≠ els_t) then
          fail ("dafny_type_of (Ite): Unexpectedly, branches have " ++
                "different types")
        else
          return thn_t
      od
  | UnOp Not e =>
      do
        e_t <- dafny_type_of env e;
        if e_t = (Primitive Bool) then
          return (Primitive Bool)
        else
          fail "dafny_type_of (UnOp Not): Unsupported type for e"
      od
  | UnOp BitwiseNot _ =>
      fail "dafny_type_of (UnOp BitwiseNot): Unsupported"
  | UnOp Cardinality e' =>
      do
        e'_t <- dafny_type_of env e';
        if is_Seq e'_t then
          return (Primitive Int)
        else
          fail "dafny_type_of (UnOp Cardinality): Unsupported type"
      od
  | BinOp bop e1 e2 =>
      (* TODO? Figure out why using | BinOp Lt _ _ and
       * | BinOp (Eq _ _) _ _ results in the | BinOp bop e1 e2 case to be
       * repeated over and over again *)
      (* TODO Add sanity checks as done below *)
      if (bop = Lt ∨ (is_Eq bop)) then return (Primitive Bool)
      else
        do
          e1_t <- dafny_type_of env e1;
          e2_t <- dafny_type_of env e2;
          if (bop = EuclidianDiv ∧ e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (Primitive Int)
          else if (bop = EuclidianMod ∧ e1_t = (Primitive Int) ∧
                   e1_t = e2_t) then
            return (Primitive Int)
          else if (bop = Plus ∧ e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (Primitive Int)
          else if (bop = Minus ∧ e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (Primitive Int)
          else if (bop = Times ∧ e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (Primitive Int)
          else if (bop = Concat ∧ e1_t = (Primitive String) ∧
                   e1_t = e2_t) then
            return (Primitive String)
          else if (bop = Concat ∧ is_Seq e1_t ∧ e1_t = e2_t) then
            return e1_t
          else if (bop = In ∧ is_Seq e2_t) then
            do
              seq_t <- dest_Seq e2_t;
              if e1_t ≠ seq_t then
                fail "dafny_type_of (BinOp In): Types did not match"
              else
                return (Primitive Bool)
            od
          else if (bop = SeqPrefix ∧ is_Seq e1_t ∧ is_Seq e2_t) then
            do
              seq1_t <- dest_Seq e1_t;
              seq2_t <- dest_Seq e2_t;
              if seq1_t ≠ seq2_t then
                fail "dafny_type_of (BinOp SeqPrefix): Types did not match"
              else
                return (Primitive Bool)
            od
          else if (bop = SeqProperPrefix ∧ is_Seq e1_t ∧ is_Seq e2_t) then
            do
              seq1_t <- dest_Seq e1_t;
              seq2_t <- dest_Seq e2_t;
              if seq1_t ≠ seq2_t then
                fail ("dafny_type_of (BinOp SeqProperPrefix): Types did " ++
                      "not match")
              else
                return (Primitive Bool)
            od
          else
            fail "dafny_type_of (BinOp): Unsupported bop/types"
        od
  | Index e' cok idxs =>
      do
        e'_t <- dafny_type_of env e';
        if cok = CollKind_Seq then
          if idxs = [] then
            fail "dafny_type_of (Index): Unexpectedly idxs was empty"
          else if LENGTH idxs > 1 then
            fail "dafny_type_of (Index): multi-dimensional indexing unsupported"
          else
            dest_Seq e'_t
        else
          fail "dafny_type_of (Index): Unsupported kind of collection"
      od
  | Expression_Call on (CallName nam onType _) _ _ =>
      if on ≠ (Companion [Ident (Name "_module");
                          Ident (Name "__default")]) then
        fail "dafny_type_of: (Call) Unsupported on expression"
      else if onType ≠ NONE then
        fail "dafny_type_of: (Call) Unsupported onType"
      else
        let ct_name = (call_type_name nam) in
        (case ALOOKUP env ct_name of
         | SOME t => return t
         | NONE => fail ("dafny_type_of: Unknown Name " ++
                         dest_Name ct_name))
  | _ => fail "dafny_type_of: Unsupported expression"
End

Definition from_assignLhs_def:
  from_assignLhs (lhs: dafny_ast$assignLhs) =
  case lhs of
  | AssignLhs_Ident id => return (from_ident id)
  | _ => fail "from_assignLhs: Unsupported"
End

Definition from_callName_def:
  (from_callName (CallName nam onType sig) =
   if onType ≠ NONE then
     fail "from_callName: non-empty onType currently unsupported"
   else
     return (from_name nam)) ∧
  (from_callName _ = fail ("from_callName: " ++
                           "Passed callName currently unsupported"))
End

(* TODO Clean up from_expression/dafny_type_of: Some code parts may be duplicated,
 some checks may be unnecessary (depending on the assumptions we make about/get from
 the Dafny AST *)
Definition from_expression_def:
  (from_expression (env: ((name, type) alist))
                   (e: dafny_ast$expression) : (ast$exp result) =
   case e of
   | Literal l =>
       from_literal l
   | Expression_Ident n =>
       return (App Opderef [Var (Short (dest_Name n))])
   | SeqValue els t =>
       do
         cml_els <- map_from_expression env els;
         return (cml_list cml_els)
       od
   | SeqUpdate se idx v =>
       do
         se_t <- dafny_type_of env se;
         idx_t <- dafny_type_of env idx;
         v_t <- dafny_type_of env v;
         if se_t ≠ Seq v_t then
           fail "dafny_type_of (SeqUpdate): Unexpectedly, se_t <> Seq v_t"
         else if idx_t ≠ Primitive Int then
           fail "dafny_type_of (SeqUpdate): Unexpectedly, idx_t wasn't an int"
         else
           do
             cml_se <- from_expression env se;
             cml_idx <- from_expression env idx;
             cml_v <- from_expression env v;
             return (cml_fapp (Var (Long "List" (Short "update")))
                              [cml_v; cml_idx; cml_se])
           od
       od
   | Ite cnd thn els =>
       do
         cml_cnd <- from_expression env cnd;
         cml_thn <- from_expression env thn;
         cml_els <- from_expression env els;
         return (If cml_cnd cml_thn cml_els)
       od
   | UnOp uop e =>
       from_unaryOp env uop e
   | BinOp bop e1 e2 =>
       from_binOp env bop e1 e2
   | Index ce cok idxs =>
       if cok = CollKind_Seq then
         if idxs = [] then
           fail ("from_expression: Unexpectedly received an empty " ++
                 "list of indices")
         else if LENGTH idxs > 1 then
           fail "from_expression: multi-dimensional indexing unsupported"
         else
           do
             cml_ce <- from_expression env ce;
             idx <- from_expression env (EL 0 idxs);
             return (cml_fapp (Var (Long "List" (Short "nth"))) [cml_ce; idx])
           od
       else
         fail "from_expression: Unsupported kind of collection"
   | Expression_Call on call_nam typeArgs args =>
       do
         if on ≠ (Companion [Ident (Name "_module");
                             Ident (Name "__default")]) then
           fail "from_expression: (Call) Unsupported on expression"
         else if typeArgs ≠ [] then
           fail "from_expression: (Call) type arguments currently unsupported"
         else
           do
             fun_name <- from_callName call_nam;
             cml_args <- result_mmap (from_expression env) args;
             return (cml_fapp fun_name cml_args)
           od
       od
   | InitializationValue t =>
       arb_value t
   | _ => fail "from_expression: Unsupported expression") ∧
  (map_from_expression env es =
   case es of
   | [] => return []
   | (e::rest) =>
       do
         se' <- from_expression env e;
         rest' <- map_from_expression env rest;
         return (se'::rest')
       od) ∧
  (from_unaryOp (env: ((name, type) alist)) (uop: dafny_ast$unaryOp)
                (e: dafny_ast$expression) =
   do
     e_t <- dafny_type_of env e;
     cml_e <- from_expression env e;
     if uop = Not then
       return (cml_fapp (Var (Short "not")) [cml_e])
     else if uop = BitwiseNot then
       fail "from_unaryOp: BitwiseNot unsupported"
     else if uop = Cardinality then
       if is_Seq e_t then
         return (cml_fapp (Var (Long "List" (Short "length"))) [cml_e])
       else
         fail "from_unaryOp (Cardinality): Unsupported type"
     else
       fail "from_unaryOp: Unexpected unary operation"
   od
  ) ∧
  (from_binOp (env: ((name, type) alist)) (bop: dafny_ast$binOp)
              (e1: dafny_ast$expression) (e2: dafny_ast$expression) =
   do
     e1_t <- dafny_type_of env e1;
     e2_t <- dafny_type_of env e2;
     cml_e1 <- from_expression env e1;
     cml_e2 <- from_expression env e2;
     (case bop of
      | Eq referential nullabl =>
          if referential then
            fail "from_binOp (Eq): referential unsupported"
          else if ~nullabl then
            (* TODO Ask Dafny team what the exact meaning of nullable is *)
            fail "from_binOp (Eq): non-nullable unexpected"
          else if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            (* TODO Unsure whether this is legal/does what I think it does *)
            return (App Equality [cml_e1; cml_e2])
          else
            fail "from_binOp (Eq): Unsupported type"
      | EuclidianDiv =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Short cml_ediv_name)) [cml_e1; cml_e2])
          else
            fail "from_binOp (EuclideanDiv): Unsupported types"
      | EuclidianMod =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Short cml_emod_name)) [cml_e1; cml_e2])
          else
            fail "from_binOp (EuclideanMod): Unexpected types"
      | Lt =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (App (Opb Lt) [cml_e1; cml_e2])
          else
            fail "from_binOp (Lt): Unsupported types"
      | Plus =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (App (Opn Plus) [cml_e1; cml_e2])
          else
            fail "from_binOp (Plus): Unsupported types"
      | Minus =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (App (Opn Minus) [cml_e1; cml_e2])
          else
            fail "from_binOp (Minus): Unsupported types"
      | Times =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (App (Opn Times) [cml_e1; cml_e2])
          else
            fail "from_binOp (Times): Unsupported types"
      | In =>
          if is_Seq e2_t then
            do
              seq_t <- dest_Seq e2_t;
              if e1_t ≠ seq_t then
                fail "from_binOp (In): Types did not match"
              else
                return (cml_fapp (Var (Long "List" (Short "member")))
                                 [cml_e1; cml_e2])
            od
          else
            fail "from_binOp (In): Unsupported types"
      | SeqProperPrefix =>
          if is_Seq e1_t ∧ is_Seq e2_t then
            do
              seq1_t <- dest_Seq e1_t;
              seq2_t <- dest_Seq e2_t;
              if seq1_t ≠ seq2_t then
                fail ("from_binOp (SeqProperPrefix): Unexpectedly types " ++
                      "did not match")
              else
                do
                  not_eq_check <<- (cml_fapp (Var (Short "not"))
                                             [App Equality [cml_e1; cml_e2]]);
                  is_prefix_check <<- (cml_fapp (Var (Long "List"
                                                           (Short "isPrefix")))
                                                [cml_e1; cml_e2]);
                  return (Log And not_eq_check is_prefix_check)
                od
            od
          else
            fail "from_binOp (SeqPrefix): Unexpected types"
      | SeqPrefix =>
          if is_Seq e1_t ∧ is_Seq e2_t then
            do
              seq1_t <- dest_Seq e1_t;
              seq2_t <- dest_Seq e2_t;
              if seq1_t ≠ seq2_t then
                fail "from_binOp (SeqPrefix): Unexpectedly types did not match"
              else
                return (cml_fapp (Var (Long "List" (Short "isPrefix")))
                                 [cml_e1; cml_e2])
            od
          else
            fail "from_binOp (SeqPrefix): Unexpected types"
      | Concat =>
          if (e1_t = (Primitive String) ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Long "String" (Short "strcat"))) [cml_e1; cml_e2])
          else if (is_Seq e1_t ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Long "List" (Short "@"))) [cml_e1; cml_e2])
          else
            fail "from_binOp (Concat): Unsupported types"
      | _ => fail "from_binOp: Unsupported bop")
  od)
Termination
  cheat
End

(* An independent statement must not depend on statements outside of it *)
(* TODO Fill out cases properly; wildcard means that I did not explicitly
   consider it yet *)
Definition is_indep_stmt_def:
  is_indep_stmt (s: dafny_ast$statement) =
  case s of
  | DeclareVar _ _ _=> F
  | Assign _ _ => T
  | If _ _ _ => T
  | Labeled _ _ => T
  | While _ _ => T
  | Call _ _ _ _ _ => T
  | Return _ => T
  | EarlyReturn => T
  | Break _ => T
  | Print _ => T
  | _ => F
End

(* TODO is_<constructor> calls could maybe be replaced using monad choice *)
(* At the moment we assume that only statements can change env *)
(* lvl = level of the next while loop *)
Definition from_stmts_def:
  (from_stmts (is_function: bool) (env: ((name, type) alist)) (lvl: int) (epilogue)
              ([]: (dafny_ast$statement list)) =
   return (env, Unit)) ∧
  (from_stmts is_function env lvl epilogue [s] =
   (* TODO Can we simplify this by just always using something like stmt1; stmt2?
    * in this case, it would become s; () *)
   if is_indep_stmt s then
     do
       cml_e <- from_indep_stmt is_function env lvl epilogue s;
       return (env, cml_e)
     od
   else
     fail ("from_stmts: " ++
           "Cannot convert single non-self-contained statement")) ∧
  (from_stmts is_function env lvl epilogue (s1::s2::rest) =
   if is_indep_stmt s1 then
     do
       e1 <- from_indep_stmt is_function env lvl epilogue s1;
       (env', e2) <- from_stmts is_function env lvl epilogue (s2::rest);
       return (env', (Let NONE e1 e2))
     od
   else if is_DeclareVar s1 then
     do
       (n, t, e_opt) <- dest_DeclareVar s1;
       n_str <<- dest_Name n;
       (* TODO look into when/why this is NONE *)
       iv_e <- if e_opt = NONE then arb_value t
               else do e <- dest_SOME e_opt; from_expression env e od;
       (env', in_e) <- from_stmts is_function ((n, t)::env) lvl epilogue (s2::rest);
       return (env', cml_ref n_str iv_e in_e)
     od
   else
     fail "from_stmts: Unsupported statement") ∧
  (from_indep_stmt (is_function: bool) (env: ((name, type) alist)) (lvl: int) epilogue
                   (s: dafny_ast$statement) =
   (case s of
    | Assign lhs e =>
        do
          cml_lhs <- from_assignLhs lhs;
          cml_rhs <- from_expression env e;
          return (cml_ref_ass cml_lhs cml_rhs)
        od
    | If cnd thn els =>
        do
          cml_cnd <- from_expression env cnd;
          (_, cml_thn) <- from_stmts is_function env lvl epilogue thn;
          (_, cml_els) <- from_stmts is_function env lvl epilogue els;
          return (If cml_cnd cml_thn cml_els)
        od
    | Labeled lbl body =>
        do
          (_, cml_body) <- from_stmts is_function env lvl epilogue body;
          return (add_labeled_break_handle lbl cml_body)
        od
    | While cnd body =>
        do
          cml_cnd <- from_expression env cnd;
          (_, cml_body) <- from_stmts is_function env (lvl + 1) epilogue body;
          exec_iter <<- (cml_fapp (Var (Short (cml_while_name lvl))) [Unit]);
          cml_while_def <<- (Letrec [((cml_while_name lvl), "",
                                     If (cml_cnd)
                                        (Let NONE cml_body exec_iter) (Unit))]
                                    (add_break_handle exec_iter));
          return cml_while_def
        od
    | Call on call_nam typeArgs args outs =>
        do
          if on ≠ (Companion [Ident (Name "_module");
                              Ident (Name "__default")]) then
            fail "from_indep_stmt: (Call) Unsupported on expression"
          else if typeArgs ≠ [] then
            fail "from_indep_stmt: (Call) type arguments currently unsupported"
          else
            do
              fun_name <- from_callName call_nam;
              cml_param_args <- result_mmap (from_expression env) args;
              cml_out_args <- (case outs of
                               | NONE => return []
                               | SOME outs =>
                                   return (MAP from_ident outs));
              return (cml_fapp fun_name (cml_param_args ++ cml_out_args))
            od
        od
    | Return e =>
        do
          if ¬is_function then
            fail ("from_indep_stmt: Assumption that Return does not occur in " ++
                  "methods was violated")
          else
            from_expression env e
        od
    | EarlyReturn =>
        if is_function then
          fail ("from_indep_stmt: Assumption that EarlyReturn does not occur in " ++
                "functions was violated")
        else
          return epilogue
    (* TODO Check if we can better test this case
     * It seems that only non-deterministic while loops make use of this, while
       other break statements are transformed into labeled ones. *)
    | Break NONE =>
        return raise_break
    | Break (SOME lbl) =>
        return (raise_labeled_break lbl)
    | Print e =>
        do
          cml_e <- from_expression env e;
          (* TODO Check if it makes sense to extract Var (...) into a function
           * in particular look at from_name *)
          return (cml_fapp (Var (Short "print")) [cml_e])
      od
    | _ => fail ("from_indep_stmt_def: Unsupported or " ++
                 "not independent statement")))
Termination
  cheat
End

Definition param_type_env_def:
  param_type_env [] acc = return acc ∧
  param_type_env ((Formal n t attrs)::rest) acc =
  if attrs ≠ [] then
    fail "param_type_env: Attributes unsupported"
  else
    param_type_env rest ((n, t)::acc)
End

Definition env_and_epilogue_from_outs_def:
  (env_and_epilogue_from_outs env epilogue [] [] =
   do
     epilogue <<- epilogue raise_return;
     return (env, epilogue)
   od) ∧
  (env_and_epilogue_from_outs env epilogue (t::rest_t) (v::rest_v) =
   do
     if LENGTH rest_t ≠ LENGTH rest_v then
       fail ("env_and_epilogue_from_outs: Length of outTypes and outVars " ++
             "is different")
     else
       do
         v_nam <<- dest_Ident v;
         v_str <<- dest_Name v_nam;
         env <<- ((v_nam, t)::env);
         out_ref_name <<- internal_varN_from_ident v;
         epilogue <<- (λx. epilogue (Let NONE (cml_ref_ass
                                               (Var (Short out_ref_name))
                                               ((App Opderef
                                                     [Var (Short v_str)])))
                                         x));
         env_and_epilogue_from_outs env epilogue rest_t rest_v
       od
   od)
End

(* Allows us to pass in out references as parameters *)
Definition fun_from_outs_def:
  fun_from_outs preamble [] = preamble ∧
  fun_from_outs preamble (v::rest_v) =
     fun_from_outs (λx. preamble (Fun (internal_varN_from_ident v) x)) rest_v
End

(* Declares additional parameters using Fun x => ... *)
Definition fun_from_params_def:
  (fun_from_params preamble [] = return preamble) ∧
  (fun_from_params preamble (fo::rest) =
   do
     param_name <- internal_varN_from_formal fo;
     preamble <<- (λx. preamble (Fun param_name x));
     fun_from_params preamble rest
   od)
End

(* Declares and initializes references for the parameters that the body will use
 *
 * We do this since within the body the parameter names act as variables, which
 * we encode using references. *)
Definition ref_from_params_def:
  (ref_from_params preamble [] = return preamble) ∧
  (ref_from_params preamble (fo::rest) =
   do
     ref_name <- varN_from_formal fo;
     ref_value_name <- internal_varN_from_formal fo;
     preamble <<- (λx. preamble ((cml_ref ref_name
                                          (Var (Short ref_value_name)) x)));
     ref_from_params preamble rest
   od)
End

Definition gen_param_preamble_epilogue_def:
  gen_param_preamble_epilogue env [] [] [] =
  do
    param <<- "";
    preamble <<- λx. x;
    epilogue <<- Unit;
    return (env, param, preamble, epilogue)
  od ∧
  gen_param_preamble_epilogue env [] (t::rest_t) (v::rest_v) =
  do
    param <<- internal_varN_from_ident v;
    preamble <<- fun_from_outs (λx. x) rest_v;
    (env, epilogue) <- env_and_epilogue_from_outs env (λx. x)
                                                  (t::rest_t) (v::rest_v);
    return (env, param, preamble, epilogue)
  od ∧
  gen_param_preamble_epilogue env (p::rest_p) outTypes outVars =
  do
    param <- internal_varN_from_formal p;
    preamble <- fun_from_params (λx. x) rest_p;
    preamble <<- fun_from_outs preamble outVars;
    preamble <- ref_from_params preamble (p::rest_p);
    env <- param_type_env (p::rest_p) env;
    (env, epilogue) <- env_and_epilogue_from_outs env (λx. x)
                                                  outTypes outVars;
    return (env, param, preamble, epilogue)
  od
End

Definition gen_param_preamble_def:
  gen_param_preamble env params =
  do
    (env, param, preamble, _) <- gen_param_preamble_epilogue env params [] [];
    return (env, param, preamble)
  od
End

Definition process_function_body_def:
  process_function_body env preamble stmts =
   do
     (env, cml_body) <- from_stmts T env 0 Unit stmts;
     return (preamble cml_body)
   od
End

Definition process_method_body_def:
  process_method_body env preamble epilogue body =
  do
    (_, cml_body) <- from_stmts F env 0 epilogue body;
    cml_body <<- (Handle cml_body
                   [Pcon (SOME (Short return_exn_name)) [], Unit]);
    return (preamble cml_body)
  od
End

Definition from_classItem_def:
  from_classItem env (ClassItem_Method m) =
  do
    is_function <- method_is_function m;
    is_method <- method_is_method m;
    if is_function then
      do
        (_, _, _, nam, _, params, body, _, _) <<- dest_Method m;
        fun_name <<- dest_Name nam;
        (env, cml_param, preamble) <- gen_param_preamble env params;
        cml_body <- process_function_body env preamble body;
        return (fun_name, cml_param, cml_body)
      od
    else if is_method then
      do
        (_, _, _, nam, _, params, body, outTypes, outVars) <<- dest_Method m;
        outVars <- dest_SOME outVars;
        fun_name <<- dest_Name nam;
        (env, cml_param,
         preamble, epilogue) <- gen_param_preamble_epilogue env params
                                                            outTypes outVars;
        cml_body <- process_method_body env preamble epilogue body;
        return (fun_name, cml_param, cml_body)
      od
    else
      fail "(Unreachable) from_method: m was neither a function nor method"
  od
End

Definition compile_def:
  (compile ([mod1; mod2]: dafny_ast$module list) =
   (* TODO Don't ignore first module which contains definitions for nat
        and tuples for now *)
   (* TODO Properly handle module (containing main) *)
   (* TODO Once we add support for modules/classes we will probably need
      to rework the way we generated the type environment for Call
      expressions *)
   case mod2 of
   | Module _ _ (SOME [ModuleItem_Class (Class _ _ _ _ _ cis _)]) =>
       do
         env <- call_type_env cis;
         fun_defs <- result_mmap (from_classItem env) cis;
         (* TODO Look at how PureCake detangles Dletrecs
          * Having one big Dletrec probably does not result in a performance
          * penalty unless functions are used in a higher order way *)
         fun_defs <<- [(Dletrec unknown_loc fun_defs)];
         return ([return_dexn; break_dexn; labeled_break_dexn;
                  cml_abs_def; cml_emod_def; cml_ediv_def] ++
                 fun_defs ++
                 [Dlet unknown_loc Pany (cml_fapp (Var (Short "Main")) [Unit])])
       od
   | _ => fail "Unexpected ModuleItem") ∧
  compile _ = fail "compile: Program does not contain exactly two modules"
End

(* Unpacks the AST from M. If the process failed, create a program that prints
   the error. *)
Definition unpack_def:
  unpack m =
  case m of
  | INR d =>
      d
  | INL s =>
      [Dlet unknown_loc Pany
            (cml_fapp (Var (Short "print")) [Lit (StrLit s)])]
End

(* Testing *)
open dafny_sexpTheory
open sexp_to_dafnyTheory
open fromSexpTheory simpleSexpParseTheory
open TextIO
(* val _ = astPP.disable_astPP(); *)
(* val _ = astPP.enable_astPP(); *)

val inStream = TextIO.openIn "./tests/seq_update.sexp";
val fileContent = TextIO.inputAll inStream;
val _ = TextIO.closeIn inStream;
val fileContent_tm = stringSyntax.fromMLstring fileContent;

val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand;
val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand;
val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand;
val cakeml_r = EVAL “(compile ^dafny_r)” |> concl |> rhs |> rand;

val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^cakeml_r)))”
                   |> concl |> rhs |> rand;
val cml_sexp_str_r = stringSyntax.fromHOLstring cml_sexp_r;
val outFile = TextIO.openOut "./tests/test.cml.sexp";
val _ = TextIO.output (outFile, cml_sexp_str_r);
val _ = TextIO.closeOut outFile

val _ = export_theory();
