(*
  Definitions to convert Dafny's AST into CakeML's AST.
*)

open preamble
open cfTacticsLib (* process_topdecs *)
open result_monadTheory
open astTheory semanticPrimitivesTheory (* CakeML AST *)
open dafny_astTheory

open alistTheory
open mlintTheory

val _ = new_theory "dafny_to_cakeml";

(* TODO Instead of breaking strings with ++, use SML style \ in all files *)

(* Defines the Dafny module containing the Dafny runtime *)
Quote dafny_module = process_topdecs:
  structure Dafny =
  struct

  exception Return;
  exception Break;
  exception LabeledBreak string;

  (* Adapted from ABS, ediv, and emod from HOL's integerTheory *)
  fun abs n = if n < 0 then ~n else n;

  fun ediv i j = if 0 < j then i div j else ~(i div ~j);

  fun emod i j = i mod (abs j);


  (* Array functions *)
  fun array_to_list arr = Array.foldr (fn x => fn xs => x :: xs) [] arr;


  (* to_string functions to be used for "Dafny-conform" printing *)
  fun bool_to_string b = if b then "true" else "false";

  fun int_to_string i = Int.int_to_string #"-" i;

  fun escape_char c =
    if c = #"'" then "\\'"
    else if c = #"\"" then "\\\""
    else if c = #"\\" then "\\\\"
    else if c = #"\000" then "\\0"
    else if c = #"\n" then "\\n"
    (* #"\r" leads to "not terminated with nil" exception *)
    else if c = #"\013" then "\\r"
    else if c = #"\t" then "\\t"
    else String.str c;

  fun char_to_string c = String.concat ["'", escape_char c, "'"];

  fun list_to_string f lst =
    String.concat ["[", String.concatWith ", " (List.map f lst), "]"];

  fun char_list_to_string cs = list_to_string char_to_string cs;

  (* f converts the tuple into a list of strings *)
  fun tuple_to_string f tpl =
    String.concat ["(", String.concatWith ", " (f tpl), ")"];

  (* Commented out because we use CakeML char list's instead of strings *)

  (* In Dafny, strings within collections are printed as a list of chars *)
  (* fun string_element_to_string s = *)
  (*   list_to_string char_to_string (String.explode s); *)

  end
End

(* TODO Check if we can reduce the number of generated cases *)
(* TODO Check if it makes sense to extract Var (...) into a function
 * in particular look at from_name *)

Overload True = “Con (SOME (Short "True")) []”
Overload False = “Con (SOME (Short "False")) []”
Overload None = “Con (SOME (Short "None")) []”
Overload Some = “λx. Con (SOME (Short "Some")) [x]”
Overload Unit = “Con NONE []”

Definition int_to_string_def:
  int_to_string (i: int) = explode (toString i)
End

Definition num_to_string_def:
  num_to_string (n: num) = int_to_string (&n)
End

Definition string_to_int_def:
  string_to_int s =
  case (fromString (implode s)) of
  | SOME i =>
      return i
  | NONE =>
      fail ("Could not convert into int: " ++ s)
End

Definition string_to_num_def:
  string_to_num s =
  do
    i <- string_to_int s;
    if i < 0
    then fail "string_to_num: Number was negative"
    else return (Num i)
  od
End

Definition strip_prefix_def:
  strip_prefix prefix str =
  if isPREFIX prefix str
  then SOME (DROP (LENGTH prefix) str)
  else NONE
End

(* Converts a HOL list of CakeML expressions into a CakeML list. *)
Definition cml_list_def:
  (cml_list [] = Con (SOME (Short "[]")) []) ∧
  (cml_list (x::rest) =
   Con (SOME (Short "::")) [x; cml_list rest])
End

(* Converts a HOL string into a CakeML char list *)
Definition string_to_cml_char_list_def:
  string_to_cml_char_list s = cml_list (MAP (λx. (Lit (Char x))) s)
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

Definition cml_id_def:
  cml_id [] = fail "cml_id: Cannot make id from empty list" ∧
  cml_id [n] = return (Short n) ∧
  cml_id (n::rest) = do rest' <- cml_id rest; return (Long n rest') od
End

Definition cml_tuple_def:
  cml_tuple [_] = fail "cml_tuple: Cannot create 1-tuple" ∧
  cml_tuple cml_es = return (Con NONE cml_es)
End

Definition cml_tuple_select_def:
  cml_tuple_select len cml_te (idx: num) =
  let field_vars = GENLIST (λn. Pvar ("t" ++ (num_to_string n))) len in
    Mat cml_te [Pcon NONE field_vars, Var (Short ("t" ++ (num_to_string idx)))]
End

Definition zip_with_def:
  zip_with f [] _ = [] ∧
  zip_with f _ [] = [] ∧
  zip_with f (x::xs) (y::ys) = (f x y)::(zip_with f xs ys)
End

Definition cml_tuple_to_string_list_def:
  cml_tuple_to_string_list fs =
  let field_name = GENLIST (λn. ("t" ++ (num_to_string n))) (LENGTH fs);
      field_pvars = (MAP (λx. Pvar x) field_name);
      field_vars = (MAP (λx. [Var (Short x)]) field_name);
      string_list = cml_list (zip_with cml_fapp fs field_vars);
      tuple_name = "tpl" in
    Fun tuple_name
        (Mat (Var (Short tuple_name))
             [Pcon NONE field_pvars, string_list])
End

Definition raise_return_def:
  raise_return = Raise (Con (SOME (Long "Dafny" (Short "Return"))) [])
End

Definition raise_break_def:
  raise_break = Raise (Con (SOME (Long "Dafny" (Short "Break"))) [])
End

Definition add_break_handle_def:
  add_break_handle e = Handle e [Pcon (SOME (Long "Dafny" (Short "Break"))) [],
                                 Unit]
End

Definition raise_labeled_break_def:
  raise_labeled_break lbl = Raise (Con (SOME (Long "Dafny"
                                                   (Short "LabeledBreak")))
                                       [Lit (StrLit lbl)])
End

Definition add_labeled_break_handle_def:
  add_labeled_break_handle cur_lbl e =
  Handle e [Pcon (SOME (Long "Dafny" (Short "LabeledBreak"))) [Pvar "lbl"],
            (If (App Equality [Var (Short "lbl"); Lit (StrLit cur_lbl)])
                (Unit)
                (Raise (Con (SOME (Long "Dafny" (Short "LabeledBreak")))
                            [Var (Short "lbl")])))]
End

Definition cml_while_name_def:
  cml_while_name (lvl: int) = "CML_while_" ++ (int_to_string lvl)
End

Definition cml_get_arr_def:
  cml_get_arr cml_e = (cml_fapp (Var (Long "Option" (Short "valOf"))) [cml_e])
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

Definition is_moditem_module_def:
  is_moditem_module (ModuleItem_Module _) = T ∧
  is_moditem_module _ = F
End

Definition is_moditem_class_def:
  is_moditem_class (ModuleItem_Class _) = T ∧
  is_moditem_class _ = F
End

Definition is_moditem_trait_def:
  is_moditem_trait (ModuleItem_Trait _) = T ∧
  is_moditem_trait _ = F
End

Definition is_moditem_newtype_def:
  is_moditem_newtype (ModuleItem_Newtype _) = T ∧
  is_moditem_newtype _ = F
End

Definition is_moditem_datatype_def:
  is_moditem_datatype (ModuleItem_Datatype _) = T ∧
  is_moditem_datatype _ = F
End

Definition dest_Array_def:
  dest_Array (Array t dims) = return (t, dims) ∧
  dest_Array _ = fail "dest_Array: Not an Array"
End

Definition dest_Seq_def:
  dest_Seq (Seq t) = return t ∧
  dest_Seq _ = fail "dest_Seq: Not a Seq"
End

Definition dest_Module_def:
  dest_Module (Module nam attrs body) = (nam, attrs, body)
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

(* In Dafny, the string and seq<char> type are synonyms. We replace the
 * former with the latter for consistency. We also replace newtypes by their
 * base type (which may be incorrect) *)
Definition normalize_type_def:
  normalize_type t =
  (case t of
   | Primitive String => Seq (Primitive Char)
   | Path _ _ (ResolvedType_Newtype bt _ _ _) => normalize_type bt
   | Nullable t => Nullable (normalize_type t)
   | Tuple ts => Tuple (map_normalize_type ts)
   | Array elem dims => Array (normalize_type elem) dims
   | Seq t => Seq (normalize_type t)
   | Set t => Set (normalize_type t)
   | Multiset t => Multiset (normalize_type t)
   | Map kt vt => Map (normalize_type kt) (normalize_type vt)
   | SetBuilder t => SetBuilder (normalize_type t)
   | MapBuilder kt vt => MapBuilder (normalize_type kt)
                                    (normalize_type vt)
   | Arrow argsT resT => Arrow (map_normalize_type argsT)
                               (normalize_type resT)
   | _ => t) ∧
  map_normalize_type ts =
  (case ts of
   | [] => []
   | (t::rest) =>
       (normalize_type t)::(map_normalize_type rest))
Termination
  cheat
End

Definition arb_value_def:
  arb_value (t: dafny_ast$type) =
  (case t of
   | Primitive Int => return (Lit (IntLit 0))
   | Primitive Bool => return False
   | Seq _ => return (cml_list [])
   | Tuple ts =>
       do
         arb_elems <- map_arb_value ts;
         cml_tuple arb_elems
       od
   | Array _ _ => return None  (* we essentially initialize with null *)
   | Path _ [] resT => arb_value_resolved_type resT
   | _ => fail "arb_value_def: Unsupported type") ∧
  arb_value_resolved_type resT =
  (case resT of
   | ResolvedType_Newtype baseT rang eras attrs =>
       if baseT ≠ Primitive Int then
         fail "arb_value_resolved_type: Unsupported base type"
       else if rang ≠ NoRange then
         fail "arb_value_resolved_type: Unsupported range"
       else if ¬eras then
         fail "arb_value_resolved_type: non-erased newtypes unsupported"
       else if attrs ≠ [Attribute "axiom" []] then
         fail "arb_value_resolved_type: unsupported attributes"
       else
         arb_value baseT
   | _ => fail "arb_value_resolved_type: Unsupported resolved type") ∧
  map_arb_value ts =
  (case ts of
   | [] => return []
   | t::rest =>
       do
         v <- arb_value t;
         vs <- map_arb_value rest;
         return (v::vs)
       od)
Termination
  cheat
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

(* Adapted from
 * https://github.com/dafny-lang/dafny/blob/bc6b587e264e3c531c4d6698abd421abdff3aea9/Source/DafnyCore/Generic/Util.cs#L341
 *)
Definition unescape_string_def:
  (unescape_string (c1::c2::rest) verbatim =
  if verbatim then
    if c1 = #"\"" ∧ c2 = #"\"" then
      #"\""::(unescape_string rest verbatim)
    else
      c1::(unescape_string (c2::rest) verbatim)
  else if c1 = #"\\" ∧ c2 = #"'" then
    #"'"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\"" then
    #"\""::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"\\" then
    #"\\"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"0" then
    #"\000"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"n" then
    #"\n"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"r" then
    #"\r"::(unescape_string rest verbatim)
  else if c1 = #"\\" ∧ c2 = #"t" then
    #"\t"::(unescape_string rest verbatim)
  else
    c1::(unescape_string (c2::rest) verbatim)) ∧
  (unescape_string (c::rest) verbatim = c::(unescape_string rest verbatim)) ∧
  (unescape_string "" _ = "")
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
         i <- string_to_int s;
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
       return (string_to_cml_char_list (unescape_string s verbatim))
   | CharLiteral ch =>
       return (Lit (Char ch))
   | CharLiteralUTF16 n =>
       fail "CharLiteralUTF16 n: Unsupported"
   (* Encode a nullable type as ((a' ref) option) *)
   | Null typ =>
       return None
End

(* Cannot merge with from_classitem, since methods may be mutually recursive/
 * not defined in the proper order, resulting in being referenced before they
 * have been added to the context *)
Definition call_type_env_from_class_body_def:
  call_type_env_from_class_body acc _ [] = return acc ∧
  call_type_env_from_class_body acc comp ((ClassItem_Method m)::rest) =
  do
    is_function <- method_is_function m;
    is_method <- method_is_method m;
    if is_function then
      do
        (_, _, _, nam, _, _, _, outTypes, _) <<- dest_Method m;
        outTypes <<- MAP normalize_type outTypes;
        acc <<- (((comp, nam), HD outTypes)::acc);
        call_type_env_from_class_body acc comp rest;
      od
    else if is_method then
      do
        (_, _, _, nam, _, _, _, _, _) <<- dest_Method m;
        (* outTypes refers to the type of outVars; the method itself returns
         * Unit (I think) *)
        acc <<- (((comp, nam), Tuple [])::acc);
        call_type_env_from_class_body acc comp rest
      od
    else
      fail "call_type_env_from_class_body: ClassItem_Method m was neither \
           \method nor function."
  od
End

Definition local_env_name_def:
  local_env_name n = (Companion [], n)
End

Definition tuple_len_def:
  tuple_len (Tuple ts) = return (LENGTH ts) ∧
  tuple_len _ = fail "tuple_len: Not a tuple type"
End

Definition dafny_type_of_def:
  dafny_type_of (env: (((expression # name), type) alist))
                (e: dafny_ast$expression) =
  (case e of
   | Literal (BoolLiteral _) => return (Primitive Bool)
   | Literal (IntLiteral _ (Primitive Int)) => return (Primitive Int)
   | Literal (StringLiteral _ _) => return (Seq (Primitive Char))
   | Literal (CharLiteral _) => return (Primitive Char)
   | Expression_Ident n =>
       (case ALOOKUP env (local_env_name n) of
        | SOME t => return t
        | NONE => fail ("dafny_type_of: Unknown Name " ++ (dest_Name n)))
   | Expression_Tuple es =>
       do
         ts <- map_dafny_type_of env es;
         return (Tuple ts)
       od
   | NewArray [_] typ => return (Array (normalize_type typ) 1)
   | Convert _ fro tot =>
       (* Assume that we are given a "correct" Dafny program, and this convert
        * is safe *)
       return (normalize_type tot)
   | SeqValue _ t =>
       return (Seq (normalize_type t))
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
           else if (bop = Concat ∧ e1_t = (Seq (Primitive Char)) ∧
                    e1_t = e2_t) then
             return (Seq (Primitive Char))
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
   | ArrayLen _ _ => return (Primitive Int)
   | Index e' cok idxs =>
       do
         e'_t <- dafny_type_of env e';
         if cok = CollKind_Seq then
           if idxs = [] then
             fail "dafny_type_of (Index/Seq): Unexpectedly idxs was empty"
           else if LENGTH idxs > 1 then
             fail "dafny_type_of (Index/Seq): multi-dimensional indexing \
                    \unsupported"
           else
             dest_Seq e'_t
         else if cok = CollKind_Array then
           if idxs = [] then
             fail "dafny_type_of (Index/Array): Unexpectedly idxs was empty"
           else if LENGTH idxs > 1 then
             fail "dafny_type_of (Index/Array): multi-dimensional indexing \
                 \uns            upported"
           else
             do
               (t, _) <- dest_Array e'_t;
               return t
             od
         else
           fail "dafny_type_of (Index): Unsupported kind of collection"
       od
   | IndexRange se isArray lo hi =>
       if isArray then
         do
           arr_t <- dafny_type_of env se;
           (elem_t, _) <- dest_Array arr_t;
           return (Seq elem_t)
         od
       else
         dafny_type_of env se
   | TupleSelect _ _ fieldT =>
       return (normalize_type fieldT)
   | Expression_Call on (CallName nam onType _) _ _ =>
       if onType ≠ NONE then
         fail "dafny_type_of: (Call) Unsupported onType"
       else
         let ct_name = nam in
           (case ALOOKUP env (on, ct_name) of
            | SOME t => return t
            | NONE => fail ("dafny_type_of: Unknown Name " ++
                            dest_Name ct_name))
           | _ => fail ("dafny_type_of: Unsupported expression" ++ (ARB e))) ∧
  map_dafny_type_of env ts =
  (case ts of
   | [] => return []
   | t::rest =>
       do
         t <- dafny_type_of env t;
         rest <- map_dafny_type_of env rest;
         return (t::rest)
       od)
Termination
  cheat
End

Definition dest_Companion_def:
  dest_Companion (Companion comp) = return comp ∧
  dest_Companion _ = fail "dest_Companion: Not a Companion"
End

Definition gen_call_name_def:
  (gen_call_name comp on (CallName nam onType _) =
   if onType ≠ NONE then
     fail "gen_call_name: non-empty onType currently unsupported"
   else if comp = on then
     do
       cml_call_name <- cml_id [dest_Name nam];
       return (Var cml_call_name)
     od
   else
     do
       on <- dest_Companion on;
       (* Convert to strings *)
       on <<- MAP (dest_Name ∘ dest_Ident) on;
       (* TODO This only works because we ignore/do not support classes ATM *)
       on <<- FILTER (λn. n ≠ "__default") on;
       cml_call_name <- cml_id (SNOC (dest_Name nam) on);
       return (Var cml_call_name)
     od) ∧
  gen_call_name _ _ _ = fail "gen_call_name: Passed callName currently \
                           \unsupported"
End

(* TODO Clean up from_expression/dafny_type_of: Some code parts may be duplicated,
 some checks may be unnecessary (depending on the assumptions we make about/get from
 the Dafny AST *)
Definition from_expression_def:
  (from_expression comp (env: (((expression # name), type) alist))
                   (e: dafny_ast$expression) : (ast$exp result) =
   case e of
   | Literal l =>
       from_literal l
   | Expression_Ident n =>
       return (App Opderef [Var (Short (dest_Name n))])
   | Expression_Tuple es =>
       do
         cml_es <- map_from_expression comp env es;
         cml_tuple cml_es
       od
   | NewArray [dim0] t =>
       do
         t <<- normalize_type t;
         cml_dim0 <- from_expression comp env dim0;
         fill_val <- arb_value t;
         return (Some (cml_fapp (Var (Long "Array" (Short "array")))
                                [cml_dim0; fill_val]))
       od
   | Convert val fro tot =>
       do
         if normalize_type fro ≠ normalize_type tot then
           fail "from_expression (Convert): Converting different types \
                \(after normalization) unsupported"
         else
           from_expression comp env val
       od
   | SeqValue els _ =>
       do
         cml_els <- map_from_expression comp env els;
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
             cml_se <- from_expression comp env se;
             cml_idx <- from_expression comp env idx;
             cml_v <- from_expression comp env v;
             return (cml_fapp (Var (Long "List" (Short "update")))
                              [cml_v; cml_idx; cml_se])
           od
       od
   | Ite cnd thn els =>
       do
         cml_cnd <- from_expression comp env cnd;
         cml_thn <- from_expression comp env thn;
         cml_els <- from_expression comp env els;
         return (If cml_cnd cml_thn cml_els)
       od
   | UnOp uop e =>
       from_unaryOp comp env uop e
   | BinOp bop e1 e2 =>
       from_binOp comp env bop e1 e2
   | ArrayLen e dim =>
       if dim ≠ 0 then
         fail "from_expression (ArrayLen): != 1 dimension unsupported"
       else
         do
           cml_e <- from_expression comp env e;
           return (cml_fapp (Var (Long "Array" (Short "length")))
                            [cml_get_arr cml_e])
         od
   | Index ce cok idxs =>
       if cok = CollKind_Seq then
         if idxs = [] then
           fail ("from_expression: Unexpectedly received an empty " ++
                 "list of indices")
         else if LENGTH idxs > 1 then
           fail "from_expression: multi-dimensional indexing unsupported"
         else
           do
             cml_ce <- from_expression comp env ce;
             idx <- from_expression comp env (EL 0 idxs);
             return (cml_fapp (Var (Long "List" (Short "nth"))) [cml_ce; idx])
           od
       else if cok = CollKind_Array then
         if idxs = [] then
           fail "from_expression (Index/Array): Unexpectedly received an \
                \empty list of indices"
         else if LENGTH idxs > 1 then
           fail "from_expression (Index/Array): multi-dimensional indexing \
                \unsupported"
         else
           do
             cml_ce <- from_expression comp env ce;
             idx <- from_expression comp env (EL 0 idxs);
             return (cml_fapp (Var (Long "Array" (Short "sub")))
                              [cml_get_arr cml_ce; idx])
           od
       else
         fail "from_expression: Unsupported kind of collection"
   | IndexRange ce isArray lo hi =>
       do
         cml_ce <- from_expression comp env ce;
         cml_se <<- if isArray then
                     cml_fapp (Var (Long "Dafny" (Short "array_to_list")))
                              [cml_get_arr cml_ce]
                    else cml_ce;
         cml_se <- case hi of
                   | NONE => return cml_se
                   | SOME hi =>
                       do
                         cml_hi <- from_expression comp env hi;
                         return (cml_fapp (Var (Long "List" (Short "take")))
                                          [cml_se; cml_hi])
                       od;
         case lo of
         | NONE => return cml_se
         | SOME lo =>
               do
                 cml_lo <- from_expression comp env lo;
                 return (cml_fapp (Var (Long "List" (Short "drop")))
                                  [cml_se; cml_lo])
               od
       od
   | TupleSelect te idx type =>
       do
         te_t <- dafny_type_of env te;
         len <- tuple_len te_t;
         cml_te <- from_expression comp env te;
         return (cml_tuple_select len cml_te idx)
       od
   | Expression_Call on call_nam typeArgs args =>
       do
         if typeArgs ≠ [] then
           fail "from_expression: (Call) type arguments currently unsupported"
         else
           do
             fun_name <- gen_call_name comp on call_nam;
             cml_args <- result_mmap (from_expression comp env) args;
             return (cml_fapp fun_name cml_args)
           od
       od
   | InitializationValue t =>
       arb_value (normalize_type t)
   | _ => fail ("from_expression: Unsupported expression" ++ (ARB e))) ∧
  (map_from_expression comp env es =
   case es of
   | [] => return []
   | (e::rest) =>
       do
         se' <- from_expression comp env e;
         rest' <- map_from_expression comp env rest;
         return (se'::rest')
       od) ∧
  (from_unaryOp comp env (uop: dafny_ast$unaryOp)
                (e: dafny_ast$expression) =
   do
     e_t <- dafny_type_of env e;
     cml_e <- from_expression comp env e;
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
  (from_binOp comp env (bop: dafny_ast$binOp)
              (e1: dafny_ast$expression) (e2: dafny_ast$expression) =
   do
     e1_t <- dafny_type_of env e1;
     e2_t <- dafny_type_of env e2;
     cml_e1 <- from_expression comp env e1;
     cml_e2 <- from_expression comp env e2;
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
            return (cml_fapp (Var (Long "Dafny" (Short "ediv")))
                             [cml_e1; cml_e2])
          else
            fail "from_binOp (EuclideanDiv): Unsupported types"
      | EuclidianMod =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Long "Dafny" (Short "emod")))
                             [cml_e1; cml_e2])
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
          if (is_Seq e1_t ∧ e1_t = e2_t) then
            return (cml_fapp (Var (Long "List" (Short "@"))) [cml_e1; cml_e2])
          else
            fail "from_binOp (Concat): Unsupported types"
      | _ => fail "from_binOp: Unsupported bop")
   od)
Termination
  cheat
End

(* Returns a function that can be applied to a CakeML expression to turn it into
 * a string *)
Definition to_string_fun_def:
  (to_string_fun _ (Primitive Char) =
   return (Var (Long "Dafny" (Short "char_to_string")))) ∧
  (to_string_fun _ (Primitive Int) =
   return (Var (Long "Dafny" (Short "int_to_string")))) ∧
  (to_string_fun _ (Primitive Bool) =
   return (Var (Long "Dafny" (Short "bool_to_string")))) ∧
  (to_string_fun inCol (Seq (Primitive Char)) =
   if inCol then
     return (Var (Long "Dafny" (Short "char_list_to_string")))
   else return (Var (Long "String" (Short "implode")))) ∧
  (to_string_fun _ (Seq t) =
   do
     elem_to_string <- to_string_fun T t;
     return (cml_fapp (Var (Long "Dafny" (Short "list_to_string")))
                      [elem_to_string])
   od) ∧
  (to_string_fun _ (Tuple ts) =
   do
     elems_to_string <- map_to_string_fun T ts;
     string_list <<- cml_tuple_to_string_list elems_to_string;
     return (cml_fapp (Var (Long "Dafny" (Short "tuple_to_string")))
                           [string_list])
   od) ∧
  (to_string_fun _ t = fail ("to_string_fun: Unsupported type" ++ ARB t)) ∧
  (map_to_string_fun inCol ts =
   case ts of
   | [] => return []
   | (t::rest) =>
       do
         t <- to_string_fun inCol t;
         rest <- map_to_string_fun inCol rest;
         return (t::rest)
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
  (from_stmts (comp: expression) (is_function: bool)
              (env: ((expression # name, type) alist))
              (lvl: int) epilogue ([]: (dafny_ast$statement list)) =
   return (env, Unit)) ∧
  (from_stmts comp is_function env lvl epilogue [s] =
   if is_indep_stmt s then
     do
       cml_e <- from_indep_stmt comp is_function env lvl epilogue s;
       return (env, cml_e)
     od
   else
     fail ("from_stmts: " ++
           "Cannot convert single non-self-contained statement")) ∧
  (from_stmts comp is_function env lvl epilogue (s1::s2::rest) =
   if is_indep_stmt s1 then
     do
       e1 <- from_indep_stmt comp is_function env lvl epilogue s1;
       (env', e2) <- from_stmts comp is_function env lvl epilogue (s2::rest);
       return (env', (Let NONE e1 e2))
     od
   else if is_DeclareVar s1 then
     do
       (n, t, e_opt) <- dest_DeclareVar s1;
       t <<- normalize_type t;
       n_str <<- dest_Name n;
       (* TODO look into when/why this is NONE *)
       iv_e <- if e_opt = NONE then arb_value t
               else do e <- dest_SOME e_opt; from_expression comp env e od;
       (env', in_e) <- from_stmts comp is_function ((local_env_name n, t)::env)
                                  lvl epilogue (s2::rest);
       return (env', cml_ref n_str iv_e in_e)
     od
   else
     fail "from_stmts: Unsupported statement") ∧
  (from_indep_stmt comp (is_function: bool) env (lvl: int) epilogue
                   (s: dafny_ast$statement) =
   (case s of
    | Assign lhs e =>
        do
          cml_rhs <- from_expression comp env e;
          case lhs of
          | AssignLhs_Ident id =>
              return (cml_ref_ass (from_ident id) cml_rhs)
          | AssignLhs_Index e' [idx] =>
              do
                cml_e' <- from_expression comp env e';
                cml_arr <<- cml_get_arr cml_e';
                cml_idx <- from_expression comp env idx;
                return (cml_fapp (Var (Long "Array" (Short "update")))
                                 [cml_arr; cml_idx; cml_rhs])
              od
          | _ =>
              fail "from_indep_stmt (Assign): Unsupported LHS"
        od
    | If cnd thn els =>
        do
          cml_cnd <- from_expression comp env cnd;
          (_, cml_thn) <- from_stmts comp is_function env lvl epilogue thn;
          (_, cml_els) <- from_stmts comp is_function env lvl epilogue els;
          return (If cml_cnd cml_thn cml_els)
        od
    | Labeled lbl body =>
        do
          (_, cml_body) <- from_stmts comp is_function env lvl epilogue body;
          return (add_labeled_break_handle lbl cml_body)
        od
    | While cnd body =>
        do
          cml_cnd <- from_expression comp env cnd;
          (_, cml_body) <- from_stmts comp is_function env (lvl + 1)
                                           epilogue body;
          exec_iter <<- (cml_fapp (Var (Short (cml_while_name lvl))) [Unit]);
          cml_while_def <<- (Letrec [((cml_while_name lvl), "",
                                     If (cml_cnd)
                                        (Let NONE cml_body exec_iter) (Unit))]
                                    (add_break_handle exec_iter));
          return cml_while_def
        od
    | Call on call_nam typeArgs args outs =>
        do
          if typeArgs ≠ [] then
            fail "from_indep_stmt: (Call) type arguments currently unsupported"
          else
            do
              fun_name <- gen_call_name comp on call_nam;
              cml_param_args <- result_mmap (from_expression comp env) args;
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
            from_expression comp env e
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
          e_t <- dafny_type_of env e;
          cml_e_to_string <- to_string_fun F e_t;
          cml_e <- from_expression comp env e;
          cml_e_string <<- cml_fapp cml_e_to_string [cml_e];
          return (cml_fapp (Var (Short "print")) [cml_e_string])
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
    param_type_env rest ((local_env_name n, (normalize_type t))::acc)
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
         env <<- ((local_env_name v_nam, t)::env);
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
  process_function_body comp env preamble stmts =
   do
     (env, cml_body) <- from_stmts comp T env 0 Unit stmts;
     return (preamble cml_body)
   od
End

Definition process_method_body_def:
  process_method_body comp env preamble epilogue body =
  do
    (_, cml_body) <- from_stmts comp F env 0 epilogue body;
    cml_body <<- (Handle cml_body
                   [Pcon (SOME (Long "Dafny" (Short "Return"))) [], Unit]);
    return (preamble cml_body)
  od
End

Definition from_classItem_def:
  from_classItem comp env (ClassItem_Method m) =
  do
    is_function <- method_is_function m;
    is_method <- method_is_method m;
    if is_function then
      do
        (_, _, _, nam, _, params, body, _, _) <<- dest_Method m;
        fun_name <<- dest_Name nam;
        (env, cml_param, preamble) <- gen_param_preamble env params;
        cml_body <- process_function_body comp env preamble body;
        return (fun_name, cml_param, cml_body)
      od
    else if is_method then
      do
        (_, _, _, nam, _, params, body, outTypes, outVars) <<- dest_Method m;
        outTypes <<- MAP normalize_type outTypes;
        outVars <- dest_SOME outVars;
        fun_name <<- dest_Name nam;
        (env, cml_param,
         preamble, epilogue) <- gen_param_preamble_epilogue env params
                                                            outTypes outVars;
        cml_body <- process_method_body comp env preamble epilogue body;
        return (fun_name, cml_param, cml_body)
      od
    else
      fail "(Unreachable) from_method: m was neither a function nor method"
  od
End

Definition from_classlist_def:
  (from_classlist env [] = return (env, [])) ∧
  (from_classlist env [ModuleItem_Class
                        (Class name enclosingModule typeParams
                               superClasses fields body attributes)] =
   if name ≠ (Name "__default") then
     fail "from_classlist: Unsupported name"
   else if typeParams ≠ [] then
     fail "from_classlist: Type params unsupported"
   else if superClasses ≠ [] then
    fail "from_classlist: Superclasses unsupported"
   else if fields ≠ [] then
     fail "from_classlist: Fields unsupported"
   else if attributes ≠ [] then
     fail "from_classlist: Attributes unsupported"
   else
     do
       comp <<- Companion [enclosingModule; Ident name];
       env <- call_type_env_from_class_body env comp body;
       fun_defs <- result_mmap (from_classItem comp env) body;
       (* TODO Look at how PureCake detangles Dletrecs
        * Having one big Dletrec probably does not result in a performance
        * penalty unless functions are used in a higher order way *)
       return (env, [(Dletrec unknown_loc fun_defs)]);
     od) ∧
  (from_classlist _ _ =
   fail "from_classlist: Unsupported item list")
End

(* Pattern matching resulting from from_module (Module nam attrs body) cannot
 * be (automatically) eliminated, hence we use dest_Module *)
Definition from_module_def:
  (from_module env m =
   let (nam, attrs, body) = dest_Module m in
     case body of
   | NONE => fail "from_module: empty body unsupported"
   | SOME modItems =>
       if attrs ≠ [] then
         fail "from_module: attributes unsupported"
       else if EXISTS is_moditem_trait modItems then
         fail "from_module: traits unsupported"
       else if EXISTS is_moditem_newtype modItems then
         fail "from_module: newtypes unsupported"
       else if EXISTS is_moditem_datatype modItems then
         fail "from_module: newtypes unsupported"
       else if EXISTS is_moditem_module modItems then
         fail "from_module: Unexpected nested module"
       else
         do
           clss <<- FILTER is_moditem_class modItems;
           (env, fun_defs) <- from_classlist env clss;
           return (env, Dmod (dest_Name nam) fun_defs)
         od)
End

Definition map_from_module_def:
  map_from_module env [] = return (env, []) ∧
  map_from_module env (m::rest) =
  do
    (env, cml_mod) <- from_module env m;
    (env, cml_mods) <- map_from_module env rest;
    return (env, (cml_mod::cml_mods))
  od
End

Definition find_main_def:
  find_main env =
  do
    main_defs <<- FILTER (λ((_, n), _). dest_Name n = "Main") env;
    if main_defs = [] then
      fail "find_main: Main could not be found"
    else if LENGTH main_defs > 1 then
      fail "find_main: More than one main found"
    else
      do
        ((on, nam), _) <<- HD main_defs;
        gen_call_name (Companion []) on (CallName nam NONE (CallSignature []))
      od
  od
End

Definition validate_system_module_body_def:
  (validate_system_module_body [] = return ()) ∧
  (validate_system_module_body ((ModuleItem_Newtype
                               (Newtype nam typeParams base rang
                                        witnessStmts witnessExpr
                                        attrs))::rest) =
   (* Restrict newtype support to Int *)
   if typeParams ≠ [] then
     fail "validate_system_module_body: Type parameters unsupported"
   else if base ≠ Primitive Int then
     fail "validate_system_module_body: base other than Primitive Int \
          \unsupported"
   else if rang ≠ NoRange then
     fail "validate_system_module_body: range other than NoRange unsupported"
   else if witnessStmts ≠ [] then
     fail "validate_system_module_body: Witness statements unsupported"
   else if witnessExpr ≠ NONE then
     fail "validate_system_module_body: Witness expression unsupported"
   else if attrs ≠ [Attribute "axiom" []] then
     fail "validate_system_module_body: Unsupported attribute list"
   else
     validate_system_module_body rest) ∧
  (validate_system_module_body ((ModuleItem_Datatype
                               (Datatype nam enclosingModule
                                             _ _ _ _ _)::rest)) =
   (* Restrict datatype support to tuples *)
   if enclosingModule ≠ (Ident (Name "_System")) then
     fail "validate_system_module_body: Unsupported enclosing module"
   else
     case strip_prefix "Tuple" (dest_Name nam) of
     | NONE => fail "validate_system_module_body: Unsupported datatype name"
     | SOME sfx => do string_to_num sfx; validate_system_module_body rest od) ∧
  (validate_system_module_body _ =
   fail "validate_system_module_body: Unsupported module item")
End

Definition validate_system_module_def:
  validate_system_module (Module nam attrs body) =
  if nam ≠ Name "_System" then
    fail "validate_system_module: Not module _System"
  else if attrs ≠ [] then
    fail "validate_system_module: Expected empty attribute list"
  else
    case body of
    | NONE => fail "validate_system_module: Unexpectedly body was empty"
    | SOME body => validate_system_module_body body
End

Definition compile_def:
  compile ((sys_mod::ms) : dafny_ast$module list) =
  do
    validate_system_module sys_mod;
    (env, cml_ms) <- map_from_module [] ms;
    main_id <- find_main env;
    return (^dafny_module ++
            cml_ms ++
            [Dlet unknown_loc Pany (cml_fapp main_id [Unit])])
  od ∧
  compile _ = fail "compile: Module layout unsupported"
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
val _ = astPP.enable_astPP();

val inStream = TextIO.openIn "./tests/dafny/firstSteps/3_Calls-As.sexp";
val fileContent = TextIO.inputAll inStream;
val _ = TextIO.closeIn inStream;
val fileContent_tm = stringSyntax.fromMLstring fileContent;

val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand;
val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand;
val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand;
val cakeml_r = EVAL “(compile ^dafny_r)” |> concl |> rhs |> rand;

val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^cakeml_r)))”
                   |> concl |> rhs |> rand;
(* Test Dafny module *)
(* val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^dafny_module)))” *)
(*                    |> concl |> rhs |> rand; *)
val cml_sexp_str_r = stringSyntax.fromHOLstring cml_sexp_r;
val outFile = TextIO.openOut "./tests/test.cml.sexp";
val _ = TextIO.output (outFile, cml_sexp_str_r);
val _ = TextIO.closeOut outFile;

val _ = export_theory();
