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

(* TODO Instead of keeping track of types manually, maybe we can add them
   in the upstream Dafny AST *)

(* TODO Separately check whether a feature is supported or not? *)

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

(* TODO? Merge is_<Con> and dest_<Con> into one def returning an option *)
Definition is_Eq_def:
  is_Eq bop =
  case bop of
  | Eq _ => T
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

Definition is_moditem_synonymtype_def:
  is_moditem_synonymtype (ModuleItem_SynonymType _) = T ∧
  is_moditem_synonymtype _ = F
End

Definition is_moditem_datatype_def:
  is_moditem_datatype (ModuleItem_Datatype _) = T ∧
  is_moditem_datatype _ = F
End

Definition dest_Array_def:
  dest_Array (Array t dims) = return (t, dims) ∧
  dest_Array _ = fail "dest_Array: Not an Array"
End

Definition dest_Arrow_def:
  dest_Arrow (Arrow argTs retT) = return (argTs, retT) ∧
  dest_Arrow _ = fail "dest_Arrow: Not an arrow"
End

Definition dest_singleton_list_def:
  dest_singleton_list [x] = return x ∧
  dest_singleton_list _ = fail "dest_singleton_list: Not a singleton list"
End

Definition dest_Seq_def:
  dest_Seq (Seq t) = return t ∧
  dest_Seq _ = fail "dest_Seq: Not a Seq"
End

Definition dest_Module_def:
  dest_Module (Module nam attrs requiresExtern body) =
  (nam, attrs, requiresExtern, body)
End

(* TODO? Move to dafny_ast *)
Definition dest_Name_def:
  dest_Name (Name s) = s
End

(* TODO move this to result_monad? *)
Definition dest_SOME_def:
  dest_SOME (SOME x) = return x ∧
  dest_SOME NONE = fail "dest_SOME: Not a SOME"
End

Definition cml_ref_ass_def:
  cml_ref_ass lhs rhs = (App Opassign [lhs; rhs])
End

Definition cml_ref_def:
  cml_ref n val_e in_e = (Let (SOME n) ((App Opref [val_e])) in_e)
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

(* TODO Find better way to generate internal names *)

Definition return_ref_name_def:
  return_ref_name = "_CML_return"
End

Definition varN_from_formal_def:
  varN_from_formal (Formal n _ attrs) =
  if attrs ≠ [] then
    fail "param_from_formals: Attributes currently unsupported"
  else
    return (dest_varName n)
End

Definition internal_varN_from_formal_def:
  internal_varN_from_formal fo =
  do
    n <- varN_from_formal fo;
    return (n ++ "_CML_param")
  od
End

Definition internal_varN_from_varName_def:
  internal_varN_from_varName (VarName n) = (n ++ "_CML_out_ref")
End

Definition local_env_name_def:
  local_env_name n = (Companion [] [], n)
End

(* In Dafny, the string and seq<char> type are synonyms. We replace the
 * former with the latter for consistency. We also replace newtypes by their
 * base type (which may be incorrect) *)
(* TODO? Maybe it is better to implement this with a map as Dafny does it;
   Seems like Dafny has a function to remove synonyms? *)
Definition normalize_type_def:
  normalize_type t =
  (case t of
   | Primitive String => Seq (Primitive Char)
   (* TODO Unsure whether we can ignore these like that *)
   | UserDefined
     (ResolvedType _ [] rtb attrs [] extendedTs) =>
       (* Returning t in this case means it is unsupported *)
       if attrs ≠ [Attribute "axiom" []] ∧ attrs ≠ [] then
         t
       else if extendedTs ≠ [Primitive Int] ∧ extendedTs ≠ [] then
         t
       else
         (case rtb of
          | ResolvedTypeBase_SynonymType bt => normalize_type bt
          (* Is dealing with newtype like this really fine? *)
          | ResolvedTypeBase_Newtype bt _ _ => normalize_type bt
          | _ => t)
   | Tuple ts => Tuple (map_normalize_type ts)
   | Array elem dims => Array (normalize_type elem) dims
   | Seq t => Seq (normalize_type t)
   | Set t => Set (normalize_type t)
   | Multiset t => Multiset (normalize_type t)
   | Type_Map kt vt => Type_Map (normalize_type kt) (normalize_type vt)
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

Definition compose_all_def:
  compose_all = FOLDR (o) I
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

Definition cml_option_def:
  cml_option (opt: exp option) : exp =
  (case opt of
   | NONE => None
   | SOME cml_e => Some cml_e)
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

Definition param_type_env_def:
  param_type_env [] acc = return acc ∧
  param_type_env ((Formal n t attrs)::rest) acc =
  if attrs ≠ [] then
    fail "param_type_env: Attributes unsupported"
  else
    let n = dest_varName n in
      param_type_env rest ((local_env_name n, (normalize_type t))::acc)
End

Definition out_type_env_def:
  out_type_env [] [] env : (((expression # string) # type) list) result =
    return env
  ∧
  out_type_env [] _ env =
    fail "out_type_env: More out variables than types"
  ∧
  out_type_env _ [] env =
    fail "out_type_env: More out variables than types"
  ∧
  out_type_env (out_t::rest_t) (out_v::rest_v) env =
  (let v_str = dest_varName out_v in
     out_type_env rest_t rest_v ((local_env_name v_str, out_t)::env))
End

Definition add_local_env_def:
  add_local_env env params (outTypes : type list) (outVars : varName list option) : (((expression # string) # type) list) result =
  do
    env <- param_type_env params env;
    case outVars of
    | NONE => return env
    | SOME outVars => out_type_env outTypes outVars env
  od
End

Definition first_param_def:
  first_param (param::params) outVars = internal_varN_from_formal param
  ∧
  first_param [] outVars =
  (case outVars of
   | NONE => return ""
   | SOME [] => return ""
   | SOME (out_v::out_vs) => return (internal_varN_from_varName out_v))
End

(* Declares additional parameters using Fun x => ... *)
Definition fun_from_params_def:
  (fun_from_params (preamble : exp -> exp) [] = return preamble) ∧
  (fun_from_params preamble (fo::rest) =
   do
     param_name <- internal_varN_from_formal fo;
     preamble <<- (λx. preamble (Fun param_name x));
     fun_from_params preamble rest
   od)
End

(* Allows us to pass in out references as parameters *)
Definition fun_from_outs_def:
  fun_from_outs (preamble : exp -> exp) [] = preamble ∧
  fun_from_outs preamble (v::rest_v) =
     fun_from_outs (λx. preamble (Fun (internal_varN_from_varName v) x)) rest_v
End

(* Declares and initializes references for the parameters that the body will use
 *
 * We do this since within the body the parameter names act as variables, which
 * we encode using references. *)
Definition ref_from_params_def:
  (ref_from_params (preamble : exp -> exp) [] = return preamble) ∧
  (ref_from_params preamble (fo::rest) =
   do
     ref_name <- varN_from_formal fo;
     ref_value_name <- internal_varN_from_formal fo;
     preamble <<- (λx. preamble ((cml_ref ref_name
                                          (Var (Short ref_value_name)) x)));
     ref_from_params preamble rest
   od)
End

(* Preamble: Rest of parameters *)
Definition gen_preamble_aux_def:
  gen_preamble_aux [] [] =
   return (λx. x)
  ∧
  gen_preamble_aux [] (out_v::rest_v) =
    return (fun_from_outs (λx. x) rest_v)
  ∧
  gen_preamble_aux (param::params) outVars =
  do
    (* First parameter is part of the function signature *)
    preamble <- fun_from_params (λx. x) params;
    preamble <<- fun_from_outs preamble outVars;
    ref_from_params preamble (param::params)
  od
End

Definition gen_preamble_def:
  gen_preamble params outVars =
  (case outVars of
   | NONE => gen_preamble_aux params []
   | SOME outVars => gen_preamble_aux params outVars)
End

Definition gen_epilogue_aux_def:
  gen_epilogue_aux [] epilogue : exp = epilogue Unit
  ∧
  gen_epilogue_aux (out_v::rest_v) epilogue =
  let v_str = dest_varName out_v;
      out_ref_name = internal_varN_from_varName out_v;
      epilogue = (λx. epilogue (Let NONE (cml_ref_ass
                                          (Var (Short out_ref_name))
                                          ((App Opderef
                                                [Var (Short v_str)])))
                                    x)) in
    gen_epilogue_aux rest_v epilogue
End

Definition gen_epilogue_def:
  gen_epilogue (SOME (outVars : varName list)) : exp =
    gen_epilogue_aux outVars (λx. x)
  ∧
  gen_epilogue NONE = Unit
End

(* Returns a function that can be applied to a CakeML expression to turn it into
 * a string *)
Definition to_string_fun_def:
  (to_string_fun _ (Primitive Char) =
   return (Var (Long "Dafny" (Short "char_to_string")))) ∧
  (to_string_fun _ (Primitive Int) =
   return (Var (Long "Dafny" (Short "int_to_string")))) ∧
  (to_string_fun _ (Primitive Primitive_Bool) =
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
  (to_string_fun _ t = fail ("to_string_fun: Unsupported type")) ∧
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

Definition dest_resolvedType_def:
  dest_resolvedType (ResolvedType path typeArgs kind attrs properMethods
                                  extendedTypes) =
  (path, typeArgs, kind, attrs, properMethods, extendedTypes)
End

Definition arb_value_def:
  arb_value (t: dafny_ast$type) =
  (case t of
   | Primitive Int => return (Lit (IntLit 0))
   | Primitive Primitive_Bool => return False
   | Seq _ => return (cml_list [])
   | Tuple ts =>
       do
         arb_elems <- map_arb_value ts;
         cml_tuple arb_elems
       od
   | Array _ _ => return None  (* we essentially initialize with null *)
   | UserDefined resT => arb_value_resolved_type resT
   | Arrow ts t =>
       do
         arb_ret <- arb_value t;
         nr_params <<- (LENGTH ts);
         params <<- if nr_params = 0
                    then [λx. Fun "u" x]
                    else GENLIST (λx. Fun ("p" ++ (num_to_string x)))
                                 (LENGTH ts);
         return (compose_all params arb_ret)
       od
   | _ => fail "arb_value_def: Unsupported type") ∧
  (arb_value_resolved_type resT =
   let (_, typeArgs, kind, attrs,
        properMethods, extendedTypes) = dest_resolvedType resT in
     if typeArgs ≠ [] then
       fail "arb_value_resolved_type: type args unsupported"
     else if attrs ≠ [] ∧ attrs ≠ [Attribute "axiom" []] then
       fail "arb_value_resolved_type: unsupported attributes"
     else if properMethods ≠ [] then
       fail "arb_value_resolved_type: proper methods unsupported"
     else if extendedTypes ≠ [] ∧ extendedTypes ≠ [Primitive Int] then
       fail "arb_value_resolved_type: unsupported extended types"
     else
       case kind of
       | ResolvedTypeBase_Newtype baseT rang eras =>
           if baseT ≠ Primitive Int then
             fail "arb_value_resolved_type: Unsupported base type"
           else if rang ≠ NoRange then
             fail "arb_value_resolved_type: Unsupported range"
           else if ¬eras then
             fail "arb_value_resolved_type: non-erased newtypes unsupported"
           else
             arb_value baseT
       | _ => fail "arb_value_resolved_type: unsupported resolved type base") ∧
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

(* Cannot have type variables in exceptions, so we need to store the return
   value of functions in a reference. *)
Definition add_return_ref_def:
  add_return_ref cml_body (outTypes : type list) (outVars : (varName list) option) =
  (case outVars of
   (* If there is exactly one return type, but no out variable, we add a
      reference for returning. *)
   | NONE =>
       (case outTypes of
        | [t] =>
            do
              (* "Return" value of return reference *)
              cml_body <<- (Let NONE cml_body
                                (App Opderef [Var (Short return_ref_name)]));
              init_v <- arb_value t;
              return (cml_ref return_ref_name init_v cml_body)
            od
        | _ =>
            fail "add_return_ref: No out variables, but not exactly one return \
                 \type")
   | SOME _ => return cml_body)
End

(* TODO double check whether this is used *)
Definition from_varName_def:
  from_varName n = Var (Short (dest_varName n))
End

(* TODO double check if this is still used *)
Definition from_name_def:
  from_name n = Var (Short (dest_Name n))
End

(* TODO double check if this is still used *)
Definition from_ident_def:
  from_ident (Ident n) = from_name n
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

Definition type_from_formals_def:
  type_from_formals [] = return [] ∧
  type_from_formals ((Formal _ t attrs)::rest) =
  if attrs ≠ [] then
    fail "type_from_formals: Attributes unsupported"
  else
    do
      restTs <- type_from_formals rest;
      return ((normalize_type t)::(map_normalize_type restTs))
    od
End

(* Cannot merge with from_classitem, since methods may be mutually recursive/
 * not defined in the proper order, resulting in being referenced before they
 * have been added to the context *)
Definition call_type_env_from_class_body_def:
  call_type_env_from_class_body acc _ [] = return acc ∧
  call_type_env_from_class_body acc (comp : expression) ((ClassItem_Method m)::rest) =
  do
    (_, _, _, _, _, _, nam, _, params, _, _, outTypes, outVars) <<- dest_Method m;
    nam <<- dest_Name nam;
    param_t <- type_from_formals params;
    ret_t <- (case outVars of
             | NONE =>
                 (case outTypes of
                  | [ret_t] => return (normalize_type ret_t)
                  | _ => fail "call_type_env_from_class_body: outTypes was not a singleton")
             | SOME _ =>
                 return (Tuple []));
    acc <<- (((comp, nam), Arrow param_t ret_t)::acc);
    call_type_env_from_class_body acc comp rest
  od
End

Definition tuple_len_def:
  tuple_len (Tuple ts) = return (LENGTH ts) ∧
  tuple_len _ = fail "tuple_len: Not a tuple type"
End

Definition dafny_type_of_def:
  dafny_type_of (env: (((expression # string), type) alist))
                (e: dafny_ast$expression) =
  (case e of
   | Literal (BoolLiteral _) => return (Primitive Primitive_Bool)
   | Literal (IntLiteral _ (Primitive Int)) => return (Primitive Int)
   | Literal (StringLiteral _ _) => return (Seq (Primitive Char))
   | Literal (CharLiteral _) => return (Primitive Char)
   | Expression_Ident n =>
       let n = dest_varName n in
         (case ALOOKUP env (local_env_name n) of
          | SOME t => return t
          | NONE => fail ("dafny_type_of: Unknown name " ++ n))
   | Expression_Tuple es =>
       do
         ts <- map_dafny_type_of env es;
         return (Tuple ts)
       od
   | NewUninitArray [_] typ => return (Array (normalize_type typ) 1)
   | FinalizeNewArray e t =>
       do
         e_t <- dafny_type_of env e;
         (* Sanity check *)
         if e_t ≠ (normalize_type t) then
           fail "dafny_type_of (FinalizeNewArray): Unexpected type mismatch"
         else
           return (e_t)
       od
   | Convert _ fro tot =>
       (* Assume that we are given a "correct" Dafny program, and this convert
        * is safe *)
       return (normalize_type tot)
   | SeqConstruct _ fe =>
       do
         fe_t <- dafny_type_of env fe;
         (argTs, retT) <- dest_Arrow fe_t;
         argT <- dest_singleton_list argTs;
         if argT ≠ Primitive Int then
           fail "dafny_type_of (SeqConstruct): Argument of function was not \
                \an int"
         else
           return (Seq retT)
       od
   | SeqValue _ t =>
       return (Seq (normalize_type t))
   | SeqUpdate se idx v collT exprT =>
       if collT ≠ exprT then
         fail "dafny_type_of (SeqUpdate): Unexpectedly, collT <> exprT"
       else
         return (normalize_type collT)
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
         if e_t = (Primitive Primitive_Bool) then
           return (Primitive Primitive_Bool)
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
   | BinOp (TypedBinOp _ _ _ resultT) _ _ => return (normalize_type resultT)
   | ArrayLen _ _ _ _ => return (Primitive Int)
   | SelectFn comp nam onDt isStatic _ _ =>
       (* TODO Figure out whether it is fine to ignore arguments *)
       (* TODO Figure out whether it is fine to ignore isConstant *)
       if onDt then
         fail "dafny_type_of (SelectFn): On datatype unsupported"
       else if ¬isStatic then
         fail "dafny_type_of (SelectFn): non-static unsupported"
       else
         (let nam = dest_varName nam in
            (case ALOOKUP env (comp, nam) of
             | SOME t => return t
             | NONE => fail ("dafny_type_of (SelectFn): Unknown name" ++ nam)))
   | Index e' cok idxs =>
       do
         e'_t <- dafny_type_of env e';
         if cok = CollKind_Seq then
           if LENGTH idxs ≠ 1 then
             fail "dafny_type_of (Index/Seq): Unexpectedly, did not receive \
                  \exactly one index"
           else
             dest_Seq e'_t
         else if cok = CollKind_Array then
           if idxs = [] then
             fail "dafny_type_of (Index/Array): Unexpectedly idxs was empty"
           else if LENGTH idxs > 1 then
             fail "dafny_type_of (Index/Array): multi-dimensional indexing \
                 \unsupported"
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
   | Expression_Call on (CallName nam onType receiverArg receiverAsArgument _)
                     _ _ =>
       if onType ≠ NONE then
         fail "dafny_type_of: (Call) Unsupported onType"
       else if receiverArg ≠ NONE then
         fail "dafny_type_of: (Call) Receiver argument unsupported"
       else if receiverAsArgument then
         fail "dafny_type_of: (Call) Receiver as argument unsupported"
       else
         (let ct_name = dest_Name nam in
            case ALOOKUP env (on, ct_name) of
            | SOME (Arrow _ retT) => return retT
            | NONE => fail ("dafny_type_of: " ++ ct_name ++
                            " not found or bad type"))
   | Lambda params retT _ =>
       do
         argT <- type_from_formals params;
         retT <<- normalize_type retT;
         return (Arrow argT retT)
       od
   | Apply e args =>
       do
         nr_args <<- LENGTH args;
         e_t <- dafny_type_of env e;
         case e_t of
         | Arrow f_argT f_retT =>
             (* We do not bother type checking again *)
             if LENGTH f_argT = nr_args then
               return f_retT
             else if LENGTH f_argT > nr_args then
               return (Arrow (DROP nr_args f_argT) f_retT)
             else
               fail "dafny_type_of (Apply): Unexpectedly, tried to apply \
                    \too many arguments"
         | _ => fail "dafny_type_of (Apply): Unexpectedly, apply used on \
                     \non-arrow type"
       od
   | _ => fail ("dafny_type_of: Unsupported expression")) ∧
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

Definition path_from_companion_def:
  path_from_companion (Companion comp _) = return comp ∧
  path_from_companion _ = fail "dest_Companion: Not a Companion"
End

Definition gen_call_name_def:
  (gen_call_name comp on (CallName nam onType receiverArg
                                   receiverAsArgument _) =
   if onType ≠ NONE then
     fail "gen_call_name: non-empty onType currently unsupported"
   else if receiverArg ≠ NONE then
     fail "gen_call_name: receiverArg unsupported"
   else if receiverAsArgument then
     fail "gen_call_name: receiverAsArgument unsupported"
   else
     do
       comp <- path_from_companion comp;
       on <- path_from_companion on;
       (* Convert to strings *)
       comp <<- MAP (dest_Name ∘ dest_Ident) comp;
       on <<- MAP (dest_Name ∘ dest_Ident) on;
       (* TODO This only works because we ignore classes at the moment *)
       comp <<- FILTER (λn. n ≠ "__default") comp;
       on <<- FILTER (λn. n ≠ "__default") on;
       if comp = on then
         cml_id [dest_Name nam]
       else
         cml_id (SNOC (dest_Name nam) on)
     od) ∧
  gen_call_name _ _ _ =
  fail "gen_call_name: Passed callName currently unsupported"
End

Definition handle_return_def:
  handle_return cml_body =
    Handle cml_body
           [(Pcon (SOME (Long "Dafny" (Short "Return"))) [], Unit)]
End

(* TODO Clean up from_expression/dafny_type_of: Some code parts may be duplicated,
 some checks may be unnecessary (depending on the assumptions we make about/get from
 the Dafny AST *)
Definition from_expression_def:
  (from_expression comp (env: (((expression # string), type) alist))
                   (e: dafny_ast$expression) : (ast$exp result) =
   case e of
   | Literal l =>
       from_literal l
   | Expression_Ident n =>
       return (App Opderef [Var (Short (dest_varName n))])
   | Expression_Tuple es =>
       do
         cml_es <- map_from_expression comp env es;
         cml_tuple cml_es
       od
   | NewUninitArray [dim0] t =>
       do
         t <<- normalize_type t;
         cml_dim0 <- from_expression comp env dim0;
         fill_val <- arb_value t;
         return (Some (cml_fapp (Var (Long "Array" (Short "array")))
                                [cml_dim0; fill_val]))
       od
   | FinalizeNewArray e _ =>
       (* Don't do anything special on finalize *)
       from_expression comp env e
   | Convert val fro tot =>
       do
         if normalize_type fro ≠ normalize_type tot then
           fail "from_expression (Convert): Converting different types \
                \(after normalization) unsupported"
         else
           from_expression comp env val
       od
   | SeqConstruct len f_e =>
       do
         fe_t <- dafny_type_of env f_e;
         (argTs, retT) <- dest_Arrow fe_t;
         argT <- dest_singleton_list argTs;
         if argT ≠ Primitive Int then
           fail "from_expression (SeqConstruct): Argument of function was not \
                \an int"
         else
           do
             cml_len <- from_expression comp env len;
             cml_f <- from_expression comp env f_e;
             return (cml_fapp (Var (Long "List" (Short "genlist")))
                              [cml_f; cml_len])
           od
       od
   | SeqValue els _ =>
       do
         cml_els <- map_from_expression comp env els;
         return (cml_list cml_els)
       od
   | SeqUpdate se idx v collT exprT =>
       do
         idx_t <- dafny_type_of env idx;
         if collT ≠ exprT then
           fail "from_expression (SeqUpdate): Unexpectedly, collT <> exprT"
         else if idx_t ≠ Primitive Int then
           fail "from_expression (SeqUpdate): Unexpectedly, idx_t wasn't an int"
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
   | BinOp (TypedBinOp bop _ _ _) e1 e2 =>
       from_binOp comp env bop e1 e2
   | ArrayLen e _ dim _ =>
       if dim ≠ 0 then
         fail "from_expression (ArrayLen): != 1 dimension unsupported"
       else
         do
           cml_e <- from_expression comp env e;
           return (cml_fapp (Var (Long "Array" (Short "length")))
                            [cml_get_arr cml_e])
         od
   | SelectFn f_comp nam onDt isStatic _ _ =>
       (* TODO Figure out whether it is fine to ignore arguments *)
       (* TODO Figure out whether it is fine to ignore isConstant *)
       if onDt then
         fail "from_expression (SelectFn): On datatype unsupported"
       else if ¬isStatic then
         fail "from_expression (SelectFn): non-static unsupported"
       else
         do
           nam <<- Name (dest_varName nam);
           f_name <- gen_call_name comp f_comp
                                   (CallName nam NONE NONE F
                                             (CallSignature [] []));
           return (Var f_name)
         od
   | Index ce cok idxs =>
       if cok = CollKind_Seq then
         if LENGTH idxs ≠ 1 then
           fail "from_expression (Index): Unexpectedly, did not receive \
                \exactly one index"
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
             cml_args <- map_from_expression comp env args;
             return (cml_fapp (Var fun_name) cml_args)
           od
       od
   | Lambda params retT body =>
       do
         env <- add_local_env env params [] NONE;
         param <- first_param params NONE;
         param <<- if param = "" then "u" else param;
         preamble <- gen_preamble params NONE;
         (* Lambda doesn't need the epilogue used for outVars, as we expect then
            to return a single value, and hence use its own return reference. *)
         cml_e <- from_stmts comp env 0 body Unit;
         cml_e <<- handle_return cml_e;
         cml_e <- add_return_ref cml_e [normalize_type retT] NONE;
         cml_e <<- preamble cml_e;
         return (Fun param cml_e)
       od
   | Apply e args =>
       do
         cml_e <- from_expression comp env e;
         cml_args <- map_from_expression comp env args;
         return (cml_fapp cml_e cml_args)
       od
   | InitializationValue t =>
       arb_value (normalize_type t)
   | _ => fail ("from_expression: Unsupported expression")) ∧
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
      | Eq referential =>
          if referential then
            fail "from_binOp (Eq): referential unsupported"
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
      | Plus overflow =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t ∧ ¬overflow) then
            return (App (Opn Plus) [cml_e1; cml_e2])
          else
            fail "from_binOp (Plus): Unsupported types"
      | Minus overflow =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t ∧ ¬overflow) then
            return (App (Opn Minus) [cml_e1; cml_e2])
          else
            fail "from_binOp (Minus): Unsupported types"
      | Times overflow =>
          if (e1_t = (Primitive Int) ∧ e1_t = e2_t ∧ ¬overflow) then
            return (App (Opn Times) [cml_e1; cml_e2])
          else
            fail "from_binOp (Times): Unsupported types"
      | And =>
          if (e1_t = Primitive Primitive_Bool ∧ e1_t = e2_t) then
            return (Log And cml_e1 cml_e2)
          else fail "from_binOp (And): Unsupported type"
      | Or =>
          if (e1_t = Primitive Primitive_Bool ∧ e1_t = e2_t) then
            return (Log Or cml_e1 cml_e2)
          else fail "from_binOp (Or): Unsupported type"
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
  ∧
  from_stmt comp env (lvl: int) stmt (epilogue : exp) =
  (case stmt of
   | DeclareVar nam typ opt_v in_stmts =>
       do
         typ <<- normalize_type typ;
         nam_str <<- dest_varName nam;
         (* TODO Look into when/why this is NONE *)
         init_v <- (case opt_v of
                    | NONE => arb_value typ
                    | SOME init_e => from_expression comp env init_e);
         env' <<- ((local_env_name nam_str, typ)::env);
         in_e <- from_stmts comp env' lvl in_stmts epilogue;
         return (cml_ref nam_str init_v in_e)
       od
   | Assign lhs e =>
       do
         cml_rhs <- from_expression comp env e;
         case lhs of
         | AssignLhs_Ident id =>
             return (cml_ref_ass (from_varName id) cml_rhs)
         | AssignLhs_Index e' [idx] =>
             do
               cml_e' <- from_expression comp env e';
               cml_arr <<- cml_get_arr cml_e';
               cml_idx <- from_expression comp env idx;
               return (cml_fapp (Var (Long "Array" (Short "update")))
                                [cml_arr; cml_idx; cml_rhs])
             od
         | _ =>
             fail "from_stmt (Assign): Unsupported LHS"
       od
   | If cnd thn els =>
       do
         cml_cnd <- from_expression comp env cnd;
         cml_thn <- from_stmts comp env lvl thn epilogue;
         cml_els <- from_stmts comp env lvl els epilogue;
         return (If cml_cnd cml_thn cml_els)
       od
   | Labeled lbl body =>
       do
         cml_body <- from_stmts comp env lvl body epilogue;
         return (add_labeled_break_handle lbl cml_body)
       od
   | While cnd body =>
       do
         cml_cnd <- from_expression comp env cnd;
         cml_body <- from_stmts comp env (lvl + 1) body epilogue;
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
           fail "from_stmt: (Call) type arguments currently unsupported"
         else
           do
             fun_name <- gen_call_name comp on call_nam;
             cml_param_args <- map_from_expression comp env args;
             cml_out_args <<- (case outs of
                              | NONE => []
                              | SOME outs => MAP from_varName outs);
             return (cml_fapp (Var fun_name) (cml_param_args ++ cml_out_args))
           od
       od
   | Return e =>
       do
         cml_e <- from_expression comp env e;
         (* Write return value to reference, which we can later use as the
            return value of the overall function *)
         return (Let NONE (cml_ref_ass (Var (Short return_ref_name)) cml_e)
                     raise_return)
       od
   | EarlyReturn =>
       return (Let NONE epilogue raise_return)
   | Break NONE =>
     (* TODO Check if we can better test this case
        It seems that only non-deterministic while loops make use of this, while
        other break statements are transformed into labeled ones. *)
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
   | _ => fail "from_stmt: Unsupported statement")
  ∧
  from_stmts (comp: expression)
             (env: ((expression # string, type) alist))
             (lvl: int) ([]: (dafny_ast$statement list)) (epilogue : exp) =
  return Unit
  ∧
  from_stmts comp env lvl (stmt::stmts) epilogue =
  do
    e1 <- from_stmt comp env lvl stmt epilogue;
    e2 <- from_stmts comp env lvl stmts epilogue;
    return (Let NONE e1 e2)
  od
Termination
  cheat
End

Definition from_classItem_def:
  from_classItem comp env (ClassItem_Method m) : (string # string # exp) result =
  do
    (_, _, _, _, _, _, nam, _, params, _,
     body, outTypes, outVars) <<- dest_Method m;
    outTypes <<- MAP normalize_type outTypes;
    fun_name <<- dest_Name nam;
    env <- add_local_env env params outTypes outVars;
    cml_param <- first_param params outVars;
    preamble <- gen_preamble params outVars;
    epilogue <<- gen_epilogue outVars;
    cml_body <- from_stmts comp env 0 body epilogue;
    cml_body <<- handle_return cml_body;
    cml_body <- add_return_ref cml_body outTypes outVars;
    cml_body <<- preamble cml_body;
    return (fun_name, cml_param, cml_body)
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
       comp <<- Companion [enclosingModule; Ident name] [];
       env <- call_type_env_from_class_body env comp body;
       fun_defs <- result_mmap (from_classItem comp env) body;
       (* TODO Look at how PureCake detangles Dletrecs
        * Having one big Dletrec probably does not result in a performance
        * penalty unless functions are used in a higher order way *)
       return (env, [(Dletrec unknown_loc fun_defs)])
     od) ∧
  (from_classlist _ _ =
   fail "from_classlist: Unsupported item list")
End

(* Pattern matching resulting from from_module (Module nam attrs body) cannot
 * be (automatically) eliminated, hence we use dest_Module *)
Definition from_module_def:
  (from_module env m =
   let (nam, attrs, requiresExtern, body) = dest_Module m in
     case body of
   | NONE => fail "from_module: empty body unsupported"
   | SOME modItems =>
       if attrs ≠ [] then
         fail "from_module: attributes unsupported"
       else if requiresExtern then
         fail "from_module: extern unsupported"
       else if EXISTS is_moditem_trait modItems then
         fail "from_module: traits unsupported"
       else if EXISTS is_moditem_synonymtype modItems then
         fail "from_module: synonym types unsupported"
       else if EXISTS is_moditem_datatype modItems then
         fail "from_module: datatype unsupported"
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
    main_defs <<- FILTER (λ((_, n), _). n = "Main") env;
    if main_defs = [] then
      fail "find_main: Main could not be found"
    else if LENGTH main_defs > 1 then
      fail "find_main: More than one main found"
    else
      do
        ((on, nam), _) <<- HD main_defs;
        main_name <- gen_call_name (Companion [] []) on
                                   (CallName (Name nam) NONE NONE F
                                             (CallSignature [] []));
        return (Var main_name)
      od
  od
End

(* TODO Verify that _System module does not get generated anymore *)

(* Definition validate_system_module_body_def: *)
(*   (validate_system_module_body [] = return ()) ∧ *)
(*   (validate_system_module_body ((ModuleItem_Newtype *)
(*                                  (Newtype _ _ _ _ constraint _ _ _))::rest) = *)
(*    (* We essentially ignore newtypes, since we simply interpret them *)
(*       as their base type *) *)
(*    (* TODO Is that really fine? Especially considering type arguments... *) *)
(*    (* The main issue with newtype constraints is probably that we need to *)
(*     * account for them in the initialization, i.e. we cannot just initialize *)
(*     * with 0 *) *)
(*    if constraint ≠ NONE then *)
(*      fail "validate_system_module_body: constraint on newtype unsupported" *)
(*    else *)
(*      validate_system_module_body rest) ∧ *)
(*   (validate_system_module_body ((ModuleItem_Datatype *)
(*                                (Datatype nam enclosingModule *)
(*                                              _ _ _ _ _)::rest)) = *)
(*    (* Restrict datatype support to tuples *) *)
(*    if enclosingModule ≠ (Ident (Name "_System")) then *)
(*      fail "validate_system_module_body: Unsupported enclosing module" *)
(*    else *)
(*      case strip_prefix "Tuple" (dest_Name nam) of *)
(*      | NONE => fail "validate_system_module_body: Unsupported datatype name" *)
(*      | SOME sfx => do string_to_num sfx; validate_system_module_body rest od) ∧ *)
(*   (validate_system_module_body _ = *)
(*    fail "validate_system_module_body: Unsupported module item") *)
(* End *)

(* Definition validate_system_module_def: *)
(*   validate_system_module (Module nam attrs requiresExterns body) = *)
(*   if nam ≠ Name "_System" then *)
(*     fail "validate_system_module: Not module _System" *)
(*   else if attrs ≠ [] then *)
(*     fail "validate_system_module: Expected empty attribute list" *)
(*   else if requiresExterns then *)
(*     fail "validate_system_module: System module should not require externs" *)
(*   else *)
(*     case body of *)
(*     | NONE => fail "validate_system_module: Unexpectedly body was empty" *)
(*     | SOME body => validate_system_module_body body *)
(* End *)

Definition compile_def:
  compile (ms : dafny_ast$module list) : (dec list) result =
  do
    (* validate_system_module sys_mod; *)
    (env, cml_ms) <- map_from_module [] ms;
    main_id <- find_main env;
    return (^dafny_module ++
            cml_ms ++
            [Dlet unknown_loc Pany (cml_fapp main_id [Unit])])
  od
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
(* open dafny_sexpTheory *)
(* open sexp_to_dafnyTheory *)
(* open fromSexpTheory simpleSexpParseTheory *)
(* open TextIO *)
(* (* val _ = astPP.disable_astPP(); *) *)
(* val _ = astPP.enable_astPP(); *)

(* val inStream = TextIO.openIn "./tests/output/multiple_out_values.dfy.sexp" *)
(* val fileContent = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)
(* val fileContent_tm = stringSyntax.fromMLstring fileContent; *)

(* val lex_r = EVAL “(lex ^fileContent_tm)” |> concl |> rhs |> rand; *)
(* val parse_r = EVAL “(parse ^lex_r)” |> concl |> rhs |> rand; *)
(* val dafny_r = EVAL “(sexp_program ^parse_r)” |> concl |> rhs |> rand; *)

(* val cakeml_r = EVAL “(compile ^dafny_r)” |> concl |> rhs |> rand; *)

(* (* Test Dafny module *) *)
(* (* val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^dafny_module)))” *) *)
(* (*                    |> concl |> rhs |> rand; *) *)

(* val cml_sexp_r = EVAL “implode (print_sexp (listsexp (MAP decsexp  ^cakeml_r)))” *)
(*                    |> concl |> rhs |> rand; *)
(* val cml_sexp_str_r = stringSyntax.fromHOLstring cml_sexp_r; *)
(* val outFile = TextIO.openOut "./tests/output/test.cml.sexp"; *)
(* val _ = TextIO.output (outFile, cml_sexp_str_r); *)
(* val _ = TextIO.closeOut outFile; *)

val _ = export_theory();
