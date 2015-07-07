open Batteries
open BatIO
open BatList
open BatResult
open BatResult.Monad

open Asttypes
open Longident
open Typedtree

let rec mapM f = function
  | [] -> return []
  | x :: xs -> f x >>= fun y ->
                 mapM f xs >>= fun ys ->
                 return (y :: ys)

let paren s = "(" ^ s ^ ")"

let id x = x
let ifThen x f = if x then f else id

let fix_identifier x = if startsWith "_" x then "u" ^ x else x

let fix_var_name = fix_identifier

let rec print_longident = function
  | Lident s -> return s
  | Ldot (t, s) -> print_longident t >>= fun ct ->
                   Bad "I don't know what this feature is. Please tell me."
  | Lapply (a, b) -> print_longident a >>= fun aname ->
                     print_longident b >>= fun bname ->
                     return @@ paren (aname ^ " " ^ bname)

let print_constant = function
  | Const_int x -> string_of_int x
  | Const_char x -> "#\"" ^ BatChar.escaped x ^ "\""
  | Const_string (x, y) -> "\"" ^ BatString.escaped x ^ "\""
  | Const_float x -> x
  | Const_int32 x -> BatInt32.to_string x
  | Const_int64 x -> BatInt64.to_string x
  | Const_nativeint x -> BatNativeint.to_string x


let rec print_pattern pat =
  match pat.pat_desc with
  | Tpat_any -> return "_"
  | Tpat_var (ident, name) -> return @@ fix_var_name name.txt
  | Tpat_constant c -> return @@ print_constant c
  | Tpat_tuple ps -> mapM print_pattern ps >>= fun ts ->
                     return @@ paren (BatString.concat ", " ts)
  | _ -> Bad "Some pattern syntax not implemented."

(*let fun_or_var desc = "val"*)

let rec print_expression parenth expr : (string,string) result =
  let thisParen = ifThen parenth paren in
  match expr.exp_desc with
  | Texp_ident (path, longident, desc) ->
    print_longident longident.txt
  | Texp_constant c -> return @@ print_constant c
  | Texp_let (r, bs, e) ->
    mapM (print_value_binding r) bs >>= fun bs' ->
    print_expression false e >>= fun e' ->
    return @@ thisParen @@
      "let\n" ^ BatString.concat "\n" bs' ^ "\nin\n" ^ e' ^ "\nend"
  | Texp_function (l, [c], p) ->
    print_case " => " c >>= fun c' ->
    return @@ thisParen @@ "fn " ^ c'
  | Texp_function (l, cs, p) ->
    print_case_cases cs >>= fun cs' ->
    return @@ thisParen @@
      "fn case_variable__ => case case_variable__ of" ^ cs'
  | Texp_apply (e0, es) ->
    print_expression true e0 >>= fun e0' ->
    mapM (function
    | l, Some e, Required -> print_expression true e
    | _ -> Bad "Optional and named arguments not supported."
    ) es >>= fun es' ->
    return @@ thisParen @@ e0' ^ " " ^ BatString.concat " " es'
  | Texp_match (exp, cs, _, p) -> print_expression false exp >>= fun exp' ->
                                  print_case_cases cs >>= fun cs' ->
                                  return @@ "case " ^ exp' ^ " of" ^ cs'
  | _ -> Bad "Some expression syntax not implemented."

and print_case conn c =
  case_parts c >>= fun (pat, exp) ->
  match c.c_guard with
  | None -> return @@ pat ^ conn ^ exp
  | _ -> Bad "Pattern guards not supported."

and print_case_cases = function
  | [] -> return ""
  | c :: cs -> print_case " => " c >>= fun c' ->
               print_case_cases cs >>= fun rest ->
               return @@ "\n  " ^ c' ^ rest

and case_parts c =
  print_pattern c.c_lhs >>= fun pat ->
  print_expression false c.c_rhs >>= fun exp ->
  return (pat, exp)

and print_value_binding rec_flag vb =
  print_pattern vb.vb_pat >>= fun name ->
  match vb.vb_expr.exp_desc, rec_flag with
  | Texp_function (l, cs', p), Recursive -> (
    match cs' with
    | [] -> Bad "Pattern match with no patterns."
    | c :: cs -> print_case " = " c >>= fun c' ->
                 print_fun_cases name cs >>= fun rest ->
                 return @@ "fun " ^ name ^ " " ^ c' ^ rest
    )
  | _, Recursive -> Bad "Recursive values not supported in CakeML"
  | _, Nonrecursive ->
    print_expression false vb.vb_expr >>= fun expr ->
    return @@ "val " ^ name ^ " = " ^ expr

and print_fun_cases name = function
  | [] -> return ""
  | c :: cs -> print_case " = " c >>= fun c' ->
               print_fun_cases name cs >>= fun rest ->
               return @@ "\n  | " ^ name ^ " " ^ c' ^ rest

let fix_type_name = fix_identifier

let rec print_core_type ctyp =
  match ctyp.ctyp_desc with
  | Ttyp_any -> return "_"
  | Ttyp_var name -> return @@ "'" ^ fix_type_name name
  | Ttyp_arrow (l, dom, cod) ->
    print_core_type dom >>= fun a ->
    print_core_type cod >>= fun b ->
    return @@ paren ((if l = "" then l ^ ":" else "") ^ a ^ " -> " ^ b)
    (* ^^ label type changes in 4.03 ^^ *)
  | Ttyp_tuple ts -> print_ttyp_tuple ts >>= fun t ->
                     return @@ paren t
  | Ttyp_constr (path, lid, ts) -> print_longident lid.txt >>= fun name ->
                                   return @@ name
  | _ -> Bad "Some core types syntax not supported."

and print_ttyp_tuple = function
  | [] -> return ""
  | [t] -> print_core_type t
  | t :: ts -> print_core_type t >>= fun core_type ->
                 print_ttyp_tuple ts >>= fun rest ->
                 return @@ core_type ^ " * " ^ rest

let print_typ_params = function
  | [] -> return ""
  | [(typ, _)] -> print_core_type typ >>= fun core_type ->
                   return @@ " " ^ core_type
  | xs ->
    let rec f = function
      | [] -> Bad "How did we get here?"
      | [typ, _] -> print_core_type typ >>= fun core_type ->
                       return @@ core_type ^ " )"
      | (typ, _) :: ys -> print_core_type typ >>= fun core_type ->
                           f ys >>= fun rest ->
                           return @@ core_type ^ " , " ^ rest
    in
    f xs >>= fun rest ->
    return @@ " ( " ^ rest

(* constructor_arguments is new (and necessary) in OCaml 4.03, in which
   support for value constructors for record types was added. *)

(*let print_constructor_arguments = function
  | Pcstr_tuple ts -> print_ttyp_tuple ts
  | Pcstr_record ds -> Bad "Record syntax not supported."*)

let print_constructor_declaration decl =
  (* Replace `print_ttyp_tuple` with `print_constructor_arguments
     in OCaml 4.03. *)
  print_ttyp_tuple decl.cd_args >>= fun constructor_args ->
  return @@ decl.cd_name.txt ^
    if constructor_args = "" then "" else " of " ^ constructor_args

let print_ttyp_variant =
  let rec f = function
    | [] -> return ""
    | d :: ds -> print_constructor_declaration d >>= fun constructor_decl ->
                 f ds >>= fun rest ->
                 return @@ "\n| " ^ constructor_decl ^ rest
  in
  function
    | [] -> return ""
    | d :: ds -> print_constructor_declaration d >>= fun constructor_decl ->
                 f ds >>= fun rest ->
                 return @@ "\n  " ^ constructor_decl ^ rest

let print_type_declaration typ =
  let keyword = match typ.typ_kind with
                | Ttype_abstract -> "type"
                | _ -> "datatype"
  in
  print_typ_params typ.typ_params >>= fun params ->
  (match typ.typ_manifest, typ.typ_kind with
  | Some m, Ttype_abstract -> print_core_type m >>= fun manifest ->
                              return @@ " = " ^ manifest
  | Some m, Ttype_variant ds -> print_core_type m >>= fun manifest ->
                                return @@ " = datatype " ^ manifest
  | None, Ttype_abstract -> return ""
  | None, Ttype_variant ds -> print_ttyp_variant ds >>= fun expr ->
                              return @@ " =" ^ expr
  | _ -> Bad "Type of type declaration not supported."
  ) >>= fun rest ->
  return @@ keyword ^ params ^ " " ^ fix_type_name typ.typ_name.txt ^ rest


let print_structure_item str =
  match str.str_desc with
  | Tstr_value (r, bs) ->
    mapM (fun b -> print_value_binding r b >>= fun x ->
                   return (x ^ ";\n")) bs >>= fun ss ->
    return @@ fold_right (^) ss ""
  | Tstr_type ds ->
    mapM (fun d -> print_type_declaration d >>= fun x ->
                   return (x ^ ";\n")) ds >>= fun ss ->
    return @@ fold_right (^) ss ""
  | _ -> Bad "Structure feature not supported."

let print_result = function
  | Ok r -> nwrite stdout r
  | Bad e -> nwrite stdout @@ "Error: " ^ e ^ "\n"

let lexbuf = Lexing.from_channel stdin
let parsetree = Parse.implementation lexbuf
let typedtree, signature, env =
  Typemod.type_structure Env.empty parsetree Location.none
let _ = map (print_result % print_structure_item) typedtree.str_items
