open Batteries
open BatIO
open BatList
open BatResult
open BatResult.Monad
open BatTuple

open Asttypes
open Ident
open Longident
open Path
open Types
open Typedtree

let rec mapM f = function
  | [] -> return []
  | x :: xs -> f x >>= fun y ->
                 mapM f xs >>= fun ys ->
                 return (y :: ys)

let paren s = "(" ^ s ^ ")"

let id x = x
let ifThen x f = if x then f else id

type assoc = Neither | Left | Right
type fixity = assoc * int

let starts_with_any starts str =
  BatList.exists (fun s -> BatString.starts_with s str) starts

let fixity_of = function
  | x when BatString.starts_with "!" x
        || (BatString.length x >= 2 && starts_with_any ["?"; "~"] x) ->
    Neither, 0
  | "." | ".(" | ".[" | ".{" -> Neither, 1
  | "#" -> Neither, 2
  | " " -> Left, 3
  | "-" | "-." -> Neither, 4
  | "lsl" | "lsr" | "asr" -> Right, 5
  | x when BatString.starts_with "**" x -> Right, 5
  | "mod" | "land" | "lor" | "lxor" -> Left, 6
  | x when starts_with_any ["*"; "/"; "%"] x -> Left, 6
  | x when starts_with_any ["+"; "-"] x -> Left, 7
  | "::" -> Right, 8
  | x when starts_with_any ["@"; "^"] x -> Right, 9
  | "!=" -> Left, 10
  | x when starts_with_any ["="; "<"; ">"; "|"; "&"; "$"] x -> Left, 10
  | "&" | "&&" -> Right, 11
  | "||" | "or" -> Right, 12
  | "," -> Neither, 13
  | "<-" | ":=" -> Right, 14
  | "if" -> Neither, 15
  | ";" -> Right, 16
  | "let" | "match" | "fun" | "function" | "try" -> Neither, 17
  | _ -> Neither, ~-1

let fix_identifier = function
  | ("abstype" | "andalso" | "case" | "datatype" | "eqtype" | "fn" | "handle"
    | "infix" | "infixr" | "local" | "nonfix" | "op" | "orelse" | "raise"
    | "sharing" | "signature" | "structure" | "where" | "withtype") as x ->
    x ^ "__"
  | x when BatString.starts_with "_" x -> "u" ^ x
  | x when
    (match fixity_of x with
    | Neither, _ -> false
    | _ -> true
    ) -> "op" ^ x
  | x -> x

let fix_var_name = fix_identifier

let rec print_longident = function
  | Lident s -> return @@ fix_identifier s
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

(* Works in both patterns and expressions. `f` is the function that prints
   subpatterns/subexpressions. *)
let print_construct parenth (f : bool -> 'a -> (string, string) result) lident cstr (xs : 'a list) =
  (match xs with
  | [] -> return ""
  | [x] -> f true x >>= fun x' ->
           return @@ " " ^ x'
  | _ -> mapM (f false) xs >>= fun xs' ->
         return @@ " (" ^ BatString.concat ", " xs' ^ ")"
  ) >>= fun args ->
  return @@ ifThen (parenth && not ([] = xs)) paren @@ cstr.cstr_name ^ args

let rec print_pattern parenth pat =
  let thisParen = ifThen parenth paren in
  match pat.pat_desc with
  | Tpat_any -> return "_"
  | Tpat_var (ident, name) -> return @@ fix_var_name name.txt
  | Tpat_constant c -> return @@ print_constant c
  | Tpat_tuple ps -> mapM (print_pattern false) ps >>= fun ps' ->
                     return @@ thisParen @@ BatString.concat ", " ps'
  | Tpat_construct (lident, desc, ps) ->
    print_construct parenth print_pattern lident desc ps
  | _ -> Bad "Some pattern syntax not implemented."

let rec convertPervasive : string -> string =
  let rec f : char list -> string list = function
    | [] -> []

    | '=' :: xs -> "equals" :: f xs
    | '<' :: xs -> "lt" :: f xs
    | '>' :: xs -> "gt" :: f xs

    | '&' :: xs -> "amp" :: f xs
    | '|' :: xs -> "bar" :: f xs

    | '@' :: xs -> "at" :: f xs

    | '~' :: xs -> "tilde" :: f xs
    | '+' :: xs -> "plus" :: f xs
    | '-' :: xs -> "minus" :: f xs
    | '*' :: xs -> "star" :: f xs
    | '/' :: xs -> "slash" :: f xs

    | xs -> [BatString.of_list xs]
  in
  BatString.concat "_" % f % BatString.to_list

let fix_path_name = fix_identifier

let rec print_path = function
  | Pident ident -> return @@ ident.name
  | Pdot (left, right, _) ->
    print_path left >>= fun left ->
    let right = ifThen (left = "Pervasives") convertPervasive right in
    return @@ fix_path_name left ^ "." ^ right
  | Papply (p0, p1) -> print_path p0 >>= fun p0 ->
                       print_path p1 >>= fun p1 ->
                       return @@ p0 ^ " " ^ p1

let rec print_expression indent parenth expr =
  let thisParen = ifThen parenth paren in
  match expr.exp_desc with
  | Texp_ident (path, longident, desc) -> print_path path
  | Texp_constant c -> return @@ print_constant c
  | Texp_let (r, bs, e) ->
    mapM (fun b -> print_value_binding (indent + 1) r b >>= fun b' ->
                   return @@ BatString.repeat "  " (indent + 1))
         bs >>= fun bs' ->
    print_expression (indent + 1) false e >>= fun e' ->
    return @@ thisParen @@
      "let" ^
      BatString.concat "" bs' ^ "\n" ^
      BatString.repeat "  " indent ^ "in\n" ^
      BatString.repeat "  " (indent + 1) ^ e' ^ "\n" ^
      BatString.repeat "  " indent ^ "end"
  | Texp_function (l, [c], p) ->
    print_case (indent + 1) true " => " c >>= fun c' ->
    return @@ thisParen @@ "fn " ^ c'
  | Texp_function (l, cs, p) ->
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@ thisParen @@ "fn tmp__ => case tmp__ of" ^ cs'
  | Texp_apply ({
      exp_desc = Texp_ident (Pdot (Pident m, n, _), _, _)
    }, [(_, Some e0, _); (_, Some e1, _)])
      when m.name = "Pervasives" && mem n ["&&"; "&"; "||"; "or"] ->
    let op = match n with
      | "&&" |  "&" -> "andalso"
      | "||" |  "or" -> "orelse"
      | x -> x
    in
    print_expression indent true e0 >>= fun e0' ->
    print_expression indent true e1 >>= fun e1' ->
    return @@ e0' ^ " " ^ op ^ " " ^ e1'
  | Texp_apply (e0, es) ->
    print_expression indent true e0 >>= fun e0' ->
    mapM (function
    | l, Some e, Required -> print_expression indent true e
    | _ -> Bad "Optional and named arguments not supported."
    ) es >>= fun es' ->
    return @@ thisParen @@ e0' ^ " " ^ BatString.concat " " es'
  | Texp_match (exp, cs, [], p) ->
    print_expression indent false exp >>= fun exp' ->
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@ "case " ^ exp' ^ " of" ^ cs'
  | Texp_match (_, _, _, _) -> Bad "Exception cases not supported."
  | Texp_try (exp, cs) ->
    print_expression indent true exp >>= fun exp' ->
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@ exp' ^ " handle" ^ cs'
  | Texp_tuple es -> mapM (print_expression indent false) es >>= fun es' ->
                     return @@ thisParen @@ BatString.concat ", " es'
  | Texp_construct (lident, desc, es) ->
    print_construct parenth (print_expression indent) lident desc es
  | Texp_ifthenelse (p, et, Some ef) ->
    print_expression indent false p >>= fun p' ->
    print_expression (indent + 1) false et >>= fun et' ->
    print_expression (indent + 1) false ef >>= fun ef' ->
    return @@ thisParen @@
      "if " ^ p' ^ " then\n" ^
      BatString.repeat "  " (indent + 1) ^ et' ^ "\n" ^
      BatString.repeat "  " indent ^ "else\n" ^
      BatString.repeat "  " (indent + 1) ^ ef'
  | Texp_sequence (e0, e1) ->
    print_expression indent false e0 >>= fun e0' ->
    print_expression indent false e1 >>= fun e1' ->
    return @@ paren @@ e0' ^ ";\n" ^ BatString.repeat "  " indent ^ e1'
  | _ -> Bad "Some expression syntax not implemented."

and print_case indent parenthPat conn c =
  case_parts indent parenthPat c >>= fun (pat, exp) ->
  match c.c_guard with
  | None -> return @@ pat ^ conn ^ exp
  | _ -> Bad "Pattern guards not supported."

and print_case_cases indent =
  let rec f = function
  | [] -> return ""
  | c :: cs ->
    print_case indent false " => " c >>= fun c' ->
    f cs >>= fun rest ->
    return @@ "\n" ^ BatString.repeat "  " indent ^ "| " ^ c' ^ rest
  in function
  | [] -> return ""
  | c :: cs ->
    print_case indent false " => " c >>= fun c' ->
    f cs >>= fun rest ->
    return @@ "\n" ^ BatString.repeat "  " indent ^ "  " ^ c' ^ rest

and case_parts indent parenthPat c =
  print_pattern parenthPat c.c_lhs >>= fun pat ->
  print_expression (indent + 1) false c.c_rhs >>= fun exp ->
  return (pat, exp)

and print_value_binding indent rec_flag vb =
  print_pattern false vb.vb_pat >>= fun name ->
  match vb.vb_expr.exp_desc, rec_flag with
  (* Special case for trivial patterns *)
  | Texp_function (l, [c], p), Recursive when
      (match c.c_lhs.pat_desc, c.c_guard with
      | Tpat_var (_,_), None -> true
      | _ -> false
      ) ->
    print_case (indent + 1) true " = " c >>= fun c' ->
    return @@ BatString.repeat "  " indent ^ "fun " ^ name ^ " " ^ c'
  | Texp_function (l, cs, p), Recursive -> (*print_fun_cases name cs*)
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@ BatString.repeat "  " indent ^
              "fun " ^ name ^ " tmp__ = case tmp__ of" ^ cs'
  | _, Recursive -> Bad "Recursive values not supported in CakeML"
  | _, Nonrecursive ->
    print_expression indent false vb.vb_expr >>= fun expr ->
    return @@ BatString.repeat "  " indent ^ "val " ^ name ^ " = " ^ expr

(* CakeML doesn't support SML-style LHS pattern matching in function
   definitions *)
(*and print_fun_cases name =
  let rec f name = function
  | [] -> return ""
  | c :: cs -> print_case true " = " c >>= fun c' ->
               f name cs >>= fun rest ->
               return @@ "\n  | " ^ name ^ " " ^ c' ^ rest
  in function
  | [] -> Bad "Pattern match with no patterns."
  | c :: cs -> print_case true " = " c >>= fun c' ->
               f name cs >>= fun rest ->
               return @@ "fun " ^ name ^ " " ^ c' ^ rest*)

let fix_type_name = fix_identifier

let rec print_core_type parenth ctyp =
  let thisParen = ifThen parenth paren in
  match ctyp.ctyp_desc with
  | Ttyp_any -> return "_"
  | Ttyp_var name -> return @@ "'" ^ fix_type_name name
  | Ttyp_arrow (l, dom, cod) ->
    print_core_type true dom >>= fun a ->
    print_core_type false cod >>= fun b ->
    return @@ thisParen @@ (if l = "" then "" else l ^ ":") ^ a ^ " -> " ^ b
    (* ^^ label type changes in 4.03 ^^ *)
  | Ttyp_tuple ts -> print_ttyp_tuple ts >>= fun t ->
                     return @@ paren t
  | Ttyp_constr (path, lid, ts) ->
    print_path path >>= fun name ->
    print_typ_params ts >>= fun params ->
    return @@ params ^ name
  | _ -> Bad "Some core types syntax not supported."

and print_typ_params = function
  | [] -> return ""
  | [t] -> print_core_type true t >>= fun t' ->
           return @@ t' ^ " "
  | ts -> mapM (print_core_type false) ts >>= fun ts' ->
         return @@ "(" ^ BatString.concat ", " ts' ^ ") "

and print_ttyp_tuple = function
  | [] -> return ""
  | [t] -> print_core_type false t
  | t :: ts -> print_core_type false t >>= fun core_type ->
                 print_ttyp_tuple ts >>= fun rest ->
                 return @@ core_type ^ " * " ^ rest

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

let print_ttyp_variant indent =
  let rec f = function
    | [] -> return ""
    | d :: ds -> print_constructor_declaration d >>= fun constructor_decl ->
                 f ds >>= fun rest ->
                 return @@ "\n" ^ BatString.repeat "  " indent ^ "| " ^
                           constructor_decl ^ rest
  in
  function
    | [] -> return ""
    | d :: ds -> print_constructor_declaration d >>= fun constructor_decl ->
                 f ds >>= fun rest ->
                 return @@ "\n" ^ BatString.repeat "  " indent ^ "  " ^
                           constructor_decl ^ rest

let print_type_declaration indent typ =
  let keyword = match typ.typ_kind with
                | Ttype_abstract -> "type"
                | _ -> "datatype"
  in
  print_typ_params (map Tuple2.first typ.typ_params) >>= fun params ->
  (match typ.typ_manifest, typ.typ_kind with
  | Some m, Ttype_abstract -> print_core_type false m >>= fun manifest ->
                              return @@ " = " ^ manifest
  | Some m, Ttype_variant ds -> print_core_type false m >>= fun manifest ->
                                return @@ " = datatype " ^ manifest
  | None, Ttype_abstract -> return ""
  | None, Ttype_variant ds ->
    print_ttyp_variant (indent + 1) ds >>= fun expr ->
    return @@ " =" ^ expr
  | _ -> Bad "Some type declarations not implemented."
  ) >>= fun rest ->
  return @@ BatString.repeat "  " indent ^ keyword ^ " " ^ params ^
            fix_type_name typ.typ_name.txt ^ rest

let rec print_module_expr indent expr =
  match expr.mod_desc with
  | Tmod_structure str ->
    mapM (print_structure_item (indent + 1)) str.str_items >>= fun items ->
    return @@ "struct\n" ^ fold_right (^) items "end"
  | _ -> Bad "Some module types not implemented."

and print_module_binding indent mb =
  print_module_expr indent mb.mb_expr >>= fun expr ->
  let name = mb.mb_id.name in
  match mb.mb_expr.mod_desc with
  | Tmod_structure str ->
    return @@
      BatString.repeat "  " indent ^ "structure " ^ name ^ " = " ^ expr
  | _ -> Bad "Some module types not implemented."

and print_structure_item indent str =
  match str.str_desc with
  | Tstr_eval (e, attrs) ->
    print_expression indent false e >>= fun e' ->
    return @@ BatString.repeat "  " indent ^ e' ^ ";\n"
  | Tstr_value (r, bs) ->
    mapM (fun b -> print_value_binding indent r b >>= fun x ->
                   return (x ^ ";\n")) bs >>= fun ss ->
    return @@ fold_right (^) ss ""
  | Tstr_type ds ->
    mapM (fun d -> print_type_declaration indent d >>= fun x ->
                   return (x ^ ";\n")) ds >>= fun ss ->
    return @@ fold_right (^) ss ""
  | Tstr_module b ->
    print_module_binding indent b >>= fun b' ->
    return @@ b' ^ ";\n"
  | _ -> Bad "Some structure items not implemented."

let output_result = function
  | Ok r -> nwrite stdout r
  | Bad e -> nwrite stdout @@ "Error: " ^ e ^ "\n"

let rec preprocess_structure_item str =
  match str.str_desc with
  | Tstr_value (r, bs) ->
    { str with str_desc = Tstr_value (r, preprocess_value_bindings [] r bs) }
  | _ -> str
and preprocess_value_bindings acc rec_flag = function
  | [] -> acc
  | vb :: vbs ->
    match vb.vb_expr.exp_desc, vb.vb_pat.pat_desc, rec_flag with
    (* This is fairly tricky; commenting out for now *)
    (*| exp_desc, Tpat_var (ident, name), Recursive when
      (match desc, vb.vb_pat.pat_desc with
      | Texp_function (_,_,_), _ -> false
      | _ -> true
      ) -> let new_name = name.txt ^ "__" in
           let new_ident = create new_name in
           let new_pat = Tpat_var (new_ident, { name with txt = new_name }) in
           let new_subexpr = Texp_apply (
             Texp_ident (Pident new_ident, Lident new_name,
                         { val_type = { vb.vb_pat.pat_type with
                                        desc = Tarrow (l, u, vb.vb_pat.pat_type, Cok) };
                           val_kind = Val_reg;
                           val_loc = ;
                           val_attributes = ;
                         }),
             []) in
           vb' :: preprocess_value_bindings acc' rec_flag vbs*)
    | _ -> vb :: preprocess_value_bindings acc rec_flag vbs

let lexbuf = Lexing.from_channel stdin
let parsetree = Parse.implementation lexbuf
let _ = Compmisc.init_path false
let typedtree, signature, env =
  Typemod.type_structure (Compmisc.initial_env ()) parsetree Location.none
let _ = map (output_result % print_structure_item 0) typedtree.str_items
