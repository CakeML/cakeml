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

let print_value_binding vb =
  Bad "Value bindings not supported."

let paren s = "(" ^ s ^ ")"

let fix_type_name x = x

let rec print_longident = function
  | Lident s -> return s
  | Ldot (t, s) -> print_longident t >>= fun ct ->
                   Bad "I don't know what this feature is. Please tell me."
  | Lapply (a, b) -> print_longident a >>= fun aname ->
                     print_longident b >>= fun bname ->
                     return @@ paren (aname ^ " " ^ bname)

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
    in f xs >>= fun rest ->
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
  in function
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
  | Tstr_value (_, bs) ->
    mapM (fun b -> print_value_binding b >>= fun x ->
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
