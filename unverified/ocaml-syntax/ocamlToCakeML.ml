open Batteries
open BatIO
open BatList
open BatResult
open BatResult.Monad

open Parsing
open Parsetree
open Asttypes

let rec mapM f = function
  | [] -> return []
  | x :: xs -> f x >>= fun y ->
                 mapM f xs >>= fun ys ->
                 return (y :: ys)

let print_value_binding pvb =
  ignore pvb.pvb_pat;
  Bad "Value bindings not supported."

let paren s = "(" ^ s ^ ")"

let fix_type_name x = x

let rec print_core_type ptyp =
  match ptyp.ptyp_desc with
  | Ptyp_any -> return "_"
  | Ptyp_var name -> return @@ "'" ^ fix_type_name name
  | Ptyp_arrow (l, dom, cod) ->
    print_core_type dom >>= fun a ->
    print_core_type cod >>= fun b ->
    return @@ paren ((if l = "" then l ^ ":" else "") ^ a ^ " -> " ^ b)
    (* ^^ label type changes in 4.03 ^^ *)
  | Ptyp_tuple ts -> print_ptyp_tuple ts >>= fun t ->
                     return @@ paren t
  | _ -> Bad "Some core types syntax not supported."

and print_ptyp_tuple = function
  | [] -> return ""
  | [t] -> print_core_type t
  | t :: ts -> print_core_type t >>= fun core_type ->
                 print_ptyp_tuple ts >>= fun rest ->
                 return @@ core_type ^ " * " ^ rest

let print_ptype_params = function
  | [] -> return ""
  | [(ptyp, _)] -> print_core_type ptyp >>= fun core_type ->
                   return @@ " " ^ core_type
  | xs ->
    let rec f = function
      | [] -> Bad "How did we get here?"
      | [ptyp, _] -> print_core_type ptyp >>= fun core_type ->
                       return @@ core_type ^ " )"
      | (ptyp, _) :: ys -> print_core_type ptyp >>= fun core_type ->
                           f ys >>= fun rest ->
                           return @@ core_type ^ " , " ^ rest
    in f xs >>= fun rest ->
       return @@ " ( " ^ rest

(* constructor_arguments is new (and necessary) in OCaml 4.03, in which
   support for value constructors for record types was added. *)

(*let print_constructor_arguments = function
  | Pcstr_tuple ts -> print_ptyp_tuple ts
  | Pcstr_record ds -> Bad "Record syntax not supported."*)

let print_constructor_declaration decl =
  (* Replace `print_ptyp_tuple` with `print_constructor_arguments
     in OCaml 4.03. *)
  print_ptyp_tuple decl.pcd_args >>= fun constructor_args ->
  return @@ decl.pcd_name.txt ^
    if constructor_args = "" then "" else " of " ^ constructor_args

let print_ptype_variant =
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

let print_type_declaration ptype =
  let keyword = match ptype.ptype_kind with
                | Ptype_abstract -> "type"
                | _ -> "datatype"
  in
  print_ptype_params ptype.ptype_params >>= fun params ->
  (match ptype.ptype_manifest, ptype.ptype_kind with
  | Some m, Ptype_abstract -> print_core_type m >>= fun manifest ->
                              return @@ " = " ^ manifest
  | Some m, Ptype_variant ds -> print_core_type m >>= fun manifest ->
                                return @@ " = datatype " ^ manifest
  | None, Ptype_abstract -> return ""
  | None, Ptype_variant ds -> print_ptype_variant ds >>= fun expr ->
                              return @@ " =" ^ expr
  | _ -> Bad "Type of type declaration not supported."
  ) >>= fun rest ->
  return @@ keyword ^ params ^ " " ^ fix_type_name ptype.ptype_name.txt ^ rest


let print_structure_item pstr =
  match pstr.pstr_desc with
  | Pstr_value (_, bs) ->
    mapM (fun b -> print_value_binding b >>= fun x ->
                   return (x ^ ";\n")) bs >>= fun ss ->
    return @@ fold_right (^) ss ""
  | Pstr_type ds ->
    mapM (fun d -> print_type_declaration d >>= fun x ->
                   return (x ^ ";\n")) ds >>= fun ss ->
    return @@ fold_right (^) ss ""
  | _ -> Bad "Structure feature not supported."

let print_result = function
  | Ok r -> nwrite stdout r
  | Bad e -> nwrite stdout @@ "Error: " ^ e ^ "\n"

let lexbuf = Lexing.from_channel stdin
let parsetree = Parse.implementation lexbuf
let _ = map (print_result % print_structure_item) parsetree
