open Batteries
open BatIO
open BatList
open BatResult
open BatResult.Monad

open Parsing
open Parsetree
open Asttypes

let rec mapM f xs =
  match xs with
  | [] -> return []
  | (x :: xs) -> f x >>= fun y ->
                 mapM f xs >>= fun ys ->
                 return (y :: ys)

let print_value_binding (pvb : value_binding) =
  ignore pvb.pvb_pat;
  Bad "Value bindings not supported."

let print_core_type ptyp =
  Bad "Core types not supported."

let print_ptype_params (xs : (core_type * variance) list) =
  match xs with
  | [] -> return ""
  | [(ptyp, _)] -> print_core_type ptyp
  | _ ->
    let rec f ys =
      match ys with
      | [] -> Bad "How did we get here?"
      | [(ptyp, _)] -> print_core_type ptyp >>= fun core_type ->
                       return @@ core_type ^ " )"
      | (ptyp, _) :: ys -> print_core_type ptyp >>= fun core_type ->
                           f ys >>= fun rest ->
                           return @@ core_type ^ " , " ^ rest
    in f xs >>= fun rest ->
       return @@ "( " ^ rest

let rec print_ptyp_tuple ts =
  match ts with
  | [] -> return ""
  | [t] -> print_core_type t
  | (t :: ts) -> print_core_type t >>= fun core_type ->
                 print_ptyp_tuple ts >>= fun rest ->
                 return @@ core_type ^ " * " ^ rest

let print_constructor_arguments (args : Parsetree.constructor_arguments) =
  match args with
  | Pcstr_tuple ts -> print_ptyp_tuple ts
  | Pcstr_record ds -> Bad "Record syntax not supported."

let print_constructor_declaration decl =
  print_constructor_arguments >>= fun constructor_args ->
  return @@ decl.pcd_name.txt ^ constructor_args

let print_ptype_variant ds =
  match ds with
  | [] -> return ""
  | (d :: ds) -> print_constructor_declaration >>= fun constructor_decl ->
                 print_ptype_variant ds >>= fun rest ->
                 return @@ "\n| " ^ constructor_decl ^ rest

let fix_type_name x = x

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
                              return @@ " =" ^ expr) >>= fun rest ->
  return @@ keyword ^ " " ^ params ^ " " ^ fix_type_name ptype.ptype_name.txt
                                         ^ rest


let print_structure_item pstr =
  match pstr.pstr_desc with
  | Pstr_value (_, bs) ->
    mapM (fun b -> print_value_binding b >>= fun x ->
                   return (x ^ "\n")) bs >>= fun ss ->
    return @@ fold_right (^) ss ""
  | Pstr_type ds ->
    mapM (fun d -> print_type_declaration d >>= fun x ->
                   return (x ^ "\n")) ds >>= fun ss ->
    return @@ fold_right (^) ss ""
  | _ -> Bad "Structure feature not supported."

let print_result x =
  match x with
  | Ok r -> nwrite stdout r
  | Bad e -> nwrite stdout @@ "Error: " ^ e ^ "\n"

let lexbuf = Lexing.from_channel stdin
let parsetree = Parse.implementation lexbuf
let _ = map (print_result % print_structure_item) parsetree
