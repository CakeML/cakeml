open Batteries

open Asttypes
open Types
open Typedtree

type 'b list_context = 'b list * 'b list

type ('a, 'b) list_zipper = 'a * 'b list_context

type var_info = Ident.t * string loc

type pattern_context = {
  patctxt_desc : pattern_desc_context;
  patctxt_loc : Location.t;
  patctxt_extra : (pat_extra * Location.t * attribute list) list;
  patctxt_type : type_expr;
  mutable patctxt_env : Env.t;
  patctxt_attributes : attribute list;
}
and pattern_desc_context =
  | Tpatctxt_var
  | Tpatctxt_alias of pattern_context * Ident.t * string loc
  | Tpatctxt_tuple of (pattern_context, pattern) list_zipper
  | Tpatctxt_construct of Longident.t loc * constructor_description *
                          (pattern_context, pattern) list_zipper
  | Tpatctxt_variant of label * pattern_context * row_desc ref
  | Tpatctxt_record of
    (Longident.t loc * label_description * pattern_context,
     Longident.t loc * label_description * pattern) list_zipper * closed_flag
  | Tpatctxt_array of (pattern_context, pattern) list_zipper
  | Tpatctxt_or of pattern_context * pattern_context * row_desc option
  | Tpatctxt_lazy of pattern_context

type pattern_zipper = var_info * pattern_context

let make_pattern_context { pat_desc; pat_loc; pat_extra; pat_type; pat_env;
                           pat_attributes; } patctxt_desc = {
  patctxt_desc;
  patctxt_loc = pat_loc;
  patctxt_extra = pat_extra;
  patctxt_type = pat_type;
  patctxt_env = pat_env;
  patctxt_attributes = pat_attributes;
}

let var_eq (x, _) (y, _) = Ident.equal x y

(* zipper_find : ('a -> bool) -> 'a list -> ('a, 'a) list_zipper option *)
let zipper_find p =
  let rec inner before = function
    | [] -> None
    | x :: xs ->
      if p x then
        Some (x, (before, xs))
      else
        inner (x :: before) xs
  in
  inner []

(* Ignore the hole, and put the list back together *)
let rec patch = function
  | [], after -> after
  | x :: xs, after -> patch (xs, x :: after)

(* match_or_bindings : pattern_zipper list -> pattern_zipper list ->
                       (var_info * pattern_context * pattern_context) list *)
let rec match_or_bindings xs ys =
  match xs, ys with
  | [], [] -> []
  | (x, xctxt) :: xs, ys ->
    (match zipper_find (fun (y, _) -> var_eq x y) ys with
    | Some ((y, yctxt), ysctxt) ->
      (x, xctxt, yctxt) :: match_or_bindings xs (patch ysctxt)
    | None -> failwith "Or pattern invariant broken"
    )
  | _ -> failwith "Or pattern invariant broken"

(* pattern_desc_zippers : pattern_desc -> pattern_desc_zipper list *)
let rec pattern_desc_zippers = function
  | Tpat_any -> []
  | Tpat_var (i, n) -> [(i, n), Tpatctxt_var]
  | Tpat_alias (p, i, n) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_alias (x, i, n)) (pattern_zippers p)
  | Tpat_constant _ -> []
  | Tpat_tuple ps ->
    BatList.map (fun (v, x) -> v, Tpatctxt_tuple x) (pattern_list_zippers ps)
  | Tpat_construct (l, d, ps) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_construct (l, d, x))
                (pattern_list_zippers ps)
  | Tpat_variant (_, None, _) -> []
  | Tpat_variant (l, Some p, r) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_variant (l, x, r))
                (pattern_zippers p)
  | Tpat_record (bs, c) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_record (x, c))
                (binding_list_zippers bs)
  | Tpat_array ps ->
    BatList.map (fun (v, x) -> v, Tpatctxt_array x) (pattern_list_zippers ps)
  | Tpat_or (p, q, r) ->
    BatList.map (fun (v, x, y) -> v, Tpatctxt_or (x, y, r))
                (match_or_bindings (pattern_zippers p) (pattern_zippers q))
  | Tpat_lazy p ->
    BatList.map (fun (v, x) -> v, Tpatctxt_lazy x) (pattern_zippers p)

(* pattern_zippers : pattern -> pattern_zipper list *)
and pattern_zippers ({ pat_desc; _ } as pat) =
  let open BatTuple.Tuple2 in
  BatList.map (map2 (make_pattern_context pat))
              (pattern_desc_zippers pat_desc)

(* pattern_list_zippers :
     pattern list -> (pattern_zipper, pattern) list_zipper list *)
and pattern_list_zippers =
  let rec inner before = function
    | [] -> []
    | x :: xs ->
      BatList.map (fun z -> z, (before, xs)) (pattern_zippers x) @
      inner (x :: before) xs
  in
  inner []

(* binding_list_zippers :
     (Longident.t loc * label_description * pattern) list ->
     (Longident.t loc * label_description * pattern_zipper,
      Longident.t loc * label_description * pattern) list_zipper list *)
and binding_list_zippers =
  let rec inner before = function
    | [] -> []
    | ((l, d, p) as b) :: bs ->
      BatList.map (fun (v, x) -> (v, (l, d, x)), (before, xs))
                  (pattern_zippers p) @
      inner (b :: before) bs
  in
  inner []
