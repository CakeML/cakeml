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
  | Tpatctxt_alias of pattern
  | Tpatctxt_alias_inner of pattern_context * Ident.t * string loc
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

type pattern_desc_zipper = var_info * pattern_desc_context

type binding = Longident.t loc * label_description * pattern
type binding_context = Longident.t loc * label_description * pattern_context
type binding_zipper = var_info * binding_context

let make_pattern_context { pat_desc; pat_loc; pat_extra; pat_type; pat_env;
                           pat_attributes; } patctxt_desc = {
  patctxt_desc;
  patctxt_loc = pat_loc;
  patctxt_extra = pat_extra;
  patctxt_type = pat_type;
  patctxt_env = pat_env;
  patctxt_attributes = pat_attributes;
}

let make_pattern { patctxt_desc; patctxt_loc; patctxt_extra; patctxt_type;
                   patctxt_env; patctxt_attributes } pat_desc = {
  pat_desc;
  pat_loc = patctxt_loc;
  pat_extra = patctxt_extra;
  pat_type = patctxt_type;
  pat_env = patctxt_env;
  pat_attributes = patctxt_attributes;
}

let var_eq (x, _) (y, _) = Ident.equal x y

(* zipper_find : ('a -> bool) -> 'a list -> ('a, 'a) list_zipper option *)
let zipper_find p : 'a list -> ('a, 'a) list_zipper option =
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
let rec patch : 'a list_context -> 'a list = function
  | [], after -> after
  | x :: xs, after -> patch (xs, x :: after)

let rec match_or_bindings xs ys :
    (var_info * pattern_context * pattern_context) list =
  match xs, ys with
  | [], [] -> []
  | (x, xctxt) :: xs, ys ->
    (match zipper_find (fun (y, _) -> var_eq x y) ys with
    | Some ((y, yctxt), ysctxt) ->
      (x, xctxt, yctxt) :: match_or_bindings xs (patch ysctxt)
    | None -> failwith "Or pattern invariant broken"
    )
  | _ -> failwith "Or pattern invariant broken"

let rec pattern_zippers pattern_desc_zippers ({ pat_desc; _ } as pat)
    : pattern_zipper list =
  let open BatTuple.Tuple2 in
  BatList.map (map2 (make_pattern_context pat))
              (pattern_desc_zippers pat_desc)

and pattern_list_zippers pattern_desc_zippers (ps : pattern list) :
    (pattern_zipper, pattern) list_zipper list =
  let rec inner before = function
    | [] -> []
    | x :: xs ->
      BatList.map (fun z -> z, (before, xs))
                  (pattern_zippers pattern_desc_zippers x) @
      inner (x :: before) xs
  in
  inner [] ps

and binding_list_zippers pattern_desc_zippers (bs : binding list)
    : (binding_zipper, binding) list_zipper list =
  let rec inner before = function
    | [] -> []
    | ((l, d, p) as b) :: bs ->
      BatList.map (fun (v, x) -> (v, (l, d, x)), (before, bs))
                  (pattern_zippers pattern_desc_zippers p) @
      inner (b :: before) bs
  in
  inner [] bs

let rec varpat_desc_zippers : pattern_desc -> pattern_desc_zipper list =
  function
  | Tpat_any -> []
  | Tpat_var (i, n) -> [(i, n), Tpatctxt_var]
  | Tpat_alias (p, i, n) ->
    ((i, n), Tpatctxt_alias p) ::
    BatList.map (fun (v, x) -> v, Tpatctxt_alias_inner (x, i, n))
                (pattern_zippers varpat_desc_zippers p)
  | Tpat_constant _ -> []
  | Tpat_tuple ps ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_tuple (x, ps))
                (pattern_list_zippers varpat_desc_zippers ps)
  | Tpat_construct (l, d, ps) ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_construct (l, d, (x, ps)))
                (pattern_list_zippers varpat_desc_zippers ps)
  | Tpat_variant (_, None, _) -> []
  | Tpat_variant (l, Some p, r) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_variant (l, x, r))
                (pattern_zippers varpat_desc_zippers p)
  | Tpat_record (bs, c) ->
    BatList.map (fun ((v, x), bs) -> v, Tpatctxt_record ((x, bs), c))
                (binding_list_zippers varpat_desc_zippers bs)
  | Tpat_array ps ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_array (x, ps))
                (pattern_list_zippers varpat_desc_zippers ps)
  | Tpat_or (p, q, r) ->
    BatList.map (fun (v, x, y) -> v, Tpatctxt_or (x, y, r))
                (match_or_bindings (pattern_zippers varpat_desc_zippers p)
                                   (pattern_zippers varpat_desc_zippers q))
  | Tpat_lazy p ->
    BatList.map (fun (v, x) -> v, Tpatctxt_lazy x)
                (pattern_zippers varpat_desc_zippers p)
let varpat_zippers = pattern_zippers varpat_desc_zippers

let rec aliaspat_desc_zippers : pattern_desc -> pattern_desc_zipper list =
  function
  | Tpat_any -> []
  | Tpat_var (i, n) -> []
  | Tpat_alias (p, i, n) ->
    ((i, n), Tpatctxt_alias p) ::
    BatList.map (fun (v, x) -> v, Tpatctxt_alias_inner (x, i, n))
                (pattern_zippers aliaspat_desc_zippers p)
  | Tpat_constant _ -> []
  | Tpat_tuple ps ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_tuple (x, ps))
                (pattern_list_zippers aliaspat_desc_zippers ps)
  | Tpat_construct (l, d, ps) ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_construct (l, d, (x, ps)))
                (pattern_list_zippers aliaspat_desc_zippers ps)
  | Tpat_variant (_, None, _) -> []
  | Tpat_variant (l, Some p, r) ->
    BatList.map (fun (v, x) -> v, Tpatctxt_variant (l, x, r))
                (pattern_zippers aliaspat_desc_zippers p)
  | Tpat_record (bs, c) ->
    BatList.map (fun ((v, x), bs) -> v, Tpatctxt_record ((x, bs), c))
                (binding_list_zippers aliaspat_desc_zippers bs)
  | Tpat_array ps ->
    BatList.map (fun ((v, x), ps) -> v, Tpatctxt_array (x, ps))
                (pattern_list_zippers aliaspat_desc_zippers ps)
  | Tpat_or (p, q, r) ->
    BatList.map (fun (v, x, y) -> v, Tpatctxt_or (x, y, r))
                (match_or_bindings (pattern_zippers aliaspat_desc_zippers p)
                                   (pattern_zippers aliaspat_desc_zippers q))
  | Tpat_lazy p ->
    BatList.map (fun (v, x) -> v, Tpatctxt_lazy x)
                (pattern_zippers aliaspat_desc_zippers p)
let aliaspat_zippers = pattern_zippers aliaspat_desc_zippers

let rec pattern_of_zipper ((i, n) as v, x) =
  make_pattern x (match x.patctxt_desc with
  | Tpatctxt_var -> Tpat_var (i, n)
  | Tpatctxt_alias p -> Tpat_alias (p, i, n)
  | Tpatctxt_alias_inner (x0, i, n) ->
    Tpat_alias (pattern_of_zipper (v, x0), i, n)
  | Tpatctxt_tuple z -> Tpat_tuple (pattern_list_of_zipper v z)
  | Tpatctxt_construct (l, d, z) ->
    Tpat_construct (l, d, pattern_list_of_zipper v z)
  | Tpatctxt_variant (l, x0, r) ->
    Tpat_variant (l, Some (pattern_of_zipper (v, x0)), r)
  | Tpatctxt_record (z, c) -> Tpat_record (binding_list_of_zipper v z, c)
  | Tpatctxt_array z -> Tpat_array (pattern_list_of_zipper v z)
  | Tpatctxt_or (x0, x1, r) ->
    Tpat_or (pattern_of_zipper (v, x0), pattern_of_zipper (v, x1), r)
  | Tpatctxt_lazy x0 -> Tpat_lazy (pattern_of_zipper (v, x0))
  )
and pattern_list_of_zipper v (x, (before, after)) =
  patch (before, (pattern_of_zipper (v, x) :: after))
and binding_list_of_zipper v ((l, d, x), (before, after)) =
  patch (before, ((l, d, pattern_of_zipper (v, x)) :: after))

let rec inner_pattern_context x =
  match x.patctxt_desc with
  | Tpatctxt_var | Tpatctxt_alias _ -> x
  | Tpatctxt_alias_inner (x0, _, _)
  | Tpatctxt_tuple (x0, _)
  | Tpatctxt_construct (_, _, (x0, _))
  | Tpatctxt_variant (_, x0, _)
  | Tpatctxt_record (((_, _, x0), _), _)
  | Tpatctxt_array (x0, _)
  | Tpatctxt_or (x0, _, _)
  | Tpatctxt_lazy x0 -> inner_pattern_context x0
