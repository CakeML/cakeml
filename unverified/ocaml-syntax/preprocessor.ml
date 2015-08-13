open Batteries
open BatResult.Monad

open Asttypes
open Ident
open Path
open Types
open Typedtree
open TypedtreeMap

(* Fixes to typed AST *)

let unit_type_expr =
  {
    desc = Tconstr (Pident (Ident.create "unit"), [], ref Mnil);
    level = 0; id = 0;
  }

let unit_constr_desc =
  {
    cstr_name = "()";
    cstr_res = unit_type_expr;
    cstr_existentials = [];
    cstr_args = [];
    cstr_arity = 0;
    cstr_tag = Cstr_constant 0;
    cstr_consts = 1;
    cstr_nonconsts = 0;
    cstr_normal = 1;
    cstr_generalized = false;
    cstr_private = Public;
    cstr_loc = Location.none;
    cstr_attributes = [];
  }

(*
oldbs: accumulator for possibly modified existing bindings. Only the LHS is
  changed at this stage.
newbs: accumulator for new bindings
sub_fn: accumulator for function to substitute expressions like `x__ ()` for
  `x` in oldbs. This is applied at the base case in order to deal with mutual
  recursion.
*)
let rec vb_inner oldbs newbs sub_fn = function
  | [] -> BatList.rev_map sub_fn oldbs, BatList.rev newbs
  | vb :: vbs ->
    match vb.vb_expr.exp_desc, vb.vb_pat.pat_desc with
    (* Rephrase recursive value bindings to turn them into functions taking
       unit. *)
    | exp_desc, Tpat_var (ident, name) when
      (match exp_desc, vb.vb_pat.pat_desc with
      | Texp_function (_,_,_), _ -> false
      | _ -> true
      ) ->
      let new_name = name.txt ^ "__" in
      let new_ident = Ident.create new_name in
      let new_pat_desc = Tpat_var (new_ident, { name with txt = new_name }) in
      let new_subexpr = Texp_apply ({ vb.vb_expr with
        exp_desc = Texp_ident (Pident new_ident,
                               mknoloc (Longident.Lident new_name), {
          val_type = { vb.vb_pat.pat_type with
            desc = Tarrow ("", unit_type_expr, vb.vb_pat.pat_type, Cunknown);
          };
          val_kind = Val_reg;
          val_loc = Location.none;
          val_attributes = [];
        }); },
        [("", Some {
            exp_desc = Texp_construct (mknoloc (Longident.Lident "()"),
                                       unit_constr_desc, []);
            exp_loc = Location.none;
            exp_extra = [];
            exp_type = unit_type_expr;
            exp_env = vb.vb_expr.exp_env;
            exp_attributes = [];
          }, Required)]
      ) in

      let module MyMapArgument : MapArgument = struct
        include DefaultMapArgument
        let leave_expression expr =
          match expr.exp_desc with
          | Texp_ident (Pident ident', _, _) when ident = ident' ->
            { expr with exp_desc = new_subexpr; }
          | _ -> expr
      end in
      let module MyMap = MakeMap(MyMapArgument) in

      let vb' = { vb with
        vb_pat = { vb.vb_pat with pat_desc = new_pat_desc };
        vb_expr = { vb.vb_expr with
          exp_desc = Texp_function ("", [{
            c_lhs = {
              pat_desc = Tpat_any;
              pat_loc = Location.none;
              pat_extra = [];
              pat_type = unit_type_expr;
              pat_env = vb.vb_expr.exp_env;
              pat_attributes = [];
            };
            c_guard = None;
            c_rhs = vb.vb_expr;
          }], Total);
          exp_type = {
            desc = Tarrow ("", unit_type_expr, vb.vb_expr.exp_type, Cunknown);
            level = 0; id = 0;
          };
        };
      } in

      let sub_fn' = (fun b -> { b with
        vb_expr = MyMap.map_expression b.vb_expr }) % sub_fn in

      let newb = { vb with
        vb_expr = { vb.vb_expr with exp_desc = new_subexpr; };
      } in
      vb_inner (vb' :: oldbs) (newb :: newbs) sub_fn' vbs
    | _ -> vb_inner (vb :: oldbs) newbs sub_fn vbs

let preprocess_valrec_value_bindings = function
  (* Rephrase recursive values *)
  | Recursive -> vb_inner [] [] (fun x -> x)
  (* Split non-recursive definitions joined by `and` *)
  | Nonrecursive -> fun bs -> [], bs

let rec preprocess_match expr cs es p =
  match cs with
  | [] -> []
  | ({ c_guard = None; _ } as c) :: cs -> c :: preprocess_match expr cs es p
  (* Unroll guards into `if` expressions, where the `else` clause is a `case`
     expression containing the remaining cases. *)
  | { c_lhs; c_guard = Some g; c_rhs; } :: cs ->
    let cs' = preprocess_match expr cs es p in
    {
      c_lhs = c_lhs;
      c_guard = None;
      c_rhs = { c_rhs with
        exp_desc = Texp_ifthenelse (g, c_rhs, Some ({ c_rhs with
          exp_desc = Texp_match (expr, cs', es, p);
        }));
      };
    } :: cs'

module MatchMapArgument : MapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_match (expr, cs, es, p) ->
          Texp_match (expr, preprocess_match expr cs es p, es, p)
        | x -> x
    }
end
module MatchMap = MakeMap (MatchMapArgument)

(*let preprocess_case (c as { c_lhs; c_guard; c_rhs; }) =
  match c_lhs with
  | Tpat_alias (p, ident, s) ->
  | _ -> c

let preprocess_expression_desc = function
  | Texp_function (l, cs, p) ->
    Texp_function (l, BatList.map preprocess_case cs, p)*)

let record_cstr_name_desc bs lbl_res path =
  let cstr_name = "Mk" ^ BatString.capitalize (Path.last path) in
  (cstr_name, {
    cstr_name = cstr_name;
    cstr_res = lbl_res;
    cstr_existentials = [];
    cstr_args = BatList.map (fun (_, { lbl_arg; _ }, _) -> lbl_arg) bs;
    cstr_arity = BatList.length bs;
    cstr_tag = Cstr_block 0;
    cstr_consts = 0;
    cstr_nonconsts = 1;
    cstr_normal = 1;
    cstr_generalized = false;
    cstr_private = Public;
    cstr_loc = Location.none;
    cstr_attributes = [];
  })

(*let preprocess_record_pat_expr mkConstruct mkRecord bs =
  let (_, { lbl_res; _ }, _) = BatList.hd bs in function
  | None ->
    (match lbl_res.desc with
    (* Should be this sort of type (by construction) *)
    | Tconstr (p, _, _) ->
      let (cstr_name, cstr_desc) = record_cstr_name_desc bs lbl_res p in
      Tpat_construct (mknoloc (Longident.Lident cstr_name),
                      cstr_desc, BatList.map (fun (_, _, x) -> x) bs)
    | _ -> Tpat_record (bs, None)
    )
  | Some base -> Tpat_record (bs, Some base)*)

let complement_positions l =
  let rec inner i xs =
    if i = l then []
    else match xs with
      | [] -> i :: inner (1 + i) []
      | x :: xs ->
        if x = i then inner (1 + i) xs else i :: inner (1 + i) (x :: xs)
  in
  inner 0

(* insert_at_gaps 9 [1;0;2;6] [0;1;2;3;4] = [0;9;9;1;2;9;3;4;9] *)
let insert_at_gaps e =
  let rec inner = function
    | [] -> fun xs -> xs
    | i :: is ->
      if i = 0
        then fun xs -> e :: inner is xs
        else function
          (* Dump everything at the end *)
          | [] -> BatList.init (1 + BatList.length is) (fun _ -> e)
          | x :: xs -> x :: inner (pred i :: is) xs
  in
  inner

let gaps =
  let rec inner last = function
    | [] -> []
    | x :: xs -> (x - last) :: inner x xs
  in
  inner 0

let ref_type_ident = Ident.create "ref"

let ref_type_expr arg =
  {
    desc = Tconstr (Pident ref_type_ident, [arg], ref Mnil);
    level = 0; id = 0;
  }

let ref_cstr arg =
  {
    cstr_name = "ref";
    cstr_res = ref_type_expr arg;
    cstr_existentials = [];
    cstr_args = [arg];
    cstr_arity = 1;
    cstr_tag = Cstr_block 0;
    cstr_consts = 0;
    cstr_nonconsts = 1;
    cstr_normal = 1;
    cstr_generalized = false;
    cstr_private = Public;
    cstr_loc = Location.none;
    cstr_attributes = [];
  }

let ref_wrap_mutable_pat (_, { lbl_mut; _ }, pat) =
  match lbl_mut with
  | Immutable -> pat
  | Mutable -> {
      pat with
      pat_desc = Tpat_construct (mknoloc (Longident.Lident "ref"),
                                 ref_cstr pat.pat_type, [pat]);
      pat_type = ref_type_expr pat.pat_type;
    }

let ref_wrap_mutable_expr (_, { lbl_mut; _ }, exp) =
  match lbl_mut with
  | Immutable -> exp
  | Mutable -> {
      exp with
      exp_desc = Texp_construct (mknoloc (Longident.Lident "ref"),
                                 ref_cstr exp.exp_type, [exp]);
      exp_type = ref_type_expr exp.exp_type;
    }

let get_patterns bs =
  let filled_positions = BatList.map (fun (_, { lbl_pos }, _) -> lbl_pos) bs in
  let unfilled_positions =
    complement_positions
      (BatArray.length (let _, x, _ = BatList.hd bs in x).lbl_all)
      filled_positions
  in
  insert_at_gaps {
    pat_desc = Tpat_any;
    pat_loc = Location.none;
    pat_extra = [];
    (* Hoping no-one wants to use this type *)
    pat_type = { desc = Tnil; level = 0; id = 0; };
    pat_env = Env.empty;
    pat_attributes = [];
  } (gaps unfilled_positions) (BatList.map ref_wrap_mutable_pat bs)

let preprocess_record_pat bs closed =
  let (_, { lbl_res; _ }, _) = BatList.hd bs in
  match lbl_res.desc with
  (* Should be this sort of type (by construction) *)
  | Tconstr (p, _, _) ->
    let (cstr_name, cstr_desc) = record_cstr_name_desc bs lbl_res p in
    Tpat_construct (mknoloc (Longident.Lident cstr_name),
                    cstr_desc, get_patterns bs)
  | _ -> Tpat_record (bs, closed)

let make_with_binding base lbl =
  let lidentloc = mknoloc (Longident.Lident lbl.lbl_name) in
  (lidentloc, lbl, {
    exp_desc = Texp_field (base, lidentloc, lbl);
    exp_loc = Location.none;
    exp_extra = [];
    exp_type = lbl.lbl_arg;
    exp_env = Env.empty;
    exp_attributes = [];
  })

let rec make_with_bindings base = function
  | [] -> BatList.map (make_with_binding base)
  | ((_, blbl, _) as b) :: bs -> function
    | [] -> b :: bs
    | lbl :: lbls ->
      if blbl.lbl_name = lbl.lbl_name then
        b :: make_with_bindings base bs lbls
      else
        make_with_binding base lbl :: make_with_bindings base (b :: bs) lbls

let rec preprocess_record_expr bs =
  let (_, { lbl_res; lbl_all; _ }, _) = BatList.hd bs in function
  | None ->
    (* No `with` *)
    (match lbl_res.desc with
    (* Should be this sort of type (by construction) *)
    | Tconstr (p, _, _) ->
      let (cstr_name, cstr_desc) = record_cstr_name_desc bs lbl_res p in
      Texp_construct (mknoloc (Longident.Lident cstr_name),
                      cstr_desc, BatList.map ref_wrap_mutable_expr bs)
    | _ -> Texp_record (bs, None)
    )
  | Some base -> (*Texp_record (bs, Some base)*)
    (* Expand `with` clause, then do preprocessing *)
    let bs' = make_with_bindings base bs (BatArray.to_list lbl_all) in
    preprocess_record_expr bs' None

let mut_and = function
  | Immutable -> fun _ -> Immutable
  | Mutable -> fun x -> x

let make_record_accessor typ rr all_labels i { ld_name; ld_type; ld_mutable } =
  let type_expr = {
    desc = Tarrow ("", typ, ld_type.ctyp_type, Cunknown);
    level = 0; id = 0;
  } in
  let varname = "x" in
  let varident = Ident.create varname in
  let name = "record_" ^ ld_name.txt in
  let ident = Ident.create name in

  let make_accessor name ident make_mutable =
    {
      str_desc = Tstr_value (Recursive, [{
        vb_pat = {
          pat_desc = Tpat_var (ident, mknoloc name);
          pat_loc = Location.none;
          pat_extra = [];
          pat_type = type_expr;
          pat_env = Env.empty;
          pat_attributes = [];
        };
        vb_expr = {
          exp_desc = Texp_function ("", [{
            c_lhs = {
              pat_desc = Tpat_record (
                [mknoloc (Longident.Lident ld_name.txt),
                 {
                   lbl_name = ld_name.txt;
                   lbl_res = typ;
                   lbl_arg = ld_type.ctyp_type;
                   lbl_mut = mut_and ld_mutable make_mutable;
                   lbl_pos = i;
                   lbl_all = all_labels;
                   lbl_repres = rr;
                   lbl_private = Public;
                   lbl_loc = Location.none;
                   lbl_attributes = [];
                 },
                 {
                   pat_desc = Tpat_var (varident, mknoloc varname);
                   pat_loc = Location.none;
                   pat_extra = [];
                   pat_type = ld_type.ctyp_type;
                   pat_env = Env.empty;
                   pat_attributes = [];
                 }], Open);
              pat_loc = Location.none;
              pat_extra = [];
              pat_type = typ;
              pat_env = Env.empty;
              pat_attributes = [];
            };
            c_guard = None;
            c_rhs = {
              exp_desc = Texp_ident (
                Pident varident,
                mknoloc (Longident.Lident varname),
                {
                  val_type = ld_type.ctyp_type;
                  val_kind = Val_reg;
                  val_loc = Location.none;
                  val_attributes = [];
                }
              );
              exp_loc = Location.none;
              exp_extra = [];
              exp_type = ld_type.ctyp_type;
              exp_env = Env.empty;
              exp_attributes = [];
            };
          }], Total);
          exp_loc = Location.none;
          exp_extra = [];
          exp_type = type_expr;
          exp_env = Env.empty;
          exp_attributes = [];
        };
        vb_attributes = [];
        vb_loc = Location.none;
      }]);
      str_loc = Location.none;
      str_env = Env.empty;
    } in

  match ld_mutable with
  | Immutable -> [make_accessor name ident Immutable]
  | Mutable ->
    let setname = "recordset_" ^ ld_name.txt in
    let setident = Ident.create setname in
    [make_accessor name ident Mutable;
     make_accessor setname setident Immutable]

let ref_core_type core_type =
  { core_type with
    ctyp_desc =
      Ttyp_constr (Pident ref_type_ident,
                   mknoloc (Longident.Lident "ref"), [core_type]);
    ctyp_type = ref_type_expr core_type.ctyp_type;
  }

let get_ld_type ld =
  match ld.ld_mutable with
  | Immutable -> ld.ld_type
  | Mutable -> ref_core_type ld.ld_type

let preprocess_record_type_declaration typ =
  match typ.typ_kind, typ.typ_type.type_kind with
  (* Paraphrase record type declarations *)
  (* `lds` comes from Typedtree and `lds'` comes from Types.
     They're subtly different, and we end up needing both. *)
  | Ttype_record lds, Type_record (lds', rr) ->
    let cstr_name = "Mk" ^ BatString.capitalize typ.typ_name.txt in
    let cstr_id = Ident.create cstr_name in
    let typ' = { typ with
      (*typ_cstrs = [cstr];*)
      typ_kind = Ttype_variant [{
        cd_id = cstr_id;
        cd_name = mknoloc cstr_name;
        cd_args = BatList.map get_ld_type lds;
        cd_res = None;
        cd_loc = Location.none;
        cd_attributes = [];
      }];
    } in
    let type_expr = {
      desc = Tconstr (Path.Pident typ'.typ_id, [], ref Mnil);
      level = 0; id = 0;
    } in
    let all_labels = BatArray.of_list (BatList.mapi (fun i ld ->
      let open BatOption in
      {
        lbl_name = ld.ld_name.txt;
        lbl_res = typ.typ_type.type_manifest |? type_expr;
        lbl_arg = ld.ld_type.ctyp_type;
        lbl_mut = ld.ld_mutable;
        lbl_pos = i;
        (* Should be `all_labels`, but I don't know how to achieve that. *)
        lbl_all = [||];
        lbl_repres = rr;
        lbl_private = Public;
        lbl_loc = Location.none;
        lbl_attributes = [];
      }) lds) in
    typ', BatList.concat (BatList.mapi
      (make_record_accessor type_expr rr all_labels) lds)
  | _ -> typ, []

let rec preprocess_record_type_declarations = function
  | [] -> [], []
  | d :: ds ->
    let d', additional = preprocess_record_type_declaration d in
    let ds', additional' = preprocess_record_type_declarations ds in
    d' :: ds', additional @ additional'

let preprocess_record_str_item item =
  match item.str_desc with
  | Tstr_type ds ->
    let ds', additional = preprocess_record_type_declarations ds in
    { item with str_desc = Tstr_type ds' } :: additional
  | _ -> [item]

let rec replaceEndOfPath ident = function
  | Pident _ -> Pident ident
  | Pdot (p, _, i) -> Pdot (p, Ident.name ident, i)
  | Papply (p, q) -> Papply (p, replaceEndOfPath ident q)

let rec unlink = function
  | Tlink t -> unlink t.desc
  | t -> t

let preprocess_field_expr doset exp record_exp lidentloc lbl =
  match unlink record_exp.exp_type.desc with
  | Tconstr (p, _, _) ->
    let accessorName =
      (if doset then "recordset_" else "record_") ^ lbl.lbl_name in
    let accessorIdent = Ident.create accessorName in
    Texp_apply ({ exp with
      exp_desc = Texp_ident (
        replaceEndOfPath accessorIdent p,
        lidentloc,
        {
          val_type = {
            desc = Tarrow ("", record_exp.exp_type, exp.exp_type, Cunknown);
            level = 0; id = 0;
          };
          val_kind = Val_reg;
          val_loc = Location.none;
          val_attributes = [];
        }
      );
    }, ["", Some record_exp, Required])
  | _ -> exp.exp_desc

let pervasives_assign =
  let dash_a = { desc = Tvar (Some "a"); level = 0; id = 0; } in
  let type_expr = {
    desc = Tarrow ("", ref_type_expr dash_a, {
      desc = Tarrow ("", dash_a, unit_type_expr, Cunknown);
      level = 0; id = 0;
    }, Cunknown);
    level = 0; id = 0;
  } in
  {
    exp_desc = Texp_ident (
      Pdot (Pident (Ident.create "Pervasives"), ":=", 0),
      mknoloc (Longident.Lident ":="),
      {
        val_type = type_expr;
        val_kind = Val_reg;
        val_loc = Location.none;
        val_attributes = [];
      }
    );
    exp_loc = Location.none;
    exp_extra = [];
    exp_type = type_expr;
    exp_env = Env.empty;
    exp_attributes = [];
  }

let preprocess_setfield_expr exp record_exp lidentloc lbl val_exp =
  let bound_exp = { exp with
    exp_desc = preprocess_field_expr true exp record_exp lidentloc lbl;
    exp_type = ref_type_expr val_exp.exp_type;
  } in
  Texp_apply (pervasives_assign, ["", Some bound_exp, Required;
                                  "", Some val_exp, Required]);

module RecordMapArgument : MapArgument = struct
  include DefaultMapArgument
  let enter_pattern pat =
    { pat with
      pat_desc =
        match pat.pat_desc with
        | Tpat_record (bs, closed) -> preprocess_record_pat bs closed
        | x -> x
    }
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_record (bs, base) -> preprocess_record_expr bs base
        | Texp_field (record_exp, lidentloc, lbl) ->
          preprocess_field_expr false exp record_exp lidentloc lbl
        | Texp_setfield (record_exp, lidentloc, lbl, val_exp) ->
          preprocess_setfield_expr exp record_exp lidentloc lbl val_exp
        | _ -> exp.exp_desc
    }
  (*let enter_type_declaration = preprocess_type_declaration*)
  let enter_structure str =
    { str with
      str_items =
        BatList.concat (BatList.map preprocess_record_str_item str.str_items)
    }
end
module RecordMap = MakeMap (RecordMapArgument)

let rec preprocess_valrec_str_item str =
  match str.str_desc with
  | Tstr_value (r, bs) ->
    let oldbs, newbs = preprocess_valrec_value_bindings r bs in
    let strs = BatList.map (fun b -> { str with
      str_desc = Tstr_value (Nonrecursive, [b]);
    }) newbs in
    (match oldbs with
    (* If no existing bindings remain, remove that structure item, and just
       keep the new items. *)
    | [] -> strs
    (* Otherwise, replace the existing bindings with the updated bindings, and
       add the new items after the existing item. *)
    | _ -> { str with str_desc = Tstr_value (r, oldbs); } :: strs
    )
  | _ -> [str]
