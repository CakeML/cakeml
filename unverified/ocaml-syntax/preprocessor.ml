open Batteries

open Asttypes
open Ident
open Path
open Types
open Typedtree
open TypedtreeMap

open PatternZipper

(* Monadic notation for lists (nondeterminism) *)
let ( <$> ) = BatList.map
let pure x = [x]
let ( <*> ) fs xs = BatList.concat (BatList.map (fun f -> f <$> xs) fs)
let ( >>= ) xs f = BatList.concat (BatList.map f xs)

let ( <&> ) xs fs = fs <$> xs
let rec mapM f = function
  | [] -> pure []
  | m :: ms -> f m >>= fun y ->
               mapM f ms >>= fun ys ->
               pure (y :: ys)

(* Fixes to typed AST *)

(* Counter for new variable names *)
module type StampRef = sig
  val v : int ref
end

let create_ident current_stamp name =
  current_stamp := !current_stamp + 1;
  { stamp = !current_stamp; name = name; flags = 0; }

(* Stock OCaml entities *)

(* unit *)
let unit_type_expr =
  {
    desc = Tconstr (Pident (Ident.create "unit"), [], ref Mnil);
    level = 0; id = 0;
  }

(* () *)
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

let bool_type_expr = {
  desc = Tconstr (Pident (Ident.create "bool"), [], ref Mnil);
  level = 0; id = 0;
}

let int_type_expr = {
  desc = Tconstr (Pident (Ident.create "int"), [], ref Mnil);
  level = 0; id = 0;
}

let var_type_expr = { desc = Tvar None; level = 0; id = 0; }

let pervasives_path = Pident (Ident.create "Pervasives")

(* Remove `when` guards
match x with       \->  match x with
| P0 -> E0         |->  | P0 -> E0
| P1 when p -> E1  |->  | P1 -> if p then E1
| P2 -> E2         |->               else (match x with
| _ -> E3          |->                    | P2 -> E2
                   |->                    | _ -> E3
                   |->                    )
                   |->  | P2 -> E2
                   /->  | _ -> E3
*)

let rec preprocess_guard_match expr cs es p =
  match cs with
  | [] -> []
  | ({ c_guard = None; _ } as c) :: cs ->
    c :: preprocess_guard_match expr cs es p
  (* Unroll guards into `if` expressions, where the `else` clause is a `case`
     expression containing the remaining cases. *)
  | { c_lhs; c_guard = Some g; c_rhs; } :: cs ->
    let cs' = preprocess_guard_match expr cs es p in
    {
      c_lhs = c_lhs;
      c_guard = None;
      c_rhs = { c_rhs with
        exp_desc = Texp_ifthenelse (g, c_rhs, Some ({ c_rhs with
          exp_desc = Texp_match (expr, cs', es, p);
        }));
      };
    } :: cs'

module GuardMapArgument : MapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_match (expr, cs, es, p) ->
          Texp_match (expr, preprocess_guard_match expr cs es p, es, p)
        | x -> x
    }
end
module GuardMap = MakeMap (GuardMapArgument)

(* Convert records into normal ADTs with accessor functions

type foo = { bar : int; mutable quux : string; }

let f { quux = x; _ } = { quux = x; bar = 0; }

let g x = x.quux <- "newstring"

||||||||||||||||||||||||||||||||||||||||||||||||
VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

type foo = MkFoo of int * string
let record_bar (MkFoo (x, _)) = x
let record_quux (MkFoo (_, ref x)) = x
let recordset_quux (MkFoo (_, x)) = x

let f (MkFoo (_, x)) = MkFoo (0, x)

let g x = recordset_quux x := "newstring"
*)

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

(* complement_positions 7 [2;3;5] = [0;1;4;6] *)
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

(* gaps [0;3;4;8] =
         [3;1;4]
   Difference between adjacent items
*)
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

(* Rewriting non-function recursive definitions

let rec zeros = Cons (fun _ -> 0, zeros)

|||||||||||||||||||||||||||||||||||||||||||||||||
VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

let rec zeros__ _ = Cons (fun _ -> 0, zeros__ ())
let zeros = zeros__ ()
*)

(*
oldbs: accumulator for possibly modified existing bindings. Only the LHS is
  changed at this stage.
newbs: accumulator for new bindings
sub_fn: accumulator for function to substitute expressions like `x__ ()` for
  `x` in oldbs. This is applied at the base case in order to deal with mutual
  recursion.
*)
let rec vb_inner oldbs newbs sub_fn current_stamp = function
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
      let new_name = name.txt ^ "_" ^ BatString.of_int !current_stamp in
      let new_ident = create_ident current_stamp new_name in
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
      vb_inner (vb' :: oldbs) (newb :: newbs) sub_fn' current_stamp vbs
    | _ -> vb_inner (vb :: oldbs) newbs sub_fn current_stamp vbs

let preprocess_valrec_value_bindings = vb_inner [] [] (fun x -> x)

let preprocess_valrec_expr current_stamp exp =
  match exp.exp_desc with
  | Texp_let (Recursive, bs, e) ->
    let oldbs, newbs = preprocess_valrec_value_bindings current_stamp bs in
    (if oldbs = [] then
      fun inner -> inner
    else
      fun inner -> { exp with exp_desc = Texp_let (Recursive, oldbs, inner); }
    ) { exp with exp_desc = Texp_let (Nonrecursive, newbs, e) }
  | _ -> exp

let rec preprocess_valrec_str_item current_stamp str =
  match str.str_desc with
  | Tstr_value (Recursive, bs) ->
    let oldbs, newbs = preprocess_valrec_value_bindings current_stamp bs in
    let strs = BatList.map (fun b -> { str with
      str_desc = Tstr_value (Nonrecursive, [b]);
    }) newbs in
    (match oldbs with
    (* If no existing bindings remain, remove that structure item, and just
       keep the new items. *)
    | [] -> strs
    (* Otherwise, replace the existing bindings with the updated bindings, and
       add the new items after the existing item. *)
    | _ -> { str with str_desc = Tstr_value (Recursive, oldbs); } :: strs
    )
  | _ -> [str]

module ValrecMapArgument (CurrentStamp : StampRef) = struct
  include DefaultMapArgument
  let enter_structure ({ str_items; _ } as str) =
    { str with
      str_items = BatList.concat (BatList.map
        (preprocess_valrec_str_item CurrentStamp.v) str_items);
    }
  let enter_expression = preprocess_valrec_expr CurrentStamp.v
end
module ValrecMap (S : StampRef) = MakeMap (ValrecMapArgument (S))

(* Rewrite pattern matching definitions

let x, y = 0, 2  \->  let tmp__ = 0, 2
                 |->  let x = match tmp__ with x, _ -> x
                 /->  let y = match tmp__ with _, y -> y
*)

let vb_from_zipper basevb tmpident (((i, n), patctxt) as z) =
  { basevb with
    vb_pat = { basevb.vb_pat with
      pat_desc = Tpat_var (i, n);
      pat_type = patctxt.patctxt_type;
    };
    vb_expr = { basevb.vb_expr with
      exp_desc = Texp_match ({
        exp_desc =
          Texp_ident (Pident tmpident,
                      mknoloc (Longident.Lident tmpident.name), {
            val_type = patctxt.patctxt_type;
            val_kind = Val_reg;
            val_loc = Location.none;
            val_attributes = [];
          });
        exp_loc = Location.none;
        exp_extra = [];
        exp_type = basevb.vb_expr.exp_type;
        exp_env = Env.empty;
        exp_attributes = [];
      }, [{
        c_lhs = pattern_of_zipper z;
        c_guard = None;
        c_rhs =
          let t = (inner_pattern_context patctxt).patctxt_type in
          {
            exp_desc = Texp_ident (Pident i,
                                   mknoloc (Longident.Lident n.txt), {
              val_type = t;
              val_kind = Val_reg;
              val_loc = Location.none;
              val_attributes = [];
            });
            exp_loc = Location.none;
            exp_extra = [];
            exp_type = t;
            exp_env = Env.empty;
            exp_attributes = [];
          };
      }], [], Partial);
      exp_type = patctxt.patctxt_type;
    };
  }

let preprocess_valpat_value_binding vb =
  match vb.vb_pat.pat_desc with
  | Tpat_any | Tpat_var _ -> [vb]
  | _ ->
    let tmpname = "tmp__" in
    let tmpnameloc = mkloc tmpname vb.vb_pat.pat_loc in
    let tmpident = Ident.create tmpname in
    let vb' = { vb with
      vb_pat = { vb.vb_pat with pat_desc = Tpat_var (tmpident, tmpnameloc); };
    } in
    let zs = varpat_zippers vb.vb_pat in
    let vbs = BatList.map (vb_from_zipper vb tmpident) zs in
    vb' :: vbs

let preprocess_valpat_value_bindings =
  BatList.concat % BatList.map preprocess_valpat_value_binding

let preprocess_valpat_expr exp =
  match exp.exp_desc with
  | Texp_let (r, bs, e) ->
    let bs' = preprocess_valpat_value_bindings bs in
    { exp with exp_desc = Texp_let (r, bs', e); }
  | _ -> exp

let preprocess_valpat_str_item str =
  match str.str_desc with
  | Tstr_value (Nonrecursive, bs) ->
    let bs' = preprocess_valpat_value_bindings bs in
    BatList.map (fun b -> { str with
      str_desc = Tstr_value (Nonrecursive, [b]);
    }) bs'
  | _ -> [str]

module ValpatMapArgument = struct
  include DefaultMapArgument
  let enter_structure ({ str_items; _ } as str) =
    { str with
      str_items =
        BatList.concat (BatList.map preprocess_valpat_str_item str_items);
    }
  let enter_expression = preprocess_valpat_expr
end
module ValpatMap = MakeMap (ValpatMapArgument)

(* Replace `_` in patterns with variables. Helps when rewriting `as` patterns

let const x _ = x  >->  let const x unused_1012 = x
*)

let map_tails f =
  let rec inner xs =
    f xs :: match xs with | [] -> [] | _ :: xs -> inner xs
  in
  inner

let rec first_some = function
  | [] -> None
  | None :: xs -> first_some xs
  | (Some _ as x) :: _ -> x

let map_option2 f x y =
  match x, y with
  | Some x, Some y -> Some (f x y)
  | _ -> None

let digits = ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9']
let int_of_charlist = BatList.fold_left (fun acc x ->
  map_option2 (fun acc x -> 10 * acc + x) acc (BatList.index_of x digits))
  (Some 0)
let number_suffix =
  let f = function
    | '_' :: xs -> int_of_charlist xs
    | _ -> None
  in
  first_some % map_tails f % BatString.to_list

let largest_stamp env =
  let open Env in
  let rec inner acc = function
    | Env_empty -> acc
    | Env_value (summary, { stamp; name; }, _)
    | Env_type (summary, { stamp; name; }, _)
    | Env_extension (summary, { stamp; name; }, _)
    | Env_module (summary, { stamp; name; }, _)
    | Env_modtype (summary, { stamp; name; }, _)
    | Env_class (summary, { stamp; name; }, _)
    | Env_cltype (summary, { stamp; name; }, _)
    | Env_functor_arg (summary, { stamp; name; }) ->
      let new_number =
        match number_suffix name with
        | None -> stamp
        | Some n -> max n stamp
      in
      inner (max acc new_number) summary
    | Env_open (summary, _) -> inner acc summary
  in
  inner 0 (summary env)

let create_unused_var current_stamp =
  let name = "unused_" ^ BatString.of_int !current_stamp in
  Tpat_var (create_ident current_stamp name, mknoloc name)

module AnypatMapArgument (CurrentStamp : StampRef) = struct
  include DefaultMapArgument
  let enter_pattern pat =
    match pat.pat_desc with
    | Tpat_any -> { pat with pat_desc = create_unused_var CurrentStamp.v }
    | _ -> pat
end
module AnypatMap (S : StampRef) = MakeMap (AnypatMapArgument (S))

let rec get_aliaspats pat : (pattern * Ident.t * string loc) list =
  match pat.pat_desc with
  | Tpat_any | Tpat_var _ | Tpat_constant _ | Tpat_variant (_, None, _) -> []
  | Tpat_alias (p, i, l) -> (p, i, l) :: get_aliaspats p
  | Tpat_tuple ps | Tpat_construct (_, _, ps) | Tpat_array ps ->
    BatList.concat (BatList.map get_aliaspats ps)
  | Tpat_variant (_, Some p, _) | Tpat_or (p, _, _) | Tpat_lazy p ->
    get_aliaspats p
  | Tpat_record (ls, c) ->
    BatList.concat (BatList.map (fun (_, _, p) -> get_aliaspats p) ls)

(* Turn `as` patterns into non-`as` patterns, with a `let` expression in the
   corresponding expression

let rec f = function           \->  let rec f = function
  | [] -> []                   |->    | [] -> []
  | [x] as xs -> xs            |->    | [x] -> let xs = [x] in xs
  | x :: y :: xs -> x :: f xs  /->    | x :: y :: xs -> x :: f xs
*)

(* This module is used selectively, despite looking like the other modules *)
module RemoveAliaspatMapArgument = struct
  include DefaultMapArgument
  let enter_pattern pat =
    match pat.pat_desc with
    | Tpat_alias (p, _, _) -> p
    | _ -> pat
end
module RemoveAliaspatMap = MakeMap (RemoveAliaspatMapArgument)

let rec expression_of_pattern
  { pat_desc; pat_loc; pat_extra; pat_type; pat_env; pat_attributes } =
  match pat_desc with
  | Tpat_alias (p, _, _) | Tpat_or (p, _, _) -> expression_of_pattern p
  | _ -> {
    exp_desc = (match pat_desc with
      | Tpat_var (i, l) ->
        Texp_ident (Pident i, mkloc (Longident.Lident l.txt) l.loc, {
          val_type = pat_type;
          val_kind = Val_reg;
          val_loc = Location.none;
          val_attributes = [];
        })
      | Tpat_constant c -> Texp_constant c
      | Tpat_tuple ps -> Texp_tuple (BatList.map expression_of_pattern ps)
      | Tpat_construct (l, cd, ps) ->
        Texp_construct (l, cd, BatList.map expression_of_pattern ps)
      | Tpat_variant (l, p, r) ->
        Texp_variant (l, BatOption.map expression_of_pattern p)
      | Tpat_record (ls, Closed) ->
        Texp_record
          (BatList.map (BatTuple.Tuple3.map3 expression_of_pattern) ls, None)
      | Tpat_record (ls, Open) -> failwith "`_` not removed"
      | Tpat_array ps -> Texp_array (BatList.map expression_of_pattern ps)
      | Tpat_lazy p -> Texp_lazy (expression_of_pattern p)
      | Tpat_any -> failwith "`_` should have been removed"
      | Tpat_alias _ | Tpat_or _ ->
        failwith "Should have been guarded against above"
      );
    exp_loc = pat_loc;
    exp_extra = [];
    exp_type = pat_type;
    exp_env = pat_env;
    exp_attributes = pat_attributes;
  }

let value_binding_of_alias_pattern (pat, i, l) = {
  vb_pat = {
    pat_desc = Tpat_var (i, l);
    pat_loc = Location.none;
    pat_extra = [];
    pat_type = pat.pat_type;
    pat_env = Env.empty;
    pat_attributes = [];
  };
  vb_expr = expression_of_pattern pat;
  vb_attributes = [];
  vb_loc = Location.none;
}

let preprocess_aliaspat_case { c_lhs; c_guard; c_rhs; } =
  let aliaspats = get_aliaspats c_lhs in
  {
    c_lhs = RemoveAliaspatMap.map_pattern c_lhs;
    c_guard = c_guard;
    c_rhs = if aliaspats = [] then c_rhs else
      let vbs = BatList.map value_binding_of_alias_pattern aliaspats in
      { c_rhs with
        exp_desc = Texp_let (Nonrecursive, vbs, c_rhs);
      };
  }

module AliaspatMapArgument = struct
  include DefaultMapArgument
  let leave_expression exp =
    match exp.exp_desc with
    | Texp_match (e, cs, es, p) ->
      { exp with
        exp_desc = Texp_match (e, BatList.map preprocess_aliaspat_case cs,
                               BatList.map preprocess_aliaspat_case es, p);
      }
    | Texp_function (l, cs, p) ->
      { exp with
        exp_desc =
          Texp_function (l, BatList.map preprocess_aliaspat_case cs, p);
      }
    | _ -> exp
end
module AliaspatMap = MakeMap (AliaspatMapArgument)

(* Turn non-trivial `function` expressions into `fun`-`match` expressions.
   This is required for `when` and `|` rewriting, and helps when printing.

let f x = function  \->  let f x = fun tmp_2520 ->
  | 1 when x -> 2   |->    match tmp_2520 with
  | _ -> 0          |->    | 1 when x -> 2
                    /->    | _ -> 0
*)

let has_guard { c_guard; _ } = BatOption.is_some c_guard

let pattern_is_trivial { pat_desc; _ } =
  match pat_desc with
  | Tpat_any | Tpat_var _ -> true
  | _ -> false
let case_is_trivial c =
  match c.c_lhs, c.c_guard with
  | p, None when pattern_is_trivial p -> true
  | _ -> false

module FunctionMapArgument (CurrentStamp : StampRef) = struct
  include DefaultMapArgument
  let enter_expression exp =
    match exp.exp_desc with
    | Texp_function (l, [c], p) when case_is_trivial c -> exp
    | Texp_function (l, cs, p) (*when BatList.exists has_guard cs*) ->
      let tmp_ident = create_ident CurrentStamp.v @@
        "tmp_" ^ BatString.of_int !CurrentStamp.v in
      let from_type, to_type =
        match unlink exp.exp_type.desc with
        | Tarrow (_, f, t, _) -> f, t
        | _ -> failwith "Function expression without function type (!?)"
      in
      { exp with
        exp_desc = Texp_function (l, [{
          c_lhs = {
            pat_desc = Tpat_var (tmp_ident, mknoloc tmp_ident.name);
            pat_loc = exp.exp_loc;
            pat_extra = [];
            pat_type = from_type;
            pat_env = exp.exp_env;
            pat_attributes = [];
          };
          c_guard = None;
          c_rhs = { exp with
            exp_desc = Texp_match ({ exp with
              exp_desc =
                Texp_ident (Pident tmp_ident,
                            mknoloc (Longident.Lident tmp_ident.name), {
                  val_type = from_type;
                  val_kind = Val_reg;
                  val_loc = exp.exp_loc;
                  val_attributes = [];
                });
              exp_type = from_type;
            }, cs, [], p);
            exp_type = to_type;
          };
        }], Total);
      }
    | _ -> exp
end
module FunctionMap (S : StampRef) = MakeMap (FunctionMapArgument (S))

(* Split up cases involving or patterns.

match x with     \->    match x with
| A | B -> true  |->    | A -> true
| C -> false     |->    | B -> true
                 /->    | C -> false
*)

let rec split_or_pattern pat =
  let wrap_pat_desc d = { pat with pat_desc = d; } in
  match pat.pat_desc with
  | Tpat_any | Tpat_var _ | Tpat_constant _ -> pure pat
  | Tpat_alias (p, i, l) ->
    (fun p -> wrap_pat_desc (Tpat_alias (p, i, l))) <$> split_or_pattern p
  | Tpat_tuple ps ->
    (fun ps -> wrap_pat_desc (Tpat_tuple ps)) <$> mapM split_or_pattern ps
  | Tpat_construct (l, d, ps) ->
    (fun ps -> wrap_pat_desc (Tpat_construct (l, d, ps))) <$>
    mapM split_or_pattern ps
  | Tpat_variant (l, p, r) ->
    (match p with
    | None -> pure pat
    | Some p ->
      (fun p -> wrap_pat_desc (Tpat_variant (l, Some p, r))) <$>
      split_or_pattern p
    )
  | Tpat_record (ls, c) ->
    (fun ls -> wrap_pat_desc (Tpat_record (ls, c))) <$>
    mapM (fun (l, d, p) -> (fun p -> l, d, p) <$> split_or_pattern p) ls
  | Tpat_array ps ->
    (fun ps -> wrap_pat_desc (Tpat_array ps)) <$> mapM split_or_pattern ps
  | Tpat_or (p, q, r) -> [p; q]
  | Tpat_lazy p ->
    (fun p -> wrap_pat_desc (Tpat_lazy p)) <$> split_or_pattern p

let preprocess_or_case c =
  (fun p -> { c with c_lhs = p; }) <$> split_or_pattern c.c_lhs

let preprocess_or_cases cs = BatList.concat (BatList.map preprocess_or_case cs)

module OrpatMapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_match (expr, cs, es, p) ->
          Texp_match (expr, preprocess_or_cases cs, preprocess_or_cases es, p)
        | x -> x
    }
end
module OrpatMap = MakeMap (OrpatMapArgument)

(* In case anyone feels like writing a `while` or `for` loop, it will be
   translated to a function application.

while c do a done               >->  Pervasives.while (fun _ -> c) (fun _ -> a)
for i = a to b do f i done      >->  Pervasives.for_up a b (fun i -> f i)
for i = a downto b do f i done  >->  Pervasives.for_down a b (fun i -> f i)
*)

let lambda_wrap ident exp = { exp with
  exp_desc = Texp_function ("", [{
      c_lhs = {
        pat_desc = Tpat_var (ident, mkloc ident.name exp.exp_loc);
        pat_loc = exp.exp_loc;
        pat_extra = [];
        pat_type = int_type_expr;
        pat_env = exp.exp_env;
        pat_attributes = [];
      };
      c_guard = None;
      c_rhs = exp;
    }], Total);
  exp_type = {
    desc = Tarrow ("", int_type_expr, exp.exp_type, Cunknown);
    level = 0; id = 0;
  };
 }

(* Tpat_any to be cleaned up later *)
let lazy_wrap exp = { exp with
  exp_desc = Texp_function ("", [{
      c_lhs = {
        pat_desc = Tpat_any;
        pat_loc = exp.exp_loc;
        pat_extra = [];
        pat_type = unit_type_expr;
        pat_env = exp.exp_env;
        pat_attributes = [];
      };
      c_guard = None;
      c_rhs = exp;
    }], Total);
  exp_type = {
    desc = Tarrow ("", unit_type_expr, exp.exp_type, Cunknown);
    level = 0; id = 0;
  };
 }

let while_type_expr = {
  desc = Tarrow ("", {
      desc = Tarrow ("", unit_type_expr, bool_type_expr, Cunknown);
      level = 0; id = 0;
    }, {
      desc = Tarrow ("", {
          desc = Tarrow ("", unit_type_expr, var_type_expr, Cunknown);
          level = 0; id = 0;
        }, unit_type_expr, Cunknown);
      level = 0; id = 0;
    }, Cunknown);
  level = 0; id = 0;
}

let while_path = Pdot (pervasives_path, "while", 0)

let while_expr base = { base with
  exp_desc =
    Texp_ident (while_path, mkloc (Longident.Lident "while") base.exp_loc, {
      val_type = while_type_expr;
      val_kind = Val_reg;
      val_loc = base.exp_loc;
      val_attributes = [];
    });
  exp_type = while_type_expr;
}

let for_type_expr = {
  desc = Tarrow ("", int_type_expr, {
      desc = Tarrow ("", int_type_expr, {
          desc = Tarrow ("", {
              desc = Tarrow ("", int_type_expr, var_type_expr, Cunknown);
              level = 0; id = 0;
            }, unit_type_expr, Cunknown);
          level = 0; id = 0;
        }, Cunknown);
      level = 0; id = 0;
    }, Cunknown);
  level = 0; id = 0;
}

let for_up_path = Pdot (pervasives_path, "for_up", 0)

let for_up base = { base with
  exp_desc =
    Texp_ident (for_up_path, mkloc (Longident.Lident "for_up") base.exp_loc, {
      val_type = for_type_expr;
      val_kind = Val_reg;
      val_loc = base.exp_loc;
      val_attributes = [];
    });
  exp_type = for_type_expr;
}

let for_down_path = Pdot (pervasives_path, "for_down", 0)

let for_down base = { base with
  exp_desc =
    Texp_ident (for_down_path,
                mkloc (Longident.Lident "for_down") base.exp_loc, {
      val_type = for_type_expr;
      val_kind = Val_reg;
      val_loc = base.exp_loc;
      val_attributes = [];
    });
  exp_type = for_type_expr;
}

module LoopMapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_while (cond, f) ->
          Texp_apply (while_expr exp, ["", Some (lazy_wrap cond), Required;
                                       "", Some (lazy_wrap f), Required])
        | Texp_for (ident, pat, first, last, Upto, f) ->
          Texp_apply (for_up exp, ["", Some first, Required;
                                   "", Some last, Required;
                                   "", Some (lambda_wrap ident f), Required])
        | Texp_for (ident, pat, first, last, Downto, f) ->
          Texp_apply (for_down exp, ["", Some first, Required;
                                     "", Some last, Required;
                                     "", Some (lambda_wrap ident f), Required])
        | x -> x
    }
end
module LoopMap = MakeMap (LoopMapArgument)

(* Add `else ()` to `if` expressions without an `else` clause.

if p then                        \->  if p then
  print_endline "Hello, world!"  |->    print_endline "Hello, world!"
                                 |->  else
                                 /->    ()
*)

module ElselessMapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_ifthenelse (p, et, None) ->
          Texp_ifthenelse (p, et, Some { exp with
              exp_desc =
                Texp_construct (mkloc (Longident.Lident "()") exp.exp_loc,
                                unit_constr_desc, []);
              exp_type = unit_type_expr;
            })
        | x -> x
    }
end
module ElselessMap = MakeMap (ElselessMapArgument)

module type EnvProvider = sig val env : Env.t end

module PreprocessorMapArgument (FinalEnv : EnvProvider) = struct
  include DefaultMapArgument

  let current_stamp = ref (largest_stamp FinalEnv.env)
  module CurrentStamp = struct let v = current_stamp end
  module ValrecMapArgument = ValrecMapArgument (CurrentStamp)
  module AnypatMapArgument = AnypatMapArgument (CurrentStamp)
  module FunctionMapArgument = FunctionMapArgument (CurrentStamp)

  let enter_pattern = AnypatMapArgument.enter_pattern
                   %> RecordMapArgument.enter_pattern
  let enter_expression = FunctionMapArgument.enter_expression
                      %> OrpatMapArgument.enter_expression
                      %> GuardMapArgument.enter_expression
                      %> RecordMapArgument.enter_expression
                      %> ValpatMapArgument.enter_expression
                      %> ValrecMapArgument.enter_expression
                      %> LoopMapArgument.enter_expression
                      %> ElselessMapArgument.enter_expression
  let leave_expression = AliaspatMapArgument.leave_expression
  let enter_structure = RecordMapArgument.enter_structure
                     %> ValrecMapArgument.enter_structure
                     %> ValpatMapArgument.enter_structure
end
module PreprocessorMap (FinalEnv : EnvProvider) =
  MakeMap (PreprocessorMapArgument (FinalEnv))
