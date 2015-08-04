open Batteries
open BatResult.Monad

open Asttypes
open Ident
open Longident
open Path
open Types
open Typedtree
open TypedtreeMap

let rec mapM f = function
  | [] -> return []
  | x :: xs -> f x >>= fun y ->
               mapM f xs >>= fun ys ->
               return (y :: ys)

let mapiM f =
  let rec g i = function
    | [] -> return []
    | x :: xs -> f i x >>= fun y ->
                 g (succ i) xs >>= fun ys ->
                 return (y :: ys)
  in
  g 0

let paren s = "(" ^ s ^ ")"

let id x = x
let ifThen x f = if x then f else id

let indent_by = BatString.repeat "  "

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
    | "sharing" | "signature" | "structure" | "where" | "withtype" | "div"
    | "SOME" | "NONE" | "oc_mod" | "oc_ref" | "oc_raise" | "Oc_Array")
    as x ->
    x ^ "__"
  | "Some" -> "SOME"
  | "None" -> "NONE"
  | "Array" -> "Oc_Array"
  | x when BatString.starts_with "_" x -> "u" ^ x
  | x when
    (match fixity_of x with
    | Neither, _ -> false
    | _ -> true
    ) -> "op" ^ x
  | x -> x

let fix_var_name = fix_identifier

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

    | '^' :: xs -> "hat" :: f xs

    | '!' :: xs -> "bang" :: f xs
    | ':' :: xs -> "colon" :: f xs

    | ['m'; 'o'; 'd'] -> ["oc_mod"]
    | ['r'; 'a'; 'i'; 's'; 'e'] -> ["oc_raise"]
    | ['r'; 'e'; 'f'] -> ["oc_ref"]

    | xs -> [BatString.of_list xs]
  in
  BatString.concat "_" % f % BatString.to_list

let rec print_longident_pure = function
  | Lident ident -> fix_identifier ident
  | Ldot (left, right) ->
    let left = print_longident_pure left in
    let right = ifThen (left = "Pervasives") convertPervasive right in
    fix_identifier left ^ "." ^ right
  | Lapply (p0, p1) -> print_longident_pure p0 ^ " " ^ print_longident_pure p1

let print_longident = return % print_longident_pure

let rec longident_of_path = function
  | Pident i -> Lident i.name
  | Pdot (l, r, _) -> Ldot (longident_of_path l, r)
  | Papply (l, r) -> Lapply (longident_of_path l, longident_of_path r)

let print_path_pure = print_longident_pure % longident_of_path
let print_path = print_longident % longident_of_path

let print_constant = function
  | Const_int x -> string_of_int x
  | Const_char x -> "#\"" ^ BatChar.escaped x ^ "\""
  | Const_string (x, y) -> "\"" ^ BatString.escaped x ^ "\""
  | Const_float x -> x
  | Const_int32 x -> BatInt32.to_string x
  | Const_int64 x -> BatInt64.to_string x
  | Const_nativeint x -> BatNativeint.to_string x

(* Precedence rules (for parenthesization):
   Low number => loose association
   0: case expression, case pattern, let expression, if condition,
      tuple term, list term
   1: Case RHS
   2: Application

   case x of
     p => ...
   | q => (case y of ...)
   | r => ...
 *)

let rec path_prefix = function
  | Pident _ -> ""
  | Pdot (p, _, _) -> print_path_pure p ^ "."
  | Papply (p, _) -> print_path_pure p ^ " "

(* Constructors don't have a fully specified path. Infer it from the type. *)
let make_constructor_path { cstr_name; cstr_res = { desc; }; } =
  match desc with
  | Tconstr (p, _, _) -> return @@ path_prefix p ^ cstr_name
  | _ -> Bad ("Can't deduce path of constructor " ^ cstr_name)

(* Works in both patterns and expressions. `f` is the function that prints
   subpatterns/subexpressions. *)
let print_construct prec (f : int -> 'a -> (string, string) result)
                    lident cstr (xs : 'a list) =
  match cstr.cstr_name, xs with
  | "::", [x; y] -> f 1 x >>= fun x' ->
                    f 0 y >>= fun y' ->
                    return @@ ifThen (prec > 0) paren @@ x' ^ " :: " ^ y'
  | _ ->
    make_constructor_path cstr >>= fun name ->
    (match xs with
    | [] -> return ""
    | [x] -> f 2 x >>= fun x' ->
             return @@ " " ^ x'
    | _ -> mapM (f 0) xs >>= fun xs' ->
           return @@ " (" ^ BatString.concat ", " xs' ^ ")"
    ) >>= fun args ->
    return @@ ifThen (prec > 1 && not ([] = xs)) paren @@
      fix_identifier name ^ args

let rec print_pattern prec pat =
  match pat.pat_desc with
  (* _ *)
  | Tpat_any -> return "unused__"
  | Tpat_var (ident, name) -> return @@ fix_var_name name.txt
  | Tpat_constant c -> return @@ print_constant c
  | Tpat_tuple ps -> mapM (print_pattern 0) ps >>= fun ps' ->
                     return @@ paren @@ BatString.concat ", " ps'
  | Tpat_construct (lident, desc, ps) ->
    print_construct prec print_pattern lident desc ps
  | _ -> Bad "Some pattern syntax not implemented."

(* Pattern can be matched on LHS; no need for case expression *)
let case_is_trivial c =
  match c.c_lhs.pat_desc, c.c_guard with
  | Tpat_any, None -> true
  | Tpat_var (_, _), None -> true
  | _ -> false

let rec print_expression indent incase prec expr =
  match expr.exp_desc with
  | Texp_ident (path, longident, desc) -> print_path path
  | Texp_constant c -> return @@ print_constant c
  | Texp_let (r, bs, e) ->
    mapiM (fun i -> print_value_binding (i = 0) (indent + 1) r)
          bs >>= fun bs' ->
    print_expression (indent + 1) false 0 e >>= fun e' ->
    return @@ ifThen (prec > 1) paren @@
      "let\n" ^
      BatString.concat "" bs' ^ "\n" ^
      indent_by indent ^ "in\n" ^
      indent_by (indent + 1) ^ e' ^ "\n" ^
      indent_by indent ^ "end"
  | Texp_function (l, [c], p) ->
    print_case indent 0 " => " c >>= fun c' ->
    return @@ ifThen (prec > 1) paren @@ "fn " ^ (match c.c_lhs.pat_desc with
    (* fn x => E *)
    | Tpat_var (_, _) -> ""
    (* fn tmp__ => case tmp of P => E *)
    | _ -> "tmp__ => case tmp__ of ") ^ c'
  (* fn tmp__ => case tmp of P0 => E0 | P1 => E1 | ... *)
  | Texp_function (l, cs, p) ->
    print_case_cases (indent) cs >>= fun cs' ->
    return @@ ifThen (prec > 1 || incase) paren @@
      "fn tmp__ => case tmp__ of" ^ cs'
  (* Special cases *)
  | Texp_apply ({ exp_desc = Texp_ident (Pdot (Pident m, n, _), _, _) },
                [(_, Some e0, _); (_, Some e1, _)])
      when m.name = "Pervasives" && BatList.mem n ["&&"; "&"; "||"; "or"] ->
    let op = match n with
      | "&&" |  "&" -> "andalso"
      | "||" |  "or" -> "orelse"
      | x -> x
    in
    print_expression indent false 2 e0 >>= fun e0' ->
    print_expression indent incase 2 e1 >>= fun e1' ->
    return @@ e0' ^ " " ^ op ^ " " ^ e1'
  (* Normal function application *)
  | Texp_apply (e0, es) ->
    print_expression indent false 2 e0 >>= fun e0' ->
    mapM (function
    | l, Some e, Required -> print_expression indent incase 2 e
    | _ -> Bad "Optional and named arguments not supported."
    ) es >>= fun es' ->
    return @@ ifThen (prec > 1) paren @@ e0' ^ " " ^ BatString.concat " " es'
  | Texp_match (exp, cs, [], p) ->
    print_expression indent false 0 exp >>= fun exp' ->
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@ ifThen (prec > 0 || incase) paren @@ "case " ^ exp' ^ " of" ^ cs'
  | Texp_match (_, _, _, _) -> Bad "Exception cases not supported."
  (* E handle with X0 => E0 | X1 => E1 *)
  | Texp_try (exp, cs) ->
    print_expression indent false 1 exp >>= fun exp' ->
    print_case_cases (indent) cs >>= fun cs' ->
    return @@ ifThen (prec > 0) paren @@ exp' ^ " handle" ^ cs'
  | Texp_tuple es -> mapM (print_expression indent false 0) es >>= fun es' ->
                     return @@ paren @@ BatString.concat ", " es'
  | Texp_construct (lident, desc, es) ->
    print_construct prec (print_expression indent incase) lident desc es
  | Texp_ifthenelse (p, et, Some ef) ->
    print_expression indent false 0 p >>= fun p' ->
    print_expression (indent + 1) false 0 et >>= fun et' ->
    print_expression (indent + 1) incase prec ef >>= fun ef' ->
    return @@ ifThen (prec > 0) paren @@
      "if " ^ p' ^ " then\n" ^
      indent_by (indent + 1) ^ et' ^ "\n" ^
      indent_by indent ^ "else\n" ^
      indent_by (indent + 1) ^ ef'
  (* E0; E1 *)
  | Texp_sequence (e0, e1) ->
    print_expression indent false 0 e0 >>= fun e0' ->
    print_expression indent incase 0 e1 >>= fun e1' ->
    return @@ paren @@ e0' ^ ";\n" ^ indent_by indent ^ e1'
  | _ -> Bad "Some expression syntax not implemented."

and print_case indent prec conn c =
  case_parts indent prec c >>= fun (pat, exp) ->
  match c.c_guard with
  | None -> return @@ pat ^ conn ^ exp
  | _ -> Bad "Pattern guards not supported."

and print_case_cases indent =
  let rec f linePrefix = function
  | [] -> return ""
  | c :: cs ->
    print_case (indent + 1) 0 " => " c >>= fun c' ->
    f "| " cs >>= fun rest ->
    return @@ "\n" ^ indent_by indent ^ linePrefix ^ c' ^ rest
  in
  f "  "  (* First case has no '|' *)

and case_parts indent prec c =
  print_pattern prec c.c_lhs >>= fun pat ->
  print_expression (indent) true 1 c.c_rhs >>= fun exp ->
  return (pat, exp)

and print_value_binding first_binding indent rec_flag vb =
  let keyword = match first_binding, rec_flag with
                | false, _ -> "and "
                | true, Recursive -> "fun "
                | true, Nonrecursive -> "val "
  in
  print_pattern 0 vb.vb_pat >>= fun name ->
  match vb.vb_expr.exp_desc, rec_flag with
  (* Special case for trivial patterns *)
  | Texp_function (l, [c], p), Recursive when case_is_trivial c ->
    (* Try to turn `fun f x = fn y => fn z => ...` into `fun f x y z = ...` *)
    let rec reduce_fn acc lastc =
      match lastc.c_rhs.exp_desc with
      | Texp_function (_, [nextc], _) when case_is_trivial nextc ->
        reduce_fn (lastc.c_lhs :: acc) nextc
      | _ -> mapM (print_pattern 0) (BatList.rev acc) >>= fun vs ->
             print_case indent 0 " = " lastc >>= fun c' ->
             return @@
               indent_by indent ^ keyword ^ name ^
               BatString.concat "" (BatList.map (fun v -> " " ^ v) vs) ^
               " " ^ c'
    in
    reduce_fn [] c
  (* fun tmp__ = case tmp__ of P0 => E0 | ... *)
  | Texp_function (l, cs, p), Recursive ->
    print_case_cases (indent + 1) cs >>= fun cs' ->
    return @@
      indent_by indent ^ keyword ^ name ^ " tmp__ = case tmp__ of" ^ cs'
  (* Should have been removed by the AST preprocessor *)
  | _, Recursive -> Bad "Recursive values are not supported in CakeML"
  (* val x = E *)
  | _, Nonrecursive ->
    print_expression indent false 0 vb.vb_expr >>= fun expr ->
    return @@ indent_by indent ^ keyword ^ name ^ " = " ^ expr

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

let rec print_core_type prec ctyp =
  let thisParen = ifThen (prec > 1) paren in
  match ctyp.ctyp_desc with
  | Ttyp_any -> return "_"
  | Ttyp_var name -> return @@ "'" ^ fix_type_name name
  | Ttyp_arrow (l, dom, cod) ->
    print_core_type 2 dom >>= fun a ->
    print_core_type 1 cod >>= fun b ->
    return @@ thisParen @@ (if l = "" then "" else l ^ ":") ^ a ^ " -> " ^ b
    (* ^^ label type changes in 4.03 ^^ *)
  | Ttyp_tuple ts -> print_ttyp_tuple ts >>= fun t ->
                     return @@ paren t
  | Ttyp_constr (path, lid, ts) ->
    print_path path >>= fun name ->
    print_typ_params ts >>= fun params ->
    return @@ params ^ name
  | Ttyp_poly (_, t) -> print_core_type prec t
  | _ -> Bad "Some core types syntax not supported."

and print_typ_params = function
  | [] -> return ""
  | [t] -> print_core_type 2 t >>= fun t' ->
           return @@ t' ^ " "
  | ts -> mapM (print_core_type 0) ts >>= fun ts' ->
          return @@ "(" ^ BatString.concat ", " ts' ^ ") "

and print_ttyp_tuple = function
  | [] -> return ""
  | [t] -> print_core_type 2 t
  | t :: ts -> print_core_type 0 t >>= fun core_type ->
               print_ttyp_tuple ts >>= fun rest ->
               return @@ core_type ^ " * " ^ rest

(* constructor_arguments is new (and necessary) in OCaml 4.03, in which
   support for value constructors for record types was added. *)

(*let print_constructor_arguments = function
  | Pcstr_tuple ts -> print_ttyp_tuple ts
  | Pcstr_record ds -> Bad "Record syntax not supported."*)
let print_constructor_arguments = print_ttyp_tuple

let print_constructor_declaration decl =
  (* Replace `print_ttyp_tuple` with `print_constructor_arguments
     in OCaml 4.03. *)
  print_constructor_arguments decl.cd_args >>= fun constructor_args ->
  return @@ decl.cd_name.txt ^
    if constructor_args = "" then "" else " of " ^ constructor_args

let print_ttyp_variant indent =
  let rec f linePrefix = function
    | [] -> return ""
    | d :: ds -> print_constructor_declaration d >>= fun constructor_decl ->
                 f "| " ds >>= fun rest ->
                 return @@ "\n" ^ indent_by indent ^ linePrefix ^
                           constructor_decl ^ rest
  in
  f "  "

let print_type_declaration first_binding indent typ =
  let keyword = match first_binding, typ.typ_kind with
                | false, _ -> "and "
                | true, Ttype_abstract -> "type "
                | true, _ -> "datatype "
  in
  print_typ_params (BatList.map Tuple2.first typ.typ_params) >>= fun params ->
  (match typ.typ_manifest, typ.typ_kind with
  (* type t' = t *)
  | Some m, Ttype_abstract -> print_core_type 0 m >>= fun manifest ->
                              return @@ " = " ^ manifest
  (* datatype t' = datatype t *)
  | Some m, Ttype_variant ds -> print_core_type 0 m >>= fun manifest ->
                                return @@ " = datatype " ^ manifest
  (* type t *)
  | None, Ttype_abstract -> return ""
  (* datatype t = A | B | ... *)
  | None, Ttype_variant ds ->
    print_ttyp_variant (indent + 1) ds >>= fun expr ->
    return @@ " =" ^ expr
  | _ -> Bad "Some type declarations not implemented."
  ) >>= fun rest ->
  return @@ indent_by indent ^ keyword ^ params ^
            fix_type_name typ.typ_name.txt ^ rest

let concat_items =
  BatList.filter (fun x -> "" <> x)
  %> BatList.map (fun x -> x ^ ";")
  %> BatString.concat "\n\n"

(* Fixes to typed AST *)

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
      let unit_type_expr = {
        desc = Tconstr (Pident (Ident.create "unit"), [], ref Mnil);
        level = 0; id = 0;
      } in
      let unit_constr_desc = {
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
      } in
      let new_subexpr = Texp_apply ({ vb.vb_expr with
        exp_desc = Texp_ident (Pident new_ident,
                               Location.mknoloc (Lident new_name), {
          val_type = { vb.vb_pat.pat_type with
            desc = Tarrow ("", unit_type_expr, vb.vb_pat.pat_type, Cunknown);
          };
          val_kind = Val_reg;
          val_loc = Location.none;
          val_attributes = [];
        }); },
        [("", Some {
            exp_desc = Texp_construct (Location.mknoloc (Lident "()"),
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

let preprocess_value_bindings = function
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

let preprocess_record_expr bs =
  let (_, { lbl_res; _ }, _) = BatList.hd bs in function
  | None ->
    (match lbl_res.desc with
    (* Should be this sort of type (by construction) *)
    | Tconstr (p, _, _) ->
      let (cstr_name, cstr_desc) = record_cstr_name_desc bs lbl_res p in
      Texp_construct (Location.mknoloc (Longident.Lident cstr_name),
                      cstr_desc, BatList.map (fun (_, _, x) -> x) bs)
    | _ -> Texp_record (bs, None)
    )
  | Some base -> Texp_record (bs, Some base)

let preprocess_type_declaration typ =
  match typ.typ_kind with
  (* Paraphrase record type declarations *)
  | Ttype_record lds ->
    let cstr_name = "Mk" ^ BatString.capitalize typ.typ_name.txt in
    { typ with
      (*typ_cstrs = [cstr];*)
      typ_kind = Ttype_variant [{
        cd_id = Ident.create cstr_name;
        cd_name = Location.mknoloc cstr_name;
        cd_args = BatList.map (fun ld -> ld.ld_type) lds;
        cd_res = None;
        cd_loc = Location.none;
        cd_attributes = [];
      }];
    }
  | _ -> typ

module RecordMapArgument : MapArgument = struct
  include DefaultMapArgument
  let enter_expression exp =
    { exp with
      exp_desc =
        match exp.exp_desc with
        | Texp_record (bs, base) -> preprocess_record_expr bs base
        | x -> x
    }
  let enter_type_declaration = preprocess_type_declaration
end
module RecordMap = MakeMap (RecordMapArgument)

let rec preprocess_structure_item str =
  match str.str_desc with
  | Tstr_value (r, bs) ->
    let oldbs, newbs = preprocess_value_bindings r bs in
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

let rec print_module_expr indent expr =
  match expr.mod_desc with
  | Tmod_structure str ->
    let str_items =
      BatList.concat (BatList.map preprocess_structure_item str.str_items) in
    mapM (print_structure_item (indent + 1)) str_items >>= fun items ->
    return @@
      indent_by indent ^ "struct\n" ^
      concat_items items ^ "\n" ^
      indent_by indent ^ "end"
  | _ -> Bad "Some module types not implemented."

and print_module_binding indent mb =
  print_module_expr indent mb.mb_expr >>= fun expr ->
  let name = mb.mb_id.name in
  match mb.mb_expr.mod_desc with
  | Tmod_structure str ->
    return @@ indent_by indent ^ "structure " ^ name ^ " = " ^ expr
  | _ -> Bad "Some types of module not implemented."

and print_structure_item indent str =
  match str.str_desc with
  | Tstr_eval (e, attrs) ->
    print_expression indent false 0 e >>= fun e' ->
    return @@ indent_by indent ^ "val eval__ = " ^ e'
  | Tstr_value (r, bs) ->
    mapiM (fun i -> print_value_binding (i = 0) indent r) bs >>= fun ss ->
    return @@ BatString.concat "\n" ss
  | Tstr_type ds ->
    mapiM (fun i -> print_type_declaration (i = 0) indent) ds >>= fun ss ->
    return @@ BatString.concat "\n" ss
  | Tstr_exception constructor ->
    (match constructor.ext_kind with
    | Text_decl ([], None) -> return ""
    | Text_decl (ts, None) -> print_constructor_arguments ts >>= fun ts' ->
                              return @@ " of " ^ ts'
    | Text_rebind (path, lident) -> print_path path >>= fun p ->
                                    return @@ " = " ^ p
    | _ -> Bad "Some exception declaration syntax not supported."
    ) >>= fun rest ->
    return @@ indent_by indent ^ "exception " ^ constructor.ext_name.txt ^
              rest
  | Tstr_module b ->
    print_module_binding indent b >>= fun b' ->
    return @@ b'
  (* Things are annotated with full module paths, making `open` unnecessary. *)
  | Tstr_open _ -> return ""
  | _ -> Bad "Some structure items not implemented."

let output_result = function
  | Ok r -> print_endline r
  | Bad e -> print_endline @@ "Error: " ^ e; exit 1

(*let return_ident = Ident.create "return";
let ok_ident = Ident.create "ok";
let bad_ident = Ident.create "bad";

let return_type ok bad : type_expr = {
  desc = Tconstr (Pident return_ident, [ok, bad], ref Mnil);
  level = 0;
  id = return_ident;
}
let ok_desc : constructor_description = {
  cstr_name = "Ok";
  cstr_res = {
    desc = return_type (Tvar (Some "a")) (Tvar (Some "b"));
    level = 0;
    id = return_ident.stamp;
  };
  cstr_existentials = [];
  cstr_args = [{
    desc = Tvar (Some "a");
    level = 0;
    id = ok_ident.stamp;
  }];
  cstr_arity = 1;
  cstr_tag = ;
  cstr_consts = ;
  cstr_nonconsts = ;
  cstr_normal = ;
  cstr_generalized = false;
  cstr_loc = Location.none;
  cstr_attributes = [];
}
let bad_desc : constructor_description = _

module MyMapArgument : MapArgument = struct
  include DefaultMapArgument
  let leave_expression exp =
    match exp.exp_desc with
    | Texp_match (_, _, [], _) -> exp
    | Texp_match (e, cs, es, p) ->
      let es' =
        map (function { c_lhs = lhs; c_guard = guard; c_rhs = rhs } -> {
          c_lhs = lhs;
          c_guard = guard;
          c_rhs = { rhs with
            exp_desc = Texp_construct ({
              txt = bad_ident;
              loc = rhs.exp_loc;
            }, bad_desc, [rhs]);
            exp_type = return_type e.exp_type rhs.exp_type;
          };
        }) es in
      let e' = { e with
        exp_desc = Texp_try ({
          exp_desc = Texp_construct ({
            txt = ok_ident;
            loc = e.exp_loc;
          }, ok_desc, [e]);
        }, es');
        exp_type = return_type e.exp_type exp.exp_type;
      } in
      let cs' = {
        c_lhs = {
          pat_desc = Tpat_construct ({
            txt = bad_ident;
            loc = exp.exp_loc
          });
          pat_loc = exp.exp_loc;
          pat_extra = [];
          pat_type = return_type e.exp_type exp.exp_type;
          pat_env = e.exp_env;
          pat_attributes = [];
        } :: cs;
      } in
      Texp_match (e', cs', [], p)
    | _ -> exp
end*)

let lexbuf = Lexing.from_channel stdin
let parsetree = Parse.implementation lexbuf
let _ = Compmisc.init_path false
let typedtree, signature, env =
  Typemod.type_structure (Compmisc.initial_env ()) parsetree Location.none
let str = RecordMap.map_structure (MatchMap.map_structure typedtree)
let str_items =
  BatList.concat (BatList.map preprocess_structure_item str.str_items)
let _ = output_result (
  mapM (print_structure_item 0) str_items >>= (return % concat_items)
)
(*let () = Printtyped.implementation Format.std_formatter
  { typedtree with str_items; }*)
