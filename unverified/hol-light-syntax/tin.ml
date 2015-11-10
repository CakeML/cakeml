open Typedtree;;
open Ast;;

(*Conversions from parse tree into internal AST*)
exception Unknown_rec_flag of Asttypes.rec_flag;;

let rec_of r =
  match r with
  | Asttypes.Nonrecursive -> false
  | Asttypes.Recursive -> true
  | _ -> raise (Unknown_rec_flag r);;

let string_of_ident i = i.Ident.name;;

exception Unknown_longident of Longident.t;;

let string_of_longident i =
  match i with
  | Longident.Lident s -> s
  | _ -> raise (Unknown_longident i)

exception Unknown_typ of Types.type_desc;;

let rec typ_of_desc t =
  match t with
  | Types.Tlink t' -> typ_of t'
  | Types.Tvar (Some s) -> Typ_var s
  | Types.Tvar None -> Typ_var_anon
  | Types.Tconstr (Path.Pident i,tl,_) ->
      Typ_constr (string_of_ident i,List.map typ_of tl)
  | Types.Tconstr (Path.Pdot (Path.Pident i,s,_),tl,_) ->
      Typ_qual_constr (string_of_ident i,s,List.map typ_of tl)
  | Types.Tarrow (_,t1,t2,_) ->
      Typ_arrow (typ_of t1,typ_of t2)
  | Types.Ttuple tl ->
      Typ_tuple (List.map typ_of tl)
  | _ -> raise (Unknown_typ t)

and typ_of t = typ_of_desc t.Types.desc;;

let typ_abbrevs = Hashtbl.create 19;;

let rec expand_typ t =
  match t with
  | Typ_arrow (t1,t2) -> Typ_arrow (expand_typ t1,expand_typ t2)
  | Typ_tuple tl -> Typ_tuple (List.map expand_typ tl)
  | Typ_constr (s,tl) ->
     (try let u = Hashtbl.find typ_abbrevs s in
        if tl <> [] then failwith "expand_typ"; u
      with Not_found ->
        Typ_constr (s,List.map expand_typ tl))
  | Typ_qual_constr (s1,s2,tl) ->
        Typ_qual_constr (s1,s2,List.map expand_typ tl)
  | _ -> t;;

exception Unknown_texp of expression;;
exception Unknown_exp of expression_desc;;
exception Unknown_tpat of pattern;;
exception Unknown_pat of pattern_desc;;
exception Unknown_arg;;

let rec texp_of e =
  let t' = typ_of e.exp_type in
  let t = expand_typ t' in
  let e' = t,exp_of e.exp_desc in
  match e.exp_extra with
  | [] -> e'
  | [Texp_constraint (Some t1,None),_] ->
      t,Exp_constraint (e',typ_of t1.ctyp_type)
  | _ -> raise (Unknown_texp e)

and exp_of e =
  match e with
  | Texp_ident (Path.Pident i,_,_) ->
      Exp_ident (string_of_ident i)
  | Texp_ident (Path.Pdot (Path.Pident i,s,_),_,_) ->
      Exp_qual_ident (string_of_ident i,s)
  | Texp_constant (Asttypes.Const_int i) ->
      Exp_int i
  | Texp_constant (Asttypes.Const_string s) ->
      Exp_string s
  | Texp_function (_,pl,_) ->
      Exp_function (gcases_of pl)
  | Texp_apply (e,el) ->
      Exp_apply (texp_of e,List.map arg_of el)
  (*removed first arg to Texp_construct*)
  | Texp_construct (i,_,el,_) ->
      Exp_construct (string_of_longident i.Asttypes.txt,List.map texp_of el)
  | Texp_tuple el ->
      Exp_tuple (List.map texp_of el)
  | Texp_match (e,pl,_) ->
      Exp_match (texp_of e,gcases_of pl)
  | Texp_try (e,pl) ->
      Exp_try (texp_of e,gcases_of pl)
  | Texp_let (r,pl,e') ->
      Exp_let (rec_of r,cases_of pl,texp_of e')
  | Texp_sequence (e1,e2) ->
      Exp_sequence (texp_of e1,texp_of e2)
  | Texp_ifthenelse (e1,e2,None) ->
      Exp_ifthenelse (texp_of e1,texp_of e2,
        (Typ_constr ("unit",[]),Exp_construct ("()",[])))
  | Texp_ifthenelse (e1,e2,Some e3) ->
      Exp_ifthenelse (texp_of e1,texp_of e2,texp_of e3)
  | _ -> raise (Unknown_exp e)

and arg_of (_,e,_) =
  match e with
  | Some e' -> texp_of e'
  | _ -> raise Unknown_arg

and tpat_of p =
  let t' = typ_of p.pat_type in
  let t = expand_typ t' in
  let p' = t,pat_of p.pat_desc in
  match p.pat_extra with
  | [] -> p'
  | [Tpat_constraint t1,_] ->
      t,Pat_constraint (p',typ_of t1.ctyp_type)
  | _ -> raise (Unknown_tpat p)

and pat_of p =
  match p with
  | Tpat_var (i,_) ->
      Pat_var (string_of_ident i)
  | Tpat_any ->
      Pat_any
  | Tpat_constant (Asttypes.Const_int i) ->
      Pat_int i
  | Tpat_constant (Asttypes.Const_string s) ->
      Pat_string s
  (*Removed first arg to Tpat_construct*)
  | Tpat_construct (i,_,pl,_) ->
      Pat_construct (string_of_longident i.Asttypes.txt,
        List.map tpat_of pl)
  | Tpat_tuple pl ->
      Pat_tuple (List.map tpat_of pl)
  | Tpat_or (p1,p2,_) ->
      Pat_or (tpat_of p1,tpat_of p2)
  | Tpat_alias ({pat_desc = Tpat_any},i,_) ->
      Pat_var (string_of_ident i)
  | Tpat_alias (p,i,_) ->
      Pat_alias (tpat_of p,string_of_ident i)
  | _ -> raise (Unknown_pat p)
  
and cases_of pl =
  List.map (fun (p,e) -> (tpat_of p,texp_of e)) pl

and gcases_of pl =
  List.map (fun (p,e) ->
    let p' = tpat_of p in
    match e.exp_desc with
    | Texp_when (e1,e2) ->
        p',Some (texp_of e1),texp_of e2
    | _ -> p',None,texp_of e) pl;;

let vcases_of pl =
  List.map (fun (p,e) ->
    let p' = tpat_of p in
    ((match p' with _,Pat_constraint (_,t) -> t | _ -> typ_of p.pat_type),
     p',texp_of e)) pl;;

exception Unknown_type_decl of Types.type_declaration;;

let type_decl_of d =
  match d.Types.type_kind with
  | Types.Type_abstract ->
     (match d.Types.type_manifest with
      | Some t -> Type_abbrev (typ_of_desc t.Types.desc)
      | None -> raise (Unknown_type_decl d))
  | Types.Type_variant vl ->
      Type_variant (List.map (fun (i',tl,_) ->
        (string_of_ident i',List.map typ_of tl)) vl)
  | _ -> raise (Unknown_type_decl d);;

exception Unknown_sig_item of signature_item_desc;;

let sig_item_of s =
  match s.sig_desc with
  | Tsig_value (i,_,{val_val = {Types.val_type = t}}) ->
      Sig_value (string_of_ident i,typ_of t)
  | Tsig_type [i,_,{typ_type =
        {Types.type_params = pl;
         Types.type_kind = Types.Type_abstract;
         Types.type_manifest = None}}] ->
      Sig_type (string_of_ident i,List.map typ_of pl,None)
  | Tsig_type [i,_,{typ_type = t}] ->
      Sig_type (string_of_ident i,List.map typ_of t.Types.type_params,
         Some (type_decl_of t))
  | s' -> raise (Unknown_sig_item s');;

exception Unknown_str_item of structure_item_desc;;

let rec str_item_of s =
  match s.str_desc with
  | Tstr_eval e ->
      Str_eval (texp_of e)
  | Tstr_value (r,pl) -> 
      Str_value (rec_of r,vcases_of pl)
  | Tstr_type tl ->
      let tl' = List.map
        (fun (i,_,{typ_type = t}) ->
           (string_of_ident i,List.map typ_of t.Types.type_params,
             type_decl_of t))
        tl in
      List.iter (fun t ->
        match t with
        | (s,[],Type_abbrev u) -> Hashtbl.replace typ_abbrevs s (expand_typ u)
        | (_,_,Type_abbrev _) -> failwith "str_item_of"
        | _ -> ()) tl';
      Str_type tl'
  | Tstr_exception (i,_,{exn_exn = {Types.exn_args = tl}}) ->
      Str_exception (string_of_ident i,List.map typ_of tl)
  | Tstr_modtype (i,_,{mty_desc = Tmty_signature {sig_items = sl}}) ->
      Str_modtype (string_of_ident i,List.map sig_item_of sl)
  | Tstr_module (i,_,{mod_desc = Tmod_constraint
        ({mod_desc = Tmod_structure {str_items = sl}},
         Types.Mty_ident (Path.Pident i'),_,_)}) ->
      Str_module (string_of_ident i,string_of_ident i',
        List.map str_item_of sl)
  | Tstr_include ({mod_desc = Tmod_ident (Path.Pident i,_)},_) ->
      Str_include (string_of_ident i)
  | s' -> raise (Unknown_str_item s');;

Hashtbl.reset typ_abbrevs;;
exception Unknown_toplevel_phrase of Parsetree.toplevel_phrase;;

(*Parse a string as a source file in OCaml*)
let rec process_string str =
  Warnings.parse_options false "-8";
  let lb = Lexing.from_string str in
  let phrases = !Toploop.parse_use_file lb in
  (Warnings.parse_options false "+8";
  List.map(fun phrase ->
    match phrase with
    | Parsetree.Ptop_def s ->
         let oldenv = !Toploop.toplevel_env in
         let (str,_,_) = Typemod.type_toplevel_phrase oldenv s in
         (*Silently execute the phrase to update OCaml state*)
          ignore (Toploop.execute_phrase false
                 Format.std_formatter phrase);
         List.map str_item_of str.str_items
    | Parsetree.Ptop_dir ("install_printer",Parsetree.Pdir_ident i) ->
         [Str_install_printer (string_of_longident i)]
    | _ -> raise (Unknown_toplevel_phrase phrase) )
    phrases);;




