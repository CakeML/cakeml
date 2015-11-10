(*Internal AST pretty ocaml_printed back to OCaml concrete syntax*)
#use "print_util.ml";;

let check_pat_constraints = ref !strip_pat_constraints;;

let ocaml_ppf = ref Format.std_formatter;; 

let ocaml_print s = Format.pp_print_string !ocaml_ppf s;;

exception Unknown_ml_typ of ml_typ;;

let rec ocaml_print_typ t =
  match t with
  | Typ_var_anon ->
      unbaked "Typ_var_anon";
      ocaml_print "?"
  | Typ_var s -> ocaml_print ("'"^s)
  | Typ_arrow (t1,t2) ->
      ocaml_print "(";
      ocaml_print_typ t1;
      ocaml_print " -> ";
      ocaml_print_typ t2;
      ocaml_print ")"
  | Typ_tuple al ->
      (if al = [] then raise (Unknown_ml_typ t));
      ocaml_print "(";
      ocaml_print_typ (hd al);
      map (fun t' -> ocaml_print " * "; ocaml_print_typ t') (tl al);
      ocaml_print ")"
  | Typ_constr (s,al) ->
      if al <> [] then
       (ocaml_print "(";
        ocaml_print_typ (hd al);
        map (fun t' -> ocaml_print ","; ocaml_print_typ t') (tl al);
        ocaml_print ") ");
        ocaml_print s
  | Typ_qual_constr (s1,s2,al) ->
      if al <> [] then
       (ocaml_print "(";
        ocaml_print_typ (hd al);
        map (fun t' -> ocaml_print ","; ocaml_print_typ t') (tl al);
        ocaml_print ") ");
        ocaml_print s1;
	ocaml_print ".";
	ocaml_print s2;;

exception Unknown_ml_exp of ml_exp;;
exception Unknown_ml_pat of ml_pat;;

let ocaml_is_operator =
  let ht = Hashtbl.create 73 in
  let ct = Hashtbl.create 73 in
  List.iter (fun x -> Hashtbl.add ht x true)
    ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "o"; "upto";
     "F_F"; "THENC"; "THEN"; "THENL"; "ORELSE"; "ORELSEC";
     "THEN_TCL"; "ORELSE_TCL"];
  List.iter (fun x -> Hashtbl.add ct x true)
    ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
     '?'; '%'; '.'; '$'];
  fun x ->
    try Hashtbl.find ht x with
    Not_found -> try Hashtbl.find ct x.[0] with _ -> false;;

let ocaml_op s = if ocaml_is_operator s then ("( "^s^" )") else s;;

let rec ocaml_print_texp (_,e) =
  match e with
  | Exp_ident s -> ocaml_print (ocaml_op s)
  | Exp_qual_ident (s1,s2) -> ocaml_print (s1^"."^ocaml_op s2)
  | Exp_int i ->
      let s = string_of_int i in
      ocaml_print (if i >= 0 then s else ("("^s^")"))
  | Exp_string s -> ocaml_print ("\""^String.escaped s^"\"")
  | Exp_construct ("::",el) ->
     (if is_exp_list e then ocaml_print_exp_list "[" e else
      match el with
      | [e1; e2] ->
          ocaml_print "(";
          ocaml_print_texp e1;
          ocaml_print "::";
          ocaml_print_texp e2;
          ocaml_print ")"
      | _ -> raise (Unknown_ml_exp e))
  | Exp_construct (s,el) ->
      ocaml_print ("("^s);
      if el <> [] then
     (ocaml_print "(";
      ocaml_print_texp (hd el);
      iter (fun e' -> ocaml_print ","; ocaml_print_texp e') (tl el);
      ocaml_print ")");
      ocaml_print ")"
  | Exp_tuple el ->
      if el = [] then ocaml_print "()" else
     (ocaml_print "(";
      ocaml_print_texp (hd el);
      iter (fun e' -> ocaml_print ","; ocaml_print_texp e') (tl el);
      ocaml_print ")")
  | Exp_function pl ->
      (if exists (fun (p,_,_) -> nontrivial false p) pl then
        unbaked "Exp_function");
      ocaml_print ("("^(if length pl = 1 then "fun" else "function")^" ");
      ocaml_print_gcases pl;
      ocaml_print ")"
  | Exp_apply (e',el) ->
      ocaml_print "(";
      ocaml_print_texp e';
      iter (fun e' -> ocaml_print " "; ocaml_print_texp e') el;
      ocaml_print ")"
  | Exp_match (e',pl) ->
      ocaml_print "(match ";
      ocaml_print_texp e';
      ocaml_print " with ";
      ocaml_print_gcases pl;
      ocaml_print ")"
  | Exp_try (e',pl) ->
      ocaml_print "(try ";
      ocaml_print_texp e';
      ocaml_print " with ";
      ocaml_print_gcases pl;
      ocaml_print ")"
  | Exp_let (r,pl,e') ->
      (if not r &&
          (length pl != 1 or exists (fun (p,_) -> nontrivial false p) pl) then
        unbaked "Exp_let");
      ocaml_print ("(let "^if r then "rec " else "");
      ocaml_print_cases pl;
      ocaml_print " in ";
      ocaml_print_texp e';
      ocaml_print ")"
  | Exp_sequence (e1,e2) ->
     (ocaml_print "(";
      ocaml_print_texp e1;
      ocaml_print "; ";
      ocaml_print_texp e2;
      ocaml_print ")")
  | Exp_ifthenelse (e1,e2,e3) ->
      ocaml_print "(if ";
      ocaml_print_texp e1;
      ocaml_print " then ";
      ocaml_print_texp e2;
      ocaml_print " else ";
      ocaml_print_texp e3;
      ocaml_print ")"
  | Exp_constraint (e,t) ->
      unbaked "Exp_constraint";
      ocaml_print "(";
      ocaml_print_texp e;
      ocaml_print ":";
      ocaml_print_typ t;
      ocaml_print ")"

and ocaml_print_exp_list s l =
  ocaml_print s;
  match l with
  | Exp_construct ("[]",[]) -> ocaml_print "]"
  | Exp_construct ("::",[e1; (_,l')]) ->
      ocaml_print_texp e1; ocaml_print_exp_list "; " l'
  | _ -> failwith "ocaml_print_exp_list"

and ocaml_print_tpat (_,p) =
  match p with
  | Pat_any -> ocaml_print "_"
  | Pat_var s -> ocaml_print (ocaml_op s)
  | Pat_int i ->
      let s = string_of_int i in
      ocaml_print (if i >= 0 then s else ("("^s^")"))
  | Pat_string s -> ocaml_print ("\""^String.escaped s^"\"")
  | Pat_construct ("::",pl) ->
     (if is_pat_list p then ocaml_print_pat_list "[" p else
      match pl with
      | [p1; p2] ->
          ocaml_print "(";
          ocaml_print_tpat p1;
          ocaml_print "::";
          ocaml_print_tpat p2;
          ocaml_print ")"
      | _ -> raise (Unknown_ml_pat p))
  | Pat_construct (s,pl) ->
      ocaml_print ("("^s);
      if pl <> [] then
     (ocaml_print "(";
      ocaml_print_tpat (hd pl);
      iter (fun p' -> ocaml_print ","; ocaml_print_tpat p') (tl pl);
      ocaml_print ")");
      ocaml_print ")"
  | Pat_tuple pl ->
      if pl = [] then ocaml_print "()" else
     (ocaml_print "(";
      ocaml_print_tpat (hd pl);
      iter (fun p' -> ocaml_print ","; ocaml_print_tpat p') (tl pl);
      ocaml_print ")")
  | Pat_constraint (p,t) ->
      (if !check_pat_constraints then unbaked "Pat_constraint");
      ocaml_print "(";
      ocaml_print_tpat p;
      ocaml_print ":";
      ocaml_print_typ t;
      ocaml_print ")"
  | Pat_alias (p',s) ->
      unbaked "Pat_alias";
      ocaml_print "(";
      ocaml_print_tpat p';
      ocaml_print (" as "^s^")")
  | Pat_or (p1,p2) ->
      unbaked "Pat_or";
      ocaml_print "(";
      ocaml_print_tpat p1;
      ocaml_print " | ";
      ocaml_print_tpat p2;
      ocaml_print ")"

and ocaml_print_pat_list s l =
  ocaml_print s;
  match l with
  | Pat_construct ("[]",[]) -> ocaml_print "]"
  | Pat_construct ("::",[p1; (_,l')]) ->
      ocaml_print_tpat p1; ocaml_print_pat_list "; " l'
  | _ -> failwith "ocaml_print_pat_list"

and ocaml_print_case b (p,e) =
  match snd p with
  | Pat_var s' ->
      let (sl,e') = collect_args [] e in
      ocaml_print (ocaml_op s');
      iter (fun s'' -> ocaml_print (" "^s'')) sl;
      ocaml_print " = ";
      ocaml_print_texp e'
  | Pat_constraint ((_,Pat_var _),_) ->
      ocaml_print_tpat p;
      ocaml_print " = ";
      ocaml_print_texp e
  | _ ->
      (if b then unbaked "Exp_let");
      ocaml_print_tpat p;
      ocaml_print " = ";
      ocaml_print_texp e

and ocaml_print_cases pl =
  ocaml_print_case true (hd pl);
  iter (fun p -> ocaml_print " and "; ocaml_print_case true p) (tl pl)
  
and ocaml_print_gcase (p,g,e) =
  ocaml_print_tpat p;
 (match g with
  | Some e' ->
      unbaked "Exp_when";
      ocaml_print " when ";
      ocaml_print_texp e'
  | None -> ());
  ocaml_print " -> ";
  ocaml_print_texp e

and ocaml_print_gcases pl =
  ocaml_print_gcase (hd pl);
  iter (fun p -> ocaml_print " | "; ocaml_print_gcase p) (tl pl);;

let ocaml_print_vcase (t,p,e) =
  match p with
  | (_,Pat_constraint(p',t')) when !check_pat_constraints ->
      ocaml_print "(";
      ocaml_print_tpat p';
      ocaml_print ":";
      ocaml_print_typ t';
      ocaml_print ")";
      ocaml_print " = ";
      ocaml_print_texp e
  | _ -> ocaml_print_case false (p,e);;

let ocaml_print_vcases pl =
  ocaml_print_vcase (hd pl);
  iter (fun p -> ocaml_print " and "; ocaml_print_vcase p) (tl pl);;

let ocaml_print_type_decl b (s,al,d) =
 (if al <> [] then
   (ocaml_print "(";
    ocaml_print_typ (hd al);
    iter (fun t -> ocaml_print ","; ocaml_print_typ t) (tl al);
    ocaml_print ") "));
  ocaml_print (s^" = "^b);
  match d with
  | Type_abbrev t -> ocaml_print_typ t
  | Type_variant dl ->
      iter (fun (s,tl') ->
        ocaml_print " | ";
        ocaml_print s;
        if tl' <> [] then
         (ocaml_print " of ";
          ocaml_print_typ (hd tl');
          iter (fun t -> ocaml_print " * "; ocaml_print_typ t) (tl tl'))) dl;;

let ocaml_print_sig_item s =
  match s with
  | Sig_value (s,t) ->
      ocaml_print ("val "^s^" : ");
      ocaml_print_typ t;
      ocaml_print "\n"
  | Sig_type (s,al,d) ->
      ocaml_print "type ";
     (match d with
      | None ->
         (if al <> [] then
           (ocaml_print "(";
            ocaml_print_typ (hd al);
            iter (fun t -> ocaml_print ","; ocaml_print_typ t) (tl al);
            ocaml_print ") "));
          ocaml_print s
      | Some d' ->
          ocaml_print_type_decl "private " (s,al,d'));
      ocaml_print "\n";;

let rec ocaml_print_str_item b s =
  match s with
  | Str_eval e ->
      ocaml_print_texp e;
      ocaml_print b
  | Str_value (r,pl) ->
      ocaml_print ("let "^if r then "rec " else "");
      ocaml_print_vcases pl;
      ocaml_print b
  | Str_type dl ->
      ocaml_print "type ";
      ocaml_print_type_decl "" (hd dl);
      iter (fun d -> ocaml_print " and "; ocaml_print_type_decl "" d) (tl dl);
      ocaml_print b
  | Str_exception (s,al) ->
      ocaml_print ("exception "^s);
      if al <> [] then
       (ocaml_print " of ";
        ocaml_print_typ (hd al);
        iter (fun t' -> ocaml_print " * "; ocaml_print_typ t') (tl al));
      ocaml_print b
  | Str_install_printer s ->
      ocaml_print ("#install_printer "^s^b)
  | Str_modtype (i,sl) ->
      ocaml_print ("module type "^i^" = sig\n");
      iter ocaml_print_sig_item sl;
      ocaml_print ("end"^b)
  | Str_module (i1,i2,sl) ->
      ocaml_print ("module "^i1^" : "^i2^" = struct\n\n");
      iter (ocaml_print_str_item "\n\n") sl;
      ocaml_print ("end"^b)
  | Str_include i ->
      ocaml_print ("include "^i^b);;

(*
let rec find_differences n l1 l2 =
  match l1,l2 with
  | [],[] -> []
  | _,[] -> map (fun x1 -> (Some x1,None),n) l1
  | [],_ -> map (fun x2 -> (None,Some x2),n) l2
  | x1::l1',x2::l2' ->
      (if x1 = x2 then [] else [(Some x1,Some x2),n])@
      find_differences (n + 1) l1' l2';;

let rec untype_tpat p =
  Typ_var_anon,
  match snd p with
  | Pat_construct (s,pl) -> Pat_construct (s,map untype_tpat pl)
  | Pat_tuple pl -> Pat_tuple (map untype_tpat pl)
  | Pat_constraint (p',t) -> Pat_constraint(untype_tpat p',t)
  | Pat_alias (p',s) -> Pat_alias (untype_tpat p',s)
  | Pat_or (p1,p2) -> Pat_or (untype_tpat p1,untype_tpat p2)
  | p' -> p';;

let rec untype_texp e =
  Typ_var_anon,
  match snd e with
  | Exp_construct (s,el) -> Exp_construct (s,map untype_texp el)
  | Exp_tuple el -> Exp_tuple (map untype_texp el)
  | Exp_function pl -> Exp_function (untype_gcases pl)
  | Exp_apply (e',el) -> Exp_apply (untype_texp e',map untype_texp el)
  | Exp_match (e',pl) -> Exp_match (untype_texp e',untype_gcases pl)
  | Exp_try (e',pl) -> Exp_try (untype_texp e',untype_gcases pl)
  | Exp_let (b,pl,e') -> Exp_let (b,untype_cases pl,untype_texp e')
  | Exp_sequence (e',e'') -> Exp_sequence (untype_texp e',untype_texp e'')
  | Exp_ifthenelse (e',e'',e''') ->
      Exp_ifthenelse (untype_texp e',untype_texp e'', untype_texp e''')
  | Exp_constraint (e',t) -> Exp_constraint (untype_texp e',t)
  | e' -> e'

and untype_cases pl =
  map (fun (p,e) -> (untype_tpat p,untype_texp e)) pl

and untype_gcases pl =
  map (fun (p,g,e) -> (untype_tpat p,
    (match g with Some e' -> Some (untype_texp e') | None -> None),
    untype_texp e)) pl;;

let untype_vcases pl =
  map (fun (t,p,e) -> (t,untype_tpat p,untype_texp e)) pl;;

let untype_str_item s =
  match s with
  | Str_eval e -> Str_eval (untype_texp e)
  | Str_value (b,pl) -> Str_value (b,untype_vcases pl)
  | _ -> s;;

let rec typs_of_tpat p =
  fst p::
  match snd p with
  | Pat_construct (_,pl) -> flat (map typs_of_tpat pl)
  | Pat_tuple pl -> flat (map typs_of_tpat pl)
  | Pat_constraint (p',_) -> typs_of_tpat p'
  | Pat_alias (p',_) -> typs_of_tpat p'
  | Pat_or (p1,p2) -> typs_of_tpat p1@typs_of_tpat p2
  | _ -> [];;

let rec typs_of_texp e =
  fst e::
  match snd e with
  | Exp_construct (_,el) -> flat (map typs_of_texp el)
  | Exp_tuple el -> flat (map typs_of_texp el)
  | Exp_function pl -> typs_of_gcases pl
  | Exp_apply (e',el) -> typs_of_texp e'@flat (map typs_of_texp el)
  | Exp_match (e',pl) -> typs_of_texp e'@typs_of_gcases pl
  | Exp_try (e',pl) -> typs_of_texp e'@typs_of_gcases pl
  | Exp_let (b,pl,e') -> typs_of_cases pl@typs_of_texp e'
  | Exp_sequence (e1,e2) -> typs_of_texp e1@typs_of_texp e2
  | Exp_ifthenelse (e1,e2,e3) ->
      typs_of_texp e1@typs_of_texp e2@typs_of_texp e3
  | Exp_constraint (e',_) -> typs_of_texp e'
  | _ -> []

and typs_of_cases pl =
  flat (map (fun (p,e) -> typs_of_tpat p@typs_of_texp e) pl)

and typs_of_gcases pl =
  flat (map (fun (p,g,e) -> typs_of_tpat p@
    (match g with Some e' -> typs_of_texp e' | None -> [])@
    typs_of_texp e) pl);;

let typs_of_vcases pl =
  flat (map (fun (_,p,e) -> typs_of_tpat p@typs_of_texp e) pl);;

let typs_of_str_item s =
  match s with
  | Str_eval e -> typs_of_texp e
  | Str_value (_,pl) -> typs_of_vcases pl
  | _ -> [];;

let typs_of_all sl = flat (map typs_of_str_item sl);;

let d = find_differences 0 str_items_baked !str_items;;
length d;;
map untype_str_item str_items_baked = map untype_str_item !str_items;;

setify (map fst (find_differences 0
  (typs_of_all str_items_baked) (typs_of_all !str_items)));;

iter (fun (t1,t2) ->
  match t1,t2 with
  | Some t1,Some t2 ->
      ocaml_print_typ t1; ocaml_print " = "; ocaml_print_typ t2; ocaml_print "\n"
  | _ -> failwith "foo") foo;;

let ((Some s1,Some s2),n) = hd d;;
#ocaml_print_depth 1000000;;
#ocaml_print_length 1000000;;
s1;;
s2;;
#ocaml_print_depth 100;;
#ocaml_print_length 300;;

iter (function
    | ((Some (Str_value (_,((_,(_,Pat_var s),_)::_))),_),_) ->
	ocaml_print (s^"\n")
    | ((Some (Str_value (_,((_,(_,Pat_constraint((_,Pat_var s),_)),_)::_))),
          _),_) ->
	ocaml_print (s^"\n")
    | ((Some (Str_value (_,((_,(_,Pat_tuple pl),_)::_))),_),_) ->
        let s_of = function (_,Pat_var s) -> s
	  | (_,Pat_constraint((_,Pat_var s),_)) -> s
	  | _ -> "foo1" in
	iter (fun s -> ocaml_print (s^" ")) (map s_of pl);
	ocaml_print "\n"
    | _ -> ocaml_print "foo\n") d;;
*)

