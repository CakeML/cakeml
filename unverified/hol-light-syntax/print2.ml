(*Internal AST to S/Cake ML concrete syntax*)
#use "print_util.ml";;

let sml_ppf = ref Format.std_formatter;; 

let sml_print s = Format.pp_print_string !sml_ppf s;;

let sml_space n = Format.pp_print_break !sml_ppf 1 n;;

let sml_emptyline () = Format.pp_print_cut !sml_ppf (); Format.pp_print_cut !sml_ppf ();;

(*Attempt to run parse_term within OCaml
  First define the primitive to string for the type system*)

let rec print_str s = "\""^s^"\"";;

let rec print_list f ls =
  (match ls with
    | [] -> ()
    | [x] -> (f x)
    | (x::xs) -> (print_list f [x]);sml_print",";print_list f xs);;

let rec print_hol_type t =
  (match t with
    |Tyvar s -> sml_print ("(Tyvar "^print_str s^")")
    |Tyapp (s,ls) -> sml_print ("(Tyapp ("^print_str s^", [");
                     print_list print_hol_type ls;
                     sml_print ("]))"));;

let rec print_hol_term t =
  (match t with
    | Var (s,t) -> sml_print("(Var ("^print_str s^",");
                 print_hol_type t;sml_print"))"
    | Const (s,t) -> sml_print ("(Const ("^print_str s^",");
                 print_hol_type t;sml_print"))"
    | Comb (t,t')-> sml_print ("(Comb (");
                  print_hol_term t; sml_print",";
                  print_hol_term t'; sml_print"))"
    | Abs (t,t')-> sml_print ("(Abs (");
                  print_hol_term t; sml_print",";
                  print_hol_term t'; sml_print"))");;

let rec sml_print_typ t =
  Format.pp_open_box !sml_ppf 0;
 (match t with
  | Typ_var s -> sml_print ("'"^s)
  | Typ_arrow (t1,t2) ->
      sml_print "(";
      sml_print_typ t1;
      sml_print " -> ";
      sml_print_typ t2;
      sml_print ")"
  | Typ_tuple al ->
      sml_print "(";
      sml_print_typ_tuple al;
      sml_print ")"
  | Typ_constr (s,al) ->
      if al <> [] then
       (sml_print "(";
        sml_print_typ (hd al);
        iter (fun t' -> sml_print ","; sml_print_typ t') (tl al);
        sml_print ") ");
        sml_print s
  | Typ_qual_constr (s1,s2,al) ->
      if al <> [] then
       (sml_print "(";
        sml_print_typ (hd al);
        iter (fun t' -> sml_print ","; sml_print_typ t') (tl al);
        sml_print ") ");
	if s1 != "Pervasives" then (sml_print s1; sml_print "__");
        sml_print s2
  | _ -> failwith "sml_print_typ");
  Format.pp_close_box !sml_ppf ()

and sml_print_typ_tuple al =
  match al with
  | [] -> failwith "sml_print_typ_tuple"
  | [t] -> sml_print_typ t
  | t::al' ->
      sml_print_typ t;
      sml_print " *";
      sml_space 0;
      sml_print_typ_tuple al';;

exception Unknown_ml_exp of ml_exp;;
exception Unknown_ml_pat of ml_pat;;

let sml_is_operator =
  let ht = Hashtbl.create 73 in
  let ct = Hashtbl.create 73 in
  List.iter (fun x -> Hashtbl.add ht x true)
    ["asr"; "land"; "lor"; "lsl"; "lsr"; "lxor"; "mod"; "or"; "o"; "upto";
     "F_F"; "THENC"; "THEN"; "THENL"; "ORELSE"; "ORELSEC";
     "THEN_TCL"; "ORELSE_TCL"; "op";"nil";];
  List.iter (fun x -> Hashtbl.add ct x true)
    ['!'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '='; '>'; '@'; '^'; '|'; '~';
     '?'; '%'; '.'; '$'];
  fun x ->
    try Hashtbl.find ht x with
    Not_found -> try Hashtbl.find ct x.[0] with _ -> false;;

let cake_ops =
  ["=","=";
   "==","=";
   ":=",":=";
   "+","+";
   "-","-";
   "*","*";
   "/","div";
   "mod","mod";
   "<","<";
   "<=","<=";
   ">",">";
   ">=",">=";
   "<>","<>";
   "=/","=";
   "+/","+";
   "-/","-";
   "*/","*";
   "//","div";
   "</","<";
   "<=/","<=";
   ">/",">";
   ">=/",">=";
   "<>/","<>";
   "&","andalso";
   "or","orelse"; 
   "@","@";
   "^","^";
   ];;

let other_ops =
  bake_ops @
  ["!","!";
   "~-","~";
   "op","op__";
   "nil","nil__";
   ];;

let ops = (map fst cake_ops)@(map fst other_ops);;

let sml_op s = if sml_is_operator s then
   (*Todo: Fix currying*)
   (try (assoc s other_ops) with _ -> "(op "^s^" )")
  else s;;

let parse_ops = ["parse_as_prefix"
                ;"parse_as_binder"
                ;"parse_as_infix"
                ;"override_interface"
                ;"parse_term"]

let extract_string e =
  match e with
  | (_,Exp_string s) -> s

let extract_int e =
  match e with
  | (_,Exp_int i) -> i

(*Specially for infix*)
let extract_infix_tuple e =
  match e with
  | (_,Exp_tuple [e;(_,Exp_tuple[n;e'])]) -> 
    (extract_string e,(extract_int n,extract_string e'))

let empty () = sml_print "()";;

let rec do_parse e ls =
  match e with
  | "parse_as_prefix" -> parse_as_prefix (extract_string ls);empty()
  | "parse_as_binder" -> parse_as_binder (extract_string ls);empty()
  | "parse_as_infix" -> parse_as_infix (extract_infix_tuple ls);empty()
  | _ -> ();;

let rec sml_print_texp (_,e) =
  Format.pp_open_box !sml_ppf 1;
 (match e with
  | Exp_ident s -> sml_print (sml_op s)
  | Exp_qual_ident (s1,s2) ->
      if s1 = "Pervasives" then sml_print (sml_op s2)
      else sml_print (s1^"__"^(sml_op s2))
  | Exp_int i ->
      if i >= 0 then sml_print (string_of_int i)
      else sml_print ("(~"^string_of_int (-i)^")")
  | Exp_string s -> sml_print ("\""^String.escaped s^"\"")
  | Exp_construct ("::",el) ->
     (if is_exp_list e then sml_print_exp_list "[" e else
      match el with
      | [e1; e2] ->
          sml_print "(";
          sml_print_texp e1;
          sml_print "::";
          sml_print_texp e2;
          sml_print ")"
      | _ -> failwith "Unknown_ml_exp")
  | Exp_construct (s,el) ->
      sml_print ("("^s);
      if el <> [] then
     (sml_print "(";
      sml_print_texp (hd el);
      iter (fun e' -> sml_print ","; sml_print_texp e') (tl el);
      sml_print ")");
      sml_print ")"
  | Exp_tuple el ->
      if el = [] then sml_print "()" else
     (Format.pp_open_box !sml_ppf 1;
      sml_print "(";
      sml_print_texp (hd el);
      iter (fun e' -> sml_print ","; Format.pp_print_break !sml_ppf 0 0; sml_print_texp e')
        (tl el);
      sml_print ")";
      Format.pp_close_box !sml_ppf ())
  | Exp_function pl ->
      (if exists (fun (p,_,_) -> nontrivial false p) pl then
        failwith "Exp_function");
      sml_print ("("^if length pl = 1 then "fn " else failwith "Exp_function");
      sml_print_gcases pl;
      sml_print ")"
  | Exp_apply ((_,Exp_ident s),[e1; e2])
    when sml_is_operator s && can (assoc s) cake_ops ->
      sml_print "(";
      sml_print_texp e1;
      sml_print (" "^(assoc s cake_ops));
      sml_space 0;
      sml_print_texp e2;
      sml_print ")"
  | Exp_apply ((_,Exp_qual_ident ("Pervasives",s)),[e1; e2])
    when sml_is_operator s && can (assoc s) cake_ops ->
      sml_print "(";
      sml_print_texp e1;
      sml_print (" "^(assoc s cake_ops));
      sml_space 0;
      sml_print_texp e2;
      sml_print ")"
  | Exp_apply ((_,Exp_ident e),[ls])
    when mem e parse_ops ->
      do_parse e ls
  | Exp_apply ((_,Exp_ident "parse_term"),[(_,Exp_string s)]) ->
      print_hol_term (parse_term s)
  | Exp_apply (e',el) ->
      Format.pp_open_box !sml_ppf 2;
      sml_print "(";
      sml_print_texp e';
      iter (fun e' -> sml_space 0; sml_print_texp e') el;
      sml_print ")";
      Format.pp_close_box !sml_ppf ()
(*
  | Exp_apply ((_,Exp_ident "then_"),[e1; e2]) ->
      sml_print "(";
      sml_print_texp e1;
      sml_print " THEN";
      sml_space 0;
      sml_print_texp e2;
      sml_print ")"
  | Exp_apply ((_,Exp_ident "thenl_"),[e1; e2]) ->
      sml_print "(";
      sml_print_texp e1;
      sml_print " THENL";
      sml_space 0;
      sml_print_texp e2;
      sml_print ")"
*)
  | Exp_match (e',pl) ->
      Format.pp_open_vbox !sml_ppf 0;
      sml_print "(case ";
      sml_print_texp e';
      sml_print " of";
      sml_space 2;
      sml_print_gcases pl;
      sml_print ")";
      Format.pp_close_box !sml_ppf ()
  | Exp_try (e',pl) ->
      Format.pp_open_hvbox !sml_ppf 1;
      sml_print "(";
      sml_print_texp e';
      sml_space 0;
      sml_print "handle";
      sml_space 2;
      sml_print_gcases pl;
      sml_print ")";
      Format.pp_close_box !sml_ppf ()
  | Exp_let (r,pl,e') ->
      (if not r &&
          (length pl != 1 or exists (fun (p,_) -> nontrivial false p) pl) then
        failwith "Exp_let");
      Format.pp_open_box !sml_ppf 0;
      sml_print "(let ";
      sml_print_cases pl;
      sml_print " in";
      sml_space 0;
      sml_print_texp e';
      sml_space 0;
      sml_print "end)";
      Format.pp_close_box !sml_ppf ()
  | Exp_sequence (e1,e2) ->
     (sml_print "(";
      sml_print_texp e1;
      sml_print "; ";
      sml_print_texp e2;
      sml_print ")")
  | Exp_ifthenelse (e1,e2,e3) ->
      Format.pp_open_hovbox !sml_ppf 1;
      Format.pp_open_hovbox !sml_ppf 1;
      sml_print "(if ";
      sml_print_texp e1;
      sml_space 0;
      sml_print "then";
      sml_space 2;
      sml_print_texp e2;
      sml_space 0;
      sml_print "else";
      Format.pp_close_box !sml_ppf ();
      sml_space 2;
      sml_print_texp e3;
      sml_print ")";
      Format.pp_close_box !sml_ppf ()
  | _ -> failwith "sml_print_texp");
  Format.pp_close_box !sml_ppf ()

and sml_print_exp_list s l =
  sml_print s;
  match l with
  | Exp_construct ("[]",[]) -> sml_print "]"
  | Exp_construct ("::",[e; (_,Exp_construct ("[]",[]))]) ->
      sml_print_texp e; sml_print "]"
  | Exp_construct ("::",[e1; (_,l')]) ->
      sml_print_texp e1; sml_print_exp_list ", " l'
  | _ -> failwith "sml_print_exp_list"

and sml_print_tpat (_,p) =
  match p with
  | Pat_any -> sml_print "_"
  | Pat_var s -> sml_print (sml_op s)
  | Pat_int i ->
      let s = string_of_int i in
      sml_print (if i >= 0 then s else ("("^s^")"))
  | Pat_string s -> sml_print ("\""^String.escaped s^"\"")
  | Pat_construct ("::",pl) ->
     (if is_pat_list p then sml_print_pat_list "[" p else
      match pl with
      | [p1; p2] ->
          sml_print "(";
          sml_print_tpat p1;
          sml_print "::";
          sml_print_tpat p2;
          sml_print ")"
      | _ -> raise (Unknown_ml_pat p))
  | Pat_construct (s,pl) ->
      sml_print ("("^s);
      if pl <> [] then
     (sml_print " (";
      sml_print_tpat (hd pl);
      iter (fun p' -> sml_print ","; sml_print_tpat p') (tl pl);
      sml_print ")");
      sml_print ")"
  | Pat_tuple pl ->
      if pl = [] then sml_print "()" else
     (sml_print "(";
      sml_print_tpat (hd pl);
      iter (fun p' -> sml_print ","; sml_print_tpat p') (tl pl);
      sml_print ")")
  | Pat_constraint (p,t) -> sml_print_tpat p
  | _ -> failwith "sml_print_tpat"

and sml_print_pat_list s l =
  sml_print s;
  match l with
  | Pat_construct ("[]",[]) -> sml_print "]"
  | Pat_construct ("::",[e; (_,Pat_construct ("[]",[]))]) ->
      sml_print_tpat e; sml_print "]"
  | Pat_construct ("::",[p1; (_,l')]) ->
      sml_print_tpat p1; sml_print_pat_list ", " l'
  | _ -> failwith "sml_print_pat_list"

and sml_print_case xx h b (p,e) =
  match snd p with
  | Pat_var s'
  | Pat_constraint ((_,Pat_var s'),_) ->
      let (sl,e') = collect_args [] e in
      let sl' = extra_args 0 (fst e') [] in
      let sl'' = sl@sl' in
      (if h then (if sl'' = [] then sml_print "val " else sml_print "fun "));
      (if xx && sl'' = [] && not (has_anon (fst p)) then
	(sml_print ("("^sml_op s'^" : ");
	 sml_print_typ (fst p);
	 sml_print ")")
       else sml_print (sml_op s'));
      (*let sl'' = if mem s' ignored_list 
                 then "compare_unknown"::s'' else s'' in *)
      iter (fun s'' -> sml_print (" "^(sml_op s''))) sl'';
      sml_print " =";
      sml_space 2;
      Format.pp_open_box !sml_ppf 0;
      sml_print_texp e';
      iter (fun s'' -> sml_print (" "^(sml_op s''))) sl';
      Format.pp_close_box !sml_ppf ()
  | _ ->
      (if b then failwith "Exp_let");
      (if xx && not (has_anon (fst p)) then
        (sml_print "val (";
         sml_print_tpat p;
         sml_print " : ";
         sml_print_typ (fst p);
         sml_print ")")
       else sml_print_tpat p);
      sml_print " =";
      sml_space 2;
      sml_print_texp e

and sml_print_cases pl =
  sml_print_case false true true (hd pl);
  iter (fun p -> sml_print " and "; sml_print_case false false true p) (tl pl)
  
and sml_print_gcase (p,g,e) =
  Format.pp_open_box !sml_ppf 0;
  sml_print_tpat p;
 (match g with
  | Some e' -> failwith "Exp_when"
  | None -> ());
  sml_print " =>";
  sml_space 2;
  sml_print_texp e;
  Format.pp_close_box !sml_ppf ()

and sml_print_gcases pl =
  sml_print_gcase (hd pl);
  iter (fun p -> sml_space 0; sml_print "| "; sml_print_gcase p) (tl pl);;

let sml_print_vcase h (t,p,e) =
  match p with
  | (_,Pat_constraint(p',t')) -> sml_print_case true h false (p',e)
  | _ -> sml_print_case true h false (p,e);;

let sml_print_vcases pl =
  sml_print_vcase true (hd pl);
  iter (fun p -> sml_print " and "; sml_print_vcase false p) (tl pl);;

let sml_print_type_decl b (s,al,d) =
  let sml_print_variant (s,tl') =
    sml_print s;
    if tl' <> [] then
     (sml_print " of ";
      sml_print_typ (hd tl');
      iter (fun t -> sml_print " * "; sml_print_typ t) (tl tl')) in
 (match d with |Type_abbrev t -> sml_print"type "|Type_variant dl -> sml_print"datatype ");
 (if al <> [] then
   (sml_print "(";
    sml_print_typ (hd al);
    iter (fun t -> sml_print ","; sml_print_typ t) (tl al);
    sml_print ") "));
  sml_print (s^" = "^b);
  match d with
  | Type_abbrev t -> sml_print_typ t
  | Type_variant dl ->
      sml_print_variant (hd dl);
      iter (fun d -> sml_space 0; sml_print "| "; sml_print_variant d) (tl dl);;

let sml_print_sig_item s =
  match s with
  | Sig_value (s,t) ->
      sml_print ("val "^s^" : ");
      sml_print_typ t;
      sml_print "\n"
  | Sig_type (s,al,d) ->
      sml_print "type ";
     (match d with
      | None ->
         (if al <> [] then
           (sml_print "(";
            sml_print_typ (hd al);
            iter (fun t -> sml_print ","; sml_print_typ t) (tl al);
            sml_print ") "));
          sml_print s
      | Some d' ->
          sml_print_type_decl "private " (s,al,d'));
      sml_print "\n";;

let rec sml_print_str_item b s =
 (match s with
  | Str_eval e ->
      Format.pp_open_box !sml_ppf 0;
      sml_print "val _ = ";
      sml_print_texp e;
      sml_print b;
      Format.pp_close_box !sml_ppf ()
  | Str_value (r,pl) ->
      Format.pp_open_vbox !sml_ppf 0;
      sml_print_vcases pl;
      sml_print b;
      Format.pp_close_box !sml_ppf ()
  | Str_type dl ->
      Format.pp_open_box !sml_ppf 0;
      (*sml_print "datatype ";*)
      sml_print_type_decl "" (hd dl);
      iter (fun d -> sml_print " and "; sml_print_type_decl "" d) (tl dl);
      sml_print b;
      Format.pp_close_box !sml_ppf ()
  | Str_exception (s,al) ->
      Format.pp_open_box !sml_ppf 0;
      sml_print ("exception "^s);
      if al <> [] then
       (sml_print " of ";
        sml_print_typ (hd al);
        iter (fun t' -> sml_print " * "; sml_print_typ t') (tl al));
      sml_print b;
      Format.pp_close_box !sml_ppf ()
  | Str_install_printer s ->
      ()
  | Str_modtype (i,sl) ->
      ()
(*
      sml_print ("module type "^i^" = sig\n");
      iter sml_print_sig_item sl;
      sml_print ("end"^b)
*)
  | Str_module (i1,i2,sl) ->
      iter (sml_print_str_item ";") sl;
(*
      sml_print ("module "^i1^" : "^i2^" = struct\n\n");
      iter (sml_print_str_item "") sl;
      sml_print ("end"^b)
*)
  | Str_include i ->
      ()
(*
      sml_print ("include "^i^b)
*)
  );
  sml_emptyline ();;


let ocaml_to_sml str = 
  iter (sml_print_str_item ";") (flatten (map bake_str_item (flatten (process_string str))));;
