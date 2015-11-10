(*Start converting the internal AST towards a more ML-like AST*)
let strip_exp_constraints = ref true;;
let strip_pat_constraints = ref false;;
let strip_functions = ref true;;
let strip_lets = ref true;;
let take_out_lets = ref true;;

let dummy_var = "v__";;

let rec has_as p =
  match snd p with
  | Pat_construct (_,pl) -> exists has_as pl
  | Pat_tuple pl -> exists has_as pl
  | Pat_constraint (p',_) -> has_as p'
  | Pat_alias (_,_) -> true
  | Pat_or (p1,p2) -> has_as p1 or has_as p2
  | _ -> false;;

let needs_dummy pl =
  exists (fun (p,g,_) ->
    match g with Some _ -> true | _ -> has_as p) pl;;

let rec has_anon t =
  match t with
  | Typ_var_anon -> true
  | Typ_var _ -> false
  | Typ_arrow (t1,t2) -> has_anon t1 or has_anon t2
  | Typ_tuple tl -> exists has_anon tl
  | Typ_constr (_,tl) -> exists has_anon tl
  | Typ_qual_constr (_,_,tl) -> exists has_anon tl;;

let rec compatible_pat p1 p2 =
  match snd p1,snd p2 with
  | Pat_any,_ | _,Pat_any | Pat_var _,_ | _,Pat_var _ -> true
  | Pat_constraint (p1,_),_ -> compatible_pat p1 p2
  | _,Pat_constraint (p2,_) -> compatible_pat p1 p2
  | Pat_alias (p1,_),_ -> compatible_pat p1 p2
  | _,Pat_alias (p2,_) -> compatible_pat p1 p2
  | Pat_or (p1a,p1b),_ -> compatible_pat p1a p2 or compatible_pat p1b p2
  | _,Pat_or (p2a,p2b) -> compatible_pat p1 p2a or compatible_pat p1 p2b
  | Pat_int i1,Pat_int i2 -> i1 = i2
  | Pat_string s1,Pat_string s2 -> s1 = s2
  | Pat_construct (s1,pl1),Pat_construct (s2,pl2) ->
      s1 = s2 && for_all2 compatible_pat pl1 pl2
  | Pat_tuple pl1,Pat_tuple pl2 -> for_all2 compatible_pat pl1 pl2
  | _,_ -> false;;

let rec remove_guards pl =
  match pl with
  | [] -> []
  | (p,None,e)::pl' -> (p,None,e)::remove_guards pl'
  | (((t,_) as p),Some e',((t',_) as e))::pl' ->
      let pl'' = remove_guards pl' in
      (p,None,(t',Exp_ifthenelse (e',e,
        (t',Exp_match ((t,Exp_ident dummy_var),
          filter (fun (p'',_,_) -> compatible_pat p p'') pl'')))))::
      (filter (fun (p'',_,_) -> p <> p'') pl'');;

let rec split_tpat p =
  let t = fst p in
  match snd p with
  | Pat_construct (s,pl) ->
      map (fun pl' -> t,Pat_construct (s,pl')) (split_tpat_list pl)
  | Pat_tuple pl ->
      map (fun pl' -> t,Pat_tuple pl') (split_tpat_list pl)
  | Pat_constraint (p,t') ->
      map (fun p' -> t,Pat_constraint(p',t')) (split_tpat p)
  | Pat_alias (p,s) ->
      map (fun p' -> t,Pat_alias(p',s)) (split_tpat p)
  | Pat_or (p1,p2) -> (split_tpat p1)@(split_tpat p2)
  | _ -> [p]
  
and split_tpat_list pl =
  match pl with
  | [] -> [[]]
  | p::pl ->
      let p' = split_tpat p in
      let pl' = split_tpat_list pl in
      flatten (map (fun p'' -> map (fun pl'' -> p''::pl'') pl') p');;

let rec (merge_tpats : ml_tpat -> ml_tpat list ->
  ml_tpat list -> ml_tpat list list -> ml_tpat list list) =
  fun q ql pl pll ->
    match pl,pll with
    | [],[] -> []
    | p'::pl',[] -> (p'::map (fun q' -> (fst q',Pat_any)) ql)::
	merge_tpats q ql pl' []
    | [],pl''::pll' -> ((fst q,Pat_any)::pl'')::
	merge_tpats q ql [] pll'
    | p'::pl',pl''::pll' -> (p'::pl'')::merge_tpats q ql pl' pll';;

let rec (split_as : ml_tpat -> ml_tpat list) =
  fun p ->
    match p with
    | (t,Pat_construct (s,pl)) ->
        map (fun pl' -> (t,Pat_construct (s,pl'))) (split_as_list pl)
    | (t,Pat_tuple pl) ->
        map (fun pl' -> (t,Pat_tuple pl')) (split_as_list pl)
    | (t,Pat_constraint (p,t')) ->
        map (fun p' -> (t,Pat_constraint (p',t'))) (split_as p)
    | (t,Pat_alias (p,s)) ->
        split_as p@[(t,Pat_var s)]
    | (t,Pat_or (p1,p2)) ->
        map (fun pl' -> (t,Pat_or (hd pl',hd (tl pl'))))
	  (split_as_list [p1; p2])
    | _ -> [p]

and split_as_list pl =
  match pl with
  | [] -> [[]]
  | p::pl ->
      let pl' = split_as p in
      let pll' = split_as_list pl in
      merge_tpats p pl pl' pll';;

let rec matchify pl e =
  match pl with
  | [] -> e
  | ((t,Pat_var _) as p)::pl' ->
      (fst e,Exp_let (false,[p,(t,Exp_ident dummy_var)],matchify pl' e))
  | p::pl' ->
      (fst e,Exp_match ((fst p,Exp_ident dummy_var),
        [p,None,matchify pl' e]));;

(*Bake, requiring type info for exprs*)
let rec bake_texp (t,e) =
  match e with
  | Exp_function pl ->
     (match pl with
      | [(_,Pat_var _),None,_] -> (t,bake_exp e)
      | [(_,Pat_constraint ((_,Pat_var _),_)),None,_] -> (t,bake_exp e)
      | _ -> if !strip_functions or needs_dummy pl then
	    let e'' =
	      match hd pl with
	      | ((t',_),_,(t'',_)) ->
		  Exp_function [(t',Pat_var dummy_var),None,(t'',
		    bake_exp (Exp_match ((t',Exp_ident dummy_var),
		      remove_guards pl)))] in
	    (t,e'')
	  else (t,bake_exp e))
  | Exp_match (((t',_) as e'),pl) ->
      if needs_dummy pl then
        let e'' = Exp_let (false,[(t',Pat_var dummy_var),e'],(t,
	  bake_exp (Exp_match ((t',Exp_ident dummy_var),
	    remove_guards pl)))) in
        (t,e'')
      else (t,bake_exp e)
  | Exp_try (e',pl) ->
      if needs_dummy pl then
        let t' = Typ_constr ("exn",[]) in
        let e'' = Exp_try (e',[(t',Pat_var dummy_var),None,(t,
	  bake_exp (Exp_match ((t',Exp_ident dummy_var),
	    remove_guards pl)))]) in
        (t,e'')
      else (t,bake_exp e)
  | Exp_apply (e',el) ->
      (*Specially handle LHS of an apply*)
      (t,Exp_apply (bake_texp e', map bake_texp el))
  | _ -> (t,bake_exp e)

(* Attempt at supporting generic compare by adding an extra type 
   parameter to func calls
and bake_apply (t,e) = 
  match e with
    Exp_qual_ident (_,funName) | Exp_ident (funName) ->
       (*For now, applied to ALL functions*)
       let funTy = Typ_var_anon in
       let tyStr =  (match t with
          Typ_arrow (Typ_constr (name,_),_) -> name
        | _ -> "unknown") in
        let e'' = Exp_apply
                          ((funTy,
                            Exp_ident funName), (*pre-gen generic version*)
                          [(Typ_arrow (Typ_var_anon,
                            Typ_arrow (Typ_var_anon, Typ_constr ("int", []))),
                            Exp_ident ("compare_"^tyStr))]) in
        (t,e'')
   | _ -> bake_texp (t,e)
*)

and bake_exp e =
  match e with
  | Exp_construct (s,el) ->
      Exp_construct (s,map bake_texp el)
  | Exp_tuple el ->
      Exp_tuple (map bake_texp el)
  | Exp_function pl ->
      Exp_function (bake_gcases pl)
  | Exp_match (e',pl) ->
      Exp_match (bake_texp e',bake_gcases pl)
  | Exp_try (e',pl) ->
      Exp_try (bake_texp e',bake_gcases pl)
  | Exp_let (r,pl,e') ->
      if not r && (!strip_lets or exists (has_as o fst) pl)
      then snd (bake_pat_let pl e')
      else Exp_let (r,bake_cases pl,bake_texp e')
  | Exp_sequence (e1,e2) ->
      Exp_sequence (bake_texp e1,bake_texp e2)
  | Exp_ifthenelse (e1,e2,e3) ->
      Exp_ifthenelse (bake_texp e1,bake_texp e2,bake_texp e3)
  | Exp_constraint (e',t) ->
      if !strip_exp_constraints then snd (bake_texp e') else
      Exp_constraint (bake_texp e',t)
(*
      let t' = expand_typ t in
      Exp_match (bake_texp e',
        [(t',Pat_constraint ((t',Pat_var dummy_var),t)),None,
	 (t',Exp_ident dummy_var)])
*)
  | _ -> e

and bake_tpat (t,p) =
  (t,bake_pat p)

and bake_pat p =
  match p with
  | Pat_construct (s,pl) -> Pat_construct (s,map bake_tpat pl)
  | Pat_tuple pl -> Pat_tuple (map bake_tpat pl)
  | Pat_constraint (p,t) ->
      if !strip_pat_constraints then snd (bake_tpat p) else
      Pat_constraint (bake_tpat p,t)
  | Pat_alias (p,s) -> Pat_alias (bake_tpat p,s)
  | Pat_or (p1,p2) -> Pat_or (bake_tpat p1,bake_tpat p2)
  | _ -> p

and bake_pat_let pl e =
  match pl with
  | [] -> bake_texp e
  | (((_,Pat_var _) as p),e')::pl' ->
      (fst e,Exp_let (false,[bake_tpat p,bake_texp e'],bake_pat_let pl' e))
  | (((_,Pat_constraint ((_,Pat_var _),_)) as p),e')::pl' ->
      (fst e,Exp_let (false,[bake_tpat p,bake_texp e'],bake_pat_let pl' e))
  | (p,e')::pl' ->
      if has_as p then
	let pl'' = map bake_tpat (split_as p) in
	if exists has_as pl'' then failwith "bake_pat_let";
	(fst e,Exp_let (false,[(fst p,Pat_var dummy_var),bake_texp e'],
	  matchify pl'' (bake_pat_let pl' e)))
      else if !strip_lets then
	(fst e,Exp_match (bake_texp e',[bake_tpat p,None,bake_pat_let pl' e]))
      else (fst e,Exp_let (false,[bake_tpat p,bake_texp e'],
        bake_pat_let pl' e))

and bake_cases pl =
  map (fun (p,e) -> (bake_tpat p,bake_texp e)) pl

and bake_gcases pl =
  flatten (map (fun (p,g,e) ->
      map (fun p' ->
          let pl' = split_as p' in
	  if exists has_as pl' then failwith "bake_gcases";
          let g' =
            match g with
            | None -> None
            | Some e'' -> Some (bake_texp e'') in
          let e' = bake_texp e in
          (hd pl',g',matchify (tl pl') e'))
        (split_tpat (bake_tpat p)))
    pl);;

let bake_vcases pl =
  map (fun (t,p,e) ->
    let p = bake_tpat p in
    let p' =
      match p with
      | _,Pat_constraint(_,_) -> p
      | _ when not (has_anon t) -> (fst p,Pat_constraint (p,t))
      | _ -> p in
    (t,p',bake_texp e)) pl;;

let rec vars_in p =
  match snd p with
  | Pat_var s -> [s]
  | Pat_construct (_,pl) -> unions (map vars_in pl)
  | Pat_tuple pl -> unions (map vars_in pl)
  | Pat_constraint (p',_) -> vars_in p'
  | Pat_alias (p',s) -> vars_in p'@[s]
  | Pat_or (p1,p2) -> vars_in p1@vars_in p2
  | _ -> [];;

let occurs_var s =
  let rec occurs_var p =
    match snd p with
    | Pat_var s' -> s' = s
    | Pat_construct (_,pl) -> exists occurs_var pl
    | Pat_tuple pl -> exists occurs_var pl
    | Pat_constraint (p',_) -> occurs_var p'
    | Pat_alias (p',s') -> s' = s or occurs_var p'
    | Pat_or (p1,p2) -> occurs_var p1 or occurs_var p2
    | _ -> false in
  occurs_var;;

let rec subst_var sl e =
  fst e,
  let e = snd e in
  match e with
  | Exp_ident s -> (try Exp_ident (assoc s sl) with _ -> e)
  | Exp_construct (s,el) -> Exp_construct (s,map (subst_var sl) el)
  | Exp_tuple el -> Exp_tuple map (subst_var sl) el
  | Exp_apply (e',el) -> Exp_apply (subst_var sl e',map (subst_var sl) el)
  | Exp_function pl -> Exp_function (map (subst_gcase sl) pl)
  | Exp_match (e',pl) -> Exp_match (subst_var sl e',map (subst_gcase sl) pl)
  | Exp_try (e',pl) -> Exp_try (subst_var sl e',map (subst_gcase sl) pl)
  | Exp_let (r,pl,e) ->
      let sl' = subtract' sl (unions (map (vars_in o fst) pl)) in
      Exp_let (r,map (fun (p,e') ->
	  (p,if r then subst_var sl' e' else subst_var sl e')) pl,
	subst_var sl' e)
  | Exp_sequence (e1,e2) -> Exp_sequence (subst_var sl e1,subst_var sl e2)
  | Exp_ifthenelse (e1,e2,e3) ->
      Exp_ifthenelse (subst_var sl e1,subst_var sl e2,subst_var sl e3)
  | Exp_constraint (e',t) -> Exp_constraint (subst_var sl e',t)
  | _ -> e 

and subst_gcase sl (p,g,e) =
  let sl' = subtract' sl (vars_in p) in
  match g with
  | Some e' -> (p,Some (subst_var sl' e'),subst_var sl' e)
  | None -> (p,None,subst_var sl' e)

and subtract' l k =
  filter (fun x -> not (mem (fst x) k)) l;;

let is_operator =
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

let bake_ops =
  ["o","op__circ";
   "--","op__upto";
   "@","op__append";
   "^","op__concat";
   "-.","op__minusf";
   "lxor","op__lxor";
   "land","op__land";
   "|->","op__mapsto";
   "|=>","op__Mapsto";
   "||","op__or";
   "++","op__seq";
   ">>","op__treat";
   "lsl","op__lsl";
   ];;

let op s = if is_operator s then
    try assoc s bake_ops with _ -> failwith "op"
  else s;;

let rec flatten_lets fl =
  let rec noclash s =
    if mem s fl then noclash (s^"'") else s in
  let rec sl_of s p =
    match p with
    | (_,Pat_any) -> []
    | (_,Pat_var s') -> [s',noclash ("l__"^op s')]
    | (_,Pat_construct (_,pl)) -> flatten (map (sl_of s) pl)
    | (_,Pat_tuple pl) -> flatten (map (sl_of s) pl)
    | (_,Pat_constraint (p',_)) -> sl_of s p'
    | _ -> failwith "flatten_lets" in
  let rec p_of sl p =
    match p with
    | (t,Pat_any) -> (t,Pat_any)
    | (t,Pat_var s') -> (t,Pat_var (assoc s' sl))
    | (t,Pat_construct (s',pl)) -> (t,Pat_construct (s',map (p_of sl) pl))
    | (t,Pat_tuple pl) -> (t,Pat_tuple (map (p_of sl) pl))
    | (t,Pat_constraint (p',t')) -> (t,Pat_constraint (p_of sl p',t'))
    | _ -> failwith "flatten_lets" in
  fun r pl ->
    if r then [Str_value (r,bake_vcases pl)] else
    if length pl != 1 then flatten (map (fun p -> flatten_lets fl r [p]) pl) else
    let (t,p,e) = hd pl in
    match e with
    | (_,Exp_let (r',pl',e'')) ->
	let s = op (match snd p with
	| Pat_var s -> s
	| Pat_constraint ((_,Pat_var s),_) -> s
	| Pat_tuple ((_,Pat_var s)::_) -> s
	| Pat_tuple ((_,Pat_constraint((_,Pat_var s),_))::_) -> s
	| Pat_construct ("::",(_,Pat_var s)::_) -> s
	| _ -> failwith "flatten_lets") in
	let sl = flatten (map (sl_of s o fst) pl') in
	flatten_lets fl r' (map (fun (p',e') -> (fst p',p_of sl p',
	  if r' then subst_var sl e' else e')) pl')@
	flatten_lets (fl@(map snd sl)) false [t,p,subst_var sl e'']
    | _ ->
      match p,e with
      | ((_,Pat_tuple pl),(_,Exp_tuple el)) ->
          flatten (map2 (fun p e -> flatten_lets fl false [fst p,p,e]) pl el)
      | _ -> [Str_value (false,bake_vcases pl)];;


(* Attempt to automatically generate an OCaml-like comparison function 
   for datatypes
(*for a single monomorphic datatype, equality for now

let eq (x,y) = 
match (x,y) with
  (Ala,Ala) -> true
|  _ -> false;;
*)

(*Generate the appropriate any pattern vars to match
    e.g. Ctor (_,_)*) 
let rec toAnyPat ls = 
  match ls with [] -> []
  |    (x::xs) -> (x,Pat_any) :: toAnyPat xs;;

(*Generate the obvious comparisons across different constructors*) 
let rec genComparisons_1 base_ty ls =
  match ls with
    [] -> []
  | ((a,b)::xs) -> 
      let rec mk ls = match ls
        with [] -> []
        |    ((c,d)::ys) -> 
                   ((Typ_tuple [base_ty; base_ty],
                     Pat_tuple
                     [(base_ty, Pat_construct (a,toAnyPat b));
                      (base_ty, Pat_construct (c,toAnyPat d))]),
                    None,
                    (Typ_constr ("int", []), Exp_int (-1)))::
                   mk ys
      in
        (mk xs) @ (genComparisons_1 base_ty xs);;

(*Generate enumerated pattern vars to match using a prefix string
    e.g. Ctor (l1,l2)*)
let rec toNamedPat str num ls =
  match ls with [] -> []
  |    (x::xs) -> 
         (x,Pat_var (str^(string_of_int num)))::toNamedPat str (num+1) xs
(*Generate the typed calls to comparator*)
let rec toCompare leftstr rightstr num ls =
  match ls with [] -> []
  |    (x::xs) ->
         (match x with Typ_constr(name,args) ->
         (Typ_constr ("int",[]),
          Exp_apply ((Typ_arrow (x,Typ_arrow (x,Typ_constr("int",[]))),
                      Exp_ident ("compare_"^name)), 
                     [(x,Exp_ident (leftstr^(string_of_int num)));
                      (x,Exp_ident (rightstr^(string_of_int num)))]))
         | _ ->  (Typ_constr ("int",[]), Exp_int (0))) 
         :: toCompare leftstr rightstr (num+1) xs;;

(*Generate the comparisons within a constructor with a catchall->false*)
let rec genComparisons_2 base_ty ls = 
  match ls with
    [] -> [((Typ_tuple [base_ty; base_ty],
                   Pat_any),
                  None,
                  (Typ_constr ("int", []), Exp_int 1))]
  | ((a,b)::xs) ->
      let comps = toCompare "l_" "r_" 0 b in
      let rec mk ls = match ls with
        [x] -> x
      | (x::xs) -> (Typ_constr ("int", []),
                   Exp_match
                    (x,
                    [((Typ_constr ("int", []), Pat_int 0), None,
                      mk xs);
                     ((Typ_constr ("int", []), Pat_var "x"), None,
                      (Typ_constr ("int", []), Exp_ident "x"))]))
in
    ((Typ_tuple [base_ty; base_ty],
      Pat_tuple [(base_ty, Pat_construct (a,toNamedPat "l_" 0 b));
                 (base_ty, Pat_construct (a,toNamedPat "r_" 0 b))]),
      None,
      (match b with [] -> (Typ_constr ("int", []), Exp_int (0))
                   | _ -> mk (toCompare "l_" "r_" 0 b)))
    ::(genComparisons_2 base_ty xs);;


let accum = ref ["data_sentinel"];;
(*To support polymorphism, need to pass the type as an argument*)
let bake_datatype d =
  match d with
  | (name,typlist,Type_variant ls) -> 
    let base_ty = Typ_constr(name,[]) in
    let fun_ty = Typ_arrow (base_ty,
                 Typ_arrow (base_ty, Typ_constr("int",[]))) in
    let (noargs,haveargs) = partition (fun (str,args) -> args = []) ls in
    let ls = noargs @ haveargs
    in
    (accum:=name::!accum;[Str_value (false,
      (*let x y = *)
      [(fun_ty, 
        (fun_ty,Pat_constraint ((fun_ty, Pat_var ("compare_"^name)),base_ty)),
        (fun_ty,
          Exp_function [((base_ty, Pat_var "x"), None,
           (Typ_arrow (base_ty, Typ_constr ("int", [])),
             Exp_function [((base_ty, Pat_var "y"), None,
              (Typ_constr ("int", []),
               (*match (x,y) with*)
               Exp_match
                ((Typ_tuple [base_ty; base_ty],
                  Exp_tuple
                   [(base_ty, Exp_ident "x");
                    (base_ty, Exp_ident "y")]),
                (*list of pattern -> expr*)
                genComparisons_1 base_ty ls @ genComparisons_2 base_ty ls
                )))]))]))])])  
    | _ -> []
*)

let rec bake_str_item s =
  match s with
  | Str_eval e -> [Str_eval (bake_texp e)]
  | Str_value (r,pl) ->
      if !take_out_lets then flatten_lets [] r pl
      else [Str_value (r,bake_vcases pl)]
  | Str_module (s1,s2,sl) -> [Str_module (s1,s2,flatten (map bake_str_item sl))]
  (*
  | Str_type ls -> s :: flatten (map bake_datatype ls)*)
  | _ -> [s];;

