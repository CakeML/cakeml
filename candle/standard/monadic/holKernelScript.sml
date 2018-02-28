open preamble mlstringTheory holSyntaxExtraTheory ml_monadBaseTheory ml_monadBaseLib

val _ = new_theory "holKernel";
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

(* we reuse the datatypes of types and terms from the inference system *)

val type_size_def = holSyntaxTheory.type_size_def

(*
  type thm = Sequent of (term list * term)
*)

val _ = Hol_datatype `
  thm = Sequent of term list => term`;

(*
  We define a record that holds the state, i.e.

  let the_type_constants = ref ["bool",0; "fun",2]x

  let the_term_constants =
     ref [("=", mk_fun_ty aty (mk_fun_ty aty bool_ty))]

  let the_axioms = ref ([]:thm list)

  The context is the global theory context tracked by the inference system, and
  subsumes the above references. But we use them instead for efficiency (and to
  be close to HOL Light).
*)

val _ = Hol_datatype `
  hol_refs = <| the_type_constants : (mlstring # num) list ;
                the_term_constants : (mlstring # type) list ;
                the_axioms : thm list ;
                the_context : update list |>`;

(* the state-exception monad *)

val _ = Hol_datatype`
  hol_exn = Fail of mlstring | Clash of term`

(* val _ = Hol_datatype `
  hol_result = HolRes of 'a | HolErr of hol_exn`; *)

val _ = type_abbrev("M", ``: (hol_refs, 'a, hol_exn) M``);

(* deref/ref functions *)

val _ = define_monad_access_funs ``:hol_refs``;


(* failwith *)

val _ = define_monad_exception_functions ``:hol_exn`` ``:hol_refs``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);
val _ = temp_overload_on ("raise_clash", ``raise_Clash``);
val _ = temp_overload_on ("handle_clash", ``handle_Clash``);

(* others *)

val _ = Define `
  try f x msg = (f x otherwise failwith msg)`;

(* define failing lookup function *)

val _ = Define `
  assoc s l =
    dtcase l of
      [] => failwith (strlit "not in list")
    | ((x:'a,y:'b)::xs) => if s = x then do return y od else assoc s xs`;

val _ = Define `
  map f l =
    dtcase l of
      [] => return []
    | (h::t) => do h <- f h ;
                   t <- map f t ;
                   return (h::t) od`

(*
val _ = Define `
  app f l =
    case l of
      [] => return ()
    | (h::t) => do f h ; app f t od`

val _ = Define`
  first p l =
    case l of
      [] => NONE
    | (h::t) => if p h then SOME h else first p t`
*)

val _ = Define `
  forall p l =
    dtcase l of
      [] => return T
    | (h::t) => do ok <- p h ;
                   if ok then forall p t else return F od`

val _ = Define `
  subset l1 l2 = EVERY (\t. MEM t l2) l1`;

(*
  let get_type_arity s = assoc s (!the_type_constants)
*)

val _ = Define `
  get_type_arity s =
    do l <- get_the_type_constants ; assoc s l od`;

(*
  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)
*)

val add_def = Define `
  add_def d = do defs <- get_the_context ;
                 set_the_context (d::defs) od`;

val _ = Define`
  add_type (name,arity) =
    do ok <- can get_type_arity name ;
       if ok then failwith ((strlit"new_type: ") ^ name ^ (strlit" has already been declared"))
             else do ts <- get_the_type_constants ;
                     set_the_type_constants ((name,arity)::ts) od od`

val _ = Define `
  new_type (name,arity) =
    do add_type (name,arity);
       add_def (NewType name arity) od`;

(*
  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)
*)

val _ = Define `
  mk_type (tyop,args) =
    do arity <- try get_type_arity tyop
         ((strlit"mk_type: type ") ^ tyop ^ (strlit" has not been defined"));
       if arity = LENGTH args then
         return (Tyapp tyop args)
       else failwith ((strlit"mk_type: wrong number of arguments to ") ^ tyop)
    od`;

(*
  let mk_vartype v = Tyvar(v)
*)

val _ = Define `
  mk_vartype v = Tyvar v`;

(*
  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"
*)

val _ = Define `
  dest_type t =
    dtcase t of
      Tyapp s ty => do return (s,ty) od
    | Tyvar _ => do failwith (strlit"dest_type: type variable not a constructor") od`;

(*
  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s
*)

val _ = Define `
  dest_vartype t =
    dtcase t of
      Tyapp _ _ => do failwith (strlit "dest_vartype: type constructor not a variable") od
    | Tyvar s => do return s od`;

(*
  let is_type = can dest_type
*)

val _ = Define `
  is_type t = dtcase t of Tyapp s ty => T | _ => F`;

(*
  let is_vartype = can dest_vartype

  We optimise this by making it perform the pattern match directly.
*)

val _ = Define `
  is_vartype t = dtcase t of Tyvar _ => T | _ => F`;

(*
  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]
*)

val _ = tDefine "tyvars" `
  tyvars x =
    dtcase x of (Tyapp _ args) => itlist union (MAP tyvars args) []
            | (Tyvar tv) => [tv]`
 (WF_REL_TAC `measure (type_size)` THEN Induct_on `args`
  THEN FULL_SIMP_TAC (srw_ss()) [type_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN REPEAT (POP_ASSUM (MP_TAC o SPEC_ALL)) THEN REPEAT STRIP_TAC
  THEN DECIDE_TAC);

(*
  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty
*)


val _ = Define `
  rev_assocd a l d =
    dtcase l of
      [] => d
    | ((x,y)::l) => if y = a then x else rev_assocd a l d`;

val _ = tDefine "type_subst" `
  type_subst i ty =
    dtcase ty of
      Tyapp tycon args =>
         let args' = MAP (type_subst i) args in
         if args' = args then ty else Tyapp tycon args'
    | _ => rev_assocd ty i ty`
 (WF_REL_TAC `measure (type_size o SND)` THEN Induct_on `args`
  THEN FULL_SIMP_TAC (srw_ss()) [type_size_def]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN RES_TAC
  THEN REPEAT (POP_ASSUM (MP_TAC o SPEC_ALL)) THEN REPEAT STRIP_TAC
  THEN DECIDE_TAC);

(*
  let bool_ty = mk_type("bool",[]);;
  let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
  let aty = mk_vartype "A";;
  let bty = mk_vartype "B";;
*)

val _ = temp_overload_on("bool_ty",``mk_type(strlit"bool",[])``);
val _ = Define `mk_fun_ty ty1 ty2 = mk_type(strlit"fun",[ty1; ty2])`;
val _ = temp_overload_on("aty",``mk_vartype (strlit "A")``);
val _ = temp_overload_on("bty",``mk_vartype (strlit "B")``);

(*
  let get_const_type s = assoc s (!the_term_constants)
*)

val _ = Define `
  get_const_type s =
    do l <- get_the_term_constants ; assoc s l od`;

(*
  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> hd(tl(snd(dest_type(type_of s))))
    | Abs(Var(_,ty),t) -> mk_fun_ty ty (type_of t)
*)

val _ = Define `
  type_of tm =
    dtcase tm of
      Var _ ty => return ty
    | Const _ ty => return ty
    | Comb s _ => do ty <- type_of s ;
                     x <- dest_type ty ;
                     dtcase x of (_,_::ty1::_) => return ty1
                             | _ => failwith (strlit "match")
                  od
    | Abs (Var _ ty) t => do x <- type_of t; mk_fun_ty ty x od
    | _ => failwith (strlit "match") `

(*
  let aconv =
    let rec alphavars env tm1 tm2 =
      match env with
        [] -> tm1 = tm2
      | (t1,t2)::oenv ->
            (t1 = tm1 & t2 = tm2) or
            (t1 <> tm1 & t2 <> tm2 & alphavars oenv tm1 tm2) in
    let rec raconv env tm1 tm2 =
      (tm1 == tm2 & env = []) or
      match (tm1,tm2) with
        Var(_,_),Var(_,_) -> alphavars env tm1 tm2
      | Const(_,_),Const(_,_) -> tm1 = tm2
      | Comb(s1,t1),Comb(s2,t2) -> raconv env s1 s2 & raconv env t1 t2
      | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
                ty1 = ty2 & raconv ((x1,x2)::env) t1 t2
      | _ -> false in
    fun tm1 tm2 -> raconv [] tm1 tm2
*)

val _ = Define `
  alphavars env tm1 tm2 =
    dtcase env of
      [] => (tm1 = tm2)
    | (t1,t2)::oenv =>
         ((t1 = tm1) /\ (t2 = tm2)) \/
         ((t1 <> tm1) /\ (t2 <> tm2) /\ alphavars oenv tm1 tm2)`;

val _ = Define `
  raconv env tm1 tm2 =
    dtcase (tm1,tm2) of
      (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2) => raconv env s1 s2 /\ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2) =>
       (dtcase (v1,v2) of
          (Var n1 ty1, Var n2 ty2) => (ty1 = ty2) /\
                                      raconv ((v1,v2)::env) t1 t2
        | _ => F)
    | _ => F`;

val _ = Define `
  aconv tm1 tm2 = raconv [] tm1 tm2`;

(*
  let is_var = function (Var(_,_)) -> true | _ -> false
  let is_const = function (Const(_,_)) -> true | _ -> false
  let is_abs = function (Abs(_,_)) -> true | _ -> false
  let is_comb = function (Comb(_,_)) -> true | _ -> false
*)

val _ = Define `is_var x = dtcase x of (Var _ _) => T | _ => F`;
val _ = Define `is_const x = dtcase x of (Const _ _) => T | _ => F`;
val _ = Define `is_abs x = dtcase x of (Abs _ _) => T | _ => F`;
val _ = Define `is_comb x = dtcase x of (Comb _ _) => T | _ => F`;

(*
  let mk_var(v,ty) = Var(v,ty)
*)

val _ = Define `mk_var(v,ty) = Var v ty`;

(*
  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)
*)

val _ = Define `
  mk_const(name,theta) =
    do uty <- try get_const_type name
         (strlit "mk_const: not a constant name") ;
       return (Const name (type_subst theta uty))
    od`;

(*
  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"
*)

val _ = Define `
  mk_abs(bvar,bod) =
    dtcase bvar of
      Var n ty => return (Abs bvar bod)
    | _ => failwith (strlit "mk_abs: not a variable")`;

(*
  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when ty = type_of a -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"
*)

val _ = Define `
  mk_comb(f,a) =
    do tyf <- type_of f ;
       tya <- type_of a ;
       dtcase tyf of
         Tyapp (strlit "fun") [ty;_] => if tya = ty then return (Comb f a) else
                                 failwith (strlit "mk_comb: types do not agree")
       | _ => failwith (strlit "mk_comb: types do not agree")
    od`;

(*
  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"
*)

val _ = Define `
  dest_var tm = dtcase tm of Var s ty => return (s,ty)
                         | _ => failwith (strlit "dest_var: not a variable")`;

val _ = Define `
  dest_const tm = dtcase tm of Const s ty => return (s,ty)
                           | _ => failwith (strlit "dest_const: not a constant")`;

val _ = Define `
  dest_comb tm = dtcase tm of Comb f x => return (f,x)
                          | _ => failwith (strlit "dest_comb: not a combination")`;

val _ = Define `
  dest_abs tm = dtcase tm of Abs v b => return (v,b)
                         | _ => failwith (strlit "dest_abs: not an abstraction")`;

(*
  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
*)

(*
  let freesl tml = itlist (union o frees) tml []
*)

val _ = Define `
  freesl tml = itlist (union o frees) tml []`;

(*
  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s & freesin acc t
*)

val _ = Define `
  freesin acc tm =
    dtcase tm of
      Var _ _ => MEM tm acc
    | Const _ _ => T
    | Abs bv bod => freesin (bv::acc) bod
    | Comb s t => freesin acc s /\ freesin acc t`;

(*
  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv & vfree_in v bod
    | Comb(s,t) -> vfree_in v s or vfree_in v t
    | _ -> tm = v
*)

(*
  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

  The Abs case is modified slightly.
*)

val _ = Define `
  type_vars_in_term tm =
    dtcase tm of
      Var _ ty   => tyvars ty
    | Const _ ty => tyvars ty
    | Comb s t   => union (type_vars_in_term s) (type_vars_in_term t)
    | Abs v t    => union (type_vars_in_term v) (type_vars_in_term t)`

(*
  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

  This function requires a non-trivial terminiation proof. We make
  this a non-failing function to make it pure.
*)

val EXISTS_IMP = Q.prove(
  `!xs p. EXISTS p xs ==> ?x. MEM x xs /\ p x`,
  Induct THEN SIMP_TAC (srw_ss()) [EXISTS_DEF] THEN METIS_TAC []);

val MEM_subtract = Q.prove(
  `!y z x. MEM x (subtract y z) = (MEM x y /\ ~MEM x z)`,
  FULL_SIMP_TAC std_ss [subtract_def,MEM_FILTER] THEN METIS_TAC []);

val vfree_in_IMP = Q.prove(
  `!(t:term) x v. vfree_in (Var v ty) x ==> MEM (Var v ty) (frees x)`,
  HO_MATCH_MP_TAC (SIMP_RULE std_ss [] (vfree_in_ind))
  THEN REPEAT STRIP_TAC THEN Cases_on `x` THEN POP_ASSUM MP_TAC
  THEN ONCE_REWRITE_TAC [vfree_in_def,frees_def]
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN FULL_SIMP_TAC (srw_ss()) [MEM_union,MEM_subtract]
  THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_SIMP_TAC std_ss []);

(*
  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s & t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t & vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"
*)

val _ = Define `
  vsubst_aux ilist tm =
    dtcase tm of
      Var _ _ => rev_assocd tm ilist tm
    | Const _ _ => tm
    | Comb s t => let s' = vsubst_aux ilist s in
                  let t' = vsubst_aux ilist t in
                    Comb s' t'
    | Abs v s  => if ~is_var v then tm else
                  let ilist' = FILTER (\(t,x). x <> v) ilist in
                  if ilist' = [] then tm else
                  let s' = vsubst_aux ilist' s in
                  (* if s' = s then tm else --- commented out becuase it doesn't
                                             seem to fit Harrison's formalisation *)
                  if EXISTS (\(t,x). vfree_in v t /\ vfree_in x s) ilist'
                  then let v' = variant [s'] v in
                         Abs v' (vsubst_aux ((v',v)::ilist') s)
                  else Abs v s'`;

val vsubst_def = Define `
  vsubst theta tm =
    if theta = [] then return tm else
    do ok <- forall (\(t,x). do ty <- type_of t ;
                                vty <- dest_var x ;
                                return (ty = SND vty) od) theta ;
       if ok
       then return (vsubst_aux theta tm)
       else failwith (strlit "vsubst: Bad substitution list") od`

(*
  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if rev_assocd tm' env tm = tm then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f & x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y & t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
      fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin
*)

val my_term_size_def = Define `
  (my_term_size (Var _ _) = 1:num) /\
  (my_term_size (Const _ _) = 1) /\
  (my_term_size (Comb s1 s2) = 1 + my_term_size s1 + my_term_size s2) /\
  (my_term_size (Abs s1 s2) = 1 + my_term_size s1 + my_term_size s2)`;

val my_term_size_variant = Q.prove(
  `!avoid t. my_term_size (variant avoid t) = my_term_size t`,
  HO_MATCH_MP_TAC (variant_ind) THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [variant_def]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [] THEN RES_TAC
  THEN FULL_SIMP_TAC std_ss [my_term_size_def]);

val is_var_variant = Q.prove(
  `!avoid t. is_var (variant avoid t) = is_var t`,
  HO_MATCH_MP_TAC (variant_ind) THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [variant_def]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
  THEN SRW_TAC [] [] THEN RES_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [my_term_size_def,fetch "-" "is_var_def"]);

val my_term_size_vsubst_aux = Q.prove(
  `!t xs. EVERY (\x. is_var (FST x)) xs ==>
           (my_term_size (vsubst_aux xs t) = my_term_size t)`,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [my_term_size_def,Once (fetch "-" "vsubst_aux_def")]
    THEN Induct_on `xs` THEN1 (EVAL_TAC THEN SRW_TAC [] [my_term_size_def])
    THEN Cases
    THEN ASM_SIMP_TAC (srw_ss()) [EVERY_DEF,Once (fetch "-" "rev_assocd_def")]
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN Cases THEN SRW_TAC [] [] THEN Cases_on `q`
    THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "is_var_def",my_term_size_def])
  THEN ASM_SIMP_TAC (srw_ss()) [my_term_size_def,
         Once (fetch "-" "vsubst_aux_def"),LET_DEF]
  THEN reverse (SRW_TAC [] [my_term_size_def])
  THEN1 (Q.PAT_X_ASSUM `!bbbb. xx ==> bbb` MATCH_MP_TAC
         THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,FILTER,MEM_FILTER])
  THEN Cases_on `is_var t` THEN FULL_SIMP_TAC std_ss [my_term_size_variant]
  THEN Q.PAT_X_ASSUM `!bbbb. xx ==> bbb` MATCH_MP_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,FILTER,MEM_FILTER,is_var_variant])
  |> Q.SPECL [`t`,`[(Var v ty,x)]`]
  |> SIMP_RULE (srw_ss()) [EVERY_DEF,fetch "-" "is_var_def"]

val ZERO_LT_term_size = Q.prove(
  `!t. 0 < my_term_size t`,
  Cases THEN EVAL_TAC THEN DECIDE_TAC);

val inst_aux_def = tDefine "inst_aux" `
  (inst_aux (env:(term # term) list) tyin tm) =
    dtcase tm of
      Var n ty   => let ty' = type_subst tyin ty in
                    let tm' = if ty' = ty then tm else Var n ty' in
                    if rev_assocd tm' env tm = tm then return tm'
                    else raise_clash tm'
    | Const c ty => let ty' = type_subst tyin ty in
                    if ty' = ty then return tm else return (Const c ty')
    | Comb f x   => do f' <- inst_aux env tyin f ;
                       x' <- inst_aux env tyin x ;
                       if (f = f') /\ (x = x') then return tm
                                               else return (Comb f' x') od
    | Abs y t    => do (y':term) <- inst_aux [] tyin y ;
                       env' <- return ((y,y')::env) ;
                       handle_clash
                        (do t' <- inst_aux env' tyin t ;
                            return (Abs y' t') od)
                        (\w'.
                         if w' <> y' then failwith (strlit "clash") else
                         do temp <- inst_aux [] tyin t ;
                            y' <- return (variant (frees temp) y') ;
                            (v1,ty') <- dest_var y' ;
                            (v2,ty) <- dest_var y ;
                            t' <- inst_aux ((Var v1 ty,Var v1 ty')::env) tyin
                                    (vsubst_aux [(Var v1 ty,y)] t) ;
                            return (Abs y' t') od)
                    od`
  (WF_REL_TAC `measure (\(env,tyin,tm). my_term_size tm)`
   THEN SIMP_TAC (srw_ss()) [my_term_size_def]
   THEN REPEAT STRIP_TAC
   THEN FULL_SIMP_TAC std_ss [my_term_size_vsubst_aux]
   THEN DECIDE_TAC)

val _ = save_thm("inst_aux_def",inst_aux_def);

val _ = Define `
  inst tyin tm = if tyin = [] then return tm else inst_aux [] tyin tm`;

(*
  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination";;

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination";;
*)

val _ = Define `
  rator tm =
    dtcase tm of
      Comb l r => return l
    | _ => failwith (strlit "rator: Not a combination")`;

val _ = Define `
  rand tm =
    dtcase tm of
      Comb l r => return r
    | _ => failwith (strlit "rand: Not a combination")`;

(*
  let mk_eq =
    let eq = mk_const("=",[]) in
    fun (l,r) ->
      try let ty = type_of l in
          let eq_tm = inst [ty,aty] eq in
          mk_comb(mk_comb(eq_tm,l),r)
      with Failure _ -> failwith "mk_eq";;
*)

val _ = Define `
  mk_eq (l,r) =
    try (\(l,r).
           do ty <- type_of l ;
              eq <- mk_const(strlit"=",[]) ;
              eq_tm <- inst [(ty,aty)] eq ;
              t <- mk_comb(eq_tm,l) ;
              t <- mk_comb(t,r) ;
              return t
           od) (l,r) (strlit "mk_eq")`

(*
  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq";;

  let is_eq tm =
    match tm with
      Comb(Comb(Const("=",_),_),_) -> true
    | _ -> false;;
*)

val _ = Define `
  dest_eq tm =
    dtcase tm of
      Comb (Comb (Const (strlit "=") _) l) r => return (l,r)
    | _ => failwith (strlit "dest_eq")`;

val _ = Define `
  is_eq tm =
    dtcase tm of
      Comb (Comb (Const (strlit "=") _) l) r => T
    | _ => F`;

(*
  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c
*)

val _ = Define `dest_thm (Sequent asl c) = (asl,c)`;
val _ = Define `hyp (Sequent asl c) = asl`;
val _ = Define `concl (Sequent asl c) = c`;

(*
  let REFL tm =
    Sequent([],mk_eq(tm,tm))
*)

val _ = Define `
  REFL tm = do eq <- mk_eq(tm,tm); return (Sequent [] eq) od`;

(*
  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb(Comb(Const("=",_),l),m1),Comb(Comb(Const("=",_),m2),r)
        when aconv m1 m2 -> Sequent(term_union asl1 asl2,mk_eq(l,r))
    | _ -> failwith "TRANS"
*)

val _ = PmatchHeuristics.with_classic_heuristic Define `
  TRANS (Sequent asl1 c1) (Sequent asl2 c2) =
    dtcase (c1,c2) of
      (Comb (Comb (Const (strlit "=") _) l) m1, Comb (Comb (Const (strlit "=") _) m2) r) =>
        if aconv m1 m2 then do eq <- mk_eq(l,r);
                               return (Sequent (term_union asl1 asl2) eq) od
        else failwith (strlit "TRANS")
    | _ => failwith (strlit "TRANS")`

(* some in-kernel but derivable rules (TRANS is also in this category) *)

val _ = Define`
  SYM (Sequent asl eq) =
    dtcase eq of
      Comb (Comb (Const (strlit "=") t) l) r =>
        return (Sequent asl (Comb (Comb (Const (strlit "=") t) r) l))
    | _ => failwith (strlit "SYM")`;

val _ = Define`
  PROVE_HYP (Sequent asl1 c1) (Sequent asl2 c2) =
    return (Sequent (term_union asl2 (term_remove c2 asl1)) c1)`;

val _ = Define`
  (list_to_hypset [] a = a) ∧
  (list_to_hypset (h::hs) a =
   list_to_hypset hs (term_union [h] a))`;

val _ = Define`
  ALPHA_THM (Sequent h c) (h',c') =
  if aconv c c' then
    let h' = list_to_hypset h' [] in
    if EVERY (λx. EXISTS (aconv x) h') h then
      do
        bty <- bool_ty;
        tys <- map type_of h';
        if EVERY (λty. ty = bty) tys then
          return (Sequent h' c')
        else failwith (strlit "ALPHA_THM")
      od
    else failwith (strlit "ALPHA_THM")
  else failwith (strlit "ALPHA_THM")`;

(* -- *)

(*
  let MK_COMB (Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2)
        -> Sequent(term_union asl1 asl2,mk_eq(mk_comb(l1,l2),mk_comb(r1,r2)))
     | _ -> failwith "MK_COMB"
*)

val _ = PmatchHeuristics.with_classic_heuristic Define `
  MK_COMB (Sequent asl1 c1,Sequent asl2 c2) =
   dtcase (c1,c2) of
     (Comb (Comb (Const (strlit "=") _) l1) r1, Comb (Comb (Const (strlit "=") _) l2) r2) =>
       do x1 <- mk_comb(l1,l2) ;
          x2 <- mk_comb(r1,r2) ;
          eq <- mk_eq(x1,x2) ;
          return (Sequent(term_union asl1 asl2) eq) od
   | _ => failwith (strlit "MK_COMB")`

(*
  let ABS v (Sequent(asl,c)) =
    match c with
      Comb(Comb(Const("=",_),l),r) ->
        if exists (vfree_in v) asl
        then failwith "ABS: variable is free in assumptions"
        else Sequent(asl,mk_eq(mk_abs(v,l),mk_abs(v,r)))
    | _ -> failwith "ABS: not an equation"
*)

val _ = Define `
  ABS v (Sequent asl c) =
    dtcase c of
      Comb (Comb (Const (strlit "=") _) l) r =>
        if EXISTS (vfree_in v) asl
        then failwith (strlit "ABS: variable is free in assumptions")
        else do a1 <- mk_abs(v,l) ;
                a2 <- mk_abs(v,r) ;
                eq <- mk_eq(a1,a2) ;
                return (Sequent asl eq) od
    | _ => failwith (strlit "ABS: not an equation")`

(*
  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when arg = v -> Sequent([],mk_eq(tm,bod))
    | _ -> failwith "BETA: not a trivial beta-redex"
*)

val _ = Define `
  BETA tm =
    dtcase tm of
      Comb (Abs v bod) arg =>
        if arg = v then do eq <- mk_eq(tm,bod) ; return (Sequent [] eq) od
        else failwith (strlit "BETA: not a trivial beta-redex")
    | _ => failwith (strlit "BETA: not a trivial beta-redex")`

(*
  let ASSUME tm =
    if type_of tm = bool_ty then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"
*)

val _ = Define `
  ASSUME tm =
    do ty <- type_of tm ;
       bty <- bool_ty ;
       if ty = bty then return (Sequent [tm] tm)
       else failwith (strlit "ASSUME: not a proposition") od`;

(*
  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when aconv l c
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"
*)

val _ = Define `
  EQ_MP (Sequent asl1 eq) (Sequent asl2 c) =
    dtcase eq of
      Comb (Comb (Const (strlit "=") _) l) r =>
        if aconv l c then return (Sequent (term_union asl1 asl2) r)
                     else failwith (strlit "EQ_MP")
    | _ => failwith (strlit "EQ_MP")`

(*
  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',mk_eq(c1,c2))
*)

val _ = Define `
  DEDUCT_ANTISYM_RULE (Sequent asl1 c1) (Sequent asl2 c2) =
    let asl1' = term_remove c2 asl1 in
    let asl2' = term_remove c1 asl2 in
      do eq <- mk_eq(c1,c2) ;
         return (Sequent (term_union asl1' asl2') eq) od`

val _ = Define`
  image f l =
  dtcase l of
    [] => return l
  | (h::t) => do h' <- f h ;
                 t' <- image f t ;
                 return ( if (h' = h) ∧ (t' = t) then l
                          else term_union [h'] t' ) od`

(*
  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fun = inst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

val _ = Define `
  INST_TYPE theta (Sequent asl c) =
    let inst_fun = inst theta in
      do l <- image inst_fun asl ;
         x <- inst_fun c ;
         return (Sequent l x) od`

(*
  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

val _ = Define `
  INST theta (Sequent asl c) =
    let inst_fun = vsubst theta in
      do l <- image inst_fun asl ;
         x <- inst_fun c ;
         return (Sequent l x) od`

(*
  let axioms() = !the_axioms
*)

val _ = Define `axioms = get_the_axioms`;

(*
  let new_axiom tm =
    if fst(dest_type(type_of tm)) = "bool" then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"
*)

val new_axiom_def = Define `
  new_axiom tm =
    do ty <- type_of tm ;
       bty <- bool_ty ;
       if ty = bty then
         do th <- return (Sequent [] tm) ;
            ax <- get_the_axioms ;
            set_the_axioms (th :: ax) ;
            add_def (NewAxiom tm) ;
            return th od
       else
         failwith (strlit "new_axiom: Not a proposition")
    od`;

val _ = Define`
  first_dup ls acc =
  dtcase ls of
  | [] => NONE
  | (h::t) =>
    if MEM h acc then SOME h else first_dup t (h::acc)`

val _ = Define `
  add_constants ls =
    do cs <- get_the_term_constants ;
       dtcase first_dup (MAP FST ls) (MAP FST cs) of
       | SOME name => failwith ((strlit "add_constants: ") ^ name ^ (strlit " appears twice or has already been declared"))
       | NONE => set_the_term_constants (ls++cs) od`;

val _ = Define`
  new_specification (Sequent eqs p) =
    do eqs <-
         map (\e. do (l,r) <- dest_eq e;
                     (s,ty) <- dest_var l;
                     if ~(freesin [] r) then
                       failwith ((strlit "new_specification: witness for ") ^ s ^ (strlit " not closed"))
                     else if ~(subset (type_vars_in_term r) (tyvars ty)) then
                       failwith ((strlit "new_specification: type variables for ") ^ s ^ (strlit " not contained in the type"))
                     else return ((s,ty),r) od) eqs ;
       let vars = MAP FST eqs in
       if ~(freesin (MAP (UNCURRY Var) vars) p) then
         failwith (strlit "new_specification: specification not closed by the definitions")
       else do
         add_constants vars ;
         add_def (ConstSpec (MAP (\((s,ty),r). (s,r)) eqs) p) ;
         let ilist = MAP (\(s,ty). (Const s ty, Var s ty)) vars in
         let p = vsubst_aux ilist p in
         return (Sequent [] p) od od`

(*
  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)
*)

val _ = Define `
  new_constant (name,ty) =
    do add_constants [(name,ty)] ;
       add_def (NewConst name ty) od`;

val _ = Define`
  new_basic_definition tm = do th <- ASSUME tm ; new_specification th od`

(*
  let new_basic_definition tm =
    let l,r = dest_eq tm in
    let cname,ty = dest_var l in
    if not(freesin [] r) then failwith "new_definition: term not closed" else
    if not (subset (type_vars_in_term r) (tyvars ty))
    then failwith "new_definition: Type variables not reflected in constant"
    else
      let c = new_constant(cname,ty); mk_const(cname,[]) in
      Sequent([],mk_eq(c,r))
*)

(*

val _ = Define `
  new_basic_definition tm =
    do (l,r) <- dest_eq tm ;
       (cname,ty) <- dest_var l ;
       if ~(freesin [] r) then failwith "new_definition: term not closed" else
       if ~(subset (type_vars_in_term r) (tyvars ty))
       then failwith "new_definition: Type variables not reflected in constant"
       else do
         new_constant(cname,ty) ;
         add_def (Constdef cname r) ;
         c <- mk_const(cname,[]) ;
         eq <- mk_eq(c,r) ;
         return (Sequent [] eq)
       od od`
*)

(*
  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = mk_type(tyname,tyvars)
    and rty = type_of x in
    let abs = new_constant(absname,mk_fun_ty rty aty); mk_const(absname,[])
    and rep = new_constant(repname,mk_fun_ty aty rty); mk_const(repname,[]) in
    let a = mk_var("a",aty) and r = mk_var("r",rty) in
    Sequent([],mk_eq(mk_comb(abs,mk_comb(rep,a)),a)),
    Sequent([],mk_eq(mk_comb(P,r),mk_eq(mk_comb(rep,mk_comb(abs,r)),r)))
*)

val new_basic_type_definition_def = Define `
  new_basic_type_definition tyname absname repname thm =
    dtcase thm of (Sequent asl c) =>
    do ok0 <- can get_type_arity tyname ;
       ok1 <- can get_const_type absname ;
       ok2 <- can get_const_type repname ;
    if ok0 then failwith (strlit "new_basic_type_definition: Type already defined") else
    if ok1 \/ ok2 then failwith (strlit "new_basic_type_definition: Constant(s) already in use") else
    if absname = repname then failwith (strlit "new_basic_type_definition: Constants must be distinct") else
    if ~(asl = []) then
      failwith (strlit "new_basic_type_definition: Assumptions in theorem") else
    do (P,x) <- try dest_comb c (strlit "new_basic_type_definition: Not a combination") ;
    if ~(freesin [] P) then
      failwith (strlit "new_basic_type_definition: Predicate is not closed") else
    let tyvars = MAP Tyvar (MAP implode (QSORT string_le (MAP explode (type_vars_in_term P)))) in
    do rty <- type_of x ;
       add_type (tyname, LENGTH tyvars) ;
       aty <- mk_type(tyname,tyvars) ;
       repty <- mk_fun_ty aty rty ;
       absty <- mk_fun_ty rty aty ;
       add_constants[(absname,absty);(repname,repty)] ;
       add_def (TypeDefn tyname P absname repname) ;
       rep <- mk_const(repname,[]) ;
       abs <- mk_const(absname,[]) ;
       a <- return (mk_var((strlit "a"),aty)) ;
       r <- return (mk_var((strlit "r"),rty)) ;
       x1 <- mk_comb(rep,a) ;
       x2 <- mk_comb(abs,x1) ;
       eq1 <- mk_eq(x2,a) ;
       y1 <- mk_comb(abs,r) ;
       y2 <- mk_comb(rep,y1) ;
       y3 <- mk_comb(P,r) ;
       eq2 <- mk_eq(y2,r) ;
       eq3 <- mk_eq(y3,eq2) ;
       return (Sequent [] eq1, Sequent [] eq3) od od od`

val _ = export_theory();
