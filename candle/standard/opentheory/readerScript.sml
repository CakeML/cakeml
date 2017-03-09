open preamble holKernelTheory

val _ = new_theory"reader"

val _ = temp_overload_on ("monad_bind", ``ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``ex_return``);
val _ = temp_add_monadsyntax()

(* We just represent names in the string (dotted) format.
   To make the namespace more explicit, the following functions could
   be useful.

val _ = type_abbrev("name",``mlstring list # mlstring``);

val name_to_string_def = Define`
  (name_to_string ([],s) = s) ∧
  (name_to_string (n::ns,s) =
   strcat (strcat n (strlit".")) (name_to_string ns s))`;

val charlist_to_name_def = Define`
  (charlist_to_name ns a [#"""] = (REVERSE ns,implode(REVERSE a))) ∧
  (charlist_to_name ns a (#"\"::#"."::cs) = charlist_to_name ns (#"."::a) cs) ∧
  (charlist_to_name ns a (#"\"::#"""::cs) = charlist_to_name ns (#"""::a) cs) ∧
  (charlist_to_name ns a (#"\"::#"\"::cs) = charlist_to_name ns (#"\"::a) cs) ∧
  (charlist_to_name ns a (#"."::cs) = charlist_to_name (implode(REVERSE a)::ns) [] cs) ∧
  (charlist_to_name ns a (c::cs) = charlist_to_name ns (c::a) cs)`;

val qstring_to_name_def = Define`
  qstring_to_name s = charlist_to_name [] [] (TL(explode s))`;
*)

val _ = Datatype`
  object = Num int
         | Name mlstring
         | List (object list)
         | TypeOp mlstring
         | Type type
         | Const mlstring
         | Var (mlstring # type)
         | Term term
         | Thm thm`;

val getNum_def = Define`
  (getNum (Num n) = return n) ∧
  (getNum _ = failwith (strlit"getNum"))`;

val getName_def = Define`
  (getName (Name n) = return n) ∧
  (getName _ = failwith (strlit"getName"))`;

val getList_def = Define`
  (getList (List ls) = return ls) ∧
  (getList _ = failwith (strlit"getList"))`;

val getTypeOp_def = Define`
  (getTypeOp (TypeOp t) = return t) ∧
  (getTypeOp _ = failwith (strlit"getTypeOp"))`;

val getType_def = Define`
  (getType (Type t) = return t) ∧
  (getType _ = failwith (strlit"getType"))`;

val getConst_def = Define`
  (getConst (Const v) = return v) ∧
  (getConst _ = failwith (strlit"getConst"))`;

val getVar_def = Define`
  (getVar (Var v) = return v) ∧
  (getVar _ = failwith (strlit"getVar"))`;

val getTerm_def = Define`
  (getTerm (Term t) = return t) ∧
  (getTerm _ = failwith (strlit"getTerm"))`;

val getThm_def = Define`
  (getThm (Thm th) = return th) ∧
  (getThm _ = failwith (strlit"getThm"))`;

val _ = Datatype`
  state = <|
    stack : object list;
    dict : object spt;
    thms : thm list |>`;

val pop_def = Define`
  pop s =
  case s.stack of
  | [] => failwith (strlit"pop")
  | (h::t) => return (h,s with <| stack := t |>)`;

val peek_def = Define`
  peek s =
  case s.stack of
  | [] => failwith (strlit"peek")
  | (h::_) => return h`;

val push_def = Define`
  push obj s = s with <| stack := obj::s.stack |>`;

val insert_dict_def = Define`
  insert_dict k obj s =
    s with <| dict := insert k obj s.dict |>`;

val delete_dict_def = Define`
  delete_dict k s =
    s with <| dict := delete k s.dict |>`;

val first_def = Define`
  first p l =
    case l of
    | [] => NONE
    | (h::t) => if p h then SOME h else first p t`;

val find_axiom_def = Define`
  find_axiom (ls,tm) =
    do
      axs <- axioms;
      case first (λth.
        case th of
        | Sequent h c =>
            EVERY (λx. EXISTS (aconv x) h) ls ∧
            aconv c tm) axs of
      | NONE => failwith (strlit"find_axiom")
      | SOME ax => return ax
    od`;

val getPair_def = Define`
  (getPair (List [x;y]) = return (x,y)) ∧
  (getPair _ = failwith (strlit"getPair"))`;

val getTys_def = Define`
  getTys p =
    do
      (a,t) <- getPair p; a <- getName a; t <- getType t;
      return (t,mk_vartype a)
    od`;

val getTms_def = Define`
  getTms p =
    do
      (v,t) <- getPair p; v <- getVar v; t <- getTerm t;
      return (t,mk_var v)
    od`;

val getNvs_def = Define`
  getNvs p =
    do
      (n,v) <- getPair p; n <- getName n; v <- getVar v;
      return (mk_var (n,SND v),mk_var v)
    od`;

val getCns_def = Define`
  getCns p =
    do
      (n,_) <- dest_var (FST p);
      return (Const n)
    od`;

val readLine_def = Define`
  readLine line s =
  if line = strlit"absTerm" then
    do
      (obj,s) <- pop s; b <- getTerm obj;
      (obj,s) <- pop s; v <- getVar obj;
      tm <- mk_abs(mk_var v,b);
      return (push (Term tm) s)
    od
  else if line = strlit"absThm" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; v <- getVar obj;
      th <- ABS (mk_var v) th;
      return (push (Thm th) s)
    od
  else if line = strlit"appTerm" then
    do
      (obj,s) <- pop s; x <- getTerm obj;
      (obj,s) <- pop s; f <- getTerm obj;
      fx <- mk_comb (f,x);
      return (push (Term fx) s)
    od
  else if line = strlit"appThm" then
    do
      (obj,s) <- pop s; xy <- getThm obj;
      (obj,s) <- pop s; fg <- getThm obj;
      th <- MK_COMB (fg,xy);
      return (push (Thm th) s)
    od
  else if line = strlit"assume" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- ASSUME tm;
      return (push (Thm th) s)
    od
  else if line = strlit"axiom" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      (obj,s) <- pop s; ls <- getList obj; ls <- map getTerm ls;
      (* We only allow axioms already in the context *)
      (* and we return an alpha-equivalent variant *)
      (* (contrary to normal article semantics) *)
      th <- find_axiom (ls,tm);
      return (push (Thm th) s)
    od
  else if line = strlit"betaConv" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- BETA tm;
      return (push (Thm th) s)
    od
  else if line = strlit"cons" then
    do
      (obj,s) <- pop s; ls <- getList obj;
      (obj,s) <- pop s;
      return (push (List (obj::ls)) s)
    od
  else if line = strlit"const" then
    do
      (obj,s) <- pop s; n <- getName obj;
      return (push (Const n) s)
    od
  else if line = strlit"constTerm" then
    do
      (obj,s) <- pop s; ty <- getType obj;
      (obj,s) <- pop s; name <- getConst obj;
      ty0 <- get_const_type name;
      tm <- case match_type ty0 ty of
            | NONE => failwith (strlit"constTerm")
            | SOME theta => mk_const(name,theta);
      return (push (Term tm) s)
    od
  else if line = strlit"deductAntysim" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- DEDUCT_ANTISYM_RULE th1 th2;
      return (push (Thm th) s)
    od
  else if line = strlit"def" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      obj <- peek s;
      return (insert_dict (Num n) obj s)
    od
  else if line = strlit"defineConst" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      (obj,s) <- pop s; n <- getName obj;
      ty <- type_of tm;
      eq <- mk_eq (mk_var(n,ty),tm);
      th <- new_basic_definition eq;
      return (push (Thm th) (push (Const n) s))
    od
  else if line = strlit"defineConstList" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; ls <- getList obj; ls <- map getNvs ls;
      th <- INST ls th;
      th <- new_specification th;
      ls <- map getCns ls;
      return (push (Thm th) (push (List ls) s))
    od
  else if line = strlit"defineTypeOp" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; ls <- getList obj;
      (obj,s) <- pop s; rep <- getName obj;
      (obj,s) <- pop s; abs <- getName obj;
      (obj,s) <- pop s; name <- getName obj;
      (th1,th2) <- new_basic_type_definition name abs rep th;
      (_,a) <- dest_eq (concl th1);
      th1 <- ABS a th1;
      th2 <- SYM th2;
      (_,Pr) <- dest_eq (concl th2);
      (_,r) <- dest_comb Pr;
      th2 <- ABS r th2;
      return (
        (push (Thm th2)
        (push (Thm th1)
        (push (Const rep)
        (push (Const abs)
        (push (TypeOp name)
         s))))))
    od
  else if line = strlit"eqMp" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- EQ_MP th1 th2;
      return (push (Thm th) s)
    od
  else if line = strlit"hdTl" then
    do
      (obj,s) <- pop s; ls <- getList obj;
      case ls of
      | [] => failwith (strlit"hdTl")
      | (h::t) => return (push (List t) (push h s))
    od
  else if line = strlit"nil" then
    return (push (List []) s)
  else if line = strlit"opType" then
    do
      (obj,s) <- pop s; ls <- getList obj; args <- map getType ls;
      (obj,s) <- pop s; tyop <- getTypeOp obj;
      t <- mk_type(tyop,args);
      return (push (Type t) s)
    od
  else if line = strlit"pop" then
    do (_,s) <- pop s; return s od
  else if line = strlit"pragma" then
    do (_,s) <- pop s; return s od
  else if line = strlit"proveHyp" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- PROVE_HYP th1 th2;
      return (push (Thm th) s)
    od
  else if line = strlit"ref" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      case lookup (Num n) s.dict of
      | NONE => failwith (strlit"ref")
      | SOME obj => return (push obj s)
    od
  else if line = strlit"refl" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- REFL tm;
      return (push (Thm th) s)
    od
  else if line = strlit"remove" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      case lookup (Num n) s.dict of
      | NONE => failwith (strlit"remove")
      | SOME obj => return (push obj (delete_dict (Num n) s))
    od
  else if line = strlit"subst" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; (tys,tms) <- getPair obj;
      tys <- getList tys; tys <- map getTys tys;
      th <- INST_TYPE tys th;
      tms <- getList tms; tms <- map getTms tms;
      th <- INST tms th;
      return (push (Thm th) s)
    od
  else if line = strlit"sym" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      th <- SYM th;
      return (push (Thm th) s)
    od
  else if line = strlit"thm" then
    do
      (obj,s) <- pop s; c <- getTerm obj;
      (obj,s) <- pop s; h <- getList obj; h <- map getTerm h;
      (obj,s) <- pop s; th <- getThm obj;
      th <- ALPHA_THM th (h,c);
      return (s with <| thms := th::s.thms |>)
    od
  else if line = strlit"trans" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- TRANS th1 th2;
      return (push (Thm th) s)
    od
  else if line = strlit"typeOp" then
    do
      (obj,s) <- pop s; n <- getName obj;
      return (push (TypeOp n) s)
    od
  else if line = strlit"var" then
    do
      (obj,s) <- pop s; ty <- getType obj;
      (obj,s) <- pop s; n <- getName obj;
      return (push (Var (n,ty)) s)
    od
  else if line = strlit"varTerm" then
    do
      (obj,s) <- pop s; v <- getVar obj;
      return (push (Term (mk_var v)) s)
    od
  else if line = strlit"varType" then
    do
      (obj,s) <- pop s; n <- getName obj;
      return (push (Type (mk_vartype n)) s)
    od
  else
    let ls = explode line in
    case ls of
    | [] => failwith (strlit"readLine")
    | (c::cs) =>
      if c = #"\"" then
        return (push (Name (implode (FRONT cs))) s)
      else if c = #"-" then
        case fromDecString cs of
        | NONE => failwith (strlit"readLine")
        | SOME n => return (push (Num (int_neg(int_of_num n))) s)
      else
        case fromDecString ls of
        | NONE => failwith (strlit"readLine")
        | SOME n => return (push (Num (int_of_num n)) s)`;

val _ = export_theory()
