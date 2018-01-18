open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     prettyTheory

val _ = new_theory"reader"

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);
val _ = temp_overload_on ("failwith", ``raise_Fail``);
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

(* TODO: these would translate to better code using PMATCH *)

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
    dict  : object spt; (* TODO keep two sptrees *)
    thms  : thm list;
    linum : int |>`;

val init_state_def = Define `
  init_state =
    <| stack := []
     ; dict  := LN
     ; thms  := []
     ; linum := 1 |>`;

val current_line_def = Define `
  current_line s = s.linum`;

val lines_read_def = Define `
  lines_read s = s.linum - 1`;

val next_line_def = Define `
  next_line s = s with linum := s.linum + 1`;

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
  find_axiom (ls, tm) =
    do
      (* axs <- axioms; *) (* the monadic translator wont figure this out *)
      axs <- get_the_axioms;
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

val BETA_CONV_def = Define `
  BETA_CONV tm =
    handle_Fail (BETA tm)
      (\e.
        handle_Fail
          (do
            (f, arg) <- dest_comb tm;
            (v, body) <- dest_abs f;
            tm <- mk_comb (f, v);
            thm <- BETA tm;
            INST [(arg, v)] thm
          od)
          (\e. failwith (strlit"BETA_CONV: not a beta-redex")))`;

(* ------------------------------------------------------------------------- *)
(* Debugging                                                                 *)
(* ------------------------------------------------------------------------- *)

val pad_def = tDefine "pad" `
  pad n s =
    if n < strlen s then
      pad (n + 4) s
    else
      concat (s::REPLICATE (n - strlen s) (strlit" "))`
 (WF_REL_TAC `measure (\x. strlen (SND x) - FST x)`);

val obj_t_def = tDefine "obj_t" `
  obj_t obj =
    case obj of
      Num n => mk_str (pad 8 (strlit"Num") ^ toString n)
    | Name s => mk_str (pad 8 (strlit"Name") ^ fix_name s)
    | List ls =>
        mk_blo 0
          ([mk_str (pad 8 (strlit"List")); mk_str (strlit"["); mk_brk 1] ++
           FLAT (MAP (\x. [obj_t x; mk_brk 1]) ls) ++
           [mk_str (strlit"]")])
    | TypeOp s => mk_str (pad 8 (strlit"TypeOp") ^ s)
    | Type ty => mk_blo 0 [mk_str (pad 8 (strlit"Type")); typ ty]
    | Const s => mk_str (pad 8 (strlit"Const") ^ fix_name s)
    | Var (s,ty) => mk_blo 0 [mk_str (pad 8 (strlit"Var") ^ s ^ strlit" : "); typ ty]
    | Term tm => mk_blo 0 [mk_str (pad 8 (strlit"Term")); term tm]
    | Thm th => mk_blo 0 [mk_str (pad 8 (strlit"Thm")); thm th]`
 (WF_REL_TAC `measure object_size`
  \\ Induct \\ rw [definition"object_size_def", pad_def]
  \\ res_tac
  \\ decide_tac);

val stack_t_def = Define `
  stack_t ls =
    mk_blo 0
      [mk_str (strlit"STACK"); mk_str newline; mk_str newline;
       mk_blo 0
         (FLAT (MAPi (\(i:num) x. [mk_str (pad 6 (toString &i ^ strlit ":"));
                                   obj_t x; mk_str newline]) ls))]`

val pair_t_def = Define `
  pair_t (k:num, v) =
    mk_blo 0 [mk_str (pad 4 (toString (&k)) ^ strlit" ->"); mk_brk 1; obj_t v]`

val dict_t_def = Define `
  dict_t (ds: object spt) =
    mk_blo 0 [mk_str (strlit"DICT"); mk_str newline; mk_str newline;
              mk_blo 0
                (FLAT (MAP (\(x,y). [pair_t (x,y); mk_str newline])
                (toAList ds)))]`

val reader_state_t_def = Define `
  reader_state_t s =
    mk_blo 0
      [ stack_t s.stack; mk_str newline; dict_t s.dict]`;

val state_to_string = Define `
  state_to_string s = pr (reader_state_t s) 78`;

(* ------------------------------------------------------------------------- *)
(* Article reader                                                            *)
(* ------------------------------------------------------------------------- *)

(* TODO The reader does not respect the "version" command. *)

val readLine_def = Define`
  readLine line s =
  if line = strlit"version" then
    do
      (obj, s) <- pop s; ver <- getNum obj;
      return s
    od
  else if line = strlit"absTerm" then
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
      (*th <- find_axiom (ls,tm);*)
      th <- find_axiom (ls,tm);
      return (push (Thm th) s)
    od
  else if line = strlit"betaConv" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- BETA_CONV tm;
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
      (* TODO this could be handled like "axiom" and allow the *)
      (* reader to fail early, since it will fail once the     *)
      (* constant is used unless it exists in the context.     *)
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
  else if line = strlit"deductAntisym" then
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
      if n < 0 then
        failwith (strlit"def")
      else
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
      (* th <- EQ_MP th1 th2; *)
      (* DEBUG: *)
      th <- handle_Fail (EQ_MP th1 th2)
              (\e. failwith (e ^ strlit ":\n" ^ thm_to_string th1
                               ^ strlit"\n" ^ thm_to_string th2));
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
    do (obj,s) <- pop s;
       name <- handle_Fail (getName obj)
                 (\e. return (strlit"bogus"));
       if name = strlit"debug" then
         failwith (state_to_string s)
       else
         return s
    od
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
      if n < 0 then
        failwith (strlit"ref")
      else
        case lookup (Num n) s.dict of
          NONE => failwith (strlit"ref")
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
      if n < 0 then
        failwith (strlit"ref")
      else
        case lookup (Num n) s.dict of
          NONE => failwith (strlit"remove")
        | SOME obj => return (push obj (delete_dict (Num n) s))
    od
  else if line = strlit"subst" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; (tys,tms) <- getPair obj;
      tys <- getList tys; tys <- map getTys tys;
      th <- handle_Clash
             (INST_TYPE tys th)
             (\e. failwith (strlit"the impossible"));
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
  else (* Integer literals and names *)
    case fromString line of
      SOME n => return (push (Num n) s)
    | NONE =>
        case explode line of
          #"\""::c::cs =>
            return (push (Name (implode (FRONT (c::cs)))) s)
        | _ => failwith (strlit"unrecognised input: " ^ line)`;

val line_Fail_def = Define `
  line_Fail s msg =
    (mlstring$concat
      [ strlit"Failure on line "
      ; toString (current_line s)
      ; strlit": "
      ; msg; strlit"\n"])`;

val fix_fun_typ_def = Define `
  fix_fun_typ s =
    if s = strlit"\"->\"" then
      strlit"\"fun\""
    else if s = strlit"\"select\"" then
      strlit"\"@\""
    else s`;

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val invalid_line_def = Define`
  invalid_line str ⇔ (strlen str) ≤ 1n ∨ strsub str 0 = #"#"`;

val readLines_def = Define `
  readLines lls s =
    case lls of
      []    => return (s, lines_read s)
    | l::ls =>
        if invalid_line l then
          readLines ls (next_line s)
        else
          do
            s <- handle_Fail
                   (readLine (fix_fun_typ (str_prefix l)) s)
                   (\e. raise_Fail (line_Fail s e));
            readLines ls (next_line s)
        od`;

val select_name_def = Define `select_name = strlit"@"`
val select_tm_def = Define `select_tm = Fun (Fun (Tyvar (strlit"A")) Bool) (Tyvar (strlit"A"))`
val select_const_def = Define `select_const = NewConst select_name select_tm`;

val ind_name_def = Define `ind_name = strlit"ind"`
val ind_ty_def = Define `ind_ty = NewType ind_name 0`;

val mk_reader_ctxt_def = Define `
  mk_reader_ctxt ctxt = select_const :: ind_ty :: ctxt`

(* TODO monadic translator wont accept this unless its a function? *)
val set_reader_ctxt = Define `
  set_reader_ctxt (): unit holKernelPmatch$M =
    do
      ts <- get_the_type_constants;
      cs <- get_the_term_constants;
      ctxt <- get_the_context;
      set_the_type_constants ((ind_name,0)::ts);
      set_the_term_constants ((select_name,select_tm)::cs);
      set_the_context (mk_reader_ctxt ctxt)
    od`

val _ = export_theory()

