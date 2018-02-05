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

val commas_def = Define `
  commas xs =
    case xs of
      [] => []
    | x::xs => mk_str(strlit", ") :: x :: commas xs`

val listof_def = Define `
  listof xs =
    case xs of
      [] => mk_str (strlit"[]")
    | x::xs =>
        mk_blo 0 ([mk_str (strlit"["); x] ++
                  commas xs ++
                  [mk_str (strlit"]")])`

val obj_t_def = tDefine "obj_t" `
  obj_t obj =
    case obj of
      Num n => mk_str (toString n)
    | Name s => mk_str (fix_name s)
    | List ls => listof (MAP obj_t ls)
    | TypeOp s => mk_str s
    | Type ty => typ ty
    | Const s => mk_str s
    | Var (s,ty) => mk_blo 0 [mk_str (s ^ strlit " :"); mk_brk 1; typ ty]
    | Term tm => term tm
    | Thm th => thm th`
 (WF_REL_TAC `measure object_size`
  \\ Induct \\ rw [definition"object_size_def"]
  \\ res_tac
  \\ decide_tac);

val obj_to_string_def = Define `
  obj_to_string t = pr (obj_t t) pp_margin`;

val state_to_string = Define `
  state_to_string s =
    let stack = concat (MAP (\t. obj_to_string t ^ strlit"\n") s.stack) in
    let dict  = concat [strlit"dict: [";
                        toString (LENGTH (toAList s.dict));
                        strlit"]\n"] in
    let thm   = concat [toString (LENGTH s.thms); strlit" theorems:\n"] in
    let thms  = concat (MAP (\t. thm_to_string t ^ strlit"\n") s.thms) in
      concat [stack; strlit"\n"; dict; thm; thms]`;

(* ------------------------------------------------------------------------- *)
(* Article reader                                                            *)
(* ------------------------------------------------------------------------- *)

(* TODO fromString is broken *)
val s2i_def = Define `
  s2i s = if s = strlit"" then NONE:int option else fromString s`

val _ = export_rewrites ["s2i_def"]

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
      (obj,s) <- pop s; nm <- getConst obj;
      ty0 <- get_const_type nm;
      tm <- case match_type ty0 ty of
            | NONE => failwith (strlit"constTerm")
            | SOME theta => mk_const(nm,theta);
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
      (obj,s) <- pop s; nm <- getName obj;
      (th1,th2) <- new_basic_type_definition nm abs rep th;
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
        (push (TypeOp nm)
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
       nm <- handle_Fail (getName obj)
                 (\e. return (strlit"bogus"));
       if nm = strlit"debug" then
         failwith (state_to_string s)
       else
         return s
    od
  else if line = strlit"proveHyp" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      (* These were called in the wrong order according to article semantics: *)
      (*th <- PROVE_HYP th1 th2;*)
      th <- PROVE_HYP th2 th1;
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
    case s2i line of
      SOME n => return (push (Num n) s)
    | NONE =>
        case explode line of
          #"\""::c::cs =>
            return (push (Name (implode (FRONT (c::cs)))) s)
        | _ => failwith (strlit"unrecognised input: " ^ line)`;

(* ------------------------------------------------------------------------- *)
(* Informative error messages                                                *)
(* ------------------------------------------------------------------------- *)

val line_Fail_def = Define `
  line_Fail s msg =
    (mlstring$concat
      [ strlit"Failure on line "
      ; toString (current_line s)
      ; strlit":\n"
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

(* TODO this could dump the theorem list *)
val msg_success_def = Define `
  msg_success s =
    let thm  = concat [toString (LENGTH s.thms); strlit" theorems:\n"] in
    let thms = concat (MAP (\t. thm_to_string t ^ strlit"\n") s.thms) in
      concat [strlit"OK! "; thm; strlit"\n"; thms]`;

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val msg_axioms_def = Define `
  msg_axioms e =
    concat[strlit"Could not initialise axioms:\n"; e; strlit "\n"]`;

(* ------------------------------------------------------------------------- *)
(* Using the reader                                                          *)
(* ------------------------------------------------------------------------- *)

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

val _ = export_theory()

