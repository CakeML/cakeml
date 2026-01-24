(*
  Shallowly embedded (monadic) functions that implement the OpenTheory
  article checker.
*)
Theory reader
Ancestors
  ml_hol_kernelProg mlint StringProg pretty
Libs
  preamble

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = SOME “raise_Failure”,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

Overload return[local] = “st_ex_return”;
Overload failwith[local] = “raise_Failure”;

(* -------------------------------------------------------------------------
 * Commands.
 * ------------------------------------------------------------------------- *)

(* OpenTheory VM commands.
 * See: http://www.gilith.com/opentheory/article.html.
 *)

Datatype:
  command = intc int
          | strc mlstring
          | unknownc mlstring
          | absTerm
          | absThm
          | appTerm
          | appThm
          | assume
          | axiom
          | betaConv
          | cons
          | const
          | constTerm
          | deductAntisym
          | def
          | defineConst
          | defineConstList
          | defineTypeOp
          | eqMp
          | hdTl
          | nil
          | opType
          | popc
          | pragma
          | proveHyp
          | ref
          | refl
          | remove
          | subst
          | sym
          | thm
          | trans
          | typeOp
          | var
          | varTerm
          | varType
          | version
          | skipc
End

(*
 * Expensive (string-comparisons) way of tokenizing the input.
 * TODO: Maybe: hash string?
 *)

Definition strh_aux_def:
  strh_aux s a n =
    if n ≥ strlen s then a else strh_aux s (13 * a + ORD (strsub s n)) (n + 1)
Termination
  WF_REL_TAC ‘measure (λ(s,a,n). strlen s - n)’
End

Definition strh_def:
  strh s = strh_aux s 0 0
End

fun str_hash mls = rconc (EVAL “strh ^(mls)”);

Definition s2c_def:
  s2c s =
    if strlen s = 0 then unknownc s else
      let c = strsub s 0 in
        if c = #"#" then skipc
        else if c = #"\"" then strc (substring s 1 (strlen s - 2))
        else if isDigit c then
          pmatch fromString s of
            NONE => unknownc s
          | SOME i => intc i
        else
          let h = strh s in
            if h = ^(str_hash “«absTerm»”) then absTerm
            else if h = ^(str_hash “«absThm»”) then absThm
            else if h = ^(str_hash “«appTerm»”) then appTerm
            else if h = ^(str_hash “«appThm»”) then appThm
            else if h = ^(str_hash “«assume»”) then assume
            else if h = ^(str_hash “«axiom»”) then axiom
            else if h = ^(str_hash “«betaConv»”) then betaConv
            else if h = ^(str_hash “«cons»”) then cons
            else if h = ^(str_hash “«const»”) then const
            else if h = ^(str_hash “«constTerm»”) then constTerm
            else if h = ^(str_hash “«deductAntisym»”) then deductAntisym
            else if h = ^(str_hash “«def»”) then def
            else if h = ^(str_hash “«defineConst»”) then defineConst
            else if h = ^(str_hash “«defineConstList»”) then defineConstList
            else if h = ^(str_hash “«defineTypeOp»”) then defineTypeOp
            else if h = ^(str_hash “«eqMp»”) then eqMp
            else if h = ^(str_hash “«hdTl»”) then hdTl
            else if h = ^(str_hash “«nil»”) then nil
            else if h = ^(str_hash “«opType»”) then opType
            else if h = ^(str_hash “«pop»”) then popc
            else if h = ^(str_hash “«pragma»”) then pragma
            else if h = ^(str_hash “«proveHyp»”) then proveHyp
            else if h = ^(str_hash “«ref»”) then ref
            else if h = ^(str_hash “«refl»”) then refl
            else if h = ^(str_hash “«remove»”) then remove
            else if h = ^(str_hash “«subst»”) then subst
            else if h = ^(str_hash “«sym»”) then sym
            else if h = ^(str_hash “«thm»”) then thm
            else if h = ^(str_hash “«trans»”) then trans
            else if h = ^(str_hash “«typeOp»”) then typeOp
            else if h = ^(str_hash “«var»”) then var
            else if h = ^(str_hash “«varTerm»”) then varTerm
            else if h = ^(str_hash “«varType»”) then varType
            else if h = ^(str_hash “«version»”) then version
            else unknownc s
End

(*
 * Line splitter for inputAllTokensFile.
 * (See readerProgScript.sml.)
 *)

Definition is_newline_def:
  is_newline c ⇔ c = #"\n"
End

(* -------------------------------------------------------------------------
 * Objects and functions on objects.
 * ------------------------------------------------------------------------- *)

(* We just represent names in the string (dotted) format.
   To make the namespace more explicit, the following functions could
   be useful.

Type name = ``mlstring list # mlstring``

Definition name_to_string_def:
  (name_to_string ([],s) = s) ∧
  (name_to_string (n::ns,s) =
   strcat (strcat n («.»)) (name_to_string ns s))
End

Definition charlist_to_name_def:
  (charlist_to_name ns a [#"""] = (REVERSE ns,implode(REVERSE a))) ∧
  (charlist_to_name ns a (#"\"::#"."::cs) = charlist_to_name ns (#"."::a) cs) ∧
  (charlist_to_name ns a (#"\"::#"""::cs) = charlist_to_name ns (#"""::a) cs) ∧
  (charlist_to_name ns a (#"\"::#"\"::cs) = charlist_to_name ns (#"\"::a) cs) ∧
  (charlist_to_name ns a (#"."::cs) = charlist_to_name (implode(REVERSE a)::ns) [] cs) ∧
  (charlist_to_name ns a (c::cs) = charlist_to_name ns (c::a) cs)
End

Definition qstring_to_name_def:
  qstring_to_name s = charlist_to_name [] [] (TL(explode s))
End
*)

Datatype:
  object = Num int
         | Name mlstring
         | List (object list)
         | TypeOp mlstring
         | Type type
         | Const mlstring
         | Var (mlstring # type)
         | Term term
         | Thm thm
End

Definition getNum_def:
  getNum (Num n) = return n ∧
  getNum _ = failwith «getNum»
End

Definition getName_def:
  getName (Name n) = return n ∧
  getName _ = failwith «getName»
End

Definition getList_def:
  getList (List ls) = return ls ∧
  getList _ = failwith «getList»
End

Definition getTypeOp_def:
  getTypeOp (TypeOp t) = return t ∧
  getTypeOp _ = failwith «getTypeOp»
End

Definition getType_def:
  getType (Type t) = return t ∧
  getType _ = failwith «getType»
End

Definition getConst_def:
  getConst (Const v) = return v ∧
  getConst _ = failwith «getConst»
End

Definition getVar_def:
  getVar (Var v) = return v ∧
  getVar _ = failwith «getVar»
End

Definition getTerm_def:
  getTerm (Term t) = return t ∧
  getTerm _ = failwith «getTerm»
End

Definition getThm_def:
  getThm (Thm th) = return th ∧
  getThm _ = failwith «getThm»
End

(*
 * OpenTheory virtual machine state.
 *)

Datatype:
  state = <|
    stack : object list; (* Machine stack                     *)
    dict  : object spt;  (* Persistent object storage         *)
    thms  : thm list;    (* Theorem export stack              *)
    linum : int          (* #commands processed (bookkeeping) *)
    |>
End

Definition init_state_def:
  init_state =
    <| stack := []
     ; dict  := LN
     ; thms  := []
     ; linum := 1
     |>
End

Definition current_line_def:
  current_line s = s.linum
End

Definition lines_read_def:
  lines_read s = s.linum - 1
End

Definition next_line_def:
  next_line s = s with linum := s.linum + 1
End

Definition pop_def:
  pop s =
    pmatch s.stack of
      [] => failwith «pop»
    | h::t => return (h,s with stack := t)
End

Definition peek_def:
  peek s =
    pmatch s.stack of
      [] => failwith «peek»
    | h::_ => return h
End

Definition push_def:
  push obj s = s with stack := obj::s.stack
End

Definition insert_dict_def:
  insert_dict k obj s =
    s with dict := insert k obj s.dict
End

Definition delete_dict_def:
  delete_dict k s =
    s with dict := delete k s.dict
End

Definition first_def:
  first p l =
    pmatch l of
      [] => NONE
    | h::t => if p h then SOME h else first p t
End

Definition find_axiom_def:
  find_axiom (ls, tm) =
    do
      axs <- axioms ();
      pmatch first (λth.
        pmatch th of
        | Sequent h c =>
            EVERY (λx. EXISTS (aconv x) h) ls ∧
            aconv c tm) axs of
      | NONE => failwith «find_axiom»
      | SOME ax => return ax
    od
End

Definition getPair_def:
  getPair (List [x;y]) = return (x,y) ∧
  getPair _ = failwith «getPair»
End

Definition getTys_def:
  getTys p =
    do
      (a,t) <- getPair p; a <- getName a; t <- getType t;
      return (t,mk_vartype a)
    od
End

Definition getTms_def:
  getTms p =
    do
      (v,t) <- getPair p; v <- getVar v; t <- getTerm t;
      return (t,mk_var v)
    od
End

Definition getNvs_def:
  getNvs p =
    do
      (n,v) <- getPair p; n <- getName n; v <- getVar v;
      return (mk_var (n,SND v),mk_var v)
    od
End

Definition getCns_def:
  getCns p =
    do
      (n,_) <- dest_var (FST p);
      return (Const n)
    od
End

Definition BETA_CONV_def:
  BETA_CONV tm =
    handle_Failure (BETA tm)
      (λe.
        handle_Failure
          (do
            (f, arg) <- dest_comb tm;
            (v, body) <- dest_abs f;
            tm <- mk_comb (f, v);
            thm <- BETA tm;
            INST [(arg, v)] thm
          od)
          (λe. failwith «BETA_CONV: not a beta-redex»))
End

(* -------------------------------------------------------------------------
 * Debugging.
 * ------------------------------------------------------------------------- *)

Definition commas_def:
  commas [] = [] ∧
  commas (x::xs) = mk_str «, » :: x :: commas xs
End

Definition listof_def:
  listof xs =
    pmatch xs of
      [] => mk_str «[]»
    | x::xs => mk_blo 0 ([mk_str «[»; x] ++ commas xs ++ [mk_str «]»])
End

Definition obj_t_def:
  obj_t obj =
    pmatch obj of
      Num n => mk_str (toString n)
    | Name s => mk_str (name_of s)
    | List ls => listof (MAP obj_t ls)
    | TypeOp s => mk_str s
    | Type ty => pp_type 0 ty
    | Const s => mk_str s
    | Term tm => pp_term 0 tm
    | Thm th => pp_thm th
    | Var (s,ty) => mk_blo 0 [mk_str s; mk_str «:»; mk_brk 1; pp_type 0 ty]
Termination
  WF_REL_TAC ‘measure object_size’
  \\ Induct \\ rw [definition"object_size_def"]
  \\ res_tac
  \\ decide_tac
End

Definition obj2str_applist_def:
  obj2str_applist t = pr (obj_t t) pp_margin
End

Overload AppendList[local] = “FOLDL SmartAppend Nil”;

Definition st2str_applist_def:
  st2str_applist s =
    let stack = AppendList (MAP (λt. Append (obj2str_applist t)
                                            (List [«\n»])) s.stack);
        dict  = List [«dict :[»; toString (LENGTH (toAList s.dict)); «]»];
        thm   = List [toString (LENGTH s.thms); « theorems:\n»];
        thms  = AppendList (MAP (λt. Append (thm2str_applist t)
                                            (List [«\n»])) s.thms) in
      AppendList [stack; List [«\n»]; dict; thm; thms]
End

(* -------------------------------------------------------------------------
 * Printing of the context.
 * ------------------------------------------------------------------------- *)

Definition pp_namepair_def:
  pp_namepair [] = [] ∧
  pp_namepair ((nm,tm)::t) =
    [mk_str «(»; mk_str nm; mk_str «, »; pp_term 0 tm; mk_str «)»] ++
    if t = [] then [] else mk_str «;»::mk_brk 1::pp_namepair t
End

Definition pp_update_def:
  pp_update upd =
    pmatch upd of
      ConstSpec nts tm =>
        mk_blo 11
          ([mk_str «ConstSpec»; mk_brk 1; mk_str «[»] ++
            pp_namepair nts ++
           [mk_str «]»; mk_brk 1; mk_str «with definition»; mk_brk 1;
            pp_term 0 tm])
    | TypeDefn nm pred abs_nm rep_nm =>
        mk_blo 9
          [mk_str «TypeDefn»; mk_brk 1; mk_str nm; mk_brk 1;
           mk_str «(absname »; mk_str abs_nm; mk_str «)»; mk_brk 1;
           mk_str «(repname »; mk_str rep_nm; mk_str «)»; mk_brk 1;
           pp_term 0 pred]
    | NewType nm arity =>
        mk_blo 8
          [mk_str «NewType»; mk_brk 1;
           mk_str nm; mk_brk 1;
           mk_str «(arity »; mk_str (toString arity); mk_str «)»]
    | NewConst nm ty =>
        mk_blo 9
          [mk_str «NewConst»; mk_brk 1;
           mk_str nm; mk_str « :»; mk_brk 1;
           pp_type 0 ty]
    | NewAxiom tm =>
        mk_blo 9
          [mk_str «NewAxiom»; mk_brk 1;
           pp_thm (Sequent [] tm)]
End

Definition upd2str_applist_def:
  upd2str_applist upd = pr (pp_update upd) pp_margin
End

(* -------------------------------------------------------------------------
 * Implementation of the article reader.
 * ------------------------------------------------------------------------- *)

(*
 * TODO The reader does not respect the "version" command.
 *)

Definition readLine_def:
  readLine s c =
    pmatch c of
      version =>
        do
          (obj, s) <- pop s;
          ver <- getNum obj;
          return s
        od
    | absTerm =>
        do
          (obj,s) <- pop s; b <- getTerm obj;
          (obj,s) <- pop s; v <- getVar obj;
          tm <- mk_abs(mk_var v,b);
          return (push (Term tm) s)
        od
    | absThm =>
        do
          (obj,s) <- pop s; th <- getThm obj;
          (obj,s) <- pop s; v <- getVar obj;
          th <- ABS (mk_var v) th;
          return (push (Thm th) s)
        od
    | appTerm =>
        do
          (obj,s) <- pop s; x <- getTerm obj;
          (obj,s) <- pop s; f <- getTerm obj;
          fx <- mk_comb (f,x);
          return (push (Term fx) s)
        od
    | appThm =>
        do
          (obj,s) <- pop s; xy <- getThm obj;
          (obj,s) <- pop s; fg <- getThm obj;
          th <- MK_COMB (fg,xy);
          return (push (Thm th) s)
        od
    | assume =>
        do
          (obj,s) <- pop s; tm <- getTerm obj;
          th <- ASSUME tm;
          return (push (Thm th) s)
        od
    | axiom =>
        do
          (obj,s) <- pop s; tm <- getTerm obj;
          (obj,s) <- pop s; ls <- getList obj; ls <- map getTerm ls;
          (* We only allow axioms already in the context *)
          (* and we return an alpha-equivalent variant *)
          (* (contrary to normal article semantics) *)
          th <- find_axiom (ls,tm);
          return (push (Thm th) s)
        od
    | betaConv =>
        do
          (obj,s) <- pop s; tm <- getTerm obj;
          th <- BETA_CONV tm;
          return (push (Thm th) s)
        od
    | cons =>
        do
          (obj,s) <- pop s; ls <- getList obj;
          (obj,s) <- pop s;
          return (push (List (obj::ls)) s)
        od
    | const =>
        do
          (* TODO this could be handled like "axiom" and allow the *)
          (* reader to fail early, since it will fail once the     *)
          (* constant is used unless it exists in the context.     *)
          (obj,s) <- pop s; n <- getName obj;
          return (push (Const n) s)
        od
    | constTerm =>
        do
          (obj,s) <- pop s; ty <- getType obj;
          (obj,s) <- pop s; nm <- getConst obj;
          ty0 <- get_const_type nm;
          tm <- pmatch match_type ty0 ty of
                  NONE => failwith «constTerm»
                | SOME theta => mk_const(nm,theta);
          return (push (Term tm) s)
        od
    | deductAntisym =>
        do
          (obj,s) <- pop s; th2 <- getThm obj;
          (obj,s) <- pop s; th1 <- getThm obj;
          th <- DEDUCT_ANTISYM_RULE th1 th2;
          return (push (Thm th) s)
        od
    | def =>
        do
          (obj,s) <- pop s; n <- getNum obj;
          obj <- peek s;
          if n < 0 then
            failwith «def»
          else
            return (insert_dict (Num n) obj s)
        od
    | defineConst =>
        do
          (obj,s) <- pop s; tm <- getTerm obj;
          (obj,s) <- pop s; n <- getName obj;
          ty <- call_type_of tm;
          eq <- mk_eq (mk_var(n,ty),tm);
          th <- new_basic_definition eq;
          return (push (Thm th) (push (Const n) s))
        od
    | defineConstList =>
        do
          (obj,s) <- pop s; th <- getThm obj;
          (obj,s) <- pop s; ls <- getList obj; ls <- map getNvs ls;
          th <- INST ls th;
          th <- new_specification th;
          ls <- map getCns ls;
          return (push (Thm th) (push (List ls) s))
        od
    | defineTypeOp =>
        do
          (obj,s) <- pop s; th <- getThm obj;
          (obj,s) <- pop s; ls <- getList obj;
          (obj,s) <- pop s; rep <- getName obj;
          (obj,s) <- pop s; abs <- getName obj;
          (obj,s) <- pop s; nm <- getName obj;
          (th1,th2) <- new_basic_type_definition (nm, abs, rep, th);
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
    | eqMp =>
        do
          (obj,s) <- pop s; th2 <- getThm obj;
          (obj,s) <- pop s; th1 <- getThm obj;
          th <- EQ_MP th1 th2;
          return (push (Thm th) s)
        od
    | hdTl =>
        do
          (obj,s) <- pop s; ls <- getList obj;
          pmatch ls of
          | [] => failwith «hdTl»
          | (h::t) => return (push (List t) (push h s))
        od
    | nil =>
        return (push (List []) s)
    | opType =>
        do
          (obj,s) <- pop s; ls <- getList obj; args <- map getType ls;
          (obj,s) <- pop s; tyop <- getTypeOp obj;
          t <- mk_type(tyop,args);
          return (push (Type t) s)
        od
    | popc =>
        do
          (_,s) <- pop s;
          return s
        od
    | pragma =>
        do
          (obj,s) <- pop s;
          nm <- handle_Failure (getName obj)
                    (λe. return «bogus»);
          (* TODO Had to drop the debug pragma because of the rigidity
           * of the exception types: we inherit a single exception from
           * Candle and it takes a string. I can't make one up on the fly:
           *)
          (* if nm = «debug» then failwith (st2str_applist s) else return s *)
          return s
        od
    | proveHyp =>
        do
          (obj,s) <- pop s; th2 <- getThm obj;
          (obj,s) <- pop s; th1 <- getThm obj;
          th <- PROVE_HYP th2 th1;
          return (push (Thm th) s)
        od
    | ref =>
        do
          (obj,s) <- pop s; n <- getNum obj;
          if n < 0 then
            failwith «ref»
          else
            pmatch lookup (Num n) s.dict of
              NONE => failwith «ref»
            | SOME obj => return (push obj s)
        od
    | refl =>
        do
          (obj,s) <- pop s; tm <- getTerm obj;
          th <- REFL tm;
          return (push (Thm th) s)
        od
    | remove =>
        do
          (obj,s) <- pop s; n <- getNum obj;
          if n < 0 then
            failwith «ref»
          else
            pmatch lookup (Num n) s.dict of
              NONE => failwith «remove»
            | SOME obj => return (push obj (delete_dict (Num n) s))
        od
    | subst =>
        do
          (obj,s) <- pop s; th <- getThm obj;
          (obj,s) <- pop s; (tys,tms) <- getPair obj;
          tys <- getList tys; tys <- map getTys tys;
          th <- handle_Clash
                 (INST_TYPE tys th)
                 (λe. failwith «the impossible»);
          tms <- getList tms; tms <- map getTms tms;
          th <- INST tms th;
          return (push (Thm th) s)
        od
    | sym =>
        do
          (obj,s) <- pop s; th <- getThm obj;
          th <- SYM th;
          return (push (Thm th) s)
        od
    | thm =>
        do
          (obj,s) <- pop s; c <- getTerm obj;
          (obj,s) <- pop s; h <- getList obj; h <- map getTerm h;
          (obj,s) <- pop s; th <- getThm obj;
          th <- ALPHA_THM th (h,c);
          return (s with thms := th::s.thms)
        od
    | trans =>
        do
          (obj,s) <- pop s; th2 <- getThm obj;
          (obj,s) <- pop s; th1 <- getThm obj;
          th <- TRANS th1 th2;
          return (push (Thm th) s)
        od
    | typeOp =>
        do
          (obj,s) <- pop s; n <- getName obj;
          return (push (TypeOp n) s)
        od
    | var =>
        do
          (obj,s) <- pop s; ty <- getType obj;
          (obj,s) <- pop s; n <- getName obj;
          return (push (Var (n,ty)) s)
        od
    | varTerm =>
        do
          (obj,s) <- pop s; v <- getVar obj;
          return (push (Term (mk_var v)) s)
        od
    | varType =>
        do
          (obj,s) <- pop s; n <- getName obj;
          return (push (Type (mk_vartype n)) s)
        od
    | intc n =>
        return (push (Num n) s)
    | strc nm =>
        return (push (Name nm) s)
    | unknownc cs =>
        failwith («unrecognised input: » ^ cs)
    | skipc =>
        return s
End

(* -------------------------------------------------------------------------
 * Some preprocessing is required.
 * ------------------------------------------------------------------------- *)

Definition fix_fun_typ_def:
  fix_fun_typ s =
    if s = «\"->\"» then
      «\"fun\"»
    else if s = «\"select\"» then
      «\"@\"»
    else s
End

Definition str_prefix_def:
  str_prefix str = extract str 0 (SOME (strlen str - 1))
End

(* This is terrible: *)
Definition unescape_def:
  unescape str =
    pmatch str of
      #"\\":: #"\\" ::cs => #"\\"::unescape cs
    | c1::c::cs    => c1::unescape (c::cs)
    | cs           => cs
End

Definition unescape_ml_def:
  unescape_ml = implode o unescape o explode
End

(*
 * Does not drop the newline character from the input, because
 * inputAllTokensFile does this on its own.
 *)

Definition tokenize_def:
  tokenize = s2c o unescape_ml o fix_fun_typ
End

(* -------------------------------------------------------------------------
 * Print out the theorems and context if we succeed.
 * ------------------------------------------------------------------------- *)

(* TODO produce applist (the context output becomes quite large) *)

Definition msg_success_def:
  msg_success s ctxt =
    let upds = AppendList (MAP (λt. Append (upd2str_applist t)
                                           (List [«\n»])) (REVERSE ctxt));
        thm  = List [toString (LENGTH s.thms); « theorems:\n»];
        thms = AppendList (MAP (λt. Append (thm2str_applist t)
                                           (List [«\n»])) (REVERSE s.thms))
    in AppendList [List [«OK!\n»; «CONTEXT:\n»];
                   upds; List [«\n»];
                   thm; List [«\n»]; thms]
End

(* -------------------------------------------------------------------------
 * Error messages.
 * ------------------------------------------------------------------------- *)

Definition line_Fail_def:
  line_Fail s msg =
    concat [
      «Failure on line »;
      toString (current_line s);
      «:\n»;
      msg; «\n»;
    ]
End

Definition msg_usage_def:
  msg_usage =
    concat [
      «Usage: reader [article]\n»;
      «\n»;
      «  OpenTheory article proof checker.\n»;
      «  If no article file is supplied, input is read from\n»;
      «  standard input.\n»;
    ]
End

Definition msg_bad_name_def:
  msg_bad_name s =
    concat [
      «No such file: »; s; «.\n\n»;
      msg_usage
    ]
End

(* -------------------------------------------------------------------------
 * Running the reader on a list of commands.
 * ------------------------------------------------------------------------- *)

Definition readLines_def:
  readLines s lls =
    pmatch lls of
      []    => return (s, lines_read s)
    | l::ls =>
        do
          s <- handle_Failure
                 (readLine s l)
                 (λe. raise_Failure (line_Fail s e));
          readLines (next_line s) ls
        od
End

(* -------------------------------------------------------------------------
 * PMATCH definitions.
 * ------------------------------------------------------------------------- *)

val _ = patternMatchesSyntax.temp_enable_pmatch();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem getNum_PMATCH:
   ∀obj.
     getNum obj =
       pmatch obj of
         Num n => return n
       | _ => failwith «getNum»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getNum_def]
QED

Theorem getName_PMATCH:
   ∀obj.
     getName obj =
       pmatch obj of
         Name n => return n
       | _ => failwith «getName»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getName_def]
QED

Theorem getList_PMATCH:
   ∀obj.
     getList obj =
       pmatch obj of
         List n => return n
       | _ => failwith «getList»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getList_def]
QED

Theorem getTypeOp_PMATCH:
   ∀obj.
     getTypeOp obj =
       pmatch obj of
         TypeOp n => return n
       | _ => failwith «getTypeOp»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTypeOp_def]
QED

Theorem getType_PMATCH:
   ∀obj.
     getType obj =
       pmatch obj of
         Type n => return n
       | _ => failwith «getType»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getType_def]
QED

Theorem getConst_PMATCH:
   ∀obj.
     getConst obj =
       pmatch obj of
         Const n => return n
       | _ => failwith «getConst»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getConst_def]
QED

Theorem getVar_PMATCH:
   ∀obj.
     getVar obj =
       pmatch obj of
         Var n => return n
       | _ => failwith «getVar»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getVar_def]
QED

Theorem getTerm_PMATCH:
   ∀obj.
     getTerm obj =
       pmatch obj of
         Term n => return n
       | _ => failwith «getTerm»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTerm_def]
QED

Theorem getThm_PMATCH:
   ∀obj.
     getThm obj =
       pmatch obj of
         Thm n => return n
       | _ => failwith «getThm»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getThm_def]
QED

Theorem getPair_PMATCH:
   ∀obj.
     getPair obj =
       pmatch obj of
         List [x;y] => return (x,y)
       | _ => failwith «getPair»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ fs [getPair_def]
  \\ rpt (PURE_CASE_TAC \\ fs [getPair_def])
QED

Theorem unescape_PMATCH:
   ∀str.
     unescape str =
       pmatch str of
         #"\\":: #"\\" ::cs => #"\\"::unescape cs
       | c1::c::cs    => c1::unescape (c::cs)
       | cs           => cs
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [Once unescape_def]
QED

