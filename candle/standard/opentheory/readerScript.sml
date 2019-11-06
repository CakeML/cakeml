(*
  Shallowly embedded (monadic) functions that implement the OpenTheory
  article checker.
*)
open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     prettyTheory

val _ = new_theory"reader"

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``
Overload failwith[local] = ``raise_Fail``
val _ = temp_add_monadsyntax()

(* ------------------------------------------------------------------------- *)
(* Objects and functions on objects.                                         *)
(* ------------------------------------------------------------------------- *)

(* We just represent names in the string (dotted) format.
   To make the namespace more explicit, the following functions could
   be useful.

Type name = ``mlstring list # mlstring``

val name_to_string_def = Define`
  (name_to_string ([],s) = s) ∧
  (name_to_string (n::ns,s) =
   strcat (strcat n (implode".")) (name_to_string ns s))`;

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
  (getNum _ = failwith (implode"getNum"))`;

val getName_def = Define`
  (getName (Name n) = return n) ∧
  (getName _ = failwith (implode"getName"))`;

val getList_def = Define`
  (getList (List ls) = return ls) ∧
  (getList _ = failwith (implode"getList"))`;

val getTypeOp_def = Define`
  (getTypeOp (TypeOp t) = return t) ∧
  (getTypeOp _ = failwith (implode"getTypeOp"))`;

val getType_def = Define`
  (getType (Type t) = return t) ∧
  (getType _ = failwith (implode"getType"))`;

val getConst_def = Define`
  (getConst (Const v) = return v) ∧
  (getConst _ = failwith (implode"getConst"))`;

val getVar_def = Define`
  (getVar (Var v) = return v) ∧
  (getVar _ = failwith (implode"getVar"))`;

val getTerm_def = Define`
  (getTerm (Term t) = return t) ∧
  (getTerm _ = failwith (implode"getTerm"))`;

val getThm_def = Define`
  (getThm (Thm th) = return th) ∧
  (getThm _ = failwith (implode"getThm"))`;

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
      [] => failwith (implode"pop")
    | (h::t) => return (h,s with <| stack := t |>)`;

val peek_def = Define`
  peek s =
    case s.stack of
      [] => failwith (implode"peek")
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
      [] => NONE
    | (h::t) => if p h then SOME h else first p t`;

val find_axiom_def = Define`
  find_axiom (ls, tm) =
    do
      axs <- axioms ();
      case first (λth.
        case th of
        | Sequent h c =>
            EVERY (λx. EXISTS (aconv x) h) ls ∧
            aconv c tm) axs of
      | NONE => failwith (implode"find_axiom")
      | SOME ax => return ax
    od`;

val getPair_def = Define`
  (getPair (List [x;y]) = return (x,y)) ∧
  (getPair _ = failwith (implode"getPair"))`;

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
          (\e. failwith (implode"BETA_CONV: not a beta-redex")))`;

(* ------------------------------------------------------------------------- *)
(* Debugging.                                                                *)
(* ------------------------------------------------------------------------- *)

val commas_def = Define `
  commas xs =
    case xs of
      [] => []
    | x::xs => mk_str(implode", ") :: x :: commas xs`

val listof_def = Define `
  listof xs =
    case xs of
      [] => mk_str (implode"[]")
    | x::xs =>
        mk_blo 0 ([mk_str (implode"["); x] ++
                  commas xs ++
                  [mk_str (implode"]")])`

val obj_t_def = tDefine "obj_t" `
  obj_t obj =
    case obj of
      Num n => mk_str (toString n)
    | Name s => mk_str (name_of s)
    | List ls => listof (MAP obj_t ls)
    | TypeOp s => mk_str s
    | Type ty => mk_str (pp_type 0 ty)
    | Const s => mk_str s
    | Term tm => pp_term 0 tm
    | Thm th => pp_thm th
    | Var (s,ty) => mk_blo 0
        [mk_str (s ^ implode ":"); mk_brk 1; mk_str (pp_type 0 ty)]`
 (WF_REL_TAC `measure object_size`
  \\ Induct \\ rw [definition"object_size_def"]
  \\ res_tac
  \\ decide_tac);

val obj_to_string_def = Define `
  obj_to_string t = pr (obj_t t) pp_margin`;

val state_to_string = Define `
  state_to_string s =
    let stack = concat (MAP (\t. obj_to_string t ^ implode"\n") s.stack) in
    let dict  = concat [implode"dict: [";
                        toString (LENGTH (toAList s.dict));
                        implode"]\n"] in
    let thm   = concat [toString (LENGTH s.thms); implode" theorems:\n"] in
    let thms  = concat (MAP (\t. thm2str t ^ implode"\n") s.thms) in
      concat [stack; implode"\n"; dict; thm; thms]`;

(* ------------------------------------------------------------------------- *)
(* Printing of the context.                                                  *)
(* ------------------------------------------------------------------------- *)

val pp_namepair_def = Define `
  pp_namepair nts =
    case nts of
      [] => []
    | (nm,tm)::nts =>
        [mk_str (implode"(" ^ nm ^ implode", ");
         pp_term 0 tm;
         mk_str (implode")")] ++
         (if nts = [] then
            []
          else
            mk_str (implode";")::mk_brk 1::pp_namepair nts)`;

val pp_update_def = Define `
  pp_update upd =
    case upd of
      ConstSpec nts tm =>
        mk_blo 11
          ([mk_str (implode"ConstSpec");
            mk_brk 1;
            mk_str (implode"[")] ++
            pp_namepair nts ++
           [mk_str (implode"]");
            mk_brk 1;
            mk_str (implode"with definition");
            mk_brk 1;
            pp_term 0 tm])
    | TypeDefn nm pred abs_nm rep_nm =>
        mk_blo 9
          [mk_str (implode"TypeDefn");
           mk_brk 1;
           mk_str nm;
           mk_brk 1;
           mk_str (implode"(absname " ^ abs_nm ^ implode")");
           mk_brk 1;
           mk_str (implode"(repname " ^ rep_nm ^ implode")");
           mk_brk 1;
           pp_term 0 pred]
    | NewType nm arity =>
        mk_blo 8
          [mk_str (implode"NewType");
           mk_brk 1;
           mk_str nm;
           mk_brk 1;
           mk_str (implode"(arity " ^ toString arity ^ implode")")]
    | NewConst nm ty =>
        mk_blo 9
          [mk_str (implode"NewConst");
           mk_brk 1;
           mk_str (nm ^ implode" :");
           mk_brk 1;
           mk_str (pp_type 0 ty)]
    | NewAxiom tm =>
        mk_blo 9
          [mk_str (implode"NewAxiom");
           mk_brk 1;
           pp_thm (Sequent [] tm)]`;

val upd2str_def = Define `
  upd2str upd = pr (pp_update upd) pp_margin`;

(* ------------------------------------------------------------------------- *)
(* Implementation of the article reader.                                     *)
(* ------------------------------------------------------------------------- *)

(* TODO fromString is broken *)
val s2i_def = Define `
  s2i s = if s = implode"" then NONE:int option else fromString s`

val _ = export_rewrites ["s2i_def"]

(* TODO The reader does not respect the "version" command. *)

val readLine_def = Define`
  readLine line s =
  if line = implode"version" then
    do
      (obj, s) <- pop s; ver <- getNum obj;
      return s
    od
  else if line = implode"absTerm" then
    do
      (obj,s) <- pop s; b <- getTerm obj;
      (obj,s) <- pop s; v <- getVar obj;
      tm <- mk_abs(mk_var v,b);
      return (push (Term tm) s)
    od
  else if line = implode"absThm" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; v <- getVar obj;
      th <- ABS (mk_var v) th;
      return (push (Thm th) s)
    od
  else if line = implode"appTerm" then
    do
      (obj,s) <- pop s; x <- getTerm obj;
      (obj,s) <- pop s; f <- getTerm obj;
      fx <- mk_comb (f,x);
      return (push (Term fx) s)
    od
  else if line = implode"appThm" then
    do
      (obj,s) <- pop s; xy <- getThm obj;
      (obj,s) <- pop s; fg <- getThm obj;
      th <- MK_COMB (fg,xy);
      return (push (Thm th) s)
    od
  else if line = implode"assume" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- ASSUME tm;
      return (push (Thm th) s)
    od
  else if line = implode"axiom" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      (obj,s) <- pop s; ls <- getList obj; ls <- map getTerm ls;
      (* We only allow axioms already in the context *)
      (* and we return an alpha-equivalent variant *)
      (* (contrary to normal article semantics) *)
      th <- find_axiom (ls,tm);
      return (push (Thm th) s)
    od
  else if line = implode"betaConv" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- BETA_CONV tm;
      return (push (Thm th) s)
    od
  else if line = implode"cons" then
    do
      (obj,s) <- pop s; ls <- getList obj;
      (obj,s) <- pop s;
      return (push (List (obj::ls)) s)
    od
  else if line = implode"const" then
    do
      (* TODO this could be handled like "axiom" and allow the *)
      (* reader to fail early, since it will fail once the     *)
      (* constant is used unless it exists in the context.     *)
      (obj,s) <- pop s; n <- getName obj;
      return (push (Const n) s)
    od
  else if line = implode"constTerm" then
    do
      (obj,s) <- pop s; ty <- getType obj;
      (obj,s) <- pop s; nm <- getConst obj;
      ty0 <- get_const_type nm;
      tm <- case match_type ty0 ty of
            | NONE => failwith (implode"constTerm")
            | SOME theta => mk_const(nm,theta);
      return (push (Term tm) s)
    od
  else if line = implode"deductAntisym" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- DEDUCT_ANTISYM_RULE th1 th2;
      return (push (Thm th) s)
    od
  else if line = implode"def" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      obj <- peek s;
      if n < 0 then
        failwith (implode"def")
      else
        return (insert_dict (Num n) obj s)
    od
  else if line = implode"defineConst" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      (obj,s) <- pop s; n <- getName obj;
      ty <- type_of tm;
      eq <- mk_eq (mk_var(n,ty),tm);
      th <- new_basic_definition eq;
      return (push (Thm th) (push (Const n) s))
    od
  else if line = implode"defineConstList" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; ls <- getList obj; ls <- map getNvs ls;
      th <- INST ls th;
      th <- new_specification th;
      ls <- map getCns ls;
      return (push (Thm th) (push (List ls) s))
    od
  else if line = implode"defineTypeOp" then
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
  else if line = implode"eqMp" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- EQ_MP th1 th2;
      return (push (Thm th) s)
    od
  else if line = implode"hdTl" then
    do
      (obj,s) <- pop s; ls <- getList obj;
      case ls of
      | [] => failwith (implode"hdTl")
      | (h::t) => return (push (List t) (push h s))
    od
  else if line = implode"nil" then
    return (push (List []) s)
  else if line = implode"opType" then
    do
      (obj,s) <- pop s; ls <- getList obj; args <- map getType ls;
      (obj,s) <- pop s; tyop <- getTypeOp obj;
      t <- mk_type(tyop,args);
      return (push (Type t) s)
    od
  else if line = implode"pop" then
    do (_,s) <- pop s; return s od
  else if line = implode"pragma" then
    do (obj,s) <- pop s;
       nm <- handle_Fail (getName obj)
                 (\e. return (implode"bogus"));
       if nm = implode"debug" then
         failwith (state_to_string s)
       else
         return s
    od
  else if line = implode"proveHyp" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- PROVE_HYP th2 th1;
      return (push (Thm th) s)
    od
  else if line = implode"ref" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      if n < 0 then
        failwith (implode"ref")
      else
        case lookup (Num n) s.dict of
          NONE => failwith (implode"ref")
        | SOME obj => return (push obj s)
    od
  else if line = implode"refl" then
    do
      (obj,s) <- pop s; tm <- getTerm obj;
      th <- REFL tm;
      return (push (Thm th) s)
    od
  else if line = implode"remove" then
    do
      (obj,s) <- pop s; n <- getNum obj;
      if n < 0 then
        failwith (implode"ref")
      else
        case lookup (Num n) s.dict of
          NONE => failwith (implode"remove")
        | SOME obj => return (push obj (delete_dict (Num n) s))
    od
  else if line = implode"subst" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      (obj,s) <- pop s; (tys,tms) <- getPair obj;
      tys <- getList tys; tys <- map getTys tys;
      th <- handle_Clash
             (INST_TYPE tys th)
             (\e. failwith (implode"the impossible"));
      tms <- getList tms; tms <- map getTms tms;
      th <- INST tms th;
      return (push (Thm th) s)
    od
  else if line = implode"sym" then
    do
      (obj,s) <- pop s; th <- getThm obj;
      th <- SYM th;
      return (push (Thm th) s)
    od
  else if line = implode"thm" then
    do
      (obj,s) <- pop s; c <- getTerm obj;
      (obj,s) <- pop s; h <- getList obj; h <- map getTerm h;
      (obj,s) <- pop s; th <- getThm obj;
      th <- ALPHA_THM th (h,c);
      return (s with <| thms := th::s.thms |>)
    od
  else if line = implode"trans" then
    do
      (obj,s) <- pop s; th2 <- getThm obj;
      (obj,s) <- pop s; th1 <- getThm obj;
      th <- TRANS th1 th2;
      return (push (Thm th) s)
    od
  else if line = implode"typeOp" then
    do
      (obj,s) <- pop s; n <- getName obj;
      return (push (TypeOp n) s)
    od
  else if line = implode"var" then
    do
      (obj,s) <- pop s; ty <- getType obj;
      (obj,s) <- pop s; n <- getName obj;
      return (push (Var (n,ty)) s)
    od
  else if line = implode"varTerm" then
    do
      (obj,s) <- pop s; v <- getVar obj;
      return (push (Term (mk_var v)) s)
    od
  else if line = implode"varType" then
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
        | _ => failwith (implode"unrecognised input: " ^ line)`;

(* ------------------------------------------------------------------------- *)
(* Some preprocessing is required.                                           *)
(* ------------------------------------------------------------------------- *)

val fix_fun_typ_def = Define `
  fix_fun_typ s =
    if s = implode"\"->\"" then
      implode"\"fun\""
    else if s = implode"\"select\"" then
      implode"\"@\""
    else s`;

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val invalid_line_def = Define`
  invalid_line str ⇔ (strlen str) ≤ 1n ∨ strsub str 0 = #"#"`;

val unescape_def = Define `
  unescape str =
    case str of
      #"\\":: #"\\" ::cs => #"\\"::unescape cs
    | c1::c::cs    => c1::unescape (c::cs)
    | cs           => cs`;

val unescape_ml_def = Define `
  unescape_ml = implode o unescape o explode`;

(* ------------------------------------------------------------------------- *)
(* Print out the theorems and context if we succeed.                         *)
(* ------------------------------------------------------------------------- *)

(* TODO produce applist (the context output becomes quite large) *)

val msg_success_def = Define `
  msg_success s ctxt =
    let upds = concat (MAP (\upd. upd2str upd ^ implode"\n") ctxt) in
    let thm  = concat [toString (LENGTH s.thms); implode" theorems:\n"] in
    let thms = concat (MAP (\t. thm2str t ^ implode"\n") s.thms) in
      concat
        [implode"OK!\n";
         implode"CONTEXT:\n"; upds; implode"\n";
         thm; implode"\n"; thms]`;

(* ------------------------------------------------------------------------- *)
(* Error messages.                                                           *)
(* ------------------------------------------------------------------------- *)

val line_Fail_def = Define `
  line_Fail s msg =
    (mlstring$concat
      [ implode"Failure on line "
      ; toString (current_line s)
      ; implode":\n"
      ; msg; implode"\n"])`;

val msg_usage_def = Define `msg_usage = implode"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [implode"Bad filename: "; s; implode".\n"]
  `;

val msg_axioms_def = Define `
  msg_axioms e =
    concat[implode"Could not initialise axioms:\n"; e; implode "\n"]`;

(* ------------------------------------------------------------------------- *)
(* Running the reader on a list of strings.                                  *)
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
                   (readLine (unescape_ml (fix_fun_typ (str_prefix l))) s)
                   (\e. raise_Fail (line_Fail s e));
            readLines ls (next_line s)
        od`;

(* ------------------------------------------------------------------------- *)
(* PMATCH definitions.                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem getNum_PMATCH:
   !obj.
     getNum obj =
       case obj of
         Num n => return n
       | _ => failwith (implode"getNum")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getNum_def]
QED

Theorem getName_PMATCH:
   !obj.
     getName obj =
       case obj of
         Name n => return n
       | _ => failwith (implode"getName")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getName_def]
QED

Theorem getList_PMATCH:
   !obj.
     getList obj =
       case obj of
         List n => return n
       | _ => failwith (implode"getList")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getList_def]
QED

Theorem getTypeOp_PMATCH:
   !obj.
     getTypeOp obj =
       case obj of
         TypeOp n => return n
       | _ => failwith (implode"getTypeOp")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTypeOp_def]
QED

Theorem getType_PMATCH:
   !obj.
     getType obj =
       case obj of
         Type n => return n
       | _ => failwith (implode"getType")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getType_def]
QED

Theorem getConst_PMATCH:
   !obj.
     getConst obj =
       case obj of
         Const n => return n
       | _ => failwith (implode"getConst")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getConst_def]
QED

Theorem getVar_PMATCH:
   !obj.
     getVar obj =
       case obj of
         Var n => return n
       | _ => failwith (implode"getVar")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getVar_def]
QED

Theorem getTerm_PMATCH:
   !obj.
     getTerm obj =
       case obj of
         Term n => return n
       | _ => failwith (implode"getTerm")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTerm_def]
QED

Theorem getThm_PMATCH:
   !obj.
     getThm obj =
       case obj of
         Thm n => return n
       | _ => failwith (implode"getThm")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getThm_def]
QED

Theorem getPair_PMATCH:
   !obj.
     getPair obj =
       case obj of
         List [x;y] => return (x,y)
       | _ => failwith (implode"getPair")
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ fs [getPair_def]
  \\ rpt (PURE_CASE_TAC \\ fs [getPair_def])
QED

Theorem unescape_PMATCH:
   !str.
     unescape str =
       case str of
         #"\\":: #"\\" ::cs => #"\\"::unescape cs
       | c1::c::cs    => c1::unescape (c::cs)
       | cs           => cs
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [Once unescape_def]
QED

val _ = export_theory()
