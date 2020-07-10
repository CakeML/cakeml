(*
  Shallowly embedded (monadic) functions that implement the OpenTheory
  article checker.
*)
open preamble ml_hol_kernelProgTheory
     mlintTheory StringProgTheory
     prettyTheory

val _ = new_theory"reader"

Overload monad_bind[local] = “st_ex_bind”
Overload monad_unitbind[local] = “λx y. st_ex_bind x (λ z. y)”
Overload monad_ignore_bind[local] = “λx y. st_ex_bind x (λz. y)”
Overload return[local] = “st_ex_return”
Overload failwith[local] = “raise_Fail”
val _ = temp_add_monadsyntax()

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
 * TODO fromString is broken, so here's this:
 *)

Definition s2i_def:
  s2i s = if s = «» then NONE:int option else fromString s
End

val _ = export_rewrites ["s2i_def"]

(*
 * Expensive (string-comparisons) way of tokenizing the input.
 * (Better but more verbose: read one character at a time, fail early.)
 *)

Definition s2c_def:
  s2c s =
    if s = «absTerm» then absTerm
    else if s = «absThm» then absThm
    else if s = «appTerm» then appTerm
    else if s = «appThm» then appThm
    else if s = «assume» then assume
    else if s = «axiom» then axiom
    else if s = «betaConv» then betaConv
    else if s = «cons» then cons
    else if s = «const» then const
    else if s = «constTerm» then constTerm
    else if s = «deductAntisym» then deductAntisym
    else if s = «def» then def
    else if s = «defineConst» then defineConst
    else if s = «defineConstList» then defineConstList
    else if s = «defineTypeOp» then defineTypeOp
    else if s = «eqMp» then eqMp
    else if s = «hdTl» then hdTl
    else if s = «nil» then nil
    else if s = «opType» then opType
    else if s = «pop» then popc
    else if s = «pragma» then pragma
    else if s = «proveHyp» then proveHyp
    else if s = «ref» then ref
    else if s = «refl» then refl
    else if s = «remove» then remove
    else if s = «subst» then subst
    else if s = «sym» then sym
    else if s = «thm» then thm
    else if s = «trans» then trans
    else if s = «typeOp» then typeOp
    else if s = «var» then var
    else if s = «varTerm» then varTerm
    else if s = «varType» then varType
    else if s = «version» then version
    else case s2i s of
           SOME i => intc i
         | NONE =>
             case explode s of
               #"\""::c::cs => strc (implode (FRONT (c::cs)))
             | #"#"::_ => skipc
             | _ => unknownc s
End

(*
 * Line splitter for b_inputAllTokensFrom.
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

val name_to_string_def = Define`
  (name_to_string ([],s) = s) ∧
  (name_to_string (n::ns,s) =
   strcat (strcat n («.»)) (name_to_string ns s))`;

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
    case s.stack of
      [] => failwith «pop»
    | h::t => return (h,s with stack := t)
End

Definition peek_def:
  peek s =
    case s.stack of
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
    case l of
      [] => NONE
    | h::t => if p h then SOME h else first p t
End

Definition find_axiom_def:
  find_axiom (ls, tm) =
    do
      axs <- axioms ();
      case first (λth.
        case th of
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
    handle_Fail (BETA tm)
      (λe.
        handle_Fail
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
  commas xs =
    case xs of
      [] => []
    | x::xs => mk_str «, » :: x :: commas xs
End

Definition listof_def:
  listof xs =
    case xs of
      [] => mk_str «[]»
    | x::xs =>
        mk_blo 0 ([mk_str «[»; x] ++
                  commas xs ++
                  [mk_str «]»])
End

Definition obj_t_def:
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
        [mk_str (s ^ «:»); mk_brk 1; mk_str (pp_type 0 ty)]
Termination
  WF_REL_TAC ‘measure object_size’
  \\ Induct \\ rw [definition"object_size_def"]
  \\ res_tac
  \\ decide_tac
End

Definition obj_to_string_def:
  obj_to_string t = pr (obj_t t) pp_margin
End

Definition state_to_string_def:
  state_to_string s =
    let stack = concat (MAP (λt. obj_to_string t ^ «\n») s.stack) in
    let dict  = concat [«dict: [»;
                        toString (LENGTH (toAList s.dict));
                        «]\n»] in
    let thm   = concat [toString (LENGTH s.thms); « theorems:\n»] in
    let thms  = concat (MAP (λt. thm2str t ^ «\n») s.thms) in
      concat [stack; «\n»; dict; thm; thms]
End

(* -------------------------------------------------------------------------
 * Printing of the context.
 * ------------------------------------------------------------------------- *)

Definition pp_namepair_def:
  pp_namepair nts =
    case nts of
      [] => []
    | (nm,tm)::nts =>
        [mk_str («(» ^ nm ^ «, »);
         pp_term 0 tm;
         mk_str «)»] ++
         (if nts = [] then
            []
          else
            mk_str «;»::mk_brk 1::pp_namepair nts)
End

Definition pp_update_def:
  pp_update upd =
    case upd of
      ConstSpec nts tm =>
        mk_blo 11
          ([mk_str «ConstSpec»;
            mk_brk 1;
            mk_str «[»] ++
            pp_namepair nts ++
           [mk_str «]»;
            mk_brk 1;
            mk_str «with definition»;
            mk_brk 1;
            pp_term 0 tm])
    | TypeDefn nm pred abs_nm rep_nm =>
        mk_blo 9
          [mk_str «TypeDefn»;
           mk_brk 1;
           mk_str nm;
           mk_brk 1;
           mk_str («(absname » ^ abs_nm ^ «)»);
           mk_brk 1;
           mk_str («(repname » ^ rep_nm ^ «)»);
           mk_brk 1;
           pp_term 0 pred]
    | NewType nm arity =>
        mk_blo 8
          [mk_str «NewType»;
           mk_brk 1;
           mk_str nm;
           mk_brk 1;
           mk_str («(arity » ^ toString arity ^ «)»)]
    | NewConst nm ty =>
        mk_blo 9
          [mk_str «NewConst»;
           mk_brk 1;
           mk_str (nm ^ « :»);
           mk_brk 1;
           mk_str (pp_type 0 ty)]
    | NewAxiom tm =>
        mk_blo 9
          [mk_str «NewAxiom»;
           mk_brk 1;
           pp_thm (Sequent [] tm)]
End

Definition upd2str_def:
  upd2str upd = pr (pp_update upd) pp_margin
End

(* -------------------------------------------------------------------------
 * Implementation of the article reader.
 * ------------------------------------------------------------------------- *)

(*
 * TODO The reader does not respect the "version" command.
 *)

Definition readLine_def:
  readLine s c =
    case c of
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
          tm <- case match_type ty0 ty of
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
          ty <- type_of tm;
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
          case ls of
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
          nm <- handle_Fail (getName obj)
                    (λe. return «bogus»);
          if nm = «debug» then
            failwith (state_to_string s)
          else
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
            case lookup (Num n) s.dict of
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
            case lookup (Num n) s.dict of
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

Definition unescape_def:
  unescape str =
    case str of
      #"\\":: #"\\" ::cs => #"\\"::unescape cs
    | c1::c::cs    => c1::unescape (c::cs)
    | cs           => cs
End

Definition unescape_ml_def:
  unescape_ml = implode o unescape o explode
End

(*
 * Does not drop the newline character from the input, because
 * b_inputAllTokensFrom does this on its own.
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
    let upds = concat (MAP (λupd. upd2str upd ^ «\n») ctxt) in
    let thm  = concat [toString (LENGTH s.thms); « theorems:\n»] in
    let thms = concat (MAP (λt. thm2str t ^ «\n») s.thms) in
      concat
        [«OK!\n»;
         «CONTEXT:\n»; upds; «\n»;
         thm; «\n»; thms]
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
    case lls of
      []    => return (s, lines_read s)
    | l::ls =>
        do
          s <- handle_Fail
                 (readLine s l)
                 (λe. raise_Fail (line_Fail s e));
          readLines (next_line s) ls
        od
End

(* -------------------------------------------------------------------------
 * PMATCH definitions.
 * ------------------------------------------------------------------------- *)

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem getNum_PMATCH:
   ∀obj.
     getNum obj =
       case obj of
         Num n => return n
       | _ => failwith «getNum»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getNum_def]
QED

Theorem getName_PMATCH:
   ∀obj.
     getName obj =
       case obj of
         Name n => return n
       | _ => failwith «getName»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getName_def]
QED

Theorem getList_PMATCH:
   ∀obj.
     getList obj =
       case obj of
         List n => return n
       | _ => failwith «getList»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getList_def]
QED

Theorem getTypeOp_PMATCH:
   ∀obj.
     getTypeOp obj =
       case obj of
         TypeOp n => return n
       | _ => failwith «getTypeOp»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTypeOp_def]
QED

Theorem getType_PMATCH:
   ∀obj.
     getType obj =
       case obj of
         Type n => return n
       | _ => failwith «getType»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getType_def]
QED

Theorem getConst_PMATCH:
   ∀obj.
     getConst obj =
       case obj of
         Const n => return n
       | _ => failwith «getConst»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getConst_def]
QED

Theorem getVar_PMATCH:
   ∀obj.
     getVar obj =
       case obj of
         Var n => return n
       | _ => failwith «getVar»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getVar_def]
QED

Theorem getTerm_PMATCH:
   ∀obj.
     getTerm obj =
       case obj of
         Term n => return n
       | _ => failwith «getTerm»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getTerm_def]
QED

Theorem getThm_PMATCH:
   ∀obj.
     getThm obj =
       case obj of
         Thm n => return n
       | _ => failwith «getThm»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [getThm_def]
QED

Theorem getPair_PMATCH:
   ∀obj.
     getPair obj =
       case obj of
         List [x;y] => return (x,y)
       | _ => failwith «getPair»
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ fs [getPair_def]
  \\ rpt (PURE_CASE_TAC \\ fs [getPair_def])
QED

Theorem unescape_PMATCH:
   ∀str.
     unescape str =
       case str of
         #"\\":: #"\\" ::cs => #"\\"::unescape cs
       | c1::c::cs    => c1::unescape (c::cs)
       | cs           => cs
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV) \\ Cases \\ rw [Once unescape_def]
QED

val _ = export_theory()

