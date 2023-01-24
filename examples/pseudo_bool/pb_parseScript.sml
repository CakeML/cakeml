(*
  Parse and print for pbc, npb_check
*)
open preamble pbcTheory pbc_normaliseTheory npbc_checkTheory;

val _ = new_theory "pb_parse";

val _ = numLib.prefer_num();

(* Print mlstring pbc *)
Definition lit_string_def:
  (lit_string (Pos v) = v) ∧
  (lit_string (Neg v) = strlit "~" ^ v)
End

Definition lhs_string_def:
  lhs_string xs =
  concatWith (strlit" ") (MAP(λ(c,l). concat [int_to_string #"-" c; strlit " " ; lit_string l]) xs)
End

Definition op_string_def:
  (op_string Equal = strlit" = ") ∧
  (op_string GreaterEqual = strlit" >= ") ∧
  (op_string Greater = strlit" > ") ∧
  (op_string LessEqual = strlit" <= ") ∧
  (op_string Less = strlit" < ")
End

Definition pbc_string_def:
  (pbc_string (pbop,xs,i) =
    concat [
      lhs_string xs;
      op_string pbop;
      int_to_string #"-" i; strlit ";\n"])
End

(*
  Parse an OPB file as string pbc
*)

(* TODO: copied from lpr_parsing *)
(* Everything recognized as a "blank" *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_def:
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

(* OPB parser
  Parses a literal s, ~s
  Valid names may contain a-zA-Z0-9-_ characters
  Any good string (length >= 1) is parsed to a Neg-ated literal if it starts with ~
*)
Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" then
    (let ss = substring s 1 (strlen s - 1) in
    if goodString ss then
      SOME (Neg ss)
    else NONE)
  else if strlen s ≥ 1 then
    (if goodString s then SOME (Pos s)
    else NONE)
  else NONE
End

(*
  EVAL ``parse_lit (strlit "xaAa_-1")``
  EVAL ``parse_lit (strlit "~x1234")``
*)

(* Parse the LHS of a constraint and returns the remainder of the line *)
Definition parse_constraint_LHS_def:
  (parse_constraint_LHS (INR n::INL v::rest) acc =
    case parse_lit v of NONE => (INR n::INL v::rest,REVERSE acc)
    | SOME lit => parse_constraint_LHS rest ((n,lit)::acc)) ∧
  (parse_constraint_LHS ls acc = (ls,REVERSE acc))
End

(* strip ; from the end of a number *)
Definition strip_terminator_def:
  strip_terminator s =
  if strlen s ≥ 1 ∧ strsub s (strlen s - 1) = #";"
  then mlint$fromString (substring s 0 (strlen s - 1))
  else NONE
End

Definition parse_op_def:
  parse_op cmp =
  if cmp = strlit ">=" then SOME GreaterEqual
  else if cmp = strlit "=" then SOME Equal
  else if cmp = strlit ">" then SOME Greater
  else if cmp = strlit "<=" then SOME LessEqual
  else if cmp = strlit "<" then SOME Less
  else NONE
End

Definition parse_constraint_def:
  parse_constraint line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  let cmpdeg =
    (case rest of
      [INL cmp; INR deg; INL term] =>
        if term ≠ str #";" then NONE else SOME(cmp,deg)
    | [INL cmp; INL degterm] =>
      (case strip_terminator degterm of NONE => NONE
      | SOME deg => SOME(cmp,deg))
    | _ => NONE) in
  case cmpdeg of NONE => NONE
  | SOME (cmp, deg) =>
    case parse_op cmp of NONE => NONE
    | SOME op =>
      SOME ((op,lhs,deg):mlstring pbc)
End

(* EVAL ``parse_constraint (toks (strlit "2 ~x1 1 ~x3 >= 1;"))``; *)

Definition parse_constraints_def:
  (parse_constraints [] acc = SOME (REVERSE acc)) ∧
  (parse_constraints (s::ss) acc =
    case parse_constraint s of
      NONE => NONE
    | SOME pbc => parse_constraints ss (pbc::acc))
End

Definition nocomment_line_def:
  (nocomment_line (INL c::cs) =
    (strlen c < 1 ∨ strsub c 0 ≠ #"*")) ∧
  (nocomment_line _ = T)
End

(* parse objective line *)
Definition parse_obj_def:
  (parse_obj [] = NONE) ∧
  (parse_obj (x::xs) =
    if x = INL (strlit "min:") then
      case parse_constraint_LHS xs [] of (rest,obj) =>
        if rest = [INL (strlit ";")] then SOME obj
        else NONE
    else NONE
  )
End

(* parse optional objective *)
Definition parse_obj_maybe_def:
  (parse_obj_maybe [] = (NONE , [])) ∧
  (parse_obj_maybe (l::ls) =
  case parse_obj l of
    NONE => (NONE, l::ls)
  | SOME obj => (SOME obj, ls))
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  let (obj,rest) = parse_obj_maybe nocomments in
  case parse_constraints rest [] of
    NONE => NONE
  | SOME pbf => SOME (obj,pbf)
End

(* Parse a list of strings in pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(*
  Parsing a proof file
*)

Type name_fun[pp] = “:(mlstring -> α -> (num # α) option) # α”

Definition apply_lit_def:
  apply_lit ((f,ns):'a name_fun) (Pos x) =
    (case f x ns of
     | NONE => NONE
     | SOME (y,ns1) => SOME (Pos y,f,ns1)) ∧
  apply_lit (f,ns) (Neg x) =
    (case f x ns of
     | NONE => NONE
     | SOME (y,ns1) => SOME (Neg y,f,ns1))
End

(* The stack is formed from constraints, where factors and variables are
  also encoded using Id *)
Definition parse_lit_num_def:
  parse_lit_num (f_ns:'a name_fun) s =
    case parse_lit s of
    | NONE => NONE
    | SOME l => apply_lit f_ns l
End

Definition parse_cutting_def:
  (parse_cutting f_ns (x::xs) stack =
  case x of INR n =>
    if n ≥ 0 then
      parse_cutting f_ns xs (Id (Num n) :: stack)
    else NONE
  | INL s =>
  if s = str #"+" then
    (case stack of
      a::b::rest => parse_cutting f_ns xs (Add b a::rest)
    | _ => NONE)
  else if s = str #"*" then
    (case stack of
      Id a::b::rest => parse_cutting f_ns xs (Mul b a::rest)
    | _ => NONE)
  else if s = str #"d" then
    (case stack of
      Id a::b::rest => parse_cutting f_ns xs (Div b a::rest)
    | _ => NONE)
  else if s = str #"s" then
    (case stack of
      a::rest => parse_cutting f_ns xs (Sat a::rest)
    | _ => NONE)
  else if s = str #"w" then
    (case stack of
      Lit (Pos v)::a::rest => parse_cutting f_ns xs (Weak a v::rest)
    | _ => NONE)
  else
    case parse_lit_num f_ns s of
    | SOME (l,f_ns1)=> parse_cutting f_ns1 xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_cutting f_ns [] [c] = SOME (c,f_ns)) ∧
  (parse_cutting f_ns [] _ = NONE)
End

Definition strip_numbers_def:
  (strip_numbers [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_numbers xs (Num n::acc)
    else NONE
  | INL _ => NONE)
End

Definition parse_var_def:
  parse_var f_ns v =
  case parse_lit_num f_ns v of SOME (Pos n,f_ns) => SOME (n,f_ns) | _ => NONE
End

(* Parse a substitution {var -> lit} *)
Definition parse_subst_def:
  (parse_subst f_ns (INL v :: INL arr :: r ::rest) acc =
  if arr = strlit "->" then
    case parse_var f_ns v of
      NONE => ([],LN,f_ns)
    | SOME (v,f_ns) =>
    (case r of
        INR r =>
          if r = 0:int then parse_subst f_ns rest (insert v (INL F) acc)
          else if r = 1 then parse_subst f_ns rest (insert v (INL T) acc)
          else ([],LN,f_ns)
      | INL r =>
          (case parse_lit_num f_ns r of NONE => ([],LN,f_ns)
          | SOME (l, f_ns)  => parse_subst f_ns rest (insert v (INR l) acc)))
  else ([],LN,f_ns)) ∧
  (parse_subst f_ns ls acc = (ls, acc,f_ns))
End

Definition parse_constraint_npbc_def:
  parse_constraint_npbc line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  (case rest of (INL cmp :: INR deg :: INL term :: rest) =>
    if term = str #";" ∧ cmp = strlit">=" then
      SOME (pbc_to_npbc (map_pbc hashString (GreaterEqual,lhs,deg)),rest)
    else
      NONE
  | _ => NONE)
End

Definition parse_red_header_def:
  parse_red_header f_ns line =
  case parse_constraint_npbc line of
    SOME (constr,rest) =>
      (case parse_subst f_ns rest LN of (rest,ss,f_ns) =>
       (case rest of
        [INL term; INL beg] =>
          if term = strlit";" ∧ beg = strlit"begin" then
            SOME (constr,ss,f_ns)
          else NONE
      | _ => NONE))
  | _ => NONE
End

Definition parse_subgoal_num_def:
  parse_subgoal_num line =
  case line of
    [INR n] => if n>=0 then SOME (INL (Num n)) else NONE
  | [INL s] =>
     if s = strlit "#1"
     then SOME (INR ())
     else NONE
  | _ => NONE
End

(* Parse a single line of an lstep,
  Except "Red", which might be a
  top-level Red step
*)
Definition parse_lstep_aux_def:
  (parse_lstep_aux s =
    case s of [] => NONE
    | (r::rs) =>
      if r = INL (strlit "c") then
        (case rs of
          [INR id] =>
          if id ≥ 0 then SOME (INL (Contradiction (Num id)))
          else NONE
        | _ => NONE)
      else if r = INL (strlit "d") then
        (case strip_numbers rs [] of NONE => NONE
        | SOME n => SOME (INL (Delete n)))
      else if r = INL (strlit "pol") then
        (case parse_cutting rs [] of NONE => NONE
        | SOME p => SOME (INL (Cutting p)))
      else if r = INL (strlit "e") then
        (case rs of
          INR id::rest =>
          if id ≥ 0 then
            (case parse_constraint_npbc rest of
              SOME (c,[]) => SOME (INL (Check (Num id) c))
            | _ => NONE)
          else NONE
        | _ => NONE)
      else if r = INL (strlit "*") then SOME (INL NoOp)
      else if r = INL (strlit "red") then
        case parse_red_header rs of NONE => NONE
        | SOME (c,s) =>
          SOME (INR (c,s))
      else NONE)
End

Definition check_end_def:
  check_end (h:(mlstring + int) list ) = (h = [INL (strlit"end")])
End

(* Parsing lsteps in a subproof until parsing
  fails and return the failing line
  (note: this expects a failing line)
  redundancy steps can not appear in subproofs
*)
Definition parse_lsteps_aux_def:
  (parse_lsteps_aux
    ([]:(mlstring + int) list list)
    (acc:lstep list) = NONE) ∧
  (parse_lsteps_aux (s::ss) acc =
    case parse_lstep_aux s of
    | NONE => SOME (REVERSE acc, s, ss)
    | SOME (INL step) =>
      parse_lsteps_aux ss (step::acc)
    | SOME (INR (c,s)) =>
      if s ≠ LN then NONE
      else
      case parse_lsteps_aux ss [] of
        NONE => NONE
      | SOME (pf,s,rest) =>
        if LENGTH rest < LENGTH ss then
          if check_end s then
            parse_lsteps_aux rest (Con c pf::acc)
          else NONE
        else NONE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’
  \\ rw[] \\ fs[]
End

Theorem parse_lsteps_aux_LENGTH:
  ∀ss acc acc' s ss'.
  parse_lsteps_aux ss acc = SOME(acc',s,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rw[parse_lsteps_aux_def]>>
  every_case_tac>>
  gs[]
QED

Theorem parse_lsteps_aux_thm:
  (∀acc. parse_lsteps_aux
    ([]:(mlstring + int) list list) acc = NONE) ∧
  (∀s ss acc.
    parse_lsteps_aux (s::ss) acc =
    case parse_lstep_aux s of
    | NONE => SOME (REVERSE acc, s, ss)
    | SOME (INL step) =>
      parse_lsteps_aux ss (step::acc)
    | SOME (INR (c,s)) =>
      if s ≠ LN then NONE
      else
      case parse_lsteps_aux ss [] of
        NONE => NONE
      | SOME (pf,s,rest) =>
          if check_end s then
            parse_lsteps_aux rest (Con c pf::acc)
          else NONE)
Proof
  rw[]
  >-
    simp[Once parse_lsteps_aux_def]
  >- (
    simp[Once parse_lsteps_aux_def]>>
    every_case_tac>>fs[]>>
    imp_res_tac parse_lsteps_aux_LENGTH)
QED

(* parse the body of a redundancy proof, which is of the form:
  lsteps
  proofgoal ... begin
  end
  lsteps
  proofgoal ... begin
  end
end
*)
Definition parse_red_body_def:
  (parse_red_body [] = NONE) ∧
  (parse_red_body (r::rs) =
    if r = INL (strlit"end") then SOME (INL ())
    else
    if r = INL (strlit"proofgoal") then
       case parse_subgoal_num rs of NONE => NONE
       | SOME ind => SOME (INR ind)
    else NONE)
End

Definition mk_acc_def:
  mk_acc pf (acc:(( (num + unit) option,lstep list) alist)) = if pf = [] then acc else (NONE,pf)::acc
End

Definition parse_red_aux_def:
  (parse_red_aux ss
    (acc:(( (num + unit) option,lstep list) alist)) =
  case parse_lsteps_aux ss [] of
    NONE => NONE
  | SOME (pf,s,rest) =>
    let acc' = mk_acc pf acc in
    (case parse_red_body s of
      NONE => NONE
    | SOME (INL u) => SOME (REVERSE acc', rest)
    | SOME (INR ind) =>
      (case parse_lsteps_aux rest [] of
        NONE => NONE
      | SOME (pf,s,rest2) =>
        if check_end s then parse_red_aux rest2 ((SOME ind,pf)::acc')
        else NONE))
  )
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’
  \\ rw[] \\ fs[]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
End

Theorem parse_red_aux_LENGTH:
  ∀ss acc acc' ss'.
  parse_red_aux ss acc = SOME(acc',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac (fetch "-" "parse_red_aux_ind")>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_red_aux_def]>>
  every_case_tac>>fs[]>>
  rw[]>>imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
QED

(* Parse 1 top level step until EOF *)
(* TODO: needs fixing
Definition parse_top_def:
  (parse_top [] = SOME NONE) ∧
  (parse_top (s::ss) =
    case parse_lstep_aux s of NONE => NONE
    | SOME (INL step) =>
        SOME (SOME (Lstep step,ss))
    | SOME (INR (c,s)) =>
      if s = LN then
        (case parse_lsteps_aux ss [] of
          NONE => NONE
        | SOME (pf,s,rest) =>
          if check_end s then
            SOME (SOME (Lstep (Con c pf),rest))
          else NONE)
      else
        (case parse_red_aux ss [] of
          NONE => NONE
        | SOME (pf,rest) =>
          SOME (SOME (Red c s pf,rest))
        ))
End
*)

Definition fromString_unsafe_def:
  fromString_unsafe str =
    if strlen str = 0
    then 0i
    else if strsub str 0 = #"~" ∨
            strsub str 0 = #"-"
      then ~&fromChars_unsafe (strlen str - 1)
                              (substring str 1 (strlen str - 1))
      else &fromChars_unsafe (strlen str) str
End

Definition tokenize_fast_def:
  tokenize_fast (s:mlstring) =
  if strlen s = 0 then INL s
  else
  let c = ORD (strsub s 0) in
  if 48 ≤ c ∧ c ≤ 57
  then INR (fromString_unsafe s)
  else INL s
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 1.2")``);

Definition parse_header_line_fast_def:
  parse_header_line_fast s = (s = ^headertrm)
End

(*

(* Parse a list of strings in pbf format *)
Definition parse_tops_def:
  (parse_tops ss =
    case ss of [] => SOME []
    | _ =>
    case parse_top ss of NONE => NONE
    | (SOME (step,rest)) =>
      case parse_tops rest of NONE => NONE
      | SOME sts => SOME (step::sts))

(* Parse the tokenized pbf file *)
Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
    if parse_header_line_fast s then
      parse_tops ss
    else NONE
  | [] => NONE
End

Definition parse_pbp_def:
  parse_pbp strs = parse_pbp_toks (MAP toks_fast strs)
End

val pbfraw = ``[
  strlit" * #variable= 4 #constraint= 7";
  strlit" 2 ~x1 1 ~x3 >= 1 ;";
  strlit" 1 ~x3 1 ~x5 >= 1 ;";
  strlit" 1 ~x1 1 ~x5 >= 1 ;";
  strlit" 1 ~x2 1 ~x4 1 ~x6 >= 2 ;";
  strlit" +1 x1 +1 x2 >= 1 ;";
  strlit" +1 x3 +1 x4 >= 1 ;";
  strlit" +1 x5 +1 x6 >= 1 ;"
  ]``;

  val pbf = rconc (EVAL ``build_fml 1 (full_normalise (SND (THE (parse_pbf ^(pbfraw)))))``);

  val pbpraw = ``[
  strlit"pseudo-Boolean proof version 1.2";
  strlit"f 7";
  strlit"pol 1 s";
  strlit"pol 8 2 + 3 +";
  strlit"pol 9 2 d";
  strlit"red 1 x1 >= 1 ; x1 -> x3 x3 -> x5 x5 -> x1 x2 -> x4 x4 -> x6 x6 -> x2 ; begin";
  strlit"e 11 1 ~x1 >= 1 ;";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"proofgoal #1";
  strlit"e 12 1 ~x3 >= 1 ;";
  strlit"pol 12 11 + 5 + 6 +";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"end";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"pol 13 4 +";
  strlit"pol 14 x6 +";
  strlit"c 15";
  strlit"end";
  strlit"proofgoal 1";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"pol 16 2 +";
  strlit"c 17";
  strlit"end";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"end";
  strlit"end";
  ]``

  val steps = rconc (EVAL``(parse_pbp ^(pbpraw))``)

  val pbpraw = ``MAP toks_fast [
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end";
  strlit"end";
  ]``

  EVAL`` parse_lstep_aux (HD ^(pbpraw))``

  EVAL`` parse_lsteps_aux ^(pbpraw) []``
  parse_lsteps_aux_def
*)

val _ = export_theory();
