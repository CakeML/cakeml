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

Definition map_f_ns_def:
  (map_f_ns f_ns [] = SOME ([],f_ns)) ∧
  (map_f_ns f_ns ((c,l)::xs) =
  case apply_lit f_ns l of
    NONE => NONE
  | SOME (l',f_ns') =>
    case map_f_ns f_ns' xs of NONE => NONE
    | SOME (ys,f_ns'') =>
      SOME ((c,l')::ys,f_ns''))
End

Definition parse_constraint_npbc_def:
  parse_constraint_npbc f_ns line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  (case rest of (INL cmp :: INR deg :: INL term :: rest) =>
    if term = str #";" ∧ cmp = strlit">=" then
      case map_f_ns f_ns lhs of NONE => NONE
      | SOME (lhs',f_ns') =>
        SOME (
          pbc_to_npbc (GreaterEqual,lhs',deg),
          rest,
          f_ns')
    else
      NONE
  | _ => NONE)
End

Definition parse_red_header_def:
  parse_red_header f_ns line =
  case parse_constraint_npbc f_ns line of
    SOME (constr,rest,f_ns') =>
      (case parse_subst f_ns' rest LN of (rest,ss,f_ns'') =>
       (case rest of
        [INL term; INL beg] =>
          if term = strlit";" ∧ beg = strlit"begin" then
            SOME (constr,ss,f_ns'')
          else NONE
      | _ => NONE))
  | _ => NONE
End

(* Parse a single line of an lstep,
  Except "Red", which will be handled later *)
Definition parse_lstep_aux_def:
  (parse_lstep_aux f_ns s =
    case s of [] => NONE
    | (r::rs) =>
      if r = INL (strlit "deld") then
        (case strip_numbers rs [] of NONE => NONE
        | SOME n => SOME (INL (Delete n),f_ns))
      else if r = INL (strlit "pol") then
        (case parse_cutting f_ns rs [] of NONE => NONE
        | SOME (p,f_ns') => SOME (INL (Cutting p),f_ns'))
      else if r = INL (strlit "red") then
        case parse_red_header f_ns rs of NONE => NONE
        | SOME (c,s,f_ns') =>
          SOME (INR (c,s),f_ns')
      else if r = INL (strlit "e") then
        (case rs of
          INR id::rest =>
          if id ≥ 0 then
            (case parse_constraint_npbc f_ns rest of
              SOME (c,[],f_ns') => SOME (INL (Check (Num id) c),f_ns')
            | _ => NONE)
          else NONE
        | _ => NONE)
      else if r = INL (strlit "*") then SOME (INL NoOp,f_ns)
      else NONE)
End

Definition check_end_def:
  check_end (h:(mlstring + int) list ) =
  case h of
    [INL e; INR n] =>
    if e = (strlit"end") ∧ n ≥ 0 then SOME (Num n) else NONE
  | _ => NONE
End

(* Parsing lsteps in a subproof until parsing
  fails and return the failing line
  (note: this expects a failing line)
  redundancy steps can not appear in subproofs
*)
Definition parse_lsteps_aux_def:
  (parse_lsteps_aux f_ns
    ([]:(mlstring + int) list list)
    (acc:lstep list) = NONE) ∧
  (parse_lsteps_aux f_ns (s::ss) acc =
    case parse_lstep_aux f_ns s of
    | NONE => SOME (REVERSE acc, f_ns, s, ss)
    | SOME (INL step, f_ns') =>
      parse_lsteps_aux f_ns' ss (step::acc)
    | SOME (INR (c,s), f_ns') =>
      if s ≠ LN then NONE
      else
        case parse_lsteps_aux f_ns' ss [] of
          NONE => NONE
        | SOME (pf,f_ns'',s,rest) =>
        if LENGTH rest < LENGTH ss then
          case check_end s of
            NONE => NONE
          | SOME id =>
            parse_lsteps_aux f_ns'' rest (Con c pf id::acc)
        else NONE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’
  \\ rw[] \\ fs[]
End

Theorem parse_lsteps_aux_LENGTH:
  ∀f_ns ss acc acc' f_ns' s ss'.
  parse_lsteps_aux f_ns ss acc = SOME(acc',f_ns' ,s,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rw[parse_lsteps_aux_def]>>
  every_case_tac>>
  gs[]
QED

Theorem parse_lsteps_aux_thm:
  (∀f_ns acc.
    parse_lsteps_aux f_ns
    ([]:(mlstring + int) list list)
    (acc:lstep list) = NONE) ∧
  (∀f_ns s ss acc.
    parse_lsteps_aux f_ns (s::ss) acc =
    case parse_lstep_aux f_ns s of
    | NONE => SOME (REVERSE acc, f_ns, s, ss)
    | SOME (INL step, f_ns') =>
      parse_lsteps_aux f_ns' ss (step::acc)
    | SOME (INR (c,s), f_ns') =>
      if s ≠ LN then NONE
      else
        case parse_lsteps_aux f_ns' ss [] of
          NONE => NONE
        | SOME (pf,f_ns'',s,rest) =>
          case check_end s of
            NONE => NONE
          | SOME id =>
            parse_lsteps_aux f_ns'' rest (Con c pf id::acc))
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
  end (id)
  lsteps
  proofgoal ... begin
  end (id)
end (NO ID HERE)
*)

(* #n -> n-1 *)
Definition parse_hash_num_def:
  parse_hash_num s =
  if strlen s ≥ 1 ∧ strsub s 0 = #"#" then
    OPTION_MAP (λn. n-1)
      (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

Definition parse_subgoal_num_def:
  parse_subgoal_num line =
  case line of
    [INR n] => if n>=0 then SOME (INL (Num n)) else NONE
  | [INL s] =>
    (case parse_hash_num s of
      SOME n => SOME (INR n)
    | NONE => NONE)
  | _ => NONE
End

Definition parse_proofgoal_def:
  parse_proofgoal (h:(mlstring + int) list ) =
  case h of
    INL e::rs =>
    (if e = (strlit"proofgoal") then
      parse_subgoal_num rs
    else NONE)
  | _ => NONE
End

Definition parse_red_body_def:
  (parse_red_body (h:(mlstring + int) list ) =
    if h = [INL (strlit "end")] then SOME (INL ())
    else
    case parse_proofgoal h of
      SOME ind => SOME (INR ind)
    | NONE => NONE)
End

Definition mk_acc_def:
  mk_acc pf (acc:(( ((num + num) # num) option,lstep list) alist)) = if pf = [] then acc else (NONE,pf)::acc
End

Definition parse_red_aux_def:
  (parse_red_aux f_ns ss
    (acc:(( ((num + num) # num) option,lstep list) alist)) =
  case parse_lsteps_aux f_ns ss [] of
    NONE => NONE
  | SOME (pf,f_ns',s,rest) =>
    let acc' = mk_acc pf acc in
    (case parse_red_body s of
      NONE => NONE
    | SOME (INL u) => SOME (REVERSE acc', f_ns', rest)
    | SOME (INR ind) =>
      (case parse_lsteps_aux f_ns' rest [] of
        NONE => NONE
      | SOME (pf,f_ns'',s,rest2) =>
        case check_end s of
          NONE => NONE
        | SOME id =>
        parse_red_aux f_ns'' rest2 ((SOME (ind,id),pf)::acc')
       ))
  )
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’
  \\ rw[] \\ fs[]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
End

Theorem parse_red_aux_LENGTH:
  ∀f_ns ss acc acc' f_ns' ss'.
  parse_red_aux f_ns ss acc = SOME(acc',f_ns',ss') ⇒
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

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 2.0")``);

(* We could check that the constraint id is correct here *)
Definition check_f_line_def:
  check_f_line s =
  case s of [] => F
  | x::xs => x = INL(strlit "f")
End

Definition parse_header_def:
  parse_header ss =
  case ss of
    x::y::rest =>
    if x = ^headertrm ∧ check_f_line y
      then SOME rest
      else NONE
  | _ => NONE
End

(* Parse only UNSAT conclusions for now *)
val outputtrm = rconc (EVAL``toks_fast (strlit"output NONE")``);
val endtrm = rconc (EVAL``toks_fast (strlit"end pseudo-Boolean proof")``);

Definition parse_conc_unsat_def:
  parse_conc_unsat s =
  case s of
    [x;y;INR n] =>
    if x = INL (strlit "conclusion") ∧
      y = INL (strlit "UNSAT") ∧ n ≥ 0
    then SOME (Num n) else NONE
  | _ => NONE
End

Definition parse_conc_def:
  parse_conc s y z =
  if s = ^outputtrm ∧ z = ^endtrm then
    parse_conc_unsat y
  else NONE
End

(* Parse 1 sstep,
  until an unparseable line is reached *)
Definition parse_sstep_def:
  (parse_sstep f_ns [] = NONE) ∧
  (parse_sstep f_ns (s::ss) =
    case parse_lstep_aux f_ns s of
      NONE => SOME (INL s,f_ns,ss)
    | SOME (INL step,f_ns') =>
        SOME (INR (Lstep step),f_ns',ss)
    | SOME (INR (c,s),f_ns') =>
      if s = LN then
        (case parse_lsteps_aux f_ns' ss [] of
          NONE => NONE
        | SOME (pf,f_ns'',s,rest) =>
          case check_end s of
            NONE => NONE
          | SOME id =>
            SOME (INR (Lstep (Con c pf id)),f_ns'',rest))
      else
        (case parse_red_aux f_ns' ss [] of
          NONE => NONE
        | SOME (pf,f_ns'',rest) =>
          SOME (INR (Red c s pf),f_ns'',rest)))
End

Definition parse_pre_order_head_def:
  parse_preorder_head s =
  case s of
    [x;INL name] =>
      if x = INL (strlit"pre_order") then
        SOME name
      else NONE
  | _ => NONE
End

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

Definition hashString_nf_def:
  hashString_nf s t = SOME(hashString s,t)
End

Definition parse_vars_line_aux_def:
  (parse_vars_line_aux f_ns [] = SOME ([],f_ns)) ∧
  (parse_vars_line_aux f_ns (x::xs) =
  case x of
    INL v =>
    (case parse_var f_ns v of
      NONE => NONE
    | SOME (vv,f_ns') =>
      (case parse_vars_line_aux f_ns' xs of NONE => NONE
      | SOME (vvs,f_ns'') => SOME (vv::vvs,f_ns'')))
  | _ => NONE)
End

Definition parse_vars_line_def:
  parse_vars_line n l =
  case l of
    h::rest =>
    if h = INL n then
      OPTION_MAP FST (parse_vars_line_aux (hashString_nf,()) rest)
    else NONE
  | _ => NONE
End

Definition parse_vars_aux_def:
  parse_vars_aux v l r a e =
    if v = [INL (strlit"vars")] ∧
       a = [INL (strlit"aux")] ∧
       e = [INL (strlit"end")] then
      case parse_vars_line (strlit "left") l of NONE => NONE
      | SOME us =>
      case parse_vars_line (strlit "right") r of NONE => NONE
      | SOME vs => SOME (us,vs)
    else NONE
End

Definition parse_vars_block_def:
  parse_vars_block ss =
  case ss of
    v::l::r::a::e::rest =>
    (case parse_vars_aux v l r a e of NONE => NONE
    | SOME res => SOME (res,rest))
  | _ => NONE
End

(* parse constraints *)
Definition parse_def_aux_def:
  (parse_def_aux [] acc = NONE) ∧
  (parse_def_aux (s::ss) acc =
    if s = [INL (strlit"end")] then
      SOME(REVERSE acc,ss)
    else
      case parse_constraint_npbc (hashString_nf,()) s of
        NONE => NONE
      | SOME (c,_) => parse_def_aux ss (c::acc))
End

Definition parse_def_block_def:
  parse_def_block ss =
  case ss of
    h::rest =>
    if h = [INL (strlit"def")] then
      parse_def_aux rest []
    else NONE
  | _ => NONE
End

Definition parse_trans_aux_def:
  parse_trans_aux t v f e p =
    if t = [INL (strlit"transitivity")] ∧
       v = [INL (strlit"vars")] ∧
       e = [INL (strlit"end")] ∧
       p = [INL (strlit"proof")]
    then
      case parse_vars_line (strlit "fresh_right") f of NONE => NONE
      | SOME ws => SOME ws
    else NONE
End

Definition parse_trans_block_def:
  parse_trans_block ss =
  case ss of
    t::v::f::e::p::rest =>
    (case parse_trans_aux t v f e p of NONE => NONE
    | SOME res => SOME (res,rest))
  | _ => NONE
End

Definition parse_proof_block_def:
  parse_proof_block ss =
  case parse_red_aux (hashString_nf,()) ss [] of
    NONE => NONE
  | SOME (pf,_,rest) => SOME (pf,rest)
End

Definition parse_end_block_def:
  parse_end_block ss =
  case ss of
    x::y::rest =>
    if x = [INL(strlit "end")] ∧ x = y then SOME rest else NONE
  | _ => NONE
End

Definition parse_pre_order_def:
  parse_pre_order ss =
  case parse_vars_block ss of NONE => NONE
  | SOME ((us,vs), ss) =>
  case parse_def_block ss of NONE => NONE
  | SOME (f, ss) =>
  case parse_trans_block ss of NONE => NONE
  | SOME (ws, ss) =>
  case parse_proof_block ss of NONE => NONE
  | SOME (pf, ss) =>
  case parse_end_block ss of NONE => NONE
  | SOME ss =>
     SOME ((f,us,vs),ws,pf,ss)
End

(*
EVAL ``
  parse_pre_order (MAP toks [
  strlit"  vars";
  strlit"  left u1";
  strlit"  right v1";
  strlit"  aux";
  strlit"  end";
  strlit"  def";
  strlit"  1 ~u1 1 v1 >= 1 ;";
  strlit"  1 ~u1 1 v1 >= 1 ;";
  strlit"  1 ~u1 1 v1 >= 1 ;";
  strlit"  end";
  strlit"  transitivity";
  strlit"  vars";
  strlit"  fresh_right w1";
  strlit"  end";
  strlit"  proof";
  strlit"  proofgoal #1";
  strlit"  pol 2 1 + 3 +";
  strlit"  end 4";
  strlit"  end";
  strlit"  end";
  strlit"  end";
])``
*)

Datatype:
  par =
  | Done cstep
  | Dompar npbc subst
  | StoreOrderpar mlstring
  | CheckedDeletepar (num list)
End

Definition parse_load_order_def:
  (parse_load_order f_ns [] = SOME (Done UnloadOrder,f_ns)) ∧
  (parse_load_order f_ns (INL r::rs) =
    case parse_vars_line_aux f_ns rs of
      NONE => NONE
    | SOME (ws,f_ns') => SOME (Done (LoadOrder r ws),f_ns'))
End

(* Partial parse *)
(* TODO: support Obj *)
(* Parse the first line of a cstep, sstep supported differently *)
Definition parse_cstep_head_def:
  parse_cstep_head f_ns s =
  case s of [] => NONE
  | (r::rs) =>
    if r = INL (strlit "load_order") then
      parse_load_order f_ns rs
    else if r = INL (strlit"core") then
      (case rs of [] => NONE
      | r::rs =>
        if r = INL(strlit"id") then
          case strip_numbers rs [] of NONE => NONE
          | SOME n => SOME (Done (Transfer n),f_ns)
        else NONE)
    else if r = INL (strlit "dom") then
      case parse_red_header f_ns rs of NONE => NONE
      | SOME (c,s,f_ns') =>
        SOME (Dompar c s,f_ns')
    else if r = INL (strlit "delc") then
      (case strip_numbers rs [] of NONE => NONE
      | SOME n => SOME (CheckedDeletepar n,f_ns))
    else if r = INL (strlit "pre_order") then
      case rs of [INL name] => SOME (StoreOrderpar name, f_ns)
      | _ => NONE
    else NONE
End

(* TODO: support subproofs in checked delete *)
Definition parse_cstep_def:
  (parse_cstep f_ns ss =
    case parse_sstep f_ns ss of
      NONE => NONE
    | SOME (INR sstep, f_ns',rest) =>
      SOME (INR (Sstep sstep), f_ns', rest)
    | SOME (INL s,f_ns',rest) =>
      case parse_cstep_head f_ns' s of
        NONE => SOME (INL s,f_ns',rest)
      | SOME(Done cstep,f_ns'') => SOME (INR cstep, f_ns'', rest)
      | SOME (Dompar c s,f_ns'') =>
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (pf,f_ns'',rest) => SOME (INR (Dom c s pf), f_ns'', rest))
      | SOME (CheckedDeletepar n, f_ns'') =>
        SOME (INR (CheckedDelete n []), f_ns'',rest)
      | SOME (StoreOrderpar name, f_ns'') =>
        (case parse_pre_order rest of NONE => NONE
        | SOME (spo,ws,pf,rest) =>
          SOME (INR (StoreOrder name spo ws pf), f_ns'',rest))
    )
End

(*
(* Parse a list of strings in pbf format, not used *)
Definition parse_csteps_def:
  (parse_csteps f_ns ss acc =
    case parse_cstep f_ns ss of
      NONE => NONE
    | SOME (res,f_ns',rest) =>
      case res of
        INL s => SOME(REVERSE acc, s, f_ns', rest)
      | INR st =>
        parse_csteps f_ns' rest (st::acc))
Termination
  cheat
End

Definition plainVar_nf_def:
  plainVar_nf s (u:unit) =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n => SOME (n,())
  else
    NONE
End

(* Parse the tokenized pbf file *)
Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  case parse_header tokss of
    SOME rest =>
      (case parse_csteps (plainVar_nf,()) rest [] of
        SOME (pf, s, f_ns', rest') =>
        SOME (pf, s, rest'))
  | NONE => NONE
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
  strlit"pseudo-Boolean proof version 2.0";
  strlit"f 7";
  strlit"pol 1 s";
  strlit"pol 8 2 + 3 +";
  strlit"pol 9 2 d";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end 500";
  strlit"red 1 x1 >= 1 ; x1 -> x3 x3 -> x5 x5 -> x1 x2 -> x4 x4 -> x6 x6 -> x2 ; begin";
  strlit"e 11 1 ~x1 >= 1 ;";
  strlit"proofgoal #1";
  strlit"e 12 1 ~x3 >= 1 ;";
  strlit"pol 12 11 + 5 + 6 +";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end 1";
  strlit"end 2";
  strlit"red 1 x1 >= 1 ; ; begin";
  strlit"end 3";
  strlit"pol 13 4 +";
  strlit"pol 14 x6 +";
  strlit"end 15";
  strlit"e 11 1 ~x1 >= 1 ;";
  strlit"proofgoal 1";
  strlit"pol 16 2 +";
  strlit"end 17";
  strlit"end";
  strlit"e 11 1 ~x1 >= 1 ;";
  strlit"output NONE";
  strlit"conclusion UNSAT 5";
  strlit"end pseudo-Boolean proof";
]``

  val pbpraw2 = ``[
  strlit"pseudo-Boolean proof version 2.0";
  strlit"f 10";
  strlit"pre_order simple";
  strlit"    vars";
  strlit"        left u1";
  strlit"        right v1";
  strlit"        aux ";
  strlit"  end";
  strlit"    def";
  strlit"        1 ~u1 1 v1 >= 1 ;";
  strlit"  end";
  strlit"    transitivity";
  strlit"        vars";
  strlit"            fresh_right w1";
  strlit"    end";
  strlit"        proof";
  strlit"      proofgoal #1";
  strlit"      pol 2 1 + 3 + ";
  strlit"      end 4";
  strlit"    end";
  strlit"  end";
  strlit"end";
  strlit"load_order simple x1";
  strlit"pol 1 2 + ";
  strlit"red 1 x3 1 x1 >= 1 ; x3 -> 1 ; begin";
  strlit"    * autoproven: goal is implied by negated constraint";
  strlit"    proofgoal #1";
  strlit"        pol 13 12 +";
  strlit"    end 14";
  strlit"end";
  strlit"dom 1 ~x1 1 x2 >= 1 ; x1 -> x2 x2 -> x1 ; begin";
  strlit"    * autoproven: goal is implied by negated constraint";
  strlit"    proofgoal #1";
  strlit"        pol 17 16 +";
  strlit"    end 18";
  strlit"    * autoproven: implied by RUP";
  strlit"    proofgoal #2";
  strlit"        pol  19 16 ~x1 + 2 d + s 16 x2 + 2 d + s";
  strlit"    end 20";
  strlit"end";
  strlit"load_order simple x1";
  strlit"output NONE";
  strlit"conclusion NONE";
  strlit"end pseudo-Boolean proof";]``

val steps = rconc (EVAL``(parse_pbp ^(pbpraw))``)
val steps = rconc (EVAL``(parse_pbp ^(pbpraw2))``)
*)

val _ = export_theory();
