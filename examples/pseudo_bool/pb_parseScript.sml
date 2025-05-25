(*
  Parse and print for pbc, npb_check
*)
open preamble pbcTheory pbc_normaliseTheory npbc_checkTheory;

val _ = new_theory "pb_parse";

val _ = numLib.temp_prefer_num();

(*
  Printing for pseudo-Boolean problems in (extended) OPB format
*)

(* Printing mlstring pbc *)
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
      int_to_string #"-" i; strlit " ;\n"])
End

Definition annot_pbc_string_def:
  annot_pbc_string (annot,str) =
    let s = pbc_string str in
      case annot of NONE => s
      | SOME l =>
      concat [ strlit"@";l; strlit" ";s]
End

(* printing a string pbf, possibly with string annotation *)
Definition obj_string_def:
  obj_string (f,c:int) =
  let c_string =
    if c = 0 then strlit"" else
    strlit " " ^
      int_to_string #"-" c in
  strlit"min: " ^ lhs_string f ^ c_string ^ strlit" ;\n"
End

Definition pres_string_def:
  pres_string pres =
  let c_string =
    concatWith (strlit" ") pres in
  strlit"preserve_init " ^ c_string ^ strlit" \n"
End

(* Problem without annotation *)
Definition print_prob_def:
  print_prob (pres,obj,fml) =
  let obstr = case obj of NONE => [] | SOME fc => [obj_string fc] in
  let presstr = case pres of NONE => [] | SOME p => [pres_string p] in
    obstr ++ presstr ++ MAP pbc_string fml
End

(* Problem without annotation *)
Definition print_annot_prob_def:
  print_annot_prob (pres,obj,fml) =
  let obstr = case obj of NONE => [] | SOME fc => [obj_string fc] in
  let presstr = case pres of NONE => [] | SOME p => [pres_string p] in
    obstr ++ presstr ++ MAP annot_pbc_string fml
End

(* Strips annotations *)
Definition strip_annot_prob_def:
  strip_annot_prob (pres,obj,afml) =
  (pres,obj,MAP SND afml)
End

(*
  Parse an OPB file as a string-variabled PB problem
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
  Valid names may contain a-z,A-Z,0-9,[]{}_^- characters
*)
Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" then
    let ss = substring s 1 (strlen s - 1) in
    if goodString ss then
        SOME (Neg ss)
    else NONE
  else if strlen s ≥ 1 then
    if goodString s then SOME (Pos s)
    else NONE
  else NONE
End

(*
  EVAL ``parse_lit (strlit "xaAa_-1")``
  EVAL ``parse_lit (strlit "~x1234")``
  EVAL ``parse_lit (strlit "fancy_{1}^[-42]")``
*)

(* Parse the LHS of a constraint and returns the remainder of the line *)
Definition parse_constraint_LHS_aux_def:
  (parse_constraint_LHS_aux (INR n::INL v::rest) acc =
    case parse_lit v of NONE => (INR n::INL v::rest,REVERSE acc)
    | SOME lit => parse_constraint_LHS_aux rest ((n,lit)::acc)) ∧
  (parse_constraint_LHS_aux ls acc = (ls,REVERSE acc))
End

Definition parse_constraint_LHS_def:
  parse_constraint_LHS ss = parse_constraint_LHS_aux ss []
End

(* Strip ; terminator from the end of a string *)
Definition strip_term_def:
  strip_term s =
  if strlen s ≥ 1 ∧ strsub s (strlen s - 1) = #";"
  then SOME (substring s 0 (strlen s - 1))
  else NONE
End

(* Strip ; from the end of a tokenized line and retokenize *)
Definition strip_term_line_aux_def:
  (strip_term_line_aux [] acc = NONE) ∧
  (strip_term_line_aux [x] acc =
    case x of INR n => NONE
    | INL s =>
    if s = strlit ";"
    then SOME (REVERSE acc)
    else
        case strip_term s of
          SOME s =>
            SOME (REVERSE (tokenize s::acc))
        | NONE => NONE) ∧
  (strip_term_line_aux (x::xs) acc =
    strip_term_line_aux xs (x::acc))
End

Definition strip_term_line_def:
  strip_term_line ss = strip_term_line_aux ss []
End

(*
  EVAL ``strip_term_line (toks (strlit "foo bar asdf;"))``
  EVAL ``strip_term_line (toks (strlit "foo bar asdf ;"))``
  EVAL ``strip_term_line (toks (strlit "foo bar ~1;"))``
  EVAL ``strip_term_line (toks (strlit "foo bar 1 ;"))``
*)

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
  case OPTION_MAP parse_constraint_LHS (strip_term_line line) of
    NONE => NONE
  | SOME(rest,lhs) =>
    (case rest of
      [INL cmp; INR deg] =>
      (case parse_op cmp of
        NONE => NONE
      | SOME op =>
        SOME ((op,lhs,deg):mlstring pbc))
    | _ => NONE)
End

(* strips off the head of a line as an annotation *)
Definition parse_annot_def:
  parse_annot line =
  case line of
    (INL s)::ls =>
    if strlen s ≥ 1 ∧ strsub s 0 = #"@" then
      (SOME (substring s 1 (strlen s - 1)), ls)
    else (NONE, line)
  | _ => (NONE, line)
End

Definition parse_annot_constraint_def:
  parse_annot_constraint line =
  case parse_annot line of (annot,line) =>
    OPTION_MAP (λres. (annot,res)) (parse_constraint line)
End

(*
  EVAL ``parse_annot (toks (strlit "2 ~x1 1 ~x3 >= 1;"))``;
  EVAL ``parse_constraint (toks (strlit "2 ~x1 1 ~x3 >= 1 ;"))``;
  EVAL ``parse_annot_constraint (toks (strlit "@asdf 2 ~x1 1 ~x3 >= 1;"))``;
*)

Definition parse_constraints_def:
  (parse_constraints [] acc = SOME (REVERSE acc)) ∧
  (parse_constraints (s::ss) acc =
    case parse_annot_constraint s of
      NONE => NONE
    | SOME pbc => parse_constraints ss (pbc::acc))
End

Definition nocomment_line_def:
  (nocomment_line (INL c::cs) =
    (strlen c < 1 ∨ strsub c 0 ≠ #"*")) ∧
  (nocomment_line _ = T)
End

(* Allow the min objective to end with either a constant or not:
  lin_term constant
  lin_term
*)

(* parse objective term in pbc ... ; *)
Definition parse_obj_term_def:
  parse_obj_term xs =
  case OPTION_MAP parse_constraint_LHS (strip_term_line xs) of
    NONE => NONE
  | SOME(rest,obj) =>
  case rest of
    [] => SOME (obj,0:int)
  | [INR c] => SOME (obj,c:int)
  | _ => NONE
End

(*
  EVAL``parse_obj_term (toks (strlit"1 ~x199 1 x2 ~5 ;"))``
  EVAL``parse_obj_term (toks (strlit"1 ~x199 1 x2 ~5;"))``
  EVAL``parse_obj_term (toks (strlit"1 ~x199 1 x2 ;"))``
  EVAL``parse_obj_term (toks (strlit"1 ~x199 1 x2;"))``
  EVAL``parse_obj_term (toks (strlit"1 ~x199 1 x2 5;"))``
*)

(* parse objective line in PBF *)
Definition parse_obj_def:
  (parse_obj [] = NONE) ∧
  (parse_obj (x::xs) =
    if x = INL (strlit "min:") then
      parse_obj_term xs
    else NONE
  )
End

(* raw string but must be a valid var name *)
Definition parse_var_raw_def:
  (parse_var_raw (INL s) =
    if goodString s then SOME s else NONE) ∧
  (parse_var_raw _ = NONE)
End

Definition parse_vars_raw_def:
  (parse_vars_raw [] = SOME []) ∧
  (parse_vars_raw (s::ss) =
    case parse_var_raw s of NONE => NONE | SOME v =>
    case parse_vars_raw ss of NONE => NONE | SOME vs => SOME (v::vs))
End

(* parse projection or preserved line in PBF *)
Definition parse_pres_def:
  (parse_pres [] = NONE) ∧
  (parse_pres (x::xs) =
    if x = INL (strlit "preserve_init") then
      OPTION_BIND (strip_term_line xs) parse_vars_raw
    else NONE)
End

(*
  EVAL``parse_pres (toks (strlit"preserve_init x1 x2 x2 a b c ;"))``
  EVAL``parse_pres (toks (strlit"preserve_init x1 x2 x2 a b c;"))``
*)

(* parse optional objective line *)
Definition parse_obj_maybe_def:
  (parse_obj_maybe [] = (NONE , [])) ∧
  (parse_obj_maybe (l::ls) =
  case parse_obj l of
    NONE => (NONE, l::ls)
  | SOME obj => (SOME obj, ls))
End

(* parse optional preserved line *)
Definition parse_pres_maybe_def:
  (parse_pres_maybe [] = (NONE , [])) ∧
  (parse_pres_maybe (l::ls) =
  case parse_pres l of
    NONE => (NONE, l::ls)
  | SOME pres => (SOME pres, ls))
End

Definition parse_obj_pres_maybe_def:
  parse_obj_pres_maybe ls =
    case parse_obj_maybe ls of
    | (SOME obj,ls) =>
        (SOME obj, parse_pres_maybe ls)
    | (NONE, ls) =>
      (case parse_pres_maybe ls of
      | (SOME pres,ls) =>
        (case parse_obj_maybe ls of (ob,ls) => (ob, SOME pres, ls))
      | (NONE,ls) => (NONE,NONE,ls))
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  let (obj,pres,rest) = parse_obj_pres_maybe nocomments in
  case parse_constraints rest [] of
    NONE => NONE
  | SOME pbf => SOME (pres,obj,pbf)
End

(* Parse a list of strings in annotated pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(*
  Parsing a proof file
*)

(* Fast tokenization *)
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

Definition is_numeric_def:
  is_numeric c =
  let n = ORD c in
  48 ≤ n ∧ n ≤ 57
End

Definition is_num_prefix_def:
  is_num_prefix c =
  (c = #"~" ∨ c = #"-")
End

Definition int_start_def:
  int_start s =
  ((strlen s > 0 ∧ is_numeric (strsub s 0)) ∨
  (strlen s > 1 ∧
    is_num_prefix (strsub s 0) ∧
    is_numeric (strsub s 1)))
End

Definition tokenize_fast_def:
  tokenize_fast (s:mlstring) =
  if int_start s then
    INR (fromString_unsafe s)
  else INL s
End

Definition toks_fast_def:
  toks_fast s = MAP tokenize_fast (tokens blanks s)
End

Type name_fun[pp] = “:(mlstring -> α -> (num # α) option) # α”

(* String literals are automatically mapped to internal names *)
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

(* Unused, but useful for testing
Definition plainVar_nf_def:
  plainVar_nf s (u:unit) =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n => SOME (n,())
  else
    NONE
End
*)

(* The cutting planes polish notation stack is formed from constraints, where
  factors and variables are also encoded using Id *)
Definition parse_lit_num_def:
  parse_lit_num (f_ns:'a name_fun) s =
    case parse_lit s of
    | NONE => NONE
    | SOME l => apply_lit f_ns l
End

(* Parsing cutting planes in polish notation (header "pol", ";" stripped) *)
Definition parse_cutting_aux_def:
  (parse_cutting_aux f_ns (x::xs) stack =
  case x of INR n =>
    if n ≥ 0 then
      parse_cutting_aux f_ns xs (Id (Num n) :: stack)
    else NONE
  | INL s =>
  if s = str #"+" then
    (case stack of
      a::b::rest => parse_cutting_aux f_ns xs (Add b a::rest)
    | _ => NONE)
  else if s = str #"*" then
    (case stack of
      Id a::b::rest => parse_cutting_aux f_ns xs (Mul b a::rest)
    | _ => NONE)
  else if s = str #"d" then
    (case stack of
      Id a::b::rest => parse_cutting_aux f_ns xs (Div b a::rest)
    | _ => NONE)
  else if s = str #"s" then
    (case stack of
      a::rest => parse_cutting_aux f_ns xs (Sat a::rest)
    | _ => NONE)
  else if s = str #"w" then
    (case stack of
      Lit (Pos v)::a::rest => parse_cutting_aux f_ns xs (Weak a [v]::rest)
    | _ => NONE)
  else
    case parse_lit_num f_ns s of
    | SOME (l,f_ns1)=> parse_cutting_aux f_ns1 xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_cutting_aux f_ns [] [c] = SOME (c,f_ns)) ∧
  (parse_cutting_aux f_ns [] _ = NONE)
End

Definition parse_cutting_def:
  parse_cutting f_ns ls = parse_cutting_aux f_ns ls []
End

(*
  EVAL ``parse_cutting (plainVar_nf,()) (toks_fast (strlit "8 2 + 3 + 1 s + 9 2 d + x5 2 * +"))``;
*)

(* Parse a pseudo-Boolean constraint *)
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
  case parse_constraint_LHS line of (rest,lhs) =>
  (case rest of (INL cmp :: INR deg :: rest) =>
    if cmp = strlit">=" then
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

(* A rup hint must be a sequence of numbers *)
Definition strip_rup_hint_def:
  (strip_rup_hint [] acc = SOME (REVERSE acc)) ∧
  (strip_rup_hint (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_rup_hint xs (Num n::acc)
    else NONE
  | INL s =>
    if s = strlit"~" then
      strip_rup_hint xs (0::acc)
    else NONE)
End

Definition parse_rup_hint_def:
  (parse_rup_hint [] = NONE) ∧
  (parse_rup_hint (x::xs) =
    case x of
      INL s =>
      if s = strlit ":" then strip_rup_hint xs [] else NONE
    | _ => NONE)
End

(* Parsing RUP step (header "rup", ";" stripped) *)
Definition parse_rup_def:
  parse_rup f_ns line =
  case parse_constraint_npbc f_ns line of
    SOME (constr,rest,f_ns') =>
      (case parse_rup_hint rest of NONE => NONE
      | SOME ns => SOME(constr,ns,f_ns'))
  | _ => NONE
End

(*
  EVAL ``parse_rup (plainVar_nf,()) (toks_fast (strlit "1 ~x5 1 x26 1 x27 1 x28 1 x29 >= 1 : 6 11 ~"))``
*)

(* TODO below --- rearrange how lsteps are parsed *)
Definition parse_var_def:
  parse_var f_ns v =
  case parse_lit_num f_ns v of
    SOME (Pos n,f_ns) => SOME (n,f_ns)
  | _ => NONE
End

(* Parse a substitution {var -> lit} *)
Definition parse_subst_aux_def:
  (parse_subst_aux f_ns (INL v :: INL arr :: r ::rest) acc =
  if arr = strlit "->" then
    case parse_var f_ns v of
      NONE => ([],[],f_ns)
    | SOME (v,f_ns) =>
    (case r of
        INR r =>
          if r = 0:int then parse_subst_aux f_ns rest ((v,INL F)::acc)
          else if r = 1 then parse_subst_aux f_ns rest ((v,INL T)::acc)
          else ([],[],f_ns)
      | INL r =>
          (case parse_lit_num f_ns r of NONE => ([],[],f_ns)
          | SOME (l, f_ns)  => parse_subst_aux f_ns rest ((v,INR l)::acc)))
  else ([],[],f_ns)) ∧
  (parse_subst_aux f_ns ls acc = (ls, acc,f_ns))
End

Definition parse_subst_def:
  parse_subst f_ns ls =
  let (ls, acc,f_ns) = parse_subst_aux f_ns ls [] in
    (ls, acc, f_ns)
End

Definition parse_red_header_def:
  parse_red_header f_ns line =
  case parse_constraint_npbc f_ns line of
    SOME (constr,rest,f_ns') =>
      (case parse_subst f_ns' rest of (rest,ss,f_ns'') =>
       (case rest of
        [INL term; INL beg] =>
          if term = strlit";" ∧ beg = strlit"begin" then
            SOME (constr,ss,f_ns'')
          else NONE
      | _ => NONE))
  | _ => NONE
End

(* formatting
  rup constraint ; ID1 ID2 ... *)


(* Parse a single line of an lstep,
  Except "Red", which will be handled later *)
Definition parse_lstep_aux_def:
  (parse_lstep_aux f_ns s =
    case s of
    | (r::rs) =>
      if r = INL (strlit "deld") then
        (case strip_numbers rs [] of NONE => NONE
        | SOME n => SOME (INL (Delete n),f_ns))
      else if r = INL (strlit "pol") then
        (case parse_cutting f_ns rs [] of NONE => NONE
        | SOME (p,f_ns') => SOME (INL (Cutting p),f_ns'))
      else if r = INL (strlit "rup") then
        (case parse_rup f_ns rs of NONE => NONE
        | SOME (c,ns,f_ns') => SOME (INL (Rup c ns),f_ns'))
      else if r = INL (strlit "red") then
        case parse_red_header f_ns rs of NONE => NONE
        | SOME (c,s,f_ns') =>
          SOME (INR (c,s),f_ns')
      else if r = INL (strlit "e") then
        (case parse_constraint_npbc f_ns rs of
          NONE => NONE
        | SOME (c,rest,f_ns') =>
          case rest of [INR id] =>
            if id ≥ 0 then
              SOME (INL (Check (Num id) c), f_ns')
            else NONE
          | _ => NONE)
      else if r = INL (strlit "*") then SOME (INL NoOp,f_ns)
      else NONE
    | [] => NONE)
End

Definition check_end_def:
  check_end (h:(mlstring + int) list ) =
  case h of
    [INL e; INR n] =>
    if e = (strlit"end") ∧ n ≥ 0 then SOME (Num n) else NONE
  | _ => NONE
End

Definition is_empty_def:
  is_empty v ⇔ v = []
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
      if ¬(is_empty s) then NONE
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
      if ¬(is_empty s) then NONE
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

Definition check_end_opt_def:
  check_end_opt (h:(mlstring + int) list ) =
  case h of
    [INL e; INR n] =>
    if e = (strlit"end") ∧ n ≥ 0 then SOME (SOME (Num n)) else NONE
  | [INL e] =>
    if e = (strlit"end") then SOME NONE else NONE
  | _ => NONE
End

Definition parse_red_body_def:
  (parse_red_body (h:(mlstring + int) list ) =
    case check_end_opt h of
      NONE =>
      (case parse_proofgoal h of
        SOME ind => SOME (INR ind)
      | NONE => NONE)
    | SOME res => SOME (INL res))
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
    | SOME (INL res) => SOME (res,REVERSE acc', f_ns', rest)
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
  ∀f_ns ss acc res acc' f_ns' ss'.
  parse_red_aux f_ns ss acc = SOME(res,acc',f_ns',ss') ⇒
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

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 2.0")``);

(* We could check that the number of constraints is correct here *)
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

(* Check special cases whether a Red step can be converted to a Con step *)
Definition reduce_pf_def:
  reduce_pf s pf res =
  if is_empty s then
    case res of NONE => NONE
    | SOME id =>(
      case pf of
      | [(NONE,pf)] => SOME (pf,id)
      | [] => SOME ([],id)
      | _ => NONE)
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
      (
        case parse_red_aux f_ns' ss [] of
          NONE => NONE
        | SOME (res, pf,f_ns'',rest) =>
          case reduce_pf s pf res of
            NONE => SOME (INR (Red c s pf res),f_ns'',rest)
          | SOME (pf,id) =>
            SOME (INR (Lstep (Con c pf id)),f_ns'',rest)
      ))
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

(* parse a regular proof block with an extra "proof" and "end" *)
Definition parse_proof_block_def:
  parse_proof_block ss =
  case ss of [] => NONE
  | h::ss =>
  if h = [INL(strlit"proof")] then
    case parse_red_aux (hashString_nf,()) ss [] of
    | SOME (NONE,pf,_,rest) =>
      (case rest of
        x::rest =>
        if x = [INL(strlit "end")]
        then
          SOME (pf,rest)
        else NONE
      | _ => NONE)
    | _ => NONE
  else NONE
End

Definition parse_trans_aux_def:
  parse_trans_aux h v f e =
    if
       h = [INL (strlit"transitivity")] ∧
       v = [INL (strlit"vars")] ∧
       e = [INL (strlit"end")]
    then
      case parse_vars_line (strlit "fresh_right") f of NONE => NONE
      | SOME ws => SOME ws
    else NONE
End

Definition parse_trans_block_def:
  parse_trans_block ss =
  case ss of
    h::v::f::e::ss =>
    (case parse_trans_aux h v f e of NONE => NONE
    | SOME ws =>
      case parse_proof_block ss of NONE => NONE
      | SOME (pf, ss) =>
        SOME (ws,pf,ss))
  | _ => NONE
End

Definition parse_refl_block_def:
  parse_refl_block ss =
  case ss of
    h::ss =>
    if h = [INL (strlit"reflexivity")] then
      parse_proof_block ss
    else NONE
  | _ => NONE
End

Definition parse_trans_refl_block_def:
  parse_trans_refl_block ss =
  case parse_trans_block ss of NONE => NONE
  | SOME (ws,pft,ss) =>
  case parse_refl_block ss of NONE => NONE
  | SOME(pfr,ss) => SOME (ws, pfr, pft, ss)
End

Definition parse_pre_order_def:
  parse_pre_order ss =
  case parse_vars_block ss of NONE => NONE
  | SOME ((us,vs), ss) =>
  case parse_def_block ss of NONE => NONE
  | SOME (f, ss) =>
  case parse_trans_refl_block ss of NONE => NONE
  | SOME (ws, pfr, pft, ss) =>
  case ss of [] => NONE
  | h::ss =>
    if h = [INL (strlit"end")] then
      SOME ((f,us,vs),ws,pfr,pft,ss)
    else NONE
End

(*
EVAL ``
parse_pre_order (MAP toks [
strlit" vars";
strlit"  left u1";
strlit"  right v1";
strlit"  aux";
strlit"end";
strlit" def";
strlit"   >= 1048575 ;";
strlit"end";
strlit" transitivity";
strlit"  vars";
strlit"   fresh_right w1";
strlit"end";
strlit"  proof";
strlit"* prove provided by user";
strlit"proofgoal #1";
strlit"pol 1 2 + 3 +";
strlit"end 4";
strlit"end";
strlit"end";
strlit" reflexivity";
strlit"  proof";
strlit"   proofgoal #1";
strlit"   end 5";
strlit"  end";
strlit" end";
strlit"end";
])``
*)

(* Partially parsed information *)
Datatype:
  par =
  | Done cstep
  | Dompar npbc subst_raw
  | StoreOrderpar mlstring
  | CheckedDeletepar num subst_raw
  | ChangeObjpar bool ((int # num) list # int)
  | ChangePrespar bool num npbc
End

Definition parse_load_order_def:
  (parse_load_order f_ns [] = SOME (Done UnloadOrder,f_ns)) ∧
  (parse_load_order f_ns (INL r::rs) =
    case parse_vars_line_aux f_ns rs of
      NONE => NONE
    | SOME (ws,f_ns') => SOME (Done (LoadOrder r ws),f_ns')) ∧
  (parse_load_order f_ns _ = NONE)
End

Definition parse_delc_header_def:
  parse_delc_header f_ns line =
  case line of
    INR id::INL term::rest =>
    if term = str #";" ∧ id ≥ 0 then
      (case parse_subst f_ns rest of (rest,ss,f_ns') =>
       (case rest of
        [INL term; INL beg] =>
          if term = strlit";" ∧ beg = strlit"begin" then
            SOME (Num id,ss,f_ns')
          else NONE
      | _ => NONE))
    else NONE
  | _ => NONE
End

Definition insert_lit_def:
  (insert_lit (Pos v) f = (v,T)::f) ∧
  (insert_lit (Neg v) f = (v,F)::f)
End

Definition parse_assg_def:
  (parse_assg f_ns [] acc = SOME (acc,NONE,f_ns)) ∧
  (parse_assg f_ns (INL s::ss) acc =
    case parse_lit_num f_ns s of
      NONE =>
        if s = strlit":" then
          (case ss of [INR i] => SOME (acc,SOME i,f_ns)
          | _ => NONE)
        else NONE
    | SOME (l,f_ns') => parse_assg f_ns' ss (insert_lit l acc)) ∧
  (parse_assg f_ns _ acc = NONE)
End

Definition parse_obj_term_npbc_def:
  parse_obj_term_npbc f_ns rest =
  case parse_obj_term rest of NONE => NONE
  | SOME (f,c) =>
    (case map_f_ns f_ns f of NONE => NONE
     | SOME (f',f_ns') =>
      case normalise_obj (SOME (f',c)) of NONE => NONE
      | SOME fc' => SOME (fc', f_ns'))
End

Definition strip_obju_end_def:
  (strip_obju_end [] acc = NONE) ∧
  (strip_obju_end [x] acc =
    if x = INL(strlit "begin")
    then
      SOME (REVERSE acc)
    else NONE) ∧
  (strip_obju_end (x::xs) acc =
    strip_obju_end xs (x::acc))
End

(* objective update *)
Definition parse_b_obj_term_npbc_def:
  (parse_b_obj_term_npbc f_ns rest =
   case strip_obju_end rest [] of NONE => NONE
  | SOME [] => NONE
  | SOME (r::rs) =>
  case parse_obj_term_npbc f_ns rs of NONE => NONE
  | SOME res =>
    if r = INL (strlit "new") then SOME (T,res)
    else if r = INL (strlit"diff") then SOME (F,res)
    else NONE)
End

Definition parse_strengthen_def:
  (parse_strengthen f_ns [INL b] =
    if b = strlit"on" then SOME (Done (StrengthenToCore T), f_ns)
    else if b = strlit "off" then SOME (Done (StrengthenToCore F), f_ns)
    else NONE) ∧
  (parse_strengthen f_ns _ = NONE)
End

Definition parse_preserve_def:
  (parse_preserve f_ns (INL c::cs) =
    case parse_var f_ns c of
      NONE => NONE
    | SOME (x,f_ns') =>
    (case parse_constraint_npbc f_ns' cs of
      SOME (constr,rest,f_ns'') =>
        (case rest of
          [INL beg] =>
            if beg = strlit"begin" then
              SOME (x,constr,f_ns'')
            else NONE
        | _ => NONE)
      | NONE => NONE)) ∧
  (parse_preserve f_ns _ = NONE)
End

(* Parse the first line of a cstep, sstep supported differently *)
Definition parse_cstep_head_def:
  parse_cstep_head f_ns s =
  case s of [] => NONE
  | (r::rs) =>
    if r = INL (strlit "load_order") then
      parse_load_order f_ns rs
    else if r = INL (strlit "strengthening_to_core") then
      parse_strengthen f_ns rs
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
      case parse_delc_header f_ns rs of
      | SOME (n,s,f_ns') =>
        SOME (CheckedDeletepar n s,f_ns')
      | NONE =>
        (case strip_numbers rs [] of NONE => NONE
        | SOME n => SOME (Done (UncheckedDelete n),f_ns))
    else if r = INL (strlit "preserve_add") ∨
            r = INL (strlit "preserve_remove") then
      case parse_preserve f_ns rs of NONE => NONE
      | SOME (x, c, f_ns') =>
        let b = (r = INL(strlit "preserve_add")) in
          SOME (ChangePrespar b x c,f_ns')
    else if r = INL (strlit "soli") ∨ r = INL (strlit "sol") then
      case parse_assg f_ns rs [] of NONE => NONE
      | SOME (assg,ov,f_ns') =>
        let b = (r = INL( strlit "soli")) in
          SOME (Done (Obj assg b ov),f_ns')
    else if r = INL (strlit"obju") then
      (case parse_b_obj_term_npbc f_ns rs of NONE => NONE
      | SOME (b,f',f_ns') =>
        SOME (ChangeObjpar b f', f_ns'))
    else if r = INL (strlit "eobj") then
      (case parse_obj_term_npbc f_ns rs of NONE => NONE
      | SOME (f',f_ns') => SOME (Done (CheckObj f'), f_ns'))
    else if r = INL (strlit "pre_order") then
      case rs of [INL n] => SOME (StoreOrderpar n, f_ns)
      | _ => NONE
    else NONE
End

Definition parse_cstep_def:
  (parse_cstep f_ns ss =
    case parse_sstep f_ns ss of
      NONE => NONE
    | SOME (INR sstep, f_ns',rest) =>
      SOME (INR (Sstep sstep), f_ns', rest)
    | SOME (INL s,f_ns',rest) =>
      case parse_cstep_head f_ns' s of
        NONE => SOME (INL s,f_ns',rest)
      | SOME (Done cstep,f_ns'') => SOME (INR cstep, f_ns'', rest)
      | SOME (Dompar c s,f_ns'') =>
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          SOME (INR (Dom c s pf res), f_ns'', rest))
      | SOME (CheckedDeletepar n s, f_ns'') =>
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          SOME (INR (CheckedDelete n s pf res), f_ns'', rest))
      | SOME (StoreOrderpar name, f_ns'') =>
        (case parse_pre_order rest of NONE => NONE
        | SOME (spo,ws,pfr,pft,rest) =>
          SOME (INR (StoreOrder name spo ws pfr pft), f_ns'',rest))
      | SOME (ChangeObjpar b f, f_ns'') =>
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          case res of NONE =>
            SOME (INR (ChangeObj b f pf), f_ns'', rest)
          | _ => NONE
        )
      | SOME (ChangePrespar b x c, f_ns'') =>
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          case res of NONE =>
            SOME (INR (ChangePres b x c pf), f_ns'', rest)
          | _ => NONE
        )
  )
End

(* parse a hconcl *)
Definition parse_unsat_def:
  parse_unsat rest =
  case rest of
    [INL s; INR n] =>
    if s = strlit":" ∧ n ≥ 0 then SOME (Num n) else NONE
  | _ => NONE
End

Definition parse_sat_def:
  parse_sat f_ns rest =
  case rest of
    INL s::rest =>
    if s = strlit":" then
      OPTION_MAP (SOME o FST) (parse_assg f_ns rest [])
    else NONE
  | [] => SOME NONE
  | _ => NONE
End

(* Parse a number or infinity *)
Definition parse_int_inf_def:
  parse_int_inf l =
  case l of INR n => SOME (SOME n)
  | INL s => if s = strlit "INF" then SOME NONE else NONE
End

(* lb : id ub [: optional assignment] *)
Definition parse_lb_def:
  parse_lb s =
  case s of
    lb :: INL s :: INR n :: rest =>
    if s = strlit":" ∧ n ≥ 0 then
      case parse_int_inf lb of NONE => NONE
      | SOME lb => SOME ((lb,Num n), rest)
    else NONE
  | _ => NONE
End

Definition parse_ub_def:
  parse_ub f_ns s =
  case s of
    ub :: rest =>
      (case parse_int_inf ub of NONE => NONE
      | SOME ub =>
        (case rest of [] => SOME(ub, NONE)
        | INL s::rest =>
          if s = strlit":" then
            (case parse_assg f_ns rest [] of NONE => NONE
            | SOME (a,f_ns') => SOME(ub,SOME a))
          else NONE
        | _ => NONE))
    | _ => NONE
End

(* parse hints for OBound *)
Definition parse_bounds_def:
  parse_bounds f_ns rest =
  case parse_lb rest of NONE => NONE
  | SOME ((lb,n),rest') =>
    (case parse_ub f_ns rest' of NONE => NONE
    | SOME (ub,a) => SOME (lb,ub,n,a))
End

Definition parse_concl_def:
  parse_concl f_ns s =
  case s of
  x::y::rest =>
  if x = INL (strlit "conclusion") then
    if y = INL (strlit "NONE") ∧ rest = [] then SOME HNoConcl
    else if y = INL (strlit "UNSAT") then
      OPTION_MAP HDUnsat (parse_unsat rest)
    else if y = INL (strlit "SAT") then
      OPTION_MAP HDSat (parse_sat f_ns rest)
    else if y = INL (strlit"BOUNDS") then
      case parse_bounds f_ns rest of NONE => NONE
      | SOME (lb,ub,n,a) => SOME (HOBounds lb ub n a)
    else NONE
  else NONE
  | _ => NONE
End

(* Parse a PBC output line *)
Definition parse_output_def:
  parse_output s =
  case s of
    [x;y] =>
    if x = INL(strlit"output") ∧ y = INL (strlit "NONE")
    then SOME NoOutput
    else NONE
  | [x;y;z] =>
    if x = INL(strlit"output") ∧ z = INL (strlit "FILE")
    then (
      if y = INL(strlit"DERIVABLE") then SOME Derivable
      else if y = INL(strlit"EQUISATISFIABLE") then SOME Equisatisfiable
      else if y = INL(strlit"EQUIOPTIMAL") then SOME Equioptimal
      else if y = INL(strlit"EQUISOLVABLE") then SOME Equisolvable
      else NONE)
    else NONE
  | _ => NONE
End

(* Parse a list of strings in pbf format, not used *)
Theorem parse_lsteps_aux_length:
  ∀f_ns ss acc a b c ss'.
  parse_lsteps_aux f_ns ss acc = SOME(a,b,c,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rw[parse_lsteps_aux_def]>>
  gvs[AllCaseEqs()]
QED

Theorem parse_red_aux_length:
  ∀f_ns ss acc a b c ss'.
  parse_red_aux f_ns ss acc = SOME(a,b,c,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac parse_red_aux_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_red_aux_def]>>
  rw[AllCaseEqs()]
  >-
    metis_tac[parse_lsteps_aux_length]>>
  first_x_assum drule_all>>
  imp_res_tac parse_lsteps_aux_length>>
  simp[]
QED

Theorem parse_sstep_length:
  parse_sstep f_ns ss = SOME(a,b,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Cases_on`ss`>>rw[parse_sstep_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_red_aux_length>>
  simp[]
QED

(*
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
  WF_REL_TAC `measure (LENGTH o FST o SND)`>>
  rw[parse_cstep_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_sstep_length>>simp[]
  >-
    (drule parse_red_aux_length>>simp[])
  >-
  >-
    (drule parse_red_aux_length>>simp[])
  >-
    (drule parse_red_aux_length>>simp[])
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
*)

val _ = export_theory();
