(*
  Parse and print for pbc, npbc_check
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
  EVAL ``strip_term_line (toks (strlit "foo bar aaa;"))``
  EVAL ``strip_term_line (toks (strlit "foo bar bbb ;"))``
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
  EVAL ``parse_annot_constraint (toks (strlit "@aaa 2 ~x1 1 ~x3 >= 1;"))``;
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

(* parse objective term in pbc ... (; stripped) *)
Definition parse_obj_term_def:
  parse_obj_term xs =
  case parse_constraint_LHS xs of (rest,obj) =>
  case rest of
    [] => SOME (obj,0:int)
  | [INR c] => SOME (obj,c:int)
  | _ => NONE
End

(* parse objective line in PBF *)
Definition parse_obj_def:
  (parse_obj [] = NONE) ∧
  (parse_obj (x::xs) =
    if x = INL (strlit "min:") then
      OPTION_BIND (strip_term_line xs) parse_obj_term
    else NONE
  )
End

(*
  EVAL``parse_obj (toks (strlit"min: 1 ~x199 1 x2 ~5 ;"))``
  EVAL``parse_obj (toks (strlit"min: 1 ~x199 1 x2 ~5;"))``
  EVAL``parse_obj (toks (strlit"min: 1 ~x199 1 x2 ;"))``
  EVAL``parse_obj (toks (strlit"min: 1 ~x199 1 x2;"))``
  EVAL``parse_obj (toks (strlit"min: 1 ~x199 1 x2 5;"))``
*)

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
  (c = #"-" ∨ c = #"+" ∨ c = #"~")
End

(* parse as integers, except if it ends with ; *)
Definition int_start_def:
  int_start s =
  if strsub s (strlen s - 1) = #";" then F
  else
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

(* Unused, but useful for testing *)
Definition plainVar_nf_def:
  plainVar_nf s (u:unit) =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n => SOME (n,())
  else
    NONE
End

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
Definition strip_rup_hint_aux_def:
  (strip_rup_hint_aux [] acc = SOME (REVERSE acc)) ∧
  (strip_rup_hint_aux (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_rup_hint_aux xs (Num n::acc)
    else NONE
  | INL s =>
    if s = strlit"~" then
      strip_rup_hint_aux xs (0::acc)
    else NONE)
End

Definition strip_rup_hint_def:
  strip_rup_hint xs = strip_rup_hint_aux xs []
End

Definition parse_rup_hint_def:
  (parse_rup_hint [] = NONE) ∧
  (parse_rup_hint (x::xs) =
    case x of
      INL s =>
      if s = strlit ":" then strip_rup_hint xs else NONE
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
  EVAL ``parse_rup (plainVar_nf,()) (toks_fast (strlit "1 ~x5 1 x26 +1 x27 1 x28 1 x29 >= 1 : 6 11 ~"))``
*)

Definition start_subproof_def:
  start_subproof rest ⇔
  rest = [INL (strlit ":"); INL (strlit"subproof")]
End

Definition colon_id_opt_def:
  colon_id_opt rest =
  case rest of
    [INL term; INR id] =>
    if term = strlit":" ∧ id ≥ 0 then SOME (SOME (Num id))
    else NONE
  | [] => SOME NONE
  | _ => NONE
End

Definition parse_pbc_header_def:
  parse_pbc_header f_ns line =
  case parse_constraint_npbc f_ns line of
    SOME (constr,rest,f_ns') =>
      if start_subproof rest
      then SOME (constr,f_ns')
      else NONE
  | _ => NONE
End

(*
  EVAL ``parse_pbc_header (plainVar_nf,()) (toks_fast (strlit "3 x1 -3 x2 2 x3 >= 5 : subproof"))``
*)

Definition strip_numbers_aux_def:
  (strip_numbers_aux [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers_aux (x::xs) acc =
  case x of INR n =>
    if n ≥ 0 then
      strip_numbers_aux xs (Num n::acc)
    else NONE
  | INL _ => NONE)
End

Definition strip_numbers_def:
  strip_numbers xs = strip_numbers_aux xs []
End

(* Parse a single line of lstep including ; terminator
  pbc does not end with terminator.
  NONE -> failed to parse
  INL c -> beginning of a proof-by-contradiction
  INR s -> lstep *)
Definition parse_lstep_aux_def:
  (parse_lstep_aux f_ns s =
    case s of [] => NONE
    | (r::rs) =>
      if r = INL (strlit "pbc") then
        case parse_pbc_header f_ns rs of NONE => NONE
        | SOME (c,f_ns') =>
          SOME (INR c,f_ns')
      else
      case strip_term_line rs of NONE => NONE
      | SOME rs =>
      if r = INL (strlit "deld") then
        (case strip_numbers rs of NONE => NONE
        | SOME n => SOME (INL (Delete n),f_ns))
      else if r = INL (strlit "pol") then
        (case parse_cutting f_ns rs of NONE => NONE
        | SOME (p,f_ns') => SOME (INL (Cutting p),f_ns'))
      else if r = INL (strlit "rup") then
        (case parse_rup f_ns rs of NONE => NONE
        | SOME (c,ns,f_ns') => SOME (INL (Rup c ns),f_ns'))
      else if r = INL (strlit "e") then
        (case parse_constraint_npbc f_ns rs of
          NONE => NONE
        | SOME (c,rest,f_ns') =>
          case colon_id_opt rest of
          | SOME (SOME res) =>
            SOME (INL (Check res c), f_ns')
          | _ => NONE)
      else if r = INL (strlit "*") then SOME (INL NoOp,f_ns)
      else NONE)
End

(* qed mark : ID ; --- ID is optional *)
Definition check_mark_qed_id_opt_def:
  check_mark_qed_id_opt mark (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => NONE
  | SOME rs =>
  case rs of
    INL q :: rest =>
    if q = strlit"qed" then
      case rest of
        s :: rest' =>
        if s = mark
        then colon_id_opt rest'
        else colon_id_opt rest
      | [] => SOME NONE
    else NONE
  | _ => NONE
End

(* qed mark : ID ; *)
Definition check_mark_qed_id_def:
  check_mark_qed_id mark (h:(mlstring + int) list ) =
  case check_mark_qed_id_opt mark h of
    SOME (SOME res) => SOME res
  | _ => NONE
End

(*
EVAL `` check_mark_qed_id (INL (strlit"pbc")) (toks_fast (strlit"qed pbc : 4 ;"))``

EVAL `` check_mark_qed_id_opt (INL (strlit"pbc")) (toks_fast (strlit"qed pbc;"))``

EVAL `` check_mark_qed_id_opt (INL (strlit"pbc")) (toks_fast (strlit"qed;"))``
*)

(* Parsing lsteps in a subproof until parsing
  fails and return the failing line
  (note: this expects a failing line, i.e.,
  in an lstep parse, it should match everything nested
  pbc step except the outermost one ) *)
Definition parse_lsteps_aux_def:
  (parse_lsteps_aux f_ns
    ([]:(mlstring + int) list list)
    (acc:lstep list) = NONE) ∧
  (parse_lsteps_aux f_ns (s::ss) acc =
    case parse_lstep_aux f_ns s of
    | NONE => SOME (REVERSE acc, f_ns, s, ss)
    | SOME (INL step, f_ns') =>
      parse_lsteps_aux f_ns' ss (step::acc)
    | SOME (INR c, f_ns') =>
      case parse_lsteps_aux f_ns' ss [] of
        NONE => NONE
      | SOME (pf,f_ns'',s,rest) =>
      if LENGTH rest < LENGTH ss then
        case check_mark_qed_id (INL (strlit"pbc")) s of
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
    | SOME (INR c, f_ns') =>
        case parse_lsteps_aux f_ns' ss [] of
          NONE => NONE
        | SOME (pf,f_ns'',s,rest) =>
          case check_mark_qed_id (INL (strlit"pbc")) s of
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

Definition parse_lsteps_def:
  parse_lsteps f_ns ss = parse_lsteps_aux f_ns ss []
End

(*
  EVAL`` parse_lsteps (plainVar_nf,())
  (MAP toks_fast [
  strlit "pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof";
  strlit "pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof";
  strlit"pol 1 2 +;";
  strlit"rup >= 1 : 1234;";
  strlit"qed pbc : 4;";
  strlit"qed pbc : 4;";
  strlit"qed pbc : 4;";
  ])``
*)

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
  (parse_subst f_ns [] = NONE) ∧
  (parse_subst f_ns (x::xs) =
    case x of
      INL s =>
      if s = strlit ":" then
      SOME (parse_subst_aux f_ns xs [])
      else NONE
    | _ => NONE)
End

(* A strengthening rule header *)
Definition parse_red_header_def:
  parse_red_header f_ns line =
  case parse_constraint_npbc f_ns line of
    SOME (constr,rest,f_ns') =>
      (case parse_subst f_ns' rest of
        NONE => NONE
      | SOME (rest,ss,f_ns'') =>
        if start_subproof rest
        then SOME (constr,ss,f_ns'')
        else NONE)
  | _ => NONE
End

(* parse a subproof and returns the next failing line
  Type subproof = ``:((((num + num) # num) option, (lstep list)) alist)``;
*)
Definition mk_acc_def:
  mk_acc pf acc = if pf = [] then acc else (NONE,pf)::acc
End

(* We map #n to n-1 internally *)
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

Definition mk_proofgoal_mark_def:
  mk_proofgoal_mark (ind : num + num) =
  case ind of
    INL n => INR (&n:int)
  | INR n => INL (strlit"#" ^ toString (n+1))
End

Definition parse_subproof_aux_def:
  (parse_subproof_aux f_ns ss (acc:subproof) =
  case parse_lsteps f_ns ss of
    NONE => NONE
  | SOME (pf,f_ns',s,rest) =>
    let acc = mk_acc pf acc in
    case parse_proofgoal s of
      NONE => SOME (REVERSE acc, f_ns', s, rest)
    | SOME ind =>
      (case parse_lsteps f_ns' rest of
        NONE => NONE
      | SOME (pf,f_ns'',s,rest) =>
        case check_mark_qed_id (mk_proofgoal_mark ind) s of
          NONE => NONE
        | SOME id =>
        parse_subproof_aux f_ns'' rest ((SOME (ind,id),pf)::acc)
       )
  )
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’
  \\ rw[] \\ fs[parse_lsteps_def]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
End

Definition parse_subproof_def:
  parse_subproof f_ns ss =
  parse_subproof_aux f_ns ss []
End

(*
  EVAL`` parse_subproof (plainVar_nf,())
  (MAP toks_fast [
  strlit"pol 12 11 + 5 + 6 +;";
  strlit"proofgoal #1";
  strlit"pol 12 11 + 5 + 6 +;";
  strlit "pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof";
  strlit"pol 1 2 +;";
  strlit "pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof";
  strlit"pol 1 2 +;";
  strlit"rup >= 1 : 1234;";
  strlit"qed pbc : 4;";
  strlit"rup >= 1 : 1234;";
  strlit"qed pbc : 4;";
  strlit"pol 14 x6 +;";
  strlit"qed #1 : 15;";
  strlit"pol 12 11 + 5 + 6 +;";
  strlit "pbc +3 x1 +3 x2 +2 x3 >= 5 : subproof";
  strlit"pol 1 2 +;";
  strlit"rup >= 1 : 1234;";
  strlit"qed pbc : 4;";
  strlit"proofgoal 1";
  strlit"pol 16 2 +;";
  strlit"qed 1 : 17;";
  strlit"qed;";
  ])``
*)

(* leq -> 0, geq -> 1 *)
Definition parse_scopetext_def:
  parse_scopetext line =
  case line of
    [INL s] =>
    if s = strlit"leq" then SOME 0
    else if s = strlit"geq" then SOME 1
    else NONE
  | _ => NONE
End

Definition parse_scopehead_def:
  parse_scopehead (h:(mlstring + int) list ) =
  case h of
    INL e::rs =>
    (if e = (strlit"scope") then
      parse_scopetext rs
    else NONE)
  | _ => NONE
End

Definition mk_scope_mark_def:
  mk_scope_mark sc =
  if sc = 0n then [INL (strlit"scope"); INL (strlit "leq")]
  else [INL (strlit"scope"); INL (strlit "geq")]
End

Definition check_end_def:
  check_end marks (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => F
  | SOME rs =>
  case rs of
    INL q :: rest =>
    q = strlit"end" ∧
      (rest = [] ∨
      rest = marks)
  | _ => F
End

Theorem parse_subproof_aux_LENGTH:
  ∀f_ns ss acc res acc' f_ns' ss'.
  parse_subproof_aux f_ns ss acc = SOME(res,acc',f_ns',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac (fetch "-" "parse_subproof_aux_ind")>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_subproof_aux_def]>>
  every_case_tac>>fs[parse_lsteps_def]>>
  rw[]>>imp_res_tac parse_lsteps_aux_LENGTH>>
  fs[]
QED

(* parse a scope and returns the next failing line
  Type scope = ``:(num option, subproof) alist``;
*)
Definition parse_scope_aux_def:
  (parse_scope_aux f_ns ss (acc:(num option, subproof) alist) =
  case parse_subproof f_ns ss of
    NONE => NONE
  | SOME (pf,f_ns',s,rest) =>
    let acc = mk_acc pf acc in
    case parse_scopehead s of
      NONE => SOME (REVERSE acc, f_ns', s, rest)
    | SOME ind =>
      (case parse_subproof f_ns' rest of
        NONE => NONE
      | SOME (pf,f_ns'',s,rest) =>
        if check_end (mk_scope_mark ind) s
        then
          parse_scope_aux f_ns'' rest ((SOME ind,pf)::acc)
        else NONE
       )
  )
Termination
  WF_REL_TAC ‘measure (LENGTH o FST o SND)’
  \\ rw[parse_subproof_def]>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  fs[]
End

Definition parse_scope_def:
  parse_scope f_ns ss =
  parse_scope_aux f_ns ss []
End

Definition parse_red_header_red_def:
  parse_red_header_red f_ns line =
  case line of [] => NONE
  | x::line =>
  if x = INL (strlit "red")
  then parse_red_header f_ns line
  else NONE
End

(* Parse 1 sstep, until an unparseable line is reached. *)
Definition parse_sstep_def:
  (parse_sstep f_ns [] = NONE) ∧
  (parse_sstep f_ns (s::ss) =
    case parse_lstep_aux f_ns s of
      NONE =>
      (case parse_red_header_red f_ns s of
        NONE => SOME (INL s,f_ns,ss)
      | SOME (c,s,f_ns') =>
        case parse_scope f_ns' ss of
          NONE => NONE
        | SOME (pf, f_ns'', h, rest) =>
          case check_mark_qed_id_opt (INL (strlit"red")) h of
            NONE => NONE
          | SOME idopt =>
            SOME (INR (Red c s pf idopt),f_ns'',rest)
      )
    | SOME (INL step,f_ns') =>
        SOME (INR (Lstep step),f_ns',ss)
    | SOME (INR c, f_ns') =>
      (case parse_lsteps_aux f_ns' ss [] of
        NONE => NONE
      | SOME (pf,f_ns'',s,rest) =>
        case check_mark_qed_id (INL (strlit"pbc")) s of
          NONE => NONE
        | SOME id =>
        SOME (INR (Lstep (Con c pf id)),f_ns'',rest)))
End

(*
  EVAL`` parse_sstep (plainVar_nf,())
  (MAP toks_fast
  [strlit"red 1 x1 >= 1 : x1 -> x3 x3 -> x5 x5 -> x1 x2 -> x4 x4 -> x6 x6 -> x2 : subproof";
  strlit"proofgoal #1";
  strlit"pol 12 11 + 5 + 6 +;";
  strlit"pol 13 4 +;";
  strlit"pol 14 x6 +;";
  strlit"qed : 15;";
  strlit"proofgoal 1";
  strlit"pol 16 2 +;";
  strlit"qed : 17;";
  strlit"qed;";])``
*)

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 3.0")``);

(* TODO: We should check that the number of constraints is correct here *)
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

(* def_order parsing. We parse the sections in order.
  First, the vars block
*)
Definition hashString_nf_def:
  hashString_nf s t = SOME(hashString s,t)
End

Definition parse_def_order_head_def:
  parse_preorder_head s =
  case s of
    [x;INL name] =>
      if x = INL (strlit"def_order") then
        SOME name
      else NONE
  | _ => NONE
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
      case strip_term_line rest of NONE => NONE
      | SOME rest =>
      OPTION_MAP FST
        (parse_vars_line_aux (hashString_nf,()) rest)
    else NONE
  | _ => NONE
End

Definition parse_vars_aux_def:
  parse_vars_aux v l r a =
    if v = [INL (strlit"vars")] then
      case parse_vars_line (strlit "left") l of NONE => NONE
      | SOME us =>
      case parse_vars_line (strlit "right") r of NONE => NONE
      | SOME vs =>
      case a of NONE => SOME (us,vs,[])
      | SOME a =>
      case parse_vars_line (strlit "aux") a of NONE => NONE
      | SOME as => SOME (us,vs,as)
  else NONE
End

Definition parse_vars_block_def:
  parse_vars_block ss =
  case ss of
    v::l::r::ae::rest =>
    if check_end [INL (strlit"vars")] ae
    then
      OPTION_MAP (λres. (res,rest))
        (parse_vars_aux v l r NONE)
    else
      (case rest of [] => NONE
      | e::rest =>
      if check_end [INL (strlit"vars")] e
      then
        OPTION_MAP (λres. (res,rest))
          (parse_vars_aux v l r (SOME ae))
      else NONE)
  | _ => NONE
End

(*
EVAL ``parse_vars_block
  (MAP toks_fast
  [strlit"vars";
  strlit"  left u1 u2 u3 u4 u5 u6 u7 u8 u9 u10;";
  strlit"  right v1 v2 v3 v4 v5 v6 v7 v8 v9 v10;";
  strlit"  aux $a1 $a2 $a3 $a4 $a5 $a6 $a7 $a8 $a9 $d1 $d2 $d3 $d4 $d5 $d6 $d7 $d8 $d9 $d10 ;";
  strlit"end;";])``

EVAL ``parse_vars_block
  (MAP toks_fast
  [strlit"vars";
  strlit"  left u1 u2 u3 u4 u5 u6 u7 u8 u9 u10;";
  strlit"  right v1 v2 v3 v4 v5 v6 v7 v8 v9 v10;";
  strlit"end;";])``
*)

Theorem parse_scope_aux_LENGTH:
  ∀f_ns ss acc res acc' f_ns' ss'.
  parse_scope_aux f_ns ss acc = SOME(res,acc',f_ns',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  ho_match_mp_tac (fetch "-" "parse_scope_aux_ind")>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_scope_aux_def]>>
  every_case_tac>>
  fs[parse_subproof_def]>>
  rw[]>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  fs[]
QED

Theorem parse_sstep_LENGTH:
  parse_sstep f_ns ss = SOME(a,b,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Cases_on`ss`>>rw[parse_sstep_def]>>
  gvs[AllCaseEqs(),parse_scope_def]
  >- (
    imp_res_tac parse_scope_aux_LENGTH>>
    simp[])>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  simp[]
QED

(* parse specification block *)
Definition parse_spec_aux_def:
  (parse_spec_aux ss acc =
     case parse_sstep (hashString_nf,()) ss of
      SOME (INR (Red c s pf idopt),_,ss) =>
      parse_spec_aux ss ((c,s,pf,idopt)::acc)
    | SOME (INL s,_,ss) =>
      if check_end [INL (strlit"spec")] s then
        SOME(REVERSE acc,ss)
      else NONE)
Termination
  WF_REL_TAC ‘measure (LENGTH o FST)’
  \\ rw[]
  \\ imp_res_tac parse_sstep_LENGTH>>
  fs[]
End

(* Return an optional line since spec block is optional,
  but following blocks are mandatory *)
Definition parse_spec_block_def:
  parse_spec_block ss =
  case ss of
    h::rest =>
    if h = [INL (strlit"spec")] then
      case parse_spec_aux rest [] of
        NONE => NONE
      | SOME (spec,ss) =>
        SOME (NONE, spec, ss)
    else
      SOME (SOME h, [], rest)
  | _ => NONE
End

(*
  -- handle spec parsing if it exists
  EVAL``parse_spec_block
  (MAP toks_fast ([strlit"spec";
  strlit"red 1 u1 1 ~v1 1 ~$a1 >= 1 : $a1 -> 0 : subproof";
  strlit"qed;";
  strlit"red 1 u1 1 ~v1 1 ~$a1 >= 1 : $a1 -> 0 : subproof";
  strlit"qed;";
  strlit"end;";
  ]))``

  -- if no spec block, then the next block is the definition block
  EVAL``parse_spec_block
  (MAP toks_fast ([strlit"def";
  strlit"FOO";
  ]))``
*)

(* parse definition block of constraints *)
Definition parse_def_aux_def:
  (parse_def_aux [] acc = NONE) ∧
  (parse_def_aux (s::ss) acc =
    if check_end [INL (strlit"def")] s then
      SOME(REVERSE acc,ss)
    else
      case strip_term_line s of NONE => NONE
      | SOME s =>
      case parse_constraint_npbc (hashString_nf,()) s of
        NONE => NONE
      | SOME (c,_) => parse_def_aux ss (c::acc))
End

Definition parse_def_block_def:
  parse_def_block s ss =
  (case s of NONE =>
    (case ss of
      h::rest =>
      if h = [INL (strlit"def")] then
        parse_def_aux rest []
      else NONE
    | _ => NONE)
  | SOME h =>
    if h = [INL (strlit"def")] then
      parse_def_aux ss []
    else NONE)
End

(* -- the def block takes an optional line from the optional spec block
  EVAL``parse_def_block
  NONE
  (MAP toks_fast ([
    strlit"def";
    strlit"1 $d10 >= 1;";
    strlit"end;";]))``

  EVAL``parse_def_block
  (SOME ([INL (strlit"def")]))
  (MAP toks_fast ([
    strlit"1 $d10 >= 1;";
    strlit"end;";]))``
*)

Definition check_qed_def:
  check_qed marks (h:(mlstring + int) list ) =
  case strip_term_line h of NONE => F
  | SOME rs =>
  case rs of
    INL q :: rest =>
    q = strlit"qed" ∧
      (rest = [] ∨
      rest = marks)
  | _ => F
End

(* parse a regular proof block WITHOUT scope and
  with an extra "proof" and "qed" at the end,
  followed by an "end" line *)
Definition parse_proof_block_def:
  parse_proof_block end ss =
  case ss of [] => NONE
  | h::ss =>
  if h = [INL(strlit"proof")] then
    case parse_subproof (hashString_nf,()) ss of
    | SOME (pf,_,s,rest) =>
      if check_qed [INL(strlit"proof")] s
      then
        case rest of [] => NONE
        | (s::rest) =>
          if check_end end s
          then
            SOME (pf,rest)
          else NONE
      else NONE
    | _ => NONE
  else NONE
End

Definition parse_trans_aux_def:
  parse_trans_aux h v f a12 =
    if
       h = [INL (strlit"transitivity")] ∧
       v = [INL (strlit"vars")]
    then
      case parse_vars_line (strlit "fresh_right") f of NONE => NONE
      | SOME ws =>
      case a12 of NONE => SOME (ws,[],[])
      | SOME (a1,a2) =>
        case parse_vars_line (strlit "fresh_aux_1") a1 of
          NONE => NONE
        | SOME bs =>
        case parse_vars_line (strlit "fresh_aux_2") a2 of
          NONE => NONE
        | SOME cs =>
          SOME (ws,bs,cs)
    else NONE
End

Definition parse_trans_block_aux_def:
  parse_trans_block_aux ss =
  case ss of
    h::v::f::ae::rest =>
    if check_end [INL (strlit"vars")] ae
    then
      case parse_trans_aux h v f NONE of
        NONE => NONE
      | SOME vars => SOME (vars,rest)
    else
      (case rest of
      | a2::e::rest =>
        if check_end [INL (strlit"vars")] e
        then
          case parse_trans_aux h v f (SOME (ae,a2)) of
            NONE => NONE
          | SOME vars => SOME (vars,rest)
        else NONE
      | _ => NONE)
  | _ => NONE
End

Definition parse_trans_block_def:
  parse_trans_block ss =
  case parse_trans_block_aux ss of
    NONE => NONE
  | SOME ((ws,bs,cs),rest) =>
  case parse_proof_block [INL (strlit"transitivity")] rest of
    NONE => NONE
  | SOME (pf,ss) =>
    SOME((ws,bs,cs,pf),ss)
End

(*
EVAL``parse_trans_block
  (MAP toks_fast ([
  strlit"transitivity";
  strlit"vars";
  strlit"fresh_right w1 w2 w3;";
  strlit"fresh_aux_1 $b1 $b2 ;";
  strlit"fresh_aux_2 $c1 $c2 ;";
  strlit"end;";
  strlit"proof";
  strlit"pol 120 148 + 222 + 223 + s 241 3 * +;";
  strlit"pol 242 114 + s;";
  strlit"proofgoal #1";
  strlit"pol 243 117 +;";
  strlit"qed : 244;";
  strlit"qed;";
  strlit"end;";]))``

EVAL``parse_trans_block
  (MAP toks_fast ([
  strlit"transitivity";
  strlit"vars";
  strlit"fresh_right w1 w2 w3;";
  strlit"end vars;";
  strlit"proof";
  strlit"pol 120 148 + 222 + 223 + s 241 3 * +;";
  strlit"pol 242 114 + s;";
  strlit"proofgoal #1";
  strlit"pol 243 117 +;";
  strlit"qed #1 : 244;";
  strlit"qed proof;";
  strlit"end transitivity;";]))``
*)

Definition parse_refl_block_def:
  parse_refl_block ss =
  case ss of
    h::ss =>
    if h = [INL (strlit"reflexivity")] then
      parse_proof_block [INL (strlit"reflexivity")] ss
    else NONE
  | _ => NONE
End

Definition parse_trans_refl_block_def:
  parse_trans_refl_block ss =
  case parse_trans_block ss of NONE => NONE
  | SOME (pft,ss) =>
  case parse_refl_block ss of NONE => NONE
  | SOME(pfr,ss) => SOME (pfr, pft, ss)
End

Definition parse_spec_def_block_def:
  parse_spec_def_block ss =
  case parse_spec_block ss of NONE => NONE
  | SOME (sopt,gspec,ss) =>
  case parse_def_block sopt ss of NONE => NONE
  | SOME (f, ss) => SOME (f,gspec,ss)
End

Definition parse_pre_order_def:
  parse_pre_order ss =
  case parse_vars_block ss of NONE => NONE
  | SOME (vars, ss) =>
  case parse_spec_def_block ss of NONE => NONE
  | SOME (f,gspec,ss) =>
  case parse_trans_refl_block ss of NONE => NONE
  | SOME (pfr, pft, ss) =>
  case ss of [] => NONE
  | h::ss =>
    if check_end [INL (strlit"def_order")] h then
      SOME (vars,gspec,f,pfr,pft,ss)
    else NONE
End

(*
  EVAL``parse_pre_order
  (MAP toks_fast ([
  strlit"vars";
  strlit"left u1;";
  strlit"right v1;";
  strlit"aux $a1;";
  strlit"end;";
  strlit"spec";
  strlit"red 1 u1 1 ~v1 1 ~$a1 >= 1 : $a1 -> 0 : subproof";
  strlit"qed;";
  strlit"end;";
  strlit"def";
  strlit"1 $d10 >= 1;";
  strlit"end;";
  strlit"transitivity";
  strlit"vars";
  strlit"fresh_right w1;";
  strlit"fresh_aux_1 $b1;";
  strlit"fresh_aux_2 $c1;";
  strlit"end;";
  strlit"proof";
  strlit"qed proof;";
  strlit"end transitivity;";
  strlit"reflexivity";
  strlit"proof";
  strlit"qed proof;";
  strlit"end reflexivity;";
  strlit"end def_order;";]))``
*)

(* Partially parsed information for csteps *)
Datatype:
  par =
  | Done cstep
  | Dompar npbc subst_raw
  | StoreOrderpar mlstring
  | CheckedDeletepar num subst_raw
  | ChangeObjpar bool ((int # num) list # int)
  | ChangePrespar bool num npbc
End

Definition split_lit_def:
  split_lit l =
  case l of Pos v => (T,v) | Neg v => (F,v)
End

Definition parse_lits_line_aux_def:
  (parse_lits_line_aux f_ns [] = SOME ([],f_ns)) ∧
  (parse_lits_line_aux f_ns (x::xs) =
  case x of
    INL v =>
    (case parse_lit_num f_ns v of
      NONE => NONE
    | SOME (ll,f_ns') =>
      (case parse_lits_line_aux f_ns' xs of NONE => NONE
      | SOME (lls,f_ns'') => SOME (split_lit ll::lls,f_ns'')))
  | _ => NONE)
End

(* load_order over literals (";" stripped) *)
Definition parse_load_order_def:
  (parse_load_order f_ns [] = SOME (Done UnloadOrder,f_ns)) ∧
  (parse_load_order f_ns (INL r::rs) =
    case parse_lits_line_aux f_ns rs of
      NONE => NONE
    | SOME (ws,f_ns') => SOME (Done (LoadOrder r ws),f_ns')) ∧
  (parse_load_order f_ns _ = NONE)
End

(* TODO: strengthening to core mode syntax? *)
Definition parse_strengthen_def:
  (parse_strengthen f_ns [INL b] =
    if b = strlit"on" then SOME (Done (StrengthenToCore T), f_ns)
    else if b = strlit "off" then SOME (Done (StrengthenToCore F), f_ns)
    else NONE) ∧
  (parse_strengthen f_ns _ = NONE)
End

Definition parse_to_core_def:
  (parse_to_core f_ns (INL r::rs) =
    if r = strlit "id"
    then
      case strip_numbers rs of NONE => NONE
      | SOME n => SOME (Done (Transfer n), f_ns)
    else NONE) ∧
  (parse_to_core _ _ = NONE)
End

(* TODO: this should be more unified with split_lit... *)
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

(* TODO: syntax?
  currently: soli l1 ... ln [: value]
  where value is optional but is meant to sanity test the logged value
*)
Definition parse_sol_def:
  (parse_sol f_ns r rs =
  case parse_assg f_ns rs [] of NONE => NONE
  | SOME (assg,ov,f_ns') =>
    let b = (r = INL( strlit "soli")) in
      SOME (Done (Obj assg b ov),f_ns'))
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

(* TODO: syntax? *)
Definition parse_eobj_def:
  parse_eobj f_ns rs =
  case parse_obj_term_npbc f_ns rs of
    NONE => NONE
  | SOME (f',f_ns') => SOME (Done (CheckObj f'), f_ns')
End

(* TODO: syntax for checked deletion *)
Definition parse_delc_header_def:
  parse_delc_header f_ns line =
  case line of
    INR id::rest =>
    if id ≥ 0 then
      (case parse_subst f_ns rest of
        NONE => NONE
      | SOME (rest,ss,f_ns'') =>
        if start_subproof rest
        then SOME (Num id,ss,f_ns'')
        else NONE)
    else NONE
  | _ => NONE
End

Definition strip_obju_end_def:
  (strip_obju_end [] acc = NONE) ∧
  (strip_obju_end [x] acc =
    if x = INL(strlit "subproof")
    then
      SOME (REVERSE acc)
    else NONE) ∧
  (strip_obju_end (x::xs) acc =
    strip_obju_end xs (x::acc))
End

(* TODO: objective update *)
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

(* TODO: preserve *)
Definition parse_preserve_def:
  (parse_preserve f_ns (INL c::cs) =
    case parse_var f_ns c of
      NONE => NONE
    | SOME (x,f_ns') =>
    (case parse_constraint_npbc f_ns' cs of
      SOME (constr,rest,f_ns'') =>
        (case rest of
          [INL beg] =>
            if beg = strlit"subproof" then
              SOME (x,constr,f_ns'')
            else NONE
        | _ => NONE)
      | NONE => NONE)) ∧
  (parse_preserve f_ns _ = NONE)
End

(* Parse the first line of a cstep, sstep supported differently later
  Here we first parse the multi-line, then the single line steps *)
Definition parse_cstep_head_def:
  parse_cstep_head f_ns s =
  case s of [] => NONE
  | (r::rs) =>
    if r = INL (strlit"dom") then
      case parse_red_header f_ns rs of
        SOME (c,s,f_ns') => SOME (Dompar c s,f_ns')
      | _ => NONE
    else if r = INL (strlit "delc") then
      case parse_delc_header f_ns rs of
      | SOME (n,s,f_ns') =>
        SOME (CheckedDeletepar n s,f_ns')
      | NONE =>
        (case OPTION_BIND (strip_term_line rs) strip_numbers of NONE => NONE
        | SOME n => SOME (Done (UncheckedDelete n),f_ns))
    else if r = INL (strlit "def_order") then
      case rs of [INL n] => SOME (StoreOrderpar n, f_ns)
      | _ => NONE
    else if r = INL (strlit"obju") then
      (case parse_b_obj_term_npbc f_ns rs of NONE => NONE
      | SOME (b,f',f_ns') =>
        SOME (ChangeObjpar b f', f_ns'))
    else if r = INL (strlit "preserve_add") ∨
            r = INL (strlit "preserve_remove") then
      case parse_preserve f_ns rs of NONE => NONE
      | SOME (x, c, f_ns') =>
        let b = (r = INL(strlit "preserve_add")) in
          SOME (ChangePrespar b x c,f_ns')
    else
    case strip_term_line rs of NONE => NONE
    | SOME rs =>
    if r = INL (strlit"core") then
      parse_to_core f_ns rs
    else if r = INL (strlit "strengthening_to_core") then
      parse_strengthen f_ns rs
    else if r = INL (strlit "load_order") then
      parse_load_order f_ns rs
    else if r = INL (strlit "soli") ∨ r = INL (strlit "sol") then
      parse_sol f_ns r rs
    else if r = INL (strlit "eobj") then
      parse_eobj f_ns rs
    else NONE
End

(*
EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"dom 1 ~x1 1 x2 >= 1 : x1 -> x2 x2 -> x1 : subproof"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"delc 2 : : subproof"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"delc 1 2 3 4 5;"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"load_order lex10 x1 ~x4 x9 ~x10 ;"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"strengthening_to_core off;"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"core id 1 2 3 4 5;"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"soli ~x1 ~x2 ~x3 ~x4 ~x5 ~x6 x7 ~x8 x9 ~x10 ~x11 x12 : 50;"))``;

EVAL
``parse_cstep_head (plainVar_nf,()) (toks_fast (strlit"eobj 1 x1 -100 ;"))``;

*)

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
        (case parse_scope f_ns'' rest of
          NONE => NONE
        | SOME (pf, f_ns''', h, rest) =>
          case check_mark_qed_id_opt (INL (strlit"dom")) h of
            NONE => NONE
          | SOME idopt =>
            SOME (INR (Dom c s pf idopt),f_ns''',rest))
      | SOME (CheckedDeletepar n s, f_ns'') => NONE
        (* TODO
        (case parse_scope f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          SOME (INR (CheckedDelete n s pf res), f_ns'', rest)) *)
      | SOME (StoreOrderpar name, f_ns'') =>
        (case parse_pre_order rest of NONE => NONE
        | SOME (vars,gspec,f,pfr,pft,rest) =>
          SOME (INR (StoreOrder name vars gspec f pfr pft), f_ns'',rest))
      | SOME (ChangeObjpar b f, f_ns'') => NONE
        (* TODO
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          case res of NONE =>
            SOME (INR (ChangeObj b f pf), f_ns'', rest)
          | _ => NONE
        ) *)
      | SOME (ChangePrespar b x c, f_ns'') => NONE
        (* TODO
        (case parse_red_aux f_ns'' rest [] of
          NONE => NONE
        | SOME (res,pf,f_ns'',rest) =>
          case res of NONE =>
            SOME (INR (ChangePres b x c pf), f_ns'', rest)
          | _ => NONE
        ) *)
  )
End

(* TODO below *)

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
  case strip_term_line s of NONE => NONE
  | SOME s =>
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

(*

EVAL
``parse_concl (plainVar_nf,()) (toks_fast (strlit"conclusion NONE ;"))``;

EVAL
``parse_concl (plainVar_nf,()) (toks_fast (strlit"conclusion UNSAT : 1234 ;"))``;

*)

(* Parse a PBC output line *)
Definition parse_output_def:
  parse_output s =
  case strip_term_line s of NONE => NONE
  | SOME s =>
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
