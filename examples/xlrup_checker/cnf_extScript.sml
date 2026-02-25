(*
  Syntax and semantics of CNF extended with theories
*)
Theory cnf_ext
Ancestors
  misc mlstring mlint
Libs
  preamble

(* The goal of this file is to provide a surface syntax and semantics that
closely resembles the meaning of CNF DIMACS files (or its extended variants) *)

Datatype:
  lit = Pos num | Neg num
End

(* Clauses and their semantics *)
Type clause = ``:lit list``;
Type assignment = ``:num -> bool``;

Definition sat_lit_def:
  sat_lit (w:assignment) l ⇔
  (case l of Pos x => w x | Neg x => ¬w x)
End

Definition sat_clause_def:
  sat_clause w C ⇔
  (∃l. l ∈ set C ∧ sat_lit w l)
End

(* XOR constraints are a list of literals required to sum (XOR) to 1 under the
given assignment. This is the format currently used by CryptoMiniSat. *)
Type cmsxor = ``:lit list``;

Definition of_bool_def:
  (of_bool T = (1:num)) ∧
  (of_bool F = 0)
End

Definition sat_cmsxor_def:
  sat_cmsxor w C =
    ODD (SUM (MAP (of_bool o sat_lit w) C))
End

(* BNN constraints are a list of literals, an RHS k and an optional literal y.
  The constraint is satisfied iff y reifies the at-least-k constraint.
  The option defaults to true if not present *)
Type cmsbnn = ``:lit list # num # lit option``;

Definition sat_cmsbnn_def:
  sat_cmsbnn w ((C, k, oy):cmsbnn) =
    (OPTION_ALL (sat_lit w) oy ⇔ (SUM (MAP (of_bool o sat_lit w) C) ≥ k))
End

(***
  Next, we define the general semantics of formulas sharing an assignment.
 ***)
Type fml = ``:clause list # cmsxor list # cmsbnn list``;

Definition sat_fml_def:
  sat_fml w ((fc,fx,fb):fml) = (
    (∀C. C ∈ set fc ⇒ sat_clause w C) ∧
    (∀C. C ∈ set fx ⇒ sat_cmsxor w C) ∧
    (∀C. C ∈ set fb ⇒ sat_cmsbnn w C)
  )
End

Definition sols_def:
  sols f = {w | sat_fml w f}
End

(***
  End mirrored definitions
 ***)

(* A parser and printed for extended CNF in CakeML *)

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

(* Extended CNF parser *)

(* Parse a literal *)
Definition mk_lit_def:
  mk_lit l =
  let n = Num (ABS l) in
  if l > 0 then Pos n else Neg n
End

(* Parse a list of literals ending with 0 and return the rest *)
Definition parse_lits_aux_def:
  (parse_lits_aux [] (acc:lit list) = NONE) ∧
  (parse_lits_aux (x::xs) acc =
    case x of
      INR l =>
      if l = 0i then SOME (REVERSE acc, xs)
      else
        parse_lits_aux xs (mk_lit l::acc)
    | INL (_:mlstring) => NONE)
End

Definition var_lit_def[simp]:
  (var_lit (Pos n) = n) ∧
  (var_lit (Neg n) = n)
End

(* Force literals to be in maxvar *)
Definition check_maxvar_def:
  check_maxvar maxvar ls =
  EVERY (λl. var_lit l ≤ maxvar) ls
End

Definition parse_lits_def:
  parse_lits maxvar ls =
  case parse_lits_aux ls [] of
    SOME (ls,[]) =>
    if check_maxvar maxvar ls then SOME ls else NONE
  | _ => NONE
End

(* Makes sure we start with cID or c ID and return the rest *)
Definition fix_hd_def:
  (fix_hd c (INL s::cs) =
    if strlen s ≥ 1 ∧ strsub s 0 = c then
    if strlen s = 1 then SOME cs
    else
      case mlint$fromString (substring s 1 (strlen s - 1)) of
        NONE => NONE
      | SOME i => SOME (INR i::cs)
    else NONE) ∧
  (fix_hd c _ = NONE)
End

Definition parse_xor_def:
  parse_xor maxvar ls =
  case fix_hd #"x" ls of
    SOME cs => parse_lits maxvar cs
  | _ => NONE
End

(* parses the tail part of the BNN constraint "k y 0" or "k 0" *)
Definition parse_bnn_tail_def:
  (parse_bnn_tail ls =
  case ls of
  | [INR k; INR y; INR n] =>
    if k ≥ 0i ∧ y ≠ 0 ∧ n = 0i
    then
      SOME (Num k, SOME (mk_lit y))
    else
      NONE
  | [INR k; INR n] =>
    if k ≥ 0i ∧ n = 0i
    then
      SOME (Num k, NONE)
    else
      NONE
  | _ => NONE)
End

Definition parse_bnn_def:
  parse_bnn maxvar ls =
  case fix_hd #"b" ls of
    SOME cs =>
    (case parse_lits_aux cs [] of
      NONE => NONE
    | SOME (ls,xs) =>
      (case parse_bnn_tail xs of NONE => NONE
      |  SOME (k,oy) =>
        if OPTION_ALL (λy. var_lit y ≤ maxvar) oy ∧ check_maxvar maxvar ls then
          SOME (ls,k,oy)
        else NONE
      ))
  | _ => NONE
End

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

Datatype:
  cnf_ext =
    Clause clause
  | Cmsxor cmsxor
  | Cmsbnn cmsbnn
End

Definition parse_line_def:
  parse_line maxvar xs =
  (case parse_lits maxvar xs of
    SOME c => SOME (Clause c)
  | NONE =>
  (case parse_xor maxvar xs of
    SOME x => SOME (Cmsxor x)
  | NONE =>
  (case parse_bnn maxvar xs of
    SOME b => SOME (Cmsbnn b)
  | NONE => NONE)))
End

(* Produces the list of clauses and XORs in order they are read *)
Definition parse_body_def:
  (parse_body maxvar [] cacc xacc bacc =
    SOME (REVERSE cacc, REVERSE xacc, REVERSE bacc)) ∧
  (parse_body maxvar (s::ss) cacc xacc bacc =
    case parse_line maxvar s of
      NONE => NONE
    | SOME cx =>
      case cx of
        Clause c => parse_body maxvar ss (c::cacc) xacc bacc
      | Cmsxor x => parse_body maxvar ss cacc (x::xacc) bacc
      | Cmsbnn b => parse_body maxvar ss cacc xacc (b::bacc)
  )
End

Definition parse_header_line_def:
  parse_header_line ls =
  case ls of
    [p; cnf; vars; numls] =>
    if p = INL (strlit "p") ∧ cnf = INL (strlit "cnf")
    then
      case (vars, numls)
      of
        (INR v,INR c) => if v ≥ 0 ∧ c ≥ 0 then SOME (Num v,Num c) else NONE
      | _ => NONE
    else NONE
  | _ => NONE
End

Definition parse_cnf_ext_toks_def:
  parse_cnf_ext_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
    (case parse_header_line s of
    SOME (vars,ncx) =>
      (case parse_body vars ss [] [] [] of NONE => NONE
      | SOME (cacc,xacc,bacc) =>
       if LENGTH cacc + LENGTH xacc + LENGTH bacc= ncx then
        SOME (vars,ncx,cacc,xacc,bacc)
        else NONE)
    | NONE => NONE)
  | [] => NONE
End

Definition parse_cnf_ext_def:
  parse_cnf_ext strs =
  let tokss = MAP toks strs in
  case parse_cnf_ext_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

val cnf_ext_raw = ``[
  strlit "c this is a comment";
  strlit "p cnf 15 11 ";
  strlit "    1  4 0";
  strlit "x1  -5 0";
  strlit "c this is a comment";
  strlit "    2  4 0";
  strlit "    2  5 0";
  strlit "x  -3  4 0";
  strlit "    3  5 0";
  strlit "-1 -2 -3 0";
  strlit "b 1 -2 -3 -4 -5 6 -7 -8 -9 -10 11 -12 13 -14 -15 0 55 11 0";
  strlit "b1 -2 -3 -4 -5 6 -7 -8 -9 -10 11 -12 13 -14 -15 0 55 -11 0";
  strlit "b1 -2 -3 -4 -5 6 -7 -8 -9 -10 11 -12 13 -14 -15 0 55 0";
  strlit "c this is a comment";
  strlit "   -4 -5 0";
  ]``;

val test = rconc (EVAL ``THE (parse_cnf_ext ^(cnf_ext_raw))``);

(* CNF ext printer *)

Definition print_lit_def:
  (print_lit (Pos n) = toString n) ∧
  (print_lit (Neg n) = strlit"-" ^ toString n)
End

Definition print_lits_def:
  (print_lits e [] = str #"0" ^ str e) ∧
  (print_lits e (x::xs) =
    print_lit x ^ strlit(" ") ^ print_lits e xs)
End

Definition print_clause_def:
  print_clause xs = print_lits (#"\n") xs
End

Definition print_xor_def:
  print_xor xs = strlit"x " ^ print_lits (#"\n") xs
End

Definition print_opt_lit_def:
  print_opt_lit oy = case oy of NONE => strlit "" | SOME y => print_lit y
End

Definition print_tail_def:
  print_tail (k:num) (oy:lit option) =
  toString k ^ strlit " " ^
  case oy of NONE => strlit "0\n"
  | SOME y => print_lit y ^ strlit " 0\n"
End

Definition print_bnn_def:
  print_bnn (ls,k,y) = strlit"b " ^ print_lits (#" ") ls ^ print_tail k y
End

Definition print_header_line_def:
  print_header_line v len =
  strlit ("p cnf ") ^  toString v ^ strlit(" ") ^ toString len ^ strlit("\n")
End

Definition max_list_def:
  (max_list k [] = k) ∧
  (max_list k (x::xs) = max_list (MAX k x) xs)
End

Definition max_var_opt_def:
  max_var_opt oy = case oy of NONE => 0n | SOME y => var_lit y
End

Definition max_var_bnn_def:
  max_var_bnn (ls,k,oy) =
    max_list (max_var_opt oy) (MAP var_lit ls)
End

Definition print_cnf_ext_def:
  print_cnf_ext (cs,xs,bs) =
  let len = LENGTH cs + LENGTH xs + LENGTH bs in
  let cmax = max_list 0 (MAP (max_list 0 o MAP var_lit) cs) in
  let xmax = max_list 0 (MAP (max_list 0 o MAP var_lit) xs) in
  let bmax = max_list 0 (MAP max_var_bnn bs) in
  print_header_line (max_list 0 [cmax;xmax;bmax]) len ::
  MAP print_clause cs ++ MAP print_xor xs ++ MAP print_bnn bs
End

val test2 = rconc (EVAL ``(print_cnf_ext ^(test))``);

Theorem tokens_unchanged:
  EVERY ($~ o P) (explode ls) ∧ ¬ NULL (explode ls) ⇒
  tokens P ls = [ls]
Proof
  rw[] >> drule TOKENS_unchanged>>
  simp[]>>
  simp[GSYM mlstringTheory.TOKENS_eq_tokens]
QED

Theorem isDigit_not_blanks[local]:
  isDigit c ==> ~ blanks c
Proof
  CCONTR_TAC \\ fs [blanks_def] \\ fs [isDigit_def]
QED

Theorem blanks_thms[simp]:
  (blanks #"\n") ∧
  (blanks #" ") ∧
  (¬blanks #"-") ∧
  (¬blanks #"x") ∧
  (¬blanks #"b")
Proof
  EVAL_TAC
QED

Theorem isDigit_thms[simp]:
  (¬isDigit #"x") ∧
  (¬isDigit #"b")
Proof
  EVAL_TAC
QED

Theorem tokens_blanks_print_lit:
  tokens blanks (print_lit l) = [print_lit l]
Proof
  match_mp_tac tokens_unchanged>>
  Cases_on`l`>>
  Cases_on`toString n`>>
  simp[print_lit_def]>>
  `~NULL s` by
    (drule num_to_str_imp_cons>>rw[]>>fs[])>>
  simp[]>>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any num_to_str_every>>
  asm_exists_tac>>simp[GSYM isDigit_def, isDigit_not_blanks]
QED

Theorem print_lit_alt:
  n ≠ 0 ⇒
  (print_lit (Pos n) = int_to_string (#"-") (&n)) ∧
  (print_lit (Neg n) = int_to_string (#"-") (-&n))
Proof
  rw[print_lit_def,int_to_string_thm,num_to_str_thm]>>
  simp[strcat_def,concat_def,implode_def]
QED

Overload nz_lit = ``(λl. var_lit l ≠ 0)``

Theorem fromString_print_lit:
  nz_lit h ⇒
  ∃i.
    fromString (print_lit h) = SOME i ∧
    Num (ABS i) = var_lit h ∧
    (if i > 0 then h = Pos (var_lit h) else h = Neg (var_lit h))
Proof
  Cases_on`h`>>rw[]>>
  drule print_lit_alt>>simp[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem parse_lits_aux_print_lits:
  ∀ys acc.
  EVERY nz_lit ys ∧ blanks c
  ⇒
  parse_lits_aux (toks (print_lits c ys ^ rest)) acc =
    SOME (REVERSE acc ++ ys,toks rest)
Proof
  simp[toks_def]>>
  Induct>>rw[print_lits_def]
  >- (
    drule mlstringTheory.tokens_append>>simp[]>>
    `strlit (STRING #"0" (STRING c "")) = strlit"0" ^ str c` by EVAL_TAC>>
    simp[]>>
    EVAL_TAC)>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  disch_then (fn th => simp[th])>>
  simp[tokens_blanks_print_lit]>>
  gvs[parse_lits_aux_def,tokenize_def]>>
  drule fromString_print_lit>>
  rw[]>>simp[]>>
  rw[]>>gvs[AllCaseEqs()]>>
  simp[mk_lit_def]>>rw[]>>
  gvs[]>>rw[]>>
  every_case_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem parse_lits_print_clause:
  EVERY nz_lit ys ∧
  EVERY (λl. var_lit l ≤ maxvar) ys
  ⇒
  parse_lits maxvar (toks (print_clause ys)) = SOME ys
Proof
  rw[parse_lits_def,print_clause_def]>>
  drule parse_lits_aux_print_lits>>
  disch_then (qspecl_then[`strlit""`,`#"\n"`,`[]`] mp_tac)>>
  gvs[check_maxvar_def]>>
  EVAL_TAC
QED

Theorem fix_hd_toks:
  s = strlit [c;#" "] ∧ ¬blanks c ∧ ¬isDigit c ⇒
  fix_hd c (toks (s ^ rest)) =
  SOME (toks rest)
Proof
  rw[toks_def]>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb`>>
  `aa = strlit[c] ^ strlit" "` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  rw[]>>
  DEP_ONCE_REWRITE_TAC[tokens_unchanged]>>
  simp[tokenize_def]>>
  EVAL_TAC>>gvs[isDigit_def,fix_hd_def]
QED

Theorem parse_xor_print_xor:
  EVERY nz_lit  ys ∧
  EVERY (λl. var_lit l ≤ maxvar) ys
  ⇒
  parse_xor maxvar (toks (print_xor ys)) = SOME ys
Proof
  rw[parse_xor_def,print_xor_def]>>
  DEP_REWRITE_TAC[fix_hd_toks]>>
  CONJ_TAC >- EVAL_TAC>>
  simp[]>>
  drule parse_lits_aux_print_lits>>
  disch_then (qspecl_then[`strlit""`,`#"\n"`,`[]`] mp_tac)>>
  fs[toks_def,parse_lits_def,check_maxvar_def]>>
  EVAL_TAC
QED

Theorem tokens_blanks_toString:
  tokens blanks (toString h) = [toString h]
Proof
  match_mp_tac tokens_unchanged>>
  Cases_on`toString h`>>
  `~NULL s` by
    (drule num_to_str_imp_cons>>rw[]>>fs[])>>
  simp[]>>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any num_to_str_every>>
  asm_exists_tac>>simp[GSYM isDigit_def, isDigit_not_blanks]
QED

Theorem tokenize_toString[simp]:
  tokenize (toString n) = INR (&n)
Proof
  rw[tokenize_def,num_to_str_def]
QED

Theorem tokenize_print_lit[simp]:
  nz_lit n ⇒
  tokenize (print_lit n) =
    INR (
      case n of Pos v => &v | Neg v => -&v)
Proof
  rw[tokenize_def]>>
  drule fromString_print_lit>>rw[]>>
  simp[]>>
  every_case_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem parse_bnn_tail_print_tail:
  OPTION_ALL nz_lit oy ⇒
  parse_bnn_tail (toks (print_tail k oy)) = SOME (k,oy)
Proof
  rw[print_tail_def,toks_def]>>
  `« 0\n» = str #" " ^ strlit"0\n"` by EVAL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>
  simp[tokens_blanks_toString]>>
  `MAP tokenize (tokens blanks «0\n») = [INR 0]` by
    EVAL_TAC>>
  Cases_on`oy`>>simp[parse_bnn_tail_def]>>
  rw[]
  >- intLib.ARITH_TAC>>
  simp[tokens_blanks_print_lit]>>
  Cases_on`x`>>rw[mk_lit_def]>>gvs[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem parse_bnn_print_bnn:
  OPTION_ALL nz_lit oy ∧ OPTION_ALL (\y. var_lit y ≤ maxvar) oy ∧
  EVERY nz_lit ls ∧ EVERY (λl. var_lit l ≤ maxvar) ls
  ⇒
  parse_bnn maxvar (toks (print_bnn (ls,k,oy))) = SOME (ls,k,oy)
Proof
  rw[parse_bnn_def,print_bnn_def]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  DEP_REWRITE_TAC[fix_hd_toks]>>
  CONJ_TAC >- EVAL_TAC>>
  drule parse_lits_aux_print_lits>>
  disch_then (qspecl_then[`print_tail k oy`,`#" "`,`[]`] mp_tac)>>
  simp[parse_bnn_tail_print_tail]>>
  rw[check_maxvar_def]
QED

Theorem fromString_toString_num:
  mlint$fromString ((toString (n:num)):mlstring) = SOME (&n)
Proof
  rw[num_to_str_def]
QED

Theorem parse_header_line_print_header_line:
  parse_header_line (toks (print_header_line v len)) = SOME(v,len)
Proof
  rw[print_header_line_def, toks_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ cc ^ dd`>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `aa = strlit"p" ^ strlit" " ^ strlit"cnf" ^ strlit" "` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  strip_tac>>
  first_assum(qspecl_then[`aa ^ bb`,`cc ^ dd`] assume_tac)>>fs[]>>
  `cc ^ dd = cc ^ dd ^ strlit""` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #"\n" ∧ str #"\n" = strlit "\n"` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  unabbrev_all_tac>>
  rw[]>>
  `tokens blanks (strlit "p") = [strlit "p"]` by EVAL_TAC>>
  `tokens blanks (strlit "cnf") = [strlit "cnf"]` by EVAL_TAC>>
  `tokens blanks (strlit "") = []` by EVAL_TAC>>
  simp[tokens_blanks_toString]>>
  simp[tokenize_def,parse_header_line_def]>>
  CONJ_TAC >- EVAL_TAC>>
  simp[fromString_toString_num]>>
  intLib.ARITH_TAC
QED

Theorem print_header_line_first:
  ∃ls. tokens blanks (print_header_line a b) =
  strlit"p"::ls
Proof
  rw[print_header_line_def]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb ^ _ ^ dd ^ ee`>>
  `aa = strlit"p" ^ strlit" " ^ strlit"cnf" ^ strlit" "` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  simp[]>>
  PURE_REWRITE_TAC[GSYM mlstringTheory.strcat_assoc]>>
  PURE_REWRITE_TAC[Once mlstringTheory.strcat_assoc]>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  `tokens blanks (strlit "p") = [strlit "p"]` by EVAL_TAC>>
  simp[]
QED

Theorem FILTER_nocomment_print_clause:
  EVERY (EVERY nz_lit) ls ⇒
  FILTER nocomment_line
    (MAP toks (MAP print_clause ls)) =
    (MAP toks (MAP print_clause ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  Cases_on`x`>>simp[print_clause_def]
  >- EVAL_TAC >>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  first_x_assum drule>>
  simp[DISJ_IMP_THM,FORALL_AND_THM]>>rw[]>>
  simp[toks_def,print_lits_def]>>
  drule mlstringTheory.tokens_append>>simp[]>>
  simp[tokens_blanks_print_lit,tokenize_def]>>
  drule fromString_print_lit >> rw[]>>simp[nocomment_line_def]
QED

Theorem FILTER_nocomment_print_xor:
  FILTER nocomment_line
    (MAP toks (MAP print_xor ls)) =
    (MAP toks (MAP print_xor ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  simp[print_xor_def]>>
  EVAL_TAC
QED

Theorem FILTER_nocomment_print_bnn:
  FILTER nocomment_line
    (MAP toks (MAP print_bnn ls)) =
    (MAP toks (MAP print_bnn ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  PairCases_on`x`>>simp[print_bnn_def]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  rename1`_ ^ bla`>>
  EVAL_TAC
QED

Theorem parse_body_MAP_print_lits:
  ∀cs cacc xacc bacc.
  EVERY (λls.
    EVERY nz_lit ls ∧
    EVERY (λl. var_lit l ≤ maxvar) ls) cs
  ⇒
  parse_body maxvar (MAP toks (MAP print_clause cs)) cacc xacc bacc =
    SOME (REVERSE cacc ++ cs, REVERSE xacc, REVERSE bacc)
Proof
  Induct>>rw[parse_body_def,parse_line_def]>>
  drule parse_lits_print_clause>> rw[]
QED

Theorem parse_lits_print_xor:
  parse_lits maxvar (toks (print_xor xs)) = NONE
Proof
  rw[parse_lits_def,print_xor_def,toks_def]>>
  `strlit "x " = strlit"x" ^ strlit" "` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  rw[]>>
  EVAL_TAC>>
  rename1`_::rest`>>
  Cases_on`rest`>> simp[parse_lits_aux_def]
QED

Theorem parse_body_MAP_print_xor:
  ∀cs xacc cacc bacc.
  EVERY (λls.
    EVERY nz_lit ls ∧
    EVERY (λl. var_lit l ≤ maxvar) ls) cs
  ⇒
  parse_body maxvar (MAP toks (MAP print_xor cs)) cacc xacc bacc =
    SOME (REVERSE cacc, REVERSE xacc ++ cs, REVERSE bacc)
Proof
  Induct>>rw[parse_body_def,parse_line_def,parse_lits_print_xor]>>
  drule parse_xor_print_xor>>rw[]
QED

Theorem parse_lits_print_bnn:
  parse_lits maxvar (toks (print_bnn b)) = NONE
Proof
  PairCases_on`b`>>
  rw[parse_lits_def,print_bnn_def,toks_def]>>
  `strlit "b " = strlit"b" ^ strlit" "` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  DISCH_THEN (fn th => simp[th])>>
  rename1`_ ++ rest`>>
  EVAL_TAC
QED

Theorem parse_xor_print_bnn:
  parse_xor maxvar (toks (print_bnn b)) = NONE
Proof
  PairCases_on`b`>>
  rw[parse_xor_def,print_bnn_def,toks_def]>>
  `strlit "b " = strlit"b" ^ strlit" "` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  PURE_REWRITE_TAC[GSYM strcat_assoc]>>
  DISCH_THEN (fn th => simp[th])>>
  rename1`_ ++ rest`>>
  EVAL_TAC
QED

Theorem parse_body_MAP_print_bnn:
  ∀cs bacc cacc xacc.
  EVERY (λ(ls,k,oy).
    OPTION_ALL nz_lit oy ∧
    OPTION_ALL (\y. var_lit y ≤ maxvar) oy ∧
    EVERY nz_lit ls ∧
    EVERY (λl. var_lit l ≤ maxvar) ls
    ) cs
  ⇒
  parse_body maxvar (MAP toks (MAP print_bnn cs)) cacc xacc bacc =
    SOME (REVERSE cacc, REVERSE xacc, REVERSE bacc ++ cs)
Proof
  Induct>>rw[parse_body_def,parse_line_def,parse_lits_print_bnn,parse_xor_print_bnn]>>
  PairCases_on`h`>>DEP_REWRITE_TAC[parse_bnn_print_bnn]>>gvs[]
QED

Theorem parse_body_append:
  ∀xs cacc xacc bacc cacc' xacc' bacc'.
  parse_body a xs cacc xacc bacc = SOME (cacc',xacc',bacc') ⇒
  parse_body a (xs++ys) cacc xacc bacc =
  parse_body a ys (REVERSE cacc') (REVERSE xacc') (REVERSE bacc')
Proof
  Induct>>rw[parse_body_def]>> simp[]>>
  gvs[AllCaseEqs()]
QED

Theorem max_list_max:
  ∀ls k.
  k ≤ max_list k ls ∧
  EVERY (λn. n ≤ max_list k ls)  ls
Proof
  Induct>>rw[max_list_def]>>
  first_x_assum(qspec_then`MAX k h` mp_tac)>>
  simp[]
QED

Theorem le_max_list:
  (∃l. v ≤ l ∧ MEM l ls) ⇒
  v ≤ max_list k ls
Proof
  rw[]>>
  assume_tac (SPEC_ALL max_list_max)>>
  rw[EVERY_MEM]>>
  first_x_assum drule>>fs[]
QED

Theorem parse_cnf_ext_toks_print_cnf_ext_toks:
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bs
  ⇒
  ∃mv cl.
  parse_cnf_ext_toks (MAP toks (print_cnf_ext (cs,xs,bs))) =
    SOME (mv,cl,(cs,xs,bs))
Proof
  strip_tac>>simp[parse_cnf_ext_toks_def,print_cnf_ext_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize (strlit "p") = INL (strlit "p")` by EVAL_TAC>>
  simp[nocomment_line_def]>>
  simp[parse_header_line_print_header_line]>>
  unabbrev_all_tac>>
  simp[FILTER_APPEND,FILTER_nocomment_print_xor,FILTER_nocomment_print_clause,FILTER_nocomment_print_bnn]>>
  qmatch_goalsub_abbrev_tac`parse_body a (b1++b2++b3) _ _`>>
  qspecl_then [`a`,`cs`,`[]`,`[]`,`[]`] mp_tac (GEN_ALL parse_body_MAP_print_lits)>>
  simp[]>>
  impl_tac >- (
    fs[EVERY_MEM,PULL_FORALL,AND_IMP_INTRO]>>rw[]
    >-
      metis_tac[]>>
    simp[Abbr`a`]>>
    irule le_max_list>>
    simp[MEM_MAP,PULL_EXISTS,SF DNF_ss]>>
    DISJ1_TAC>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    metis_tac[LESS_EQ_REFL])>>
  strip_tac>>
  drule parse_body_append>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  simp[]>> disch_then kall_tac>>
  qspecl_then [`a`,`xs`,`[]`,`(REVERSE cs)`,`[]`] mp_tac (GEN_ALL parse_body_MAP_print_xor)>>
  impl_tac >- (
    fs[EVERY_MEM,PULL_FORALL,AND_IMP_INTRO]>>rw[]
    >-
      metis_tac[]>>
    simp[Abbr`a`]>>
    irule le_max_list>>
    simp[MEM_MAP,PULL_EXISTS,SF DNF_ss]>>
    DISJ2_TAC>>DISJ1_TAC>>
    irule le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    metis_tac[LESS_EQ_REFL])>>
  strip_tac>>
  drule parse_body_append>>
  rw[]>>
  qspecl_then [`a`,`bs`,`[]`,`(REVERSE cs)`,`REVERSE xs`] mp_tac (GEN_ALL parse_body_MAP_print_bnn)>>
  simp[]>>
  impl_tac >- (
    fs[EVERY_MEM,PULL_FORALL,AND_IMP_INTRO]>>rw[]>>
    first_x_assum drule>>
    pairarg_tac>>simp[Abbr`a`]>>rw[]>>
    TRY(Cases_on`oy`>>simp[])>>
    irule le_max_list>>
    simp[MEM_MAP,PULL_EXISTS,SF DNF_ss]>>
    DISJ2_TAC>>DISJ2_TAC>>
    irule le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    first_x_assum (irule_at Any)>>
    simp[max_var_bnn_def,max_var_opt_def]
    >-
      metis_tac[max_list_max]>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    metis_tac[LESS_EQ_REFL])>>
  simp[]
QED

Theorem parse_cnf_ext_print_cnf_ext:
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bs
  ⇒
  parse_cnf_ext (print_cnf_ext (cs,xs,bs)) = SOME (cs,xs,bs)
Proof
  rw[parse_cnf_ext_def]>>
  assume_tac parse_cnf_ext_toks_print_cnf_ext_toks>>
  gvs[]
QED

Theorem parse_lits_aux_nz_lit:
  ∀ls acc c rest.
  parse_lits_aux ls acc = SOME (c,rest) ∧
  EVERY nz_lit acc ⇒
  EVERY nz_lit c
Proof
  Induct>>
  rw[parse_lits_aux_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  last_x_assum (irule_at Any)>>
  rw[mk_lit_def]
QED

Theorem parse_line_nz_lit:
  case parse_line v h of
    SOME (Clause c) => EVERY nz_lit c
  | SOME (Cmsxor x) => EVERY nz_lit x
  | SOME (Cmsbnn (ls,k,oy)) => OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls
  | _ => T
Proof
  rw[parse_line_def]>>
  TOP_CASE_TAC>>simp[]>>
  gvs[AllCaseEqs()]
  >- (
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    gvs[parse_bnn_def,parse_lits_def,AllCaseEqs(),parse_bnn_tail_def]>>
    drule parse_lits_aux_nz_lit>>simp[]>>
    rw[mk_lit_def])
  >- (
    last_x_assum kall_tac>>
    gvs[parse_xor_def,parse_lits_def,AllCaseEqs()]>>
    drule parse_lits_aux_nz_lit>>
    simp[])
  >- (
    gvs[parse_lits_def,AllCaseEqs()]>>
    drule parse_lits_aux_nz_lit>>
    simp[])
QED

Theorem parse_body_nz_lit:
  ∀ss cacc xacc bacc.
  parse_body v ss cacc xacc bacc = SOME (cs,xs,bs) ∧
  EVERY (EVERY nz_lit) cacc ∧
  EVERY (EVERY nz_lit) xacc ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bacc ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bs
Proof
  Induct >- (
    rw[parse_body_def]>>
    gvs[])>>
  simp[parse_body_def]>>
  ntac 5 strip_tac>>
  assume_tac parse_line_nz_lit>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  impl_tac >> simp[]>>
  pairarg_tac>>gvs[]
QED

Theorem parse_cnf_ext_toks_nz_lit:
  parse_cnf_ext_toks tokss = SOME (v,n,cs,xs,bs) ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bs
Proof
  rw[parse_cnf_ext_toks_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_body_nz_lit>>simp[]
QED

Theorem parse_cnf_ext_nz_lit:
  parse_cnf_ext ls = SOME (cs,xs,bs) ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ∧
  EVERY (λ(ls,k,oy). OPTION_ALL nz_lit oy ∧ EVERY nz_lit ls) bs
Proof
  strip_tac>>gvs[parse_cnf_ext_def,AllCaseEqs()]>>
  metis_tac[parse_cnf_ext_toks_nz_lit]
QED

