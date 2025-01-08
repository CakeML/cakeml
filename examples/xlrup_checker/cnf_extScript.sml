(*
  Syntax and semantics of CNF extended with theories
*)
open preamble miscTheory mlstringTheory mlintTheory;

val _ = new_theory "cnf_ext";

(*
  The goal of this file is to provide a surface syntax and semantics that
  closely resembles the informal meaning of CNF DIMACS files (or its extended
  variants)
*)

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

(* BNN constraints are a list (set) of variables, an RHS k and a variable y.
  The constraint is satisfied iff y reifies the at-least-k constraint *)
Type cmsbnn = ``:num list # num # num``;

Definition sat_cmsbnn_def:
  sat_cmsbnn w ((C, k, y):cmsbnn) =
    (w y ⇔ (∑ (λv. of_bool (w v)) (set C) ≥ k))
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

(* Parse a list of literals ending with 0
  Literals only use variables between 1 to maxvar (inclusive) *)
Definition parse_lits_aux_def:
  (parse_lits_aux maxvar [] (acc:lit list) = NONE) ∧
  (parse_lits_aux maxvar [c] acc =
    if c = INR 0i then SOME (REVERSE acc) else NONE) ∧
  (parse_lits_aux maxvar (x::xs) acc =
    case x of
      INR l =>
      let n = Num (ABS l) in
      let v = if l > 0 then Pos n else Neg n in
      if n = 0 ∨ n > maxvar then NONE
      else parse_lits_aux maxvar xs (v::acc)
    | INL (_:mlstring) => NONE)
End

Definition parse_lits_def:
  parse_lits maxvar ls = parse_lits_aux maxvar ls []
End

Definition parse_clause_def:
  parse_clause maxvar xs = parse_lits_aux maxvar xs []
End

(* Special handling for "xID" no space *)
Definition parse_xvar_def:
  parse_xvar s =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    mlint$fromString (substring s 1 (strlen s - 1))
  else NONE
End

Definition parse_xor_def:
  parse_xor maxvar xs =
  case xs of
    (INL c::cs) =>
    if c = strlit "x"
    then parse_lits_aux maxvar cs []
    else (
      case parse_xvar c of NONE => NONE
      | SOME i => parse_lits_aux maxvar (INR i::cs) [])
  | _ => NONE
End

(* Special handling for "bID" no space *)
Definition parse_bvar_def:
  parse_bvar s =
  if strlen s ≥ 1 ∧ strsub s 0 = #"b" then
    mlint$fromNatString (substring s 1 (strlen s - 1))
  else NONE
End

(* parses the tail part of the BNN constraint "k y 0" *)
Definition parse_bnn_tail_def:
  (parse_bnn_tail [INR k; INR y; INR n] =
    if k ≥ 0i ∧ y ≥ 0i ∧ n = 0i
    then
      SOME (Num k, Num y)
    else
      NONE) ∧
  (parse_bnn_tail _ = NONE)
End

(* Parse a list of BNN LHS variables ending with 0
  Variables between 1 to maxvar (inclusive) *)
Definition parse_bnn_vars_aux_def:
  (parse_bnn_vars_aux maxvar [] (acc:lit list) = NONE) ∧
  (parse_bnn_vars_aux maxvar (x::xs) acc =
    case x of
      INR l =>
      let n = Num (ABS l) in
      let v = if l > 0 then Pos n else Neg n in
      if n = 0 ∨ n > maxvar then NONE
      else parse_bnn_vars_aux maxvar xs (v::acc)
    | INL (_:mlstring) => NONE)
End

Definition parse_bnn_vars_def:
  parse_bnn_vars maxvar ls = parse_bnn_vars_aux maxvar ls []
End

(* lines which are not comments don't start with a single "c" *)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

Definition parse_line_def:
  parse_line maxvar xs =
  case parse_clause maxvar xs of
    SOME c => SOME (INL c)
  | NONE =>
  case parse_xor maxvar xs of
    SOME x => SOME (INR x)
  | NONE => NONE
End

(* Produces the list of clauses and XORs in order they are read *)
Definition parse_body_def:
  (parse_body maxvar [] cacc xacc =
    SOME (REVERSE cacc, REVERSE xacc)) ∧
  (parse_body maxvar (s::ss) cacc xacc =
    case parse_line maxvar s of
      NONE => NONE
    | SOME cx =>
      case cx of
        INL c => parse_body maxvar ss (c::cacc) xacc
      | INR x => parse_body maxvar ss cacc (x::xacc)
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

Definition parse_cnf_xor_toks_def:
  parse_cnf_xor_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  case nocomments of
    s::ss =>
    (case parse_header_line s of
    SOME (vars,ncx) =>
      (case parse_body vars ss [] [] of NONE => NONE
      | SOME (cacc,xacc) =>
       if LENGTH cacc + LENGTH xacc = ncx then
        SOME (vars,ncx,cacc,xacc)
        else NONE)
    | NONE => NONE)
  | [] => NONE
End

Definition parse_cnf_xor_def:
  parse_cnf_xor strs =
  let tokss = MAP toks strs in
  case parse_cnf_xor_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

val cnf_xor_raw = ``[
  strlit "c this is a comment";
  strlit "p cnf 5 8 ";
  strlit "    1  4 0";
  strlit "x1  -5 0";
  strlit "c this is a comment";
  strlit "    2  4 0";
  strlit "    2  5 0";
  strlit "x  -3  4 0";
  strlit "    3  5 0";
  strlit "-1 -2 -3 0";
  strlit "c this is a comment";
  strlit "   -4 -5 0";
  ]``;

val test = rconc (EVAL ``THE (parse_cnf_xor ^(cnf_xor_raw))``);

(* CNF-XOR printer *)

Definition print_lit_def:
  (print_lit (Pos n) = toString n) ∧
  (print_lit (Neg n) = strlit"-" ^ toString n)
End

Definition print_clause_def:
  (print_clause [] = strlit "0\n") ∧
  (print_clause (x::xs) =
    print_lit x ^ strlit(" ") ^ print_clause xs)
End

Definition print_xor_def:
  print_xor xs = strlit"x " ^ print_clause xs
End

Definition print_header_line_def:
  print_header_line v len =
  strlit ("p cnf ") ^  toString v ^ strlit(" ") ^ toString len ^ strlit("\n")
End

Definition var_lit_def:
  (var_lit (Pos n) = n) ∧
  (var_lit (Neg n) = n)
End

Definition max_list_def:
  (max_list k [] = k) ∧
  (max_list k (x::xs) = max_list (MAX k x) xs)
End

Definition print_cnf_xor_def:
  print_cnf_xor (cs,xs) =
  let len = LENGTH cs + LENGTH xs in
  let cmax = max_list 0 (MAP (max_list 0 o MAP var_lit) cs) in
  let xmax = max_list 0 (MAP (max_list 0 o MAP var_lit) xs) in
  print_header_line (MAX cmax xmax) len ::
  MAP print_clause cs ++ MAP print_xor xs
End

val test2 = rconc (EVAL ``(print_cnf_xor ^(test))``);

Theorem tokens_unchanged:
  EVERY ($~ o P) (explode ls) ∧ ¬ NULL (explode ls) ⇒
  tokens P ls = [ls]
Proof
  rw[] >> drule TOKENS_unchanged>>
  simp[]>>
  simp[GSYM mlstringTheory.TOKENS_eq_tokens]
QED

Triviality isDigit_not_blanks:
  isDigit c ==> ~ blanks c
Proof
  CCONTR_TAC \\ fs [blanks_def] \\ fs [isDigit_def]
QED

Theorem tokens_blanks_print_lit:
  tokens blanks (print_lit l) = [print_lit l]
Proof
  match_mp_tac tokens_unchanged>>
  Cases_on`l`>>
  Cases_on`toString n`>>
  simp[print_lit_def,EVAL ``blanks #"-"``]>>
  `~NULL s` by
    (drule num_to_str_imp_cons>>rw[]>>fs[])>>
  simp[]>>
  irule listTheory.EVERY_MONOTONIC >>
  irule_at Any num_to_str_every>>
  asm_exists_tac>>simp[GSYM isDigit_def, isDigit_not_blanks]
QED

Theorem tokens_print_clause_nonempty:
  ∀ys. tokens blanks (print_clause ys) ≠ []
Proof
  Induct>>fs[print_clause_def]
  >-
    EVAL_TAC
  >>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]
QED

Theorem print_lit_alt:
  n ≠ 0 ⇒
  (print_lit (Pos n) = int_to_string (#"-") (&n)) ∧
  (print_lit (Neg n) = int_to_string (#"-") (-&n))
Proof
  rw[print_lit_def,int_to_string_thm,num_to_str_thm]>>
  simp[strcat_def,concat_def,implode_def]
QED

Theorem fromString_print_lit:
  var_lit h ≠ 0 ⇒
  ∃i.
    fromString (print_lit h) = SOME i ∧
    Num (ABS i) = var_lit h ∧
    (if i > 0 then h = Pos (var_lit h) else h = Neg (var_lit h))
Proof
  Cases_on`h`>>rw[var_lit_def]>>
  drule print_lit_alt>>simp[]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem parse_lits_aux_print_clause:
  ∀ys maxvar acc.
  EVERY (λl. var_lit l ≠ 0 ∧ var_lit l ≤ maxvar) ys
  ⇒
  parse_lits_aux maxvar (toks (print_clause ys)) acc =
    SOME (REVERSE acc ++ ys)
Proof
  simp[toks_def]>>
  Induct>>rw[print_clause_def]
  >-
    EVAL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  disch_then kall_tac>>
  simp[tokens_blanks_print_lit]>>
  simp[tokenize_def]>>
  Cases_on`tokens blanks (print_clause ys)`
  >-
    fs[tokens_print_clause_nonempty] >>
  simp[parse_lits_aux_def]>>
  drule fromString_print_lit>>
  rw[]>>simp[]>>
  qmatch_goalsub_abbrev_tac`ll::acc`>>
  gvs[]>>
  Cases_on`h`>>gvs[var_lit_def]
QED

Theorem parse_clause_print_clause:
  EVERY (λl. var_lit l ≠ 0 ∧ var_lit l ≤ maxvar) ys
  ⇒
  parse_clause maxvar (toks (print_clause ys)) = SOME ys
Proof
  rw[parse_clause_def]>>
  drule parse_lits_aux_print_clause>>
  disch_then (qspec_then`[]` assume_tac)>>simp[]
QED

Theorem parse_xor_print_xor:
  EVERY (λl. var_lit l ≠ 0 ∧ var_lit l ≤ maxvar) ys
  ⇒
  parse_xor maxvar (toks (print_xor ys)) = SOME ys
Proof
  rw[parse_xor_def,print_xor_def]>>
  simp[toks_def]>>
  `strlit "x " = strlit"x" ^ strlit" "` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #" " ∧ str #" " = strlit " "` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  disch_then kall_tac>>
  `MAP tokenize (tokens blanks «x») = [INL (strlit"x")]` by EVAL_TAC>>
  simp[]>>
  drule parse_lits_aux_print_clause>>
  disch_then (qspec_then`[]` assume_tac)>>fs[toks_def]
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
  EVERY (EVERY (λl. var_lit l ≠ 0)) ls ⇒
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
  simp[toks_def]>>
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

Theorem parse_body_MAP_print_clause:
  ∀cs cacc xacc.
  EVERY (EVERY (λl. var_lit l ≠ 0 ∧ var_lit l ≤ maxvar)) cs
  ⇒
  parse_body maxvar (MAP toks (MAP print_clause cs)) cacc xacc =
    SOME (REVERSE cacc ++ cs, REVERSE xacc)
Proof
  Induct>>rw[parse_body_def,parse_line_def]>>
  drule parse_clause_print_clause>> rw[]
QED

Theorem parse_clause_print_xor:
  parse_clause maxvar (toks (print_xor xs)) = NONE
Proof
  rw[parse_clause_def,print_xor_def,toks_def]>>
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
  ∀cs cacc xacc.
  EVERY (EVERY (λl. var_lit l ≠ 0 ∧ var_lit l ≤ maxvar)) cs
  ⇒
  parse_body maxvar (MAP toks (MAP print_xor cs)) cacc xacc =
    SOME (REVERSE cacc, REVERSE xacc ++ cs)
Proof
  Induct>>rw[parse_body_def,parse_line_def,parse_clause_print_xor]>>
  drule parse_xor_print_xor>>rw[]
QED

Theorem parse_body_append:
  ∀xs cacc xacc cacc' xacc'.
  parse_body a xs cacc xacc = SOME (cacc',xacc') ⇒
  parse_body a (xs++ys) cacc xacc =
  parse_body a ys (REVERSE cacc') (REVERSE xacc')
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

Theorem parse_cnf_xor_toks_print_cnf_xor_toks:
  EVERY (EVERY (λl. var_lit l ≠ 0)) cs ∧
  EVERY (EVERY (λl. var_lit l ≠ 0)) xs
  ⇒
  ∃mv cl.
  parse_cnf_xor_toks (MAP toks (print_cnf_xor (cs,xs))) =
    SOME (mv,cl,(cs,xs))
Proof
  strip_tac>>simp[parse_cnf_xor_toks_def,print_cnf_xor_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize (strlit "p") = INL (strlit "p")` by EVAL_TAC>>
  simp[nocomment_line_def]>>
  simp[parse_header_line_print_header_line]>>
  unabbrev_all_tac>>
  simp[FILTER_APPEND,FILTER_nocomment_print_xor,FILTER_nocomment_print_clause]>>
  qmatch_goalsub_abbrev_tac`parse_body a b _ _`>>
  qspecl_then [`a`,`cs`,`[]`,`[]`] mp_tac (GEN_ALL parse_body_MAP_print_clause)>>
  simp[]>>
  impl_tac >- (
    fs[EVERY_MEM,PULL_FORALL,AND_IMP_INTRO]>>rw[]
    >-
      metis_tac[]>>
    simp[Abbr`a`]>>
    DISJ1_TAC>>
    match_mp_tac le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    metis_tac[LESS_EQ_REFL])>>
  strip_tac>>
  drule parse_body_append>>
  disch_then(qspec_then`MAP toks (MAP print_xor xs)` assume_tac)>>
  simp[Abbr`b`]>>
  qspecl_then [`a`,`xs`,`(REVERSE cs)`,`[]`] mp_tac (GEN_ALL parse_body_MAP_print_xor)>>
  simp[]>>
  impl_tac >- (
    fs[EVERY_MEM,PULL_FORALL,AND_IMP_INTRO]>>rw[]
    >-
      metis_tac[]>>
    simp[Abbr`a`]>>
    DISJ2_TAC>>
    match_mp_tac le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    irule_at Any le_max_list>>
    simp[MEM_MAP,PULL_EXISTS]>>
    metis_tac[LESS_EQ_REFL])>>
  simp[]
QED

Theorem parse_cnf_xor_print_cnf_xor:
  EVERY (EVERY (λl. var_lit l ≠ 0)) cs ∧
  EVERY (EVERY (λl. var_lit l ≠ 0)) xs ⇒
  parse_cnf_xor (print_cnf_xor (cs,xs)) = SOME (cs,xs)
Proof
  rw[]>>
  simp[parse_cnf_xor_def]>>
  assume_tac parse_cnf_xor_toks_print_cnf_xor_toks>>
  gvs[]
QED

val _ = export_theory ();
