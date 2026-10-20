(*
  Syntax and semantics of CNF extended with XOR constraints
*)
Theory xlrup_cnf
Ancestors
  misc cnf ccnf dimacs syntax_helper xor mlstring mlint
Libs
  preamble

(* This file provides a surface syntax and semantics that closely resembles
  the meaning of CNF DIMACS files (or its extended variants).

  Clauses, literals and their semantics are inherited from cnf; the DIMACS
  header, comment stripping, literal print/parse and body engine from
  syntax_helper; XOR constraints from xor.

  BNN constraints are part of the wider format but are not supported here. *)

(***
  Semantics of formulas sharing an assignment.
 ***)
Type fml = ``:num clause list # cmsxor list``;

Definition sat_fml_def:
  sat_fml w ((fc,fx):fml) ⇔
    satisfies_cnf w (set fc) ∧
    satisfies_xfml w (set fx)
End

Definition sols_def:
  sols f = {w | sat_fml w f}
End

(***
  A parser and printer for extended CNF in CakeML
 ***)

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

Datatype:
  cnf_ext =
    Clause (num clause)
  | Cmsxor cmsxor
End

Definition parse_line_def:
  parse_line maxvar xs =
  (case parse_lits maxvar xs of
    SOME c => SOME (Clause c)
  | NONE =>
  (case parse_xor maxvar xs of
    SOME x => SOME (Cmsxor x)
  | NONE => NONE))
End

(* Partition the parsed lines, keeping each kind in the order it was read *)
Definition split_cnf_ext_def:
  (split_cnf_ext [] = ([],[])) ∧
  (split_cnf_ext (l::ls) =
    let (cs,xs) = split_cnf_ext ls in
    case l of
      Clause c => (c::cs,xs)
    | Cmsxor x => (cs,x::xs))
End

Definition parse_cnf_ext_toks_def:
  parse_cnf_ext_toks tokss =
  case parse_dimacs_toks_gen parse_line tokss of
    NONE => NONE
  | SOME (vars,ncx,ls) =>
    let (cs,xs) = split_cnf_ext ls in
      SOME (vars,ncx,cs,xs)
End

Definition parse_cnf_ext_def:
  parse_cnf_ext strs =
  let tokss = MAP toks strs in
  case parse_cnf_ext_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

val cnf_ext_raw = ``[
  «c this is a comment»;
  «p cnf 15 8 »;
  «    1  4 0»;
  «x1  -5 0»;
  «c this is a comment»;
  «    2  4 0»;
  «    2  5 0»;
  «x  -3  4 0»;
  «    3  5 0»;
  «-1 -2 -3 0»;
  «c this is a comment»;
  «   -4 -5 0»;
  ]``;

(* Comments are skipped, and the XOR lines are split out from the clauses *)
Theorem parse_cnf_ext_test[local]:
  parse_cnf_ext ^(cnf_ext_raw) =
  SOME
    ([[Pos 1; Pos 4]; [Pos 2; Pos 4]; [Pos 2; Pos 5]; [Pos 3; Pos 5];
      [Neg 1; Neg 2; Neg 3]; [Neg 4; Neg 5]],
     [[Pos 1; Neg 5]; [Neg 3; Pos 4]])
Proof
  EVAL_TAC
QED

(* CNF ext printer *)

Definition print_xor_def:
  print_xor xs = «x » ^ print_lits (#"\n") xs
End

(* The variable count declared in the printed header *)
Definition max_cnf_ext_def:
  max_cnf_ext (cs,xs) = MAX (max_cnf cs) (max_cnf xs)
End

Definition print_cnf_ext_def:
  print_cnf_ext (cs,xs) =
  let len = LENGTH cs + LENGTH xs in
  print_header_line (max_cnf_ext (cs,xs)) len ::
  MAP (print_lits #"\n") cs ++ MAP print_xor xs
End

(* The printer reprints the clauses first, then the XORs, under a header
  whose variable count is recomputed from the formula *)
Theorem print_cnf_ext_test[local]:
  OPTION_MAP print_cnf_ext (parse_cnf_ext ^(cnf_ext_raw)) =
  SOME
    [«p cnf 5 8\n»; «1 4 0\n»; «2 4 0\n»; «2 5 0\n»; «3 5 0\n»;
     «-1 -2 -3 0\n»; «-4 -5 0\n»; «x 1 -5 0\n»; «x -3 4 0\n»]
Proof
  EVAL_TAC
QED

(***
  Round trip: parsing the printed formula returns it unchanged
 ***)

(* The XOR line tag is neither a blank nor a digit *)
Theorem blanks_isDigit_x[simp]:
  ¬blanks #"x" ∧ ¬isDigit #"x"
Proof
  EVAL_TAC
QED

Theorem fix_hd_toks:
  s = strlit [c;#" "] ∧ ¬blanks c ∧ ¬isDigit c ⇒
  fix_hd c (toks (s ^ rest)) =
  SOME (toks rest)
Proof
  rw[toks_def]>>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  qmatch_goalsub_abbrev_tac`aa ^ bb`>>
  `aa = strlit[c] ^ « »` by
    (fs[Abbr`aa`]>>EVAL_TAC)>>
  rw[]>>
  DEP_ONCE_REWRITE_TAC[tokens_unchanged]>>
  simp[tokenize_def]>>
  EVAL_TAC>>gvs[isDigit_def,fix_hd_def]
QED

Theorem parse_xor_print_xor:
  EVERY nz_lit ys ∧
  EVERY (λl. var_lit l ≤ maxvar) ys
  ⇒
  parse_xor maxvar (toks (print_xor ys)) = SOME ys
Proof
  rw[parse_xor_def,print_xor_def]>>
  DEP_REWRITE_TAC[fix_hd_toks]>>
  CONJ_TAC >- EVAL_TAC>>
  simp[parse_lits_print_lits]
QED

Theorem FILTER_keep_line_print_xor:
  FILTER keep_line
    (MAP toks (MAP print_xor ls)) =
    (MAP toks (MAP print_xor ls))
Proof
  simp[FILTER_EQ_ID,EVERY_MAP,EVERY_MEM]>>
  rw[]>>
  simp[print_xor_def]>>
  EVAL_TAC
QED

Theorem parse_lits_print_xor:
  parse_lits maxvar (toks (print_xor xs)) = NONE
Proof
  rw[parse_lits_def,print_xor_def,toks_def,parse_until_zero_def]>>
  `«x » = «x» ^ « »` by EVAL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  `blanks #" " ∧ toString #" " = « »` by EVAL_TAC>>
  drule mlstringTheory.tokens_append>>simp[]>>
  rw[]>>
  EVAL_TAC>>
  rename1`_::rest`>>
  Cases_on`rest`>> simp[parse_until_zero_aux_def]
QED

Theorem parse_line_print_lits:
  EVERY nz_lit c ∧
  EVERY (λl. var_lit l ≤ maxvar) c ⇒
  parse_line maxvar (toks (print_lits #"\n" c)) = SOME (Clause c)
Proof
  rw[parse_line_def]>>
  DEP_REWRITE_TAC[parse_lits_print_lits]>>
  simp[]
QED

Theorem parse_line_print_xor:
  EVERY nz_lit x ∧
  EVERY (λl. var_lit l ≤ maxvar) x ⇒
  parse_line maxvar (toks (print_xor x)) = SOME (Cmsxor x)
Proof
  rw[parse_line_def,parse_lits_print_xor]>>
  DEP_REWRITE_TAC[parse_xor_print_xor]>>
  simp[]
QED

Theorem split_cnf_ext_APPEND:
  ∀l1 l2.
  split_cnf_ext (l1 ++ l2) =
  (let (c1,x1) = split_cnf_ext l1 in
   let (c2,x2) = split_cnf_ext l2 in
   (c1++c2,x1++x2))
Proof
  Induct>>rw[split_cnf_ext_def]>>
  rpt(pairarg_tac>>gvs[])>>
  every_case_tac>>gvs[]
QED

Theorem split_cnf_ext_MAP_Clause:
  ∀cs. split_cnf_ext (MAP Clause cs) = (cs,[])
Proof
  Induct>>rw[split_cnf_ext_def]
QED

Theorem split_cnf_ext_MAP_Cmsxor:
  ∀xs. split_cnf_ext (MAP Cmsxor xs) = ([],xs)
Proof
  Induct>>rw[split_cnf_ext_def]
QED

Theorem split_cnf_ext_EVERY_Clause:
  ∀ls cs xs.
  split_cnf_ext ls = (cs,xs) ∧
  EVERY (λcx. ∀c. cx = Clause c ⇒ P c) ls ⇒
  EVERY P cs
Proof
  Induct>>simp[split_cnf_ext_def]>>
  rpt gen_tac>>
  pairarg_tac>>simp[]>>
  Cases_on`h`>>simp[]>>
  strip_tac>>gvs[]>>
  metis_tac[]
QED

(* Every literal printed fits under the declared variable count *)
Theorem max_cnf_ext_clause[local]:
  MEM c cs ∧ MEM l c ⇒
  var_lit l ≤ max_cnf_ext (cs,xs)
Proof
  rw[max_cnf_ext_def]>>
  drule_all max_cnf_clause>>
  simp[]
QED

Theorem max_cnf_ext_xor[local]:
  MEM x xs ∧ MEM l x ⇒
  var_lit l ≤ max_cnf_ext (cs,xs)
Proof
  rw[max_cnf_ext_def]>>
  drule_all max_cnf_clause>>
  simp[]
QED

Theorem LIST_REL_parse_line_print[local]:
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs ⇒
  LIST_REL (λs c. parse_line (max_cnf_ext (cs,xs)) s = SOME c)
    (MAP toks (MAP (print_lits #"\n") cs) ++ MAP toks (MAP print_xor xs))
    (MAP Clause cs ++ MAP Cmsxor xs)
Proof
  strip_tac>>
  rpt (irule_at Any EVERY2_APPEND_suff)>>
  simp[LIST_REL_MAP1,LIST_REL_MAP2,LIST_REL_EL_EQN,EVERY_EL]>>
  rw[]
  >- (
    DEP_REWRITE_TAC[parse_line_print_lits]>>
    gvs[EVERY_EL,EVERY_MEM]>>
    metis_tac[max_cnf_ext_clause,MEM_EL])>>
  DEP_REWRITE_TAC[parse_line_print_xor]>>
  gvs[EVERY_EL,EVERY_MEM]>>
  metis_tac[max_cnf_ext_xor,MEM_EL]
QED

Theorem parse_cnf_ext_toks_print_cnf_ext_toks:
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs
  ⇒
  ∃mv cl.
  parse_cnf_ext_toks (MAP toks (print_cnf_ext (cs,xs))) =
    SOME (mv,cl,cs,xs)
Proof
  strip_tac>>
  simp[parse_cnf_ext_toks_def,parse_dimacs_toks_gen_def,print_cnf_ext_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize «p» = INL «p»` by EVAL_TAC>>
  simp[keep_line_def]>>
  simp[GSYM toks_def,parse_header_line_print_header_line]>>
  simp[FILTER_APPEND,FILTER_keep_line_print_xor,
    FILTER_keep_line_print_lits]>>
  simp[Abbr`b`]>>
  qmatch_goalsub_abbrev_tac`parse_body_gen _ _ ss []`>>
  `LIST_REL (λs c. parse_line a s = SOME c) ss
    (MAP Clause cs ++ MAP Cmsxor xs)` by
    simp[Abbr`ss`,Abbr`a`,LIST_REL_parse_line_print]>>
  drule parse_body_gen_LIST_REL>>
  disch_then(qspec_then`[]` mp_tac)>>
  simp[]>>
  disch_then kall_tac>>
  `LENGTH ss = LENGTH cs + LENGTH xs` by
    simp[Abbr`ss`]>>
  simp[split_cnf_ext_APPEND,split_cnf_ext_MAP_Clause,
    split_cnf_ext_MAP_Cmsxor]
QED

Theorem parse_cnf_ext_print_cnf_ext:
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs
  ⇒
  parse_cnf_ext (print_cnf_ext (cs,xs)) = SOME (cs,xs)
Proof
  rw[parse_cnf_ext_def]>>
  assume_tac parse_cnf_ext_toks_print_cnf_ext_toks>>
  gvs[]
QED

(***
  Everything the parser accepts uses non-zero literals
 ***)

Definition nz_cnf_ext_def:
  (nz_cnf_ext (Clause c) ⇔ EVERY nz_lit c) ∧
  (nz_cnf_ext (Cmsxor x) ⇔ EVERY nz_lit x)
End

Theorem parse_line_nz_cnf_ext:
  parse_line v h = SOME cx ⇒
  nz_cnf_ext cx
Proof
  rw[parse_line_def]>>
  gvs[AllCaseEqs(),nz_cnf_ext_def]
  >- (
    gvs[parse_xor_def,AllCaseEqs()]>>
    metis_tac[parse_lits_nz_lit])>>
  metis_tac[parse_lits_nz_lit]
QED

Theorem split_cnf_ext_nz:
  ∀ls cs xs.
  split_cnf_ext ls = (cs,xs) ∧
  EVERY nz_cnf_ext ls ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs
Proof
  Induct>>rw[split_cnf_ext_def]>>
  rpt(pairarg_tac>>gvs[])>>
  Cases_on`h`>>gvs[nz_cnf_ext_def]
QED

Theorem parse_cnf_ext_toks_nz_lit:
  parse_cnf_ext_toks tokss = SOME (v,n,cs,xs) ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs
Proof
  strip_tac>>
  gvs[parse_cnf_ext_toks_def,AllCaseEqs(),parse_dimacs_toks_gen_def]>>
  rpt(pairarg_tac>>gvs[])>>
  qmatch_asmsub_abbrev_tac`parse_body_gen parse_line _ _ [] = SOME body`>>
  `EVERY nz_cnf_ext body` by (
    drule parse_body_gen_EVERY>>
    disch_then match_mp_tac>>
    simp[]>>
    metis_tac[parse_line_nz_cnf_ext])>>
  drule split_cnf_ext_nz>>
  simp[]
QED

Theorem parse_cnf_ext_nz_lit:
  parse_cnf_ext ls = SOME (cs,xs) ⇒
  EVERY (EVERY nz_lit) cs ∧
  EVERY (EVERY nz_lit) xs
Proof
  strip_tac>>gvs[parse_cnf_ext_def,AllCaseEqs()]>>
  metis_tac[parse_cnf_ext_toks_nz_lit]
QED

(* Every clause the parser accepts fits under the declared variable count *)
Theorem parse_cnf_ext_toks_bound:
  parse_cnf_ext_toks tokss = SOME (vars,ncx,cacc,xacc) ⇒
  EVERY (EVERY (λl. var_lit l ≤ vars)) cacc
Proof
  rw[parse_cnf_ext_toks_def]>>
  gvs[AllCaseEqs(),parse_dimacs_toks_gen_def]>>
  pairarg_tac>>gvs[]>>
  drule_at Any split_cnf_ext_EVERY_Clause>>
  disch_then irule>>
  drule parse_body_gen_EVERY>>
  disch_then irule>>
  rw[]>>
  gvs[parse_line_def,AllCaseEqs(),parse_lits_def,check_maxvar_def]
QED
