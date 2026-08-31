(*
  Syntax and semantics of CNF in the DIMACS format
*)
Theory dimacs
Ancestors
  misc cnf syntax_helper mlstring mlint
Libs
  preamble

(* This file provides a surface syntax and semantics that closely resembles
  the meaning of CNF DIMACS files.

  Clauses, literals and their semantics are inherited from cnf; the DIMACS
  header, comment stripping, literal print/parse and body engine from
  syntax_helper. *)

(***
  A parser and printer for CNF in CakeML
 ***)

Definition parse_cnf_toks_def:
  parse_cnf_toks tokss = parse_dimacs_toks_gen parse_lits tokss
End

Definition parse_cnf_def:
  parse_cnf strs =
  let tokss = MAP toks strs in
  case parse_cnf_toks tokss of
    NONE => NONE
  | SOME (nvars, nclauses, ls) => SOME ls
End

(* CNF printer *)

(* The variable count declared in the printed header *)
Definition max_cnf_def:
  max_cnf cs = max_list 0 (MAP (max_list 0 o MAP var_lit) cs)
End

Definition print_cnf_def:
  print_cnf cs =
  print_header_line (max_cnf cs) (LENGTH cs) ::
  MAP (print_lits #"\n") cs
End

(***
  Round trip: parsing the printed formula returns it unchanged
 ***)

(* Every literal printed fits under the declared variable count *)
Theorem max_cnf_clause[local]:
  MEM c cs ∧ MEM l c ⇒
  var_lit l ≤ max_cnf cs
Proof
  rw[max_cnf_def]>>
  irule le_max_list>>
  simp[MEM_MAP,PULL_EXISTS]>>
  irule_at Any le_max_list>>
  simp[MEM_MAP,PULL_EXISTS]>>
  metis_tac[LESS_EQ_REFL]
QED

Theorem LIST_REL_parse_lits_print[local]:
  EVERY (EVERY nz_lit) cs ⇒
  LIST_REL (λs c. parse_lits (max_cnf cs) s = SOME c)
    (MAP toks (MAP (print_lits #"\n") cs)) cs
Proof
  strip_tac>>
  simp[LIST_REL_MAP1,LIST_REL_EL_EQN,EVERY_EL]>>
  rw[]>>
  DEP_REWRITE_TAC[parse_lits_print_lits]>>
  gvs[EVERY_EL,EVERY_MEM]>>
  metis_tac[max_cnf_clause,MEM_EL]
QED

Theorem parse_cnf_toks_print_cnf_toks:
  EVERY (EVERY nz_lit) cs
  ⇒
  ∃mv cl.
  parse_cnf_toks (MAP toks (print_cnf cs)) = SOME (mv,cl,cs)
Proof
  strip_tac>>
  simp[parse_cnf_toks_def,parse_dimacs_toks_gen_def,print_cnf_def]>>
  qmatch_goalsub_abbrev_tac`print_header_line a b`>>
  simp[Once toks_def]>>
  assume_tac print_header_line_first>>fs[]>>
  pop_assum sym_sub_tac>>
  `tokenize «p» = INL «p»` by EVAL_TAC>>
  simp[keep_line_def]>>
  simp[GSYM toks_def,parse_header_line_print_header_line]>>
  simp[FILTER_keep_line_print_lits]>>
  simp[Abbr`b`]>>
  qmatch_goalsub_abbrev_tac`parse_body_gen _ _ ss []`>>
  `LIST_REL (λs c. parse_lits a s = SOME c) ss cs` by
    simp[Abbr`ss`,Abbr`a`,LIST_REL_parse_lits_print]>>
  drule parse_body_gen_LIST_REL>>
  disch_then(qspec_then`[]` mp_tac)>>
  simp[]
QED

Theorem parse_cnf_print_cnf:
  EVERY (EVERY nz_lit) cs
  ⇒
  parse_cnf (print_cnf cs) = SOME cs
Proof
  rw[parse_cnf_def]>>
  assume_tac parse_cnf_toks_print_cnf_toks>>
  gvs[]
QED

(***
  Everything the parser accepts uses non-zero literals
 ***)

Theorem parse_cnf_toks_nz_lit:
  parse_cnf_toks tokss = SOME (v,n,cs) ⇒
  EVERY (EVERY nz_lit) cs
Proof
  strip_tac>>
  gvs[parse_cnf_toks_def,parse_dimacs_toks_gen_def,AllCaseEqs()]>>
  drule parse_body_gen_EVERY>>
  disch_then match_mp_tac>>
  simp[]>>
  metis_tac[parse_lits_nz_lit]
QED

Theorem parse_cnf_nz_lit:
  parse_cnf ls = SOME cs ⇒
  EVERY (EVERY nz_lit) cs
Proof
  strip_tac>>gvs[parse_cnf_def,AllCaseEqs()]>>
  metis_tac[parse_cnf_toks_nz_lit]
QED

(***
  Every literal the parser accepts is bounded by the declared variable count
 ***)

Theorem parse_cnf_toks_bound:
  parse_cnf_toks tokss = SOME (v,n,cs) ⇒
  EVERY (EVERY (λl. var_lit l ≤ v)) cs
Proof
  strip_tac>>
  gvs[parse_cnf_toks_def,parse_dimacs_toks_gen_def,AllCaseEqs()]>>
  drule parse_body_gen_EVERY>>
  disch_then match_mp_tac>>
  simp[]>>
  rw[]>>
  gvs[parse_lits_def,AllCaseEqs(),check_maxvar_def]
QED
