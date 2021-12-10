(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble pb_constraintTheory mlstringTheory mlintTheory;

val _ = new_theory "pb_check";

val _ = numLib.prefer_num();

(* TODO: move *)
Theorem lookup_spt_size:
  ∀n x a. lookup n x = SOME a ⇒ ∀f. f a < spt_size f x
Proof
  recInduct lookup_ind \\ rw []
  \\ gvs [lookup_def,spt_size_def,AllCaseEqs()]
  \\ first_x_assum (qspec_then ‘f’ assume_tac) \\ fs []
QED

Theorem MEM_list_size:
  ∀xs x. MEM x xs ⇒ ∀f. f x < list_size f xs
Proof
  Induct \\ fs [list_size_def] \\ rw [] \\ fs [] \\ res_tac
  \\ first_x_assum (qspec_then ‘f’ assume_tac) \\ fs []
QED

(* pbp = pseudo-boolean proof format
  Below, nums represent ConstraintIds, which are 1-indexed (although 0s internally work fine)
*)

(* A constraint to be added by a cutting planes proof *)
Datatype:
  constr =
  | Id num              (* Constraints can refer to earlier IDs *)
  | Add constr constr   (* Add two constraints *)
  | Mul constr num      (* Multiply by a constant factor *)
  | Div constr num      (* Divide by a constant factor *)
  | Sat constr          (* Saturation *)
  | Lit lit             (* Literal axiom lit ≥ 0 *)
  | Weak constr var     (* Addition of literal axioms until "var" disappears *)
End

(* TODO: some syntactic representation of a substitution
  This is a dummy type, unused for now*)
Type subst = ``:(bool + lit) num_map``;

Datatype:
  pbpstep =
  | Contradiction num (* Id representing a contradiction *)
  | Delete (num list) (* Ids to to delete *)
  | Polish constr     (* Adds a constraint, written in reverse polish notation *)
  | Red npbc subst (pbpstep list) (pbpstep list spt)
End

(* Red steps add the constraint npbc by contradiction,
  - subst is the witness substitution for substitution redundancy steps (currently unused)
  - pbpstep list is the "preamble" subproof
  - (pbpstep list sptree) is the indexed list of subproofs (currently unused) *)

Definition pbpstep_ok_def[simp]:
  (pbpstep_ok (Red n _ pf pfs) ⇔
    compact n ∧ EVERY pbpstep_ok pf ∧
    ∀n p. lookup n pfs = SOME p ⇒ EVERY pbpstep_ok p) ∧
  (pbpstep_ok _ ⇔ T)
Termination
  WF_REL_TAC ‘measure pbpstep_size’ \\ rw []
  \\ drule_then (qspec_then ‘list_size pbpstep_size’ mp_tac) lookup_spt_size
  \\ gvs [fetch "-" "pbpstep_size_eq"] \\ rw []
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any MEM_list_size
  \\ first_x_assum $ irule_at Any
  \\ fs []
End

(*
  The type of PB formulas represented as a finite map
  num -> pbc
*)
Type pbf = ``:npbc spt``;
Type pbp = ``:pbpstep list``;

(* Computes the LHS term of the slack of a constraint under
  a partial assignment p (list of literals) *)
Definition lslack_def:
  lslack (PBC ls num) p =
  SUM (MAP FST (FILTER (λ(a,b). ¬MEM (negate b) p) ls))
End

Definition check_contradiction_def:
  check_contradiction (PBC ls num) =
  let l = lslack (PBC ls num) [] in
    l < num
End

Definition check_polish_def:
  (check_polish fml (Id n) = lookup n fml) ∧
  (check_polish fml (Add c1 c2) =
    OPTION_MAP2 add (check_polish fml c1) (check_polish fml c2)) ∧
  (check_polish fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_polish fml c)) ∧
  (check_polish fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_polish fml c)
    else NONE) ∧
  (check_polish fml (Sat c) =
    OPTION_MAP saturate (check_polish fml c)) ∧
  (check_polish fml (Lit l) = SOME (PBC [(1,l)] 0)) ∧
  (check_polish fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_polish fml c))
End

(* The result is either:
  Unsat -> unsatisfiability proved
  Fail -> proof step failed (more errors can be added in imperative part)
  Cont (pbf,num) -> continue with pbf and next ID (input formula is sat equiv to the pbv)
*)
Datatype:
  pbpres = Unsat | Fail | Cont pbf num
End

Definition subst_fun_def:
  subst_fun (s:subst) n = lookup n s
End

Definition is_pol_con_def[simp]:
  is_pol_con (Polish _) = T ∧
  is_pol_con (Contradiction _) = T ∧
  is_pol_con _ = F
End

Definition map_opt_def:
  map_opt f LN = LN ∧
  map_opt f (LS x) = (case f x of NONE => LN | SOME a => LS a) ∧
  map_opt f (BN t1 t2) = mk_BN (map_opt f t1) (map_opt f t2) ∧
  map_opt f (BS t1 x t2) =
    case f x of
    | NONE => mk_BN (map_opt f t1) (map_opt f t2)
    | SOME a => mk_BS (map_opt f t1) a (map_opt f t2)
End

Definition check_pbpstep_def:
  (check_pbpstep (step:pbpstep) (fml:pbf) (id:num) =
   case step of
     Contradiction n =>
       (case lookup n fml of
          NONE => Fail
        | SOME c =>
            if check_contradiction c then Unsat else Fail)
   | Delete ls =>
       Cont (FOLDL (λa b. delete b a) fml ls) id
   | Polish constr =>
       (case check_polish fml constr of
          NONE => Fail
        | SOME c => Cont (insert id c fml) (id+1))
   | Red c s pf pfs =>
       (if ~EVERY is_pol_con pf then Fail else
        let fml_not_c = insert id (not c) fml in
          case check_pbpsteps pf fml_not_c (id+1) of
          | Unsat => Cont (insert id c fml) (id+1)  (* the ids are slightly off here *)
          | Fail => Fail
          | Cont fml' id' =>
              let w = subst_fun s in
              let goals = (id, subst w c) :: toAList (map_opt (subst_opt w) fml) in
              let success = EVERY (λ(n,g).
                              case lookup n pfs of
                              | NONE => F
                              | SOME steps =>
                                  let fml'_g = insert id' (not g) fml' in
                                    check_pbpsteps steps fml'_g (id'+1) = Unsat) goals in
                if success then
                  Cont (insert id c fml) (id+1)  (* the ids are slightly off here *)
                else Fail)) ∧
  (check_pbpsteps [] fml id = Cont fml id) ∧
  (check_pbpsteps (step::steps) fml id =
   case check_pbpstep step fml id of
     Cont fml' id' => check_pbpsteps steps fml' id'
   | res => res)
Termination
  WF_REL_TAC ‘measure (sum_size (pbpstep_size o FST) (list_size pbpstep_size o FST))’
  \\ fs [fetch "-" "pbpstep_size_eq"] \\ rw []
  \\ drule_then (qspec_then ‘list_size pbpstep_size’ mp_tac) lookup_spt_size
  \\ fs []
End

(* Copied from satSem: this is the set of pseudoboolean constraints *)
Theorem check_polish_correct:
  ∀n c w.
  check_polish fml n = SOME c ∧ satisfies w (range fml) ⇒
  satisfies_npbc w c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[satisfies_def,range_def]>>metis_tac[])
  >- (
    (* add case *)
    match_mp_tac add_thm>>
    metis_tac[])
 >- (
    (* multiply case *)
    match_mp_tac multiply_thm>>
    metis_tac[])
  >- (
    (* divide case *)
    match_mp_tac divide_thm>>
    metis_tac[])
  >- (
    (* saturate case *)
    match_mp_tac saturate_thm>>
    metis_tac[])
  >- (
    (* literal case *)
    EVAL_TAC)
  >- (
    (* weaken case *)
    match_mp_tac weaken_thm>>
    metis_tac[])
QED

Theorem check_polish_compact:
  ∀n c.
  (∀c. c ∈ range fml ⇒ compact c) ∧
  check_polish fml n = SOME c ⇒
  compact c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[range_def]>>metis_tac[])
  >- (
    (* add case *)
    metis_tac[compact_add])
 >- (
    (* multiply case *)
    metis_tac[compact_multiply])
  >- (
    metis_tac[compact_divide])
  >- (
    metis_tac[compact_saturate])
  >- (
    (* literal case *)
    EVAL_TAC)
  >- (
    (* weaken case *)
    metis_tac[compact_weaken])
QED

Theorem check_contradiction_unsat:
  check_contradiction c ⇒
  ¬satisfies_npbc w c
Proof
  Cases_on`c`>>
  rw[check_contradiction_def,satisfies_npbc_def,lslack_def]>>
  qmatch_asmsub_abbrev_tac`MAP FST lss`>>
  `lss = l` by
    fs[Abbr`lss`,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD]>>
  rw[]>>
  `SUM (MAP (eval_term w) l) ≤ SUM (MAP FST l)` by
      (match_mp_tac SUM_MAP_same_LE>>
      fs[EVERY_MEM,FORALL_PROD]>>
      rw[]>>
      rename1`eval_lit w r`>>
      assume_tac eval_lit_bool>>
      fs[])>>
  fs[]
QED

Theorem range_FOLDL_delete:
  ∀ls v.
  range (FOLDL (λa b. delete b a) v ls) ⊆ range v
Proof
  Induct>>rw[]>>
  first_x_assum (qspec_then`delete h v` mp_tac)>>rw[]>>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>>simp[]>>
  simp[range_delete]
QED

Theorem satisfiable_subset:
  satisfiable t ∧ s ⊆ t ⇒
  satisfiable s
Proof
  rw[satisfiable_def,SUBSET_DEF,satisfies_def]>>
  metis_tac[]
QED

Theorem implies_explode:
  a ⊨ s ⇔ ∀c. c ∈ s ⇒ a ⊨ {c}
Proof
  fs [sat_implies_def,satisfies_def]
  \\ metis_tac []
QED

Theorem unsat_iff_implies:
  ¬satisfiable (not x INSERT fml) ⇔ fml ⊨ {x}
Proof
  fs [sat_implies_def,satisfiable_def,not_thm]
  \\ metis_tac []
QED

Definition id_ok_def:
  id_ok fml id = ∀n. id ≤ n ⇒ n ∉ domain fml
End

Theorem lookup_mk_BS:
  lookup i (mk_BS t1 a t2) = lookup i (BS t1 a t2)
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ fs [mk_BS_def,lookup_def]
QED

Theorem lookup_map_opt:
  ∀n t f.
    lookup n (map_opt f t) =
    case lookup n t of
    | NONE => NONE
    | SOME x => f x
Proof
  recInduct lookup_ind \\ fs [map_opt_def,lookup_def] \\ rw []
  \\ rpt (fs [lookup_def,lookup_mk_BN,lookup_mk_BS] \\ CASE_TAC)
QED

Theorem check_pbpstep_correct:
  (∀step fml id.
     id_ok fml id ⇒
     case check_pbpstep step fml id of
     | Cont fml' id' =>
         id_ok fml' id' ∧
         (satisfiable (range fml) ⇒ satisfiable (range fml')) ∧
         ∀w. satisfies w (range fml) ∧ is_pol_con step ⇒
             satisfies w (range fml')
     | Unsat =>
         ¬ satisfiable (range fml)
     | Fail => T) ∧
  (∀steps fml id.
     id_ok fml id ⇒
     case check_pbpsteps steps fml id of
     | Cont fml' id' =>
         id_ok fml' id' ∧
         (satisfiable (range fml) ⇒ satisfiable (range fml')) ∧
         ∀w. satisfies w (range fml) ∧ EVERY is_pol_con steps ⇒
             satisfies w (range fml')
     | Unsat =>
         ¬ satisfiable (range fml)
     | Fail => T)
Proof
  ho_match_mp_tac check_pbpstep_ind \\ reverse (rpt strip_tac)
  THEN1 (rw[Once check_pbpstep_def] \\ every_case_tac \\ gvs [])
  THEN1 (rw[Once check_pbpstep_def])
  \\ Cases_on ‘∃n. step = Contradiction n’
  THEN1
   (rw[check_pbpstep_def] \\ every_case_tac \\ fs [] >>
    rw[satisfiable_def,range_def,satisfies_def]>>
    drule check_contradiction_unsat>>
    metis_tac[])
  \\ Cases_on ‘∃n. step = Delete n’
  THEN1
   (rw[check_pbpstep_def] \\ every_case_tac \\ rw []
    THEN1
     (pop_assum mp_tac
      \\ qid_spec_tac ‘fml’ \\ Induct_on ‘l’ \\ fs []
      \\ rw [] \\ first_x_assum irule \\ fs [id_ok_def,domain_delete]) >>
    drule satisfiable_subset>>
    disch_then match_mp_tac>>
    fs[range_FOLDL_delete])
  \\ Cases_on ‘∃c. step = Polish c’
  THEN1
   (rw[check_pbpstep_def] \\ every_case_tac \\ rw []
    THEN1 fs [id_ok_def] >>
    drule check_polish_correct>>
    fs[satisfiable_def,satisfies_def]>>
    ‘id ∉ domain fml’ by fs [id_ok_def]  >>
    fs [range_insert] >>
    metis_tac [])
  \\ ‘∃c s pf pfs. step = Red c s pf pfs’ by (Cases_on ‘step’ \\ fs [])
  \\ gvs []
  \\ CASE_TAC
  THEN1 (pop_assum mp_tac \\ simp [Once check_pbpstep_def,AllCaseEqs()])
  \\ rename [‘_ = Cont x1 y1’]
  \\ ‘x1 = insert id c fml ∧ y1 = id+1’ by
   (pop_assum mp_tac
    \\ simp [Once check_pbpstep_def,AllCaseEqs()]
    \\ rpt strip_tac \\ gvs [])
  \\ conj_tac THEN1 gvs [id_ok_def]
  \\ gvs []
  \\ qsuff_tac ‘c redundant_wrt (range fml)’
  THEN1
   (fs [redundant_wrt_def] \\ rw []
    \\ irule satisfiable_subset
    \\ pop_assum $ irule_at Any
    \\ rw [SUBSET_DEF] \\ imp_res_tac range_insert_2 \\ fs [])
  \\ rewrite_tac [substitution_redundancy]
  \\ qexists_tac ‘subst_fun s’ \\ fs []
  \\ pop_assum mp_tac
  \\ simp [Once check_pbpstep_def]
  \\ IF_CASES_TAC \\ fs []
  \\ ‘id ∉ domain fml’ by fs [id_ok_def]
  \\ ‘EVERY is_pol_con pf’ by fs [EVERY_MEM]
  \\ ‘id_ok (insert id (not c) fml) (id + 1)’ by fs [id_ok_def]
  \\ gvs []
  \\ TOP_CASE_TAC \\ fs []
  THEN1 (gvs [sat_implies_def,satisfiable_def,range_insert] \\ metis_tac [])
  \\ gvs [AllCaseEqs()]
  \\ strip_tac
  \\ gvs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,MEM_toAList]
  \\ ‘n ∉ domain s'’ by fs [id_ok_def]
  \\ fs [range_insert]
  \\ qpat_x_assum ‘_ ⇒ satisfiable _’ kall_tac
  \\ simp [Once implies_explode] \\ reverse (rw [])
  THEN1
   (last_x_assum (qspecl_then [‘id’,‘subst (subst_fun s) c’] mp_tac)
    \\ simp [] \\ Cases_on ‘lookup id pfs’ \\ fs []
    \\ impl_tac THEN1 fs [id_ok_def]
    \\ gvs [GSYM unsat_iff_implies]
    \\ strip_tac \\ CCONTR_TAC \\ fs []
    \\ fs [satisfiable_def]
    \\ gvs [range_insert]
    \\ metis_tac [])
  \\ gvs [GSYM unsat_iff_implies]
  \\ pop_assum mp_tac
  \\ simp [Once range_def] \\ rw []
  \\ rename [‘lookup a fml = SOME xx’]
  \\ fs [lookup_map_opt,CaseEq"option",PULL_EXISTS]
  \\ first_x_assum drule
  \\ Cases_on ‘subst_opt (subst_fun s) xx’ \\ fs []
  THEN1
   (imp_res_tac subst_opt_NONE
    \\ CCONTR_TAC \\ gvs [satisfiable_def,not_thm]
    \\ fs [satisfies_def,range_def,PULL_EXISTS]
    \\ res_tac \\ fs [])
  \\ Cases_on ‘lookup a pfs’ \\ fs []
  \\ first_x_assum (qspec_then ‘a’ mp_tac) \\ fs []
  \\ disch_then (qspec_then ‘x’ mp_tac) \\ fs []
  \\ impl_tac THEN1 fs [id_ok_def]
  \\ rpt strip_tac \\ fs []
  \\ imp_res_tac subst_opt_SOME \\ gvs []
  \\ gvs [satisfiable_def,range_insert]
  \\ metis_tac []
QED

Theorem check_pbpstep_compact:
  (∀step fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ pbpstep_ok step ∧
     check_pbpstep step fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c)) ∧
  (∀steps fml id fml' id'.
     (∀c. c ∈ range fml ⇒ compact c) ∧ EVERY pbpstep_ok steps ∧
     check_pbpsteps steps fml id = Cont fml' id' ⇒
     (∀c. c ∈ range fml' ⇒ compact c))
Proof
  ho_match_mp_tac check_pbpstep_ind \\ reverse (rw [])
  THEN1
   (ntac 2 (pop_assum mp_tac)
    \\ simp [Once check_pbpstep_def,AllCaseEqs()]
    \\ rw [] \\ fs [])
  THEN1 (fs [Once check_pbpstep_def,AllCaseEqs()]) >>
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>rw[]
  >- metis_tac[range_FOLDL_delete,SUBSET_DEF]
  >- (drule range_insert_2>>rw[]>>
      metis_tac[check_polish_compact])
  \\ imp_res_tac range_insert_2 \\ gvs []
QED

(*
  Parse an OPB file as an unnormalized formula
  For now, use the standard format where variables are named x1,...,xn
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
  Parses a literal xi, ~xi
  Note: for now, only handle default "xi" var names
*)

Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" /\ strsub s 1 = #"x" then
    OPTION_MAP Neg (mlint$fromNatString (substring s 2 (strlen s - 2)))
  else if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    OPTION_MAP Pos (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

(*
  EVAL ``parse_lit (strlit "x1")``
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
    if cmp = implode ">=" then
      SOME (GreaterEqual lhs deg)
    else if cmp = implode "=" then
      SOME (Equal lhs deg)
    else NONE
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
  (nocomment_line (INL c::cs) = (c ≠ strlit "*")) ∧
  (nocomment_line _ = T)
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  (* TODO: parse the header line ? *)
  parse_constraints nocomments []
End

(* Parse a list of strings in pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(*
  Parsing a proof file
*)

(* The stack is formed from constraints, where factors and variables are
  also encoded using Id *)
Definition parse_polish_def:
  (parse_polish (x::xs) stack =
  case x of INR n =>
    parse_polish xs (Id n :: stack)
  | INL s =>
  if s = str #"+" then
    (case stack of
      a::b::rest => parse_polish xs (Add b a::rest)
    | _ => NONE)
  else if s = str #"*" then
    (case stack of
      Id a::b::rest => parse_polish xs (Mul b a::rest)
    | _ => NONE)
  else if s = str #"d" then
    (case stack of
      Id a::b::rest => parse_polish xs (Div b a::rest)
    | _ => NONE)
  else if s = str #"s" then
    (case stack of
      a::rest => parse_polish xs (Sat a::rest)
    | _ => NONE)
  else if s = str #"w" then
    (case stack of
      Lit (Pos v)::a::rest => parse_polish xs (Weak a v::rest)
    | _ => NONE)
  else
    case parse_lit s of SOME l => parse_polish xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_polish [] [c] = SOME c) ∧
  (parse_polish [] _ = NONE)
End

Definition strip_numbers_def:
  (strip_numbers [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers (x::xs) acc =
  case x of INR n =>
    strip_numbers xs (n::acc)
  | INL _ => NONE)
End

Definition parse_pbpstep_def:
  (parse_pbpstep (first::rest) =
  if first = INL (strlit "c") then
    case rest of
      [INR id] => SOME (Contradiction id)
    | _ => NONE
  else if first = INL (strlit "d") then
    OPTION_MAP Delete (strip_numbers rest [])
  else if first = INL (strlit "p") then
    OPTION_MAP Polish (parse_polish rest [])
  else NONE) ∧
  (parse_pbpstep _ = NONE)
End

Definition parse_pbpsteps_def:
  (parse_pbpsteps [] acc = SOME (REVERSE acc)) ∧
  (parse_pbpsteps (s::ss) acc =
    case parse_pbpstep s of
      NONE => NONE
    | SOME pbpstep => parse_pbpsteps ss (pbpstep::acc))
End

Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  (* TODO: parse the header line ? *)
  parse_pbpsteps nocomments []
End

(* Exactly the same as tokenize, but parses to nums instead of ints *)
Definition tokenize_num_def:
  tokenize_num (s:mlstring) =
  case mlint$fromNatString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_num_def:
  toks_num s = MAP tokenize_num (tokens blanks s)
End

(* Parse a list of strings in pbf format *)
Definition parse_pbp_def:
  parse_pbp strs = parse_pbp_toks (MAP toks_num strs)
End

(* build an sptree for the PBF from an initial ID *)
Definition build_fml_def:
  (build_fml (id:num) [] acc = (acc,id)) ∧
  (build_fml id (s::ss) acc =
    build_fml (id+1) ss (insert id s acc))
End

val pbfraw = ``[
  strlit "* #variable= 4 #constraint= 7";
  strlit "2 ~x1 1 ~x3 >= 1;";
  strlit "1 ~x3 1 ~x5 >= 1 ;";
  strlit "1 ~x1 1 ~x5 >= 1;";
  strlit "1 ~x2 1 ~x4 1 ~x6 >= 2 ;";
  strlit "* test comment 1234567";
  strlit "+1 x1 +1 x2 >= 1 ;";
  strlit "+1 x3 +1 x4 >= 1 ;";
  strlit "+1 x5 +1 x6 >= 1 ;";
]``;

val pbf = rconc (EVAL ``THE (parse_pbf ^(pbfraw))``);

val pbpraw = ``[
  strlit"* comment";
  strlit"p 1 s";
  strlit"* comment 2";
  strlit"p 8 2 + 3 +";
  strlit"p 9 2 d";
  strlit"p 10 4 + 5 + 6 + 7 +";
  strlit"c 11";
]``;

val pbp = rconc (EVAL ``THE (parse_pbp ^(pbpraw))``);

val check = rconc (EVAL``((UNCURRY (check_pbpsteps ^(pbp))) (build_fml 1 (normalize ^(pbf)) LN))``);

val _ = export_theory ();
