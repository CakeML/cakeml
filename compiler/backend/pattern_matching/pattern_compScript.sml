(*
  A simple pattern compiler that moves constant patterns upwards,
  checks for exhaustiveness, and then converts the pattern rows into
  an if-then-else decision tree.
*)
open preamble astTheory semanticPrimitivesTheory pattern_commonTheory
     pattern_semanticsTheory;

val _ = new_theory "pattern_comp";

val _ = set_grammar_ancestry
  ["pattern_common", "semanticPrimitives", "pattern_semantics"];


(* moving constant patterns up *)

Definition is_const_row_def:
  is_const_row (Cons _ pats, x) = NULL pats /\
  is_const_row _ = F
End

Definition is_Any_def:
  is_Any Any = T /\
  is_Any (Or p1 p2) = (is_Any p1 \/ is_Any p2) /\
  is_Any _ = F
End

Definition is_Or_row_def:
  is_Or_row (Or p1 p2,_) = T /\
  is_Or_row _ = F
End

Definition take_until_Any_def:
  take_until_Any [] = [] /\
  take_until_Any ((p,x)::xs) =
    if is_Any p then [(p,x)] else (p,x)::take_until_Any xs
End

Definition move_const_up_def:
  move_const_up rows =
    let new_rows = take_until_Any rows in
      if 5 <= LENGTH new_rows \/ EXISTS is_Or_row new_rows then
        new_rows (* long pattern rows should not be changed *)
      else
        FILTER is_const_row new_rows ++
        FILTER (\x. ~is_const_row x) new_rows
End

Theorem is_Any_pmatch:
  !p. is_Any p ==> pmatch refs p v <> PMatchFailure
Proof
  ho_match_mp_tac is_Any_ind \\ fs [is_Any_def] \\ fs [pmatch_def]
  \\ rw [] \\ every_case_tac \\ fs []
QED

Theorem match_take_until_Any:
  !rows.
    match refs rows v <> NONE ==>
    match refs (take_until_Any rows) v = match refs rows v
Proof
  Induct \\ fs [take_until_Any_def,FORALL_PROD]
  \\ fs [match_def] \\ rw []
  THEN1
   (fs [pmatch_def,match_def,CaseEq"option"]
    \\ ‘pmatch refs p_1 v <> PMatchFailure’ by metis_tac [is_Any_pmatch]
    \\ every_case_tac \\ fs [])
  \\ fs [pmatch_def,match_def,CaseEq"pmatchResult"]
  \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem match_append:
  !xs ys refs v.
    match refs (xs ++ ys) v =
    case match refs xs v of
    | NONE => NONE
    | SOME (MatchSuccess e) => if match refs ys v <> NONE
                               then SOME (MatchSuccess e) else NONE
    | SOME _ => match refs ys v
Proof
  Induct \\ fs [match_def,FORALL_PROD]
  \\ rw [] \\ every_case_tac \\ fs []
QED

Triviality pmatchResult_case_NONE:
  (case x of PMatchSuccess => NONE
           | PMatchFailure => NONE
           | PTypeFailure => K NONE NONE) = NONE
Proof
  Cases_on ‘x’ \\ fs []
QED

Theorem pmatchResult_case_NONE = pmatchResult_case_NONE |> REWRITE_RULE [K_THM];

Theorem is_const_row_lemma:
  (∀t. v ≠ Term t []) /\ is_const_row (p_1,p_2) /\
  pmatch refs p_1 v <> PTypeFailure ==>
  pmatch refs p_1 v = PMatchFailure
Proof
  Cases_on ‘p_1’ \\ fs [is_const_row_def]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘v’ \\ fs [pmatch_def]
  \\ Cases_on ‘l’ \\ fs [pmatch_def]
  \\ Cases_on ‘o'’ \\ Cases_on ‘o''’ \\ fs [pmatch_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ fs [pmatch_def,CaseEq"bool"]
QED

Theorem not_is_const_row:
  ~is_const_row (p,x) /\ ~is_Or_row (p,x) /\ ~is_Any p ==>
  pmatch refs p (Term t []) ≠ PMatchSuccess
Proof
  Cases_on ‘p’ \\ fs [pmatch_def,is_const_row_def,is_Or_row_def,is_Any_def]
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘o'’ \\ Cases_on ‘t’ \\ fs [pmatch_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ fs [pmatch_def]
  \\ every_case_tac \\ fs []
QED

Theorem EVERY_take_until_Any:
  !rows. EVERY (\(x,y). ~is_Any x) (TL (REVERSE (take_until_Any (rows :(pat # num) list))))
Proof
  Induct
  \\ fs [take_until_Any_def,FORALL_PROD] \\ rw []
  \\ rename [‘xs ++ _’] \\ Cases_on ‘xs’ \\ fs []
QED

Theorem matdch_FILTER_NOT_NONE:
  !xs. match refs xs v ≠ NONE ==>
       match refs (FILTER P xs) v ≠ NONE
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ fs [match_def] \\ every_case_tac \\ fs []
QED

Theorem match_move_const_up:
  match refs rows v <> NONE ==>
  match refs (move_const_up rows) v = match refs rows v
Proof
  rw [move_const_up_def]
  \\ drule match_take_until_Any
  \\ assume_tac (SPEC_ALL EVERY_take_until_Any)
  \\ rename [‘_ xx v = _’] \\ fs []
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ qpat_x_assum ‘match refs xx v ≠ NONE’ mp_tac
  \\ qpat_x_assum ‘EVERY _ _’ mp_tac
  \\ qpat_x_assum ‘EVERY _ _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp [match_def,match_append]
  \\ reverse (Cases_on ‘?t. v = Term t []’)
  THEN1
   (disch_then kall_tac
    \\ disch_then kall_tac
    \\ strip_tac
    \\ ‘match refs (FILTER is_const_row xx) v = SOME MatchFailure’ by
         (Induct_on ‘xx’ \\ fs [match_def,FORALL_PROD]
          \\ rw [] \\ fs [match_def]
          \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
          \\ Cases_on ‘match refs xx v’ \\ fs []
          \\ Cases_on ‘p_1’ \\ fs [is_const_row_def]
          \\ Cases_on ‘l’ \\ fs []
          \\ Cases_on ‘v’ \\ fs [pmatch_def]
          \\ Cases_on ‘l’ \\ fs []
          \\ Cases_on ‘o'’ \\ Cases_on ‘o''’ \\ fs [pmatch_def]
          \\ Cases_on ‘x'’ \\ Cases_on ‘x''’ \\ fs [pmatch_def,CaseEq"bool"])
    \\ fs [] \\ pop_assum kall_tac
    \\ Induct_on ‘xx’ \\ fs [match_def,FORALL_PROD]
    \\ Cases_on ‘match refs xx v = NONE’ \\ fs []
    THEN1 (rw [] \\ every_case_tac \\ fs [])
    \\ reverse (rw []) \\ fs [match_def]
    \\ Cases_on ‘pmatch refs p_1 v = PTypeFailure’ \\ fs []
    \\ imp_res_tac is_const_row_lemma \\ fs [])
  \\ fs [] \\ rveq \\ rw []
  \\ Cases_on ‘match refs (FILTER is_const_row xx) (Term t [])’
  \\ rfs [matdch_FILTER_NOT_NONE]
  \\ ‘xx = [] ∨ ∃x l. xx = SNOC x l’ by metis_tac [SNOC_CASES]
  THEN1 (fs [] \\ CASE_TAC \\ fs [])
  \\ fs [REVERSE_APPEND] \\ rveq \\ fs [EVERY_REVERSE]
  \\ Induct_on ‘l’
  THEN1 (fs [] \\ rw [] \\ fs [match_def] \\ CASE_TAC \\ fs [])
  \\ fs [FORALL_PROD]
  \\ rw [] \\ fs []
  THEN1
   (fs [match_def] \\ Cases_on ‘pmatch refs p_1 (Term t [])’ \\ fs []
    \\ Cases_on ‘match refs (l ++ [x']) (Term t [])’ \\ fs []
    \\ Cases_on ‘match refs (FILTER is_const_row (l ++ [x'])) (Term t [])’ \\ fs []
    \\ rveq \\ fs [])
  \\ fs [match_def]
  \\ qsuff_tac ‘pmatch refs p_1 (Term t []) <> PMatchSuccess’
  THEN1 (Cases_on ‘pmatch refs p_1 (Term t [])’ \\ fs [])
  \\ imp_res_tac not_is_const_row \\ fs []
QED


(* simple check for exhaustiveness, either:
    - one row is a trivially exhaustive pattern (exh_pat)
    - one top-level constructor (and its simblings)
      with only trivially exhaustive subpatterns
*)

Definition exh_pat_def:
  exh_pat Any = T /\
  exh_pat (Or p1 p2) = (exh_pat p1 \/ exh_pat p2) /\
  exh_pat (Cons NONE ps) = EVERY exh_pat ps /\
  exh_pat _ = F
Termination
  WF_REL_TAC ‘measure pat_size’ \\ fs []
  \\ Induct \\ fs [] \\ rw [] \\ res_tac \\ fs [pat_size_def]
End

Definition cons_exh_pat_def:
  cons_exh_pat (Cons t ps) = EVERY exh_pat ps /\
  cons_exh_pat _ = F
End

Definition sib_exists_def:
  sib_exists [] (t:num,l:num) = F /\
  sib_exists ((Cons (SOME (t1,_)) ps) :: xs) (t,l) =
    ((if t = t1 /\ l = LENGTH ps then T else sib_exists xs (t,l))) /\
  sib_exists _ _ = F
End

Definition exh_rows_def:
  exh_rows rows =
    let ps = MAP FST rows in
      if EXISTS exh_pat ps then T else
        EVERY cons_exh_pat ps /\
        case ps of
        | ((Cons (SOME (t,SOME sibs)) _) :: rest) => EVERY (sib_exists ps) sibs
        | _ => F
End

Theorem exh_pat_thm:
  !p v. exh_pat p ==> pmatch refs p v <> PMatchFailure
Proof
  ho_match_mp_tac exh_pat_ind \\ rw []
  \\ fs [pmatch_def,exh_pat_def] \\ rfs []
  THEN1 (every_case_tac \\ fs [] \\ rfs [])
  THEN1 (every_case_tac \\ fs [] \\ rfs [])
  \\ Cases_on ‘v’ \\ fs [pmatch_def]
  \\ Cases_on ‘o'’ \\ fs [pmatch_def]
  \\ rpt (pop_assum mp_tac)
  \\ qid_spec_tac ‘l’
  \\ Induct_on ‘ps’ \\ Cases_on ‘l’ \\ fs [pmatch_def]
  \\ fs [EVERY_MEM] \\ rw []
  \\ pop_assum mp_tac
  \\ first_assum (qspec_then ‘h'’ mp_tac)
  \\ rewrite_tac []
  \\ disch_then drule
  \\ disch_then (qspec_then ‘h’ assume_tac)
  \\ Cases_on ‘pmatch refs h' h’ \\ fs []
QED

Theorem exh_pat_pmatch_list:
  ∀l l'. EVERY exh_pat l /\ LENGTH l = LENGTH l' ==>
         pmatch_list refs l l' <> PMatchFailure
Proof
  Induct \\ fs [pmatch_def,FORALL_PROD]
  \\ rw [] \\ rename [‘_ = LENGTH xs’] \\ Cases_on ‘xs’  \\ fs []
  \\ fs [pmatch_def]
  \\ drule exh_pat_thm
  \\ disch_then (qspecl_then [‘refs’,‘h'’] assume_tac)
  \\ rename [‘LENGTH ts = _’]
  \\ first_x_assum (qspec_then ‘t’ mp_tac)
  \\ every_case_tac \\ fs []
QED

Theorem pmatch_list_LENGTH:
  !ps vs. pmatch_list refs ps vs ≠ PTypeFailure ==> LENGTH vs = LENGTH ps
Proof
  Induct \\ Cases_on ‘vs’ \\ fs [pmatch_def]
  \\ fs [CaseEq"pmatchResult"] \\ rw [] \\ res_tac \\ fs []
  \\ Cases_on ‘pmatch refs h' h’ \\ fs []
QED

Theorem exh_rows_thm:
  match refs rows v <> NONE /\ exh_rows rows ==>
  match refs rows v <> SOME MatchFailure
Proof
  rw [exh_rows_def]
  THEN1
   (Induct_on ‘rows’ \\ fs [match_def,FORALL_PROD] \\ rw []
    THEN1
     (drule exh_pat_thm
      \\ disch_then (qspecl_then [‘refs’,‘v’] assume_tac)
      \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
      \\ CASE_TAC \\ fs [])
    \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
    \\ TRY CASE_TAC \\ fs [])
  \\ Cases_on ‘MAP FST rows’ \\ fs []
  \\ Cases_on ‘h’ \\ fs []
  \\ Cases_on ‘o'’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘r’ \\ fs []
  \\ qabbrev_tac ‘ts = Cons (SOME (q,SOME x)) l::t’
  \\ Cases_on ‘rows’ \\ fs [] THEN1 fs [Abbr‘ts’]
  \\ PairCases_on ‘h’ \\ fs [Abbr‘ts’]
  \\ rveq \\ fs []
  \\ fs [match_def]
  \\ Cases_on ‘pmatch refs (Cons (SOME (q,SOME x)) l) v’ \\ fs []
  THEN1 (TOP_CASE_TAC \\ fs [])
  \\ Cases_on ‘v’ \\ fs [pmatch_def]
  \\ Cases_on ‘o'’ \\ fs [pmatch_def]
  \\ fs [CaseEq"bool"] \\ rveq \\ fs []
  THEN1 (fs [cons_exh_pat_def] \\ metis_tac [exh_pat_pmatch_list])
  \\ fs [is_sibling_def]
  \\ fs [EVERY_MEM]
  \\ first_x_assum drule
  \\ fs [sib_exists_def] \\ rw []
  \\ Induct_on ‘t'’ \\ fs [sib_exists_def]
  \\ fs [FORALL_PROD] \\ rw []
  \\ fs [match_def]
  \\ Cases_on ‘pmatch refs p_1 (Term (SOME x') l')’ \\ fs []
  \\ TRY (TOP_CASE_TAC \\ fs [] \\ NO_TAC)
  \\ Cases_on ‘p_1’ \\ fs [sib_exists_def]
  \\ Cases_on ‘o'’ \\ fs [sib_exists_def]
  \\ Cases_on ‘x''’ \\ fs [sib_exists_def] \\ rveq \\ fs []
  \\ rfs [pmatch_def]
  \\ rename [‘Cons (SOME (q1,r1)) l1’]
  \\ first_x_assum (qspec_then ‘Cons (SOME (q1,r1)) l1’ assume_tac)
  \\ fs [cons_exh_pat_def]
  \\ imp_res_tac exh_pat_pmatch_list
  \\ rename [‘pmatch_list refs t5 t6 = PMatchFailure’]
  \\ rpt (first_x_assum (qspec_then ‘t6’ assume_tac))
  \\ rfs [] \\ fs []
QED

(* replace last pattern with Any (used if rows are exhaustive) *)

Definition insert_Any_def:
  insert_Any [] = [] /\
  insert_Any [(p,x)] = [(Any,x)] /\
  insert_Any (x::xs) = x :: insert_Any xs
End

Theorem match_insert_Any:
  !rows.
    match refs rows v <> NONE ==>
    match refs (insert_Any rows) v <> NONE /\
    (match refs rows v <> SOME MatchFailure ==>
     match refs (insert_Any rows) v = match refs rows v)
Proof
  Induct \\ fs [match_def,insert_Any_def]
  \\ Cases_on ‘rows’ \\ Cases
  \\ fs [insert_Any_def]
  \\ fs [match_def,pmatch_def,CaseEq"pmatchResult"]
  \\ Cases_on ‘pmatch refs q v’ \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
QED


(* turning the pattern rows into code *)

Definition is_True_def:
  is_True True = T /\
  is_True _ = F
End

Definition mk_Disj_def:
  mk_Disj p q = if is_True p \/ is_True q then True else Disj p q
End

Definition mk_Conj_def:
  mk_Conj p q =
    if is_True p then q else
    if is_True q then p else Conj p q
End

Definition mk_If_def:
  mk_If g p q = if is_True g then p else If g p q
End

Definition get_pos_def:
  get_pos [] = EmptyPos /\
  get_pos (n::ns) = Pos n (get_pos ns)
End

Definition pat_to_guard_def:
  pat_to_guard l Any = True /\
  pat_to_guard l (Lit r) = PosTest (get_pos (REVERSE l)) (LitEq r) /\
  pat_to_guard l (Cons NONE pats) = pats_to_guard l 0 pats /\
  pat_to_guard l (Cons (SOME (t,_)) pats) =
    mk_Conj (PosTest (get_pos (REVERSE l))
      (TagLenEq t (LENGTH pats))) (pats_to_guard l 0 pats) /\
  pat_to_guard l (Or p1 p2) = mk_Disj (pat_to_guard l p1) (pat_to_guard l p2) /\
  pat_to_guard l (Ref p) = pat_to_guard (0::l) p /\
  pats_to_guard l k [] = True /\
  pats_to_guard l k [p] = pat_to_guard (k::l) p /\
  pats_to_guard l k (p::ps) = mk_Conj (pat_to_guard (k::l) p) (pats_to_guard l (k+1) ps)
Termination
  WF_REL_TAC ‘measure (\x. case x of INL (_,p) => pat_size p
                           | INR (_,k,p) => pat1_size p)’
End

Definition pats_to_code_def:
  pats_to_code [] = Fail /\
  pats_to_code ((p,x)::rows) =
    mk_If (pat_to_guard [] p) (Leaf x) (pats_to_code rows)
End

Definition walk_def:
  walk [] x refs = SOME x /\
  walk (n::ns) x refs =
    (case x of
     | (Term t xs) => (if n < LENGTH xs then walk ns (EL n xs) refs else NONE)
     | (RefPtr p) => (if n <> 0 then NONE else
                      case FLOOKUP refs p of SOME y => walk ns y refs | _ => NONE)
     | _ => NONE)
End

Definition walk_list_def:
  walk_list ns x refs =
    case walk ns x refs of SOME (Term _ vs) => SOME vs | _ => NONE
End

Theorem app_pos_Pos:
  !n xs.
    n < LENGTH xs ==>
    app_pos refs (Pos n x) (Term t xs) = app_pos refs x (EL n xs)
Proof
  Induct \\ Cases \\ fs [app_pos_def]
QED

Theorem walk_thm:
  !l v refs x.
    walk l v refs = SOME x ==>
    app_pos refs (get_pos l) v = SOME x
Proof
  Induct \\ fs [walk_def,get_pos_def,app_pos_def]
  \\ fs [CaseEq"option",CaseEq"bool",CaseEq"term"]
  \\ rw [] \\ fs [] \\ rw []
  \\ fs [app_pos_Pos] \\ fs [app_pos_def]
QED

Theorem walk_append:
  !xs ys v refs.
    walk (xs ++ ys) v refs =
    case walk xs v refs of
    | NONE => NONE
    | SOME v => walk ys v refs
Proof
  Induct \\ fs [walk_def]
  \\ Cases_on ‘v’ \\ fs [] \\ rw []
  \\ CASE_TAC \\ fs []
QED

Triviality is_True_thm:
  is_True t <=> t = True
Proof
  Cases_on `t` \\ fs [is_True_def]
QED

Triviality dt_eval_guard_mk_Conj:
  dt_eval_guard refs v (mk_Conj p q) =
  dt_eval_guard refs v (Conj p q)
Proof
  rw [mk_Conj_def] \\ fs [is_True_thm,dt_eval_guard_def]
  \\ rveq \\ fs [] \\ every_case_tac \\ fs []
QED

Theorem dt_eval_guard_pat_to_guard:
  (!l p x.
    pmatch refs p x <> PTypeFailure /\
    walk (REVERSE l) v refs = SOME x ==>
    dt_eval_guard refs v (pat_to_guard l p) =
      SOME (pmatch refs p x = PMatchSuccess)) /\
  (!l k ps xs ys.
    pmatch_list refs ps xs <> PTypeFailure /\ LENGTH ys = k /\
    walk_list (REVERSE l) v refs = SOME (ys ++ xs) /\ LENGTH xs = LENGTH ps ==>
    dt_eval_guard refs v (pats_to_guard l k ps) =
      SOME (pmatch_list refs ps xs = PMatchSuccess))
Proof
  ho_match_mp_tac pat_to_guard_ind \\ rw []
  THEN1 fs [pmatch_def,pat_to_guard_def,dt_eval_guard_def]
  THEN1
   (Cases_on ‘x’ \\ fs [pmatch_def,CaseEq"bool"]
    \\ fs [pat_to_guard_def,dt_eval_guard_def]
    \\ imp_res_tac walk_thm \\ fs [] \\ EVAL_TAC
    \\ Cases_on ‘r’ \\ Cases_on ‘l'’ \\ fs [lit_same_type_def])
  THEN1
   (Cases_on ‘x’ \\ fs [pmatch_def] \\ Cases_on ‘o'’ \\ fs [pmatch_def]
    \\ fs [walk_list_def,pat_to_guard_def]
    \\ imp_res_tac pmatch_list_LENGTH \\ fs [])
  THEN1
   (Cases_on ‘x’ \\ fs [pmatch_def] \\ Cases_on ‘o'’ \\ fs [pmatch_def]
    \\ fs [walk_list_def,pat_to_guard_def]
    \\ imp_res_tac pmatch_list_LENGTH \\ fs [dt_eval_guard_mk_Conj]
    \\ fs [CaseEq"bool"] \\ rveq \\ fs [dt_eval_guard_def,dt_test_def]
    \\ imp_res_tac walk_thm \\ fs [dt_test_def]
    \\ IF_CASES_TAC \\ fs [])
  THEN1
   (fs [pat_to_guard_def,dt_eval_guard_def,pmatch_def]
    \\ Cases_on ‘pmatch refs p x ≠ PTypeFailure’ \\ fs []
    \\ Cases_on ‘pmatch refs p' x ≠ PTypeFailure’ \\ fs []
    \\ Cases_on ‘pmatch refs p x’ \\ fs []
    \\ Cases_on ‘pmatch refs p' x’ \\ fs []
    \\ res_tac \\ fs []
    \\ rw [mk_Disj_def,dt_eval_guard_def]
    \\ fs [is_True_thm,dt_eval_guard_def])
  THEN1
   (Cases_on ‘x’ \\ fs [pat_to_guard_def,pmatch_def]
    \\ fs [CaseEq"option"]
    \\ Cases_on ‘FLOOKUP refs n’ \\ fs []
    \\ fs [pmatch_def]
    \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [walk_append]
    \\ fs [walk_def])
  THEN1 fs [pat_to_guard_def,pmatch_def,dt_eval_guard_def]
  THEN1
   (Cases_on ‘xs’ \\ fs [pmatch_def]
    \\ rveq \\ fs [pmatch_def,CaseEq"pmatchResult"]
    \\ Cases_on ‘pmatch refs p h’ \\ fs []
    \\ fs [walk_list_def,CaseEq"option",CaseEq"term"]
    \\ rveq \\ fs [pat_to_guard_def]
    \\ first_x_assum (qspec_then ‘h’ assume_tac) \\ rfs []
    \\ rfs [walk_def,walk_append] \\ rfs [rich_listTheory.EL_LENGTH_APPEND])
  THEN1
   (Cases_on ‘xs’ \\ fs [pmatch_def]
    \\ Cases_on ‘pmatch refs p h ≠ PTypeFailure’ \\ fs []
    \\ rename [‘pmatch_list refs (n::ns) t’]
    \\ Cases_on ‘pmatch_list refs (n::ns) t = PTypeFailure’
    THEN1 (fs [CaseEq"pmatchResult"] \\ Cases_on ‘pmatch refs p h’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ strip_tac
    \\ first_x_assum drule \\ strip_tac
    \\ rfs [walk_append,walk_def]
    \\ rfs [walk_def,walk_list_def,CaseEq"option",CaseEq"term"]
    \\ rfs [] \\ rveq \\ fs []
    \\ fs [pat_to_guard_def,dt_eval_guard_def,dt_eval_guard_mk_Conj]
    \\ rpt (pop_assum mp_tac)
    \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
    \\ rfs [rich_listTheory.EL_LENGTH_APPEND]
    \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
    \\ rfs [rich_listTheory.EL_LENGTH_APPEND]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [CaseEq"pmatchResult"])
QED

Triviality mk_If_thm:
  dt_eval refs v (mk_If g p q) = dt_eval refs v (If g p q)
Proof
  rw [mk_If_def] \\ fs [is_True_thm,dt_eval_def,dt_eval_guard_def]
QED

Theorem pat_to_code_thm:
  !rows.
    match refs rows v <> NONE ==>
    dt_eval refs v (pats_to_code rows) = match refs rows v
Proof
  Induct
  \\ fs [match_def,pats_to_code_def,dt_eval_def,FORALL_PROD,mk_If_thm]
  \\ fs [CaseEq"pmatchResult",CaseEq"option",GSYM IMP_DISJ_THM]
  \\ rw [] \\ fs [dt_eval_def]
  \\ Cases_on ‘pmatch refs p_1 v <> PTypeFailure’ \\ fs []
  \\ drule (dt_eval_guard_pat_to_guard |> CONJUNCT1)
  \\ disch_then (qspecl_then [‘v’,‘[]’] assume_tac) \\ fs [walk_def]
  \\ Cases_on ‘pmatch refs p_1 v = PMatchSuccess’ \\ fs []
  THEN1 (Cases_on ‘match refs rows v’ \\ fs [dt_eval_def])
  \\ Cases_on ‘pmatch refs p_1 v = PMatchFailure’ \\ fs []
  \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
QED


(* plug all the parts together *)

Definition comp_def:
  comp rows =
    let rows0 = move_const_up rows in
    let rows1 = (if exh_rows rows0 then insert_Any rows0 else rows0) in
      pats_to_code rows1
End

Theorem comp_thm:
  match refs rows v <> NONE ==>
  dt_eval refs v (comp rows) = match refs rows v
Proof
  fs [comp_def] \\ strip_tac
  \\ drule match_move_const_up
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ metis_tac [pat_to_code_thm,exh_rows_thm,match_insert_Any]
QED

val _ = export_theory();
