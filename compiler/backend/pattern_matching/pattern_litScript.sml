(*
  This theory extends pattern matching with support for literals in
  the patterns.
*)
open preamble;
open pattern_matchingTheory;

val _ = new_theory "pattern_lit";

val _ = set_grammar_ancestry ["pattern_matching"]

Type kind[local] = ``:num``

(* input syntax *)

Datatype:
  pat =
    Any
  | Cons kind num (((num # num) list) option) (pat list)
  | Or pat pat
  | Lit kind 'literal (* new in this language *)
End

Datatype:
  branch = Branch (('literal pat) list) num
End

(* output syntax *)

Datatype:
  dTest = TagLenEq kind num num | LitEq kind 'literal
End

Datatype:
  dTree =
    Leaf num
  | Fail
  | DTypeFail
  | If listPos ('literal dTest) dTree dTree
End

(* semantic values *)

Datatype:
  term = Term kind num (term list)
       | Litv kind 'literal (* new in this language *)
       | Other
End

(* semantics of input *)

Definition is_sibling_def:
  is_sibling x NONE = T /\
  is_sibling x (SOME l) = MEM x l
End

Definition pmatch_def:
  (pmatch Any t = PMatchSuccess) /\
  (pmatch (Lit k l) (Litv k' l') =
     if k <> k' then PTypeFailure else
     if l = l' then PMatchSuccess else PMatchFailure) /\
  (pmatch (Cons k pcons siblings pargs) (Term k' tcons targs) =
    if k <> k' then PTypeFailure else
    if pcons = tcons
    then pmatch_list pargs targs
    else if is_sibling (tcons,LENGTH targs) siblings
         then PMatchFailure else PTypeFailure) /\
  (pmatch (Or p1 p2) t =
    case pmatch p1 t of
       PMatchSuccess => (case pmatch p2 t of
                           PTypeFailure => PTypeFailure
                         | _ => PMatchSuccess)
     | PMatchFailure => pmatch p2 t
     | PTypeFailure => PTypeFailure) /\
  (pmatch _ _ = PTypeFailure) /\
  (pmatch_list [] [] = PMatchSuccess) /\
  (pmatch_list [] ts = PTypeFailure) /\
  (pmatch_list ps [] = PTypeFailure) /\
  (pmatch_list (p::ps) (t::ts) =
    case pmatch p t of
      PMatchSuccess => pmatch_list ps ts
    | PMatchFailure => (case pmatch_list ps ts of
                           PTypeFailure => PTypeFailure
                         | _ => PMatchFailure)
    | PTypeFailure => PTypeFailure)
Termination
  WF_REL_TAC `measure (\x. case x of INL (p,_) => pat_size (K 0) p
                                   | INR (ps,_) => pat1_size (K 0) ps)`
End

Definition match_def:
  (match [] ts = SOME MatchFailure) /\
  (match ((Branch ps e)::bs) ts =
    case pmatch_list ps ts of
       PMatchSuccess =>
         (case match bs ts of
           NONE => NONE
         | SOME _ => SOME (MatchSuccess e))
     | PMatchFailure => match bs ts
     | PTypeFailure => NONE)
End

(* semantics of output *)

Definition app_pos_def:
  (app_pos EmptyPos p = SOME p) /\
  (app_pos (Pos _ _) (Term k c []) = NONE) /\
  (app_pos (Pos 0 pos) (Term k c (x::xs)) = app_pos pos x) /\
  (app_pos (Pos (SUC n) pos) (Term k c (x::xs)) =
    app_pos (Pos n pos) (Term k c xs)) /\
  (app_pos (Pos _ _) _ = NONE)
End

Definition app_list_pos_def:
  (app_list_pos [] (_,_) = NONE) /\
  (app_list_pos (x::xs) (0, pos) = app_pos pos x) /\
  (app_list_pos (x::xs) (SUC n, pos) =
    app_list_pos xs (n, pos))
End

Definition dt_test_def:
  dt_test (TagLenEq k t l) (Term k' c args) =
    (if k = k' then SOME (t = c /\ l = LENGTH args) else NONE) /\
  dt_test (LitEq k l1) (Litv k' l2) =
    (if k = k' then SOME (l1 = l2) else NONE) /\
  dt_test _ _ = NONE
End

Definition dt_eval_def:
  (dt_eval ts (Leaf k) = SOME (MatchSuccess k)) /\
  (dt_eval _ Fail = SOME (MatchFailure)) /\
  (dt_eval _ DTypeFail = NONE) /\
  (dt_eval ts (If pos test dt1 dt2) =
    case (app_list_pos ts pos) of
    | NONE => NONE
    | SOME x => case dt_test test x of
                | NONE => NONE
                | SOME b => dt_eval ts (if b then dt1 else dt2))
End

(* pattern compiler -- built around the previous one *)

Definition pat_lits_def:
  (pat_lits Any ts = ts) /\
  (pat_lits (Or p1 p2) ts = pat_lits p2 (pat_lits p1 ts)) /\
  (pat_lits (Lit k l) ts = if MEM l ts then ts else l::ts) /\
  (pat_lits (Cons _ _ _ pargs) ts = pat_list_lits pargs ts) /\
  (pat_list_lits [] ts = ts) /\
  (pat_list_lits (p::ps) ts = pat_list_lits ps (pat_lits p ts))
Termination
  WF_REL_TAC `measure (\x. case x of INL p => pat_size (K 0) p
                                   | INR ps => pat1_size (K 0) ps)`
End

Definition all_lits_def:
  (all_lits [] ts = ts) /\
  (all_lits ((Branch ps e)::bs) ts = all_lits bs (pat_list_lits ps ts))
End

Definition encode_def:
  (encode Any ts = Any) /\
  (encode (Or p1 p2) ts = Or (encode p1 ts) (encode p2 ts)) /\
  (encode (Lit k l) ts = pattern_matching$Cons (2 * k + 1) (findi l ts) NONE []) /\
  (encode (Cons k t r pargs) ts = Cons (2 * k) t r (encode_list pargs ts)) /\
  (encode_list [] ts = []) /\
  (encode_list (p::ps) ts = encode p ts :: encode_list ps ts)
Termination
  WF_REL_TAC `measure (\x. case x of INL p => pat_size (K 0) p
                                   | INR ps => pat1_size (K 0) ps)`
End

Definition encode_all_def:
  encode_all [] ts = [] /\
  encode_all ((Branch ps e)::bs) ts =
    Branch (encode_list ps ts) e :: encode_all bs ts
End

Definition decode_def:
  decode Fail ts = Fail /\
  decode (Leaf i) ts = Leaf i /\
  decode DTypeFail ts = DTypeFail /\
  decode (Swap _ dt) ts = decode dt ts /\
  decode (If pos k c a dt1 dt2) ts =
      If pos (let n = k DIV 2 in
                if ODD k /\ c < LENGTH ts
                then LitEq n (EL c ts)
                else TagLenEq n c a)
        (decode dt1 ts)
        (decode dt2 ts)
End

Definition pat_compile_def:
  pat_compile h m =
    let lits = all_lits m [] in
    let m1 = encode_all m lits in
    let t1 = pattern_matching$pat_compile h m1 in
      decode t1 lits
End

(* correctness proof *)

Definition msize_def:
  msize [] = 0 ∧
  msize (Branch l e::bs) = LENGTH l
End

Definition patterns_def:
  patterns (Branch ps e) = ps
End

Definition inv_mat_def:
  inv_mat m = ∃n. EVERY (λl. LENGTH (patterns l) = n) m
End

Definition embed_def:
  embed ts Other = pattern_matching$Other /\
  embed ts (Term k n xs) = Term (2 * k) n (MAP (\c. embed ts c) xs) /\
  embed ts (Litv k l) = Term (2 * k + 1) (if MEM l ts then findi l ts else LENGTH ts) []
Termination
  WF_REL_TAC `measure (term_size (K 0) o SND)`
  \\ Induct_on `xs` \\ fs [] \\ rw [fetch "-" "term_size_def"]
  \\ res_tac \\ fs [] \\ pop_assum (assume_tac o SPEC_ALL) \\ fs []
End

Theorem LENGTH_encode_list:
  !l lits. LENGTH (encode_list l lits) = LENGTH l
Proof
  Induct \\ fs [encode_def]
QED

Theorem inv_mat_dcmp:
  !b m. inv_mat (b::m) ==> inv_mat m
Proof
  rw[inv_mat_def] \\
  qexists_tac `LENGTH (patterns b)` \\
  rw[]
QED;

Theorem inv_mat_encode_all:
  !m lits. inv_mat m ==> pattern_matching$inv_mat (encode_all m lits)
Proof
  Induct
  >- fs[encode_all_def, pattern_matchingTheory.inv_mat_def]
  >- (rw[encode_all_def] \\
      imp_res_tac inv_mat_dcmp \\
      Cases_on `m`
      >- (Cases_on `h` \\ fs[encode_all_def, pattern_matchingTheory.inv_mat_def])
      >- (Cases_on `h` \\ Cases_on `h'` \\
          fs[encode_all_def, pattern_matchingTheory.inv_mat_aux_def, LENGTH_encode_list] \\
          fs[inv_mat_def, patterns_def]))
QED

Theorem findi_11:
  !xs x y. MEM x xs ==> (findi x xs = findi y xs <=> x = y)
Proof
  Induct \\ fs [findi_def] \\ rw []
QED

Definition pat_ok_def:
  pat_ok p Any = T /\
  pat_ok p (Lit k l) = T /\
  pat_ok p (Cons k c _ pargs) = (p k c (LENGTH pargs) /\ EVERY (pat_ok p) pargs) /\
  pat_ok p (Or p1 p2) = (pat_ok p p1 /\ pat_ok p p2)
Termination
  WF_REL_TAC `measure (pat_size (K 0) o SND)` \\ fs [] \\ rw []
  \\ Induct_on `pargs` \\ fs [] \\ rw [fetch "-" "pat_size_def"] \\ fs []
End

Definition branches_ok_def:
  branches_ok p [] = T /\
  branches_ok p (Branch ps k :: bs) = (EVERY (pat_ok p) ps /\ branches_ok p bs)
End

Theorem pat_ind = fetch "-" "pat_ok_ind"
  |> Q.SPEC `\x y. P y` |> SIMP_RULE std_ss [] |> GEN_ALL;

Theorem set_pat_lits:
  (!p lits:'a list.
     set (pat_lits p lits) = set (pat_lits p []) UNION set lits) /\
  (!ps lits:'a list.
     set (pat_list_lits ps lits) = set (pat_list_lits ps []) UNION set lits)
Proof
  reverse conj_asm1_tac
  THEN1
   (Induct THEN1 fs [pat_lits_def]
    \\ rewrite_tac [pat_lits_def]
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ fs [AC UNION_COMM UNION_ASSOC])
  \\ ho_match_mp_tac pat_ind
  \\ rewrite_tac [pat_lits_def,MEM]
  \\ rpt strip_tac
  THEN1 fs []
  THEN1 (rw [] \\ fs [EXTENSION] \\ metis_tac [])
  THEN1
   (qid_spec_tac `lits` \\ Induct_on `pargs`
    \\ rpt strip_tac THEN1 fs [pat_lits_def]
    \\ rpt strip_tac
    \\ last_x_assum mp_tac
    \\ impl_tac THEN1 (metis_tac [MEM])
    \\ rewrite_tac [pat_lits_def]
    \\ disch_then (fn th => once_rewrite_tac [th])
    \\ first_x_assum (qspec_then `h` mp_tac)
    \\ impl_tac THEN1 fs []
    \\ disch_then (fn th => once_rewrite_tac [th])
    \\ fs [AC UNION_COMM UNION_ASSOC])
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [AC UNION_COMM UNION_ASSOC]
QED

Theorem set_all_lits:
  !m lits. set (all_lits m lits) = set (all_lits m []) UNION set lits
Proof
  Induct \\ fs [all_lits_def] \\ Cases \\ rewrite_tac [all_lits_def]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ once_rewrite_tac [set_pat_lits]
  \\ fs [AC UNION_COMM UNION_ASSOC]
QED

Theorem ALL_DISTINCT_pat_lits:
  (!p lits:'a list.
     ALL_DISTINCT (pat_lits p lits) = ALL_DISTINCT lits) /\
  (!ps lits:'a list.
     ALL_DISTINCT (pat_list_lits ps lits) = ALL_DISTINCT lits)
Proof
  reverse conj_asm1_tac
  THEN1 (Induct \\ fs [pat_lits_def])
  \\ ho_match_mp_tac pat_ind
  \\ rewrite_tac [pat_lits_def,MEM]
  \\ fs [] \\ rw []
  \\ qid_spec_tac `lits` \\ Induct_on `pargs`
  \\ fs [pat_lits_def]
QED

Theorem ALL_DISTINCT_all_lits:
  !m lits. ALL_DISTINCT (all_lits m lits) <=> ALL_DISTINCT lits
Proof
  Induct \\ fs [all_lits_def] \\ Cases \\ rewrite_tac [all_lits_def]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [ALL_DISTINCT_pat_lits]
QED

Theorem pmatch_encode:
  (!l v res.
    pmatch l v = res /\ res <> PTypeFailure /\
    set (pat_lits l []) ⊆ set lits /\ ALL_DISTINCT lits ==>
    pmatch (encode l lits) (embed lits v) = res) /\
  (!l v res.
    pmatch_list l v = res /\ res <> PTypeFailure /\
    set (pat_list_lits l []) ⊆ set lits /\ ALL_DISTINCT lits ==>
    pmatch_list (encode_list l lits) (MAP (embed lits) v) = res)
Proof
  ho_match_mp_tac pmatch_ind \\ rpt strip_tac
  \\ fs [pmatch_def,pattern_matchingTheory.pmatch_def,encode_def,embed_def]
  THEN1
   (IF_CASES_TAC \\ fs [] \\ rveq \\ fs [] \\ rename [`MEM l1 lits`]
    \\ Cases_on `l = l1` \\ fs [] \\ rveq \\ fs [bool_case_eq]
    \\ fs [pat_lits_def] \\ Cases_on `MEM l1 lits` \\ fs []
    \\ imp_res_tac indexedListsTheory.MEM_findi \\ fs []
    \\ fs [findi_11])
  \\ qpat_x_assum `_ ⊆ set lits` mp_tac
  \\ fs [pat_lits_def] \\ once_rewrite_tac [set_pat_lits]
  \\ reverse strip_tac
  \\ fs [CaseEq"pmatchResult"] \\ rveq \\ fs [pat_lits_def,encode_def]
  \\ Cases_on `siblings` \\ fs [is_sibling_def]
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem match_encode_all:
  !m v res lits.
    match m v = SOME res /\ set (all_lits m []) ⊆ set lits /\ ALL_DISTINCT lits ==>
    match (encode_all m lits) (MAP (embed lits) v) = SOME res
Proof
  Induct \\ fs [encode_all_def]
  THEN1 (Cases_on `v` \\ fs [match_def,pattern_matchingTheory.match_def])
  \\ Cases
  \\ fs [match_def,pattern_matchingTheory.match_def,CaseEq"pmatchResult",option_case_eq]
  \\ rpt strip_tac \\ rveq
  \\ fs [encode_all_def,match_def,pattern_matchingTheory.match_def]
  \\ drule (CONJUNCT2 pmatch_encode) \\ fs []
  \\ disch_then (qspec_then `lits` mp_tac)
  \\ fs [all_lits_def]
  \\ qpat_x_assum `_ ⊆ set lits` mp_tac
  \\ once_rewrite_tac [set_all_lits] \\ fs [] \\ strip_tac
  \\ fs [] \\ rw []
  \\ first_x_assum drule
  \\ disch_then (qspec_then `lits` mp_tac) \\ fs []
QED

Theorem app_list_pos_embed:
  !v p.
    app_list_pos (MAP (embed lits) v) p = SOME x ==>
    ?y. app_list_pos v p = SOME y /\ x = embed lits y
Proof
  fs [FORALL_PROD]
  \\ recInduct app_list_pos_ind
  \\ fs [app_list_pos_def,pattern_matchingTheory.app_list_pos_def]
  \\ rpt gen_tac
  \\ rename [`app_pos pos x`]
  \\ qid_spec_tac `x`
  \\ qid_spec_tac `pos`
  \\ recInduct app_pos_ind
  \\ fs [app_pos_def,pattern_matchingTheory.app_pos_def,embed_def]
QED

Theorem findi_eq_EL:
  !lits l n.
    n < LENGTH lits /\ ALL_DISTINCT lits ==>
    (findi l lits = n <=> EL n lits = l)
Proof
  Induct \\ fs [findi_def] \\ rpt gen_tac
  \\ Cases_on `n` \\ fs []
  THEN1 (rw [] \\ fs [])
  \\ fs [GSYM ADD1] \\ rw []
  \\ CCONTR_TAC \\ rveq \\ fs [] \\ fs [MEM_EL]
  \\ metis_tac []
QED

Theorem dt_eval_embed:
  !t v lits.
    dt_eval (MAP (embed lits) v) t = SOME res /\
    dt_ok (\k c a. ODD k ==> c < LENGTH lits /\ a = 0) t /\
    ALL_DISTINCT lits ==>
    dt_eval v (decode t lits) = SOME res
Proof
  Induct
  \\ fs [decode_def,dt_eval_def,pattern_matchingTheory.dt_eval_def]
  \\ fs [option_case_eq,PULL_EXISTS,dt_ok_def]
  \\ rpt strip_tac
  \\ drule app_list_pos_embed
  \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ Cases_on `y` \\ fs [embed_def]
  THEN1
   (fs [ODD_EVEN,EVEN_DOUBLE,miscTheory.TWOxDIV2]
    \\ fs [dt_test_def] \\ rw [] \\ fs [])
  \\ rewrite_tac [GSYM ADD1,arithmeticTheory.ODD_DOUBLE]
  \\ rveq \\ qpat_x_assum `_ ==> _` mp_tac
  \\ rewrite_tac [GSYM ADD1,arithmeticTheory.ODD_DOUBLE]
  \\ strip_tac \\ rveq \\ fs []
  \\ once_rewrite_tac [MULT_COMM] \\ rewrite_tac [ADD1]
  \\ fs [arithmeticTheory.DIV_MULT]
  \\ fs [dt_test_def]
  \\ qpat_x_assum `_ = SOME res` (assume_tac o GSYM)
  \\ asm_rewrite_tac []
  \\ drule EL_MEM \\ strip_tac
  \\ reverse (Cases_on `MEM l lits`) \\ fs []
  THEN1 (IF_CASES_TAC \\ fs [])
  \\ fs [findi_eq_EL] \\ rw [] \\ fs []
QED

Theorem pat_ok_encode:
  ∀l. set (pat_lits l []) ⊆ set lits ==>
      pat_ok (λk c a. ODD k ⇒ c < LENGTH lits ∧ a = 0) (encode l lits)
Proof
  ho_match_mp_tac pat_ind
  \\ fs [pattern_matchingTheory.pat_ok_def,encode_def]
  \\ fs [pat_lits_def]
  \\ once_rewrite_tac [set_pat_lits] \\ fs []
  \\ fs [ODD_EVEN,EVEN_DOUBLE]
  \\ conj_tac
  THEN1 (rw [] \\ imp_res_tac indexedListsTheory.MEM_findi \\ fs [])
  \\ Induct \\ fs [encode_def]
  \\ fs [pat_lits_def]
  \\ once_rewrite_tac [set_pat_lits] \\ fs []
QED

Theorem branches_ok_encode_all:
  !m lits.
    set (all_lits m []) ⊆ set lits ==>
    branches_ok (λk c a. ODD k ⇒ c < LENGTH lits ∧ a = 0) (encode_all m lits)
Proof
  Induct \\ fs [pattern_matchingTheory.branches_ok_def,encode_all_def]
  \\ Cases \\ fs [pattern_matchingTheory.branches_ok_def,encode_all_def]
  \\ fs [all_lits_def]
  \\ once_rewrite_tac [set_all_lits] \\ fs []
  \\ Induct_on `l` \\ fs [encode_def,pat_ok_encode]
  \\ fs [pat_lits_def]
  \\ once_rewrite_tac [set_pat_lits] \\ fs [pat_ok_encode]
QED

Theorem pat_compile_correct:
  !h m v res.
    match m v = SOME res /\ LENGTH v = msize m /\ inv_mat m ==>
    dt_eval v (pattern_lit$pat_compile h m) = SOME res
Proof
  fs [pat_compile_def] \\ rw []
  \\ qabbrev_tac `lits = all_lits m []`
  \\ drule match_encode_all
  \\ disch_then (qspec_then `lits` mp_tac)
  \\ impl_keep_tac THEN1 (fs [Abbr`lits`,ALL_DISTINCT_all_lits])
  \\ strip_tac
  \\ qspecl_then [`h`,`encode_all m lits`,`MAP (embed lits) v`] mp_tac
        pattern_matchingTheory.pat_compile_correct
  \\ fs [] \\ impl_tac
  THEN1
   (conj_tac THEN1
     (Cases_on `m` \\ fs [msize_def,pattern_matchingTheory.msize_def,encode_all_def]
      \\ Cases_on `h` \\ fs [msize_def,pattern_matchingTheory.msize_def,encode_all_def]
      \\ qid_spec_tac `l` \\ Induct \\ fs [encode_def])
    \\ Cases_on `m` \\ fs [inv_mat_def,pattern_matchingTheory.inv_mat_def,encode_all_def]
    \\ qexists_tac `LENGTH (patterns h)` \\ fs []
    \\ Cases_on `h` \\ fs [encode_all_def,patterns_def,pattern_matchingTheory.patterns_def]
    \\ fs [LENGTH_encode_list]
    \\ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac `t` \\ fs []
    \\ Induct \\ fs [encode_all_def]
    \\ Cases \\ fs [encode_all_def,patterns_def,pattern_matchingTheory.patterns_def]
    \\ fs [LENGTH_encode_list])
  \\ disch_then (assume_tac o GSYM)
  \\ match_mp_tac dt_eval_embed \\ fs []
  \\ match_mp_tac dt_ok_pat_compile  \\ rw[]
  >- fs[inv_mat_encode_all]
  >- fs [branches_ok_encode_all]
QED

Definition dt_ok_def:
  dt_ok p (Leaf k) = T /\
  dt_ok p Fail = T /\
  dt_ok p DTypeFail = T /\
  dt_ok p (If pos test dt1 dt2) =
    (dt_ok p dt1 /\ dt_ok p dt2 /\
     case test of TagLenEq k c a => p k c a | _ => T)
End

Theorem encode_list_eq_MAP:
  !xs lits. encode_list xs lits = MAP (\p. encode p lits) xs
Proof
  Induct \\ fs [encode_def]
QED

Theorem pat_ok_encode:
  !l p lits:'a list.
    pat_ok p l /\ set (pat_lits l []) ⊆ set lits ⇒
    pat_ok (λk c a. if EVEN k then p (k DIV 2) c a else c < LENGTH lits)
             (encode l lits)
Proof
  ho_match_mp_tac pat_ind \\ rpt strip_tac
  \\ fs [encode_def,pat_ok_def,pattern_matchingTheory.pat_ok_def]
  \\ fs [pat_lits_def,EVEN_DOUBLE,EVEN_ADD,
         MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]]
  \\ imp_res_tac indexedListsTheory.MEM_findi \\ fs []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [set_pat_lits] \\ fs [LENGTH_encode_list]
  \\ strip_tac
  \\ fs [EVERY_MEM,encode_list_eq_MAP,MEM_MAP,PULL_EXISTS,
         PULL_FORALL,AND_IMP_INTRO]
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac \\ fs []
  \\ ntac 2 (pop_assum mp_tac)
  \\ rename [`MEM q xs`]
  \\ qid_spec_tac `q`
  \\ qid_spec_tac `xs`
  \\ Induct \\ fs [pat_lits_def]
  \\ once_rewrite_tac [set_pat_lits] \\ fs []
  \\ metis_tac []
QED

Theorem pat_ok_encode_list:
  !l p lits:'a list.
    EVERY (pat_ok p) l /\ set (pat_list_lits l []) ⊆ set lits ⇒
    EVERY (pat_ok (λk c a. if EVEN k then p (k DIV 2) c a else c < LENGTH lits))
             (encode_list l lits)
Proof
  Induct \\ fs [encode_def,pat_lits_def]
  \\ once_rewrite_tac [set_pat_lits] \\ fs [pat_ok_encode]
QED

Theorem branches_ok_encode_all:
  !m p.
    branches_ok p m /\ set (all_lits m []) ⊆ set lits ==>
    branches_ok (\k c a. if EVEN k then p (k DIV 2) c a else c < LENGTH lits)
      (encode_all m lits)
Proof
  Induct
  \\ fs [encode_all_def,branches_ok_def,pattern_matchingTheory.branches_ok_def]
  \\ Cases
  \\ fs [encode_all_def,branches_ok_def,pattern_matchingTheory.branches_ok_def]
  \\ fs [all_lits_def] \\ once_rewrite_tac [set_all_lits] \\ fs []
  \\ fs [pat_ok_encode_list]
QED

Theorem dt_ok_pat_compile:
  inv_mat m /\ branches_ok p m ==> dt_ok p (pat_compile h m)
Proof
  fs [pat_compile_def]
  \\ qabbrev_tac `lits = all_lits m []`
  \\ strip_tac
  \\ drule branches_ok_encode_all
  \\ disch_then (qspec_then `lits` mp_tac)
  \\ impl_tac THEN1 fs [Abbr`lits`]
  \\ strip_tac
  \\ imp_res_tac pattern_matchingTheory.dt_ok_pat_compile
  \\ pop_assum mp_tac
  \\ impl_tac THEN1
   (fs [inv_mat_def,pattern_matchingTheory.inv_mat_def]
    \\ qexists_tac `n`
    \\ qpat_x_assum `EVERY _ _` mp_tac
    \\ qid_spec_tac `m` \\ Induct \\ fs [encode_all_def] \\ Cases
    \\ fs [encode_all_def,patterns_def,pattern_matchingTheory.patterns_def,
           LENGTH_encode_list])
  \\ disch_then (qspec_then `h` mp_tac)
  \\ qspec_tac (`pat_compile h (encode_all m lits)`,`t`)
  \\ Induct
  \\ fs [dt_ok_def,pattern_matchingTheory.dt_ok_def,decode_def]
  \\ rw [] \\ fs [EVEN_ODD]
QED

val _ = export_theory();
