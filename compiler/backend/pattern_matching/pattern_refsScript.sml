(*
  This theory extends pattern matching with support for references in
  the patterns. It extends the version that has literals in patterns.
*)
open preamble;
open pattern_litTheory pattern_commonTheory;

val _ = new_theory "pattern_refs";

val _ = set_grammar_ancestry ["pattern_lit"]

Type kind[local] = ``:num``

(* input syntax *)

Datatype:
  pat =
    Any
  | Cons kind num (((num # num) list) option) (pat list)
  | Or pat pat
  | Lit ast$lit
  | Ref pat (* new in this language *)
End

Datatype:
  branch = Branch (pat list) num
End

(* output syntax -- same as pattern_lit *)

(* semantic values *)

Datatype:
  term = Term kind num (term list)
       | Litv ast$lit
       | RefPtr num (* new in this language *)
       | Other
End

(* semantics of input *)

Definition pmatch_def:
  (pmatch refs Any t = PMatchSuccess) /\
  (pmatch refs (Lit l) (Litv l') =
     if ~(lit_same_type l l') then PTypeFailure else
     if l = l' then PMatchSuccess else PMatchFailure) /\
  (pmatch refs (Cons k pcons siblings pargs) (Term k' tcons targs) =
    if k <> k' then PTypeFailure else
    if pcons = tcons /\ LENGTH pargs = LENGTH targs
    then pmatch_list refs pargs targs
    else if is_sibling (tcons,LENGTH targs) siblings
         then PMatchFailure else PTypeFailure) /\
  (pmatch refs (Ref p) (RefPtr r) =
    case FLOOKUP refs r of
    | NONE => PTypeFailure
    | SOME v => pmatch refs p v) /\
  (pmatch refs (Or p1 p2) t =
    case pmatch refs p1 t of
       PMatchSuccess => (case pmatch refs p2 t of
                           PTypeFailure => PTypeFailure
                         | _ => PMatchSuccess)
     | PMatchFailure => pmatch refs p2 t
     | PTypeFailure => PTypeFailure) /\
  (pmatch refs _ _ = PTypeFailure) /\
  (pmatch_list refs [] [] = PMatchSuccess) /\
  (pmatch_list refs [] ts = PTypeFailure) /\
  (pmatch_list refs ps [] = PTypeFailure) /\
  (pmatch_list refs (p::ps) (t::ts) =
    case pmatch refs p t of
      PMatchSuccess => pmatch_list refs ps ts
    | PMatchFailure => (case pmatch_list refs ps ts of
                           PTypeFailure => PTypeFailure
                         | _ => PMatchFailure)
    | PTypeFailure => PTypeFailure)
Termination
  WF_REL_TAC `measure (\x. case x of INL (r,p,_) => pat_size p
                                   | INR (r,ps,_) => pat1_size ps)`
End

Definition match_def:
  (match refs [] ts = SOME MatchFailure) /\
  (match refs ((Branch ps e)::bs) ts =
    case pmatch_list refs ps ts of
       PMatchSuccess =>
         (case match refs bs ts of
           NONE => NONE
         | SOME _ => SOME (MatchSuccess e))
     | PMatchFailure => match refs bs ts
     | PTypeFailure => NONE)
End

(* semantics of output *)

Definition app_pos_def:
  (app_pos refs EmptyPos p = SOME p) /\
  (app_pos refs (Pos 0 pos) (RefPtr r) =
     case FLOOKUP refs r of
     | NONE => NONE
     | SOME v => app_pos refs pos v) /\
  (app_pos refs (Pos _ _) (Term k c []) = NONE) /\
  (app_pos refs (Pos 0 pos) (Term k c (x::xs)) = app_pos refs pos x) /\
  (app_pos refs (Pos (SUC n) pos) (Term k c (x::xs)) =
    app_pos refs (Pos n pos) (Term k c xs)) /\
  (app_pos refs (Pos _ _) _ = NONE)
End

Definition app_list_pos_def:
  (app_list_pos refs [] (_,_) = NONE) /\
  (app_list_pos refs (x::xs) (0, pos) = app_pos refs pos x) /\
  (app_list_pos refs (x::xs) (SUC n, pos) =
    app_list_pos refs xs (n, pos))
End

Definition dt_test_def:
  dt_test (TagLenEq k t l) (Term k' c args) =
    (if k = k' then SOME (t = c /\ l = LENGTH args) else NONE) /\
  dt_test (LitEq l1) (Litv l2) =
    (if lit_same_type l1 l2 then SOME (l1 = l2) else NONE) /\
  dt_test _ _ = NONE
End

Definition dt_eval_def:
  (dt_eval refs _ (Leaf k) = SOME (MatchSuccess k)) /\
  (dt_eval refs _ Fail = SOME (MatchFailure)) /\
  (dt_eval refs _ DTypeFail = NONE) /\
  (dt_eval refs ts (If pos test dt1 dt2) =
    case (app_list_pos refs ts pos) of
    | NONE => NONE
    | SOME x => case dt_test test x of
                | NONE => NONE
                | SOME b => dt_eval refs ts (if b then dt1 else dt2))
End

(* pattern compiler -- built around the previous one *)

Definition encode_def:
  (encode Any = pattern_lit$Any) /\
  (encode (Ref p) = Cons 0 0 (SOME [(0,1)]) [encode p]) /\
  (encode (Or p1 p2) = Or (encode p1) (encode p2)) /\
  (encode (Lit l) = Lit l) /\
  (encode (Cons k t r pargs) = Cons (k + 1) t r (MAP encode pargs))
Termination
  WF_REL_TAC `measure pat_size` \\ fs []
  \\ Induct_on `pargs` \\ fs [fetch "-" "pat_size_def"]
  \\ rw [] \\ res_tac \\ fs [fetch "-" "pat_size_def"]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs []
End

Definition encode_br_def:
  encode_br (Branch ps e) = Branch (MAP encode ps) e
End

Definition decode_def:
  decode Fail = Fail /\
  decode (Leaf i) = Leaf i /\
  decode DTypeFail = DTypeFail /\
  decode (If pos (LitEq l) dt1 dt2) =
    If pos (LitEq l) (decode dt1) (decode dt2) /\
  decode (If pos (TagLenEq k t a) dt1 dt2) =
    if k = 0 then decode dt1 else
      If pos (TagLenEq (k - 1) t a) (decode dt1) (decode dt2)
End

Definition pat_compile_def:
  pat_compile h m =
    let m1 = MAP encode_br m in
    let t1 = pattern_lit$pat_compile h m1 in
      decode t1
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

Definition pat_ok_def:
  pat_ok p Any = T /\
  pat_ok p (Lit l) = T /\
  pat_ok p (Ref p1) = pat_ok p p1 /\
  pat_ok p (Cons k c _ pargs) = (p k c (LENGTH pargs) /\ EVERY (pat_ok p) pargs) /\
  pat_ok p (Or p1 p2) = (pat_ok p p1 /\ pat_ok p p2)
Termination
  WF_REL_TAC `measure (pat_size o SND)` \\ fs [] \\ rw []
  \\ Induct_on `pargs` \\ fs [] \\ rw [fetch "-" "pat_size_def"] \\ fs []
End

Definition branches_ok_def:
  branches_ok p [] = T /\
  branches_ok p (Branch ps k :: bs) = (EVERY (pat_ok p) ps /\ branches_ok p bs)
End

Theorem pat_ind = fetch "-" "pat_ok_ind"
  |> Q.SPEC `\x y. P y` |> SIMP_RULE std_ss [] |> GEN_ALL;

Definition embed_def:
  embed refs n Other = pattern_lit$Other /\
  embed refs n (Litv l) = Litv l /\
  embed refs n (Term k t xs) =
    (if n = 0 then Other else Term (k + 1) t (MAP (embed refs (n-1)) xs)) /\
  embed refs n (RefPtr r) =
    if n = 0 then Other else
    case FLOOKUP refs r of
    | NONE => Other
    | SOME v => Term 0 0 [embed refs (n-1:num) v]
End

val bsize_def = Define `
  bsize (Branch ps e) = pat1_size ps`

Theorem pmatch_encode:
  (!refs (l:pat) v res d.
    pmatch refs l v = res /\ res <> PTypeFailure /\
    pat_size l <= d ==>
    pmatch (encode l) (embed refs d v) = res) /\
  (!refs (l:pat list) v res d.
    pmatch_list refs l v = res /\ res <> PTypeFailure /\
    pat1_size l <= d ==>
    pmatch_list (MAP encode l) (MAP (embed refs d) v) = res)
Proof
  ho_match_mp_tac pmatch_ind \\ rpt strip_tac
  \\ fs [encode_def,pmatch_def,pattern_litTheory.pmatch_def,embed_def]
  \\ fs [fetch "-" "pat_size_def",pattern_litTheory.pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  THEN1
   (IF_CASES_TAC \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum match_mp_tac \\ fs [])
  THEN1
   (fs [option_case_eq] \\ rveq \\ fs [pattern_litTheory.pmatch_def]
    \\ every_case_tac \\ fs [])
  \\ fs [option_case_eq] \\ fs [pmatch_def,pattern_litTheory.pmatch_def]
  THEN1 (Cases_on `res` \\ fs [])
  \\ fs [CaseEq"pmatchResult"]
QED

Theorem match_encode:
  !l v res d refs.
    match refs l v = SOME res /\ SUM (MAP bsize l) <= d ==>
    match (MAP encode_br l) (MAP (embed refs d) v) = SOME res
Proof
  Induct \\ fs [match_def,pattern_litTheory.match_def]
  \\ Cases \\ fs [match_def,pattern_litTheory.match_def,encode_br_def]
  \\ fs [CaseEq"pmatchResult",option_case_eq]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspec_then `d` mp_tac) \\ fs []
  \\ drule (CONJUNCT2 pmatch_encode) \\ fs []
  \\ disch_then (qspec_then `d` mp_tac) \\ fs [bsize_def]
QED

Theorem app_pos_embed:
  !refs p v d x.
    app_pos p (embed refs d v) = SOME x /\ position_size p + 1 <= d ==>
    ?w d1. x = embed refs d1 w /\ d1 <> 0 /\
           app_pos refs p v = SOME w
Proof
  ho_match_mp_tac app_pos_ind
  \\ fs [app_pos_def,embed_def,pattern_litTheory.app_pos_def]
  \\ rpt strip_tac \\ fs [position_size_def]
  THEN1 (qexists_tac `d` \\ fs [])
  THEN1
    (Cases_on `FLOOKUP refs r` \\ fs [pattern_litTheory.app_pos_def]
     \\ first_x_assum drule \\ fs [])
  THEN1 (rw [] \\ fs [pattern_litTheory.app_pos_def])
  THEN1
   (fs [pattern_litTheory.app_pos_def]
    \\ first_x_assum drule \\ fs [])
  THEN1
   (fs [pattern_litTheory.app_pos_def,GSYM ADD1,app_pos_def]
    \\ first_x_assum match_mp_tac \\ qexists_tac `d` \\ fs [])
  \\ every_case_tac \\ fs []
  \\ fs [pattern_litTheory.app_pos_def,app_pos_def]
QED

Definition pos_size_def:
  pos_size (_,p) = position_size p + 1
End

Theorem app_list_pos_embed:
  !refs v p d x.
    app_list_pos (MAP (embed refs d) v) p = SOME x /\
    pos_size p <= d ==>
    ?w d1. x = embed refs d1 w /\ d1 <> 0 /\
           app_list_pos refs v p = SOME w
Proof
  fs [FORALL_PROD]
  \\ ho_match_mp_tac app_list_pos_ind
  \\ fs [app_list_pos_def,pattern_litTheory.app_list_pos_def]
  \\ rpt strip_tac
  THEN1 (fs [pos_size_def]
    \\ match_mp_tac app_pos_embed \\ asm_exists_tac \\ fs [])
  \\ first_x_assum drule \\ fs [pos_size_def]
QED

Definition dt_size_def:
  dt_size (If p _ t1 t2) = pos_size p + dt_size t1 + dt_size t2 /\
  dt_size _ = 0
End

Theorem dt_eval_embed:
  !t v d refs.
    dt_eval (MAP (embed refs d) v) t = SOME res /\
    dt_ok (\k c a. k = 0 ==> c = 0 /\ a = 1) t /\
    dt_size t <= d ==>
    dt_eval refs v (decode t) = SOME res
Proof
  Induct
  \\ fs [dt_eval_def,decode_def,pattern_litTheory.dt_eval_def]
  \\ fs [option_case_eq,PULL_EXISTS] \\ rpt strip_tac
  \\ rename [`If p test`] \\ Cases_on `test`
  \\ fs [dt_eval_def,decode_def,pattern_litTheory.dt_eval_def]
  \\ rw []
  \\ drule app_list_pos_embed
  \\ fs [dt_size_def]
  \\ strip_tac \\ rveq \\ fs []
  \\ Cases_on `w`
  \\ fs [embed_def,dt_test_def,pattern_litTheory.dt_test_def]
  \\ rveq \\ fs []
  \\ TRY
   (rename [`FLOOKUP refs r`] \\ Cases_on `FLOOKUP refs r`
    \\ fs [dt_test_def,pattern_litTheory.dt_test_def])
  \\ fs [dt_ok_def,pattern_litTheory.dt_ok_def] \\ rveq \\ fs []
  \\ res_tac \\ rfs [dTree_size_def]
  \\ fs [dt_eval_def,decode_def,pattern_litTheory.dt_eval_def]
  \\ fs [embed_def,dt_test_def,pattern_litTheory.dt_test_def]
  \\ fs [] \\ rw [] \\ fs [] \\ res_tac \\ rfs [dTree_size_def]
QED

Theorem branches_ok_encode:
  !m. branches_ok (λk c a. k = 0 ⇒ c = 0 ∧ a = 1) (MAP encode_br m)
Proof
  Induct \\ fs [pattern_litTheory.branches_ok_def]
  \\ Cases \\ fs [pattern_litTheory.branches_ok_def,encode_br_def]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ rw []
  \\ rename [`encode p`] \\ qid_spec_tac `p`
  \\ ho_match_mp_tac pat_ind \\ rw []
  \\ fs [encode_def,pattern_litTheory.pat_ok_def]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem pat_compile_correct:
  !h m v res refs.
    match refs m v = SOME res /\ LENGTH v = msize m /\ inv_mat m ==>
    dt_eval refs v (pattern_refs$pat_compile h m) = SOME res
Proof
  fs [pat_compile_def] \\ rw []
  \\ drule match_encode
  \\ qabbrev_tac `dd = SUM (MAP bsize m) +
        dt_size (pat_compile h (MAP encode_br m))`
  \\ disch_then (qspec_then `dd` mp_tac) \\ fs []
  \\ impl_tac THEN1 fs [Abbr `dd`]
  \\ strip_tac
  \\ drule pattern_litTheory.pat_compile_correct
  \\ disch_then (qspec_then `h` mp_tac) \\ fs []
  \\ impl_keep_tac THEN1
   (conj_tac THEN1
     (Cases_on `m` \\ fs [msize_def,pattern_litTheory.msize_def]
      \\ rename [`x::xs`]
      \\ Cases_on `x` \\ fs [msize_def,pattern_litTheory.msize_def,encode_br_def])
    \\ fs [inv_mat_def,pattern_litTheory.inv_mat_def]
    \\ qexists_tac `n` \\ fs []
    \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
    \\ Cases \\ rw [] \\ res_tac \\ fs [encode_br_def]
    \\ fs [patterns_def,pattern_litTheory.patterns_def])
  \\ strip_tac
  \\ match_mp_tac dt_eval_embed
  \\ asm_exists_tac \\ fs []
  \\ reverse conj_tac THEN1 fs [Abbr`dd`]
  \\ match_mp_tac dt_ok_pat_compile \\ fs []
  \\ fs [branches_ok_encode]
QED

Theorem pat_ok_encode:
  !y p. pat_ok p y ==> pat_ok (\k n l. k <> 0 ==> p (k-1) n l) (encode y)
Proof
  recInduct pat_ind
  \\ rw [encode_def,pat_ok_def,pattern_litTheory.pat_ok_def]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

Theorem branches_ok_encode_br:
  !m. branches_ok p m ==> branches_ok (\k n l. k <> 0 ==> p (k-1) n l) (MAP encode_br m)
Proof
  Induct \\ fs [branches_ok_def,pattern_litTheory.branches_ok_def]
  \\ Cases \\ fs [branches_ok_def,pattern_litTheory.branches_ok_def,encode_br_def]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs [pat_ok_encode]
QED

Theorem dt_ok_decode:
  !t. dt_ok (λk n l. k ≠ 0 ⇒ p (k - 1) n l) t ==> dt_ok p (decode t)
Proof
  Induct \\ fs [dt_ok_def,decode_def]
  \\ Cases \\ fs [dt_ok_def,decode_def]
  \\ rw [] \\ fs [dt_ok_def,decode_def]
QED

Theorem dt_ok_pat_compile:
  inv_mat m /\ branches_ok p m ==> dt_ok p (pat_compile h m)
Proof
  fs [pat_compile_def] \\ rw []
  \\ imp_res_tac branches_ok_encode_br
  \\ imp_res_tac pattern_litTheory.dt_ok_pat_compile
  \\ pop_assum mp_tac
  \\ impl_tac THEN1
   (fs [inv_mat_def,pattern_litTheory.inv_mat_def,EVERY_MAP]
    \\ fs [EVERY_MEM] \\ qexists_tac `n` \\ rw []
    \\ Cases_on `x` \\ fs [encode_br_def] \\ fs [pattern_litTheory.patterns_def]
    \\ res_tac \\ fs [patterns_def])
  \\ disch_then (qspec_then `h` assume_tac)
  \\ match_mp_tac dt_ok_decode \\ fs []
QED

Theorem app_pos_EL:
  !n xs.
    app_pos refs (Pos n p) (Term k t xs) =
    if n < LENGTH xs then app_pos refs p (EL n xs) else NONE
Proof
  Induct \\ Cases_on `xs` \\ fs [app_pos_def]
QED

val _ = export_theory();
