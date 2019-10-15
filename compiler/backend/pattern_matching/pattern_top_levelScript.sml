(*
  Defines the top-level interface to the pattern-match compiler.
*)
open preamble;
open pattern_litTheory pattern_refsTheory;

val _ = new_theory "pattern_top_level";

val _ = set_grammar_ancestry ["pattern_refs"]

Type kind[local] = ``:num``
Type tag[local] = ``:num``
Type siblings[local] = ``:((num # num) list) option``

(* input syntax *)

Datatype:
  pat =
    Any
  | Cons ((tag # siblings) option) (pat list)
  | Or pat pat
  | Lit ast$lit
  | Ref pat
End

(* output syntax *)

Datatype:
  dTest = TagLenEq num num | LitEq ast$lit
End

Datatype:
  dGuard = PosTest position dTest
         | Not dGuard | Conj dGuard dGuard | Disj dGuard dGuard
End

Datatype:
  dTree =
    Leaf num
  | Fail
  | TypeFail
  | If dGuard dTree dTree
End

(* semantic values *)

Datatype:
  term = Term (tag option) (term list)
       | Litv ast$lit
       | RefPtr num
       | Other
End

(* semantics of input *)

Definition pmatch_def:
  (pmatch refs Any t = PMatchSuccess) /\
  (pmatch refs (Lit l) (Litv l') =
     if ~lit_same_type l l' then PTypeFailure else
     if l = l' then PMatchSuccess else PMatchFailure) /\
  (pmatch refs (Cons (SOME (tag,siblings)) pargs) (Term (SOME t) targs) =
    if tag = t /\ LENGTH pargs = LENGTH targs then pmatch_list refs pargs targs else
    if is_sibling (t,LENGTH targs) siblings
    then PMatchFailure else PTypeFailure) /\
  (pmatch refs (Cons NONE pargs) (Term NONE targs) =
    pmatch_list refs pargs targs) /\
  (pmatch refs (Ref p) (RefPtr r) =
    case FLOOKUP refs r of
    | NONE => PTypeFailure
    | SOME v => pmatch refs p v) /\
  (pmatch refs (pattern_top_level$Or p1 p2) t =
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
  (match refs [] v = SOME MatchFailure) /\
  (match refs ((p,e)::rows) v =
    case pmatch refs p v of
       PMatchSuccess =>
         (case match refs rows v of
           NONE => NONE
         | SOME _ => SOME (MatchSuccess e))
     | PMatchFailure => match refs rows v
     | PTypeFailure => NONE)
End

(* semantics of output *)

Definition dt_test_def:
  dt_test (TagLenEq t l) (Term (SOME c) args) =
    SOME (t = c /\ l = LENGTH args) /\
  dt_test (LitEq l1) (Litv l2) =
    (if lit_same_type l1 l2 then SOME (l1 = l2) else NONE) /\
  dt_test _ _ = NONE
End

Definition app_pos_def:
  (app_pos refs EmptyPos p = SOME p) /\
  (app_pos refs (Pos 0 pos) (RefPtr r) =
     case FLOOKUP refs r of
     | NONE => NONE
     | SOME v => app_pos refs pos v) /\
  (app_pos refs (Pos 0 pos) (Term c (x::xs)) = app_pos refs pos x) /\
  (app_pos refs (Pos (SUC n) pos) (Term c (x::xs)) =
    app_pos refs (Pos n pos) (Term c xs)) /\
  (app_pos refs (Pos _ _) _ = NONE)
End

Definition dt_eval_guard_def:
  (dt_eval_guard refs v (PosTest pos test) =
     case app_pos refs pos v of
     | NONE => NONE
     | SOME x => dt_test test x) /\
  (dt_eval_guard refs v (Not g) =
     case dt_eval_guard refs v g of
     | NONE => NONE
     | SOME b => SOME (~b)) /\
  (dt_eval_guard refs v (Conj g1 g2) =
     case dt_eval_guard refs v g1 of
     | NONE => NONE
     | SOME T => dt_eval_guard refs v g2
     | SOME F => SOME F) /\
  (dt_eval_guard refs v (Disj g1 g2) =
     case dt_eval_guard refs v g1 of
     | NONE => NONE
     | SOME T => SOME T
     | SOME F => dt_eval_guard refs v g2)
End

Definition dt_eval_def:
  (dt_eval refs _ (Leaf k) = SOME (MatchSuccess k)) /\
  (dt_eval refs _ Fail = SOME (MatchFailure)) /\
  (dt_eval refs _ TypeFail = NONE) /\
  (dt_eval refs v (If guard dt1 dt2) =
     case dt_eval_guard refs v guard of
     | NONE => NONE
     | SOME b => dt_eval refs v (if b then dt1 else dt2))
End

(* pattern compiler -- built around the previous one *)

Definition destIf_def:
  destIf (If test t1 t2) = SOME (test,t1,t2) /\
  destIf _ = NONE
End

Definition smart_If'_def:
  smart_If' test t1 t2 =
    case destIf t2 of
    | NONE => If test t1 t2
    | SOME (g2,x2,y2) =>
        if x2 = t1 then (* if test then t1 else (if g2 then t1 else y2) *)
          If (Disj test g2) t1 y2
        else if y2 = t1 then (* if test then t1 else (if g2 then x2 else t1) *)
          If (Disj test (Not g2)) t1 x2
        else If test t1 t2
End

Definition smart_If_def:
  smart_If test t1 t2 =
    if t1 = t2 then t1 else
      case destIf t1 of
      | NONE => smart_If' test t1 t2
      | SOME (g1,x1,y1) =>
          if x1 = t2 then (* if test then (if g1 then t2 else y1) else t2 *)
            If (Conj test (Not g1)) y1 t2
          else if y1 = t2 then (* if test then (if g1 then x1 else t2) else t2 *)
            If (Conj test g1) x1 t2
          else smart_If' test t1 t2
End

Definition convert_dtree_def:
  convert_dtree (Leaf i) = Leaf i /\
  convert_dtree (Fail) = Fail /\
  convert_dtree (DTypeFail) = TypeFail /\
  convert_dtree (pattern_lit$If (_,p) (LitEq lit) d1 d2) =
    smart_If (PosTest p (LitEq lit)) (convert_dtree d1) (convert_dtree d2) /\
  convert_dtree (pattern_lit$If (_,p) (TagLenEq k t l) d1 d2) =
    if k = 0 then
      smart_If (PosTest p (TagLenEq t l)) (convert_dtree d1) (convert_dtree d2)
    else convert_dtree d1
End

Definition encode_def:
  (encode Any = pattern_refs$Any) /\
  (encode (Ref p) = Ref (encode p)) /\
  (encode (Or p1 p2) = Or (encode p1) (encode p2)) /\
  (encode (Lit l) = Lit l) /\
  (encode (Cons NONE pargs) = Cons (LENGTH pargs + 1) 0 NONE (MAP encode pargs)) /\
  (encode (Cons (SOME (t,sib)) pargs) = Cons 0 t sib (MAP encode pargs))
Termination
  WF_REL_TAC `measure pat_size` \\ fs []
  \\ qsuff_tac `∀pargs a. MEM a pargs ⇒ pat_size a < pat1_size pargs`
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ Induct \\ fs [fetch "-" "pat_size_def"]
  \\ rw [] \\ res_tac \\ fs [fetch "-" "pat_size_def"]
End

Definition top_level_pat_compile_def:
  top_level_pat_compile h rows =
    let m = MAP (\(p,e). Branch [encode p] e) rows in
    let t = pattern_refs$pat_compile h m in
      convert_dtree t
End

(* correctness proof *)

Theorem dt_eval_smart_If':
  dt_eval refs v (If test t1 t2) = SOME res ==>
  dt_eval refs v (smart_If' test t1 t2) = SOME res
Proof
  fs [smart_If'_def] \\ rw []
  \\ Cases_on `destIf t2` \\ fs [] \\ PairCases_on `x` \\ fs []
  \\ Cases_on `t2` \\ fs [] \\ fs [destIf_def] \\ rveq \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [dt_eval_def,dt_eval_guard_def]
  \\ CASE_TAC \\ fs [] \\ fs []
  \\ fs [dt_eval_def,dt_eval_guard_def]
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ rfs [dt_eval_def] \\ fs []
  \\ CASE_TAC \\ fs []
  \\ fs [dt_eval_def,dt_eval_guard_def] \\ rfs []
  \\ CASE_TAC \\ rfs [dt_eval_def] \\ fs []
QED

Theorem dt_eval_smart_If:
  dt_eval refs v (If test t1 t2) = SOME res ==>
  dt_eval refs v (smart_If test t1 t2) = SOME res
Proof
  Cases_on `(smart_If test t1 t2) = (smart_If' test t1 t2)`
  THEN1 metis_tac [dt_eval_smart_If']
  \\ fs [smart_If_def] \\ rw []
  THEN1 (fs [dt_eval_def,option_case_eq])
  \\ Cases_on `destIf t1` \\ fs [] \\ PairCases_on `x` \\ fs []
  \\ Cases_on `t1` \\ fs [] \\ fs [destIf_def] \\ rveq \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [dt_eval_def,dt_eval_guard_def]
  \\ CASE_TAC \\ fs [] \\ fs []
  \\ fs [dt_eval_def,dt_eval_guard_def]
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ rfs [dt_eval_def]
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ rfs [dt_eval_def]
QED

Definition embed_def:
  embed Other = pattern_refs$Other /\
  embed (Litv l) = Litv l /\
  embed (RefPtr r) = RefPtr r /\
  embed (Term opt xs) =
    let ys = MAP embed xs in
      case opt of
      | NONE => Term (LENGTH xs + 1) 0 ys
      | SOME t => Term 0 t ys
Termination
  WF_REL_TAC `measure term_size` \\ gen_tac
  \\ Induct_on `xs` \\ fs [fetch "-" "term_size_def"]
  \\ rw [] \\ res_tac \\ fs []
End

Definition ref_map_def:
  ref_map f refs = FUN_FMAP (\n. f (refs ' n)) (FDOM refs)
End

Theorem app_pos_EL:
  !n xs.
    app_pos refs (Pos n p) (Term t xs) =
    if n < LENGTH xs then app_pos refs p (EL n xs) else NONE
Proof
  Induct \\ Cases_on `xs` \\ fs [app_pos_def]
QED

Theorem app_pos_embed:
  !refs p v x.
    app_pos (ref_map embed refs) p (embed v) = SOME x ==>
    ?w. x = embed w /\ app_pos refs p v = SOME w
Proof
  Induct_on `p`
  \\ fs [app_pos_def,embed_def,pattern_refsTheory.app_pos_def]
  \\ reverse (Cases_on `v`)
  \\ fs [app_pos_def,embed_def,pattern_refsTheory.app_pos_def]
  THEN1
   (Cases \\ fs [app_pos_def,pattern_refsTheory.app_pos_def] \\ rw []
    \\ fs [ref_map_def,FLOOKUP_FUN_FMAP,FLOOKUP_DEF] \\ IF_CASES_TAC \\ fs []
    \\ fs [FUN_FMAP_DEF])
  \\ every_case_tac
  \\ fs [pattern_refsTheory.app_pos_EL,GSYM AND_IMP_INTRO] \\ fs [EL_MAP]
  \\ rw [] \\ res_tac \\ fs [] \\ qexists_tac `w` \\ fs [app_pos_EL]
QED

Theorem dt_eval_convert_dtree:
  !t refs v res.
    dt_eval (ref_map embed refs) [embed v] t = SOME res /\
    dt_ok (\k t l. k <> 0 ==> t = 0 /\ k = l + 1) t ==>
    dt_eval refs v (convert_dtree t) = SOME res
Proof
  Induct \\ fs [dt_eval_def,pattern_refsTheory.dt_eval_def,convert_dtree_def]
  \\ rpt gen_tac \\ rename [`If pos test`]
  \\ Cases_on `test` \\ fs [option_case_eq]
  \\ strip_tac \\ Cases_on `pos` \\ fs [convert_dtree_def]
  \\ Cases_on `q` \\ fs [app_list_pos_def]
  \\ drule app_pos_embed \\ strip_tac \\ rveq \\ fs []
  \\ TRY (reverse IF_CASES_TAC)
  \\ fs [dt_ok_def] \\ rveq \\ fs []
  THEN1
   (Cases_on `b` \\ fs []
    \\ Cases_on `w` \\ fs [dt_test_def,embed_def]
    \\ every_case_tac \\ fs [pattern_refsTheory.dt_test_def])
  \\ match_mp_tac dt_eval_smart_If
  \\ Cases_on `w`
  \\ fs [dt_eval_def,dt_eval_guard_def,dt_test_def,embed_def,pattern_refsTheory.dt_test_def]
  \\ every_case_tac
  \\ fs [dt_eval_def,dt_eval_guard_def,dt_test_def,embed_def,pattern_refsTheory.dt_test_def]
QED

Theorem pmatch_list_LENGTH_IMP:
  !ps vs refs.
    LENGTH ps ≠ LENGTH vs ==>
    pmatch_list refs ps vs = PTypeFailure
Proof
  Induct \\ Cases_on `vs` \\ fs [pmatch_def,CaseEq"pmatchResult"]
  \\ rw [] \\ Cases_on `pmatch refs h' h` \\ fs []
QED

Theorem pmatch_encode:
  (!refs p (v:term) res.
     pmatch refs p v = res ==>
     pmatch (ref_map embed refs) (encode p) (embed v) = res) /\
  (!refs ps (vs:term list) res.
     pmatch_list refs ps vs = res ==>
     pmatch_list (ref_map embed refs) (MAP encode ps) (MAP embed vs) = res)
Proof
  ho_match_mp_tac pmatch_ind \\ fs [FORALL_PROD] \\ rw []
  \\ fs [encode_def,pmatch_def,pattern_refsTheory.pmatch_def,embed_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  THEN1 (IF_CASES_TAC \\ fs [])
  THEN1 (IF_CASES_TAC \\ fs [] \\ imp_res_tac pmatch_list_LENGTH_IMP \\ fs [])
  THEN1 (fs [ref_map_def,FLOOKUP_FUN_FMAP,FLOOKUP_DEF] \\ IF_CASES_TAC \\ fs []
         \\ fs [FUN_FMAP_DEF])
  THEN1 (TOP_CASE_TAC \\ fs [])
  \\ TRY (rename [`Cons x`] \\ Cases_on `x`
    \\ fs [encode_def,pattern_refsTheory.pmatch_def]
    \\ rename [`SOME x`] \\ PairCases_on `x`
    \\ fs [pattern_refsTheory.pmatch_def,encode_def])
  \\ every_case_tac
  \\ fs [pattern_refsTheory.pmatch_def,encode_def]
QED

Theorem match_encode:
  !refs rows v res.
    match refs rows v = SOME res ==>
    match (ref_map embed refs) (MAP (\(p,e). Branch [encode p] e) rows) [embed v] = SOME res
Proof
  Induct_on `rows` \\ fs [FORALL_PROD]
  \\ fs [match_def,pattern_refsTheory.match_def]
  \\ rpt gen_tac
  \\ TOP_CASE_TAC
  \\ fs [option_case_eq] \\ rpt strip_tac \\ rveq \\ fs []
  \\ res_tac \\ fs []
  \\ imp_res_tac pmatch_encode
  \\ fs [pattern_refsTheory.pmatch_def]
QED

Theorem pat_compile_correct:
  !rows v res refs h.
    match refs rows v = SOME res ==>
    dt_eval refs v (top_level_pat_compile h rows) = SOME res
Proof
  fs [top_level_pat_compile_def] \\ rw []
  \\ drule match_encode \\ strip_tac
  \\ Cases_on `rows = []`
  THEN1 (rveq \\ fs [] \\ pop_assum mp_tac \\ EVAL_TAC)
  \\ drule pattern_refsTheory.pat_compile_correct
  \\ disch_then (qspec_then `h` mp_tac)
  \\ reverse impl_keep_tac
  THEN1
    (rw [] \\ match_mp_tac dt_eval_convert_dtree \\ fs []
     \\ match_mp_tac dt_ok_pat_compile \\ fs []
     \\ qpat_x_assum `1 = _` (assume_tac o GSYM) \\ fs []
     \\ rpt (pop_assum kall_tac)
     \\ Induct_on `rows` \\ fs [branches_ok_def,FORALL_PROD,msize_def]
     \\ recInduct encode_ind
     \\ fs [encode_def,pat_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS])
  \\ conj_tac
  THEN1 (Cases_on `rows` \\ fs [msize_def] \\ Cases_on `h` \\ fs [msize_def])
  \\ fs [inv_mat_def,EVERY_MAP] \\ fs [EVERY_MEM,FORALL_PROD,patterns_def]
  \\ qexists_tac `1` \\ fs []
QED

val _ = export_theory();
