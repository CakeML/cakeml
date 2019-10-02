(*
  Defines the top-level interface to the pattern-match compiler.
*)
open preamble;
open pattern_litTheory pattern_refsTheory;

val _ = new_theory "pattern_top_level";

val _ = set_grammar_ancestry ["pattern_refs"]

Type kind[local] = ``:num``

(* input syntax -- inherited from previous language *)

(* output syntax *)

Datatype:
  dGuard = PosTest listPos ('literal dTest)
         | Not dGuard | And dGuard dGuard | Or dGuard dGuard
End

Datatype:
  dTree =
    Leaf num
  | Fail
  | TypeFail
  | If ('literal dGuard) dTree dTree
End

(* semantic values -- inherited from previous language *)

(* semantics of input -- inherited from previous language *)

Definition match_def:
  match refs rows v =
    pattern_refs$match refs (MAP (\(p,e). Branch [p] e) rows) [v]
End

(* semantics of output *)

Definition dt_eval_guard_def:
  (dt_eval_guard refs v (PosTest pos test) =
     case (app_list_pos refs [v] pos) of
     | NONE => NONE
     | SOME x => dt_test test x) /\
  (dt_eval_guard refs v (Not g) =
     case dt_eval_guard refs v g of
     | NONE => NONE
     | SOME b => SOME (~b)) /\
  (dt_eval_guard refs v (And g1 g2) =
     case dt_eval_guard refs v g1 of
     | NONE => NONE
     | SOME T => dt_eval_guard refs v g2
     | SOME F => SOME F) /\
  (dt_eval_guard refs v (Or g1 g2) =
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
          If (Or test g2) t1 y2
        else if y2 = t1 then (* if test then t1 else (if g2 then x2 else t1) *)
          If (Or test (Not g2)) t1 x2
        else If test t1 t2
End

Definition smart_If_def:
  smart_If test t1 t2 =
    if t1 = t2 then t1 else
      case destIf t1 of
      | NONE => smart_If' test t1 t2
      | SOME (g1,x1,y1) =>
          if x1 = t2 then (* if test then (if g1 then t2 else y1) else t2 *)
            If (And test (Not g1)) y1 t2
          else if y1 = t2 then (* if test then (if g1 then x1 else t2) else t2 *)
            If (And test g1) x1 t2
          else smart_If' test t1 t2
End

Definition convert_dtree_def:
  convert_dtree (Leaf i) = Leaf i /\
  convert_dtree (Fail) = Fail /\
  convert_dtree (DTypeFail) = TypeFail /\
  convert_dtree (If pos test d1 d2) =
    smart_If (PosTest pos test) (convert_dtree d1) (convert_dtree d2)
End

Definition top_level_pat_compile_def:
  top_level_pat_compile h rows =
    let m = MAP (\(p,e). Branch [p] e) rows in
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

Theorem dt_eval_convert_dtree:
  !t refs v res.
    dt_eval refs [v] t = SOME res ==>
    dt_eval refs v (convert_dtree t) = SOME res
Proof
  Induct \\ fs [dt_eval_def,pattern_refsTheory.dt_eval_def,convert_dtree_def]
  \\ rw []
  \\ match_mp_tac dt_eval_smart_If
  \\ fs [dt_eval_def,dt_eval_guard_def]
  \\ every_case_tac \\ fs []
QED

Theorem pat_compile_correct:
  !rows v res refs h.
    match refs rows v = SOME res ==>
    dt_eval refs v (top_level_pat_compile h rows) = SOME res
Proof
  fs [top_level_pat_compile_def,match_def] \\ rw []
  \\ Cases_on `rows = []`
  THEN1 (rveq \\ fs [] \\ pop_assum mp_tac \\ EVAL_TAC)
  \\ drule pattern_refsTheory.pat_compile_correct
  \\ disch_then (qspec_then `h` mp_tac)
  \\ reverse impl_tac
  THEN1 (fs [dt_eval_convert_dtree])
  \\ conj_tac
  THEN1 (Cases_on `rows` \\ fs [msize_def] \\ Cases_on `h` \\ fs [msize_def])
  \\ fs [inv_mat_def,EVERY_MAP] \\ fs [EVERY_MEM,FORALL_PROD,patterns_def]
  \\ qexists_tac `1` \\ fs []
QED

val _ = export_theory();
