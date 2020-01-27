(*
  The syntax and semantics of the input and output to the
  pattern-match compiler.
*)
open preamble astTheory semanticPrimitivesTheory pattern_commonTheory;

val _ = new_theory "pattern_semantics";

val _ = set_grammar_ancestry ["pattern_common", "semanticPrimitives"];


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
Definition is_sibling_def:
  is_sibling x NONE = T /\
  is_sibling x (SOME l) = MEM x l
End

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
  (app_pos refs EmptyPos v = SOME v) /\
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

val _ = export_theory();
