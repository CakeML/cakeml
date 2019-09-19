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
  | Cons kind num (num option) (pat list)
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

Definition pmatch_def:
  (pmatch Any t = PMatchSuccess) /\
  (pmatch (Lit k l) (Litv k' l') =
     if k <> k' then PTypeFailure else
     if l = l' then PMatchSuccess else PMatchFailure) /\
  (pmatch (Cons k pcons _ pargs) (Term k' tcons targs) =
    if k <> k' then PTypeFailure else
    if pcons = tcons
    then pmatch_list pargs targs
    else PMatchFailure) /\
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
  (app_pos (Pos _ _) Other = NONE) /\
  (app_pos (Pos _ _) (Term k c []) = NONE) /\
  (app_pos (Pos 0 pos) (Term k c (x::xs)) = app_pos pos x) /\
  (app_pos (Pos (SUC n) pos) (Term k c (x::xs)) =
    app_pos (Pos n pos) (Term k c xs))
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

Theorem pat_compile_correct:
  !h m v res.
    match m v = SOME res /\ LENGTH v = msize m /\ inv_mat m ==>
    dt_eval v (pattern_lit$pat_compile h m) = SOME res
Proof
  fs [pat_compile_def] \\ rw []
  \\ qabbrev_tac `lits = all_lits m []`
  (* pattern_matchingTheory.pat_compile_correct *)
  \\ cheat
QED

val _ = export_theory();
