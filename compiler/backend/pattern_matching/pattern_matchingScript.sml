(*
  Pattern-matching compilation to decision trees
  See issue #667 for details and references
*)
open preamble;
open numTheory listTheory arithmeticTheory;

val _ = new_theory "pattern_matching";

(*
Definition of terms
Every term is a constructor with 0 or more arguments
Constructors are identified by num
Constructors have a kind

Term kind cons-id args
*)
Datatype:
  term = Term num num (term list) | Other
End

Definition get_cons_def:
  (get_cons (Term _ c ts) = SOME (c, LENGTH ts)) /\
  (get_cons Other = NONE)
End

(*
A position describes a path to a sub-term in a term
*)
Datatype:
  position =
    EmptyPos
  | Pos num position
End

Definition app_pos_def:
  (app_pos EmptyPos p = SOME p) /\
  (app_pos (Pos _ _) Other = NONE) /\
  (app_pos (Pos _ _) (Term _ c []) = NONE) /\
  (app_pos (Pos 0 pos) (Term _ c (x::xs)) =
    app_pos pos x) /\
  (app_pos (Pos (SUC n) pos) (Term k c (x::xs)) =
    app_pos (Pos n pos) (Term k c xs))
End

Definition snoc_pos_def:
  (snoc_pos n EmptyPos = (Pos n EmptyPos)) /\
  (snoc_pos n (Pos m pos) = (Pos m (snoc_pos n pos)))
End

(* a list position describes a path to a sub-term in a list of term *)
Type listPos = ``:(num # position)``

Definition app_list_pos_def:
  (app_list_pos [] (_,_) = NONE) /\
  (app_list_pos (x::xs) (0, pos)  =
    app_pos pos x) /\
  (app_list_pos (x::xs) (SUC n, pos) =
    app_list_pos xs (n, pos))
End

Theorem app_list_pos_drop:
  !v p. app_list_pos v ((LENGTH v), p) = app_list_pos (DROP (LENGTH v) v) (0, p)
Proof
  Induct_on `v` \\
  EVAL_TAC \\ rw[]
QED

Definition apply_positions_def:
  (apply_positions _ [] = []) /\
  (apply_positions [] _ = []) /\
  (apply_positions positions values = MAP (app_list_pos values) positions)
End

Theorem apply_positions_length:
  !p v. (LENGTH v) = (LENGTH p) ==> LENGTH (apply_positions p v) = LENGTH p
Proof
  rpt Cases \\ fs[apply_positions_def]
QED;


(*
definition of full patterns with as clauses
Variables are identified by num
*)
Datatype:
  pat =
    Any
  (* A constructor pattern is a kind, a constructor id, the number of constructors
     in its type and a list of other patterns
     If the number of constructor in its type is NONE, it means it can be
     infinite, and we have to assume it is never exhaustive
  *)
  | Cons num num (num option) (pat list)
  | Or pat pat
End

(*
Represent a branch (p => e) in a match expression
the result expression is just a number for now
*)
Datatype:
  branch = Branch (pat list) num
End

Definition patterns_def:
  patterns (Branch ps e) = ps
End

Definition expr_def:
  expr (Branch ps e) = e
End

(* pattern matrix *)
Type patmat = ``:branch list``

(* Invariant of pattern matrices *)
Definition inv_mat_aux_def:
  (inv_mat [] = T) /\
  (inv_mat [x] = T) /\
  (inv_mat ((Branch l1 e1)::(Branch l2 e2)::m) =
    ((LENGTH l1 = LENGTH l2) /\ (inv_mat ((Branch l2 e2)::m))))
End

Theorem inv_mat_def:
  !m. inv_mat m = ?n. EVERY (\l. (LENGTH (patterns l)) = n) m
Proof
  Induct_on `m`
  >- (rw[] \\ fs[inv_mat_aux_def])
  >- (rw[] \\ EQ_TAC \\ rw[]
      >- (Cases_on `m`
          >- fs[inv_mat_aux_def]
          >- (Cases_on `h` \\
              Cases_on `h'` \\
              fs[inv_mat_aux_def, patterns_def]))
      >- (Cases_on `m`
          >- fs[inv_mat_aux_def]
          >- (Cases_on `h` \\
              Cases_on `h'` \\
              fs[inv_mat_aux_def, patterns_def])))
QED;

Theorem inv_mat_dcmp:
  !b m. inv_mat (b::m) ==> inv_mat m
Proof
  rw[inv_mat_def] \\
  qexists_tac `LENGTH (patterns b)` \\
  rw[]
QED;

Theorem inv_mat_cons:
  !b m. inv_mat (b::m) ==> inv_mat [b]
Proof
  rw[inv_mat_def]
QED;

Theorem inv_mat_or1:
  !p1 p2 ps e m. inv_mat ((Branch (Or p1 p2::ps) e)::m) ==>
                 inv_mat ((Branch (p1::ps) e)::m)
Proof
  rw[inv_mat_def, patterns_def]
QED;

Theorem inv_mat_or2:
  !p1 p2 ps e m. inv_mat ((Branch (Or p1 p2::ps) e)::m) ==>
                 inv_mat ((Branch (p2::ps) e)::m)
Proof
  rw[inv_mat_def, patterns_def]
QED;

(*
The size of a pattern matrix is the number of patterns
in each branch. It makes sense only for matrices that
respect the invariant.
*)
Definition msize_def:
  (msize [] = 0) /\
  (msize ((Branch l e)::bs) = LENGTH l)
End

Theorem msize_inv:
  !m b x. inv_mat (b::m) /\
          m <> [] /\
          (msize (b::m) = x) ==>
          (msize m = x)
Proof
  rw[msize_def, inv_mat_def] \\
  Cases_on `b` \\
  fs[patterns_def] \\
  Cases_on `m`
  >- fs[]
  >- (fs[msize_def, EVERY_DEF] \\
      Cases_on `h` \\
      fs[patterns_def, msize_def])
QED;

Theorem msize_inv':
  !m b. inv_mat (b::m) /\
          m <> [] ==>
          (msize (b::m) = msize m)
Proof
  rw[] \\
  imp_res_tac msize_inv \\
  rpt (first_x_assum (qspec_then `msize (b::m)` assume_tac)) \\
  fs[]
QED;

Theorem msize_cons:
  !b bs. msize (b::bs) = msize [b]
Proof
  Cases_on `b` \\ rw[msize_def]
QED;

Theorem msize_app:
  !xs ys. xs <> [] ==>
          msize (xs ++ ys) =
          msize xs
Proof
  Cases_on `xs`
  >- rw[]
  >- (rw[] \\
      Cases_on `h` \\
      fs[msize_def])
QED;

Theorem msize_app2:
  !xs ys. xs = [] ==>
          msize (xs ++ ys) =
          msize ys
Proof
  rw[]
QED;

Theorem msize_inv_gt_zero:
  !m b x. inv_mat (b::m) /\
          m <> [] /\
          (msize (b::m) > x) ==>
          (msize m > x)
Proof
  rw[msize_def, inv_mat_def] \\
  Cases_on `b` \\
   fs[patterns_def] \\
  Cases_on `m`
  >- fs[]
  >- (fs[msize_def, EVERY_DEF] \\
      Cases_on `h` \\
      fs[patterns_def, msize_def])
QED;

Theorem inv_mat_recompose:
  !b m. inv_mat m /\
        (LENGTH (patterns b)) = (msize m) ==>
        inv_mat (b::m)
Proof
  Cases_on `m`
  >- fs[inv_mat_aux_def]
  >- (Cases_on `b` \\ fs[patterns_def] \\
      Cases_on `h` \\
      rw[msize_def, inv_mat_aux_def])
QED;

Theorem inv_mat_fst:
  !b m. inv_mat (b::m) /\ m <> [] ==> msize [b] = msize m
Proof
  Cases_on `m`
  >- fs[]
  >- (rw[inv_mat_aux_def, msize_def] \\
      Cases_on `b` \\
      Cases_on `h` \\
      fs[inv_mat_aux_def, msize_def])
QED;

(*
We parametrize the size function by an arity a to take into account the fact
that a Any or a Var can be expanded into a list of Any patterns
*)
Definition psize_def:
  (psize Any = (1:num)) /\
  (psize (Cons _ n t []) = 2) /\
  (psize (Cons k n t (x::xs)) = 1 + (psize x) + psize (Cons k n t xs)) /\
  (psize (Or p1 p2) = 1 + (psize p1) + (psize p2))
End

Definition plist_size_def:
  (plist_size [] = 1) /\
  (plist_size (p::ps) = psize p + plist_size ps)
End

Theorem psize_gt_zero:
  !p. 0 < (psize p)
Proof
  ho_match_mp_tac (theorem "psize_ind") \\ rw[psize_def, ZERO_LESS_ADD]
QED

Theorem plist_size_gt_zero:
  !ps. 0 < plist_size ps
Proof
  Cases_on `ps` \\
  fs[plist_size_def, psize_gt_zero, ZERO_LESS_ADD]
QED

(* Semantics of matching *)
Datatype:
  pmatchResult =
    PMatchSuccess
  | PMatchFailure
  | PTypeFailure
End

Definition pmatch_def:
  (pmatch Any t = PMatchSuccess) /\
  (pmatch (Cons _ _ _ _) Other = PTypeFailure) /\
  (pmatch (Cons pkind pcons _ pargs) (Term tkind tcons targs) =
    if pkind = tkind then
      (if pcons = tcons
       then pmatch_list pargs targs
       else PMatchFailure)
    else PTypeFailure) /\
  (pmatch (Or p1 p2) t =
    case pmatch p1 t of
       PMatchSuccess => (case pmatch p2 t of
                           PTypeFailure => PTypeFailure
                         | _ => PMatchSuccess)
     | PMatchFailure => pmatch p2 t
     | PTypeFailure => PTypeFailure) /\
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
  WF_REL_TAC `measure (\x. case x of INL(p,t) => psize p
                                    | INR(ps,ts) => plist_size ps)` \\ rw[]
  >- fs[plist_size_def, plist_size_gt_zero]
  >- fs[plist_size_def, psize_gt_zero]
  >- fs[plist_size_def, psize_gt_zero]
  >- (Induct_on `pargs` \\ fs[plist_size_def, psize_def])
  >- fs[psize_def]
  >- fs[psize_def]
  >- fs[psize_def]
End

Theorem pmatch_list_app:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PMatchSuccess ==>
    (pmatch_list t1 p1 = PMatchSuccess /\
     pmatch_list t2 p2 = PMatchSuccess)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      first_x_assum (qspecl_then [`t`,`p2`,`t2`] assume_tac) \\
      fs[] \\ rfs[])
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      first_x_assum (qspecl_then [`t`,`p2`,`t2`] assume_tac) \\
      fs[])
QED;

Theorem pmatch_list_app2:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t1 p1 = PMatchSuccess /\
    pmatch_list t2 p2 = PMatchSuccess ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PMatchSuccess
Proof
  Induct_on `t1`
  >- fs[]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      rw[] \\ every_case_tac \\ fs[]
      >- (res_tac \\ fs[])
      >- (res_tac \\ fs[]))
QED

Theorem npmatch_list_app:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PMatchFailure ==>
    (pmatch_list t1 p1 = PMatchFailure \/
     pmatch_list t2 p2 = PMatchFailure)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[]
      >- (res_tac \\ fs[] \\ fs[])
      >- (res_tac \\ fs[] \\ fs[])
      >- (imp_res_tac pmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\
          fs[])
      >- (res_tac \\ fs[] \\ fs[]))
QED

Theorem nmatch_list_app2:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    ((pmatch_list t1 p1 = PMatchFailure /\
      pmatch_list t2 p2 <> PTypeFailure) \/
     (pmatch_list t1 p1 <> PTypeFailure /\
      pmatch_list t2 p2 = PMatchFailure)) ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PMatchFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[]
      >- (res_tac \\ fs[] \\ fs[])
      >- (res_tac \\ fs[] \\ fs[])
      >- (Cases_on `pmatch_list t2 p2`
          >- (imp_res_tac pmatch_list_app2 \\
              fs[])
          >- (res_tac \\ fs[] \\ fs[])
          >- fs[])
      >- (Cases_on `pmatch_list t2 p2`
          >- (res_tac \\ fs[] \\ fs[])
          >- (res_tac \\ fs[] \\ fs[])
          >- fs[]))
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem tfpmatch_list_app:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PTypeFailure ==>
    (pmatch_list t1 p1 = PTypeFailure \/
     pmatch_list t2 p2 = PTypeFailure)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem tfpmatch_list_app2:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    (pmatch_list t1 p1 = PTypeFailure \/
     pmatch_list t2 p2 = PTypeFailure) ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PTypeFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem npmatch_list_app21:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t1 p1 = PMatchFailure ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) <> PMatchSuccess
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (fs[pmatch_def] \\
      Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem npmatch_list_app22:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t2 p2 = PMatchFailure ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) <> PMatchSuccess
Proof
  Induct_on `t1` \\ rw[] \\
  fs[pmatch_def] \\
  Cases_on `p1` \\ fs[pmatch_def] \\
  every_case_tac \\ fs[] \\
  res_tac \\ fs[] \\ fs[]
QED


Theorem pmatch_list_length:
  !ps ts. pmatch_list ps ts <> PTypeFailure ==>
          (LENGTH ps = LENGTH ts)
Proof
  Induct_on `ps`
  >- (Cases_on `ts` \\
      fs[pmatch_def])
  >- (Cases_on `ts` \\
      fs[pmatch_def] \\
      Cases_on `pmatch h' h` \\
      rw[] \\
      every_case_tac \\ fs[])
QED;

Theorem pmatch_list_app_cases:
  !p1 p2 t1 t2.
    LENGTH p1 = LENGTH t1 /\
    LENGTH p2 = LENGTH t2 ==>
    pmatch_list (p1 ++ p2) (t1 ++ t2) =
    case pmatch_list p1 t1 of
      PMatchSuccess => pmatch_list p2 t2
    | PMatchFailure => (case pmatch_list p2 t2 of
                          PTypeFailure => PTypeFailure
                        | _ => PMatchFailure)
    | PTypeFailure => PTypeFailure
Proof
  rw[] \\
  every_case_tac \\ fs[]
  >- (ho_match_mp_tac pmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_app2 \\ rw[])
QED

Theorem pmatch_list_or:
  !ps p1 p2 ts. pmatch_list ((Or p1 p2)::ps) ts = PMatchSuccess ==>
                (pmatch_list (p1::ps) ts = PMatchSuccess) \/
                (pmatch_list (p2::ps) ts = PMatchSuccess)
Proof
  rw[] \\
  Cases_on `ts` \\ fs[pmatch_def] \\
  every_case_tac \\ fs[]
QED;

Theorem not_pmatch_list_or:
  !ps p1 p2 ts. pmatch_list ((Or p1 p2)::ps) ts = PMatchFailure ==>
                (pmatch_list (p1::ps) ts = PMatchFailure) \/
                (pmatch_list (p2::ps) ts = PMatchFailure)
Proof
  rw[] \\
  Cases_on `ts` \\ fs[pmatch_def] \\
  every_case_tac \\ fs[]
QED;

(*
  Pattern matching can return three results :
    - Success, with the number of the right hand side that succeeded
    - MatchFailure, when no branch has matched the value
    - TypeFailure, when there was a type mismatch between the value
      to be matched and the patterns
*)
Datatype:
  matchResult =
    MatchSuccess num
  | MatchFailure
End

(* Returns (SOME result) if the matching could be executed
   properly, and NONE if there was a type failure *)
Definition match_def:
  (match [] ts = SOME MatchFailure) /\
  (match ((Branch ps e)::bs) ts =
    case pmatch_list ps ts of
       PMatchSuccess =>
         (* A pattern matching success is valid only if
            matching on the other branches doesn't produce
            any type errors *)
         (case match bs ts of
           NONE => NONE
         | SOME _ => SOME (MatchSuccess e))
     | PMatchFailure => match bs ts
     | PTypeFailure => NONE)
End

Theorem match_no_values:
  !m. inv_mat m /\
      msize m = 0 ==>
      IS_SOME (match m [])
Proof
  rw[] \\
  Induct_on `m`
  >- fs[match_def]
  >- (rw[] \\
      Cases_on `h` \\
      Cases_on `l` \\
      fs[match_def, pmatch_def] \\
      Cases_on `m`
      >- fs[match_def]
      >- (fs[match_def] \\
          imp_res_tac msize_inv \\ fs[] \\
          imp_res_tac inv_mat_dcmp \\ fs[] \\
          Cases_on `match (h::t) []` \\ fs[])
      >- fs[msize_def]
      >- fs[msize_def])
QED



Theorem match_eq_length:
  !m vs r. inv_mat m /\
           match m vs = SOME (MatchSuccess r) ==>
           (msize m) = LENGTH vs
Proof
  Induct_on `m` \\
  rw[match_def] \\
  Cases_on `m`
  >- (Cases_on `h` \\
      fs[msize_def, match_def] \\
      every_case_tac \\ fs[pmatch_list_length])
  >- (Cases_on `h` \\
      fs[match_def] \\
      every_case_tac
      >- (imp_res_tac pmatch_list_length \\ fs[msize_def])
      >- (imp_res_tac pmatch_list_length \\ fs[msize_def])
      >- (imp_res_tac pmatch_list_length \\ fs[msize_def])
      >- fs[pmatch_list_length, msize_def]
      >- (fs[] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv \\
          fs[])
      >- fs[])
QED;

Theorem match_first_patlist:
  !ps ts e xs.
    pmatch_list ps ts = PMatchSuccess /\
    IS_SOME (match xs ts) ==>
    match ((Branch ps e)::xs) ts = SOME (MatchSuccess e)
Proof
  rw[] \\
  Cases_on `ps` \\
  rw[match_def] \\
  every_case_tac \\ fs[]
QED;

Theorem nmatch_first_patlist:
  !ps ts e xs.
    pmatch_list ps ts = PMatchFailure ==>
    match ((Branch ps e)::xs) ts = match xs ts
Proof
  rw[] \\
  Cases_on `ps` \\
  rw[match_def]
QED;

Theorem match_first_patlist2:
  !ps ts e xs.
    IS_SOME (match ((Branch ps e)::xs) ts) ==>
    (pmatch_list ps ts = PMatchFailure \/
     pmatch_list ps ts = PMatchSuccess)
Proof
  rw[match_def] \\ every_case_tac \\ fs[]
QED

Theorem tfmatch_app:
  !b1 ts b2.
    IS_SOME (match b1 ts) /\
    IS_SOME (match b2 ts) ==>
    IS_SOME (match (b1++b2) ts)
Proof
  Induct_on `b1`
  >- fs[]
  >- (fs[] \\
      Cases_on `h` \\ rw[match_def] \\
      every_case_tac \\ rw[]
      >- (`IS_SOME (match b1 ts)` by fs[] \\
          res_tac \\ metis_tac[IS_SOME_DEF])
      >- (res_tac \\ metis_tac[IS_SOME_DEF]))
QED

Theorem match_app:
  !b1 ts b2 x.
    match b1 ts = SOME (MatchSuccess x) /\
    IS_SOME (match b2 ts) ==>
    match (b1 ++ b2) ts = SOME (MatchSuccess x)
Proof
  ho_match_mp_tac (theorem "match_ind") \\ rw[]
  >- fs[match_def]
  >- (fs[match_def] \\
      every_case_tac \\
      rw[]
      >- metis_tac[tfmatch_app, IS_SOME_DEF]
      >- metis_tac[tfmatch_app, IS_SOME_DEF]
      >- (res_tac \\ fs[]))
QED;

Theorem match_app2:
  !b1 ts b2.
    match b1 ts = SOME MatchFailure ==>
    match (b1 ++ b2) ts = match b2 ts
Proof
  ho_match_mp_tac (theorem "match_ind") \\ rw[] \\
  fs[match_def] \\
  every_case_tac \\ fs[]
QED;

Theorem nmatch_app:
  !b1 ts b2.
    match b1 ts = SOME MatchFailure /\
    match b2 ts = SOME x ==>
    match (b1 ++ b2) ts = SOME x
Proof
  ho_match_mp_tac (theorem "match_ind") \\ rw[] \\
  rw[match_def] \\
  TOP_CASE_TAC
  >- (TOP_CASE_TAC
      >- (fs[match_def] \\
          Cases_on `match b1 ts` \\ fs[])
      >- (fs[match_def] \\
          Cases_on `match b1 ts` \\ fs[]))
  >- (fs[] \\
      first_x_assum ho_match_mp_tac \\ rw[] \\
      fs[match_def])
  >- fs[match_def]
QED


Theorem tf_first_branch:
  !b e bs ts.
    IS_SOME (match (Branch b e::bs) ts) ==>
    IS_SOME (match [Branch b e] ts)
Proof
  rw[match_def] \\
  every_case_tac \\ fs[]
QED

Theorem tf_or:
  !p1 p2 ps e bs ts.
    IS_SOME (match (Branch (Or p1 p2::ps) e::bs) ts) ==>
    IS_SOME (match (Branch (p1::ps) e::bs) ts) /\
    IS_SOME (match (Branch (p2::ps) e::bs) ts)
Proof
  rw[match_def] \\
  every_case_tac \\ fs[] \\
  Cases_on `ts` \\ fs[pmatch_def] \\
  every_case_tac \\ fs[]
QED

Theorem tf_dcmp:
  !b bs ts.
    IS_SOME (match (b::bs) ts) ==>
    IS_SOME (match bs ts)
Proof
  Cases_on `b` \\ rw[match_def] \\
  every_case_tac \\ fs[]
QED

Theorem tf_app:
  !b1 b2 ts.
    IS_SOME (match b1 ts) /\
    IS_SOME (match b2 ts) ==>
    IS_SOME (match (b1++b2) ts)
Proof
  rw[] \\
  Induct_on `b1` \\ rw[] \\
  Cases_on `h` \\
  fs[match_def] \\
  every_case_tac \\ fs[]
QED

Definition n_any_def:
  (n_any 0 = []) /\
  (n_any (SUC n) = Any::(n_any n))
End

Theorem pmatch_list_nany:
  !t. pmatch_list (n_any (LENGTH t)) t = PMatchSuccess
Proof
  Induct_on `t` \\
  rw[pmatch_def, n_any_def, pmatch_def]
QED;

Theorem n_any_length:
  !n. LENGTH (n_any n) = n
Proof
  Induct_on `n` \\
  rw[n_any_def]
QED;


(* Specialization of a pattern matrix for a constructor c of arity a *)
Definition spec_def:
  (spec c a [] = []) /\
  (spec c a ((Branch (Any::ps) e)::rs) =
    (Branch ((n_any a)++ps) e)::(spec c a rs)) /\
  (spec c a ((Branch ((Cons _ pcons _ pargs)::ps) e)::rs) =
    if (c = pcons /\ (a = LENGTH pargs))
    then (Branch (pargs++ps) e)::(spec c a rs)
    else (spec c a rs)) /\
  (spec c a ((Branch ((Or p1 p2)::ps) e)::rs) =
    (spec c a [Branch (p1::ps) e]) ++
    (spec c a [Branch (p2::ps) e]) ++
    (spec c a rs))
End

(* Show that spec preserves type safety *)
Theorem spec_tf:
  !c a m ts targs k.
    a = LENGTH targs /\
    inv_mat m /\
    msize m = (LENGTH ts) + 1 /\
    IS_SOME (match m ((Term k c targs)::ts)) ==>
    IS_SOME (match (spec c a m) (targs ++ ts))
Proof
  ho_match_mp_tac (theorem "spec_ind") \\ rw[]
  >- fs[match_def, spec_def]
  >- (imp_res_tac tf_dcmp \\
      res_tac \\ fs[] \\
      rw[match_def, spec_def] \\
      every_case_tac \\ fs[pmatch_def]
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              imp_res_tac inv_mat_dcmp \\
              res_tac))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              imp_res_tac inv_mat_dcmp \\
              res_tac))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              imp_res_tac inv_mat_dcmp \\
              res_tac))
      >- (fs[match_def, pmatch_def] \\
          every_case_tac \\ fs[] \\
          `pmatch_list ps ts <> PTypeFailure` by fs[] \\
          imp_res_tac pmatch_list_length \\
          imp_res_tac tfpmatch_list_app \\
          fs[n_any_length, pmatch_list_nany]))
  >- (imp_res_tac tf_dcmp \\
      rw[match_def, spec_def] \\
      every_case_tac \\ fs[pmatch_def]
      >- (rfs[] \\
          `LENGTH pargs = LENGTH targs` by fs[] \\
          res_tac \\ fs[] \\
          Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\
              fs[IS_SOME_EXISTS] \\ rfs[]))
      >- (rfs[] \\
          `LENGTH pargs = LENGTH targs` by fs[] \\
          res_tac \\ fs[] \\
          Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\
              fs[IS_SOME_EXISTS] \\ rfs[]))
      >- (rfs[] \\
          `LENGTH pargs = LENGTH targs` by fs[] \\
          res_tac \\ fs[] \\
          Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\
              fs[IS_SOME_EXISTS] \\ rfs[]))
      >- (rpt (WEAKEN_TAC is_imp) \\
          fs[match_def, pmatch_def] \\
          every_case_tac \\ fs[] \\
          `pmatch_list ps ts <> PTypeFailure` by fs[]  \\
          `pmatch_list pargs targs <> PTypeFailure` by fs[] \\
          imp_res_tac pmatch_list_length \\
          imp_res_tac tfpmatch_list_app)
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              res_tac \\ fs[]))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              res_tac \\ fs[])))
  >- (rw[match_def, spec_def] \\
      imp_res_tac tf_or \\
      imp_res_tac tf_first_branch \\
      imp_res_tac tf_dcmp \\
      Cases_on `m`
      >- (rw[match_def, spec_def] \\
          fs[msize_def, inv_mat_aux_def] \\
          res_tac \\ fs[] \\
          imp_res_tac tfmatch_app)
      >- (imp_res_tac msize_inv \\ fs[] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac inv_mat_cons \\
          res_tac \\ fs[msize_def] \\ rfs[] \\
          `SUC (LENGTH ps) = LENGTH ts + 1` by fs[] \\
          res_tac \\ fs[] \\
          imp_res_tac tfmatch_app))
  >- fs[msize_def]
QED

(* Key property of matrix decomposition (Lemma 1 of article) *)
Theorem spec_lem:
  !c a m ts targs k.
    (inv_mat m /\
    ((LENGTH targs) = a) /\
    IS_SOME (match m ((Term k c targs)::ts)) /\
    ((msize m) = (LENGTH ts) + 1)) ==>
    (match m ((Term k c targs)::ts) =
     match (spec c (LENGTH targs) m) (targs++ts))
Proof
  ho_match_mp_tac (fetch "-" "spec_ind") \\ rw[]
  >- fs[msize_def]
  >- (fs[match_def, spec_def] \\
      every_case_tac \\ fs[pmatch_def] \\
     `LENGTH ps = LENGTH ts` by fs[msize_def] \\
     `LENGTH (n_any (LENGTH targs)) = LENGTH targs` by fs[n_any_length]
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (imp_res_tac npmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\
          fs[pmatch_list_nany])
      >- (`pmatch_list (n_any (LENGTH targs)) targs = PMatchSuccess`
          by fs[pmatch_list_nany] \\
          imp_res_tac pmatch_list_app2 \\
          rpt (WEAKEN_TAC is_imp) \\ fs[])
      >- imp_res_tac npmatch_list_app22
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (imp_res_tac pmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\
          fs[pmatch_list_nany])
      >- (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              `IS_SOME (match (h::t) (Term k c targs::ts))` by fs[] \\
              res_tac \\ fs[]))
      >- (imp_res_tac tfpmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\
          fs[pmatch_list_nany]))
  >- (imp_res_tac match_first_patlist2 \\
      fs[match_def, spec_def] \\
      `LENGTH ps = LENGTH ts` by fs[msize_def] \\
      fs[pmatch_def] \\ every_case_tac \\
      fs[match_def] \\ every_case_tac \\ fs[] \\
      TRY (`LENGTH pargs = LENGTH targs` by fs[]) \\
      TRY (Cases_on `m`
           >- fs[match_def, spec_def]
           >- (imp_res_tac msize_inv \\ fs[] \\
               imp_res_tac inv_mat_dcmp \\
               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
               fs[])) \\
      TRY (Cases_on `m`
          >- fs[match_def, spec_def]
          >- (imp_res_tac msize_inv \\ fs[] \\
              imp_res_tac inv_mat_dcmp \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
              fs[IS_SOME_EXISTS] \\ rfs[] \\ res_tac \\ rfs[]))
      >- (imp_res_tac pmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\ fs[])
      >- (imp_res_tac tfpmatch_list_app \\ fs[])
      >- (imp_res_tac pmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\ fs[])
      >- (imp_res_tac tfpmatch_list_app \\ fs[])
      >- (imp_res_tac pmatch_list_app \\
          rpt (WEAKEN_TAC is_forall) \\ fs[])
      >- (imp_res_tac tfpmatch_list_app \\ fs[])
      >- (imp_res_tac npmatch_list_app \\ fs[])
      >- (imp_res_tac tfpmatch_list_app \\ fs[])
      >- (`pmatch_list pargs targs <> PTypeFailure` by fs[] \\
          fs[pmatch_list_length]))
  >- (fs[match_def, pmatch_def, spec_def] \\
      rpt (first_x_assum (qspecl_then [`ts`, `targs`, `k`] assume_tac)) \\
      every_case_tac \\ fs[]
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (rw[IS_SOME_EXISTS] \\
                  qexists_tac `MatchSuccess e` \\
                  first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
          >- (rw[IS_SOME_EXISTS] \\
              qexists_tac `x` \\
              Cases_on `m`
              >- fs[inv_mat_def, msize_def, match_def,spec_def]
              >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[spec_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
           >- (rw[IS_SOME_EXISTS] \\
               qexists_tac `x` \\
               Cases_on `m`
               >- fs[spec_def, match_def]
               >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                   >- imp_res_tac inv_mat_dcmp
                   >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[spec_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (rw[IS_SOME_EXISTS] \\
                  qexists_tac `MatchFailure` \\
                  first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
          >- (rw[IS_SOME_EXISTS] \\
              qexists_tac `x` \\
              Cases_on `m`
              >- fs[match_def, spec_def]
              >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[spec_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (sg `match m (Term k c targs::ts) =
              match (spec c (LENGTH targs) m) (targs ++ ts)`
          >- (Cases_on `m`
              >- fs[match_def, spec_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[])))
          >- (fs[] \\
              ho_match_mp_tac (GSYM match_app2) \\
              ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])))
      >- (sg `match m (Term k c targs::ts) =
              match (spec c (LENGTH targs) m) (targs ++ ts)`
          >- (Cases_on `m`
              >- fs[match_def, spec_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv \\ fs[])))
          >- (fs[] \\
              ho_match_mp_tac (GSYM match_app2) \\
              ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[msize_def]))))
  >- fs[msize_def]
QED;

Theorem spec_msize:
  !c a m. (inv_mat m) /\
          (msize m) > 0 /\
          m <> [] /\
          (spec c a m) <> [] ==>
          msize (spec c a m) =
          a + (msize m) - 1
Proof
  ho_match_mp_tac (theorem "spec_ind") \\ rw[]
  >- (Cases_on `m` \\
      fs[spec_def, msize_def, n_any_length])
  >- (Cases_on `m` \\
      Cases_on `c = pcons'` \\
      Cases_on `a = LENGTH pargs` \\
      fs[spec_def]
      >- fs[msize_def]
      >- fs[msize_def]
      >- (imp_res_tac msize_inv' \\
          imp_res_tac inv_mat_dcmp \\
          fs[])
      >- (imp_res_tac msize_inv' \\
          imp_res_tac inv_mat_dcmp \\
          fs[])
      >- (imp_res_tac msize_inv' \\
          imp_res_tac inv_mat_dcmp \\
          fs[]))
  >- (Cases_on `m`
      >- (fs[spec_def, msize_def, msize_app]
          >- (imp_res_tac inv_mat_or1 \\
              fs[])
          >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (fs[msize_app2] \\
                  imp_res_tac inv_mat_or2 \\
                  fs[])
              >- (fs[msize_app] \\
                  imp_res_tac inv_mat_or1 \\
                  fs[])))
      >- (fs[spec_def, msize_def, msize_app]
          >- (imp_res_tac inv_mat_or1 \\
              imp_res_tac inv_mat_cons \\
              fs[])
          >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (fs[msize_app2] \\
                  imp_res_tac inv_mat_or2 \\
                  imp_res_tac inv_mat_cons \\
                  fs[])
              >- (fs[msize_app] \\
                  imp_res_tac inv_mat_or1 \\
                  imp_res_tac inv_mat_cons \\
                  fs[]))
          >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (Cases_on `spec c a [Branch (p2::ps) e] = []`
                  >- (fs[msize_app2] \\
                      imp_res_tac inv_mat_dcmp \\
                      fs[inv_mat_def, EVERY_DEF, patterns_def] \\
                      Cases_on `h` \\
                      fs[msize_def, patterns_def])
                  >- (fs[msize_app2, msize_app] \\
                      imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons \\
                      fs[]))
              >- (fs[msize_app] \\
                  imp_res_tac inv_mat_or1 \\
                  imp_res_tac inv_mat_cons \\
                  fs[]))))
  >- fs[msize_def]
QED;

Theorem spec_inv_mat:
  !c a m. inv_mat m ==>
          inv_mat (spec c a m)
Proof
  cheat
QED

(* Default matrix transformation *)
Definition default_def:
  (default [] = []) /\
  (default ((Branch (Any::ps) e)::rs) =
    (Branch ps e)::(default rs)) /\
  (default ((Branch ((Cons _ pcons _ pargs)::ps) e)::rs) =
    (default rs)) /\
  (default ((Branch ((Or p1 p2)::ps) e)::rs) =
    (default [Branch (p1::ps) e]) ++
    (default [Branch (p2::ps) e]) ++
    (default rs))
End

Theorem default_inv_mat:
  !m. inv_mat m ==>
      inv_mat (default m)
Proof
  cheat
QED

(* Key property of default matrix (Lemma 2 of article) *)
Definition is_cons_head_def:
  (is_cons_head c a [] = F) /\
  (is_cons_head c a ((Branch [] e)::rs) =
    (is_cons_head c a rs)) /\
  (is_cons_head c a ((Branch (Any::ps) e)::rs) =
    (is_cons_head c a rs)) /\
  (is_cons_head c a ((Branch ((Cons _ pcons _ pargs)::ps) e)::rs) =
    (if c = pcons /\ (a = LENGTH pargs)
    then T
    else (is_cons_head c a rs))) /\
  (is_cons_head c a ((Branch ((Or p1 p2)::ps) e)::rs) =
    ((is_cons_head c a [Branch (p1::ps) e]) \/
     (is_cons_head c a [Branch (p2::ps) e]) \/
     (is_cons_head c a rs)))
End

Theorem is_cons_head_app:
  !c a m1 m2. (~(is_cons_head c a m1) /\
               ~(is_cons_head c a m2)) ==>
              ~(is_cons_head c a (m1 ++ m2))
Proof
  ho_match_mp_tac is_cons_head_ind \\ rw[] \\
  fs[is_cons_head_def]
QED;

Theorem default_tf:
  !m c ts targs k.
    inv_mat m /\
    msize m = (LENGTH ts) + 1 /\
    IS_SOME (match m ((Term k c targs)::ts)) ==>
    IS_SOME (match (default m) ts)
Proof
  ho_match_mp_tac (theorem "default_ind") \\ rw[]
  >- fs[msize_def]
  >- (fs[match_def, default_def] \\
      every_case_tac \\ fs[pmatch_def] \\
      (Cases_on `m`
       >- fs[match_def, default_def]
       >- (imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv \\ fs[] \\
          fs[IS_SOME_EXISTS] \\
          res_tac \\ fs[msize_def, ADD1] \\
          `LENGTH ps = LENGTH ts` by fs[] \\
          fs[] \\ res_tac \\ fs[])))
  >- (fs[match_def, default_def] \\
      every_case_tac \\ fs[pmatch_def] \\
      every_case_tac \\ fs[pmatch_def] \\
      (Cases_on `m`
       >- fs[default_def, match_def]
       >- (first_x_assum ho_match_mp_tac \\
           qexists_tac `c` \\
           qexists_tac `targs` \\
           qexists_tac `k` \\ rw[]
           >- imp_res_tac inv_mat_dcmp
           >- (imp_res_tac msize_inv \\ fs[]))))
  >- (fs[match_def, default_def] \\
      ho_match_mp_tac tf_app \\ rw[]
      >- (ho_match_mp_tac tf_app \\ rw[]
          >- (first_x_assum ho_match_mp_tac \\
              qexists_tac `c` \\
              qexists_tac `targs` \\
              qexists_tac `k` \\ rw[]
              >- (imp_res_tac inv_mat_or1 \\
                  imp_res_tac inv_mat_cons)
              >- fs[msize_def]
              >- (fs[pmatch_def] \\
                  every_case_tac \\ fs[]))
          >- (first_x_assum ho_match_mp_tac \\
              qexists_tac `c` \\
              qexists_tac `targs` \\
              qexists_tac `k` \\ rw[]
              >- (imp_res_tac inv_mat_or2 \\
                  imp_res_tac inv_mat_cons)
              >- fs[msize_def]
              >- (fs[pmatch_def] \\
                  every_case_tac \\ fs[])))
      >- (Cases_on `m`
          >- fs[match_def, default_def]
          >- (first_x_assum ho_match_mp_tac \\
              qexists_tac `c` \\
              qexists_tac `targs` \\
              qexists_tac `k` \\ rw[]
              >- imp_res_tac inv_mat_dcmp
              >- (imp_res_tac msize_inv \\ fs[])
              >- (fs[pmatch_def] \\
                  every_case_tac \\ fs[]))))
  >- fs[msize_def]
QED

Theorem default_lem:
  !m c ts targs k.
    inv_mat m /\
    ~(is_cons_head c (LENGTH targs) m) /\
    IS_SOME (match m ((Term k c targs)::ts)) /\
    msize m = (LENGTH ts) + 1 ==>
   (match m ((Term k c targs)::ts) =
    match (default m) ts)
Proof
  ho_match_mp_tac (fetch "-" "default_ind") \\ rw[]
  >- fs[msize_def]
  >- (fs[match_def, default_def] \\
      every_case_tac \\ fs[pmatch_def] \\
      (Cases_on `m`
       >- fs[match_def, default_def]
       >- (imp_res_tac inv_mat_dcmp \\
           fs[is_cons_head_def] \\
           imp_res_tac msize_inv \\ fs[IS_SOME_EXISTS] \\
           res_tac \\ fs[msize_def])))
  >- (fs[match_def, default_def] \\
      every_case_tac \\ fs[pmatch_def] \\
      every_case_tac \\ fs[pmatch_def, is_cons_head_def]
      >- (`pmatch_list pargs targs <> PTypeFailure` by fs[] \\
          imp_res_tac pmatch_list_length \\ fs[])
      >- (`pmatch_list pargs targs <> PTypeFailure` by fs[] \\
          imp_res_tac pmatch_list_length \\ fs[])
      >- (`pmatch_list pargs targs <> PTypeFailure` by fs[] \\
          imp_res_tac pmatch_list_length \\ fs[])
      >- (Cases_on `m`
          >- fs[match_def, default_def]
          >- (imp_res_tac inv_mat_dcmp \\
              imp_res_tac msize_inv \\ fs[IS_SOME_EXISTS] \\
              res_tac \\ fs[msize_def]))
      >- (Cases_on `m`
          >- fs[match_def, default_def]
          >- (imp_res_tac inv_mat_dcmp \\
              imp_res_tac msize_inv \\ fs[IS_SOME_EXISTS] \\
              res_tac \\ fs[msize_def]))
      >- (Cases_on `m`
          >- fs[match_def, default_def]
          >- (imp_res_tac inv_mat_dcmp \\
              imp_res_tac msize_inv \\ fs[IS_SOME_EXISTS] \\
              res_tac \\ fs[msize_def])))
  >- (fs[pmatch_def, match_def, default_def] \\
      rpt (first_x_assum (qspecl_then [`c`, `ts`, `targs`, `k`] assume_tac)) \\
      every_case_tac \\ fs[]
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (rw[IS_SOME_EXISTS] \\
                  qexists_tac `MatchSuccess e` \\
                  first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
          >- (rw[IS_SOME_EXISTS] \\
              qexists_tac `x` \\
              Cases_on `m`
              >- fs[inv_mat_def, msize_def, match_def,default_def]
              >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[default_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
           >- (rw[IS_SOME_EXISTS] \\
               qexists_tac `x` \\
               Cases_on `m`
               >- fs[default_def, match_def]
               >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                   >- imp_res_tac inv_mat_dcmp
                   >- fs[is_cons_head_def]
                   >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[default_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM match_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (rw[IS_SOME_EXISTS] \\
                  qexists_tac `MatchFailure` \\
                  first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
          >- (rw[IS_SOME_EXISTS] \\
              qexists_tac `x` \\
              Cases_on `m`
              >- fs[match_def, default_def]
              >- (first_x_assum (ho_match_mp_tac o GSYM) \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
          >- (ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))
          >- (Cases_on `m`
              >- fs[default_def, match_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[]))))
      >- (sg `match m (Term k c targs::ts) =
              match (default m) ts`
          >- (Cases_on `m`
              >- fs[match_def, default_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[])))
          >- (fs[] \\
              ho_match_mp_tac (GSYM match_app2) \\
              ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])))
      >- (sg `match m (Term k c targs::ts) =
              match (default m) ts`
          >- (Cases_on `m`
              >- fs[match_def, default_def]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- fs[is_cons_head_def]
                  >- (imp_res_tac msize_inv \\ fs[])))
          >- (fs[] \\
              ho_match_mp_tac (GSYM match_app2) \\
              ho_match_mp_tac (GSYM nmatch_app) \\ rw[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or1 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- (imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons)
                  >- fs[is_cons_head_def]
                  >- fs[msize_def]))))
  >- fs[msize_def]
QED;

(* definition of decision trees *)
Datatype:
  dTree =
    Leaf num
  | Fail
  | DTypeFail
  | Swap num dTree
  (*
     kind constructor arity
     If pos k c a dt1 dt2
     if value at position pos has constructor c
     and a arguments, then go to decision tree
     dt1 else go to decision tree dt2
  *)
  | If listPos num num num dTree dTree
End

(* Swap the first and ith items in a list *)
Definition get_ith_def:
  get_ith n ts = HD (DROP n ts)
End

Definition replace_ith_def:
  replace_ith l i e = TAKE (LENGTH l) ((TAKE i l) ++ e ++ (DROP (SUC i) l))
End

Definition swap_items_def:
  (swap_items i ts =
    if i > 0 /\ i < (LENGTH ts)
    then (get_ith i ts)::(TL (replace_ith ts i (TAKE 1 ts)))
    else ts)
End

(* Swap the first and ith columns in a matrix *)
Definition swap_columns_def:
  (swap_columns i [] = []) /\
  (swap_columns i ((Branch b e)::bs) =
     (Branch (swap_items i b) e)::(swap_columns i bs))
End

Theorem swap_items_length:
  !l i. i < LENGTH l ==> LENGTH (swap_items i l) = LENGTH l
Proof
  Cases_on `l` \\
  fs[swap_items_def] \\
  Cases_on `t` \\
  fs[swap_items_def] \\
  Cases_on `i` \\
  rw[swap_items_def, get_ith_def, replace_ith_def]
QED;

Theorem swap_columns_msize:
  !m i. inv_mat m /\ i < (msize m) ==> msize (swap_columns i m) = msize m
Proof
  Induct_on `m`
  >- fs[msize_def, swap_columns_def]
  >- (Cases_on `h` \\
      rw[msize_def, swap_columns_def, swap_items_length])
QED;

Theorem swap_items_zero:
  !l. swap_items 0 l = l
Proof
  Cases_on `l`
  >- fs[swap_items_def]
  >- (Cases_on `t` \\
      fs[swap_items_def])
QED;

Theorem swap_columns_zero:
  !m. swap_columns 0 m = m
Proof
  Induct_on `m`
  >- fs[swap_columns_def]
  >- (Cases_on `h` \\
      fs[swap_columns_def, swap_items_zero])
QED;

Theorem swap_columns_inv_mat:
  !i m. (inv_mat m) /\
        i < (msize m) ==>
        (inv_mat (swap_columns i m))
Proof
  Induct_on `m`
  >- fs[msize_def]
  >- (Cases_on `h` \\
      rw[swap_columns_def] \\
      Cases_on `m`
      >- fs[inv_mat_def, swap_columns_def]
      >- (imp_res_tac msize_inv' \\
          fs[] \\
          imp_res_tac inv_mat_dcmp \\
          res_tac \\
          fs[inv_mat_aux_def] \\
          imp_res_tac inv_mat_recompose \\
          rpt (first_x_assum (qspec_then `Branch (swap_items i l) n` assume_tac)) \\
          fs[patterns_def, msize_def] \\
          `i < LENGTH l` by fs[] \\
          fs[swap_items_length, swap_columns_msize]))
QED;

Theorem map_hd:
  !l f. l <> [] ==> HD (MAP f l) = f (HD l)
Proof
  Cases_on `l` \\
  fs[]
QED

Theorem drop_not_nil:
  !n l. n < LENGTH l ==> (DROP n l) <> []
Proof
  rw[] \\
  rewrite_tac [Once (GSYM LENGTH_NIL)] \\
  rewrite_tac [Once (LENGTH_DROP)] \\
  `0 < LENGTH l - n` suffices_by fs[] \\
  fs[]
QED

(* Remove the first column of a matrix *)
Definition remove_fst_col_def:
  (remove_fst_col [] = []) /\
  (remove_fst_col ((Branch (p::ps) e)::bs) =
    (Branch ps e)::(remove_fst_col bs))
End

Theorem remove_fst_col_msize:
  !m. (msize m) > 0 ==> msize (remove_fst_col m) = (msize m) - 1
Proof
  Cases_on `m` \\ fs[msize_def] \\
  Cases_on `h` \\
  Cases_on `l` \\
  fs[remove_fst_col_def, msize_def]
QED

Theorem inv_mat_remove_fst_col:
  !m. (msize m) > 0 /\ inv_mat m ==> inv_mat (remove_fst_col m)
Proof
  ho_match_mp_tac (theorem "remove_fst_col_ind") \\ rw[]
  >- fs[msize_def]
  >- (Cases_on `m`
      >- fs[remove_fst_col_def, inv_mat_def]
      >- (imp_res_tac inv_mat_fst \\
          fs[] \\
          imp_res_tac inv_mat_cons \\
          Cases_on `h` \\
          Cases_on `l` \\
          fs[inv_mat_aux_def, remove_fst_col_def, msize_def]))
  >- fs[msize_def]
QED

(* Semantics of decision trees *)
Definition dt_eval_def:
  (dt_eval ts (Leaf k) = SOME (MatchSuccess k)) /\
  (dt_eval _ Fail = SOME (MatchFailure)) /\
  (dt_eval _ DTypeFail = NONE) /\
  (dt_eval ts (Swap i dt) = dt_eval ts dt) /\
  (dt_eval ts (If pos k c' a dt1 dt2) =
    case (app_list_pos ts pos) of
      SOME (Term k' c targs) =>
        (if k = k' then
           (if c = c' /\ (LENGTH targs) = a
            then dt_eval ts dt1
            else dt_eval ts dt2)
         else NONE)
    | SOME Other => NONE
    | NONE => NONE)
End

Definition all_wild_def:
  (all_wild [] = T) /\
  (all_wild (Any::ps) = all_wild ps) /\
  (all_wild ((Cons _ _ _ _)::_) = F) /\
  (all_wild ((Or p1 p2)::ps) = ((all_wild [p1]) /\
                                        (all_wild [p2]) /\
                                        (all_wild ps)))
End

Theorem all_wild_dcmp:
  !p ps. all_wild (p::ps) ==>
         (all_wild [p] /\
          all_wild ps)
Proof
  Cases_on `p` \\ fs[all_wild_def]
QED;

(*
Column infos

Returns a pair containing identifiers to be bound in default case and a list
containing pairs of constructors, expected number of constructors for a type,
an arity for the constructor, and list of identifiers to be bound for each of
these constructors
*)
Type cinfos = ``:(num # num # num) list``

(* Add a constructor to the list of constructors of the column *)
Definition add_cons_def:
  (add_cons k c n a [] = [(k,c,n,a)]) /\
  (add_cons k c n a ((k', c', n', a')::cinfos) =
    if c = c' /\ a = a' /\ k = k'
    then ((k', c', n', a')::cinfos)
    else ((k', c', n', a')::(add_cons k c n a cinfos)))
End

Theorem add_cons_not_empty:
  !k c n a l. (add_cons k c n a l) <> []
Proof
  Cases_on `l` \\ rw[]
  >- fs[add_cons_def]
  >- (Cases_on `h` \\ Cases_on `r` \\ Cases_on `r'` \\
      fs[add_cons_def] \\
      every_case_tac)
QED

Definition merge_cinfos_def:
  (merge_cinfos [] ys = ys) /\
  (merge_cinfos (x::xs) ys =
    if MEM x ys
    then (merge_cinfos xs ys)
    else x::(merge_cinfos xs ys))
End

Theorem merge_cinfos_not_empty:
  !c1 c2. (c1 <> [] \/ c2 <> []) ==> (merge_cinfos c1 c2) <> []
Proof
  Induct_on `c1` \\
  rw[merge_cinfos_def] \\
  first_x_assum (qspec_then `c2` assume_tac) \\
  Cases_on `c2` \\ fs[]
QED


(* Build the informations on a constructor *)
Definition cinfos_def:
  (cinfos [] = []) /\
  (cinfos ((Branch [] e)::rs) = cinfos rs) /\
  (cinfos ((Branch (Any::ps) e)::rs) = cinfos rs) /\
  (cinfos ((Branch ((Cons k c n sub_ps)::ps) e)::rs) =
    add_cons k c n (LENGTH sub_ps) (cinfos rs)) /\
  (cinfos ((Branch ((Or p1 p2)::ps) e)::rs) =
    merge_cinfos (merge_cinfos (cinfos [(Branch [p1] e)])
                               (cinfos [(Branch [p2] e)]))
                 (cinfos rs))
End

(* Is a constructor in some column informations ? *)
Definition in_cinfos_def:
  (in_cinfos (_,_) [] = F) /\
  (in_cinfos (c,a) ((_,c',_,a')::cinfos) =
    if c = c' /\ a = a'
    then T
    else in_cinfos (c,a) cinfos)
End


(* Tell if the patterns contain all the constructors of a signature
   from a column_infos *)
Definition is_col_complete_def:
  (is_col_complete [] = F) /\
  (is_col_complete ((_,_,NONE,_)::_) = F) /\
  (is_col_complete ((_,_,SOME n,_)::cons) =
    (((LENGTH cons) + 1:num) = n))
End

(* Counting the number of constructors to prove termination *)
Definition nb_cons_pat_def:
  (nb_cons_pat Any = (1:num)) /\
  (nb_cons_pat (Cons _ _ _ []) = 2) /\
  (nb_cons_pat (Cons k c a (p::ps)) =
    (nb_cons_pat p) * (nb_cons_pat (Cons k c a ps))) /\
  (nb_cons_pat (Or p1 p2) = (nb_cons_pat p1) + (nb_cons_pat p2))
End

Definition nb_cons_branch_def:
  (nb_cons_branch [] = 1) /\
  (nb_cons_branch (p::ps) = (nb_cons_pat p) * (nb_cons_branch ps))
End

Definition nb_cons_def:
  (nb_cons [] = 0) /\
  (nb_cons ((Branch l e)::bs) = (nb_cons_branch l) + (nb_cons bs))
End

Definition is_cons_fcol_pat_def:
  (is_cons_fcol_pat Any = F) /\
  (is_cons_fcol_pat (Cons _ _ _ _) = T) /\
  (is_cons_fcol_pat (Or p1 p2) =
    ((is_cons_fcol_pat p1) \/ (is_cons_fcol_pat p2)))
End

Definition is_cons_fcol_branch_def:
  (is_cons_fcol_branch [] = F) /\
  (is_cons_fcol_branch (p::ps) = is_cons_fcol_pat p)
End

Definition is_cons_fcol_def:
  (is_cons_fcol [] = F) /\
  (is_cons_fcol ((Branch l e)::bs) = ((is_cons_fcol_branch l) \/ (is_cons_fcol bs)))
End

Theorem is_cons_fcol_cinfos_not_empty:
  !m. is_cons_fcol m ==> cinfos m <> []
Proof
  ho_match_mp_tac (theorem "cinfos_ind") \\ rw[] \\
  fs[is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def, cinfos_def, add_cons_not_empty] \\
  res_tac \\ fs[merge_cinfos_not_empty]
QED;

Theorem nb_cons_app:
  !l1 l2. nb_cons (l1 ++ l2) = nb_cons l1 + nb_cons l2
Proof
  Induct_on `l1` \\
  fs[nb_cons_def] \\
  Cases_on `h` \\
  fs[nb_cons_def]
QED;

Theorem nb_cons_gt_zero:
  !p. 0 < nb_cons_pat p
Proof
  ho_match_mp_tac (theorem "nb_cons_pat_ind") \\ rw[nb_cons_pat_def, LESS_MULT2]
QED;

Theorem nb_cons_branch_gt_zero:
  !ps. 0 < nb_cons_branch ps
Proof
  Induct_on `ps` \\
  rw[nb_cons_branch_def] \\
  `0 < nb_cons_pat h` by fs[nb_cons_gt_zero] \\
  fs[LESS_MULT2]
QED;

Theorem nb_cons_cons_gt_zero:
  !k c a p. 0 < nb_cons_pat (Cons k c a p)
Proof
  fs[nb_cons_gt_zero]
QED;

Theorem nb_cons_default_aux:
  !m. inv_mat m /\
      (msize m) > 0 /\
      m <> [] ==>
      nb_cons (default m) <= nb_cons m
Proof
  ho_match_mp_tac (theorem "default_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def]
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def]))
  >- (Cases_on `m`
      >- fs[default_def, nb_cons_def, nb_cons_branch_def]
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[default_def, nb_cons_def, nb_cons_branch_def]))
  >- (Cases_on `m`
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
            nb_cons_app] \\
          `msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          fs[])
      >- (`msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac inv_mat_cons \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
             nb_cons_app]))
  >- fs[msize_def]
QED;

Theorem nb_cons_default:
  !m. inv_mat m /\
      (msize m) > 0 /\
      m <> [] /\
      is_cons_fcol m ==>
      nb_cons (default m) < nb_cons m
Proof
  ho_match_mp_tac (theorem "default_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def]
      >- (fs[is_cons_fcol_def, is_cons_fcol_branch_def, nb_cons_pat_def,
             is_cons_fcol_pat_def, nb_cons_def, nb_cons_branch_def, default_def] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[]))
  >- (Cases_on `m`
      >- (fs[nb_cons_def, nb_cons_branch_def, nb_cons_pat_def, default_def] \\
          ho_match_mp_tac LESS_MULT2 \\ rw[nb_cons_branch_gt_zero, nb_cons_cons_gt_zero])
      >- (fs[nb_cons_def, nb_cons_branch_def, nb_cons_pat_def, default_def] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[] \\
          imp_res_tac nb_cons_default_aux \\
          rfs[] \\
          Cases_on `nb_cons (default (h::t)) = nb_cons (h::t)`
          >- (fs[] \\
              `0 < nb_cons_pat (Cons v0 pcons' v1 pargs)` by fs[nb_cons_cons_gt_zero] \\
              `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
              fs[LESS_MULT2])
          >- (`nb_cons (default (h::t)) < nb_cons (h::t)` by fs[] \\
              fs[])))
  >- (Cases_on `m`
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
             nb_cons_app] \\
          `msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac nb_cons_default_aux \\
          rfs[nb_cons_def, nb_cons_branch_def, is_cons_fcol_def,
              is_cons_fcol_branch_def, nb_cons_pat_def,
              is_cons_fcol_pat_def]  \\
          fs[])
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
             nb_cons_app] \\
          `msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac inv_mat_cons \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac nb_cons_default_aux \\
          fs[nb_cons_def, nb_cons_branch_def, is_cons_fcol_def,
              is_cons_fcol_branch_def, nb_cons_pat_def,
              is_cons_fcol_pat_def] \\
          rfs[] \\ fs[]))
  >- fs[msize_def]
QED;

Theorem nb_cons_branch_app:
  !ps qs. nb_cons_branch (ps ++ qs) =
          (nb_cons_branch ps) * (nb_cons_branch qs)
Proof
  Induct_on `ps` \\
  fs[nb_cons_branch_def]
QED;

Theorem nb_cons_branch_n_any:
  !n. nb_cons_branch (n_any n) = 1
Proof
  Induct_on `n` \\
  fs[n_any_def, nb_cons_branch_def, nb_cons_pat_def]
QED;

Theorem nb_cons_cons_pargs:
  !k c a p. nb_cons_branch p < nb_cons_pat (Cons k c a p)
Proof
  Induct_on `p` \\
  rw[nb_cons_pat_def, nb_cons_branch_def] \\
  `0 < nb_cons_pat h` by fs[nb_cons_gt_zero] \\
  rewrite_tac[Once MULT_COMM] \\
  fs[LT_MULT_LCANCEL]
QED;

Theorem nb_cons_spec_aux:
  !c a m. inv_mat m /\
          (msize m) > 0 /\
          m <> [] ==>
          nb_cons (spec c a m) <= nb_cons m
Proof
  ho_match_mp_tac (theorem "spec_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
            nb_cons_branch_app, nb_cons_branch_n_any]
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
            nb_cons_branch_app, nb_cons_branch_n_any] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          fs[nb_cons_def, nb_cons_branch_app, nb_cons_branch_def, nb_cons_branch_n_any,
             nb_cons_pat_def]))
  >- (Cases_on `m` \\ Cases_on `c=pcons'` \\ Cases_on `a = LENGTH pargs` \\
      fs[spec_def, nb_cons_def, nb_cons_branch_app, nb_cons_branch_def]
      >- (`0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
          rewrite_tac [Once MULT_COMM] \\
          fs[LT_MULT_LCANCEL] \\
          `nb_cons_branch pargs < nb_cons_pat (Cons v0 pcons' a' pargs)` by fs[nb_cons_cons_pargs] \\
          fs[])
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[] \\
          `nb_cons_branch pargs * nb_cons_branch ps <=
           nb_cons_branch ps * nb_cons_pat (Cons v0 pcons' a' pargs)`
          suffices_by fs[LESS_EQ_LESS_EQ_MONO] \\
          `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
          rewrite_tac [Once MULT_COMM] \\
          fs[LT_MULT_LCANCEL] \\
          `nb_cons_branch pargs < nb_cons_pat (Cons v0 pcons' a' pargs)` by fs[nb_cons_cons_pargs] \\
          fs[])
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[])
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[])
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[]))
  >- (Cases_on `m` \\
      fs[spec_def, nb_cons_def, nb_cons_app, nb_cons_branch_def, nb_cons_pat_def]
      >- (`msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          fs[])
      >- (`msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac inv_mat_cons \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[]))
  >- fs[msize_def]
QED;

Theorem nb_cons_spec:
  !c a m. inv_mat m /\
          (msize m) > 0 /\
          m <> [] /\
          is_cons_fcol m ==>
          nb_cons (spec c a m) < nb_cons m
Proof
  ho_match_mp_tac (theorem "spec_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[spec_def, is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def]
      >- (fs[spec_def, is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          fs[nb_cons_def, nb_cons_branch_app, nb_cons_branch_def, nb_cons_branch_n_any,
             nb_cons_pat_def]))
  >- (Cases_on `m`
      >- (Cases_on `c=pcons'` \\ Cases_on `a = LENGTH pargs`
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_app, nb_cons_branch_def] \\
              `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
              rewrite_tac [Once MULT_COMM] \\
              fs[LT_MULT_LCANCEL, nb_cons_pat_def, nb_cons_cons_pargs])
          >- fs[spec_def, nb_cons_def, nb_cons_branch_gt_zero]
          >- fs[spec_def, nb_cons_def, nb_cons_branch_gt_zero]
          >- fs[spec_def, nb_cons_def, nb_cons_branch_gt_zero])
      >- (Cases_on `c=pcons'` \\ Cases_on `a = LENGTH pargs`
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_app, nb_cons_branch_def] \\
              imp_res_tac msize_inv_gt_zero \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\
              imp_res_tac nb_cons_spec_aux \\
              rfs[] \\
              rpt (first_x_assum (qspecl_then [`pcons'`,`LENGTH pargs`] assume_tac)) \\
              Cases_on `nb_cons (spec pcons' (LENGTH pargs) (h::t)) = nb_cons (h::t)`
              >- (fs[] \\
                  `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
                  rewrite_tac [Once MULT_COMM] \\
                  fs[LT_MULT_LCANCEL, nb_cons_pat_def, nb_cons_cons_pargs])
              >- (`nb_cons (spec c a (h::t)) < nb_cons (h::t)` by fs[] \\
                  `nb_cons_branch pargs * nb_cons_branch ps <
                   nb_cons_branch ps * nb_cons_pat (Cons v0 pcons' a' pargs)`
                  suffices_by fs[LESS_EQ_LESS_EQ_MONO] \\
                  `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
                  rewrite_tac [Once MULT_COMM] \\
                  fs[LT_MULT_LCANCEL, nb_cons_pat_def, nb_cons_cons_pargs]))
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_def] \\
              imp_res_tac msize_inv_gt_zero \\
              imp_res_tac inv_mat_dcmp \\
              imp_res_tac nb_cons_spec_aux \\
              fs[] \\
              rfs[] \\
              rpt (first_x_assum (qspecl_then [`pcons'`,`a`] assume_tac)) \\
              Cases_on `nb_cons (spec pcons' a (h::t)) = nb_cons (h::t)`
              >- fs[nb_cons_branch_gt_zero, nb_cons_gt_zero, LESS_MULT2]
              >- (`nb_cons (spec c a (h::t)) < nb_cons (h::t)` by fs[] \\
                  fs[]))
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_def] \\
              imp_res_tac msize_inv_gt_zero \\
              imp_res_tac inv_mat_dcmp \\
              imp_res_tac nb_cons_spec_aux \\
              fs[] \\
              rfs[] \\
              rpt (first_x_assum (qspecl_then [`c`,`LENGTH pargs`] assume_tac)) \\
              Cases_on `nb_cons (spec c (LENGTH pargs) (h::t)) = nb_cons (h::t)`
              >- fs[nb_cons_branch_gt_zero, nb_cons_gt_zero, LESS_MULT2]
              >- (`nb_cons (spec c a (h::t)) < nb_cons (h::t)` by fs[] \\
                  fs[]))
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_def] \\
              imp_res_tac msize_inv_gt_zero \\
              imp_res_tac inv_mat_dcmp \\
              imp_res_tac nb_cons_spec_aux \\
              fs[] \\
              rfs[] \\
              rpt (first_x_assum (qspecl_then [`c`,`a`] assume_tac)) \\
              Cases_on `nb_cons (spec c a (h::t)) = nb_cons (h::t)`
              >- fs[nb_cons_branch_gt_zero, nb_cons_gt_zero, LESS_MULT2]
              >- (`nb_cons (spec c a (h::t)) < nb_cons (h::t)` by fs[] \\
                  fs[]))))
  >- (Cases_on `m`
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
             nb_cons_app] \\
          `msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac nb_cons_spec_aux \\
          rfs[nb_cons_def, nb_cons_branch_def, is_cons_fcol_def,
              is_cons_fcol_branch_def, nb_cons_pat_def,
              is_cons_fcol_pat_def]  \\
          rpt (first_x_assum (qspecl_then [`c`,`a`] assume_tac)) \\
          fs[])
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
             nb_cons_app] \\
          `msize [Branch (p1::ps) e] > 0` by fs[msize_def]  \\
          `msize [Branch (p2::ps) e] > 0` by fs[msize_def]  \\
          imp_res_tac inv_mat_or1 \\
          imp_res_tac inv_mat_or2 \\
          imp_res_tac inv_mat_cons \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac nb_cons_spec_aux \\
          fs[nb_cons_def, nb_cons_branch_def, is_cons_fcol_def,
              is_cons_fcol_branch_def, nb_cons_pat_def,
              is_cons_fcol_pat_def] \\
          rfs[] \\
          rpt (first_x_assum (qspecl_then [`c`,`a`] assume_tac)) \\
          fs[]))
  >- fs[msize_def]
QED;

Theorem drop_take_nb_cons:
  !i t. i < LENGTH t ==>
        (nb_cons_branch (TAKE i t)) * (nb_cons_branch (DROP i t)) =
        nb_cons_branch t
Proof
  rw[] \\
  `nb_cons_branch t = nb_cons_branch ((TAKE i t) ++ (DROP i t))` by fs[] \\
  fs[nb_cons_branch_app]
QED;

Theorem drop_nb_cons_decompose:
  !i t. i < LENGTH t ==>
       (nb_cons_pat (HD (DROP i t))) *
       (nb_cons_branch (DROP (SUC i) t)) =
        nb_cons_branch (DROP i t)
Proof
  Induct_on `t`
  >- fs[DROP_def]
  >- (fs[DROP_def] \\
     Cases_on `i=0` \\
     rw[nb_cons_branch_def] \\
     first_x_assum (qspec_then `i'-1` assume_tac) \\
     rfs[ADD1])
QED;

Theorem nb_cons_branch_swap:
  !l i. i < LENGTH l ==> nb_cons_branch (swap_items i l) = nb_cons_branch l
Proof
  Cases_on `l` \\
  fs[swap_items_def] \\
  Cases_on `t` \\
  fs[swap_items_def] \\
  Cases_on `i` \\
  rw[swap_items_def, get_ith_def, replace_ith_def] \\
  fs[LENGTH_APPEND, LENGTH_TAKE_EQ, TAKE_LENGTH_ID_rwt] \\
  Cases_on `n`
  >- fs[nb_cons_def, nb_cons_branch_def]
  >- (fs[DROP_def, nb_cons_branch_def, nb_cons_branch_app] \\
      `n' < LENGTH t'` by fs[] \\
      `0 < nb_cons_pat h` by fs[nb_cons_gt_zero] \\
      `0 < nb_cons_pat h'` by fs[nb_cons_gt_zero] \\
      fs[] \\
      `nb_cons_branch (DROP n' t') * nb_cons_branch (TAKE n' t') =
       nb_cons_branch t'`
      suffices_by metis_tac[MULT_COMM, MULT_ASSOC, drop_nb_cons_decompose] \\
      metis_tac[MULT_COMM, drop_take_nb_cons])
QED;

Theorem nb_cons_swap:
  !m i. i < (msize m) /\ inv_mat m ==>
        nb_cons (swap_columns i m) = nb_cons m
Proof
  Induct_on `m`
  >- fs[swap_columns_def]
  >- (Cases_on `h` \\
      rw[swap_columns_def, nb_cons_def]  \\
      Cases_on `m`
      >- fs[msize_def, nb_cons_branch_swap, swap_columns_def]
      >- (imp_res_tac msize_inv \\
          first_x_assum (qspec_then `msize (Branch l n::h::t)` assume_tac) \\
          fs[] \\
          imp_res_tac inv_mat_dcmp \\
           res_tac \\
          fs[msize_def, nb_cons_branch_swap]))
QED;

Definition pos_default_def:
  (pos_default (p::pos) = pos)
End


Definition pos_spec_aux_def:
  (pos_spec_aux a n p =
    GENLIST (\x. (n, snoc_pos x p)) a)
End

Definition pos_spec_def:
  (pos_spec a ((n,p)::pos) =
    (pos_spec_aux a n p) ++ pos)
End

Theorem pos_spec_size:
  !a pos. pos <> [] ==> LENGTH (pos_spec a pos) = a + (LENGTH pos) - 1
Proof
  Cases_on `pos` \\ rw[] \\
  Cases_on `h` \\
  fs[pos_spec_def, pos_spec_aux_def]
QED;

(* Fallback heuristic *)
Definition simple_heuristic_def:
  (simple_heuristic ((Branch [] _)::_) = 0) /\
  (simple_heuristic ((Branch (p::ps) e)::bs) =
    if is_cons_fcol_pat p then (0:num)
    else 1 + (simple_heuristic (((Branch ps e)::bs))))
End

Definition inv_heuristic_def:
  inv_heuristic h =
    (!ps e bs. 0 < LENGTH ps /\
               ~(all_wild ps) ==>
               (h ((Branch ps e)::bs) < LENGTH ps) /\
               (is_cons_fcol (swap_columns (h ((Branch ps e)::bs)) ((Branch ps e)::bs))))
End

Theorem inv_simple_heuristic_aux:
  !m. 0 < msize m ==>
      (simple_heuristic m) < msize m
Proof
  cheat
QED

Theorem inv_simple_heuristic:
  inv_heuristic simple_heuristic
Proof
  cheat
QED

(* compilation scheme a pattern matrix to a decision tree
   based on a heuristic h *)

(* Add typefail to decision trees, and replace ARB with it *)
Definition compile_def:
  (compile h pos [] useh = Fail) /\
  (compile h pos ((Branch [] e)::bs) useh = Leaf e) /\
  (compile h pos ((Branch ps e)::bs) useh =
    if ~(inv_mat ((Branch ps e)::bs)) then DTypeFail else
    if all_wild ps
    then Leaf e
    else
      (* we select a column using heuristic h *)
      let sel_col = (h ((Branch ps e)::bs)) in
      if useh
      then (if (sel_col > 0 /\ (sel_col < (msize ((Branch ps e)::bs))))
            then (let s_pos = swap_items sel_col pos in
                  let s_mat = swap_columns sel_col ((Branch ps e )::bs) in
                    if is_cons_fcol s_mat
                    then compile h s_pos s_mat F
                    else (let sel_col = simple_heuristic ((Branch ps e)::bs) in
                          compile h (swap_items sel_col pos) (swap_columns sel_col ((Branch ps e)::bs)) F))
            else (let sel_col = simple_heuristic ((Branch ps e)::bs) in
                  compile h (swap_items sel_col pos) (swap_columns sel_col ((Branch ps e)::bs)) F))
      else (let cinfos = cinfos ((Branch ps e)::bs) in
            if (is_col_complete cinfos)
            then make_complete h pos ((Branch ps e)::bs) cinfos []
            else make_partial h pos ((Branch ps e)::bs) cinfos [])) /\
  (* add a list of already treated constructors *)
  (make_complete h pos m ((_,c,_,a)::[]) t =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
       (compile h (pos_spec a pos) (spec c a m) T)
    else DTypeFail) /\
  (make_complete h pos m ((k,c,n,a)::cons) t =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If (HD pos) k c a (compile h (pos_spec a pos) (spec c a m) T)
                      (make_complete h pos m cons ((k,c,n,a)::t))
    else DTypeFail) /\
  (make_partial h pos m [] t =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
      (compile h (pos_default pos) (default m) T)
    else DTypeFail) /\
  (make_partial h pos m ((k,c,n,a)::cons) t =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If (HD pos) k c a (compile h (pos_spec a pos) (spec c a m) T)
                    (make_partial h pos m cons ((k,c,n,a)::t))
    else DTypeFail)
Termination

(WF_REL_TAC `(inv_image ($< LEX ($< LEX $<))
            (\x. case x of INL(_,_,m,b) => (nb_cons m, (1:num), if b then (1:num) else 0)
                         | INR y => (case y of INL(_,_,m,i,_) =>
                                      (nb_cons m, (0:num), LENGTH i)
                                     | INR(_,_,m,i,_) =>
                                      (nb_cons m, (0:num), LENGTH i))))` \\
rw[]
>- (DISJ2_TAC \\
    assume_tac nb_cons_swap \\
    first_x_assum (qspecl_then [`Branch (v13::v14) e::bs`,`simple_heuristic (Branch (v13::v14) e::bs)`] assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
    fs[])
>- (DISJ2_TAC \\
    imp_res_tac nb_cons_swap \\
    first_x_assum (qspec_then `simple_heuristic (Branch (v13::v14) e::bs)` assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
    fs[])
>- (DISJ2_TAC \\
    imp_res_tac nb_cons_swap \\
    first_x_assum (qspec_then `simple_heuristic (Branch (v13::v14) e::bs)` assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
    fs[])
>- (DISJ2_TAC \\
    imp_res_tac nb_cons_swap \\
    first_x_assum (qspec_then `simple_heuristic (Branch (v13::v14) e::bs)` assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
    fs[])
>- imp_res_tac nb_cons_default) \\
metis_tac [nb_cons_spec]
End

Definition ipos_aux_def:
  ipos_aux (n:num) = (n, EmptyPos)
End

Definition initial_pos_def:
  (initial_pos (width:num) =
    GENLIST ipos_aux width)
End

Definition pmatch_list_pos_def:
  (pmatch_list_pos [] v [] = PMatchSuccess) /\
  (pmatch_list_pos ps v [] = PTypeFailure) /\
  (pmatch_list_pos [] v ts = PTypeFailure) /\
  (pmatch_list_pos (p::ps) v (t::ts) =
     case app_list_pos v t of
       NONE => PTypeFailure
     | SOME sub_v =>
       (case pmatch p sub_v of
         PTypeFailure => PTypeFailure
       | PMatchFailure => (case (pmatch_list_pos ps v ts) of
                             PTypeFailure => PTypeFailure
                           | _ => PMatchFailure)
       | PMatchSuccess => pmatch_list_pos ps v ts))
End

Theorem pmatch_list_pos_app:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
     LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PMatchSuccess ==>
    (pmatch_list_pos t1 v p1 = PMatchSuccess /\
     pmatch_list_pos t2 v p2 = PMatchSuccess)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- fs[pmatch_list_pos_def]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      first_x_assum (qspecl_then [`t`,`p2`,`t2`,`v`] assume_tac) \\
      fs[] \\ rfs[])
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      first_x_assum (qspecl_then [`t`,`p2`,`t2`,`v`] assume_tac) \\
      fs[] \\ rfs[])
QED

Theorem pmatch_list_pos_app2:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos t1 v p1 = PMatchSuccess /\
    pmatch_list_pos t2 v p2 = PMatchSuccess ==>
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PMatchSuccess
Proof
  Induct_on `t1`
  >- fs[]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      rw[] \\ every_case_tac \\ fs[]
      >- (res_tac \\ fs[])
      >- (res_tac \\ fs[]))
QED

Theorem npmatch_list_app:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PMatchFailure ==>
    (pmatch_list_pos t1 v p1 = PMatchFailure \/
     pmatch_list_pos t2 v p2 = PMatchFailure)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[]
      >- (res_tac \\ fs[] \\ fs[])
      >- (res_tac \\ fs[] \\ fs[])
      >- (imp_res_tac pmatch_list_pos_app \\
          rpt (WEAKEN_TAC is_forall) \\
          fs[])
      >- (res_tac \\ fs[] \\ fs[]))
QED

Theorem nmatch_list_pos_app2:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    ((pmatch_list_pos t1 v p1 = PMatchFailure /\
      pmatch_list_pos t2 v p2 <> PTypeFailure) \/
     (pmatch_list_pos t1 v p1 <> PTypeFailure /\
      pmatch_list_pos t2 v p2 = PMatchFailure)) ==>
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PMatchFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[]
      >- (res_tac \\ fs[] \\ fs[])
      >- (res_tac \\ fs[] \\ fs[])
      >- (Cases_on `pmatch_list_pos t2 v p2`
          >- (imp_res_tac pmatch_list_pos_app2 \\
              fs[])
          >- (res_tac \\ fs[] \\ fs[])
          >- fs[])
      >- (Cases_on `pmatch_list_pos t2 v p2`
          >- (res_tac \\ fs[] \\ fs[])
          >- (res_tac \\ fs[] \\ fs[])
          >- fs[]))
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem tfpmatch_list_pos_app:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PTypeFailure ==>
    (pmatch_list_pos t1 v p1 = PTypeFailure \/
     pmatch_list_pos t2 v p2 = PTypeFailure)
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem tfpmatch_list_pos_app2:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    (pmatch_list_pos t1 v p1 = PTypeFailure \/
     pmatch_list_pos t2 v p2 = PTypeFailure) ==>
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) = PTypeFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
  >- (Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem npmatch_list_pos_app21:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos t1 v p1 = PMatchFailure ==>
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) <> PMatchSuccess
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (fs[pmatch_list_pos_def] \\
      Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[] \\
      res_tac \\ fs[] \\ fs[])
QED

Theorem npmatch_list_pos_app22:
  !p1 t1 p2 t2 v.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list_pos t2 v p2 = PMatchFailure ==>
    pmatch_list_pos (t1 ++ t2) v (p1 ++ p2) <> PMatchSuccess
Proof
  Induct_on `t1` \\ rw[] \\
  fs[pmatch_list_pos_def] \\
  Cases_on `p1` \\ fs[pmatch_list_pos_def] \\
  every_case_tac \\ fs[] \\
  res_tac \\ fs[] \\ fs[]
QED

Theorem pmatch_list_app_pos_cases:
  !p1 p2 t1 t2 v.
    LENGTH p1 = LENGTH t1 /\
    LENGTH p2 = LENGTH t2 ==>
    pmatch_list_pos (p1 ++ p2) v (t1 ++ t2) =
    case pmatch_list_pos p1 v t1 of
      PMatchSuccess => pmatch_list_pos p2 v t2
    | PMatchFailure => (case pmatch_list_pos p2 v t2 of
                          PTypeFailure => PTypeFailure
                        | _ => PMatchFailure)
    | PTypeFailure => PTypeFailure
Proof
  rw[] \\
  every_case_tac \\ fs[]
  >- (ho_match_mp_tac pmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac nmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_pos_app2 \\ rw[])
  >- (ho_match_mp_tac tfpmatch_list_pos_app2 \\ rw[])
QED

Theorem app_list_pos_middle:
  !l1 l2 x. app_list_pos (l1 ++ [x] ++ l2) (ipos_aux (LENGTH l1)) = SOME x
Proof
  Induct_on `l1` \\
  fs[app_list_pos_def, app_pos_def, ipos_aux_def]
QED

Theorem app_list_pos_last:
  !l1 x. app_list_pos (l1 ++ [x]) (ipos_aux (LENGTH l1)) = SOME x
Proof
  Induct_on `l1` \\
  fs[app_list_pos_def, app_pos_def, ipos_aux_def]
QED

Theorem pmatch_list_pos_app_too_much:
  !vs ps l .
    LENGTH ps = LENGTH vs ==>
    pmatch_list_pos ps (vs ++ l) (GENLIST ipos_aux (LENGTH vs)) =
    pmatch_list_pos ps vs (GENLIST ipos_aux (LENGTH vs))
Proof
  ho_match_mp_tac SNOC_INDUCT \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (rw[GENLIST, SNOC_APPEND] \\
      Cases_on `ps = []`
      >- fs[]
      >- (`?p qs. ps = SNOC p qs` by metis_tac[SNOC_CASES] \\
          fs[ADD_1_SUC] \\
          fs[pmatch_list_app_pos_cases] \\
          fs[pmatch_list_pos_def, app_list_pos_last, app_list_pos_middle] \\
          rewrite_tac [Once (GSYM APPEND_ASSOC)] \\
          first_assum (qspecl_then [`ps`, `[x] ++ l`] assume_tac) \\
          rfs[]))
QED

Theorem pmatch_list_pos_pmatch_list:
  !v ps.
    LENGTH ps = LENGTH v ==>
    pmatch_list_pos ps v (initial_pos (LENGTH v)) =
    pmatch_list     ps v
Proof
  ho_match_mp_tac SNOC_INDUCT \\ rw[]
  >- fs[initial_pos_def, pmatch_list_pos_def, pmatch_def]
  >- (rw[initial_pos_def, GENLIST, SNOC_APPEND] \\
      fs[initial_pos_def] \\
      Cases_on `ps = []`
      >- fs[]
      >- (`?p qs. ps = SNOC p qs` by metis_tac[SNOC_CASES] \\
          fs[ADD_1_SUC] \\
          fs[pmatch_list_app_cases, pmatch_list_app_pos_cases] \\
          first_x_assum (qspec_then `qs` assume_tac) \\
          rfs[] \\ fs[pmatch_list_pos_def, app_list_pos_def, app_pos_def] \\
          fs[app_list_pos_last, pmatch_def] \\
          fs[pmatch_list_pos_app_too_much]))
QED

Definition match_pos_def:
  (match_pos [] v ts = SOME MatchFailure) /\
  (match_pos ((Branch ps e)::bs) v ts =
    case pmatch_list_pos ps v ts of
       PMatchSuccess =>
         (case match_pos bs v ts of
           NONE => NONE
         | SOME _ => SOME (MatchSuccess e))
     | PMatchFailure => match_pos bs v ts
     | PTypeFailure => NONE)
End

Theorem tf_match_pos_match:
  !m v pos. inv_mat m /\
            msize m = LENGTH v /\
            pos = initial_pos (LENGTH v) /\
            IS_SOME (match m v) ==>
            IS_SOME (match_pos m v pos)
Proof
  ho_match_mp_tac (theorem "match_pos_ind") \\ rw[]
  >- (Cases_on `v` \\
      fs[initial_pos_def, match_pos_def, match_pos_def])
  >- (fs[match_pos_def, match_def] \\
      Cases_on `m`
      >- (fs[msize_def] \\
          imp_res_tac pmatch_list_pos_pmatch_list \\ fs[] \\
          every_case_tac \\ fs[]
          >- (Cases_on `v` \\ fs[initial_pos_def, match_pos_def])
          >- (Cases_on `v` \\ fs[initial_pos_def, match_pos_def]))
      >- (imp_res_tac msize_inv \\
          imp_res_tac inv_mat_dcmp \\
          fs[msize_def, initial_pos_def] \\
          assume_tac pmatch_list_pos_pmatch_list \\
          first_x_assum (qspecl_then [`v`, `ps`] assume_tac) \\
          `LENGTH ps = LENGTH v` by fs[] \\
          fs[] \\
          fs[initial_pos_def] \\
          every_case_tac \\ fs[]))
QED

Theorem match_pos_match:
  !m v pos. inv_mat m /\
            pos = initial_pos (LENGTH v) /\
            (msize m) = (LENGTH v) /\
            IS_SOME (match m v) ==>
            match_pos m v pos =
            match     m v
Proof
  ho_match_mp_tac (theorem "match_pos_ind") \\ rw[]
  >- (Cases_on `v`
      >- fs[initial_pos_def, match_pos_def, match_def]
      >- fs[msize_def])
  >- (Cases_on `m`
      >- (fs[match_pos_def, match_def, msize_def] \\
          fs[pmatch_list_pos_pmatch_list])
      >- (imp_res_tac tf_match_pos_match \\
          first_x_assum (qspec_then `initial_pos (LENGTH v)` assume_tac) \\ fs[] \\
          fs[match_pos_def, match_def] \\
          assume_tac pmatch_list_pos_pmatch_list \\
          first_x_assum (qspecl_then [`v`, `ps`] assume_tac) \\
          `LENGTH ps = LENGTH v` by fs[msize_def] \\
          Cases_on `pmatch_list ps v`
          >- (fs[] \\
              imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\ fs[] \\
              Cases_on `match_pos (h::t) v (initial_pos (msize (Branch ps e::h::t)))` \\
              Cases_on `match (h::t) v` \\ fs[])
          >- (fs[] \\
              imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\ fs[])
          >- fs[]))
QED;

Theorem swap_positions:
  !pos v i. i < (LENGTH pos) ==>
            apply_positions (swap_items i pos) v =
            swap_items i (apply_positions pos v)
Proof
  ho_match_mp_tac apply_positions_ind \\ rw[] \\
  fs[apply_positions_def, swap_items_def] \\
  Cases_on `i` \\ fs[apply_positions_def] \\
  rw[swap_items_def, get_ith_def, replace_ith_def] \\
  fs[LENGTH_APPEND, LENGTH_TAKE_EQ, TAKE_LENGTH_ID_rwt]
  >- (fs[GSYM MAP_DROP] \\
      fs[drop_not_nil, map_hd])
  >- fs[MAP_TAKE, MAP_DROP]
QED

Theorem swap_match_pos:
  !m v i pos.
    (LENGTH pos) = (msize m) /\
    inv_mat m /\
    i < (LENGTH pos) ==>
    match_pos (swap_columns i m) v (swap_items i pos) =
    match_pos m v pos
Proof
  cheat
QED

Theorem pmatch_all_wild:
  !p t. all_wild [p] ==>
        pmatch p t = PMatchSuccess
Proof
  `(!p t. all_wild [p] ==> pmatch p t = PMatchSuccess) /\
   (!(x: pat list) (y: term list). T)` suffices_by rw[] \\
  ho_match_mp_tac (theorem "pmatch_ind") \\ rw[]
  >- fs[pmatch_def]
  >- fs[all_wild_def]
  >- fs[all_wild_def]
  >- fs[all_wild_def, pmatch_def]
QED

Theorem pmatch_list_pos_all_wild:
  !ps v pos.
    LENGTH ps = LENGTH pos /\
    all_wild ps /\
    pmatch_list_pos ps v pos <> PTypeFailure ==>
    pmatch_list_pos ps v pos = PMatchSuccess
Proof
  ho_match_mp_tac (theorem "pmatch_list_pos_ind") \\ rw[]
  >- fs[pmatch_list_pos_def]
  >- (fs[pmatch_list_pos_def] \\
      every_case_tac \\ fs[]
      >- (imp_res_tac all_wild_dcmp \\
          imp_res_tac pmatch_all_wild \\
          fs[])
      >- (imp_res_tac all_wild_dcmp \\ fs[])
      >- (imp_res_tac all_wild_dcmp \\ fs[]))
QED

Theorem match_pos_match_spec:
  !m v pos c a.
    msize m = LENGTH pos /\
    m <> [] /\
    0 < msize m /\
    is_cons_fcol m /\
    IS_SOME (match_pos m v pos) /\
    inv_mat m ==>
    match_pos m v pos =
    match_pos (spec c a m) v (pos_spec a pos)
Proof
  cheat
QED

Theorem compile_correct:
  (!h pos m useh v.
    msize m = LENGTH pos /\
    IS_SOME (match_pos m v pos) /\
    (~useh ==> is_cons_fcol m) /\
    inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (compile h pos m useh))) /\
  (!h pos m cinfos t v.
    msize m = LENGTH pos /\
    m <> [] /\
    0 < (msize m) /\
    is_cons_fcol m /\
    IS_SOME (match_pos m v pos) /\
    inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (make_complete h pos m cinfos t))) /\
  (!h pos m cinfos t v.
    msize m = LENGTH pos /\
    m <> [] /\
    is_cons_fcol m /\
    0 < (msize m) /\
    IS_SOME (match_pos m v pos) /\
    inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (make_partial h pos m cinfos t)))
Proof
  ho_match_mp_tac (theorem "compile_ind") \\ rw[]
  (* There are no branches *)
  >- fs[match_pos_def, compile_def, dt_eval_def]
  (* We don't have columns anymore *)
  >- (fs[match_pos_def] \\
      Cases_on `v` \\
      Cases_on `pos` \\
      Cases_on `bs` \\
      every_case_tac \\
      fs[apply_positions_def, pmatch_list_pos_def, msize_def, compile_def,
         dt_eval_def, match_pos_def])
  (* We have at least one column, and one row*)
  >- (fs[compile_def] \\
      TOP_CASE_TAC  \\ fs[]
      >- (Cases_on `pmatch_list_pos (v13::v14) v pos = PTypeFailure` \\
          fs[match_pos_def, pmatch_list_pos_all_wild, msize_def] \\
          every_case_tac \\ fs[dt_eval_def, pmatch_list_pos_all_wild])
      >- (TOP_CASE_TAC \\ fs[]
          >- (TOP_CASE_TAC \\ fs[]
              >- (TOP_CASE_TAC \\ fs[]
                  >- (qpat_assum `msize _ = _` (assume_tac o GSYM) \\
                      imp_res_tac (GSYM swap_match_pos) \\
                      rpt (first_x_assum (qspec_then `v` assume_tac)) \\
                      fs[] \\ first_x_assum ho_match_mp_tac \\ rw[]
                      >- fs[swap_columns_msize, swap_items_length]
                      >- fs[swap_columns_inv_mat])
                  >- (qpat_assum `msize _ = _` (assume_tac o GSYM) \\
                      assume_tac (GSYM swap_match_pos) \\
                      first_x_assum (qspecl_then [`Branch (v13::v14) e::bs`, `v`,
                                                   `simple_heuristic (Branch (v13::v14) e::bs)`, `pos`] assume_tac) \\
                      rfs[] \\
                      `LENGTH pos = SUC (LENGTH v14)` by fs[msize_def] \\
                      assume_tac inv_simple_heuristic \\ fs[inv_heuristic_def] \\
                      first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
                      fs[] \\ res_tac \\
                      fs[] \\ first_x_assum ho_match_mp_tac \\ rw[]
                      >- fs[swap_columns_msize, swap_items_length]
                      >- fs[swap_columns_inv_mat]))
              >- (qpat_assum `msize _ = _` (assume_tac o GSYM) \\
                  assume_tac (GSYM swap_match_pos) \\
                  first_x_assum (qspecl_then [`Branch (v13::v14) e::bs`, `v`,
                                              `simple_heuristic (Branch (v13::v14) e::bs)`, `pos`] assume_tac) \\
                  rfs[] \\
                  `LENGTH pos = SUC (LENGTH v14)` by fs[msize_def] \\
                  assume_tac inv_simple_heuristic \\ fs[inv_heuristic_def] \\
                  first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
                  fs[] \\ res_tac \\
                  fs[] \\ first_x_assum ho_match_mp_tac \\ rw[]
                  >- fs[swap_columns_msize, swap_items_length]
                  >- fs[swap_columns_inv_mat])
              >- (qpat_assum `msize _ = _` (assume_tac o GSYM) \\
                  assume_tac (GSYM swap_match_pos) \\
                  first_x_assum (qspecl_then [`Branch (v13::v14) e::bs`, `v`,
                                              `simple_heuristic (Branch (v13::v14) e::bs)`, `pos`] assume_tac) \\
                  rfs[] \\
                  `LENGTH pos = SUC (LENGTH v14)` by fs[msize_def] \\
                  assume_tac inv_simple_heuristic \\ fs[inv_heuristic_def] \\
                  first_x_assum (qspecl_then [`v13::v14`, `e`, `bs`] assume_tac) \\
                  fs[] \\ res_tac \\
                  fs[] \\ first_x_assum ho_match_mp_tac \\ rw[]
                  >- fs[swap_columns_msize, swap_items_length]
                  >- fs[swap_columns_inv_mat]))
          >- (TOP_CASE_TAC \\
              first_x_assum ho_match_mp_tac \\ rw[] \\ fs[msize_def])))
  >- (fs[compile_def] \\
      sg `match_pos m v pos = match_pos (spec c a m) v (pos_spec a pos)`
      >- (ho_match_mp_tac match_pos_match_spec \\ rw[])
      >- (fs[] \\
          Cases_on `spec c a m = []`
          >- fs[match_pos_def, compile_def, dt_eval_def]
          >- (fs[] \\
              first_x_assum ho_match_mp_tac \\ rw[]
              >- (`msize m > 0` by fs[] \\
                  imp_res_tac spec_msize \\ fs[] \\
                  Cases_on `pos`
                  >- fs[]
                  >- (Cases_on `h` \\ fs[pos_spec_def, pos_spec_aux_def]))
              >- fs[spec_inv_mat])))
  >- cheat
  (* same for make partial *)
  >- cheat
  >- cheat
  >- cheat
QED;

Definition merge_tree_def:
  merge_tree (If p k c a t1 t2) =
       (let o1 = merge_tree t1 in
        let o2 = merge_tree t2 in
          if o1 = o2 then o1 else If p k c a o1 o2) /\
  merge_tree (Swap n t1) = merge_tree t1 /\
  merge_tree res = res
End

Theorem dt_eval_merge_tree:
  !t v res.
    dt_eval v t = SOME res ==>
    dt_eval v (merge_tree t) = SOME res
Proof
  Induct \\ fs [merge_tree_def,dt_eval_def]
  \\ Cases_on `merge_tree t = merge_tree t'` \\ fs []
  \\ fs [merge_tree_def,dt_eval_def]
  \\ fs [option_case_eq,CaseEq"term",CaseEq"bool"]
  \\ rpt strip_tac \\ rveq \\ fs []
QED

Definition pat_compile_def:
  pat_compile h m = merge_tree (compile h (initial_pos (msize m)) m T)
End

Theorem pat_compile_correct:
  !h m v.
    LENGTH v = msize m /\
    inv_mat m /\
    IS_SOME (match m v) ==>
      match m v =
      dt_eval v (pat_compile h m)
Proof
  rw[pat_compile_def] \\
  `match m v = match_pos m v (initial_pos (LENGTH v))` by
     (ho_match_mp_tac (GSYM match_pos_match) \\ rw[]) \\
  qsuff_tac `match m v =
        dt_eval v (compile h (initial_pos (msize m)) m T)`
  >- (strip_tac \\ fs [] \\ metis_tac [dt_eval_merge_tree,IS_SOME_EXISTS]) \\
  fs[] \\
  assume_tac compile_correct \\ fs[] \\
  first_x_assum ho_match_mp_tac \\ rw[] \\
  rfs[] \\ rw[initial_pos_def]
QED

Definition pat_ok_def:
  pat_ok p Any = T /\
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

Theorem branches_ok_app:
  !b1 b2 p.
    branches_ok p (b1 ++ b2) =
    (branches_ok p b1 /\
     branches_ok p b2)
Proof
  Induct_on `b1` \\ rw[]
  >- fs[branches_ok_def]
  >- (Cases_on `h` \\ fs[branches_ok_def] \\
      metis_tac[CONJ_SYM])
QED

Theorem branches_ok_n_any:
  !n p. EVERY (pat_ok p) (n_any n)
Proof
  Induct_on `n` \\ rw[n_any_def, pat_ok_def]
QED

Theorem branches_ok_spec:
  !c a m p. inv_mat m /\
            msize m > 0 /\
            m <> [] /\
            branches_ok p m ==>
            branches_ok p (spec c a m)
Proof
  ho_match_mp_tac (theorem "spec_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[spec_def, branches_ok_def, branches_ok_n_any]
      >- (fs[spec_def, branches_ok_def, branches_ok_n_any] \\
          first_x_assum ho_match_mp_tac \\ rw[]
          >- imp_res_tac inv_mat_dcmp
          >- (imp_res_tac msize_inv_gt_zero \\ fs[])))
  >- (Cases_on `m`
      >- (fs[spec_def, branches_ok_def] \\
          every_case_tac \\ fs[]
          >- (fs[pat_ok_def, branches_ok_def] \\
              `EVERY (\a. pat_ok p a) pargs` suffices_by
              rewrite_tac [Once ETA_THM] \\
              fs[])
          >- fs[branches_ok_def]
          >- fs[branches_ok_def])
      >- (fs[spec_def, branches_ok_def] \\
          every_case_tac \\ fs[]
          >- (fs[branches_ok_def] \\ rw[]
              >- (fs[pat_ok_def] \\
                  `EVERY (\a. pat_ok p a) pargs` suffices_by
                  rewrite_tac [Once ETA_THM] \\
                  fs[])
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- imp_res_tac inv_mat_dcmp
                  >- (imp_res_tac msize_inv_gt_zero \\ fs[])))
          >- (first_x_assum ho_match_mp_tac \\ rw[]
              >- imp_res_tac inv_mat_dcmp
              >- (imp_res_tac msize_inv_gt_zero \\ fs[]))
          >- (first_x_assum ho_match_mp_tac \\ rw[]
              >- imp_res_tac inv_mat_dcmp
              >- (imp_res_tac msize_inv_gt_zero \\ fs[]))))
  >- (fs[spec_def, branches_ok_def, branches_ok_app] \\ rw[]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- (imp_res_tac inv_mat_or1 \\ imp_res_tac inv_mat_cons)
          >- fs[msize_def]
          >- fs[pat_ok_def])
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- (imp_res_tac inv_mat_or2 \\ imp_res_tac inv_mat_cons)
          >- fs[msize_def]
          >- fs[pat_ok_def])
      >- (Cases_on `m`
          >- fs[spec_def]
          >- (first_x_assum ho_match_mp_tac \\ rw[]
              >- imp_res_tac inv_mat_dcmp
              >- (imp_res_tac msize_inv_gt_zero \\ fs[]))))
  >- fs[msize_def]
QED

Theorem branches_ok_default:
  !m p. inv_mat m /\
        msize m > 0 /\
        m <> [] /\
        branches_ok p m ==>
        branches_ok p (default m)
Proof
  ho_match_mp_tac (theorem "default_ind") \\ rw[]
  >- (fs[default_def, branches_ok_def] \\
      Cases_on `m`
      >- fs[default_def]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- imp_res_tac inv_mat_dcmp
          >- (imp_res_tac msize_inv_gt_zero \\ fs[])))
  >- (fs[default_def, branches_ok_def] \\
      Cases_on `m`
      >- fs[default_def]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- imp_res_tac inv_mat_dcmp
          >- (imp_res_tac msize_inv_gt_zero \\ fs[])))
  >- (fs[default_def, branches_ok_def, branches_ok_app] \\ rw[]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- (imp_res_tac inv_mat_or1 \\ imp_res_tac inv_mat_cons)
          >- fs[msize_def]
          >- fs[pat_ok_def])
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- (imp_res_tac inv_mat_or2 \\ imp_res_tac inv_mat_cons)
          >- fs[msize_def]
          >- fs[pat_ok_def])
      >- (Cases_on `m`
          >- fs[default_def]
          >- (first_x_assum ho_match_mp_tac \\ rw[]
              >- imp_res_tac inv_mat_dcmp
              >- (imp_res_tac msize_inv_gt_zero \\ fs[]))))
  >- fs[msize_def]
QED

Theorem drop_pat_ok_decompose:
  !i t p. i < LENGTH t ==>
          (pat_ok p (HD (DROP i t)) /\
           EVERY (pat_ok p) (DROP (SUC i) t)) =
          EVERY (pat_ok p) (DROP i t)
Proof
  Induct_on `t`
  >- fs[DROP_def]
  >- (fs[DROP_def] \\
      Cases_on `i = 0` \\
      rw[pat_ok_def] \\
      first_x_assum (qspec_then `i' - 1` assume_tac) \\
      rfs[ADD1])
QED

Theorem drop_take_pat_ok:
  !i t p. i < LENGTH t ==>
          ((EVERY (pat_ok p) (TAKE i t)) /\ (EVERY (pat_ok p) (DROP i t))) =
          EVERY (pat_ok p) t
Proof
  rw[] \\
  `EVERY (pat_ok p) t = EVERY (pat_ok p) ((TAKE i t) ++ (DROP i t))` by rewrite_tac[TAKE_DROP] \\
  fs[]
QED

Theorem pat_ok_swap:
  !l p i. i < LENGTH l ==>
          EVERY (pat_ok p) (swap_items  i l) =
          EVERY (pat_ok p) l
Proof
  Cases_on `l` \\
  fs[swap_items_def] \\
  Cases_on `t` \\
  fs[swap_items_def] \\
  Cases_on `i` \\
  rw[swap_items_def, get_ith_def, replace_ith_def] \\
  fs[LENGTH_APPEND, LENGTH_TAKE_EQ, TAKE_LENGTH_ID_rwt] \\
  Cases_on `n`
  >- (fs[pat_ok_def] \\
      Cases_on `EVERY (pat_ok p) t'` \\ fs[] \\
      Cases_on `pat_ok p h'` \\ fs[])
  >- (fs[DROP_def, pat_ok_def] \\
      Cases_on `pat_ok p h` \\ fs[] \\
      Cases_on `pat_ok p h'` \\ fs[] \\
      metis_tac [CONJ_SYM, drop_take_pat_ok, drop_pat_ok_decompose])
QED

Theorem branches_ok_swap:
  !m p i.
    i < (msize m) /\ inv_mat m ==>
    branches_ok p (swap_columns i m) =
    branches_ok p m
Proof
  Induct_on `m`
  >- fs[swap_columns_def]
  >- (Cases_on `h` \\
      rw[swap_columns_def, branches_ok_def] \\
      Cases_on `branches_ok p m` \\ fs[] \\
      `i < LENGTH l` by fs[msize_def] \\
      fs[pat_ok_swap]
      >- (Cases_on `m`
          >- fs[msize_def, pat_ok_def, swap_columns_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\ res_tac))
      >- (Cases_on `m`
          >- fs[swap_columns_def]
          >- (imp_res_tac msize_inv \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\ res_tac)))
QED

Definition dt_ok_def:
  dt_ok p (Leaf k) = T /\
  dt_ok p Fail = T /\
  dt_ok p DTypeFail = T /\
  dt_ok p (Swap _ dt) = dt_ok p dt /\
  dt_ok p (If pos k c a dt1 dt2) = (dt_ok p dt1 /\ dt_ok p dt2 /\ p k c a)
End

Theorem every_add_cons:
  !k c n a infos p.
    EVERY (λ(k,c,_,a). p k c a) (add_cons k c n a infos) =
    ((λ(k,c,_,a). p k c a) (k, c, n, a) /\ EVERY (λ(k,c,_,a). p k c a) infos)
Proof
  ho_match_mp_tac (theorem "add_cons_ind") \\ rw[]
  >- fs[add_cons_def]
  >- (fs[add_cons_def] \\
      every_case_tac \\ fs[]
      >- (Cases_on `p k' c' a'` \\ fs[])
      >- (Cases_on `p k c a` \\
          Cases_on `p k' c' a'` \\ fs[])
      >- (Cases_on `p k c a` \\
          Cases_on `p k' c' a'` \\ fs[])
      >- (Cases_on `p k c a` \\
          Cases_on `p k' c' a'` \\ fs[]))
QED

Theorem every_merge_cinfos:
  !inf1 inf2 p.
    EVERY p (merge_cinfos inf1 inf2) =
    (EVERY p inf1 /\ EVERY p inf2)
Proof
  Induct_on `inf1`
  >- fs[merge_cinfos_def]
  >- (rw[merge_cinfos_def]
      >- (eq_tac \\ rw[] \\
          imp_res_tac EVERY_MEM)
      >- (eq_tac \\ rw[]))
QED

Theorem branches_ok_cinfos:
  !m p. branches_ok p m ==>
        EVERY (λ(k,c,_,a). p k c a) (cinfos m)
Proof
  ho_match_mp_tac (theorem "cinfos_ind") \\ rw[]
  >- fs[cinfos_def]
  >- fs[cinfos_def, branches_ok_def]
  >- fs[cinfos_def, branches_ok_def]
  >- fs[cinfos_def, branches_ok_def, every_add_cons, pat_ok_def]
  >- (fs[cinfos_def, every_merge_cinfos] \\ rw[] \\
      first_x_assum ho_match_mp_tac \\ rw[] \\
      fs[branches_ok_def, pat_ok_def])
QED

Definition list_to_bag_def:
  (list_to_bag [] = {||}) ∧
  (list_to_bag (h::t) = BAG_INSERT h (list_to_bag t))
End

Theorem every_bag_every:
  !l p. EVERY p l <=> BAG_EVERY p (list_to_bag l)
Proof
  Induct_on `l` \\ fs[list_to_bag_def]
QED

Theorem add_cons_not_empty:
  !k c n a m.
    add_cons k c n a m <> []
Proof
  ho_match_mp_tac (theorem "add_cons_ind") \\ rw[]
  >- fs[add_cons_def]
  >- (fs[add_cons_def] \\
      every_case_tac \\ fs[])
QED

Theorem mem_not_empty:
  !l x. MEM x l ==> l <> []
Proof
  Cases_on `l` \\ fs[]
QED

Theorem merge_cinfos_not_empty:
  !inf1 inf2.
    (inf1 <> [] \/
     inf2 <> []) ==>
    (merge_cinfos inf1 inf2) <> []
Proof
  Induct_on `inf1` \\ rw[]
  >- fs[merge_cinfos_def]
  >- (fs[merge_cinfos_def] \\
      TOP_CASE_TAC \\ rw[] \\
      imp_res_tac mem_not_empty \\
      fs[])
QED

Theorem cinfos_not_empty:
  !m.
    is_cons_fcol m ==>
    cinfos m <> []
Proof
  ho_match_mp_tac cinfos_ind \\ rw[]
  >- fs[is_cons_fcol_def, is_cons_fcol_branch_def]
  >- fs[cinfos_def, is_cons_fcol_def, is_cons_fcol_branch_def]
  >- fs[cinfos_def, is_cons_fcol_def, is_cons_fcol_branch_def,
        is_cons_fcol_pat_def]
  >- fs[cinfos_def, add_cons_not_empty]
  >- (fs[cinfos_def, is_cons_fcol_def, is_cons_fcol_branch_def,
         is_cons_fcol_pat_def] \\
      res_tac \\
      metis_tac [merge_cinfos_not_empty])
QED

Theorem dt_ok_pat_compile_aux:
  (!h pos m useh v p.
    inv_mat m /\
    branches_ok p m ==>
    dt_ok p (compile h pos m useh)) /\
  (!h pos m cinf t v p.
    inv_mat m /\
    branches_ok p m /\
    cinf <> [] /\
    (list_to_bag (cinfos m)) = (list_to_bag cinf) ⊎ (list_to_bag t) ==>
    dt_ok p (make_complete h pos m cinf t)) /\
  (!h pos m cinf t v p.
    inv_mat m /\
    branches_ok p m /\
    (list_to_bag (cinfos m)) = (list_to_bag cinf) ⊎ (list_to_bag t) ==>
    dt_ok p (make_partial h pos m cinf t))
Proof
  ho_match_mp_tac (theorem "compile_ind") \\ rw[]
  >- fs[compile_def, dt_ok_def]
  >- fs[compile_def, dt_ok_def]
  >- (fs[compile_def] \\
      TOP_CASE_TAC \\ fs[dt_ok_def] \\
      TOP_CASE_TAC \\ fs[]
      >- (TOP_CASE_TAC \\ fs[]
          >- (TOP_CASE_TAC \\ fs[]
              >- (first_x_assum ho_match_mp_tac \\ rw[]
                  >- fs[swap_columns_inv_mat]
                  >- fs[branches_ok_swap])
              >- (first_x_assum ho_match_mp_tac \\ rw[] \\
                  `0 < msize (Branch (v13::v14) e::bs)` by fs[msize_def] \\
                  imp_res_tac inv_simple_heuristic_aux
                  >- fs[swap_columns_inv_mat]
                  >- fs[branches_ok_swap]))
          >- (first_x_assum ho_match_mp_tac \\ rw[] \\
              `0 < msize (Branch (v13::v14) e::bs)` by fs[msize_def] \\
              imp_res_tac inv_simple_heuristic_aux
              >- fs[swap_columns_inv_mat]
              >- fs[branches_ok_swap])
          >- (first_x_assum ho_match_mp_tac \\ rw[] \\
              `0 < msize (Branch (v13::v14) e::bs)` by fs[msize_def] \\
              imp_res_tac inv_simple_heuristic_aux
              >- fs[swap_columns_inv_mat]
              >- fs[branches_ok_swap]))
      >- (TOP_CASE_TAC
          >- (fs[list_to_bag_def] \\
              Cases_on `cinfos (Branch (v13::v14) e::bs) = []`
              >- fs[is_col_complete_def]
              >- fs[])
          >- fs[list_to_bag_def]))
  >- (fs[compile_def] \\
      every_case_tac \\ fs[dt_ok_def] \\
      first_x_assum ho_match_mp_tac \\ rw[]
      >- fs[spec_inv_mat]
      >- fs[branches_ok_spec])
  >- (fs[compile_def] \\
      every_case_tac \\ fs[dt_ok_def] \\ rw[]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- fs[spec_inv_mat]
          >- fs[branches_ok_spec])
      >- (first_x_assum ho_match_mp_tac \\ rw[list_to_bag_def] \\
          fs[list_to_bag_def] \\
          metis_tac[BAG_INSERT_UNION, COMM_BAG_UNION, ASSOC_BAG_UNION])
      >- (imp_res_tac branches_ok_cinfos \\
          imp_res_tac every_bag_every \\
          rfs[list_to_bag_def]))
  >- (fs[compile_def] \\
      every_case_tac \\ fs[dt_ok_def] \\
      first_x_assum ho_match_mp_tac \\ rw[]
      >- fs[default_inv_mat]
      >- fs[branches_ok_default])
  >- (fs[compile_def] \\
      every_case_tac \\ fs[dt_ok_def] \\ rw[]
      >- (first_x_assum ho_match_mp_tac \\ rw[]
          >- fs[spec_inv_mat]
          >- fs[branches_ok_spec])
      >- (first_x_assum ho_match_mp_tac \\ rw[list_to_bag_def] \\
          fs[list_to_bag_def] \\
          metis_tac[BAG_INSERT_UNION, COMM_BAG_UNION, ASSOC_BAG_UNION])
      >- (imp_res_tac branches_ok_cinfos \\
          imp_res_tac every_bag_every \\
          rfs[list_to_bag_def]))
QED

Theorem dt_ok_merge_tree:
  !p t. dt_ok p t ==> dt_ok p (merge_tree t)
Proof
  Induct_on `t` \\ fs [merge_tree_def,dt_ok_def]
  \\ rw [] \\ fs [merge_tree_def,dt_ok_def]
QED

Theorem dt_ok_pat_compile:
  inv_mat m /\ branches_ok p m ==> dt_ok p (pat_compile h m)
Proof
  rw[pat_compile_def] \\
  match_mp_tac dt_ok_merge_tree \\
  assume_tac dt_ok_pat_compile_aux \\ rw[]
QED

(*
The example from my report (Figure 4.1):

case (l1,l2) of
  (Nil, Nil) => 1
  (_::_, Nil) => 2
  (Nil, _::_) => 3
  (_::_, _::_) => 4

Patterns:

Nil = Cons 0 2 []
(x::l) = Cons 1 2 [x;l]

Terms:

Nil = Term 0 []
(x::l) = Term 1 [x;l]
x = Term 3 []
y = Term 4 []
*)

Theorem test1:
  dt_eval [Term 0 0 []; Term 0 0 []]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 0 (SOME 2) []        ; Cons 0 0 (SOME 2) []]        1;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 0 (SOME 2) []]        2;
          Branch [Cons 0 0 (SOME 2) []        ; Cons 0 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 1)
Proof
  EVAL_TAC
QED

Theorem test2:
  dt_eval [Term 0 1 [Term 0 3 []; Term 0 0 []]; Term 0 0 []]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 0 (SOME 2) []        ; Cons 0 0 (SOME 2) []]        1;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 0 (SOME 2) []]        2;
          Branch [Cons 0 0 (SOME 2) []        ; Cons 0 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 2)
Proof
  EVAL_TAC
QED

Theorem test3:
  dt_eval [Term 0 0 []; Term 0 1 [Term 0 3 []; Term 0 0 []]]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 0 (SOME 2) []        ; Cons 0 0 (SOME 2) []]        1;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 0 (SOME 2) []]        2;
          Branch [Cons 0 0 (SOME 2) []        ; Cons 0 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 3)
Proof
  EVAL_TAC
QED

Theorem test4:
  dt_eval [Term 0 1 [Term 0 3 []; Term 0 0 []]; Term 0 1 [Term 0 4 []; Term 0 0 []]]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 0 (SOME 2) []        ; Cons 0 0 (SOME 2) []]        1;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 0 (SOME 2) []]        2;
          Branch [Cons 0 0 (SOME 2) []        ; Cons 0 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 0 1 (SOME 2) [Any;Any] ; Cons 0 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 4)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
