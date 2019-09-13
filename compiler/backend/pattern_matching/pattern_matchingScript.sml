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
*)
Datatype:
  term = Term num (term list) | Other
End

Definition get_cons_def:
  (get_cons (Term c ts) = SOME (c, LENGTH ts)) /\
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
  (app_pos (Pos _ _) (Term c []) = NONE) /\
  (app_pos (Pos 0 pos) (Term c (x::xs)) =
    app_pos pos x) /\
  (app_pos (Pos (SUC n) pos) (Term c (x::xs)) =
    app_pos (Pos n pos) (Term c xs))
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
  (* A constructor pattern is an constructor id, the number of constructors
     in its type and a list of other patterns
     If the number of constructor in its type is NONE, it means it can be
     infinite, and we have to assume it is never exhaustive
  *)
  | Cons num (num option) (pat list)
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
  (psize (Cons n t []) = 2) /\
  (psize (Cons n t (x::xs)) = 1 + (psize x) + psize (Cons n t xs)) /\
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
  (pmatch (Cons _ _ _) Other = PTypeFailure) /\
  (pmatch (Cons pcons _ pargs) (Term tcons targs) =
    if pcons = tcons
    then pmatch_list pargs targs
    else PMatchFailure) /\
  (pmatch (Or p1 p2) t =
    case pmatch p1 t of
       PMatchSuccess => PMatchSuccess
     | PMatchFailure => pmatch p2 t
     | PTypeFailure => PTypeFailure) /\
  (pmatch_list [] [] = PMatchSuccess) /\
  (pmatch_list [] ts = PTypeFailure) /\
  (pmatch_list ps [] = PTypeFailure) /\
  (pmatch_list (p::ps) (t::ts) =
    case pmatch p t of
      PMatchSuccess => pmatch_list ps ts
    | PMatchFailure => PMatchFailure
    | PTypeFailure => PTypeFailure)
Termination
  WF_REL_TAC `measure (λx. case x of INL(p,t) => psize p
                                    | INR(ps,ts) => plist_size ps)` \\ rw[]
  >- fs[plist_size_def, plist_size_gt_zero]
  >- fs[plist_size_def, psize_gt_zero]
  >- (Induct_on `pargs` \\ fs[plist_size_def, psize_def])
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
      fs[])
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
      rw[] \\ every_case_tac
      >- res_tac
      >- fs[]
      >- fs[])
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
      every_case_tac \\ fs[])
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
      every_case_tac \\ fs[])
QED

Theorem tfpmatch_list_app2:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t1 p1 = PTypeFailure ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PTypeFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[])
QED

Theorem npmatch_list_app21:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t1 p1 = PMatchFailure ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) = PMatchFailure
Proof
  Induct_on `t1` \\ rw[]
  >- fs[pmatch_def]
  >- (fs[pmatch_def] \\
      Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[])
QED

Theorem npmatch_list_app22:
  !p1 t1 p2 t2.
    LENGTH t1 = LENGTH p1 /\
    LENGTH t2 = LENGTH p2 /\
    pmatch_list t2 p2 = PMatchFailure ==>
    pmatch_list (t1 ++ t2) (p1 ++ p2) <> PMatchSuccess
Proof
  Induct_on `t1` \\ rw[]
  >- (fs[pmatch_def] \\
      Cases_on `p1` \\ fs[pmatch_def] \\
      every_case_tac \\ fs[])
QED

Theorem pmatch_list_length:
  !ps ts. pmatch_list ps ts = PMatchSuccess ==>
          (LENGTH ps = LENGTH ts)
Proof
  Induct_on `ps`
  >- (Cases_on `ts` \\
      fs[pmatch_def])
  >- (Cases_on `ts` \\
      fs[pmatch_def] \\
      Cases_on `pmatch h' h` \\
      rw[])
QED;

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
       PMatchSuccess => SOME (MatchSuccess e)
     | PMatchFailure => match bs ts
     | PTypeFailure => NONE)
End

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
      every_case_tac \\ fs[] \\
      imp_res_tac pmatch_list_length)
  >- (Cases_on `h` \\
      fs[match_def] \\
      every_case_tac
      >- (imp_res_tac pmatch_list_length \\ fs[msize_def]) \\
      res_tac \\
      imp_res_tac inv_mat_dcmp \\
      fs[] \\
      imp_res_tac msize_inv \\
      fs[])
QED;

Theorem match_first_patlist:
  !ps ts e xs.
    pmatch_list ps ts = PMatchSuccess ==>
    match ((Branch ps e)::xs) ts = SOME (MatchSuccess e)
Proof
  rw[] \\
  Cases_on `ps` \\
  rw[match_def]
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

Theorem match_app:
  !b1 ts b2 x.
    match b1 ts = SOME (MatchSuccess x) ==>
    match (b1 ++ b2) ts = SOME (MatchSuccess x)
Proof
  ho_match_mp_tac (theorem "match_ind") \\ rw[]
  >- fs[match_def]
  >- (fs[match_def] \\
      every_case_tac \\
      rw[])
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
  (spec c a ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
    if (c = pcons /\ (a = LENGTH pargs))
    then (Branch (pargs++ps) e)::(spec c a rs)
    else (spec c a rs)) /\
  (spec c a ((Branch ((Or p1 p2)::ps) e)::rs) =
    (spec c a [Branch (p1::ps) e]) ++
    (spec c a [Branch (p2::ps) e]) ++
    (spec c a rs))
End

(* Key property of matrix decomposition (Lemma 1 of article) *)
Theorem spec_lem:
  !c a m ts targs.
    (inv_mat m /\
    ((LENGTH targs) = a) /\
    IS_SOME (match m ((Term c targs)::ts)) /\
    ((msize m) = (LENGTH ts) + 1)) ==>
    (match m ((Term c targs)::ts) =
     match (spec c (LENGTH targs) m) (targs++ts))
Proof
  cheat
(*   ho_match_mp_tac (fetch "-" "spec_ind") \\ rw[] *)
(*   >- fs[msize_def] *)
(*   >- (fs[match_def, spec_def] \\ *)
(*       every_case_tac \\ fs[pmatch_def] \\ *)
(*      `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*      `LENGTH (n_any (LENGTH targs)) = LENGTH targs` by fs[n_any_length] *)
(*       >- (imp_res_tac npmatch_list_app \\ *)
(*           rpt (WEAKEN_TAC is_forall) \\ *)
(*           fs[pmatch_list_nany]) *)
(*       >- (`pmatch_list (n_any (LENGTH targs)) targs = PMatchSuccess` *)
(*           by fs[pmatch_list_nany] \\ *)
(*           imp_res_tac pmatch_list_app2 \\ *)
(*           rpt (WEAKEN_TAC is_imp) \\ fs[]) *)
(*       >- imp_res_tac npmatch_list_app22 *)
(*       >- (Cases_on `m` *)
(*           >- rw[match_def, spec_def] *)
(*           >- (`msize (h::t) = LENGTH ts + 1` by *)
(*               (imp_res_tac msize_inv \\ fs[]) \\ *)
(*               `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*                fs[])) *)
(*       >- (imp_res_tac tfpmatch_list_app \\ *)
(*           rpt (WEAKEN_TAC is_forall) \\ *)
(*           fs[pmatch_list_nany])) *)
(*   >- (imp_res_tac match_first_patlist2 \\ *)
(*       fs[match_def, spec_def] \\ *)
(*       `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*       fs[pmatch_def] \\ every_case_tac \\ *)
(*       fs[match_def] \\ every_case_tac \\ *)
(*       TRY (`LENGTH pargs = LENGTH targs` by fs[]) *)
(*       >- (imp_res_tac pmatch_list_app \\ *)
(*           rpt (WEAKEN_TAC is_forall) \\ fs[]) *)
(*       >- (Cases_on `m` *)
(*           >- fs[match_def, spec_def] *)
(* 	  >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*               imp_res_tac inv_mat_dcmp \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*               fs[])) *)
(*       >- (imp_res_tac tfpmatch_list_app \\ fs[]) *)
(*       >- (imp_res_tac pmatch_list_app \\ *)
(*           rpt (WEAKEN_TAC is_forall) \\ fs[]) *)
(*       >- (Cases_on `m` *)
(*           >- fs[match_def, spec_def] *)
(* 	  >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*               imp_res_tac inv_mat_dcmp \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*               fs[])) *)
(*       >- (imp_res_tac npmatch_list_app21 \\ fs[]) *)
(*       >- (Cases_on `m` *)
(*           >- fs[match_def, spec_def] *)
(* 	  >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*               imp_res_tac inv_mat_dcmp \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*               fs[])) *)
(*       >- (Cases_on `m` *)
(*           >- fs[match_def, spec_def] *)
(* 	  >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*               imp_res_tac inv_mat_dcmp \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*               fs[])) *)
(*       >- (Cases_on `m` *)
(*           >- fs[match_def, spec_def] *)
(* 	  >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*               imp_res_tac inv_mat_dcmp \\ *)
(*               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\ *)
(*               fs[])) *)
(*       >- (imp_res_tac npmatch_list_app \\ fs[]) *)
(*       >- (imp_res_tac tfpmatch_list_app \\ fs[]) *)
(*       >- (imp_res_tac pmatch_list_length \\ fs[])) *)

(*   >- (fs[match_def, spec_def] \\ *)
(*       fs[pmatch_def] \\ every_case_tac \\ fs[] \\ *)
(*       rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\ rfs[] *)
(*       >- (imp_res_tac inv_mat_or1 \\ *)
(*           imp_res_tac inv_mat_cons \\ *)
(*           rfs[msize_def] \\ fs[] \\ *)
(*           `match (spec c (LENGTH targs) [Branch (p1::ps) e]) (targs ++ ts) = *)
(*            SOME (MatchSuccess e)` by fs[] \\ *)
(*           fs[match_app]) *)
(*       >- (imp_res_tac inv_mat_dcmp \\ *)
(*           imp_res_tac inv_mat_or1 \\ *)
(*           imp_res_tac inv_mat_or2 \\ *)
(*           imp_res_tac inv_mat_cons \\ *)
(* 	  every_case_tac \\ fs[] \\ rfs[] *)
(*           >- (Cases_on `m` *)
(*               >- (fs[match_def, spec_def, msize_def] \\ *)
(*                   rfs[] \\ *)
(*                   `match (spec c (LENGTH targs) [Branch (p1::ps) e]) (targs ++ ts) = *)
(*                    SOME MatchFailure` by fs[] \\ *)
(*                   fs[match_app2, match_app]) *)
(*               >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*                   fs[match_def, spec_def, msize_def] \\ *)
(*                   rfs[] \\ *)
(*                   `match (spec c (LENGTH targs) [Branch (p1::ps) e]) (targs ++ ts) = *)
(*                    SOME MatchFailure` by fs[] \\ *)
(*                   fs[match_app2, match_app])) *)
(*           >- (Cases_on `m` *)
(*               >- (fs[match_def, spec_def, msize_def] \\ *)
(*                   rfs[] \\ *)
(*                   `match (spec c (LENGTH targs) [Branch (p1::ps) e]) (targs ++ ts) = *)
(*                    SOME MatchFailure` by fs[] \\ *)
(*                   fs[match_app2, match_app]) *)
(*               >- (imp_res_tac msize_inv \\ fs[] \\ *)
(*                   fs[match_def, spec_def, msize_def] \\ *)
(*                   rfs[] \\ *)
(*                   `match (spec c (LENGTH targs) [Branch (p1::ps) e]) (targs ++ ts) = *)
(*                    SOME MatchFailure` by fs[] \\ *)
(*                   fs[match_app2, match_app])) *)
(*           >- *)




(*   >- (fs[match_def, spec_def] *)
(*     >- (imp_res_tac pmatch_list_or *)
(*       >- (match [Branch (p1::ps) e] (Term c targs::ts) = MatchResult e *)
(*           by rw[match_def] \\ *)
(*           `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*           fs[msize_def] \\ *)
(*           `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*           rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\ *)
(*           fs[] \\ res_tac \\ fs[] \\ *)
(*           metis_tac[match_app]) *)
(*       >- (Cases_on `pmatch_list (p1::ps) (Term c targs::ts)` *)
(*           >- (`match [Branch (p1::ps) e] (Term c targs::ts) = MatchResult e` *)
(*               by rw[match_def] \\ *)
(*               `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*               fs[msize_def] \\ *)
(*               `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*               rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\ *)
(*               fs[] \\ res_tac \\ fs[] \\ *)
(*               metis_tac[match_app]) *)
(*           >- (`match [Branch (p1::ps) e] (Term c targs::ts) = MatchFailure` *)
(*               by (imp_res_tac nmatch_first_patlist \\ *)
(*                  first_x_assum (qspecl_then [`[]`, `e`] assume_tac) \\ *)
(*                  fs[match_def]) \\ *)
(*               `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*               fs[msize_def] \\ *)
(*               `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*               `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\ *)
(*               rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac))\\ *)
(*               fs[] \\ res_tac \\ fs[] \\ *)
(*               imp_res_tac match_app2 \\ *)
(*               first_x_assum (qspec_then *)
(*               `spec c (LENGTH targs) [Branch (p2::ps) e] ++ *)
(*                spec c (LENGTH targs) m` assume_tac) \\ *)
(*               fs[] \\ *)
(*               `match [Branch (p2::ps) e] (Term c targs::ts) = MatchResult e` *)
(*               by (imp_res_tac match_first_patlist \\ *)
(*                   rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*                   fs[]) \\ *)
(*               rfs[] \\ *)
(*               metis_tac[match_app]))) *)
(*     >- (imp_res_tac not_pmatch_list_or \\ *)
(*         `match [Branch (p1::ps) e] (Term c targs::ts) = MatchFailure` *)
(*         by (imp_res_tac nmatch_first_patlist \\ *)
(*             rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*             fs[match_def]) \\ *)
(*         `match [Branch (p2::ps) e] (Term c targs::ts) = MatchFailure` *)
(*         by (imp_res_tac nmatch_first_patlist \\ *)
(*             rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*             fs[match_def]) \\ *)
(*         `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*         `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*         `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\ *)
(*         `match m (Term c targs::ts) = *)
(*          match (spec c (LENGTH targs) m) (targs ++ ts)` *)
(*         suffices_by *)
(*         (fs[msize_def] \\ *)
(*         rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\ *)
(*         fs[] \\ res_tac \\ fs[] \\ *)
(*         imp_res_tac match_app2 \\ *)
(*         first_assum (qspec_then *)
(*         `spec c (LENGTH targs) [Branch (p2::ps) e] ++ *)
(*          spec c (LENGTH targs) m` assume_tac) \\ *)
(*         fs[]) \\ *)
(*         Cases_on `m` *)
(*         >- rw[match_def, spec_def] *)
(*         >- (`inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*             `msize (h::t) = LENGTH ts + 1` by *)
(*             (imp_res_tac msize_inv \\ fs[]) \\ *)
(*             rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\ *)
(*             fs[]))) *)
(*   >- fs[msize_def] *)
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

(* Default matrix transformation *)
Definition default_def:
  (default [] = []) /\
  (default ((Branch (Any::ps) e)::rs) =
    (Branch ps e)::(default rs)) /\
  (default ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
    (default rs)) /\
  (default ((Branch ((Or p1 p2)::ps) e)::rs) =
    (default [Branch (p1::ps) e]) ++
    (default [Branch (p2::ps) e]) ++
    (default rs))
End

(* Key property of default matrix (Lemma 2 of article) *)
Definition is_cons_head_def:
  (is_cons_head c a [] = F) /\
  (is_cons_head c a ((Branch [] e)::rs) =
    (is_cons_head c a rs)) /\
  (is_cons_head c a ((Branch (Any::ps) e)::rs) =
    (is_cons_head c a rs)) /\
  (is_cons_head c a ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
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

Theorem default_lem:
  !m c ts targs.
   (inv_mat m /\
   ~(is_cons_head c (LENGTH targs) m) /\
    ((msize m) = (LENGTH ts) + 1)) ==>
   (match m ((Term c targs)::ts) =
    match (default m) ts)
Proof
  cheat
(*   ho_match_mp_tac (fetch "-" "default_ind") \\ rw[] *)
(*   >- fs[msize_def] *)
(*   >- (rw[match_def, default_def] *)
(*       >- fs[pmatch_list_def, pmatch_def] *)
(*       >- fs[pmatch_list_def, pmatch_def] *)
(*       >- (fs[is_cons_head_def] \\ *)
(*           Cases_on `m` *)
(*           >- rw[match_def, default_def] *)
(*           >- (`(msize (h::t)) = LENGTH ts + 1` *)
(*               by (imp_res_tac msize_inv \\ fs[]) \\ *)
(*               `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*               first_x_assum (qspecl_then [`c`,`ts`,`targs`] assume_tac) \\ *)
(*               res_tac))) *)
(*   >- (rw[match_def, default_def] *)
(*       >- (fs[pmatch_list_def, pmatch_def, is_cons_head_def] \\ *)
(*           imp_res_tac LIST_REL_LENGTH \\ fs[]) *)
(*       >- (fs[is_cons_head_def] \\ *)
(*           Cases_on `m` *)
(*           >- rw[match_def, default_def] *)
(*           >- (`(msize (h::t)) = LENGTH ts + 1` *)
(*               by (imp_res_tac msize_inv \\ fs[]) \\ *)
(*               `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*               res_tac) *)
(*           >- rw[match_def, default_def] *)
(*           >- (`(msize (h::t)) = LENGTH ts + 1` *)
(*               by (imp_res_tac msize_inv \\ fs[]) \\ *)
(*               `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*               res_tac))) *)
(*   >- (rw[match_def, default_def] *)
(*       >- (fs[is_cons_head_def] \\ *)
(*           imp_res_tac pmatch_list_or *)
(*           >- (`match [Branch (p1::ps) e] (Term c targs::ts) = MatchResult e` *)
(*               by rw[match_def] \\ *)
(*               `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*               `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*               `msize [Branch (p1::ps) e] = LENGTH ts + 1` *)
(*               by fs[msize_def] \\ *)
(*               res_tac \\ *)
(*               metis_tac[match_app]) *)
(*           >- (Cases_on `pmatch_list (p1::ps) (Term c targs::ts)` *)
(*               >- (`match [Branch (p1::ps) e] (Term c targs::ts) = MatchResult e` *)
(*                   by rw[match_def] \\ *)
(*                   `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*                   `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*                   `msize [Branch (p1::ps) e] = LENGTH ts + 1` *)
(*                   by fs[msize_def] \\ *)
(*                   res_tac \\ *)
(*                   metis_tac[match_app]) *)
(*               >- (`match [Branch (p1::ps) e] (Term c targs::ts) = MatchFailure` *)
(*                   by (imp_res_tac nmatch_first_patlist \\ *)
(*                   first_x_assum (qspecl_then [`[]`, `e`] assume_tac) \\ *)
(*                   fs[match_def]) \\ *)
(*                   `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*                   fs[msize_def] \\ *)
(*                   `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*                   `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\ *)
(*                   rpt (first_x_assum (qspecl_then [`c`, `ts`, `targs`] *)
(*                        assume_tac))\\ *)
(*                   fs[] \\ res_tac \\ fs[] \\ *)
(*                   imp_res_tac match_app2 \\ *)
(*                   first_x_assum (qspec_then *)
(*                   `default [Branch (p2::ps) e] ++ *)
(*                   default m` assume_tac) \\ *)
(*                   res_tac \\ *)
(*                   fs[] \\ *)
(*                   `match [Branch (p2::ps) e] (Term c targs::ts) = MatchResult e` *)
(*                   by (imp_res_tac match_first_patlist \\ *)
(*                      rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*                      fs[]) \\ *)
(*                   rfs[] \\ *)
(*                   metis_tac[match_app]))) *)
(*       >- (imp_res_tac not_pmatch_list_or \\ *)
(*           `match [Branch (p1::ps) e] (Term c targs::ts) = MatchFailure` *)
(*           by (imp_res_tac nmatch_first_patlist \\ *)
(*             rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*             fs[match_def]) \\ *)
(*           `match [Branch (p2::ps) e] (Term c targs::ts) = MatchFailure` *)
(*           by (imp_res_tac nmatch_first_patlist \\ *)
(*             rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\ *)
(*             fs[match_def]) \\ *)
(*           `LENGTH ps = LENGTH ts` by fs[msize_def] \\ *)
(*           `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\ *)
(*           `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\ *)
(*           fs[is_cons_head_def] \\ *)
(*           `match m (Term c targs::ts) = *)
(*           match (default m) ts` *)
(*           suffices_by *)
(*           (fs[msize_def] \\ *)
(*            rpt (first_x_assum (qspecl_then [`c`,`ts`, `targs`] assume_tac)) \\ *)
(*           fs[] \\ res_tac \\ fs[] \\ *)
(*           imp_res_tac match_app2 \\ *)
(*           first_assum (qspec_then *)
(*           `default [Branch (p2::ps) e] ++ *)
(*            default m` assume_tac) \\ *)
(*           fs[]) \\ *)
(*           Cases_on `m` *)
(*           >- rw[match_def, default_def] *)
(*           >- (`inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\ *)
(*               `msize (h::t) = LENGTH ts + 1` by *)
(*               (imp_res_tac msize_inv \\ fs[]) \\ *)
(*               rpt (first_x_assum (qspecl_then [`c`,`ts`, `targs`] assume_tac)) \\ *)
(*               fs[]))) *)
(*   >- fs[msize_def] *)
QED;

(* definition of decision trees *)
Datatype:
  dTree =
    Leaf num
  | Fail
  | DTypeFail
  | Swap num dTree
  (*
     If pos c a dt1 dt2
     if value at position pos has constructor c
     and a arguments, then go to decision tree
     dt1 else go to decision tree dt2
  *)
  | If listPos num num dTree dTree
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

(* Theorem drop_take_pmatch_list: *)
(*   !i ps ts. (LENGTH ps) = (LENGTH ts) /\ *)
(*             i < LENGTH ts ==> *)
(*             (((pmatch_list (TAKE i ps) (TAKE i ts)) /\ *)
(*               (pmatch_list (DROP i ps) (DROP i ts))) <=> *)
(*              (pmatch_list ps ts)) *)
(* Proof *)
(*   rw[] \\ *)
(*   sg `(((pmatch_list (TAKE i ps) (TAKE i ts)) /\ *)
(*         (pmatch_list (DROP i ps) (DROP i ts))) <=> *)
(*        (pmatch_list ((TAKE i ps) ++ (DROP i ps)) ((TAKE i ts) ++ (DROP i ts))))` \\ *)
(*   fs[pmatch_list_app] *)
(* QED; *)

(* Theorem drop_pmatch_list_decompose: *)
(*   !ps ts i. (LENGTH ts) = (LENGTH ps) /\ *)
(*             i < LENGTH ts ==> *)
(*             (((pmatch (HD (DROP i ps)) (HD (DROP i ts))) /\ *)
(*               (pmatch_list (DROP (SUC i) ps) (DROP (SUC i) ts))) <=> *)
(*              (pmatch_list (DROP i ps) (DROP i ts))) *)
(* Proof *)
(*   ho_match_mp_tac (theorem "pmatch_list_ind") \\ rw[] \\ *)
(*   fs[DROP_def] \\ *)
(*   Cases_on `i` \\ *)
(*   fs[pmatch_list_def] *)
(* QED; *)

(* Theorem swap_pmatch_list: *)
(*   !ps ts i. (LENGTH ts) = (LENGTH ps) /\ *)
(*             i < (LENGTH ts) ==> *)
(*             pmatch_list (swap_items i ps) *)
(*                         (swap_items i ts) = *)
(*             pmatch_list ps ts *)
(* Proof *)
(*   ho_match_mp_tac (theorem "pmatch_list_ind") \\ rw[] \\ *)
(*   Cases_on `i` \\ *)
(*   fs[swap_items_def] \\ *)
(*   rw[replace_ith_def, get_ith_def, pmatch_list_def] \\ *)
(*   fs[LENGTH_APPEND, LENGTH_TAKE_EQ, TAKE_LENGTH_ID_rwt] \\ *)
(*   fs[pmatch_list_app, pmatch_list_def] \\ *)
(*   Cases_on `pmatch p t` \\ fs[] \\ *)
(*   `LENGTH ps = LENGTH ts` by fs[] \\ *)
(*   `n < LENGTH ps` by fs[] \\ *)
(*   imp_res_tac drop_pmatch_list_decompose \\ *)
(*   rpt (WEAKEN_TAC is_imp) \\ *)
(*   imp_res_tac drop_take_pmatch_list \\ *)
(*   rpt (WEAKEN_TAC is_imp) \\ *)
(*   `(pmatch_list (TAKE n ps) (TAKE n ts) /\ *)
(*     pmatch (HD (DROP n ps)) (HD (DROP n ts)) /\ *)
(*    pmatch_list (DROP (SUC n) ps) (DROP (SUC n) ts)) <=> *)
(*    pmatch_list ps ts` suffices_by metis_tac[CONJ_COMM] \\ *)
(*   fs[] *)
(* QED; *)

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
  (dt_eval ts (If pos c' a dt1 dt2) =
    case (app_list_pos ts pos) of
      SOME (Term c targs) =>
        (if c = c' /\ (LENGTH targs) = a
         then dt_eval ts dt1
         else dt_eval ts dt2)
    | SOME Other => NONE
    | NONE => NONE)
End

Definition all_wild_or_vars_def:
  (all_wild_or_vars [] = T) /\
  (all_wild_or_vars (Any::ps) = all_wild_or_vars ps) /\
  (all_wild_or_vars ((Cons _ _ _)::_) = F) /\
  (all_wild_or_vars ((Or p1 p2)::ps) = ((all_wild_or_vars [p1]) /\
                                        (all_wild_or_vars [p2]) /\
                                        (all_wild_or_vars ps)))
End

Theorem all_wild_vars_dcmp:
  !p ps. all_wild_or_vars (p::ps) ==>
         (all_wild_or_vars [p] /\
          all_wild_or_vars ps)
Proof
  Cases_on `p` \\ fs[all_wild_or_vars_def]
QED;

(* Theorem all_wild_vars_pmatch_list_aux: *)
(*    (!p t. all_wild_or_vars [p] ==> *)
(*           pmatch p t) /\ *)
(*    (!ps ts. all_wild_or_vars ps /\ *)
(*             (LENGTH ps) = (LENGTH ts) ==> *)
(*             pmatch_list ps ts) *)
(* Proof *)
(*   ho_match_mp_tac (theorem "pat_induction") \\ rw[] *)
(*   >- fs[pmatch_def] *)
(*   >- fs[all_wild_or_vars_def] *)
(*   >- fs[all_wild_or_vars_def, pmatch_def] *)
(*   >- fs[pmatch_list_def] *)
(*   >- (Cases_on `ts` *)
(*       >- (Cases_on `ps` \\ fs[]) *)
(*       >- (fs[all_wild_or_vars_def] \\ *)
(*           imp_res_tac all_wild_vars_dcmp \\ *)
(*           fs[pmatch_list_def])) *)
(* QED; *)

(* Theorem all_wild_vars_pmatch_list: *)
(*   !ps ts. (LENGTH ps) = (LENGTH ts) /\ *)
(*          all_wild_or_vars ps ==> *)
(*          pmatch_list ps ts *)
(* Proof *)
(*   Cases_on `ps` \\ Cases_on `ts` \\ rw[] *)
(*   >- fs[pmatch_list_def] *)
(*   >- (rw[pmatch_list_def] \\ *)
(*       imp_res_tac all_wild_vars_dcmp \\ *)
(*       imp_res_tac all_wild_vars_pmatch_list_aux \\ *)
(*       first_assum (qspec_then `h'` mp_tac) \\ fs[]) *)
(* QED; *)

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
  (add_cons c n a [] = [(c,n,a)]) /\
  (add_cons c n a ((c', n', a')::cinfos) =
    if c = c' /\ a = a'
    then ((c', n', a')::cinfos)
    else ((c', n', a')::(add_cons c n a cinfos)))
End

Theorem add_cons_not_empty:
  !c n a l. (add_cons c n a l) <> []
Proof
  Cases_on `l` \\ rw[]
  >- fs[add_cons_def]
  >- (Cases_on `h` \\ Cases_on `r` \\
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
  (cinfos ((Branch ((Cons c n sub_ps)::ps) e)::rs) =
    add_cons c n (LENGTH sub_ps) (cinfos rs)) /\
  (cinfos ((Branch ((Or p1 p2)::ps) e)::rs) =
    merge_cinfos (merge_cinfos (cinfos [(Branch [p1] e)])
                               (cinfos [(Branch [p2] e)]))
                 (cinfos rs))
End

(* Is a constructor in some column informations ? *)
Definition in_cinfos_def:
  (in_cinfos (_,_) [] = F) /\
  (in_cinfos (c,a) ((c',_,a')::cinfos) =
    if c = c' /\ a = a'
    then T
    else in_cinfos (c,a) cinfos)
End


(* Tell if the patterns contain all the constructors of a signature
   from a column_infos *)
Definition is_col_complete_def:
  (is_col_complete [] = F) /\
  (is_col_complete ((_,NONE,_)::_) = F) /\
  (is_col_complete ((_,SOME n,_)::cons) =
    (((LENGTH cons) + 1:num) = n))
End

(* Counting the number of constructors to prove termination *)
Definition nb_cons_pat_def:
  (nb_cons_pat Any = (1:num)) /\
  (nb_cons_pat (Cons _ _ []) = 2) /\
  (nb_cons_pat (Cons c a (p::ps)) =
    (nb_cons_pat p) * (nb_cons_pat (Cons c a ps))) /\
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
  (is_cons_fcol_pat (Cons _ _ _) = T) /\
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
  !c a p. 0 < nb_cons_pat (Cons c a p)
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
          `0 < nb_cons_pat (Cons pcons' v0 pargs)` by fs[nb_cons_cons_gt_zero] \\
          `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
          fs[LESS_MULT2])
      >- (fs[nb_cons_def, nb_cons_branch_def, nb_cons_pat_def, default_def] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[] \\
          imp_res_tac nb_cons_default_aux \\
          rfs[] \\
          Cases_on `nb_cons (default (h::t)) = nb_cons (h::t)`
          >- (fs[] \\
              `0 < nb_cons_pat (Cons pcons' v0 pargs)` by fs[nb_cons_cons_gt_zero] \\
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
  !c a p. nb_cons_branch p < nb_cons_pat (Cons c a p)
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
          `nb_cons_branch pargs < nb_cons_pat (Cons pcons' v0 pargs)` by fs[nb_cons_cons_pargs] \\
          fs[])
      >- (imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          fs[] \\
          `nb_cons_branch pargs * nb_cons_branch ps <=
           nb_cons_branch ps * nb_cons_pat (Cons pcons' v0 pargs)`
          suffices_by fs[LESS_EQ_LESS_EQ_MONO] \\
          `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
          rewrite_tac [Once MULT_COMM] \\
          fs[LT_MULT_LCANCEL] \\
          `nb_cons_branch pargs < nb_cons_pat (Cons pcons' v0 pargs)` by fs[nb_cons_cons_pargs] \\
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
                   nb_cons_branch ps * nb_cons_pat (Cons pcons' v0 pargs)`
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
    GENLIST (λx. (n, snoc_pos x p)) a)
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
  (simple_heuristic ((Branch (p::ps) e)::bs) =
    if is_cons_fcol_pat p then (0:num)
    else 1 + (simple_heuristic (((Branch ps e)::bs))))
End

Definition inv_heuristic_def:
  inv_heuristic h =
    (!ps e bs. 0 < LENGTH ps /\
               ~(all_wild_or_vars ps) ==>
               (h ((Branch ps e)::bs) < LENGTH ps) /\
               (is_cons_fcol (swap_columns (h ((Branch ps e)::bs)) ((Branch ps e)::bs))))
End

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
    if all_wild_or_vars ps
    then Leaf e
    else
      (* we select a column using heuristic h *)
      let sel_col = (h ((Branch ps e)::bs)) in
      if useh
      then (if (sel_col > 0 /\ (sel_col < (msize ((Branch ps e)::bs))))
            then Swap sel_col (compile h (swap_items sel_col pos) (swap_columns sel_col ((Branch ps e)::bs)) F)
            else (let sel_col = simple_heuristic ((Branch ps e)::bs) in
                  compile h (swap_items sel_col pos) (swap_columns sel_col ((Branch ps e)::bs)) F))
      else (let cinfos = cinfos ((Branch ps e)::bs) in
                  if (is_col_complete cinfos)
                  then make_complete h pos ((Branch ps e)::bs) cinfos
                  else make_partial h pos ((Branch ps e)::bs) cinfos)) /\
  (* add a list of already treated constructors *)
  (make_complete h pos m ((c,_,a)::[]) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
       (compile h (pos_spec a pos) (spec c a m) T)
    else DTypeFail) /\
  (make_complete h pos m ((c,_,a)::cons) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If (HD pos) c a (compile h (pos_spec a pos) (spec c a m) T)
                    (make_complete h pos m cons)
    else DTypeFail) /\
  (make_partial h pos m [] =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
      (compile h (pos_default pos) (default m) T)
    else DTypeFail) /\
  (make_partial h pos m ((c,_,a)::cons) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If (HD pos) c a (compile h (pos_spec a pos) (spec c a m) T)
                    (make_partial h pos m cons)
    else DTypeFail)
Termination
(WF_REL_TAC `(inv_image ($< LEX ($< LEX $<))
            (\x. case x of INL(_,_,m,b) => (nb_cons m, (1:num), if b then (1:num) else 0)
                         | INR y => (case y of INL(_,_,m,i) =>
                                      (nb_cons m, (0:num), LENGTH i)
                                     | INR(_,_,m,i) =>
                                      (nb_cons m, (0:num), LENGTH i))))` \\
rw[]
>- (DISJ2_TAC \\
    imp_res_tac nb_cons_swap \\
    first_x_assum (qspec_then `simple_heuristic (Branch (v14::v15) e::bs)` assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v14::v15`, `e`, `bs`] assume_tac) \\
    fs[])
>- (DISJ2_TAC \\
    imp_res_tac nb_cons_swap \\
    first_x_assum (qspec_then `simple_heuristic (Branch (v14::v15) e::bs)` assume_tac) \\
    fs[msize_def] \\
    assume_tac inv_simple_heuristic \\
    fs[inv_heuristic_def] \\
    first_x_assum (qspecl_then [`v14::v15`, `e`, `bs`] assume_tac) \\
    fs[])
>- (DISJ2_TAC \\ fs[nb_cons_swap])
>- imp_res_tac nb_cons_default) \\
metis_tac [nb_cons_spec]
End

Definition initial_pos_def:
  (initial_pos (width:num) =
    GENLIST (λx. (x, EmptyPos)) width)
End

Definition initial_pos_def:
  (initial_pos 0 = [(0, EmptyPos)]) /\
  (initial_pos (SUC n) =
    SNOC ((SUC n), EmptyPos) (initial_pos n))
End

(* Theorem apply_initial_pos: *)
(*   !v. apply_positions (initial_pos (LENGTH v)) v = v *)
(* Proof *)
(*  Induct_on `v` *)
(*  >- fs[apply_positions_def] *)
(* (*   >- (rw[initial_pos_def, GENLIST_CONS] \\ *) *)
(* (*       fs[apply_positions_def, app_list_pos_def, app_pos_def, MAP_GENLIST, *) *)
(* (* 	 initial_pos_def] *) *)
(*  >- (Cases_on `v` *)
(*      >- (fs[initial_pos_def, apply_positions_def, app_list_pos_def, app_pos_def] \\ cheat) *)
(*      >- (rw[] \\ fs[] \\ *)
(*          fs[initial_pos_def, apply_positions_def, app_list_pos_def, app_pos_def] \\ cheat)) *)
(* QED *)

Definition pmatch_list_pos_def:
  (pmatch_list_pos [] v [] = PMatchSuccess) /\
  (pmatch_list_pos ps v [] = PTypeFailure) /\
  (pmatch_list_pos [] v ts = PTypeFailure) /\
  (pmatch_list_pos (p::ps) v (t::ts) =
     case app_list_pos v t of
       NONE => PTypeFailure
     | SOME sub_v => (case pmatch p sub_v of
                         PTypeFailure => PTypeFailure
                       | PMatchFailure => PMatchFailure
                       | PMatchSuccess => pmatch_list_pos ps v ts))
End

Definition match_pos_def:
  (match_pos [] v ts = SOME MatchFailure) /\
  (match_pos ((Branch ps e)::bs) v ts =
    case pmatch_list_pos ps v ts of
       PMatchSuccess => SOME (MatchSuccess e)
     | PMatchFailure => match_pos bs v ts
     | PTypeFailure => NONE)
End

Theorem match_pos_match:
  !v m. (msize m) = (LENGTH v) ==>
        match_pos m v (initial_pos (LENGTH v)) =
        match     m v
Proof
  cheat
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

(* Theorem swap_pmatch_list_pos: *)
(*   !ps ts pos i. (LENGTH ts) = (LENGTH pos) /\ *)
(*                 (LENGTH ts) = (LENGTH ps) /\ *)
(*                 i < (LENGTH ts) ==> *)
(*                 pmatch_list (swap_items i ps) *)
(*                             (apply_positions (swap_items i pos) ts) = *)
(*                 pmatch_list ps (apply_positions pos ts) *)
(* Proof *)
(*   rw[swap_positions, apply_positions_length, swap_pmatch_list] *)
(* QED *)

(* Theorem swap_match: *)
(*   !m ts i pos. (LENGTH pos) = (msize m) /\ *)
(*                inv_mat m /\ *)
(*                i < (LENGTH ts) ==> *)
(*                match (swap_columns i m) *)
(*                      (apply_positions (swap_items i pos) (swap_items i ts)) = *)
(*                match m (apply_positions pos ts) *)
(* Proof *)
(*   ho_match_mp_tac (theorem "match_ind") \\ rw[] *)
(*   >- (Cases_on `pos` *)
(*       >- (fs[swap_columns_def, swap_items_def, msize_def] \\ *)
(*           every_case_tac \\ *)
(*           fs[match_def]) *)
(*       >- fs[msize_def]) *)
(*   >- (fs[swap_columns_def, match_def] \\ *)
(*       fs[swap_items_def, msize_def, swap_pmatch_list] \\ *)
(*       Cases_on `pmatch_list ps (apply_positions pos ts)` \\ fs[] \\ *)
(*       imp_res_tac msize_inv' \\ *)
(*       Cases_on `m` *)
(*       >- fs[swap_columns_def, match_def] *)
(*       >- (fs[msize_def] \\ *)
(*           imp_res_tac inv_mat_dcmp \\ *)
(*           rfs[])) *)
(* QED; *)

(* Theorem swap_match_aux: *)
(*   !m ts i pos. (LENGTH pos) = (msize m) /\ *)
(*                inv_mat m /\ *)
(*                i < (LENGTH pos) ==> *)
(*                match (swap_columns i m) *)
(*                      (swap_items i (apply_positions pos ts)) = *)
(*                match m (apply_positions pos ts) *)
(* Proof *)
(*   ho_match_mp_tac (theorem "match_ind") \\ rw[] *)
(*   >- (Cases_on `i` \\ rfs[msize_def]) *)
(*   >- fs[swap_columns_def, match_def, swap_items_def] *)
(* QED *)

(* Theorem swap_match: *)
(*   !m ts i pos. (LENGTH pos) = (msize m) /\ *)
(*                inv_mat m /\ *)
(*                i < (LENGTH pos) ==> *)
(*                match (swap_columns i m) *)
(*                      (apply_positions (swap_items i pos) ts) = *)
(*                match m (apply_positions pos ts) *)
(* Proof *)
(*   rw[swap_positions, swap_match_aux] *)
(* QED *)

Theorem compile_correct:
  (!h pos m useh v.
    msize m = LENGTH v /\
    IS_SOME (match_pos m v pos) /\
	inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (compile h pos m useh))) /\
  (!h pos m cinfos v.
    msize m = LENGTH pos /\
    m <> [] /\
    0 < (msize m) /\
    IS_SOME (match_pos m v pos) /\
    inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (make_complete h pos m cinfos))) /\
  (!h pos m cinfos v.
    msize m = LENGTH pos /\
    m <> [] /\
    0 < (msize m) /\
    IS_SOME (match_pos m v pos) /\
    inv_mat m ==>
    (match_pos m v pos =
     dt_eval v (make_partial h pos m cinfos)))
Proof
  cheat
  (* ho_match_mp_tac (theorem "compile_ind") \\ rw[] *)
  (* >- fs[match_def] *)
  (* >- (fs[match_def] \\ *)
  (*     Cases_on `v` \\ *)
  (*     Cases_on `pos` \\ *)
  (*     fs[apply_positions_def, pmatch_list_def, msize_def, compile_def, *)
  (*        dt_eval_def]) *)
  (* >- (fs[compile_def] \\ *)
  (*     Cases_on `all_wild_or_vars (v14::v15)` \\ fs[] *)
  (*     >- (imp_res_tac match_eq_length \\ *)
  (*         fs[match_def, msize_def] \\ *)
  (*         imp_res_tac all_wild_vars_pmatch_list \\ *)
  (*         fs[] \\ res_tac \\ fs[dt_eval_def]) *)
  (*     >- (imp_res_tac match_eq_length \\ *)
  (*         fs[match_def, msize_def] \\ *)
  (*         Cases_on `h (Branch (v14::v15) e::bs) = 0` \\ fs[] *)
  (* 	  >- (fs[inv_heuristic_def] \\ *)
  (*             `is_cons_fcol (Branch (v14::v15) e::bs)` by *)
  (*             (first_x_assum (qspec_then `(Branch (v14::v15) e::bs)` assume_tac) \\ *)
  (*              rfs[swap_columns_zero]) \\ *)
  (*             fs[] \\ *)
  (*             Cases_on `is_col_complete (cinfos (Branch (v14::v15) e::bs))` \\ *)
  (*             fs[]) *)
  (*        >- (fs[inv_heuristic_def] \\ *)
  (*            first_x_assum (qspec_then `(Branch (v14::v15) e::bs)` assume_tac) \\ *)
  (* 	     fs[msize_def] \\ *)
  (*            Cases_on `useh` \\ fs[dt_eval_def] *)
  (* 	     >- (imp_res_tac swap_columns_msize \\ *)
  (*                fs[msize_def] \\ res_tac \\ fs[] \\ *)
  (* 		 imp_res_tac swap_columns_inv_mat \\ *)
  (*                fs[msize_def] \\ res_tac \\ fs[] \\ *)
  (*                fs[swap_items_length] \\ *)
  (*                first_x_assum (qspecl_then [`v`,`k`] assume_tac) \\ *)
  (*                Cases_on `swap_columns (h (Branch (v14::v15) e::bs)) *)
  (*                                       (Branch (v14::v15) e::bs)` *)
  (*                >- fs[is_cons_fcol_def] *)
  (* 		 >- (`match (h'::t) *)
  (*                     (apply_positions (swap_items (h (Branch (v14::v15) e::bs)) pos) *)
  (*                     v) = SOME k` *)
  (*                    suffices_by fs[] \\ *)
  (*                    fs[match_def] *)
  (*     >- (imp_res_tac match_eq_length \\ *)
  (*         fs[match_def, msize_def] \\ *)
  (*         Cases_on `h (Branch (v14::v15) e::bs) = 0` \\ fs[] *)
  (* 	  >- (fs[inv_heuristic_def] \\ *)
  (*             `is_cons_fcol (Branch (v14::v15) e::bs)` by *)
  (*             (first_x_assum (qspec_then `(Branch (v14::v15) e::bs)` assume_tac) \\ *)
  (*              rfs[swap_columns_zero]) \\ *)
  (*             Cases_on `pos` \\ fs[] \\ *)
  (*             fs[type_coherent_def] \\ *)
  (*             Cases_on `is_col_complete (cinfos (Branch (v14::v15) e::bs))` \\ *)
  (*             fs[] \\ rfs[] \\ *)
  (*             first_x_assum (qspecl_then [`(h'::t)`, `k`] assume_tac) \\ *)
  (*             fs[is_cons_fcol_cinfos_not_empty]) *)
  (* 	  >- (rfs[] \\ *)
  (*             fs[inv_heuristic_def] \\ *)
  (*             first_x_assum (qspec_then `(Branch (v14::v15) e::bs)` assume_tac) \\ *)
  (*             fs[msize_def, dt_eval_def] \\ *)
  (*             Cases_on `useh` \\ fs[] *)
  (* 	      >- (imp_res_tac swap_columns_msize \\ *)
  (*                 fs[msize_def] \\ res_tac \\ *)
  (*                 fs[] \\ *)
  (*                 imp_res_tac swap_columns_inv_mat \\ *)
  (*                 fs[msize_def] \\ res_tac \\ *)
  (*                 fs[msize_def] \\ rfs[] \\ fs[dt_eval_def] \\ *)
  (*                 first_x_assum (qspecl_then [`swap_items (h (Branch (v14::v15) e::bs)) (h'::t)`, *)
  (*                                             `k`] assume_tac) \\ *)
  (*                 `h (Branch (v14::v15) e::bs) < LENGTH (h'::t)` by fs[] \\ *)
  (*                 imp_res_tac swap_items_length \\ *)
  (*                 fs[match_def] \\ *)
  (*                 Cases_on `swap_columns (h (Branch (v14::v15) e::bs)) *)
  (*                             (Branch (v14::v15) e::bs)` *)
  (*                 >- fs[is_cons_fcol_def] *)
  (* 		  >- (`CARD (set (MAP FST (swap_items (h (Branch (v14::v15) e::bs)) pos))) = SUC (LENGTH t) /\ *)
  (*                      match (h''::t') (swap_items (h (Branch (v14::v15) e::bs)) (h'::t)) = SOME k` *)
  (*                     suffices_by fs[] \\ *)
  (*                     rw[] *)
  (*                     >- rfs[GSYM swap_map, swap_set] *)
  (*                     >- (`LENGTH (h'::t) = msize (Branch (v14::v15) e::bs)` by fs[msize_def] \\ *)
  (*                         imp_res_tac swap_match \\ *)
  (*                         rpt (first_x_assum (qspec_then `h (Branch (v14::v15) e::bs)` assume_tac)) \\ *)
  (*                         `h (Branch (v14::v15) e::bs) < LENGTH (h'::t)` by fs[] \\ *)
  (*                         fs[match_def] \\ *)
  (*                         metis_tac[]))) *)
  (* 	      >- (Cases_on `is_col_complete (cinfos (Branch (v14::v15) e::bs))` \\ *)
  (*                 fs[] \\ rfs[] \\ *)
  (*                 first_x_assum (qspecl_then [`(h'::t)`, `k`] assume_tac) \\ *)
  (*                 fs[is_cons_fcol_cinfos_not_empty])))) *)
  (* >- (fs[compile_def] \\ *)
  (* >- (fs[compile_def, dt_eval_def] \\ *)
  (*     (* Cases analysis on head of c *) *)
  (*     cheat) *)
  (* (* same for make partial *) *)
  (* >- cheat *)
  (* >- cheat *)
  (* >- (fs[compile_def, dt_eval_def] \\ *)
  (*     (* Somehow show that this case is not possible, case *)
  (*       analysis on on the first column of h ? *) *)
  (*     cheat) *)
QED;

Theorem compile_correct_toplevel:
  !h m v.
    LENGTH v = msize m /\
    inv_mat m /\
    IS_SOME (match m v) ==>
      match m v =
      dt_eval v (compile h (initial_pos (msize m)) m T)
Proof
  rw[] \\
  imp_res_tac (GSYM match_pos_match) \\
  fs[] \\
  imp_res_tac compile_correct \\
  metis_tac[]
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
  dt_eval [Term 0 []; Term 0 []]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 (SOME 2) []        ; Cons 0 (SOME 2) []]        1;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 0 (SOME 2) []]        2;
          Branch [Cons 0 (SOME 2) []        ; Cons 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 1)
Proof
  EVAL_TAC
QED

Theorem test2:
  dt_eval [Term 1 [Term 3 []; Term 0 []]; Term 0 []]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 (SOME 2) []        ; Cons 0 (SOME 2) []]        1;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 0 (SOME 2) []]        2;
          Branch [Cons 0 (SOME 2) []        ; Cons 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 2)
Proof
  EVAL_TAC
QED

Theorem test3:
  dt_eval [Term 0 []; Term 1 [Term 3 []; Term 0 []]]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 (SOME 2) []        ; Cons 0 (SOME 2) []]        1;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 0 (SOME 2) []]        2;
          Branch [Cons 0 (SOME 2) []        ; Cons 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 3)
Proof
  EVAL_TAC
QED

Theorem test4:
  dt_eval [Term 1 [Term 3 []; Term 0 []]; Term 1 [Term 4 []; Term 0 []]]
    (compile simple_heuristic (initial_pos 2)
         [Branch [Cons 0 (SOME 2) []        ; Cons 0 (SOME 2) []]        1;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 0 (SOME 2) []]        2;
          Branch [Cons 0 (SOME 2) []        ; Cons 1 (SOME 2) [Any;Any]] 3;
          Branch [Cons 1 (SOME 2) [Any;Any] ; Cons 1 (SOME 2) [Any;Any]] 4] T) = SOME (MatchSuccess 4)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
