(*
  Pattern-matching compilation to decision trees
  See issue #667 for details and references
*)
open preamble;
open numTheory listTheory arithmeticTheory;

(*
Definition of terms
Every term is a constructor with 0 or more arguments
Constructors are identified by num
*)
Datatype `term = Term num (term list)`;

(*
Definition of full patterns with as clauses
Variables are identified by num
*)
Datatype `pat =
    Any
  | Var num
  (* A constructor pattern is an constructor id, the number of constructors
     in its type and a list of other patterns *)
  | Cons num num (pat list)
  | Or pat pat
  | As pat num (* (p:pat) as (x:num) *)
`;

(*
We parametrize the size function by an arity a to take into account the fact
that a Any or a Var can be expanded into a list of Any patterns
*)
Definition psize_def:
  (* (psize a Any = ((2:num) ** (a+2)) + 1) /\ *)
  (psize a Any = (2:num) ** (2 ** a)) /\
  (psize a (Var n) = (2 ** (2 ** a))) /\
  (psize a (Cons n t []) = 2 + a) /\
  (psize a (Cons n t (x::xs)) = 2 + a + ((psize a x) * psize a (Cons n t xs))) /\
  (psize a (Or p1 p2) = 2 + (psize a p1) + (psize a p2)) /\
  (psize a (As p n) = 2 + (psize a p))
End

(*
Represent a branch (p => e) in a match expression
the result expression is just a number for now
*)
Datatype `branch = Branch (pat list) num`;

Definition patterns_def:
  patterns (Branch ps e) = ps
End

Definition expr_def:
  expr (Branch ps e) = e
End

(* pattern matrix *)
val _ = type_abbrev("patmat", ``:branch list``)

(* Invariant of pattern matrices *)
Definition inv_mat_def:
  inv_mat m = ?n. EVERY (\l. (LENGTH (patterns l)) = n) m
End

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

Theorem inv_mat_as:
  !p n ps e rs.
    inv_mat ((Branch ((As p n)::ps) e)::rs) ==>
    inv_mat ((Branch (p::ps) e)::rs)
Proof
  rw[inv_mat_def] \\
  fs[patterns_def]
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

Theorem psize_gt_zero:
  !a p. 0 < (psize a p)
Proof
  ho_match_mp_tac (theorem "psize_ind") \\ rw[psize_def]
QED;

(* Theorem psize_gt_one: *)
(*   !a p. 1 < (psize a p) *)
(* Proof *)
(*   ho_match_mp_tac (theorem "psize_ind") \\ rw[psize_def] \\ *)
(*   Cases_on `a` \\ fs[] \\ *)
(*   `0 < SUC n` by fs[] \\ *)
(*   imp_res_tac X_LE_X_EXP \\ *)
(*   first_x_assum (qspec_then `2` assume_tac) \\ *)
(*   `0 < 2 ** SUC n` by fs[] \\ *)
(*   imp_res_tac X_LE_X_EXP \\ *)
(*   first_x_assum (qspec_then `2` assume_tac) \\ *)
(*   fs[OR_LESS] *)
(* QED; *)


Definition ars_pat_def:
  (ars_pat c a Any = T) /\
  (ars_pat c a (Var _) = T) /\
  (ars_pat c a (Cons c' _ ps) =
    if c = c'
    then (LENGTH ps) = a
    else T) /\
  (ars_pat c a (Or p1 p2) =
    ((ars_pat c a p1) /\ (ars_pat c a p2))) /\
  (ars_pat c a (As p n) =
    ars_pat c a p)
End

Definition ars_branch_def:
  (ars_branch c a [] = T) /\
  (ars_branch c a (p::ps) =
    ((ars_pat c a p) /\
     (ars_branch c a ps)))
End

Definition ars_inv_def:
  (ars_inv _ _ [] = T) /\
  (ars_inv c a ((Branch ps e)::bs) =
    ((ars_branch c a ps) /\
     (ars_inv c a bs)))
End

Theorem ars_inv_dcmp:
  !b bs c a. inv_mat (b::bs) /\
             ars_inv c a (b::bs) ==> ars_inv c a bs
Proof
  Cases_on `b` \\
  fs[ars_inv_def]
QED;

Theorem ars_inv_cons:
  !b bs c a. ars_inv c a (b::bs) ==>
             ars_inv c a [b]
Proof
  Cases_on `b` \\
  rw[ars_inv_def]
QED;

Theorem ars_inv_or1:
  !c a p1 p2 ps e m.
    ars_inv c a ((Branch (Or p1 p2::ps) e)::m) ==>
    ars_inv c a ((Branch (p1::ps) e)::m)
Proof
  fs[ars_inv_def, ars_branch_def, ars_pat_def]
QED;

Theorem ars_inv_or2:
  !c a p1 p2 ps e m.
    ars_inv c a ((Branch (Or p1 p2::ps) e)::m) ==>
    ars_inv c a ((Branch (p2::ps) e)::m)
Proof
  fs[ars_inv_def, ars_branch_def, ars_pat_def]
QED;

Theorem ars_inv_as:
  !c a p n ps e m.
    ars_inv c a ((Branch (As p n::ps) e)::m) ==>
    ars_inv c a ((Branch (p::ps) e)::m)
Proof
  rw[ars_inv_def, ars_branch_def, ars_pat_def]
QED;

(* Semantics of matching *)
val pmatch_def = tDefine "match_def" `
  (pmatch Any  t = T) /\
  (pmatch (Var n) t = T) /\
  (pmatch (Cons pcons _ pargs) (Term tcons targs) =
    ((pcons = tcons) /\
    (LIST_REL (\p t. pmatch p t) pargs targs))) /\
  (pmatch (Cons pcons _ []) (Term tcons []) = (pcons = tcons)) /\
  (pmatch (Cons pcons _ ps) (Term tcons []) = F) /\
  (pmatch (Cons pcons _ []) (Term tcons ts) = F) /\
  (pmatch (Cons pcons tinfo (p::ps)) (Term tcons (t::ts)) =
    ((pmatch p t) /\
     (pmatch (Cons pcons tinfo ps) (Term tcons ts)))) /\
  (pmatch (Or p1 p2) t = ((pmatch p1 t) \/ (pmatch p2 t))) /\
  (pmatch (As p num) t = pmatch p t)`
  (WF_REL_TAC `measure (\ (x,_). psize 1 x)` \\ rw[psize_def] \\
  Induct_on `pargs`
  >- fs[psize_def]
  >- (rpt strip_tac \\
      fs[MEM]
      >- (fs[psize_def] \\
          `0 < psize 1 (Cons pcons' v0 pargs) ` by fs[psize_gt_zero] \\
	  `(psize 1 h) <= ((psize 1 h) * (psize 1 (Cons pcons' v0 pargs)))` by
	  fs[LE_MULT_CANCEL_LBARE] \\
	  decide_tac)
      >- (res_tac \\
          fs[psize_def] \\
          `0 < psize 1 h ` by fs[psize_gt_zero] \\
          `psize 1 (Cons pcons' v0 pargs) <= (psize 1 h) * (psize 1 (Cons pcons' v0 pargs))` by
          fs[] \\
	  decide_tac)))

Definition pmatch_list_def:
  (pmatch_list [] [] = T) /\
  (pmatch_list ps [] = F) /\
  (pmatch_list [] ts = F) /\
  (pmatch_list (p::ps) (t::ts) =
   ((pmatch p t) /\ (pmatch_list ps ts)))
End

Theorem pmatch_list_rel:
  !ps ts. LIST_REL (\p t. pmatch p t) ps ts ==>
          pmatch_list ps ts
Proof
  ho_match_mp_tac LIST_REL_ind \\ rw[pmatch_list_def]
QED;

Theorem not_pmatch_list_rel:
  !ps ts. ~(LIST_REL (\p t. pmatch p t) ps ts) ==>
          ~(pmatch_list ps ts)
Proof
  Induct_on `ps`
  >- (Cases_on `ts` \\ rw[] \\
      fs[pmatch_list_def])
  >- (rw[pmatch_list_def] \\
      Cases_on `ts`
      >- fs[pmatch_list_def]
      >- fs[pmatch_list_def])
QED;

Theorem pmatch_list_app:
  !p1 t1 p2 t2.
    ((LENGTH t1 = LENGTH p1) /\
     (LENGTH t2 = LENGTH p2)) ==>
    (pmatch_list (t1 ++ t2) (p1 ++ p2) =
    ((pmatch_list t1 p1) /\ (pmatch_list t2 p2)))
Proof
  Induct_on `t1`
  >- (rw[] \\
      eq_tac \\
      rw[pmatch_list_def])
  >- (Cases_on `p1`
      >- fs[]
      >- (rw[pmatch_list_def] \\
          eq_tac \\ rw[]))
QED;

Theorem pmatch_list_length:
  !ps ts. pmatch_list ps ts ==>
          (LENGTH ps = LENGTH ts)
Proof
  ho_match_mp_tac (fetch "-" "pmatch_list_ind") \\
  rw[pmatch_list_def]
QED;

Theorem pmatch_list_or:
  !ps p1 p2 ts. pmatch_list ((Or p1 p2)::ps) ts ==>
                (pmatch_list (p1::ps) ts) \/
                (pmatch_list (p2::ps) ts)
Proof
  rpt strip_tac \\
  fs[pmatch_list_def] \\
  Cases_on `ts` \\ fs[pmatch_list_def] \\
  fs[pmatch_def]
QED;

Theorem not_pmatch_list_or:
  !ps p1 p2 ts. ~(pmatch_list ((Or p1 p2)::ps) ts) ==>
                ~(pmatch_list (p1::ps) ts) /\
                ~(pmatch_list (p2::ps) ts)
Proof
  rpt strip_tac \\
  fs[pmatch_list_def] \\
  Cases_on `ts` \\ fs[pmatch_list_def, pmatch_def]
QED;

Theorem pmatch_list_as:
  !ps p n ts. (pmatch_list ((As p n)::ps) ts) ==>
              (pmatch_list (p::ps) ts)
Proof
  rpt strip_tac \\
  Cases_on `ts` \\
  fs[pmatch_list_def, pmatch_def]
QED;

Theorem not_pmatch_list_as:
  !ps p n ts. ~(pmatch_list ((As p n)::ps) ts) ==>
              ~(pmatch_list (p::ps) ts)
Proof
  rpt strip_tac \\
  Cases_on `ts` \\
  fs[pmatch_list_def, pmatch_def]
QED;


Definition match_def:
  (match [] ts = NONE) /\
  (match ((Branch ps e)::bs) ts =
    (if pmatch_list ps ts
     then (SOME e)
     else match bs ts))
End

Theorem match_first_patlist:
  !ps ts e xs.
    pmatch_list ps ts ==> (match ((Branch ps e)::xs) ts = (SOME e))
Proof
  rpt strip_tac \\
  Cases_on `ps` \\
  rw[match_def]
QED;

Theorem nmatch_first_patlist:
  !ps ts e xs.
    ~(pmatch_list ps ts) ==> (match ((Branch ps e)::xs) ts = match xs ts)
Proof
  rpt strip_tac \\
  Cases_on `ps` \\
  rw[match_def]
QED;

Theorem match_app:
  !b1 ts b2 x.
    (match b1 ts = (SOME x)) ==>
    (match (b1 ++ b2) ts = (SOME x))
Proof
  ho_match_mp_tac (fetch "-" "match_ind") \\ rw[]
  >- fs[match_def]
  >- (rw[match_def]
     >- fs[match_def]
     >- (res_tac \\
         fs[match_def]))
QED;

Theorem match_app2:
  !b1 ts b2.
    (match b1 ts = NONE) ==>
    (match (b1 ++ b2) ts = match b2 ts)
Proof
  ho_match_mp_tac (fetch "-" "match_ind") \\ rw[] \\
  fs[match_def] \\
  Cases_on `pmatch_list ps ts` \\ fs[]
QED;

Definition n_any_def:
  (n_any 0 = []) /\
  (n_any (SUC n) = Any::(n_any n))
End

Theorem pmatch_list_nany:
  !t. pmatch_list (n_any (LENGTH t)) t
Proof
  Induct_on `t` \\
  rw[pmatch_list_def, n_any_def, pmatch_def]
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
  (spec c a ((Branch ((Var n)::ps) e)::rs) =
    (Branch ((n_any a)++ps) e)::(spec c a rs)) /\
  (spec c a ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
    if c = pcons
    then (Branch (pargs++ps) e)::(spec c a rs)
    else (spec c a rs)) /\
  (spec c a ((Branch ((Or p1 p2)::ps) e)::rs) =
    (spec c a [Branch (p1::ps) e]) ++
    (spec c a [Branch (p2::ps) e]) ++
    (spec c a rs)) /\
  (spec c a ((Branch ((As p n)::ps) e)::rs) =
    spec c a ((Branch (p::ps) e)::rs))
End

(* Key property of matrix decomposition (Lemma 1 of article) *)
Theorem spec_lem:
  !c a m ts targs.
    (inv_mat m /\
     ((LENGTH targs) = a) /\
     ((msize m) = (LENGTH ts) + 1)) ==>
    (match m ((Term c targs)::ts) =
     match (spec c (LENGTH targs) m) (targs++ts))
Proof
  ho_match_mp_tac (fetch "-" "spec_ind") \\ rw[]
  >- fs[msize_def]
  >- (rw[match_def, spec_def]
      >- (`pmatch_list (n_any (LENGTH targs) ++ ps) (targs ++ ts)`
          suffices_by metis_tac[match_first_patlist] \\
          `LENGTH ps = LENGTH ts` by fs[msize_def] \\
          `pmatch_list ps ts` by fs[pmatch_list_def, pmatch_def] \\
           metis_tac[n_any_length, pmatch_list_app, pmatch_list_nany])
      >- (`~(pmatch_list ps ts)` by fs[pmatch_list_def, pmatch_def] \\
          imp_res_tac pmatch_list_length \\
          fs[LENGTH_APPEND, n_any_length] \\
          `LENGTH ps = LENGTH ts` by fs[] \\
          metis_tac[pmatch_list_app, pmatch_list_nany, n_any_length])
      >- (Cases_on `m`
          >- rw[match_def, spec_def]
        >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
               fs[])))
  >- (rw[match_def, spec_def]
      >- (`pmatch_list (n_any (LENGTH targs) ++ ps) (targs ++ ts)`
          suffices_by metis_tac[match_first_patlist] \\
          `LENGTH ps = LENGTH ts` by fs[msize_def] \\
          `pmatch_list ps ts` by fs[pmatch_list_def, pmatch_def] \\
        metis_tac[n_any_length, pmatch_list_app, pmatch_list_nany])
      >- (`~(pmatch_list ps ts)` by fs[pmatch_list_def, pmatch_def] \\
          imp_res_tac pmatch_list_length \\
          fs[LENGTH_APPEND, n_any_length] \\
          `LENGTH ps = LENGTH ts` by fs[] \\
          metis_tac[pmatch_list_app, pmatch_list_nany, n_any_length])
      >- (Cases_on `m`
          >- rw[match_def, spec_def]
          >- (`msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
               fs[])))
  >- (rw[match_def, spec_def] \\
      fs[pmatch_list_def, pmatch_def]
      >- (imp_res_tac pmatch_list_rel \\
          imp_res_tac pmatch_list_length \\
          metis_tac[pmatch_list_app])
      >- (Cases_on `pmatch_list (pargs ++ ps) (targs ++ ts)`
          >- (imp_res_tac not_pmatch_list_rel \\
              imp_res_tac pmatch_list_length \\
              `LENGTH ps = LENGTH ts` by fs[msize_def] \\
              fs[LENGTH_APPEND] \\
              metis_tac[pmatch_list_app])
          >- (fs[] \\
              Cases_on `m`
              >- rw[match_def, spec_def]
              >- (`msize (h::t) = LENGTH ts + 1` by
                  (imp_res_tac msize_inv \\ fs[]) \\
                  `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
                  first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
                  fs[])))
       >- (Cases_on `pmatch_list (pargs ++ ps) (targs ++ ts)`
           >- (imp_res_tac pmatch_list_length \\
               `LENGTH ps = LENGTH ts` by fs[msize_def] \\
               fs[LENGTH_APPEND] \\
               metis_tac[pmatch_list_app])
           >- (fs[] \\
               Cases_on `m`
               >- rw[match_def, spec_def]
               >- (`msize (h::t) = LENGTH ts + 1` by
                   (imp_res_tac msize_inv \\ fs[]) \\
                   `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
                   first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
                   fs[])))
       >- (Cases_on `m`
           >- rw[match_def, spec_def]
           >- (`msize (h::t) = LENGTH ts + 1` by
               (imp_res_tac msize_inv \\ fs[]) \\
               `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
               first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
               fs[])))
  >- (rw[match_def, spec_def]
    >- (imp_res_tac pmatch_list_or
      >- (`match [Branch (p1::ps) e] (Term c targs::ts) = SOME e`
          by rw[match_def] \\
          `LENGTH ps = LENGTH ts` by fs[msize_def] \\
          fs[msize_def] \\
          `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
          rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\
          fs[] \\ res_tac \\ fs[] \\
          metis_tac[match_app])
      >- (Cases_on `pmatch_list (p1::ps) (Term c targs::ts)`
          >- (`match [Branch (p1::ps) e] (Term c targs::ts) = SOME e`
              by rw[match_def] \\
              `LENGTH ps = LENGTH ts` by fs[msize_def] \\
              fs[msize_def] \\
              `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
              rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\
              fs[] \\ res_tac \\ fs[] \\
              metis_tac[match_app])
          >- (`match [Branch (p1::ps) e] (Term c targs::ts) = NONE`
              by (imp_res_tac nmatch_first_patlist \\
                 first_x_assum (qspecl_then [`[]`, `e`] assume_tac) \\
                 fs[match_def]) \\
              `LENGTH ps = LENGTH ts` by fs[msize_def] \\
              fs[msize_def] \\
              `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
              `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\
              rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac))\\
              fs[] \\ res_tac \\ fs[] \\
              imp_res_tac match_app2 \\
              first_x_assum (qspec_then
              `spec c (LENGTH targs) [Branch (p2::ps) e] ++
               spec c (LENGTH targs) m` assume_tac) \\
              fs[] \\
              `match [Branch (p2::ps) e] (Term c targs::ts) = SOME e`
              by (imp_res_tac match_first_patlist \\
                  rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
                  fs[]) \\
              rfs[] \\
              metis_tac[match_app])))
    >- (imp_res_tac not_pmatch_list_or \\
        `match [Branch (p1::ps) e] (Term c targs::ts) = NONE`
        by (imp_res_tac nmatch_first_patlist \\
            rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
            fs[match_def]) \\
        `match [Branch (p2::ps) e] (Term c targs::ts) = NONE`
        by (imp_res_tac nmatch_first_patlist \\
            rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
            fs[match_def]) \\
        `LENGTH ps = LENGTH ts` by fs[msize_def] \\
        `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
        `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\
        `match m (Term c targs::ts) =
         match (spec c (LENGTH targs) m) (targs ++ ts)`
        suffices_by
        (fs[msize_def] \\
        rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\
        fs[] \\ res_tac \\ fs[] \\
        imp_res_tac match_app2 \\
        first_assum (qspec_then
        `spec c (LENGTH targs) [Branch (p2::ps) e] ++
         spec c (LENGTH targs) m` assume_tac) \\
        fs[]) \\
        Cases_on `m`
        >- rw[match_def, spec_def]
        >- (`inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
            `msize (h::t) = LENGTH ts + 1` by
            (imp_res_tac msize_inv \\ fs[]) \\
            rpt (first_x_assum (qspecl_then [`ts`, `targs`] assume_tac)) \\
            fs[])))
  >- (rw[match_def, spec_def] \\
      `inv_mat (Branch (p::ps) e::rs)` by fs[inv_mat_def, patterns_def] \\
      `msize (Branch (p::ps) e::rs) = LENGTH ts + 1` by fs[msize_def] \\
      first_x_assum (qspecl_then [`ts`, `targs`] assume_tac) \\
      rfs[] \\
      fs[match_def, spec_def, pmatch_list_def, pmatch_def] \\
      rfs[])
  >- fs[msize_def]
QED;

(* Default matrix transformation *)
Definition default_def:
  (default [] = []) /\
  (default ((Branch (Any::ps) e)::rs) =
    (Branch ps e)::(default rs)) /\
  (default ((Branch ((Var n)::ps) e)::rs) =
    (Branch ps e)::(default rs)) /\
  (default ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
    (default rs)) /\
  (default ((Branch ((Or p1 p2)::ps) e)::rs) =
    (default [Branch (p1::ps) e]) ++
    (default [Branch (p2::ps) e]) ++
    (default rs)) /\
  (default ((Branch ((As p n)::ps) e)::rs) =
    default ((Branch (p::ps) e)::rs))
End

(* Key property of default matrix (Lemma 2 of article) *)
Definition is_cons_head_def:
  (is_cons_head c [] = F) /\
  (is_cons_head c ((Branch [] e)::rs) =
    (is_cons_head c rs)) /\
  (is_cons_head c ((Branch (Any::ps) e)::rs) =
    (is_cons_head c rs)) /\
  (is_cons_head c ((Branch ((Var n)::ps) e)::rs) =
    (is_cons_head c rs)) /\
  (is_cons_head c ((Branch ((Cons pcons _ pargs)::ps) e)::rs) =
    (if c = pcons
    then T
    else (is_cons_head c rs))) /\
  (is_cons_head c ((Branch ((Or p1 p2)::ps) e)::rs) =
    ((is_cons_head c [Branch (p1::ps) e]) \/
     (is_cons_head c [Branch (p2::ps) e]) \/
     (is_cons_head c rs))) /\
  (is_cons_head c ((Branch ((As p n)::ps) e)::rs) =
    ((is_cons_head c [Branch (p::ps) e]) \/
    (is_cons_head c rs)))
End

Theorem spec_msize:
  !c a m. ars_inv c a m /\
          (inv_mat m) /\
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
      fs[spec_def, msize_def, n_any_length])
  >- (Cases_on `m` \\
      Cases_on `c = pcons'`
      >- fs[spec_def, msize_def, n_any_length, ars_inv_def,
	    ars_branch_def, ars_pat_def]
      >- fs[spec_def]
      >- fs[spec_def, msize_def, n_any_length, ars_inv_def,
	    ars_branch_def, ars_pat_def]
      >- (fs[spec_def, msize_def, ars_inv_def, inv_mat_dcmp, inv_mat_def] \\
          Cases_on `h` \\
          fs[patterns_def, msize_def]))
  >- (Cases_on `m`
      >- (fs[spec_def, msize_def, msize_app]
          >- (imp_res_tac ars_inv_or1 \\
              imp_res_tac inv_mat_or1 \\
              fs[])
	  >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (fs[msize_app2] \\
                  imp_res_tac ars_inv_or2 \\
                  imp_res_tac inv_mat_or2 \\
                  fs[])
	      >- (fs[msize_app] \\
                  imp_res_tac ars_inv_or1 \\
                  imp_res_tac inv_mat_or1 \\
                  fs[])))
      >- (fs[spec_def, msize_def, msize_app]
	  >- (imp_res_tac ars_inv_or1 \\
              imp_res_tac inv_mat_or1 \\
              imp_res_tac inv_mat_cons \\
              imp_res_tac ars_inv_cons \\
              fs[])
          >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (fs[msize_app2] \\
                  imp_res_tac ars_inv_or2 \\
                  imp_res_tac inv_mat_or2 \\
                  imp_res_tac inv_mat_cons \\
                  imp_res_tac ars_inv_cons \\
                  fs[])
              >- (fs[msize_app] \\
                  imp_res_tac ars_inv_or1 \\
                  imp_res_tac inv_mat_or1 \\
                  imp_res_tac inv_mat_cons \\
                  imp_res_tac ars_inv_cons \\
                  fs[]))
          >- (Cases_on `spec c a [Branch (p1::ps) e] = []`
              >- (Cases_on `spec c a [Branch (p2::ps) e] = []`
                  >- (fs[msize_app2] \\
                      imp_res_tac ars_inv_dcmp \\
                      imp_res_tac inv_mat_dcmp \\
                      fs[inv_mat_def, EVERY_DEF, patterns_def] \\
                      Cases_on `h` \\
                      fs[msize_def, patterns_def])
                  >- (fs[msize_app2, msize_app] \\
                      imp_res_tac ars_inv_or2 \\
                      imp_res_tac inv_mat_or2 \\
                      imp_res_tac inv_mat_cons \\
                      imp_res_tac ars_inv_cons \\
                      fs[]))
              >- (fs[msize_app] \\
                  imp_res_tac ars_inv_or1 \\
                  imp_res_tac inv_mat_or1 \\
                  imp_res_tac ars_inv_cons \\
                  imp_res_tac inv_mat_cons \\
                  fs[]))))
  >- (fs[spec_def] \\
      imp_res_tac inv_mat_as \\
      imp_res_tac ars_inv_as \\
      fs[msize_def])
  >- fs[msize_def]
QED;

Theorem is_cons_head_app:
  !c m1 m2. (~(is_cons_head c m1) /\
             ~(is_cons_head c m2)) ==>
            ~(is_cons_head c (m1 ++ m2))
Proof
  ho_match_mp_tac is_cons_head_ind \\ rw[] \\
  fs[is_cons_head_def]
QED;

Theorem default_lem:
  !m c ts targs.
   (inv_mat m /\
   ~(is_cons_head c m) /\
    ((msize m) = (LENGTH ts) + 1)) ==>
   (match m ((Term c targs)::ts) =
    match (default m) ts)
Proof
  ho_match_mp_tac (fetch "-" "default_ind") \\ rw[]
  >- fs[msize_def]
  >- (rw[match_def, default_def]
      >- fs[pmatch_list_def, pmatch_def]
      >- fs[pmatch_list_def, pmatch_def]
      >- (fs[is_cons_head_def] \\
          Cases_on `m`
          >- rw[match_def, default_def]
          >- (`(msize (h::t)) = LENGTH ts + 1`
              by (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`c`,`ts`,`targs`] assume_tac) \\
              res_tac)))
  >- (rw[match_def, default_def]
      >- fs[pmatch_list_def, pmatch_def]
      >- fs[pmatch_list_def, pmatch_def]
      >- (fs[is_cons_head_def] \\
          Cases_on `m`
          >- rw[match_def, default_def]
          >- (`(msize (h::t)) = LENGTH ts + 1`
              by (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`c`,`ts`,`targs`] assume_tac) \\
              res_tac)))
  >- (rw[match_def, default_def]
      >- fs[pmatch_list_def, pmatch_def, is_cons_head_def]
      >- (fs[is_cons_head_def] \\
          Cases_on `m`
          >- rw[match_def, default_def]
          >- (`(msize (h::t)) = LENGTH ts + 1`
              by (imp_res_tac msize_inv \\ fs[]) \\
              `inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              first_x_assum (qspecl_then [`c`,`ts`,`targs`] assume_tac) \\
              res_tac)))
  >- (rw[match_def, default_def]
      >- (fs[is_cons_head_def] \\
          imp_res_tac pmatch_list_or
          >- (`match [Branch (p1::ps) e] (Term c targs::ts) = SOME e`
              by rw[match_def] \\
              `LENGTH ps = LENGTH ts` by fs[msize_def] \\
              `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
              `msize [Branch (p1::ps) e] = LENGTH ts + 1`
              by fs[msize_def] \\
              rpt (first_x_assum (qspecl_then [`c`, `ts`, `targs`] assume_tac)) \\
              res_tac \\ rpt (WEAKEN_TAC is_imp) \\ fs[] \\
              metis_tac[match_app])
          >- (Cases_on `pmatch_list (p1::ps) (Term c targs::ts)`
              >- (`match [Branch (p1::ps) e] (Term c targs::ts) = SOME e`
                  by rw[match_def] \\
                  `LENGTH ps = LENGTH ts` by fs[msize_def] \\
                  `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
                  `msize [Branch (p1::ps) e] = LENGTH ts + 1`
                  by fs[msize_def] \\
                  rpt (first_x_assum (qspecl_then [`c`, `ts`, `targs`]
                       assume_tac)) \\
                  res_tac \\ rpt (WEAKEN_TAC is_imp) \\ fs[] \\
                  metis_tac[match_app])
              >- (`match [Branch (p1::ps) e] (Term c targs::ts) = NONE`
                  by (imp_res_tac nmatch_first_patlist \\
                  first_x_assum (qspecl_then [`[]`, `e`] assume_tac) \\
                  fs[match_def]) \\
                  `LENGTH ps = LENGTH ts` by fs[msize_def] \\
                  fs[msize_def] \\
                  `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
                  `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\
                  rpt (first_x_assum (qspecl_then [`c`, `ts`, `targs`]
                       assume_tac))\\
                  fs[] \\ res_tac \\ fs[] \\
                  imp_res_tac match_app2 \\
                  first_x_assum (qspec_then
                  `default [Branch (p2::ps) e] ++
                  default m` assume_tac) \\
                  fs[] \\
                  `match [Branch (p2::ps) e] (Term c targs::ts) = SOME e`
                  by (imp_res_tac match_first_patlist \\
                     rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
                     fs[]) \\
                  rfs[] \\
                  metis_tac[match_app])))
      >- (imp_res_tac not_pmatch_list_or \\
          `match [Branch (p1::ps) e] (Term c targs::ts) = NONE`
          by (imp_res_tac nmatch_first_patlist \\
            rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
            fs[match_def]) \\
          `match [Branch (p2::ps) e] (Term c targs::ts) = NONE`
          by (imp_res_tac nmatch_first_patlist \\
            rpt (first_x_assum (qspecl_then [`[]`, `e`] assume_tac)) \\
            fs[match_def]) \\
          `LENGTH ps = LENGTH ts` by fs[msize_def] \\
          `inv_mat [Branch (p1::ps) e]` by fs[inv_mat_def] \\
          `inv_mat [Branch (p2::ps) e]` by fs[inv_mat_def] \\
          fs[is_cons_head_def] \\
          `match m (Term c targs::ts) =
          match (default m) ts`
          suffices_by
          (fs[msize_def] \\
           rpt (first_x_assum (qspecl_then [`c`,`ts`, `targs`] assume_tac)) \\
          fs[] \\ res_tac \\ fs[] \\
          imp_res_tac match_app2 \\
          first_assum (qspec_then
          `default [Branch (p2::ps) e] ++
           default m` assume_tac) \\
          fs[]) \\
          Cases_on `m`
          >- rw[match_def, default_def]
          >- (`inv_mat (h::t)` by (imp_res_tac inv_mat_dcmp) \\
              `msize (h::t) = LENGTH ts + 1` by
              (imp_res_tac msize_inv \\ fs[]) \\
              rpt (first_x_assum (qspecl_then [`c`,`ts`, `targs`] assume_tac)) \\
              fs[])))
  >- (rw[match_def, default_def]
      >- (imp_res_tac pmatch_list_as \\
          `match ((Branch (p::ps) e)::rs) (Term c targs::ts) = SOME e`
          by rw[match_def] \\
          imp_res_tac inv_mat_as \\
          `msize ((Branch (p::ps) e)::rs) = LENGTH ts + 1`
          by fs[msize_def] \\
          `~(is_cons_head c (Branch (p::ps) e::rs))`
          by (fs[is_cons_head_def] \\ imp_res_tac is_cons_head_app \\ fs[]) \\
          first_x_assum (qspecl_then [`c`, `ts`, `targs`] assume_tac) \\
          res_tac \\ fs[])
      >- (imp_res_tac not_pmatch_list_as \\
          `match ((Branch (p::ps) e)::rs) (Term c targs::ts) =
           match rs (Term c targs::ts)`
          by (imp_res_tac nmatch_first_patlist \\
              rpt (first_x_assum (qspecl_then [`rs`, `e`] assume_tac)) \\
              fs[match_def] \\ rfs[]) \\
          imp_res_tac inv_mat_as \\
          `msize ((Branch (p::ps) e)::rs) = LENGTH ts + 1` by
          fs[msize_def] \\
          `~(is_cons_head c (Branch (p::ps) e::rs))`
          by (fs[is_cons_head_def] \\ imp_res_tac is_cons_head_app \\ fs[]) \\
          first_x_assum (qspecl_then [`c`, `ts`, `targs`] assume_tac) \\
          res_tac \\ fs[]))
  >- fs[msize_def]
QED;

(* definition of decision trees *)
Datatype `dTree =
    Leaf num
  | Fail
  | Swap num dTree
  | If num dTree dTree
  | Let num dTree
`;

(* Swap the first and ith items in a list *)
Definition get_ith_def:
  get_ith n ts = HD (DROP n ts)
End

Definition replace_ith_def:
  (replace_ith [] _ _ = []) /\
  (replace_ith (t::ts) (0:num) u = (u::ts)) /\
  (replace_ith (t::ts) n u = t::(replace_ith ts (n-1) u))
End

Theorem replace_ith_droptake:
  !l i e. replace_ith l i e =
          TAKE (LENGTH l) ((TAKE i l) ++ [e] ++ (DROP (SUC i) l))
Proof
  ho_match_mp_tac (theorem "replace_ith_ind") \\ rw[]
  >- fs[replace_ith_def]
  >- fs[replace_ith_def]
  >- fs[replace_ith_def, DROP_def]
QED;

Definition swap_items_def:
  (swap_items i [] = []) /\
  (swap_items i [x] = [x]) /\
  (swap_items i (t::ts) = (get_ith (i-1) ts)::(replace_ith ts (i-1) t))
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
  rw[get_ith_def, replace_ith_droptake]
QED;

Theorem swap_columns_msize:
  !m i. inv_mat m /\ i < (msize m) ==> msize (swap_columns i m) = msize m
Proof
  Induct_on `m`
  >- fs[msize_def, swap_columns_def]
  >- (Cases_on `h` \\
      rw[msize_def, swap_columns_def, swap_items_length])
QED;

(* Remove the first column of a matrix *)
Definition remove_fst_col_def:
  (remove_fst_col [] = []) /\
  (remove_fst_col ((Branch (p::ps) e)::bs) =
    (Branch ps e)::(remove_fst_col bs))
End

(* Semantics of decision trees *)
Definition dt_eval_def:
  (dt_eval ts (Leaf k) = k) /\
  (dt_eval ts (Swap i dt) = dt_eval (swap_items i ts) dt) /\
  (dt_eval ((Term c targs)::ts) (If c' dt1 dt2) =
    if c = c'
    then dt_eval (targs++ts) dt1
    else dt_eval (targs++ts) dt2) /\
  (dt_eval ts (Let k dt) = dt_eval ts dt)
End

(* Definition of occurences and their application to terms *)
(* val _ = type_abbrev("occurences", ``:num list``) *)

(* Definition occur_term_def: *)
(*   (occur_term t [] = t) /\ *)
(*   (occur_term (Term tcons targs) (occ::os) = *)
(*     occur_term (get_ith occ targs) os) *)
(* End *)

Definition all_wild_or_vars_def:
  (all_wild_or_vars [] = T) /\
  (all_wild_or_vars (Any::ps) = all_wild_or_vars ps) /\
  (all_wild_or_vars ((Var _)::ps) = all_wild_or_vars ps) /\
  (all_wild_or_vars ((Cons _ _ _)::_) = F) /\
  (all_wild_or_vars ((Or p1 p2)::ps) = ((all_wild_or_vars [p1]) /\
                                        (all_wild_or_vars [p2]) /\
                                        (all_wild_or_vars ps))) /\
  (all_wild_or_vars ((As p _)::ps) = ((all_wild_or_vars [p]) /\
                                      (all_wild_or_vars ps)))
End

Theorem all_wild_vars_dcmp:
  !p ps. all_wild_or_vars (p::ps) ==>
         (all_wild_or_vars [p] /\
          all_wild_or_vars ps)
Proof
  Cases_on `p` \\ fs[all_wild_or_vars_def]
QED;

Theorem all_wild_vars_pmatch_list_aux:
   (!p t. all_wild_or_vars [p] ==>
          pmatch p t) /\
   (!ps ts. all_wild_or_vars ps /\
            (LENGTH ps) = (LENGTH ts) ==>
            pmatch_list ps ts)
Proof
  ho_match_mp_tac (theorem "pat_induction") \\ rw[]
  >- fs[pmatch_def]
  >- fs[pmatch_def]
  >- fs[all_wild_or_vars_def]
  >- fs[all_wild_or_vars_def, pmatch_def]
  >- fs[all_wild_or_vars_def, pmatch_def]
  >- fs[pmatch_list_def]
  >- (Cases_on `ts`
      >- (Cases_on `ps` \\ fs[])
      >- (fs[all_wild_or_vars_def] \\
          imp_res_tac all_wild_vars_dcmp \\
          fs[pmatch_list_def]))
QED;

Theorem all_wild_vars_pmatch_list:
  !ps ts. (LENGTH ps) = (LENGTH ts) /\
         all_wild_or_vars ps ==>
         pmatch_list ps ts
Proof
  Cases_on `ps` \\ Cases_on `ts` \\ rw[]
  >- fs[pmatch_list_def]
  >- (rw[pmatch_list_def] \\
      imp_res_tac all_wild_vars_dcmp \\
      imp_res_tac all_wild_vars_pmatch_list_aux \\
      first_assum (qspec_then `h'` mp_tac) \\ fs[])
QED;

(* add bindings add let expressions to an existing decision tree *)
Definition add_bindings_def:
  (add_bindings [] d = d) /\
  (add_bindings (Any::ps) d = add_bindings ps d) /\
  (add_bindings ((Var n)::ps) d = Let n (add_bindings ps d)) /\
  (add_bindings ((Cons _ _ _)::ps) d = add_bindings ps d) /\
  (add_bindings ((Or p1 p2)::ps) d =
    add_bindings [p1] (add_bindings [p2] (add_bindings ps d))) /\
  (add_bindings ((As p n)::ps) d = Let n (add_bindings [p] (add_bindings ps d)))
End

(*
TODO: when we add a semantic meaning to let bindings, this has to change
*)
Theorem eval_add_bindings:
  !vs bs dt. dt_eval vs (add_bindings bs dt) =
             dt_eval vs dt
Proof
  gen_tac \\
  ho_match_mp_tac (theorem "add_bindings_ind") \\ rw[] \\
  fs[add_bindings_def, dt_eval_def]
QED;

(*
Column infos

Returns a pair containing identifiers to be bound in default case and a list
containing pairs of constructors, expected number of constructors for a type,
an arity for the constructor, and list of identifiers to be bound for each of
these constructors
*)
val _ = type_abbrev("cons_infos", ``:((num # num # num # (num list)) list)``)
val _ = type_abbrev("col_infos", ``:(num list) # cons_infos``)

(* Add an indentifier to the "default" identifiers *)
Definition add_def_id_def:
  add_def_id id (ids, cinfos) = (id::ids, cinfos)
End

(* Add a constructor to the list of constructors of the column *)
Definition add_cons_id_aux_def:
  (add_cons_id_aux c n a id ([]: cons_infos) = [(c,n,a,[id])]) /\
  (add_cons_id_aux c n a id ((c', n', a', cids)::cinfos) =
    if c = c'
    then ((c', n', a', id::cids)::cinfos)
    else ((c', n', a', cids)::(add_cons_id_aux c n a id cinfos)))
End

Definition add_cons_id_def:
  (add_cons_id c n a id ((ids, cinfos): col_infos) =
    (ids, (add_cons_id_aux c n a id cinfos)))
End

(* Adds an identifier associated with the constructor c *)
Definition add_cons_aux_def:
  (add_cons_aux c n a [] = [(c,n,a,[])]) /\
  (add_cons_aux c n a ((c', n', a', cids)::cinfos) =
    if c = c'
    then ((c', n', a', cids)::cinfos)
    else ((c', n', a', cids)::(add_cons_aux c n a cinfos)))
End

Definition add_cons_def:
  (add_cons c n a ((ids, cinfos): col_infos) =
    (ids, (add_cons_aux c n a cinfos)))
End

(* Merge two columns informations *)
Definition merge_list_def:
  (merge_list [] ys = ys) /\
  (merge_list (x::xs) ys =
    if MEM x ys
    then (merge_list xs ys)
    else x::(merge_list xs ys))
End

Definition merge_cinfos_aux_def:
  (merge_cinfos_aux c n a [] cinfos =
    add_cons_aux c n a cinfos) /\
  (merge_cinfos_aux c n a (cid::cids) cinfos =
    add_cons_id_aux c n a cid (merge_cinfos_aux c n a cids cinfos))
End

Definition merge_cinfos_def:
  (merge_cinfos [] cinfos = cinfos) /\
  (merge_cinfos ((c', n, a, cids)::cinfos) cinfos' =
    merge_cinfos_aux c' n a cids (merge_cinfos cinfos cinfos'))
End

Definition merge_colinfos_def:
  merge_colinfos (ids, cinfos) (ids', cinfos') =
    (merge_list ids ids', merge_cinfos cinfos cinfos')
End

(* Add the identifiers of a default pattern to the infos of a column *)
Definition add_def_bindings_def:
  (add_def_bindings Any col_infos = col_infos) /\
  (add_def_bindings (Var n) col_infos = add_def_id n col_infos) /\
  (add_def_bindings (Or p1 p2) col_infos = merge_colinfos
                                            (add_def_bindings p1 col_infos)
                                            (add_def_bindings p2 col_infos)) /\
  (add_def_bindings (As p n) col_infos = add_def_id n
                                           (add_def_bindings p col_infos))
End

(* Add the identifiers for constructor c to the infos of a column *)
Definition add_cons_bindings_def:
  (add_cons_bindings c n a Any col_infos = col_infos) /\
  (add_cons_bindings c n a (Var n') col_infos = add_cons_id c n a n' col_infos) /\
  (add_cons_bindings c n a (Cons _ _ _) col_infos = col_infos) /\
  (add_cons_bindings c n a (Or p1 p2) col_infos = merge_colinfos
                                          (add_cons_bindings c n a p1 col_infos)
                                          (add_cons_bindings c n a p2 col_infos)) /\
  (add_cons_bindings c n a (As p n') col_infos = add_cons_id c n a n'
                                            (add_cons_bindings c n a p col_infos))
End

(* Get the list of constructors and arities in a pattern *)
Definition get_cons_in_def:
  (get_cons_in Any = []) /\
  (get_cons_in (Var _) = []) /\
  (get_cons_in (Cons c _ sub_pats) = [(c, (LENGTH sub_pats))]) /\
  (get_cons_in (Or p1 p2) = merge_list (get_cons_in p1)
                                       (get_cons_in p2)) /\
  (get_cons_in (As p _) = get_cons_in p)
End

(* Get number of constructors that match the type of the pattern *)
Definition get_nb_types_def:
  (get_nb_types Any = 0) /\
  (get_nb_types (Var _) = 0) /\
  (get_nb_types (Cons _ n _) = n) /\
  (get_nb_types (Or p1 p2) = MAX (get_nb_types p1) (get_nb_types p2)) /\
  (get_nb_types (As p _) = get_nb_types p)
End

(* Build the informations on a constructor *)
Definition col_infos_def:
  (col_infos [] = ([],[])) /\
  (col_infos ((Branch (Any::ps) e)::rs) = col_infos rs) /\
  (col_infos ((Branch ((Var n)::ps) e)::rs) =
    add_def_id n (col_infos rs)) /\
  (col_infos ((Branch ((Cons c n sub_ps)::ps) e)::rs) =
    add_cons c n (LENGTH sub_ps) (col_infos rs)) /\
  (col_infos ((Branch ((Or p1 p2)::ps) e)::rs) =
    merge_colinfos (merge_colinfos (col_infos [(Branch [p1] e)])
                                   (col_infos [(Branch [p2] e)]))
                   (col_infos rs)) /\
  (col_infos ((Branch ((As p n)::ps) e)::rs) =
    if all_wild_or_vars [As p n]
    then add_def_id n (add_def_bindings p (col_infos rs))
    else FOLDL (\infos (cons, arity). add_cons_bindings cons (get_nb_types p) arity p infos)
               (col_infos rs)
               (get_cons_in p))
End

Definition cinfo_size_def:
  cinfo_size (_,cons) = LENGTH cons
End

(* Tell if the patterns contain all the constructors of a signature
   from a column_infos *)
Definition is_col_complete_def:
  (is_col_complete (_,[]) = F) /\
  (is_col_complete (_,(c,a,binds)::cons) =
    (((LENGTH cons) + 1:num) = a))
End

(* Add let-bindings to a decision tree from a list of identifiers *)
Definition add_bindings_from_ids_def:
  (add_bindings_from_ids [] dt = dt) /\
  (add_bindings_from_ids (id::ids) dt = Let id (add_bindings_from_ids ids dt))
End

(* The new attempt : couting the number of constructors *)
Definition nb_cons_pat_def:
  (nb_cons_pat Any = (1:num)) /\
  (nb_cons_pat (Var _) = 1) /\
  (nb_cons_pat (Cons _ _ []) = 2) /\
  (nb_cons_pat (Cons c a (p::ps)) =
    (nb_cons_pat p) * (nb_cons_pat (Cons c a ps))) /\
  (nb_cons_pat (Or p1 p2) = (nb_cons_pat p1) + (nb_cons_pat p2)) /\
  (nb_cons_pat (As p _) = nb_cons_pat p)
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
  (is_cons_fcol_pat (Var _) = F) /\
  (is_cons_fcol_pat (Cons _ _ _) = T) /\
  (is_cons_fcol_pat (Or p1 p2) =
    ((is_cons_fcol_pat p1) \/ (is_cons_fcol_pat p2))) /\
  (is_cons_fcol_pat (As p _) = is_cons_fcol_pat p)
End

Definition is_cons_fcol_branch_def:
  (is_cons_fcol_branch [] = F) /\
  (is_cons_fcol_branch (p::ps) = is_cons_fcol_pat p)
End

Definition is_cons_fcol_def:
  (is_cons_fcol [] = F) /\
  (is_cons_fcol ((Branch l e)::bs) = ((is_cons_fcol_branch l) \/ (is_cons_fcol bs)))
End

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
  >- (Cases_on `rs`
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def] \\
          `msize [Branch (p::ps) e] > 0` by fs[msize_def] \\
          imp_res_tac inv_mat_as \\
          fs[nb_cons_pat_def])
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def] \\
          `msize (Branch (p::ps) e::h::t) > 0` by fs[msize_def] \\
	  imp_res_tac inv_mat_as \\
          fs[]))
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
  >- (Cases_on `rs`
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	     is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_as \\
          `msize [Branch (p::ps) e] > 0` by fs[msize_def] \\
          fs[])
      >- (fs[default_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	     is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_as \\
          `msize (Branch (p::ps) e::h::t) > 0` by fs[msize_def] \\
          fs[]))
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
  >- (Cases_on `m`
      >- fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	    nb_cons_branch_app, nb_cons_branch_n_any]
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	    nb_cons_branch_app, nb_cons_branch_n_any] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          fs[nb_cons_def, nb_cons_branch_app, nb_cons_branch_def, nb_cons_branch_n_any,
	     nb_cons_pat_def]))
  >- (Cases_on `m` \\ Cases_on `c=pcons'` \\
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
  >- (Cases_on `rs`
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def] \\
          `msize [Branch (p::ps) e] > 0` by fs[msize_def] \\
          imp_res_tac inv_mat_as \\
          fs[nb_cons_pat_def])
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def] \\
          `msize (Branch (p::ps) e::h::t) > 0` by fs[msize_def] \\
	  imp_res_tac inv_mat_as \\
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
      >- fs[spec_def, is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def]
      >- (fs[spec_def, is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_dcmp \\
          imp_res_tac msize_inv_gt_zero \\
          fs[nb_cons_def, nb_cons_branch_app, nb_cons_branch_def, nb_cons_branch_n_any,
	     nb_cons_pat_def]))
  >- (Cases_on `m`
      >- (Cases_on `c=pcons'`
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_app, nb_cons_branch_def] \\
              `0 < nb_cons_branch ps` by fs[nb_cons_branch_gt_zero] \\
              rewrite_tac [Once MULT_COMM] \\
              fs[LT_MULT_LCANCEL, nb_cons_pat_def, nb_cons_cons_pargs])
          >- fs[spec_def, nb_cons_def, nb_cons_branch_gt_zero])
      >- (Cases_on `c=pcons'`
          >- (fs[spec_def, nb_cons_def, nb_cons_branch_app, nb_cons_branch_def] \\
              imp_res_tac msize_inv_gt_zero \\
              imp_res_tac inv_mat_dcmp \\
              fs[] \\
              imp_res_tac nb_cons_spec_aux \\
              rfs[] \\
              rpt (first_x_assum (qspecl_then [`pcons'`,`a`] assume_tac)) \\
              Cases_on `nb_cons (spec pcons' a (h::t)) = nb_cons (h::t)`
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
  >- (Cases_on `rs`
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	     is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_as \\
          `msize [Branch (p::ps) e] > 0` by fs[msize_def] \\
          fs[])
      >- (fs[spec_def, nb_cons_def, nb_cons_branch_def, nb_cons_pat_def,
	     is_cons_fcol_def, is_cons_fcol_branch_def, is_cons_fcol_pat_def] \\
          imp_res_tac inv_mat_as \\
          `msize (Branch (p::ps) e::h::t) > 0` by fs[msize_def] \\
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
  rw[max_a_branch_def, get_ith_def, replace_ith_droptake] \\
  fs[LENGTH_APPEND, LENGTH_TAKE_EQ, TAKE_LENGTH_ID_rwt, max_a_app] \\
  Cases_on `i-1`
  >- fs[nb_cons_def, nb_cons_branch_def]
  >- (fs[DROP_def, nb_cons_branch_def, nb_cons_branch_app] \\
      `n < LENGTH t'` by fs[] \\
      `0 < nb_cons_pat h` by fs[nb_cons_gt_zero] \\
      `0 < nb_cons_pat h'` by fs[nb_cons_gt_zero] \\
      `nb_cons_pat h * (nb_cons_pat h' * (nb_cons_pat (HD (DROP n t')) *
       nb_cons_branch (DROP (SUC n) t') * nb_cons_branch (TAKE n t'))) =
       nb_cons_pat h * (nb_cons_pat h' * nb_cons_branch t')` suffices_by metis_tac[MULT_COMM, MULT_ASSOC] \\
      fs[LT_MULT_LCANCEL] \\
      `nb_cons_branch (DROP n t') * nb_cons_branch (TAKE n t') =
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

(* compilation scheme a pattern matrix to a decision tree
   based on a heuristic h *)
Definition compile_def:
  (compile h [] useh = Fail) /\
  (compile h ((Branch [] e)::bs) useh = Leaf e) /\
  (compile h ((Branch ps e)::bs) useh =
    if ~(inv_mat ((Branch ps e)::bs)) then ARB else
    if all_wild_or_vars ps
    then (add_bindings ps (Leaf e))
    else
      (* we select a column using heuristic h *)
      let sel_col = (h ((Branch ps e)::bs)) in
      if ((sel_col > 0) /\ (sel_col < (msize ((Branch ps e)::bs))) /\ useh)
      then Swap sel_col (compile h (swap_columns sel_col ((Branch ps e)::bs)) F)
      else (if (is_cons_fcol ((Branch ps e)::bs)) then
            (let cinfos = col_infos ((Branch ps e)::bs) in
             if (is_col_complete cinfos)
             then make_complete h ((Branch ps e)::bs) cinfos
             else make_partial h ((Branch ps e)::bs) cinfos) else ARB)) /\
  (make_complete h m (defs,(c,_,a,binds)::[]) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
     (add_bindings_from_ids defs
      (add_bindings_from_ids binds
       (compile h (spec c a m) T)))
    else ARB) /\
  (make_complete h m (defs,(c,_,a,binds)::cons) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If c (add_bindings_from_ids defs
          (add_bindings_from_ids binds
           (compile h (spec c a m) T)))
         (make_complete h m (defs, cons))
    else ARB) /\
  (make_partial h m (defs,[]) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    add_bindings_from_ids defs
      (compile h (default m) T)
    else ARB) /\
  (make_partial h m (defs,(c,_,a,binds)::cons) =
    if inv_mat m /\ (msize m) > 0 /\ m <> [] /\ is_cons_fcol m then
    If c (add_bindings_from_ids defs
          (add_bindings_from_ids binds
           (compile h (spec c a m) T)))
         (make_partial h m (defs, cons))
    else ARB)
Termination
WF_REL_TAC `(inv_image ($< LEX ($< LEX $<))
            (\x. case x of INL(_,m,b) => (nb_cons m, (1:num), if b then (1:num) else 0)
                         | INR y => (case y of INL(_,m,_,i) =>
                                      (nb_cons m, (0:num), LENGTH i)
                                     | INR(_,m,_,i) =>
                                      (nb_cons m, (0:num), LENGTH i))))` \\
rw[]
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v12::v13) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (DISJ2_TAC \\ fs[nb_cons_swap])
>- imp_res_tac nb_cons_default
>- (imp_res_tac nb_cons_spec \\
    first_x_assum (qspecl_then [`c`, `a`] assume_tac) \\
    fs[])
>- (imp_res_tac nb_cons_spec \\
    first_x_assum (qspecl_then [`c`, `a`] assume_tac) \\
    fs[])
End

Theorem compile_complete:
  (!c h m useh v k. (msize m) = (LENGTH v) /\
                    useh /\
                    c > (3 * (LENGTH m) * (msize m) + 1) ==>
                    ((match m v = SOME k) ==>
                    (dt_eval v (compile c h m useh) = k))) /\
  (!c h m cinfos v k. (msize m) = (LENGTH v) /\
                      c > (3 * (LENGTH m) * (msize m)) /\
                      (is_col_complete cinfos) ==>
                      ((match m v = SOME k) ==>
                       (dt_eval v (make_complete c h m cinfos) = k))) /\
  (!c h m cinfos v k. (msize m) = (LENGTH v) /\
                      c > (3 * (LENGTH m) * (msize m)) /\
                      ~(is_col_complete cinfos) ==>
                      ((match m v = SOME k) ==>
                       (dt_eval v (make_partial c h m cinfos) = k)))
Proof
  ho_match_mp_tac (theorem "compile_ind") \\ rw[]
  >- fs[match_def]
  >- (fs[match_def, compile_def, msize_def] \\
      Cases_on `v` \\
      fs[pmatch_list_def, dt_eval_def])
  >- (fs[compile_def] \\
      Cases_on `v` \\ fs[msize_def] \\
      Cases_on `all_wild_or_vars (v14::v15)` \\ fs[]
      >- (fs[match_def] \\
          `LENGTH (h::t) = LENGTH (v14::v15)` by fs[] \\
          imp_res_tac all_wild_vars_pmatch_list \\
          fs[eval_add_bindings, dt_eval_def])
      >- cheat)
      (*
      >- (Cases_on `h (Branch (v12::v13) e::bs) > 0` \\ fs[]
          >- (fs[swap_columns_length, swap_columns_msize, msize_def,
		 dt_eval_def]
              `SUC`*)
  >- (fs[compile_def] \\
      (* we must show that add_bindings_from_id doesn't effect evaluation *)
      fs[eval_add_bindings, dt_eval_def]
      cheat)
  >- (fs[compile_def, dt_eval_def] \\
      (* Cases analysis on head of c *)
      cheat)
  (* same for make partial *)
  >- cheat
  >- cheat
  >- (fs[compile_def, dt_eval_def] \\
      (* Somehow show that this case is not possible, case
        analysis on on the first column of h ? *)
      cheat)
QED;

val _ = export_theory ();
