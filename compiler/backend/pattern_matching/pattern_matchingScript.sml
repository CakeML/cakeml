(*
  Pattern-matching compilation to decision trees
  See issue #667 for details and references
*)
open preamble;
open numTheory listTheory;

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
     in its type an a list of other patterns *)
  | Cons num num (pat list)
  | Or pat pat
  | As pat num (* (p:pat) as (x:num) *)
`;

Definition psize_def:
  (psize Any = (2:num)) /\
  (psize (Var n) = 2) /\
  (psize (Cons n t []) = 2) /\
  (psize (Cons n t (x::xs)) = 2 + ((psize x) * psize (Cons n t xs))) /\
  (psize (Or p1 p2) = 2 + (psize p1) + (psize p2)) /\
  (psize (As p n) = 2 + (psize p))
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

Theorem inv_mat_as:
  !p n ps e rs.
    inv_mat ((Branch ((As p n)::ps) e)::rs) ==>
    inv_mat ((Branch (p::ps) e)::rs)
Proof
  rw[inv_mat_def] \\
  fs[patterns_def]
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
  !p. 0 < (psize p)
Proof
  ho_match_mp_tac (theorem "psize_ind") \\ rw[psize_def]
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
  (WF_REL_TAC `measure (\ (x,_). psize x)` \\ rw[psize_def] \\
  Induct_on `pargs`
  >- fs[psize_def]
  >- (rpt strip_tac \\
      fs[MEM]
      >- (fs[psize_def] \\
          `0 < psize (Cons pcons' v0 pargs) ` by fs[psize_gt_zero] \\
	  `(psize h) <= ((psize h) * (psize (Cons pcons' v0 pargs)))` by
	  fs[LE_MULT_CANCEL_LBARE] \\
	  decide_tac)
      >- (res_tac \\
          fs[psize_def] \\
          `0 < psize h ` by fs[psize_gt_zero] \\
          `psize (Cons pcons' v0 pargs) <= (psize h) * (psize (Cons pcons' v0 pargs))` by
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
  (swap_items i (t::ts) = (get_ith (i-1) ts)::(replace_ith ts (i-1) t))
End


(* Swap the first and ith columns in a matrix *)
Definition swap_columns_def:
  (swap_columns i [] = []) /\
  (swap_columns i ((Branch b e)::bs) =
     (Branch (swap_items i b) e)::(swap_columns i bs))
End

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

(*
Computing the size of a pattern matrix by giving a weight to each
of these parts. The weights are set these way to have the specialization
of m or the default matrix associated to m strictly smaller than m.
*)
Definition plist_size_def:
  (plist_size [] = 1) /\
  (plist_size (p::ps) = (psize p) * (plist_size ps))
End

Theorem plist_size_gt_zero:
  !ps. 0 < plist_size ps
Proof
  Induct_on `ps` \\
  fs[plist_size_def] \\
  rw[] \\
  `0 < psize h` by fs[psize_gt_zero] \\
  fs[LESS_MULT2]
QED;

Definition pm_size_def:
  (pm_size [] = 0) /\
  (pm_size ((Branch ps e)::bs) =
    (plist_size ps) +
    (pm_size bs))
End

(* Most of these theorems are not working with the special
  case for or-patterns *)
Theorem pm_size_product_patterns:
  !p ps e. pm_size [Branch (p::ps) e] = psize p * pm_size [Branch ps e]
Proof
  Cases_on `p` \\
  fs[pm_size_def, psize_def, plist_size_def]
QED;

Theorem pm_size_cons:
  !b bs. pm_size (b::bs) = (pm_size [b]) + (pm_size bs)
Proof
  Cases_on `b` \\
  fs[pm_size_def]
QED;

Theorem pm_size_app:
  !p1 p2 e. pm_size [Branch (p1 ++ p2) e] = pm_size [Branch p1 e] * pm_size [Branch p2 e]
Proof
  Induct_on `p1` \\
  fs[pm_size_def, plist_size_def]
QED;

Theorem pm_size_app2:
  !b1 b2. pm_size (b1++b2) = pm_size b1 + pm_size b2
Proof
  Induct_on `b1` \\
  rw[] \\
  fs[pm_size_def] \\
  rewrite_tac [Once pm_size_cons] \\
  `pm_size (h::b1) = pm_size [h] + pm_size b1` by
  rewrite_tac [Once pm_size_cons] \\
  fs[]
QED;

Theorem plist_size_app:
  !ps qs. plist_size (ps ++ qs) = (plist_size ps) * (plist_size qs)
Proof
  Induct_on `ps` \\
  fs[plist_size_def]
QED;

Theorem drop_plist_size_decompose:
  !t i. i < LENGTH t ==>
        (psize (HD (DROP i t)) *
         plist_size (DROP (SUC i) t)) =
        plist_size (DROP i t)
Proof
  Induct_on `t`
  >- fs[DROP_def]
  >- (fs[DROP_def] \\
     Cases_on `i=0` \\ rw[]
     >- rw[plist_size_def]
     >- (first_x_assum (qspec_then `i'-1` assume_tac) \\
         `SUC (i'-1) = i'` by fs[SUB_LEFT_SUC] \\
         fs[])
     >- rw[plist_size_def]
     >- (first_x_assum (qspec_then `i'-1` assume_tac) \\
         `SUC (i'-1) = i'` by fs[SUB_LEFT_SUC] \\
         fs[]))
QED;

Theorem drop_take_plist_size:
  !i t. (plist_size (TAKE i t) * plist_size (DROP i t)) =
        plist_size t
Proof
  rw[] \\
  `plist_size t = plist_size ((TAKE i t) ++ (DROP i t))` by fs[] \\
  fs[plist_size_app]
QED;


Theorem swapi_plist_size:
  !i ps e. i > 0 /\
           i < (LENGTH ps) ==>
           plist_size (swap_items i ps) = plist_size ps
Proof
  Cases_on `ps`
  >- fs[swap_items_def]
  >- (fs[swap_items_def, get_ith_def, replace_ith_droptake, plist_size_def] \\
      rw[] \\
      `LENGTH (TAKE (i-1) t ++ [h] ++ DROP i t) = (LENGTH t)`
      by fs[LENGTH_APPEND, LENGTH_TAKE_EQ] \\
      fs[TAKE_LENGTH_ID_rwt] \\
      fs[plist_size_app, plist_size_def] \\
      `(psize (HD (DROP (i-1) t)) *
      plist_size (DROP (SUC (i-1)) t)) *
      plist_size (TAKE (i-1) t) *
      psize h = (plist_size t) * psize h` suffices_by metis_tac[MULT_ASSOC, MULT_COMM] \\
      `i - 1 < LENGTH t` by fs[] \\
      metis_tac[drop_plist_size_decompose, drop_take_plist_size, MULT_COMM])
QED;

Theorem swap_pmsize:
  !i m. inv_mat m /\
        i > 0 /\
        i < (msize m) ==>
        pm_size (swap_columns i m) = pm_size m
Proof
  Induct_on `m`
  >- fs[swap_columns_def, pm_size_def]
  >- (Cases_on `h` \\
      fs[swap_columns_def, pm_size_def, swap_items_def] \\
      rewrite_tac[Once pm_size_cons] \\
      `pm_size (Branch l n::m) = (pm_size [Branch l n] + pm_size m)`
      by rewrite_tac [Once pm_size_cons] \\
      rw[] \\
      imp_res_tac inv_mat_dcmp \\
      Cases_on `m = []`
      >- fs[swap_columns_def, swapi_plist_size, msize_def]
      >- (imp_res_tac msize_inv' \\
          fs[msize_def, swapi_plist_size]))
QED;

Theorem pm_size_default:
  !m. inv_mat m /\
      (msize m) > 0 /\
      m <> [] ==>
      pm_size (default m) < pm_size m
Proof
  ho_match_mp_tac (theorem "default_ind") \\ rw[]
  >- (Cases_on `m`
      >- fs[default_def, pm_size_def, psize_def, plist_size_def,
	    plist_size_gt_zero]
      >- (`h::t <> []` by fs[] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          res_tac \\
          fs[default_def, pm_size_def, psize_def, plist_size_def]))
  >- (Cases_on `m`
      >- fs[default_def, pm_size_def, psize_def, plist_size_def,
	    plist_size_gt_zero]
      >- (`h::t <> []` by fs[] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          res_tac \\
          fs[default_def, pm_size_def, psize_def, plist_size_def]))
  >- (Cases_on `m`
      >- fs[default_def, pm_size_def, psize_def, plist_size_gt_zero]
      >- (`h::t <> []` by fs[] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          res_tac \\
          fs[default_def, pm_size_def, psize_def, plist_size_gt_zero]))
  >- (Cases_on `m`
      >- fs[default_def, pm_size_def, pm_size_app2, plist_size_def, psize_def,
            inv_mat_def, msize_def]
      >- (`h::t <> []` by fs[] \\
          imp_res_tac msize_inv_gt_zero \\
          imp_res_tac inv_mat_dcmp \\
          res_tac \\
          fs[default_def, pm_size_def, psize_def, plist_size_gt_zero, pm_size_app2,
             plist_size_def, inv_mat_def, msize_def]))
  >- (Cases_on `rs`
      >- fs[default_def, pm_size_def, plist_size_def, psize_def, inv_mat_def, msize_def]
      >- (imp_res_tac inv_mat_as \\
          `msize (Branch (p::ps) e::h::t) > 0` by fs[msize_def] \\
          res_tac \\
          fs[default_def, pm_size_def, plist_size_def, psize_def]))
  >- fs[msize_def]
QED;

(* Compilation scheme a pattern matrix to a decision tree
   based on a heuristic h
*)
val compile_def = Hol_defn "compile" `
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
      else (let cinfos = col_infos ((Branch ps e)::bs) in
            if (is_col_complete cinfos)
            then make_complete h ((Branch ps e)::bs) cinfos
            else make_partial h ((Branch ps e)::bs) cinfos)) /\
  (make_complete h m (defs,(c,_,a,binds)::[]) =
     (add_bindings_from_ids defs
      (add_bindings_from_ids binds
       (compile h (spec c a m) T)))) /\
  (make_complete h m (defs,(c,_,a,binds)::cons) =
    If c (add_bindings_from_ids defs
          (add_bindings_from_ids binds
           (compile h (spec c a m) T)))
         (make_complete h m (defs, cons))) /\
  (make_partial h m (defs,[]) =
    add_bindings_from_ids defs
      (compile h (default m) T)) /\
  (make_partial h m (defs,(c,_,a,binds)::cons) =
    If c (add_bindings_from_ids defs
          (add_bindings_from_ids binds
           (compile h (spec c a m) T)))
         (make_partial h m (defs, cons)))
`

Defn.tgoal compile_def;

WF_REL_TAC `(inv_image ($< LEX $<)
            (\x. case x of INL(_,m,b) => ((pm_size m) + 1, (if b then (1:num) else 0))
                         | INR y => (case y of INL(_,m,_,i) => (pm_size m, LENGTH i)
                                             | INR(_,m,_,i) => (pm_size m, LENGTH i))))` \\
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
>- (DISJ2_TAC \\
    imp_res_tac swap_pmsize)
>-



>- cheat
>- cheat
>- cheat
>- cheat
>- (`col_infos (Branch (v14::v15) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v14::v15) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v14::v15) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- (`col_infos (Branch (v14::v15) e::bs) = (p_1, p_2)` by fs[] \\
    fs[])
>- cheat




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
