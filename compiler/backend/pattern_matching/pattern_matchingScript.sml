(*
  Pattern-matching compilation to decision trees
  See issue #667 for details and references
*)
open listTheory;

val _ = new_theory "pattern_matching";

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
  | Cons num (pat list)
  | Or pat pat
  | As pat num (* pat as var *)
`;

Definition psize_def:
  (psize Any = (1:num)) /\
  (psize (Var n) = 1) /\
  (psize (Cons n []) = 1) /\
  (psize (Cons n (x::xs)) = 1 + (psize x) + psize (Cons n xs)) /\
  (psize (Or p1 p2) = 1 + (psize p1) + (psize p2)) /\
  (psize (As p n) = 1 + (psize p))
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

(* Semantics of matching *)
val pmatch_def = tDefine "match_def" `
  (pmatch Any  t = T) /\
  (pmatch (Var n) t = T) /\
  (pmatch (Cons pcons pargs) (Term tcons targs) =
    ((pcons = tcons) /\
    (LIST_REL (\p t. pmatch p t) pargs targs))) /\
  (pmatch (Cons pcons []) (Term tcons []) = (pcons = tcons)) /\
  (pmatch (Cons pcons ps) (Term tcons []) = F) /\
  (pmatch (Cons pcons []) (Term tcons ts) = F) /\
  (pmatch (Cons pcons (p::ps)) (Term tcons (t::ts)) =
    ((pmatch p t) /\
     (pmatch (Cons pcons ps) (Term tcons ts)))) /\
  (pmatch (Or p1 p2) t = ((pmatch p1 t) \/ (pmatch p2 t))) /\
  (pmatch (As p num) t = pmatch p t)`
  (WF_REL_TAC `measure (\ (x,_). psize x)` \\ rw[psize_def] \\
  Induct_on `pargs`
  >- fs[psize_def]
  >- (rpt strip_tac \\
      fs[MEM]
      >- fs[psize_def]
      >- (res_tac \\ fs[psize_def])));

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
  (spec c a ((Branch ((Cons pcons pargs)::ps) e)::rs) =
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
  (default ((Branch ((Cons pcons pargs)::ps) e)::rs) =
    (default rs)) /\
  (default ((Branch ((Or p1 p2)::ps) e)::rs) =
    (default [Branch (p1::ps) e]) ++
    (default [Branch (p2::ps) e]) ++
    (default rs)) /\
  (default ((Branch ((As p n)::ps) e)::rs) =
    (default (Branch (p::ps) e)::rs))
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
  (is_cons_head c ((Branch ((Cons pcons pargs)::ps) e)::rs) =
    (if c = pcons
    then T
    else (is_cons_head c rs))) /\
  (is_cons_head c ((Branch ((Or p1 p2)::ps) e)::rs) =
    (is_cons_head c [Branch (p1::ps) e]) \/
    (is_cons_head c [Branch (p2::ps) e]) \/
    (is_cons_head c rs)) /\
  (is_cons_head c ((Branch ((As p n)::ps) e)::rs) =
    (is_cons_head c [Branch (p::ps) e]) \/
    (is_cons_head c rs))
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

val _ = export_theory ();
