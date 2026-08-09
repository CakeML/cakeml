(*
  An exhaustiveness checker for pattern-match rows, in the style of
  Maranget's usefulness algorithm, but using sibling annotations instead
  of a typing environment.

  The entry point is exh_rows.  It first removes all Or-patterns by
  expanding each row into its Or-free variants, then decides whether the
  resulting one-column pattern matrix covers every value.

  The matrix algorithm (exh_matrix) works on a matrix of pattern vectors.
  Looking at the first column it computes, from the sibling information in
  the patterns, an over-approximation col_ctors of the set of constructors
  a well-typed value can have there.

    - If that set is unknown (NONE) the matrix is exhaustive when the
      default matrix is: only rows starting with a wildcard can match a
      value whose constructor is not mentioned.

    - If the set is known, the matrix is exhaustive when every
      specialised matrix is: each constructor of the set is considered in
      turn, and its arguments are pushed onto the front of the vector.

  Only well-typed values matter, i.e. values for which no row of the
  original match yields PTypeFailure.  Since match walks *every* row and
  fails with NONE as soon as one row type-fails, all rows constrain the
  value simultaneously.  Hence the constructor set of a column is the
  *intersection* over the rows of the constructors each head pattern
  allows, which is what col_ctors computes.
*)
Theory pattern_exh
Ancestors
  pattern_common pattern_semantics ast
Libs
  preamble


(* -------------------------------------------------------------------- *
   Constructors of values.

   A well-typed value at a given position is a tagged term (TagC), an
   untagged term, i.e. a tuple (TupC), or a reference (RefC).  Literals
   are deliberately not constructors here: their type is (for all
   practical purposes) infinite, so a column of literals is never a
   complete signature.
 * -------------------------------------------------------------------- *)

Datatype:
  ctor = TagC num num   (* tag and arity of a Term (SOME tag) *)
       | TupC num       (* arity of a Term NONE               *)
       | RefC           (* a RefPtr                           *)
End

Definition ctor_arity_def:
  ctor_arity (TagC t a) = a /\
  ctor_arity (TupC a) = a /\
  ctor_arity RefC = 1
End

Definition anys_def:
  anys 0 = [] /\
  anys (SUC n) = Any :: anys n
End


(* -------------------------------------------------------------------- *
   Removing Or-patterns.

   expand p is the list of Or-free patterns p can be split into.  Given
   that pmatch does not type-fail, p matches a value exactly when one of
   the patterns in expand p does.
 * -------------------------------------------------------------------- *)

Definition add_head_def:
  add_head x [] = [] /\
  add_head x (ys::yss) = (x::ys) :: add_head x yss
End

Definition mk_prods_def:
  mk_prods [] ys = [] /\
  mk_prods (x::xs) ys = add_head x ys ++ mk_prods xs ys
End

Definition mk_refs_def:
  mk_refs [] = [] /\
  mk_refs (p::ps) = Ref p :: mk_refs ps
End

Definition mk_conses_def:
  mk_conses t [] = [] /\
  mk_conses t (ps::pss) = Cons t ps :: mk_conses t pss
End

Definition expand_def:
  expand Any = [Any] /\
  expand (Lit l) = [Lit l] /\
  expand (Or p q) = expand p ++ expand q /\
  expand (Ref p) = mk_refs (expand p) /\
  expand (Cons t ps) = mk_conses t (expand_list ps) /\
  expand_list [] = [[]] /\
  expand_list (p::ps) = mk_prods (expand p) (expand_list ps)
Termination
  WF_REL_TAC ‘measure (\x. case x of INL p => pat_size p
                                   | INR ps => list_size pat_size ps)’
End

Definition mk_rows_def:
  mk_rows [] = [] /\
  mk_rows (p::ps) = [p] :: mk_rows ps
End

Definition or_rows_def:
  or_rows [] = [] /\
  or_rows ((p,e)::rows) = mk_rows (expand p) ++ or_rows rows
End


(* -------------------------------------------------------------------- *
   The constructors a head pattern allows a well-typed value to have.

   NONE means "no information", i.e. every constructor is allowed.  Note
   that a missing sibling list (Cons (SOME (t,NONE)) _), which is how
   exceptions are encoded, gives no information, and neither does a
   literal pattern.
 * -------------------------------------------------------------------- *)

Definition tag_ctors_def:
  tag_ctors [] = [] /\
  tag_ctors ((t,a)::sibs) = TagC t a :: tag_ctors sibs
End

Definition ctor_nub_def:
  ctor_nub [] = [] /\
  ctor_nub (x::xs) = if MEM x xs then ctor_nub xs else x :: ctor_nub xs
End

Definition ctors_of_def:
  ctors_of Any = NONE /\
  ctors_of (Lit _) = NONE /\
  ctors_of (Or _ _) = NONE /\
  ctors_of (Ref _) = SOME [RefC] /\
  ctors_of (Cons NONE qs) = SOME [TupC (LENGTH qs)] /\
  ctors_of (Cons (SOME (t,NONE)) qs) = NONE /\
  ctors_of (Cons (SOME (t,SOME sibs)) qs) =
    SOME (ctor_nub (TagC t (LENGTH qs) :: tag_ctors sibs))
End

Definition ctor_keep_def:
  ctor_keep [] ys = [] /\
  ctor_keep (x::xs) ys =
    if MEM x ys then x :: ctor_keep xs ys else ctor_keep xs ys
End

Definition ctor_inter_def:
  ctor_inter NONE ys = ys /\
  ctor_inter xs NONE = xs /\
  ctor_inter (SOME xs) (SOME ys) = SOME (ctor_keep xs ys)
End

Definition col_ctors_def:
  col_ctors [] = NONE /\
  col_ctors ([]::rows) = col_ctors rows /\
  col_ctors ((p::_)::rows) = ctor_inter (ctors_of p) (col_ctors rows)
End


(* -------------------------------------------------------------------- *
   Specialised and default matrices.

   spec_row c takes the rows that can match a value whose head
   constructor is c, and replaces the head pattern by the patterns for
   the arguments of c.  default_row keeps only the rows that start with a
   wildcard, dropping the head pattern.
 * -------------------------------------------------------------------- *)

Definition spec_row_def:
  spec_row c [] = [] /\
  spec_row c (Any::rest) = [anys (ctor_arity c) ++ rest] /\
  spec_row c ((Cons NONE qs)::rest) =
    (if c = TupC (LENGTH qs) then [qs ++ rest] else []) /\
  spec_row c ((Cons (SOME ts) qs)::rest) =
    (if c = TagC (FST ts) (LENGTH qs) then [qs ++ rest] else []) /\
  spec_row c ((Ref q)::rest) = (if c = RefC then [q::rest] else []) /\
  spec_row c ((Lit l)::rest) = [] /\
  spec_row c ((Or p q)::rest) = []
End

Definition spec_mat_def:
  spec_mat c [] = [] /\
  spec_mat c (r::rows) = spec_row c r ++ spec_mat c rows
End

Definition spec_mats_def:
  spec_mats [] rows = [] /\
  spec_mats (c::cs) rows = spec_mat c rows :: spec_mats cs rows
End

Definition default_row_def:
  default_row (Any::rest) = [rest] /\
  default_row _ = []
End

Definition default_mat_def:
  default_mat [] = [] /\
  default_mat (r::rows) = default_row r ++ default_mat rows
End


(* -------------------------------------------------------------------- *
   Measures used for the termination of exh_matrix.

   Specialising strictly decreases the number of constructor nodes in the
   matrix, provided some head pattern is a constructor pattern -- which
   is exactly what col_ctors returning SOME guarantees.  Taking the
   default matrix does not increase that count, and strictly decreases
   the total number of columns.
 * -------------------------------------------------------------------- *)

Definition pat_weight_def:
  pat_weight Any = (0:num) /\
  pat_weight (Lit l) = 0 /\
  pat_weight (Or p q) = 1 + pat_weight p + pat_weight q /\
  pat_weight (Ref p) = 1 + pat_weight p /\
  pat_weight (Cons t ps) = 1 + pats_weight ps /\
  pats_weight [] = 0 /\
  pats_weight (p::ps) = pat_weight p + pats_weight ps
Termination
  WF_REL_TAC ‘measure (\x. case x of INL p => pat_size p
                                   | INR ps => list_size pat_size ps)’
End

Definition mat_weight_def:
  mat_weight [] = 0 /\
  mat_weight (r::rows) = pats_weight r + mat_weight rows
End

Definition mat_len_def:
  mat_len [] = 0 /\
  mat_len (r::rows) = LENGTH r + mat_len rows
End

Definition mats_weight_def:
  mats_weight [] = 0 /\
  mats_weight (m::ms) = MAX (mat_weight m) (mats_weight ms)
End

Definition mats_len_def:
  mats_len [] = 0 /\
  mats_len (m::ms) = MAX (mat_len m) (mats_len ms)
End

Theorem pats_weight_append[local]:
  !xs ys. pats_weight (xs ++ ys) = pats_weight xs + pats_weight ys
Proof
  Induct \\ fs [pat_weight_def]
QED

Theorem pats_weight_anys[local]:
  !n. pats_weight (anys n) = 0
Proof
  Induct \\ fs [anys_def,pat_weight_def]
QED

Theorem mat_weight_append[local]:
  !xs ys. mat_weight (xs ++ ys) = mat_weight xs + mat_weight ys
Proof
  Induct \\ fs [mat_weight_def]
QED

Theorem mat_len_append[local]:
  !xs ys. mat_len (xs ++ ys) = mat_len xs + mat_len ys
Proof
  Induct \\ fs [mat_len_def]
QED

Theorem mat_weight_spec_row[local]:
  !c r. mat_weight (spec_row c r) <= pats_weight r
Proof
  ho_match_mp_tac spec_row_ind
  \\ rw [spec_row_def,mat_weight_def,pat_weight_def,
         pats_weight_append,pats_weight_anys]
QED

Theorem mat_weight_spec_mat[local]:
  !c rows. mat_weight (spec_mat c rows) <= mat_weight rows
Proof
  gen_tac \\ Induct \\ fs [spec_mat_def,mat_weight_def,mat_weight_append]
  \\ rw []
  \\ match_mp_tac arithmeticTheory.LESS_EQ_LESS_EQ_MONO
  \\ fs [mat_weight_spec_row]
QED

Theorem mat_weight_spec_row_less[local]:
  !c p r. ctors_of p <> NONE ==>
          mat_weight (spec_row c (p::r)) < pats_weight (p::r)
Proof
  gen_tac \\ Cases \\ fs [ctors_of_def]
  \\ rw [spec_row_def,mat_weight_def,pat_weight_def,pats_weight_append]
  \\ rename [‘Cons o' l’] \\ Cases_on ‘o'’
  \\ fs [ctors_of_def,spec_row_def]
  \\ rw [mat_weight_def,pat_weight_def,pats_weight_append]
  \\ rename [‘Cons (SOME ts) l’] \\ PairCases_on ‘ts’
  \\ Cases_on ‘ts1’ \\ fs [ctors_of_def]
  \\ rw [spec_row_def,mat_weight_def,pat_weight_def,pats_weight_append]
QED

Theorem mat_weight_spec_mat_less[local]:
  !c rows cs. col_ctors rows = SOME cs ==>
              mat_weight (spec_mat c rows) < mat_weight rows
Proof
  gen_tac \\ ho_match_mp_tac col_ctors_ind
  \\ rw [col_ctors_def,spec_mat_def,mat_weight_def,mat_weight_append]
  >- (fs [spec_row_def,mat_weight_def,pat_weight_def] \\ res_tac \\ fs [])
  \\ rename [‘spec_row c (p::qs)’]
  \\ Cases_on ‘ctors_of p’ \\ fs [ctor_inter_def]
  >-
   (res_tac
    \\ qspecl_then [‘c’,‘p::qs’] mp_tac mat_weight_spec_row \\ fs [])
  \\ qspecl_then [‘c’,‘rows’] mp_tac mat_weight_spec_mat
  \\ qspecl_then [‘c’,‘p’,‘qs’] mp_tac mat_weight_spec_row_less
  \\ fs []
QED

Theorem mat_weight_default_mat[local]:
  !rows. mat_weight (default_mat rows) <= mat_weight rows
Proof
  Induct \\ fs [default_mat_def,mat_weight_def,mat_weight_append]
  \\ Cases \\ fs [default_row_def,mat_weight_def]
  \\ rename [‘p::t’] \\ Cases_on ‘p’
  \\ fs [default_row_def,mat_weight_def,pat_weight_def]
QED

Theorem mat_len_default_mat[local]:
  !rows. mat_len (default_mat rows) <= mat_len rows
Proof
  Induct \\ fs [default_mat_def,mat_len_def,mat_len_append]
  \\ Cases \\ fs [default_row_def,mat_len_def]
  \\ rename [‘p::t’] \\ Cases_on ‘p’
  \\ fs [default_row_def,mat_len_def]
QED

Theorem mats_weight_spec_mats[local]:
  !cs rows ds.
    col_ctors rows = SOME ds ==>
    mats_weight (spec_mats cs rows) < mat_weight rows
Proof
  Induct \\ fs [spec_mats_def,mats_weight_def]
  >- (rw [] \\ qspecl_then [‘RefC’,‘rows’,‘ds’] mp_tac mat_weight_spec_mat_less \\ fs [])
  \\ rw [] \\ res_tac \\ fs []
  \\ imp_res_tac mat_weight_spec_mat_less \\ fs []
QED

Theorem mat_len_default_mat_less[local]:
  !r rows. r <> [] ==>
           mat_len (default_mat (r::rows)) < mat_len (r::rows)
Proof
  rpt gen_tac \\ strip_tac
  \\ qspec_then ‘rows’ mp_tac mat_len_default_mat
  \\ Cases_on ‘r’ \\ fs [default_mat_def,mat_len_def,mat_len_append]
  \\ rename [‘p::t’] \\ Cases_on ‘p’
  \\ fs [default_row_def,mat_len_def]
QED


(* -------------------------------------------------------------------- *
   The matrix algorithm and the entry point.
 * -------------------------------------------------------------------- *)

Definition exh_matrix_def:
  exh_matrix [] = F /\
  exh_matrix (r::rows) =
    (if NULL r then T else
       case col_ctors (r::rows) of
       | NONE => exh_matrix (default_mat (r::rows))
       | SOME cs => exh_mats (spec_mats cs (r::rows))) /\
  exh_mats [] = T /\
  exh_mats (m::ms) = (exh_matrix m /\ exh_mats ms)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $< LEX $<)
    (\x. case x of
         | INL rows => (mat_weight rows, mat_len rows, 0:num)
         | INR ms => (mats_weight ms, mats_len ms, LENGTH ms + 1))’
  \\ rw [mats_weight_def,mats_len_def,arithmeticTheory.MAX_DEF]
  >- (imp_res_tac mats_weight_spec_mats \\ fs [])
  \\ ‘mat_weight (default_mat (r::rows)) <= mat_weight (r::rows)’ by
       fs [mat_weight_default_mat]
  \\ Cases_on ‘mat_weight (default_mat (r::rows)) = mat_weight (r::rows)’ \\ fs []
  \\ ‘r <> []’ by (Cases_on ‘r’ \\ fs [])
  \\ imp_res_tac mat_len_default_mat_less \\ fs []
End

Definition exh_rows_def:
  exh_rows rows = exh_matrix (or_rows rows)
End


(* -------------------------------------------------------------------- *
   A fuelled version, for execution.

   exh_matrix is a mutual recursion justified by a non-structural
   measure, which cv_translation cannot take.  exh_fuel is a single
   recursion, structural in its fuel, that keeps the matrices still to be
   checked in a worklist.  It either agrees with exh_matrix or runs out
   of fuel and says F, so accepting is always safe -- exh_rows_fuel_imp
   below.  This is the version the compiler runs.
 * -------------------------------------------------------------------- *)

Definition exh_fuel_def:
  exh_fuel (n:num) ms =
    if n = 0 then F else
      case ms of
      | [] => T
      | ([]::ms) => F
      | ((r::rows)::ms) =>
          if NULL r then exh_fuel (n-1) ms else
            case col_ctors (r::rows) of
            | NONE => exh_fuel (n-1) (default_mat (r::rows) :: ms)
            | SOME cs => exh_fuel (n-1) (spec_mats cs (r::rows) ++ ms)
Termination
  WF_REL_TAC ‘measure FST’ \\ fs []
End

Definition exh_rows_fuel_def:
  exh_rows_fuel rows = exh_fuel 1000000 [or_rows rows]
End

Theorem exh_mats_append[local]:
  !xs ys. exh_mats (xs ++ ys) <=> exh_mats xs /\ exh_mats ys
Proof
  Induct \\ fs [exh_matrix_def] \\ metis_tac []
QED

Theorem exh_fuel_imp[local]:
  !n ms. exh_fuel n ms ==> exh_mats ms
Proof
  ho_match_mp_tac exh_fuel_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once exh_fuel_def]
  \\ every_case_tac
  \\ rw [] \\ gvs [exh_matrix_def]
  \\ fs [exh_mats_append]
QED

Theorem exh_rows_fuel_imp:
  exh_rows_fuel rows ==> exh_rows rows
Proof
  fs [exh_rows_fuel_def,exh_rows_def] \\ strip_tac
  \\ imp_res_tac exh_fuel_imp \\ fs [exh_matrix_def]
QED


(* ====================================================================== *
   Soundness

   The theorem to prove is the one that justifies replacing the last row
   by a wildcard:

     match refs rows v <> NONE /\ exh_rows rows ==>
     match refs rows v <> SOME MatchFailure

   Read through match_def that says: if no row type-fails on v, then some
   row succeeds on v.  Everything below is phrased in those terms, at the
   level of matrices: "ok" means no row type-fails, "hit" means some row
   succeeds.
 * ====================================================================== *)


(* ---------------------------------------------------------------------- *
   pand combines the results of two matches performed one after the
   other.  It is exactly how pmatch_list glues a row together, and it
   makes the case analysis below disappear into two rewrite rules.
 * ---------------------------------------------------------------------- *)

Definition pand_def:
  pand PMatchSuccess y = y /\
  pand PMatchFailure y = (if y = PTypeFailure then PTypeFailure
                          else PMatchFailure) /\
  pand PTypeFailure y = PTypeFailure
End

Theorem pand_simps[local,simp]:
  pand PMatchSuccess y = y /\
  pand x PMatchSuccess = x /\
  pand PTypeFailure y = PTypeFailure /\
  pand x PTypeFailure = PTypeFailure
Proof
  Cases_on ‘x’ \\ fs [pand_def]
QED

Theorem pand_eq_PTypeFailure[local,simp]:
  (pand x y = PTypeFailure) <=> x = PTypeFailure \/ y = PTypeFailure
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs [pand_def]
QED

Theorem pand_eq_PMatchSuccess[local,simp]:
  (pand x y = PMatchSuccess) <=> x = PMatchSuccess /\ y = PMatchSuccess
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs [pand_def]
QED

Theorem pand_assoc[local]:
  pand (pand x y) z = pand x (pand y z)
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ fs [pand_def]
QED

(* From here on pmatch_list is only ever unfolded through these four
   rewrites, never through pmatch_def, the raw clauses of pmatch_def
   would compete with pmatch_list_cons and leave case expressions
   behind. *)

Theorem pmatch_Any[local,simp]:
  pmatch refs Any v = PMatchSuccess
Proof
  fs [pmatch_def]
QED

Theorem pmatch_list_nil[local,simp]:
  pmatch_list refs [] [] = PMatchSuccess /\
  pmatch_list refs [] (v::vs) = PTypeFailure /\
  pmatch_list refs (p::ps) [] = PTypeFailure
Proof
  fs [pmatch_def]
QED

Theorem pmatch_list_cons[local,simp]:
  pmatch_list refs (p::ps) (v::vs) =
  pand (pmatch refs p v) (pmatch_list refs ps vs)
Proof
  fs [pmatch_def] \\ Cases_on ‘pmatch refs p v’ \\ fs [pand_def]
  \\ Cases_on ‘pmatch_list refs ps vs’ \\ fs []
QED

Theorem pmatch_list_LENGTH[local]:
  !ps vs. pmatch_list refs ps vs <> PTypeFailure ==> LENGTH ps = LENGTH vs
Proof
  Induct \\ Cases_on ‘vs’ \\ fs []
QED

Theorem pmatch_list_append[local]:
  !ps us qs ws refs.
    LENGTH ps = LENGTH us ==>
    pmatch_list refs (ps ++ qs) (us ++ ws) =
    pand (pmatch_list refs ps us) (pmatch_list refs qs ws)
Proof
  Induct \\ Cases_on ‘us’ \\ fs [pand_assoc]
QED

Theorem LENGTH_anys[local,simp]:
  !n. LENGTH (anys n) = n
Proof
  Induct \\ fs [anys_def]
QED

(* Stated with the width as an argument rather than as LENGTH as, so that
   it also rewrites the anys (ctor_arity c) that spec_row produces. *)
Theorem pmatch_list_anys[local,simp]:
  !n as refs.
    pmatch_list refs (anys n) as =
    (if LENGTH as = n then PMatchSuccess else PTypeFailure)
Proof
  Induct \\ Cases_on ‘as’ \\ fs [anys_def]
QED


(* ---------------------------------------------------------------------- *
   What the first-order list-building helpers put into their results.
 * ---------------------------------------------------------------------- *)

Theorem MEM_ctor_nub[local,simp]:
  !l x. MEM x (ctor_nub l) <=> MEM x l
Proof
  Induct \\ fs [ctor_nub_def] \\ rw [] \\ metis_tac []
QED

Theorem MEM_ctor_keep[local,simp]:
  !xs ys x. MEM x (ctor_keep xs ys) <=> MEM x xs /\ MEM x ys
Proof
  Induct \\ fs [ctor_keep_def] \\ rw [] \\ metis_tac []
QED

Theorem MEM_tag_ctors[local]:
  !sibs t a. MEM (TagC t a) (tag_ctors sibs) <=> MEM (t,a) sibs
Proof
  Induct \\ fs [tag_ctors_def,FORALL_PROD] \\ metis_tac []
QED

Theorem MEM_spec_mats[local]:
  !cs c rows. MEM c cs ==> MEM (spec_mat c rows) (spec_mats cs rows)
Proof
  Induct \\ fs [spec_mats_def] \\ metis_tac []
QED

Theorem MEM_add_head[local,simp]:
  !yss x ys. MEM ys (add_head x yss) <=> ?zs. MEM zs yss /\ ys = x::zs
Proof
  Induct \\ fs [add_head_def] \\ metis_tac []
QED

Theorem MEM_mk_prods[local,simp]:
  !xs yss zs. MEM zs (mk_prods xs yss) <=>
              ?x ys. MEM x xs /\ MEM ys yss /\ zs = x::ys
Proof
  Induct \\ fs [mk_prods_def] \\ metis_tac []
QED

Theorem MEM_mk_refs[local,simp]:
  !ps q. MEM q (mk_refs ps) <=> ?p. MEM p ps /\ q = Ref p
Proof
  Induct \\ fs [mk_refs_def] \\ metis_tac []
QED

Theorem MEM_mk_conses[local,simp]:
  !pss t q. MEM q (mk_conses t pss) <=> ?ps. MEM ps pss /\ q = Cons t ps
Proof
  Induct \\ fs [mk_conses_def] \\ metis_tac []
QED

Theorem MEM_mk_rows[local,simp]:
  !ps r. MEM r (mk_rows ps) <=> ?p. MEM p ps /\ r = [p]
Proof
  Induct \\ fs [mk_rows_def] \\ metis_tac []
QED


(* ---------------------------------------------------------------------- *
   Expanding Or-patterns.

   An expanded pattern never type-fails where the original does not, and
   if an expanded pattern matches then so does the original.  (The
   converse also holds, but soundness does not need it.)
 * ---------------------------------------------------------------------- *)

Theorem LENGTH_expand_list[local]:
  !ps qs. MEM qs (expand_list ps) ==> LENGTH qs = LENGTH ps
Proof
  Induct \\ fs [expand_def] \\ rw [] \\ res_tac \\ fs []
QED

Theorem expand_thm[local]:
  (!p q refs v.
     MEM q (expand p) /\ pmatch refs p v <> PTypeFailure ==>
     pmatch refs q v <> PTypeFailure /\
     (pmatch refs q v = PMatchSuccess ==> pmatch refs p v = PMatchSuccess)) /\
  (!ps qs refs vs.
     MEM qs (expand_list ps) /\ pmatch_list refs ps vs <> PTypeFailure ==>
     pmatch_list refs qs vs <> PTypeFailure /\
     (pmatch_list refs qs vs = PMatchSuccess ==>
      pmatch_list refs ps vs = PMatchSuccess))
Proof
  ho_match_mp_tac pattern_semanticsTheory.pat_induction \\ rpt conj_tac
  >- (* Any *) fs [expand_def]
  >- (* Cons *)
   (rw [expand_def] \\ imp_res_tac LENGTH_expand_list
    \\ Cases_on ‘v’ \\ fs [pmatch_def]
    \\ Cases_on ‘o'’ \\ Cases_on ‘o''’ \\ fs [pmatch_def]
    \\ TRY (Cases_on ‘x’) \\ fs [pmatch_def]
    \\ rw [] \\ rfs [] \\ res_tac \\ fs [])
  >- (* Or: both branches must be free of type failures, and once that
           is known the induction hypotheses apply directly *)
   (rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ ‘pmatch refs p v <> PTypeFailure /\ pmatch refs p' v <> PTypeFailure’ by
         (qpat_x_assum ‘pmatch refs (Or _ _) _ <> _’ mp_tac
          \\ fs [pmatch_def] \\ every_case_tac \\ fs [])
    \\ fs [expand_def] \\ res_tac \\ fs [pmatch_def]
    \\ Cases_on ‘pmatch refs p v’ \\ Cases_on ‘pmatch refs p' v’ \\ fs [])
  >- (* Lit *) fs [expand_def]
  >- (* Ref *)
   (fs [expand_def] \\ rw []
    \\ Cases_on ‘v’ \\ fs [pmatch_def]
    \\ Cases_on ‘FLOOKUP refs n’ \\ fs [pmatch_def] \\ res_tac \\ fs [])
  >- (* [] *) fs [expand_def]
  \\ (* p::ps *)
  fs [expand_def] \\ rw []
  \\ Cases_on ‘vs’ \\ fs [] \\ res_tac \\ fs []
QED


(* ---------------------------------------------------------------------- *
   The constructor of a value, and its arguments.

   dest_val is only defined for the values that a constructor pattern can
   possibly match; literals and Other have no constructor.  Note that a
   reference has a constructor only when the pointer is in the heap,
   which is exactly when Ref does not type-fail.
 * ---------------------------------------------------------------------- *)

Definition dest_val_def:
  dest_val refs (Term (SOME t) vs) = SOME (TagC t (LENGTH vs), vs) /\
  dest_val refs (Term NONE vs) = SOME (TupC (LENGTH vs), vs) /\
  dest_val refs (RefPtr r) = (case FLOOKUP refs r of
                              | NONE => NONE
                              | SOME w => SOME (RefC,[w])) /\
  dest_val refs (Litv l) = NONE /\
  dest_val refs Other = NONE
End

Theorem dest_val_eq_SOME[local]:
  dest_val refs v = SOME (c,as) <=>
  (?t. v = Term (SOME t) as /\ c = TagC t (LENGTH as)) \/
  (v = Term NONE as /\ c = TupC (LENGTH as)) \/
  (?r w. v = RefPtr r /\ FLOOKUP refs r = SOME w /\ as = [w] /\ c = RefC)
Proof
  Cases_on ‘v’ \\ fs [dest_val_def]
  >- (Cases_on ‘o'’ \\ fs [dest_val_def] \\ metis_tac [])
  \\ CASE_TAC \\ fs [] \\ metis_tac []
QED

Theorem LENGTH_dest_val[local]:
  dest_val refs v = SOME (c,as) ==> LENGTH as = ctor_arity c
Proof
  fs [dest_val_eq_SOME] \\ rw [] \\ fs [ctor_arity_def]
QED

(* A head pattern that reports a constructor set really does confine a
   value that it does not type-fail on to that set. *)

Theorem ctors_of_thm[local]:
  ctors_of p = SOME xs /\ pmatch refs p v <> PTypeFailure ==>
  ?c as. dest_val refs v = SOME (c,as) /\ MEM c xs
Proof
  Cases_on ‘p’ \\ fs [ctors_of_def]
  >- (* Cons *)
   (Cases_on ‘o'’ \\ fs [ctors_of_def]
    >- (* a tuple pattern: the value is a tuple of the same width *)
     (Cases_on ‘v’ \\ fs [pmatch_def]
      \\ Cases_on ‘o'’ \\ fs [pmatch_def,dest_val_def]
      \\ strip_tac \\ imp_res_tac pmatch_list_LENGTH \\ gvs [])
    \\ (* a tagged pattern: the value's tag/arity is either the pattern's
          own or, since pmatch did not type-fail, one of the siblings *)
    Cases_on ‘x’ \\ Cases_on ‘r’ \\ fs [ctors_of_def]
    \\ Cases_on ‘v’ \\ fs [pmatch_def]
    \\ Cases_on ‘o'’ \\ fs [pmatch_def,dest_val_def]
    \\ strip_tac \\ gvs [MEM_tag_ctors]
    \\ Cases_on ‘q = x' /\ LENGTH l = LENGTH l'’ \\ fs [is_sibling_def]
    \\ Cases_on ‘MEM (x',LENGTH l') x’ \\ fs [])
  \\ (* Ref: the pointer must be in the heap, or Ref would type-fail *)
  Cases_on ‘v’ \\ fs [pmatch_def]
  \\ Cases_on ‘FLOOKUP refs n’ \\ fs [pmatch_def,dest_val_def]
QED

(* ... and therefore so does the intersection over a whole column. *)

Theorem col_ctors_thm[local]:
  !M cs refs v vs.
    col_ctors M = SOME cs /\
    EVERY (\r. pmatch_list refs r (v::vs) <> PTypeFailure) M ==>
    ?c as. dest_val refs v = SOME (c,as) /\ MEM c cs
Proof
  ho_match_mp_tac col_ctors_ind \\ rw [col_ctors_def]
  \\ Cases_on ‘ctors_of p’ \\ fs [ctor_inter_def]
  >- (* the head pattern says nothing, so the rest of the column decides *)
        (res_tac \\ fs [])
  \\ (* otherwise the value's constructor is in the head pattern's set, and
        also -- by induction -- in the set of the rest of the column *)
  drule_all ctors_of_thm \\ strip_tac
  \\ Cases_on ‘col_ctors M’ \\ fs [ctor_inter_def]
  \\ res_tac \\ gvs []
QED


(* ---------------------------------------------------------------------- *
   Specialising and defaulting preserve match results.

   This is the one fact that makes the whole induction go through: every
   row of a transformed matrix gives exactly the same three-valued match
   result, against the transformed value vector, as the row it came from
   does against the original one.  Rows that are dropped simply have no
   counterpart, which costs nothing here -- dropping rows can only make a
   matrix less exhaustive, and soundness is the direction we need.
 * ---------------------------------------------------------------------- *)

Theorem spec_row_thm[local]:
  !c r row refs v vs as.
    dest_val refs v = SOME (c,as) /\ MEM row (spec_row c r) ==>
    pmatch_list refs row (as ++ vs) = pmatch_list refs r (v::vs)
Proof
  ho_match_mp_tac spec_row_ind \\ rw [spec_row_def]
  \\ TRY (PairCases_on ‘ts’)
  \\ imp_res_tac LENGTH_dest_val
  \\ gvs [dest_val_eq_SOME,pmatch_list_append,ctor_arity_def,pmatch_def]
  \\ every_case_tac \\ fs [pand_def]
QED

Theorem spec_mat_MEM[local]:
  !M c as refs v vs row.
    dest_val refs v = SOME (c,as) /\ MEM row (spec_mat c M) ==>
    ?r. MEM r M /\
        pmatch_list refs row (as ++ vs) = pmatch_list refs r (v::vs)
Proof
  Induct \\ fs [spec_mat_def] \\ rw []
  >- (drule_all spec_row_thm \\ metis_tac [])
  \\ res_tac \\ metis_tac []
QED

Theorem default_row_thm[local]:
  !r row refs v vs.
    MEM row (default_row r) ==>
    pmatch_list refs row vs = pmatch_list refs r (v::vs)
Proof
  ho_match_mp_tac default_row_ind \\ rw [default_row_def]
QED

Theorem default_mat_MEM[local]:
  !M refs v vs row.
    MEM row (default_mat M) ==>
    ?r. MEM r M /\ pmatch_list refs row vs = pmatch_list refs r (v::vs)
Proof
  Induct \\ fs [default_mat_def] \\ rw []
  >- (drule default_row_thm \\ metis_tac [])
  \\ res_tac \\ metis_tac []
QED


(* ---------------------------------------------------------------------- *
   Soundness of the matrix algorithm.

   "ok" (no row type-fails) is inherited by the sub-matrices, and "hit"
   (some row succeeds) is reflected back out of them.
 * ---------------------------------------------------------------------- *)

Theorem exh_matrix_thm[local]:
  (!M refs vs.
     exh_matrix M /\ EVERY (\r. pmatch_list refs r vs <> PTypeFailure) M ==>
     EXISTS (\r. pmatch_list refs r vs = PMatchSuccess) M) /\
  (!ms m refs vs.
     exh_mats ms /\ MEM m ms /\
     EVERY (\r. pmatch_list refs r vs <> PTypeFailure) m ==>
     EXISTS (\r. pmatch_list refs r vs = PMatchSuccess) m)
Proof
  ho_match_mp_tac exh_matrix_ind \\ rpt conj_tac
  >- (* the empty matrix is never accepted *) fs [exh_matrix_def]
  >-
   (rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ qpat_x_assum ‘exh_matrix _’ mp_tac
    \\ simp [Once exh_matrix_def]
    \\ Cases_on ‘NULL r’ \\ fs []
    >- (* a row of width zero: the value vector must be empty too, and
             then that row matches *)
     (Cases_on ‘r’ \\ fs [] \\ Cases_on ‘vs’ \\ fs [])
    \\ ‘?v vs'. vs = v::vs'’ by
         (Cases_on ‘vs’ \\ fs [] \\ Cases_on ‘r’ \\ fs [])
    \\ gvs []
    \\ Cases_on ‘col_ctors (r::rows)’ \\ fs []
    >- (* nothing is known about the column, so only the wildcard rows
             can be relied on: work in the default matrix *)
     (strip_tac
      \\ first_x_assum (qspecl_then [‘refs’,‘vs'’] mp_tac)
      \\ impl_tac
      >- (fs [EVERY_MEM] \\ rw []
             \\ drule default_mat_MEM
             \\ disch_then (qspecl_then [‘refs’,‘v’,‘vs'’] strip_assume_tac)
             \\ gvs [] \\ res_tac \\ fs [])
      \\ fs [EXISTS_MEM] \\ rw []
      \\ drule default_mat_MEM
      \\ disch_then (qspecl_then [‘refs’,‘v’,‘vs'’] strip_assume_tac)
      \\ gvs [] \\ metis_tac [])
    \\ (* the column's constructors are known, so the value has one of
          them: work in the matrix specialised for it *)
    strip_tac
    \\ ‘EVERY (\r. pmatch_list refs r (v::vs') <> PTypeFailure) (r::rows)’ by fs []
    \\ drule_all col_ctors_thm \\ strip_tac
    \\ first_x_assum
         (qspecl_then [‘spec_mat c (r::rows)’,‘refs’,‘as ++ vs'’] mp_tac)
    \\ impl_tac
    >- (fs [MEM_spec_mats,EVERY_MEM] \\ rw []
           \\ drule_all spec_mat_MEM
           \\ disch_then (qspec_then ‘vs'’ strip_assume_tac)
           \\ gvs [] \\ res_tac \\ fs [])
    \\ fs [EXISTS_MEM] \\ rw []
    \\ drule_all spec_mat_MEM
    \\ disch_then (qspec_then ‘vs'’ strip_assume_tac)
    \\ gvs [] \\ metis_tac [])
  >- fs []
  \\ fs [exh_matrix_def] \\ rw [] \\ fs [] \\ res_tac
QED


(* ---------------------------------------------------------------------- *
   From the matrix back to match.
 * ---------------------------------------------------------------------- *)

Theorem match_no_PTypeFailure[local]:
  !rows. match refs rows v <> NONE ==>
         EVERY (\ (p,e). pmatch refs p v <> PTypeFailure) rows
Proof
  Induct \\ fs [match_def,FORALL_PROD] \\ rw []
  \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem match_EXISTS[local]:
  !rows. match refs rows v <> NONE /\
         EXISTS (\ (p,e). pmatch refs p v = PMatchSuccess) rows ==>
         match refs rows v <> SOME MatchFailure
Proof
  Induct \\ fs [match_def,FORALL_PROD] \\ rw []
  \\ Cases_on ‘pmatch refs p_1 v’ \\ fs []
  \\ every_case_tac \\ fs []
QED

Theorem or_rows_ok[local]:
  !rows. EVERY (\ (p,e). pmatch refs p v <> PTypeFailure) rows ==>
         EVERY (\r. pmatch_list refs r [v] <> PTypeFailure) (or_rows rows)
Proof
  Induct \\ fs [or_rows_def,FORALL_PROD] \\ rw []
  \\ fs [EVERY_MEM] \\ rw [] \\ fs []
  \\ drule_all (CONJUNCT1 expand_thm) \\ fs []
QED

Theorem or_rows_hit[local]:
  !rows. EVERY (\ (p,e). pmatch refs p v <> PTypeFailure) rows /\
         EXISTS (\r. pmatch_list refs r [v] = PMatchSuccess) (or_rows rows) ==>
         EXISTS (\ (p,e). pmatch refs p v = PMatchSuccess) rows
Proof
  Induct \\ fs [or_rows_def,FORALL_PROD] \\ rw []
  \\ fs [EXISTS_MEM] \\ rw [] \\ fs []
  >- (drule_all (CONJUNCT1 expand_thm) \\ fs [])
  \\ metis_tac []
QED


(* ---------------------------------------------------------------------- *
   Soundness of exh_rows: the theorem the pattern compiler needs.
 * ---------------------------------------------------------------------- *)

Theorem exh_rows_thm:
  match refs rows v <> NONE /\ exh_rows rows ==>
  match refs rows v <> SOME MatchFailure
Proof
  strip_tac
  \\ irule match_EXISTS \\ fs []
  \\ drule match_no_PTypeFailure \\ strip_tac
  \\ irule or_rows_hit \\ fs []
  \\ irule (CONJUNCT1 exh_matrix_thm)
  \\ fs [or_rows_ok] \\ fs [exh_rows_def]
QED
