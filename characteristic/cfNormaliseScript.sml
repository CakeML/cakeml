(*
  Defines the normalise_prog function which puts an arbitrary program
  in A-normal form.
*)
Theory cfNormalise
Ancestors
  set_sep ml_translator semanticPrimitives cfHeaps cfStore
  evaluate ASCIInumbers
Libs
  preamble helperLib ConseqConv cfHeapsBaseLib cfTacticsBaseLib

(*------------------------------------------------------------------*)
(** The [cf] function assumes that programs are in "normal form"
    (which is close to ANF). These lemmas exploit the fact that some
    program is in normal form.

    The [cfNormaliseLib.normalise_prog] function puts an arbitrary
    program in normal form.
*)

Definition exp2v_def:
  exp2v _ (Lit l) = SOME (Litv l) /\
  exp2v env (Var name) = nsLookup env.v name /\
  exp2v _ _ = NONE
End

Theorem exp2v_evaluate:
   !e env st v. exp2v env e = SOME v ==>
    evaluate st env [e] = (st, Rval [v])
Proof
  Induct \\ fs [exp2v_def, evaluate_def]
QED

Definition exp2v_list_def:
  exp2v_list env [] = SOME [] /\
  exp2v_list env (x :: xs) =
    (case exp2v env x of
      | NONE => NONE
      | SOME v =>
        (case exp2v_list env xs of
          | NONE => NONE
          | SOME vs => SOME (v :: vs)))
End

Theorem exp2v_list_evaluate:
   !l lv env st. exp2v_list env l = SOME lv ==>
    evaluate st env l = (st, Rval lv)
Proof
  Induct
  THEN1 (fs [exp2v_list_def, evaluate_def])
  THEN1 (
    rpt strip_tac \\ fs [exp2v_list_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ progress exp2v_evaluate \\
    Cases_on `l` \\ fs [evaluate_def]
  )
QED

Theorem evaluate_rcons:
   !env st st' st'' l x lv v.
     evaluate st env l = (st', Rval lv) /\
     evaluate st' env [x] = (st'', Rval [v]) ==>
     evaluate st env (l ++ [x]) = (st'', Rval (lv ++ [v]))
Proof
  Induct_on `l`
  THEN1 (
    rpt strip_tac \\ fs [evaluate_def]
  )
  THEN1 (
    rpt strip_tac \\ fs [evaluate_def] \\
    Cases_on `l` \\ fs []
    THEN1 (
      fs [evaluate_def] \\
      last_assum (fn t =>
        progress_with t
          (CONJ_PAIR evaluatePropsTheory.evaluate_length |> fst)) \\
      fs [LENGTH_EQ_NUM_compute]
    )
    THEN1 (
      qpat_x_assum `evaluate _ _ (_::_::_) = _`
        (assume_tac o REWRITE_RULE [evaluate_def]) \\
      every_case_tac \\ fs [] \\ rw [] \\ first_assum progress \\
      simp [evaluate_def]
    )
  )
QED

Theorem exp2v_list_REVERSE:
   !l (st: 'ffi semanticPrimitives$state) lv env. exp2v_list env l = SOME lv ==>
    evaluate st env (REVERSE l) = (st, Rval (REVERSE lv))
Proof
  Induct \\ rpt gen_tac \\ disch_then (assume_tac o GSYM) \\
  fs [exp2v_list_def, evaluate_def] \\
  every_case_tac \\ fs [] \\ rw [] \\ irule evaluate_rcons \\
  metis_tac [exp2v_evaluate]
QED

Theorem exp2v_list_rcons:
   !xs x l env.
     exp2v_list env (xs ++ [x]) = SOME l ==>
     ?xvs xv.
       l = xvs ++ [xv] /\
       exp2v_list env xs = SOME xvs /\
       exp2v env x = SOME xv
Proof
  Induct_on `xs` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\
  first_assum progress \\ fs [] \\ rw []
QED

Theorem exp2v_list_LENGTH:
   !l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv
Proof
  Induct_on `l` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ res_tac \\ fs [] \\ rw []
QED

(* [dest_opapp]: destruct an n-ary application. *)
Definition dest_opapp_def:
  dest_opapp (App Opapp l) =
       (case l of
          | [f; x] =>
            (case dest_opapp f of
               | SOME (f', args) => SOME (f', args ++ [x])
               | NONE => SOME (f, [x]))
          | _ => NONE) /\
  dest_opapp _ = NONE
End

(*------------------------------------------------------------------*)

(*
(* Old implementation of the normalisation pass, as a HOL function.
   It has been replaced by the ML implementation in
   [cfNormaliseLib.sml], see this file for more details.
*)

(* [mk_opapp]: construct an n-ary application. *)
Definition mk_opapp_def:
  mk_opapp xs =
    if LENGTH xs < 2 then HD xs else
      App Opapp [mk_opapp (FRONT xs); LAST xs]
Termination
  WF_REL_TAC `measure LENGTH`
  \\ fs [LENGTH_FRONT] \\ Cases \\ fs []
End

Theorem MEM_exp_size[local]:
  !args a. MEM a args ==> exp_size a <= exp6_size args
Proof
  Induct \\ fs [astTheory.exp_size_def] \\ rw [] \\ res_tac \\ fs []
QED

Theorem MEM_exp1_size[local]:
  !rs. MEM (v,a,e') rs ==> exp_size e' < exp1_size rs
Proof
  Induct \\ fs [astTheory.exp_size_def] \\ rw [] \\ res_tac \\ fs []
  \\ fs [astTheory.exp_size_def]
QED

Theorem exp6_size_lemma[local]:
  !xs ys. exp6_size (xs ++ ys) = exp6_size xs + exp6_size ys
Proof
  Induct \\ fs [astTheory.exp_size_def]
QED

Theorem dest_opapp_size[local]:
  !xs p_1 p_2.
      dest_opapp xs = SOME (p_1,p_2) ==>
      exp_size p_1 + exp6_size p_2 < exp_size xs
Proof
  recInduct (theorem "dest_opapp_ind") \\ fs [dest_opapp_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [astTheory.exp_size_def]
  \\ res_tac \\ fs [exp6_size_lemma,astTheory.exp_size_def]
QED

Definition get_name_aux_def:
  get_name_aux n vs =
    let v = "t" ++ num_toString n in
      if MEM v vs then get_name_aux (n+1) (FILTER (\x. v <> x) vs) else v
Termination
  WF_REL_TAC `measure (\(n,vs). LENGTH vs)`
  \\ rw [] \\ fs [MEM_SPLIT,FILTER_APPEND]
  \\ match_mp_tac (DECIDE ``m <= m1 /\ n <= n1 ==> m + n < m1 + (n1 + 1n)``)
  \\ fs [LENGTH_FILTER_LEQ]
End

val alpha = EVAL ``GENLIST (\n. CHR (n + ORD #"a")) 26`` |> concl |> rand

Definition alpha_def:
  alpha = ^alpha
End

(* [get_name vs] returns a fresh name given a list [vs] of already
   used names. *)
Definition get_name_def:
  get_name vs =
    let ws = FILTER (\s. ~(MEM [s] vs)) alpha in
      if NULL ws then get_name_aux 0 vs else [HD ws]
End

(* [Lets [(n1, x1); ...; (nm, xm)] e] is the sequence of Lets:

   let n1 = x1 in
   let n2 = x2 in
   ...
   let nm = xm in
   e
*)
Definition Lets_def:
  Lets [] e = e /\
  Lets ((n,x)::xs) e = Let (SOME n) x (Lets xs e)
End

Definition wrap_if_needed_def:
  wrap_if_needed needs_wrapping ns e b =
    if needs_wrapping then (
      let x = get_name ns in
      (Var (Short x), x::ns, SNOC (x,e) b)
    ) else (
      (e, ns, b)
    )
End

Definition strip_annot_pat_def:
  strip_annot_pat (Pvar v) = Pvar v /\
  strip_annot_pat (Plit l) = Plit l /\
  strip_annot_pat (Pcon c xs) = Pcon c (strip_annot_pat_list xs) /\
  strip_annot_pat (Pref a) = Pref (strip_annot_pat a) /\
  strip_annot_pat (Ptannot p _) = strip_annot_pat p /\
  strip_annot_pat Pany = Pany /\
  strip_annot_pat_list [] = [] /\
  strip_annot_pat_list (x::xs) =
    strip_annot_pat x :: strip_annot_pat_list xs
End

Definition strip_annot_exp_def:
  (strip_annot_exp (Raise e) =
    ast$Raise (strip_annot_exp e))
  ∧
  (strip_annot_exp (Handle e pes) =
    Handle (strip_annot_exp e) (strip_annot_pes pes))
  ∧
  (strip_annot_exp (ast$Lit l) = Lit l)
  ∧
  (strip_annot_exp (Con cn es) = Con cn (strip_annot_exps es))
  ∧
  (strip_annot_exp (Var x) = Var x)
  ∧
  (strip_annot_exp (Fun x e) =
    Fun x (strip_annot_exp e))
  ∧
  (strip_annot_exp (App op es) =
    App op (strip_annot_exps es))
  ∧
  (strip_annot_exp (Log lop e1 e2) =
    Log lop (strip_annot_exp e1) (strip_annot_exp e2))
  ∧
  (strip_annot_exp (If e1 e2 e3) =
    If (strip_annot_exp e1)
       (strip_annot_exp e2)
       (strip_annot_exp e3))
  ∧
  (strip_annot_exp (Mat e pes) =
    Mat (strip_annot_exp e) (strip_annot_pes pes))
  ∧
  (strip_annot_exp (Let (SOME x) e1 e2) =
    Let (SOME x) (strip_annot_exp e1) (strip_annot_exp e2))
  ∧
  (strip_annot_exp (Let NONE e1 e2) =
    Let NONE (strip_annot_exp e1) (strip_annot_exp e2))
  ∧
  (strip_annot_exp (Letrec funs e) =
      Letrec (strip_annot_funs funs) (strip_annot_exp e))
  ∧
  (strip_annot_exp (Tannot e t) = strip_annot_exp e)
  ∧
  (strip_annot_exp (Lannot e l) = strip_annot_exp e)
  ∧
  (strip_annot_exps [] = [])
  ∧
  (strip_annot_exps (e::es) =
     strip_annot_exp e :: strip_annot_exps es)
  ∧
  (strip_annot_pes [] = [])
  ∧
  (strip_annot_pes ((p,e)::pes) =
    (strip_annot_pat p, strip_annot_exp e)
    :: strip_annot_pes pes)
  ∧
  (strip_annot_funs [] = [])
  ∧
  (strip_annot_funs ((f,x,e)::funs) =
    (f,x,strip_annot_exp e) :: strip_annot_funs funs)
Termination
  WF_REL_TAC `inv_image $< (\x. case x of INL e => exp_size e
                                 | INR (INL es) => exps_size es
                                 | INR (INR (INL pes)) => pes_size pes
                                 | INR (INR (INR funs)) => funs_size funs)` >>
   srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]
End

(*
Definition norm_def:
  norm (is_named: bool) (as_value: bool) (ns: string list) (Lit l) = (Lit l, ns, ([]: (string # exp) list)) /\
  norm is_named as_value ns (Var (Short name)) = (Var (Short name), name::ns, []) /\
  norm is_named as_value ns (Var long) = (Var long, ns, []) /\
  norm is_named as_value ns (Let opt e1 e2) =
    (case opt of
         SOME x =>
         (let (e1',ns,b1) = norm T F ns e1 in
          let (e2',ns) = protect F (x::ns) e2 in
          let e' = Lets b1 (Lets [(x, e1')] e2') in
          wrap_if_needed as_value ns e' [])
       | NONE =>
         (let (e1', ns, b1) = norm F F ns e1 in
          let (e2', ns) = protect F ns e2 in
          wrap_if_needed as_value ns (Let NONE e1' e2') b1)) /\
  norm is_named as_value ns (App Opapp args) =
    (case dest_opapp (App Opapp args) of
         SOME (f, args) =>
         (let (f', ns, b0) = norm F T ns f in
          let (args', ns, bi) = norm_list F T ns args in
          let e' = mk_opapp (f' :: args') in
          let b' = FLAT (REVERSE (b0 :: bi)) (* right-to-left evaluation *) in
          wrap_if_needed as_value ns e' b')
       | NONE => ARB) /\
  norm is_named as_value ns (App op args) =
    (let (args', ns, bi) = norm_list F T ns args in
     let b' = FLAT (REVERSE bi) in (* right-to-left evaluation *)
     wrap_if_needed as_value ns (App op args') b') /\
  norm is_named as_value ns (Con x args) =
    (let (args', ns, bi) = norm_list F T ns args in
     let b = FLAT (REVERSE bi) in (* right-to-left evaluation *)
     wrap_if_needed as_value ns (Con x args') b) /\
  norm is_named as_value ns (Raise e) =
    (let (e',ns,b) = norm F T ns e in
     wrap_if_needed as_value ns (Raise e') b) /\
  norm is_named as_value ns (Log l e1 e2) =
    (let (e1', n1, b1) = norm F T ns e1 in
     let (e2', n2, b2) = norm F T n1 e2 in
     if b2 = [] then (
       if b1 = [] then (
         (* produce: <e1> op <e2> *)
         (Log l e1' e2', n2, [])
       ) else (
         (* produce: let <b1> in <e1> op <e2> *)
         wrap_if_needed as_value n2 (Log l e1' e2') b1
       )
     ) else (
       let (e2', n2, b2) = norm F F n1 e2 in
       case l of
           Andalso =>
           (* produce: let <b1> in <e1'> andalso (lets <b2> in <e2'>) *)
           wrap_if_needed as_value n2 (Log Andalso e1' (Lets b2 e2')) b1
         | Orelse =>
           (* produce: let <b1> in <e1'> orelse (let <b2> in <e2'>) *)
           wrap_if_needed as_value n2 (Log Orelse e1' (Lets b2 e2')) b1
     )) /\
  norm is_named as_value ns (Fun v e) =
    (let (e', ns) = protect is_named (v::ns) e in
     wrap_if_needed (as_value \/ ~is_named) ns (Fun v e') []) /\
  norm is_named as_value ns (Mat e1 e2) =
    (let (e1',n1,b1) = norm F T ns e1 in
     let (rows', ni) = norm_rows n1 e2 in
     let e' = Mat e1' rows' in
     wrap_if_needed as_value ni e' b1) /\
  norm is_named as_value ns (Handle e1 e2) =
    (let (e1',n1) = protect F ns e1 in
     let (rows', ni) = norm_rows n1 e2 in
     let e' = Handle e1' rows' in
     wrap_if_needed as_value ni e' []) /\
  norm is_named as_value ns (If e1 e2 e3) =
    (let (e1', ns, b) = norm F T ns e1 in
     let (e2', ns) = protect F ns e2 in
     let (e3', ns) = protect F ns e3 in
     wrap_if_needed as_value ns (If e1' e2' e3') b) /\
  norm is_named as_value ns (Letrec rs e) =
    (let (rs', ns) = norm_letrec_branches ns rs in
     let (e', ns) = protect F ns e in
     wrap_if_needed as_value ns (Letrec rs' e') []) /\
  norm is_named as_value ns (Tannot e _) =
    norm is_named as_value ns e /\
  norm is_named as_value ns (Lannot e _) =
    norm is_named as_value ns e /\
  norm_list is_named as_value ns ([]: exp list) = ([], ns, []) /\
  norm_list is_named as_value ns (e::es) =
    (let (e', ns, b) = norm is_named as_value ns e in
     let (es', ns, bs) = norm_list is_named as_value ns es in
     (e' :: es', ns, b::bs)) /\
  norm_rows ns ([]: (pat, exp) alist) = ([], ns) /\
  norm_rows ns (row :: rows) =
    (let (row', ns) = protect_row F ns row in
     let (rows', ns) = norm_rows ns rows in
     (row' :: rows', ns)) /\
  norm_letrec_branches ns ([]: (string, string # exp) alist) = ([], ns) /\
  norm_letrec_branches ns (branch :: branches) =
    (let (branch', ns) = protect_letrec_branch T ns branch in
     let (branches', ns) = norm_letrec_branches ns branches in
     (branch' :: branches', ns)) /\
  protect is_named ns e =
    (let (e',ns,b) = norm is_named F ns e in
     (Lets b e', ns)) /\
  protect_row is_named ns row =
    (let (row_e', ns) = protect is_named ns (SND row) in
     ((FST row, row_e'), ns)) /\
  protect_letrec_branch is_named ns branch =
    (let (branch_e', ns) = protect is_named ns (SND (SND branch)) in
     ((FST branch, FST (SND branch), branch_e'), ns))
Termination
  ...
End
(* TODO: prove the termination of [norm]. This is probably a bit tricky and
   requires refactoring the way [norm] is defined. *)
*)

Definition full_normalise_def:
  full_normalise ns e = FST (protect T ns (strip_annot_exp e))
End

Theorem MEM_v_size[local]:
  !xs. MEM a xs ==> v_size a < v7_size xs
Proof
  Induct  \\ fs [v_size_def] \\ rw [] \\ res_tac \\ fs []
QED

Definition norm_exp_rel_def:
  norm_exp_rel ns e1 e2 <=> (e1 = e2) \/
                            (full_normalise ns e1 = e2)
End

Definition free_in_def:
  (* TODO: complete *)
  free_in (Lit l) v = T /\
  free_in (Var w) v = (w = v) /\
  free_in (Let NONE e1 e2) v = (free_in e1 v \/ free_in e2 v) /\
  free_in (Let (SOME x) e1 e2) v = (free_in e1 v \/ (free_in e2 v /\ v <> Short x))
End

Inductive norm_rel:
  (!i.
     norm_rel (Litv i) (Litv i)) /\
  (!i.
     norm_rel (Loc i) (Loc i)) /\
  (!xs ys.
     EVERY2 norm_rel xs ys ==>
     norm_rel (Vectorv xs) (Vectorv ys)) /\
  (!xs ys t.
     EVERY2 norm_rel xs ys ==>
     norm_rel (Conv t xs) (Conv t ys)) /\
  (!v env1 env2 ns e1 e2.
     norm_exp_rel ns e1 e2 /\ (free_in e1 = free_in e2) /\
     env_rel (free_in e1 DELETE Short v1) env1 env2 ==>
     norm_rel (Closure env1 v e1) (Closure env2 v e2)) /\
  (!v env1 env2 ns es1 es2.
     EVERY2 (\(n1,v1,e1) (n2,v2,e2).
       n1 = n2 /\ v1 = v2 /\ norm_exp_rel ns e1 e2 /\ (free_in e1 = free_in e2) /\
       env_rel (free_in e1 DELETE Short v1) env1 env2) es1 es2 ==>
     norm_rel (Recclosure env1 es1 v) (Recclosure env2 es2 v)) /\
  (!env1 env2 s.
     (!v x y. v IN s /\
              nsLookup env1.v v = SOME x /\
              nsLookup env2.v v = SOME y ==>
              norm_rel x y) ==>
     env_rel s env1 env2)
End

Inductive norm_ref_rel:
  (!v1 v2. norm_rel v1 v2 ==> norm_ref_rel (Refv v1) (Refv v2)) /\
  (!v1 v2. EVERY2 norm_rel v1 v2 ==> norm_ref_rel (Varray v1) (Varray v2)) /\
  (!b. norm_ref_rel (W8array b) (W8array b))
End

Inductive norm_res_rel:
  (!v1 v2. norm_rel v1 v2 ==> norm_res_rel (Rval v1) (Rval v2)) /\
  (!v1 v2. norm_rel v1 v2 ==> norm_res_rel (Rerr (Rraise v1)) (Rerr (Rraise v2))) /\
  (!a. norm_rel v1 v2 ==> norm_res_rel (Rerr (Rabort a)) (Rerr (Rabort a)))
End

Definition norm_state_rel_def:
  norm_state_rel s1 s2 <=>
     s1.clock = s2.clock ∧
     EVERY2 norm_ref_rel s1.refs s2.refs ∧
     s1.ffi = s2.ffi ∧
     s1.defined_types = s2.defined_types ∧
     s1.defined_mods = s2.defined_mods
End

(*
Theorem full_normalise_correct:
   env_rel (free_in e) env1 env2 /\ norm_state_rel s1 s2 /\
    evaluate ck env1 s1 e1 (rs1,res1) /\ norm_exp_rel e1 e2 ==>
    ?rs2 res2. evaluate ck env2 s2 e2 (rs2,res2) /\
               norm_state_rel rs1 rs2 /\ norm_res_rel res1 res2
Proof
  ...
QED TODO
*)

Definition full_normalise_exp_def:
  full_normalise_exp exp = full_normalise [] exp
End

Definition full_normalise_decl_def:
  full_normalise_decl (Dlet locs pat exp) =
    Dlet locs pat (full_normalise [] exp) /\
  full_normalise_decl (Dletrec locs l) =
    Dletrec locs (MAP (\ (f, n, e). (f, n, full_normalise [f; n] e)) l) /\
  full_normalise_decl decl = decl
End

Definition full_normalise_top_def:
  full_normalise_top (Tdec decl) = Tdec (full_normalise_decl decl) /\
  full_normalise_top top = top
End

Definition full_normalise_prog_def:
  full_normalise_prog prog = MAP full_normalise_top prog
End

*)
