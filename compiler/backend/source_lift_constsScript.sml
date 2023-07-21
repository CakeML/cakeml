(*
  This is a source-to-source transformation that lifts constants
  from within function expressions to top-level local-declarations.

  This optimisation is implemented as two passes over the input.

    1. The first pass performs a bottom-up annotation of the
       expressions, where every subexpression that is a constant will
       be wrapped in a Tannot. This bottom-up pass also collects data
       that can be used to generate fresh names. This pass does not
       change the semantics of the expressions it traverses.

    2. The second pass performs a top-down walk, where it lifts out
       any Tannot experssion that appears within a function body. Each
       lifted expression is given a new name. At the top-level, a new
       Dlocal is introduced if any new local expression definitions
       need to be made.

 *)

open preamble astTheory mlmapTheory mlstringTheory;

val _ = new_theory "source_lift_consts";

val _ = set_grammar_ancestry ["ast", "mlstring", "mlmap", "misc"];

(* --------------------------------------------------------- *
    Set up for handling variable sets and fresh names
 * --------------------------------------------------------- *)

Definition str_empty_def:
  str_empty = mlmap$empty mlstring$compare
End

Overload constant_prefix[local] = “strlit "constant_"”

Definition bump_def:
  bump new_name n =
    if isPrefix constant_prefix new_name then
      MAX n (strlen new_name + 1)
    else n
End

Definition bump_all_def:
  bump_all [] n = n ∧
  bump_all (x::xs) n = bump_all xs (bump (implode x) n)
End

Definition bump_pat_def:
  bump_pat n Pany = (n:num) ∧
  bump_pat n (Pvar vname) = bump (implode vname) n ∧
  bump_pat n (Plit l) = n ∧
  bump_pat n (Pref p) = bump_pat n p ∧
  bump_pat n (Pas p x) = bump_pat n p ∧
  bump_pat n (Ptannot p y) = bump_pat n p ∧
  bump_pat n (Pcon _ ps) = bump_pats n ps ∧
  bump_pats n [] = n ∧
  bump_pats n (p::ps) = bump_pats (bump_pat n p) ps
End

Definition delete_all_def:
  delete_all [] s = s ∧
  delete_all (n::ns) s = delete (delete_all ns s) (implode n)
End

Definition disjoint_def:
  disjoint [] s = T ∧
  disjoint (n::ns) s = case lookup s (implode n) of
                       | NONE => disjoint ns s
                       | SOME (_:unit) => F
End

(* --------------------------------------------------------- *
    Pass 1
 * --------------------------------------------------------- *)

Overload Constant[local] = “λe. ast$Tannot e (Attup [])”

Definition is_Constant_def:
  is_Constant (Tannot _ _) = T ∧
  is_Constant _ = F
End

Definition dest_Constant_def:
  dest_Constant (Tannot e _) = SOME e ∧
  dest_Constant _ = NONE
End

Definition max_list_def:
  (max_list [] = 0) ∧
  (max_list (x::xs) = MAX x (max_list xs))
End

Definition is_Fun_def:
  is_Fun (Fun _ _) = T ∧
  is_Fun _ = F
End

Definition no_const_fun_def:
  no_const_fun e =
    case dest_Constant e of
    | NONE => e
    | SOME e1 => if is_Fun e1 then e1 else e
End

Definition annotate_exp_def:
  (annotate_exp (t:string list) (ast$Lit l) =
     (Constant (Lit l),0,str_empty)) ∧
  (annotate_exp t (Con cn es) =
     let (es,n,fvs) = annotate_exps t es in
       if EVERY is_Constant es then
         (Constant (Con cn es),n,fvs)
       else (Con cn es,n,fvs)) ∧
  (annotate_exp t (Fun x e) =
     let (e,n,fvs1) = annotate_exp (x :: t) e in
     let fvs = delete fvs1 (implode x) in
       if disjoint t fvs then
         (Constant (Fun x (no_const_fun e)),n,fvs)
       else
         (Fun x (no_const_fun e),n,fvs)) ∧
  (annotate_exp t (ast$Letrec funs e) =
     let names = MAP FST funs in
     let (funs1,n,fvs1) = annotate_funs (names ++ t) funs in
     let (e,n',fvs) = annotate_exp (names ++ t) e in
       (Letrec funs1 e,MAX n n',
         delete_all names (union fvs fvs1))) ∧
  (annotate_exp t (Var x) =
     case x of
     | Short vname =>
        (Var x, bump (implode vname) 0,
          insert str_empty (implode vname) ())
     | _ => (Var x,0,str_empty)) ∧
  (annotate_exp t (ast$App op es) =
     let (es,n,fvs) = annotate_exps t es in
       (App op es,n,fvs)) ∧
  (annotate_exp t (Log lop e1 e2) =
     let (e1,n1,fvs1) = annotate_exp t e1 in
     let (e2,n2,fvs2) = annotate_exp t e2 in
       (Log lop e1 e2,MAX n1 n2,union fvs1 fvs2)) ∧
  (annotate_exp t (If e1 e2 e3) =
     let (e1,n1,fvs1) = annotate_exp t e1 in
     let (e2,n2,fvs2) = annotate_exp t e2 in
     let (e3,n3,fvs3) = annotate_exp t e3 in
       (If e1 e2 e3,MAX n1 (MAX n2 n3),
         union fvs1 $ union fvs2 fvs3)) ∧
  (annotate_exp t (Let (SOME x) e1 e2) =
     let (e1,n1,fvs1) = annotate_exp t e1 in
     let (e2,n2,fvs2) = annotate_exp (x::t) e2 in
       (Let (SOME x) e1 e2, MAX n1 n2,
         union fvs1 (delete fvs2 (implode x)))) ∧
  (annotate_exp t (Let NONE e1 e2) =
     let (e1,n1,fvs1) = annotate_exp t e1 in
     let (e2,n2,fvs2) = annotate_exp t e2 in
       (Let NONE e1 e2, MAX n1 n2,
         union fvs1 fvs2)) ∧
  (annotate_exp t (Raise e) =
     let (e,n,fvs) = annotate_exp t e in
       (Raise e,n,fvs)) ∧
  (annotate_exp t (Mat e pes) =
     let (e,n,fvs) = annotate_exp t e in
     let (pes,n',fvs1) = annotate_pes t pes in
       (Mat e pes,MAX n n',
         union fvs fvs1)) ∧
  (annotate_exp t (Handle e pes) =
     let (e,n,fvs) = annotate_exp t e in
     let (pes,n',fvs1) = annotate_pes t pes in
       (Handle e pes,MAX n n',
         union fvs fvs1)) ∧
  (annotate_exp t (Tannot e _) = annotate_exp t e) ∧
  (annotate_exp t (Lannot e _) = annotate_exp t e) ∧
  (annotate_exp t (FpOptimise sc e) = annotate_exp t e) /\
  (* -- boilerplate -- *)
  (annotate_exps t [] = ([],0,str_empty)) ∧
  (annotate_exps t (e::es) =
     let (e,n,fvs) = annotate_exp t e in
       if NULL es then
         ([e],n,fvs)
       else
         let (es,n',fvs1) = annotate_exps t es in
           (e::es,MAX n n',union fvs fvs1)) ∧
  (annotate_pes t [] = ([],0,str_empty)) ∧
  (annotate_pes t ((p,e)::pes) =
     let pbs = pat_bindings p [] in
     let (e,n,fvs) = annotate_exp (pbs ++ t) e in
     let fvs' = delete_all pbs fvs in
     let (pes,n',fvs1) = annotate_pes t pes in
       ((p,e)::pes,MAX n n',union fvs' fvs1)) ∧
  (annotate_funs t [] = ([],0,str_empty)) ∧
  (annotate_funs t ((f,x,e)::funs) =
     let (e,n,fvs) = annotate_exp (x :: t) e in
     let fvs' = delete fvs (implode x) in
     let (funs,n',fvs1) = annotate_funs t funs in
       ((f,x,e)::funs,MAX n n',union fvs' fvs1))
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL (t,e) => exp_size e
   | INR (INL (t,es)) => list_size exp_size es
   | INR (INR (INL (t,pes))) =>
       list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR (t,funs))) =>
       list_size (pair_size (list_size char_size)
                  (pair_size (list_size char_size) exp_size)) funs’
End

(* --------------------------------------------------------- *
    Pass 2
 * --------------------------------------------------------- *)

Definition is_trivial_def:
  is_trivial (Con _ es) = NULL es ∧
  is_trivial (Lit l) =
    (case l of
     | IntLit i => -2**31 < i ∧ i < 2**31
     | Char c => T
     | Word8 b => T
     | _ => F) ∧
   is_trivial _ = F
End

Definition make_name_def:
  make_name n =
    constant_prefix ^ implode (REPLICATE n #"_")
End

Definition allow_lift_def:
  allow_lift op (es:exp list) ⇔
    op ≠ Equality
    (* TODO: make also flag Opapp of Var (Short "=") *)
End

Definition lift_exp_def:
  (lift_exp allow xs n (Tannot e _) =
     if allow then
       if is_trivial e then
         (e,n,xs)
       else
         let (e1,n1,xs1) = lift_exp F xs n e in
         let new_name = make_name n1 in
           (Var (Short (explode new_name)),n1+1,(new_name,e1)::xs1)
     else lift_exp allow xs n e) ∧
  (lift_exp allow xs n (ast$Lit l) =
     (Lit l,n,xs)) ∧
  (lift_exp allow xs n (Con cn es) =
     let (es,n,xs) = lift_exps allow xs n es in
       (Con cn es,n,xs)) ∧
  (lift_exp allow xs n (Fun x e) =
     let (e,n,xs) = lift_exp T xs n e in
       (Fun x e,n,xs)) ∧
  (lift_exp allow xs n (ast$Letrec funs e) =
     let (funs,n,xs) = lift_funs T xs n funs in
     let (e,n,xs) = lift_exp allow xs n e in
       (Letrec funs e,n,xs)) ∧
  (lift_exp allow xs n (Var v) =
    (Var v,n,xs)) ∧
  (lift_exp allow xs n (ast$App op es) =
     let (es,n,xs) = lift_exps (allow ∧ allow_lift op es) xs n es in
       (App op es,n,xs)) ∧
  (lift_exp allow xs n (Log lop e1 e2) =
     let (e1,n,xs) = lift_exp allow xs n e1 in
     let (e2,n,xs) = lift_exp allow xs n e2 in
       (Log lop e1 e2,n,xs)) ∧
  (lift_exp allow xs n (If e1 e2 e3) =
     let (e1,n,xs) = lift_exp allow xs n e1 in
     let (e2,n,xs) = lift_exp allow xs n e2 in
     let (e3,n,xs) = lift_exp allow xs n e3 in
       (If e1 e2 e3,n,xs)) ∧
  (lift_exp allow xs n (Let (SOME x) e1 e2) =
     let (e1,n,xs) = lift_exp allow xs n e1 in
     let (e2,n,xs) = lift_exp allow xs n e2 in
       (Let (SOME x) e1 e2,n,xs)) ∧
  (lift_exp allow xs n (Let NONE e1 e2) =
     let (e1,n,xs) = lift_exp allow xs n e1 in
     let (e2,n,xs) = lift_exp allow xs n e2 in
       (Let NONE e1 e2,n,xs)) ∧
  (lift_exp allow xs n (Raise e) =
     let (e,n,xs) = lift_exp allow xs n e in
       (Raise e,n,xs)) ∧
  (lift_exp allow xs n (Mat e pes) =
     let (e,n,xs) = lift_exp allow xs n e in
     let (pes,n,xs) = lift_pes allow xs n pes in
       (Mat e pes,n,xs)) ∧
  (lift_exp allow xs n (Handle e pes) =
     let (e,n,xs) = lift_exp allow xs n e in
     let (pes,n,xs) = lift_pes allow xs n pes in
       (Handle e pes,n,xs)) ∧
  (lift_exp allow xs n (Lannot e _) = lift_exp allow xs n e) ∧
  (lift_exp allow xs n (FpOptimise sc e) = lift_exp allow xs n e) ∧
  (* -- boilerplate -- *)
  (lift_exps allow xs n [] = ([],n,xs)) ∧
  (lift_exps allow xs n (e::es) =
     let (e,n,xs) = lift_exp allow xs n e in
     let (es,n,xs) = lift_exps allow xs n es in
       (e::es,n,xs)) ∧
  (lift_pes allow xs n [] = ([],n,xs)) ∧
  (lift_pes allow xs n ((p,e)::pes) =
     let (e,n,xs) = lift_exp allow xs n e in
     let (pes,n,xs) = lift_pes allow xs n pes in
       ((p,e)::pes,n,xs)) ∧
  (lift_funs allow xs n [] = ([],n,xs)) ∧
  (lift_funs allow xs n ((f,x,e)::funs) =
     let (e,n,xs) = lift_exp T xs n e in
     let (funs,n,xs) = lift_funs allow xs n funs in
       ((f,x,e)::funs,n,xs))
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL (t,xs,x,e) => exp_size e
   | INR (INL (t,xs,x,es)) => list_size exp_size es
   | INR (INR (INL (t,xs,x,pes))) =>
       list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR (t,xs,x,funs))) =>
       list_size (pair_size (list_size char_size)
                  (pair_size (list_size char_size) exp_size)) funs’
End

(* --------------------------------------------------------- *
    Putting it all together
 * --------------------------------------------------------- *)

Definition make_local_def:
  make_local xs d =
    if NULL xs then d else
      Dlocal (MAP (λ(n,e).
        Dlet unknown_loc (Pvar (explode n)) e) (REVERSE xs)) [d]
End

Definition compile_dec_def:
  compile_dec (Dlet l p e) =
    (let (e,n,fvs) = annotate_exp [] e in
     let np = MAX n (bump_pat 0 p) in
     let (e,n,xs) = lift_exp F [] (MAX n np) e in
       make_local xs (Dlet l p e)) ∧
  compile_dec (Dletrec l funs) =
    (let names = MAP FST funs in
     let (funs,n,fvs) = annotate_funs names funs in
    let np = MAX n (bump_all names 0) in
     let (funs,n,xs) = lift_funs T [] np funs in
       make_local xs (Dletrec l funs)) ∧
  compile_dec (Dtype l tds) = Dtype l tds ∧
  compile_dec (Dtabbrev l x y z) = Dtabbrev l x y z ∧
  compile_dec (Dexn l x y) = Dexn l x y ∧
  compile_dec (Denv v) = Denv v ∧
  compile_dec (Dmod m ds) = Dmod m (compile_decs ds) ∧
  compile_dec (Dlocal xs ys) = Dlocal (compile_decs xs) (compile_decs ys) ∧
  compile_decs [] = [] ∧
  compile_decs (d::ds) = compile_dec d :: compile_decs ds
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL x => dec_size y
                            | INR y => list_size dec_size x’
End

Theorem map_ok_str_empty_cmp:
  map_ok str_empty ∧
  cmp_of str_empty = compare
Proof
  fs [str_empty_def,mlmapTheory.empty_thm,mlstringTheory.TotOrd_compare]
QED

Theorem map_ok_delete_all_cmp:
  ∀ls m.
    (map_ok m ⇒ map_ok (delete_all ls m)) ∧
    cmp_of (delete_all ls m) = cmp_of m
Proof
  Induct>>rw[delete_all_def]>>
  metis_tac[delete_thm]
QED

Theorem map_ok_annotate_exp_cmp:
  (∀t e.
    map_ok (SND (SND (annotate_exp t e))) ∧
    cmp_of (SND (SND (annotate_exp t e))) = compare
  ) ∧
  (∀t es.
    map_ok (SND (SND (annotate_exps t es))) ∧
    cmp_of (SND (SND (annotate_exps t es))) = compare
  ) ∧
  (∀t pes.
    map_ok (SND (SND (annotate_pes t pes))) ∧
    cmp_of (SND (SND (annotate_pes t pes))) = compare
  ) ∧
  (∀t funs.
    map_ok (SND (SND (annotate_funs t funs))) ∧
    cmp_of (SND (SND (annotate_funs t funs))) = compare
  )
Proof
  ho_match_mp_tac annotate_exp_ind>>
  rw[annotate_exp_def,map_ok_str_empty_cmp]>>
  rpt(pairarg_tac>>fs[])>>every_case_tac>>
  rw[map_ok_str_empty_cmp]
  >- metis_tac[delete_thm]
  >- metis_tac[delete_thm]
  >- metis_tac[map_ok_delete_all_cmp,union_thm]
  >- metis_tac[map_ok_delete_all_cmp,union_thm]
  >- metis_tac[insert_thm,map_ok_str_empty_cmp]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm,delete_thm,cmp_of_delete]
  >- metis_tac[union_thm,delete_thm,cmp_of_delete]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[union_thm]
  >- metis_tac[map_ok_delete_all_cmp,union_thm]
  >- metis_tac[map_ok_delete_all_cmp,union_thm]
  >- metis_tac[union_thm,delete_thm,cmp_of_delete]
  >- metis_tac[union_thm,delete_thm,cmp_of_delete]
QED

Definition map_eq_def:
  map_eq (map1:('a,'b) map) (map2:('a,'b) map) ⇔
  to_fmap map1 = to_fmap map2
End

Theorem annotate_exps_CONS:
  annotate_exp t x = (e,n,fv1) ∧
  annotate_exps t xs = (es,n',fv2) ⇒
  ∃fvs.
    annotate_exps t (x::xs) = (e::es, MAX n n', fvs) ∧
    map_eq fvs (union fv1 fv2)
Proof
  rw[annotate_exp_def]>>
  Cases_on`xs`>>gvs[annotate_exp_def,map_eq_def]>>
  DEP_REWRITE_TAC
    (CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM] mlmapTheory.union_thm))>>
  CONJ_TAC>- (
    simp[map_ok_str_empty_cmp]>>
    metis_tac[map_ok_annotate_exp_cmp,SND,PAIR])>>
  EVAL_TAC>>
  metis_tac[FUNION_FEMPTY_2]
QED

Theorem map_eq_trans:
  map_eq a b ∧
  map_eq b c ⇒
  map_eq a c
Proof
  rw[map_eq_def]
QED

Theorem map_eq_cong:
  map_eq a a' ∧
  map_eq b b' ∧
  map_eq a' b' ⇒
  map_eq a b
Proof
  rw[map_eq_def]
QED

Theorem annotate_exps_APPEND:
  ∀xs' xn xfvs.
  annotate_exps t xs = (xs',xn,xfvs) ∧
  annotate_exps t ys = (ys',yn,yfvs) ⇒
  ∃fvs.
    annotate_exps t (xs ++ ys) = (xs'++ys', MAX xn yn, fvs) ∧
    map_eq fvs (union xfvs yfvs)
Proof
  Induct_on`xs`
  >- (
    simp[map_eq_def]>>
    rw[annotate_exp_def]>>
    DEP_REWRITE_TAC
      (CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM] mlmapTheory.union_thm))>>
    CONJ_TAC>- (
      simp[map_ok_str_empty_cmp]>>
      metis_tac[map_ok_annotate_exp_cmp,SND,PAIR])>>
    EVAL_TAC>>
    metis_tac[FUNION_FEMPTY_1])>>
  rw[]>>
  qpat_x_assum`_ _ (h::xs) = _ `mp_tac>>
  simp[Once annotate_exp_def]>>
  rpt(pairarg_tac>>fs[])>>rw[]
  >- (
    Cases_on`xs`>>fs[]>>
    metis_tac[annotate_exps_CONS])>>
  drule annotate_exps_CONS>>
  last_x_assum assume_tac>>
  disch_then drule>>
  rw[]>>simp[]>>
  CONJ_TAC >-
    rw[MAX_DEF]>>
  drule map_eq_trans>>
  disch_then match_mp_tac>>
  last_x_assum mp_tac>>
  simp[map_eq_def]>>
  DEP_REWRITE_TAC
      (CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM] mlmapTheory.union_thm))>>
  CONJ_TAC>- (
    metis_tac[map_ok_annotate_exp_cmp,SND,PAIR])>>
  CONJ_TAC>- (
    metis_tac[map_ok_annotate_exp_cmp,SND,PAIR])>>
  simp[FUNION_ASSOC]
QED

Theorem FUNION_UNIT_COMM:
  FUNION (f1 : 'a |-> unit) (f2 : 'a |-> unit) =
  FUNION f2 f1
Proof
  Induct_on`f1`>>rw[]>>
  simp[FUNION_FUPDATE_1,FUNION_FUPDATE_2]>>
  rw[]
  >- (
    last_x_assum SUBST_ALL_TAC>>
    match_mp_tac FUPDATE_ELIM>>
    fs[])
  >- metis_tac[]
QED

Theorem annotate_exps_REVERSE:
  ∀es t es' n fvs.
  annotate_exps t es = (es',n,fvs) ⇒
  ∃fvs'.
    annotate_exps t (REVERSE es) = (REVERSE es', n, fvs') ∧
    map_eq fvs fvs'
Proof
  Induct
  >- (
    rw[annotate_exp_def]>>
    EVAL_TAC)>>
  rw[]>>
  `∃a1 b1 c1 a2 b2 c2.
    annotate_exps t es = (a2,b2,c2) ∧
    annotate_exps t [h] = (a1,b1,c1)` by metis_tac[PAIR]>>
  drule annotate_exps_APPEND>>
  qpat_x_assum`_ _ es = _` assume_tac>>
  disch_then drule>>
  rw[]>>
  last_x_assum drule>>rw[]>>
  drule annotate_exps_APPEND>>
  qpat_x_assum`_ _ [h] = _` assume_tac>>
  disch_then drule>>
  rw[]>>simp[]>>
  CONJ_TAC >- (
    fs[annotate_exp_def]>>
    rpt(pairarg_tac>>fs[])>>gvs[])>>
  CONJ_TAC >-
    rw[MAX_DEF]>>
  rpt(qpat_x_assum`map_eq _ _` mp_tac)>>
  simp[map_eq_def]>>
  DEP_REWRITE_TAC
      (CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM] mlmapTheory.union_thm))>>
  CONJ_TAC>- (
    metis_tac[map_ok_annotate_exp_cmp,SND,PAIR])>>
  rw[]>>
  metis_tac[FUNION_ASSOC,FUNION_UNIT_COMM]
QED

(* --------------------------------------------------------- *
    Some simple sanity tests
 * --------------------------------------------------------- *)

Triviality test1: (* no lift outside of closures *)
  compile_dec (Dlet unknown_loc (Pvar "a") (Con NONE [Lit (IntLit 1); Lit (IntLit 2)]))
  =
  Dlet unknown_loc (Pvar "a") (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])
Proof
  EVAL_TAC
QED

Triviality test2: (* constants lifted from within closures *)
  compile_dec (Dlet unknown_loc (Pvar "a")
    (Fun "a" (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])))
  =
  Dlocal
     [Dlet unknown_loc (Pvar "constant_") (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet unknown_loc (Pvar "a") (Fun "a" (Var (Short "constant_")))]
Proof
  EVAL_TAC
QED

Triviality test3: (* constants are *not* lifted under Equality *)
  compile_dec
    (Dlet unknown_loc (Pvar "a")
      (Fun "a" (App Equality [Var (Short "a");
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
    (Dlet unknown_loc (Pvar "a")
      (Fun "a" (App Equality [Var (Short "a");
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
Proof
  EVAL_TAC
QED

Triviality test4: (* constants are lifted under App *)
  compile_dec
    (Dlet unknown_loc (Pvar "a")
      (Fun "a" (App ListAppend [Var (Short "a");
                                Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
  Dlocal
     [Dlet unknown_loc (Pvar "constant_")
        (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet unknown_loc (Pvar "a")
        (Fun "a" (App ListAppend [Var (Short "a"); Var (Short "constant_")]))]
Proof
  EVAL_TAC
QED

Triviality test5: (* curried functions are not taken apart *)
  compile_dec
    (Dlet unknown_loc (Pvar "a") (Fun "a" (Fun "b" (Lit (IntLit 5)))))
  =
  Dlet unknown_loc (Pvar "a") (Fun "a" (Fun "b" (Lit (IntLit 5))))
Proof
  EVAL_TAC
QED

Triviality test6: (* constants from within closures are lifted *)
  compile_dec
    (Dlet unknown_loc (Pvar "a") (Fun "a" (Con NONE [Fun "b" (Lit (IntLit 5))])))
  =
  Dlocal
     [Dlet unknown_loc (Pvar "constant_")
        (Con NONE [Fun "b" (Lit (IntLit 5))])]
     [Dlet unknown_loc (Pvar "a")
        (Fun "a" (Var (Short "constant_")))]
Proof
  EVAL_TAC
QED

val _ = export_theory ();
