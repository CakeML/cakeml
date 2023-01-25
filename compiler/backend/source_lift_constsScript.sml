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

Definition annotate_exp_def:
  (annotate_exp (t:string list) n (ast$Lit l) =
     (Constant (Lit l),n,str_empty)) ∧
  (annotate_exp t n (Con cn es) =
     let (es,n,fvs) = annotate_exps t n es in
       if EVERY is_Constant es then
         (Constant (Con cn es),n,fvs)
       else (Con cn es,n,fvs)) ∧
  (annotate_exp t n (Fun x e) =
     let (e,n,fvs1) = annotate_exp (x :: t) n e in
     let fvs = delete fvs1 (implode x) in
       if disjoint t fvs then
         (Constant (Fun x e),n,fvs)
       else
         (Fun x e,n,fvs)) ∧
  (annotate_exp t n (ast$Letrec funs e) =
     let names = MAP FST funs in
     let (funs1,n,fvs1) = annotate_funs (names ++ t) n funs in
     let (e,n,fvs) = annotate_exp (names ++ t) n e in
       (Letrec funs1 e,n, delete_all names (union fvs fvs1))) ∧
  (annotate_exp t n (Var x) =
     case x of
     | Short vname => (Var x,bump (implode vname) n,insert str_empty (implode vname) ())
     | _ => (Var x,n,str_empty)) ∧
  (annotate_exp t n (ast$App op es) =
     let (es,n,fvs) = annotate_exps t n es in
       (App op es,n,fvs)) ∧
  (annotate_exp t n (Log lop e1 e2) =
     let (e1,n,fvs1) = annotate_exp t n e1 in
     let (e2,n,fvs2) = annotate_exp t n e2 in
       (Log lop e1 e2,n,union fvs1 fvs2)) ∧
  (annotate_exp t n (If e1 e2 e3) =
     let (e1,n,fvs1) = annotate_exp t n e1 in
     let (e2,n,fvs2) = annotate_exp t n e2 in
     let (e3,n,fvs3) = annotate_exp t n e3 in
       (If e1 e2 e3,n,union fvs1 $ union fvs2 fvs3)) ∧
  (annotate_exp t n (Let (SOME x) e1 e2) =
     let (e1,n,fvs1) = annotate_exp t n e1 in
     let (e2,n,fvs2) = annotate_exp t n e2 in
       (Let (SOME x) e1 e2,n,union fvs1 (delete fvs2 (implode x)))) ∧
  (annotate_exp t n (Let NONE e1 e2) =
     let (e1,n,fvs1) = annotate_exp t n e1 in
     let (e2,n,fvs2) = annotate_exp t n e2 in
       (Let NONE e1 e2,n,union fvs1 fvs2)) ∧
  (annotate_exp t n (Raise e) =
     let (e,n,fvs) = annotate_exp t n e in
       (Raise e,n,fvs)) ∧
  (annotate_exp t n (Mat e pes) =
     let (e,n,fvs) = annotate_exp t n e in
     let (pes,n,fvs1) = annotate_pes t n pes in
       (Mat e pes,n,union fvs fvs1)) ∧
  (annotate_exp t n (Handle e pes) =
     let (e,n,fvs) = annotate_exp t n e in
     let (pes,n,fvs1) = annotate_pes t n pes in
       (Handle e pes,n,union fvs fvs1)) ∧
  (annotate_exp t n (Tannot e _) = annotate_exp t n e) ∧
  (annotate_exp t n (Lannot e _) = annotate_exp t n e) ∧
  (annotate_exp t n (FpOptimise sc e) = annotate_exp t n e) /\
  (* -- boilerplate -- *)
  (annotate_exps t n [] = ([],n,str_empty)) ∧
  (annotate_exps t n (e::es) =
     let (e,n,fvs) = annotate_exp t n e in
     let (es,n,fvs1) = annotate_exps t n es in
       (e::es,n,union fvs fvs1)) ∧
  (annotate_pes t n [] = ([],n,str_empty)) ∧
  (annotate_pes t n ((p,e)::pes) =
     let pbs = pat_bindings p [] in
     let (e,n,fvs) = annotate_exp (pbs ++ t) n e in
     let fvs' = delete_all pbs fvs in
     let (pes,n,fvs1) = annotate_pes t n pes in
       ((p,e)::pes,n,union fvs' fvs1)) ∧
  (annotate_funs t n [] = ([],n,str_empty)) ∧
  (annotate_funs t n ((f,x,e)::funs) =
     let (e,n,fvs) = annotate_exp (x :: t) n e in
     let fvs' = delete fvs (implode x) in
     let (funs,n,fvs1) = annotate_funs t n funs in
       ((f,x,e)::funs,n,union fvs' fvs1))
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL (t,x,e) => exp_size e
   | INR (INL (t,x,es)) => list_size exp_size es
   | INR (INR (INL (t,x,pes))) =>
       list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR (t,x,funs))) =>
       list_size (pair_size (list_size char_size)
                  (pair_size (list_size char_size) exp_size)) funs’
End

(* --------------------------------------------------------- *
    Pass 2
 * --------------------------------------------------------- *)

(* TODO:
 - be careful about Equality, don't pull out a constant that's
   an operand to Equality
 - make it recurse into the lifted constants?
 - make it not split curried functions
*)

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

Definition lift_exp_def:
  (lift_exp allow xs n (Tannot e _) =
     if allow then
       if is_trivial e then
         (e,n,xs)
       else
         let new_name = make_name n in
           (Var (Short (explode new_name)),n+1,(new_name,e)::xs)
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
     let (es,n,xs) = lift_exps allow xs n es in
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
  make_local l xs d =
    if NULL xs then d else
      Dlocal (MAP (λ(n,e). Dlet l (Pvar (explode n)) e) (REVERSE xs)) [d]
End

Definition compile_dec_def:
  compile_dec (Dlet l p e) =
    (let (e,n,fvs) = annotate_exp [] (bump_pat 0 p) e in
     let (e,n,xs) = lift_exp F [] n e in
       make_local l xs (Dlet l p e)) ∧
  compile_dec (Dletrec l funs) =
    (let names = MAP FST funs in
     let (funs,n,fvs) = annotate_funs names (bump_all names 0) funs in
     let (funs,n,xs) = lift_funs T [] n funs in
       make_local l xs (Dletrec l funs)) ∧
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

val _ = export_theory ();
