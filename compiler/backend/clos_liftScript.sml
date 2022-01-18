(*
  Lift constant expressions to a large Block stored in a mutable global.
  This optimisation only fires within function bodies (inside Fn and Letrec).
*)
open preamble closLangTheory clos_annotateTheory clos_opTheory;

val _ = new_theory "clos_lift";
val _ = set_grammar_ancestry ["closLang","clos_annotate","backend_common"];

Definition trivial_op_def:
  trivial_op op xs =
    case clos_op$dest_Const op of
    | SOME i => (-1000000 < i ∧ i < 1000000)
    | NONE =>
      case clos_op$dest_Cons op of
      | SOME t => NULL xs
      | NONE => F
End

Definition lift_def:
  (lift (b:bool) [] n acc = ([],n:num,acc:exp list)) /\
  (lift b ((x:closLang$exp)::y::xs) n acc =
     let (c1,n,acc) = lift b [x] n acc in
     let (c2,n,acc) = lift b (y::xs) n acc in
       (c1 ++ c2,n,acc)) /\
  (lift b [Var t v] n acc = ([Var t v], n, acc)) /\
  (lift b [If t x1 x2 x3] n acc =
     let (c1,n,acc) = lift b [x1] n acc in
     let (c2,n,acc) = lift b [x2] n acc in
     let (c3,n,acc) = lift b [x3] n acc in
       ([If t (HD c1) (HD c2) (HD c3)],n,acc)) /\
  (lift b [Let t xs x2] n acc =
     if b ∧ t = IsConstant then
       ([Op t (ElemAt n) [Op t GlobalsPtr []]],n+1,Let t xs x2 :: acc)
     else
       let (c1,n,acc) = lift b xs n acc in
       let (c2,n,acc) = lift b [x2] n acc in
         ([Let t c1 (HD c2)],n,acc)) /\
  (lift b [Raise t x1] n acc =
     let (c1,n,acc) = lift b [x1] n acc in
       ([Raise t (HD c1)],n,acc)) /\
  (lift b [Tick t x1] n acc =
     let (c1,n,acc) = lift b [x1] n acc in
       ([Tick t (HD c1)],n,acc)) /\
  (lift b [Op t op xs] n acc =
     if b ∧ t = IsConstant ∧ ¬(trivial_op op xs) then
       ([Op t (ElemAt n) [Op t GlobalsPtr []]],n+1,Op t op xs :: acc)
     else
       let (c1,n,acc) = lift b xs n acc in
         ([Op t op c1],n,acc)) /\
  (lift b [App t loc_opt x1 xs2] n acc =
     let (c1,n,acc) = lift b [x1] n acc in
     let (c2,n,acc) = lift b xs2 n acc in
       ([App t loc_opt (HD c1) c2],n,acc)) /\
  (lift b [Fn t loc _ num_args x1] n acc =
     let (c1,n,acc) = lift T [x1] n acc in
       ([Fn t loc NONE num_args (HD c1)],n,acc)) /\
  (lift b [Letrec t loc _ fns x1] n acc =
     let (c1,n,acc) = lift T (MAP SND fns) n acc in
     let (c2,n,acc) = lift b [x1] n acc in
       ([Letrec t loc NONE (ZIP (MAP FST fns, c1)) (HD c2)],n,acc)) /\
  (lift b [Handle t x1 x2] n acc =
     let (c1,n,acc) = lift b [x1] n acc in
     let (c2,n,acc) = lift b [x2] n acc in
       ([Handle t (HD c1) (HD c2)],n,acc)) /\
  (lift b [Call t ticks dest xs] n acc =
     let (c1,n,acc) = lift b xs n acc in
       ([Call t ticks dest c1],n,acc))
Termination
  WF_REL_TAC `measure (list_size exp_size o FST o SND)`
  \\ fs [exp_size_eq] \\ rw []
  \\ qsuff_tac ‘list_size exp_size (MAP SND fns) ≤ list_size (pair_size (λx. x) exp_size) fns’
  \\ fs [] \\ Induct_on ‘fns’ \\ fs [list_size_def,FORALL_PROD,basicSizeTheory.pair_size_def]
End

Definition set_mutable_def:
  set_mutable n n1 vs =
    if NULL vs then [] else
      if n = 0 then
        [Op None SetGlobalsPtr [Op None (Cons 0) vs]]
      else
        [] (* hmm, ConsExtend isn't quite right here *)
End

Definition lift_compile_inc_def:
  lift_compile_inc (n:num) (exps:exp list) =
    let (xs,_) = alt_free exps in
    let (ys,n1,acc) = lift F xs n [] in
      (n1, set_mutable n n1 (REVERSE acc) ++ ys)
End

Definition compile_def:
  compile (n:num) ((p,l):clos_prog) =
    let (n,p) = lift_compile_inc 0 p in
      (n,(p,l))
End

val _ = export_theory()
