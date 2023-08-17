(*
  This is file implements a "smart" version of ClosLang's Op
  constructor. When possible, this smart constructor breaks
  the operation into faster separate operators.
*)
open preamble closLangTheory;

val _ = new_theory "clos_op";

val _ = set_grammar_ancestry ["closLang","backend_common","misc"]

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* matchers *)

Definition dest_Const_def:
  dest_Const (Const i) = SOME i ∧
  dest_Const _ = NONE
End

Theorem dest_Const_pmatch:
  dest_Const x = case x of Const i => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_Constant_def:
  dest_Constant (Constant (ConstStr c)) = SOME (Str c) ∧
  dest_Constant (Constant (ConstInt c)) = SOME (Int c) ∧
  dest_Constant (Constant (ConstWord64 c)) = SOME (W64 c) ∧
  dest_Constant _ = NONE
End

Theorem dest_Constant_pmatch:
  dest_Constant x = case x of
                    | Constant (ConstStr c) => SOME (Str c)
                    | Constant (ConstInt c) => SOME (Int c)
                    | Constant (ConstWord64 c) => SOME (W64 c)
                    | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
  \\ Cases_on ‘c’ \\ fs [dest_Constant_def]
QED

Definition dest_Cons_def:
  dest_Cons (closLang$Cons i) = SOME i ∧
  dest_Cons _ = NONE
End

Theorem dest_Cons_pmatch:
  dest_Cons x = case x of Cons i => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_ElemAt_def:
  dest_ElemAt (ElemAt i) = SOME i ∧
  dest_ElemAt _ = NONE
End

Theorem dest_ElemAt_pmatch:
  dest_ElemAt x = case x of ElemAt i => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_TagEq_def:
  dest_TagEq (TagEq i) = SOME i ∧
  dest_TagEq _ = NONE
End

Theorem dest_TagEq_pmatch:
  dest_TagEq x = case x of TagEq i => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_LenEq_def:
  dest_LenEq (LenEq i) = SOME i ∧
  dest_LenEq _ = NONE
End

Theorem dest_LenEq_pmatch:
  dest_LenEq x = case x of LenEq i => SOME i | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_TagLenEq_def:
  dest_TagLenEq (TagLenEq i j) = SOME (i,j) ∧
  dest_TagLenEq _ = NONE
End

Theorem dest_TagLenEq_pmatch:
  dest_TagLenEq x = case x of TagLenEq i j => SOME (i,j) | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_Op_def:
  dest_Op f (Op t op xs) =
    (dtcase f op of
     | NONE => NONE
     | SOME i => SOME (i,xs)) ∧
  dest_Op f _ = NONE
End

Theorem dest_Op_pmatch:
  dest_Op f x =
    case x of Op t op xs =>
      (dtcase f op of
       | NONE => NONE
       | SOME i => SOME (i,xs))
    | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition dest_Op_Nil_def:
  dest_Op_Nil f x =
    dtcase dest_Op f x of
    | NONE => NONE
    | SOME (i,xs) => if NULL xs then SOME i else NONE
End

Overload dest_Op_Cons[local]     = “dest_Op dest_Cons”
Overload dest_Op_Cons_Nil[local] = “dest_Op_Nil dest_Cons”
Overload dest_Op_Const[local]    = “dest_Op_Nil dest_Const”
Overload dest_Op_Constant[local]    = “dest_Op_Nil dest_Constant”

Definition dest_Op_Consts_def:
  dest_Op_Consts x y =
    dtcase dest_Op_Const x of
    | NONE => NONE
    | SOME i =>
      dtcase dest_Op_Const y of
      | NONE => NONE
      | SOME j => SOME (i,j)
End

Definition MakeBool_def:
  MakeBool b = closLang$Op None (Cons (if b then 1 else 0)) []
End

Definition MakeInt_def:
  MakeInt i = Op None (Const i) []
End

Definition int_op_def:
  int_op op i j =
    if op = Add then SOME (MakeInt (j+i)) else
    if op = Sub then SOME (MakeInt (j-i)) else
    if op = Mult then SOME (MakeInt (j*i)) else
    if op = Div then SOME (MakeInt (if i = 0 then 0 else j / i)) else
    if op = Mod then SOME (MakeInt (if i = 0 then 0 else j % i)) else
    if op = Less then SOME (MakeBool (j < i)) else
    if op = LessEq then SOME (MakeBool (j ≤ i)) else
    if op = Greater then SOME (MakeBool (i < j)) else
    if op = GreaterEq then SOME (MakeBool (i ≤ j)) else
    if op = Equal then SOME (MakeBool (j = i)) else NONE
End

Definition cons_op_def:
  cons_op op t xs =
    dtcase dest_ElemAt op of
    | SOME n => (if n < LENGTH xs then
                   SOME (Let None xs (Var None (LENGTH xs - (n + 1))))
                 else NONE)
    | NONE =>
    dtcase dest_TagLenEq op of
    | SOME (n,l) => SOME (Let None xs (MakeBool (n = t ∧ LENGTH xs = l)))
    | NONE =>
    dtcase dest_TagEq op of
    | SOME n => SOME (Let None xs (MakeBool (n = t)))
    | NONE =>
    dtcase dest_LenEq op of
    | SOME l => SOME (Let None xs (MakeBool (LENGTH xs = l)))
    | NONE => NONE
End

Definition is_Var_def:
  is_Var (Var _ _) = T ∧
  is_Var _ = F
End

Theorem is_Var_pmatch:
  is_Var x = case x of Var _ _ => T | _ => F
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘x’ \\ EVAL_TAC
QED

Definition eq_direct_nil_def:
  eq_direct_nil x y =
    dtcase dest_Op_Cons_Nil x of
    | SOME i =>
        (dtcase dest_Op_Cons_Nil y of
         | SOME j => SOME (MakeBool (i = j))
         | NONE => SOME (Op None (TagLenEq i 0) [y]))
    | NONE =>
        (dtcase dest_Op_Cons_Nil y of
         | SOME i => SOME (Op None (TagLenEq i 0) [x])
         | NONE => NONE)
End

Definition eq_direct_const_def:
  eq_direct_const x y =
    dtcase dest_Op_Const x of
    | SOME i =>
        (dtcase dest_Op_Const y of
         | SOME j => SOME (MakeBool (i = j))
         | NONE => SOME (Op None (EqualConst (Int i)) [y]))
    | NONE =>
        (dtcase dest_Op_Const y of
         | SOME i => SOME (Op None (EqualConst (Int i)) [x])
         | NONE => NONE)
End

Definition eq_direct_constant_def:
  eq_direct_constant x y =
    dtcase dest_Op_Constant x of
    | SOME p =>
        (dtcase dest_Op_Constant y of
         | SOME q => SOME (MakeBool (q = p))
         | NONE => SOME (Op None (EqualConst p) [y]))
    | NONE =>
        (dtcase dest_Op_Constant y of
         | SOME p => SOME (Op None (EqualConst p) [x])
         | NONE => NONE)
End

Definition eq_direct_def:
  eq_direct x y =
    dtcase eq_direct_const x y of
    | SOME res => SOME res
    | NONE => dtcase eq_direct_constant x y of
              | SOME res => SOME res
              | NONE => eq_direct_nil x y
End

Definition cons_measure_def:
  cons_measure x =
    case dest_Op_Cons x of
    | NONE => 0
    | SOME (_,xs) => SUM (MAP cons_measure xs) + LENGTH xs + 1
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ Cases \\ fs [dest_Op_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Cons_def,exp_size_def]
  \\ Induct_on ‘l’ \\ fs [exp_size_def]
  \\ rw [] \\ res_tac \\ fs []
End

Triviality cons_measure_lemma:
  (dest_Op_Cons x = SOME (t,xs) ⇒ cons_measure x = SUM (MAP cons_measure xs) + LENGTH xs + 1) ∧
  (dest_Op_Cons x = NONE ⇒ cons_measure x = 0) ∧
  (cons_measure (Op None (ElemAt i) [y]) = 0)
Proof
  rw [] \\ simp [Once cons_measure_def,SF ETA_ss] \\ EVAL_TAC
QED

Definition eq_pure_list_def:
  eq_pure_list [] = Nil ∧
  eq_pure_list [(x,y)] =
   (dtcase eq_direct x y of
    | SOME z => List [z]
    | NONE =>
      dtcase dest_Op_Cons x, dest_Op_Cons y of
      | (NONE, NONE) => List [Op None Equal [x;y]]
      | (SOME (t1,xs), SOME (t2,ys)) =>
           if t1 ≠ t2 ∨ LENGTH xs ≠ LENGTH ys then List [MakeBool F]
           else eq_pure_list (ZIP (REVERSE xs, REVERSE ys))
      | (SOME (t1,xs), NONE) =>
           Append (List [Op None (TagLenEq t1 (LENGTH xs)) [y]])
                  (eq_pure_list (MAPi (λi x. (x, Op None (ElemAt i) [y])) (REVERSE xs)))
      | (NONE, SOME (t1,ys)) => eq_pure_list [(y,x)]) ∧
  eq_pure_list (xy::xys) = Append (eq_pure_list [xy]) (eq_pure_list xys)
Termination
  WF_REL_TAC ‘measure (SUM o MAP (λ(x,y). 1 + cons_measure x + cons_measure y +
                                          if cons_measure x < cons_measure y then 1 else 0))’
  \\ reverse (rpt strip_tac) \\ fs []
  THEN1 (imp_res_tac cons_measure_lemma \\ fs [cons_measure_lemma])
  THEN1
   (fs [o_DEF,cons_measure_lemma]
    \\ imp_res_tac cons_measure_lemma \\ fs []
    \\ ‘LENGTH p_2 = LENGTH (REVERSE p_2)’ by fs []
    \\ ‘SUM (MAP cons_measure p_2) = SUM (MAP cons_measure (REVERSE p_2))’ by
      (rpt (pop_assum kall_tac) \\ Induct_on ‘p_2’ \\ fs [SUM_APPEND])
    \\ asm_rewrite_tac[]
    \\ qspec_tac (‘REVERSE p_2’,‘p_3’) \\ Induct using SNOC_INDUCT
    \\ fs [SNOC_APPEND,MAPi_APPEND,SUM_APPEND])
  \\ imp_res_tac cons_measure_lemma \\ fs [cons_measure_lemma,MEM_SPLIT,SUM_APPEND]
  \\ qpat_x_assum ‘LENGTH _ = _’ mp_tac
  \\ rename [‘LENGTH xs = LENGTH ys’]
  \\ qid_spec_tac ‘ys’
  \\ qid_spec_tac ‘xs’
  \\ Induct THEN1 (Cases \\ fs [])
  \\ Cases_on ‘ys'’ \\ fs [] \\ rpt strip_tac
  \\ first_x_assum drule
  \\ fs [GSYM rich_listTheory.ZIP_APPEND,SUM_APPEND]
End

Definition ConjList_def:
  ConjList [] = MakeBool T ∧
  ConjList [x] = x ∧
  ConjList (x::xs) = If None x (ConjList xs) (MakeBool F)
End

Definition eq_pure_def:
  eq_pure x y = ConjList (append (eq_pure_list [(x,y)]))
End

Triviality eq_pure_list_test:
   append
       (eq_pure_list
          [(Var None 5,
            Op None (Cons 70) [Op None (Const 2) []; Op None (Cons 4) []])]) =
     [Op None (TagLenEq 70 2) [Var None 5];
      Op None (TagLenEq 4 0) [Op None (ElemAt 0) [Var None 5]];
      Op None (EqualConst (Int 2)) [Op None (ElemAt 1) [Var None 5]]]
Proof
  EVAL_TAC
QED

Definition dont_lift_def:
  dont_lift x =
    dtcase dest_Op_Const x of
    | SOME i => T
    | NONE =>
      dtcase dest_Op_Cons_Nil x of
      | SOME t => T
      | NONE =>
        dtcase dest_Op_Constant x of
        | SOME t => T
        | NONE => F
End

Definition lift_exps_def:
  lift_exps [] n binds = ([],n,binds) ∧
  lift_exps (x::xs) n binds =
    if dont_lift x then
      (let (xs,n,binds) = lift_exps xs n binds in
         (x::xs,n,binds))
    else dtcase dest_Op_Cons x of
         | SOME (t,ys) =>
            (let (ys,n,binds) = lift_exps ys n binds in
             let (xs,n,binds) = lift_exps xs n binds in
               (Op None (Cons t) ys::xs,n,binds))
         | NONE =>
            (let (xs,n1,binds) = lift_exps xs (n + 1) (binds ++ [x]) in
              (Var None n::xs,n1,binds))
Termination
  WF_REL_TAC ‘measure (λ(xs,n,binds). exp3_size xs)’ \\ rw []
  \\ Cases_on ‘x’ \\ fs [dest_Op_def,dest_Cons_def,exp_size_def]
  \\ rename [‘Op _ oo _’] \\ Cases_on ‘oo’ \\ gvs [dest_Cons_def]
End

Definition eq_any_def:
  eq_any x y =
    dtcase lift_exps [x;y] 0 [] of
    | (x::y::_, _, binds) => SOME (Let None binds (eq_pure x y))
    | _ => NONE
End

Definition eq_op_def:
  eq_op x y =
    if is_Var x ∧ is_Var y then NONE else
      dtcase eq_direct x y of
      | NONE => eq_any x y
      | SOME res => SOME res
End

(* top-level implementations *)

Definition SmartOp'_def:
  SmartOp' tra op xs =
    dtcase xs of
    | [x] =>
      (dtcase dest_Op_Cons x of
       | SOME (t,xs) => cons_op op t xs
       | NONE => NONE)
    | [x;y] =>
      (dtcase dest_Op_Consts x y of
       | SOME (i,j) => int_op op i j
       | NONE => if op = Equal then eq_op x y else NONE)
    | _ => NONE
End

Definition SmartOp_def:
  SmartOp tra op xs =
    dtcase SmartOp' tra op xs of
    | NONE => closLang$Op tra op xs
    | SOME x => x
End

val _ = export_theory();
