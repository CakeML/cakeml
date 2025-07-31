(*
  This compiler phase copies simple definition of constants
  forward, so their definition always exists right before their
  uses. This is to prevent cheap to compute constants from
  using space in cutsets and thus being stored on the stack.
*)
open preamble dataLangTheory;

val _ = new_theory "data_consts";

Definition dest_cheap_def:
  dest_cheap (IntOp (Const i)) = SOME (INR i) ∧
  dest_cheap (BlockOp (Cons tag)) = SOME (INL tag) ∧
  dest_cheap _ = NONE
End

Definition mk_const_assign_def:
  mk_const_assign v (INL i) = Assign v (IntOp (Const i)) [] NONE ∧
  mk_const_assign v (INR tag) = Assign v (BlockOp (Cons tag)) [] NONE
End

Definition mk_assigns_def:
  mk_assigns [] m p = p ∧
  mk_assigns (v::vs) m p =
    case lookup v m of
    | NONE => mk_assigns vs m p
    | SOME const => Seq (mk_const_assign v const) (mk_assigns vs m p)
End

Definition comp_def:
  (comp Skip m = (Skip,m)) /\
  (comp (Return n) m = (mk_assigns [n] m $ Return n, m)) /\
  (comp (Raise n) m = (mk_assigns [n] m $ Raise n, m)) /\
  (comp (Move n1 n2) m =
    case lookup n2 m of
    | NONE => (Move n1 n2, delete n1 m)
    | SOME const => (mk_const_assign n1 const, insert n1 const m)) /\
  (comp (Seq c1 c2) m =
     let (d1,m1) = comp c1 m in
     let (d2,m2) = comp c2 m1 in
       (Seq d1 d2, m2)) /\
  (comp Tick m = (Tick, m)) /\
  (comp (MakeSpace k names) m =
     let m1 = inter m names in
       (MakeSpace k names, m1)) /\
  (comp (If n c2 c3) m =
     let (d3,m3) = comp c3 m in
     let (d2,m2) = comp c2 m in
       (mk_assigns [n] m $ If n d2 d3, LN)) /\
  (comp (Assign v op vs NONE) m =
     (mk_assigns vs m $ Assign v op vs NONE, delete v m)) /\
  (comp (Assign v op vs (SOME l)) m =
     (mk_assigns vs m $ Assign v op vs (SOME l), delete v (inter m l))) /\
  (comp (Call NONE dest vs handler) m =
     (mk_assigns vs m $ Call NONE dest vs handler, LN)) /\
  (comp (Call (SOME (n,names)) dest vs NONE) m =
     (mk_assigns vs m $ Call (SOME (n,names)) dest vs NONE,
      delete n (inter m names))) /\
  (comp (Call (SOME (n,names)) dest vs (SOME (v,c))) m =
     (mk_assigns vs m $ Call (SOME (n,names)) dest vs (SOME (v,c)), LN))
End

Definition copy_consts_def:
  copy_consts p = FST (comp p LN)
End

val _ = export_theory();
