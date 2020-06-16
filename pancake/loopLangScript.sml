(*
  loopLang intermediate language
*)
open preamble
     asmTheory (* for importing binop and cmp *)
     backend_commonTheory (* for overloading shift operation  *);

val _ = new_theory "loopLang";

Type shift = ``:ast$shift``

Datatype:
  exp = Const ('a word)
      | Var num
      | Lookup (5 word)
      | Load exp
      | Op binop (exp list)
      | Shift shift exp num
End

Datatype:
  prog = Skip
       | Assign num ('a exp)           (* dest, source *)
       | Store ('a exp) num            (* dest, source *)
       | SetGlobal (5 word) ('a exp)   (* dest, source *)
       | LoadByte num num               (* TODISC: have removed imm, why num num? *)
       | StoreByte num num
       | Seq prog prog
       | If cmp num ('a reg_imm) prog prog num_set
       | Loop num_set prog num_set     (* names in, body, names out *)
       | Break
       | Continue
       | Raise num
       | Return num
       | Tick
       | Mark prog
       | Fail
       | LocValue num num  (* assign v1 := Loc v2 0 *)
       | Call ((num # num_set) option) (* return var *)
              (num option) (* target of call *)
              (num list)   (* arguments *)
              ((num # prog # prog # num_set) option) (* var to store exception,
                                                        exception-handler code,
                                                        normal-return handler code,
                                                        live vars after call *)
       | FFI string num num num num num_set (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End

Definition locals_touched_def:
  (locals_touched (Const w) = []) /\
  (locals_touched (Var v) = [v]) /\
  (locals_touched (Lookup name) = []) /\
  (locals_touched (Load addr) = locals_touched addr) /\
  (locals_touched (Op op wexps) = FLAT (MAP locals_touched wexps)) /\
  (locals_touched (Shift sh wexp n) = locals_touched wexp)
Termination
  cheat
End

Definition assigned_vars_def:
  (assigned_vars Skip = []) ∧
  (assigned_vars (Assign n e) = [n]) ∧
  (assigned_vars (LoadByte n m) = [m]) ∧
  (assigned_vars (Seq p q) = assigned_vars p ++ assigned_vars q) ∧
  (assigned_vars (If cmp n r p q ns) = assigned_vars p ++ assigned_vars q) ∧
  (assigned_vars (LocValue n m) = [n]) ∧
  (assigned_vars (Mark p) = assigned_vars p) ∧
  (assigned_vars (Loop _ p _) = assigned_vars p) ∧
  (assigned_vars (Call NONE _ _ _) = []) ∧
  (assigned_vars (Call (SOME (n,_)) _ _ NONE) = [n]) ∧
  (assigned_vars (Call (SOME (n,_)) _ _ (SOME (m,p,q, _))) =
     n::m::assigned_vars p ++ assigned_vars q) ∧
  (assigned_vars _ = [])
End


(*
Definition cutset_def:
  (cutset l (If _ _ _ p q cs) =
     inter (inter (inter l (cutset l p)) (cutset l q)) cs) ∧
  (cutset l (Loop il p ol) = inter (inter (inter l il) (cutset l p)) ol) ∧
  (cutset l (Call NONE _ _ _) = l) ∧
  (cutset l (Call (SOME (n,cs)) _ _ NONE) = inter l cs) ∧
  (cutset l (Call (SOME (n,cs)) _ _ (SOME (_,p,q, ps))) =
   inter (inter (inter (inter l cs) (cutset l p)) (cutset l q)) ps) ∧
  (cutset l (FFI _ _ _ _ _ cs) = inter l cs) ∧
  (cutset l (Mark p) = inter l (cutset l p))  ∧
  (cutset l (Seq p q) = inter (inter l (cutset l p)) (cutset l q)) ∧
  (cutset l _ = l)
End


Definition upd_cutset_def:
  (upd_cutset n (If c r ri p q cs) =
     If c r ri (upd_cutset n p) (upd_cutset n q) (insert n () cs)) ∧
  (upd_cutset n (Loop il p ol) =
     Loop (insert n () il) (upd_cutset n p) (insert n () ol)) ∧
  (upd_cutset n (Call (SOME (m,cs)) trgt args NONE) =
     Call (SOME (m,insert n () cs)) trgt args NONE) ∧
  (upd_cutset n (Call (SOME (m,cs)) trgt args (SOME (r,p,q, ps))) =
     Call (SOME (m,insert n () cs)) trgt args
          (SOME (r,(upd_cutset n p),(upd_cutset n q), (insert n () ps)))) ∧
  (upd_cutset n (FFI fi ptr1 len1 ptr2 len2 cs) = FFI fi ptr1 len1 ptr2 len2 (insert n () cs)) ∧
  (upd_cutset n (Mark p) = Mark (upd_cutset n p))  ∧
  (upd_cutset n (Seq p q) = Seq (upd_cutset n p) (upd_cutset n q)) ∧
  (upd_cutset n p = p)
End
*)
(*
Definition cutset_def:
  (cutset l (If _ _ _ p q cs) = cs) ∧
  (cutset l (Loop il p ol) = inter il ol) ∧
  (cutset l (Call NONE _ _ _) = l) ∧
  (cutset l (Call (SOME (n,cs)) _ _ NONE) = cs) ∧
  (cutset l (Call (SOME (n,cs)) _ _ (SOME (_,p,q, ps))) = ps) ∧
  (cutset l (FFI _ _ _ _ _ cs) = cs) ∧
  (cutset l (Mark p) = cutset l p)  ∧
  (cutset l (Seq p q) = inter (cutset l p) (cutset l q)) ∧
  (cutset l _ = l)
End
*)


(*
Definition cutset_def:
  (cutset l (If _ _ _ p q cs) =
     inter (inter (cutset l p) (cutset l q)) cs) ∧
  (cutset l (Loop il _ ol ) = inter il ol) ∧
  (cutset l (Call NONE _ _ _) = l) ∧
  (cutset l (Call (SOME (n,cs)) _ _ (SOME (_,p,q, ps))) =
     inter cs (inter (inter (cutset l p) (cutset l q)) ps)) ∧
  (cutset l (FFI _ _ _ _ _ cs) = cs) ∧
  (cutset l (Mark p) = cutset l p)  ∧
  (cutset l (Seq p q) = inter (cutset l p) (cutset l q)) ∧
  (cutset l _ = l)
End
*)


val _ = export_theory();
