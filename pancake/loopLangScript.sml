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
       | FFI string num num num num num_set
         (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
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
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
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

Definition acc_vars_def:
  (acc_vars (Seq p1 p2) l = acc_vars p1 (acc_vars p2 l)) ∧
  (acc_vars Break l = (l:num_set)) ∧
  (acc_vars Continue l = l) ∧
  (acc_vars (Loop l1 body l2) l = acc_vars body l) ∧
  (acc_vars (If x1 x2 x3 p1 p2 l1) l = acc_vars p1 (acc_vars p2 l)) ∧
  (acc_vars (Mark p1) l = acc_vars p1 l) /\
  (acc_vars Tick l = l) /\
  (acc_vars Skip l = l) /\
  (acc_vars Fail l = l) /\
  (acc_vars (Raise v) l = l) /\
  (acc_vars (Return v) l = l) /\
  (acc_vars (Call ret dest args handler) l =
       case ret of
       | NONE => l
       | SOME (v,live) =>
         let l = insert v () l in
           case handler of
           | NONE => l
           | SOME (n,p1,p2,l1) =>
               acc_vars p1 (acc_vars p2 (insert n () l))) /\
  (acc_vars (LocValue n m) l = insert n () l) /\
  (acc_vars (Assign n exp) l = insert n () l) /\
  (acc_vars (Store exp n) l = l) /\
  (acc_vars (SetGlobal w exp) l = l) /\
  (acc_vars (LoadByte n m) l = insert m () l) /\
  (acc_vars (StoreByte n m) l = l) /\
  (acc_vars (FFI name n1 n2 n3 n4 live) l = l)
End


val _ = export_theory();
