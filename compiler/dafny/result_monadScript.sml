(*
  Definition of a specialized Either monad, where an error is an mlstring.
*)
Theory result_monad
Ancestors
  mlstring
Libs
  preamble


Type error = “:mlstring”;

Type result[pp] = “:error + α”

Definition bind_def:
  bind (INR x) f = f x ∧
  bind (INL y) f = INL y
End

val error_monad_info : monadinfo = {
  bind = “bind”,
  ignorebind = NONE,
  unit = “INR”,
  fail = SOME “INL”,
  choice = NONE,
  guard = NONE
  };

val _ = declare_monad ("error", error_monad_info);
val _ = enable_monadsyntax ();
val _ = enable_monad "error";

Definition result_mmap_def:
  result_mmap f [] : ((α list) result) =
    return [] ∧
  result_mmap f (h0::t0) =
    do
      h <- f h0;
      t <- result_mmap f t0;
      return (h::t)
    od
End

Theorem result_mmap_len:
  ∀f xs ys. result_mmap f xs = INR ys ⇒ LENGTH ys = LENGTH xs
Proof
  Induct_on ‘xs’ \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ res_tac
QED

Theorem mem_result_mmap_rl:
  ∀xs ys.
    result_mmap f xs = INR ys ∧ MEM y ys ⇒
    ∃x. f x = INR y ∧ MEM x xs
Proof
  Induct
  \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
  \\ first_assum $ irule_at (Pos hd) \\ simp []
QED

Theorem mem_result_mmap_lr:
  ∀xs ys.
    result_mmap f xs = INR ys ∧ MEM x xs ⇒
    ∃y. f x = INR y ∧ MEM y ys
Proof
  Induct
  \\ rpt strip_tac
  \\ gvs [result_mmap_def, oneline bind_def, CaseEq "sum"]
QED

Definition result_mmap2_def:
  result_mmap2 f [] [] = return [] ∧
  result_mmap2 f (h0::t0) (h1::t1) =
  do
    h <- f h0 h1;
    t <- result_mmap2 f t0 t1;
    return (h::t)
  od ∧
  result_mmap2 _ _ _ = fail «result_mmap2: Lists of different size»
End

Theorem result_mmap2_len:
  ∀f xs ys zs.
    result_mmap2 f xs ys = INR zs ⇒
    LENGTH zs = LENGTH ys ∧ LENGTH ys = LENGTH xs
Proof
  Induct_on ‘xs’ \\ Cases_on ‘ys’
  \\ gvs [result_mmap2_def, oneline bind_def, CaseEq "sum"]
  \\ rpt strip_tac
  \\ res_tac
  \\ Cases_on ‘zs’ \\ gvs []
QED

Definition prefix_error_def:
  prefix_error s r =
  (case r of
   | INL e => INL (s ^ e)
   | r => r)
End

Definition extend_path_def:
  extend_path cur next = concat [cur; next; «:»]
End
