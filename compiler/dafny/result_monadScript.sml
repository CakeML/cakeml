(*
 * Definition of a specialized Either monad, where an error is a string.
 *)

open preamble

val _ = new_theory "result_monad"

Type error = “:string”;

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

val _ = export_theory();
