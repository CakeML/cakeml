(**
  A simple Result datatype to ease some implementations
**)
open stringTheory;
open preambleFloVer;

val _ = new_theory "Results";

Datatype:
  result = Succes 'a | Fail string | FailDet string 'a
End

Definition injectResult_def:
  injectResult (Succes _) = T /\
  injectResult _ = F
End

Definition result_bind_def:
  result_bind (Fail s) f = Fail s /\
  result_bind (FailDet s x) f = FailDet s x /\
  result_bind (Succes x) f = f x
End

Definition result_ignore_bind_def:
  result_ignore_bind m1 m2 = result_bind m1 (K m2)
End

Definition result_return_def:
  result_return x = Succes x
End

val _ = export_rewrites ["result_return_def", "result_bind_def", "result_ignore_bind_def"]

val _ = export_theory();
