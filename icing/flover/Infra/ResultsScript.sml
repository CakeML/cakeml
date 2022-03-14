open stringTheory;
open preambleFloVer;

val _ = new_theory "Results";

val _ = Datatype `
  result = Succes 'a | Fail string | FailDet string 'a`;

val injectResult_def = Define `
  injectResult (Succes _) = T /\
  injectResult _ = F`;

val result_bind_def = Define `
  result_bind (Fail s) f = Fail s /\
  result_bind (FailDet s x) f = FailDet s x /\
  result_bind (Succes x) f = f x`;

val result_ignore_bind_def = Define `
  result_ignore_bind m1 m2 = result_bind m1 (K m2) `;

val result_return_def = Define `
  result_return x = Succes x`;

val _ = export_rewrites ["result_return_def", "result_bind_def", "result_ignore_bind_def"]

val _ = export_theory();
