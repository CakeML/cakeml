open preamble conLangTheory
open backend_commonTheory

val _ = new_theory"con_to_dec"

(* The translator to decLang maps a declaration to an expression that sets of
 * the global environment in the right way. If evaluating the expression
 * results in an exception, then the exception is handled, and a SOME
 * containing the exception is returned. Otherwise, a NONE is returned.
 *)

val _ = Define`
  (init_globals [] idx =
   Con NONE [])
  ∧
  (init_globals (x::vars) idx =
   Let NONE (App (Init_global_var idx) [Var_local x]) (init_globals vars (idx+1)))`;


val _ = Define `
  (init_global_funs next [] = Con NONE [])
  ∧
  (init_global_funs next ((f,x,e)::funs) =
   Let NONE (App (Init_global_var next) [Fun x e]) (init_global_funs (next+1) funs))`;

val _ = Define `
  (compile_decs next [] = Con NONE [])
  ∧
  (compile_decs next (d::ds) =
   case d of
   | Dlet n e =>
     let vars = (GENLIST (λn. STRCAT"x"(num_to_dec_string n)) n) in
       Let NONE (Mat e [(Pcon NONE (MAP Pvar vars), init_globals vars next)])
         (compile_decs (next+n) ds)
   | Dletrec funs =>
     let n = (LENGTH funs) in
       Let NONE (init_global_funs next funs) (compile_decs (next+n) ds))`;

val _ = Define `
  (compile_prompt none_tag some_tag next prompt =
   case prompt of
    | Prompt ds =>
      let n = (num_defs ds) in
        (next+n,
         Let NONE (Extend_global n)
           (Handle (Let NONE (compile_decs next ds)
                     (Con (SOME none_tag) []))
             [(Pvar "x",
               Con (SOME some_tag) [Var_local "x"])])))`;

val _ = Define`
  (compile_prog none_tag some_tag next [] = (next, Con (SOME none_tag) []))
  ∧
  (compile_prog none_tag some_tag next (p::ps) =
   let (next',p') = compile_prompt none_tag some_tag next p in
   let (next'',ps') = compile_prog none_tag some_tag next' ps in
     (next'',Mat p' [(Pcon (SOME none_tag) [], ps'); (Pvar "x", Var_local "x")]))`;

val _ = Define`
  compile =
    compile_prog
    (none_tag, TypeId(Short"option"))
    (some_tag, TypeId(Short "option"))`;

val _ = export_theory()
