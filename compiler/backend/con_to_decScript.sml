open preamble conLangTheory
open backend_commonTheory

val _ = new_theory"con_to_dec"

(* The translator to decLang maps a declaration to an expression that sets of
 * the global environment in the right way. If evaluating the expression
 * results in an exception, then the exception is handled, and a SOME
 * containing the exception is returned. Otherwise, a NONE is returned.
 *)

val _ = Define`
  (init_globals tra tidx [] idx =
   Con (mk_cons tra tidx) NONE [])
  ∧
  (init_globals tra tidx (x::vars) idx =
   Let (mk_cons tra tidx) NONE (App (mk_cons tra (tidx+1)) (Init_global_var idx)
   [Var_local (mk_cons tra (tidx+2)) x]) (init_globals tra (tidx+3) vars (idx+1)))`;


val _ = Define `
  (init_global_funs tra tidx next [] = Con (mk_cons tra tidx) NONE [])
  ∧
  (init_global_funs tra tidx next ((f,x,e)::funs) =
   Let (mk_cons tra tidx) NONE (App (mk_cons tra (tidx+1)) (Init_global_var next) [Fun (mk_cons tra (tidx+2)) x e]) (init_global_funs tra (tidx+3) (next+1) funs))`;
(*TODO: We should check whether introducing a trace to Dletrec and is sensible, in
  * that case we should change from passing on Empty into init_global_funs to
  * the correct trace *)
val _ = Define `
  (compile_decs next [] = Con Empty NONE [])
  ∧
  (compile_decs next (d::ds) =
   case d of
   | Dlet n e =>
     let vars = (GENLIST (λn. STRCAT"x"(num_to_dec_string n)) n) in
       Let (mk_cons Empty 1) NONE (Mat (mk_cons Empty 2) e [(Pcon NONE (MAP Pvar
       vars), init_globals Empty 3 vars next)])
         (compile_decs (next+n) ds)
   | Dletrec funs =>
     let n = (LENGTH funs) in
       Let (mk_cons Empty 1) NONE (init_global_funs Empty 2 next funs) (compile_decs (next+n) ds))`;

(* Since the Lets, cons and var_local doesn't have a trace, nor does the prompts we'll leave
* them as empty *)
val _ = Define `
  (compile_prompt none_tag some_tag next prompt =
   case prompt of
    | Prompt ds =>
      let n = (num_defs ds) in
        (next+n,
         Let Empty NONE (Extend_global Empty n)
           (Handle Empty (Let Empty NONE (compile_decs next ds)
                     (Con Empty (SOME none_tag) []))
             [(Pvar "x",
               Con Empty (SOME some_tag) [Var_local Empty "x"])])))`;

val _ = Define`
  (compile_prog none_tag some_tag next [] = (next, Con Empty (SOME none_tag) []))
  ∧
  (compile_prog none_tag some_tag next (p::ps) =
   let (next',p') = compile_prompt none_tag some_tag next p in
   let (next'',ps') = compile_prog none_tag some_tag next' ps in
     (next'',Mat Empty p' [(Pcon (SOME none_tag) [], ps'); (Pvar "x", Var_local
     Empty "x")]))`;

val _ = Define`
  compile =
    compile_prog
    (none_tag, TypeId(Short"option"))
    (some_tag, TypeId(Short "option"))`;

val _ = export_theory()
