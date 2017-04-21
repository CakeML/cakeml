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

(* Special orphan trace for decLang. 3 is because decLang is the third lanugage. *)
val oc_tra_def = Define`
  (oc_tra = Cons orphan_trace 3)`;

val _ = Define `
  (compile_decs c next [] = (c + 1, Con (Cons oc_tra c) NONE []))
  ∧
  (compile_decs c next (d::ds) =
   (* Up to 3 new expressions are created at this point, so we need 7 new traces. *)
   let (c, ts) = (c + 3, MAP (Cons oc_tra) (GENLIST (\n. n + c) 3)) in
   case d of
   | Dlet n e =>
     let vars = (GENLIST (λn. STRCAT"x"(num_to_dec_string n)) n) in
     let (c, decs) = compile_decs c (next + n) ds in
       (c,
       Let (EL 0 ts) NONE (Mat (EL 1 ts) e [(Pcon NONE (MAP Pvar
       vars), init_globals (EL 2 ts) 3 vars next)]) decs)
   | Dletrec funs =>
     let n = (LENGTH funs) in
     let (c, decs) = compile_decs c (next + n) ds in
       (c,
       Let (EL 0 ts) NONE (init_global_funs (EL 1 ts) 2 next funs) decs))`;

val _ = Define `
  (compile_prompt c none_tag some_tag next prompt =
   case prompt of
    | Prompt ds =>
      let n = (num_defs ds) in
      let (c, decs) = compile_decs c next ds in
      (* 7 new expressions are created at this point, so we need 7 new traces. *)
      let (c, ts) = (c + 7, MAP (Cons oc_tra) (GENLIST (\n. n + c) 7)) in
        (c, next+n,
         Let (EL 0 ts) NONE (Extend_global (EL 1 ts) n)
           (Handle (EL 2 ts) (Let (EL 3 ts) NONE decs
                     (Con (EL 4 ts) (SOME none_tag) []))
             [(Pvar "x",
               Con (EL 5 ts) (SOME some_tag) [Var_local (EL 6 ts) "x"])])))`;

(* c is a trace counter, which holds the value of the next trace number to be
* used. *)
val _ = Define`
  (compile_prog c none_tag some_tag next [] = (c + 1, next, Con (Cons oc_tra c) (SOME none_tag) []))
  ∧
  (compile_prog c none_tag some_tag next (p::ps) =
   let (c, next',p') = compile_prompt c none_tag some_tag next p in
   let (c, next'',ps') = compile_prog c none_tag some_tag next' ps in
     (c + 2, next'',Mat (Cons oc_tra c) p'
                        [(Pcon (SOME none_tag) [], ps'); (Pvar "x", Var_local
                        (Cons oc_tra (c + 1)) "x")]))`;

val _ = Define`
  compile conf p =
    let (c, n, e) = 
      compile_prog 1
        (none_tag, TypeId(Short"option"))
        (some_tag, TypeId(Short "option")) conf p in
          (n, e)`;

val _ = export_theory()
