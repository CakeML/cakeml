open preamble exhLangTheory

val _ = new_theory"exh_reorder";

(*dest_type*)

val is_const_con_def = Define`
    (is_const_con (Pcon tag plist) = (plist = [])) /\
    (is_const_con _  = F)`

(*operates on (pat # exp) list*)
val const_cons_sep_def = Define`
    (const_cons_sep [] cons vars = (cons, vars)) /\
    (const_cons_sep (x::xs) cons vars = 
        if (is_const_con (FST x)) 
            then (const_cons_sep xs (x::cons) vars)
            else (const_cons_sep xs cons (x::vars)) 
)`

val const_cons_fst_def = Define`
    const_cons_fst pes = ((\(cons, vars). cons ++ vars) (const_cons_sep pes [] []))
`

val compile_def = tDefine "compile" `
    (compile [] = []) /\
    (compile [Raise e] = [Raise (HD (compile [e]))]) /\
    (compile [Handle e pes] =  [Handle (HD (compile [e])) (const_cons_fst pes)]) /\
    (compile [Lit l] = [Lit l]) /\
    (compile [Con n es] = [Con n (compile es)] ) /\
    (compile [Var_local v] = [Var_local v]) /\
    (compile [Var_global n] = [Var_global n]) /\
    (compile [Fun v e] = [Fun v (HD (compile [e]))]) /\
    (compile [App op es] = [App op (compile es)]) /\
    (compile [Mat e pes] =  [Mat (HD (compile [e])) (const_cons_fst pes)]) /\
    (compile [Let vo e1 e2] = [Let vo (HD (compile [e1])) (HD (compile [e2]))]) /\
    (compile [Letrec funs e] = 
        [Letrec (MAP (\(a, b, e). (a,b, HD (compile [e]))) funs) (HD (compile [e]))]) /\
    (compile [Extend_global n] = [Extend_global n]) /\
    (compile (x::y::xs) = 
        compile [x] ++ compile (y::xs)
    )`
    (
     WF_REL_TAC `measure exp6_size` 
     \\ simp []
     \\ gen_tac
     \\ Induct_on `funs`
     \\ rw [exp_size_def]
     \\ rw [exp_size_def]
     \\ res_tac
     \\ rw []
     )

val compile_def = tDefine "compile" `
    (compile [] = []) /\
    (compile [Raise e] = [Raise (HD (compile [e]))]) /\
    (compile [Handle e pes] =  [Handle (HD (compile [e])) (const_cons_fst pes)]) /\
    (compile [Lit l] = [Lit l]) /\
    (compile [Con n es] = [Con n (compile es)] ) /\
    (compile [Var_local v] = [Var_local v]) /\
    (compile [Var_global n] = [Var_global n]) /\
    (compile [Fun v e] = [Fun v (HD (compile [e]))]) /\
    (compile [App op es] = [App op (compile es)]) /\
    (compile [Mat e pes] =  [Mat (HD (compile [e])) (const_cons_fst pes)]) /\
    (compile [Let vo e1 e2] = [Let vo (HD (compile [e1])) (HD (compile [e2]))]) /\
    (compile [Letrec funs e] = 
        [Letrec (MAP (\(a, b, e). (a,b, HD (compile [e]))) funs) (HD (compile [e]))]) /\
    (compile [Extend_global n] = [Extend_global n]) /\
    (compile (x::y::xs) = 
        compile [x] ++ compile (y::xs)
    )`
    (
     WF_REL_TAC `measure exp6_size` 
     \\ simp []
     \\ gen_tac
     \\ Induct_on `funs`
     \\ rw [exp_size_def]
     \\ rw [exp_size_def]
     \\ res_tac
     \\ rw []
     )


 
val () = export_theory();
