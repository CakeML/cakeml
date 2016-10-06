open preamble exhLangTheory

val _ = new_theory"exh_reorder";

(*dest_type*)

val is_const_con_def = Define`
    (is_const_con (Pcon tag plist) = (plist = [])) /\
    (is_const_con _  = F)`

(*operates on (pat # exp) list*)

val isPvar_def = Define`
    (isPvar (Pvar _) = T) /\
    isPvar _ = F`

val _ = export_rewrites ["isPvar_def", "is_const_con_def"]

val const_cons_sep_def = Define`
    (const_cons_sep (x::xs) non_con_cons = 
        if (isPvar (FST x))
            then non_con_cons ++ (x::xs)
        else if (is_const_con (FST x))
            then x::(const_cons_sep xs non_con_cons)
            else (const_cons_sep xs (non_con_cons ++ [x]))
    ) /\
    const_cons_sep [] non_con_cons = non_con_cons`


val const_cons_fst_def = Define`
    const_cons_fst pes = const_cons_sep pes []`

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
