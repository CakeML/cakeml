open preamble exh_reorderTheory exhSemTheory

val _ = new_theory "exh_reorderProof";

val s = ``s:'a exhSem$state``;

val v_rel_def = Define `
    (v_rel (Litv l) v2 = (v2 = Litv l)) /\
    (v_rel (Conv n vs) v2 = ?vs2. (v2 = Conv n vs2) /\ (LIST_REL v_rel vs vs2)) /\

    `;

val compile_v_def = tDefine "compile_v" `
    (compile_v (Litv l) = Litv l) /\
    (compile_v (Conv n vs) = Conv n (MAP compile_v vs)) /\
    (compile_v (Closure env name e) = Closure (MAP (\(a, v). (a, compile_v v) ) env) name (HD (compile [e]))) /\
    (compile_v (Recclosure env funs name) = Recclosure (MAP (\(a, v). (a, compile_v v) ) env) (MAP (\(a, b, e). (a, b, HD(compile [e]))) funs) name) /\
    (compile_v (Loc n) = Loc n) /\
    (compile_v (Vectorv vs) = Vectorv (MAP compile_v vs))
` 
(
    WF_REL_TAC `measure v_size`
    \\ rpt conj_tac
    >- (
        ntac 2 gen_tac
        \\ Induct
        \\ rw []
        \\ rw [v_size_def]
        \\ res_tac
        \\ rw []
        )
    >- (
        ntac 1 gen_tac
        \\ Induct
        \\ rw []
        \\ rw [v_size_def,list_size_def]
        (*Here i am *)
        >- (
            Induct
        )
        \\ res_tac
        \\ rw []
    )


)

val compile_correct = Q.store_thm( "compile_correct",
    `(! env ^s es. evaluate env s es = evaluate env s (compile es)) /\
    (! env ^s err_v pes. evaluate_match env s err_v pes = 
        evaluate_match env s err_v (const_cons_fst pes))
    `,
    
    ho_match_mp_tac evaluate_ind
    \\ rw [compile_def] 
    >- rw [evaluate_def]
