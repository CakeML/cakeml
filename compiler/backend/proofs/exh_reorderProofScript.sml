open preamble exh_reorderTheory exhSemTheory exhPropsTheory

val _ = new_theory "exh_reorderProof";

val s = ``s:'ffi exhSem$state``;

val MEM_size_mono = Q.store_thm("MEM_size_mono",
`! a b. (MEM a b) ==> ((v_size a) < 1 + v3_size b)`,
    Induct_on `b`
    \\ rw [v_size_def]
    \\ res_tac
    \\ rw []
)

val MEM_size_mono_v1_size = Q.store_thm("MEM_size_mono_v1_size",
`! a v env. MEM (a,v) env ==> v_size v  < 1 + v1_size env`,
   Induct_on `env`
   \\ rw [v_size_def]
   >- (
     rw [v_size_def] 
   )
   \\ res_tac 
   \\ rw []
)

val compile_v_def = tDefine "compile_v" `
    (compile_v (Litv l) = Litv l) /\
    (compile_v (Conv n vs) = Conv n (MAP compile_v vs)) /\
    (compile_v (Closure env name e) = Closure (MAP (\(a, v). (a, compile_v v) ) env) name (HD (compile [e]))) /\
    (compile_v (Recclosure env funs name) = Recclosure (MAP (\(a, v). (a, compile_v v) ) env) (MAP (\(a, b, e). (a, b, HD(compile [e]))) funs) name) /\
    (compile_v (Loc n) = Loc n) /\
    (compile_v (Vectorv vs) = Vectorv (MAP compile_v vs)) ` 

   (
    WF_REL_TAC `measure v_size`
    \\ rw []
    \\ imp_res_tac MEM_size_mono_v1_size    
    \\ imp_res_tac MEM_size_mono
    \\ rw []
    )

val _ = export_rewrites ["compile_v_def"];

val _ = overload_on ("compile_env", ``MAP \(tn, v). (tn, compile_v v)``);

val compile_store_v_def = Define `
    (compile_store_v (Refv v) = Refv (compile_v v)) /\
    (compile_store_v (W8array l) = W8array l) /\
    (compile_store_v (Varray vs) = Varray (MAP compile_v vs))`

val compile_state_def = Define `
    compile_state (^s) = 
    <| clock := s.clock;
       refs := MAP compile_store_v s.refs;
       ffi := s.ffi;
       globals := MAP (OPTION_MAP compile_v) s.globals
    |>`;

val compile_state_simps = save_thm ("compile_state_simps", LIST_CONJ
    [EVAL ``(compile_state s).globals``,
     EVAL ``(compile_state s).clock``,
     EVAL ``(compile_state s).ffi``,
     EVAL ``(compile_state s).refs``]);

val _ = export_rewrites ["compile_state_simps"];

val compile_length = Q.store_thm ("compile_length",
    `! es. LENGTH (compile es) = LENGTH es`,
    ho_match_mp_tac compile_ind
    \\ rw [compile_def]
    )

val compile_singleton = Q.store_thm ("compile_singleton",
   `! e. ?e2. compile [e] = [e2]`,
    rw []
    \\ qspec_then `[e]` mp_tac compile_length
    \\ rw [LENGTH_EQ_NUM_compute]
)

infixr $;
fun (f $ x) = f x

(*
val (asl, w) = top_goal ();
*)
fun hd_compile_sing_tac (goal as (asl,w)) = 
    let 
       val t = find_term (can (match_term ``HD (exh_reorder$compile [e])``)) w;
       val e_term =  rand $ rator $ rand $ rand t;
       in 
        strip_assume_tac $ SPEC e_term compile_singleton
    end
    goal

val compile_cons = Q.store_thm ("compile_cons",
   `! e es. compile (e::es) = HD (compile [e]) :: (compile es)`,
   rw []
   \\ Cases_on `es`
   \\ rw [compile_def]
   \\ METIS_TAC [compile_singleton, HD]
)

val compile_nil = save_thm ("compile_nil[simp]", EVAL ``exh_reorder$compile []``);

val compile_correct = Q.store_thm( "compile_correct",
    `(!env ^s es s1 r1. 
        (evaluate env s es = (s1, r1)) ==>
        (evaluate (compile_env env) (compile_state s) (compile es) =
            (compile_state s1, map_result (MAP compile_v) compile_v r1)
            ))
       /\ 
        (!env ^s err_v pes s1 r1. 
            evaluate_match env s err_v pes = (s1, r1) ==>
            evaluate_match (compile_env env) (compile_state s) (compile_v err_v) (const_cons_fst pes) = 
              (compile_state s1, map_result (MAP compile_v) compile_v r1))`,
    
    ho_match_mp_tac evaluate_ind
    \\ rw [compile_def] 
    \\ fs [evaluate_def]
    \\ rw []
    \\ fs []
    >- (
        (*step case (?) *)
        every_case_tac
        >- 
        (
            fs []
            \\ rw []
            \\ rfs []
            \\ rw [Once compile_cons, SimpR ``$++``] 
            \\ rw [Once compile_cons, SimpR ``CONS``] 
            \\ rw [evaluate_def]
            \\ hd_compile_sing_tac
            \\ rw []
            \\ hd_compile_sing_tac
            \\ rw []
            \\ rw [evaluate_def]
            \\ fs []
            \\ rfs [Once compile_cons]
            \\ fs []
            \\ imp_res_tac evaluate_sing
            \\ rw []
            \\ fs []
        )
    )


        \\ qspec_then `e1` strip_assume_tac compile_singleton
        \\ rw [] 
        \\ rw [evaluate_def]
    )
        >- (
            (*fun case*)
            fs [evaluate_def]
            \\ rw []
        )
