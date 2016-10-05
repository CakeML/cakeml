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
   >- rw [v_size_def] 
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

val ALOOKUP_compile_env = Q.store_thm ("ALOOKUP_compile_env",
    `! env q x. 
        (ALOOKUP (compile_env env) q) = OPTION_MAP compile_v (ALOOKUP env q)`,
    Induct \\ rw []
    \\ pairarg_tac
    \\ fs []
    \\ rw []
)

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
val goal = top_goal ();
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

fun app_compile_sing_tac (goal as (asl,w)) =
    let 
        val t = find_term (can (match_term 
            ``(evaluate env s (exh_reorder$compile [e1] ++ exh_reorder$compile (e2::es)))``)) w;
        val app_term = rand $ t;
        val e1_term = rand $ rator $ rand $ rand $ rator app_term;
        val e2_term = rand $ rator $ rand $ rand app_term;
        in 
                (
                 rw [Once compile_cons, SimpR ``$++``]
                 THEN rw [Once compile_cons, SimpR ``CONS``]
                 THEN (strip_assume_tac $ SPEC e1_term compile_singleton)
                 THEN (strip_assume_tac $ SPEC e2_term compile_singleton)
                )
                goal

    end

val compile_nil = save_thm ("compile_nil[simp]", EVAL ``exh_reorder$compile []``);

val compile_app_tran = Q.store_thm ("compile_app_tran", 
    `! x h. compile (x ++ h) = (compile x) ++ (compile h)`,
    Induct_on `x`
    \\ fs []
    \\ rw [Once compile_cons] 
    \\ hd_compile_sing_tac
    \\ rw [Once compile_cons]
)

val rev_compile_compile_rev = Q.store_thm ("rev_compile_compile_rev", 
    `! x. REVERSE (compile x) = compile (REVERSE x)`,
    Induct
    \\ fs []
    \\ rw [Once compile_cons]
    \\ hd_compile_sing_tac
    \\ rw [EQ_SYM_EQ, REVERSE_DEF]
    \\ rw [compile_app_tran]
   )

val map_reverse_reverse_map = Q.store_thm ("map_reverse_reverse_map", 
    `! f l. REVERSE (MAP f l) = MAP f (REVERSE l)`,
    Induct_on `l`
    \\ fs [])


val ALOOKUP_none_not_some = Q.store_thm ("ALOOKUP_none_not_some",
    `! env n. (ALOOKUP env n = NONE) ==> (ALOOKUP env n = SOME x) ==> F`,
    Induct_on `env`
    \\ fs []
)

val MAP_FST_MAP_triple = Q.store_thm ("MAP_FST_MAP_triple",
    `! a b c y l. (MAP FST (MAP (\(a,b,c). a, b, (y c)) l)) = (MAP FST l)`,
    Induct_on `l`
    \\ fs []
    \\ rw []
    \\ pairarg_tac
    \\ fs []
)

val _ = temp_overload_on ("None",``NONE``)
val _ = temp_overload_on ("Some",``SOME``)
val _ = temp_overload_on ("Length",``LENGTH``)

val find_match_aux_def = Define`
    find_match_aux refs v [] i = NONE /\
    find_match_aux refs v (p::ps) i = 
        if ALL_DISTINCT (pat_bindings p []) then
            case pmatch refs p v [] of
            | Match env' => SOME i
            | _ => find_match_aux refs v ps (SUC i)
        else NONE
    `

val find_match_def = Define`
    find_match refs v ps = 
        find_match_aux refs v ps 0
`

(*connection between evaluate_match and find_match*)
val evaluate_match_find_match_none = Q.store_thm ("evaluate_match_find_match",
    `!i. find_match_aux s.refs v (MAP FST pes) i = NONE ==>
            evaluate_match env s v pes = (s, Rerr(Rabort Rtype_error))
            `,
    Induct_on `pes`
    \\ fs [find_match_aux_def, evaluate_def]
    \\ Cases
    \\ fs [evaluate_def]
    \\ gen_tac \\ strip_tac
    \\ simp [Once pmatch_nil]
    \\ every_case_tac
    \\ fs []
    \\ res_tac 
)

(*connection between evaluate_match and find_match*)
val evaluate_match_find_match_some = Q.store_thm ("evaluate_match_find_match",
    `!n i. find_match_aux s.refs v (MAP FST pes) n = Some (n + i) ==>
            (i < Length pes /\
            ? env'. pmatch s.refs (FST (EL i pes)) v env = 
                Match env' /\
                    evaluate_match env s v pes = evaluate env' s [(SND (EL i pes))])
            `,
    Induct_on `pes`
    \\ fs [find_match_aux_def, evaluate_def]
    \\ Cases
    \\ fs [evaluate_def]
    \\ ntac 2 gen_tac 
    \\ fs [ADD1]
    \\ TOP_CASE_TAC
    here...
    does i = 0 ?? is that insane ? 
     
    \\ strip_tac
    \\ simp [Once pmatch_nil]
    \\ every_case_tac
    \\ fs []
    \\ res_tac 
)


(*prove the connection to const_fst*)

        
    
`

val compile_correct = Q.store_thm( "compile_correct",
    `(!env ^s es s1 r1. 
        (evaluate env s es = (s1, r1)) /\
        r1 <> Rerr (Rabort Rtype_error) ==>
        (evaluate (compile_env env) (compile_state s) (compile es) =
            (compile_state s1, map_result (MAP compile_v) compile_v r1)
            ))
       /\ 
        (!env ^s err_v pes s1 r1. 
            evaluate_match env s err_v pes = (s1, r1) /\
            r1 <> Rerr (Rabort Rtype_error) =>
            evaluate_match (compile_env env) (compile_state s) (compile_v err_v) (const_cons_fst pes) = 
              (compile_state s1, map_result (MAP compile_v) compile_v r1))`,
    
    ho_match_mp_tac evaluate_ind
    \\ rw [compile_def] 
    \\ fs [evaluate_def]
    \\ rw []
    \\ fs [MAP_FST_MAP_triple]
    (*17 subgoals*)
    >- (
        (*step case ? *)
        every_case_tac
        \\ fs []
        \\ rfs []
        \\ app_compile_sing_tac
        \\ fs []
        \\ rfs []
        \\ rfs [Once compile_cons]
        \\ imp_res_tac evaluate_sing
        \\ rw []
        \\ fs []
        \\ rfs [Once evaluate_def]
       )
    (*16 subgoals left*)
   >- (
       hd_compile_sing_tac
       \\ every_case_tac \\ fs [] \\ rw [] \\ rfs []
       \\ imp_res_tac evaluate_sing \\ fs []
   )
   >- (
      hd_compile_sing_tac
      \\ every_case_tac \\ fs [] \\ rw [] \\ rfs []
   )
   >- (
      every_case_tac \\ fs [] \\ rw [] \\ rfs []
      \\ rfs [rev_compile_compile_rev]
      \\ rw [map_reverse_reverse_map]
      \\ fs [ETA_AX]
   )
   (*13 subgoals left...*)
   >- (
      every_case_tac \\ fs [ALOOKUP_compile_env]  
   )
   (* 12 subgoals *)
   >- (
      rfs [EL_MAP]
      \\ fs [IS_SOME_EXISTS]
   )
   >- (
      rfs [EL_MAP]
   )
   (*10*)
   >- (
      fs [EL_MAP]
      \\ fs [IS_SOME_EXISTS]
      \\ fs []
   )

   r 1
  (*9*)
   >- (
      (*the app case*)
      every_case_tac  \\ fs [rev_compile_compile_rev] \\ rfs []  \\ rw [compile_state_def]
      (*32 subgoals...*)
      >- (
         \\ fs [] \\ rfs []
         \\ rw []
         \\ Induct_on `a'`
         \\ fs []
         \\ rw []
         \\ rw [do_opapp_def]
         \\ fs []
         \\ rw []
         \\ every_case_tac
         >- (
            fs [REVERSE_APPEND] \\ rfs [] \\ rw []
            \\ fs [do_opapp_def]
         )
         >- (
            fs []
            \\ fs [do_opapp_def] 
            \\ rw []
            \\ res_tac 
         )
        
   )
   )
   
   >- (
    (*the match case*)

   )
   >- (
      fs [compile_state_def,MAP_GENLIST]
   )
   >- (
     fs [const_cons_fst_def,const_cons_sep_def]
     \\ fs [evaluate_def]
   )
   >-(
    (*The actual pattern matching case*)

   )
        (*
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
        *)

        >- 
        (
            app_compile_sing_tac
            \\ fs []
            \\ rfs []
            \\ rfs [Once compile_cons]
            \\ imp_res_tac evaluate_sing
            \\ rw []
            \\ fs []
            \\ rfs [Once evaluate_def]
        )
        >- 
        (
            app_compile_sing_tac
            \\ rw [Once evaluate_def]
            \\ fs []
        )
        >- 
        (
            \\ fs []
            \\ rw []
            \\ res_tac
            \\ app_compile_sing_tac
            \\ rw [] 
            \\ rw [Once evaluate_def]
            \\ rfs []
            \\ rw []
            \\ rw [Once evaluate_def]
            \\ fs []
            \\ fs [Once compile_cons]
        )
        >-
        (
            fs []
            \\ rw []
            \\ app_compile_sing_tac
            \\ rw []
            \\ rw [Once evaluate_def]
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
