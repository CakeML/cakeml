Theory bvi_lclunfProof
Ancestors
  bvi_lclunf bviProps bviSem
Libs
  preamble

        
Theorem revar_ssh_push:
  revar_ssh (Push push::xs) ssh n = let n' = revar_ssh xs ssh n in if ssh ≤ n' then n' + push else n'
Proof
  rw[revar_ssh_def]
QED

Theorem revar_ssh_reoderadd:
  revar_ssh (ReorderAdd n1 n2 v::xs) ssh n =
  let
    n' = revar_ssh xs ssh n
  in
    if n' < ssh then n'
    else if n' < ssh + n1 then n' + n2 + v
    else if n' < ssh + n1 + n2 then n' − n1
    else n' + v
Proof
  rw[revar_ssh_def]
QED

Theorem revar_ssh_delay:
  revar_ssh (Delay d::xs) ssh n = revar_ssh xs (ssh + d) n
Proof
  rw[revar_ssh_def]
QED


Theorem revar_ssh_shift:
  ∀rn ssh n.
    revar_ssh rn ssh n =
    if n < ssh then n else revar_ssh rn 0 (n − ssh) + ssh
Proof
  Induct >> rw[]
  >- rw[revar_ssh_def]
  >- rw[revar_ssh_def]
  >- (Cases_on ‘h’ >> rw[]
      >- (PURE_REWRITE_TAC[revar_ssh_def]
          >> first_x_assum $ qspecl_then [‘ssh’, ‘n’] assume_tac >> gvs[]
         )

      >- (PURE_REWRITE_TAC[revar_ssh_def]
          >> first_x_assum $ qspecl_then [‘ssh’, ‘n’] assume_tac >> gvs[]
         )
      >- (PURE_REWRITE_TAC[revar_ssh_def]
          >> first_x_assum $ qspecl_then [‘ssh + n'’, ‘n’] assume_tac >> gvs[]
         )
     )
  >> Cases_on ‘h’ >> rw[] >> gvs[NOT_LESS]
  >- (PURE_REWRITE_TAC[revar_ssh_push]
      >> first_assum $ qspecl_then [‘ssh’, ‘n’] assume_tac
      >> first_x_assum $ qspecl_then [‘0’, ‘n - ssh’] assume_tac
      >> fs[]
     )
  >- (PURE_REWRITE_TAC[revar_ssh_reoderadd]
      >> first_assum $ qspecl_then [‘ssh’, ‘n’] assume_tac
      >> first_x_assum $ qspecl_then [‘0’, ‘n - ssh’] assume_tac
      >> fs[]
     )
  >- (PURE_REWRITE_TAC[revar_ssh_delay]
      >> first_assum $ qspecl_then [‘ssh + n'’, ‘n’] assume_tac
      >> first_x_assum $ qspecl_then [‘0 + n'’, ‘n - ssh’] assume_tac
      >> fs[]
     )

QED

Theorem revar_nil[simp]:
  revar [] n = n
Proof
  fs [revar_def, revar_ssh_def]
QED

Theorem revar_Push[simp]:
  revar (Push p::rn) n = revar rn n + p
Proof
  fs [revar_def, revar_ssh_def]
QED

Theorem revar_Delay:
  revar (Delay d::rn) n = if n < d then n else revar rn (n − d) + d
Proof
  fs [revar_def, revar_ssh_def]
  \\ once_rewrite_tac [revar_ssh_shift] \\ rw []
QED

Theorem revar_ReorderAdd:
  revar (ReorderAdd n1 n2 v::rn) n =
  (let m = revar rn n in
     if m < n1 then m + n2 + v
     else if m < n1 + n2 then m − n1
     else m + v)
Proof
  fs [revar_def, revar_ssh_def]
QED

Definition env_rel_def:
  env_rel rn env env' <=>
    (!n. n < LENGTH env ==>
           revar rn n < LENGTH env' /\ EL (revar rn n) env' = EL n env) /\
    (!n. LENGTH env <= n ==> LENGTH env' <= revar rn n)
End

Theorem env_rel_nil:
  !env. env_rel [] env env
Proof
  fs [env_rel_def]
QED

Theorem env_rel_Push:
  !rn env env' ws p.
    env_rel rn env env' /\ LENGTH ws = p ==>
    env_rel (Push p::rn) env (ws ++ env')
Proof
  rw [env_rel_def] \\ res_tac \\ fs [EL_APPEND_EQN]
QED

Theorem env_rel_Delay:
  !rn env env' ws d.
    env_rel rn env env' /\ LENGTH ws = d ==>
    env_rel (Delay d::rn) (ws ++ env) (ws ++ env')
Proof
  rw [env_rel_def, revar_Delay] \\ rw [] \\ fs [EL_APPEND_EQN]
  \\ first_x_assum (qspec_then `n - LENGTH ws` mp_tac) \\ fs []
QED

Theorem env_rel_ReorderAdd:
  !rn env as bs env2 ws n1 n2 v.
    env_rel rn env (as ++ bs ++ env2) /\
    LENGTH as = n1 /\ LENGTH bs = n2 /\ LENGTH ws = v ==>
    env_rel (ReorderAdd n1 n2 v::rn) env (bs ++ ws ++ as ++ env2)
Proof
  rw [env_rel_def, revar_ReorderAdd] \\ res_tac \\ rw [] \\ fs [EL_APPEND_EQN]
QED

Definition letrest_def:
  letrest xs e pvs env s =
    case evaluate (xs, env, s) of
      (Rval nvs, s2) => evaluate ([e], pvs ++ nvs ++ env, s2)
    | res => res
End

Theorem letrest_CONS:
  !x xs e pvs env s v s'.
    evaluate ([x], env, s) = (Rval [v], s') ==>
    letrest (x::xs) e pvs env s = letrest xs e (pvs ++ [v]) env s'
Proof
  rw [letrest_def]
  \\ once_rewrite_tac [evaluate_CONS] \\ fs []
  \\ every_case_tac \\ fs [evaluate_def]
  >> ‘pvs ++ v::a ++ env = pvs ++ [v] ++ a ++ env’ by rw[]
  >> gvs[]
QED

Theorem letrest_CONS_err:
  !x xs e pvs env s err s'.
    evaluate ([x], env, s) = (Rerr err, s') ==>
    letrest (x::xs) e pvs env s = (Rerr err, s')
Proof
  rw [letrest_def]
  \\ once_rewrite_tac [evaluate_CONS] \\ fs []
QED

Theorem renames_err:
  !xs rs bs e racc envT t err t'.
    evaluate (REVERSE racc, envT, t) = (Rerr err, t') ==>
    evaluate ([renames rs bs xs e racc], envT, t) = (Rerr err, t')
Proof
  Induct_on ‘xs’
  >- rw[rename_def, evaluate_def]
  >> rw[]
  >> Cases_on ‘h’ >> rw[rename_def]
  >~ [‘LetCall’]
  >- (Cases_on ‘racc = []’ >> gvs[evaluate_def, list_case_compute]
      >> subgoal ‘¬NULL racc’
      >- (Cases_on ‘racc’ >> gvs[]
         )
      >> rw[evaluate_def]
     )

  >> first_x_assum $ irule
  >> PURE_REWRITE_TAC[Once CONS_APPEND, REVERSE_APPEND]
  >> rw[evaluate_APPEND]
QED


   
Theorem rename_eq:
  (!rs x env env' (s: ('a,'b) state).
     env_rel rs env env' ==>
     evaluate ([rename rs x], env', s) = evaluate ([x], env, s)) /\
  (!rs xs env env' (s: ('a,'b) state).
     env_rel rs env env' ==>
     evaluate (renamel rs xs, env', s) = evaluate (xs, env, s)) /\
  (!rs bs xs e racc env envT pvs qvs (s: ('a,'b) state) t0.
     env_rel bs env envT /\
     (!nvs. LENGTH nvs = LENGTH xs ==>
              env_rel rs (pvs ++ nvs ++ env) (qvs ++ nvs ++ envT)) /\
     evaluate (REVERSE racc, envT, t0) = (Rval qvs, s) ==>
     evaluate ([renames rs bs xs e racc], envT, t0) = letrest xs e pvs env s)
Proof
  ho_match_mp_tac rename_ind \\ rw []
  >- (gvs[env_rel_def, evaluate_def, rename_def, revar_def,revar_ssh_def]
      >> rw[] >> gvs[NOT_LESS]
      >- (first_x_assum $ qspec_then ‘n’ assume_tac >> gvs[]
         )
      >> last_x_assum $ qspec_then ‘n’ assume_tac >> gvs[]
     )
  >- (rw[evaluate_def, rename_def]
      >> subgoal ‘evaluate ([rename rs x],env',s) = evaluate ([x],env,s)’
      >- (first_x_assum $ irule
          >> rw[]
         )
      >> rw[]
      >> CASE_TAC >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> rw[]
     )
  >- (gvs[evaluate_def, rename_def, letrest_def]
      >> first_x_assum $ qspecl_then [‘env’, ‘env'’, ‘[]’, ‘s’] assume_tac >> gvs[]
      >> pop_assum $ irule
      >> rw[env_rel_Delay]
     )
  >- (rw[evaluate_def, rename_def]
      >> subgoal ‘evaluate ([rename rs x],env',s) = evaluate ([x],env,s)’
      >- (first_x_assum $ irule
          >> rw[]
         )
      >> rw[]
     )
  >- rw[evaluate_def, rename_def]
  >- (gvs[evaluate_def, rename_def]
      >> subgoal ‘IS_SOME (OPTION_MAP (λa. rename (Delay 1::rs) a) hdl) = IS_SOME hdl’
      >- (Cases_on ‘hdl’ >> rw[]
         )
      >> rw[]
      >> subgoal ‘evaluate (renamel rs xs,env',s) = evaluate (xs,env,s)’
      >- (first_x_assum irule
          >> rw[]
         )
      >> CONV_TAC $ DEPTH_CONV ETA_CONV
      >> rw[]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘find_code fn a r.code’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >> Cases_on ‘e’ >> gvs[]
      >> Cases_on ‘a'’ >> gvs[]
      >> Cases_on ‘hdl’ >> gvs[]
      >> subgoal ‘evaluate ([rename (Delay 1::rs) x],v::env',r'') = evaluate ([x],v::env,r'')’
      >- (first_x_assum $ irule
          >> PURE_ONCE_REWRITE_TAC[CONS_APPEND]
          >> irule $ PURE_ONCE_REWRITE_RULE [CONS_APPEND] env_rel_Delay
          >> rw[]
         )
      >> rw[]
     )
  >- (gvs[env_rel_def, evaluate_def, rename_def, revar_def, revar_ssh_def, NOT_LESS]
      >> Cases_on ‘LENGTH env ≤ n’ >> rw[]
      >> gvs[NOT_LESS_EQUAL]
      >> first_x_assum $ drule_then assume_tac
      >> gvs[]
      >> gvs[dest_thunk_def]
     )
  >- (gvs[evaluate_def, rename_def, revar_def, revar_ssh_def]
      >> subgoal ‘evaluate (renamel rs xs,env',s) = evaluate (xs,env,s)’
      >- (first_x_assum irule
          >> rw[]
         )
      >> rw[]
     )
  >- (gvs[evaluate_def, rename_def, revar_def, revar_ssh_def]
      >> subgoal ‘evaluate (renamel rs xs,env',s) = evaluate (xs,env,s)’
      >- (first_x_assum irule
          >> rw[]
         )
      >> rw[]
      >> Cases_on ‘evaluate (xs,env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘find_code (SOME fn) a r.code’ >> gvs[]
      >> Cases_on ‘x'’ >> gvs[]
      >> Cases_on ‘r.clock < ticks + 1’ >> gvs[]
      >> Cases_on ‘evaluate ([r'],q,dec_clock (ticks + 1) r)’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >> Cases_on ‘e’ >> gvs[]
      >> Cases_on ‘a'’ >> gvs[]
      >> Cases_on ‘LENGTH l = nret’ >> gvs[]
      >> first_x_assum $ irule
      >> PURE_ONCE_REWRITE_TAC[CONS_APPEND]
      >> irule $ PURE_ONCE_REWRITE_RULE [CONS_APPEND] env_rel_Delay
      >> rw[]
     )
  >- (gvs[evaluate_def, rename_def, revar_def, revar_ssh_def]
      >> subgoal ‘evaluate (renamel rs xs,env',s) = evaluate (xs,env,s)’
      >- (first_x_assum irule
          >> rw[]
         )
      >> rw[]
     )
  >- rw[rename_def, evaluate_def]
  >- (rw[rename_def]
      >> once_rewrite_tac [evaluate_CONS]
      >> ntac 2 (first_x_assum (drule_then assume_tac))
      >> gvs[]
     )
  >- rw[evaluate_def, letrest_def, rename_def]
  >> Cases_on ‘x’ >> rw[]
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Var n],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Var n]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([If e' e0 e1],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[If e' e0 e1]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Let l e'],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Let l e']’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Raise e'],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Raise e']’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Tick e'],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Tick e']’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Call n o0 l o'],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Call n o0 l o']’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
 >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Force n n0],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Force n n0]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
    )
  >- (first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘evaluate ([Op o' l],env,s)’ >> gvs[]
      >> Cases_on ‘q’ >> gvs[]
      >- (assume_tac evaluate_LENGTH
          >> first_x_assum $ qspecl_then [‘[Op o' l]’, ‘env’, ‘s’] assume_tac
          >> gvs[]
          >> Cases_on ‘a’ >> gvs[]
          >> drule_then assume_tac letrest_CONS
          >> gvs[rename_def]
          >> first_x_assum $ irule
          >> rw[evaluate_APPEND]
          >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
          >> gvs[]
       )
      >> drule_then assume_tac letrest_CONS_err
      >> gvs[]
      >> gvs[rename_def]
      >> irule renames_err
      >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
     )
  >- (rw[rename_def]
      >> Cases_on ‘racc = []’ >> gvs[]
      >- (gvs[evaluate_def, letrest_def]
          >> irule EQ_SYM
          >> PURE_REWRITE_TAC[Once CONS_APPEND, evaluate_APPEND]
          >> rw[evaluate_def]
          >> subgoal ‘evaluate (renamel (Push 0::bs) l,envT,s) = evaluate (l,env,s)’
          >- (first_x_assum irule
              >> ‘env_rel (Push 0::bs) env ([] ++ envT)’ suffices_by rw[]
              >> irule env_rel_Push
              >> rw[]
             )
          >> rw[]
          >> Cases_on ‘evaluate (l,env,s)’ >> rw[]
          >> Cases_on ‘q’ >> gvs[]
          >> Cases_on ‘find_code (SOME n) a r.code’ >> gvs[]
          >> Cases_on ‘x’ >> gvs[]
          >> Cases_on ‘r.clock < n0 + 1’ >> gvs[]
          >> Cases_on ‘evaluate ([r'],q,dec_clock (n0 + 1) r)’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
          >> Cases_on ‘e''’ >> gvs[]
          >> Cases_on ‘a'’ >> gvs[]
          >> Cases_on ‘LENGTH l' = n1’ >> gvs[]
          >> Cases_on ‘evaluate ([e'],l' ++ env,r'')’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
          >- (irule EQ_SYM
              >> irule EQ_TRANS
              >> first_assum $ irule_at Any
              >> irule_at Any env_rel_Push
              >> last_assum $ irule_at Any
              >> rw[]
              >> irule_at Any EQ_TRANS
              >> last_assum $ irule_at Any
              >> first_assum $ irule_at Any
              >> irule_at Any env_rel_Delay

              >> qexists ‘pvs ++ a'’ >> rw[]
              >- (‘env_rel (Push 0::bs) env ([] ++ envT)’ suffices_by rw[]
                  >> irule env_rel_Push
                  >> rw[]
                 )
              >- (last_x_assum $ qspec_then ‘a'++ nvs’ mp_tac
                  >> impl_tac
                  >- (assume_tac evaluate_LENGTH
                      >> pop_assum $ qspecl_then [‘[e']’, ‘l' ++ env’, ‘r''’] assume_tac
                      >> gvs[]
                     )
                  >> rw[]
                  >> ‘env_rel rs (pvs ++ a' ++ nvs ++ env) ([] ++ (a' ++ nvs) ++ envT)’ by rw[]
                  >> drule_then assume_tac env_rel_ReorderAdd
                  >> gvs[]
                  >> assume_tac evaluate_LENGTH
                  >> pop_assum $ qspecl_then [‘[e']’, ‘l' ++ env’, ‘r''’] assume_tac
                  >> gvs[]
                 )

              >> Cases_on ‘evaluate (xs,env,r'³')’ >> gvs[]
              >> Cases_on ‘q'’ >> gvs[]
             )
          >> irule EQ_SYM
          >> irule EQ_TRANS
          >> irule_at Any renames_err
          >> rw[]
          >> irule EQ_TRANS
          >> pop_assum $ irule_at Any
          >> first_x_assum $ irule_at Any
          >> irule env_rel_Delay
          >> rw[]
          >> ‘env_rel (Push 0::bs) env ([] ++ envT)’ suffices_by rw[]
          >> irule env_rel_Push
          >> rw[]
         )
      >> gvs[evaluate_def, letrest_def, list_case_compute]
      >> subgoal ‘¬NULL racc’
      >- (Cases_on ‘racc’ >> gvs[]
         )
      >> gvs[evaluate_def]
      >> assume_tac evaluate_LENGTH
      >> pop_assum $ qspecl_then [‘REVERSE racc’, ‘envT’, ‘t0’] assume_tac >> gvs[]
      >> subgoal ‘evaluate (renamel (Push (LENGTH qvs)::bs) l, qvs ++ envT,s) = evaluate (l,env,s)’
      >- (first_x_assum irule
          >> rw[]
          >> irule env_rel_Push
          >> rw[]
         )
      >> gvs[]
      >> irule EQ_SYM
      >> PURE_REWRITE_TAC[Once CONS_APPEND, evaluate_APPEND]
      >> rw[evaluate_def]
      >> Cases_on ‘evaluate (l,env,s)’ >> rw[]
      >> Cases_on ‘q’ >> gvs[]
      >> Cases_on ‘find_code (SOME n) a r.code’ >> gvs[]
      >> Cases_on ‘x’ >> gvs[]
      >> Cases_on ‘r.clock < n0 + 1’ >> gvs[]
      >> Cases_on ‘evaluate ([r'],q,dec_clock (n0 + 1) r)’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >> Cases_on ‘e''’ >> gvs[]
      >> Cases_on ‘a'’ >> gvs[]
      >> Cases_on ‘LENGTH l' = n1’ >> gvs[]
      >> Cases_on ‘evaluate ([e'],l' ++ env,r'')’ >> gvs[]
      >> Cases_on ‘q'’ >> gvs[]
      >- (irule EQ_SYM
          >> irule EQ_TRANS
          >> first_assum $ irule_at Any
          >> irule_at Any env_rel_Push
          >> last_assum $ irule_at Any
          >> rw[]
          >> irule_at Any EQ_TRANS
          >> qpat_x_assum ‘∀_ _ _. _ ⇒ _ = _’ $ irule_at Any
          >> PURE_REWRITE_TAC [Once $ GSYM APPEND_ASSOC]
          >> irule_at Any env_rel_Delay
          >> rw[]
          >> irule_at Any env_rel_Push
          >> last_x_assum $ irule_at Any
          >> rw[]

          >> qexists ‘pvs ++ a'’ >> rw[]
          >- (last_x_assum $ qspec_then ‘a'++ nvs’ mp_tac
              >> impl_tac
              >- (assume_tac evaluate_LENGTH
                  >> pop_assum $ qspecl_then [‘[e']’, ‘l' ++ env’, ‘r''’] assume_tac
                  >> gvs[]
                 )
              >> rw[]
              >> ‘env_rel rs (pvs ++ a' ++ nvs ++ env) (qvs ++ (a' ++ nvs) ++ envT)’ by rw[]
              >> drule_then assume_tac env_rel_ReorderAdd
              >> gvs[]
              >> assume_tac evaluate_LENGTH
              >> pop_assum $ qspecl_then [‘[e']’, ‘l' ++ env’, ‘r''’] assume_tac
              >> gvs[]
             )
          >> Cases_on ‘evaluate (xs,env,r'³')’ >> gvs[]
          >> Cases_on ‘q'’ >> gvs[]
         )
      >> irule EQ_SYM
      >> irule EQ_TRANS
      >> irule_at Any renames_err
      >> rw[]
      >> irule EQ_TRANS
      >> pop_assum $ irule_at Any
      >> first_x_assum $ irule_at Any
      >> PURE_ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]
      >> irule env_rel_Delay
      >> rw[]
      >> irule env_rel_Push
      >> rw[]
     )
  >> first_x_assum $ qspecl_then [‘env’, ‘envT’, ‘s’] assume_tac
  >> gvs[]
  >> Cases_on ‘evaluate ([Return l],env,s)’ >> gvs[]
  >> Cases_on ‘q’ >> gvs[]
  >- (assume_tac evaluate_LENGTH
      >> first_x_assum $ qspecl_then [‘[Return l]’, ‘env’, ‘s’] assume_tac
      >> gvs[]
      >> Cases_on ‘a’ >> gvs[]
      >> drule_then assume_tac letrest_CONS
      >> gvs[rename_def]
      >> first_x_assum $ irule
      >> rw[evaluate_APPEND]
      >> last_x_assum $ qspec_then ‘[h] ++ nvs’ assume_tac
      >> gvs[]
     )
  >> drule_then assume_tac letrest_CONS_err
  >> gvs[]
  >> gvs[rename_def]
  >> irule renames_err
  >> rw[REVERSE_SNOC_DEF, SNOC_APPEND, evaluate_APPEND]
QED

Theorem renamel_eq = CONJUNCT1 (CONJUNCT2 rename_eq)

Theorem lc_unfold_eq:
  !e env s. evaluate ([lc_unfold e], env, s) = evaluate ([e], env, s)
Proof
  rw [lc_unfold_def]
  \\ irule (CONJUNCT1 rename_eq)
  \\ fs [env_rel_nil]
QED
