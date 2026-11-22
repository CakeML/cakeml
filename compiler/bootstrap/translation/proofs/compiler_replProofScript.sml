(*
  Verification of the function (called repl) that implements the REPL
*)
Theory compiler_replProof
Ancestors
  semanticsProps source_eval_oracleProof[qualified] evalSem[qualified]
  evalSemProps[qualified]
  compiler_mainProg
  evaluate semanticPrimitives ml_translator repl_types
  repl_check_and_tweak repl_init repl_inputRepresentation
Libs
  preamble

val _ = (max_print_depth := 12);

Definition compiler_inst_def:
  compiler_inst c = (λ(x,y,z).
                do
                  cfg <- v_fun_abs 𝕌(:backend$config) BACKEND_CONFIG_v y;
                  (cfg2,bs,ws) <- compile_inc_progs_for_eval c (x,cfg,z);
                  SOME (BACKEND_CONFIG_v cfg2,bs,ws)
                od)
End

val EqualityType_LIST_TYPE_DEC_TYPE =
  decProgTheory.EqualityType_LIST_TYPE_DEC_TYPE;

val EqualityType_BACKEND_CONFIG_TYPE =
  decodeProgTheory.EqualityType_BACKEND_CONFIG_TYPE;

Theorem LIST_TYPE_AST_DEC_IMP:
  LIST_TYPE DEC_TYPE decs decs_v ⇒
  ∀x. LIST_v DEC_v x = decs_v ⇔ x = decs
Proof
  assume_tac EqualityType_LIST_TYPE_DEC_TYPE
  \\ rw []
  \\ ‘IsTypeRep (LIST_v DEC_v) (LIST_TYPE DEC_TYPE)’ by
      (irule decProgTheory.IsTypeRep_LIST_v
       \\ fs [decProgTheory.IsTypeRep_DEC_v])
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem BACKEND_CONFIG_IMP:
  BACKEND_CONFIG_TYPE c v ⇒
  ∀x. BACKEND_CONFIG_v x = v ⇔ x = c
Proof
  assume_tac EqualityType_BACKEND_CONFIG_TYPE
  \\ rw [] \\ assume_tac decodeProgTheory.IsTypeRep_BACKEND_CONFIG_v
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem v_fun_abs_BACKEND_CONFIG_v:
  BACKEND_CONFIG_TYPE s1 s1_v ⇒
  v_fun_abs 𝕌(:backend$config) BACKEND_CONFIG_v s1_v = SOME s1
Proof
  fs [source_eval_oracleProofTheory.v_rel_abs,BACKEND_CONFIG_IMP]
  \\ strip_tac \\ imp_res_tac BACKEND_CONFIG_IMP \\ fs []
QED

Theorem v_to_word64_list_thm:
  ∀ws ws_v. LIST_TYPE WORD ws ws_v ⇒ v_to_word64_list ws_v = SOME ws
Proof
  Induct \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
                v_to_list_def,list_type_num_def]
  THEN1 EVAL_TAC \\ rw []
  \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
         v_to_list_def,list_type_num_def]
  \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ res_tac \\ fs []
  \\ simp [Once maybe_all_list_def,AllCaseEqs()]
  \\ gvs [ml_translatorTheory.WORD_def]
  \\ EVAL_TAC
QED

Theorem v_to_mlstring_thm:
  ∀bs bs_v. STRING_TYPE bs bs_v ⇒ v_to_mlstring bs_v = SOME bs
Proof
  fs [ml_translatorTheory.STRING_TYPE_def,v_to_mlstring_def]
QED

Theorem evaluate_Con = SIMP_CONV std_ss [evaluateTheory.evaluate_def,do_con_check_def,build_conv_def]
  “evaluate$evaluate (st:'ffi semanticPrimitives$state) env [Con NONE xs]”;

Theorem evaluate_Var = SIMP_CONV std_ss [evaluateTheory.evaluate_def,do_con_check_def]
  “evaluate$evaluate (st:'ffi semanticPrimitives$state) env [Var n]”;

Theorem evaluate_Lit = SIMP_CONV std_ss [evaluate_def]
  “evaluate$evaluate (st:'ffi semanticPrimitives$state) env [Lit n]”;

Theorem evaluate_list = List.take (evaluateTheory.evaluate_def |> CONJUNCTS,2) |> LIST_CONJ;

Theorem evaluate_App_Opapp = SIMP_CONV std_ss [evaluateTheory.evaluate_def,REVERSE_DEF,APPEND]
  “evaluate$evaluate (st:'ffi semanticPrimitives$state) env [App Opapp [f;x]]”;

Theorem Arrow_IMP:
  ∀x v (s:'ffi semanticPrimitives$state).
    (a --> b) (f:'a -> 'b) vv ∧ a x v ⇒
    ∃env exp junk u ck s1 res po.
      do_opapp [vv; v] = SOME (env,exp) ∧ b (f x) u ∧
      evaluate s env [exp] = (s1,res) ∧
      (res ≠ Rerr (Rabort Rtimeout_error) ⇒
        s1 = s with <| clock := s.clock - ck; refs := s.refs ++ junk;
                       ptr_eq_oracle := po |> ∧
        res = Rval [u])
Proof
  rw [Arrow_def,
      ml_translatorTheory.AppReturns_def]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [‘s.refs’,‘s.ptr_eq_oracle’] strip_assume_tac)
  \\ fs [] \\ pop_assum $ irule_at Any
  \\ drule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def] \\ strip_tac
  \\ drule evaluatePropsTheory.evaluate_set_init_clock
  \\ fs [] \\ disch_then (qspec_then ‘s.clock’ strip_assume_tac)
  \\ rw [] \\ ‘(s with clock := s.clock) = (s:'ffi semanticPrimitives$state)’ by
               fs [semanticPrimitivesTheory.state_component_equality]
  \\ gvs []
  \\ gvs [semanticPrimitivesTheory.state_component_equality]
  \\ qspecl_then [‘s’,‘env’,‘[exp]’] mp_tac
       (evaluatePropsTheory.is_clock_io_mono_evaluate |> CONJUNCT1)
  \\ fs [evaluatePropsTheory.is_clock_io_mono_def,LESS_EQ_EXISTS]
  \\ strip_tac \\ fs []
  \\ qexists_tac ‘p’ \\ fs []
QED

(* a run from a state without an eval state that does not touch the ffi or
   the stamps can be replayed from any state that agrees on the store and
   the pointer equality oracle *)
Theorem evaluate_transfer:
  evaluate (s0:'a semanticPrimitives$state) env xs = (s1,res) ∧
  s0.eval_state = NONE ∧
  s1.ffi = s0.ffi ∧ s1.next_type_stamp = s0.next_type_stamp ∧
  s1.next_exn_stamp = s0.next_exn_stamp ∧
  (∀outcome. res ≠ Rerr (Rabort (Rffi_error outcome))) ∧
  (s:'ffi semanticPrimitives$state).eval_state = NONE ∧ s.refs = s0.refs ∧
  s.ptr_eq_oracle = s0.ptr_eq_oracle ∧ s.clock = s0.clock ⇒
  evaluate s env xs =
    (s with <| refs := s1.refs; clock := s1.clock;
               ptr_eq_oracle := s1.ptr_eq_oracle |>, res)
Proof
  strip_tac
  \\ drule_all (INST_TYPE [“:'b” |-> “:'ffi”]
                 (CONJUNCT1 evaluatePropsTheory.evaluate_ffi_intro))
  \\ disch_then (qspec_then ‘s.ffi’ assume_tac)
  \\ drule (CONJUNCT1 evaluatePropsTheory.evaluate_set_next_stamps)
  \\ simp [] \\ disch_then (qspec_then ‘s.next_type_stamp’ assume_tac o CONJUNCT1)
  \\ drule (CONJUNCT1 evaluatePropsTheory.evaluate_set_next_stamps)
  \\ simp [] \\ disch_then (qspec_then ‘s.next_exn_stamp’ assume_tac o CONJUNCT2)
  \\ drule (Q.INST [‘eo’ |-> ‘(s:'ffi semanticPrimitives$state).eval_oracle’]
               (CONJUNCT1 evaluatePropsTheory.eval_no_eval_oracle))
  \\ simp [] \\ strip_tac
  \\ ‘s = s0 with <| ffi := s.ffi; next_type_stamp := s.next_type_stamp;
                     next_exn_stamp := s.next_exn_stamp;
                     eval_oracle := s.eval_oracle |>’
    by simp [semanticPrimitivesTheory.state_component_equality]
  \\ pop_assum SUBST1_TAC
  \\ gvs [semanticPrimitivesTheory.state_component_equality]
QED

(* translator certificates as runs whose clock, new references, pointer
   equality oracle and result depend only on the store and the pointer
   equality oracle of the state they start from *)
Theorem Arrow_IMP_exact:
  (a --> b) f vv ∧ a x v ⇒
  ∃env exp.
    do_opapp [vv; v] = SOME (env,exp) ∧
    ∀refs po. ∃junk po' u.
      b (f x) u ∧
      ∀k. ∃ck. ∀(s:'ffi semanticPrimitives$state).
        s.eval_state = NONE ∧ s.refs = refs ∧ s.ptr_eq_oracle = po ⇒
        evaluate (s with clock := ck) env [exp] =
          (s with <| clock := k; refs := refs ++ junk;
                     ptr_eq_oracle := po' |>, Rval [u])
Proof
  rw [Arrow_def, ml_translatorTheory.AppReturns_def]
  \\ first_assum drule
  \\ disch_then (qspecl_then [‘[]’,‘ARB’] strip_assume_tac)
  \\ qexistsl_tac [‘env’,‘exp’] \\ rw []
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [‘refs’,‘po’] strip_assume_tac)
  \\ gvs [ml_progTheory.eval_rel_def]
  \\ qexistsl_tac [‘refs''’,‘po''’,‘u'’] \\ rw []
  \\ drule evaluatePropsTheory.evaluate_set_clock
  \\ simp [] \\ disch_then (qspec_then ‘k’ strip_assume_tac) \\ fs []
  \\ qexists_tac ‘ck1''’ \\ rw []
  \\ drule evaluate_transfer
  \\ disch_then (qspec_then ‘(s:'ffi semanticPrimitives$state) with clock := ck1''’
                   mp_tac)
  \\ simp [ml_translatorTheory.build_state_def,
           ml_translatorTheory.empty_state_def]
QED

(* automation proving data_v for the value-embedding functions generated
   by the translator *)

val data_v_simps = prove(“
  data_v (Litv l) ∧
  (data_v (Conv c vs) ⇔ data_v_list vs) ∧
  (data_v_list [] ⇔ T) ∧
  (data_v_list (v::vs) ⇔ data_v v ∧ data_v_list vs)”,
  rpt conj_tac \\ simp [Once semanticPrimitivesTheory.data_v_def]);

val v_ty = “:v”;

fun is_vfun c =
  is_const c andalso
  (let val {Name,...} = dest_thy_const c
       val (_,r) = strip_fun (type_of c)
   in r = v_ty andalso
      (String.isSuffix "_v" Name orelse String.isSubstring "_v_aux" Name)
   end handle HOL_ERR _ => false);

fun generic c = let val {Thy,Name,...} = dest_thy_const c
                in prim_mk_const {Thy=Thy,Name=Name} end;

fun base_name Name =
  let val ss = Substring.full Name
      val (pre, suf) = Substring.position "_v_aux" ss
  in if Substring.isEmpty suf then Name
     else Substring.string pre ^ "_v" end;

fun def_of c = let val {Thy,Name,...} = dest_thy_const c
               in DB.fetch Thy (base_name Name ^ "_def") end;
fun ind_of c = let val {Thy,Name,...} = dest_thy_const c
               in SOME (DB.fetch Thy (base_name Name ^ "_ind"))
                  handle HOL_ERR _ => NONE end;

fun vfuns_in tm =
  HOLset.listItems
    (HOLset.addList (empty_tmset, map generic (find_terms is_vfun tm)));

val proved = ref ([] : (term * thm) list);
fun lemmas () = map snd (!proved);
fun is_proved c = List.exists (fn (d,_) => aconv d c) (!proved);

fun mk_goal c = let
  val tys = fst (strip_fun (type_of c))
  val params = List.take (tys, length tys - 1)
  val argty = List.last tys
  val fs = mapi (fn i => fn ty => mk_var ("f" ^ Int.toString i, ty)) params
  val hyps = map (fn f => let val y = mk_var ("y", fst (dom_rng (type_of f)))
                          in mk_forall (y, mk_comb (“data_v”, mk_comb (f, y))) end) fs
  val x = mk_var ("x", argty)
  val c_tm = mk_forall (x, mk_comb (“data_v”, list_mk_comb (c, fs @ [x])))
  in list_mk_imp (hyps, c_tm) end;

(* the lemmas for parametric functions (LIST_v, PAIR_v, ...) have
   hypotheses (∀y. data_v (f y)), which simp does not discharge for nested
   instantiations, so these are applied with irule *)
fun dv_tac simps =
  rw simps \\
  rpt ((gen_tac ORELSE FIRST (map (fn th => irule th) (lemmas ())) ORELSE
        first_assum irule) \\ rw simps);

fun prove_one c = let
  val def = def_of c
  val goal = mk_goal c
  fun try_tacs [] = failwith ("cannot prove data_v for " ^ term_to_string c)
    | try_tacs (t::ts) = (prove (goal, t) handle HOL_ERR _ => try_tacs ts)
  val simps = def :: data_v_simps :: semanticPrimitivesTheory.Boolv_def :: lemmas ()
  in try_tacs
     [dv_tac simps,
      rpt disch_tac \\ Cases \\ dv_tac simps,
      rpt disch_tac \\ Induct \\ dv_tac simps]
  end;

fun group_of c =
  HOLset.listItems (HOLset.addList (empty_tmset,
    map (generic o fst o strip_comb o lhs o snd o strip_forall)
        (strip_conj (concl (def_of c)))));

fun dfs c =
  if is_proved c then () else let
    val group = group_of c
    val def = def_of c
    val deps = List.filter (fn d => not (List.exists (aconv d) group))
                 (vfuns_in (concl def))
    val _ = List.app dfs deps
    in if length group = 1 then
         proved := (c, prove_one c) :: !proved
       else let
         val _ = print ("\nGROUP: " ^ String.concatWith ", " (map term_to_string group) ^ "\n")
         val ind = case ind_of c of SOME i => i
                   | NONE => (print "NO IND\n"; raise Option)
         val (Ps, body) = strip_forall (concl ind)
         val concl_ind = snd (dest_imp body)
         val lhss = map (lhs o snd o strip_forall) (strip_conj (concl def))
         fun applied l = let val (h, args) = strip_comb l
                         in (list_mk_comb (h, List.take (args, length args - 1)),
                             type_of (List.last args)) end
         val apps = map applied lhss
         fun inst_for P = let
           val (argtys, _) = strip_fun (type_of P)
           val ty = List.last argtys
           val (f, _) = case List.find (fn (_, aty) => aty = ty) apps of
                          SOME x => x
                        | NONE => (print ("NO APP for " ^ type_to_string ty ^ "\n");
                                   raise Option)
           val h = fst (strip_comb f)
           val args = mapi (fn i => fn t => mk_var ("a" ^ Int.toString i, t)) argtys
           val fargs = List.take (args, length args - 1)
           val hyps = map (fn a => let val z = mk_var ("z", fst (dom_rng (type_of a)))
                            in mk_forall (z, mk_comb (“data_v”, mk_comb (a, z))) end) fargs
           val body = list_mk_imp (hyps, mk_comb (“data_v”, list_mk_comb (h, args)))
           in P |-> list_mk_abs (args, body) end
         val concl_goal = rhs (concl (QCONV (DEPTH_CONV BETA_CONV)
                                  (subst (map inst_for
                                     (List.filter (fn P => snd (strip_fun (type_of P)) = bool) Ps))
                                     concl_ind)))
         val goal = concl_goal
         val simps = def :: data_v_simps :: semanticPrimitivesTheory.Boolv_def :: lemmas ()
         val th = prove (goal, ho_match_mp_tac ind \\ dv_tac simps)
         in List.app (fn t => let
              val f = t |> concl |> strip_forall |> snd |> strip_imp |> snd
                        |> rand |> strip_comb |> fst
              in proved := (generic f, t) :: !proved end) (CONJUNCTS th)
         end
  end;

fun data_v_thm c = (dfs c; snd (valOf (List.find (fn (d,_) => aconv d c) (!proved))));

Theorem data_v_DEC_v = data_v_thm “AstProg$DEC_v”;

Theorem data_v_BACKEND_CONFIG_v = data_v_thm “from_labProg$BACKEND_CONFIG_v”;

Theorem data_v_LIST_v = data_v_thm (generic “LIST_v”);

Theorem LIST_TYPE_DEC_TYPE_decode:
  LIST_TYPE DEC_TYPE decs decs_v ∧ decs_allowed decs ⇒
  data_v decs_v ∧ v_fun_abs decs_allowed (LIST_v DEC_v) decs_v = SOME decs
Proof
  strip_tac
  \\ ‘decs_v = LIST_v DEC_v decs’ by metis_tac [LIST_TYPE_AST_DEC_IMP]
  \\ gvs [source_eval_oracleProofTheory.v_rel_abs]
  \\ conj_tac >- (irule data_v_LIST_v \\ simp [data_v_DEC_v])
  \\ drule LIST_TYPE_AST_DEC_IMP \\ simp []
  \\ DEEP_INTRO_TAC some_intro \\ simp [IN_DEF]
QED

Overload eval_res_stamp[local] =
  (COMPILER_MAINPROG_EVAL_RES_TYPE_def
   |> concl |> find_term (can (match_term “TypeStamp _ _ _”)) |> rator |> rand);

Theorem nsLookup_Short_nsBind[local]:
  nsLookup_Short (nsBind n v e) m =
    (if n = m then SOME v else nsLookup_Short e m) ∧
  nsLookup_Short nsEmpty m = NONE
Proof
  rw [ml_progTheory.nsLookup_Short_def]
QED

Theorem eval_env_lookups[local] =
  “nsLookup (merge_env compiler_mainProg_env_8 init_env).v (Short «=») = SOME eq_v ∧
   nsLookup (merge_env compiler_mainProg_env_8 init_env).v (Short «eval_prim») =
     SOME eval_prim_v”
  |> (DEPTH_CONV ml_progLib.nsLookup_conv THENC SIMP_CONV (srw_ss()) [])
  |> EQT_ELIM |> REWRITE_RULE [ml_progTheory.nsLookup_eq];

val eval_thms =
  [evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def,
   namespaceTheory.nsOptBind_def,build_rec_env_def,eval_env_lookups,
   do_opapp_def,mlbasicsProgTheory.eq_v_def,nsLookup_Short_nsBind,
   do_app_def,do_eq_def,do_if_def,Boolv_def,do_con_check_def,
   build_conv_def,lit_same_type_def,declare_env_def,
   reset_env_generation_def,markerTheory.Abbrev_def];

Theorem evaluate_eval:
  ∀(st:'ffi semanticPrimitives$state).
    st.eval_state = SOME s ∧
    s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
    s.env_id_counter = (cur_gen1,next_id1,next_gen1) ∧
    decs_allowed decs ∧
    nsLookup env.v (Short eval_str) = SOME eval_v ⇒
    nsLookup env.v (Short arg_str) =
      SOME (Conv NONE [Env env1 env_id; decs_v]) ∧
    LIST_TYPE DEC_TYPE decs decs_v ∧
    (∀ck junk po st1 res.
       evaluate_decs (st with <|clock := st.clock − ck; refs := st.refs ++ junk;
                                eval_state := NONE; ptr_eq_oracle := po |>)
         env1 decs = (st1,res) ⇒ res ≠ Rerr (Rabort Rtype_error)) ⇒
    ∃res s1 ck msg junk po.
      evaluate st env [App Opapp [Var (Short eval_str); Var (Short arg_str)]] =
        (s1,res) ∧
      (res ≠ Rerr (Rabort Rtimeout_error) ⇒
       res = Rval
             [Conv (SOME (TypeStamp «Compile_error» eval_res_stamp 0))
                   [Litv (StrLit msg)]] ∧
       s1 = st with <|clock := st.clock − ck; refs := st.refs ++ junk;
                      ptr_eq_oracle := po|> ∨
       (∃f. res = Rerr (Rabort (Rffi_error f))) ∨
       (∃exn st7 ck1 ck2.
          evaluate_decs (st with
                           <|clock := st.clock − ck1; refs := st.refs ++ junk;
                             eval_state := NONE; ptr_eq_oracle := po|>)
            env1 decs = (st7,Rerr (Rraise exn)) ∧
          res = Rval [Conv (SOME (TypeStamp «Eval_exn» eval_res_stamp 2)) [exn]] ∧
          s1 = st7 with <| clock := st7.clock - ck2 ;
                           eval_state := SOME
                             (s with <|env_id_counter := (cur_gen1,next_id1,next_gen1 + 1);
                                       history := s.history ++ [(env_id,decs_v)]|>) |>) ∨
       (∃env2 st7 ck1 ck2.
          evaluate_decs (st with
                           <|clock := st.clock − ck1; refs := st.refs ++ junk;
                             eval_state := NONE; ptr_eq_oracle := po|>)
            env1 decs = (st7,Rval env2) ∧
          res = Rval [Conv (SOME (TypeStamp «Eval_result» eval_res_stamp 1))
                        [Env (extend_dec_env env2 env1) (next_gen1,0)]] ∧
          s1 = st7 with <| clock := st7.clock - ck2 ;
                           eval_state := SOME
                             (s with <|env_id_counter := (cur_gen1,next_id1,next_gen1 + 1);
                                       history := s.history ++ [(env_id,decs_v)]|>) |>))
Proof
  rpt strip_tac \\ gvs []
  \\ simp [evaluate_def,eval_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def,
           build_rec_env_def,namespaceTheory.nsOptBind_def,do_con_check_def,
           build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [do_opapp_def,eval_prim_v_def,dec_clock_def]
  \\ IF_CASES_TAC >- simp []
  \\ simp [evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [do_eval_init_def]
  \\ drule_all LIST_TYPE_DEC_TYPE_decode \\ strip_tac
  \\ simp [do_eval_res_def,do_eval_def]
  \\ Cases_on ‘FST (st.eval_oracle (s.initialised,s.history,env_id,decs_v))’
  \\ simp []
  >- (
    IF_CASES_TAC >- simp []
    \\ qabbrev_tac ‘es1 = s with <|env_id_counter := (next_gen1,0,next_gen1 + 1);
                                    history := s.history ++ [(env_id,decs_v)]|>’
    \\ ‘∃st7 r. evaluate_decs (st with <|clock := st.clock − 3; refs := st.refs ++ [];
                                         eval_state := NONE;
                                         ptr_eq_oracle := shift_seq 1 st.ptr_eq_oracle|>)
                   env1 decs = (st7,r)’ by metis_tac [PAIR]
    \\ ‘r ≠ Rerr (Rabort Rtype_error)’ by metis_tac []
    \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> last
               |> Q.INST [‘es’ |-> ‘SOME es1’])
    \\ simp [] \\ disch_then (qspec_then ‘es1’ strip_assume_tac)
    \\ gvs [evaluateTheory.dec_clock_def]
    \\ ‘st with <|clock := st.clock − 3; refs := st.refs; eval_state := SOME es1;
                  ptr_eq_oracle := shift_seq 1 st.ptr_eq_oracle|> =
        st with <|clock := st.clock − 3; eval_state := SOME es1;
                  ptr_eq_oracle := shift_seq 1 st.ptr_eq_oracle|>’
      by simp [semanticPrimitivesTheory.state_component_equality]
    \\ gvs []
    \\ Cases_on ‘r’
    >- (
      gvs eval_thms
      \\ IF_CASES_TAC >- simp []
      \\ simp eval_thms
      \\ IF_CASES_TAC >- simp []
      \\ simp eval_thms
      \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
      \\ qexistsl_tac [‘[]’,‘shift_seq 1 st.ptr_eq_oracle’,‘a’,‘st7’,‘3’,‘2’]
      \\ gvs [semanticPrimitivesTheory.state_component_equality])
    \\ Cases_on ‘e’
    \\ gvs eval_thms
    >- (
      qexistsl_tac [‘[]’,‘shift_seq 1 st.ptr_eq_oracle’,‘st7’,‘3’,‘0’]
      \\ gvs [semanticPrimitivesTheory.state_component_equality])
    \\ Cases_on ‘a’ \\ gvs [])
  \\ simp eval_thms
  \\ IF_CASES_TAC >- simp []
  \\ simp eval_thms
  \\ IF_CASES_TAC >- simp []
  \\ simp eval_thms
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ qexistsl_tac [‘4’,‘[]’]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

val _ = map Parse.hide ["types","types_v","parse","parse_v"];

Theorem repl_types_alt:
  repl_types catalogue slots T (ffi,rs) (types,s,env) ∧
  infertype_prog_inc types decs = M_success new_t ⇒
  evaluate_decs s env decs ≠ (new_s,Rerr (Rabort Rtype_error))
Proof
  strip_tac \\ drule repl_types_thm \\ strip_tac
  \\ first_x_assum (qspecl_then
       [‘decs’,‘new_t’,‘new_s’,‘Rerr (Rabort Rtype_error)’] mp_tac) \\ simp []
QED

Theorem repl_types_clock_refs:
  repl_types catalogue slots T (ffi,rs)
    (types,st with eval_state := NONE,env1) ⇒
  repl_types catalogue slots T (ffi,rs)
    (types, st with <| clock := st.clock − ck;
                       refs := st.refs ++ junk;
                       eval_state := NONE;
                       ptr_eq_oracle := po |>,env1)
Proof
  strip_tac \\ drule_then irule repl_types_skip_alt \\ simp []
QED

Theorem evaluate_clock_decs:
  evaluate_decs (s:'ffi semanticPrimitives$state) env xs = (s1,res) ⇒
  s1.clock ≤ s.clock
Proof
  rw []
  \\ qspecl_then [‘s’,‘env’,‘xs’] mp_tac
       (evaluatePropsTheory.is_clock_io_mono_evaluate |> CONJUNCTS |> last)
  \\ fs [evaluatePropsTheory.is_clock_io_mono_def]
QED

Theorem evaluate_decs_with_NONE:
  evaluate_decs (s:'ffi semanticPrimitives$state) env1 safe_decs = (s1,res) ∧
  s.eval_state = NONE ∧
  res ≠ Rerr (Rabort Rtype_error) ⇒
  evaluate_decs s env1 safe_decs = (s1 with eval_state := NONE,res)
Proof
  strip_tac
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> last)
  \\ fs [] \\ rw [GSYM PULL_FORALL]
  \\ fs [state_component_equality]
QED

Overload TYPES_TYPE =
  “PAIR_TYPE ADDPRINTVALS_TYPE_NAMES_TYPE (PAIR_TYPE INFER_INF_ENV_TYPE NUM)”

val (repl_input_binder, repl_input_body) = let
  val sites = find_terms (can (match_term
    “ast$Let _ (ast$App Opapp
        [ast$Ident _; ast$Ident (Long «Repl» (Short «nextInput»))]) _”))
    (concl repl_v_def)
  val site = case sites of
      [site] => site
    | _ => failwith "Expected exactly one REPL input read"
  val (binder,_,body) = astSyntax.dest_Let site
  val (_,input_case,_) = astSyntax.dest_Let body
  val _ = astSyntax.dest_Mat input_case
  in (optionSyntax.dest_some binder,input_case) end;

Overload repl_input_name[local] =
  repl_input_binder;

Overload repl_input_case[local] =
  repl_input_body;

fun sum_type_stamp constructor =
  std_preludeTheory.SUM_TYPE_def |> CONJUNCTS
  |> first (fn th => th |> SPEC_ALL |> concl |> lhs |> rator |> rand
                        |> strip_comb |> fst |> same_const constructor)
  |> concl |> find_term semanticPrimitivesSyntax.is_TypeStamp;

Overload repl_input_inl_stamp[local] = (sum_type_stamp ``INL``);

Overload repl_input_inr_stamp[local] = (sum_type_stamp ``INR``);

Overload repl_error_location[local] =
  (repl_moduleProgTheory.errorMessage_def |> CONJUNCT2 |> concl |> rhs
    |> semanticPrimitivesSyntax.dest_Loc |> snd);

Theorem evaluate_repl_input[local]:
  (STRING_TYPE --> SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE)) parse parse_v ∧
  SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) input input_v ∧
  nsLookup env.v (Short repl_input_name) = SOME input_v ∧
  nsLookup env.v (Short «parse») = SOME parse_v ∧
  nsLookup env.c (Short «Inl») = SOME (1,repl_input_inl_stamp) ∧
  nsLookup env.c (Short «Inr») = SOME (1,repl_input_inr_stamp) ⇒
  ∃next_st result.
    evaluate (st:'ffi semanticPrimitives$state) env [repl_input_case] =
      (next_st,result) ∧
    (result ≠ Rerr (Rabort Rtimeout_error) ⇒
      ∃ck junk po normalized_v.
        next_st = st with <|clock := st.clock − ck; refs := st.refs ++ junk;
                            ptr_eq_oracle := po|> ∧
        result = Rval [normalized_v] ∧
        PAIR_TYPE (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE)) STRING_TYPE
          (case input of INL text => (parse text,text) | INR decs => (INR decs,«»))
          normalized_v)
Proof
  Cases_on ‘input’
  >- (
    rename1 ‘SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) (INL source_text) input_v’
    \\ strip_tac
    \\ gvs [std_preludeTheory.SUM_TYPE_def,ml_translatorTheory.STRING_TYPE_def]
    \\ simp [Once evaluate_def,evaluate_Var,can_pmatch_all_def,pmatch_def,same_ctor_def]
    \\ simp [Once evaluate_def,pmatch_def,same_ctor_def,astTheory.pat_bindings_def]
    \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
    \\ ‘STRING_TYPE source_text (Litv (StrLit source_text))’ by
         simp [ml_translatorTheory.STRING_TYPE_def]
    \\ drule_all Arrow_IMP
    \\ disch_then (qspec_then ‘dec_clock st’ (qx_choosel_then
         [‘parser_env’,‘parser_exp’,‘parser_junk’,‘parser_value’,‘parser_ck’,
          ‘parser_st’,‘parser_result’,‘parser_po’] strip_assume_tac))
    \\ simp [] \\ IF_CASES_TAC \\ simp []
    \\ Cases_on ‘parser_result = Rerr (Rabort Rtimeout_error)’
    \\ gvs [dec_clock_def]
    \\ simp [evaluate_Con,evaluate_list,evaluate_Var]
    \\ qexistsl_tac [‘parser_ck + 1’,‘parser_junk’,‘parser_po’]
    \\ simp [ml_translatorTheory.PAIR_TYPE_def,ml_translatorTheory.STRING_TYPE_def])
  \\ rename1 ‘SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) (INR ast_decs) input_v’
  \\ strip_tac \\ gvs [std_preludeTheory.SUM_TYPE_def]
  \\ qmatch_asmsub_rename_tac ‘LIST_TYPE DEC_TYPE ast_decs ast_value’
  \\ simp [Once evaluate_def,evaluate_Var,can_pmatch_all_def,pmatch_def,same_ctor_def]
  \\ simp [Once evaluate_def,pmatch_def,same_ctor_def]
  \\ simp [astTheory.pat_bindings_def,Once evaluate_def,pmatch_def,same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,do_con_check_def,build_conv_def]
  \\ simp [evaluate_Con,evaluate_list,evaluate_Var,evaluate_Lit]
  \\ qexists_tac ‘0’ \\ qexists_tac ‘[]’ \\ qexists_tac ‘st.ptr_eq_oracle’
  \\ simp [semanticPrimitivesTheory.state_component_equality,ml_translatorTheory.PAIR_TYPE_def,
        std_preludeTheory.SUM_TYPE_def,ml_translatorTheory.STRING_TYPE_def]
QED

Theorem evaluate_repl:
  ∀(st:'ffi semanticPrimitives$state) s repl_str arg_str
   env types cur_gen next_id next_gen env1
   parse_v types_v env_v decs_v input_str_v
   types decs input_str env_id parse.
     st.eval_state = SOME s ∧
     s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
     s.env_id_counter = (cur_gen,next_id,next_gen) ∧
     LIST_TYPE DEC_TYPE decs decs_v ∧
     TYPES_TYPE types types_v ∧
     STRING_TYPE input_str input_str_v ∧
     (STRING_TYPE --> SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE)) parse parse_v ∧
     env_v = Env env1 env_id ∧
     repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
       (SND types,st with eval_state := NONE,env1) ∧
     nsLookup env.v repl_str = SOME repl_v ⇒
     nsLookup env.v arg_str =
       SOME (Conv NONE [parse_v; types_v; env_v; decs_v; input_str_v]) ⇒
     ∃res s1.
       evaluate st env [App Opapp [Var repl_str; Var arg_str]] = (s1,res) ∧
       res ≠ Rerr (Rabort Rtype_error) ∧
       (∀vs. res = Rval vs ⇒ vs = [Conv NONE []])
Proof
  strip_tac \\ completeInduct_on `st.clock`
  \\ rpt strip_tac \\ gvs [PULL_FORALL,AND_IMP_INTRO]
  \\ gvs [GSYM PULL_FORALL]
  (* expand App repl *)
  \\ simp [evaluate_def,repl_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  \\ rename [`evaluate _ _ [Mat _ _]`]
  \\ simp [Once evaluate_def]
  \\ simp [can_pmatch_all_def,pmatch_def,evaluate_Var]
  \\ simp [Once evaluate_def,astTheory.pat_bindings_def,pmatch_def]
  (* calling check_and_tweak *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ rename [`evaluate _ _ [App Opapp _]`]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [`do_opapp [repl_check_and_tweak_check_and_tweak_v;_]`]
  \\ qmatch_goalsub_abbrev_tac `do_opapp [_; arg_v]`
  \\ assume_tac repl_check_and_tweak_check_and_tweak_v_thm
  \\ `PAIR_TYPE (LIST_TYPE DEC_TYPE) (PAIR_TYPE TYPES_TYPE STRING_TYPE)
           (decs,types,input_str) arg_v` by
    fs [Abbr`arg_v`,PAIR_TYPE_def]
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ disch_then (qspec_then `st with clock := st.clock − 2`
       (qx_choosel_then [`check_env`,`check_body`,`junk`,`check_value`,
                        `ck`,`check_state`,`res`,`check_po`] strip_assume_tac))
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `res = Rerr (Rabort Rtimeout_error)` \\ gvs []
  (* case split on result of check_and_tweak *)
  \\ rename [`evaluate _ _ [Mat _ _]`]
  \\ Cases_on `check_and_tweak (decs,types,input_str)`
  \\ gvs []
  >- suspend "CheckError"
  >- suspend "CheckSuccess"
QED

Resume evaluate_repl[CheckError]:
  rename [‘_ = INL msg’]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  (* call report_error *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                   namespaceTheory.nsOptBind_def,build_rec_env_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_app_def]
  \\ simp [repl_moduleProgTheory.errorMessage_def]
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
        (SND types,st with <| eval_state := NONE ; refs := st.refs ++ junk;
                               ptr_eq_oracle := check_po |>,env1)’
       by (drule_then irule repl_types_skip_alt \\ fs [])
  \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
           the_Loc errorMessage_loc) repl_rs’ by (
    simp [repl_rs_def,
          repl_moduleProgTheory.errorMessage_def,the_Loc_def])
  \\ drule_then drule repl_types_str_assign
  \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
  \\ Cases_on ‘msg’ \\ gvs [STRING_TYPE_def]
  \\ rename [‘(Refv (Litv (StrLit sss)))’]
  \\ disch_then (qspec_then ‘sss’ mp_tac)
  \\ impl_keep_tac
  >-
   (drule repl_types_thm \\ simp [EVERY_MEM]
    \\ strip_tac \\ first_x_assum drule
    \\ simp [ref_lookup_ok_def]
    \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ strip_tac \\ fs [store_v_same_type_def])
  \\ simp [] \\ strip_tac
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* recursive call *)
  \\ last_x_assum irule \\ gvs []
  \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
  \\ assume_tac compiler_mainprog_report_error_dec_v_thm
  \\ rpt (first_assum $ irule_at Any)
  \\ simp []
  \\ drule_then irule repl_types_skip_alt \\ fs []
QED

Resume evaluate_repl[CheckSuccess]:
  rename [‘_ = INR xx’] \\ PairCases_on ‘xx’
  \\ rename [‘_ = INR (safe_decs,new_types)’]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def,
          PAIR_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [astTheory.pat_bindings_def,pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st6 env6’
  \\ ‘st6.eval_state = SOME s’ by fs [Abbr‘st6’]
  \\ drule (evaluate_eval |> Q.INST [‘arg_str’|->‘« v5»’]) \\ simp []
  \\ ‘nsLookup env6.v (Short «eval») = SOME eval_v’ by
   (fs [Abbr‘env6’]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [])
  \\ drule check_and_tweak \\ strip_tac
  \\ disch_then $ drule_then drule
  \\ gvs [Abbr‘env6’]
  \\ impl_tac
  THEN1
   (gvs [Abbr‘st6’] \\ rw []
    \\ irule_at Any repl_types_alt
    \\ first_assum $ irule_at Any
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule_at Any repl_types_clock_refs
    \\ first_assum $ irule_at Any)
  \\ disch_then (qx_choosel_then
       [`res`,`eval_result_state`,`eval_cost`,`msg`,`eval_junk`,`eval_po`]
       strip_assume_tac)
  \\ fs []
  \\ simp [Once evaluate_def,namespaceTheory.nsOptBind_def]
  \\ Cases_on ‘∃f. res = Rerr (Rabort (Rffi_error f))’ \\ fs []
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ fs []
  \\ gvs []
  >- suspend "CompileError"
  >- suspend "EvalException"
  >- suspend "EvalSuccess"
QED

Resume evaluate_repl[CompileError]:
  simp [Once evaluate_def,evaluate_Var]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  (* call report_error *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                   namespaceTheory.nsOptBind_def,build_rec_env_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_app_def]
  \\ simp [repl_moduleProgTheory.errorMessage_def]
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
        (SND types,st6 with <| eval_state := NONE ; refs := st6.refs ++ eval_junk ;
                               ptr_eq_oracle := eval_po |>,env1)’
       by (drule_then irule repl_types_skip_alt \\ fs [Abbr‘st6’]
           \\ simp_tac std_ss [GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPEND3])
  \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
           the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def,
          repl_moduleProgTheory.errorMessage_def,the_Loc_def]
  \\ drule_then drule repl_types_str_assign
  \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
  \\ disch_then (qspec_then ‘msg’ mp_tac)
  \\ impl_keep_tac
  >-
   (drule repl_types_thm \\ simp [EVERY_MEM]
    \\ strip_tac \\ pop_assum kall_tac \\ pop_assum drule
    \\ simp [ref_lookup_ok_def] \\ unabbrev_all_tac \\ fs []
    \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ strip_tac \\ fs [store_v_same_type_def])
  \\ simp [] \\ strip_tac
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* recursive call *)
  \\ last_x_assum irule \\ unabbrev_all_tac \\ gvs []
  \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
  \\ assume_tac compiler_mainprog_report_error_dec_v_thm
  \\ rpt (first_assum $ irule_at Any)
  \\ simp []
  \\ drule_then irule repl_types_skip_alt \\ fs []
QED

Resume evaluate_repl[EvalException]:
  qmatch_asmsub_rename_tac
       ‘evaluate_decs (st6 with <|clock := st6.clock − decl_cost; refs := _;
                                  eval_state := NONE; ptr_eq_oracle := _|>) env1 safe_decs =
        (evaluated_state,Rerr (Rraise raised_exn))’
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  (* call report_exn *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,report_exn_v_def,do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                   namespaceTheory.nsOptBind_def,build_rec_env_def])
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_app_def]
  \\ simp [repl_moduleProgTheory.exn_def]
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
        (SND types,st6 with <| clock := st6.clock - decl_cost ;
                               refs := st6.refs ++ eval_junk ;
                               eval_state := NONE ;
                               ptr_eq_oracle := eval_po |>,env1)’
       by (drule_then irule repl_types_skip_alt \\ fs [Abbr‘st6’]
           \\ simp_tac std_ss [GSYM APPEND_ASSOC,rich_listTheory.IS_PREFIX_APPEND3])
  \\ ‘MEM (Long «Repl» (Short «exn»),Exn,the_Loc exn) repl_rs’ by simp [repl_rs_def,
          repl_moduleProgTheory.exn_def,the_Loc_def]
  \\ drule_then drule repl_types_exn_assign
  \\ disch_then drule
  \\ disch_then drule
  \\ Cases_on ‘store_assign (the_Loc exn) (Refv raised_exn) evaluated_state.refs’
  >-
   (qsuff_tac ‘F’ \\ fs [] \\ pop_assum mp_tac \\ simp []
    \\ fs [store_assign_def]
    \\ drule_all repl_types_exn \\ strip_tac
    \\ drule repl_types_thm \\ simp [EVERY_MEM]
    \\ strip_tac \\ pop_assum kall_tac \\ pop_assum drule
    \\ simp [ref_lookup_ok_def] \\ unabbrev_all_tac \\ fs []
    \\ simp [store_lookup_def,repl_moduleProgTheory.exn_def,the_Loc_def]
    \\ strip_tac \\ fs [store_v_same_type_def])
  \\ fs [] \\ strip_tac \\ fs []
  \\ fs [repl_moduleProgTheory.exn_def,the_Loc_def]
  \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
                   namespaceTheory.nsOptBind_def,do_app_def])
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ fs [] \\ IF_CASES_TAC >- fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,do_app_def]
  \\ simp [repl_moduleProgTheory.errorMessage_def]
  \\ qmatch_goalsub_abbrev_tac ‘StrLit msg_e’
  \\ ‘MEM (Long «Repl» (Short «errorMessage»),Str,
           the_Loc errorMessage_loc) repl_rs’ by simp [repl_rs_def,
          repl_moduleProgTheory.errorMessage_def,the_Loc_def]
  \\ drule_then drule repl_types_str_assign
  \\ simp [store_assign_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
  \\ disch_then (qspec_then ‘msg_e’ mp_tac)
  \\ impl_keep_tac
  >-
   (drule repl_types_thm \\ simp [EVERY_MEM]
    \\ strip_tac \\ first_x_assum drule
    \\ simp [ref_lookup_ok_def]
    \\ simp [store_lookup_def,repl_moduleProgTheory.errorMessage_def,the_Loc_def]
    \\ strip_tac \\ fs [store_v_same_type_def])
  \\ simp [] \\ strip_tac
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* call roll_back *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ rename [‘evaluate _ _ [App Opapp _]’]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ qmatch_goalsub_abbrev_tac ‘do_opapp [_; arg_v]’
  \\ assume_tac repl_check_and_tweak_roll_back_v_thm
  \\ ‘PAIR_TYPE TYPES_TYPE TYPES_TYPE (types,new_types) arg_v’ by
    fs [Abbr‘arg_v’,PAIR_TYPE_def]
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘(st3, Rerr (Rabort Rtimeout_error))’
  \\ disch_then (qspec_then ‘dec_clock st3’
       (qx_choosel_then [‘rollback_env’,‘rollback_body’,‘rollback_junk’,‘rollback_value’,
                        ‘rollback_cost’,‘rollback_state’,‘res’,‘rollback_po’]
       strip_assume_tac))
  \\ fs []
  \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ unabbrev_all_tac \\ gvs [dec_clock_def]
  \\ Cases_on ‘res = Rerr (Rabort Rtimeout_error)’ \\ gvs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* recursive call *)
  \\ last_x_assum irule \\ unabbrev_all_tac \\ gvs []
  \\ conj_tac THEN1 (imp_res_tac evaluate_clock \\ fs [])
  \\ conj_tac THEN1 rewrite_tac [GSYM repl_v_def]
  \\ assume_tac compiler_mainprog_report_exn_dec_v_thm
  \\ rpt (first_assum $ irule_at Any)
  \\ rewrite_tac [GSYM APPEND_ASSOC,integerTheory.INT_ADD_CALCULATE]
  \\ ‘SND (roll_back (types,new_types)) = roll_back (SND types) (SND new_types)’
     by (PairCases_on ‘types’ \\ PairCases_on ‘new_types’ \\ fs [] \\ EVAL_TAC)
  \\ fs []
  \\ drule_then irule repl_types_skip_alt \\ fs []
  \\ drule evaluate_decs_with_NONE \\ fs []
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

Resume evaluate_repl[EvalSuccess]:
  qmatch_asmsub_rename_tac
       `evaluate_decs _ env1 safe_decs = (evaluated_state,Rval evaluated_env)`
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,std_preludeTheory.SUM_TYPE_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [Once evaluate_def]
  \\ gvs [can_pmatch_all_def,pmatch_def,evaluate_Var,astTheory.pat_bindings_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
                 (SND new_types,
                  evaluated_state with eval_state := NONE,
                  extend_dec_env evaluated_env env1)’ by
   (irule repl_types_eval
    \\ drule check_and_tweak \\ strip_tac
    \\ first_assum $ irule_at (Pos hd)
    \\ irule_at Any evaluate_decs_with_NONE
    \\ first_assum $ irule_at Any \\ simp [Abbr‘st6’]
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ simp [])
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  (* evaluating !REPL.isEOF *)
  \\ simp [mlbasicsProgTheory.deref_v_def,do_opapp_def]
  \\ IF_CASES_TAC \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,do_app_def]
  \\ ‘∃eof_n oef_b bv. isEOF_loc = Loc oef_b eof_n ∧
       store_lookup eof_n evaluated_state.refs = SOME (Refv (Boolv bv))’ by
   (drule repl_types_thm \\ strip_tac
    \\ fs [repl_rs_def]
    \\ fs [repl_moduleProgTheory.isEOF_def,the_Loc_def,ref_lookup_ok_def])
  \\ fs []
  (* evaluate if *)
  \\ rename [‘evaluate _ _ [If _ _ _]’]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def,do_if_def]
  \\ IF_CASES_TAC THEN1 simp [evaluate_Con]
  \\ simp []
  \\ simp [Once evaluate_def,evaluate_Var]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [same_ctor_def]
  \\ simp [mlbasicsProgTheory.deref_v_def,do_opapp_def]
  \\ IF_CASES_TAC \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,do_app_def]
  \\ qpat_assum
       ‘repl_types _ _ _ _ (SND new_types,_,_)’
       (mp_tac o MATCH_MP repl_input_read)
  \\ disch_then (qx_choosel_then [‘next_input’,‘next_value’] strip_assume_tac)
  \\ fs [repl_moduleProgTheory.nextInput_def,repl_input_location_def]
  \\ simp (LENGTH :: (DB.find "refs_def" |> map (#1 o #2)))
  \\ qmatch_goalsub_abbrev_tac ‘evaluate input_state input_env [Let _ repl_input_case _]’
  \\ ‘nsLookup input_env.v (Short repl_input_name) = SOME next_value ∧
      nsLookup input_env.v (Short «parse») = SOME parse_v ∧
      nsLookup input_env.c (Short «Inl») = SOME (1,repl_input_inl_stamp) ∧
      nsLookup input_env.c (Short «Inr») = SOME (1,repl_input_inr_stamp)’ by (
    simp [Abbr ‘input_env’,namespaceTheory.nsOptBind_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [ml_progTheory.nsLookup_pf_nsBind,
         ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def])
  \\ drule_all evaluate_repl_input
  \\ disch_then (qspec_then ‘input_state’
       (qx_choosel_then [‘normalized_state’,‘normalized_result’] strip_assume_tac))
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘normalized_result = Rerr (Rabort Rtimeout_error)’
  >- (gvs [] \\ simp [])
  \\ qpat_x_assum ‘_ ≠ _ ⇒ _’ (mp_tac o UNDISCH)
  \\ disch_then (qx_choosel_then [‘input_ck’,‘input_junk’,‘input_po’,
       ‘normalized_value’] strip_assume_tac)
  \\ qmatch_asmsub_abbrev_tac
       ‘PAIR_TYPE (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE)) STRING_TYPE
          normalized_input normalized_value’
  \\ namedCases_on ‘normalized_input’ ["parsed_input input_text"]
  \\ gvs [ml_translatorTheory.PAIR_TYPE_def]
  \\ qmatch_asmsub_rename_tac ‘SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) parsed_input parsed_value’
  \\ qmatch_asmsub_rename_tac ‘STRING_TYPE input_text input_text_value’
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
        (SND new_types,input_state with <|clock := input_state.clock - input_ck;
          refs := input_state.refs ++ input_junk; eval_state := NONE;
          ptr_eq_oracle := input_po|>,
         evaluated_env +++ env1)’ by (
    simp [Abbr ‘input_state’]
    \\ drule_then irule repl_types_skip_alt \\ simp [])
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def,
       namespacePropsTheory.nsLookup_nsBind]
  \\ simp [can_pmatch_all_def,pmatch_def,same_ctor_def,astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,pmatch_def,same_ctor_def]
  \\ namedCases_on ‘parsed_input’ ["input_error","input_decs"]
  \\ gvs [std_preludeTheory.SUM_TYPE_def]
  >- (
    qmatch_asmsub_rename_tac ‘STRING_TYPE input_error input_error_value’
    \\ simp [astTheory.pat_bindings_def,Once evaluate_def,evaluate_Var,
         namespaceTheory.nsOptBind_def,namespacePropsTheory.nsLookup_nsBind]
    \\ simp [can_pmatch_all_def,pmatch_def,same_ctor_def]
    \\ simp [Once evaluate_def,pmatch_def,same_ctor_def,astTheory.pat_bindings_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def,evaluate_Lit,Abbr ‘input_env’]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [ml_progTheory.nsLookup_pf_nsBind,
         ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
    \\ simp [pmatch_def,astTheory.pat_bindings_def,same_ctor_def]
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def,evaluate_Lit]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [ml_progTheory.nsLookup_pf_nsBind,
         ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
    \\ simp [dec_clock_def,report_error_v_def,do_opapp_def,
         EVAL “find_recfun s [(s,y,x)]”]
    \\ IF_CASES_TAC >- simp []
    \\ ntac 3 (simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def,build_rec_env_def])
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [ml_progTheory.nsLookup_pf_nsBind,
         ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
    \\ simp [dec_clock_def,mlbasicsProgTheory.assign_v_def,do_opapp_def]
    \\ IF_CASES_TAC >- simp []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def]
    \\ IF_CASES_TAC >- simp []
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def,do_app_def]
    \\ simp [repl_moduleProgTheory.errorMessage_def]
    \\ ‘∃previous_error.
          store_lookup repl_error_location (input_state.refs ++ input_junk) =
            SOME (Refv (Litv (StrLit previous_error)))’ by (
      qpat_x_assum ‘repl_types _ _ _ _ (SND new_types,input_state with <|clock := _;
        refs := _; eval_state := NONE; ptr_eq_oracle := _|>,_)’
        (mp_tac o MATCH_MP repl_types_thm)
      \\ simp [PULL_EXISTS,repl_rs_def,ref_lookup_ok_def,
           repl_moduleProgTheory.errorMessage_def,the_Loc_def])
    \\ gvs [ml_translatorTheory.STRING_TYPE_def,store_lookup_def,
         store_assign_def,store_v_same_type_def]
    \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
          (SND new_types,
           (input_state with <|clock := input_state.clock - input_ck;
             refs := input_state.refs ++ input_junk; eval_state := NONE;
             ptr_eq_oracle := input_po|>) with
             refs := LUPDATE (Refv (Litv (StrLit input_error))) repl_error_location
               (input_state.refs ++ input_junk),evaluated_env +++ env1)’ by (
      irule repl_types_str_assign
      \\ conj_tac
      >- (
        qexistsl_tac [‘repl_error_location’,‘Long «Repl» (Short «errorMessage»)’,
          ‘input_error’]
        \\ simp [store_assign_def,store_v_same_type_def,repl_rs_def,
             repl_moduleProgTheory.errorMessage_def,the_Loc_def])
      \\ simp [])
    \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
         namespaceTheory.nsOptBind_def,evaluate_Lit]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ simp [ml_progTheory.nsLookup_pf_nsBind,
         ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
    \\ last_x_assum irule
    \\ simp [Abbr ‘input_state’]
    \\ drule evaluate_clock_decs \\ strip_tac
    \\ fs [Abbr ‘st6’]
    \\ conj_tac >- rewrite_tac [GSYM repl_v_def]
    \\ assume_tac compiler_mainprog_report_error_dec_v_thm
    \\ rpt (first_assum $ irule_at Any)
    \\ simp [integerTheory.INT_ADD_CALCULATE]
    \\ drule_then irule repl_types_skip_alt \\ simp [])
  \\ qmatch_asmsub_rename_tac ‘LIST_TYPE DEC_TYPE input_decs input_decs_value’
  \\ simp [astTheory.pat_bindings_def,Once evaluate_def,evaluate_Var,
       namespaceTheory.nsOptBind_def,namespacePropsTheory.nsLookup_nsBind]
  \\ simp [can_pmatch_all_def,pmatch_def,same_ctor_def]
  \\ simp [Once evaluate_def,pmatch_def,same_ctor_def,astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit,Abbr ‘input_env’]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [ml_progTheory.nsLookup_pf_nsBind,
       ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
  \\ simp [pmatch_def,astTheory.pat_bindings_def,same_ctor_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [ml_progTheory.nsLookup_pf_nsBind,
       ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [ml_progTheory.nsLookup_pf_nsBind,
       ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
  \\ last_x_assum irule
  \\ simp [Abbr ‘input_state’]
  \\ drule evaluate_clock_decs \\ strip_tac
  \\ simp [Abbr ‘st6’]
  \\ conj_tac >- (fs [] \\ decide_tac)
  \\ conj_tac >- rewrite_tac [GSYM repl_v_def]
  \\ rpt (first_assum $ irule_at Any)
  \\ simp [integerTheory.INT_ADD_CALCULATE]
  \\ drule_then irule repl_types_skip_alt \\ simp []
QED

Finalise evaluate_repl;

(* the closure that start_repl passes to the one-argument Eval *)
Definition compiler_fun_cl_def:
  compiler_fun_cl host_v =
    case do_opapp [compiler_fun_v; host_v] of
    | SOME (env, Fun x e) => Closure env x e
    | _ => Conv NONE []
End

Theorem do_opapp_compiler_fun:
  ∃env e. do_opapp [compiler_fun_v; host_v] = SOME (env, Fun «» e) ∧
          compiler_fun_cl host_v = Closure env «» e
Proof
  simp [compiler_fun_cl_def,compiler_fun_v_def,do_opapp_def,
        EVAL “find_recfun s [(s,y,x)]”]
QED

Theorem evaluate_repl_thm =
  evaluate_repl |> SIMP_RULE std_ss [] |> SPEC_ALL
  |> Q.INST [‘cur_gen’|->‘0’,‘next_id’|->‘1’,‘next_gen’|->‘1’,‘env_id’|->‘(0,0)’,
             ‘input_str’|->‘«»’,‘decs’|->‘[]’] |> GEN_ALL
  |> SIMP_RULE std_ss [STRING_TYPE_def,LIST_TYPE_def] |> SPEC_ALL;

Theorem evaluate_start_repl:
  (st:'ffi semanticPrimitives$state).eval_state = SOME s ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,1,1) ∧
  LIST_TYPE STRING_TYPE cl cl_v ∧
  repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
    (repl_prog_types, st with eval_state := NONE, repl_init_env) ∧
  nsLookup env.v start_repl_str = SOME start_repl_v ⇒
  nsLookup env.v arg_str = SOME cl_v ⇒
  ∃res s1.
    evaluate st env [App Opapp [Var start_repl_str; Var arg_str]] = (s1,res) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    (∀vs. res = Rval vs ⇒ vs = [Conv NONE []])
Proof
  rpt strip_tac
  (* expand App start_repl *)
  \\ simp [evaluate_def,start_repl_v_def]
  \\ simp [do_opapp_def,find_recfun_def]
  \\ IF_CASES_TAC \\ simp []
  (* let parse = parse_cakeml_syntax *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let types = init_types *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let env = ... *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let decs = [] *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* let input_str = «» *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  (* call boot_marker *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ rename [`evaluate _ _ [App Opapp _]`]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,build_rec_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rename [`do_opapp [compiler_mainprog_boot_marker_v;_]`]
  \\ assume_tac compiler_mainprog_boot_marker_v_thm
  \\ drule_all Arrow_IMP
  \\ fs [dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac `(st2, Rerr (Rabort Rtimeout_error))`
  \\ disch_then (qspec_then `st2 with clock := st2.clock − 1`
       (qx_choosel_then [`next_env`,`next_body`,`next_junk`,`next_value`,
                        `next_cost`,`next_state`,`next_res`,`next_po`] strip_assume_tac))
  \\ fs [] \\ IF_CASES_TAC \\ fs [Abbr`st2`]
  \\ Cases_on `next_res = Rerr (Rabort Rtimeout_error)` \\ gvs []
  \\ rename1 ‘evaluate _ _ [_] =
    (st with <|clock := st.clock - (source_ck + 2);
               refs := st.refs ++ source_junk;
               ptr_eq_oracle := source_po|>,
     Rval [source_value])’
  (* Wrap the boot marker in Inl. *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,
       namespaceTheory.nsOptBind_def,do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  (* Evaluate the curried reference assignment. *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ fs [mlbasicsProgTheory.assign_v_def,do_opapp_def,dec_clock_def]
  \\ IF_CASES_TAC \\ fs []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ IF_CASES_TAC >- fs []
  \\ qmatch_goalsub_abbrev_tac ‘evaluate startup_state assignment_env [App Opassign _]’
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
       (repl_prog_types, startup_state with eval_state := NONE, repl_init_env)’ by (
    simp [Abbr ‘startup_state’] \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ irule repl_types_clock_refs \\ simp [])
  \\ qpat_assum ‘repl_types _ _ _ _
      (repl_prog_types,startup_state with eval_state := NONE,repl_init_env)’
      (mp_tac o MATCH_MP repl_input_read)
  \\ disch_then (qx_choosel_then [‘initial_input’,‘initial_value’] strip_assume_tac)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,
       namespaceTheory.nsOptBind_def,Abbr ‘assignment_env’,do_app_def]
  \\ fs [repl_moduleProgTheory.nextInput_def,repl_input_location_def,
       store_lookup_def,store_assign_def,store_v_same_type_def]
  \\ simp (LENGTH :: (DB.find "refs_def" |> map (#1 o #2)))
  \\ fs [STRING_TYPE_def]
  \\ ‘repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
       (repl_prog_types,
        startup_state with <|refs := LUPDATE
          (Refv (repl_source_value (boot_marker cl))) repl_input_location
          startup_state.refs; eval_state := NONE|>,repl_init_env)’ by (
    irule repl_input_source_assign
    \\ simp [repl_input_location_def,store_assign_def,store_lookup_def,
         store_v_same_type_def]
    \\ qexists_tac ‘boot_marker cl’ \\ simp [])
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
       namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ irule (GEN_ALL evaluate_repl_thm)
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [ml_progTheory.nsLookup_pf_nsBind,
       ml_progTheory.option_choice_f_apply,alistTheory.ALOOKUP_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [Abbr ‘startup_state’]
  \\ assume_tac compiler_mainprog_parse_cakeml_syntax_v_thm
  \\ assume_tac repl_init_types_repl_init_types_v_thm
  \\ rpt (first_assum $ irule_at Any)
  \\ simp [repl_init_typesTheory.repl_init_types_def]
  \\ qexists_tac ‘ffi’ \\ fs [repl_input_location_def,repl_source_value_def]
QED

(* main_host is everything a target's main calls; its hypotheses are what
   repl_types_repl_prog provides about the state after the program prefix *)
Theorem evaluate_main_host:
  COMPILER_MAINPROG_COMPILER_HOST_TYPE host host_v ∧
  (st:'ffi semanticPrimitives$state).eval_state = SOME s ∧ ¬s.initialised ∧
  s.init_ok (BACKEND_CONFIG_v conf) (compiler_fun_cl host_v) ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,1,1) ∧ has_repl_flag cl ∧
  do_opapp [CommandLine_arguments_v; Conv NONE []] = SOME (env_cl,e_cl) ∧
  evaluate (st with <|eval_state := NONE; clock := st.clock − 2|>) env_cl [e_cl] =
    (s_cl,res_cl) ∧
  (res_cl ≠ Rerr (Rabort Rtimeout_error) ⇒
   ∃cl_v.
     LIST_TYPE STRING_TYPE cl cl_v ∧ res_cl = Rval [cl_v] ∧
     ∀ck junk po1. ∃env_pr e_pr res_pr s_pr.
       do_opapp [Repl_charsFrom_v; Litv (StrLit «config_enc_str.txt»)] =
         SOME (env_pr,e_pr) ∧
       evaluate
         (s_cl with <|clock := s_cl.clock − (ck + 3); refs := s_cl.refs ++ junk;
                      ptr_eq_oracle := po1|>) env_pr [e_pr] = (s_pr,res_pr) ∧
       (res_pr ≠ Rerr (Rabort Rtimeout_error) ⇒
        ∃pr_v.
          res_pr = Rval [pr_v] ∧ LIST_TYPE CHAR (encode_backend_config conf) pr_v ∧
          repl_types repl_input_catalogue repl_input_slots T (ffi,repl_rs)
            (repl_prog_types,s_pr,repl_init_env))) ∧
  nsLookup env.v main_host_str = SOME main_host_v ∧
  nsLookup env.v arg_str = SOME (Conv NONE [host_v; Conv NONE []]) ∧
  evaluate st env [App Opapp [Var main_host_str; Var arg_str]] = (st1,res) ⇒
  res ≠ Rerr (Rabort Rtype_error) ∧ (∀vs. res = Rval vs ⇒ vs = [Conv NONE []])
Proof
  strip_tac \\ qpat_x_assum ‘evaluate st env _ = _’ mp_tac
  \\ simp [evaluate_App_Opapp,evaluate_Var]
  \\ rewrite_tac [main_host_v_def,EVAL
       ``semanticPrimitives$do_opapp [Recclosure env [(n,u,e)] n; arg]``]
  \\ simp []
  \\ IF_CASES_TAC >- (rw [] \\ simp [])
  \\ simp [dec_clock_def,Once evaluate_def,evaluate_Var,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def]
  \\ simp [astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ IF_CASES_TAC >- (rw [] \\ simp [])
  (* CommandLine.arguments *)
  \\ ‘dec_clock (st with clock := st.clock − 1) =
      (st with <|eval_state := NONE; clock := st.clock − 2|>) with
        eval_state := SOME s’
    by simp [evaluateTheory.dec_clock_def,
             semanticPrimitivesTheory.state_component_equality]
  \\ pop_assum SUBST1_TAC
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd)
  \\ disch_then (qspec_then ‘SOME s’ mp_tac)
  \\ impl_tac >- (simp [] \\ Cases_on ‘res_cl’ \\ gvs [])
  \\ strip_tac \\ simp []
  \\ Cases_on ‘res_cl = Rerr (Rabort Rtimeout_error)’ >- rw []
  \\ gvs []
  (* call compiler_has_repl_flag *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ assume_tac compiler_mainprog_has_repl_flag_v_thm
  \\ drule_all Arrow_IMP
  \\ disch_then (qspec_then `dec_clock (s_cl with eval_state := SOME s)`
       (qx_choosel_then [`flag_env`,`flag_exp`,`junk`,`flag_value`,
                        `ck`,`flag_state`,`flag_res`,`flag_po`] strip_assume_tac))
  \\ simp []
  \\ IF_CASES_TAC >- rw []
  \\ Cases_on `flag_res = Rerr (Rabort Rtimeout_error)` >- rw []
  \\ gvs [ml_translatorTheory.BOOL_def]
  (* if *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,do_if_def]
  \\ fs [evaluateTheory.dec_clock_def]
  (* call run_interactive_repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [evaluate_App_Opapp,evaluate_Var]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rewrite_tac [run_interactive_repl_v_def,EVAL “semanticPrimitives$do_opapp
       [Recclosure env [(n, u, e)] n; cl_v]”] \\ simp []
  \\ IF_CASES_TAC >- rw []
  \\ fs [evaluateTheory.dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def,
           astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [evaluateTheory.dec_clock_def]
  (* charsFrom *)
  \\ first_x_assum (qspecl_then [`ck`,`junk`,`flag_po`]
       (qx_choosel_then [`env_pr`,`e_pr`,`res_pr`,`s_pr`] strip_assume_tac))
  \\ simp []
  \\ IF_CASES_TAC >- rw []
  \\ qpat_x_assum ‘evaluate$evaluate _ env_pr _ = _’
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd
        |> SPEC_ALL
        |> INST [“es:source_eval_state option” |-> “SOME (s:source_eval_state)”])))
  \\ impl_tac >- simp []
  \\ impl_tac >- (Cases_on ‘res_pr’ \\ gvs [])
  \\ strip_tac \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st_pr env_pr _’
  \\ ‘st_pr = s_cl with <|eval_state := SOME s; clock := s_cl.clock − (ck + 3);
                           refs := s_cl.refs ++ junk; ptr_eq_oracle := flag_po|>’
    by simp [Abbr ‘st_pr’,semanticPrimitivesTheory.state_component_equality]
  \\ pop_assum SUBST1_TAC \\ simp []
  \\ Cases_on ‘res_pr = Rerr (Rabort Rtimeout_error)’ >- rw []
  \\ gvs []
  (* decode_backend_config *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [evaluateTheory.dec_clock_def]
  \\ assume_tac decodeProgTheory.decode_backend_config_v_thm
  \\ drule_all Arrow_IMP
  \\ disch_then (qspec_then `s_pr with <|clock := s_pr.clock − 1;
                                        eval_state := SOME s|>`
       (qx_choosel_then [`decode_env`,`decode_exp`,`decode_junk`,`decode_value`,
                        `decode_cost`,`decode_state`,`decode_res`,`decode_po`]
        strip_assume_tac))
  \\ simp []
  \\ IF_CASES_TAC >- rw []
  \\ Cases_on `decode_res = Rerr (Rabort Rtimeout_error)` >- rw []
  \\ gvs [backend_enc_decTheory.encode_backend_config_thm]
  \\ ‘decode_value = BACKEND_CONFIG_v conf’ by metis_tac [BACKEND_CONFIG_IMP]
  \\ gvs []
  (* let v0 = compiler_fun host *)
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_assume_tac do_opapp_compiler_fun \\ simp []
  \\ simp [build_rec_env_def,nsLookup_Short_nsBind,ml_progTheory.nsLookup_Short_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [evaluateTheory.dec_clock_def]
  \\ IF_CASES_TAC >- rw []
  \\ simp [Once evaluate_def]
  \\ qpat_x_assum ‘compiler_fun_cl _ = _’ (rewrite_tac o single o GSYM)
  (* eval_init_prim (s1, v0) *)
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list]
  \\ simp [build_rec_env_def,nsLookup_Short_nsBind,ml_progTheory.nsLookup_Short_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ simp [do_opapp_def,eval_init_prim_v_def]
  \\ IF_CASES_TAC >- rw []
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_list,evaluateTheory.dec_clock_def,
           nsLookup_Short_nsBind]
  \\ asm_simp_tac (srw_ss()) [do_eval_init_def]
  (* start_repl cl *)
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st9 env9 [_]’
  \\ mp_tac (Q.INST [‘st’|->‘st9’,‘env’|->‘env9’,
                     ‘start_repl_str’|->‘Short «start_repl»’,
                     ‘arg_str’|->‘Short «cl»’,
                     ‘s’|->‘s with <|initialised := T;
                                     closure := compiler_fun_cl host_v|>’]
                evaluate_start_repl)
  \\ simp [Abbr ‘st9’,Abbr ‘env9’]
  \\ impl_tac
  >- (
    conj_tac >- (drule_then irule repl_types_skip_alt \\ simp [])
    \\ simp [namespaceTheory.nsOptBind_def,build_rec_env_def,nsLookup_Short_nsBind,
             ml_progTheory.nsLookup_Short_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [])
  \\ impl_tac >- simp [namespaceTheory.nsOptBind_def]
  \\ strip_tac \\ rw [] \\ gvs []
QED

Theorem BUTLAST_LAST:
  ∀xs. ~NULL xs ⇒ xs = BUTLAST xs ++ [LAST xs]
Proof
  Induct \\ fs []
  \\ Cases_on ‘xs’ \\ fs []
QED

(* the compiler closure passed to Eval implements compiler_inst *)

Theorem compiler_reach_BACKEND_CONFIG_v[local]:
  ∀st. evalSem$compiler_reach (compiler_inst c) (BACKEND_CONFIG_v cfg0) st ⇒
       ∃cfg. st = BACKEND_CONFIG_v cfg
Proof
  ho_match_mp_tac evalSemTheory.compiler_reach_ind \\ rw []
  >- metis_tac []
  \\ gvs [compiler_inst_def,AllCaseEqs(),UNCURRY]
  \\ metis_tac []
QED

Theorem compiler_fun_cl_eq =
  SIMP_CONV (srw_ss()) [compiler_fun_cl_def,compiler_fun_v_def,
    semanticPrimitivesTheory.do_opapp_def,EVAL “find_recfun s [(s,y,x)]”]
  “compiler_fun_cl host_v”;

Theorem cl_env_lookups[local] =
  “nsLookup (merge_env compiler_mainProg_env_7 init_env).v (Short «compiler_for_eval») =
     SOME compiler_mainprog_compiler_for_eval_v ∧
   nsLookup (merge_env compiler_mainProg_env_7 init_env).c (Short «None») =
     SOME (0,TypeStamp «None» 2 0) ∧
   nsLookup (merge_env compiler_mainProg_env_7 init_env).c (Short «Some») =
     SOME (1,TypeStamp «Some» 2 1) ∧
   nsLookup (merge_env compiler_mainProg_env_7 init_env).c (Short «Bind») =
     SOME (0,ExnStamp 0)”
  |> (DEPTH_CONV ml_progLib.nsLookup_conv THENC SIMP_CONV (srw_ss()) [])
  |> EQT_ELIM |> (fn th => CONJ th (REWRITE_RULE [ml_progTheory.nsLookup_eq] th));

Theorem compiler_fun_cl_closure:
  COMPILER_MAINPROG_COMPILER_HOST_TYPE host host_v ⇒
  evalSem$compiler_closure (compiler_inst (host_config host))
    (v_fun_abs decs_allowed (LIST_v DEC_v)) (BACKEND_CONFIG_v cfg0)
    (compiler_fun_cl host_v) (:'ffi)
Proof
  rw [evalSemTheory.compiler_closure_def]
  \\ drule compiler_reach_BACKEND_CONFIG_v
  \\ strip_tac \\ gvs []
  \\ ‘decs_v = LIST_v DEC_v decs ∧ decs_allowed decs’ by (
    qpat_x_assum ‘v_fun_abs _ _ _ = _’ mp_tac
    \\ simp [source_eval_oracleProofTheory.v_rel_abs]
    \\ DEEP_INTRO_TAC some_intro \\ simp [IN_DEF])
  \\ gvs []
  \\ ‘LIST_TYPE DEC_TYPE decs (LIST_v DEC_v decs)’ by (
    ‘IsTypeRep (LIST_v DEC_v) (LIST_TYPE DEC_TYPE)’ by (
      irule decProgTheory.IsTypeRep_LIST_v
      \\ fs [decProgTheory.IsTypeRep_DEC_v])
    \\ fs [ml_translatorTheory.IsTypeRep_def])
  \\ ‘BACKEND_CONFIG_TYPE cfg (BACKEND_CONFIG_v cfg)’ by (
    assume_tac decodeProgTheory.IsTypeRep_BACKEND_CONFIG_v
    \\ fs [ml_translatorTheory.IsTypeRep_def])
  \\ ‘PAIR_TYPE (PAIR_TYPE NUM NUM)
        (PAIR_TYPE BACKEND_CONFIG_TYPE (LIST_TYPE DEC_TYPE)) ((gen,id),cfg,decs)
        (Conv NONE [Conv NONE [nat_to_v gen; nat_to_v id];
                    Conv NONE [BACKEND_CONFIG_v cfg; LIST_v DEC_v decs]])’
    by simp [ml_translatorTheory.PAIR_TYPE_def,ml_translatorTheory.NUM_def,
             ml_translatorTheory.INT_def,nat_to_v_def]
  \\ assume_tac compiler_mainprog_compiler_for_eval_v_thm
  \\ drule_all Arrow_IMP_exact
  \\ disch_then (qx_choosel_then [‘host_env’,‘host_exp’] strip_assume_tac)
  \\ simp [compiler_fun_cl_eq,do_opapp_def]
  \\ rpt gen_tac
  \\ first_x_assum (qspecl_then [‘refs’,‘po’]
       (qx_choosel_then [‘junk1’,‘po1’,‘u1’] strip_assume_tac))
  \\ drule_all Arrow_IMP_exact
  \\ disch_then (qx_choosel_then [‘cfe_env’,‘cfe_exp’] strip_assume_tac)
  \\ first_x_assum (qspecl_then [‘refs ++ junk1’,‘po1’]
       (qx_choosel_then [‘junk2’,‘po2’,‘u2’] strip_assume_tac))
  \\ qpat_x_assum ‘∀k. ∃ck. ∀s. _ ⇒ evaluate _ cfe_env _ = _’
       (qspec_then ‘0’ (qx_choose_then ‘ck2’ assume_tac))
  \\ qpat_x_assum ‘∀k. ∃ck. ∀s. _ ⇒ evaluate _ host_env _ = _’
       (qspec_then ‘ck2 + 1’ (qx_choose_then ‘ck1’ assume_tac))
  \\ qexistsl_tac [‘ck1 + 1’,‘junk1 ++ junk2’,‘po2’]
  \\ drule v_fun_abs_BACKEND_CONFIG_v \\ strip_tac
  \\ simp [compiler_inst_def,GSYM compiler_for_eval_def]
  \\ Cases_on ‘compiler_for_eval host ((gen,id),cfg,decs)’
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  >- (
    rpt strip_tac
    \\ qpat_x_assum ‘∀s. _ ⇒ evaluate (s with clock := ck1) _ _ = _’
         (qspec_then ‘s’ mp_tac) \\ simp [] \\ strip_tac
    \\ qpat_x_assum ‘∀s. _ ⇒ evaluate (s with clock := ck2) _ _ = _’
         (qspec_then ‘s with <|refs := refs ++ junk1; ptr_eq_oracle := po1|>’ mp_tac)
    \\ simp [] \\ strip_tac
    \\ simp [evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def,
             namespaceTheory.nsOptBind_def,build_rec_env_def,cl_env_lookups,
             nsLookup_Short_nsBind,do_con_check_def,build_conv_def,same_ctor_def,
             evaluateTheory.dec_clock_def]
    \\ EVAL_TAC)
  \\ PairCases_on ‘x’ \\ gvs [ml_translatorTheory.PAIR_TYPE_def]
  \\ rename1 ‘BACKEND_CONFIG_TYPE cfg2 cfg2_v’
  \\ ‘cfg2_v = BACKEND_CONFIG_v cfg2’ by metis_tac [BACKEND_CONFIG_IMP]
  \\ gvs [] \\ irule_at Any v_to_mlstring_thm \\ first_assum (irule_at Any)
  \\ irule_at Any v_to_word64_list_thm \\ first_assum (irule_at Any)
  \\ simp [] \\ rpt strip_tac
  \\ qmatch_goalsub_rename_tac ‘evaluate (s0 with clock := ck1 + 1) _ _’
  \\ qpat_x_assum ‘∀s. _ ⇒ evaluate (s with clock := ck1) _ _ = _’
       (qspec_then ‘s0’ mp_tac) \\ simp [] \\ strip_tac
  \\ qpat_x_assum ‘∀s. _ ⇒ evaluate (s with clock := ck2) _ _ = _’
       (qspec_then ‘s0 with <|refs := refs ++ junk1; ptr_eq_oracle := po1|>’ mp_tac)
  \\ simp [] \\ strip_tac
  \\ simp [evaluate_def,can_pmatch_all_def,pmatch_def,astTheory.pat_bindings_def,
           namespaceTheory.nsOptBind_def,build_rec_env_def,cl_env_lookups,
           nsLookup_Short_nsBind,do_con_check_def,build_conv_def,same_ctor_def,
           evaluateTheory.dec_clock_def]
QED
