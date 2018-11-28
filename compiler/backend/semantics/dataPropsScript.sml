(*
  Properties about dataLang and its semantics
*)
open preamble dataLangTheory dataSemTheory semanticsPropsTheory;
local open bviPropsTheory in end;

val _ = new_theory"dataProps";

val s = ``s:('c,'ffi) dataSem$state``

val bvi_to_data_id = Q.store_thm("bvi_to_data_id[simp]",
  `bvi_to_data (data_to_bvi x) x = x`,
  EVAL_TAC \\ rw[state_component_equality]);

val initial_state_simp = Q.store_thm("initial_state_simp[simp]",
  `(initial_state f c co cc k).clock = k ∧
   (initial_state f c co cc k).locals = LN ∧
   (initial_state f c co cc k).code = c ∧
   (initial_state f c co cc k).ffi = f ∧
   (initial_state f c co cc k).compile_oracle = co ∧
   (initial_state f c co cc k).compile = cc ∧
   (initial_state f c co cc k).stack = []`,
  srw_tac[][initial_state_def]);

val initial_state_with_simp = Q.store_thm("initial_state_with_simp[simp]",
  `(initial_state f c co cc k with clock := k' = initial_state f c co cc k') ∧
   (initial_state f c co cc k with stack := [] = initial_state f c co cc k) ∧
   (initial_state f c co cc k with locals := LN = initial_state f c co cc k)`,
  srw_tac[][initial_state_def]);

val with_same_locals = Q.store_thm("with_same_locals",
  `(s with locals := s.locals) = s`,
  full_simp_tac(srw_ss())[state_component_equality]);

val var_corr_def = Define `
  var_corr env corr t <=>
    EVERY2 (\v x. get_var v t = SOME x) corr env`;

val get_vars_thm = Q.store_thm("get_vars_thm",
  `!vs a t2. var_corr a vs t2 ==> (get_vars vs t2 = SOME a)`,
  Induct \\ Cases_on `a` \\ FULL_SIMP_TAC std_ss [get_vars_def]
  \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val get_vars_append = Q.store_thm("get_vars_append",
  `∀l1 l2 s. get_vars (l1 ++ l2) s = OPTION_BIND (get_vars l1 s)(λy1. OPTION_BIND (get_vars l2 s)(λy2. SOME(y1 ++ y2)))`,
  Induct >> simp[get_vars_def,OPTION_BIND_SOME,ETA_AX] >> srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[]);

val get_vars_reverse = Q.store_thm("get_vars_reverse",
  `∀ls s ys. get_vars ls s = SOME ys ⇒ get_vars (REVERSE ls) s = SOME (REVERSE ys)`,
  Induct >> simp[get_vars_def] >> srw_tac[][get_vars_append] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  srw_tac[][get_vars_def]);

val EVERY_get_vars = Q.store_thm("EVERY_get_vars",
  `!args s1 s2.
      EVERY (\a. lookup a s1 = lookup a s2) args ==>
      (get_vars args s1 = get_vars args s2)`,
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val get_vars_IMP_domain = Q.store_thm("get_vars_IMP_domain",
  `!args x s vs. MEM x args /\ (get_vars args s = SOME vs) ==>
                  x IN domain s`,
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[domain_lookup]);

val cut_state_opt_with_const = Q.store_thm("cut_state_opt_with_const",
  `(cut_state_opt x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (cut_state_opt x y)) ∧
   (cut_state_opt x (y with clock := k) = OPTION_MAP (λs. s with clock := k) (cut_state_opt x y))`,
  EVAL_TAC >> every_case_tac >> simp[]);

val consume_space_add_space = Q.store_thm("consume_space_add_space",
  `consume_space k (add_space t k with locals := env1) =
    SOME (t with <| locals := env1 ; space := 0  |>)`,
  full_simp_tac(srw_ss())[consume_space_def,add_space_def,state_component_equality] \\ DECIDE_TAC);

val consume_space_with_stack = Q.prove(
  `consume_space x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][])

val consume_space_with_locals = Q.prove(
  `consume_space x (y with locals := z) = OPTION_MAP (λs. s with locals := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][])

val do_app_with_stack = Q.prove(
  `do_app op vs (s with stack := z) = map_result (λ(x,y). (x,y with stack := z)) I (do_app op vs s)`,
  srw_tac[][do_app_def,do_space_def,bvi_to_data_def,data_to_bvi_def,do_install_def] >>
  rpt (every_case_tac >>
       full_simp_tac(srw_ss())[consume_space_with_stack] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[]));

val do_app_with_locals = Q.prove(
  `do_app op vs (s with locals := z) = map_result (λ(x,y). (x,y with locals := z)) I (do_app op vs s)`,
  srw_tac[][do_app_def,do_space_def,bvi_to_data_def,data_to_bvi_def,do_install_def] >>
  rpt (every_case_tac >> full_simp_tac(srw_ss())[consume_space_with_locals] >> srw_tac[][] >> full_simp_tac(srw_ss())[]));

val do_app_err = Q.store_thm("do_app_err",
  `do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x)) `,
  srw_tac[][do_app_def,do_install_def]
  THEN1 (rpt (every_case_tac \\ fs [] \\ pairarg_tac \\ fs [])) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac bviPropsTheory.do_app_err >> full_simp_tac(srw_ss())[]);

val do_app_const = Q.store_thm("do_app_const",
  `do_app op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile`,
  simp[do_app_def,do_space_def,do_install_def] >>
  IF_CASES_TAC THEN1
    (every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
     \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  every_case_tac >> simp[bvi_to_data_def] >> strip_tac >>
  rpt var_eq_tac >> simp[] >>
  full_simp_tac(srw_ss())[bviSemTheory.do_app_def] >> rfs [] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
  full_simp_tac(srw_ss())[bviSemTheory.bvl_to_bvi_def,data_to_bvi_def,bviSemTheory.bvi_to_bvl_def] >>
  imp_res_tac bvlSemTheory.do_app_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac bviPropsTheory.do_app_aux_const >> full_simp_tac(srw_ss())[] >>
  fs [data_to_bvi_def] >>
  full_simp_tac(srw_ss())[consume_space_def] >> TRY var_eq_tac >> simp[]);

val do_app_locals = Q.store_thm("do_app_locals",
  `(do_app op x s = Rval (q,r)) ==>
    (do_app op x (s with locals := extra) =
       Rval (q,r with locals := extra))`,
  full_simp_tac(srw_ss())[do_app_def,do_space_def,consume_space_def,data_to_bvi_def]
  \\ IF_CASES_TAC THEN1
    (fs [do_install_def]
     \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
     \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ every_case_tac >> full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bvi_to_data_def,state_component_equality]);

val do_space_alt = Q.store_thm("do_space_alt",
  `do_space op l s =
      if op_space_reset op then SOME (s with space := 0)
      else consume_space (op_space_req op l) s`,
  full_simp_tac(srw_ss())[do_space_def] \\ SRW_TAC [] [consume_space_def]
  \\ full_simp_tac(srw_ss())[state_component_equality] \\ full_simp_tac(srw_ss())[] \\ DECIDE_TAC);

val Seq_Skip = Q.store_thm("Seq_Skip",
  `evaluate (Seq c Skip,s) = evaluate (c,s)`,
  full_simp_tac(srw_ss())[evaluate_def] \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []);

val evaluate_stack_swap = Q.store_thm("evaluate_stack_swap",
  `!c ^s.
     case evaluate (c,s) of
     | (SOME (Rerr(Rabort Rtype_error)),s1) => T
     | (SOME (Rerr(Rabort a)),s1) => (s1.stack = []) /\
                   (!xs. (LENGTH s.stack = LENGTH xs) ==>
                           evaluate (c,s with stack := xs) =
                             (SOME (Rerr(Rabort a)),s1))
     | (SOME (Rerr (Rraise t)),s1) =>
           (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                 (s2.stack = s1.stack) /\ (s2.handler = s1.handler) /\
                 (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                          (LENGTH s.stack = LENGTH xs) ==>
                          (evaluate (c,s with stack := xs) =
                             (SOME (Rerr (Rraise t)),
                              s1 with <| stack := s7.stack ;
                                         handler := s7.handler ;
                                         locals := s7.locals |>))))
     | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                   (!xs. (LENGTH s.stack = LENGTH xs) ==>
                           evaluate (c,s with stack := xs) =
                             (res, s1 with stack := xs))`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >> EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[set_var_def,cut_state_opt_with_const,do_app_with_stack] >>
    imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    full_simp_tac(srw_ss())[cut_state_opt_def,cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[do_app_with_locals] >>
    TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> full_simp_tac(srw_ss())[]) >>
    imp_res_tac do_app_const >> simp[] >>
    EVAL_TAC >> simp[])
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt gen_tac >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> simp[])
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `evaluate (c2,r)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `q = NONE` \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
    \\ TRY (Cases_on `x`) \\ TRY (Cases_on`e`) \\ full_simp_tac(srw_ss())[jump_exc_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ full_simp_tac(srw_ss())[])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `evaluate (c2,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x = Boolv T` \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `x = Boolv F` \\ full_simp_tac(srw_ss())[get_var_def])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
    \\ TRY (full_simp_tac(srw_ss())[call_env_def] \\ NO_TAC)
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[call_env_def,dec_clock_def,jump_exc_def]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `xxx = SOME s7` MP_TAC
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1 (full_simp_tac(srw_ss())[call_env_def])
    \\ Cases_on `evaluate (r,call_env q (push_env x' (IS_SOME handler) (dec_clock ^s)))` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q''` \\ fs []
    \\ Cases_on `x''` \\ full_simp_tac(srw_ss())[]
    THEN1 (Cases_on `handler`
       \\ full_simp_tac(srw_ss())[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ REPEAT STRIP_TAC
       \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `Exc x' ^s.handler::xs`)
       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ reverse(Cases_on`e`)\\full_simp_tac(srw_ss())[] THEN1 (
         Cases_on`a`>>full_simp_tac(srw_ss())[]>>
         srw_tac[][]>>
         qpat_abbrev_tac`ss = call_env X Y` >>
         first_x_assum(qspec_then`ss.stack`mp_tac) >>
         (impl_tac >- (
            simp[Abbr`ss`] >>
            EVAL_TAC >>
            Cases_on`handler`>>EVAL_TAC >>
            simp[] )) >>
         qpat_abbrev_tac`st:('c,'ffi) dataSem$state = X Y` >>
         `st = ss` by (
           simp[Abbr`ss`,Abbr`st`,dataSemTheory.state_component_equality] >>
           EVAL_TAC >>
           Cases_on`handler`>>EVAL_TAC >>
           simp[] ) >>
         full_simp_tac(srw_ss())[])
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[jump_exc_def]
      \\ Cases_on `s.handler = LENGTH s.stack` \\ full_simp_tac(srw_ss())[LASTN_LEMMA]
      \\ `s.handler < LENGTH s.stack` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `LASTN (s.handler + 1) s.stack` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPECL [`Env x'::xs`,
           `s7 with clock := s7.clock - 1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on `x''` \\ full_simp_tac(srw_ss())[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r,call_env q (push_env x8 T (dec_clock s))) =
          (SOME (Rerr (Rraise b)),s9)`
    \\ Cases_on `evaluate (r''',set_var q'' b s9)` \\ full_simp_tac(srw_ss())[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r''',set_var q'' b s9) = (res,r5)`
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    THEN1 (* NONE *)
     (STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
          \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    THEN1 (* SOME Rval *)
     (STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
          \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]
    THEN1 (* Rraise *)
     (FIRST_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock ^s))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock s))).stack) =
          (call_env q (push_env x8 T (dec_clock s)))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ SIMP_TAC std_ss [Once dec_clock_def]
      \\ SIMP_TAC std_ss [Once push_env_def]
      \\ SIMP_TAC std_ss [Once call_env_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ SIMP_TAC (srw_ss()) [LASTN_LEMMA] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
      \\ Q.PAT_X_ASSUM `jump_exc (set_var q'' b s9) = SOME s2'` MP_TAC
      \\ SIMP_TAC std_ss [Once set_var_def]
      \\ SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ Cases_on `LASTN (s9.handler + 1) s9.stack` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ SIMP_TAC std_ss [Once jump_exc_def] \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH _.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `LASTN (s9.handler + 1) xs` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ `s9 with <|locals := insert q'' b s9.locals; stack := xs;
             handler := s9.handler|> =
          s9 with <|locals := insert q'' b s9.locals; stack := xs|>` by (full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on`a` \\ full_simp_tac(srw_ss())[]
    THEN (* Rtimeout_error *)
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])));

val evaluate_stack = Q.store_thm("evaluate_stack",
  `!c ^s.
      case evaluate (c,s) of
      | (SOME (Rerr(Rabort Rtype_error)),s1) => T
      | (SOME (Rerr(Rabort _)),s1) => (s1.stack = [])
      | (SOME (Rerr _),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler))
      | (_,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler)`,
  REPEAT STRIP_TAC \\ ASSUME_TAC (SPEC_ALL evaluate_stack_swap)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val evaluate_NONE_jump_exc = Q.store_thm("evaluate_NONE_jump_exc",
  `(evaluate (c,^s) = (NONE,u1)) /\ (jump_exc u1 = SOME x) ==>
    (jump_exc s = SOME (s with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))`,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[jump_exc_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] []);

val evaluate_NONE_jump_exc_ALT = Q.store_thm("evaluate_NONE_jump_exc_ALT",
  `(evaluate (c,^s) = (NONE,u1)) /\ (jump_exc s = SOME x) ==>
    (jump_exc u1 = SOME (u1 with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))`,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[jump_exc_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] []);

val evaluate_locals_LN_lemma = Q.prove(
  `!c ^s.
      FST (evaluate (c,s)) <> NONE /\
      FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) ==>
      ((SND (evaluate (c,s))).locals = LN) \/
      ?t. FST (evaluate (c,s)) = SOME (Rerr(Rraise t))`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[call_env_def,fromList_def]
  \\ imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on`a`>>full_simp_tac(srw_ss())[]);

val evaluate_locals_LN = Q.store_thm("evaluate_locals_LN",
  `!c ^s res t.
      (evaluate (c,s) = (res,t)) /\ res <> NONE /\ res <> SOME (Rerr(Rabort Rtype_error)) ==>
      (t.locals = LN) \/ ?t. res = SOME (Rerr(Rraise t))`,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_locals_LN_lemma) \\ full_simp_tac(srw_ss())[]);

val locals_ok_def = Define `
  locals_ok l1 l2 =
    !v x. (sptree$lookup v l1 = SOME x) ==> (sptree$lookup v l2 = SOME x)`;

val locals_ok_IMP = Q.store_thm("locals_ok_IMP",
  `locals_ok l1 l2 ==> domain l1 SUBSET domain l2`,
  full_simp_tac(srw_ss())[locals_ok_def,SUBSET_DEF,domain_lookup] \\ METIS_TAC []);

val locals_ok_refl = Q.store_thm("locals_ok_refl",
  `!l. locals_ok l l`,
  full_simp_tac(srw_ss())[locals_ok_def]);

val locals_ok_cut_env = Q.store_thm("locals_ok_cut_env",
  `locals_ok l1 l2 /\
    (cut_env names l1 = SOME x) ==>
    (cut_env names l2 = SOME x)`,
  full_simp_tac(srw_ss())[cut_env_def] \\ SRW_TAC [] []
  THEN1 (IMP_RES_TAC locals_ok_IMP \\ IMP_RES_TAC SUBSET_TRANS)
  \\ full_simp_tac(srw_ss())[lookup_inter_alt] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[locals_ok_def,domain_lookup,SUBSET_DEF,PULL_EXISTS]
  \\ full_simp_tac(srw_ss())[oneTheory.one] \\ RES_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[]);

val locals_ok_get_var = Q.store_thm("locals_ok_get_var",
  `locals_ok s l /\
    (get_var x s = SOME w) ==>
    (get_var x l = SOME w)`,
  full_simp_tac(srw_ss())[locals_ok_def,get_var_def]);

val locals_ok_get_vars = Q.store_thm("locals_ok_get_vars",
  `!x w.
      locals_ok s l /\
      (get_vars x s = SOME w) ==>
      (get_vars x l = SOME w)`,
  Induct \\ full_simp_tac(srw_ss())[get_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `get_var h s` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars x s` \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]);

val data_to_bvi_ignore = Q.store_thm("data_to_bvi_ignore",
  `(data_to_bvi (s with space := t) = data_to_bvi ^s) ∧
   (data_to_bvi (s with locals := l) = data_to_bvi s) ∧
   (data_to_bvi (s with <| locals := l; space := t |>) = data_to_bvi s)`,
  EVAL_TAC);

val data_to_bvi_refs = Q.store_thm("data_to_bvi_refs",
  `data_to_bvi (s with refs := r) = data_to_bvi s with refs := r ∧
   (data_to_bvi s).refs = s.refs`,
  EVAL_TAC);

val data_to_bvi_ffi = Q.store_thm("data_to_bvi_ffi",
  `(data_to_bvi s).ffi = s.ffi`,
  EVAL_TAC);

val bvi_to_data_refs = Q.store_thm("bvi_to_data_refs",
  `((bvi_to_data s t with refs := z) = bvi_to_data (s with refs := z) t) /\
   ((bvi_to_data s t).refs = s.refs)`,
  EVAL_TAC);

val data_to_bvi_to_data_with_ffi = Q.store_thm("data_to_bvi_to_data_with_ffi",
  `bvi_to_data (data_to_bvi s with ffi := f) s = s with ffi := f`,
  EVAL_TAC \\ rw[state_component_equality]);

val data_to_bvi_to_data_with_refs = Q.store_thm("data_to_bvi_to_data_with_refs",
  `bvi_to_data (data_to_bvi s with refs := f) s = s with refs := f`,
  EVAL_TAC \\ rw[state_component_equality]);

val bvi_to_data_space_locals = Q.store_thm("bvi_to_data_space_locals",
  `((bvi_to_data s t with locals := x) = bvi_to_data s (t with locals := x)) /\
   ((bvi_to_data s t).locals = t.locals) /\
   ((bvi_to_data s t with space := y) = bvi_to_data s (t with space := y)) /\
   ((bvi_to_data s t).space = t.space)`,
  EVAL_TAC);

val evaluate_locals = Q.store_thm("evaluate_locals",
  `!c s res s2 vars l.
      res <> SOME (Rerr(Rabort Rtype_error)) /\ (evaluate (c,s) = (res,s2)) /\
      locals_ok s.locals l ==>
      ?w. (evaluate (c, s with locals := l) =
             (res,if res = NONE then s2 with locals := w
                                else s2)) /\
          locals_ok s2.locals w`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (* Skip *) (METIS_TAC [])
  THEN1 (* Move *)
   (Cases_on `get_var src s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ Q.EXISTS_TAC `insert dest x l` \\ full_simp_tac(srw_ss())[lookup_insert]
    \\ METIS_TAC [])
  THEN1 (* Assign *)
   (Cases_on `names_opt` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `op_requires_names op` \\ full_simp_tac(srw_ss())[cut_state_opt_def] THEN1
     (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[cut_state_opt_def]
      \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
      \\ reverse(Cases_on `do_app op x s`) \\ full_simp_tac(srw_ss())[] >- (
           imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >>
           fs [do_app_def,do_space_def,bvi_to_dataTheory.op_space_reset_def] >>
           full_simp_tac(srw_ss())[do_app_def,do_space_def,data_to_bvi_ignore,
              bvi_to_data_space_locals,
              data_spaceTheory.op_space_req_def,
              bvi_to_dataTheory.op_space_reset_def] >>
           BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[]
           \\ TRY (Cases_on `a`) \\ fs [call_env_def]
           \\ qexists_tac `s2.locals` \\ fs [locals_ok_def]
           \\ rw [] \\ fs [state_component_equality])
      \\ Cases_on `a` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ IMP_RES_TAC do_app_locals \\ full_simp_tac(srw_ss())[set_var_def]
      \\ Q.EXISTS_TAC `insert dest q l`
      \\ full_simp_tac(srw_ss())[set_var_def,locals_ok_def,lookup_insert]
      \\ METIS_TAC [do_app_const])
    \\ full_simp_tac(srw_ss())[cut_state_def]
    \\ Cases_on `cut_env x s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_def]
    \\ SRW_TAC [] [state_component_equality])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def,
           dec_clock_def] \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (Cases_on `cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env
    \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,state_component_equality,locals_ok_def])
  THEN1 (* Raise *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := l) = jump_exc s` by
         full_simp_tac(srw_ss())[jump_exc_def] \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[]
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
    \\ full_simp_tac(srw_ss())[locals_ok_def])
  THEN1 (* Return *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [call_env_def]
    \\ simp[locals_ok_def,lookup_fromList])
  THEN1 (* Seq *)
   (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ METIS_TAC [])
  THEN1 (* If *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x = Boolv T` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x = Boolv F` \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ `call_env q (dec_clock (s with locals := l)) =
          call_env q (dec_clock s)` by
         full_simp_tac(srw_ss())[state_component_equality,dec_clock_def,call_env_def] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def]
      \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_refl]
      \\ SRW_TAC [] [state_component_equality])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
    \\ `call_env q (push_env x' (IS_SOME handler)
          (dec_clock (s with locals := l))) =
        call_env q (push_env x' (IS_SOME handler)
          (dec_clock s))` by
     (Cases_on `handler`
      \\ full_simp_tac(srw_ss())[state_component_equality,dec_clock_def,call_env_def,push_env_def])
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def]
    \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [locals_ok_refl,with_same_locals]));

val funpow_dec_clock_clock = Q.store_thm ("funpow_dec_clock_clock",
  `!n s. FUNPOW dec_clock n s = (s with clock := s.clock - n)`,
  Induct_on `n` >>
  srw_tac[][FUNPOW, state_component_equality, dec_clock_def, ADD1] >>
  decide_tac);

val evaluate_mk_ticks = Q.store_thm ("evaluate_mk_ticks",
  `!p s n.
    evaluate (mk_ticks n p, s)
    =
    if s.clock < n then
      (SOME (Rerr(Rabort Rtimeout_error)), s with <| clock := 0; locals := fromList []; stack := [] |>)
    else
      evaluate (p, FUNPOW dec_clock n s)`,
  Induct_on `n` >>
  srw_tac[][evaluate_def, mk_ticks_def, FUNPOW] >>
  full_simp_tac(srw_ss())[mk_ticks_def, evaluate_def] >>
  srw_tac[][funpow_dec_clock_clock, dec_clock_def] >>
  simp [call_env_def] >>
  `s.clock - n = 0` by decide_tac >>
  `s.clock - (n+1) = 0` by decide_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ADD1, LESS_OR_EQ] >>
  full_simp_tac (srw_ss()++ARITH_ss) []);

val FUNPOW_dec_clock_code = Q.store_thm("FUNPOW_dec_clock_code[simp]",
  `((FUNPOW dec_clock n t).code = t.code) /\
    ((FUNPOW dec_clock n t).stack = t.stack) /\
    ((FUNPOW dec_clock n t).handler = t.handler) /\
    ((FUNPOW dec_clock n t).refs = t.refs) /\
    ((FUNPOW dec_clock n t).ffi = t.ffi) /\
    ((FUNPOW dec_clock n t).global = t.global) /\
    ((FUNPOW dec_clock n t).locals = t.locals) /\
    ((FUNPOW dec_clock n t).compile = t.compile) /\
    ((FUNPOW dec_clock n t).compile_oracle = t.compile_oracle) /\
    ((FUNPOW dec_clock n t).clock = t.clock - n)`,
  Induct_on `n` \\ full_simp_tac(srw_ss())[FUNPOW_SUC,dec_clock_def] \\ DECIDE_TAC);

val jump_exc_NONE = Q.store_thm("jump_exc_NONE",
  `(jump_exc (t with locals := x) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with clock := c) = NONE <=> jump_exc t = NONE)`,
  FULL_SIMP_TAC (srw_ss()) [jump_exc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ FULL_SIMP_TAC std_ss []);

val jump_exc_IMP = Q.store_thm("jump_exc_IMP",
  `(jump_exc s = SOME t) ==>
    s.handler < LENGTH s.stack /\
    ?n e xs. (LASTN (s.handler + 1) s.stack = Exc e n::xs) /\
             (t = s with <|handler := n; locals := e; stack := xs|>)`,
  SIMP_TAC std_ss [jump_exc_def]
  \\ Cases_on `LASTN (s.handler + 1) s.stack` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]);

val do_app_Rerr = Q.store_thm("do_app_Rerr",
  `dataSem$do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x)) `,
  rw[dataSemTheory.do_app_def,dataSemTheory.do_install_def]
  \\ every_case_tac \\ fs[]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac bviPropsTheory.do_app_err \\ fs []);

val do_app_change_clock = Q.store_thm("do_app_change_clock",
  `(do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))`,
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def,do_install_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac bviPropsTheory.do_app_change_clock >>
  full_simp_tac(srw_ss())[data_to_bvi_def,bvi_to_data_def,state_component_equality] >>
  rpt var_eq_tac >> simp[] >>
  full_simp_tac(srw_ss())[consume_space_def] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] );

val do_app_change_clock_err = Q.store_thm("do_app_change_clock_err",
  `(do_app op args s1 = Rerr e) ==>
   (do_app op args (s1 with clock := ck) = Rerr e)`,
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac bviPropsTheory.do_app_change_clock_err >>
  full_simp_tac(srw_ss())[data_to_bvi_def,bvi_to_data_def,state_component_equality] >>
  rpt var_eq_tac >> simp[] >>
  full_simp_tac(srw_ss())[consume_space_def] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] );

val cut_state_eq_some = Q.store_thm("cut_state_eq_some",
  `cut_state names s = SOME y ⇔ ∃z. cut_env names s.locals = SOME z ∧ y = s with locals := z`,
  srw_tac[][cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[EQ_IMP_THM]);

val cut_state_eq_none = Q.store_thm("cut_state_eq_none",
  `cut_state names s = NONE ⇔ cut_env names s.locals = NONE`,
  srw_tac[][cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[EQ_IMP_THM]);

val with_same_clock = Q.store_thm("with_same_clock[simp]",
  `^s with clock := s.clock = s`,
  srw_tac[][state_component_equality]);

val evaluate_add_clock = Q.store_thm ("evaluate_add_clock",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2) ∧
    res ≠ SOME(Rerr(Rabort Rtimeout_error))
    ⇒
    !ck. evaluate (exps,s1 with clock := s1.clock + ck) = (res, s2 with clock := s2.clock + ck)`,
  recInduct evaluate_ind >> srw_tac[][evaluate_def]
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[get_var_def,set_var_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[cut_state_opt_def,cut_state_eq_some,cut_state_eq_none] >>
    every_case_tac >> full_simp_tac(srw_ss())[cut_state_eq_some,cut_state_eq_none] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[set_var_def] >> srw_tac[][] >>
    imp_res_tac do_app_change_clock >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[state_component_equality] >>
    imp_res_tac do_app_const >> full_simp_tac(srw_ss())[] >>
    imp_res_tac do_app_Rerr >> full_simp_tac(srw_ss())[] >>
    TRY (first_x_assum(qspec_then`s.clock`mp_tac)) >> simp[] >>
    fs [do_app_def,option_case_eq,bviPropsTheory.case_eq_thms,call_env_def,
        dataSemTheory.do_space_def,bvi_to_dataTheory.op_requires_names_def] >>
    imp_res_tac do_app_Rerr \\ fs [] \\ rveq \\ fs [] >>
    fs [do_app_def,option_case_eq,bviPropsTheory.case_eq_thms,call_env_def,
        dataSemTheory.do_space_def,bvi_to_dataTheory.op_requires_names_def,
        data_to_bvi_def,bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,
        bviSemTheory.bvi_to_bvl_def,bvlSemTheory.do_app_def,
        data_spaceTheory.op_space_req_def]
    \\ fs [] \\ rveq \\ fs []
    \\ fs [] \\ rveq \\ fs [])
  >- ( EVAL_TAC >> simp[state_component_equality] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> EVAL_TAC )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[jump_exc_NONE] >>
    imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[jump_exc_def])
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][call_env_def] )
  >- (
    full_simp_tac(srw_ss())[LET_THM] >>
    pairarg_tac >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    rev_full_simp_tac(srw_ss())[] >> srw_tac[][] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][call_env_def,dec_clock_def,push_env_def,pop_env_def,set_var_def] >>
    first_x_assum(qspec_then`ck`mp_tac) >> simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]))

val set_var_const = Q.store_thm("set_var_const[simp]",
  `(set_var x y z).ffi = z.ffi ∧
   (set_var x y z).clock = z.clock`,
  EVAL_TAC)

val set_var_with_const = Q.store_thm("set_var_with_const",
  `(set_var x y (z with clock := k)) = set_var x y z with clock := k`,
  EVAL_TAC)

val cut_state_opt_const = Q.store_thm("cut_state_opt_const",
  `cut_state_opt x y = SOME z ⇒
   z.ffi = y.ffi ∧
   z.global = y.global`,
   EVAL_TAC >>
   every_case_tac >> EVAL_TAC >>
   srw_tac[][] >> srw_tac[][]);

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app x y z = Rval (a,b) ⇒
   z.ffi.io_events ≼ b.ffi.io_events`,
  Cases_on `x = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  srw_tac[][bvi_to_data_def] >>
  imp_res_tac bviPropsTheory.do_app_io_events_mono >>
  full_simp_tac(srw_ss())[data_to_bvi_def] >>
  full_simp_tac(srw_ss())[consume_space_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[])

val call_env_const = Q.store_thm("call_env_const[simp]",
  `(call_env x y).ffi = y.ffi ∧
   (call_env x y).clock = y.clock`,
  EVAL_TAC);

val call_env_with_const = Q.store_thm("call_env_with_const",
  `(call_env x  (y with clock := z)) = call_env x y with clock := z`,
  EVAL_TAC);

val dec_clock_const = Q.store_thm("dec_clock_const[simp]",
  `(dec_clock s).ffi = s.ffi`,
  EVAL_TAC);

val add_space_const = Q.store_thm("add_space_const[simp]",
  `(add_space s k).ffi = s.ffi`,
  EVAL_TAC);

val push_env_const = Q.store_thm("push_env_const[simp]",
  `(push_env x y z).ffi = z.ffi ∧
   (push_env x y z).clock = z.clock`,
  Cases_on`y`>> EVAL_TAC);

val push_env_with_const = Q.store_thm("push_env_with_const",
  `(push_env x y (z with clock := k)) = (push_env x y z) with clock := k`,
  Cases_on`y`>>EVAL_TAC);

val pop_env_const = Q.store_thm("pop_env_const",
  `pop_env a = SOME b ⇒
   b.ffi = a.ffi`,
   EVAL_TAC >>
   every_case_tac >> EVAL_TAC >>
   srw_tac[][] >> srw_tac[][]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events`,
  recInduct evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  TRY (pairarg_tac >> full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])>>
  imp_res_tac cut_state_opt_const >>full_simp_tac(srw_ss())[] >>
  imp_res_tac pop_env_const >>full_simp_tac(srw_ss())[] >>
  imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_io_events_mono  >>full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]);

val with_clock_ffi = Q.store_thm("with_clock_ffi",
  `(^s with clock := y).ffi = s.ffi`,
  EVAL_TAC)

val evaluate_add_clock_io_events_mono = Q.store_thm("evaluate_add_clock_io_events_mono",
  `∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`find_code` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][dec_clock_def,call_env_with_const,push_env_with_const] >>
    imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][call_env_with_const] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[set_var_with_const] >>
    metis_tac[evaluate_io_events_mono,SND,PAIR,IS_PREFIX_TRANS,set_var_const,set_var_with_const,with_clock_ffi]) >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[cut_state_opt_with_const] >> rev_full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_change_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_change_clock_err >> full_simp_tac(srw_ss())[] >>
  imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[jump_exc_NONE] >>
  rveq >> full_simp_tac(srw_ss())[state_component_equality] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]);

val semantics_Div_IMP_LPREFIX = Q.store_thm("semantics_Div_IMP_LPREFIX",
  `semantics ffi prog co cc start = Diverge l ==> LPREFIX (fromList ffi.io_events) l`,
  simp[semantics_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ rw[]
  \\ qmatch_abbrev_tac`LPREFIX l1 (build_lprefix_lub l2)`
  \\ `l1 ∈ l2 ∧ lprefix_chain l2` suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_def]
  \\ conj_tac
  >- (
    unabbrev_all_tac >> simp[]
    \\ qexists_tac`0`>>fs[evaluate_def]
    \\ CASE_TAC >> fs[]
    \\ CASE_TAC >> fs[]
    \\ CASE_TAC >> fs[] )
  \\ simp[Abbr`l2`]
  \\ simp[Once(GSYM o_DEF),IMAGE_COMPOSE]
  \\ match_mp_tac prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def,PULL_EXISTS]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES
  \\ simp[LESS_EQ_EXISTS]
  \\ metis_tac[evaluate_add_clock_io_events_mono,
               initial_state_simp,initial_state_with_simp]);

val semantics_Term_IMP_PREFIX = Q.store_thm("semantics_Term_IMP_PREFIX",
  `semantics ffi prog co cc start = Terminate tt l ==> ffi.io_events ≼ l`,
  simp[semantics_def] \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[]
  \\ imp_res_tac evaluate_io_events_mono \\ fs[]);

val Resource_limit_hit_implements_semantics =
  Q.store_thm("Resource_limit_hit_implements_semantics",
  `implements {Terminate Resource_limit_hit ffi.io_events}
       {semantics ffi (fromAList prog) co cc start}`,
  fs [implements_def,extend_with_resource_limit_def]
  \\ Cases_on `semantics ffi (fromAList prog) co cc start` \\ fs []
  \\ imp_res_tac semantics_Div_IMP_LPREFIX \\ fs []
  \\ imp_res_tac semantics_Term_IMP_PREFIX \\ fs []);

val _ = export_theory();
