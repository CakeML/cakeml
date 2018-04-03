open preamble astTheory terminationTheory flatLangTheory;

val _ = numLib.prefer_num();

val _ = new_theory "flat_uncheck_ctors";

val compile_pat_def = tDefine "compile_pat" `
  (compile_pat flatLang$Pany = flatLang$Pany) ∧
  (compile_pat (Pvar v) = Pvar v) ∧
  (compile_pat (Plit l) = Plit l) ∧
  (compile_pat (Pcon tag ps) = Pcon (SOME (the (0,NONE) tag)) (MAP compile_pat ps)) ∧
  (compile_pat (Pref p) = Pref (compile_pat p))`
 (WF_REL_TAC `measure pat_size` >>
  rw [] >>
  Induct_on `ps` >>
  rw [pat_size_def] >>
  fs []);

val compile_def = tDefine "compile" `
  (compile [] = []) /\
  (compile [Raise t e] = [Raise t (HD (compile [e]))]) /\
  (compile [Handle t e pes] =  [Handle t (HD (compile [e])) (MAP (λ(p,e). (p,HD (compile [e]))) pes)]) /\
  (compile [Lit t l] = [Lit t l]) /\
  (compile [Con t tag es] = [Con t (SOME (the (0,NONE) tag)) (compile es)] ) /\
  (compile [Var_local t v] = [Var_local t v]) /\
  (compile [Fun t v e] = [Fun t v (HD (compile [e]))]) /\
  (compile [App t op es] = [App t op (compile es)]) /\
  (compile [If t e1 e2 e3] = [If t (HD (compile [e1])) (HD (compile [e2])) (HD (compile [e3]))]) ∧
  (compile [Mat t e pes] =  [Mat t (HD (compile [e])) (MAP (λ(p,e). (p,HD (compile [e]))) pes)]) /\
  (compile [Let t vo e1 e2] = [Let t vo (HD (compile [e1])) (HD (compile [e2]))]) /\
  (compile [Letrec t funs e] =
      [Letrec t (MAP (\(a, b, e). (a,b, HD (compile [e]))) funs) (HD (compile [e]))]) /\
  (compile (x::y::xs) = compile [x] ++ compile (y::xs))`
 (WF_REL_TAC `measure exp6_size`
  \\ simp []
  \\ conj_tac
  >- (
     gen_tac
     \\ Induct_on `funs`
     \\ rw [exp_size_def]
     \\ rw [exp_size_def]
     \\ res_tac \\ rw []
     \\ qmatch_goalsub_rename_tac `tra_size t2`
     \\ pop_assum (qspec_then `t2` mp_tac) \\ fs []
  )
  >- (
     rpt strip_tac
     \\ Induct_on `pes`
     \\ rw [exp_size_def]
     \\ rw [exp_size_def]
     \\ res_tac \\ rw []
  ));

val compile_ind = theorem"compile_ind";

val compile_length = Q.store_thm ("compile_length[simp]",
  `! es. LENGTH (compile es) = LENGTH es`,
  ho_match_mp_tac compile_ind
  \\ rw [compile_def]);

val compile_sing = Q.store_thm ("compile_sing",
  `! e. ?e2. compile [e] = [e2]`,
  rw []
  \\ qspec_then `[e]` mp_tac compile_length
  \\ simp_tac(std_ss++listSimps.LIST_ss)[LENGTH_EQ_NUM_compute]);

val compile_nil = save_thm ("compile_nil[simp]", EVAL ``compile []``);

val compile_cons = Q.store_thm ("compile_cons",
  `! e es. compile (e::es) = HD (compile [e]) :: (compile es)`,
  rw []
  \\ Cases_on `es`
  \\ rw [compile_def]
  \\ METIS_TAC [compile_sing, HD]);

val compile_decs = Define `
  (compile_decs [] = []) ∧
  (compile_decs (flatLang$Dlet e :: ds) = flatLang$Dlet (HD (compile [e])) :: compile_decs ds) ∧
  (compile_decs (_::ds) = compile_decs ds)`;

val _ = export_theory();

