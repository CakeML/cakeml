(*
  This compiler phase replaces tuples with constructors (with tag 0).
*)
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
  (compile [Handle t e pes] =
    [Handle t (HD (compile [e])) (MAP (λ(p,e). (compile_pat p,HD (compile [e]))) pes)]) /\
  (compile [Lit t l] = [Lit t l]) /\
  (compile [Con t tag es] = [Con t (SOME (the (0,NONE) tag)) (compile es)] ) /\
  (compile [Var_local t v] = [Var_local t v]) /\
  (compile [Fun t v e] = [Fun t v (HD (compile [e]))]) /\
  (compile [App t op es] = [App t op (compile es)]) /\
  (compile [If t e1 e2 e3] = [If t (HD (compile [e1])) (HD (compile [e2])) (HD (compile [e3]))]) ∧
  (compile [Mat t e pes] =  [Mat t (HD (compile [e])) (MAP (λ(p,e). (compile_pat p,HD (compile [e]))) pes)]) /\
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

Theorem compile_length[simp]:
   ! es. LENGTH (compile es) = LENGTH es
Proof
  ho_match_mp_tac compile_ind
  \\ rw [compile_def]
QED

Theorem compile_sing:
   ! e. ?e2. compile [e] = [e2]
Proof
  rw []
  \\ qspec_then `[e]` mp_tac compile_length
  \\ simp_tac(std_ss++listSimps.LIST_ss)[LENGTH_EQ_NUM_compute]
QED

val compile_nil = save_thm ("compile_nil[simp]", EVAL ``compile []``);

Theorem compile_not_nil[simp]:
   compile [x] <> []
Proof
  strip_tac \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [compile_length]
QED

Theorem compile_cons:
   ! e es. compile (e::es) = HD (compile [e]) :: (compile es)
Proof
  rw []
  \\ Cases_on `es`
  \\ rw [compile_def]
  \\ METIS_TAC [compile_sing, HD]
QED

Theorem compile_append:
   !es es2. compile (es:flatLang$exp list ++ es2) = compile es ++ compile es2
Proof
  Induct >>
  rw [compile_def] >>
  Cases_on `es` >>
  rw [compile_def] >>
  fs [compile_def] >>
  Cases_on `es2` >>
  rw [] >>
  Cases_on `h` >>
  rw [compile_def]
QED

Theorem compile_reverse:
   !es. compile (REVERSE es) = REVERSE (compile es:flatLang$exp list)
Proof
  ho_match_mp_tac compile_ind >>
  rw [compile_def, compile_append]
QED

Theorem compile_HD_sing:
   [HD (compile [e])] = compile [e:flatLang$exp]
Proof
  qspec_then`e`strip_assume_tac compile_sing
  \\ fs[]
QED

val compile_decs = Define `
  (compile_decs [] = []) ∧
  (compile_decs (flatLang$Dlet e :: ds) = flatLang$Dlet (HD (compile [e])) :: compile_decs ds) ∧
  (compile_decs (_::ds) = compile_decs ds)`;

val _ = export_theory();
