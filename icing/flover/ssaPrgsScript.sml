(**
  We define a pseudo SSA predicate.
  The formalization is similar to the renamedApart property in the LVC framework
  by Schneider, Smolka and Hack (http://dblp.org/rec/conf/itp/SchneiderSH15)
  Our predicate is not as fully fledged as theirs, but we especially borrow the
  idea of annotating the program with the predicate with the set of free and
  defined variables
**)
open pred_setSyntax pred_setTheory;
open AbbrevsTheory ExpressionsTheory ExpressionAbbrevsTheory FloverTactics
CommandsTheory MachineTypeTheory;
open preambleFloVer;

val _ = new_theory "ssaPrgs";

Theorem validVars_add:
  !(e:'a expr) Vs n.
     domain (usedVars e) ⊆ domain Vs ==>
     domain (usedVars e) ⊆ domain (insert n () Vs)
Proof
  fs [domain_insert, SUBSET_DEF]
QED

(**
  Inductive ssa predicate, following the definitions from the LVC framework,
  see top of file for citation
  We maintain as an invariant that if we have
  ssa f
**)
Inductive ssa:
  (!m x e s inVars (Vterm:num_set).
     (domain (usedVars e)) SUBSET (domain inVars) /\
     (~ (x IN (domain inVars)))  /\
     ssa s (insert x () inVars) Vterm ==>
     ssa (Let m x e s) inVars Vterm) /\
  (!e inVars Vterm.
     (domain (usedVars e)) SUBSET (domain inVars) /\
     (domain inVars = domain Vterm) ==>
     ssa (Ret e) inVars Vterm)
End

(*
  As usual
*)
Theorem ssa_cases[allow_rebind] =
  map (GEN_ALL o SIMP_CONV (srw_ss()) [Once ssa_cases])
    [``ssa (Let m x e s) inVars Vterm``,
     ``ssa (Ret e) inVars Vterm``] |> LIST_CONJ;

val [ssaLet, ssaRet] = CONJ_LIST 2 ssa_rules;

Theorem ssaLet = ssaLet
Theorem ssaRet = ssaRet

Theorem ssa_subset_freeVars:
  !(f:'a cmd) inVars outVars.
      ssa f inVars outVars ==>
      (domain (freeVars f)) SUBSET (domain inVars)
Proof
  ho_match_mp_tac ssa_ind \\ rw []
  >- (once_rewrite_tac [freeVars_def, domain_insert] \\ simp []
      \\ once_rewrite_tac [domain_union]
      \\ fs[SUBSET_DEF]
      \\ rpt strip_tac
      >- (first_x_assum match_mp_tac
          \\ simp [])
      >- (fs [ domain_insert]
          \\ metis_tac[]))
  >- (once_rewrite_tac[freeVars_def]
      \\ fs [])
QED

Theorem ssa_equal_set_ind:
  !(f:'a cmd) inVars outVars.
       ssa f inVars outVars ==>
        (!inVars'.
           (domain inVars' = domain inVars) ==>
           ssa f inVars' outVars)
Proof
  qspec_then `\f inVars outVars.
    !inVars'. (domain inVars' = domain inVars) ==> ssa f inVars' outVars`
    (fn thm => assume_tac (SIMP_RULE std_ss [] thm)) ssa_ind
  \\ first_x_assum match_mp_tac
  \\ conj_tac \\ rw[]
  >- (match_mp_tac ssaLet \\ fs[]
      \\ first_x_assum match_mp_tac
      \\ simp[ domain_insert])
  >- (match_mp_tac ssaRet \\ fs[])
QED

Theorem ssa_equal_set:
  !(f:'a cmd) inVars outVars inVars'.
       (domain inVars' = domain inVars) /\
       ssa f inVars outVars ==>
       ssa f inVars' outVars
Proof
  rpt strip_tac
  \\ qspecl_then [`f`, `inVars`, `outVars`] assume_tac ssa_equal_set_ind
  \\ specialize `ssa _ _ _ ==> _` `ssa f inVars outVars`
  \\ specialize `!inVars'. A ==> B` `inVars'`
  \\ first_x_assum match_mp_tac \\ fs[]
QED

Definition validSSA_def:
  validSSA (f:real cmd) (inVars:num_set) =
    case f of
      |Let m x e g =>
        ((lookup x inVars = NONE) /\
         (subspt (usedVars e) inVars) /\
         (validSSA g (insert x () inVars)))
      |Ret e =>
         (subspt (usedVars e) inVars)
End

Theorem validSSA_sound:
  !(f:real cmd) (inVars:num_set).
       (validSSA f inVars) ==>
       ?outVars.
         ssa f inVars outVars
Proof
  Induct \\ once_rewrite_tac [validSSA_def] \\ rw[]
  >- (specialize `!inVars. _ ==> _` `insert n () inVars`
      \\ `?outVars. ssa f (insert n () inVars) outVars` by (first_x_assum match_mp_tac \\ simp[])
      \\ qexists_tac `outVars`
      \\ match_mp_tac ssaLet
      \\ fs [subspt_def, SUBSET_DEF, lookup_NONE_domain])
  >- (exists_tac ``inVars:num_set``
      \\ match_mp_tac ssaRet
      \\ fs[subspt_def, SUBSET_DEF])
QED

Theorem ssa_shadowing_free:
  !m x y v v' e f inVars outVars E Gamma.
      ssa (Let m x (toREval e) (toREvalCmd f)) inVars outVars /\
      (y IN (domain inVars)) /\
      eval_expr E Gamma (toREval e) v REAL ==>
      !E n. updEnv x v (updEnv y v' E) n = updEnv y v' (updEnv x v E) n
Proof
  rpt strip_tac
  \\ inversion `ssa (Let m x (toREval e) (toREvalCmd f)) _ _` ssa_cases
  \\ fs[updEnv_def]
  \\ Cases_on `n = x` \\ rveq \\ simp[]
  \\ Cases_on `n = y` \\ rveq \\ rw[]
  \\ metis_tac[]
QED

val _ = export_theory ();
