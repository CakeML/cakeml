(**
 Formalization of the Abstract Syntax Tree of a subset used in the Flover
 framework
 **)
Theory Commands
Ancestors
  real Abbrevs Expressions ExpressionAbbrevs ExpressionSemantics
  MachineType
Libs
  simpLib realLib RealArith preambleFloVer

(**
  Next define what a program is.
  Currently no loops, or conditionals.
  Only assignments and return statement
**)
Datatype:
  cmd = Let mType num ('v expr) cmd
       | Ret ('v expr)
End

Definition toREvalCmd_def:
  toREvalCmd (f:real cmd) : real cmd =
  case f of
    | Let m x e g => Let REAL x (toREval e) (toREvalCmd g)
    | Ret e => Ret (toREval e)
End

(**
  Define big step semantics for the Flover language, terminating on a "returned"
  result value
 **)
Inductive bstep:
  (!m m' x e s E v res Gamma.
      eval_expr E Gamma e v m /\
      Gamma (Var x) = SOME m ∧
      bstep s (updEnv x v E) Gamma res m' ==>
      bstep (Let m x e s) E Gamma res m') /\
  (!m e E v Gamma.
      eval_expr E Gamma e v m ==>
      bstep (Ret e) E Gamma v m)
End

(**
  Generate a better case lemma
**)
Theorem bstep_cases[allow_rebind] =
  map (GEN_ALL o SIMP_CONV (srw_ss()) [Once bstep_cases])
    [``bstep (Let m x e s) E defVars vR m'``,
     ``bstep (Ret e) E defVars vR m``] |> LIST_CONJ

val [let_b, ret_b] = CONJ_LIST 2 bstep_rules;
Theorem let_b = let_b
Theorem ret_b = ret_b

(**
  The free variables of a command are all used variables of exprressions
  without the let bound variables
**)
Definition freeVars_def:
  freeVars (f: 'a cmd) :num_set =
    case f of
      |Let m x e g => delete x (union (usedVars e) (freeVars g))
      |Ret e => usedVars e
End

(**
  The defined variables of a command are all let bound variables
**)
Definition definedVars_def:
  definedVars (f:'a cmd) :num_set =
    case f of
      |Let m (x:num) e g => insert x () (definedVars g)
      |Ret e => LN
End

Theorem bstep_eq_env:
  !f E1 E2 Gamma v m.
      (!x. E1 x = E2 x) /\
      bstep f E1 Gamma v m ==>
      bstep f E2 Gamma v m
Proof
  Induct \\ rpt strip_tac \\ fs[bstep_cases]
  >- (qexists_tac `v'` \\ conj_tac
      \\ TRY (drule eval_eq_env \\ disch_then drule \\ fs[] \\ FAIL_TAC"")
      \\ first_x_assum irule \\ qexists_tac `updEnv n v' E1` \\ fs[]
      \\ rpt strip_tac \\ fs[updEnv_def])
  \\ irule eval_eq_env \\ asm_exists_tac \\ fs[]
QED

Theorem swap_Gamma_bstep:
  !f E vR m Gamma1 Gamma2.
      (! e. Gamma1 e = Gamma2 e) /\
      bstep f E Gamma1 vR m ==>
      bstep f E Gamma2 vR m
Proof
  Induct_on `f` \\ rpt strip_tac \\ fs[bstep_cases]
  \\ metis_tac [swap_Gamma_eval_expr]
QED

Theorem bstep_Gamma_det:
  !f E1 E2 Gamma v1 v2 m1 m2.
      bstep f E1 Gamma v1 m1 /\
      bstep f E2 Gamma v2 m2 ==>
      m1 = m2
Proof
  Induct_on `f` \\ rpt strip_tac \\ fs[bstep_cases]
  \\ metis_tac[Gamma_det]
QED

Definition getRetExp_def:
(getRetExp (Let m x e g) = getRetExp g) /\
(getRetExp (Ret e) = e)
End

