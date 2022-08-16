(*
   Interpreter function for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory compute_syntaxTheory
     compute_evalTheory compute_evalProofTheory;
open ml_monadBaseTheory ml_monadBaseLib;
open mlvectorTheory

val _ = new_theory "compute_exec";

(* -------------------------------------------------------------------------
 * st_ex_monad setup
 * ------------------------------------------------------------------------- *)

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = SOME “raise_Failure”,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

Overload return[local] = “st_ex_return”;
Overload failwith[local] = “raise_Failure”;
Overload handle[local] = “handle_Failure”;
Overload error[local] = “raise_Failure «error»”;
Overload timeout[local] = “raise_Failure «timeout»”;

(* -------------------------------------------------------------------------
 * execute engine
 * ------------------------------------------------------------------------- *)

Datatype:
  cv = Num num | Pair cv cv
End

Datatype:
  ce = Const num
     | Var num
     | Monop (cv -> cv) ce
     | Binop (cv -> cv -> cv) ce ce
     | App num (ce list)
     | If ce ce ce
     | Let ce ce
End

Definition env_lookup_def:
  env_lookup n [] = Num 0 /\
  env_lookup n (x::xs) =
    if n = 0n then x else env_lookup (n-1) xs
End

Definition exec_def:
  exec funs env ck (Const n) =
    return (Num n) ∧
  exec funs env ck (Var n) =
    return (env_lookup n env) ∧
  exec funs env ck (Monop m x) =
    do
      v <- exec funs env ck x;
      return (m v)
    od ∧
  exec funs env ck (Binop b x y) =
    do
      v <- exec funs env ck x;
      w <- exec funs env ck y;
      return (b v w)
    od ∧
  exec funs env ck (App f xs) =
    (if ck = 0 then timeout else
    do
      vs <- exec_list funs env ck xs [];
      exec funs vs (ck-1n) (sub funs f)
    od) ∧
  exec funs env ck (Let x y) =
    (if ck = 0 then timeout else
    do
      v <- exec funs env ck x;
      exec funs (v::env) (ck-1) y
    od) ∧
  exec funs env ck (If x y z) =
    do
      v <- exec funs env ck x;
      exec funs env ck (if v = Num 0 then z else y)
    od ∧
  exec_list funs env ck [] acc =
    return acc ∧
  exec_list funs env ck (x::xs) acc =
    do
      v <- exec funs env ck x;
      exec_list funs env ck xs (v::acc)
    od
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) $
              λx. case x of INL (_,_,ck,cv) => (ck, ce_size cv)
                          | INR (_,_,ck,cv,_) => (ck, ce1_size cv)’
  \\ rw [] \\ fs []
End

Definition monop_def:
  (monop Fst    = λx. case x of Pair y z => y | _ => Num 0) ∧
  (monop Snd    = λx. case x of Pair y z => z | _ => Num 0) ∧
  (monop IsPair = λx. case x of Pair y z => Num 1 | _ => Num 0)
End

Definition to_num_def[simp]:
  to_num (Pair _ _) = 0 ∧
  to_num ((Num n):cv) = n
End

Definition cv_T_def:
  cv_T = Num 1 : cv
End

Definition cv_F_def:
  cv_F = Num 0 : cv
End

Definition binop_def:
  binop op =
    case op of
    | Add => (λx y. Num (to_num x + to_num y))
    | Sub => (λx y. Num (to_num x - to_num y))
    | Mul => (λx y. Num (to_num x * to_num y))
    | Div => (λx y. Num (let k = to_num y in if k = 0 then 0 else to_num x DIV k))
    | Mod => (λx y. Num (let k = to_num y in if k = 0 then to_num x else to_num x MOD k))
    | Eq   => (λx y. if x = y then cv_T else cv_F)
    | Less => (λx y. case x of
                     | Pair _ _ => cv_F
                     | Num n    => case y of
                                   | Pair _ _ => cv_F
                                   | Num m    => if n < m then cv_T else cv_F)
End

Definition to_ce_def:
  to_ce eqs args body = ARB
End

Definition compile_to_ce_def:
  compile_to_ce eqs (n,args,body) = to_ce eqs args body
End

Definition build_funs_def:
  build_funs eqs = Vector ((MAP (compile_to_ce eqs) eqs) : ce list)
End

Definition from_cv_def[simp]:
  from_cv ((Num n):cv) = (Num n : compute_exp) ∧
  from_cv (Pair x y) = Pair (from_cv x) (from_cv y)
End

Definition from_res_def[simp]:
  from_res f (M_success v) = M_success (f v) ∧
  from_res f (M_failure e) = M_failure e
End

Inductive code_rel:
  (∀eqs env vars n k.
     LENGTH env ≤ k ∧ EL (k - LENGTH env) vars = n ⇒
     code_rel eqs env vars ((Var n):compute_exp) ((Var k):ce)) ∧
  (∀eqs env vars n k.
     k < LENGTH env ∧ EL k env = Num n ⇒
     code_rel eqs env vars (Num n) (Var k)) ∧
  (∀eqs env vars x y k.
     k < LENGTH env ∧ EL k env = Pair x y ⇒
     code_rel eqs env vars (Pair (from_cv x) (from_cv y)) (Var k)) ∧
  (∀eqs env vars n.
     code_rel eqs env vars (Num n) (Const n)) ∧
  (∀eqs env vars x y x1 y1.
     code_rel eqs env vars x x1 ∧
     code_rel eqs env vars y y1 ⇒
     code_rel eqs env vars (Pair x y) (Binop Pair x1 y1)) ∧
  (∀eqs env vars x y z x1 y1 z1.
     code_rel eqs env vars x x1 ∧
     code_rel eqs env vars y y1 ∧
     code_rel eqs env vars z z1 ⇒
     code_rel eqs env vars (If x y z) (If x1 y1 z1)) ∧
  (∀eqs env vars s x y x1 y1.
     code_rel eqs env vars x x1 ∧
     code_rel eqs env (s::vars) y y1 ⇒
     code_rel eqs env vars (Let s x y) (Let x1 y1)) ∧
  (∀eqs env vars xs xs1 f l body n.
     LIST_REL (code_rel eqs env vars) xs xs1 ∧
     n < LENGTH eqs ∧ EL n eqs = (f,l,body) ∧
     LENGTH l = LENGTH xs ∧
     (∀k. k < n ⇒ FST (EL k eqs) ≠ f) ⇒
     code_rel eqs env vars (App f xs) (App n xs1)) ∧
  (∀eqs env vars x x1 m.
     code_rel eqs env vars x x1 ⇒
     code_rel eqs env vars (Uop m x) (Monop (monop m) x1)) ∧
  (∀eqs env vars x y x1 y1 b.
     code_rel eqs env vars x x1 ∧
     code_rel eqs env vars y y1 ⇒
     code_rel eqs env vars (Binop b x y) (Binop (binop b) x1 y1))
End

Theorem option_ALOOKUP:
  ∀eqs n f l body s.
    n < LENGTH eqs ∧
    EL n eqs = (f,l,body) ∧
    (∀k. k < n ⇒ FST (EL k eqs) ≠ f) ⇒
    option (ALOOKUP eqs) f s = (M_success (l,body),s)
Proof
  Induct \\ fs []
  \\ Cases_on ‘n’ \\ fs []
  \\ gvs [option_def,st_ex_return_def,ALOOKUP_def,FORALL_PROD]
  \\ rpt strip_tac
  \\ first_assum $ qspec_then ‘0’ mp_tac
  \\ strip_tac \\ fs []
  \\ first_x_assum irule
  \\ first_x_assum $ irule_at Any
  \\ rw []
  \\ ‘SUC k < SUC n'’ by fs []
  \\ res_tac \\ fs []
QED

Theorem LESS_LENGTH_env_lookup:
  ∀xs n. n < LENGTH xs ⇒ env_lookup n xs = EL n xs
Proof
  Induct \\ fs []
  \\ Cases_on ‘n’ \\ fs [env_lookup_def]
QED

Theorem compute_eval_from_cv:
  ∀x s ck eqs. compute_eval ck eqs (from_cv x) s = (M_success (from_cv x),s)
Proof
  Induct
  \\ fs [compute_eval_def,st_ex_return_def,st_ex_bind_def]
QED

Theorem compile_eval_list_length:
  ∀cvs xs ck ceqs s s'.
    compute_eval_list ck ceqs cvs s = (M_success xs,s') ⇒ LENGTH xs = LENGTH cvs
Proof
  Induct \\ fs [compute_eval_def,st_ex_return_def,st_ex_bind_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
QED

Theorem cexp_value_from_cv:
  ∀y. cexp_value (from_cv y)
Proof
  Induct \\ fs [cexp_value_def]
QED

Triviality cexp_vars_def[simp] = compute_syntaxProofTheory.cexp_vars_def;

Definition eqs_ok_def:
  eqs_ok eqs ⇔
    EVERY (λ(n,args,body).
             ∀vs. LENGTH vs = LENGTH args ∧
                  cexp_vars body ⊆ set args ∧
                  code_rel eqs vs [] (subst (ZIP (args,REVERSE (MAP from_cv vs))) body)
                           (compile_to_ce eqs (n,args,body))) eqs
End

Theorem do_uop_from_cv:
  do_uop uop (from_cv a) s = (M_success (from_cv (monop uop a)),s)
Proof
  Cases_on ‘uop’ \\ Cases_on ‘a’
  \\ fs [do_uop_def,monop_def,do_fst_def,do_snd_def,do_ispair_def,st_ex_return_def]
QED

Theorem from_cv_11:
  ∀x y. from_cv x = from_cv y ⇔ x = y
Proof
  Induct \\ Cases_on ‘y’ \\ fs []
QED

Theorem do_binop_from_cv:
  do_binop bop (from_cv a) (from_cv b) s = (M_success (from_cv (binop bop a b)),s)
Proof
  Cases_on ‘bop’ \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ fs []
  \\ fs [binop_def,do_binop_def,do_arith_def,st_ex_return_def,
         SAFEDIV_def,SAFEMOD_def,do_reln_def,cv_T_def,cv_F_def]
  \\ rw [] \\ fs [DIV_EQ_X,do_eq_def,st_ex_return_def,from_cv_11]
  \\ rw []
QED

Theorem exec_thm:
  (∀ck eqs e res env vars e1 s s1.
    compute_eval ck eqs e s = (res,s1) ∧
    cexp_vars e = {} ∧ eqs_ok eqs ∧
    code_rel eqs env vars e e1 ⇒
    ∃res1.
      exec (build_funs eqs) env ck e1 s = (res1,s1) ∧
      res = from_res from_cv res1) ∧
  (∀ck eqs e res env vars e1 s s1 acc.
    compute_eval_list ck eqs e s = (res,s1) ∧
    EVERY (λe. cexp_vars e = {}) e ∧ eqs_ok eqs ∧
    LIST_REL (code_rel eqs env vars) e e1 ⇒
    ∃res1.
      exec_list (build_funs eqs) env ck e1 acc s = (res1,s1) ∧
      from_res (λxs. REVERSE xs ++ MAP from_cv acc) res = from_res (MAP from_cv) res1)
Proof
  ho_match_mp_tac compute_eval_ind \\ rpt strip_tac
  >~ [‘Var’] >- fs []
  >~ [‘Num’] >-
   (gvs [Once code_rel_cases]
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup])
  >~ [‘Pair x y’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs []
    \\ Cases_on ‘res1'’ \\ gvs [])
  >~ [‘If x y z’] >-
   (gvs [cexp_consts_ok_def]
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [AllCaseEqs()]
    \\ pop_assum mp_tac \\ simp [Once code_rel_cases] \\ rw []
    \\ first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def]
    \\ Cases_on ‘res1’ \\ gvs []
    \\ Cases_on ‘a’ \\ gvs []
    \\ TRY (first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def])
    \\ Cases_on ‘n’ \\ gvs []
    \\ first_x_assum drule_all \\ strip_tac \\ fs [exec_def,st_ex_bind_def])
  >~ [‘Let s e1 e2’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac
    \\ Cases_on ‘ck = 0’ \\ gvs [compute_eval_def,exec_def]
    \\ gvs [raise_Failure_def,exec_def,st_ex_bind_def]
    \\ gvs [AllCaseEqs(),PULL_EXISTS]
    \\ first_x_assum drule_all \\ gvs [] \\ strip_tac \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs []
    \\ first_x_assum drule
    \\ disch_then irule
    \\ DEP_REWRITE_TAC [compute_evalProofTheory.closed_subst]
    \\ fs [cexp_value_from_cv]
    \\ qexists_tac ‘s::vars’ \\ fs []
    \\ cheat)
  >~ [‘App f xs’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac
    \\ qpat_x_assum ‘cexp_vars (App f xs) = ∅’ mp_tac
    \\ gvs []
    \\ Cases_on ‘ck = 0’ \\ gvs [compute_eval_def]
    \\ gvs [raise_Failure_def,exec_def]
    \\ drule_all option_ALOOKUP
    \\ strip_tac \\ fs [st_ex_bind_def,check_def,st_ex_return_def,st_ex_ignore_bind_def]
    \\ disch_then assume_tac
    \\ ‘EVERY (λe. cexp_vars e = ∅) xs’ by
     (fs [EVERY_MEM,EXTENSION,MEM_MAP,PULL_EXISTS]
      \\ metis_tac [])
    \\ qpat_x_assum ‘_ ∨ _’ kall_tac
    \\ reverse $ gvs [AllCaseEqs()]
    \\ first_x_assum drule_all
    \\ disch_then $ qspec_then ‘[]’ mp_tac \\ strip_tac \\ gvs []
    >- (Cases_on ‘res1’ \\ fs [])
    \\ Cases_on ‘res1’ \\ fs []
    \\ first_x_assum irule
    \\ first_x_assum $ irule_at Any
    \\ qexists_tac ‘[]’ \\ fs []
    \\ DEP_REWRITE_TAC [compute_evalProofTheory.closed_subst]
    \\ rename [‘REVERSE vs = _’]
    \\ imp_res_tac compile_eval_list_length \\ fs [MAP_ZIP,MEM_ZIP,PULL_EXISTS]
    \\ gvs [SWAP_REVERSE_SYM,sub_def,build_funs_def,EL_MAP]
    \\ simp [EVERY_MEM,MEM_MAP,PULL_EXISTS,cexp_value_from_cv]
    \\ gvs [eqs_ok_def,EVERY_EL]
    \\ last_x_assum drule \\ fs []
    \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
  >~ [‘Uop’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs [do_uop_from_cv])
  >~ [‘Binop’] >-
   (pop_assum mp_tac
    \\ simp [Once code_rel_cases] \\ strip_tac \\ gvs []
    \\ gvs [compute_eval_def,st_ex_return_def,exec_def,from_cv_def,
            LESS_LENGTH_env_lookup,compute_eval_from_cv,st_ex_bind_def]
    \\ gvs [cexp_consts_ok_def]
    \\ gvs [AllCaseEqs()]
    \\ rpt $ first_x_assum drule_all
    \\ rw [] \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs [do_binop_from_cv]
    \\ Cases_on ‘res1'’ \\ gvs [do_binop_from_cv])
  >- (gvs [exec_def,st_ex_return_def,compute_eval_def])
  \\ gvs [compute_eval_def,exec_def]
  \\ fs [Once st_ex_bind_def]
  \\ reverse (gvs [AllCaseEqs()])
  \\ last_x_assum drule_all \\ fs [] \\ strip_tac \\ fs []
  \\ Cases_on ‘res1’ \\ gvs []
  \\ gvs [compute_eval_def,exec_def]
  \\ fs [st_ex_bind_def,st_ex_return_def]
  \\ reverse (gvs [AllCaseEqs()])
  \\ last_x_assum drule_all \\ fs [] \\ strip_tac \\ fs []
  \\ first_x_assum $ qspec_then ‘a::acc’ strip_assume_tac
  \\ gvs [] \\ Cases_on ‘res1’ \\ gvs []
QED

val _ = export_theory ();
