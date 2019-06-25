(*
  This compiler phase reorders patterns in pattern matches to improve
  code quality.
*)
open preamble flatLangTheory

val _ = new_theory"flat_reorder_match";

val is_const_con_def = Define`
  (is_const_con (Pcon (SOME tag) plist) = (plist = [])) /\
  (is_const_con _  = F)`

val isPvar_def = Define`
  (isPvar (Pvar _) = T) /\
  (isPvar Pany = T) /\
  isPvar _ = F`

val isPcon_def = Define`
  (isPcon (Pcon (SOME _) _) = T) /\
  isPcon _ = F`

val same_con_def = Define`
  (same_con (Pcon (SOME (t,_)) []) (Pcon (SOME (t',_)) []) ⇔ t = t') ∧
  (same_con _ _ ⇔ F)`;

val _ = export_rewrites ["isPvar_def","isPcon_def", "is_const_con_def", "same_con_def"]

val const_cons_sep_def=Define `
  (const_cons_sep [] a const_cons = (const_cons,a) ) /\
  (const_cons_sep (b::c) a const_cons=
      if (isPvar (FST b)) then
          (const_cons,(b::a))
      else if (is_const_con (FST b)) then
              if EXISTS (same_con (FST b) o FST) const_cons then
                   const_cons_sep c a const_cons
              else const_cons_sep c a (b::const_cons)
      else if isPcon (FST b) then
          const_cons_sep c (b::a) const_cons
      else (const_cons, REVERSE (b::c)++a))`

val const_cons_fst_def = Define`
    const_cons_fst pes =
        let (const_cons, a) = const_cons_sep pes [] []
        in const_cons ++ REVERSE a`

val const_cons_sep_MEM= Q.store_thm("const_cons_sep_MEM",
  `! y z. ¬ (MEM x y ) /\ ¬ (MEM x z) /\
          MEM x ((\(a,b). a ++ REVERSE b) (const_cons_sep pes y z)) ==> MEM x pes`,
  Induct_on `pes`
  \\ rw [const_cons_sep_def] \\ METIS_TAC [MEM])

Theorem const_cons_fst_MEM:
   MEM x (const_cons_fst pes) ==> MEM x pes
Proof
  rw [const_cons_fst_def]
  \\ METIS_TAC [MEM, const_cons_sep_MEM]
QED

(*
 example:
 n.b. the constant constructors come in reverse order
 to fix this, const_cons_fst could REVERSE the const_cons accumulator
EVAL ``
const_cons_fst [
  (Pcon 1 [Pvar "x"], e1);
  (Pcon 3 [], e3);
  (Pvar "z", ez);
  (Pcon 2 [Pvar "y"], e2);
  (Pcon 4 [], e4)]``;
*)

val compile_def = tDefine "compile" `
    (compile [] = []) /\
    (compile [Raise t e] = [Raise t (HD (compile [e]))]) /\
    (compile [Handle t e pes] =  [Handle t (HD (compile [e])) (MAP (λ(p,e). (p,HD (compile [e]))) (const_cons_fst pes))]) /\
    (compile [Lit t l] = [Lit t l]) /\
    (compile [Con t n es] = [Con t n (compile es)] ) /\
    (compile [Var_local t v] = [Var_local t v]) /\
    (compile [Fun t v e] = [Fun t v (HD (compile [e]))]) /\
    (compile [App t op es] = [App t op (compile es)]) /\
    (compile [If t e1 e2 e3] = [If t (HD (compile [e1])) (HD (compile [e2])) (HD (compile [e3]))]) ∧
    (compile [Mat t e pes] =  [Mat t (HD (compile [e])) (MAP (λ(p,e). (p,HD (compile [e]))) (const_cons_fst pes))]) /\
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
     \\ imp_res_tac const_cons_fst_MEM
     \\ last_x_assum kall_tac
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

val compile_decs_def = Define `
  (compile_decs [] = []) /\
  (compile_decs (d::ds) =
    case d of
      Dlet e => Dlet (HD (compile [e]))::compile_decs ds
    | _ => d::compile_decs ds)`;

val () = export_theory();
