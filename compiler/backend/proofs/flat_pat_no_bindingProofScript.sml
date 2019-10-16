(*
  Correctness proof for flat_pat_no_binding

  .. a compile phase that adds let bindings to simplify pattern matches,
  so that pattern matches can compile into If expressions. This phase ensures:
  - patterns add no bindings
    i.e. case x of [v] => ..   compiles to   case x of [_] => let v = .. in ..
  - pattern matches always match on a variable
    i.e. case f x of ..   compiles to   let v = f x in case v of ...
  - Handle expressions always match the universal pattern
    i.e. (f handle ..   compiles to   f handle v => case v of ..)
*)

open preamble
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     flatLangTheory flatSemTheory flatPropsTheory backendPropsTheory
     pattern_top_levelTheory

val _ = new_theory "flat_pat_no_bindingProof"

val _ = set_grammar_ancestry ["misc","ffi","bag","flatProps",
                              (*"flat_pat_no_binding",*)
                              "backendProps","backend_common",
                              "pattern_top_level"];

val _ = Datatype `config =
  <| pat_heuristic : pattern_matching$branch list -> num ;
    type_map : (num # num) list spt |>`;

val sum_string_ords_def = tDefine "sum_string_ords" `
  sum_string_ords i str = if i < LENGTH str
  then ORD (EL i str) + sum_string_ords (i + 1) str
  else 0`
  (WF_REL_TAC `measure (\(i, str). LENGTH str - i)`);

Theorem sum_string_ords_eq:
  sum_string_ords i str = FOLDR (\c i. i + ORD c) 0 (DROP i str)
Proof
  measureInduct_on `(\i. LENGTH str - i) i`
  \\ simp [Once sum_string_ords_def]
  \\ rw [rich_listTheory.DROP_EL_CONS, listTheory.DROP_LENGTH_TOO_LONG]
QED

val dec_name_to_num_def = Define `
  dec_name_to_num name = if LENGTH name < 2 then 0
    else if EL 0 name = #"." /\ EL 1 name = #"."
    then sum_string_ords 2 name else 0`;

val enc_num_to_name_def = Define `
  enc_num_to_name i xs = if i < 200 then #"." :: #"." :: CHR i :: xs
    else enc_num_to_name (i - 200) (CHR 200 :: xs)`;

Theorem dec_enc:
  !xs. dec_name_to_num (enc_num_to_name i xs) = i + FOLDR (\c i. i + ORD c) 0 xs
Proof
  measureInduct_on `I i`
  \\ simp [Once enc_num_to_name_def]
  \\ CASE_TAC \\ simp [dec_name_to_num_def, sum_string_ords_eq]
QED

Theorem enc_num_to_name_inj:
  (enc_num_to_name i [] = enc_num_to_name j []) = (i = j)
Proof
  metis_tac [dec_enc |> Q.SPEC `[]` |> SIMP_RULE list_ss []]
QED

Theorem env_is_v_fold:
  <| v := env.v |> = env
Proof
  simp [environment_component_equality]
QED

(* lists and lookups *)

Theorem LIST_REL_ALOOKUP_OPTREL:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==>
    FST x = FST y /\ R2 (SND x) (SND y))
  ==> OPTREL R2 (ALOOKUP xs v) (ALOOKUP ys v)
Proof
  Induct \\ rpt (Cases ORELSE gen_tac)
  \\ simp [optionTheory.OPTREL_def]
  \\ qmatch_goalsub_abbrev_tac `ALOOKUP (pair :: _)`
  \\ Cases_on `pair`
  \\ simp []
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ impl_tac >- metis_tac []
  \\ simp []
  \\ strip_tac
  \\ first_x_assum drule
  \\ rw []
  \\ fs [optionTheory.OPTREL_def]
QED

Theorem LIST_REL_ALOOKUP:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==> x = y)
  ==> ALOOKUP xs v = ALOOKUP ys v
Proof
  REWRITE_TAC [GSYM optionTheory.OPTREL_eq]
  \\ rpt strip_tac
  \\ drule_then irule LIST_REL_ALOOKUP_OPTREL
  \\ metis_tac []
QED

Theorem LIST_REL_FILTER_MONO:
  !xs ys. LIST_REL R (FILTER P1 xs) (FILTER P2 ys) /\
  (!x. MEM x xs /\ P3 x ==> P1 x) /\
  (!y. MEM y ys /\ P4 y ==> P2 y) /\
  (!x y. MEM x xs /\ MEM y ys /\ R x y ==> P3 x = P4 y)
  ==> LIST_REL R (FILTER P3 xs) (FILTER P4 ys)
Proof
  Induct
  >- (
    simp [FILTER_EQ_NIL, EVERY_MEM]
    \\ metis_tac []
  )
  \\ gen_tac
  \\ simp []
  \\ reverse CASE_TAC
  >- (
    CASE_TAC
    >- metis_tac []
    \\ rw []
  )
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [FILTER_EQ_CONS]
  \\ rename [`_ = ys_pre ++ [y] ++ ys_post`]
  \\ rveq \\ fs []
  \\ fs [FILTER_APPEND]
  \\ first_x_assum drule
  \\ simp []
  \\ disch_tac
  \\ `FILTER P4 ys_pre = []` by (fs [FILTER_EQ_NIL, EVERY_MEM] \\ metis_tac [])
  \\ rw []
  \\ metis_tac []
QED

Theorem COND_false:
  ~ P ==> ((if P then x else y) = y)
Proof
  simp []
QED

Theorem COND_true:
  P ==> ((if P then x else y) = x)
Proof
  simp []
QED

Theorem FILTER_EQ_MONO = LIST_REL_FILTER_MONO
  |> Q.GEN `R` |> Q.ISPEC `(=)` |> REWRITE_RULE [LIST_REL_eq]

Theorem FILTER_EQ_MONO_TRANS = FILTER_EQ_MONO
  |> Q.GEN `P2` |> Q.SPEC `\x. T`
  |> Q.GEN `P4` |> Q.SPEC `P3`
  |> REWRITE_RULE [FILTER_T]

Theorem FILTER_EQ_ALOOKUP_EQ:
  !xs ys. FILTER P xs = ys /\ (!z. P (x, z)) ==>
  ALOOKUP xs x = ALOOKUP ys x
Proof
  Induct \\ simp []
  \\ Cases
  \\ rw []
  \\ fs []
QED

Theorem ALOOKUP_FILTER_EQ = FILTER_EQ_ALOOKUP_EQ |> SIMP_RULE bool_ss []
  |> GSYM;

Theorem MEM_enumerate_EL:
  !xs i x. MEM x (enumerate i xs) = (?j. j < LENGTH xs /\ x = (i + j, EL j xs))
Proof
  Induct \\ rw [miscTheory.enumerate_def]
  \\ simp [indexedListsTheory.LT_SUC]
  \\ EQ_TAC \\ rw []
  \\ simp [EL_CONS, ADD1]
  \\ simp [GSYM ADD1]
  \\ qexists_tac `0` \\ simp []
QED

Theorem ALL_DISTINCT_enumerate:
  !xs i. ALL_DISTINCT (enumerate i xs)
Proof
  Induct \\ rw [miscTheory.enumerate_def, MEM_enumerate_EL]
QED

Theorem LE_LT_ADD_MONO_NUM:
  a <= b /\ c < d ==> a + c < b + (d : num)
Proof
  simp []
QED

Definition BAG_SUM_DEF:
  BAG_SUM b = BAG_GEN_SUM b 0
End

Theorem BAG_SUM:
  BAG_SUM {||} = 0 /\
  (!b x. FINITE_BAG b ==> BAG_SUM (BAG_INSERT x b) = x + BAG_SUM b)
Proof
  simp [BAG_SUM_DEF, BAG_GEN_SUM_EMPTY]
  \\ simp [GSYM PULL_FORALL]
  \\ simp [BAG_GEN_SUM_TAILREC]
  \\ Induct
  \\ simp [BAG_GEN_SUM_EMPTY]
  \\ rpt strip_tac
  \\ first_x_assum (assume_tac o Q.GEN `y` o Q.SPEC `e + y`)
  \\ simp [BAG_GEN_SUM_TAILREC]
QED

Theorem SUM_EQ_BAG_SUM:
  SUM xs = BAG_SUM (LIST_TO_BAG xs)
Proof
  Induct_on `xs`
  \\ simp [BAG_SUM]
QED

Theorem LENGTH_EQ_SUM:
  LENGTH xs = SUM (MAP (K 1) xs)
Proof
  Induct_on `xs` \\ simp []
QED

Theorem SUM_MAP_FILTER_LE_TRANS:
  !xs N. SUM (MAP f xs) <= N ==> SUM (MAP f (FILTER P xs)) <= N
Proof
  Induct \\ simp []
  \\ rw []
  \\ first_x_assum (qspec_then `N - f h` assume_tac)
  \\ fs []
QED

Theorem MAPi_eq_MAP:
  MAPi (\n x. f x) xs = MAP f xs
Proof
  Induct_on `xs` \\ simp [o_DEF]
QED

Theorem MAPi_eq_ZIP_left:
  MAPi (\n x. (x, f n)) xs = ZIP (xs, GENLIST f (LENGTH xs))
Proof
  irule listTheory.LIST_EQ \\ simp [EL_ZIP]
QED

(* compiling the name bindings of a pattern into the RHS expression *)

Theorem pat1_size:
  flatLang$pat1_size xs = LENGTH xs + SUM (MAP pat_size xs)
Proof
  Induct_on `xs` \\ simp [flatLangTheory.pat_size_def]
QED

Definition compile_pat_bindings_def:
  compile_pat_bindings _ _ [] exp = (LN, exp) /\
  compile_pat_bindings t i ((Pany, _, _) :: m) exp =
    compile_pat_bindings t i m exp /\
  compile_pat_bindings t i ((Pvar s, k, x) :: m) exp = (
    let (spt, exp2) = compile_pat_bindings t i m exp in
    (insert k () spt, Let t (SOME s) x exp2)) /\
  compile_pat_bindings t i ((Plit _, _, _) :: m) exp =
    compile_pat_bindings t i m exp /\
  compile_pat_bindings t i ((Pcon stmp ps, k, x) :: m) exp = (
    let j_nms = MAP (\(j, p). let k = i + 1 + j in
        let nm = enc_num_to_name k [] in
        ((j, nm), (p, k, Var_local t nm))) (enumerate 0 ps) in
    let (spt, exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
        (MAP SND j_nms ++ m) exp in
    let j_nms_used = FILTER (\(_, (_, k, _)). IS_SOME (lookup k spt)) j_nms in
    let exp3 = FOLDR (\((j, nm), _) exp.
        flatLang$Let t (SOME nm) (App t (El j) [x]) exp) exp2 j_nms_used in
    let spt2 = if NULL j_nms_used then spt else insert k () spt in
    (spt2, exp3)) /\
  compile_pat_bindings t i ((Pref p, k, x) :: m) exp = (
    let nm = enc_num_to_name (i + 1) [] in
    let (spt, exp2) = compile_pat_bindings t (i + 2)
        ((p, i + 1, Var_local t nm) :: m) exp in
    (insert k () spt, Let t (SOME nm) (App t (El 0) [x]) exp2))
Termination
  WF_REL_TAC `measure (\(t, i, m, exp). SUM (MAP (pat_size o FST) m) + LENGTH m)`
  \\ simp [flatLangTheory.pat_size_def]
  \\ rw [MAP_MAP_o, o_DEF, UNCURRY, SUM_APPEND, pat1_size]
  \\ simp [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP]
End

Definition pure_eval_to_def:
  pure_eval_to s env exp v = (evaluate env s [exp] = (s, Rval [v]))
End

Theorem pmatch_list_Match_IMP_LENGTH:
  !xs ys env env' s. pmatch_list s xs ys env = Match env' ==>
  LENGTH xs = LENGTH ys
Proof
  Induct
  >- (
    Cases \\ simp [flatSemTheory.pmatch_def]
  )
  >- (
    gen_tac \\ Cases \\ simp [flatSemTheory.pmatch_def]
    \\ simp [CaseEq "match_result"]
    \\ metis_tac []
  )
QED

Theorem pmatch_list_append_Match_exists:
  (pmatch_list s (xs ++ ys) vs pre_bindings = Match bindings) =
  (?vs1 vs2 bindings1. vs = vs1 ++ vs2 /\
  pmatch_list s xs vs1 pre_bindings = Match bindings1 /\
  pmatch_list s ys vs2 bindings1 = Match bindings)
Proof
  Cases_on `LENGTH vs <> LENGTH xs + LENGTH ys`
  >- (
    EQ_TAC \\ rw []
    \\ imp_res_tac pmatch_list_Match_IMP_LENGTH
    \\ fs []
  )
  \\ fs []
  \\ qspecl_then [`xs`, `TAKE (LENGTH xs) vs`, `ys`, `DROP (LENGTH xs) vs`,
        `s`, `pre_bindings`]
    mp_tac flatPropsTheory.pmatch_list_append
  \\ rw []
  \\ simp [CaseEq "match_result"]
  \\ EQ_TAC \\ rw []
  \\ imp_res_tac pmatch_list_Match_IMP_LENGTH
  \\ simp [TAKE_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
  \\ simp []
QED

Theorem pmatch_list_eq_append:
  LENGTH vs1 = LENGTH ps1 ==>
  (case pmatch_list s ps1 vs1 pre_bindings of
      No_match => (case pmatch_list s ps2 vs2 pre_bindings
        of Match_type_error => Match_type_error
        | _ => No_match)
    | Match_type_error => Match_type_error
    | Match bindings => pmatch_list s ps2 vs2 bindings) =
  pmatch_list s (ps1 ++ ps2) (vs1 ++ vs2) pre_bindings
Proof
  simp [pmatch_list_append, TAKE_APPEND, DROP_APPEND]
  \\ simp [TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG]
QED

Definition ALOOKUP_rel_def:
  ALOOKUP_rel P R env1 env2 =
  (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))
End

Theorem ALOOKUP_rel_empty:
  ALOOKUP_rel P R [] []
Proof
  simp [ALOOKUP_rel_def, OPTREL_def]
QED

Theorem ALOOKUP_rel_cons_false:
  (~ P x ==> ALOOKUP_rel P R ((x, y) :: env1) env2 = ALOOKUP_rel P R env1 env2)
  /\
  (~ P x ==> ALOOKUP_rel P R env1 ((x, y) :: env2) = ALOOKUP_rel P R env1 env2)
Proof
  simp [ALOOKUP_rel_def]
  \\ metis_tac [COND_CLAUSES]
QED

Theorem ALOOKUP_rel_APPEND_L_false:
  EVERY ((~) o P o FST) xs ==>
  ALOOKUP_rel P R (xs ++ ys) zs =
  ALOOKUP_rel P R ys zs
Proof
  rw [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ EQ_TAC \\ rw []
  \\ first_x_assum drule
  \\ CASE_TAC \\ simp []
  \\ drule ALOOKUP_MEM
  \\ fs [EVERY_MEM, FORALL_PROD]
  \\ metis_tac []
QED

Theorem ALOOKUP_rel_refl:
  (!x y. P x /\ MEM (x, y) xs ==> R y y) ==> ALOOKUP_rel P R xs xs
Proof
  rw [ALOOKUP_rel_def]
  \\ Cases_on `ALOOKUP xs x`
  \\ simp [OPTREL_def]
  \\ metis_tac [ALOOKUP_MEM]
QED

Theorem ALOOKUP_rel_cons:
  (P x ==> R y z) /\ ALOOKUP_rel P R ys zs ==>
  ALOOKUP_rel P R ((x, y) :: ys) ((x, z) :: zs)
Proof
  rw [ALOOKUP_rel_def] \\ rw [] \\ simp [OPTREL_def]
QED

Theorem ALOOKUP_rel_mono:
  ALOOKUP_rel P R xs ys /\
  (!x y z. P' x ==> P x) /\
  (!x y z. P' x /\ R y z ==> R' y z) ==>
  ALOOKUP_rel P' R' xs ys
Proof
  rw [ALOOKUP_rel_def]
  \\ fs [OPTREL_def]
  \\ metis_tac []
QED

Theorem ALOOKUP_rel_mono_rel:
  (!y z. R y z ==> R' y z) ==>
  ALOOKUP_rel P R xs ys ==>
  ALOOKUP_rel P R' xs ys
Proof
  metis_tac [ALOOKUP_rel_mono]
QED

Theorem ALOOKUP_rel_append_suff:
  ALOOKUP_rel P R xs1 xs3 /\ ALOOKUP_rel P R xs2 xs4 ==>
  ALOOKUP_rel P R (xs1 ++ xs2) (xs3 ++ xs4)
Proof
  rw [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ res_tac
  \\ EVERY_CASE_TAC
  \\ fs [OPTREL_def]
QED

Theorem ALOOKUP_rel_EQ_ALOOKUP:
  ALOOKUP_rel P (=) xs ys /\ P x ==>
  ALOOKUP xs x = ALOOKUP ys x
Proof
  simp [ALOOKUP_rel_def]
QED

Theorem ALOOKUP_rel_eq_fst:
  !xs ys.
  LIST_REL (\x y. FST x = FST y /\ (P (FST x) ==> R (SND x) (SND y))) xs ys ==>
  ALOOKUP_rel P R xs ys
Proof
  Induct \\ rpt Cases
  \\ fs [ALOOKUP_rel_def, OPTREL_def]
  \\ Cases_on `h`
  \\ rw []
  \\ rw []
QED

Theorem pat_bindings_evaluate_FOLDR_lemma1:
  !xs.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
    evaluate env2 s [g x] = (s, Rval [rv])))
  ==>
  !env2.
  ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
  evaluate env2 s
    [FOLDR (λx exp. flatLang$Let t (f x) (g x) exp) exp xs] =
  evaluate (env2 with v := MAP (λx. (THE (f x),
        case evaluate env s [g x] of (_, Rval rv) => HD rv)) (REVERSE xs)
             ++ env2.v) s [exp]
Proof
  Induct \\ simp [env_is_v_fold]
  \\ rw []
  \\ simp [evaluate_def]
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM, IS_SOME_EXISTS]
  \\ rfs []
  \\ simp [libTheory.opt_bind_def, ALOOKUP_rel_cons_false]
  \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
  \\ simp [ALOOKUP_rel_refl]
QED

Theorem pat_bindings_evaluate_FOLDR_lemma:
  !new_names.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
    evaluate env2 s [g x] = (s, Rval [rv])))
  ==>
  evaluate env s
    [FOLDR (λx exp. flatLang$Let t (f x) (g x) exp) exp xs] =
  evaluate (env with v := MAP (λx. (THE (f x),
        case evaluate env s [g x] of (_, Rval rv) => HD rv)) (REVERSE xs)
             ++ env.v) s [exp]
Proof
  rw []
  \\ DEP_REWRITE_TAC [pat_bindings_evaluate_FOLDR_lemma1]
  \\ simp [ALOOKUP_rel_refl]
QED

Definition pmatch_stamps_ok_def:
  pmatch_stamps_ok s (SOME n) (SOME n') ps vs =
    (s.check_ctor ==> (n, LENGTH ps) ∈ s.c /\ ctor_same_type (SOME n) (SOME n'))
  /\
  pmatch_stamps_ok s NONE NONE ps vs = (s.check_ctor ∧ LENGTH ps = LENGTH vs)
  /\
  pmatch_stamps_ok s _ _ ps vs = F
End

(* stick together the two constructor cases for pmatch *)
Theorem pmatch_con_case_opt:
  flatSem$pmatch s (Pcon stmp ps) (Conv stmp' vs) bindings =
  if ~ pmatch_stamps_ok s stmp stmp' ps vs
  then Match_type_error
  else if LENGTH ps = LENGTH vs /\ OPTION_MAP FST stmp = OPTION_MAP FST stmp'
  then pmatch_list s ps vs bindings
  else No_match
Proof
  Cases_on `THE stmp` \\ Cases_on `THE stmp'`
  \\ Cases_on `stmp` \\ Cases_on `stmp'`
  \\ simp [flatSemTheory.pmatch_def, pmatch_stamps_ok_def]
  \\ rw []
  \\ fs []
  \\ rveq \\ fs []
  \\ rfs [same_ctor_def, ctor_same_type_def]
QED

Definition store_v_vs_def[simp]:
  store_v_vs (Varray vs) = vs /\
  store_v_vs (Refv v) = [v] /\
  store_v_vs (W8array xs) = []
End

Definition result_vs_def[simp]:
  result_vs (Rval xs) = xs /\
  result_vs (Rerr (Rraise x)) = [x] /\
  result_vs (Rerr (Rabort y)) = []
End

Theorem v1_size:
  v1_size xs = LENGTH xs + SUM (MAP v2_size xs)
Proof
  Induct_on `xs` \\ simp [v_size_def]
QED

Theorem v3_size:
  v3_size xs = LENGTH xs + SUM (MAP v_size xs)
Proof
  Induct_on `xs` \\ simp [v_size_def]
QED

Definition v_cons_in_c_def1:
  v_cons_in_c c (Conv stmp xs) = (
    (case stmp of SOME con_stmp => (con_stmp, LENGTH xs) ∈ c
        | NONE => T) /\
    EVERY (v_cons_in_c c) xs) /\
  v_cons_in_c c (Vectorv vs) = EVERY (v_cons_in_c c) vs /\
  v_cons_in_c c (Closure env n exp) = EVERY (\x. v_cons_in_c c (SND x)) env /\
  v_cons_in_c c (Recclosure env funs n) = EVERY (\x. v_cons_in_c c (SND x)) env /\
  v_cons_in_c c other = T
Termination
  WF_REL_TAC `measure (v_size o SND)`
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND, v3_size, v1_size, v_size_def]
End

Theorem v_cons_in_c_def[simp] = v_cons_in_c_def1
    |> CONV_RULE (DEPTH_CONV ETA_CONV)
    |> SIMP_RULE bool_ss [prove (``(λx. v_cons_in_c c (SND x))
        = (v_cons_in_c c o SND)``, simp [o_DEF])]

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i, with
   new names i < nm < j appearing in the new env, and in *expressions* in
   n_bindings. note *names* in n_bindings/pre_bindings come from the original
   program. also new/old names mix in env, thus the many filters. *)

Theorem compile_pat_bindings_simulation_lemma:
  ! t i n_bindings exp exp2 spt s vs pre_bindings bindings env s2 res vset.
  compile_pat_bindings t i n_bindings exp = (spt, exp2) /\
  pmatch_list s (MAP FST n_bindings) vs pre_bindings = Match bindings /\
  evaluate env s [exp2] = (s2, res) /\
  LIST_REL (\(_, k, v_exp) v. !env2. k ∈ domain spt /\
        ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=) env2.v env.v
        ==>
        pure_eval_to s env2 v_exp v)
    n_bindings vs /\
  EVERY ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
  j < i /\
  ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=) env.v
    (pre_bindings ++ base_vs) /\
  EVERY (\(p, k, _). EVERY (\nm. dec_name_to_num nm < j) (pat_bindings p []) /\
        j < k /\ k < i) n_bindings /\
  EVERY (v_cons_in_c s.c ∘ SND) env.v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (v_cons_in_c s.c) vs
  ==>
  ?env2. evaluate env2 s [exp] = (s2, res) /\
  EVERY (v_cons_in_c s.c ∘ SND) env2.v /\
  ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=) env2.v (bindings ++ base_vs)
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rpt conj_tac
  \\ simp_tac bool_ss [compile_pat_bindings_def, flatSemTheory.pmatch_def,
        PULL_EXISTS, EVERY_DEF, PAIR_EQ, MAP, LIST_REL_NIL, LIST_REL_CONS1,
        LIST_REL_CONS2, FORALL_PROD]
  \\ rpt strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ fs [flatSemTheory.pmatch_def]
  >- (
    metis_tac []
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ last_x_assum (drule_then (drule_then irule))
    \\ simp []
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [pure_eval_to_def, ALOOKUP_rel_refl]
    \\ rw []
    \\ fs [pat_bindings_def]
    \\ last_x_assum (drule_then (drule_then irule))
    \\ simp [libTheory.opt_bind_def]
    \\ simp [ALOOKUP_rel_cons]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD, ALOOKUP_rel_cons_false]
  )
  >- (
    qmatch_asmsub_abbrev_tac `pmatch _ (Plit l) lv`
    \\ Cases_on `lv` \\ fs [flatSemTheory.pmatch_def]
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ simp [CaseEq "match_result", bool_case_eq]
    \\ rw []
    \\ metis_tac []
  )
  >- (
    (* Pcon *)
    qmatch_asmsub_abbrev_tac `pmatch _ (Pcon stmp _) con_v`
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ simp [CaseEq "match_result"]
    \\ rw []
    \\ Cases_on `con_v` \\ fs [flatSemTheory.pmatch_def]
    \\ fs [pmatch_con_case_opt, bool_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [MAP_MAP_o |> REWRITE_RULE [o_DEF], UNCURRY, Q.ISPEC `SND` ETA_THM]
    \\ fs [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP]
    \\ qpat_x_assum `evaluate _ _ [FOLDR _ _ _] = _` mp_tac
    \\ simp [ELIM_UNCURRY]
    \\ DEP_REWRITE_TAC [pat_bindings_evaluate_FOLDR_lemma]
    \\ simp []
    \\ conj_tac >- (
      qexists_tac `{x | ~ (dec_name_to_num x < i)}`
      \\ simp [SUBSET_DEF, MEM_FILTER, MEM_MAPi, PULL_EXISTS]
      \\ simp [dec_enc]
      \\ simp [evaluate_def]
      \\ rw [IS_SOME_EXISTS]
      \\ rename [`pmatch_stamps_ok _ _ cstmp _ con_vs`]
      \\ qexists_tac `EL n con_vs`
      \\ rw []
      \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [PULL_EXISTS, NULL_FILTER, MEM_MAPi]
      \\ asm_exists_tac \\ simp []
      \\ simp [pure_eval_to_def]
      \\ disch_then (fn t => DEP_REWRITE_TAC [t])
      \\ simp [do_app_def]
      \\ drule_then irule ALOOKUP_rel_mono
      \\ simp []
    )
    \\ rw []
    \\ fs [Q.ISPEC `Match m` EQ_SYM_EQ]
    \\ last_x_assum irule
    \\ simp [PULL_EXISTS, pmatch_list_append_Match_exists]
    \\ goal_assum (first_assum o mp_then (Pat `pmatch_list _ _ _ _ = _`) mp_tac)
    \\ goal_assum (first_assum o mp_then (Pat `pmatch_list _ _ _ _ = _`) mp_tac)
    \\ goal_assum (first_assum o mp_then (Pat `evaluate _ _ _ = _`) mp_tac)
    \\ simp []
    \\ rpt (conj_tac
    >- (
      fs [pat_bindings_def, pats_bindings_FLAT_MAP, EVERY_FLAT, EVERY_REVERSE]
      \\ fs [EVERY_EL, FORALL_PROD, UNCURRY, EL_MAP]
      \\ rw []
      \\ res_tac
      \\ simp []
    ))
    \\ DEP_REWRITE_TAC [ALOOKUP_rel_APPEND_L_false]
    \\ simp [MAP_APPEND, REVERSE_APPEND, MEM_MAP, MEM_FILTER,
      EVERY_MEM, MEM_MAPi, PULL_EXISTS, dec_enc]
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` (qspec_then `env` mp_tac)
    \\ rpt strip_tac
    >- (
      rw []
      \\ qpat_x_assum `_ ==> pure_eval_to _ _ x _` mp_tac
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [ALOOKUP_rel_refl, pure_eval_to_def, NULL_FILTER]
      \\ simp [MEM_MAPi, PULL_EXISTS]
      \\ asm_exists_tac \\ simp []
      \\ simp [evaluate_def, do_app_def]
      \\ metis_tac [EVERY_EL]
    )
    \\ irule LIST_REL_APPEND_suff
    \\ conj_tac
    >- (
      (* new elements *)
      simp [LIST_REL_EL_EQN, LENGTH_enumerate, EL_enumerate, EL_MAP]
      \\ simp [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ rw []
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc]
      \\ qpat_x_assum `_ ==> pure_eval_to _ _ x _` mp_tac
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [NULL_FILTER, MEM_MAPi, PULL_EXISTS]
      \\ fs [sptreeTheory.domain_lookup]
      \\ asm_exists_tac \\ simp []
      \\ rw [ALOOKUP_rel_refl, pure_eval_to_def]
      \\ simp [do_app_def, option_case_eq]
      \\ simp [ALOOKUP_APPEND, option_case_eq]
      \\ DEP_REWRITE_TAC [GSYM MEM_ALOOKUP |> Q.SPEC `MAP f zs`]
      \\ simp [MEM_MAP, EXISTS_PROD, MEM_FILTER, MEM_MAPi, enc_num_to_name_inj]
      \\ simp [MAP_MAP_o, o_DEF, MAP_REVERSE]
      \\ irule ALL_DISTINCT_MAP_INJ
      \\ simp [MEM_FILTER, FORALL_PROD, MEM_MAPi, enc_num_to_name_inj]
      \\ irule FILTER_ALL_DISTINCT
      \\ simp [MAPi_enumerate_MAP]
      \\ irule ALL_DISTINCT_MAP_INJ
      \\ simp [FORALL_PROD, ALL_DISTINCT_enumerate]
    )
    (* prior env *)
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ simp []
    \\ conj_tac \\ TRY (IF_CASES_TAC \\ simp [] \\ NO_TAC)
    \\ rw [ALOOKUP_rel_def]
    \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
    \\ simp [ALOOKUP_APPEND, option_case_eq, ALOOKUP_NONE, MEM_MAP, FORALL_PROD,
        MEM_FILTER, MEM_MAPi]
    \\ CCONTR_TAC \\ fs []
    \\ fs [dec_enc]
  )
  >- (
    (* Pref *)
    qpat_x_assum `_ = Match _` mp_tac
    \\ qmatch_goalsub_abbrev_tac `pmatch _ (Pref _) ref_v`
    \\ Cases_on `ref_v` \\ simp [flatSemTheory.pmatch_def]
    \\ rw [CaseEq "match_result", option_case_eq, CaseEq "store_v"]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [evaluate_def, pure_eval_to_def, ALOOKUP_rel_refl]
    \\ rw []
    \\ fs [evaluate_def, do_app_def]
    \\ last_x_assum match_mp_tac
    \\ simp [CaseEq "match_result", PULL_EXISTS]
    \\ rpt (CHANGED_TAC (asm_exists_tac \\ simp []))
    \\ fs [libTheory.opt_bind_def, pat_bindings_def]
    \\ simp [ALOOKUP_rel_cons_false, dec_enc]
    \\ rpt conj_tac
    >- (
      rw [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc]
    )
    >- (
      first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
      \\ simp [FORALL_PROD]
      \\ rw []
      \\ first_x_assum irule
      \\ simp []
      \\ rw [ALOOKUP_rel_def]
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc, FILTER_FILTER]
      \\ rw []
      \\ fs [dec_enc]
    )
    >- (
      fs [EVERY_MEM, FORALL_PROD]
      \\ rw [] \\ res_tac \\ simp []
    )
    >- (
      fs [store_lookup_def, Q.ISPEC `st.refs` EVERY_EL]
      \\ first_x_assum drule
      \\ simp []
    )
  )
QED

Definition drop_pat_bindings_def:
  (drop_pat_bindings (flatLang$Pany) = Pany) /\
  (drop_pat_bindings (Pvar _) = Pany) /\
  (drop_pat_bindings (Plit l) = Plit l) /\
  (drop_pat_bindings (Pcon stmp ps) = Pcon stmp (MAP drop_pat_bindings ps)) /\
  (drop_pat_bindings (Pref p) = Pref (drop_pat_bindings p))
Termination
  WF_REL_TAC `measure pat_size`
  \\ rw [pat1_size]
  \\ fs [MEM_SPLIT, SUM_APPEND]
End

val s = ``s:'ffi flatSem$state``;
val s1 = mk_var ("s1", type_of s);
val s2 = mk_var ("s2", type_of s);

Theorem drop_pat_bindings_simulation:
  (! ^s p v pre_bindings.
  pmatch s (drop_pat_bindings p) v [] = (case
    pmatch s p v pre_bindings of Match _ => Match []
      | res => res)) /\
  (! ^s ps vs pre_bindings.
  pmatch_list s (MAP drop_pat_bindings ps) vs [] = (case
    pmatch_list s ps vs pre_bindings of Match _ => Match []
      | res => res))
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind
  \\ simp [flatSemTheory.pmatch_def, drop_pat_bindings_def]
  \\ rw [Q.ISPEC `drop_pat_bindings` ETA_THM]
  \\ rpt (CASE_TAC \\ fs [])
QED

Theorem pmatch_drop_pat_bindings = drop_pat_bindings_simulation
  |> CONJUNCTS |> hd |> Q.SPECL [`s`, `p`, `v`, `[]`]

Definition compile_pat_rhs_def:
  compile_pat_rhs t i v (p, exp) =
  SND (compile_pat_bindings t (i + 1) [(p, i, v)] exp)
End

Definition decode_pos_def:
  decode_pos t v EmptyPos = v /\
  decode_pos t v (Pos i pos) = decode_pos t (App t (El i) [v]) pos
End

Definition decode_test_def:
  decode_test t (TagLenEq tag l) v = App t (TagLenEq tag l) [v] /\
  decode_test t (LitEq lit) v = App t Equality [v; Lit t lit]
End

Definition decode_guard_def:
  decode_guard t v (Not gd) = App t Equality [decode_guard t v gd; Bool t F] /\
  decode_guard t v (Conj gd1 gd2) = If t (decode_guard t v gd1)
    (decode_guard t v gd2) (Bool t F) /\
  decode_guard t v (Disj gd1 gd2) = If t (decode_guard t v gd1) (Bool t T)
    (decode_guard t v gd2) /\
  decode_guard t v (PosTest pos test) = decode_test t test (decode_pos t v pos)
End

Definition decode_dtree_def:
  decode_dtree t br v df (Leaf n) = EL n br /\
  decode_dtree t br v df Fail = df /\
  decode_dtree t br v df TypeFail = Var_local t "impossible-case" /\
  decode_dtree t br v df (pattern_top_level$If guard dt1 dt2) = If t
    (decode_guard t v guard) (decode_dtree t br v df dt1)
    (decode_dtree t br v df dt2)
End

Definition encode_pat_def:
  encode_pat type_map (flatLang$Pany) = pattern_top_level$Any /\
  encode_pat type_map (Plit l) = Lit l /\
  encode_pat type_map (Pvar _) = Any /\
  encode_pat type_map (Pcon stmp ps) = Cons
    (case stmp of NONE => NONE | SOME (i, NONE) => SOME (i, NONE)
        | SOME (i, SOME ty) => SOME (i, lookup ty type_map))
    (MAP (encode_pat type_map) ps) /\
  encode_pat type_map (Pref p) = Ref (encode_pat type_map p)
Termination
  WF_REL_TAC `measure (pat_size o SND)`
  \\ rw [pat1_size]
  \\ fs [MEM_SPLIT, SUM_APPEND]
End

Definition compile_pats_def:
  compile_pats cfg t i v default_x ps =
  let pats = MAPi (\j (p, _). (encode_pat cfg.type_map p, j)) ps in
  let branches = MAP (compile_pat_rhs t i v) ps in
  let dt = pattern_top_level$top_level_pat_compile cfg.pat_heuristic pats in
  decode_dtree t branches v default_x dt
End

Definition max_dec_name_def:
  max_dec_name [] = 0 /\
  max_dec_name (nm :: nms) = MAX (dec_name_to_num nm) (max_dec_name nms)
End

Definition compile_exps_def:
  (compile_exps cfg [] = (0, [])) /\
  (compile_exps cfg (x::y::xs) =
    let (i, cx) = compile_exps cfg [x] in
    let (j, cy) = compile_exps cfg (y::xs) in
    (MAX i j, HD cx :: cy)) /\
  (compile_exps cfg [Var_local t vid] =
    (dec_name_to_num vid, [Var_local t vid])) /\
  (compile_exps cfg [Raise t x] =
    let (i, xs) = compile_exps cfg [x] in
    (i, [Raise t (HD xs)])) /\
  (compile_exps cfg [Handle t x ps] =
    let (i, xs) = compile_exps cfg [x] in
    let (j, ps2) = compile_match cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k [] in
    let v = Var_local t nm in
    let r = Raise t v in
    let exp = compile_pats cfg t k v r ps2 in
    (k, [Handle t (HD xs) [(Pvar nm, exp)]])) /\
  (compile_exps cfg [Con t ts xs] =
    let (i, ys) = compile_exps cfg (REVERSE xs) in
    (i, [Con t ts (REVERSE ys)])) /\
  (compile_exps cfg [Fun t vs x] =
    let (i, xs) = compile_exps cfg [x] in
    (i, [Fun t vs (HD xs)])) /\
  (compile_exps cfg [App t op xs] =
    let (i, ys) = compile_exps cfg (REVERSE xs) in
    (i, [App t op (REVERSE ys)])) /\
  (compile_exps cfg [Mat t x ps] =
    let (i, xs) = compile_exps cfg [x] in
    let (j, ps2) = compile_match cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k [] in
    let v = Var_local t nm in
    let r = Raise t (Con t (SOME (bind_tag, NONE)) []) in
    let exp = compile_pats cfg t k v r ps2 in
    (k, [Let t (SOME nm) (HD xs) exp])) /\
  (compile_exps cfg [Let t v x1 x2] =
    let (i, xs1) = compile_exps cfg [x1] in
    let (j, xs2) = compile_exps cfg [x2] in
    let k = (case v of NONE => 0 | SOME vid => dec_name_to_num vid) in
    (MAX i (MAX j k), [Let t v (HD xs1) (HD xs2)])) /\
  (compile_exps cfg [Letrec t fs x] =
    let ys      = MAP (\(a,b,c). (a, b, compile_exps cfg [c])) fs in
    let (i, xs) = compile_exps cfg [x] in
    let j       = list_max (MAP (\(_,_,(j,_)). j) ys) in
    let fs1     = MAP (\(a,b,(_,xs)). (a,b,HD xs)) ys in
    (MAX i j, [Letrec t fs1 (HD xs)])) /\
  (compile_exps cfg [If t x1 x2 x3] =
    let (i, xs1) = compile_exps cfg [x1] in
    let (j, xs2) = compile_exps cfg [x2] in
    let (k, xs3) = compile_exps cfg [x3] in
    (MAX i (MAX j k), [If t (HD xs1) (HD xs2) (HD xs3)])) /\
  (compile_exps cfg [expr] = (0, [expr])) /\
  (compile_match cfg [] = (0, [])) /\
  (compile_match cfg ((p, x)::ps) =
    let (i, xs) = compile_exps cfg [x] in
    let j = max_dec_name (pat_bindings p []) in
    let (k, ps2) = compile_match cfg ps in
    (MAX i (MAX j k), ((p, HD xs) :: ps2)))
Termination
  WF_REL_TAC `measure (\x. case x of INL (_, xs) => exp6_size xs
    | INR (_, ps) => exp3_size ps)`
  \\ rw [flatLangTheory.exp_size_def]
  \\ imp_res_tac flatLangTheory.exp_size_MEM
  \\ fs []
End

Definition compile_decs_def:
  compile_decs cfg [] = [] /\
  (compile_decs cfg ((Dlet e)::xs) =
    let (_, ys) = compile_exps cfg [e] in
    (Dlet (HD ys) :: compile_decs cfg xs)) /\
  (compile_decs cfg ((Dtype n s)::xs) = Dtype n s :: compile_decs cfg xs) /\
  (compile_decs cfg ((Dexn n n2)::xs) = Dexn n n2 :: compile_decs cfg xs)
End

Theorem LENGTH_compile_exps_IMP:
  (!cfg xs i ys. compile_exps cfg xs = (i, ys) ==> LENGTH ys = LENGTH xs) /\
  (!cfg ps i ps2. compile_match cfg ps = (i, ps2) ==> LENGTH ps2 = LENGTH ps)
Proof
  ho_match_mp_tac compile_exps_ind \\ rw [compile_exps_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Theorem LENGTH_SND_compile_exps:
  LENGTH (SND (compile_exps cfg xs)) = LENGTH xs /\
  LENGTH (SND (compile_match cfg ps)) = LENGTH ps
Proof
  Cases_on `compile_exps cfg xs` \\ Cases_on `compile_match cfg ps`
  \\ imp_res_tac LENGTH_compile_exps_IMP \\ simp []
QED

val _ = IndDefLib.add_mono_thm ALOOKUP_rel_mono_rel;

Inductive v_rel:
  (!v v'. simple_basic_val_rel v v' /\
    LIST_REL (v_rel cfg) (v_container_xs v) (v_container_xs v') ==>
    v_rel cfg v v') /\
  (!N vs1 n x vs2.
     ALOOKUP_rel (\x. dec_name_to_num x < N) (v_rel cfg) vs1 vs2 /\
     FST (compile_exps cfg [x]) < N ==>
     v_rel cfg (Closure vs1 n x)
       (Closure vs2 n (HD (SND (compile_exps cfg [x]))))) /\
  (!N vs1 fs x vs2.
     ALOOKUP_rel (\x. dec_name_to_num x < N) (v_rel cfg) vs1 vs2 /\
     EVERY (\(n,m,e). FST (compile_exps cfg [e]) < N) fs ==>
     v_rel cfg (Recclosure vs1 fs x) (Recclosure vs2
         (MAP (\(n,m,e). (n,m,HD (SND (compile_exps cfg [e])))) fs) x))
End

Theorem v_rel_l_cases = TypeBase.nchotomy_of ``: v``
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (curry mk_comb ``v_rel cfg``)
  |> map (fn t => mk_comb (t, ``v2 : v``))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

val add_q = augment_srw_ss [simpLib.named_rewrites "pair_rel_thm"
  [quotient_pairTheory.PAIR_REL_THM]];

Definition state_rel_def:
  state_rel cfg (s:'ffi flatSem$state) (t:'ffi flatSem$state) <=>
    t.clock = s.clock /\
    LIST_REL (sv_rel (v_rel cfg)) s.refs t.refs /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL (v_rel cfg)) s.globals t.globals /\
    t.c = s.c /\
    s.check_ctor /\
    t.check_ctor
End

Theorem state_rel_initial_state:
  state_rel cfg (initial_state ffi k T T) (initial_state ffi k T T)
Proof
  fs [state_rel_def, initial_state_def]
QED

Triviality state_rel_IMP_check_ctor:
  state_rel cfg s t ==> s.check_ctor /\ t.check_ctor
Proof
  fs [state_rel_def]
QED

Triviality state_rel_IMP_clock:
  state_rel cfg s t ==> t.clock = s.clock
Proof
  fs [state_rel_def]
QED

Triviality state_rel_IMP_c:
  state_rel cfg s t ==> t.c = s.c
Proof
  fs [state_rel_def]
QED

Overload nv_rel[local] =
  ``\cfg N. ALOOKUP_rel (\x. dec_name_to_num x < N) (v_rel cfg)``

Definition env_rel_def:
  env_rel cfg N env1 env2 = nv_rel cfg N env1.v env2.v
End

(* fixme does everyone define match_rel themselves the same way? *)
val match_rel_def = Define `
  (match_rel cfg N (Match env1) (Match env2) <=> nv_rel cfg N env1 env2) /\
  (match_rel cfg N No_match No_match <=> T) /\
  (match_rel cfg N Match_type_error Match_type_error <=> T) /\
  (match_rel cfg N _ _ <=> F)`

Theorem match_rel_thms[simp]:
   (match_rel cfg N Match_type_error e <=> e = Match_type_error) /\
   (match_rel cfg N e Match_type_error <=> e = Match_type_error) /\
   (match_rel cfg N No_match e <=> e = No_match) /\
   (match_rel cfg N e No_match <=> e = No_match)
Proof
  Cases_on `e` \\ rw [match_rel_def]
QED

Theorem MAX_ADD_LESS:
  (MAX i j + k < l) = (i + k < l /\ j + k < l)
Proof
  rw [MAX_DEF]
QED

Theorem LESS_MAX_ADD:
  (l < MAX i j + k) = (l < i + k \/ l < j + k)
Proof
  rw [MAX_DEF]
QED

Theorem MAX_ADD_LE:
  (MAX i j + k <= l) = (i + k <= l /\ j + k <= l)
Proof
  rw [MAX_DEF]
QED

Theorem LE_MAX_ADD:
  (l <= MAX i j + k) = (l <= i + k \/ l <= j + k)
Proof
  rw [MAX_DEF]
QED

Theorem env_rel_add_enc:
  N <= i ==>
  env_rel cfg N env1 <|v := (enc_num_to_name i "", x)::vs|> =
  env_rel cfg N env1 <|v := vs|>
Proof
  simp [env_rel_def, ALOOKUP_rel_cons_false, dec_enc]
QED

Theorem env_rel_mono:
  env_rel cfg i env1 env2 /\ j <= i ==>
  env_rel cfg j env1 env2
Proof
  rw [env_rel_def]
  \\ drule_then irule ALOOKUP_rel_mono
  \\ simp [FORALL_PROD]
QED

Theorem env_rel_ALOOKUP:
  env_rel cfg N env1 env2 /\ dec_name_to_num n < N ==>
  OPTREL (v_rel cfg) (ALOOKUP env1.v n) (ALOOKUP env2.v n)
Proof
  rw [env_rel_def, ALOOKUP_rel_def]
QED

Theorem ALOOKUP_MAP_3:
  (!x. MEM x xs ==> FST (f x) = FST x) ==>
  ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x, y))) (ALOOKUP xs x)
Proof
  Induct_on `xs` \\ rw []
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h`
  \\ Cases_on `h`
  \\ rw []
  \\ fs []
QED

Theorem ALOOKUP_rel_MAP_same:
  (!x. MEM x xs ==> FST (f x) = FST (g x) /\
    (P (FST (g x)) ==> R (SND (f x)) (SND (g x)))) ==>
  ALOOKUP_rel P R (MAP f xs) (MAP g xs)
Proof
  Induct_on `xs` \\ rw [ALOOKUP_rel_empty]
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h` \\ Cases_on `g h`
  \\ fs [ALOOKUP_rel_cons]
QED

Theorem do_opapp_thm:
  do_opapp vs1 = SOME (nvs1, exp) /\ LIST_REL (v_rel cfg) vs1 vs2
  ==>
  ?i exps nvs2. compile_exps cfg [exp] = (i, exps) /\
  nv_rel cfg (i + 1) nvs1 nvs2 /\ do_opapp vs2 = SOME (nvs2, HD exps)
Proof
  simp [do_opapp_def, pair_case_eq, case_eq_thms, PULL_EXISTS]
  \\ rw []
  \\ fs [v_rel_l_cases]
  \\ rveq \\ fs []
  \\ simp [PAIR_FST_SND_EQ]
  >- (
    irule ALOOKUP_rel_cons
    \\ simp []
    \\ drule_then irule ALOOKUP_rel_mono
    \\ simp []
  )
  \\ fs [PULL_EXISTS, find_recfun_ALOOKUP, ALOOKUP_MAP]
  \\ simp [ALOOKUP_MAP_3, FORALL_PROD]
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ irule ALOOKUP_rel_cons
  \\ simp [build_rec_env_eq_MAP]
  \\ irule ALOOKUP_rel_append_suff
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY]
  \\ conj_tac
  >- (
    irule ALOOKUP_rel_MAP_same
    \\ rw [UNCURRY, v_rel_l_cases]
    \\ asm_exists_tac \\ simp []
  )
  \\ drule_then irule ALOOKUP_rel_mono
  \\ simp []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM]
  \\ res_tac
  \\ fs []
QED

Theorem do_opapp_thm_REVERSE:
  do_opapp (REVERSE vs1) = SOME (nvs1, exp) /\ LIST_REL (v_rel cfg) vs1 vs2
  ==>
  ?i exps nvs2.
  compile_exps cfg [exp] = (i, exps) /\
  nv_rel cfg (i + 1) nvs1 nvs2 /\
  do_opapp (REVERSE vs2) = SOME (nvs2, HD exps)
Proof
  rw []
  \\ drule_then irule do_opapp_thm
  \\ simp []
QED

Theorem pmatch_thm:
  (!(s:'ffi state) p v vs r s1 v1 vs1.
    pmatch s p v vs = r /\
    r <> Match_type_error /\
    state_rel cfg s s1 /\
    v_rel cfg v v1 /\
    nv_rel cfg N vs vs1
    ==> ?r1. pmatch s1 p v1 vs1 = r1 /\ match_rel cfg N r r1) /\
  (!(s:'ffi state) ps v vs r s1 v1 vs1.
    pmatch_list s ps v vs = r /\
    r <> Match_type_error /\
    state_rel cfg s s1 ∧
    LIST_REL (v_rel cfg) v v1 /\
    nv_rel cfg N vs vs1
    ==> ?r1. pmatch_list s1 ps v1 vs1 = r1 /\ match_rel cfg N r r1)
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind
  \\ simp [flatSemTheory.pmatch_def, match_rel_def, v_rel_l_cases]
  \\ rw [match_rel_def]
  \\ imp_res_tac state_rel_IMP_check_ctor
  \\ imp_res_tac state_rel_IMP_c
  \\ fs [flatSemTheory.pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  >- ( irule ALOOKUP_rel_cons \\ simp [] )
  >- (
    fs [store_lookup_def, bool_case_eq, option_case_eq]
    \\ every_case_tac \\ rfs []
    \\ rpt (first_x_assum drule)
    \\ fs [state_rel_def, LIST_REL_EL_EQN]
    \\ rfs []
    \\ rpt (first_x_assum drule)
    \\ simp []
  )
  >- (
    every_case_tac \\ fs []
    \\ rpt (first_x_assum drule \\ rw [])
    \\ TRY (rpt (asm_exists_tac \\ simp []) \\ NO_TAC)
    \\ fs [match_rel_def]
  )
QED

Theorem simple_val_rel_step_isClosure:
  simple_basic_val_rel x y ==> ~ isClosure x /\ ~ isClosure y
Proof
  Cases_on `x` \\ simp [simple_basic_val_rel_def]
  \\ rw [] \\ simp []
QED

Theorem simple_val_rel:
  simple_val_rel (v_rel cfg)
Proof
  simp [simple_val_rel_def, v_rel_cases]
  \\ rw [] \\ simp []
  \\ EQ_TAC \\ rw [] \\ fs []
  \\ metis_tac [simple_val_rel_step_isClosure]
QED

Theorem simple_state_rel:
  simple_state_rel (v_rel cfg) (state_rel cfg)
Proof
  simp [simple_state_rel_def, state_rel_def]
QED

Theorem do_app_thm = MATCH_MP simple_do_app_thm
    (CONJ simple_val_rel simple_state_rel)

Theorem do_app_thm_REVERSE:
  do_app cc s1 op (REVERSE vs1) = SOME (t1, r1) /\
  state_rel cfg s1 s2 /\ LIST_REL (v_rel cfg) vs1 vs2
  ==>
  ?t2 r2. result_rel (v_rel cfg) (v_rel cfg) r1 r2 /\
  state_rel cfg t1 t2 /\ do_app cc s2 op (REVERSE vs2) = SOME (t2, r2)
Proof
  rw []
  \\ drule_then irule do_app_thm
  \\ simp []
QED

Theorem do_if_helper:
  do_if b x y = SOME e /\ v_rel cfg b b' ==>
  ((b' = Boolv T) = (b = Boolv T)) /\ ((b' = Boolv F) = (b = Boolv F))
Proof
  simp [Once v_rel_cases]
  \\ Cases_on `b`
  \\ rw [Boolv_def]
  \\ EQ_TAC \\ rw [] \\ fs []
QED

Theorem list_max_LESS:
  (list_max xs < N) = (0 < N /\ EVERY (\x. x < N) xs)
Proof
  Induct_on `xs`
  \\ simp [list_max_def |> REWRITE_RULE [GSYM MAX_DEF]]
  \\ metis_tac []
QED

Theorem pat_bindings_drop_pat_bindings:
  !p bs. pat_bindings (drop_pat_bindings p) bs = bs
Proof
  ho_match_mp_tac drop_pat_bindings_ind
  \\ simp [drop_pat_bindings_def, pat_bindings_def, ETA_THM]
  \\ simp [pats_bindings_FLAT_MAP, FLAT_EQ_NIL, EVERY_REVERSE, EVERY_MAP]
  \\ simp [EVERY_MEM]
QED

Theorem max_dec_name_LESS_EVERY:
  (max_dec_name ns < N) = (0 < N /\ EVERY (\n. dec_name_to_num n < N) ns)
Proof
  Induct_on `ns` \\ simp [max_dec_name_def]
  \\ metis_tac []
QED

Definition encode_val_def:
  encode_val (Litv l) = Litv l /\
  encode_val (Conv stmp xs) = Term
    (case stmp of NONE => NONE | SOME (i, _) => SOME i)
    (MAP encode_val xs) /\
  encode_val (Loc n) = RefPtr n /\
  encode_val others = Other
Termination
  WF_REL_TAC `measure v_size`
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND, v3_size]
End

Theorem decode_test_simulation:
  dt_test test enc_v = SOME b /\
  pure_eval_to s env x v /\
  enc_v = encode_val v
  ==>
  pure_eval_to s env (decode_test tr test x) (Boolv b)
Proof
  Cases_on `test` \\ Cases_on `v`
  \\ simp [encode_val_def]
  \\ EVERY_CASE_TAC
  \\ rw []
  \\ fs [dt_test_def]
  \\ fs [decode_test_def, pure_eval_to_def, evaluate_def]
  \\ simp [do_app_def, do_eq_def, lit_same_type_sym]
  \\ rw [Boolv_def]
QED

Theorem app_list_pos_LESS:
  !xs i. app_list_pos refs xs (i, pos) = SOME res ==> i < LENGTH xs
Proof
  Induct \\ rw [pattern_refsTheory.app_list_pos_def]
  \\ Cases_on `i`
  \\ rfs [pattern_refsTheory.app_list_pos_def]
QED

Theorem app_pos_Term_IMP:
  !xs n. app_pos refs (Pos n pos) (Term c xs) = SOME y ==>
  n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y
Proof
  Induct_on `xs`
  \\ simp [app_pos_def]
  \\ rw []
  \\ Cases_on `n`
  \\ fs [app_pos_def]
QED

Definition encode_refs_def:
  encode_refs s = FUN_FMAP (\i. encode_val (case EL i s.refs of Refv v => v))
    (count (LENGTH s.refs) ∩ {i | ?v. EL i s.refs = Refv v})
End

Theorem FLOOKUP_encode_refs:
  FLOOKUP (encode_refs s) n = if n < LENGTH s.refs
  then (case EL n s.refs of Refv v => SOME (encode_val v) | _ => NONE)
  else NONE
Proof
  simp [encode_refs_def, FLOOKUP_FUN_FMAP]
  \\ EVERY_CASE_TAC \\ simp []
QED

Theorem decode_pos_simulation:
  !pos exp x. app_pos (encode_refs s) pos (encode_val x) = SOME enc_y /\
  pure_eval_to s env exp x
  ==>
  ?y. enc_y = encode_val y /\
  pure_eval_to s env (decode_pos tr exp pos) y
Proof
  Induct
  \\ simp [app_pos_def, decode_pos_def]
  \\ rw []
  \\ fs [pure_eval_to_def]
  \\ first_x_assum irule
  \\ Cases_on `n` \\ Cases_on `x` \\ fs [app_pos_def, encode_val_def]
  >- (
    Cases_on `l` \\ fs [app_pos_def]
    \\ simp [evaluate_def, do_app_def]
  )
  >- (
    fs [option_case_eq]
    \\ simp [evaluate_def, do_app_def]
    \\ fs [store_lookup_def, FLOOKUP_encode_refs, case_eq_thms]
  )
  >- (
    simp [evaluate_def, do_app_def]
    \\ Cases_on `l` \\ fs [app_pos_def]
    \\ drule app_pos_Term_IMP
    \\ csimp [EL_MAP]
  )
QED

Theorem fold_Boolv = GSYM (LIST_CONJ [
  Boolv_def |> REWRITE_RULE [GSYM backend_commonTheory.bool_to_tag_def],
  backend_commonTheory.bool_to_tag_def])

Theorem do_eq_Boolv:
  do_eq (Boolv x) (Boolv y) = Eq_val (x = y)
Proof
  EVAL_TAC \\ EVERY_CASE_TAC \\ fs []
QED

Theorem do_if_Boolv:
  do_if (Boolv x) y z = SOME (if x then y else z)
Proof
  EVAL_TAC \\ EVERY_CASE_TAC \\ fs []
QED

Theorem decode_guard_simulation:
  !b. dt_eval_guard (encode_refs s) (encode_val y) gd = SOME b /\
  pure_eval_to s env x y /\
  (!bv. ((bool_to_tag bv,SOME bool_id),0) ∈ s.c)
  ==>
  pure_eval_to s env (decode_guard tr x gd) (Boolv b)

Proof

  Induct_on `gd`
  \\ simp [decode_guard_def, FORALL_PROD, dt_eval_guard_def]
  \\ fs [pure_eval_to_def, evaluate_def, option_case_eq]
  \\ rw []
  \\ fs [Bool_def, evaluate_def, fold_Boolv, do_app_def, do_eq_Boolv,
        do_if_Boolv, bool_case_eq]

  \\ drule decode_test_simulation
  \\ imp_res_tac app_list_pos_LESS
  \\ fs [pure_eval_to_def, pattern_refsTheory.app_list_pos_def]
  \\ disch_then irule
  \\ drule decode_pos_simulation
  \\ simp [pure_eval_to_def]
  \\ disch_then drule
  \\ metis_tac []
QED

Definition base_cons_in_c_def:
  base_cons_in_c c <=> EVERY (v_cons_in_c c)
    [Boolv T; Boolv F; Unitv T; Unitv F; bind_exn_v; subscript_exn_v;
        div_exn_v; chr_exn_v] /\
    list_ctors ⊆ c
End

Theorem base_cons_in_c_imps1 = ASSUME ``base_cons_in_c c``
    |> SIMP_RULE list_ss [base_cons_in_c_def] |> CONJUNCTS
    |> map DISCH_ALL |> LIST_CONJ

Theorem base_cons_in_c_bool_tag:
  base_cons_in_c c ==>
  ((bool_to_tag bv,SOME bool_id),0) ∈ c
Proof
  rw [base_cons_in_c_def, v_cons_in_c_def, Boolv_def,
    backend_commonTheory.bool_to_tag_def]
QED

Theorem base_cons_in_c_imps2:
  (base_cons_in_c c ==> v_cons_in_c c (Unitv cc)) /\
  (base_cons_in_c c ==> v_cons_in_c c (Boolv b))
Proof
  rw [base_cons_in_c_def, Unitv_def, Boolv_def]
QED

Theorem base_cons_in_c_list_to_v:
  base_cons_in_c c ==>
  v_cons_in_c c (list_to_v xs) = EVERY (v_cons_in_c c) xs
Proof
  Induct_on `xs` \\ simp [list_to_v_def, base_cons_in_c_def, list_ctors_def]
QED

Theorem base_cons_in_c_v_to_list:
  !v vs. v_to_list v = SOME vs /\ v_cons_in_c c v ==>
  EVERY (v_cons_in_c c) vs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ simp [v_to_list_def, case_eq_thms]
  \\ rw [] \\ simp []
QED

val base_cons_in_c_imps = CONJUNCTS base_cons_in_c_imps1
    @ CONJUNCTS base_cons_in_c_imps2 @ [base_cons_in_c_list_to_v]

Theorem decode_dtree_simulation:
  pattern_top_level$dt_eval (encode_refs s) (encode_val y) dtree = SOME v /\
  pure_eval_to s env x y /\
  base_cons_in_c s.c
  ==>
  evaluate env s [decode_dtree tr exps x default_x dtree] =
  evaluate env s [case v of MatchSuccess i => EL i exps | _ => default_x]
Proof
  Induct_on `dtree`
  \\ simp [dt_eval_def, decode_dtree_def]
  \\ rw [evaluate_def]
  \\ fs [option_case_eq]
  \\ drule_then drule decode_guard_simulation
  \\ simp [base_cons_in_c_bool_tag]
  \\ rw [pure_eval_to_def]
  \\ simp [do_if_Boolv]
  \\ CASE_TAC \\ fs []
QED

Definition c_type_map_rel_def:
  c_type_map_rel c type_map = (!stmp ty_id len.
    (((stmp, SOME ty_id), len) ∈ c) <=>
        ?tys. lookup ty_id type_map = SOME tys /\ MEM (stmp, len) tys)
End

Theorem ctor_same_type_v_cons_is_sibling:
  ctor_same_type (SOME stmp) (SOME stmp') /\
  c_type_map_rel c tm /\
  (stmp, len) ∈ c /\
  (stmp', len') ∈ c /\
  stmp' = (x, SOME y) ==>
  is_sibling (x, len') (lookup y tm)
Proof
  simp [c_type_map_rel_def]
  \\ Cases_on `stmp` \\ Cases_on `stmp'` \\ rw []
  \\ rfs [ctor_same_type_def]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ simp [pattern_litTheory.is_sibling_def]
QED

Theorem encode_pat_match_simulation:
  (! ^s pat v pre_bindings res.
  flatSem$pmatch s pat v pre_bindings = res /\
  res <> Match_type_error /\
  s.check_ctor /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c tm
  ==>
  pattern_top_level$pmatch (encode_refs s) (encode_pat tm pat) (encode_val v) =
  (if res = No_match then PMatchFailure else PMatchSuccess)
  ) /\
  (! ^s ps vs pre_bindings res.
  flatSem$pmatch_list s ps vs pre_bindings = res /\
  res <> Match_type_error /\
  s.check_ctor /\
  EVERY (v_cons_in_c s.c) vs /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c tm
  ==>
  pattern_top_level$pmatch_list (encode_refs s) (MAP (encode_pat tm) ps)
    (MAP encode_val vs) =
  (if res = No_match then PMatchFailure else PMatchSuccess))
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind
  \\ rpt strip_tac
  \\ fs [encode_pat_def, encode_val_def,
    Q.ISPEC `encode_val` ETA_THM, Q.ISPEC `encode_pat m` ETA_THM]
  \\ fs [pmatch_con_case_opt]
  \\ fs [flatSemTheory.pmatch_def, pmatch_def]
  \\ TRY (fs [pmatch_stamps_ok_def, bool_case_eq] \\ rveq \\ fs [] \\ NO_TAC)
  >- (
    (* conses with tag *)
    fs [Q.GEN `t` bool_case_eq |> Q.ISPEC `Match_type_error`] \\ fs []
    \\ fs [pmatch_stamps_ok_def, v_cons_in_c_def]
    \\ rfs []
    \\ drule_then drule ctor_same_type_v_cons_is_sibling
    \\ disch_then drule
    \\ rpt (CASE_TAC \\ fs [ctor_same_type_def, same_ctor_def, pmatch_def,
            pattern_litTheory.is_sibling_def])
    \\ rveq \\ fs []
  )
  >- (
    (* refs *)
    fs [case_eq_thms]
    \\ rveq \\ fs []
    \\ fs [FLOOKUP_encode_refs, store_lookup_def, EVERY_EL]
    \\ first_x_assum drule
    \\ simp []
  )
  >- (
    fs [CaseEq "match_result"]
    \\ rveq \\ fs []
  )
QED

Theorem pmatch_rows_encode:
  !pats j_offs.
  pmatch_rows pats s v <> Match_type_error /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c cfg.type_map /\ s.check_ctor
  ==>
  case (pattern_top_level$match (encode_refs s)
    (MAPi (λj (p,_). (encode_pat cfg.type_map p, j + j_offs)) pats) (encode_val v))
    of NONE => F
    | SOME (MatchSuccess n) => ?i env. n = i + j_offs /\ i < LENGTH pats /\
        pmatch s (FST (EL i pats)) v [] = Match env /\
        pmatch_rows pats s v = Match (env, EL i pats)
    | _ => pmatch_rows pats s v = No_match
Proof
  Induct_on `pats`
  \\ simp [FORALL_PROD, pmatch_rows_def, match_def]
  \\ rw []
  \\ qmatch_asmsub_abbrev_tac `pmatch _ hd_pat _ []`
  \\ Cases_on `pmatch s hd_pat v [] = Match_type_error`
  \\ fs []
  \\ drule_then drule
    (SIMP_RULE bool_ss [] (hd (CONJUNCTS encode_pat_match_simulation)))
  \\ simp [combinTheory.o_ABS_L]
  \\ first_x_assum (qspec_then `SUC j_offs` mp_tac)
  \\ simp_tac (bool_ss ++ numSimps.ARITH_AC_ss) [ADD1]
  (* make this variable sort left by hand. ugh *)
  \\ qabbrev_tac `aj_offs = j_offs`
  \\ rw []
  >- (
    (* match failed *)
    rpt (CASE_TAC \\ fs [])
    \\ rfs []
    \\ simp [GSYM ADD1]
  )
  \\ Cases_on `pmatch s hd_pat v []` \\ fs []
  \\ EVERY_CASE_TAC \\ fs []
  \\ qexists_tac `0` \\ simp []
QED

Theorem evaluate_compile_pats:
  pmatch_rows pats s v <> Match_type_error /\
  pure_eval_to s env exp v /\
  v_cons_in_c s.c v /\
  base_cons_in_c s.c /\
  s.check_ctor /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c cfg.type_map ==>
  evaluate env s [compile_pats cfg t N exp default_x pats] =
  evaluate env s [case pmatch_rows pats s v of
    | Match (env', p', e') => compile_pat_rhs t N exp (p', e')
    | _ => default_x]
Proof
  rw [compile_pats_def]
  \\ simp []
  \\ drule (Q.SPECL [`pats`, `0`] pmatch_rows_encode)
  \\ rpt (disch_then drule)
  \\ TOP_CASE_TAC
  \\ drule_then (qspec_then `cfg.pat_heuristic` assume_tac)
    pattern_top_levelTheory.pat_compile_correct
  \\ drule_then drule decode_dtree_simulation
  \\ simp []
  \\ disch_then (fn t => DEP_REWRITE_TAC [t])
  \\ EVERY_CASE_TAC \\ fs []
  \\ rw [] \\ fs []
  \\ simp [EL_MAP]
QED

Theorem pmatch_rows_IMP_pmatch:
  pmatch_rows pats s v = Match (env, p, exp) ==>
  pmatch s p v [] = Match env
Proof
  Induct_on `pats` \\ simp [FORALL_PROD, pmatch_rows_def]
  \\ rw []
  \\ fs [CaseEq "match_result"] \\ rveq \\ fs []
QED

Theorem compile_match_pmatch_rows:
  !pats k pats2 res.
  compile_match cfg pats = (k, pats2) /\
  v_rel cfg v v' /\
  state_rel cfg s t /\
  k <= N /\
  pmatch_rows pats s v = res ==>
  case res of
    | Match_type_error => T
    | No_match => pmatch_rows pats2 t v' = No_match
    | Match (env, p, e) => ?i env'. i < LENGTH pats /\ i < LENGTH pats2 /\
        (p, e) = EL i pats /\ nv_rel cfg N env env' /\
        pmatch_rows pats2 t v' = Match (env', EL i pats2)
Proof
  Induct
  \\ simp [FORALL_PROD, compile_exps_def, pmatch_rows_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on `pmatch s p_1 v []` \\ fs []
  \\ drule (CONJUNCT1 pmatch_thm)
  \\ simp []
  \\ disch_then (drule_then drule)
  \\ simp []
  \\ disch_then (qspecl_then [`N`, `[]`] mp_tac)
  \\ simp [ALOOKUP_rel_empty]
  \\ rw []
  \\ fs [pmatch_rows_def]
  \\ EVERY_CASE_TAC \\ fs [match_rel_def]
  \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
  \\ TRY (qexists_tac `SUC i'` \\ simp [] \\ NO_TAC)
QED

Theorem compile_match_EL:
  !pats pats2 k i.
  compile_match cfg pats = (k, pats2) /\
  i < LENGTH pats /\
  EL i pats = (pat, exp) ==>
  ?exp_i exp'.
  compile_exps cfg [exp] = (exp_i, [exp']) /\
  EL i pats2 = (pat, exp') /\
  exp_i <= k /\ max_dec_name (pat_bindings pat []) <= k
Proof
  Induct
  \\ simp [FORALL_PROD, compile_exps_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ Cases_on `i`
  \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ rw []
  \\ simp []
QED

Theorem evaluate_compile_pat_rhs:
  evaluate uenv s [compile_pat_rhs tr N (Var_local tr (enc_num_to_name N ""))
    (p, exp)] = (t, res) /\
  pmatch s p v [] = Match bindings /\
  env_rel cfg M env1 env2 /\
  nv_rel cfg M l_bindings bindings /\
  uenv.v = (enc_num_to_name N "", v) :: env2.v /\
  N <= M /\
  max_dec_name (pat_bindings p []) < N - 1 /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (v_cons_in_c s.c ∘ SND) env2.v
  ==>
  ?ext_env.
  evaluate ext_env s [exp] = (t, res) /\
  env_rel cfg (N - 1) <| v := l_bindings ++ env1.v |> ext_env /\
  EVERY (v_cons_in_c s.c ∘ SND) ext_env.v
Proof
  simp [compile_pat_rhs_def, max_dec_name_LESS_EVERY]
  \\ qmatch_goalsub_abbrev_tac `evaluate _ _ [SND comp]`
  \\ PairCases_on `comp`
  \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ rw []
  \\ drule (compile_pat_bindings_simulation_lemma |> SPEC_ALL |> Q.GEN `vs`
        |> Q.SPEC `[v]`)
  \\ simp [flatSemTheory.pmatch_def, CaseEq "match_result"]
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`N - 1`, `env2.v`] mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    simp [ALOOKUP_rel_def, pure_eval_to_def, evaluate_def, dec_enc]
    \\ rw [] \\ fs [dec_enc]
  )
  \\ rw []
  \\ asm_exists_tac
  \\ fs [env_rel_def]
  \\ fs [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ rw []
  \\ rpt (first_x_assum (qspec_then `x` mp_tac))
  \\ simp [OPTREL_def, case_eq_thms]
  \\ rw [] \\ fs []
QED

val EVERY_EL_IMP = ASSUME ``EVERY P xs`` |> REWRITE_RULE [EVERY_EL]
  |> DISCH_ALL

Theorem do_app_v_inv:
  do_app cc s op vs = SOME (t, r) /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (OPTION_ALL (v_cons_in_c s.c)) s.globals /\
  base_cons_in_c s.c /\
  EVERY (v_cons_in_c s.c) vs
  ==>
  t.c = s.c /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) t.refs /\
  EVERY (OPTION_ALL (v_cons_in_c s.c)) t.globals /\
  EVERY (v_cons_in_c s.c) (result_vs (list_result r))
Proof
  simp [do_app_def, case_eq_thms, pair_case_eq, bool_case_eq, store_alloc_def,
    store_assign_def]
  \\ rpt disch_tac \\ fs []
  \\ rveq \\ simp base_cons_in_c_imps
  \\ TRY (pairarg_tac \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [])
  \\ fs [IMP_EVERY_LUPDATE, EVERY_MAP, IS_SOME_EXISTS, GREATER_EQ,
    NOT_LESS_EQUAL, EVERY_REPLICATE]
  \\ TRY (drule_then drule EVERY_EL_IMP \\ simp [])
  \\ TRY (
    drule_then drule base_cons_in_c_v_to_list
    \\ imp_res_tac base_cons_in_c_v_to_list
    \\ simp []
  )
  \\ fs [store_lookup_def]
  \\ rw [IMP_EVERY_LUPDATE]
  \\ drule_then drule EVERY_EL_IMP \\ rw []
  \\ drule_then drule EVERY_EL_IMP \\ rw []
QED

Theorem do_opapp_v_inv:
  do_opapp vs = SOME (nvs, exp) /\
  EVERY (v_cons_in_c c) vs
  ==>
  EVERY (v_cons_in_c c ∘ SND) nvs
Proof
  simp [do_opapp_def, case_eq_thms]
  \\ rw [] \\ fs []
  \\ fs [find_recfun_ALOOKUP, pair_case_eq]
  \\ rveq \\ fs [build_rec_env_eq_MAP, EVERY_MAP]
  \\ simp [UNCURRY]
QED

Theorem nv_rel_to_env_rel:
  nv_rel cfg N vs vs' ==> env_rel cfg N <| v := vs |> <| v := vs' |>
Proof
  simp [env_rel_def]
QED

Theorem state_rel_dec_clock:
  state_rel cfg s1 s2 ==> state_rel cfg (dec_clock s1) (dec_clock s2)
Proof
  simp [state_rel_def, dec_clock_def]
QED

Theorem compile_exps_evaluate:
  !env1 ^s1 xs t1 r1 i ys N env2 ^s2 c2.
    evaluate env1 s1 xs = (t1, r1) /\
    compile_exps cfg xs = (i, ys) /\
    r1 <> Rerr (Rabort Rtype_error) /\
    env_rel cfg N env1 env2 /\ state_rel cfg s1 s2 /\ i < N /\
    EVERY (EVERY (v_cons_in_c s2.c) ∘ store_v_vs) s2.refs /\
    EVERY (OPTION_ALL (v_cons_in_c s2.c)) s2.globals /\
    base_cons_in_c s2.c /\
    EVERY (v_cons_in_c s2.c ∘ SND) env2.v /\
    c_type_map_rel s2.c cfg.type_map
    ==>
    ?t2 r2.
      result_rel (LIST_REL (v_rel cfg)) (v_rel cfg) r1 r2 /\
      state_rel cfg t1 t2 /\
      evaluate env2 s2 ys = (t2, r2) /\
      EVERY (EVERY (v_cons_in_c s2.c) ∘ store_v_vs) t2.refs /\
      EVERY (OPTION_ALL (v_cons_in_c s2.c)) t2.globals /\
      EVERY (v_cons_in_c s2.c) (result_vs r2) /\
      t2.c = s2.c
Proof
  ho_match_mp_tac evaluate_ind
  \\ simp [evaluate_def, compile_exps_def, result_vs_def]
  \\ rpt (gen_tac ORELSE disch_tac ORELSE conj_tac)
  \\ simp [v_rel_rules]
  \\ fs [pair_case_eq, Q.GEN `t` bool_case_eq
    |> Q.ISPEC `(x, Rerr (Rabort Rtype_error))`, Q.GEN `f` bool_case_eq
    |> Q.ISPEC `(x, Rerr (Rabort Rtype_error))`] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
  \\ rveq \\ fs [evaluate_def, v_rel_rules, GSYM PULL_FORALL]
  \\ TRY (rename [`rv_1 ≠ Rerr (Rabort Rtype_error) ==> _`]
    \\ (Cases_on `rv_1 = Rerr (Rabort Rtype_error)` >- fs [])
    \\ fs [])
  \\ TRY (rename [`rv_1 ≠ Rerr (Rabort Rtype_error) /\ _`]
    \\ (Cases_on `rv_1 = Rerr (Rabort Rtype_error)` >- fs [])
    \\ fs [])
  \\ TRY (rename [`~ st.check_ctor`]
    \\ imp_res_tac state_rel_IMP_check_ctor \\ fs [])
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rpt (first_x_assum drule \\ rw [])
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
    \\ rveq \\ fs []
  )
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ simp [evaluate_def, v_cons_in_c_def]
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rpt (first_x_assum drule \\ rw [])
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
    \\ rveq \\ fs []
  )
  >- (
    (* Handle *)
    simp [evaluate_def, pat_bindings_def, pmatch_rows_def,
        flatSemTheory.pmatch_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ rw []
    \\ first_x_assum (drule_then drule)
    \\ TRY (fs [MAX_ADD_LESS, PULL_EXISTS] \\ NO_TAC)
    (* down to raise+pmatch case *)
    \\ impl_tac >- fs [MAX_ADD_LESS]
    \\ rw []
    \\ fs [result_vs_def]
    \\ rename [`compile_match _ _ = (k, _)`]
    \\ `k <= N` by fs [MAX_ADD_LESS]
    \\ drule_then (drule_then drule) compile_match_pmatch_rows
    \\ disch_then drule
    \\ rw []
    \\ DEP_REWRITE_TAC [Q.GEN `v` evaluate_compile_pats |> Q.SPEC `v'`]
    \\ imp_res_tac state_rel_IMP_check_ctor
    \\ simp [pure_eval_to_def, evaluate_def]
    \\ fs [CaseEq "match_result", pair_case_eq, bool_case_eq] \\ rveq
    \\ fs [] \\ rfs [] \\ simp [evaluate_def, result_vs_def]
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then (drule_then drule) compile_match_EL
    \\ rw [] \\ fs []
    \\ imp_res_tac pmatch_rows_IMP_pmatch
    \\ qmatch_goalsub_abbrev_tac `x = (_, _)`
    \\ PairCases_on `x`
    \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then drule evaluate_compile_pat_rhs
    \\ simp [LESS_MAX_ADD]
    \\ rpt (disch_then drule)
    \\ simp []
    \\ disch_tac
    \\ fs []
    \\ last_x_assum (drule_then drule)
    \\ simp [LESS_MAX_ADD]
  )
  >- (
    (* Conv, no tag *)
    imp_res_tac state_rel_IMP_check_ctor
    \\ last_x_assum (drule_then drule)
    \\ rw [] \\ simp []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [v_rel_rules, EVERY_REVERSE]
  )
  >- (
    (* Conv with tag *)
    imp_res_tac state_rel_IMP_check_ctor
    \\ last_x_assum (drule_then drule)
    \\ rw [] \\ simp []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [PULL_EXISTS, v_rel_rules, EVERY_REVERSE]
    \\ imp_res_tac evaluate_length
    \\ fs [state_rel_def]
    \\ rfs []
  )
  >- (
    drule_then drule env_rel_ALOOKUP
    \\ strip_tac \\ fs [optionTheory.OPTREL_def]
  )
  >- (
    (* invs of looked up var *)
    fs [case_eq_thms]
    \\ drule_then drule env_rel_ALOOKUP
    \\ simp [optionTheory.OPTREL_def]
    \\ rw []
    \\ simp []
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [EVERY_MEM]
    \\ res_tac \\ fs []
  )
  >- (
    simp [Once v_rel_cases]
    \\ fs [env_rel_def]
    \\ asm_exists_tac \\ simp []
  )
  >- (
    (* App *)
    first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `op = Opapp`
    >- (
      fs [option_case_eq, pair_case_eq]
      \\ rveq \\ fs []
      \\ drule_then drule do_opapp_thm_REVERSE
      \\ rw []
      \\ imp_res_tac state_rel_IMP_clock
      \\ imp_res_tac LENGTH_compile_exps_IMP
      \\ fs [bool_case_eq, quantHeuristicsTheory.LIST_LENGTH_2]
      \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
      \\ imp_res_tac state_rel_dec_clock
      \\ last_x_assum (first_assum o mp_then (Pat `state_rel _ _ _`) mp_tac)
      \\ simp [dec_clock_def]
      \\ disch_then irule
      \\ drule do_opapp_v_inv
      \\ rw [EVERY_REVERSE]
      \\ simp [env_rel_def]
      \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ simp []
    )
    \\ fs [option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ drule_then (drule_then drule) do_app_thm_REVERSE
    \\ imp_res_tac state_rel_IMP_check_ctor
    \\ rw []
    \\ fs []
    \\ drule do_app_v_inv
    \\ simp [EVERY_REVERSE]
  )
  >- (
    (* If *)
    first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ imp_res_tac flatPropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ drule_then drule do_if_helper
    \\ rw []
    \\ fs [do_if_def, bool_case_eq]
    \\ rveq \\ fs []
    \\ last_x_assum (drule_then drule)
    \\ simp []
  )
  >- (
    (* Mat *)
    simp [evaluate_def, pat_bindings_def, flatSemTheory.pmatch_def]
    \\ first_x_assum (drule_then drule)
    \\ impl_tac >- (fs [MAX_ADD_LESS])
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ DEP_REWRITE_TAC [Q.GEN `v` evaluate_compile_pats |> Q.SPEC `HD v'`]
    \\ simp [pure_eval_to_def, evaluate_def, libTheory.opt_bind_def]
    \\ imp_res_tac flatPropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ rename [`compile_match _ _ = (k, _)`]
    \\ drule_then (drule_then drule) compile_match_pmatch_rows
    \\ `k <= N` by fs [MAX_ADD_LESS]
    \\ disch_then drule
    \\ fs [CaseEq "match_result", pair_case_eq, bool_case_eq] \\ rveq \\ fs []
    >- (
      (* no match *)
      simp [PULL_EXISTS, evaluate_def]
      \\ simp (map (SIMP_RULE (srw_ss()) [bind_exn_v_def]) base_cons_in_c_imps)
      \\ imp_res_tac state_rel_IMP_check_ctor
      \\ simp [bind_exn_v_def, v_rel_l_cases]
    )
    \\ imp_res_tac state_rel_IMP_check_ctor
    \\ rw [] \\ simp []
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then (drule_then drule) compile_match_EL
    \\ rw []
    \\ fs []
    \\ imp_res_tac pmatch_rows_IMP_pmatch
    (* pull out evaluate *)
    \\ qmatch_goalsub_abbrev_tac `x = (_, _)`
    \\ PairCases_on `x`
    \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then drule evaluate_compile_pat_rhs
    \\ simp [LESS_MAX_ADD]
    \\ rpt (disch_then drule)
    \\ simp [libTheory.opt_bind_def]
    \\ disch_tac \\ fs []
    \\ last_x_assum (drule_then drule)
    \\ simp [LESS_MAX_ADD]
  )
  >- (
    (* Let *)
    first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ last_x_assum (first_assum o mp_then (Pat `state_rel _ _ _`) mp_tac)
    \\ simp []
    \\ disch_then irule
    \\ simp []
    \\ imp_res_tac evaluate_sing
    \\ rveq \\ fs []
    \\ conj_tac
    >- (
      simp [libTheory.opt_bind_def]
      \\ CASE_TAC \\ simp []
    )
    \\ asm_exists_tac
    \\ fs [env_rel_def, libTheory.opt_bind_def]
    \\ CASE_TAC \\ simp []
    \\ simp [ALOOKUP_rel_cons]
  )
  >- (
    fs [bool_case_eq]
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [MAP_MAP_o, o_DEF, UNCURRY, ETA_THM]
    \\ first_x_assum irule
    \\ simp [build_rec_env_eq_MAP, EVERY_MAP, o_DEF]
    \\ asm_exists_tac
    \\ fs [env_rel_def, FILTER_APPEND]
    \\ irule ALOOKUP_rel_append_suff
    \\ simp [UNCURRY, MAP_MAP_o, o_DEF]
    \\ irule ALOOKUP_rel_eq_fst
    \\ rw [LIST_REL_EL_EQN, EL_MAP, UNCURRY]
    \\ simp [Once v_rel_cases]
    \\ qexists_tac `N`
    \\ fs [ELIM_UNCURRY, list_max_LESS, EVERY_MAP]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac MONO_EVERY)
    \\ simp []
  )
QED

Definition compile_dec_def:
  compile_dec cfg (Dlet exp) = (cfg, Dlet (HD (compile_exps cfg [exp]))) /\
  compile_dec cfg (Dtype tid amap) =
    (cfg with type_map update_by (insert tid
        (FLAT (

  , Dtype tid amap) /\
  compile_dec cfg (Dexn n n') = (cfg, Dexn n n')

QED

[evaluate_dec_def, c_type_map_rel_def]

val compile_dec_def = Define `
  (compile_dec ctors (Dlet exp) = (ctors, Dlet (compile_exp ctors exp))) /\
  (compile_dec ctors (Dtype tid amap) =
     (ctors |+ (tid, amap), Dtype tid amap)) /\
  (compile_dec ctors dec = (ctors, dec))`

val compile_decs_def = Define `
  (compile_decs ctors [] = (ctors, [])) /\
  (compile_decs ctors (d::ds) =
    let (ctor1, e)  = compile_dec  ctors d  in
    let (ctor2, es) = compile_decs ctor1 ds in
      (ctor2, e::es))`;


Theorem compile_decs_evaluate

val _ = export_theory()
