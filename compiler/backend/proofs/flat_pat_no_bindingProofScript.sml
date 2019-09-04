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

val _ = new_theory "flat_pat_no_bindingProof"

val _ = set_grammar_ancestry ["misc","ffi","bag","flatProps",
                              (*"flat_pat_no_binding",*)
                              "backendProps","backend_common"];

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

Theorem name_to_id_to_name:
  !xs. dec_name_to_num (enc_num_to_name i xs) = i + FOLDR (\c i. i + ORD c) 0 xs
Proof
  measureInduct_on `I i`
  \\ simp [Once enc_num_to_name_def]
  \\ CASE_TAC \\ simp [dec_name_to_num_def, sum_string_ords_eq]
QED

Theorem enc_num_to_name_inj:
  (enc_num_to_name i [] = enc_num_to_name j []) = (i = j)
Proof
  metis_tac [name_to_id_to_name |> Q.SPEC `[]` |> SIMP_RULE list_ss []]
QED

Definition compile_exps_def:
  (compile_exps [] = (0, [])) /\
  (compile_exps (x::y::xs) =
    let (i, cx) = compile_exps [x] in
    let (j, cy) = compile_exps (y::xs) in
    (MAX i j, HD cx :: cy)) /\
  (compile_exps [Var_local t vid] =
    (dec_name_to_num vid, [Var_local t vid])) /\
  (compile_exps [Raise t x] =
    let (i, xs) = compile_exps [x] in
    (i, [Raise t (HD xs)])) /\
  (compile_exps [Handle t x ps] =
    let (i, xs) = compile_exps [x] in
    let (j, ps2) = compile_match ps in
    let k = MAX i j + 1 in
    let nm = enc_num_to_name k [] in
    (k, [Handle t (HD xs) [(Pvar nm, Mat t (Var_local t nm) ps2)]])) /\
  (compile_exps [Con t ts xs] =
    let (i, ys) = compile_exps (REVERSE xs) in
    (i, [Con t ts (REVERSE ys)])) /\
  (compile_exps [Fun t vs x] =
    let (i, xs) = compile_exps [x] in
    (i, [Fun t vs (HD xs)])) /\
  (compile_exps [App t op xs] =
    let (i, ys) = compile_exps (REVERSE xs) in
    (i, [App t op (REVERSE ys)])) /\
  (compile_exps [Mat t x ps] =
    let (i, xs) = compile_exps [x] in
    let (j, ps2) = compile_match ps in
    let k = MAX i j + 1 in
    let nm = enc_num_to_name k [] in
    (k, [Let t (SOME nm) (HD xs) (Mat t (Var_local t nm) ps2)])) /\
  (compile_exps [Let t v x1 x2] =
    let (i, xs1) = compile_exps [x1] in
    let (j, xs2) = compile_exps [x2] in
    let k = (case v of NONE => 0 | SOME vid => dec_name_to_num vid) in
    (MAX i (MAX j k), [Let t v (HD xs1) (HD xs2)])) /\
  (compile_exps [Letrec t fs x] =
    let ys      = MAP (\(a,b,c). (a, b, compile_exps [c])) fs in
    let (i, xs) = compile_exps [x] in
    let j       = list_max (MAP (\(_,_,(j,_)). j) ys) in
    let fs1     = MAP (\(a,b,(_,xs)). (a,b,HD xs)) ys in
    (MAX i j, [Letrec t fs1 (HD xs)])) /\
  (compile_exps [If t x1 x2 x3] =
    let (i, xs1) = compile_exps [x1] in
    let (j, xs2) = compile_exps [x2] in
    let (k, xs3) = compile_exps [x3] in
    (MAX i (MAX j k), [If t (HD xs1) (HD xs2) (HD xs3)])) /\
  (compile_exps [expr] = (0, [expr])) /\
  (compile_match [] = (0, [])) /\
  (compile_match ((p, x)::ps) =
    let (i, xs) = compile_exps [x] in
    let (j, ps2) = compile_match ps in
    (MAX i j, ((p, HD xs) :: ps2)))
Termination
  WF_REL_TAC `measure (\x. case x of INL xs => exp6_size xs
    | INR ps => exp3_size ps)`
  \\ rw [flatLangTheory.exp_size_def]
  \\ imp_res_tac flatLangTheory.exp_size_MEM
  \\ fs []
End

Definition compile_decs_def:
  compile_decs [] = [] /\
  (compile_decs ((Dlet e)::xs) =
    let (_, ys) = compile_exps [e] in
    (Dlet (HD ys) :: compile_decs xs)) /\
  (compile_decs ((Dtype n s)::xs) = Dtype n s :: compile_decs xs) /\
  (compile_decs ((Dexn n n2)::xs) = Dexn n n2 :: compile_decs xs)
End

Theorem LENGTH_compile_exps_IMP:
  (!xs i ys. compile_exps xs = (i, ys) ==> LENGTH ys = LENGTH xs) /\
  (!ps i ps2. compile_match ps = (i, ps2) ==> LENGTH ps2 = LENGTH ps)
Proof
  ho_match_mp_tac compile_exps_ind \\ rw [compile_exps_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Theorem LENGTH_SND_compile_exps:
  LENGTH (SND (compile_exps xs)) = LENGTH xs /\
  LENGTH (SND (compile_match ps)) = LENGTH ps
Proof
  Cases_on `compile_exps xs` \\ Cases_on `compile_match ps`
  \\ imp_res_tac LENGTH_compile_exps_IMP \\ simp []
QED

Inductive v_rel:
  (!v. v_rel (Litv v) (Litv v)) /\
  (!n. v_rel (Loc n) (Loc n)) /\
  (!vs1 vs2. LIST_REL v_rel vs1 vs2 ==>
     v_rel (Vectorv vs1) (Vectorv vs2)) /\
  (!stmp vs1 vs2. LIST_REL v_rel vs1 vs2 ==>
     v_rel (Conv stmp vs1) (Conv stmp vs2)) /\
  (!N vs1 n x vs2.
     nv_rel N vs1 vs2 /\ FST (compile_exps [x]) <= N ==>
     v_rel (Closure vs1 n x) (Closure vs2 n (HD (SND (compile_exps [x]))))) /\
  (!N vs1 fs x vs2.
     nv_rel N vs1 vs2 /\ EVERY (\(n,m,e). FST (compile_exps [e]) <= N) fs ==>
     v_rel (Recclosure vs1 fs x) (Recclosure vs2
         (MAP (\(n,m,e). (n,m,HD (SND (compile_exps [e])))) fs) x)) /\
  (!N vs1 vs2. nv_rel2 N (FILTER (\x. dec_name_to_num (FST x) < N) vs1)
    (FILTER (\x. dec_name_to_num (FST x) < N) vs2) ==> nv_rel N vs1 vs2) /\
  (!N vs1 vs2. MAP FST vs1 = MAP FST vs2 /\
    LIST_REL v_rel (MAP SND vs1) (MAP SND vs2) ==> nv_rel2 N vs1 vs2)
End

Theorem v_rel_l_cases = TypeBase.nchotomy_of ``: v``
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (curry mk_comb ``v_rel``)
  |> map (fn t => mk_comb (t, ``v2 : v``))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

val v = augment_srw_ss [simpLib.named_rewrites "seriously"
  [quotient_pairTheory.PAIR_REL_THM]];

Theorem nv_rel2_LIST_REL:
  !vs2 vs1. nv_rel2 N vs1 vs2 =
  LIST_REL ((=) ### v_rel) vs1 vs2
Proof
  simp [Once v_rel_cases]
  \\ CONV_TAC (STRIP_QUANT_CONV (REWR_CONV EQ_SYM_EQ))
  \\ Induct \\ rpt Cases \\ simp []
  \\ simp [quotient_pairTheory.PAIR_REL, UNCURRY]
  \\ metis_tac []
QED

Theorem nv_rel_LIST_REL:
  !vs2 vs1. nv_rel N vs1 vs2 =
  LIST_REL ((=) ### v_rel) (FILTER (\x. dec_name_to_num (FST x) < N) vs1)
    (FILTER (\x. dec_name_to_num (FST x) < N) vs2)
Proof
  simp [Once v_rel_cases, nv_rel2_LIST_REL]
QED

Theorem nv_rel_cons:
  FST x = FST y /\ (dec_name_to_num (FST x) < N ==> v_rel (SND x) (SND y)) /\
  nv_rel N xs ys ==>
  nv_rel N (x :: xs) (y :: ys)
Proof
  simp [nv_rel_LIST_REL]
  \\ rw [quotient_pairTheory.PAIR_REL, UNCURRY]
QED

Definition state_rel_def:
  state_rel (s:'ffi flatSem$state) (t:'ffi flatSem$state) <=>
    t.clock = s.clock /\
    LIST_REL (sv_rel v_rel) s.refs t.refs /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL v_rel) s.globals t.globals /\
    t.c = s.c /\
    s.exh_pat /\
    t.exh_pat /\
    ~s.check_ctor /\
    ~t.check_ctor
End

Theorem state_rel_initial_state:
  state_rel (initial_state ffi k T F) (initial_state ffi k T F)
Proof
  fs [state_rel_def, initial_state_def]
QED

Triviality state_rel_IMP_check_ctor:
  state_rel s t ==> ~s.check_ctor /\ ~t.check_ctor
Proof
  fs [state_rel_def]
QED

Triviality state_rel_IMP_clock:
  state_rel s t ==> t.clock = s.clock
Proof
  fs [state_rel_def]
QED

Definition env_rel_def:
  env_rel N env1 env2 = nv_rel N env1.v env2.v
End

(* fixme does everyone define match_rel themselves the same way? *)
val match_rel_def = Define `
  (match_rel N (Match env1) (Match env2) <=> nv_rel N env1 env2) /\
  (match_rel N No_match No_match <=> T) /\
  (match_rel N Match_type_error Match_type_error <=> T) /\
  (match_rel N _ _ <=> F)`

Theorem match_rel_thms[simp]:
   (match_rel N Match_type_error e <=> e = Match_type_error) /\
   (match_rel N e Match_type_error <=> e = Match_type_error) /\
   (match_rel N No_match e <=> e = No_match) /\
   (match_rel N e No_match <=> e = No_match)
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

Theorem env_is_v_fold:
  <| v := env.v |> = env
Proof
  simp [environment_component_equality]
QED

Theorem env_rel_add_enc:
  N <= i ==>
  env_rel N env1 <|v := (enc_num_to_name i "", x)::vs|> =
  env_rel N env1 <|v := vs|>
Proof
  simp [env_rel_def, nv_rel_LIST_REL, name_to_id_to_name]
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

Theorem env_rel_mono:
  env_rel i env1 env2 /\ j <= i ==>
  env_rel j env1 env2
Proof
  rw [env_rel_def, nv_rel_LIST_REL]
  \\ drule_then irule LIST_REL_FILTER_MONO
  \\ simp [FORALL_PROD]
QED

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

Theorem env_rel_ALOOKUP:
  env_rel N env1 env2 /\ dec_name_to_num n < N ==>
  OPTREL v_rel (ALOOKUP env1.v n) (ALOOKUP env2.v n)
Proof
  rw [env_rel_def, nv_rel_LIST_REL]
  \\ drule LIST_REL_ALOOKUP_OPTREL
  \\ disch_then (qspecl_then [`n`, `v_rel`] mp_tac)
  \\ simp [FORALL_PROD]
  \\ simp [ALOOKUP_FILTER |> SIMP_RULE bool_ss [ELIM_UNCURRY]]
QED

Theorem do_opapp_thm:
  do_opapp vs1 = SOME (nvs1, exp) /\ LIST_REL v_rel vs1 vs2
  ==>
  ?i exps nvs2. compile_exps [exp] = (i, exps) /\
  nv_rel (i + 1) nvs1 nvs2 /\ do_opapp vs2 = SOME (nvs2, HD exps)
Proof
  simp [do_opapp_def, pair_case_eq, case_eq_thms, PULL_EXISTS]
  \\ cheat
QED

Theorem do_opapp_thm_REVERSE:
  do_opapp (REVERSE vs1) = SOME (nvs1, exp) /\ LIST_REL v_rel vs1 vs2
  ==>
  ?i exps nvs2.
  compile_exps [exp] = (i, exps) /\
  nv_rel (i + 1) nvs1 nvs2 /\
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
    state_rel s s1 /\
    v_rel v v1 /\
    nv_rel N vs vs1
    ==> ?r1. pmatch s1 p v1 vs1 = r1 /\ match_rel N r r1) /\
  (!(s:'ffi state) ps v vs r s1 v1 vs1.
    pmatch_list s ps v vs = r /\
    r <> Match_type_error /\
    state_rel s s1 ∧
    LIST_REL v_rel v v1 /\
    nv_rel N vs vs1
    ==> ?r1. pmatch_list s1 ps v1 vs1 = r1 /\ match_rel N r r1)
Proof
  ho_match_mp_tac pmatch_ind
  \\ simp [pmatch_def, match_rel_def, v_rel_l_cases]
  \\ rw [match_rel_def]
  \\ imp_res_tac state_rel_IMP_check_ctor
  \\ fs [pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  >- ( irule nv_rel_cons \\ simp [] )
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

Theorem do_app_thm:
  do_app cc s1 op vs1 = SOME (t1, r1) /\
  state_rel s1 s2 /\ LIST_REL v_rel vs1 vs2
  ==>
  ?t2 r2. result_rel v_rel v_rel r1 r2 /\
  state_rel t1 t2 /\ do_app cc s2 op vs2 = SOME (t2, r2)
Proof
  cheat
QED

Theorem do_app_thm_REVERSE:
  do_app cc s1 op (REVERSE vs1) = SOME (t1, r1) /\
  state_rel s1 s2 /\ LIST_REL v_rel vs1 vs2
  ==>
  ?t2 r2. result_rel v_rel v_rel r1 r2 /\
  state_rel t1 t2 /\ do_app cc s2 op (REVERSE vs2) = SOME (t2, r2)
Proof
  rw []
  \\ drule_then irule do_app_thm
  \\ simp []
QED

Theorem do_if_helper:
  do_if b x y = SOME e /\ v_rel b b' ==>
  ((b' = Boolv T) = (b = Boolv T)) /\ ((b' = Boolv F) = (b = Boolv F))
Proof
  simp [Once v_rel_cases]
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

val s = ``s:'ffi flatSem$state``;
val s1 = mk_var ("s1", type_of s);
val s2 = mk_var ("s2", type_of s);

Theorem compile_exps_evaluate:
  (!env1 ^s1 xs t1 r1 i ys N.
    evaluate env1 s1 xs = (t1, r1) /\
    compile_exps xs = (i, ys) /\
    r1 <> Rerr (Rabort Rtype_error)
    ==>
    !env2 s2. env_rel N env1 env2 /\ state_rel s1 s2 /\ i < N
    ==>
    ?t2 r2.
      result_rel (LIST_REL v_rel) v_rel r1 r2 /\
      state_rel t1 t2 /\
      evaluate env2 s2 ys = (t2, r2)) /\
  (!env1 ^s1 v ps err_v t1 r1 i ps2 N.
    evaluate_match env1 s1 v ps err_v = (t1, r1) /\
    compile_match ps = (i, ps2) /\
    r1 <> Rerr (Rabort Rtype_error)
    ==>
    !env2 s2 v2 err_v2.
    env_rel N env1 env2 /\
    state_rel s1 s2 /\
    v_rel v v2 /\
    i < N
    ==>
    ?t2 r2.
      result_rel (LIST_REL v_rel) v_rel r1 r2 /\
      state_rel t1 t2 /\
      evaluate_match env2 s2 v2 ps2 err_v2 = (t2, r2))
Proof
  ho_match_mp_tac evaluate_ind
  \\ simp [evaluate_def, compile_exps_def]
  \\ rpt (gen_tac ORELSE disch_tac ORELSE conj_tac)
  \\ simp [v_rel_rules]
  \\ fs [pair_case_eq] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
  \\ rveq \\ fs [evaluate_def, v_rel_rules, GSYM PULL_FORALL]
  \\ TRY (imp_res_tac state_rel_IMP_check_ctor \\ simp [] \\ NO_TAC)
  \\ TRY (rename [`rv_1 ≠ Rerr (Rabort Rtype_error) ==> _`]
    \\ (Cases_on `rv_1 = Rerr (Rabort Rtype_error)` >- fs [])
    \\ fs [])
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rpt (first_x_assum drule \\ rw [])
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
  )
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ simp [evaluate_def]
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rpt (first_x_assum drule \\ rw [])
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
  )
  >- (
    simp [evaluate_def, pat_bindings_def, pmatch_def]
    \\ first_x_assum (drule_then drule)
    \\ impl_tac >- (fs [MAX_ADD_LESS])
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum irule
    \\ simp []
    \\ qmatch_asmsub_abbrev_tac `MAX a b + _ < _`
    \\ qexists_tac `MAX a b + 1`
    \\ simp [LESS_MAX_ADD, env_rel_add_enc, env_is_v_fold]
    \\ drule_then irule env_rel_mono
    \\ simp []
  )
  >- (
    imp_res_tac state_rel_IMP_check_ctor
    \\ fs []
    \\ rveq \\ fs []
  )
  >- (
    imp_res_tac state_rel_IMP_check_ctor
    \\ fs [pair_case_eq] \\ fs []
    \\ fs [GSYM PULL_FORALL]
    \\ rename [`rv_1 ≠ Rerr (Rabort Rtype_error) ==> _`]
    \\ Cases_on `rv_1 = Rerr (Rabort Rtype_error)` \\ fs []
    \\ first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ simp [v_rel_rules]
  )
  >- (
    drule_then drule env_rel_ALOOKUP
    \\ strip_tac \\ fs [optionTheory.OPTREL_def]
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
    \\ fs [case_eq_thms] \\ rveq \\ fs []
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
      \\ first_x_assum irule
      \\ fs [env_rel_def, state_rel_def, dec_clock_def]
      \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ simp []
    )
    \\ fs [option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ drule_then (drule_then drule) do_app_thm_REVERSE
    \\ imp_res_tac state_rel_IMP_check_ctor
    \\ rw []
    \\ fs []
  )
  >- (
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
    \\ first_x_assum irule
    \\ simp []
    \\ asm_exists_tac
    \\ simp []
  )
  >- (
    (* Mat *)
    simp [evaluate_def, pat_bindings_def, pmatch_def]
    \\ first_x_assum (drule_then drule)
    \\ impl_tac >- (fs [MAX_ADD_LESS])
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ fs [libTheory.opt_bind_def]
    \\ first_x_assum irule
    \\ rveq \\ fs []
    \\ imp_res_tac flatPropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ fs [libTheory.opt_bind_def]
    \\ qmatch_asmsub_abbrev_tac `MAX a b + _ < _`
    \\ qexists_tac `MAX a b + 1`
    \\ drule_then (qspec_then `MAX a b + 1` mp_tac) env_rel_mono
    \\ simp [env_rel_def, libTheory.opt_bind_def, nv_rel_LIST_REL,
        name_to_id_to_name, LESS_MAX_ADD]
  )
  >- (
    (* Let *)
    first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum irule
    \\ simp []
    \\ asm_exists_tac
    \\ fs [env_rel_def, libTheory.opt_bind_def]
    \\ CASE_TAC \\ simp []
    \\ imp_res_tac evaluate_sing
    \\ rveq \\ fs []
    \\ fs [nv_rel_LIST_REL]
  )
  >- (
    fs [bool_case_eq]
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [MAP_MAP_o, o_DEF, UNCURRY, ETA_THM]
    \\ first_x_assum irule
    \\ simp []
    \\ qexists_tac `N`
    \\ fs [build_rec_env_eq_MAP, env_rel_def, nv_rel_LIST_REL, FILTER_APPEND]
    \\ irule LIST_REL_APPEND_suff
    \\ simp [UNCURRY, MAP_MAP_o, o_DEF]
    \\ simp [FILTER_MAP, o_DEF, UNCURRY, LIST_REL_MAP1,
        LIST_REL_MAP2 |> CONV_RULE (DEPTH_CONV ETA_CONV)]
    \\ irule listTheory.EVERY2_refl
    \\ rw []
    \\ simp [Once v_rel_cases]
    \\ qexists_tac `N`
    \\ fs [ELIM_UNCURRY, list_max_LESS, EVERY_MAP, nv_rel_LIST_REL]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac MONO_EVERY)
    \\ simp []
  )
  >- (
    fs [state_rel_def]
  )
  >- (
    fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [CaseEq "match_result"] \\ rveq \\ fs []
    (* cases divide *)
    \\ drule (CONJUNCT1 pmatch_thm)
    \\ simp []
    \\ rpt (disch_then drule)
    \\ rpt (first_x_assum (drule_then strip_assume_tac))
    \\ disch_then (qspecl_then [`N`, `[]`] mp_tac)
    \\ simp [nv_rel_LIST_REL]
    (* easy case done *)
    \\ qmatch_goalsub_abbrev_tac `match_rel _ _ mr` \\ Cases_on `mr`
    \\ fs[markerTheory.Abbrev_def, Q.ISPEC `Match a` EQ_SYM_EQ]
    \\ rw [match_rel_def]
    \\ first_x_assum irule
    \\ fs [env_rel_def, nv_rel_LIST_REL]
    \\ asm_exists_tac
    \\ simp [FILTER_APPEND]
    \\ irule LIST_REL_APPEND_suff
    \\ simp []
  )
QED

Theorem pat1_size:
  pat1_size xs = LENGTH xs + SUM (MAP pat_size xs)
Proof
  Induct_on `xs` \\ simp [pat_size_def]
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

Definition extra_pat_bindings_def:
  extra_pat_bindings t [] = [] /\
  extra_pat_bindings t ((Pany, _) :: m) = extra_pat_bindings t m /\
  extra_pat_bindings t ((Pvar s, x) :: m) = (s, x) :: extra_pat_bindings t m /\
  extra_pat_bindings t ((Plit _, _) :: m) = extra_pat_bindings t m /\
  extra_pat_bindings t ((Pcon stmp ps, x) :: m) =
  extra_pat_bindings t (MAPi (\i p. (p, App t (El i) [x])) ps ++ m) /\
  extra_pat_bindings t ((Pref p, x) :: m) =
  extra_pat_bindings t ((p, App t Opderef [x]) :: m)
Termination
  WF_REL_TAC `measure (\(t, m). pat1_size (MAP FST m))`
  \\ simp [pat_size_def]
  \\ simp [pat1_size, SUM_APPEND, o_DEF, MAPi_eq_MAP]
End

Theorem extra_pat_bindings_append:
  !t xs. extra_pat_bindings t (xs ++ ys) =
  extra_pat_bindings t xs ++ extra_pat_bindings t ys
Proof
  ho_match_mp_tac extra_pat_bindings_ind
  \\ simp [extra_pat_bindings_def]
QED

Theorem extra_pat_bindings_cons =
  extra_pat_bindings_append |> Q.SPECL [`t`, `[x]`] |> SIMP_RULE list_ss []

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
    (insert k () spt, Let t (SOME nm) (App t Opderef [x]) exp2))
Termination
  WF_REL_TAC `measure (\(t, i, m, exp). SUM (MAP (pat_size o FST) m) + LENGTH m)`
  \\ simp [pat_size_def]
  \\ rw [MAP_MAP_o, o_DEF, UNCURRY, SUM_APPEND, pat1_size]
  \\ simp [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP]
End

Definition pure_eval_to_def:
  pure_eval_to s env exp v = (evaluate env s [exp] = (s, Rval [v]))
End

Definition simple_env_rel_def:
  simple_env_rel P env env2 = (
    FILTER (\x. P (dec_name_to_num (FST x))) env.v =
    FILTER (\x. P (dec_name_to_num (FST x))) env2.v)
End

Theorem simple_env_rel_refl:
  simple_env_rel P env env
Proof
  simp [simple_env_rel_def]
QED

Theorem simple_env_rel_cons_discarded:
  ~ P (dec_name_to_num (FST v1)) ==>
  simple_env_rel P env <| v := v1 :: vs |> =
  simple_env_rel P env <| v := vs |> /\
  simple_env_rel P <| v := v1 :: vs |> env =
  simple_env_rel P <| v := vs |> env
Proof
  simp [simple_env_rel_def]
QED

Theorem pmatch_list_append:
  !xs vs pre_bindings. pmatch_list s (xs ++ ys) vs pre_bindings =
  (case pmatch_list s xs (TAKE (LENGTH xs) vs) pre_bindings of
      No_match => No_match
    | Match_type_error => Match_type_error
    | Match bindings => pmatch_list s ys (DROP (LENGTH xs) vs) bindings)
Proof
  Induct
  \\ simp [pmatch_def]
  \\ gen_tac \\ Cases
  \\ simp [pmatch_def]
  \\ rw []
  \\ every_case_tac \\ simp []
QED

Theorem pmatch_list_eq_append:
  LENGTH vs1 = LENGTH ps1 ==>
  (case pmatch_list s ps1 vs1 pre_bindings of
      No_match => No_match
    | Match_type_error => Match_type_error
    | Match bindings => pmatch_list s ps2 vs2 bindings) =
  pmatch_list s (ps1 ++ ps2) (vs1 ++ vs2) pre_bindings
Proof
  simp [pmatch_list_append, TAKE_APPEND, DROP_APPEND]
  \\ simp [TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG]
QED

Theorem pat_bindings_evaluate_FOLDR_lemma1:
  !xs.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    FILTER (\x. FST x ∉ new_names) env2.v =
    FILTER (\x. FST x ∉ new_names) env.v ==>
    evaluate env2 s [g x] = (s, Rval [rv])))
  ==>
  !env2.
  FILTER (\x. FST x ∉ new_names) env2.v =
  FILTER (\x. FST x ∉ new_names) env.v ==>
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
  \\ simp [libTheory.opt_bind_def]
  \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem pat_bindings_evaluate_FOLDR_lemma:
  !new_names.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    FILTER (\x. FST x ∉ new_names) env2.v =
    FILTER (\x. FST x ∉ new_names) env.v ==>
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
  \\ simp []
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
  FILTER P xs = ys /\ (!z. P (x, z)) ==>
  ALOOKUP xs x = ALOOKUP ys x
Proof
  cheat
QED

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

(* ok, naming. the existing names in the program (the original x and exp)
   are < j for starting val j. during the recursion, j increases to i, with
   new names i < nm < j appearing in the new env, and in *expressions* in
   n_bindings. note *names* in n_bindings/pre_bindings come from the original
   program. also new/old names mix in env, thus the many filters. *)

(* TODO: why are the initial simplification steps so slow? *)

Theorem compile_pat_bindings_simulation_proof:
  ! t i n_bindings exp exp2 spt s vs pre_bindings bindings env s2 res.
  compile_pat_bindings t i n_bindings exp = (spt, exp2) /\
  pmatch_list s (MAP FST n_bindings) vs pre_bindings = Match bindings /\
  LIST_REL (\(_, k, exp) v. !env2. k ∈ domain spt /\
        FILTER ((\k. k > j /\ k < i) o dec_name_to_num o FST) env2.v =
        FILTER ((\k. k > j /\ k < i) o dec_name_to_num o FST) env.v ==>
        pure_eval_to s env2 exp v)
    n_bindings vs /\
  EVERY ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
  j < i /\
  FILTER ((\k. k < j) o dec_name_to_num o FST) env.v =
  pre_bindings ++ base_vs /\
  (!env2. FILTER ((\k. k < j) o dec_name_to_num o FST) env2.v =
    bindings ++ base_vs ==>
    evaluate env2 s [exp] = (s2, res)) /\
  ~ s.check_ctor /\
  EVERY (\(p, k, _). EVERY (\nm. dec_name_to_num nm < j) (pat_bindings p []) /\
        j < k /\ k < i) n_bindings
  ==>
  evaluate env s [exp2] = (s2, res)
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rpt conj_tac
  \\ simp [compile_pat_bindings_def, pmatch_def, PULL_EXISTS]
  \\ rw []
  >- (
    metis_tac []
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ simp [evaluate_def]
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [pure_eval_to_def]
    \\ rw []
    \\ fs [pat_bindings_def]
    \\ last_x_assum drule
    \\ simp []
    \\ disch_then irule
    \\ simp [libTheory.opt_bind_def]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD]
  )
  >- (
    qmatch_asmsub_abbrev_tac `pmatch _ (Plit l) lv`
    \\ Cases_on `lv` \\ fs [pmatch_def]
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ rw []
    \\ metis_tac []
  )
  >- (
    (* Pcon *)
    qmatch_asmsub_abbrev_tac `pmatch _ (Pcon stmp _) con_v`
    \\ Cases_on `case con_v of Conv cstmp _ => cstmp | _ => NONE`
    \\ Cases_on `con_v` \\ Cases_on `stmp` \\ fs [pmatch_def]
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ rw []
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [MAP_MAP_o |> REWRITE_RULE [o_DEF], UNCURRY, Q.ISPEC `SND` ETA_THM]
    \\ fs [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP,
        pmatch_list_eq_append]
    \\ simp [ELIM_UNCURRY]
    \\ DEP_REWRITE_TAC [pat_bindings_evaluate_FOLDR_lemma]
    \\ simp []
    \\ conj_tac >- (
      qexists_tac `{x | ~ (dec_name_to_num x < i)}`
      \\ simp [SUBSET_DEF, MEM_FILTER, MEM_MAPi, PULL_EXISTS]
      \\ simp [name_to_id_to_name]
      \\ simp [evaluate_def]
      \\ rw [IS_SOME_EXISTS]
      \\ rename [`n < LENGTH con_v_xs`]
      \\ qexists_tac `EL n con_v_xs`
      \\ rw []
      \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [PULL_EXISTS, NULL_FILTER, MEM_MAPi]
      \\ asm_exists_tac \\ simp []
      \\ simp [pure_eval_to_def]
      \\ disch_then (fn t => DEP_REWRITE_TAC [t])
      \\ simp [do_app_def]
      \\ drule_then irule FILTER_EQ_MONO
      \\ simp []
    )
    \\ last_x_assum (drule_then irule)
    \\ simp [FILTER_APPEND, FILTER_EQ_NIL, EVERY_MAP, EVERY_REVERSE,
        EVERY_FILTER, MAPi_enumerate_MAP, UNCURRY, name_to_id_to_name]
    \\ fs [pat_bindings_def, pats_bindings_FLAT_MAP, EVERY_FLAT, EVERY_REVERSE]
    \\ fs [EVERY_EL, FORALL_PROD, UNCURRY]
    \\ rpt conj_tac
    \\ rw [LENGTH_enumerate, EL_enumerate] \\ res_tac \\ simp [] \\ fs [EL_MAP]
    \\ irule LIST_REL_APPEND_suff
    \\ conj_tac
    >- (
      (* new elements *)
      simp [LIST_REL_EL_EQN, LENGTH_enumerate, EL_enumerate, EL_MAP]
      \\ simp [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ rw []
      \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [NULL_FILTER, MEM_MAPi, PULL_EXISTS]
      \\ fs [sptreeTheory.domain_lookup]
      \\ asm_exists_tac \\ simp []
      \\ rw [pure_eval_to_def]
      \\ drule FILTER_EQ_ALOOKUP_EQ
      \\ disch_then (fn t => DEP_REWRITE_TAC [t])
      \\ simp [FILTER_MAP, o_DEF, GSYM MAP_REVERSE, UNCURRY, name_to_id_to_name,
            MAP_MAP_o, ALOOKUP_APPEND]
      \\ simp [do_app_def, option_case_eq]
      \\ DEP_REWRITE_TAC [GSYM MEM_ALOOKUP |> Q.SPEC `MAP f zs`]
      \\ simp [MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_enumerate,
            enc_num_to_name_inj, MAP_MAP_o, o_DEF]
      \\ irule ALL_DISTINCT_MAP_INJ
      \\ simp [enc_num_to_name_inj, MEM_FILTER, FORALL_PROD, MEM_enumerate_EL]
      \\ simp [FILTER_ALL_DISTINCT, ALL_DISTINCT_enumerate]
    )
    (* prior env *)
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ simp []
    \\ conj_tac \\ TRY (IF_CASES_TAC \\ simp [] \\ NO_TAC)
    \\ drule_then (fn t => DEP_REWRITE_TAC [t]) FILTER_EQ_MONO_TRANS
    \\ simp [MEM_FILTER, FILTER_APPEND, FILTER_FILTER]
    \\ simp [FILTER_MAP, FILTER_REVERSE, o_DEF, UNCURRY, name_to_id_to_name]
    \\ csimp [FILTER_EQ]
  )
  >- (
    qpat_x_assum `_ = Match _` mp_tac
    \\ qmatch_goalsub_abbrev_tac `pmatch _ (Pref _) ref_v`
    \\ Cases_on `ref_v` \\ simp [pmatch_def]
    \\ rw [CaseEq "match_result", option_case_eq, CaseEq "store_v"]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [evaluate_def, pure_eval_to_def, do_app_def]
    \\ rw []
    \\ last_x_assum match_mp_tac
    \\ simp [CaseEq "match_result", PULL_EXISTS]
    \\ asm_exists_tac \\ simp []
    \\ asm_exists_tac \\ simp []
    \\ fs [libTheory.opt_bind_def, pat_bindings_def]
    \\ simp [name_to_id_to_name]
    \\ rpt conj_tac
    >- (
      rw [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ drule FILTER_EQ_ALOOKUP_EQ
      \\ disch_then (fn t => DEP_REWRITE_TAC [t])
      \\ simp [name_to_id_to_name]
    )
    >- (
      first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
      \\ simp [FORALL_PROD]
      \\ rw []
      \\ first_x_assum irule
      \\ simp []
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) FILTER_EQ_MONO_TRANS
      \\ simp [name_to_id_to_name, FILTER_FILTER]
      \\ csimp [FILTER_EQ]
    )
    >- (
      fs [EVERY_MEM, FORALL_PROD]
      \\ rw [] \\ res_tac \\ simp []
    )
  )
QED

Theorem compile_pat_bindings_simulation:
  ! t i exp exp2 spt s p v bindings env s2 res.
  compile_pat_bindings t (i + 2)
    [(p, i + 1, Var_local t (enc_num_to_name (i + 1) []))] exp = (spt, exp2) /\
  pmatch s p v [] = Match bindings /\
  (!ext_env. FILTER ((\k. k < i) o dec_name_to_num o FST) ext_env.v =
    bindings ++ FILTER ((\k. k < i) o dec_name_to_num o FST) base_v ==>
    evaluate ext_env s [exp] = (s2, res)) /\
  ~ s.check_ctor /\
  EVERY (\nm. dec_name_to_num nm < i) (pat_bindings p []) /\
  env.v = (enc_num_to_name (i + 1) [], v) :: base_v
  ==>
  evaluate env s [exp2] = (s2, res)
Proof
  rw []
  \\ drule_then match_mp_tac compile_pat_bindings_simulation_induct
  \\ simp [name_to_id_to_name, PULL_EXISTS]
  \\ simp [pmatch_def]
  \\ GEN_EXISTS_TAC "j" `i`
  \\ simp [CaseEq "match_result", PULL_EXISTS]
  \\ asm_exists_tac \\ simp []
  \\ simp [pure_eval_to_def, evaluate_def]
  \\ rw [option_case_eq]
  \\ drule FILTER_EQ_ALOOKUP_EQ
  \\ disch_then (fn t => DEP_REWRITE_TAC [t])
  \\ simp [name_to_id_to_name]
QED

Theorem MAPi_eq_ZIP_left:
  MAPi (\n x. (x, f n)) xs = ZIP (xs, GENLIST f (LENGTH xs))
Proof
  irule listTheory.LIST_EQ \\ simp [EL_ZIP]
QED


val _ = export_theory()
