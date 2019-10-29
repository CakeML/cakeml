(*
  Interface between flatLang and pattern compiler.

  - ensures every case match is on a variable
  - sends case matches to pattern compiler to get a decision tree
  - decodes decision tree to if-tree
  - encodes the variable bindings of each case as let-bindings
*)

open preamble sptreeTheory flatLangTheory pattern_top_levelTheory

val _ = new_theory "flat_pattern";

val _ = set_grammar_ancestry ["misc","flatLang","sptree","pattern_top_level"];

val _ = Datatype `config =
  <| pat_heuristic : pattern_matching$branch list -> num ;
    type_map : (num # num) list spt |>`;

Definition init_type_map_def:
  init_type_map = sptree$fromAList
    [(bool_id, [(0 : num, 0 : num); (1, 0)]);
        (1 (* list_id *), [(0, 0); (0, 2)])]
End

Definition init_config_def:
  init_config ph = <| pat_heuristic := ph; type_map := init_type_map |>
End

Definition sum_string_ords_def:
  sum_string_ords i str = if i < LENGTH str
    then ORD (EL i str) + sum_string_ords (i + 1) str
    else 0
Termination
  WF_REL_TAC `measure (\(i, str). LENGTH str - i)`
End

Definition dec_name_to_num_def:
  dec_name_to_num name = if LENGTH name < 2 then 0
    else if EL 0 name = #"." /\ EL 1 name = #"."
    then sum_string_ords 2 name else 0
End

Definition enc_num_to_name_def:
  enc_num_to_name i xs = if i < 200 then #"." :: #"." :: CHR i :: xs
    else enc_num_to_name (i - 200) (CHR 200 :: xs)
End

Theorem pat1_size:
  flatLang$pat1_size xs = LENGTH xs + SUM (MAP pat_size xs)
Proof
  Induct_on `xs` \\ simp [flatLangTheory.pat_size_def]
QED

Theorem MAPi_eq_MAP:
  MAPi (\n x. f x) xs = MAP f xs
Proof
  Induct_on `xs` \\ simp [o_DEF]
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

Definition naive_pattern_match_def:
  naive_pattern_match t [] = Bool t T /\
  naive_pattern_match t ((flatLang$Pany, _) :: mats) = naive_pattern_match t mats
  /\
  naive_pattern_match t ((Pvar _, _) :: mats) = naive_pattern_match t mats /\
  naive_pattern_match t ((Plit l, v) :: mats) = If t
    (App t Equality [v; Lit t l]) (naive_pattern_match t mats) (Bool t F) /\
  naive_pattern_match t ((Pcon NONE ps, v) :: mats) =
    naive_pattern_match t (MAPi (\i p. (p, App t (El i) [v])) ps ++ mats) /\
  naive_pattern_match t ((Pcon (SOME stmp) ps, v) :: mats) =
    If t (App t (TagLenEq (FST stmp) (LENGTH ps)) [v])
      (naive_pattern_match t (MAPi (\i p. (p, App t (El i) [v])) ps ++ mats))
      (Bool t F)
  /\
  naive_pattern_match t ((Pref p, v) :: mats) =
    naive_pattern_match t ((p, App t (El 0) [v]) :: mats)
Termination
  WF_REL_TAC `measure (\x. SUM (MAP (pat_size o FST) (SND x)) + LENGTH (SND x))`
  \\ simp [flatLangTheory.pat_size_def]
  \\ rw []
  \\ simp [o_DEF, MAPi_eq_MAP, SUM_APPEND, pat1_size]
End

Definition naive_pattern_matches_def:
  naive_pattern_matches t v [] dflt_x = dflt_x /\
  naive_pattern_matches t v ((p, x) :: ps) dflt_x =
  If t (naive_pattern_match t [(p, v)]) x (naive_pattern_matches t v ps dflt_x)
End

Definition compile_pats_def:
  compile_pats cfg naive t i v default_x ps =
  let branches = MAP (compile_pat_rhs t i v) ps in
  if naive then naive_pattern_matches t v (ZIP (MAP FST ps, branches))
    default_x
  else let pats = MAPi (\j (p, _). (encode_pat cfg.type_map p, j)) ps in
  let dt = pattern_top_level$top_level_pat_compile cfg.pat_heuristic pats
  in decode_dtree t branches v default_x dt
End

Definition max_dec_name_def:
  max_dec_name [] = 0 /\
  max_dec_name (nm :: nms) = MAX (dec_name_to_num nm) (max_dec_name nms)
End

Definition op_sets_globals_def:
  op_sets_globals (GlobalVarInit n) = T /\
  op_sets_globals _ = F
End

Theorem op_sets_globals_EX:
  op_sets_globals op = (?n. op = GlobalVarInit n)
Proof
  Cases_on `op` \\ simp [op_sets_globals_def]
QED

Definition compile_exps_def:
  (compile_exps cfg [] = (0, F, [])) /\
  (compile_exps cfg (x::y::xs) =
    let (i, sgx, cx) = compile_exps cfg [x] in
    let (j, sgy, cy) = compile_exps cfg (y::xs) in
    (MAX i j, sgx \/ sgy, HD cx :: cy)) /\
  (compile_exps cfg [Var_local t vid] =
    (dec_name_to_num vid, F, [Var_local t vid])) /\
  (compile_exps cfg [Raise t x] =
    let (i, sg, xs) = compile_exps cfg [x] in
    (i, sg, [Raise t (HD xs)])) /\
  (compile_exps cfg [Handle t x ps] =
    let (i, sgx, xs) = compile_exps cfg [x] in
    let (j, sgp, ps2) = compile_match cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k [] in
    let v = Var_local t nm in
    let r = Raise t v in
    let exp = compile_pats cfg sgp t k v r ps2 in
    (k, sgx \/ sgp, [Handle t (HD xs) [(Pvar nm, exp)]])) /\
  (compile_exps cfg [Con t ts xs] =
    let (i, sg, ys) = compile_exps cfg (REVERSE xs) in
    (i, sg, [Con t ts (REVERSE ys)])) /\
  (compile_exps cfg [Fun t vs x] =
    let (i, sg, xs) = compile_exps cfg [x] in
    (i, sg, [Fun t vs (HD xs)])) /\
  (compile_exps cfg [App t op xs] =
    let (i, sg, ys) = compile_exps cfg (REVERSE xs) in
    (i, sg \/ op_sets_globals op, [App t op (REVERSE ys)])) /\
  (compile_exps cfg [Mat t x ps] =
    let (i, sgx, xs) = compile_exps cfg [x] in
    let (j, sgp, ps2) = compile_match cfg ps in
    let k = MAX i j + 2 in
    let nm = enc_num_to_name k [] in
    let v = Var_local t nm in
    let r = Raise t (Con t (SOME (bind_tag, NONE)) []) in
    let exp = compile_pats cfg sgp t k v r ps2 in
    (k, sgx \/ sgp, [Let t (SOME nm) (HD xs) exp])) /\
  (compile_exps cfg [Let t v x1 x2] =
    let (i, sg1, xs1) = compile_exps cfg [x1] in
    let (j, sg2, xs2) = compile_exps cfg [x2] in
    let k = (case v of NONE => 0 | SOME vid => dec_name_to_num vid) in
    (MAX i (MAX j k), sg1 \/ sg2, [Let t v (HD xs1) (HD xs2)])) /\
  (compile_exps cfg [Letrec t fs x] =
    let ys = MAP (\(a,b,c). (a, b, compile_exps cfg [c])) fs in
    let (i, sgx, xs) = compile_exps cfg [x] in
    let j = list_max (MAP (\(_,_,(j,_,_)). j) ys) in
    let sgfs = EXISTS (\(_,_,(_,sg,_)). sg) ys in
    let fs1 = MAP (\(a,b,(_,_,xs)). (a,b,HD xs)) ys in
    (MAX i j, sgfs \/ sgx, [Letrec t fs1 (HD xs)])) /\
  (compile_exps cfg [If t x1 x2 x3] =
    let (i, sg1, xs1) = compile_exps cfg [x1] in
    let (j, sg2, xs2) = compile_exps cfg [x2] in
    let (k, sg3, xs3) = compile_exps cfg [x3] in
    (MAX i (MAX j k), sg1 \/ sg2 \/ sg3, [If t (HD xs1) (HD xs2) (HD xs3)])) /\
  (compile_exps cfg [exp] = (0, F, [exp])) /\
  (compile_match cfg [] = (0, F, [])) /\
  (compile_match cfg ((p, x)::ps) =
    let (i, sgx, xs) = compile_exps cfg [x] in
    let j = max_dec_name (pat_bindings p []) in
    let (k, sgp, ps2) = compile_match cfg ps in
    (MAX i (MAX j k), sgx \/ sgp, ((p, HD xs) :: ps2)))
Termination
  WF_REL_TAC `measure (\x. case x of INL (_, xs) => exp6_size xs
    | INR (_, ps) => exp3_size ps)`
  \\ rw [flatLangTheory.exp_size_def]
  \\ imp_res_tac flatLangTheory.exp_size_MEM
  \\ fs []
End

Theorem LENGTH_compile_exps_IMP:
  (!cfg xs i sg ys. compile_exps cfg xs = (i, sg, ys) ==>
    LENGTH ys = LENGTH xs) /\
  (!cfg ps i sg ps2. compile_match cfg ps = (i, sg, ps2) ==>
    LENGTH ps2 = LENGTH ps)
Proof
  ho_match_mp_tac compile_exps_ind \\ rw [compile_exps_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Theorem LENGTH_SND_compile_exps:
  LENGTH (SND (SND (compile_exps cfg xs))) = LENGTH xs /\
  LENGTH (SND (SND (compile_match cfg ps))) = LENGTH ps
Proof
  Cases_on `SND (compile_exps cfg xs)` \\ Cases_on `SND (compile_match cfg ps)`
  \\ Cases_on `compile_exps cfg xs` \\ Cases_on `compile_match cfg ps`
  \\ rfs []
  \\ imp_res_tac LENGTH_compile_exps_IMP \\ simp []
QED

Definition compile_dec_def:
  compile_dec cfg (Dlet exp) =
  (cfg, Dlet (HD (SND (SND (compile_exps cfg [exp])))))
  /\
  compile_dec cfg (Dtype tid amap) =
    (let new = FLAT (MAP (\(arity, max). MAP (\i. (i, arity)) (COUNT_LIST max))
                (toAList amap)) in
    (if NULL new then cfg
        else cfg with type_map updated_by (insert tid new), Dtype tid amap)) /\
  compile_dec cfg (Dexn n n') = (cfg, Dexn n n')
End

Definition compile_decs_def:
  (compile_decs cfg [] = (cfg, [])) /\
  (compile_decs cfg (d::ds) =
    let (cfg1, e) = compile_dec cfg d in
    let (cfg2, es) = compile_decs cfg1 ds in
      (cfg2, e::es))
End



val _ = export_theory()

