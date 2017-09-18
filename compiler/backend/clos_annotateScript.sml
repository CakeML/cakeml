open preamble closLangTheory db_varsTheory;

val _ = new_theory "clos_annotate";
val _ = set_grammar_ancestry ["closLang","db_vars"]

(* free calculates free variable annotations, and replaces unused lets with dummies *)

val const_0_def = Define `
  const_0 t = Op t (Const 0) []`;

val no_overlap_def = Define `
  (no_overlap 0 l <=> T) /\
  (no_overlap (SUC n) l <=>
     if has_var n l then F else no_overlap n l)`

val free_def = tDefine "free" `
  (free [] = ([],Empty)) /\
  (free ((x:closLang$exp)::y::xs) =
     let (c1,l1) = free [x] in
     let (c2,l2) = free (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (free [Var t v] = ([Var t v], Var v)) /\
  (free [If t x1 x2 x3] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
     let (c3,l3) = free [x3] in
       ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (free [Let t xs x2] =
     let m = LENGTH xs in
     let (c2,l2) = free [x2] in
       if no_overlap m l2 /\ EVERY pure xs then
         ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
       else
         let (c1,l1) = free xs in
           ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (free [Raise t x1] =
     let (c1,l1) = free [x1] in
       ([Raise t (HD c1)],l1)) /\
  (free [Tick t x1] =
     let (c1,l1) = free [x1] in
       ([Tick t (HD c1)],l1)) /\
  (free [Op t op xs] =
     let (c1,l1) = free xs in
       ([Op t op c1],l1)) /\
  (free [App t loc_opt x1 xs2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free xs2 in
       ([App t loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (free [Fn t loc _ num_args x1] =
     let (c1,l1) = free [x1] in
     let l2 = Shift num_args l1 in
       ([Fn t loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
  (free [Letrec t loc _ fns x1] =
     let m = LENGTH fns in
     let (c2,l2) = free [x1] in
       if no_overlap m l2 then
         ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
       else
     let res = MAP (\(n,x). let (c,l) = free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
       ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (free [Handle t x1 x2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
       ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (free [Call t ticks dest xs] =
     let (c1,l1) = free xs in
       ([Call t ticks dest c1],l1))`
 (WF_REL_TAC `measure exp3_size`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp1_size_lemma \\ simp[]
  \\ rename1 `MEM ee xx`
  \\ Induct_on `xx` \\ rpt strip_tac \\ lfs[exp_size_def] \\ res_tac
  \\ simp[]);

val free_ind = theorem "free_ind";

val free_LENGTH_LEMMA = Q.prove(
  `!xs. (case free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ rw [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val free_LENGTH = Q.store_thm("free_LENGTH",
  `!xs ys l. (free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)`,
  REPEAT STRIP_TAC \\ MP_TAC free_LENGTH_LEMMA \\ fs []);

val free_SING = Q.store_thm("free_SING",
  `(free [x] = (ys,l)) ==> ?y. ys = [y]`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]);

val LENGTH_FST_free = Q.store_thm("LENGTH_FST_free",
  `LENGTH (FST (free fns)) = LENGTH fns`,
  Cases_on `free fns` \\ fs [] \\ IMP_RES_TAC free_LENGTH);

val HD_FST_free = Q.store_thm("HD_FST_free",
  `[HD (FST (free [x1]))] = FST (free [x1])`,
  Cases_on `free [x1]` \\ fs []
  \\ imp_res_tac free_SING \\ fs[]);

val free_CONS = Q.store_thm("free_CONS",
  `FST (free (x::xs)) = HD (FST (free [x])) :: FST (free xs)`,
  Cases_on `xs` \\ fs [free_def,SING_HD,LENGTH_FST_free,LET_DEF]
  \\ Cases_on `free [x]` \\ fs []
  \\ Cases_on `free (h::t)` \\ fs [SING_HD]
  \\ IMP_RES_TAC free_SING \\ fs []);

(* shift renames variables to use only those in the annotations *)

val get_var_def = Define `
  get_var m l i v =
    if v < l then v else l + zlookup i (v - l)`;

val shifted_env_def = Define `
  (shifted_env n [] = LN) /\
  (shifted_env n (x::xs) = insert x (n:num) (shifted_env (n+1) xs))`;

val shift_def = tDefine "shift" `
  (shift [] (m:num) (l:num) (i:num num_map) = []) /\
  (shift ((x:closLang$exp)::y::xs) m l i =
     let c1 = shift [x] m l i in
     let c2 = shift (y::xs) m l i in
       (c1 ++ c2:closLang$exp list)) /\
  (shift [Var t v] m l i =
     [Var t (get_var m l i v)]) /\
  (shift [If t x1 x2 x3] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m l i in
     let c3 = shift [x3] m l i in
       ([If t (HD c1) (HD c2) (HD c3)])) /\
  (shift [Let t xs x2] m l i =
     let c1 = shift xs m l i in
     let c2 = shift [x2] m (l + LENGTH xs) i in
       ([Let t c1 (HD c2)])) /\
  (shift [Raise t x1] m l i =
     let (c1) = shift [x1] m l i in
       ([Raise t (HD c1)])) /\
  (shift [Tick t x1] m l i =
     let c1 = shift [x1] m l i in
       ([Tick t (HD c1)])) /\
  (shift [Op t op xs] m l i =
     let c1 = shift xs m l i in
       ([Op t op c1])) /\
  (shift [App t loc_opt x1 xs2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift xs2 m l i in
       ([App t loc_opt (HD c1) c2])) /\
  (shift [Fn t loc vs_opt num_args x1] m l i =
     let k = m + l in
     let vs = case vs_opt of NONE => [] | SOME vs => vs in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = shift [x1] k num_args (shifted_env 0 live) in
       ([Fn t loc (SOME vars) num_args (HD c1)])) /\
  (shift [Letrec t loc vsopt fns x1] m l i =
     let vs = case vsopt of NONE => [] | SOME x => x in
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let new_i = shifted_env 0 live in
     let fns_len = LENGTH fns in
     let cs = MAP (\(n,x). let c = shift [x] k (n + fns_len) new_i in
                             (n,HD c)) fns in
     let c1 = shift [x1] m (l + LENGTH fns) i in
       ([Letrec t loc (SOME vars) cs (HD c1)])) /\
  (shift [Handle t x1 x2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m (l+1) i in
       ([Handle t (HD c1) (HD c2)])) /\
  (shift [Call t ticks dest xs] m l i =
     let c1 = shift xs m l i in
       ([Call t ticks dest c1]))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val shift_ind = theorem "shift_ind";

val shift_LENGTH_LEMMA = Q.store_thm("shift_LENGTH_LEMMA",
  `!xs m l i. LENGTH (shift xs m l i) = LENGTH xs`,
  recInduct shift_ind \\ REPEAT STRIP_TAC
  \\ fs [shift_def,LET_DEF,ADD1,AC ADD_COMM ADD_ASSOC])

val shift_SING = Q.store_thm("shift_SING",
  `!ys. (shift [x] m l i = ys) ==> ?y. ys = [y]`,
  fs [] \\ MP_TAC (Q.SPEC `[x]` shift_LENGTH_LEMMA |> SPEC_ALL)
  \\ Cases_on `shift [x] m l i` \\ fs [LENGTH_NIL])
  |> SIMP_RULE std_ss [];

val shift_CONS = Q.store_thm("shift_CONS",
  `shift ((x:closLang$exp)::xs) m l i =
      let c1 = shift [x] m l i in
      let c2 = shift xs m l i in
        (HD c1 :: c2:closLang$exp list)`,
  Cases_on `xs` \\ fs [shift_def,LET_DEF,SING_HD,shift_LENGTH_LEMMA]);

val HD_shift = Q.store_thm("HD_shift[simp]",
  `[HD (shift [x] m l i)] = shift [x] m l i`,
  STRIP_ASSUME_TAC shift_SING \\ fs []);

(* main functions *)

val annotate_def = Define `
  annotate arity xs = shift (FST (free xs)) 0 arity LN`;

val compile_def = Define `
  compile prog =
    MAP (λ(n,args,exp). (n,args, HD (annotate args [exp]))) prog`

val _ = export_theory();
