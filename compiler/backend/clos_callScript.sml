(*
  This compiler phase moves code from closures into a separate code
  table and tries to change calls to known closures into fast C-style
  function calls.
*)
open preamble closLangTheory db_varsTheory;

val _ = new_theory "clos_call";

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
     let (c1,l1) = free xs in
     let (c2,l2) = free [x2] in
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
     let res = MAP (\(n,x). let (c,l) = free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
     let (c2,l2) = free [x1] in
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
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val free_ind = theorem "free_ind";

val free_LENGTH_LEMMA = Q.prove(
  `!xs. (case free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

Theorem free_LENGTH:
   !xs ys l. (free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC free_LENGTH_LEMMA \\ fs []
QED

Theorem free_SING:
   (free [x] = (ys,l)) ==> ?y. ys = [y]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_FST_free:
   LENGTH (FST (free fns)) = LENGTH fns
Proof
  Cases_on `free fns` \\ fs [] \\ IMP_RES_TAC free_LENGTH
QED

Theorem HD_FST_free:
   [HD (FST (free [x1]))] = FST (free [x1])
Proof
  Cases_on `free [x1]` \\ fs []
  \\ imp_res_tac free_SING \\ fs[]
QED

Theorem free_CONS:
   FST (free (x::xs)) = HD (FST (free [x])) :: FST (free xs)
Proof
  Cases_on `xs` \\ fs [free_def,SING_HD,LENGTH_FST_free,LET_DEF]
  \\ Cases_on `free [x]` \\ fs []
  \\ Cases_on `free (h::t)` \\ fs [SING_HD]
\\ IMP_RES_TAC free_SING \\ fs []
QED
val closed_def = Define `
  closed x = isEmpty (db_to_set (SND (free [x])))`

val EL_MEM_LEMMA = Q.prove(
  `!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs`,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);

val insert_each_def = Define `
  (insert_each p 0 g = g) /\
  (insert_each p (SUC n) (g1,g2) = insert_each (p+2) n (insert p () g1,g2))`

val code_list_def = Define `
  (code_list loc [] g = g) /\
  (code_list loc ((n,p)::xs) (g1,g2) =
     code_list (loc+2n) xs (g1,(loc+1,n,p)::g2))`

val GENLIST_Var_def = Define `
  GENLIST_Var t i n =
    if n = 0 then [] else
      GENLIST_Var t (i+1) (n-1:num) ++ [Var (t § i) (n-1)]`;

val calls_list_def = Define `
  (calls_list t i loc [] = []) /\
  (calls_list t i loc ((n,_)::xs) =
     (n,Call (t§i§0) 0 (loc+1) (GENLIST_Var (t§i) 1 n))::
          calls_list t (i+1) (loc+2n) xs)`;

val exp3_size_MAP_SND = Q.prove(
  `!fns. exp3_size (MAP SND fns) <= exp1_size fns`,
  Induct \\ fs [exp_size_def,FORALL_PROD]);

val calls_def = tDefine "calls" `
  (calls [] g = ([],g)) /\
  (calls ((x:closLang$exp)::y::xs) g =
     let (e1,g) = calls [x] g in
     let (e2,g) = calls (y::xs) g in
       (e1 ++ e2,g)) /\
  (calls [Var t v] g =
     ([Var t v],g)) /\
  (calls [If t x1 x2 x3] g =
     let (e1,g) = calls [x1] g in
     let (e2,g) = calls [x2] g in
     let (e3,g) = calls [x3] g in
     let e1 = HD e1 in
     let e2 = HD e2 in
     let e3 = HD e3 in
       ([If t e1 e2 e3],g)) /\
  (calls [Let t xs x2] g =
     let (e1,g) = calls xs g in
     let (e2,g) = calls [x2] g in
     let e2 = HD e2 in
       ([Let t e1 e2],g)) /\
  (calls [Raise t x1] g =
     let (e1,g) = calls [x1] g in
     let e1 = HD e1 in
       ([Raise t e1],g)) /\
  (calls [Tick t x1] g =
     let (e1,g) = calls [x1] g in
     let e1 = HD e1 in
       ([Tick t e1],g)) /\
  (calls [Handle t x1 x2] g =
     let (e1,g) = calls [x1] g in
     let (e2,g) = calls [x2] g in
     let e1 = HD e1 in
     let e2 = HD e2 in
       ([Handle t e1 e2],g)) /\
  (calls [Call t ticks dest xs] g =
     let (xs,g) = calls xs g in
       ([Call t ticks dest xs],g)) /\
  (calls [Op t op xs] g =
     let (e1,g) = calls xs g in
       ([Op t op e1],g)) /\
  (calls [App t loc_opt x xs] g =
     let (es,g) = calls xs g in
     let (e1,g) = calls [x] g in
     let e1 = HD e1 in
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
       if IS_SOME loc_opt /\ IS_SOME (lookup loc (FST g)) then
         if pure x then ([Call t (LENGTH es) (loc+1) es],g) else
           ([Let (t§0) (SNOC e1 es)
              (Call (t§1) (LENGTH es) (loc+1) (GENLIST_Var t 2 (LENGTH es)))],g)
       else ([App t loc_opt e1 es],g)) /\
  (calls [Fn t loc_opt ws num_args x1] g =
     (* loc_opt ought to be SOME loc, with loc being EVEN *)
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
     let new_g = insert_each loc 1 g in
     let (e1,new_g) = calls [x1] new_g in
     let new_g = (FST new_g,(loc+1,num_args,HD e1)::SND new_g) in
       (* Closedness is checked on the transformed program because
          the calls function can sometimes remove free variables. *)
       if closed (Fn t loc_opt ws num_args (HD e1)) then
         ([Fn (t§0) loc_opt ws num_args
             (Call (t§0§0) 0 (loc+1) (GENLIST_Var (t§0) 1 num_args))],new_g)
       else
         let (e1,g) = calls [x1] g in
           ([Fn t loc_opt ws num_args (HD e1)],g)) /\
  (calls [Letrec t loc_opt ws fns x1] g =
     let loc = (case loc_opt of SOME loc => loc | NONE => 0) in
     let new_g = insert_each loc (LENGTH fns) g in
     let (fns1,new_g) = calls (MAP SND fns) new_g in
       if EVERY2 (\(n,_) p. closed (Fn t NONE NONE n p)) fns fns1 then
         let new_g = code_list loc (ZIP (MAP FST fns,fns1)) new_g in
         let (e1,g) = calls [x1] new_g in
           ([Letrec (t§0) loc_opt ws (calls_list t 1 loc fns) (HD e1)],g)
       else
         let (fns1,g) = calls (MAP SND fns) g in
         let (e1,g) = calls [x1] g in
           ([Letrec t loc_opt ws (ZIP (MAP FST fns,fns1)) (HD e1)],g))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ fs [GSYM NOT_LESS]
  \\ IMP_RES_TAC EL_MEM_LEMMA
  \\ IMP_RES_TAC exp1_size_lemma
  \\ assume_tac (SPEC_ALL exp3_size_MAP_SND)
  \\ DECIDE_TAC);

val compile_def = Define `
  compile F x = (x,(LN,[])) /\
  compile T x = let (xs,g) = calls x (LN,[]) in (xs,g)`

Theorem calls_length:
   ∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ LENGTH ys = LENGTH xs
Proof
  ho_match_mp_tac (fetch "-" "calls_ind")
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
QED

Theorem calls_sing:
   ∀x g0 ys g. calls [x] g0 = (ys,g) ⇒ ?y. ys = [y]
Proof
  rw [] \\ imp_res_tac calls_length \\ fs []
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]
QED

Theorem compile_LENGTH:
   compile x y = (a,b) ⇒ LENGTH y = LENGTH a
Proof
  Cases_on`x` \\ rw[compile_def] \\ pairarg_tac \\ fs[]
  \\ imp_res_tac calls_length \\ rw[]
QED

Theorem compile_nil:
   clos_call$compile x [] = (a,g,b) ⇒ a =[] ∧ g = LN ∧ b = []
Proof
  Cases_on`x` \\ rw[compile_def]
  \\ pairarg_tac \\ fs[] \\ fs[calls_def] \\ rw[]
QED

val selftest = let
  (* example code *)
  val f = ``Fn None (SOME 800) NONE 1 (Op None Add [Var None 0; Op None (Const 1) []])``
  val g = ``Fn None (SOME 900) NONE 1 (App None (SOME 800) (Var None 1) [Var None 0])``
  val f_g_5 = ``App None (SOME 800) (Var None 1) [App None (SOME 900) (Var None 0) [Op None (Const 5) []]]``
  val let_let = ``[Let None [^f] (Let None [^g] ^f_g_5)]``
  (* compiler evaluation *)
  val tm = EVAL ``compile T ^let_let`` |> concl
  val n = tm |> find_terms (aconv ``closLang$Call``) |> length
  val _ = (n = 5) orelse failwith "clos_call implementation broken"
  in tm end

val _ = export_theory();
