open preamble closLangTheory clos_freeTheory;

val _ = new_theory "clos_call";

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
             (Call (t§1) 0 (loc+1) (GENLIST_Var t 2 num_args))],new_g)
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
  compile F x = (x,[]) /\
  compile T x = let (xs,g) = calls [x] (LN,[]) in (HD xs,SND g)`

val calls_length = Q.store_thm("calls_length",
  `∀xs g0 ys g. calls xs g0 = (ys,g) ⇒ LENGTH ys = LENGTH xs`,
  ho_match_mp_tac (fetch "-" "calls_ind")
  \\ rw[calls_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]);

val calls_sing = Q.store_thm("calls_sing",
  `∀x g0 ys g. calls [x] g0 = (ys,g) ⇒ ?y. ys = [y]`,
  rw [] \\ imp_res_tac calls_length \\ fs []
  \\ Cases_on `ys` \\ fs [LENGTH_NIL] );

val selftest = let
  (* example code *)
  val f = ``Fn Empty (SOME 800) NONE 1 (Op Empty Add [Var Empty 0; Op Empty (Const 1) []])``
  val g = ``Fn Empty (SOME 900) NONE 1 (App Empty (SOME 800) (Var Empty 1) [Var Empty 0])``
  val f_g_5 = ``App Empty (SOME 800) (Var Empty 1) [App Empty (SOME 900) (Var Empty 0) [Op Empty (Const 5) []]]``
  val let_let = ``Let Empty [^f] (Let Empty [^g] ^f_g_5)``
  (* compiler evaluation *)
  val tm = EVAL ``compile T ^let_let`` |> concl
  val n = tm |> find_terms (aconv ``closLang$Call``) |> length
  val _ = (n = 5) orelse failwith "clos_call implementation broken"
  in tm end

val _ = export_theory();
