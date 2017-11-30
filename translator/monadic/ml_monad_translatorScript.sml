open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory Satisfy
open cfHeapsBaseTheory basisFunctionsLib AC_Sort
open determTheory ml_monadBaseTheory ml_monad_translatorBaseTheory
open cfStoreTheory cfTheory cfTacticsLib packLib

val _ = new_theory "ml_monad_translator";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("ex_bind", ``st_ex_bind``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);

val _ = temp_overload_on ("CONTAINER", ``ml_translator$CONTAINER``);

val _ = hide "state";

val HCOND_EXTRACT = cfLetAutoTheory.HCOND_EXTRACT;

val REF_EXISTS_LOC = Q.prove(`(rv ~~> v * H) s ==> ?l. rv = Loc l`,
rw[REF_def, SEP_CLAUSES, SEP_EXISTS_THM, GSYM STAR_ASSOC, HCOND_EXTRACT]);

val ARRAY_EXISTS_LOC  = Q.prove(`(ARRAY rv v * H) s ==> ?l. rv = Loc l`,
rw[STAR_def, SEP_EXISTS_THM, SEP_CLAUSES, REF_def, ARRAY_def, cond_def]);

val UNIQUE_CELLS = Q.prove(
`!p s. !l xv xv' H H'. (l ~~>> xv * H) (st2heap p s) /\ (l ~~>> xv' * H') (st2heap p s) ==> xv' = xv`,
rw[] >>
IMP_RES_TAC st2heap_CELL_MEM >>
IMP_RES_TAC store2heap_IN_unique_key);

(* Should be moved *)
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
(* *)

(*********** Comes from cfLetAutoLib.sml ***********************************************)
(* [dest_pure_fact]
   Deconstruct a pure fact (a heap predicate of the form &P) *)
val set_sep_cond_tm = ``set_sep$cond : bool -> hprop``;
fun dest_pure_fact p =
  case (dest_term p) of
  COMB dp =>
    (if same_const set_sep_cond_tm (#1 dp) then (#2 dp)
    else raise (ERR "dest_pure_fact" "Not a pure fact"))
  | _ => raise (ERR "dest_pure_fact" "Not a pure fact");
(***************************************************************************************)

fun PURE_FACTS_FIRST_CONV H =
  let
      val preds = list_dest dest_star H
      val (pfl, hpl) = List.partition (can dest_pure_fact) preds
      val ordered_preds = pfl @ hpl
  in
      if List.null ordered_preds then REFL H
      else
	  let val H' = List.foldl (fn (x, y) => mk_star(y, x)) (List.hd ordered_preds)
				  (List.tl ordered_preds)
          (* For some strange reason, AC_CONV doesn't work *)
          val H_to_norm = STAR_AC_CONV H
	  val norm_to_H' = (SYM(STAR_AC_CONV H') handle UNCHANGED => REFL H')
	  in TRANS H_to_norm norm_to_H'
	  end
  end;

val EXTRACT_PURE_FACTS_CONV =
  (RATOR_CONV PURE_FACTS_FIRST_CONV)
  THENC (SIMP_CONV pure_ss [GSYM STAR_ASSOC])
  THENC (SIMP_CONV pure_ss [HCOND_EXTRACT])
  THENC (SIMP_CONV pure_ss [STAR_ASSOC]);

(* TODO: use EXTRACT_PURE_FACT_CONV to rewrite EXTRACT_PURE_FACTS_TAC *)
fun EXTRACT_PURE_FACTS_TAC (g as (asl, w)) =
  let
      fun is_hprop a = ((dest_comb a |> fst |> type_of) = ``:hprop`` handle HOL_ERR _ => false)
      val hpreds = List.filter is_hprop asl
      val hpreds' = List.map (fst o dest_comb) hpreds
      val hpreds_eqs = mapfilter (PURE_FACTS_FIRST_CONV) hpreds'
  in
      ((fs hpreds_eqs) >> fs[GSYM STAR_ASSOC] >> fs[HCOND_EXTRACT] >> fs[STAR_ASSOC]) g
  end;
(***********************************************************************************************)

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(***)

val evaluate_unique_result = Q.store_thm("evaluate_unique_result",
`!expr env s s1 s2 res1 res2. evaluate F env s expr (s1, res1) ==>
(evaluate F env s expr (s2, res2) <=> (s2 = s1 /\ res2 = res1))`,
rw[] \\ EQ_TAC >-(rw[] \\ IMP_RES_TAC big_exp_determ \\ rw[]) \\ rw[]);

fun evaluate_unique_result_tac (g as (asl, w)) = let
    val asl = List.map ASSUME asl
    val uniques = mapfilter (MATCH_MP evaluate_unique_result) asl
in simp uniques g end;

(*
 * Definition of EvalM
 *)

val EvalM_def = Define `
  EvalM env st exp P H <=>
    !(s:unit state) p. REFS_PRED H st p s  ==>
    !junk.
    ?s2 res st2. evaluate F env (s with refs := s.refs ++ junk) exp (s2,res) /\
    P (st, s) (st2, s2, res) /\ REFS_PRED_FRAME H p (st, s) (st2, s2)`;

(* refinement invariant for ``:('a, 'b, 'c) M`` *)
val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val MONAD_def = Define `
  MONAD (a:'a->v->bool) (b: 'b->v->bool) (x:('refs, 'a, 'b) M)
                                    (state1:'refs,s1:unit state)
                                     (state2:'refs,s2:unit state,
                                      res: (v,v) result) =
    case (x state1, res) of
      ((Success y, st), Rval v) => (st = state2) /\ a y v
    | ((Failure e, st), Rerr (Rraise v)) => (st = state2) /\
                                              b e v
    | _ => F`

(* return *)
val EvalM_return = Q.store_thm("EvalM_return",
  `!H b. Eval env exp (a x) ==>
    EvalM env st exp (MONAD a b (ex_return x)) H`,
  rw[Eval_def,EvalM_def,st_ex_return_def,MONAD_def] \\
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP
                  |> INST_TYPE [``:'ffi``|->``:unit``]) \\
  asm_exists_tac \\ simp[] \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\
  fs[REFS_PRED_FRAME_append]
  );

(* bind *)
val EvalM_bind = Q.store_thm("EvalM_bind",
  `(a1 ==> EvalM env st e1 (MONAD b c (x:('refs, 'b, 'c) M)) H) /\
   (!z v. b z v ==> a2 z ==> EvalM (write name v env) (SND (x st)) e2 (MONAD a c ((f z):('refs, 'a, 'c) M)) H) ==>
   (a1 /\ !z. (CONTAINER(FST(x st) = Success z) ==> a2 z)) ==>
   EvalM env st (Let (SOME name) e1 e2) (MONAD a c (ex_bind x f)) H`,
  rw[EvalM_def,MONAD_def,st_ex_return_def,PULL_EXISTS, CONTAINER_def] \\ fs[] \\
  rw[Once evaluate_cases] \\
  last_x_assum drule \\ rw[] \\
  first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC) \\
  evaluate_unique_result_tac \\
  IMP_RES_TAC REFS_PRED_FRAME_imp \\
  fs[write_def, namespaceTheory.nsOptBind_def, with_same_refs] \\
  reverse(Cases_on`x st` \\ Cases_on`q` \\ Cases_on `res` \\ fs[] \\ rw[])
  >-(Cases_on `e` \\ fs[st_ex_bind_def])
  \\ fs[st_ex_bind_def] \\
  last_x_assum drule \\ rw[] \\
  first_x_assum drule \\ rw[] \\
  first_x_assum(qspec_then `[]` STRIP_ASSUME_TAC) \\
  fs[with_same_refs] \\ evaluate_unique_result_tac \\
  Cases_on `f a' r` \\ Cases_on `res'` \\ Cases_on `q` \\ fs[] \\ rw[] \\
  IMP_RES_TAC REFS_PRED_FRAME_trans \\
  Cases_on `e` \\ fs[])

(* lift pure refinement invariants *)

val _ = type_abbrev("H",``:'a -> 'refs # unit state ->
                                 'refs # unit state # (v,v) result -> bool``);

val PURE_def = Define `
  PURE a (x:'a) (st1:'refs,s1:unit state) (st2,s2,res:(v,v) result) =
    ?v:v junk. (res = Rval v) /\ (st1 = st2) /\ (s2 = s1 with refs := s1.refs ++ junk) /\ a x v`;

val EqSt_def = Define `
EqSt abs st = \x (st1, s1) (st2, s2, res). st = st1 /\ abs x (st1, s1) (st2, s2, res)`;

val Eval_IMP_PURE = Q.store_thm("Eval_IMP_PURE",
  `!H env exp P x. Eval env exp (P x) ==> EvalM env st exp (PURE P x) H`,
  rw[Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP
                  |> INST_TYPE [``:'ffi``|->``:unit``])
  \\ fs[]
  \\ metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append]);

(* function abstraction and application *)

val ArrowP_def = Define `
  (ArrowP : ('refs -> hprop) -> ('a, 'refs) H -> ('b, 'refs) H -> ('a -> 'b) -> v -> bool) H a b f c =
     !x p st1 s1 st2 s2 (res:(v,v) result).
       a x (st1,s1) (st2,s2,res) /\ REFS_PRED H st1 p s1 ==>
       ?junk v env exp.
       (st2 = st1) /\ (s2 = s1 with refs := s1.refs ++ junk) /\
       (res = Rval v) /\ do_opapp [c;v] = SOME (env,exp) /\
       !junk. ?st3 s3 res3.
         evaluate F env (s2 with refs := s2.refs ++ junk) exp (s3,res3) /\
         b (f x) (st1,s1) (st3,s3,res3) /\
         REFS_PRED_FRAME H p (st1, s1) (st3, s3)`;

val ArrowM_def = Define `
(ArrowM : ('refs -> hprop) -> ('a, 'refs) H -> ('b, 'refs) H -> ('a -> 'b, 'refs) H) H a b =
     PURE (ArrowP H a b)`;

(*val _ = add_infix("-M->",400,HOLgrammars.RIGHT)
val _ = overload_on ("-M->",``ArrowM``) *)

val evaluate_list_cases = let
  val lemma = evaluate_cases |> CONJUNCTS |> el 2
  in CONJ (``evaluate_list a5 a6 a7 [] (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma])
          (``evaluate_list a5 a6 a7 (x::xs) (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma]) end

val EvalM_ArrowM = Q.store_thm("EvalM_ArrowM",
  `EvalM env st x1 ((ArrowM H (PURE a) b) f) H ==>
    EvalM env st x2 (PURE a x) H ==>
    EvalM env st (App Opapp [x1;x2]) (b (f x)) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ evaluate_unique_result_tac
  \\ last_x_assum IMP_RES_TAC
  \\ first_x_assum(qspec_then`junk'`strip_assume_tac)
  \\ fs[GSYM AND_IMP_INTRO]
  \\ qpat_x_assum `!p. P` IMP_RES_TAC
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ evaluate_unique_result_tac
  \\ first_x_assum (qspec_then `junk''` STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[] \\ metis_tac[]);

val EvalM_ArrowM_EqSt = Q.store_thm("EvalM_ArrowM_EqSt",
  `EvalM env st x1 ((ArrowM H (EqSt (PURE a) st) b) f) H ==>
    EvalM env st x2 (PURE a x) H ==>
    EvalM env st (App Opapp [x1;x2]) (b (f x)) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ evaluate_unique_result_tac
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`junk'`strip_assume_tac)
  \\ fs[GSYM AND_IMP_INTRO]
  \\ fs[EqSt_def]
  \\ `PURE a x (st,s) (st,s with refs := s.refs ++ ARB,Rval v)`
     by fs[PURE_def, state_component_equality]
  \\ qpat_assum `!p. P` IMP_RES_TAC
  \\ fs[state_component_equality] \\ rw[]
  \\ evaluate_unique_result_tac
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ `PURE a x (st,s) (st,s with refs := s.refs ++ junk'',Rval v)`
     by fs[PURE_def, state_component_equality]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[]);

val EvalM_ArrowM_Eq = Q.store_thm("EvalM_ArrowM_Eq",
  `EvalM env st x1 ((ArrowM H (PURE (Eq a x)) b) f) H ==>
    EvalM env st x2 (PURE a x) H ==>
    EvalM env st (App Opapp [x1;x2]) (b (f x)) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ evaluate_unique_result_tac
  \\ last_x_assum IMP_RES_TAC
  \\ first_x_assum(qspec_then`junk'`strip_assume_tac)
  \\ fs[GSYM AND_IMP_INTRO,Eq_def]
  \\ qpat_x_assum `!p. P` IMP_RES_TAC
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ evaluate_unique_result_tac
  \\ first_x_assum (qspec_then `junk''` STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[] \\ metis_tac[]);

val EvalM_ArrowM_EqSt_Eq = Q.store_thm("EvalM_ArrowM_EqSt_Eq",
  `EvalM env st x1 ((ArrowM H (EqSt (PURE (Eq a x)) st) b) f) H ==>
    EvalM env st x2 (PURE a x) H ==>
    EvalM env st (App Opapp [x1;x2]) (b (f x)) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ evaluate_unique_result_tac
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`junk'`strip_assume_tac)
  \\ fs[GSYM AND_IMP_INTRO]
  \\ fs[EqSt_def]
  \\ `PURE a x (st,s) (st,s with refs := s.refs ++ ARB,Rval v)`
     by fs[PURE_def, state_component_equality]
  \\ qpat_assum `!p. P` IMP_RES_TAC
  \\ fs[state_component_equality] \\ rw[]
  \\ evaluate_unique_result_tac
  \\ `PURE (Eq a x) x (st,s) (st,s with refs := s.refs ++ junk'',Rval v)`
     by fs[PURE_def, Eq_def, state_component_equality]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[]);

val EvalM_Fun = Q.store_thm("EvalM_Fun",
  `(!v x. a x v ==> EvalM (write name v env) n_st body (b (f x)) H) ==>
    EvalM env st (Fun name body) (ArrowM H (EqSt (PURE a) n_st) b f) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[state_component_equality, REFS_PRED_FRAME_append]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ fs[EqSt_def, PURE_def] \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk ++ junk'` STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ SATISFY_TAC);

val EvalM_Fun_Var_intro = Q.store_thm("EvalM_Fun_Var_intro",
  `EvalM cl_env st (Fun n exp) (PURE P f) H ==>
   ∀name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
   EvalM env st (Var (Short name)) (PURE P f) H`,
  rw[EvalM_def, PURE_def, LOOKUP_VAR_def]
  \\ rw[Once evaluate_cases]
  \\ fs[lookup_var_def]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`[]` STRIP_ASSUME_TAC)
  \\ fs[Once evaluate_cases]
  \\ metis_tac[REFS_PRED_FRAME_append]);

val EvalM_Fun_Eq = Q.store_thm("EvalM_Fun_Eq",
  `(!v. a x v ==> EvalM (write name v env) n_st body (b (f x)) H) ==>
    EvalM env st (Fun name body) ((ArrowM H (EqSt (PURE (Eq a x)) n_st) b) f) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ reverse(rw[Once state_component_equality,REFS_PRED_append]) >-(fs[REFS_PRED_FRAME_append])
  \\ rw[Once state_component_equality]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ fs[EqSt_def, PURE_def] \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk ++ junk'` assume_tac)
  \\ fs[]
  \\ SATISFY_TAC);

(* val EvalM_Fun_Eq = Q.store_thm("EvalM_Fun_Eq",
  `(!st v. a x v ==> EvalM (write name v env) st body (b (f x)) H) ==>
    EvalM env st (Fun name body) ((ArrowM H (PURE (Eq a x)) b) f) H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ reverse(rw[Once state_component_equality,REFS_PRED_append]) >-(fs[REFS_PRED_FRAME_append])
  \\ rw[Once state_component_equality]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ PURE_REWRITE_TAC [GSYM APPEND_ASSOC]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk ++ junk'` assume_tac)
  \\ rw[] \\ SATISFY_TAC); *)

(* More proofs *)
val EvalM_Fun_PURE_IMP = Q.store_thm("EvalM_Fun_PURE_IMP",
  `VALID_REFS_PRED H ==>
    (!st. EvalM env st (Fun n exp) (PURE P f) H) ==>
    P f (Closure env n exp)`,
  fs [EvalM_def,PURE_def,PULL_EXISTS,Once evaluate_cases, VALID_REFS_PRED_def]
     \\ rw [] \\ metis_tac[]);

val LOOKUP_VAR_EvalM_ArrowM_IMP = Q.store_thm("LOOKUP_VAR_EvalM_ArrowM_IMP",
  `(!st env. LOOKUP_VAR n env v ==> EvalM env st (Var (Short n)) (ArrowM H a b f) H) ==>
    ArrowP H a b f v`,
  fs [LOOKUP_VAR_def,lookup_var_def,EvalM_def,ArrowP_def,ArrowM_def,PURE_def,AND_IMP_INTRO,
      Once evaluate_cases,PULL_EXISTS, VALID_REFS_PRED_def]
  \\ `nsLookup (<|v := nsBind n v nsEmpty|>).v (Short n) = SOME v` by EVAL_TAC
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[state_component_equality]);

val EvalM_ArrowM_IMP = Q.store_thm("EvalM_ArrowM_IMP",
  `VALID_REFS_PRED H ==>
   (!st. EvalM env st (Var x) ((ArrowM H a b) f) H) ==>
    Eval env (Var x) (ArrowP H a b f)`,
  rw[ArrowM_def,EvalM_def,Eval_def,PURE_def,PULL_EXISTS, VALID_REFS_PRED_def] \\
  first_x_assum drule \\
  disch_then(qspec_then`[]`strip_assume_tac) \\
  fs[Once evaluate_cases] \\
  rw[state_component_equality]);

val EvalM_PURE_EQ = Q.store_thm("EvalM_PURE_EQ",
  `VALID_REFS_PRED H ==>
   (!st. EvalM env st (Fun n exp) (PURE P x) H) = Eval env (Fun n exp) (P x)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_IMP_PURE]
  \\ FULL_SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ fs[VALID_REFS_PRED_def] \\ rw[]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`[]`strip_assume_tac)
  \\ fs[Once evaluate_cases]
  \\ rw[state_component_equality]);

val EvalM_Var_SIMP = Q.store_thm("EvalM_Var_SIMP",
  `EvalM (write n x env) st (Var (Short y)) p H =
    if n = y then EvalM (write n x env) st (Var (Short y)) p H
             else EvalM env st (Var (Short y)) p H`,
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,write_def]);

val EvalM_Var_SIMP_ArrowM = Q.store_thm("EvalM_Var_SIMP_ArrowM",
  `(!st. EvalM (write nv v env) st (Var (Short n)) (ArrowM H a b x) H) =
    if nv = n then ArrowP H a b x v
    else (!st. EvalM env st (Var (Short n)) (ArrowM H a b x) H)`,
  SIMP_TAC std_ss [EvalM_def, ArrowM_def, VALID_REFS_PRED_def]
  \\ SRW_TAC [] []
  >-(
      ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
      \\ ASM_SIMP_TAC (srw_ss()) [write_def]
      \\ EQ_TAC
      >-(
	  fs[PURE_def]
	  \\ rw[ArrowP_def]
	  \\ first_x_assum drule \\ rw[]
	  \\ fs[state_component_equality])
      \\ metis_tac[PURE_def, REFS_PRED_FRAME_append])
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [write_def]);

val EvalM_Recclosure_ALT = Q.store_thm("EvalM_Recclosure_ALT",
`!H funs fname name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        a n v ==>
        EvalM (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM env st (Var (Short fname)) ((ArrowM H (PURE (Eq a n)) b) f) H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ `s2 = s1 with refs := s1.refs ++ junk'` by rw[state_component_equality]
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk' ++ junk''` STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[]);

val EvalM_Recclosure_ALT2 = Q.store_thm("EvalM_Recclosure_ALT2",
`!H funs fname.
     A n_st ==>
     !name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        A st ==>
        a n v ==>
        EvalM (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM env st (Var (Short fname)) ((ArrowM H (EqSt (PURE (Eq a n)) n_st) b) f) H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def, EqSt_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ `s2 = s1 with refs := s1.refs ++ junk'` by rw[state_component_equality]
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk' ++ junk''` STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[]);

val EvalM_Recclosure_ALT3 = Q.store_thm("EvalM_Recclosure_ALT3",
`!H funs fname name body.
     (∀st v.
        A st ==>
        a n v ==>
        EvalM (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     A n_st ==>
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM env st (Var (Short fname)) ((ArrowM H (EqSt (PURE (Eq a n)) n_st) b) f) H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def, EqSt_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ `s2 = s1 with refs := s1.refs ++ junk'` by rw[state_component_equality]
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk' ++ junk''` STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[]);

val EvalM_Recclosure = Q.store_thm("EvalM_Recclosure",
  `!H. (!st v. a n v ==>
         EvalM (write name v (write_rec [(fname,name,body)] env2 env2))
               st body (b (f n)) H) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    EvalM env st (Var (Short fname)) ((ArrowM H (PURE (Eq a n)) b) f) H`,
  GEN_TAC \\ NTAC 2 STRIP_TAC \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ rw[Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,ArrowP_def,PULL_EXISTS]
  \\ ntac 2 (pop_assum mp_tac)
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ fs[state_component_equality]
  \\ reverse(rw[Eq_def,do_opapp_def,Once find_recfun_def,REFS_PRED_append])  >-(fs[REFS_PRED_FRAME_append])
  \\ fs[build_rec_env_def,write_rec_def,FOLDR,write_def]
  \\ METIS_TAC[APPEND_ASSOC]);

val EvalM_Eq_Recclosure = Q.store_thm("EvalM_Eq_Recclosure",
  `LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
    (ArrowP H a b f (Recclosure x1 x2 x3) =
     (!st. EvalM env st (Var (Short name)) (ArrowM H a b f) H))`,
  rw[EvalM_Var_SIMP, EvalM_def, ArrowM_def, LOOKUP_VAR_def, lookup_var_def, PURE_def]
  \\ EQ_TAC
  >-(
      rw[]
      \\ rw[Once evaluate_cases]
      \\ fs[state_component_equality]
      \\ fs[REFS_PRED_FRAME_append])
  \\ fs [AND_IMP_INTRO, Once evaluate_cases,PULL_EXISTS,PULL_FORALL, VALID_REFS_PRED_def]
  \\ simp[state_component_equality]
  \\ simp[ArrowP_def]
  \\ metis_tac[REFS_PRED_FRAME_append]);

val write_rec_one = Q.store_thm("write_rec_one",
  `write_rec [(x,y,z)] env env = write x (Recclosure env [(x,y,z)] x) env`,
  SIMP_TAC std_ss [write_rec_def,write_def,build_rec_env_def,FOLDR]);

val evaluate_Var = Q.prove(
  `evaluate F env s (Var (Short n)) (s',Rval r) <=>
    ?v. lookup_var n env = SOME r ∧ s' = s`,
  fs [Once evaluate_cases] \\ EVAL_TAC \\ fs[EQ_IMP_THM]);

val EvalM_Var = Q.store_thm("EvalM_Var",
  `VALID_REFS_PRED H ==>
   ((!st. EvalM env st (Var (Short n)) (PURE P x) H) <=>
   ?v. lookup_var n env = SOME v /\ P x v)`,
  rw[EvalM_def, PURE_def, VALID_REFS_PRED_def, EQ_IMP_THM]
  >-(
      first_x_assum IMP_RES_TAC
      \\ first_x_assum(qspec_then `[]` STRIP_ASSUME_TAC)
      \\ fs[with_same_refs, evaluate_Var])
  \\ metis_tac[evaluate_Var, REFS_PRED_FRAME_append]);

val EvalM_Var_ArrowP = Q.store_thm("EvalM_Var_ArrowP",
  `(!st. EvalM env st (Var (Short n)) (ArrowM H (PURE a) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP H (PURE a) b x v`,
  rw[EvalM_def]
  \\fs[Once evaluate_cases]
  \\ fs[ArrowP_def, ArrowM_def] \\ rw[]
  \\ fs[LOOKUP_VAR_def, lookup_var_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` strip_assume_tac)
  \\ fs[PURE_def] \\ fs[state_component_equality]
  \\ rw[] \\ fs[ArrowP_def]
  \\ `PURE a x' (st1,s1) (st1,s2,Rval v')`
     by fs[PURE_def,state_component_equality]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[state_component_equality]);

val EvalM_Var_ArrowP_EqSt = Q.store_thm("EvalM_Var_ArrowP_EqSt",
  `(!st. EvalM env st (Var (Short n)) (ArrowM H (EqSt (PURE a) n_st) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP H (EqSt (PURE a) n_st) b x v`,
  rw[EvalM_def]
  \\ fs[Once evaluate_cases]
  \\ fs[ArrowP_def, ArrowM_def] \\ rw[]
  \\ fs[LOOKUP_VAR_def, lookup_var_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` strip_assume_tac)
  \\ fs[Once PURE_def, EqSt_def] \\ fs[state_component_equality]
  \\ rw[] \\ fs[ArrowP_def]
  \\ `PURE a x' (n_st,s1) (n_st,s2,Rval v')`
     by fs[PURE_def,state_component_equality]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[state_component_equality]);

(* Eq simps *)

val EvalM_FUN_FORALL = Q.store_thm("EvalM_FUN_FORALL",
  `(!x. EvalM env st exp (PURE (p x) f) H) ==>
    EvalM env st exp (PURE (FUN_FORALL x. p x) f) H`,
  rw[EvalM_def,PURE_def]
  \\ first_x_assum drule
  \\ simp[PULL_EXISTS,FUN_FORALL]
  \\ strip_tac
  \\ first_assum(qspecl_then[`ARB`,`junk`]strip_assume_tac)
  \\ asm_exists_tac \\ simp[]
  \\ qx_gen_tac`x`
  \\ first_assum(qspecl_then[`x`,`junk`]strip_assume_tac)
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]);

val EvalM_FUN_FORALL_EQ = Q.store_thm("EvalM_FUN_FORALL_EQ",
  `(!x. EvalM env st exp (PURE (p x) f) H) =
    EvalM env st exp (PURE (FUN_FORALL x. p x) f) H`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ fs [EvalM_def,PURE_def,PULL_EXISTS,FUN_FORALL] \\ METIS_TAC []);

val M_FUN_FORALL_PUSH1 = Q.prove(
  `(FUN_FORALL x. ArrowP H a (PURE (b x))) = (ArrowP H a (PURE (FUN_FORALL x. b x)))`,
  rw[FUN_EQ_THM,FUN_FORALL,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ reverse EQ_TAC >- METIS_TAC[] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum IMP_RES_TAC
  \\ first_assum(qspec_then`ARB`strip_assume_tac) \\ fs[]
  \\ fs[state_component_equality]
  \\ qx_gen_tac`junk2`
  \\ first_assum(qspecl_then[`ARB`,`junk2`]strip_assume_tac)
  \\ asm_exists_tac \\ fs[]
  \\ qx_gen_tac`y`
  \\ first_assum(qspecl_then[`y`,`junk2`]strip_assume_tac)
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]) |> GEN_ALL;

val M_FUN_FORALL_PUSH2 = Q.prove(
  `(FUN_FORALL x. ArrowP H ((PURE (a x))) b) =
    (ArrowP H (PURE (FUN_EXISTS x. a x)) b)`,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,PURE_def] \\ METIS_TAC []) |> GEN_ALL;

val M_FUN_FORALL_PUSH3 = Q.prove(
  `(FUN_FORALL st. ArrowP H (EqSt a st) b) =
    (ArrowP H a b)`,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,EqSt_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = Q.prove(
  `(FUN_EXISTS x. Eq a x) = a`,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val M_FUN_QUANT_SIMP = save_thm("M_FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,M_FUN_FORALL_PUSH1,M_FUN_FORALL_PUSH2,M_FUN_FORALL_PUSH3]);

val EvalM_Eq = Q.store_thm("EvalM_Eq",
`EvalM env st exp (PURE a x) H ==> EvalM env st exp (PURE (Eq a x) x) H`,
fs[EvalM_def, PURE_def, Eq_def]);

val ArrowM_EqSt_elim = Q.store_thm("ArrowM_EqSt_elim",
  `(!st_v. EvalM env st exp (ArrowM H (EqSt a st_v) b f) H) ==>
   EvalM env st exp (ArrowM H a b f) H`,
  fs[EvalM_def, ArrowP_def, ArrowM_def]
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum (qspecl_then [`st`, `junk`] strip_assume_tac)
  \\ fs[PURE_def, EqSt_def, ArrowP_def]
  \\ rw[]
  \\ evaluate_unique_result_tac
  \\ qexists_tac `st`
  \\ rw[state_component_equality]
  \\ last_x_assum (qspecl_then [`st1`, `junk`] strip_assume_tac)
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[state_component_equality]
  \\ IMP_RES_TAC evaluate_unique_result \\ rw[]
  \\ fs[state_component_equality] \\ rw[] \\ fs[] \\ rw[]);

val ArrowP_EqSt_elim = Q.store_thm("ArrowP_EqSt_elim",
  `(!st_v. ArrowP H (EqSt a st_v) b f v) ==> ArrowP H a b f v`,
  fs[EqSt_def, ArrowP_def, ArrowM_def] \\ metis_tac[]);

(* otherwise *)

val EvalM_otherwise = Q.store_thm("EvalM_otherwise",
  `!H b n. ((a1 ==> EvalM env st exp1 (MONAD a b x1) H) /\
   (!st i. a2 st ==> EvalM (write n i env) st exp2 (MONAD a b x2) H)) ==>
   (a1 /\ !st'. (CONTAINER(SND(x1 st) = st') ==> a2 st')) ==>
   EvalM env st (Handle exp1 [(Pvar n,exp2)]) (MONAD a b (x1 otherwise x2)) H`,
  SIMP_TAC std_ss [EvalM_def, EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ `a1` by metis_tac[] \\ fs[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ Cases_on `res` THEN1
   (srw_tac[DNF_ss][] >> disj1_tac \\
    asm_exists_tac \\ fs[MONAD_def,otherwise_def] \\
    CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ Q.PAT_X_ASSUM `MONAD xx yy zz t1 t2` MP_TAC
  \\ SIMP_TAC std_ss [Once MONAD_def] \\ STRIP_TAC
  \\ Cases_on `x1 st` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ srw_tac[DNF_ss][] \\ disj2_tac \\ disj1_tac
  \\ asm_exists_tac \\ fs[CONTAINER_def]
  \\ simp[Once evaluate_cases,pat_bindings_def,pmatch_def,GSYM write_def]
  \\ IMP_RES_TAC REFS_PRED_FRAME_imp
  \\ first_x_assum drule \\ disch_then drule
  \\ qmatch_goalsub_rename_tac`write n v`
  \\ disch_then(qspecl_then[`v`,`[]`]strip_assume_tac)
  \\ fs[with_same_refs]
  \\ IMP_RES_TAC REFS_PRED_FRAME_imp
  \\ asm_exists_tac \\ fs[]
  \\ IMP_RES_TAC REFS_PRED_FRAME_trans
  \\ fs[MONAD_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ asm_exists_tac \\ fs[]);

(* if *)

val EvalM_If = Q.store_thm("EvalM_If",
  `!H. (a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> EvalM env st x2 (a b2) H) /\
    (a3 ==> EvalM env st x3 (a b3) H) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM env st (If x1 x2 x3) (a (if b1 then b2 else b3)) H)`,
  rpt strip_tac \\ fs[]
  \\ `∀(H:'a -> hprop). EvalM env st x1 (PURE BOOL b1) H` by metis_tac[Eval_IMP_PURE]
  \\ fs[EvalM_def,PURE_def, BOOL_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then(qspec_then`junk`strip_assume_tac)
  \\ simp[Once evaluate_cases]
  \\ simp_tac(srw_ss()++DNF_ss)[]
  \\ disj1_tac
  \\ asm_exists_tac
  \\ simp[do_if_def]
  \\ rw[]
  \\ first_x_assum (match_mp_tac o MP_CANON)
  \\ fs[ml_translatorTheory.CONTAINER_def]);

val EvalM_Let = Q.store_thm("EvalM_Let",
  `!H. Eval env exp (a res) /\
    (!v. a res v ==> EvalM (write name v env) st body (b (f res)) H) ==>
    EvalM env st (Let (SOME name) exp body) (b (LET f res)) H`,
  rw[]
  \\ imp_res_tac Eval_IMP_PURE
  \\ fs[EvalM_def]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then(qspec_then`junk`strip_assume_tac)
  \\ simp[Once evaluate_cases,GSYM write_def,namespaceTheory.nsOptBind_def]
  \\ srw_tac[DNF_ss][]
  \\ fs[PURE_def] \\ rveq
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ asm_exists_tac \\ fs[]);

(* PMATCH *)

val EvalM_PMATCH_NIL = Q.store_thm("EvalM_PMATCH_NIL",
  `!H b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      EvalM env st (Mat x []) (b (PMATCH xv [])) H`,
  rw[ml_translatorTheory.CONTAINER_def]);

val EvalM_PMATCH = Q.store_thm("EvalM_PMATCH",
  `!H b a x xv.
      ALL_DISTINCT (pat_bindings p []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval env x (a xv) ⇒
      (p1 xv ⇒ EvalM env st (Mat x ys) (b (PMATCH xv yrs)) H) ⇒
      EvalPatRel env a p pat ⇒
      (∀env2 vars.
        EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
        EvalM env2 st e (b (res vars)) H) ⇒
      (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ p2 vars) ∧
      ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ p1 xv) ⇒
      EvalM env st (Mat x ((p,e)::ys))
        (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs))) H`,
  rw[EvalM_def] >>
  imp_res_tac Eval_IMP_PURE >>
  fs[EvalM_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_x_assum drule >>
  disch_then(qspec_then`junk`strip_assume_tac) >>
  fs[PURE_def] \\ rveq \\
  srw_tac[DNF_ss][] \\ disj1_tac \\
  asm_exists_tac \\ fs[] \\
  rw[Once evaluate_cases,PULL_EXISTS] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    qpat_x_assum`p1 xv ⇒ $! _`kall_tac >>
    qpat_x_assum`_ ==> p1 xv`kall_tac >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    fs[PMATCH_ROW_COND_def] \\
    last_x_assum (qspec_then `s.refs ++ junk'` ASSUME_TAC) \\ rw[] \\
    `EvalPatBind env a p pat vars (env with v := nsAppend (alist_to_ns env2) env.v)`
    by (
	simp[EvalPatBind_def,sem_env_component_equality] \\
        qexists_tac `v` >> fs[] >>
      qspecl_then[`s.refs ++ junk'`,`p`,`v`,`[]`,`env`]mp_tac(CONJUNCT1 pmatch_imp_Pmatch) \\
      simp[] \\
      metis_tac[] ) \\
    first_x_assum drule \\ simp[]
    \\ disch_then(qspec_then`s`mp_tac)
    \\ disch_then drule
    \\ disch_then(qspec_then`junk'`strip_assume_tac) \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars) = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >>
    asm_exists_tac \\ fs[]) >>
  drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match)
  \\ disch_then drule \\ disch_then drule
  \\ simp[] \\ strip_tac \\
  first_x_assum(qspec_then`s`mp_tac) \\
  disch_then drule \\
  simp[Once evaluate_cases,PULL_EXISTS] \\
  disch_then(qspec_then`junk`mp_tac) \\
  strip_tac \\ imp_res_tac determTheory.big_exp_determ \\ fs[] \\
  rw[] \\ asm_exists_tac \\ fs[] \\
  fs[PMATCH_def,PMATCH_ROW_def] \\
  asm_exists_tac \\ fs[]);

(* Exception handling *)

val prove_EvalM_handle_tac =
  rw[EvalM_def]
  \\ rw[Once evaluate_cases]
  \\ `a1` by metis_tac[] \\ fs[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[]
  \\ rw[MONAD_def]
  \\ Cases_on `res` >> fs[MONAD_def]
  >> Cases_on `x1 st` >> fs[]
  >> Cases_on `q` >> fs[]
  >> Cases_on `e` >> fs[]
  \\ rw[]
  \\ Cases_on `?e. b = ECons e`
  >-(
      rw[]
      \\ last_x_assum(qspecl_then[`st`, `e`, `r`] IMP_RES_TAC)
      \\ last_x_assum(fn x => ALL_TAC)
      \\ rw[]
      \\ rw[Once evaluate_cases]
      \\ last_x_assum drule \\ rw[]
      \\ last_x_assum(fn x => ALL_TAC)
      \\ rw[]
      \\ fs[pat_bindings_def, pmatch_def]
      \\ fs[lookup_cons_def, same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
      \\ IMP_RES_TAC REFS_PRED_FRAME_imp
      \\ last_x_assum drule \\ rw[] \\ fs[CONTAINER_def]
      \\ last_x_assum (qspec_then `e` strip_assume_tac) \\ fs[]
      \\ first_x_assum drule \\ rw[]
      \\ first_x_assum drule \\ rw[]
      \\ first_x_assum(qspec_then `[]` STRIP_ASSUME_TAC)
      \\ fs[with_same_refs]
      \\ fs[write_def]
      \\ evaluate_unique_result_tac
      \\ Cases_on `x2 e r` >> fs[]
      \\ Cases_on `q` >> fs[]
      \\ Cases_on `res` >> fs[]
      >> IMP_RES_TAC REFS_PRED_FRAME_trans
      >> Cases_on `e'` >> fs[])
  \\ rw[]
  \\ last_x_assum(fn x => ALL_TAC)
  \\ last_x_assum(qspec_then `st` ASSUME_TAC)
  \\ `!e s1. x1 st <> (Failure (ECons e), s1)` by (rw[] \\ DISJ1_TAC \\ fs[])
  \\ qpat_x_assum `P ==> Q` IMP_RES_TAC
  \\ fs[]
  \\ rw[Once evaluate_cases]
  \\ last_x_assum(fn x => ALL_TAC)
  \\ last_x_assum IMP_RES_TAC
  \\ rw[]
  \\ fs[pat_bindings_def, pmatch_def]
  \\ fs[lookup_cons_def, same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[Once evaluate_cases];

val EvalM_handle_MODULE = Q.store_thm("EvalM_handle_MODULE",
 `!cons_name module_name ECons TYPE EXN_TYPE handle_fun H n x1 exp1 x2 exp2 env a.
  (!s e s1. x1 s = (Failure (ECons e), s1) ==> handle_fun x1 x2 s = x2 e s1) ==>
  (!s. (!e s1. x1 s <> (Failure (ECons e), s1)) ==> handle_fun x1 x2 s = x1 s) ==>
  (!e ev. EXN_TYPE (ECons e) ev ==>
   ?ev'.
   ev = Conv (SOME (cons_name,TypeExn (Long module_name (Short cons_name)))) [ev'] /\
   TYPE e ev') ==>
  (!e ev. EXN_TYPE e ev ==>
   (!e'. e <> ECons e') ==>
   ?ev' cons_name_1.
   ev = Conv (SOME (cons_name_1,TypeExn (Long module_name (Short cons_name_1)))) [ev'] /\
   cons_name_1 <> cons_name) ==>
  lookup_cons cons_name env = SOME (1,TypeExn (Long module_name (Short cons_name))) ==>
  ((a1 ==> EvalM env st exp1 (MONAD a EXN_TYPE x1) H) /\
  (!st t v.
     TYPE t v ==>
     a2 st t ==>
     EvalM (write n v env) st exp2 (MONAD a EXN_TYPE (x2 t)) H)) ==>
  (!st' t. a1 /\ (CONTAINER(x1 st = (Failure (ECons t), st')) ==> a2 st' t)) ==>
  EvalM env st (Handle exp1 [(Pcon (SOME (Short cons_name)) [Pvar n],exp2)])
    (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  prove_EvalM_handle_tac);

val EvalM_handle_SIMPLE = Q.store_thm("EvalM_handle_SIMPLE",
 `!cons_name ECons TYPE EXN_TYPE handle_fun H n x1 exp1 x2 exp2 env a.
  (!s e s1. x1 s = (Failure (ECons e), s1) ==> handle_fun x1 x2 s = x2 e s1) ==>
  (!s. (!e s1. x1 s <> (Failure (ECons e), s1)) ==> handle_fun x1 x2 s = x1 s) ==>
  (!e ev. EXN_TYPE (ECons e) ev ==>
   ?ev'.
   ev = Conv (SOME (cons_name,TypeExn (Short cons_name))) [ev'] /\
   TYPE e ev') ==>
  (!e ev. EXN_TYPE e ev ==>
   (!e'. e <> ECons e') ==>
   ?ev' cons_name_1.
   ev = Conv (SOME (cons_name_1,TypeExn (Short cons_name_1))) [ev'] /\
   cons_name_1 <> cons_name) ==>
  lookup_cons cons_name env = SOME (1,TypeExn (Short cons_name)) ==>
  ((a1 ==> EvalM env st exp1 (MONAD a EXN_TYPE x1) H) /\
  (!st t v.
     TYPE t v ==>
     a2 st t ==>
     EvalM (write n v env) st exp2 (MONAD a EXN_TYPE (x2 t)) H)) ==>
  (!st' t. a1 /\ (CONTAINER(x1 st = (Failure (ECons t), st')) ==> a2 st' t)) ==>
  EvalM env st (Handle exp1 [(Pcon (SOME (Short cons_name)) [Pvar n],exp2)])
    (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  prove_EvalM_handle_tac);

(* read and update refs *)

val EvalM_read_heap = Q.store_thm("EvalM_read_heap",
`!vname loc TYPE EXC_TYPE H get_var.
  (nsLookup env.v (Short vname) = SOME loc) ==>
  EvalM env st (App Opderef [Var (Short vname)])
  (MONAD TYPE EXC_TYPE (λrefs. (Success (get_var refs), refs)))
  (λrefs. REF_REL TYPE loc (get_var refs) * H refs)`,
  rw[EvalM_def, REF_REL_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 6 (rw[Once evaluate_cases])
  \\ fs[REFS_PRED_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[do_app_def]
  \\ fs[MONAD_def]
  \\ rw[store_lookup_def,EL_APPEND1,EL_APPEND2]
  >-(
      qexists_tac `s with refs := s.refs ++ junk`
      \\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
      \\ POP_ASSUM (fn x => fs[x])
      \\ fs[with_same_refs, with_same_ffi]
      \\ fs[REFS_PRED_FRAME_append]
  ) >>
  IMP_RES_TAC st2heap_REF_MEM
  \\ IMP_RES_TAC store2heap_IN_LENGTH
  \\ fs[]);

val EvalM_write_heap = Q.store_thm("EvalM_write_heap",
  `!vname loc TYPE PINV EXC_TYPE H get_var set_var x exp env.
  (!refs x. get_var (set_var x refs) = x) ==>
  (!refs x. H (set_var x refs) = H refs) ==>
  nsLookup env.v (Short vname) = SOME loc ==>
  CONTAINER (PINV st ==> PINV (set_var x st)) ==>
  Eval env exp (TYPE x) ==>
  EvalM env st (App Opassign [Var (Short vname); exp])
  ((MONAD UNIT_TYPE EXC_TYPE) (λrefs. (Success (), set_var x refs)))
  (λrefs. REF_REL TYPE loc (get_var refs) * H refs * &PINV refs)`,
  rw[REF_REL_def]
  \\ ASSUME_TAC (Thm.INST_TYPE [``:'a`` |-> ``:'b``, ``:'b`` |-> ``:'a``] Eval_IMP_PURE)
  \\ POP_ASSUM IMP_RES_TAC
  \\ fs[EvalM_def] \\ rw[]
  \\ `?loc'. loc = Loc loc'` by (fs[REFS_PRED_def, SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC] >>
				   IMP_RES_TAC REF_EXISTS_LOC >> rw[])
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 3 (rw[Once(CONJUNCT2 evaluate_cases)])
  \\ rw[CONJUNCT1 evaluate_cases |> Q.SPECL[`F`,`env`,`s`,`Var _`]]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ Q.PAT_X_ASSUM `!H. P` IMP_RES_TAC
  \\ first_x_assum(qspec_then `junk` strip_assume_tac)
  \\ fs[PURE_def, CONTAINER_def] \\ rw[]
  \\ asm_exists_tac \\ fs[]
  \\ fs[do_app_def]
  \\ qexists_tac `Rval (Conv NONE [])`
  \\ qexists_tac `set_var x st`
  \\ qexists_tac `LUPDATE (Refv v) loc' (s.refs ++ junk')`
  \\ qexists_tac `s.ffi`
  \\ IMP_RES_TAC (Thm.INST_TYPE [``:'b`` |-> ``:unit``, ``:'c`` |-> ``:unit``] REFS_PRED_FRAME_imp)
  \\ fs[REFS_PRED_def]
  \\ qpat_x_assum `P (st2heap p s)` (fn x => ALL_TAC)
  \\ fs[store_assign_def,EL_APPEND1,EL_APPEND2,store_v_same_type_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC] \\ IMP_RES_TAC st2heap_REF_MEM
  \\ IMP_RES_TAC store2heap_IN_LENGTH
  \\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
  \\ POP_ASSUM (qspec_then `[]` ASSUME_TAC)
  \\ fs[] \\ POP_ASSUM(fn x => ALL_TAC)
  \\ fs[MONAD_def]
  \\ fs[REFS_PRED_FRAME_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ simp[state_component_equality]
  \\ rpt STRIP_TAC
  \\ qexists_tac `v`
  \\ qpat_x_assum `!F. P` IMP_RES_TAC
  \\ EXTRACT_PURE_FACTS_TAC
  \\ POP_ASSUM (fn x => ASSUME_TAC (CONV_RULE (RATOR_CONV PURE_FACTS_FIRST_CONV) x))
  \\ CONV_TAC (STRIP_QUANT_CONV (RATOR_CONV PURE_FACTS_FIRST_CONV))
  \\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
  \\ fs[LUPDATE_APPEND1,LUPDATE_APPEND2,LUPDATE_def]
  \\ IMP_RES_TAC STATE_UPDATE_HPROP_REF
  \\ last_x_assum(qspec_then `v` ASSUME_TAC)
  \\ fs[with_same_ffi]);

(* Dynamic allocation of references *)

val STATE_REF_def = Define`
STATE_REF A r x = SEP_EXISTS v. REF r v * &A x v`;

val STATE_REFS_def = Define`
STATE_REFS A [] [] = emp /\
STATE_REFS A (r::refs) (x::state) = STATE_REF A r x * STATE_REFS A refs state /\
STATE_REFS A [] (x::state) = &F /\
STATE_REFS A (r::refs) [] = &F`;

val RES_MONAD = Define `RES_MONAD A = MONAD A (\x v. F)`;

val GC_ABSORB_L = Q.prove(`!A B s. (A * B * GC) s ==> (A * GC) s`,
rw[]
\\ fs[GSYM STAR_ASSOC]
\\ fs[Once STAR_def]
\\ qexists_tac `u`
\\ qexists_tac `v`
\\ fs[SAT_GC]);

val GC_ABSORB_R = Q.prove(`!A B s. (A * GC * B) s ==> (A * GC) s`,
rw[]
\\ `A * GC * B = A * B * GC` by metis_tac[STAR_COMM, STAR_ASSOC]
\\ POP_ASSUM(fn x => fs[x])
\\ IMP_RES_TAC GC_ABSORB_L);

(* Validity of a store extension *)
val valid_state_refs_frame_extension = Q.prove(
`!H junk. A (cons x) res ==> (STATE_REFS A ptrs state * H) (st2heap p s) ==>
(STATE_REFS A (Loc (LENGTH (s.refs ++ junk))::ptrs) (cons x::state) * H * GC) (st2heap p (s with refs := s.refs ++ junk ++ [Refv res]))`,
rw[]
\\ rw[Once STATE_REFS_def]
\\ rw[GSYM STAR_ASSOC]
\\ rw[Once STAR_COMM]
\\ rw[STAR_ASSOC]
\\ rw[Once (GSYM STAR_ASSOC)]
\\ rw[Once STAR_def]
\\ qexists_tac `st2heap p s`
\\ qexists_tac `store2heap_aux (LENGTH s.refs) (junk++[Refv res])`
\\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
\\ `st2heap p s = st2heap p (s with refs := s.refs)` by fs[with_same_refs]
\\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
\\ PURE_REWRITE_TAC[STATE_SPLIT_REFS]
\\ rw[with_same_refs]
\\ rw[STAR_def]
\\ qexists_tac `store2heap_aux (LENGTH s.refs) junk`
\\ qexists_tac `store2heap_aux (LENGTH s.refs + LENGTH junk) [Refv res]`
\\ fs[store2heap_aux_SPLIT]
\\ fs[SAT_GC, STATE_REF_def]
\\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
\\ qexists_tac `res`
\\ EXTRACT_PURE_FACTS_TAC
\\ fs[store2heap_aux_def, REF_def, cell_def, one_def]
\\ fs[SEP_EXISTS_THM, HCOND_EXTRACT]
);

val valid_state_refs_extension = Q.prove(
`A (cons x) res ==> REFS_PRED (STATE_REFS A ptrs) refs p s ==>
REFS_PRED (STATE_REFS A (Loc (LENGTH (s.refs ++ junk))::ptrs)) (cons x ::refs) p (s with refs := s.refs ++ junk ++ [Refv res])`,
rw[REFS_PRED_def, REFS_PRED_FRAME_def]
\\ IMP_RES_TAC valid_state_refs_frame_extension
\\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
);

val STATE_REFS_LENGTH = Q.prove(
`!ptrs state H. (STATE_REFS A ptrs state * H) s ==> LENGTH ptrs = LENGTH state`,
Induct
>-(
    rw[STATE_REFS_def]
    >> Cases_on `state`
    >> fs[STATE_REFS_def]
    >> fs[SEP_CLAUSES, SEP_F_def])
\\ rw[]
\\ Cases_on `state`
>-(
    fs[STATE_REFS_def]
    >> fs[STATE_REFS_def]
    >> fs[SEP_CLAUSES, SEP_F_def])
\\ fs[STATE_REFS_def]
\\ fs[GSYM STAR_ASSOC]
\\ POP_ASSUM(fn x => SIMP_RULE bool_ss [Once STAR_COMM] x |> ASSUME_TAC)
\\ fs[GSYM STAR_ASSOC]
\\ last_x_assum IMP_RES_TAC
);

val valid_state_refs_reduction = Q.prove(
`(STATE_REFS A (rv::ptrs) refs * H * GC) s ==> (STATE_REFS A ptrs (TL refs) * H * GC) s`,
rw[]
\\ fs[GSYM STAR_ASSOC]
\\ IMP_RES_TAC STATE_REFS_LENGTH
\\ Cases_on`refs`
\\ fs[]
\\ fs[STATE_REFS_def]
\\ fs[GSYM STAR_ASSOC]
\\ last_x_assum(fn x => SIMP_RULE bool_ss [Once STAR_COMM] x |> ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ IMP_RES_TAC GC_ABSORB_R);

(* Validity of ref_bind *)

val EvalM_ref_bind = Q.store_thm("EvalM_ref_bind",
`Eval env xexpr (A (cons x)) ==>
(!rv r. EvalM (write rname rv env) ((cons x)::st) exp (MONAD TYPE MON_EXN_TYPE (f r)) (STATE_REFS A (rv::ptrs))) ==>
EvalM env st (Let (SOME rname) (App Opref [xexpr]) exp) (MONAD TYPE MON_EXN_TYPE (ref_bind (Mref cons x) f (Mpop_ref e))) (STATE_REFS A ptrs)`,
rw[]
\\ fs[Eval_def]
\\ rw[EvalM_def]
\\ ntac 3 (rw[Once evaluate_cases])
\\ first_x_assum(qspec_then `s.refs ++ junk` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
\\ evaluate_unique_result_tac
\\ rw[evaluate_list_cases]
\\ rw[do_app_def]
\\ rw[store_alloc_def]
\\ rw[namespaceTheory.nsOptBind_def]
\\ fs[write_def]
\\ last_x_assum(qspec_then `Loc (LENGTH junk + (LENGTH refs' + LENGTH s.refs))` ASSUME_TAC)
\\ first_x_assum(qspec_then `StoreRef (LENGTH st)` ASSUME_TAC)
\\ fs[with_same_ffi]
\\ fs[EvalM_def]
\\ first_x_assum(qspecl_then [`s with refs := s.refs ++ junk ++ refs' ++ [Refv res]`, `p`] ASSUME_TAC)
\\ IMP_RES_TAC valid_state_refs_extension
\\ first_x_assum(qspec_then`junk ++ refs'` ASSUME_TAC)
\\ fs[]
\\ first_x_assum(qspec_then`[]` STRIP_ASSUME_TAC)
\\ fs[]
\\ evaluate_unique_result_tac
\\ qexists_tac `s2`
\\ qexists_tac `res'`
\\ fs[]
\\ qexists_tac `TL st2`
\\ fs[REFS_PRED_FRAME_def]
\\ fs[REFS_PRED_def]
\\ rw[]
>-(fs[MONAD_def]
   >> fs[ref_bind_def]
   >> fs[Mref_def]
   >> fs[Mpop_ref_def]
   >> Cases_on `f (StoreRef (LENGTH st)) (cons x::st)`
   >> fs[]
   >> Cases_on `q`
   >> Cases_on `res'`
   >> Cases_on `r`
   >> fs[]
   >> rw[]
   >-(
	qpat_x_assum `!F. P` IMP_RES_TAC
        >> fs[Once STATE_REFS_def]
	>> fs[SEP_CLAUSES, SEP_F_def])
   >-(
	Cases_on `e'`
        >> fs[]
        >> irule FALSITY
	>> qpat_x_assum `!F. P` IMP_RES_TAC
	>> fs[GSYM STAR_ASSOC]
	>> IMP_RES_TAC STATE_REFS_LENGTH
        >> rw[]
	>> fs[LENGTH])
   >> Cases_on `e'`
   >> fs[]
   >> rw[])
\\ simp[state_component_equality]
\\ rpt STRIP_TAC
\\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ qspecl_then [`F'`, `junk++refs'`] IMP_RES_TAC valid_state_refs_frame_extension
\\ ntac 2 (POP_ASSUM(fn x => ALL_TAC))
\\ fs[]
\\ POP_ASSUM(fn x => ALL_TAC)
\\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
\\ fs[STAR_ASSOC]
\\ IMP_RES_TAC valid_state_refs_reduction);

(* Validity of a deref operation *)
val STATE_REFS_EXTRACT = Q.prove(
`!ptrs1 r ptrs2 refs TYPE H p s. ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) ==>
((STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) refs) *
(STATE_REF TYPE r (EL (LENGTH ptrs1) refs)) *
(STATE_REFS TYPE ptrs2 (DROP (LENGTH ptrs1 + 1) refs)) *
H)) (st2heap p s)`,
Induct
>-(
    rw[]
    >> rw[STATE_REFS_def]
    >> rw[SEP_CLAUSES]
    >> rw[GSYM STATE_REFS_def]
    >> IMP_RES_TAC STATE_REFS_LENGTH
    >> Cases_on `refs`
    >> fs[])
\\ rw[]
\\ IMP_RES_TAC STATE_REFS_LENGTH
\\ Cases_on `refs`
\\ fs[]
\\ fs[STATE_REFS_def]
\\ fs[GSYM STAR_ASSOC]
\\ qpat_x_assum `H' (st2heap p s)` (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_COMM] x |> ASSUME_TAC)
\\ rw[Once STAR_COMM]
\\ fs[STAR_ASSOC]
\\ qpat_x_assum `H' (st2heap p s)` (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_ASSOC] x |> ASSUME_TAC)
\\ rw[Once (GSYM STAR_ASSOC)]
\\ last_x_assum IMP_RES_TAC
\\ fs[SUC_ONE_ADD]);

val STATE_REFS_EXTRACT_2 = Q.prove(
`!ptrs1 r ptrs2 refs1 x refs2 TYPE H p s.
LENGTH ptrs1 = LENGTH refs1 ==>
LENGTH ptrs2 = LENGTH refs2 ==>
(STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) (refs1 ++ [x] ++ refs2) * H) (st2heap p s) ==>
(STATE_REFS TYPE ptrs1 refs1 *
STATE_REF TYPE r x *
STATE_REFS TYPE ptrs2 refs2 *
H) (st2heap p s)`,
rw[]
\\ IMP_RES_TAC STATE_REFS_EXTRACT
\\ sg `TAKE (LENGTH ptrs1) (refs1 ++ [x] ++ refs2) = refs1`
>-(
    last_x_assum (fn x => PURE_REWRITE_TAC[x])
    >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    >> PURE_REWRITE_TAC[TAKE_LENGTH_APPEND]
    >> fs[])
>> sg `EL(LENGTH ptrs1) (refs1 ++ [x] ++ refs2) = x`
>-(
    last_x_assum (fn x => PURE_REWRITE_TAC[x])
    >> PURE_REWRITE_TAC[el_append3]
    >> fs[])
>> sg `DROP (LENGTH ptrs1 + 1) (refs1 ++ [x] ++ refs2) = refs2`
>-(
    `(LENGTH ptrs1 + 1) = LENGTH(refs1 ++ [x])` by rw[]
    >> POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
    >> PURE_REWRITE_TAC[DROP_LENGTH_APPEND]
    >> fs[])
>> metis_tac[]);

val STATE_REFS_RECONSTRUCT = Q.prove(
`!ptrs1 r ptrs2 refs1 y refs2 TYPE H p s.
((STATE_REFS TYPE ptrs1 refs1) *
(STATE_REF TYPE r y) *
(STATE_REFS TYPE ptrs2 refs2) *
H) (st2heap p s) ==>
((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) (refs1 ++ [y] ++ refs2)) * H) (st2heap p s)`,
Induct
>-(
    rw[]
    >> Cases_on `refs1`
    >> fs[STATE_REFS_def]
    >> fs[SEP_CLAUSES, SEP_F_def])
\\ rw[]
\\ Cases_on `refs1`
\\ fs[]
\\ fs[SUC_ONE_ADD]
\\ fs[STATE_REFS_def, GSYM STAR_ASSOC, HCOND_EXTRACT]
\\ first_x_assum (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_COMM] x |> ASSUME_TAC)
\\ rw[Once STAR_COMM]
\\ fs[STAR_ASSOC]
\\ first_x_assum (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_ASSOC] x |> ASSUME_TAC)
\\ rw[Once (GSYM STAR_ASSOC)]);

val STATE_REFS_DECOMPOSE = Q.store_thm("STATE_REFS_DECOMPOSE",
`!ptrs1 r ptrs2 refs TYPE H p s. ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) <=>
?refs1 y refs2.
refs = refs1 ++ [y] ++ refs2 /\
((STATE_REFS TYPE ptrs1 refs1 *
(STATE_REF TYPE r y) *
(STATE_REFS TYPE ptrs2 refs2) *
H)) (st2heap p s)`,
rpt STRIP_TAC
\\ EQ_TAC
>-(
    rw[]
    >> sg `?refs1 refs'. refs = refs1 ++ refs' /\ LENGTH refs1 = LENGTH ptrs1`
    >-(
	IMP_RES_TAC STATE_REFS_LENGTH
        >> qexists_tac `TAKE (LENGTH ptrs1) refs`
        >> qexists_tac `DROP (LENGTH ptrs1) refs`
        >> rw[TAKE_DROP]
	>> fs[LENGTH_TAKE])
    >> sg `?y refs2. refs' = [y] ++ refs2 /\ LENGTH refs2 = LENGTH ptrs2`
    >-(
	qexists_tac `HD refs'`
        >> qexists_tac `TL refs'`
        >> IMP_RES_TAC STATE_REFS_LENGTH
        >> Cases_on `refs'`
        >> rw[]
        >> fs[])
    >> rw[]
    >> qexists_tac `refs1`
    >> qexists_tac `y`
    >> qexists_tac `refs2`
    >> fs[]
    >> sg `TAKE (LENGTH ptrs1) (refs1 ++ [y] ++ refs2) = refs1`
    >-(
        PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
        >> qpat_x_assum `LENGTH refs1 = X` (fn x => PURE_REWRITE_TAC[GSYM x])
	>> PURE_REWRITE_TAC[TAKE_LENGTH_APPEND]
        >> fs[])
    >> sg `EL(LENGTH ptrs1) (refs1 ++ [y] ++ refs2) = y`
    >-(
	qpat_x_assum `LENGTH refs1 = X` (fn x => PURE_REWRITE_TAC[GSYM x])
        >> PURE_REWRITE_TAC[el_append3]
	>> fs[])
    >> sg `DROP (LENGTH ptrs1 + 1) (refs1 ++ [y] ++ refs2) = refs2`
    >-(
	`(LENGTH ptrs1 + 1) = LENGTH(refs1 ++ [y])` by rw[]
        >> POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
        >> PURE_REWRITE_TAC[DROP_LENGTH_APPEND]
	>> fs[])
    >> IMP_RES_TAC STATE_REFS_EXTRACT
    >> metis_tac[])
\\ rw[]
\\ fs[STATE_REFS_RECONSTRUCT]);

val STATE_REFS_DECOMPOSE_2 = Q.store_thm("STATE_REFS_DECOMPOSE_2",
`!ptrs1 r ptrs2 refs1 x refs2 TYPE H p s.
LENGTH ptrs1 = LENGTH refs1 ==>
LENGTH ptrs2 = LENGTH refs2 ==>
(((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) (refs1 ++ [x] ++ refs2)) * H) (st2heap p s) <=>
((STATE_REFS TYPE ptrs1 refs1 *
(STATE_REF TYPE r x) *
(STATE_REFS TYPE ptrs2 refs2) *
H)) (st2heap p s))`,
rpt STRIP_TAC
\\ EQ_TAC
>-(
    rw[]
    >> fs[STATE_REFS_EXTRACT_2])
\\ rw[]
\\ fs[STATE_REFS_RECONSTRUCT]);

val store_lookup_CELL_st2heap = Q.store_thm("store_lookup_CELL_st2heap",
`(l ~~>> res * H) (st2heap p s) ==> store_lookup l (s.refs ++ junk) = SOME res`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP
\\ IMP_RES_TAC st2heap_CELL_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_lookup_def]);

val store_lookup_REF_st2heap = Q.store_thm("store_lookup_REF_st2heap",
`(Loc l ~~> v * H) (st2heap p s) ==> store_lookup l (s.refs ++ junk) = SOME (Refv v)`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
\\ IMP_RES_TAC st2heap_REF_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_lookup_def]);

val store_lookup_ARRAY_st2heap = Q.store_thm("store_lookup_ARRAY_st2heap",
`(ARRAY (Loc l) av * H) (st2heap p s) ==> store_lookup l (s.refs ++ junk) = SOME (Varray av)`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_ARRAY
\\ IMP_RES_TAC st2heap_ARRAY_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_lookup_def]);

val EvalM_Mdref = Q.store_thm("EvalM_Mdref",
`nsLookup env.v (Short rname) = SOME rv ==>
r = LENGTH ptrs2 ==>
EvalM env st (App Opderef [Var (Short rname)])
(MONAD TYPE (\x v. F) (Mdref e (StoreRef r))) (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2))`,
rw[]
\\ fs[EvalM_def]
\\ rw[]
\\ ntac 20 (rw[Once evaluate_cases])
\\ rw[do_app_def]
\\ fs[REFS_PRED_def]
\\ IMP_RES_TAC STATE_REFS_EXTRACT
\\ fs[GSYM STAR_ASSOC]
\\ POP_ASSUM(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ fs[STATE_REF_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ EXTRACT_PURE_FACTS_TAC
\\ fs[GSYM STAR_ASSOC]
\\ IMP_RES_TAC REF_EXISTS_LOC
\\ fs[]
\\ IMP_RES_TAC store_lookup_REF_st2heap
\\ fs[]
\\ qexists_tac `s with refs := s.refs ++ junk`
\\ qexists_tac `Rval v`
\\ fs[with_same_ffi]
\\ qexists_tac `st`
\\ fs[MONAD_def]
\\ `LENGTH ptrs2 < LENGTH st` by (IMP_RES_TAC STATE_REFS_LENGTH \\ fs[])
\\ fs[Mdref_eq]
\\ fs[dref_def]
\\ `LENGTH st - (LENGTH ptrs2 + 1) = LENGTH ptrs1` by (IMP_RES_TAC STATE_REFS_LENGTH \\ fs[])
\\ POP_ASSUM(fn x => fs[x])
\\ fs[REFS_PRED_FRAME_def]
\\ rw[state_component_equality]
\\ fs[Once (GSYM with_same_refs)]
\\ fs[STATE_APPEND_JUNK]);

(* Validity of an assigment operation *)
val store_assign_REF_st2heap = Q.store_thm("store_assign_REF_st2heap",
`(Loc l ~~> v * H) (st2heap p s) ==>
store_assign l (Refv res) (s.refs ++ junk) = SOME (LUPDATE (Refv res) l (s.refs ++ junk))`,
rw[]
\\ simp[store_assign_def]
\\ IMP_RES_TAC st2heap_REF_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_v_same_type_def]
\\ IMP_RES_TAC store2heap_IN_EL
\\ fs[EL_APPEND1]);

val UPDATE_STATE_REFS = Q.prove(
`!ptrs2 l ptrs1 x res TYPE junk refs p s.
TYPE x res ==>
REFS_PRED_FRAME (STATE_REFS TYPE (ptrs1 ++ [Loc l] ++ ptrs2)) p (refs, s)
(ref_assign (LENGTH ptrs2) x refs, s with refs := LUPDATE (Refv res) l (s.refs ++ junk))`,
rw[]
\\ fs[REFS_PRED_def, REFS_PRED_FRAME_def]
\\ rw[]
\\ fs[STATE_REFS_DECOMPOSE]
\\ rw[ref_assign_def, state_component_equality]
\\ sg `LENGTH ptrs2 = LENGTH refs2`
   >-(fs[Once STAR_COMM, STAR_ASSOC]
      >> fs[Once STAR_COMM]
      >> IMP_RES_TAC STATE_REFS_LENGTH)
\\ fs[lupdate_append2]
\\ fs[STATE_REFS_DECOMPOSE]
\\ fs[GSYM STAR_ASSOC]
\\ IMP_RES_TAC STATE_REFS_LENGTH
\\ fs[STATE_REFS_DECOMPOSE_2]
\\ fs[STAR_ASSOC]
\\ fs[GSYM STAR_ASSOC]
\\ fs[Once STAR_COMM]
\\ fs[GSYM STAR_ASSOC]
\\ fs[STATE_REF_def]
\\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
\\ qexists_tac `res`
\\ EXTRACT_PURE_FACTS_TAC
\\ fs[SEP_CLAUSES]
\\ fs[GSYM STAR_ASSOC]
\\ IMP_RES_TAC STATE_UPDATE_HPROP_REF
\\ POP_ASSUM(qspec_then `res` ASSUME_TAC)
\\ IMP_RES_TAC st2heap_REF_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ IMP_RES_TAC STATE_APPEND_JUNK
\\ fs[LUPDATE_APPEND1]
\\ metis_tac[STAR_ASSOC, STAR_COMM]);

val EvalM_Mref_assign = Q.store_thm("EvalM_Mref_assign",
`nsLookup env.v (Short rname) = SOME rv ==>
r = LENGTH ptrs2 ==>
Eval env xexpr (TYPE x) ==>
EvalM env st (App Opassign [Var (Short rname); xexpr])
(MONAD UNIT_TYPE (\x v. F) (Mref_assign e (StoreRef r) x)) (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2))`,
rw[]
\\ fs[EvalM_def]
\\ ntac 2 (rw[Once evaluate_cases])
\\ fs[Eval_def]
\\ first_x_assum(qspec_then `s.refs++junk` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
\\ evaluate_unique_result_tac
\\ rw[evaluate_list_cases]
\\ rw[Once evaluate_cases]
\\ fs[REFS_PRED_def]
\\ IMP_RES_TAC STATE_REFS_EXTRACT
\\ fs[GSYM STAR_ASSOC]
\\ POP_ASSUM(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
\\ fs[STATE_REF_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ EXTRACT_PURE_FACTS_TAC
\\ fs[GSYM STAR_ASSOC]
\\ IMP_RES_TAC REF_EXISTS_LOC
\\ rw[do_app_def]
\\ IMP_RES_TAC store_assign_REF_st2heap
\\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
\\ POP_ASSUM(fn x => simp[x])
\\ qexists_tac `s with refs := LUPDATE (Refv res) l (s.refs ++ junk ++ refs')`
\\ qexists_tac `Rval (Conv NONE [])`
\\ fs[state_component_equality]
\\ qexists_tac `ref_assign (LENGTH ptrs2) x st`
\\ `s.refs ++ junk ++ refs' = s.refs ++ (junk ++ refs')` by fs[]
\\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
\\ fs[UPDATE_STATE_REFS]
\\ fs[MONAD_def]
\\ IMP_RES_TAC STATE_REFS_LENGTH
\\ fs[Mref_assign_eq]);

(* Allocation of the initial store for dynamic references *)
val STATE_REFS_EXTEND = Q.store_thm(
"STATE_REFS_EXTEND",
`!H s refs. (STATE_REFS A ptrs refs * H) (st2heap p s) ==>
!x xv. A x xv ==>
(STATE_REFS A (Loc (LENGTH s.refs)::ptrs) (x::refs) * H)(st2heap p (s with refs := s.refs ++ [Refv xv]))`,
rw[]
\\ rw[STATE_REFS_def]
\\ rw[GSYM STAR_ASSOC]
\\ rw[Once STAR_def]
\\ qexists_tac `store2heap_aux (LENGTH s.refs) [Refv xv]`
\\ qexists_tac `st2heap p s`
\\ PURE_REWRITE_TAC[Once SPLIT_SYM]
\\ `st2heap p s = st2heap p (s with refs := s.refs)` by fs[with_same_refs]
\\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
\\ fs[STATE_SPLIT_REFS]
\\ fs[with_same_refs]
\\ simp[STATE_REF_def, store2heap_aux_def]
\\ simp[SEP_EXISTS_THM]
\\ qexists_tac `xv`
\\ EXTRACT_PURE_FACTS_TAC
\\ simp[REF_def, cell_def, one_def, SEP_EXISTS_THM, HCOND_EXTRACT]);

(* Resizable arrays *)
val ABS_NUM_EQ = Q.prove(`Num(ABS(&n))=n`,
rw[DB.fetch "integer" "Num", integerTheory.INT_ABS]);

val evaluate_Opdref_REF = Q.prove(
`nsLookup env.v (Short vname) = SOME (Loc loc) ==>
(REF (Loc loc) v * H refs) (st2heap p s) ==>
!junk. evaluate F env (s with refs := s.refs ++ junk) (App Opderef [Var (Short vname)]) (s with refs := s.refs ++ junk, Rval v)`,
rw[]
\\ rw[Once evaluate_cases]
\\ CONV_TAC SWAP_EXISTS_CONV
\\ qexists_tac `s with refs := s.refs ++ junk`
\\ fs[state_component_equality]
\\ rw[Once evaluate_cases, evaluate_list_cases]
\\ rw[do_app_def]
\\ IMP_RES_TAC store_lookup_REF_st2heap
\\ fs[]);

val do_app_Alength_ARRAY = Q.prove(
`(ARRAY rv v * H) (st2heap p (s with refs := s.refs ++ junk)) ==>
do_app (s.refs ++ junk, s.ffi) Alength [rv] =
SOME ((s.refs ++ junk, s.ffi), Rval (Litv(IntLit(int_of_num(LENGTH v)))))`,
rw[do_app_def]
\\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
\\ IMP_RES_TAC store_lookup_CELL_st2heap
\\ first_x_assum(qspec_then `[]` ASSUME_TAC)
\\ fs[]);

val EvalM_Marray_length = Q.store_thm("EvalM_Marray_length",
  `!vname loc TYPE EXC_TYPE H get_arr x env.
    nsLookup env.v (Short vname) = SOME loc ==>
    EvalM env st (App Alength [App Opderef [Var (Short vname)]])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    (λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ fs[REFS_PRED_def, RARRAY_REL_def, RARRAY_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ first_x_assum(qspec_then `junk` ASSUME_TAC)
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Marray_length_def]
  \\ fs[MONAD_def]
  \\ qexists_tac `s with refs := s.refs ++ junk`
  \\ fs[state_component_equality]
  \\ fs[STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ IMP_RES_TAC STATE_APPEND_JUNK
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ first_x_assum(qspec_then `junk` ASSUME_TAC)
  \\ fs[Once (GSYM STAR_COMM)]
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC do_app_Alength_ARRAY
  \\ POP_ASSUM(fn x => fs[x])
  \\ qexists_tac `Rval (Litv (IntLit (&LENGTH av)))`
  \\ fs[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[REFS_PRED_FRAME_append]);

val do_app_Asub_ARRAY = Q.prove(
`(ARRAY rv v * H) (st2heap p (s with refs := s.refs ++ junk)) ==>
do_app (s.refs ++ junk, s.ffi) Asub [rv; Litv (IntLit (&n))] =
if n < LENGTH v then SOME ((s.refs ++ junk, s.ffi), Rval (EL n v))
else SOME ((s.refs ++ junk, s.ffi), Rerr (Rraise (prim_exn "Subscript")))`,
rw[do_app_def]
\\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
\\ IMP_RES_TAC store_lookup_CELL_st2heap
\\ first_x_assum(qspec_then `[]` ASSUME_TAC)
\\ fs[ABS_NUM_EQ]);

val EvalM_Marray_sub = Q.store_thm("EvalM_Marray_sub",
  `!vname loc TYPE EXC_TYPE H get_arr e rexp env n nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   EvalM env st (Handle (App Asub [App Opderef [Var (Short vname)]; nexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   (λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[Once evaluate_cases,evaluate_list_cases]
  \\ last_assum(qspec_then `s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ POP_ASSUM(qspec_then `junk++refs'` ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ fs[STAR_ASSOC]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ rw[]
  \\ rw[Once evaluate_cases,evaluate_list_cases]
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ POP_ASSUM(fn x => PURE_REWRITE_RULE [GSYM STAR_ASSOC, GC_STAR_GC] x |> ASSUME_TAC)
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ POP_ASSUM(qspec_then `junk ++ refs'` ASSUME_TAC)
  \\ IMP_RES_TAC do_app_Asub_ARRAY
  \\ evaluate_unique_result_tac
  \\ Cases_on `n < LENGTH (get_arr st)`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def]
     \\ qexists_tac `s with refs := s.refs ++ junk ++ refs'`
     \\ qexists_tac `Rval (EL n av)`
     \\ fs[state_component_equality]
     \\ fs[Msub_eq]
     \\ fs[LIST_REL_EL_EQN]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ qpat_x_assum `evaluate a0 a1 a2 a3 a4` (fn x => SIMP_RULE pure_ss [GSYM APPEND_ASSOC] x |> ASSUME_TAC)
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ fs[]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ rw[prim_exn_def]
  \\ fs[lookup_cons_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ first_assum(qspec_then `s.refs ++ (junk ++ refs')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[with_same_ffi]
  \\ evaluate_unique_result_tac
  \\ fs[]
  \\ qexists_tac `s with refs := s.refs ++ junk ++ refs' ++ refs''`
  \\ qexists_tac `Rerr (Rraise res)`
  \\ fs[state_component_equality]
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rw[REFS_PRED_FRAME_append]);

val EvalM_Marray_update = Q.store_thm("EvalM_Marray_update",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr e rexp env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   Eval env xexp (TYPE x) ==>
   EvalM env st (Handle (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   (λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[]
  \\ rw[Once evaluate_cases]
  \\ last_x_assum(qspec_then `s.refs ++ (junk ++ refs')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[]
  \\ rw[]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ first_x_assum(qspec_then `junk ++ refs' ++ refs''` ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ rw[Once evaluate_list_cases]
  \\ fs[]
  \\ rw[Once evaluate_list_cases]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ IMP_RES_TAC STATE_APPEND_JUNK
  \\ POP_ASSUM(qspec_then`junk++refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC]))
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[do_app_def]
      >> fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
      >> EXTRACT_PURE_FACTS_TAC
      >> rw[]
      >> IMP_RES_TAC LIST_REL_LENGTH
      >> fs[GSYM STAR_ASSOC]
      >> IMP_RES_TAC store_lookup_CELL_st2heap
      >> POP_ASSUM(fn x => ALL_TAC)
      >> POP_ASSUM(qspec_then `[]` ASSUME_TAC)
      >> fs[ABS_NUM_EQ]
      >> IMP_RES_TAC st2heap_CELL_MEM
      >> IMP_RES_TAC store2heap_IN_LENGTH
      >> fs[store_assign_def, store_v_same_type_def]
      >> IMP_RES_TAC store2heap_IN_EL
      >> fs[]
      >> qexists_tac `s with refs := LUPDATE (Varray (LUPDATE res n av)) loc
         (s.refs ++ junk ++ refs' ++ refs'')`
      >> fs[state_component_equality]
      >> qexists_tac `Rval (Conv NONE [])`
      >> rw[]
      >> qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      >> fs[MONAD_def, Marray_update_def, Mupdate_eq]
      >> fs[REFS_PRED_FRAME_def]
      >> rw[state_component_equality]
      >> fs[Once (GSYM with_same_refs)]
      >> POP_ASSUM(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      >> POP_ASSUM(qspec_then`junk++refs'++refs''` ASSUME_TAC)
      >> fs[GSYM STAR_ASSOC]
      >> fs[Once STAR_COMM]
      >> fs[RARRAY_def, RARRAY_REL_def, SEP_CLAUSES, SEP_EXISTS_THM]
      >> fs[STAR_ASSOC, PULL_EXISTS]
      >> qexists_tac `LUPDATE res n av`
      >> qexists_tac `arv`
      >> EXTRACT_PURE_FACTS_TAC
      >> fs[EVERY2_LUPDATE_same]
      >> fs[GSYM STAR_ASSOC]
      >> fs[Once STAR_COMM]
      >> sg `arv  = Loc loc`
      >-(fs[STAR_ASSOC]
	 >> POP_ASSUM(fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
	 >> fs[GSYM STAR_ASSOC]
	 >> qpat_x_assum `(GC * H1) X` (fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
	 >> fs[GSYM STAR_ASSOC]
	 >> fs[REF_def, SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC, HCOND_EXTRACT]
	 >> IMP_RES_TAC UNIQUE_CELLS
	 >> rw[])
      >> rw[]
      >> fs[GSYM STAR_ASSOC]
      >> IMP_RES_TAC STATE_UPDATE_HPROP_ARRAY
      >> POP_ASSUM(qspec_then `LUPDATE res n av` ASSUME_TAC)
      >> fs[])
  \\ rw[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC store_lookup_CELL_st2heap
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ POP_ASSUM(qspec_then `[]` ASSUME_TAC)
  \\ rw[Once evaluate_cases, evaluate_list_cases]
  \\ fs [] \\ rw [do_app_def]
  \\ ntac 4 (rw[Once evaluate_cases])
  \\ rw[prim_exn_def]
  \\ rw[Once evaluate_cases]
  \\ fs[lookup_cons_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[Once evaluate_cases]
  \\ fs[with_same_ffi]
  \\ last_x_assum(qspec_then `s.refs ++ (junk ++ refs' ++ refs'')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ qexists_tac `s with refs := s.refs ++ junk ++ refs' ++ refs'' ++ refs'''` \\ fs []
  \\ qexists_tac `Rerr (Rraise res')` \\ fs []
  \\ fs[state_component_equality]
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]);

val HPROP_TO_GC_R = Q.prove(`(A * B) s ==> (A * GC) s`,
rw[STAR_def]
\\ qexists_tac `u`
\\ qexists_tac `v`
\\ fs[SAT_GC]);

val HPROP_TO_GC_L = Q.prove(`(A * B) s ==> (GC * B) s`,
rw[STAR_def]
\\ qexists_tac `u`
\\ qexists_tac `v`
\\ fs[SAT_GC]);

val EvalM_Marray_alloc = Q.store_thm("EvalM_Marray_alloc",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr n x env nexp xexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM env st (App Opassign [Var (Short vname); App Aalloc [nexp; xexp]])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_alloc set_arr n x))
   (λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ first_x_assum(qspec_then `s.refs ++ junk` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Once evaluate_cases]
  \\ first_x_assum(qspec_then `s.refs ++ (junk ++ refs')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Once evaluate_cases]
  \\ rw[do_app_def]
  \\ rw[store_alloc_def]
  \\ rw[with_same_ffi]
  \\ rw[Once evaluate_cases]
  \\ qpat_x_assum `REFS_PRED H1 st p s` (fn x => PURE_REWRITE_RULE[REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ fs[Once (GSYM with_same_refs)]
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ IMP_RES_TAC store_assign_REF_st2heap
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ fs[]
  \\ Q.PAT_ABBREV_TAC `loc = LENGTH junk + L`
  \\ Q.PAT_ABBREV_TAC `srefs = A ++ [Varray X]`
  \\ qexists_tac `s with refs := LUPDATE (Refv (Loc loc)) l srefs`
  \\ qexists_tac `Rval (Conv NONE [])`
  \\ fs[state_component_equality]
  \\ fs[MONAD_def, Marray_alloc_def]
  \\ rw[REFS_PRED_FRAME_def, state_component_equality]
  \\ fs[RARRAY_def, RARRAY_REL_def, SEP_EXISTS_THM, SEP_CLAUSES]
  (*\\ qexists_tac `REPLICATE (Num (ABS (&n))) res`*)
  \\ qexists_tac `REPLICATE n res`
  \\ qexists_tac `Loc loc`
  \\ qpat_x_assum `Abbrev X` (fn x => fs[PURE_REWRITE_RULE[markerTheory.Abbrev_def] x])
  \\ IMP_RES_TAC st2heap_REF_MEM
  \\ IMP_RES_TAC store2heap_IN_LENGTH
  \\ fs[with_same_refs]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ fs[LUPDATE_APPEND1]
  \\ rw[GSYM STAR_ASSOC]
  \\ rw[Once STAR_COMM]
  \\ rw[GSYM STAR_ASSOC]
  \\ rw[Once STAR_def]
  \\ qexists_tac `store2heap_aux (LENGTH(LUPDATE (Refv (Loc loc)) l s.refs ++ junk ++ refs' ++ refs'')) [Varray (REPLICATE n res)]`
  \\ qexists_tac `st2heap p (s with
        refs := LUPDATE (Refv (Loc loc)) l s.refs ++ junk ++ refs' ++ refs'')`
  \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
  \\ fs[STATE_SPLIT_REFS]
  \\ simp[ARRAY_def, store2heap_aux_def, SEP_EXISTS_THM, GSYM STAR_ASSOC, HCOND_EXTRACT, cell_def, one_def]
  \\ simp[LIST_REL_REPLICATE_same]
  \\ rw[STAR_ASSOC, Once STAR_COMM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ sg `(Loc l ~~> arv' * H st * F' * GC) (st2heap p s)`
  >-(fs[GSYM STAR_ASSOC]
     \\ fs[Once STAR_COMM]
     \\ fs[GSYM STAR_ASSOC]
     \\ ntac 2 (POP_ASSUM (fn x => ALL_TAC))
     \\ POP_ASSUM(fn x => MATCH_MP HPROP_TO_GC_L x |> ASSUME_TAC)
     \\ metis_tac[STAR_ASSOC, STAR_COMM])
  \\ fs[GSYM STAR_ASSOC]
  \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_REF) x |> ASSUME_TAC)
  \\ first_x_assum(qspec_then `Loc loc` ASSUME_TAC)
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ POP_ASSUM(qspec_then `junk ++ refs' ++ refs''` ASSUME_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]);

(* TODO: implement a resize pattern *)
(* val array_copy_v = ``
Letrec [("array_copy", "d",
Fun "n" (Fun "x" (Fun "src" (Fun "dst" (
If (App (Opb Lt) [Var (Short "x"); Lit(IntLit 0)])
(Con NONE [])
(Let NONE (App Aupdate [Var (Short "dst"); App (Opn Plus) [Var (Short "n"); Var (Short "d")];
           App Asub [Var (Short "src")]])
(App Opapp[
App Opapp[
App Opapp[
App Opapp [App Opapp [Var (Short "array_copy"); App (Opn Plus) [Var (Short "d"); Lit(IntLit 1)]];
           App (Opn Minus) [Var (Short "n"); Lit(IntLit 1)]];
Var (Short "x")];
Var (Short "src")];
Var (Short "dest")]))
)))))] (Var (Short "array_copy"))
``; *)

(* TODO: implement support for 2d arrays *)
val ARRAY2D_def = Define `
ARRAY2D av l = SEP_EXISTS fl. ARRAY av fl * &(fl = FLAT l)`;

val RARRAY2D_def = Define `
RARRAY2D rv l = SEP_EXISTS av. REF rv av * ARRAY2D av l`;

(* TODO: implement support for n-dimensional arrays? *)

(*
 * Run
 *)
val EvalSt_def = Define `
EvalSt env st exp P H =
!(s : unit semanticPrimitives$state) p. REFS_PRED H st p s ==>
!junk. ?s2 res st2.
evaluate F env (s with refs := s.refs ++ junk) exp (s2, Rval res) /\
P res /\ REFS_PRED_FRAME H p (st, s) (st2, s2)`;

val LENGTH_Mem_IN_store2heap = Q.prove(`!refs n. n < LENGTH refs ==> (Mem n (EL n refs)) IN (store2heap refs)`,
ASSUME_TAC(Q.ISPEC `\refs. !n. n < LENGTH refs ==> (Mem n (EL n refs)) IN (store2heap refs)` SNOC_INDUCT)
\\ fs[]
\\ first_x_assum MATCH_MP_TAC
\\ rw[SNOC_APPEND]
\\ Cases_on `LENGTH l - n`
>-(
    `n = LENGTH l` by rw[]
    \\ rw[EL_LENGTH_APPEND]
    \\ rw[store2heap_append])
\\ `n < LENGTH l` by rw[]
\\ rw[EL_APPEND1]
\\ suff_tac ``(Mem n (EL n l)) IN (store2heap l)``
>-(rw[store2heap_append])
\\ rw[]);

val REFS_PRED_FRAME_partial_frame_rule = Q.prove(`!s refs'. (!F. F (st2heap p s) ==> (F * GC) (st2heap p (s with refs := refs'))) ==>
?junk. refs' = s.refs ++ junk`,
rw[]
\\ first_x_assum(qspec_then `(\h. h = store2heap s.refs) * (\h. h = ffi2heap p s.ffi)` ASSUME_TAC)
\\ `((\h. h = store2heap s.refs) * (\h. h = ffi2heap p s.ffi)) (st2heap p s)` by simp[st2heap_def, STAR_def, st2heap_SPLIT_FFI]
\\ fs[]
\\ POP_ASSUM(fn x => ALL_TAC)
\\ sg `!n. n < LENGTH s.refs ==> (Mem n (EL n s.refs)) IN st2heap p (s with refs := refs')`
>-(
    rw[]
    \\ IMP_RES_TAC LENGTH_Mem_IN_store2heap
    \\ fs[STAR_def]
    \\ fs[SPLIT_def]
    \\ last_x_assum(fn x => ASSUME_TAC (ONCE_REWRITE_RULE[EQ_SYM_EQ] x))
    \\ rw[])
\\ sg `!n. n < LENGTH s.refs ==> EL n s.refs = EL n refs'`
>-(
    rw[]
    \\ first_x_assum(qspec_then `n` IMP_RES_TAC)
    \\ fs[st2heap_def, Mem_NOT_IN_ffi2heap]
    \\ IMP_RES_TAC store2heap_IN_EL
    \\ fs[])
\\ Cases_on `s.refs`
>-(fs[])
\\ sg `LENGTH (h::t) <= LENGTH refs'`
>-(
    last_x_assum(qspec_then `LENGTH s.refs - 1` ASSUME_TAC)
    \\ `LENGTH s.refs - 1 < LENGTH (h::t)` by rw[]
    \\ fs[st2heap_def, Mem_NOT_IN_ffi2heap]
    \\ IMP_RES_TAC store2heap_IN_LENGTH
    \\ `LENGTH s.refs - 1 = LENGTH t` by rw[]
    \\ fs[])
\\ IMP_RES_TAC (SPEC_ALL IS_PREFIX_THM |> EQ_IMP_RULE |> snd)
\\ IMP_RES_TAC IS_PREFIX_APPEND
\\ rw[]);

val EvalSt_to_Eval = Q.store_thm("EvalSt_to_Eval",
`EvalSt env st exp P (\s. emp) ==>
Eval env exp P`,
rw[EvalSt_def, Eval_def]
\\ fs[REFS_PRED_def, SEP_CLAUSES, SAT_GC]
\\ first_x_assum(qspecl_then [`empty_state with refs := refs`, `p`, `[]`] STRIP_ASSUME_TAC)
\\ fs[state_component_equality]
\\ fs[REFS_PRED_FRAME_def, SEP_CLAUSES]
\\ rw[]
\\ ASSUME_TAC (ISPEC ``empty_state with refs := refs`` REFS_PRED_FRAME_partial_frame_rule)
\\ fs[]
\\ first_x_assum IMP_RES_TAC
\\ rw[]
\\ evaluate_unique_result_tac
\\ fs[state_component_equality]);

val handle_one_def = Define `
handle_one vname cname exp1 exp2 =
(Handle exp1 [(Pcon (SOME (Short cname)) [Pvar vname], Let (SOME vname) (Con (SOME (Short cname)) [Var(Short vname)]) exp2)])`;

val handle_mult_def = Define `
handle_mult varname (cname::cons_names) exp1 exp2 =
handle_one varname cname (handle_mult varname cons_names exp1 exp2) exp2 /\
handle_mult varname [] exp1 exp2 = exp1`;

val handle_mult_append = Q.prove(
`!cons_names1 cons_names2 vname exp1 exp2.
handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2 =
handle_mult vname cons_names1 (handle_mult vname cons_names2 exp1 exp2) exp2`,
Induct >-(rw[handle_mult_def])
\\ rw[handle_mult_def]);

val evaluate_handle_mult_Rval = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rval res) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rval res)`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_mult_Rabort = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rerr (Rabort res)) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rerr (Rabort res))`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_THROUGH = Q.prove(`
!cons_names exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names ==>
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F env s exp1`,
Induct >-(rw[handle_mult_def])
\\ rw[]
\\ rw[handle_mult_def]
\\ irule EQ_EXT
\\ rw[]
\\ last_assum (fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
\\ Cases_on `x`
\\ fs[]
\\ rw[handle_one_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[ALL_DISTINCT, pat_bindings_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_compos_suffices = Q.prove(`evaluate F env s exp3 = evaluate F env s exp4 ==>
(evaluate F env s
  (Handle exp3
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]) =
evaluate F env s
  (Handle exp4
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]))`,
rw[]
\\ irule EQ_EXT
\\ rw[Once evaluate_cases]
\\ rw[Once EQ_SYM_EQ]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_PARTIAL_THROUGH = Q.prove(`!cons_names1 cons_names2 exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2 ==>
evaluate F env s (handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2) =
evaluate F env s (handle_mult vname cons_names1 exp1 exp2)`,
Induct
>-(
    rw[handle_mult_def]
    \\ IMP_RES_TAC evaluate_handle_EXN_THROUGH
    \\ fs[])
\\ rw[handle_mult_def, handle_one_def]
\\ irule evaluate_handle_compos_suffices
\\ last_assum IMP_RES_TAC
\\ fs[]);

val EVERY_CONJ_1 = GSYM EVERY_CONJ |> SPEC_ALL |> EQ_IMP_RULE |> fst |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO];

val prove_evaluate_handle_mult_CASE =
rw[]
\\ last_x_assum IMP_RES_TAC
\\ qexists_tac `cname`
\\ qexists_tac `ev'`
\\ simp[]
\\ sg `?cons_names1 cons_names2. cons_names = cons_names1 ++ [cname] ++ cons_names2`
>-(
    fs[MEM_EL]
    \\ sg `?cons_names1 cons_names'. cons_names = cons_names1 ++ cons_names' /\ LENGTH cons_names1 = n`
    >-(
	qexists_tac `TAKE n cons_names`
        \\ qexists_tac `DROP n cons_names`
        \\ simp[TAKE_DROP, LENGTH_TAKE])
    \\ qexists_tac `cons_names1`
    \\ fs[]
    \\ qexists_tac `TL cons_names'`
    \\ Cases_on `cons_names'` >> fs[]
    \\ rw[]
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ `~NULL ([h] ++ t)` by fs[]
    \\ IMP_RES_TAC EL_LENGTH_APPEND
    \\ fs[])
\\ sg `EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2`
>-(
    fs[ALL_DISTINCT_APPEND]
    \\ fs[EVERY_MEM]
    \\ rw[]
    \\ fs[EL_APPEND1, EL_APPEND2]
    \\ rw[Once pmatch_def]
    \\ fs[lookup_cons_def]
    \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
    \\ `cname' <> cname` by (first_assum(qspec_then `cname` ASSUME_TAC) \\ fs[] \\ metis_tac[])    \\ fs[])
\\ fs[EL_APPEND1, EL_APPEND2]
\\ rw[]
\\ IMP_RES_TAC evaluate_handle_EXN_PARTIAL_THROUGH
\\ fs[]
\\ rw[handle_mult_append, handle_mult_def]
\\ fs[Eval_def]
\\ qpat_x_assum `!e' ev1 cname'. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `s2.refs ++ []` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
\\ fs[with_same_refs]
\\ sg `evaluate F env s (handle_mult vname cons_names1 (handle_one vname cname exp1 exp2) exp2) =
    evaluate F env s (handle_one vname cname exp1 exp2)`
>-(
    sg `?s' res. evaluate F env s (handle_one vname cname exp1 exp2) (s', Rval res)`
    >-(
	rw[handle_one_def]
	\\ rw[Once evaluate_cases]
	\\ last_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
	\\ rw[Once evaluate_cases]
	\\ fs[pat_bindings_def]
	\\ fs[pmatch_def]
	\\ fs[EVERY_MEM, lookup_cons_def]
	\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
	\\ fs[write_def]
	\\ fs[with_same_refs]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
	\\ fs[namespaceTheory.id_to_n_def]
	\\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x]))
    \\ first_assum(fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
    \\ first_x_assum(qspecl_then [`cons_names1`, `vname`, `exp2`] ASSUME_TAC)
    \\ irule EQ_EXT
    \\ rw[]
    \\ Cases_on `x`
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ fs[])
\\ rw[]
\\ rw[handle_one_def]
\\ irule EQ_EXT
\\ rw[]
\\ Cases_on `x`
\\ rw[Once evaluate_cases]
\\ qpat_assum `evaluate F env s exp1 R` (fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ fs[pat_bindings_def]
\\ fs[pmatch_def]
\\ fs[EVERY_MEM, lookup_cons_def]
\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ fs[write_def]
\\ fs[with_same_refs]
\\ pop_assum(fn x => ALL_TAC)
\\ first_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def];

val evaluate_handle_mult_CASE_MODULE = Q.prove(`
!EXN_TYPE cons_names module_name vname exp1 exp2 s s2 e ev env.
(!e ev. EXN_TYPE e ev ==> ?ev' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
(∀e ev ev1 cname.
EXN_TYPE e ev ==>
ev = Conv (SOME (cname,TypeExn (Long module_name (Short cname)))) [ev1] ==>
Eval (write vname ev (write vname ev1 env)) exp2 (\v. T)) ==>
evaluate F env s exp1 (s2, Rerr (Rraise ev))
/\ EXN_TYPE e ev ==>
?cname ev'. ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev'] /\
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F (write vname ev (write vname ev' env)) s2 exp2`,
prove_evaluate_handle_mult_CASE);

val evaluate_handle_mult_CASE_SIMPLE = Q.prove(`
!EXN_TYPE cons_names vname exp1 exp2 s s2 e ev env.
(!e ev. EXN_TYPE e ev ==> ?ev' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Short cname))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Short cname))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
(∀e ev ev1 cname.
EXN_TYPE e ev ==>
ev = Conv (SOME (cname,TypeExn (Short cname))) [ev1] ==>
Eval (write vname ev (write vname ev1 env)) exp2 (\v. T)) ==>
evaluate F env s exp1 (s2, Rerr (Rraise ev))
/\ EXN_TYPE e ev ==>
?cname ev'. ev = Conv (SOME (cname, TypeExn (Short cname))) [ev'] /\
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F (write vname ev (write vname ev' env)) s2 exp2`,
prove_evaluate_handle_mult_CASE);

val evaluate_Success_CONS = Q.prove(
`lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
evaluate F env s e (s', Rval v) ==>
evaluate F env s (Con (SOME (Short "Success")) [e]) (s', Rval (Conv (SOME ("Success",TypeId (Short "exc"))) [v]))`,
rw[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ rw[Once evaluate_cases]
\\ qexists_tac `s'`
\\ rw[Once evaluate_cases]);

val evaluate_Success_CONS_err = Q.prove(
`lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
evaluate F env s e (s', Rerr v) ==>
evaluate F env s (Con (SOME (Short "Success")) [e]) (s', Rerr v)`,
rw[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ rw[Once evaluate_cases]
\\ qexists_tac `s'`
\\ rw[Once evaluate_cases]);

(* For the dynamic store initialisation *)
(* It is not possible to use register_type here... *)
val EXC_TYPE_aux_def = Define `
      (EXC_TYPE_aux a b (Failure x_2) v =
      ?v2_1.
        v = Conv (SOME ("Failure",TypeId (Short "exc"))) [v2_1] ∧
        b x_2 v2_1) /\
     (EXC_TYPE_aux a b (Success x_1) v <=>
     ?v1_1.
       v = Conv (SOME ("Success",TypeId (Short "exc"))) [v1_1] ∧
		a x_1 v1_1)`;

fun prove_EvalM_to_EvalSt handle_mult_CASE =
rw[EvalM_def, EvalSt_def]
\\ qpat_x_assum `!s p. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ Cases_on `res`
(* res is an Rval *)
>-(
    IMP_RES_TAC evaluate_Success_CONS
    \\ first_x_assum (fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
    \\ first_x_assum (qspecl_then [`cons_names`, `vname`, `(Con (SOME (Short "Failure")) [Var (Short vname)])`] ASSUME_TAC)
    \\ evaluate_unique_result_tac
    \\ fs[MONAD_def, run_def, EXC_TYPE_aux_def]
    \\ Cases_on `x init_state'`
    \\ Cases_on `q` \\ fs[]
    \\ fs[EXC_TYPE_aux_def]
    \\ metis_tac[])
\\ reverse(Cases_on `e`)
(* res is an Rerr (Rabort ...) *)
>-(
    irule FALSITY
    \\ fs[MONAD_def]
    \\ Cases_on `x init_state'`
    >> Cases_on `q`
    >> fs[])
(* res is an Rerr (Rraise ...) *)
\\ qpat_x_assum `MONAD A B X S1 S2` (fn x => RW[MONAD_def] x |> ASSUME_TAC)
\\ fs[]
\\ Cases_on `x init_state'` \\ fs[]
\\ Cases_on `q` \\ fs[]
\\ LAST_ASSUM IMP_RES_TAC
\\ IMP_RES_TAC (Thm.INST_TYPE [``:'b`` |-> ``:unit``] handle_mult_CASE)
\\ POP_ASSUM(fn x => ALL_TAC)
\\ first_x_assum(qspecl_then [`vname`, `Con (SOME (Short "Failure")) [Var (Short vname)]`] ASSUME_TAC)
\\ IMP_RES_TAC evaluate_Success_CONS_err
\\ first_assum(fn x => sg `^(fst(dest_imp (concl x)))`)
>-(
    rw[]
    \\ fs[EVERY_MEM]
    \\ first_x_assum(qspec_then `cname` IMP_RES_TAC)
    \\ fs[lookup_cons_def]
    \\ rw[Eval_def]
    \\ rw[Once evaluate_cases]
    \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
    \\ fs[namespaceTheory.id_to_n_def]
    \\ fs[write_def]
    \\ rw[Once evaluate_cases]
    \\ rw[Once evaluate_cases]
    \\ rw[Once evaluate_cases]
    \\ rw[state_component_equality])
\\ qpat_x_assum `P ==> Q` IMP_RES_TAC
\\ ntac 2 (POP_ASSUM (fn x => ALL_TAC))
\\ fs[]
\\ rw[Once evaluate_cases]
\\ fs[lookup_cons_def]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def, write_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[run_def, EXC_TYPE_aux_def]
\\ metis_tac[];

val EvalM_to_EvalSt_MODULE = Q.store_thm("EvalM_to_EvalSt_MODULE",
`!cons_names module_name vname TYPE EXN_TYPE x exp H init_state env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
(ALL_DISTINCT cons_names) ==>
vname <> "Success" ==>
vname <> "Failure" ==>
EvalM env init_state exp (MONAD TYPE EXN_TYPE x) H ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
lookup_cons "Failure" env = SOME (1,TypeId (Short "exc")) ==>
EvalSt env init_state (handle_mult vname cons_names (Con (SOME (Short "Success")) [exp]) (Con (SOME (Short "Failure")) [Var (Short vname)]))
(EXC_TYPE_aux TYPE EXN_TYPE (run x init_state)) H`,
prove_EvalM_to_EvalSt evaluate_handle_mult_CASE_MODULE);

val EvalM_to_EvalSt_SIMPLE = Q.store_thm("EvalM_to_EvalSt_SIMPLE",
`!cons_names vname TYPE EXN_TYPE x exp H init_state env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Short cname))) [ev']) ==>
(ALL_DISTINCT cons_names) ==>
vname <> "Success" ==>
vname <> "Failure" ==>
EvalM env init_state exp (MONAD TYPE EXN_TYPE x) H ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Short cname))) cons_names ==>
lookup_cons "Success" env = SOME (1,TypeId (Short "exc")) ==>
lookup_cons "Failure" env = SOME (1,TypeId (Short "exc")) ==>
EvalSt env init_state (handle_mult vname cons_names (Con (SOME (Short "Success")) [exp]) (Con (SOME (Short "Failure")) [Var (Short vname)]))
(EXC_TYPE_aux TYPE EXN_TYPE (run x init_state)) H`,
prove_EvalM_to_EvalSt evaluate_handle_mult_CASE_SIMPLE);

val evaluate_let_opref = Q.store_thm("evaluate_let_opref",
`Eval env exp1 P ==>
?junk v. evaluate F env s (Let (SOME vname) (App Opref [exp1]) exp2) = evaluate F (write vname (Loc (LENGTH (s.refs ++ junk))) env) (s with refs := s.refs ++ junk ++ [Refv v]) exp2 /\ P v`,
rw[Eval_def]
\\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
\\ IMP_RES_TAC evaluate_empty_state_IMP
\\ qexists_tac `refs'`
\\ qexists_tac `res`
\\ simp[]
\\ irule EQ_EXT
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def, store_alloc_def]
\\ fs[write_def, namespaceTheory.nsOptBind_def]
\\ rw[Once DISJ_COMM]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def, store_alloc_def]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[with_same_ffi]);

val EvalSt_Let_Fun = Q.store_thm("EvalSt_Let_Fun",
`EvalSt (write vname (Closure env xv fexp) env) st exp P H ==>
EvalSt env st (Let (SOME vname) (Fun xv fexp) exp) P H`,
rw[EvalSt_def]
\\ last_x_assum IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[namespaceTheory.nsOptBind_def]
\\ fs[write_def, merge_env_def]
\\ metis_tac[]);

val nsAppend_build_rec_env_eq_lemma = Q.prove(
`!funs funs0 cl_env v0 v1.
nsAppend (FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cl_env funs0 f) env') v1 funs) v0 =
FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cl_env funs0 f) env') (nsAppend v1 v0) funs`,
Induct_on `funs`
>-(fs[merge_env_def, build_rec_env_def, namespaceTheory.nsAppend_def])
\\ rw[]
\\ Cases_on `h`
\\ Cases_on `r`
\\ fs[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def]);

val nsAppend_build_rec_env_eq = Q.prove(`!funs cl_env v0 v1.
nsAppend (build_rec_env funs cl_env v1) v0 = build_rec_env funs cl_env (nsAppend v1 v0)`,
fs[build_rec_env_def]
\\ fs[nsAppend_build_rec_env_eq_lemma]);

val merge_build_rec_env = Q.prove(`!funs env1 env0.
merge_env <|v := (build_rec_env funs (merge_env env1 env0) env1.v); c := env1.c|> env0 =
(merge_env env1 env0) with v := build_rec_env funs (merge_env env1 env0) (merge_env env1 env0).v`,
fs[merge_env_def, nsAppend_build_rec_env_eq]);

val EvalSt_Letrec_Fun = Q.store_thm("EvalSt_Letrec_Fun",
`!funs env exp st P H.
(ALL_DISTINCT (MAP (\(x,y,z). x) funs)) ==>
EvalSt <|v := (build_rec_env funs env env.v); c := env.c|> st exp P H ==>
EvalSt env st (Letrec funs exp) P H`,
rw[EvalSt_def]
\\ qpat_x_assum `!s. A` IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ rw[Once evaluate_cases]
\\ `<|v := build_rec_env funs env env.v; c := env.c|> = env with v := build_rec_env funs env env.v` by fs[sem_env_component_equality]
\\ fs[]
\\ metis_tac[]);

val merge_env_bind_empty = Q.store_thm("merge_env_bind_empty",
`merge_env <| v := Bind [] []; c := Bind [] [] |> env  = env`,
rw[merge_env_def]
\\ Cases_on `env`
\\ Cases_on `n`
\\ Cases_on `n0`
\\ rw[namespaceTheory.nsAppend_def, sem_env_component_equality]);

val Bind_list_to_write = Q.store_thm("Bind_list_to_write",
`merge_env <|v := Bind ((vname, v)::binds) []; c := Bind [] []|> env =
write vname v (merge_env <|v := Bind binds []; c := Bind [] []|> env)`,
rw[merge_env_def, write_def]
\\ Cases_on `env`
\\ rw[]
\\ Cases_on `n`
\\ rw[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def]);

val VALID_REFS_PRED_EvalM_simp = Q.store_thm("VALID_REFS_PRED_EvalM_simp",
`(VALID_REFS_PRED H ==> EvalM env st exp P H) <=> EvalM env st exp P H`,
EQ_TAC
\\ rw[]
\\ Cases_on `VALID_REFS_PRED H` >> fs[]
\\ rw[]
\\ fs[VALID_REFS_PRED_def, EvalM_def]);

val evaluate_Var_IMP = Q.prove(
 `evaluate F env s1 (Var (Short name)) (s2, Rval v) ==>
  nsLookup env.v (Short name) = SOME v`,
  rw[Once evaluate_cases]);

val evaluate_Var_same_state = Q.prove(
 `evaluate F env s1 (Var (Short name)) (s2, res) <=>
  evaluate F env s1 (Var (Short name)) (s2, res) /\ s2 = s1`,
  EQ_TAC \\ ntac 2 (rw[Once evaluate_cases]));

val EvalSt_Opref = Q.store_thm("EvalSt_Opref",
`!exp get_ref_exp get_ref loc_name TYPE st_name env H P st.
Eval env get_ref_exp (TYPE (get_ref st)) ==>
(!loc. EvalSt (write loc_name loc env) st exp P (\st. REF_REL TYPE loc (get_ref st) * H st)) ==>
EvalSt env st
(Let (SOME loc_name) (App Opref [get_ref_exp]) exp) P H`,
rw[EvalSt_def]
\\ ntac 3 (rw[Once evaluate_cases])
\\ fs[Eval_def]
\\ fs[PULL_EXISTS]
\\ last_x_assum (qspec_then `s.refs++junk` strip_assume_tac)
\\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> ASSUME_TAC)
\\ evaluate_unique_result_tac
\\ rw[Once evaluate_cases]
\\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
\\ rw[state_component_equality,with_same_ffi]
\\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ junk ++ refs'))`, `s with refs := s.refs ++ junk ++ refs' ++ [Refv res]`, `p`] ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    POP_ASSUM (fn x => ALL_TAC)
    \\ SIMP_TAC bool_ss [REFS_PRED_def]
    \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
    \\ SIMP_TAC bool_ss [Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk ++ refs')) [Refv res]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk ++ refs')`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ SIMP_TAC bool_ss [STATE_SPLIT_REFS]
    \\ SIMP_TAC bool_ss [GSYM REFS_PRED_def, REFS_PRED_append, GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL REFS_PRED_append) \\ strip_tac
    \\ ASM_SIMP_TAC bool_ss []
    \\ rw[REF_REL_def]
    \\ rw[SEP_CLAUSES, SEP_EXISTS_THM]
    \\ qexists_tac `res`
    \\ EXTRACT_PURE_FACTS_TAC
    \\ rw[REF_HPROP_SAT_EQ, cfStoreTheory.store2heap_aux_def])
\\ first_x_assum drule \\ rw[]
\\ first_x_assum (qspec_then `[]` strip_assume_tac)
\\ fs[merge_env_def, write_def]
\\ evaluate_unique_result_tac
\\ fs[REFS_PRED_FRAME_def]
\\ rw[state_component_equality]
\\ qexists_tac `st2` \\ rw[]
\\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    rw[GSYM STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk ++ refs')) [Refv res]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk ++ refs')`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ rw[STATE_SPLIT_REFS]
    >-(
	rw[REF_REL_def]
	\\ rw[SEP_CLAUSES, SEP_EXISTS_THM]
	\\ qexists_tac `res`
        \\ EXTRACT_PURE_FACTS_TAC
	\\ rw[REF_HPROP_SAT_EQ, cfStoreTheory.store2heap_aux_def])
    \\ rw[STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `st2heap p (s with refs := s.refs)`
    \\ qexists_tac `store2heap_aux (LENGTH s.refs) (junk ++ refs')`
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ rw[STATE_SPLIT_REFS, SAT_GC]
    \\ fs[REFS_PRED_def, with_same_refs])
\\ qpat_x_assum `A ==> R` IMP_RES_TAC
\\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
\\ first_x_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
\\ fs[]);

val EQ_def = Define `EQ x y <=> x = y`;

val EvalSt_Alloc = Q.store_thm("EvalSt_Alloc",
`!exp get_ref loc_name STATE_TYPE TYPE st_name env H P st.
EQ (get_ref st) [] ==>
Eval env (Var (Short st_name)) (STATE_TYPE st) ==>
(!loc. EvalSt (write loc_name loc env) st exp P (\st. RARRAY_REL TYPE loc (get_ref st) * H st)) ==>
EvalSt env st
(Let (SOME loc_name) (App Opref [App AallocEmpty [Con NONE []]]) exp) P H`,
rw[EvalSt_def]
\\ ntac 9 (rw[Once evaluate_cases])
\\ fs[PULL_EXISTS]
\\ fs[do_con_check_def, build_conv_def]
\\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
\\ simp[with_same_ffi]
\\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ junk ++ [Varray []]))`, `s with refs := s.refs ++ junk ++ [Varray []; Refv (Loc (LENGTH (s.refs ++ junk)))]`, `p`] ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    POP_ASSUM (fn x => ALL_TAC)
    \\ SIMP_TAC bool_ss [REFS_PRED_def]
    \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
    \\ SIMP_TAC bool_ss [Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk)) [Varray []; Refv (Loc (LENGTH (s.refs ⧺ junk)))]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk)`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ SIMP_TAC bool_ss [STATE_SPLIT_REFS]
    \\ ASM_SIMP_TAC bool_ss [GSYM REFS_PRED_def, REFS_PRED_append]
    \\ fs[RARRAY_REL_def, SEP_EXISTS]
    \\ EXTRACT_PURE_FACTS_TAC
    \\ fs[RARRAY_HPROP_SAT_EQ,EQ_def,store2heap_aux_def]
    \\ metis_tac[])
\\ first_x_assum drule \\ rw[]
\\ first_x_assum (qspec_then `[]` strip_assume_tac)
\\ fs[merge_env_def, write_def]
\\ evaluate_unique_result_tac
\\ fs[REFS_PRED_FRAME_def]
\\ rw[state_component_equality]
\\ qexists_tac `st2` \\ rw[]
\\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
\\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
>-(
    rw[GSYM STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ junk)) [Varray []; Refv (Loc (LENGTH junk + LENGTH s.refs))]`
    \\ qexists_tac `st2heap p (s with refs := s.refs ++ junk)`
    \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
    \\ fs[STATE_SPLIT_REFS]
    \\ rw[]
    >-(
	fs[RARRAY_REL_def,SEP_EXISTS]
	\\ EXTRACT_PURE_FACTS_TAC
	\\ fs[LIST_REL_def,EQ_def]
	\\ fs[RARRAY_HPROP_SAT_EQ,EQ_def,store2heap_aux_def]
	\\ metis_tac[])
    \\ fs[STAR_ASSOC]
    \\ rw[Once STAR_def]
    \\ qexists_tac `st2heap p s`
    \\ qexists_tac `store2heap_aux (LENGTH s.refs) junk`
    \\ fs[SAT_GC]
    \\ metis_tac[GSYM with_same_refs, STATE_SPLIT_REFS])
\\ first_x_assum drule \\ rw[]
\\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
\\ first_x_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
\\ fs[STAR_ASSOC]
\\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
\\ fs[]);

val Eval_lookup_var = Q.store_thm("Eval_lookup_var",
`!env vname xv x TYPE. nsLookup env.v (Short vname) = SOME xv ==>
(Eval env (Var (Short vname)) (TYPE x) <=> TYPE x xv)`,
rw[Eval_def]
\\ EQ_TAC
>-(simp[Once evaluate_cases] \\ rw[] \\ metis_tac[])
\\ rw[Once evaluate_cases]
\\ rw[state_component_equality]);

val nsBind_to_write = Q.prove(
 `<|v := nsBind name v env1; c := env2|> =
  write name v <|v := env1; c := env2|>`,
 fs[write_def,sem_env_component_equality]);

val nsLookup_write_simp = Q.prove(
 `nsLookup (write name1 exp env).v (Short name2) =
  if name1 = name2 then SOME exp
  else nsLookup env.v (Short name2)`,
  Cases_on `name1 = name2`
  \\ fs[namespaceTheory.nsLookup_def, merge_env_def, write_def]);

val sem_env_same_components = Q.prove(
 `<|v := env.v; c := env.c|> = (env : v sem_env)`,
 fs[sem_env_component_equality]);

val lookup_cons_write_simp = Q.prove(
 `lookup_cons name2 (write name1 exp env) =
  lookup_cons name2 env`,
 fs[lookup_cons_def, write_def]);

val lookup_cons_build_rec_env_simp = Q.prove(
 `lookup_cons name2 <|v := build_rec_env exp env env.v; c := env.c|> =
  lookup_cons name2 env`,
  fs[lookup_cons_def]);

val LOOKUP_ASSUM_SIMP = save_thm("LOOKUP_ASSUM_SIMP",
LIST_CONJ[nsBind_to_write,Eval_Var_SIMP,Eval_lookup_var,nsLookup_write_simp,sem_env_same_components,lookup_cons_write_simp,lookup_cons_build_rec_env_simp]);

(* Terms used by the ml_monad_translatorLib *)
val m_translator_terms = save_thm("m_translator_terms",
  pack_list (pack_pair pack_string pack_term)
    [("EqSt remove",``!a st. EqSt a st = (a : ('a, 'b) H)``),
     ("PURE ArrowP eq", ``PURE(ArrowP H (PURE (Eq a x)) b)``),
     ("ArrowP PURE", ``ArrowP H a (PURE b)``),
     ("ArrowP EqSt", ``ArrowP H (EqSt a st) b``)
]);

(* val m_translator_types = save_thm("m_translator_types",
  pack_list (pack_pair pack_string pack_type)
    [];
[; *)

val _ = (print_asts := true);

val _ = export_theory();
