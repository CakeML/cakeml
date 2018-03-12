open ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory Satisfy
open cfHeapsBaseTheory AC_Sort
open determTheory ml_monadBaseTheory ml_monad_translatorBaseTheory
open cfStoreTheory cfTheory cfTacticsLib packLib;
open preamble;

val _ = new_theory "ml_monad_translator";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("ex_bind", ``st_ex_bind``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);

val _ = temp_overload_on ("CONTAINER", ``ml_translator$CONTAINER``);

val _ = hide "state";

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

fun first_assum_rewrite_once th =
  POP_ASSUM(fn x => ASSUME_TAC(PURE_ONCE_REWRITE_RULE[th] x))

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(***)

(* COPY/PASTE from ml_monadStoreScript *)
fun evaluate_unique_result_tac (g as (asl, w)) = let
    val asl = List.map ASSUME asl
    val uniques = mapfilter (MATCH_MP evaluate_unique_result) asl
in simp uniques g end;
(* End of COPY/PASTE from ml_monadStoreScript *)

(*
 * Definition of EvalM
 * `ro`: references only
 *)

val EvalM_def = Define `
  EvalM ro env st exp P H <=>
    !(s:'ffi state). REFS_PRED H st s  ==>
    ?s2 res st2. evaluate F env s exp (s2,res) /\
    P st (st2, res) /\ REFS_PRED_FRAME ro H (st, s) (st2, s2)`;

(* refinement invariant for ``:('a, 'b, 'c) M`` *)
val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val MONAD_def = Define `
  MONAD (a:'a->v->bool) (b: 'b->v->bool) (x:('refs, 'a, 'b) M)
                                    (state1:'refs)
                                    (state2:'refs,res: (v,v) result) =
    case (x state1, res) of
      ((Success y, st), Rval v) => (st = state2) /\ a y v
    | ((Failure e, st), Rerr (Rraise v)) => (st = state2) /\
                                              b e v
    | _ => F`

val H = mk_var("H",``:('a -> hprop) # 'ffi ffi_proj``);

(* return *)
val EvalM_return = Q.store_thm("EvalM_return",
  `!H b. Eval env exp (a x) ==>
    EvalM ro env st exp (MONAD a b (ex_return x)) ^H`,
  rw[Eval_def,EvalM_def,st_ex_return_def,MONAD_def] \\
  first_x_assum(qspec_then`s.refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP) \\
  asm_exists_tac \\ simp[] \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\
  fs[REFS_PRED_FRAME_append]);

(* bind *)
val EvalM_bind = Q.store_thm("EvalM_bind",
  `(a1 ==> EvalM ro env st e1 (MONAD b c (x:('refs, 'b, 'c) M)) (H:('refs -> hprop) # 'ffi ffi_proj)) /\
   (!z v. b z v ==> a2 z ==> EvalM ro (write name v env) (SND (x st)) e2 (MONAD a c ((f z):('refs, 'a, 'c) M)) H) ==>
   (a1 /\ !z. (CONTAINER(FST(x st) = Success z) ==> a2 z)) ==>
   EvalM ro env st (Let (SOME name) e1 e2) (MONAD a c (ex_bind x f)) H`,
  rw[EvalM_def,MONAD_def,st_ex_return_def,PULL_EXISTS, CONTAINER_def] \\ fs[] \\
  rw[Once evaluate_cases] \\
  last_x_assum drule \\ rw[] \\
  evaluate_unique_result_tac \\
  IMP_RES_TAC REFS_PRED_FRAME_imp \\
  fs[write_def, namespaceTheory.nsOptBind_def, with_same_refs] \\
  reverse(Cases_on`x st` \\ Cases_on`q` \\ Cases_on `res` \\ fs[] \\ rw[])
  >-(Cases_on `e` \\ fs[st_ex_bind_def])
  \\ fs[st_ex_bind_def] \\
  last_x_assum drule \\ rw[] \\
  first_x_assum drule \\ rw[] \\
  fs[with_same_refs] \\ evaluate_unique_result_tac \\
  Cases_on `f a' r` \\ Cases_on `res'` \\ Cases_on `q` \\ fs[] \\ rw[] \\
  IMP_RES_TAC REFS_PRED_FRAME_trans \\
  Cases_on `e` \\ fs[]);

(* lift ro refinement invariants *)

val _ = type_abbrev("H",``:'a -> 'refs ->
                                 'refs # (v,v) result -> bool``);

val PURE_def = Define `
  PURE a (x:'a) (st1:'refs) (st2,res:(v,v) result) =
    ?v:v. (res = Rval v) /\ (st1 = st2) /\ a x v`;

val EqSt_def = Define `
EqSt abs st = \x st1 (st2, res). st = st1 /\ abs x st1 (st2, res)`;

val Eval_IMP_PURE = Q.store_thm("Eval_IMP_PURE",
  `!H env exp P x. Eval env exp (P x) ==> EvalM ro env st exp (PURE P x) ^H`,
  rw[Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ first_x_assum(qspec_then`s.refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP)
  \\ fs[]
  \\ metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append]);

val Eval_IMP_PURE_EvalM_T = Q.store_thm("Eval_IMP_PURE_EvalM_T",
  `!H env exp P x. Eval env exp (P x) ==> EvalM T env st exp (PURE P x) ^H`,
  rw[Eval_IMP_PURE]);

(* function abstraction and application *)

val ArrowP_def = Define `
  ArrowP ro H (a:('a, 'refs) H) b f c =
     !x st1 s1 st2 (res:(v,v) result).
       a x st1 (st2,res) /\ REFS_PRED H st1 s1 ==>
       ?v env exp.
       (st2 = st1) /\
       (res = Rval v) /\ do_opapp [c;v] = SOME (env,exp) /\
       !junk. ?st3 s3 res3.
         evaluate F env (s1 with refs := s1.refs ++ junk) exp (s3,res3) /\
         b (f x) st1 (st3,res3) /\
         REFS_PRED_FRAME ro H (st1, s1) (st3, s3)`;

val ArrowM_def = Define `
  ArrowM ro H (a:('a, 'refs) H) (b:('b, 'refs) H) =
     PURE (ArrowP ro H a b) : ('a -> 'b, 'refs) H`;

val evaluate_list_cases = let
  val lemma = evaluate_cases |> CONJUNCTS |> el 2
  in CONJ (``evaluate_list a5 a6 a7 [] (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma])
          (``evaluate_list a5 a6 a7 (x::xs) (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma]) end

val EvalM_ArrowM = Q.store_thm("EvalM_ArrowM",
  `EvalM ro env st x1 ((ArrowM ro H (PURE a) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ evaluate_unique_result_tac
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ fs[with_same_refs]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_trans]);

val EvalM_ArrowM_EqSt = Q.store_thm("EvalM_ArrowM_EqSt",
  `EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE a) st) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ evaluate_unique_result_tac
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ fs[EqSt_def]
  \\ `PURE a x st (st,Rval v)` by fs[PURE_def]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ fs[with_same_refs]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_trans]);

val EvalM_ArrowM_Eq = Q.store_thm("EvalM_ArrowM_Eq",
  `EvalM ro env st x1 ((ArrowM ro H (PURE (Eq a x)) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ evaluate_unique_result_tac
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ fs[with_same_refs]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_trans]);

val EvalM_ArrowM_EqSt_Eq = Q.store_thm("EvalM_ArrowM_EqSt_Eq",
  `EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE (Eq a x)) st) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ evaluate_unique_result_tac
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ fs[EqSt_def,Eq_def,PURE_def]
  \\ first_x_assum (qspecl_then [`x`,`s2'`,`st`,`Rval v`] assume_tac)
  \\ fs[]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` STRIP_ASSUME_TAC) \\ fs[]
  \\ fs[with_same_refs]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_trans]);

val EvalM_Fun = Q.store_thm("EvalM_Fun",
  `(!v x. a x v ==> EvalM ro (write name v env) n_st body (b (f x)) H) ==>
    EvalM ro env st (Fun name body) (ArrowM ro H (EqSt (PURE a) n_st) b f) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS,REFS_PRED_FRAME_same]
  \\ rw[state_component_equality, REFS_PRED_FRAME_append]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ fs[EqSt_def, PURE_def] \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ qpat_assum `!x.P` drule
  \\ disch_then strip_assume_tac
  \\ evaluate_unique_result_tac
  \\ qexists_tac `st2'` \\ fs[]
  \\ drule REFS_PRED_FRAME_remove_junk \\ fs[]);

val EvalM_Fun_Var_intro = Q.store_thm("EvalM_Fun_Var_intro",
  `EvalM ro cl_env st (Fun n exp) (PURE P f) H ==>
   ∀name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
   EvalM ro env st (Var (Short name)) (PURE P f) ^H`,
  rw[EvalM_def, PURE_def, LOOKUP_VAR_def]
  \\ rw[Once evaluate_cases]
  \\ fs[lookup_var_def]
  \\ last_x_assum drule \\ rw[REFS_PRED_FRAME_same]
  \\ fs[Once evaluate_cases]
  \\ rw[]);

val EvalM_Fun_Eq = Q.store_thm("EvalM_Fun_Eq",
  `(!v. a x v ==> EvalM ro (write name v env) n_st body (b (f x)) H) ==>
    EvalM ro env st (Fun name body) ((ArrowM ro H (EqSt (PURE (Eq a x)) n_st) b) f) ^H`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS,REFS_PRED_FRAME_same]
  \\ fs[EqSt_def, PURE_def] \\ rw[]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ drule REFS_PRED_append \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ qexists_tac `st2'` \\ fs[]
  \\ drule REFS_PRED_FRAME_remove_junk \\ fs[]);

(* More proofs *)

val LOOKUP_VAR_EvalM_ArrowM_IMP = Q.store_thm("LOOKUP_VAR_EvalM_ArrowM_IMP",
  `(!st env. LOOKUP_VAR n env v ==> EvalM ro env st (Var (Short n)) (ArrowM ro H a b f) H) ==>
    ArrowP ro ^H a b f v`,
  fs [LOOKUP_VAR_def,lookup_var_def,EvalM_def,ArrowP_def,ArrowM_def,PURE_def,AND_IMP_INTRO,
      Once evaluate_cases,PULL_EXISTS, VALID_REFS_PRED_def]
  \\ `nsLookup (<|v := nsBind n v nsEmpty|>).v (Short n) = SOME v` by EVAL_TAC
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ rw[]);

val EvalM_Var_SIMP = Q.store_thm("EvalM_Var_SIMP",
  `EvalM ro (write n x env) st (Var (Short y)) P ^H =
    if n = y then EvalM ro (write n x env) st (Var (Short y)) P H
             else EvalM ro env st (Var (Short y)) P H`,
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,write_def]);

val EvalM_Var_SIMP_ArrowM = Q.store_thm("EvalM_Var_SIMP_ArrowM",
  `(!st. EvalM ro (write nv v env) st (Var (Short n)) (ArrowM ro H a b x) H) =
    if nv = n then ArrowP ro H a b x v
    else (!st. EvalM ro env st (Var (Short n)) (ArrowM ro H a b x) ^H)`,
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
      \\ metis_tac[PURE_def, REFS_PRED_FRAME_same])
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [write_def]);

val EvalM_Recclosure_ALT = Q.store_thm("EvalM_Recclosure_ALT",
`!H funs fname name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (Eq a n)) b) f) ^H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]);

val EvalM_Recclosure_ALT2 = Q.store_thm("EvalM_Recclosure_ALT2",
`!H funs fname.
     A n_st ==>
     !name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        A st ==>
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (EqSt (PURE (Eq a n)) n_st) b) f) ^H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def, EqSt_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]);

val EvalM_Recclosure_ALT3 = Q.store_thm("EvalM_Recclosure_ALT3",
`!H funs fname name body.
     (∀st v.
        A st ==>
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     A n_st ==>
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (EqSt (PURE (Eq a n)) n_st) b) f) ^H`,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def, EqSt_def] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]
  \\ reverse(rw[])
  >-(metis_tac[APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ rw[do_opapp_def]
  \\ fs[state_component_equality] \\ rw[]
  \\ fs[Eq_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]);

val EvalM_Recclosure = Q.store_thm("EvalM_Recclosure",
  `!H. (!st v. a n v ==>
         EvalM ro (write name v (write_rec [(fname,name,body)] env2 env2))
               st body (b (f n)) H) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (Eq a n)) b) f) ^H`,
  GEN_TAC \\ NTAC 2 STRIP_TAC \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ rw[Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,ArrowP_def,PULL_EXISTS]
  \\ first_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ first_assum_rewrite_once evaluate_cases \\ fs[]
  \\ rw[Once evaluate_cases,REFS_PRED_FRAME_same]
  \\ fs[Eq_def,do_opapp_def,Once find_recfun_def] \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[build_rec_env_def,write_rec_def,FOLDR,write_def]
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]);

val EvalM_Eq_Recclosure = Q.store_thm("EvalM_Eq_Recclosure",
  `LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
    (ArrowP ro H a b f (Recclosure x1 x2 x3) =
     (!st. EvalM ro env st (Var (Short name)) (ArrowM ro H a b f) ^H))`,
  rw[EvalM_Var_SIMP, EvalM_def, ArrowM_def, LOOKUP_VAR_def, lookup_var_def, PURE_def]
  \\ EQ_TAC
  >-(
      rw[]
      \\ rw[Once evaluate_cases]
      \\ fs[state_component_equality]
      \\ fs[REFS_PRED_FRAME_same])
  \\ fs [AND_IMP_INTRO, Once evaluate_cases,PULL_EXISTS,PULL_FORALL, VALID_REFS_PRED_def]
  \\ simp[state_component_equality]
  \\ simp[ArrowP_def]
  \\ metis_tac[REFS_PRED_FRAME_same]);

val EvalM_Var_ArrowP = Q.store_thm("EvalM_Var_ArrowP",
  `(!st. EvalM ro env st (Var (Short n)) (ArrowM ro H (PURE a) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro ^H (PURE a) b x v`,
  rw[EvalM_def]
  \\fs[Once evaluate_cases]
  \\ fs[ArrowP_def, ArrowM_def] \\ rw[]
  \\ fs[LOOKUP_VAR_def, lookup_var_def]
  \\ fs[PURE_def] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ fs[ArrowP_def]
  \\ `PURE a x' st1 (st1,Rval v')` by fs[PURE_def]
  \\ first_x_assum drule \\ rw[]);

val EvalM_Var_ArrowP_EqSt = Q.store_thm("EvalM_Var_ArrowP_EqSt",
  `(!st. EvalM ro env st (Var (Short n)) (ArrowM ro H (EqSt (PURE a) n_st) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro ^H (EqSt (PURE a) n_st) b x v`,
  rw[EvalM_def]
  \\ fs[Once evaluate_cases]
  \\ fs[ArrowP_def, ArrowM_def] \\ rw[]
  \\ fs[LOOKUP_VAR_def, lookup_var_def]
  \\ first_x_assum drule \\ rw[]
  \\ fs[Once PURE_def, EqSt_def] \\ fs[state_component_equality]
  \\ rw[] \\ fs[ArrowP_def]
  \\ `PURE a x' n_st (n_st,Rval v')` by fs[PURE_def]
  \\ first_x_assum drule \\ rw[]
  \\ fs[state_component_equality]);

(* Eq simps *)

val EvalM_FUN_FORALL = Q.store_thm("EvalM_FUN_FORALL",
  `(!x. EvalM ro env st exp (PURE (P x) f) H) ==>
    EvalM ro env st exp (PURE (FUN_FORALL x. P x) f) ^H`,
  rw[EvalM_def,PURE_def]
  \\ first_x_assum drule
  \\ simp[PULL_EXISTS,FUN_FORALL]
  \\ strip_tac
  \\ first_assum(qspecl_then[`ARB`]strip_assume_tac)
  \\ asm_exists_tac \\ simp[]
  \\ qx_gen_tac`x`
  \\ first_assum(qspecl_then[`x`]strip_assume_tac)
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]);

val EvalM_FUN_FORALL_EQ = Q.store_thm("EvalM_FUN_FORALL_EQ",
  `(!x. EvalM ro env st exp (PURE (P x) f) H) =
    EvalM ro env st exp (PURE (FUN_FORALL x. P x) f) ^H`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ fs [EvalM_def,PURE_def,PULL_EXISTS,FUN_FORALL] \\ METIS_TAC []);

val M_FUN_FORALL_PUSH1 = Q.prove(
  `(FUN_FORALL x. ArrowP ro ^H a (PURE (b x))) = (ArrowP ro H a (PURE (FUN_FORALL x. b x)))`,
  rw[FUN_EQ_THM,FUN_FORALL,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ reverse EQ_TAC >- METIS_TAC[] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum(qspec_then`ARB`strip_assume_tac) \\ fs[]
  \\ first_assum drule \\ disch_then strip_assume_tac \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ disch_then strip_assume_tac
  \\ fs[]
  \\ first_x_assum(qspecl_then[`[]`]strip_assume_tac)
  \\ fs[] \\ rw[] \\ evaluate_unique_result_tac
  \\ reverse(rw[])
  >-(metis_tac[REFS_PRED_FRAME_remove_junk])
  \\ first_x_assum(qspecl_then[`y`]strip_assume_tac)
  \\ first_x_assum drule \\ disch_then strip_assume_tac
  \\ first_x_assum(qspecl_then[`[]`]strip_assume_tac)
  \\ fs[] \\ rw[]
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]) |> GEN_ALL;

val M_FUN_FORALL_PUSH2 = Q.prove(
  `(FUN_FORALL x. ArrowP ro H ((PURE (a x))) b) =
    (ArrowP ro ^H (PURE (FUN_EXISTS x. a x)) b)`,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,PURE_def] \\ METIS_TAC []) |> GEN_ALL;

val M_FUN_FORALL_PUSH3 = Q.prove(
  `(FUN_FORALL st. ArrowP ro H (EqSt a st) b) =
    (ArrowP ro ^H a b)`,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,EqSt_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = Q.prove(
  `(FUN_EXISTS x. Eq a x) = a`,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val M_FUN_QUANT_SIMP = save_thm("M_FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,M_FUN_FORALL_PUSH1,M_FUN_FORALL_PUSH2,M_FUN_FORALL_PUSH3]);

val EvalM_Eq = Q.store_thm("EvalM_Eq",
`EvalM ro env st exp (PURE a x) H ==> EvalM ro env st exp (PURE (Eq a x) x) ^H`,
fs[EvalM_def, PURE_def, Eq_def]);

val ArrowM_EqSt_elim = Q.store_thm("ArrowM_EqSt_elim",
  `(!st_v. EvalM ro env st exp (ArrowM ro H (EqSt a st_v) b f) H) ==>
   EvalM ro env st exp (ArrowM ro H a b f) ^H`,
  fs[EvalM_def, ArrowP_def, ArrowM_def]
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum (qspec_then `st` strip_assume_tac)
  \\ evaluate_unique_result_tac
  \\ fs[PURE_def] \\ rw[]
  \\ ntac 2 (POP_ASSUM (fn x => ALL_TAC))
  \\ rw[ArrowP_def]
  \\ last_x_assum (qspec_then `st1` strip_assume_tac)
  \\ rw[]
  \\ fs[ArrowP_def,EqSt_def]
  \\ fs[GSYM AND_IMP_INTRO]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum drule \\ disch_then strip_assume_tac
  \\ IMP_RES_TAC evaluate_unique_result \\ rw[] \\ fs[] \\ rw[]);

val ArrowP_EqSt_elim = Q.store_thm("ArrowP_EqSt_elim",
  `(!st_v. ArrowP ro H (EqSt a st_v) b f v) ==> ArrowP ro ^H a b f v`,
  fs[EqSt_def, ArrowP_def, ArrowM_def] \\ metis_tac[]);

(* otherwise *)

val EvalM_otherwise = Q.store_thm("EvalM_otherwise",
  `!H b n. ((a1 ==> EvalM ro env st exp1 (MONAD a b x1) H) /\
   (!st i. a2 st ==> EvalM ro (write n i env) st exp2 (MONAD a b x2) H)) ==>
   (a1 /\ !st'. (CONTAINER(SND(x1 st) = st') ==> a2 st')) ==>
   EvalM ro env st (Handle exp1 [(Pvar n,exp2)]) (MONAD a b (x1 otherwise x2)) ^H`,
  SIMP_TAC std_ss [EvalM_def, EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ `a1` by metis_tac[] \\ fs[]
  \\ last_x_assum drule \\ rw[]
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
  \\ disch_then(qspecl_then[`v`]strip_assume_tac)
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
    (a2 ==> EvalM ro env st x2 (a b2) H) /\
    (a3 ==> EvalM ro env st x3 (a b3) H) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM ro env st (If x1 x2 x3) (a (if b1 then b2 else b3)) ^H)`,
  rpt strip_tac \\ fs[]
  \\ `∀H. EvalM ro env st x1 (PURE BOOL b1) ^H` by metis_tac[Eval_IMP_PURE]
  \\ fs[EvalM_def,PURE_def, BOOL_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then strip_assume_tac
  \\ simp[Once evaluate_cases]
  \\ simp_tac(srw_ss()++DNF_ss)[]
  \\ disj1_tac
  \\ asm_exists_tac
  \\ simp[do_if_def]
  \\ rw[]
  >>  fs[CONTAINER_def]
  >> IMP_RES_TAC REFS_PRED_FRAME_imp
  >> first_x_assum drule \\ rw[]
  >> evaluate_unique_result_tac
  >> metis_tac[REFS_PRED_FRAME_trans]);

(* Let *)

val EvalM_Let = Q.store_thm("EvalM_Let",
  `!H. Eval env exp (a res) /\
    (!v. a res v ==> EvalM ro (write name v env) st body (b (f res)) H) ==>
    EvalM ro env st (Let (SOME name) exp body) (b (LET f res)) ^H`,
  rw[]
  \\ drule Eval_IMP_PURE \\ rw[]
  \\ fs[EvalM_def]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then strip_assume_tac
  \\ simp[Once evaluate_cases,GSYM write_def,namespaceTheory.nsOptBind_def]
  \\ srw_tac[DNF_ss][]
  \\ fs[PURE_def] \\ rveq
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ asm_exists_tac \\ fs[]
  \\ last_x_assum drule \\ rw[]
  \\ IMP_RES_TAC REFS_PRED_FRAME_imp
  \\ first_x_assum drule \\ disch_then strip_assume_tac
  \\ evaluate_unique_result_tac
  \\ metis_tac[REFS_PRED_FRAME_trans]);

(* PMATCH *)

val EvalM_PMATCH_NIL = Q.store_thm("EvalM_PMATCH_NIL",
  `!H b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      EvalM ro env st (Mat x []) (b (PMATCH xv [])) ^H`,
  rw[ml_translatorTheory.CONTAINER_def]);


val EvalM_PMATCH = Q.store_thm("EvalM_PMATCH",
  `!H b a x xv.
      ALL_DISTINCT (pat_bindings pt []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval env x (a xv) ⇒
      (pt1 xv ⇒ EvalM ro env st (Mat x ys) (b (PMATCH xv yrs)) H) ⇒
      EvalPatRel env a pt pat ⇒
      (∀env2 vars.
        EvalPatBind env a pt pat vars env2 ∧ pt2 vars ⇒
        EvalM ro env2 st e (b (res vars)) H) ⇒
      (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ pt2 vars) ∧
      ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ pt1 xv) ⇒
      EvalM ro env st (Mat x ((pt,e)::ys))
        (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs))) ^H`,
  rw[EvalM_def] >>
  drule Eval_IMP_PURE >> rw[] >>
  fs[EvalM_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_x_assum drule >>
  disch_then strip_assume_tac >>
  fs[PURE_def] \\ rveq \\
  srw_tac[DNF_ss][] \\ disj1_tac \\
  asm_exists_tac \\ fs[] \\
  rw[Once evaluate_cases,PULL_EXISTS] >>
  IMP_RES_TAC REFS_PRED_FRAME_imp >> (**)
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    qpat_x_assum`pt1 xv ⇒ $! _`kall_tac >>
    qpat_x_assum`_ ==> pt1 xv`kall_tac >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    fs[PMATCH_ROW_COND_def] \\
    last_x_assum (qspec_then `s2.refs` ASSUME_TAC) \\ rw[] \\
    `EvalPatBind env a pt pat vars (env with v := nsAppend (alist_to_ns env2) env.v)`
    by (
      simp[EvalPatBind_def,sem_env_component_equality] \\
      qexists_tac `v` >> fs[] >>
      qspecl_then[`s2.refs`,`pt`,`v`,`[]`,`env`]mp_tac(CONJUNCT1 pmatch_imp_Pmatch) \\
      simp[] \\
      metis_tac[] ) \\
    first_x_assum drule \\ simp[]
    \\ disch_then(qspec_then`s2`mp_tac)
    \\ disch_then drule
    \\ disch_then strip_assume_tac \\ fs[]
    \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars) = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >>
    evaluate_unique_result_tac >>
    metis_tac[REFS_PRED_FRAME_trans]) >>
  drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match)
  \\ disch_then drule \\ disch_then drule
  \\ simp[] \\ strip_tac \\
  first_x_assum(qspec_then`s`mp_tac) \\
  disch_then drule \\
  simp[Once evaluate_cases,PULL_EXISTS] \\
  rw[] \\ imp_res_tac determTheory.big_exp_determ \\ fs[] \\ rw[] \\
  asm_exists_tac \\ fs[] \\
  fs[PMATCH_def,PMATCH_ROW_def] \\
  metis_tac[]);

(* Exception handling *)
val write_list_def = Define `
  (write_list [] [] env = env) /\
  (write_list (n::nl) (v::vl) env = write_list nl vl (write n v env))`;

val pats_bindings_MAP_Pvar = Q.prove(
 `!bind_names already_bound.
  pats_bindings (MAP (\x. Pvar x) bind_names) already_bound =
  (REVERSE bind_names) ++ already_bound`,
  Induct_on `bind_names` >> rw[pat_bindings_def]);

val ALL_DISTINCT_pats_bindings = Q.prove(
 `!bind_names. ALL_DISTINCT bind_names ==>
  ALL_DISTINCT (pats_bindings (MAP (λx. Pvar x) bind_names) [])`,
  Induct_on `bind_names` >> rw[pat_bindings_def]
  \\ rw[pats_bindings_MAP_Pvar]
  \\ PURE_ONCE_REWRITE_TAC[GSYM ALL_DISTINCT_REVERSE]
  \\ PURE_REWRITE_TAC[REVERSE_APPEND]
  \\ rw[]);

val pmatch_list_MAP_Pvar = Q.prove(
 `!bind_names paramsv env already_bound s.
  LENGTH paramsv = LENGTH bind_names==>
  pmatch_list env s (MAP (λx. Pvar x) bind_names) paramsv already_bound = Match ((REVERSE(ZIP (bind_names,paramsv))) ++ already_bound)`,
  Induct_on `bind_names` >> rw[pmatch_def]
  \\ Cases_on `paramsv` \\ fs[pmatch_def]);

val nsAppend_append = Q.prove(
 `!a b env. nsAppend (Bind (a ++ b) []) env = nsAppend (Bind a []) (nsAppend (Bind b []) env)`,
  Induct_on `a` >> rw[namespaceTheory.nsAppend_def]);

val write_list_eq = Q.prove(
 `!bind_names paramsv l1 l2 cenv.
  LENGTH paramsv = LENGTH bind_names ==>
  write_list bind_names paramsv (sem_env (Bind l1 l2) cenv) = sem_env (Bind ((REVERSE (ZIP (bind_names,paramsv))) ++ l1) l2) cenv`,
  Induct_on `bind_names`
  >> Cases_on `paramsv`
  >> rw[namespaceTheory.nsAppend_def, namespaceTheory.alist_to_ns_def, write_list_def, write_def]
  >> rw (TypeBase.updates_of ``:v sem_env``)
  >> rw[namespaceTheory.nsBind_def]);

val nsAppend_write_list_eq = Q.prove(
 `!bind_names paramsv env.
  LENGTH paramsv = LENGTH bind_names ==>
  env with v := nsAppend (alist_to_ns (REVERSE (ZIP (bind_names,paramsv)))) env.v = write_list bind_names paramsv env`,
  rw[namespaceTheory.nsAppend_def, namespaceTheory.alist_to_ns_def]
  \\ Cases_on `env`
  \\ Cases_on `n`
  \\ rw[write_list_eq]
  \\ rw[sem_env_component_equality]
  \\ rw[namespaceTheory.nsAppend_def]);

val prove_EvalM_handle =
  rw[EvalM_def]
  \\ rw[Once evaluate_cases]
  \\ `a1` by metis_tac[] \\ fs[]
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ rw[MONAD_def]
  \\ Cases_on `res` >> fs[MONAD_def]
  >> Cases_on `x1 st` >> fs[]
  >> Cases_on `q` >> fs[]
  >> Cases_on `e` >> fs[]
  \\ rw[]
  \\ Cases_on `CORRECT_CONS b`
  >-(
      rw[]
      (* Instantiate the appropriate assumptions, throw away the others *)
      \\ first_x_assum (qspecl_then [`r`, `b`] assume_tac) \\ fs[CONTAINER_def]
      \\ first_x_assum drule \\ rw[]
      \\ last_x_assum(qspecl_then[`st`, `b`, `r`] drule) \\ rw[]
      \\ last_x_assum(fn x => ALL_TAC)
      \\ last_x_assum drule \\ rw[]
      \\ last_x_assum(fn x => ALL_TAC)
      (* evaluate *)
      \\ rw[Once evaluate_cases]
      (* Pattern matching *)
      \\ fs[pat_bindings_def]
      \\ drule ALL_DISTINCT_pats_bindings \\ rw[]
      \\ fs[pmatch_def,lookup_cons_def,same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
      \\ drule pmatch_list_MAP_Pvar \\ rw[]
      \\ POP_ASSUM (fn x => ALL_TAC)
      (* Apply the assumption evaluate assumption *)
      \\ first_x_assum drule \\ rw[]
      \\ first_x_assum drule \\ rw[]
      \\ IMP_RES_TAC REFS_PRED_FRAME_imp
      \\ first_x_assum drule \\ rw[]
      \\ fs[with_same_refs]
      \\ rw[nsAppend_write_list_eq]
      \\ evaluate_unique_result_tac
      (* Last simplifications*)
      \\ Cases_on `x2 b r` >> fs[]
      \\ Cases_on `q` >> fs[]
      \\ Cases_on `res` >> fs[]
      >> IMP_RES_TAC REFS_PRED_FRAME_trans
      >> Cases_on `e` >> fs[])
  \\ rw[]
  (* Throw away *)
  \\ last_x_assum(fn x => ALL_TAC)
  \\ last_x_assum(qspec_then `st` ASSUME_TAC)
  (* Branching *)
  \\ `handle_fun x1 x2 st = x1 st` by (
      first_x_assum irule
      \\ rw[] \\ DISJ1_TAC
      \\ metis_tac[])
  \\ rw[Once evaluate_cases]
  \\ last_x_assum(fn x => ALL_TAC)
  \\ last_x_assum drule \\ rw[]
  (* pattern matching *)
  \\ fs[pat_bindings_def]
  \\ drule ALL_DISTINCT_pats_bindings \\ rw[]
  \\ fs[pmatch_def]
  \\ fs[lookup_cons_def, same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[Once evaluate_cases];

val EvalM_handle_MODULE = Q.store_thm("EvalM_handle_MODULE",
 `!module_name cons_name CORRECT_CONS PARAMS_CONDITIONS EXN_TYPE handle_fun x1 x2 arity a2 bind_names a H.
  (!s E s1. CORRECT_CONS E ==>
            x1 s = (Failure E, s1) ==>
            handle_fun x1 x2 s = x2 E s1) ==>
  (!s. (!E s1. CORRECT_CONS E ==> x1 s <> (Failure E, s1)) ==>
       handle_fun x1 x2 s = x1 s) ==>
  (!E ev. EXN_TYPE E ev ==>
          CORRECT_CONS E ==>
   ?paramsv.
   ev = Conv (SOME (cons_name,TypeExn (Long module_name (Short cons_name)))) paramsv /\
   PARAMS_CONDITIONS E paramsv /\ LENGTH paramsv = arity) ==>
  (!E ev. EXN_TYPE E ev ==>
   ~CORRECT_CONS E ==>
   ?paramsv cons_name_1.
   ev = Conv (SOME (cons_name_1,TypeExn (Long module_name (Short cons_name_1)))) paramsv /\
   cons_name_1 <> cons_name) ==>
  ALL_DISTINCT bind_names ==>
  LENGTH bind_names = arity ==>
  lookup_cons cons_name env = SOME (arity,TypeExn (Long module_name (Short cons_name))) ==>
  ((a1 ==> EvalM ro env st exp1 (MONAD a EXN_TYPE x1) H) /\
  (!st E paramsv.
     PARAMS_CONDITIONS E paramsv ==>
     a2 st E ==>
     EvalM ro (write_list bind_names paramsv env) st exp2 (MONAD a EXN_TYPE (x2 E)) H)) ==>
  (!st' E. a1 /\ (CONTAINER(x1 st = (Failure E, st') /\ CORRECT_CONS E) ==> a2 st' E)) ==>
  EvalM ro env st (Handle exp1 [(Pcon (SOME (Short cons_name)) (MAP (\x. Pvar x) bind_names),exp2)])
    (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  prove_EvalM_handle);

val EvalM_handle_SIMPLE = Q.store_thm("EvalM_handle_SIMPLE",
 `!cons_name CORRECT_CONS PARAMS_CONDITIONS EXN_TYPE handle_fun x1 x2 arity a2 bind_names a H.
  (!s E s1. CORRECT_CONS E ==>
            x1 s = (Failure E, s1) ==>
            handle_fun x1 x2 s = x2 E s1) ==>
  (!s. (!E s1. CORRECT_CONS E ==> x1 s <> (Failure E, s1)) ==>
       handle_fun x1 x2 s = x1 s) ==>
  (!E ev. EXN_TYPE E ev ==>
          CORRECT_CONS E ==>
   ?paramsv.
   ev = Conv (SOME (cons_name,TypeExn (Short cons_name))) paramsv /\
   PARAMS_CONDITIONS E paramsv /\ LENGTH paramsv = arity) ==>
  (!E ev. EXN_TYPE E ev ==>
   ~CORRECT_CONS E ==>
   ?paramsv cons_name_1.
   ev = Conv (SOME (cons_name_1,TypeExn (Short cons_name_1))) paramsv /\
   cons_name_1 <> cons_name) ==>
  ALL_DISTINCT bind_names ==>
  LENGTH bind_names = arity ==>
  lookup_cons cons_name env = SOME (arity,TypeExn (Short cons_name)) ==>
  ((a1 ==> EvalM ro env st exp1 (MONAD a EXN_TYPE x1) H) /\
  (!st E paramsv.
     PARAMS_CONDITIONS E paramsv ==>
     a2 st E ==>
     EvalM ro (write_list bind_names paramsv env) st exp2 (MONAD a EXN_TYPE (x2 E)) H)) ==>
  (!st' E. a1 /\ (CONTAINER(x1 st = (Failure E, st') /\ CORRECT_CONS E) ==> a2 st' E)) ==>
  EvalM ro env st (Handle exp1 [(Pcon (SOME (Short cons_name)) (MAP (\x. Pvar x) bind_names),exp2)])
    (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  prove_EvalM_handle);

val ZIP3_def = Define `
  ZIP3 ([],[],[]) = [] /\
  ZIP3 (x1::l1,x2::l2,x3::l3) = (x1,x2,x3)::(ZIP3 (l1,l2,l3))`;

val LIST_CONJ_def = Define `
  LIST_CONJ [] = T /\
  LIST_CONJ (x::l) = (x /\ LIST_CONJ l)`;

val LIST_CONJ_APPEND = Q.prove(
 `!a b. LIST_CONJ (a++b) = (LIST_CONJ a /\ LIST_CONJ b)`,
  Induct_on `a` >> rw[LIST_CONJ_def]
  \\ EQ_TAC >> rw[LIST_CONJ_def]);

val LIST_CONJ_REVERSE = Q.prove(
 `!x. LIST_CONJ (REVERSE x) = LIST_CONJ x`,
  Induct_on `x` >> rw[LIST_CONJ_def, LIST_CONJ_APPEND]
  \\ EQ_TAC >> rw[]);

val LIST_CONJ_evaluate_list_aux = Q.prove(
 `!n exprs EVAL_CONDS s env.
  LENGTH exprs = n ==>
  LENGTH EVAL_CONDS = n ==>
  LIST_CONJ (MAP (\(exp,P). Eval env exp P) (ZIP (exprs,EVAL_CONDS))) ==>
  ?junk vs.
  evaluate_list F env s exprs (s with refs := s.refs ++ junk,Rval vs) /\
  LIST_CONJ (MAP (\(P,v). P v) (ZIP(EVAL_CONDS,vs))) /\
  LENGTH vs = n`,
  Induct_on `n`
  >-(
      rw[Once evaluate_cases]
      \\ qexists_tac `[]`
      \\ rw[with_same_refs])
  \\ Cases_on `exprs`
  \\ Cases_on `EVAL_CONDS`
  \\ rw[LIST_CONJ_def,ZIP3_def]
  \\ rw[Once evaluate_cases]
  \\ qpat_x_assum `Eval _ _ _` (fn x => REWRITE_RULE[Eval_def] x |> ASSUME_TAC)
  \\ first_x_assum (qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ drule evaluate_empty_state_IMP \\ rw[]
  \\ evaluate_unique_result_tac
  \\ last_x_assum (qspecl_then [`t`, `t'`, `(s with refs := s.refs ⧺ refs')`, `env`] ASSUME_TAC)
  \\ fs[]
  \\ POP_ASSUM drule \\ rw[]
  \\ qexists_tac `refs' ++ junk`
  \\ qexists_tac `res::vs`
  \\ rw[LIST_CONJ_def])

val LIST_CONJ_evaluate_list = Q.prove(
 `!s exprs EVAL_CONDS env.
  LENGTH exprs = LENGTH EVAL_CONDS ==>
  LIST_CONJ (MAP (\(exp,P). Eval env exp P) (ZIP (exprs,EVAL_CONDS))) ==>
  ?junk vs.
  evaluate_list F env s (REVERSE exprs) (s with refs := s.refs ++ junk,Rval vs) /\
  LIST_CONJ (MAP (\(P,v). P v) (ZIP(REVERSE EVAL_CONDS,vs))) /\
  LENGTH vs = LENGTH EVAL_CONDS`,
  rw[]
  \\ irule LIST_CONJ_evaluate_list_aux
  >> rw[Once (GSYM LIST_CONJ_REVERSE), GSYM MAP_REVERSE,REVERSE_ZIP,REVERSE_REVERSE]);

fun evaluate_list_unique_result_tac (g as (asl, w)) = let
    val asl = List.map ASSUME asl
    val uniques = mapfilter (MATCH_MP evaluate_list_unique_result) asl
in simp uniques g end;

val prove_EvalM_raise =
  rw[EvalM_def]
  \\ ntac 2 (rw[Once evaluate_cases])
  \\ rw[do_con_check_def,build_conv_def]
  \\ fs [lookup_cons_def]
  \\ rw[namespaceTheory.id_to_n_def]
  (* qspec and Q.ISPEC don't work?? *)
  \\ drule (ISPEC ``(s : 'd state)`` LIST_CONJ_evaluate_list)
  (**)
  \\ disch_then drule
  \\ rw[]
  \\ evaluate_list_unique_result_tac
  \\ qexists_tac `s with refs := s.refs ⧺ junk`
  \\ fs[MONAD_def]
  \\ rw[Once evaluate_cases]
  \\ rw[do_con_check_def,build_conv_def]
  \\ evaluate_list_unique_result_tac
  \\ last_x_assum (qspec_then `REVERSE vs` assume_tac) \\ fs[]
  \\ first_x_assum drule
  \\ rw[Once (GSYM LIST_CONJ_REVERSE), GSYM MAP_REVERSE,REVERSE_ZIP,REVERSE_REVERSE]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append];

val EvalM_raise_MODULE = Q.store_thm("EvalM_raise_MODULE",
 `!module_name cons_name EXN_TYPE EVAL_CONDS arity E exprs f a H.
  (!values.
   LENGTH values = arity ==>
   LIST_CONJ (MAP (\(P,v). P v) (ZIP(EVAL_CONDS,values))) ==>
   EXN_TYPE E (Conv (SOME (cons_name, TypeExn (Long module_name (Short cons_name)))) values)) ==>
  f st = (Failure E, st) ==>
  LENGTH exprs = arity ==>
  LENGTH EVAL_CONDS = arity ==>
  lookup_cons cons_name env = SOME (arity, TypeExn (Long module_name (Short cons_name))) ==>
  LIST_CONJ (MAP (\(exp,P). Eval env exp P) (ZIP (exprs,EVAL_CONDS))) ==>
  EvalM ro env st (Raise (Con (SOME (Short cons_name)) exprs))
    (MONAD a EXN_TYPE f) H`,
  prove_EvalM_raise);

val EvalM_raise_SIMPLE = Q.store_thm("EvalM_raise_SIMPLE",
 `!cons_name EXN_TYPE EVAL_CONDS arity E exprs f a H.
  (!values.
   LENGTH values = arity ==>
   LIST_CONJ (MAP (\(P,v). P v) (ZIP(EVAL_CONDS,values))) ==>
   EXN_TYPE E (Conv (SOME (cons_name, TypeExn (Short cons_name))) values)) ==>
  f st = (Failure E, st) ==>
  LENGTH exprs = arity ==>
  LENGTH EVAL_CONDS = arity ==>
  lookup_cons cons_name env = SOME (arity, TypeExn (Short cons_name)) ==>
  LIST_CONJ (MAP (\(exp,P). Eval env exp P) (ZIP (exprs,EVAL_CONDS))) ==>
  EvalM ro env st (Raise (Con (SOME (Short cons_name)) exprs))
    (MONAD a EXN_TYPE f) H`,
  prove_EvalM_raise);

(* read and update refs *)

val EvalM_read_heap = Q.store_thm("EvalM_read_heap",
`!vname loc TYPE EXC_TYPE H get_var.
  (nsLookup env.v (Short vname) = SOME loc) ==>
  EvalM ro env st (App Opderef [Var (Short vname)])
  (MONAD TYPE EXC_TYPE (λrefs. (Success (get_var refs), refs)))
  ((λrefs. REF_REL TYPE loc (get_var refs) * H refs), (p:'ffi ffi_proj))`,
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
      qexists_tac `s`
      \\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
      \\ first_x_assum (qspec_then `[]` assume_tac) \\ fs[]
      \\ fs[with_same_refs, with_same_ffi]
      \\ fs[REFS_PRED_FRAME_same]
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
  EvalM ro env st (App Opassign [Var (Short vname); exp])
  ((MONAD UNIT_TYPE EXC_TYPE) (λrefs. (Success (), set_var x refs)))
  ((λrefs. REF_REL TYPE loc (get_var refs) * H refs * &PINV refs), p:'ffi ffi_proj)`,
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
  (* \\ first_x_assum(qspec_then `junk` strip_assume_tac) *)
  \\ fs[PURE_def, CONTAINER_def] \\ rw[]
  \\ asm_exists_tac \\ fs[]
  \\ fs[do_app_def]
  \\ qexists_tac `Rval (Conv NONE [])`
  \\ qexists_tac `set_var x st`
  \\ qexists_tac `LUPDATE (Refv v) loc' s2.refs`
  \\ qexists_tac `s2.ffi`
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
  \\ rw[]
  >-(rw[] \\ fs[state_component_equality] \\ rw[])
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

(* Validity of a store extension *)
val valid_state_refs_frame_extension = Q.prove(
`!H junk. A (cons x) res ==> (STATE_REFS A ptrs state * H) (st2heap (p:'ffi ffi_proj) s) ==>
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
`A (cons x) res ==> REFS_PRED (STATE_REFS A ptrs,p:'ffi ffi_proj) refs s ==>
REFS_PRED (STATE_REFS A (Loc (LENGTH (s.refs ++ junk))::ptrs),p) (cons x ::refs) (s with refs := s.refs ++ junk ++ [Refv res])`,
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
   (!rv r.
      EvalM ro (write rname rv env) ((cons x)::st) exp
        (MONAD TYPE MON_EXN_TYPE (f r))
        (STATE_REFS A (rv::ptrs),p:'ffi ffi_proj)) ==>
   EvalM ro env st (Let (SOME rname) (App Opref [xexpr]) exp)
     (MONAD TYPE MON_EXN_TYPE (ref_bind (Mref cons x) f (Mpop_ref e)))
     (STATE_REFS A ptrs,p)`,
  rw[]
  \\ fs[Eval_def]
  \\ rw[EvalM_def]
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[evaluate_list_cases]
  \\ rw[do_app_def]
  \\ rw[store_alloc_def]
  \\ rw[namespaceTheory.nsOptBind_def]
  \\ fs[write_def]
  \\ last_x_assum(qspec_then `Loc (LENGTH refs' + LENGTH s.refs)` ASSUME_TAC)
  \\ first_x_assum(qspec_then `StoreRef (LENGTH st)` ASSUME_TAC)
  \\ fs[with_same_ffi]
  \\ fs[EvalM_def]
  \\ first_x_assum(qspecl_then [`s with refs := s.refs ++ refs' ++ [Refv res]`] ASSUME_TAC)
  \\ IMP_RES_TAC valid_state_refs_extension
  \\ first_x_assum(qspec_then`refs'` ASSUME_TAC)
  \\ fs[]
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
  \\ qspecl_then [`F'`, `refs'`] IMP_RES_TAC valid_state_refs_frame_extension
  \\ ntac 2 (POP_ASSUM(fn x => ALL_TAC))
  \\ fs[]
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ fs[STAR_ASSOC]
  \\ irule valid_state_refs_reduction
  \\ metis_tac[]);

(* Validity of a deref operation *)
val STATE_REFS_EXTRACT = Q.prove(
`!ptrs1 r ptrs2 refs TYPE H (p:'ffi ffi_proj) s. ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) ==>
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
`!ptrs1 r ptrs2 refs1 x refs2 TYPE H (p:'ffi ffi_proj) s.
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
`!ptrs1 r ptrs2 refs1 y refs2 TYPE H (p:'ffi ffi_proj) s.
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
`!ptrs1 r ptrs2 refs TYPE H (p:'ffi ffi_proj) s. ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) <=>
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
`!ptrs1 r ptrs2 refs1 x refs2 TYPE H (p:'ffi ffi_proj) s.
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
`(l ~~>> res * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l (s.refs ++ junk) = SOME res`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP
\\ IMP_RES_TAC st2heap_CELL_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_lookup_def]);

val store_lookup_REF_st2heap = Q.store_thm("store_lookup_REF_st2heap",
`(Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l s.refs = SOME (Refv v)`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
\\ IMP_RES_TAC st2heap_REF_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ first_x_assum (qspec_then `[]` assume_tac)
\\ fs[store_lookup_def]);

val store_lookup_REF_st2heap_junk = Q.store_thm("store_lookup_REF_st2heap_junk",
`(Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l (s.refs ++ junk) = SOME (Refv v)`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_REF
\\ IMP_RES_TAC st2heap_REF_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ fs[store_lookup_def]);

val store_lookup_ARRAY_st2heap = Q.store_thm("store_lookup_ARRAY_st2heap",
`(ARRAY (Loc l) av * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l s.refs = SOME (Varray av)`,
rw[]
\\ IMP_RES_TAC STATE_EXTRACT_FROM_HPROP_ARRAY
\\ IMP_RES_TAC st2heap_ARRAY_MEM
\\ IMP_RES_TAC store2heap_IN_LENGTH
\\ first_x_assum (qspec_then `[]` assume_tac)
\\ fs[store_lookup_def]);

val EvalM_Mdref = Q.store_thm("EvalM_Mdref",
`nsLookup env.v (Short rname) = SOME rv ==>
r = LENGTH ptrs2 ==>
EvalM ro env st (App Opderef [Var (Short rname)])
(MONAD TYPE (\x v. F) (Mdref e (StoreRef r))) (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2),p:'ffi ffi_proj)`,
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
\\ qexists_tac `s`
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
\\ irule H_STAR_GC_SAT_IMP \\ fs[]);

(* Validity of an assigment operation *)
val store_assign_REF_st2heap = Q.store_thm("store_assign_REF_st2heap",
`(Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==>
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
REFS_PRED_FRAME ro (STATE_REFS TYPE (ptrs1 ++ [Loc l] ++ ptrs2),p:'ffi ffi_proj) (refs, s)
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
EvalM ro env st (App Opassign [Var (Short rname); xexpr])
(MONAD UNIT_TYPE (\x v. F) (Mref_assign e (StoreRef r) x)) (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2),p:'ffi ffi_proj)`,
rw[]
\\ fs[EvalM_def]
\\ ntac 2 (rw[Once evaluate_cases])
\\ fs[Eval_def]
\\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
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
\\ qexists_tac `s with refs := LUPDATE (Refv res) l (s.refs ++ refs')`
\\ qexists_tac `Rval (Conv NONE [])`
\\ fs[state_component_equality]
\\ qexists_tac `ref_assign (LENGTH ptrs2) x st`
\\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
\\ fs[UPDATE_STATE_REFS]
\\ fs[MONAD_def]
\\ IMP_RES_TAC STATE_REFS_LENGTH
\\ fs[Mref_assign_eq]);

(* Allocation of the initial store for dynamic references *)
val STATE_REFS_EXTEND = Q.store_thm(
"STATE_REFS_EXTEND",
`!H s refs. (STATE_REFS A ptrs refs * H) (st2heap (p:'ffi ffi_proj) s) ==>
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
(REF (Loc loc) v * H refs) (st2heap (p:'ffi ffi_proj) s) ==>
!junk. evaluate F env (s with refs := s.refs ++ junk) (App Opderef [Var (Short vname)]) (s with refs := s.refs ++ junk, Rval v)`,
rw[]
\\ rw[Once evaluate_cases]
\\ CONV_TAC SWAP_EXISTS_CONV
\\ qexists_tac `s with refs := s.refs ++ junk`
\\ fs[state_component_equality]
\\ rw[Once evaluate_cases, evaluate_list_cases]
\\ rw[do_app_def]
\\ IMP_RES_TAC store_lookup_REF_st2heap_junk
\\ fs[]);

val do_app_Alength_ARRAY = Q.prove(
`(ARRAY rv v * H) (st2heap (p:'ffi ffi_proj) s) ==>
do_app (s.refs, s.ffi) Alength [rv] =
SOME ((s.refs, s.ffi), Rval (Litv(IntLit(int_of_num(LENGTH v)))))`,
rw[do_app_def]
\\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
\\ IMP_RES_TAC store_lookup_CELL_st2heap
\\ first_x_assum(qspec_then `[]` ASSUME_TAC)
\\ fs[]);

val EvalM_R_Marray_length = Q.store_thm("EvalM_R_Marray_length",
  `!vname loc TYPE EXC_TYPE H get_arr x env.
    nsLookup env.v (Short vname) = SOME loc ==>
    EvalM ro env st (App Alength [App Opderef [Var (Short vname)]])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ fs[REFS_PRED_def, RARRAY_REL_def, RARRAY_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ first_x_assum(qspec_then `[]` ASSUME_TAC) \\ fs[with_same_refs]
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Marray_length_def]
  \\ fs[MONAD_def]
  \\ qexists_tac `s`
  \\ fs[state_component_equality]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM STAR_COMM)]
  \\ fs[GSYM STAR_ASSOC]
    \\ drule do_app_Alength_ARRAY \\ rw[]
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ qexists_tac `Rval (Litv (IntLit (&LENGTH av)))`
  \\ fs[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[REFS_PRED_FRAME_same]);

val do_app_Asub_ARRAY = Q.prove(
`(ARRAY rv v * H) (st2heap (p:'ffi ffi_proj) s) ==>
!junk. do_app (s.refs ++ junk, s.ffi) Asub [rv; Litv (IntLit (&n))] =
if n < LENGTH v then SOME ((s.refs ++ junk, s.ffi), Rval (EL n v))
else SOME ((s.refs ++ junk, s.ffi), Rerr (Rraise (prim_exn "Subscript")))`,
rw[do_app_def]
\\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
\\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
\\ IMP_RES_TAC store_lookup_CELL_st2heap
\\ fs[ABS_NUM_EQ]
\\ Cases_on `n ≥ LENGTH v` \\ fs[]);

val EvalM_R_Marray_sub_subscript = Q.store_thm("EvalM_R_Marray_sub_subscript",
  `!vname loc TYPE EXC_TYPE H get_arr e env n nexp.
   EXC_TYPE e (prim_exn "Subscript") ==>
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   Eval env nexp (NUM n) ==>
   EvalM ro env st (App Asub [App Opderef [Var (Short vname)]; nexp])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ first_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ POP_ASSUM(qspec_then `refs'` ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ fs[STAR_ASSOC]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ rw[]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC do_app_Asub_ARRAY
  \\ first_x_assum (qspecl_then [`n`, `refs'`] assume_tac)
  \\ fs[]
  \\ Cases_on `n < LENGTH (get_arr st)`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def]
     \\ qexists_tac `s with refs := s.refs ++ refs'`
     \\ qexists_tac `Rval (EL n av)`
     \\ fs[state_component_equality]
     \\ fs[Msub_eq]
     \\ fs[LIST_REL_EL_EQN]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[with_same_ffi]
  \\ qexists_tac `s with refs := s.refs ++ refs'`
  \\ qexists_tac `Rerr (Rraise (prim_exn "Subscript"))`
  \\ qexists_tac `st`
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ fs[REFS_PRED_FRAME_append]);

val EvalM_R_Marray_sub_handle = Q.store_thm("EvalM_R_Marray_sub_handle",
  `!vname loc TYPE EXC_TYPE H get_arr e rexp env n nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   EvalM ro env st (Handle (App Asub [App Opderef [Var (Short vname)]; nexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[Once evaluate_cases,evaluate_list_cases]
  \\ last_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ POP_ASSUM(qspec_then `refs'` ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ fs[STAR_ASSOC]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ rw[]
  \\ rw[Once evaluate_cases,evaluate_list_cases]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC do_app_Asub_ARRAY
  \\ first_x_assum (qspecl_then [`n`, `refs'`] assume_tac)
  \\ evaluate_unique_result_tac
  \\ Cases_on `n < LENGTH (get_arr st)`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def]
     \\ qexists_tac `s with refs := s.refs ++ refs'`
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
  \\ first_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[with_same_ffi]
  \\ evaluate_unique_result_tac
  \\ fs[]
  \\ qexists_tac `s with refs := s.refs ++ refs' ++ refs''`
  \\ qexists_tac `Rerr (Rraise res)`
  \\ fs[state_component_equality]
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rw[REFS_PRED_FRAME_append]);

val EvalM_R_Marray_update_subscript = Q.store_thm("EvalM_R_Marray_update_subscript",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr e env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   EXC_TYPE e (prim_exn "Subscript") ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[]
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[] \\ rw[]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ first_x_assum(qspec_then `refs' ++ refs''` ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ rw[Once evaluate_list_cases]
  \\ fs[]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ IMP_RES_TAC STATE_APPEND_JUNK
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC]))
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
         (s.refs ++ refs' ++ refs'')`
      >> fs[state_component_equality]
      >> qexists_tac `Rval (Conv NONE [])`
      >> rw[]
      >> qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      >> fs[MONAD_def, Marray_update_def, Mupdate_eq]
      >> fs[REFS_PRED_FRAME_def]
      >> rw[state_component_equality]
      >> fs[Once (GSYM with_same_refs)]
      >> POP_ASSUM(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      >> POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC)
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
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ IMP_RES_TAC store_lookup_CELL_st2heap
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ POP_ASSUM(qspec_then `[]` ASSUME_TAC)
  \\ rw[Once evaluate_cases, evaluate_list_cases]
  \\ fs [with_same_refs, with_same_ffi] \\ rw [do_app_def]
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ qexists_tac `s with refs := s.refs ++ refs' ++ refs''`
  \\ qexists_tac `Rerr (Rraise (prim_exn "Subscript"))`
  \\ qexists_tac `st`
  \\ rw[with_same_ffi]
  \\ metis_tac[REFS_PRED_FRAME_append, GSYM APPEND_ASSOC]);

val EvalM_R_Marray_update_handle = Q.store_thm("EvalM_R_Marray_update_handle",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr e rexp env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (Handle (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ IMP_RES_TAC REF_EXISTS_LOC
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[]
  \\ rw[Once evaluate_cases]
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ first_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ fs[]
  \\ rw[]
  \\ IMP_RES_TAC evaluate_Opdref_REF
  \\ first_x_assum(qspec_then `refs' ++ refs''` ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
  \\ rw[Once evaluate_list_cases]
  \\ fs[]
  \\ rw[Once evaluate_list_cases]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ IMP_RES_TAC STATE_APPEND_JUNK
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC]))
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
         (s.refs ++ refs' ++ refs'')`
      >> fs[state_component_equality]
      >> qexists_tac `Rval (Conv NONE [])`
      >> rw[]
      >> qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      >> fs[MONAD_def, Marray_update_def, Mupdate_eq]
      >> fs[REFS_PRED_FRAME_def]
      >> rw[state_component_equality]
      >> fs[Once (GSYM with_same_refs)]
      >> POP_ASSUM(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      >> POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC)
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
  \\ fs [with_same_refs] \\ rw [do_app_def]
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
  \\ last_x_assum(qspec_then `s.refs ++ (refs' ++ refs'')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ qexists_tac `s with refs := s.refs ++ refs' ++ refs'' ++ refs'''` \\ fs []
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

val EvalM_R_Marray_alloc = Q.store_thm("EvalM_R_Marray_alloc",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr n x env nexp xexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (App Opassign [Var (Short vname); App Aalloc [nexp; xexp]])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_alloc set_arr n x))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Once evaluate_cases]
  \\ first_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
  \\ rw[Once evaluate_cases]
  \\ rw[do_app_def]
  \\ rw[store_alloc_def]
  \\ rw[with_same_ffi]
  \\ rw[Once evaluate_cases]
  \\ qpat_x_assum `REFS_PRED H1 st s` (fn x => PURE_REWRITE_RULE[REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
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
  \\ qexists_tac `store2heap_aux (LENGTH(LUPDATE (Refv (Loc loc)) l s.refs ++ refs' ++ refs'')) [Varray (REPLICATE n res)]`
  \\ qexists_tac `st2heap p (s with
        refs := LUPDATE (Refv (Loc loc)) l s.refs ++ refs' ++ refs'')`
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
  \\ POP_ASSUM(qspec_then `refs' ++ refs''` ASSUME_TAC)
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

(* Fixed-size arrays *)
val EvalM_F_Marray_length = Q.store_thm("EvalM_F_Marray_length",
  `!vname loc TYPE EXC_TYPE H get_arr x env.
    nsLookup env.v (Short vname) = SOME loc ==>
    EvalM ro env st (App Alength [Var (Short vname)])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ ntac 11 (rw[Once evaluate_cases])
  \\ fs[REFS_PRED_def, ARRAY_REL_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_x_assum (fn x => MATCH_MP do_app_Alength_ARRAY x |> ASSUME_TAC)
  \\ fs[with_same_refs, with_same_ffi]
  \\ qexists_tac `s`
  \\ POP_ASSUM (fn x => fs[x])
  \\ fs[MONAD_def, Marray_length_def]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[REFS_PRED_FRAME_same]);

val EvalM_F_Marray_sub_subscript = Q.store_thm("EvalM_F_Marray_sub_subscript",
  `!vname loc TYPE EXC_TYPE H get_arr e env n nexp.
   EXC_TYPE e (prim_exn "Subscript") ==>
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   Eval env nexp (NUM n) ==>
   EvalM ro env st (App Asub [Var (Short vname); nexp])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_x_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum (fn x => MATCH_MP ARRAY_EXISTS_LOC x |> ASSUME_TAC)
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ last_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ first_x_assum (fn x => MATCH_MP do_app_Asub_ARRAY x |> ASSUME_TAC)
  \\ first_x_assum (qspec_then `refs'` assume_tac) \\ fs[]
  \\ Cases_on `n < LENGTH av`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def]
     \\ qexists_tac `s with refs := s.refs ++ refs'`
     \\ qexists_tac `Rval (EL n av)`
     \\ fs[state_component_equality]
     \\ fs[Msub_eq]
     \\ fs[LIST_REL_EL_EQN]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]
     \\ rw[Once evaluate_cases]
     \\ evaluate_unique_result_tac
     \\ ntac 3 (rw[Once evaluate_cases]))
  \\ rw[Once evaluate_cases, with_same_ffi]
  \\ qexists_tac `s with refs := s.refs ++ refs'`
  \\ qexists_tac `Rerr (Rraise (prim_exn "Subscript"))`
  \\ qexists_tac `st`
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq, REFS_PRED_FRAME_append]
  \\ evaluate_unique_result_tac
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ fs[with_same_ffi]);

val EvalM_F_Marray_sub_handle = Q.store_thm("EvalM_F_Marray_sub_handle",
  `!vname loc TYPE EXC_TYPE H get_arr e rexp env n nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   EvalM ro env st (Handle (App Asub [Var (Short vname); nexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_x_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum (fn x => MATCH_MP ARRAY_EXISTS_LOC x |> ASSUME_TAC)
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ rw[Once evaluate_cases,evaluate_list_cases]
  \\ ntac 2 (rw[Once evaluate_cases])
  \\ rw[evaluate_list_cases]
  \\ last_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum (fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ first_x_assum(qspec_then `refs'` ASSUME_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ first_x_assum (fn x => MATCH_MP do_app_Asub_ARRAY x |> ASSUME_TAC)
  \\ first_x_assum (qspec_then `[]` assume_tac) \\ fs[]
  \\ Cases_on `n < LENGTH av`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def]
     \\ qexists_tac `s with refs := s.refs ++ refs'`
     \\ qexists_tac `Rval (EL n av)`
     \\ fs[state_component_equality]
     \\ fs[Msub_eq]
     \\ fs[LIST_REL_EL_EQN]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[with_same_refs]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ ntac 5 (rw[Once evaluate_cases])
  \\ rw[prim_exn_def]
  \\ fs[lookup_cons_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[Once evaluate_cases]
  \\ fs[with_same_ffi]
  \\ first_x_assum (qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC) \\ fs[]
  \\ evaluate_unique_result_tac
  \\ qexists_tac `s with refs := s.refs ++ refs' ++ refs''`
  \\ qexists_tac `Rerr (Rraise res)`
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rw[REFS_PRED_FRAME_append])

val EvalM_F_Marray_update_subscript = Q.store_thm("EvalM_F_Marray_update_subscript",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr e env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   EXC_TYPE e (prim_exn "Subscript") ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (App Aupdate [Var (Short vname); nexp; xexp])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ POP_ASSUM(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP ARRAY_EXISTS_LOC x |> STRIP_ASSUME_TAC)
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ rw[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP (GEN_ALL store_lookup_CELL_st2heap) x |> ASSUME_TAC)
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ fs[]
  (* \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC])) *)
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[]
      \\ first_assum(fn x => MATCH_MP st2heap_CELL_MEM x |> ASSUME_TAC)
      \\ first_assum(fn x => MATCH_MP store2heap_IN_LENGTH x |> ASSUME_TAC)
      \\ fs[store_assign_def, store_v_same_type_def]
      \\ first_assum(fn x => MATCH_MP store2heap_IN_EL x |> ASSUME_TAC)
      \\ fs[]
      \\ qexists_tac `s with refs := LUPDATE (Varray (LUPDATE res n av)) l
         (s.refs ++ refs' ++ refs'')`
      \\ fs[state_component_equality]
      \\ qexists_tac `Rval (Conv NONE [])`
      \\ drule EL_APPEND1 \\ disch_then (qspec_then `refs' ++ refs''` assume_tac)
      \\ reverse(rw[] \\ fs[])
      >-(ntac 2 (qpat_x_assum `_ = _` (fn x => fs [x])))
      \\ qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      \\ fs[MONAD_def, Marray_update_def, Mupdate_eq]
      \\ fs[REFS_PRED_FRAME_def]
      \\ rw[state_component_equality]
      \\ fs[Once (GSYM with_same_refs)]
      \\ POP_ASSUM(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC)
      \\ fs[ARRAY_REL_def, SEP_CLAUSES, SEP_EXISTS_THM]
      \\ qexists_tac `LUPDATE res n av`
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[EVERY2_LUPDATE_same]
      \\ fs[GSYM STAR_ASSOC]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_ARRAY) x |> ASSUME_TAC)
      \\ POP_ASSUM(qspec_then `LUPDATE res n av` ASSUME_TAC)
      \\ fs[])
  \\ fs[with_same_ffi]
  \\ qexists_tac ` s with refs := s.refs ++ refs' ++ refs''`
  \\ qexists_tac `Rerr (Rraise (prim_exn "Subscript"))`
  \\ qexists_tac `st`
  \\ fs[MONAD_def,Marray_update_def,Mupdate_exn_eq]
  \\ metis_tac[REFS_PRED_FRAME_append, GSYM APPEND_ASSOC]);

val EvalM_F_Marray_update_handle = Q.store_thm("EvalM_F_Marray_update_handle",
  `!vname loc TYPE EXC_TYPE H get_arr set_arr e rexp env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons "Subscript" env = SOME (0,TypeExn (Short "Subscript")) ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (Handle (App Aupdate [Var (Short vname); nexp; xexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)`,
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ POP_ASSUM(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP ARRAY_EXISTS_LOC x |> STRIP_ASSUME_TAC)
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ evaluate_unique_result_tac
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ last_x_assum(qspec_then `s.refs ++ (refs' ++ refs'')` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ rw[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP (GEN_ALL store_lookup_CELL_st2heap) x |> ASSUME_TAC)
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ fs[]
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[]
      \\ first_assum(fn x => MATCH_MP st2heap_CELL_MEM x |> ASSUME_TAC)
      \\ first_assum(fn x => MATCH_MP store2heap_IN_LENGTH x |> ASSUME_TAC)
      \\ fs[store_assign_def, store_v_same_type_def]
      \\ first_assum(fn x => MATCH_MP store2heap_IN_EL x |> ASSUME_TAC)
      \\ fs[]
      \\ qexists_tac `s with refs := LUPDATE (Varray (LUPDATE res n av)) l
         (s.refs ++ refs' ++ refs'')`
      \\ fs[state_component_equality]
      \\ qexists_tac `Rval (Conv NONE [])`
      \\ rw[]
      \\ qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      \\ fs[MONAD_def, Marray_update_def, Mupdate_eq]
      \\ fs[REFS_PRED_FRAME_def]
      \\ rw[state_component_equality]
      \\ fs[Once (GSYM with_same_refs)]
      \\ POP_ASSUM(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      \\ POP_ASSUM(qspec_then`refs'++refs''` ASSUME_TAC)
      \\ fs[ARRAY_REL_def, SEP_CLAUSES, SEP_EXISTS_THM]
      \\ qexists_tac `LUPDATE res n av`
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[EVERY2_LUPDATE_same]
      \\ fs[GSYM STAR_ASSOC]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_ARRAY) x |> ASSUME_TAC)
      \\ POP_ASSUM(qspec_then `LUPDATE res n av` ASSUME_TAC)
      \\ fs[])
  \\ fs[with_same_refs]
  \\ ntac 2 (rw[Once evaluate_cases])
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ rw[do_app_def]
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ rw[prim_exn_def]
  \\ rw[Once evaluate_cases]
  \\ evaluate_unique_result_tac
  \\ fs[lookup_cons_def]
  \\ ntac 5 (rw[Once evaluate_cases])
  \\ fs[lookup_cons_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[Once evaluate_cases]
  \\ fs[with_same_ffi]
  \\ evaluate_unique_result_tac
  \\ qexists_tac `s with refs := s.refs ++ refs' ++ refs'' ++ refs'''` \\ fs []
  \\ qexists_tac `Rerr (Rraise res')` \\ fs []
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]);

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
    !(s: unit semanticPrimitives$state). REFS_PRED H st s ==>
    ?s2 res st2.
    evaluate F env s exp (s2, Rval res) /\
    P res /\ REFS_PRED_FRAME T H (st, s) (st2, s2)`;

val LENGTH_Mem_IN_store2heap = Q.prove(
  `!refs n. n < LENGTH refs ==> (Mem n (EL n refs)) IN (store2heap refs)`,
  ASSUME_TAC(Q.ISPEC `\refs. !n. n < LENGTH refs ==>
                (Mem n (EL n refs)) IN (store2heap refs)` SNOC_INDUCT)
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

val REFS_PRED_FRAME_partial_frame_rule = Q.prove(
  `!s refs'.
     (!F. F (st2heap p s) ==>
     (F * GC) (st2heap p (s with refs := refs'))) ==>
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
  `EvalSt env st exp P ((\s. emp),p) ==> Eval env exp P`,
  rw[EvalSt_def, Eval_def]
  \\ fs[REFS_PRED_def, SEP_CLAUSES, SAT_GC]
  \\ first_x_assum(qspecl_then [`empty_state with refs := refs`]
        STRIP_ASSUME_TAC)
  \\ fs[state_component_equality]
  \\ fs[REFS_PRED_FRAME_def, SEP_CLAUSES]
  \\ rw[]
  \\ ASSUME_TAC (ISPEC ``empty_state with refs := refs``
       REFS_PRED_FRAME_partial_frame_rule)
  \\ fs(TypeBase.updates_of ``:'a state``)
  \\ first_x_assum drule \\ rw[]
  \\ evaluate_unique_result_tac
  \\ fs[state_component_equality]);

val handle_mult_def = Define `
  handle_mult [] exp1 ename = exp1 /\
  handle_mult (_:string list) exp1 ename =
    Handle exp1 [(Pvar "e",(Con (SOME (Short ename)) [Var (Short "e")]))]`;

val evaluate_handle_mult_Rval = Q.prove(
  `!cons_names exp1 ename res s s2 env.
     evaluate F env s exp1 (s2, Rval res) ==>
     evaluate F env s (handle_mult cons_names exp1 ename) (s2, Rval res)`,
  Cases
  \\ rw[handle_mult_def]
  \\ rw[Once evaluate_cases]);

val evaluate_handle_mult_Rabort = Q.prove(
  `!cons_names exp1 ename res s s2 env.
     evaluate F env s exp1 (s2, Rerr (Rabort res)) ==>
     evaluate F env s (handle_mult cons_names exp1 ename)
       (s2, Rerr (Rabort res))`,
  Cases
  \\ rw[handle_mult_def]
  \\ rw[Once evaluate_cases]);

val EVERY_CONJ_1 = GSYM EVERY_CONJ |> SPEC_ALL |> EQ_IMP_RULE
                     |> fst |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO];

val evaluate_11 = Q.store_thm("evaluate_11",
  `!b env s exp x.
     evaluate b env s exp x ==>
     !y. evaluate b env s exp y <=> x = y`,
  metis_tac [big_exp_determ]);

val prove_evaluate_handle_mult_CASE =
  rw[]
  \\ last_x_assum IMP_RES_TAC
  \\ rveq \\ fs []
  \\ Cases_on `cons_names`
  \\ fs [handle_mult_def,FUN_EQ_THM]
  \\ simp [Once bigStepTheory.evaluate_cases]
  \\ drule evaluate_11
  \\ fs []
  \\ disch_then kall_tac
  \\ simp [Once bigStepTheory.evaluate_cases]
  \\ fs [pmatch_def,pat_bindings_def,write_def]

val evaluate_handle_mult_CASE_MODULE = Q.prove(`
  ∀EXN_TYPE cons_names module_name ename exp1 s s2 e ev env.
     (∀e ev.
         EXN_TYPE e ev ⇒
         ∃evp cname.
            MEM cname cons_names ∧
            ev =
            Conv (SOME (cname,TypeExn (Long module_name (Short cname))))
              evp) ⇒
     evaluate F env (s:unit state) exp1 (s2,Rerr (Rraise ev)) ∧ EXN_TYPE e ev ⇒
     ∃cname evp.
        ev =
        Conv (SOME (cname,TypeExn (Long module_name (Short cname))))
          evp ∧
        evaluate F env s (handle_mult cons_names exp1 ename) =
        evaluate F (write "e" ev env) s2
          (Con (SOME (Short ename)) [Var (Short "e")])`,
  prove_evaluate_handle_mult_CASE);

val evaluate_handle_mult_CASE_SIMPLE = Q.prove(`
  ∀EXN_TYPE cons_names module_name ename exp1 s s2 e ev env.
     (∀e ev.
         EXN_TYPE e ev ⇒
         ∃evp cname.
            MEM cname cons_names ∧
            ev =
            Conv (SOME (cname,TypeExn (Short cname)))
              evp) ⇒
     evaluate F env (s:unit state) exp1 (s2,Rerr (Rraise ev)) ∧ EXN_TYPE e ev ⇒
     ∃cname evp.
        ev =
        Conv (SOME (cname,TypeExn (Short cname)))
          evp ∧
        evaluate F env s (handle_mult cons_names exp1 ename) =
        evaluate F (write "e" ev env) s2
          (Con (SOME (Short ename)) [Var (Short "e")])`,
  prove_evaluate_handle_mult_CASE);

val evaluate_Success_CONS = Q.prove(
  `lookup_cons "Success" env = SOME (1,TypeId (Short MNAME)) ==>
  evaluate F env s e (s', Rval v) ==>
  evaluate F env s (Con (SOME (Short "Success")) [e]) (s', Rval (Conv (SOME ("Success",TypeId (Short MNAME))) [v]))`,
  rw[]
  \\ rw[Once evaluate_cases]
  \\ fs[lookup_cons_def]
  \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
  \\ fs[namespaceTheory.id_to_n_def]
  \\ rw[Once evaluate_cases]
  \\ qexists_tac `s'`
  \\ rw[Once evaluate_cases]);

val evaluate_Success_CONS_err = Q.prove(
  `lookup_cons "Success" env = SOME (1,TypeId (Short MNAME)) ==>
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
     (EXC_TYPE_aux MNAME a b (Failure x_2) v =
      ?v2_1.
        v = Conv (SOME ("Failure",TypeId (Short MNAME))) [v2_1] ∧
        b x_2 v2_1) /\
     (EXC_TYPE_aux MNAME a b (Success x_1) v <=>
      ?v1_1.
        v = Conv (SOME ("Success",TypeId (Short MNAME))) [v1_1] ∧
        a x_1 v1_1)`;

val prove_EvalM_to_EvalSt =
  rw[EvalM_def, EvalSt_def]
  \\ first_x_assum drule \\ rw[]
  \\ Cases_on `res`
  (* res is an Rval *)
  >-(
      IMP_RES_TAC evaluate_Success_CONS
      \\ first_x_assum (fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
      \\ first_x_assum (qspecl_then [`cons_names`, `"Failure"`] ASSUME_TAC)
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
  \\ (drule evaluate_handle_mult_CASE_MODULE
      ORELSE drule evaluate_handle_mult_CASE_SIMPLE)
  \\ `evaluate F env s
        (Con (SOME (Short "Success")) [exp])
        (s2,Rerr (Rraise a))` by
   (simp [Once evaluate_cases]
    \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def,
          write_def,lookup_cons_def,PULL_EXISTS]
    \\ simp [Once evaluate_cases])
  \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then (qspec_then `"Failure"` strip_assume_tac)
  \\ rveq \\ fs []
  \\ simp [Once evaluate_cases]
  \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def,
        write_def,lookup_cons_def,PULL_EXISTS]
  \\ simp [Once evaluate_cases,PULL_EXISTS]
  \\ simp [Once evaluate_cases,PULL_EXISTS]
  \\ simp [Once evaluate_cases,PULL_EXISTS]
  \\ simp [Once evaluate_cases,PULL_EXISTS]
  \\ simp [run_def,EXC_TYPE_aux_def,namespaceTheory.id_to_n_def]
  \\ asm_exists_tac \\ simp [];

val EvalM_to_EvalSt_MODULE = Q.store_thm("EvalM_to_EvalSt_MODULE",`
  ∀cons_names module_name TYPE EXN_TYPE x exp H init_state MNAME env.
   (∀e ev.
       EXN_TYPE e ev ⇒
       ∃evp e' cname.
          MEM cname cons_names ∧
          ev =
          Conv (SOME (cname,TypeExn (Long module_name (Short cname))))
            evp) ⇒
   EvalM T env init_state exp (MONAD TYPE EXN_TYPE x) H ⇒
   lookup_cons "Success" env = SOME (1,TypeId (Short MNAME)) ⇒
   lookup_cons "Failure" env = SOME (1,TypeId (Short MNAME)) ⇒
   EvalSt env init_state
     (handle_mult cons_names (Con (SOME (Short "Success")) [exp])
        "Failure") (EXC_TYPE_aux MNAME TYPE EXN_TYPE (run x init_state)) H`,
  prove_EvalM_to_EvalSt);

val EvalM_to_EvalSt_SIMPLE = Q.store_thm("EvalM_to_EvalSt_SIMPLE",`
  ∀cons_names module_name TYPE EXN_TYPE x exp H init_state MNAME env.
   (∀e ev.
       EXN_TYPE e ev ⇒
       ∃evp e' cname.
          MEM cname cons_names ∧
          ev =
          Conv (SOME (cname,TypeExn ((Short cname))))
            evp) ⇒
   EvalM T env init_state exp (MONAD TYPE EXN_TYPE x) H ⇒
   lookup_cons "Success" env = SOME (1,TypeId (Short MNAME)) ⇒
   lookup_cons "Failure" env = SOME (1,TypeId (Short MNAME)) ⇒
   EvalSt env init_state
     (handle_mult cons_names (Con (SOME (Short "Success")) [exp])
        "Failure") (EXC_TYPE_aux MNAME TYPE EXN_TYPE (run x init_state)) H`,
  prove_EvalM_to_EvalSt);

val evaluate_let_opref = Q.store_thm("evaluate_let_opref",
  `Eval env exp1 P ==>
   ?junk v.
     evaluate F env s (Let (SOME vname) (App Opref [exp1]) exp2) =
     evaluate F (write vname (Loc (LENGTH (s.refs ++ junk))) env)
       (s with refs := s.refs ++ junk ++ [Refv v]) exp2 /\ P v`,
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
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ rw[namespaceTheory.nsOptBind_def]
  \\ fs[write_def, merge_env_def]
  \\ metis_tac[]);

val nsAppend_build_rec_env_eq_lemma = Q.prove(
  `!funs funs0 cl_env v0 v1.
    nsAppend (FOLDR (λ(f,x,e) env'. nsBind f
      (Recclosure cl_env funs0 f) env') v1 funs) v0 =
    FOLDR (λ(f,x,e) env'. nsBind f
      (Recclosure cl_env funs0 f) env') (nsAppend v1 v0) funs`,
  Induct_on `funs`
  >-(fs[merge_env_def, build_rec_env_def, namespaceTheory.nsAppend_def])
  \\ rw[]
  \\ Cases_on `h`
  \\ Cases_on `r`
  \\ fs[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def]);

val nsAppend_build_rec_env_eq = Q.prove(
  `!funs cl_env v0 v1.
     nsAppend (build_rec_env funs cl_env v1) v0 =
     build_rec_env funs cl_env (nsAppend v1 v0)`,
  fs[build_rec_env_def]
  \\ fs[nsAppend_build_rec_env_eq_lemma]);

val merge_build_rec_env = Q.prove(
  `!funs env1 env0.
     merge_env <|v := (build_rec_env funs (merge_env env1 env0) env1.v);
                 c := env1.c|> env0 =
     (merge_env env1 env0) with v :=
        build_rec_env funs (merge_env env1 env0) (merge_env env1 env0).v`,
  fs[merge_env_def, nsAppend_build_rec_env_eq]);

val EvalSt_Letrec_Fun = Q.store_thm("EvalSt_Letrec_Fun",
  `!funs env exp st P H.
  (ALL_DISTINCT (MAP (\(x,y,z). x) funs)) ==>
  EvalSt <|v := (build_rec_env funs env env.v); c := env.c|> st exp P H ==>
  EvalSt env st (Letrec funs exp) P H`,
  rw[EvalSt_def]
  \\ qpat_x_assum `!s. A` IMP_RES_TAC
  \\ rw[Once evaluate_cases]
  \\ `<|v := build_rec_env funs env env.v; c := env.c|> =
      env with v := build_rec_env funs env env.v` by fs[sem_env_component_equality]
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
    (!loc. EvalSt (write loc_name loc env) st exp P
      ((\st. REF_REL TYPE loc (get_ref st) * H st),p)) ==>
    EvalSt env st
      (Let (SOME loc_name) (App Opref [get_ref_exp]) exp) P (H,p)`,
  rw[EvalSt_def]
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ fs[Eval_def]
  \\ fs[PULL_EXISTS]
  \\ last_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ rw[state_component_equality,with_same_ffi]
  \\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ refs'))`, `s with refs := s.refs ++ refs' ++ [Refv res]`] ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      POP_ASSUM (fn x => ALL_TAC)
      \\ SIMP_TAC bool_ss [REFS_PRED_def]
      \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
      \\ SIMP_TAC bool_ss [Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ refs')) [Refv res]`
      \\ qexists_tac `st2heap p (s with refs := s.refs ++ refs')`
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
  \\ fs[merge_env_def, write_def]
  \\ evaluate_unique_result_tac
  \\ fs[REFS_PRED_FRAME_def]
  \\ qexists_tac `st2` \\ rw[]
  >-(fs[state_component_equality])
  \\ rw[state_component_equality]
  \\ rw[]
  \\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      rw[GSYM STAR_ASSOC]
      \\ rw[Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ refs')) [Refv res]`
      \\ qexists_tac `st2heap p (s with refs := s.refs ++ refs')`
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
      \\ qexists_tac `store2heap_aux (LENGTH s.refs) (refs')`
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

val EvalSt_AllocEmpty = Q.store_thm("EvalSt_AllocEmpty",
  `!exp get_ref loc_name TYPE st_name env H P st.
     EQ (get_ref st) [] ==>
     (!loc.
       EvalSt (write loc_name loc env) st exp P
         ((\st. RARRAY_REL TYPE loc (get_ref st) * H st),p)) ==>
     EvalSt env st
       (Let (SOME loc_name) (App Opref [App AallocEmpty [Con NONE []]]) exp)
         P (H,p)`,
  rw[EvalSt_def]
  \\ ntac 9 (rw[Once evaluate_cases])
  \\ fs[PULL_EXISTS]
  \\ fs[do_con_check_def, build_conv_def]
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ simp[with_same_ffi]
  \\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ [Varray []]))`, `s with refs := s.refs ++ [Varray []; Refv (Loc (LENGTH s.refs))]`] ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      POP_ASSUM (fn x => ALL_TAC)
      \\ SIMP_TAC bool_ss [REFS_PRED_def]
      \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
      \\ SIMP_TAC bool_ss [Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH s.refs) [Varray []; Refv (Loc (LENGTH s.refs))]`
      \\ qexists_tac `st2heap p (s with refs := s.refs)`
      \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
      \\ SIMP_TAC bool_ss [STATE_SPLIT_REFS]
      \\ ASM_SIMP_TAC bool_ss [GSYM REFS_PRED_def, with_same_refs]
      \\ fs[RARRAY_REL_def, SEP_EXISTS]
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[RARRAY_HPROP_SAT_EQ,EQ_def,store2heap_aux_def]
      \\ metis_tac[])
  \\ first_x_assum drule \\ rw[]
(*  \\ first_x_assum (qspec_then `[]` strip_assume_tac) *)
  \\ fs[merge_env_def, write_def]
  \\ evaluate_unique_result_tac
  \\ fs[REFS_PRED_FRAME_def]
  \\ qexists_tac `st2` \\ rw[]
  >-(rw[state_component_equality])
  \\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      rw[GSYM STAR_ASSOC]
      \\ rw[Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH s.refs) [Varray []; Refv (Loc (LENGTH s.refs))]`
      \\ qexists_tac `st2heap p (s with refs := s.refs)`
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
      \\ irule H_STAR_GC_SAT_IMP
      \\ fs[with_same_refs])
  \\ first_x_assum drule \\ rw[]
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ first_x_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
  \\ fs[]);

val EvalSt_Alloc = Q.store_thm("EvalSt_Alloc",
  `!exp nexp n xexp x get_farray loc_name TYPE env H P st.
     EQ (get_farray st) (REPLICATE n x) ==>
     Eval env nexp (\v. v = Litv (IntLit (&n))) ==>
     Eval env xexp (TYPE x) ==>
     (!loc.
        EvalSt (write loc_name loc env) st exp P
          ((\st. ARRAY_REL TYPE loc (get_farray st) * H st),p)) ==>
     EvalSt env st (Let (SOME loc_name) (App Aalloc [nexp; xexp]) exp) P (H,p)`,
  rw[EvalSt_def]
  \\ ntac 3 (rw[Once evaluate_cases])
  \\ fs[PULL_EXISTS]
  \\ fs[Eval_def]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ first_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
  \\ fs[] \\ evaluate_unique_result_tac
  \\ rw[Once evaluate_cases]
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ fs[with_same_ffi]
  \\ first_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ refs' ++ refs''))`, `s with refs := s.refs ++ refs' ++ refs'' ++ [Varray (REPLICATE n res)]`] STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      POP_ASSUM (fn x => ALL_TAC)
      \\ SIMP_TAC bool_ss [REFS_PRED_def]
      \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
      \\ SIMP_TAC bool_ss [Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ refs' ++ refs'')) [Varray (REPLICATE n res)]`
      \\ qexists_tac `st2heap p (s with refs := s.refs ++ refs' ++ refs'')`
      \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
      \\ SIMP_TAC bool_ss [STATE_SPLIT_REFS]
      \\ fs[REFS_PRED_def] \\ fs[Once (GSYM with_same_refs)]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_APPEND_JUNK) x |> STRIP_ASSUME_TAC)
      \\ first_x_assum(qspec_then `refs' ++ refs''` STRIP_ASSUME_TAC)
      \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
      \\ fs[store2heap_aux_def, ARRAY_REL_def, SEP_EXISTS]
      \\ qexists_tac `REPLICATE n res`
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[EQ_def, LIST_REL_REPLICATE_same]
      \\ rw[ARRAY_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def, store2heap_aux_def])
  \\ fs[write_def]
  \\ evaluate_unique_result_tac
  \\ fs[REFS_PRED_FRAME_def]
  \\ qexists_tac `st2` \\ rw []
  >-(rw[state_component_equality])
  \\ first_x_assum(qspec_then `F' * GC` STRIP_ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      POP_ASSUM (fn x => ALL_TAC)
      \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
      \\ SIMP_TAC bool_ss [Once STAR_def]
      \\ qexists_tac `store2heap_aux (LENGTH (s.refs ++ refs' ++ refs'')) [Varray (REPLICATE n res)]`
      \\ qexists_tac `st2heap p (s with refs := s.refs ++ refs' ++ refs'')`
      \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
      \\ SIMP_TAC bool_ss [STATE_SPLIT_REFS]
      \\ fs[REFS_PRED_def] \\ fs[Once (GSYM with_same_refs)]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_APPEND_JUNK) x |> STRIP_ASSUME_TAC)
      \\ first_x_assum(qspec_then `refs' ++ refs''` STRIP_ASSUME_TAC)
      \\ fs[STAR_ASSOC]
      \\ rw[ARRAY_REL_def, ARRAY_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def, store2heap_aux_def]
      \\ fs[EQ_def, LIST_REL_REPLICATE_same])
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ POP_ASSUM(fn x => ALL_TAC)
  \\ first_x_assum(fn x => REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
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
  LIST_CONJ[nsBind_to_write,Eval_Var_SIMP,Eval_lookup_var,
    nsLookup_write_simp,sem_env_same_components,lookup_cons_write_simp,
    lookup_cons_build_rec_env_simp]);

val EVAL_T_F = save_thm("EVAL_T_F",
  LIST_CONJ [EVAL ``ml_translator$CONTAINER ml_translator$TRUE``,
             EVAL ``ml_translator$CONTAINER ml_translator$FALSE``]);

val EVAL_PRECONDITION_T = save_thm("EVAL_PRECONDITION_T",
  EVAL (``ml_translator$PRECONDITION T``));

val H_STAR_emp = store_thm("H_STAR_emp",
  ``H * emp = H``, simp[SEP_CLAUSES]);

val H_STAR_TRUE = store_thm("H_STAR_TRUE",
  ``(H * &T = H) /\ (&T * H = H)``, fs[SEP_CLAUSES]);

val PreImp_PRECONDITION_T_SIMP = Q.store_thm("PreImp_PRECONDITION_T_SIMP",
  `PreImp T a /\ PRECONDITION T <=> a`,
  fs[PreImp_def, PRECONDITION_def]);

val IF_T = Q.store_thm("IF_T",`(if T then x else y) = x:'a`,SIMP_TAC std_ss []);

val IF_F = Q.store_thm("IF_F",`(if F then x else y) = y:'a`,SIMP_TAC std_ss []);

val IMP_EQ_T = Q.store_thm("IMP_EQ_T",`a ==> (a <=> T)`,fs []);

val BETA_PAIR_THM = Q.store_thm("BETA_PAIR_THM",`(\(x, y). f x y) (x, y) = (\x y. f x y) x y`, fs[]);

(* Terms used by the ml_monad_translatorLib *)
val parsed_terms = save_thm("parsed_terms",
  pack_list (pack_pair pack_string pack_term)
    [("EqSt remove",``!a st. EqSt a st = (a : ('a, 'b) H)``),
     ("PURE ArrowP ro eq", ``PURE(ArrowP ro H (PURE (Eq a x)) b)``),
     ("ArrowP ro PURE", ``ArrowP ro H a (PURE b)``),
     ("ArrowP ro EqSt", ``ArrowP ro H (EqSt a st) b``),
     ("ArrowM_const",``ArrowM``),
     ("Eval_const",``Eval``),
     ("EvalM_const",``EvalM``),
     ("MONAD_const",``MONAD : (α->v->bool) -> (β->v->bool) -> ((γ,α,β)M,γ) H``),
     ("PURE_const",``PURE : (α -> v -> bool) -> (α, β) H``),
     ("FST_const",``FST : 'a # 'b -> 'a``),
     ("SND_const",``SND : 'a # 'b -> 'b``),
     ("LENGTH_const", ``LENGTH : 'a list -> num``),
     ("EL_const", ``EL : num -> 'a list -> 'a``),
     ("Fun_const",``ast$Fun``),
     ("Short_const",``namespace$Short``),
     ("Var_const",``ast$Var``),
     ("Closure_const",``semanticPrimitives$Closure``),
     ("failure_pat",``\v. (Failure(C v), state_var)``),
     ("Eval_pat",``Eval env exp (P (res:'a))``),
     ("Eval_pat2",``Eval env exp P``),
     ("derive_case_EvalM_abs",``\EXN_TYPE res (H:('a -> hprop) # 'ffi ffi_proj). EvalM ro env st exp (MONAD P EXN_TYPE res) H``),
     ("Eval_name_RI_abs",``\name RI. Eval env (Var (Short name)) RI``),
     ("write_const",``write``),
     ("RARRAY_REL_const",``RARRAY_REL``),
     ("ARRAY_REL_const",``ARRAY_REL``),
     ("run_const",``ml_monadBase$run``),
     ("EXC_TYPE_aux_const",``EXC_TYPE_aux``),
     ("return_pat",``st_ex_return x``),
     ("bind_pat",``st_ex_bind x y``),
     ("otherwise_pat",``x otherwise y``),
     ("if_statement_pat",``if b then (x:('a,'b,'c) M) else (y:('a,'b,'c) M)``),
     ("PreImp_EvalM_abs",``\a name RI f (H: ('a -> hprop) # 'ffi ffi_proj). PreImp a (!st. EvalM ro env st (Var (Short name)) (RI f) H)``),
     ("refs_emp",``\refs. emp``),
     ("UNIT_TYPE",``UNIT_TYPE``),
     ("namespaceLong_tm",``namespace$Long``),
     ("eval Mat",``evaluate c x env (Mat e pats) (xx,res)``),
     ("eval_match Pcon",``evaluate_match c x env args ((Pcon xx pats,exp2)::pats2) errv (yyy,y)``),
     ("nsLookup_val_pat",``nsLookup (env : env_val) (Short (vname : tvarN)) = SOME (loc : v)``),
     ("CONTAINER",``ml_translator$CONTAINER (b:bool)``),
     ("EvalM_pat",``EvalM ro env st e p H``),
     ("var_assum",``Eval env (Var n) (a (y:'a))``),
     ("nsLookup_assum",``nsLookup env name = opt``),
     ("lookup_cons_assum",``lookup_cons name env = opt``),
     ("eqtype_assum",``EqualityType A``),
     ("nsLookup_closure_pat",``nsLookup env1.v (Short name1) =
                             SOME (Closure env2 name2 exp)``),
     ("nsLookup_recclosure_pat",``nsLookup env1.v (Short name1) =
                                SOME (Recclosure env2 exps name2)``),
     ("Eq_pat",``Eq a x``),
     ("EqSt_pat",``EqSt a x``),
     ("PreImp simp",``(PreImp a b /\ PRECONDITION a) <=> b``),
     ("PRECONDITION_pat",``ml_translator$PRECONDITION x``),
     ("LOOKUP_VAR_pat",``LOOKUP_VAR name env exp``),
     ("Long_tm",``namespace$Long : tvarN -> (tvarN, tvarN) id -> (tvarN, tvarN) id ``),
     ("nsLookup_pat",``nsLookup (env : v sem_env).v (Short name) = SOME exp``),
     ("emp_tm",``set_sep$emp``),
     ("ffi_ffi_proj", ``p:'ffi ffi_proj``)
    ]);

(* Types used by the ml_monad_translatorLib *)
val parsed_types = save_thm("parsed_types",
  pack_list (pack_pair pack_string pack_type)
    [("exp",``:ast$exp``),
     ("string_ty",``:tvarN``),
     ("unit",``:unit``),
     ("pair", ``:'a # 'b``),
     ("num", ``:num``),
     ("poly_M_type",``:'a -> ('b, 'c) exc # 'a``),
     ("v_bool_ty",``:v -> bool``),
     ("hprop_ty",``:hprop``),
     ("recclosure_exp_ty",``:(tvarN, tvarN # ast$exp) alist``),
     ("register_pure_type_pat",``:('a, 'b) ml_monadBase$exc``),
     ("exc_ty",``:('a, 'b) exc``),
     ("ffi",``:'ffi``),
     ("v_list", ``:v list``)
    ]);

val _ = (print_asts := true);

val _ = export_theory();
