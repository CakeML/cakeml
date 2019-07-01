(*
  Defines EvalM and other judgements that are central to the monadic
  translator.
*)
open ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory semanticPrimitivesTheory evaluateTheory evaluatePropsTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory Satisfy
open cfHeapsBaseTheory AC_Sort
open ml_monadBaseTheory ml_monad_translatorBaseTheory
open cfStoreTheory cfTheory cfTacticsLib packLib;
open preamble;

val _ = new_theory "ml_monad_translator";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``st_ex_ignore_bind``);
val _ = temp_overload_on ("monad_ignore_bind", ``st_ex_ignore_bind``);
val _ = temp_overload_on ("ex_bind", ``st_ex_bind``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);

val _ = temp_overload_on ("CONTAINER", ``ml_translator$CONTAINER``);

val _ = hide "state";

(* TODO: move *)
Theorem s_with_same_clock[simp]:
   !s. (s with clock := s.clock) = s
Proof
  fs [state_component_equality]
QED
(* -- *)

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
  \\ pop_assum(fn x => fs[x])
  \\ imp_res_tac GC_ABSORB_L);

val HCOND_EXTRACT = cfLetAutoTheory.HCOND_EXTRACT;

val REF_EXISTS_LOC = Q.prove(`(rv ~~> v * H) s ==> ?l. rv = Loc l`,
  rw[REF_def, SEP_CLAUSES, SEP_EXISTS_THM, GSYM STAR_ASSOC, HCOND_EXTRACT]);

val ARRAY_EXISTS_LOC  = Q.prove(`(ARRAY rv v * H) s ==> ?l. rv = Loc l`,
  rw[STAR_def, SEP_EXISTS_THM, SEP_CLAUSES, REF_def, ARRAY_def, cond_def]);

val UNIQUE_CELLS = Q.prove(
  `!p s. !l xv xv' H H'. (l ~~>> xv * H) (st2heap p s) /\ (l ~~>> xv' * H') (st2heap p s) ==> xv' = xv`,
  rw[] >>
  imp_res_tac st2heap_CELL_MEM >>
  imp_res_tac store2heap_IN_unique_key);

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
  pop_assum(fn x => ASSUME_TAC(PURE_ONCE_REWRITE_RULE[th] x))

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(***)

(*
 * Definition of EvalM
 * `ro`: references only
 *)

val EvalM_def = Define `
  EvalM ro env st exp P H <=>
    !(s:'ffi state).
      REFS_PRED H st s ==>
      ?s2 res st2 ck.
        evaluate (s with clock := ck) env [exp] = (s2,res) /\
        P st (st2, res) /\ REFS_PRED_FRAME ro H (st, s) (st2, s2)`;

(* refinement invariant for ``:('a, 'b, 'c) M`` *)
val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val MONAD_def = Define `
  MONAD (a:'a->v->bool) (b: 'b->v->bool) (x:('refs, 'a, 'b) M)
                                    (state1:'refs)
                                    (state2:'refs,res: (v list,v) result) =
    case (x state1, res) of
      ((Success y, st), Rval [v]) => (st = state2) /\ a y v
    | ((Failure e, st), Rerr (Rraise v)) => (st = state2) /\
                                              b e v
    | _ => F`

val H = mk_var("H",``:('a -> hprop) # 'ffi ffi_proj``);

(* return *)
Theorem EvalM_return:
   !H b. Eval env exp (a x) ==>
         EvalM ro env st exp (MONAD a b (ex_return x)) ^H
Proof
  rw[Eval_def,EvalM_def,st_ex_return_def,MONAD_def]
  \\ first_x_assum(qspec_then`s.refs`strip_assume_tac)
  \\ imp_res_tac (evaluate_empty_state_IMP)
  \\ fs [eval_rel_def,PULL_EXISTS]
  \\ drule evaluate_set_clock \\ simp []
  \\ disch_then (qspec_then `s.clock` mp_tac)
  \\ strip_tac \\ fs []
  \\ asm_exists_tac \\ simp []
  \\ `(s with <|clock := s.clock; refs := s.refs ⧺ refs'|>) =
      (s with <|refs := s.refs ⧺ refs'|>)` by fs [state_component_equality]
  \\ fs [REFS_PRED_FRAME_append]
QED

(* bind *)
Theorem EvalM_bind:
   (a1 ==> EvalM ro env st e1 (MONAD b c (x:('refs, 'b, 'c) M))
             (H:('refs -> hprop) # 'ffi ffi_proj)) /\
   (!z v. b z v ==> a2 z ==>
      EvalM ro (write name v env) (SND (x st)) e2
        (MONAD a c ((f z):('refs, 'a, 'c) M)) H) ==>
   (a1 /\ !z. (CONTAINER(FST(x st) = Success z) ==> a2 z)) ==>
   EvalM ro env st (Let (SOME name) e1 e2) (MONAD a c (ex_bind x f)) H
Proof
  rw[EvalM_def,MONAD_def,st_ex_return_def,PULL_EXISTS, CONTAINER_def] \\ fs[]
  \\ last_x_assum drule \\ rw[]
  \\ imp_res_tac REFS_PRED_FRAME_imp
  \\ Cases_on `x st` \\ fs []
  \\ rename1 `x st = (succ,new_state)`
  \\ simp [evaluate_def,pair_case_eq,PULL_EXISTS]
  \\ reverse (Cases_on `succ`) \\ fs []
  THEN1
   (Cases_on `res` \\ fs[] \\ rw [] \\ Cases_on `e`
    \\ fs [st_ex_bind_def] \\ rveq \\ asm_exists_tac \\ fs [])
  \\ fs[st_ex_bind_def]
  \\ Cases_on `res` \\ fs []
  \\ drule evaluate_sing \\ strip_tac \\ rveq \\ fs []
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ Cases_on `f a' new_state` \\ fs []
  \\ drule evaluate_set_clock
  \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
  \\ disch_then (qspec_then `s2'.clock` mp_tac)
  \\ impl_tac THEN1 (CCONTR_TAC \\ fs [] \\ EVERY_CASE_TAC \\ fs [])
  \\ strip_tac \\ fs [] \\ pop_assum mp_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck1` mp_tac)
  \\ rpt strip_tac \\ fs []
  \\ asm_exists_tac \\ fs [write_def,namespaceTheory.nsOptBind_def]
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `res'` \\ fs []
  \\ TRY (Cases_on `e`) \\ fs []
  \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac REFS_PRED_FRAME_trans
QED

(* lift ro refinement invariants *)

val _ = type_abbrev("H",``:'a -> 'refs ->
                                 'refs # (v list,v) result -> bool``);

val PURE_def = Define `
  PURE a (x:'a) (st1:'refs) (st2,res:(v list,v) result) =
    ?v:v. (res = Rval [v]) /\ (st1 = st2) /\ a x v`;

val EqSt_def = Define `
  EqSt abs st = \x st1 (st2, res). st = st1 /\ abs x st1 (st2, res)`;

Theorem state_update_clock_id[simp]:
   (s with <|clock := s.clock; refs := refs'|>) =
    s with <| refs := refs'|>
Proof
  fs [state_component_equality]
QED

Theorem Eval_IMP_PURE:
   !H env exp P x. Eval env exp (P x) ==> EvalM ro env st exp (PURE P x) ^H
Proof
  rw[Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ first_x_assum(qspec_then`s.refs`strip_assume_tac)
  \\ imp_res_tac evaluate_empty_state_IMP
  \\ fs[eval_rel_def]
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `s.clock` mp_tac)
  \\ strip_tac \\ fs [] \\ asm_exists_tac
  \\ fs [REFS_PRED_FRAME_append]
QED

Theorem Eval_IMP_PURE_EvalM_T:
   !H env exp P x. Eval env exp (P x) ==> EvalM T env st exp (PURE P x) ^H
Proof
  rw[Eval_IMP_PURE]
QED

(* function abstraction and application *)

val ArrowP_def = Define `
  ArrowP ro H (a:('a, 'refs) H) b f c =
     !x st1 s1 st2 (res:(v list,v) result).
       a x st1 (st2,res) /\ REFS_PRED H st1 s1 ==>
       ?v env exp.
         (st2 = st1) /\
         (res = Rval [v]) /\ do_opapp [c;v] = SOME (env,exp) /\
         !junk. ?st3 s3 res3 ck.
           evaluate (s1 with <| refs := s1.refs ++ junk ; clock := ck |>)
             env [exp] = (s3,res3) /\
           b (f x) st1 (st3,res3) /\
           REFS_PRED_FRAME ro H (st1, s1) (st3, s3)`;

val ArrowM_def = Define `
  ArrowM ro H (a:('a, 'refs) H) (b:('b, 'refs) H) =
     PURE (ArrowP ro H a b) : ('a -> 'b, 'refs) H`;

val EvalM_Arrow_tac =
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS,evaluate_def,
     pair_case_eq,result_case_eq,PULL_EXISTS,EqSt_def,Eq_def]
  \\ first_x_assum drule \\ strip_tac
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule
  \\ `REFS_PRED H st s2'` by metis_tac [REFS_PRED_FRAME_imp]
  \\ disch_then drule \\ strip_tac
  \\ imp_res_tac REFS_PRED_FRAME_trans
  \\ qpat_x_assum `!x. _` mp_tac
  \\ qpat_x_assum `!x. _` (qspec_then `[]` strip_assume_tac)
  \\ disch_then kall_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ imp_res_tac REFS_PRED_FRAME_trans
  \\ asm_exists_tac \\ fs []
  \\ qpat_x_assum `evaluate _ _ [x1] = _` assume_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck''+1` mp_tac) \\ strip_tac
  \\ qpat_x_assum `evaluate _ _ [x2] = _` assume_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck1` mp_tac) \\ strip_tac
  \\ asm_exists_tac
  \\ `(s2' with <|clock := ck''; refs := s2'.refs|>) =
      s2' with <|clock := ck''|>` by fs [state_component_equality]
  \\ fs [dec_clock_def];

Theorem EvalM_ArrowM:
    EvalM ro env st x1 ((ArrowM ro H (PURE a) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H
Proof
  EvalM_Arrow_tac
QED

Theorem EvalM_ArrowM_EqSt:
    EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE a) st) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H
Proof
  EvalM_Arrow_tac
QED

Theorem EvalM_ArrowM_Eq:
    EvalM ro env st x1 ((ArrowM ro H (PURE (Eq a x)) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H
Proof
  EvalM_Arrow_tac
QED

Theorem EvalM_ArrowM_EqSt_Eq:
   EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE (Eq a x)) st) b) f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (App Opapp [x1;x2]) (b (f x)) ^H
Proof
  EvalM_Arrow_tac
QED

Theorem EvalM_Fun:
   (!v x. a x v ==> EvalM ro (write name v env) n_st body (b (f x)) H) ==>
    EvalM ro env st (Fun name body) (ArrowM ro H (EqSt (PURE a) n_st) b f) ^H
Proof
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def,evaluate_def,
     EqSt_def,PULL_EXISTS] \\ fs [PULL_FORALL]
  \\ qexists_tac `s.clock`
  \\ fs [REFS_PRED_FRAME_same] \\ rw []
  \\ fs [do_opapp_def,GSYM PULL_FORALL] \\ simp [PULL_EXISTS]
  \\ strip_tac
  \\ first_x_assum drule
  \\ `REFS_PRED H n_st (s1 with refs := s1.refs ++ junk)` by
        (drule REFS_PRED_append \\ rw[])
  \\ disch_then drule
  \\ strip_tac \\ fs [write_def]
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ drule REFS_PRED_FRAME_remove_junk \\ fs[]
QED

Theorem EvalM_Fun_Var_intro:
   EvalM ro cl_env st (Fun n exp) (PURE P f) H ==>
   ∀name. LOOKUP_VAR name env (Closure cl_env n exp) ==>
          EvalM ro env st (Var (Short name)) (PURE P f) ^H
Proof
  fs[EvalM_def, PURE_def, LOOKUP_VAR_def, evaluate_def,
     PULL_EXISTS, lookup_var_def]
QED

Theorem EvalM_Fun_Eq:
   (!v. a x v ==> EvalM ro (write name v env) n_st body (b (f x)) H) ==>
   EvalM ro env st (Fun name body)
     ((ArrowM ro H (EqSt (PURE (Eq a x)) n_st) b) f) ^H
Proof
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def, evaluate_def,EqSt_def]
  \\ qexists_tac `s.clock` \\ fs []
  \\ `(s with clock := s.clock) = s` by simp [state_component_equality]
  \\ fs [REFS_PRED_FRAME_same,PULL_EXISTS] \\ rw []
  \\ fs [do_opapp_def,GSYM PULL_FORALL] \\ simp [PULL_EXISTS] \\ rw []
  \\ first_x_assum drule
  \\ `REFS_PRED H n_st (s1 with refs := s1.refs ++ junk)` by
        (drule REFS_PRED_append \\ rw[])
  \\ disch_then drule
  \\ strip_tac \\ fs [write_def]
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ drule REFS_PRED_FRAME_remove_junk \\ fs[]
QED


(* More proofs *)

Theorem LOOKUP_VAR_EvalM_ArrowM_IMP:
   (!st env. LOOKUP_VAR n env v ==>
             EvalM ro env st (Var (Short n)) (ArrowM ro H a b f) H) ==>
    ArrowP ro ^H a b f v
Proof
  fs [LOOKUP_VAR_def,lookup_var_def,EvalM_def,ArrowP_def,
      ArrowM_def,PURE_def,AND_IMP_INTRO,
      evaluate_def, PULL_EXISTS, VALID_REFS_PRED_def]
  \\ `nsLookup (<|v := nsBind n v nsEmpty|>).v (Short n) = SOME v` by EVAL_TAC
  \\ rw[] \\ first_x_assum drule \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[]
QED

Theorem EvalM_Var_SIMP:
   EvalM ro (write n x env) st (Var (Short y)) P ^H =
    if n = y then EvalM ro (write n x env) st (Var (Short y)) P H
             else EvalM ro env st (Var (Short y)) P H
Proof
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [evaluate_def,write_def]
QED

Theorem EvalM_Var_SIMP_ArrowM:
   (!st. EvalM ro (write nv v env) st (Var (Short n)) (ArrowM ro H a b x) H) =
    if nv = n then ArrowP ro H a b x v
    else (!st. EvalM ro env st (Var (Short n)) (ArrowM ro H a b x) ^H)
Proof
  SIMP_TAC std_ss [EvalM_def, ArrowM_def, VALID_REFS_PRED_def]
  \\ reverse (SRW_TAC [] [])
  THEN1 fs [evaluate_def,write_def]
  \\ simp [PURE_def, evaluate_def,write_def]
  \\ rw[ArrowP_def]
  \\ EQ_TAC THEN1 metis_tac []
  \\ rw []
  \\ qexists_tac `s.clock`
  \\ fs [REFS_PRED_FRAME_same]
QED

Theorem EvalM_Recclosure_ALT:
   !H funs fname name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (Eq a n)) b) f) ^H
Proof
  rw[write_rec_thm,write_def]
  \\ imp_res_tac LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def] \\ rpt strip_tac
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ fs [evaluate_def,eval_rel_def,option_case_eq,PULL_EXISTS,Eq_def]
  \\ fs[state_component_equality] \\ rveq \\ fs [PULL_FORALL]
  \\ qexists_tac `s.clock` \\ rpt gen_tac \\ strip_tac
  \\ fs [REFS_PRED_FRAME_same]
  \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ fs [do_opapp_def,GSYM PULL_FORALL]
  \\ strip_tac
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]
QED

Theorem EvalM_Recclosure_ALT2:
   !H funs fname.
     A n_st ==>
     !name body.
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     (∀st v.
        A st ==>
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (Eq a n)) n_st) b) f) ^H
Proof
  rw[write_rec_thm,write_def]
  \\ imp_res_tac LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def] \\ rpt strip_tac
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ fs [evaluate_def,eval_rel_def,option_case_eq,PULL_EXISTS,Eq_def,
         EqSt_def,PURE_def]
  \\ fs[state_component_equality] \\ rveq \\ fs [PULL_FORALL]
  \\ qexists_tac `s.clock` \\ rpt gen_tac \\ strip_tac
  \\ fs [REFS_PRED_FRAME_same]
  \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ fs [do_opapp_def,GSYM PULL_FORALL]
  \\ strip_tac
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]
QED

Theorem EvalM_Recclosure_ALT3:
   !H funs fname name body.
     (∀st v.
        A st ==>
        a n v ==>
        EvalM ro (write name v (write_rec funs env2 env2)) st body (b (f n)) H) ==>
     A n_st ==>
     ALL_DISTINCT (MAP (λ(f,x,e). f) funs) ==>
     LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (Eq a n)) n_st) b) f) ^H
Proof
  rw[write_rec_thm,write_def]
  \\ imp_res_tac LOOKUP_VAR_THM
  \\ fs[Eval_def, EvalM_def,ArrowM_def, ArrowP_def, PURE_def] \\ rpt strip_tac
  \\ first_x_assum(qspec_then`s.refs` STRIP_ASSUME_TAC)
  \\ fs [evaluate_def,eval_rel_def,option_case_eq,PULL_EXISTS,Eq_def,
         EqSt_def,PURE_def]
  \\ fs[state_component_equality] \\ rveq \\ fs [PULL_FORALL]
  \\ qexists_tac `s.clock` \\ rpt gen_tac \\ strip_tac
  \\ fs [REFS_PRED_FRAME_same]
  \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ fs [do_opapp_def,GSYM PULL_FORALL]
  \\ strip_tac
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]
QED

Theorem EvalM_Recclosure:
   !H. (!st v. a n v ==>
         EvalM ro (write name v (write_rec [(fname,name,body)] env2 env2))
               st body (b (f n)) H) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    EvalM ro env st (Var (Short fname)) ((ArrowM ro H (PURE (Eq a n)) b) f) ^H
Proof
  gen_tac \\ NTAC 2 strip_tac \\ imp_res_tac LOOKUP_VAR_THM
  \\ pop_assum mp_tac \\ pop_assum (K ALL_TAC) \\ pop_assum mp_tac
  \\ rw[Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,
        ArrowP_def,Eq_def,PULL_EXISTS]
  \\ first_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ fs [evaluate_def,option_case_eq,eval_rel_def,state_component_equality]
  \\ rveq \\ fs []
  \\ qexists_tac `s` \\ fs []
  \\ fs [REFS_PRED_FRAME_same]
  \\ rw [do_opapp_def,find_recfun_def]
  \\ drule REFS_PRED_append \\ rw[]
  \\ last_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[] \\ fs [write_def,write_rec_def,build_rec_env_def]
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_remove_junk]
QED

Theorem EvalM_Eq_Recclosure:
   LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
    (ArrowP ro H a b f (Recclosure x1 x2 x3) =
     (!st. EvalM ro env st (Var (Short name)) (ArrowM ro H a b f) ^H))
Proof
  rw[EvalM_Var_SIMP, EvalM_def, ArrowM_def, LOOKUP_VAR_def, lookup_var_def,
     PURE_def, PULL_EXISTS, evaluate_def]
  \\ eq_tac
  THEN1 (rw[] \\ qexists_tac `s.clock` \\ fs [REFS_PRED_FRAME_same])
  \\ rw []
  \\ simp[ArrowP_def,PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ fs [ArrowP_def]
QED

Theorem EvalM_Var_ArrowP:
   (!st. EvalM ro env st (Var (Short n)) (ArrowM ro H (PURE a) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro ^H (PURE a) b x v
Proof
  rw[EvalM_def,evaluate_def]
  \\ fs[ArrowP_def, ArrowM_def,PURE_def,PULL_EXISTS,evaluate_def,option_case_eq]
  \\ rw [] \\ fs [LOOKUP_VAR_def,lookup_var_def]
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED

Theorem EvalM_Var_ArrowP_EqSt:
   (!st. EvalM ro env st (Var (Short n)) (ArrowM ro H (EqSt (PURE a) n_st) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro ^H (EqSt (PURE a) n_st) b x v
Proof
  rw[EvalM_def,evaluate_def]
  \\ fs[ArrowP_def, ArrowM_def,PURE_def,PULL_EXISTS,evaluate_def,
        option_case_eq,EqSt_def]
  \\ rw [] \\ fs [LOOKUP_VAR_def,lookup_var_def]
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac \\ fs []
QED

(* Eq simps *)

Theorem EvalM_FUN_FORALL:
   (!x. EvalM ro env st exp (PURE (P x) f) H) ==>
    EvalM ro env st exp (PURE (FUN_FORALL x. P x) f) ^H
Proof
  rw[EvalM_def,PURE_def,PULL_EXISTS]
  \\ first_x_assum drule
  \\ simp[PULL_EXISTS,FUN_FORALL]
  \\ strip_tac
  \\ first_assum(qspecl_then[`ARB`]strip_assume_tac)
  \\ asm_exists_tac \\ simp[]
  \\ qx_gen_tac`x`
  \\ first_assum(qspecl_then[`x`]strip_assume_tac)
  \\ drule evaluate_add_to_clock \\ fs []
  \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
  \\ drule evaluate_add_to_clock \\ fs []
  \\ disch_then (qspec_then `ck'` strip_assume_tac)
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ fs []
QED

Theorem EvalM_FUN_FORALL_EQ:
   (!x. EvalM ro env st exp (PURE (P x) f) H) =
    EvalM ro env st exp (PURE (FUN_FORALL x. P x) f) ^H
Proof
  REPEAT strip_tac \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ fs [EvalM_def,PURE_def,PULL_EXISTS,FUN_FORALL] \\ METIS_TAC []
QED

val M_FUN_FORALL_PUSH1 = Q.prove(
  `(FUN_FORALL x. ArrowP ro ^H a (PURE (b x))) =
   (ArrowP ro H a (PURE (FUN_FORALL x. b x)))`,
  rw[FUN_EQ_THM,FUN_FORALL,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ reverse EQ_TAC >- METIS_TAC[] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum(qspec_then`ARB`strip_assume_tac) \\ fs[]
  \\ first_assum drule \\ disch_then strip_assume_tac \\ rw[]
  \\ drule REFS_PRED_append \\ rw[]
  \\ first_x_assum drule \\ disch_then strip_assume_tac
  \\ fs[]
  \\ first_x_assum(qspecl_then[`[]`]strip_assume_tac)
  \\ fs[] \\ rw[]
  \\ asm_exists_tac \\ fs []
  \\ reverse(rw[])
  THEN1 (metis_tac[REFS_PRED_FRAME_remove_junk])
  \\ first_x_assum(qspecl_then[`y`]strip_assume_tac)
  \\ first_x_assum drule \\ disch_then strip_assume_tac
  \\ first_x_assum(qspecl_then[`[]`]strip_assume_tac)
  \\ fs[] \\ rw[]
  \\ drule evaluate_add_to_clock \\ fs []
  \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
  \\ drule evaluate_add_to_clock \\ fs []
  \\ disch_then (qspec_then `ck'` strip_assume_tac)
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ fs []);

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

Theorem EvalM_Eq:
   EvalM ro env st exp (PURE a x) H ==> EvalM ro env st exp (PURE (Eq a x) x) ^H
Proof
  fs[EvalM_def, PURE_def, Eq_def]
QED

Theorem ArrowM_EqSt_elim:
   (!st_v. EvalM ro env st exp (ArrowM ro H (EqSt a st_v) b f) H) ==>
   EvalM ro env st exp (ArrowM ro H a b f) ^H
Proof
  fs[EvalM_def, ArrowP_def, ArrowM_def]
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum (qspec_then `st` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs[PURE_def] \\ rw[]
  \\ fs [PULL_EXISTS]
  \\ qpat_x_assum `ArrowP ro H (EqSt a st) b f v` mp_tac
  \\ rw [ArrowP_def,EqSt_def]
  \\ last_x_assum (qspec_then `st1` strip_assume_tac)
  \\ `v' = v` by
   (drule evaluate_add_to_clock \\ fs []
    \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
    \\ drule evaluate_add_to_clock \\ fs []
    \\ disch_then (qspec_then `ck'` strip_assume_tac)
    \\ disch_then (qspec_then `ck` strip_assume_tac)
    \\ fs [] \\ rveq \\ fs [])
  \\ rveq \\ fs []
  \\ qpat_x_assum `ArrowP ro H _ b f v` mp_tac
  \\ rw [ArrowP_def,EqSt_def]
QED

Theorem ArrowP_EqSt_elim:
   (!st_v. ArrowP ro H (EqSt a st_v) b f v) ==> ArrowP ro ^H a b f v
Proof
  fs[EqSt_def, ArrowP_def, ArrowM_def] \\ metis_tac[]
QED

(* otherwise *)

Theorem EvalM_otherwise:
   !H b n.
     ((a1 ==> EvalM ro env st exp1 (MONAD a b x1) H) /\
     (!st i. a2 st ==> EvalM ro (write n i env) st exp2 (MONAD a b x2) H)) ==>
     (a1 /\ !st'. (CONTAINER(SND(x1 st) = st') ==> a2 st')) ==>
     EvalM ro env st (Handle exp1 [(Pvar n,exp2)])
       (MONAD a b (x1 otherwise x2)) ^H
Proof
  simp [EvalM_def, EvalM_def, evaluate_def] \\ rpt strip_tac
  \\ fs [pair_case_eq,result_case_eq,PULL_EXISTS,PULL_EXISTS]
  \\ last_x_assum drule \\ rw[]
  \\ Cases_on `x1 st` \\ fs [CONTAINER_def]
  \\ last_x_assum drule
  \\ fs[otherwise_def]
  \\ rename1 `x1 st = (res1,new_state)`
  \\ Cases_on `res` THEN1
   (rw [] \\ asm_exists_tac \\ fs [MONAD_def]
    \\ imp_res_tac evaluate_sing \\ rveq \\ fs []
    \\ CASE_TAC \\ fs [])
  \\ Q.PAT_X_ASSUM `MONAD xx yy zz t1 t2` mp_tac
  \\ SIMP_TAC std_ss [Once MONAD_def] \\ strip_tac
  \\ fs [] \\ rfs []
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac REFS_PRED_FRAME_imp
  \\ disch_then drule
  \\ fs [EVAL ``ALL_DISTINCT (pat_bindings (Pvar n) [])``]
  \\ rename1 `b b1 b_v`
  \\ disch_then (qspec_then `b_v` strip_assume_tac)
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck'` strip_assume_tac) \\ strip_tac
  \\ asm_exists_tac \\ fs [pmatch_def]
  \\ fs [write_def]
  \\ imp_res_tac REFS_PRED_FRAME_trans
  \\ fs[MONAD_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ asm_exists_tac \\ fs[]
QED

(* if *)

Theorem EvalM_If:
   !H.
     (a1 ==> Eval env x1 (BOOL b1)) /\
     (a2 ==> EvalM ro env st x2 (a b2) H) /\
     (a3 ==> EvalM ro env st x3 (a b3) H) ==>
     (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM ro env st (If x1 x2 x3) (a (if b1 then b2 else b3)) ^H)
Proof
  rpt strip_tac \\ fs[]
  \\ `∀H. EvalM ro env st x1 (PURE BOOL b1) ^H` by metis_tac[Eval_IMP_PURE]
  \\ fs[EvalM_def,PURE_def, BOOL_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then strip_assume_tac
  \\ simp[evaluate_def,pair_case_eq,result_case_eq,PULL_EXISTS]
  \\ fs [CONTAINER_def,PULL_EXISTS]
  \\ Cases_on `b1` \\ fs []
  \\ imp_res_tac REFS_PRED_FRAME_imp
  \\ first_x_assum drule
  \\ strip_tac
  \\ rename1 `evaluate (_ with clock := ck0) _ _ = _`
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck0` strip_assume_tac)
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [do_if_def]
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_trans]
QED

(* Let *)

Theorem EvalM_Let:
   !H.
    Eval env exp (a res) /\
    (!v. a res v ==> EvalM ro (write name v env) st body (b (f res)) H) ==>
    EvalM ro env st (Let (SOME name) exp body) (b (LET f res)) ^H
Proof
  rw[]
  \\ drule Eval_IMP_PURE \\ rw[]
  \\ fs[EvalM_def]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then strip_assume_tac
  \\ fs [evaluate_def,GSYM write_def,namespaceTheory.nsOptBind_def,PURE_def,
         pair_case_eq,result_case_eq] \\ rveq \\ fs [PULL_EXISTS]
  \\ imp_res_tac REFS_PRED_FRAME_imp
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ rename1 `evaluate (_ with clock := ck0) _ _ = _`
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck0` strip_assume_tac)
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_trans]
QED

(* PMATCH *)

Theorem EvalM_PMATCH_NIL:
   !H b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      EvalM ro env st (Mat x []) (b (PMATCH xv [])) ^H
Proof
  rw[ml_translatorTheory.CONTAINER_def]
QED

Theorem EvalM_PMATCH:
   !H b a x xv.
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
        (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs))) ^H
Proof
  rw[EvalM_def]
  \\ drule Eval_IMP_PURE \\ rw[]
  \\ fs[EvalM_def]
  \\ rw[evaluate_def,PULL_EXISTS] \\ fs[]
  \\ first_x_assum drule
  \\ disch_then strip_assume_tac
  \\ fs[PURE_def,pair_case_eq,result_case_eq,PULL_EXISTS] \\ rveq
  \\ imp_res_tac REFS_PRED_FRAME_imp
  \\ reverse (Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars`) \\ fs[]
  THEN1
   (drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match)
    \\ disch_then drule \\ disch_then drule
    \\ simp[] \\ strip_tac
    \\ first_x_assum(qspec_then`s`mp_tac)
    \\ disch_then drule \\ rw[]
    \\ reverse (fs [evaluate_def,pair_case_eq,result_case_eq])
    \\ rveq \\ fs []
    THEN1
     (rename1 `_ = (s4,Rerr err)`
      \\ Cases_on `err = Rabort Rtimeout_error`
      THEN1
       (rveq \\ fs [] \\ asm_exists_tac \\ fs []
        \\ fs[PMATCH_def,PMATCH_ROW_def] \\ asm_exists_tac \\ fs [])
      \\ drule evaluate_add_to_clock \\ simp []
      \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
      \\ drule evaluate_add_to_clock \\ simp []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ disch_then (qspec_then `ck` assume_tac)
      \\ fs [])
    \\ drule evaluate_sing \\ rw []
    \\ asm_exists_tac \\ fs []
    \\ rename1 `_ = (_,Rval [v2])`
    \\ `v2 = v` by
     (drule evaluate_add_to_clock \\ simp []
      \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
      \\ drule evaluate_add_to_clock \\ simp []
      \\ disch_then (qspec_then `ck'` assume_tac)
      \\ disch_then (qspec_then `ck` assume_tac)
      \\ fs [])
    \\ rveq \\ fs []
    \\ fs[PMATCH_def,PMATCH_ROW_def]
    \\ asm_exists_tac \\ fs [])
  \\ imp_res_tac pmatch_PMATCH_ROW_COND_Match
  \\ fs[EvalPatRel_def]
  \\ fs[PMATCH_ROW_COND_def]
  \\ first_x_assum(qspec_then`vars`mp_tac)\\simp[] \\ strip_tac
  \\ first_x_assum (qspec_then `s2.refs` strip_assume_tac)
  \\ fs [] \\ rveq \\ fs []
  \\ `EvalPatBind env a pt pat vars (env with v := nsAppend (alist_to_ns env2) env.v)`
    by (
      simp[EvalPatBind_def,sem_env_component_equality]
      \\ qexists_tac `v` \\ fs[]
      \\ qspecl_then[`s2.refs`,`pt`,`v`,`[]`,`env`]
            mp_tac(CONJUNCT1 pmatch_imp_Pmatch)
      \\ simp[]
      \\ metis_tac[])
  \\ first_x_assum drule
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac
  \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def]
  \\ `(some x. pat x = pat vars) = SOME vars` by
        (simp[optionTheory.some_def] \\ metis_tac[]) \\ fs []
  \\ qpat_x_assum `_ = (s2,Rval [v])` assume_tac
  \\ drule evaluate_set_clock \\ simp []
  \\ disch_then (qspec_then `ck'` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ metis_tac[REFS_PRED_FRAME_trans]
QED

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

Theorem EvalM_handle:
  !cons_name stamp CORRECT_CONS PARAMS_CONDITIONS EXN_TYPE
   handle_fun x1 x2 arity a2 bind_names a H.
  (!s E s1.
     CORRECT_CONS E ==>
     x1 s = (Failure E, s1) ==>
     handle_fun x1 x2 s = x2 E s1)
   ==>
  (!s.
    (!E s1.
       CORRECT_CONS E ==> x1 s <> (Failure E, s1)) ==>
       handle_fun x1 x2 s = x1 s)
  ==>
  (!E ev. EXN_TYPE E ev ==>
          CORRECT_CONS E ==>
   ?paramsv.
   ev = Conv (SOME (ExnStamp stamp)) paramsv /\
   PARAMS_CONDITIONS E paramsv /\ LENGTH paramsv = arity)
  ==>
  (!E ev.
     EXN_TYPE E ev ==>
     ~CORRECT_CONS E ==>
     ?paramsv stamp_1.
     ev = Conv (SOME (ExnStamp stamp_1)) paramsv
          /\ stamp_1 <> stamp)
  ==>
  ALL_DISTINCT bind_names ==>
  LENGTH bind_names = arity ==>
  lookup_cons cons_name env = SOME (arity,ExnStamp stamp)
  ==>
    ((a1 ==> EvalM ro env st exp1 (MONAD a EXN_TYPE x1) H) /\
     (!st E paramsv.
        PARAMS_CONDITIONS E paramsv ==>
        a2 st E ==>
        EvalM ro (write_list bind_names paramsv env) st exp2
          (MONAD a EXN_TYPE (x2 E)) H)) ==>
     (!st' E.
        a1 /\
        (CONTAINER (x1 st = (Failure E, st') /\ CORRECT_CONS E) ==> a2 st' E))
    ==>
      EvalM ro env st
        (Handle exp1 [(Pcon (SOME cons_name)
                            (MAP (\x. Pvar x) bind_names),exp2)])
        (MONAD a EXN_TYPE (handle_fun x1 x2)) H
Proof
  rw [EvalM_def]
  \\ rw[evaluate_def]
  \\ `a1` by fs []
  \\ first_x_assum drule
  \\ disch_then drule
  \\ rw [MONAD_def]
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ Cases_on `res` \\ fs [MONAD_def]
  \\ Cases_on `x1 st` \\ fs []
  \\ Cases_on `q` \\ fs []
  >-
   (qexists_tac `ck` \\ fs []
    \\ imp_res_tac evaluate_sing \\ fs [])
  \\ Cases_on `e` \\ fs [] \\ rw[]
  \\ Cases_on `CORRECT_CONS b`
  >-
   (rw []
    (* Instantiate the appropriate assumptions, throw away the others *)
    \\ first_x_assum (qspecl_then [`r`, `b`] assume_tac) \\ fs [CONTAINER_def]
    \\ first_x_assum drule \\ rw []
    \\ last_x_assum (qspecl_then[`st`, `b`, `r`] drule) \\ rw []
    \\ last_x_assum drule \\ rw []
    (* Pattern matching *)
    \\ fs [pat_bindings_def]
    \\ drule ALL_DISTINCT_pats_bindings \\ rw []
    \\ fs [pmatch_def, lookup_cons_def, same_type_def,
           namespaceTheory.id_to_n_def, same_ctor_def]
    \\ drule pmatch_list_MAP_Pvar \\ rw []
    (* Apply the assumption evaluate assumption *)
    \\ imp_res_tac REFS_PRED_FRAME_imp
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw []
    \\ fs [with_same_refs]
    \\ rw [nsAppend_write_list_eq]
    \\ qpat_x_assum `evaluate _ env [exp1] = _` assume_tac
    \\ drule evaluate_set_clock \\ fs []
    \\ disch_then (qspec_then `ck'` strip_assume_tac)
    \\ qexists_tac `ck1` \\ fs []
    \\ fs [pmatch_def, lookup_cons_def, same_type_def,
           namespaceTheory.id_to_n_def, same_ctor_def]
    \\ drule pmatch_list_MAP_Pvar \\ rw[]
    \\ fs [nsAppend_write_list_eq]
    \\ every_case_tac \\ fs []
    \\ imp_res_tac REFS_PRED_FRAME_trans \\ fs [])
  \\ qexists_tac `ck` \\ fs []
  \\ fs [pat_bindings_def]
  \\ drule ALL_DISTINCT_pats_bindings \\ rw []
  \\ rw []
  (* Throw away *)
  \\ last_x_assum kall_tac
  \\ last_x_assum (qspec_then `st` ASSUME_TAC)
  (* Branching *)
  \\ `handle_fun x1 x2 st = x1 st`
    by (first_x_assum irule
        \\ rw [] \\ metis_tac [])
  \\ last_x_assum kall_tac
  \\ last_x_assum drule \\ rw [] \\ rfs []
  (* pattern matching *)
  \\ fs [pat_bindings_def]
  \\ drule ALL_DISTINCT_pats_bindings \\ rw []
  \\ fs [pmatch_def]
  \\ fs [lookup_cons_def, same_type_def, same_ctor_def]
QED

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

val LIST_CONJ_Eval = prove(
  ``!xs Ps s:'d state.
      LIST_CONJ (MAP (λ(exp,P). Eval env exp P) (ZIP (xs,Ps))) /\
      LENGTH xs = LENGTH Ps ==>
      ?ck vs junk.
         evaluate (s with clock := ck) env xs =
           (s with refs := s.refs ++ junk,Rval vs) /\ LIST_REL (\f x. f x) Ps vs``,
  Induct \\ Cases_on `Ps` \\ fs [LIST_CONJ_def]
  THEN1 fs [state_component_equality]
  \\ rw []
  \\ first_x_assum drule \\ fs []
  \\ fs [Eval_def]
  \\ first_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ imp_res_tac (evaluate_empty_state_IMP)
  \\ fs [eval_rel_def]
  \\ disch_then (qspec_then `s with <|clock := ck2'; refs := s.refs ⧺ refs'|>`
       mp_tac)
  \\ strip_tac \\ fs []
  \\ drule evaluate_set_clock \\ fs []
  \\ qpat_x_assum `evaluate _ env _ = _` kall_tac
  \\ disch_then (qspec_then `s.clock` strip_assume_tac)
  \\ qpat_x_assum `evaluate _ env [_] = _` assume_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck1''` strip_assume_tac)
  \\ qexists_tac `ck1'''` \\ once_rewrite_tac [evaluate_cons]
  \\ fs [state_component_equality]);

Theorem LIST_REL_EQ_LIST_CONJ_MAP:
   !xs ys.
      LENGTH xs = LENGTH ys ⇒
      LIST_REL (λf x. f x) xs ys =
      LIST_CONJ (MAP (λ(P,v). P v) (ZIP (xs,ys)))
Proof
  Induct \\ fs [LIST_CONJ_def]
  \\ Cases_on `ys` \\ fs [LIST_CONJ_def]
QED

Theorem EvalM_raise:
  !cons_name stamp EXN_TYPE EVAL_CONDS arity E exprs f a H.
  (!values.
     LENGTH values = arity ==>
     LIST_CONJ (MAP (\(P,v). P v) (ZIP(EVAL_CONDS,values))) ==>
     EXN_TYPE E (Conv (SOME (ExnStamp stamp)) values))
  ==>
  f st = (Failure E, st) ==>
  LENGTH exprs = arity ==>
  LENGTH EVAL_CONDS = arity ==>
  lookup_cons cons_name env = SOME (arity, ExnStamp stamp) ==>
  LIST_CONJ (MAP (\(exp,P). Eval env exp P) (ZIP (exprs,EVAL_CONDS))) ==>
  EvalM ro env st (Raise (Con (SOME cons_name) exprs))
    (MONAD a EXN_TYPE f) H
Proof
  rw [EvalM_def]
  \\ rw [evaluate_def, do_con_check_def, build_conv_def]
  \\ fs [lookup_cons_def]
  \\ qpat_x_assum `LIST_CONJ _` mp_tac
  \\ once_rewrite_tac [GSYM LIST_CONJ_REVERSE]
  \\ rewrite_tac [GSYM MAP_REVERSE]
  \\ simp [REVERSE_ZIP]
  \\ strip_tac
  \\ drule LIST_CONJ_Eval
  \\ fs []
  \\ disch_then (qspec_then `s` strip_assume_tac)
  \\ fs [GSYM EVERY2_REVERSE1]
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qexists_tac `ck` \\ fs []
  \\ qexists_tac `st` \\ fs []
  \\ PURE_REWRITE_TAC [GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]
  \\ fs [MONAD_def]
  \\ first_x_assum irule
  \\ imp_res_tac evaluate_length \\ fs []
  \\ `LENGTH EVAL_CONDS = LENGTH (REVERSE vs)` by fs []
  \\ drule LIST_REL_EQ_LIST_CONJ_MAP
  \\ fs [GSYM EVERY2_REVERSE1]
QED

(* read and update refs *)

Theorem EvalM_read_heap:
   !vname loc TYPE EXC_TYPE H get_var.
    (nsLookup env.v (Short vname) = SOME loc) ==>
    EvalM ro env st (App Opderef [Var (Short vname)])
    (MONAD TYPE EXC_TYPE (λrefs. (Success (get_var refs), refs)))
    ((λrefs. REF_REL TYPE loc (get_var refs) * H refs), (p:'ffi ffi_proj))
Proof
  rw[EvalM_def, REF_REL_def]
  \\ rw[evaluate_def,PULL_EXISTS]
  \\ fs[REFS_PRED_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[do_app_def]
  \\ fs[MONAD_def]
  \\ rw[store_lookup_def,EL_APPEND1,EL_APPEND2]
  >-(
      qexists_tac `s`
      \\ imp_res_tac STATE_EXTRACT_FROM_HPROP_REF
      \\ first_x_assum (qspec_then `[]` assume_tac) \\ fs[]
      \\ fs[with_same_refs, with_same_ffi]
      \\ fs[REFS_PRED_FRAME_same]
      \\ fs [state_component_equality]) >>
  imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ fs[]
QED

Theorem EvalM_write_heap:
   !vname loc TYPE PINV EXC_TYPE H get_var set_var x exp env.
  (!refs x. get_var (set_var x refs) = x) ==>
  (!refs x. H (set_var x refs) = H refs) ==>
  nsLookup env.v (Short vname) = SOME loc ==>
  CONTAINER (PINV st ==> PINV (set_var x st)) ==>
  Eval env exp (TYPE x) ==>
  EvalM ro env st (App Opassign [Var (Short vname); exp])
  ((MONAD UNIT_TYPE EXC_TYPE) (λrefs. (Success (), set_var x refs)))
  ((λrefs. REF_REL TYPE loc (get_var refs) * H refs * &PINV refs), p:'ffi ffi_proj)
Proof
  rw[REF_REL_def]
  \\ ASSUME_TAC (Thm.INST_TYPE [``:'a``|->``:'b``,``:'b``|->``:'a``]Eval_IMP_PURE)
  \\ pop_assum imp_res_tac
  \\ fs[EvalM_def] \\ rw[]
  \\ `?loc'. loc = Loc loc'` by
        (fs[REFS_PRED_def, SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC] >>
                                   imp_res_tac REF_EXISTS_LOC >> rw[])
  \\ rw[evaluate_def,PULL_EXISTS]
  \\ fs [Eval_def]
  \\ last_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ drule evaluate_empty_state_IMP
  \\ strip_tac
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x3 x2 x1. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ fs [eval_rel_def]
  \\ drule evaluate_set_clock
  \\ pop_assum kall_tac
  \\ disch_then (qspec_then `s.clock` mp_tac) \\ fs [] \\ strip_tac
  \\ rename1 `evaluate (s with clock := ck5) env [exp] = _`
  \\ qexists_tac `ck5` \\ fs []
  \\ Q.PAT_X_ASSUM `!H. P` imp_res_tac
  \\ fs[PURE_def, CONTAINER_def] \\ rw[]
  \\ fs[do_app_def]
  \\ drule evaluate_add_to_clock \\ disch_then (qspec_then `ck5` mp_tac)
  \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
  \\ drule evaluate_add_to_clock \\ disch_then (qspec_then `ck` mp_tac)
  \\ fs [] \\ simp [state_component_equality]
  \\ strip_tac
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ strip_tac \\ fs [] \\ rveq
  \\ qexists_tac `set_var x st`
  \\ imp_res_tac
       (Thm.INST_TYPE[``:'b``|->``:unit``,``:'c``|->``:unit``] REFS_PRED_FRAME_imp)
  \\ fs[REFS_PRED_def]
  \\ qpat_x_assum `P (st2heap p s)` (fn x => ALL_TAC)
  \\ fs[store_assign_def,EL_APPEND1,EL_APPEND2,store_v_same_type_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC] \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ rfs []
  \\ imp_res_tac STATE_EXTRACT_FROM_HPROP_REF
  \\ pop_assum (qspec_then `[]` ASSUME_TAC) \\ rfs []
  \\ fs[] \\ rfs []
  \\ pop_assum(fn x => ALL_TAC)
  \\ fs[MONAD_def]
  \\ fs[REFS_PRED_FRAME_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ rw[]
  >-(rw[] \\ fs[state_component_equality] \\ rw[])
  \\ qexists_tac `res`
  \\ qpat_x_assum `!F. P` imp_res_tac
  \\ EXTRACT_PURE_FACTS_TAC
  \\ pop_assum (fn x => ASSUME_TAC (CONV_RULE (RATOR_CONV PURE_FACTS_FIRST_CONV) x))
  \\ CONV_TAC (STRIP_QUANT_CONV (RATOR_CONV PURE_FACTS_FIRST_CONV))
  \\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT] \\ rfs []
  \\ fs[LUPDATE_APPEND1,LUPDATE_APPEND2,LUPDATE_def]
  \\ imp_res_tac STATE_UPDATE_HPROP_REF
  \\ last_x_assum(qspec_then `res` ASSUME_TAC)
  \\ fs[with_same_ffi] \\ rfs [st2heap_def]
QED

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
  `!H junk. A (cons x) res ==>
            (STATE_REFS A ptrs state * H) (st2heap (p:'ffi ffi_proj) s) ==>
    (STATE_REFS A (Loc (LENGTH (s.refs ++ junk))::ptrs)
     (cons x::state) * H * GC) (st2heap p
        (s with refs := s.refs ++ junk ++ [Refv res]))`,
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
  \\ pop_assum(fn x => PURE_REWRITE_TAC[x])
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
  \\ fs[SEP_EXISTS_THM, HCOND_EXTRACT]);

val valid_state_refs_extension = Q.prove(
  `A (cons x) res
   ==>
   REFS_PRED (STATE_REFS A ptrs,p:'ffi ffi_proj) refs s
   ==>
   REFS_PRED (STATE_REFS A (Loc (LENGTH (s.refs ++ junk))::ptrs), p)
             (cons x ::refs)
             (s with refs := s.refs ++ junk ++ [Refv res])`,
  rw [REFS_PRED_def, REFS_PRED_FRAME_def]
  \\ imp_res_tac valid_state_refs_frame_extension
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]);

val STATE_REFS_LENGTH = Q.prove(
  `!ptrs state H.
   (STATE_REFS A ptrs state * H) s ==> LENGTH ptrs = LENGTH state`,
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
  \\ pop_assum(fn x => SIMP_RULE bool_ss [Once STAR_COMM] x |> ASSUME_TAC)
  \\ fs[GSYM STAR_ASSOC]
  \\ last_x_assum imp_res_tac);

val valid_state_refs_reduction = Q.prove(
  `(STATE_REFS A (rv::ptrs) refs * H * GC) s
   ==>
   (STATE_REFS A ptrs (TL refs) * H * GC) s`,
  rw[]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac STATE_REFS_LENGTH
  \\ Cases_on`refs`
  \\ fs[]
  \\ fs[STATE_REFS_def]
  \\ fs[GSYM STAR_ASSOC]
  \\ last_x_assum(fn x => SIMP_RULE bool_ss [Once STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ imp_res_tac GC_ABSORB_R);

(* Validity of ref_bind *)

Theorem EvalM_ref_bind:
   Eval env xexpr (A (cons x)) ==>
   (!rv r.
      EvalM ro (write rname rv env) ((cons x)::st) exp
        (MONAD TYPE MON_EXN_TYPE (f r))
        (STATE_REFS A (rv::ptrs),p:'ffi ffi_proj)) ==>
   EvalM ro env st (Let (SOME rname) (App Opref [xexpr]) exp)
     (MONAD TYPE MON_EXN_TYPE (ref_bind (Mref cons x) f (Mpop_ref e)))
     (STATE_REFS A ptrs,p)
Proof
  rw[]
  \\ fs[Eval_def]
  \\ rw[EvalM_def]
  \\ fs [evaluate_def]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ fs [eval_rel_def]
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x1 x2 x3. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ rw[do_app_def]
  \\ rw[store_alloc_def]
  \\ rw[namespaceTheory.nsOptBind_def]
  \\ fs[write_def]
  \\ last_x_assum(qspec_then `Loc (LENGTH refs' + LENGTH s.refs)` ASSUME_TAC)
  \\ first_x_assum(qspec_then `StoreRef (LENGTH st)` ASSUME_TAC)
  \\ fs[with_same_ffi]
  \\ fs[EvalM_def]
  \\ first_x_assum(qspecl_then [`s with refs := s.refs ++ refs' ++ [Refv res]`] ASSUME_TAC)
  \\ imp_res_tac valid_state_refs_extension
  \\ first_x_assum(qspec_then`refs'` ASSUME_TAC)
  \\ fs[]
  \\ fs[]
  \\ qpat_x_assum `evaluate (s with clock := ck1) env [xexpr] = _` assume_tac
  \\ drule evaluate_set_clock
  \\ pop_assum kall_tac \\ simp []
  \\ disch_then (qspec_then `ck` mp_tac) \\ strip_tac
  \\ qexists_tac `ck1'` \\ fs [with_same_ffi]
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
     >> Cases_on `q` \\ fs []
     >> Cases_on `res'` \\ fs []
     >> imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
     >> Cases_on `r` \\ fs []
     >> fs[]
     >> rw[]
     >-(
          qpat_x_assum `!F. P` imp_res_tac
          >> fs[Once STATE_REFS_def]
          >> fs[SEP_CLAUSES, SEP_F_def])
     >-(
          Cases_on `e'`
          >> fs[]
          >> irule FALSITY
          >> qpat_x_assum `!F. P` imp_res_tac
          >> fs[GSYM STAR_ASSOC]
          >> imp_res_tac STATE_REFS_LENGTH
          >> rw[]
          >> fs[LENGTH])
     >> Cases_on `e'`
     >> fs[]
     >> rw[])
  \\ simp[state_component_equality]
  \\ rpt strip_tac
  \\ first_x_assum(qspec_then `F' * GC` ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ qspecl_then [`F'`, `refs'`] imp_res_tac valid_state_refs_frame_extension
  \\ ntac 2 (pop_assum(fn x => ALL_TAC))
  \\ fs[]
  \\ pop_assum(fn x => ALL_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ fs[STAR_ASSOC]
  \\ irule valid_state_refs_reduction
  \\ metis_tac[]
QED

(* Validity of a deref operation *)
val STATE_REFS_EXTRACT = Q.prove(
  `!ptrs1 r ptrs2 refs TYPE H (p:'ffi ffi_proj) s.
   ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) ==>
   ((STATE_REFS TYPE ptrs1 (TAKE (LENGTH ptrs1) refs) *
   (STATE_REF TYPE r (EL (LENGTH ptrs1) refs)) *
   (STATE_REFS TYPE ptrs2 (DROP (LENGTH ptrs1 + 1) refs)) * H)) (st2heap p s)`,
  Induct
  >-(
      rw[]
      >> rw[STATE_REFS_def]
      >> rw[SEP_CLAUSES]
      >> rw[GSYM STATE_REFS_def]
      >> imp_res_tac STATE_REFS_LENGTH
      >> Cases_on `refs`
      >> fs[])
  \\ rw[]
  \\ imp_res_tac STATE_REFS_LENGTH
  \\ Cases_on `refs`
  \\ fs[]
  \\ fs[STATE_REFS_def]
  \\ fs[GSYM STAR_ASSOC]
  \\ qpat_x_assum `H' (st2heap p s)` (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_COMM] x |> ASSUME_TAC)
  \\ rw[Once STAR_COMM]
  \\ fs[STAR_ASSOC]
  \\ qpat_x_assum `H' (st2heap p s)` (fn x => PURE_ONCE_REWRITE_RULE[GSYM STAR_ASSOC] x |> ASSUME_TAC)
  \\ rw[Once (GSYM STAR_ASSOC)]
  \\ last_x_assum imp_res_tac
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
  \\ imp_res_tac STATE_REFS_EXTRACT
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
      >> pop_assum(fn x => PURE_REWRITE_TAC[x])
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

Theorem STATE_REFS_DECOMPOSE:
   !ptrs1 r ptrs2 refs TYPE H (p:'ffi ffi_proj) s. ((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) refs) * H) (st2heap p s) <=>
  ?refs1 y refs2.
  refs = refs1 ++ [y] ++ refs2 /\
  ((STATE_REFS TYPE ptrs1 refs1 *
  (STATE_REF TYPE r y) *
  (STATE_REFS TYPE ptrs2 refs2) *
  H)) (st2heap p s)
Proof
  rpt strip_tac
  \\ EQ_TAC
  >-(
      rw[]
      >> sg `?refs1 refs'. refs = refs1 ++ refs' /\ LENGTH refs1 = LENGTH ptrs1`
      >-(
          imp_res_tac STATE_REFS_LENGTH
          >> qexists_tac `TAKE (LENGTH ptrs1) refs`
          >> qexists_tac `DROP (LENGTH ptrs1) refs`
          >> rw[TAKE_DROP]
          >> fs[LENGTH_TAKE])
      >> sg `?y refs2. refs' = [y] ++ refs2 /\ LENGTH refs2 = LENGTH ptrs2`
      >-(
          qexists_tac `HD refs'`
          >> qexists_tac `TL refs'`
          >> imp_res_tac STATE_REFS_LENGTH
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
          >> pop_assum(fn x => PURE_REWRITE_TAC[x])
          >> PURE_REWRITE_TAC[DROP_LENGTH_APPEND]
          >> fs[])
      >> imp_res_tac STATE_REFS_EXTRACT
      >> metis_tac[])
  \\ rw[]
  \\ fs[STATE_REFS_RECONSTRUCT]
QED

Theorem STATE_REFS_DECOMPOSE_2:
   !ptrs1 r ptrs2 refs1 x refs2 TYPE H (p:'ffi ffi_proj) s.
  LENGTH ptrs1 = LENGTH refs1 ==>
  LENGTH ptrs2 = LENGTH refs2 ==>
  (((STATE_REFS TYPE (ptrs1 ++ [r] ++ ptrs2) (refs1 ++ [x] ++ refs2)) * H) (st2heap p s) <=>
  ((STATE_REFS TYPE ptrs1 refs1 *
  (STATE_REF TYPE r x) *
  (STATE_REFS TYPE ptrs2 refs2) *
  H)) (st2heap p s))
Proof
  rpt strip_tac
  \\ EQ_TAC
  >-(
      rw[]
      >> fs[STATE_REFS_EXTRACT_2])
  \\ rw[]
  \\ fs[STATE_REFS_RECONSTRUCT]
QED

Theorem store_lookup_CELL_st2heap:
   (l ~~>> res * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l (s.refs ++ junk) = SOME res
Proof
  rw[]
  \\ imp_res_tac STATE_EXTRACT_FROM_HPROP
  \\ imp_res_tac st2heap_CELL_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ fs[store_lookup_def]
QED

Theorem store_lookup_REF_st2heap:
   (Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l s.refs = SOME (Refv v)
Proof
  rw[]
  \\ imp_res_tac STATE_EXTRACT_FROM_HPROP_REF
  \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ first_x_assum (qspec_then `[]` assume_tac)
  \\ fs[store_lookup_def]
QED

Theorem store_lookup_REF_st2heap_junk:
   (Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l (s.refs ++ junk) = SOME (Refv v)
Proof
  rw[]
  \\ imp_res_tac STATE_EXTRACT_FROM_HPROP_REF
  \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ fs[store_lookup_def]
QED

Theorem store_lookup_ARRAY_st2heap:
   (ARRAY (Loc l) av * H) (st2heap (p:'ffi ffi_proj) s) ==> store_lookup l s.refs = SOME (Varray av)
Proof
  rw[]
  \\ imp_res_tac STATE_EXTRACT_FROM_HPROP_ARRAY
  \\ imp_res_tac st2heap_ARRAY_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ first_x_assum (qspec_then `[]` assume_tac)
  \\ fs[store_lookup_def]
QED

Theorem EvalM_Mdref:
   nsLookup env.v (Short rname) = SOME rv ==>
  r = LENGTH ptrs2 ==>
  EvalM ro env st (App Opderef [Var (Short rname)])
  (MONAD TYPE (\x v. F) (Mdref e (StoreRef r)))
    (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2),p:'ffi ffi_proj)
Proof
  rw[]
  \\ fs[EvalM_def]
  \\ rw[evaluate_def]
  \\ rw[do_app_def]
  \\ fs[REFS_PRED_def]
  \\ imp_res_tac STATE_REFS_EXTRACT
  \\ fs[GSYM STAR_ASSOC]
  \\ pop_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ fs[STATE_REF_def, SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ fs[]
  \\ imp_res_tac store_lookup_REF_st2heap
  \\ fs[]
  \\ qexists_tac `st`
  \\ qexists_tac `s.clock`
  \\ fs[with_same_ffi]
  \\ fs[MONAD_def]
  \\ `LENGTH ptrs2 < LENGTH st` by (imp_res_tac STATE_REFS_LENGTH \\ fs[])
  \\ fs[Mdref_eq]
  \\ fs[dref_def]
  \\ `LENGTH st - (LENGTH ptrs2 + 1) = LENGTH ptrs1` by (imp_res_tac STATE_REFS_LENGTH \\ fs[])
  \\ pop_assum(fn x => fs[x])
  \\ fs[REFS_PRED_FRAME_def]
  \\ rw[state_component_equality]
  \\ fs[Once (GSYM with_same_refs)]
  \\ irule H_STAR_GC_SAT_IMP \\ fs[]
QED

(* Validity of an assigment operation *)
Theorem store_assign_REF_st2heap:
   (Loc l ~~> v * H) (st2heap (p:'ffi ffi_proj) s) ==>
  store_assign l (Refv res) (s.refs ++ junk) = SOME (LUPDATE (Refv res) l (s.refs ++ junk))
Proof
  rw[]
  \\ simp[store_assign_def]
  \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ fs[store_v_same_type_def]
  \\ imp_res_tac store2heap_IN_EL
  \\ fs[EL_APPEND1]
QED

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
        >> imp_res_tac STATE_REFS_LENGTH)
  \\ fs[lupdate_append2]
  \\ fs[STATE_REFS_DECOMPOSE]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac STATE_REFS_LENGTH
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
  \\ imp_res_tac STATE_UPDATE_HPROP_REF
  \\ pop_assum(qspec_then `res` ASSUME_TAC)
  \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ imp_res_tac STATE_APPEND_JUNK
  \\ fs[LUPDATE_APPEND1]
  \\ metis_tac[STAR_ASSOC, STAR_COMM]);

Theorem EvalM_Mref_assign:
   nsLookup env.v (Short rname) = SOME rv ==>
  r = LENGTH ptrs2 ==>
  Eval env xexpr (TYPE x) ==>
  EvalM ro env st (App Opassign [Var (Short rname); xexpr])
  (MONAD UNIT_TYPE (\x v. F) (Mref_assign e (StoreRef r) x)) (STATE_REFS TYPE (ptrs1 ++ [rv] ++ ptrs2),p:'ffi ffi_proj)
Proof
  rw[]
  \\ fs[EvalM_def,evaluate_def]
  \\ fs[Eval_def] \\ rw []
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ rw [] \\ fs [eval_rel_def]
  \\ drule evaluate_set_clock
  \\ disch_then (qspec_then `s.clock` strip_assume_tac) \\ fs []
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x1 x2 x3. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ qexists_tac `ck1'` \\ fs []
  \\ fs[REFS_PRED_def]
  \\ imp_res_tac STATE_REFS_EXTRACT
  \\ fs[GSYM STAR_ASSOC]
  \\ pop_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STATE_REF_def, SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[do_app_def]
  \\ imp_res_tac store_assign_REF_st2heap
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ pop_assum(fn x => simp[x])
  \\ qexists_tac `ref_assign (LENGTH ptrs2) x st`
  \\ pop_assum(fn x => PURE_REWRITE_TAC[x])
  \\ fs[UPDATE_STATE_REFS,with_same_ffi]
  \\ fs[MONAD_def]
  \\ imp_res_tac STATE_REFS_LENGTH
  \\ fs[Mref_assign_eq]
QED

(* Allocation of the initial store for dynamic references *)
Theorem STATE_REFS_EXTEND:
   !H s refs. (STATE_REFS A ptrs refs * H) (st2heap (p:'ffi ffi_proj) s) ==>
  !x xv. A x xv ==>
  (STATE_REFS A (Loc (LENGTH s.refs)::ptrs) (x::refs) * H)(st2heap p (s with refs := s.refs ++ [Refv xv]))
Proof
  rw[]
  \\ rw[STATE_REFS_def]
  \\ rw[GSYM STAR_ASSOC]
  \\ rw[Once STAR_def]
  \\ qexists_tac `store2heap_aux (LENGTH s.refs) [Refv xv]`
  \\ qexists_tac `st2heap p s`
  \\ PURE_REWRITE_TAC[Once SPLIT_SYM]
  \\ `st2heap p s = st2heap p (s with refs := s.refs)` by fs[with_same_refs]
  \\ pop_assum(fn x => PURE_REWRITE_TAC[x])
  \\ fs[STATE_SPLIT_REFS]
  \\ fs[with_same_refs]
  \\ simp[STATE_REF_def, store2heap_aux_def]
  \\ simp[SEP_EXISTS_THM]
  \\ qexists_tac `xv`
  \\ EXTRACT_PURE_FACTS_TAC
  \\ simp[REF_def, cell_def, one_def, SEP_EXISTS_THM, HCOND_EXTRACT]
QED

(* Resizable arrays *)
val ABS_NUM_EQ = Q.prove(`Num(ABS(&n))=n`,
  rw[DB.fetch "integer" "Num", integerTheory.INT_ABS]);

val do_app_Opderef_REF = Q.prove(
  `(REF (Loc loc) v * H refs) (st2heap (p:'ffi ffi_proj) s) ==>
  !junk. do_app (s.refs ++ junk, s.ffi) Opderef [Loc loc] =
    SOME ((s.refs ++ junk, s.ffi), Rval v)`,
  rw[do_app_def]
  \\ imp_res_tac store_lookup_REF_st2heap_junk
  \\ fs[with_same_ffi]);

val do_app_Alength_ARRAY = Q.prove(
  `(ARRAY rv v * H) (st2heap (p:'ffi ffi_proj) s) ==>
  do_app (s.refs, s.ffi) Alength [rv] =
  SOME ((s.refs, s.ffi), Rval (Litv(IntLit(int_of_num(LENGTH v)))))`,
  rw[do_app_def]
  \\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
  \\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
  \\ imp_res_tac store_lookup_CELL_st2heap
  \\ first_x_assum(qspec_then `[]` ASSUME_TAC)
  \\ fs[]);

Theorem EvalM_R_Marray_length:
   !vname loc TYPE EXC_TYPE H get_arr x env.
    nsLookup env.v (Short vname) = SOME loc ==>
    EvalM ro env st (App Alength [App Opderef [Var (Short vname)]])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[REFS_PRED_def, RARRAY_REL_def, RARRAY_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[]
  \\ rw[evaluate_def]
  \\ imp_res_tac do_app_Opderef_REF
  \\ first_x_assum(qspecl_then [`[]`] ASSUME_TAC) \\ fs[with_same_refs]
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x1 x2 x3. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ once_rewrite_tac [evaluate_def] \\ fs []
  \\ qexists_tac `s.clock` \\ fs [with_same_refs]
  \\ rw[Marray_length_def]
  \\ fs[MONAD_def]
  \\ qexists_tac `s`
  \\ fs[state_component_equality]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM STAR_COMM)]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[state_component_equality]
  \\ drule do_app_Alength_ARRAY \\ rw[]
  \\ fs[state_component_equality]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[REFS_PRED_FRAME_same]
QED

val Conv_Subscript = EVAL ``sub_exn_v`` |> concl |> rand
val Stamp_Subscript = Conv_Subscript |> rator |> rand |> rand

val do_app_Asub_ARRAY = Q.prove(
 `(ARRAY rv v * H) (st2heap (p:'ffi ffi_proj) s) ==>
  !junk. do_app (s.refs ++ junk, s.ffi) Asub [rv; Litv (IntLit (&n))] =
    if n < LENGTH v then SOME ((s.refs ++ junk, s.ffi), Rval (EL n v))
    else SOME ((s.refs ++ junk, s.ffi), Rerr (Rraise ^Conv_Subscript))`,
  rw[do_app_def]
  \\ fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM]
  \\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]
  \\ imp_res_tac store_lookup_CELL_st2heap
  \\ fs[ABS_NUM_EQ]
  \\ Cases_on `n ≥ LENGTH v` \\ fs[] \\ EVAL_TAC);

val evaluate_empty_state_IMP_2 =
  evaluate_empty_state_IMP
  |> Q.GEN`s` |> Q.SPEC`s with refs := s.refs ++ more`
  |> SIMP_RULE(srw_ss())[]

val evaluate_empty_state_IMP_3 =
  evaluate_empty_state_IMP
  |> Q.GEN`s` |> Q.SPEC`s with refs := s.refs ++ more ++ more2`
  |> SIMP_RULE(srw_ss())[]

Theorem EvalM_R_Marray_sub_subscript:
   !vname loc TYPE EXC_TYPE H get_arr e env n nexp.
     EXC_TYPE e ^Conv_Subscript ==>
     nsLookup env.v (Short vname) = SOME loc ==>
     lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
     Eval env nexp (NUM n) ==>
     EvalM ro env st (App Asub [App Opderef [Var (Short vname)]; nexp])
     ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
     ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ rw[evaluate_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ first_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[]))
  \\ disch_then(qx_choose_then`ck`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`ck` \\ rw[]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac do_app_Opderef_REF
  \\ pop_assum(qspec_then `refs'` ASSUME_TAC)
  \\ fs[]
  \\ fs[STAR_ASSOC]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw[]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac do_app_Asub_ARRAY
  \\ first_x_assum (qspecl_then [`n`, `refs'`] assume_tac)
  \\ fs[]
  \\ Cases_on `n < LENGTH (get_arr st)`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def, Msub_eq]
     \\ fs[LIST_REL_EL_EQN]
     \\ fs[with_same_ffi]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[with_same_ffi]
  \\ qexists_tac `st`
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ fs[REFS_PRED_FRAME_append]
QED

Theorem EvalM_R_Marray_sub_handle:
   !vname loc TYPE EXC_TYPE H get_arr e rexp env n nexp.
     nsLookup env.v (Short vname) = SOME loc ==>
     lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
     Eval env nexp (NUM n) ==>
     Eval env rexp (EXC_TYPE e) ==>
     EvalM ro env st (Handle (App Asub [App Opderef [Var (Short vname)]; nexp])
                [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
     ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
     ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ rw[evaluate_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ last_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ first_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [nexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`if n < LENGTH (get_arr st) then s.clock else k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ ASM_REWRITE_TAC[] \\ simp_tac(srw_ss())[]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac do_app_Opderef_REF
  \\ pop_assum(qspec_then `refs'` ASSUME_TAC)
  \\ fs[]
  \\ fs[STAR_ASSOC]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ imp_res_tac LIST_REL_LENGTH
  \\ simp[]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac do_app_Asub_ARRAY
  \\ first_x_assum (qspecl_then [`n`, `refs'`] assume_tac)
  \\ Cases_on `n < LENGTH (get_arr st)`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def, Msub_eq]
     \\ fs[LIST_REL_EL_EQN, with_same_ffi]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[]
  \\ fs[lookup_cons_def]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ fs[with_same_ffi]
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rw[REFS_PRED_FRAME_append]
QED

Theorem EvalM_R_Marray_update_subscript:
   !vname loc TYPE EXC_TYPE H get_arr set_arr e env n x xexp nexp.
     nsLookup env.v (Short vname) = SOME loc ==>
     lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
     EXC_TYPE e ^Conv_Subscript ==>
     (!refs x. get_arr (set_arr x refs) = x) ==>
     (!refs x. H (set_arr x refs) = H refs) ==>
     Eval env nexp (NUM n) ==>
     Eval env xexp (TYPE x) ==>
     EvalM ro env st (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
     ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
     ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[evaluate_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`(*if n < LENGTH av then s.clock else*) k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1`
  \\ fs[] \\ rw[]
  \\ imp_res_tac do_app_Opderef_REF
  \\ first_x_assum(qspec_then `refs' ++ refs''` ASSUME_TAC)
  \\ fs[]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ imp_res_tac STATE_APPEND_JUNK
  \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC]))
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[do_app_def]
      >> fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
      >> EXTRACT_PURE_FACTS_TAC
      >> rw[]
      >> imp_res_tac LIST_REL_LENGTH
      >> fs[GSYM STAR_ASSOC]
      >> imp_res_tac store_lookup_CELL_st2heap
      >> pop_assum(fn x => ALL_TAC)
      >> pop_assum(qspec_then `[]` ASSUME_TAC)
      >> fs[ABS_NUM_EQ]
      >> imp_res_tac st2heap_CELL_MEM
      >> imp_res_tac store2heap_IN_LENGTH
      >> fs[store_assign_def, store_v_same_type_def]
      >> imp_res_tac store2heap_IN_EL
      >> fs[]
      >> qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      >> fs[MONAD_def, Marray_update_def, Mupdate_eq]
      >> fs[REFS_PRED_FRAME_def]
      >> rw[state_component_equality]
      >> fs[Once (GSYM with_same_refs)]
      >> pop_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      >> pop_assum(qspec_then`refs'++refs''` ASSUME_TAC)
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
         >> pop_assum(fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
         >> fs[GSYM STAR_ASSOC]
         >> qpat_x_assum `(GC * H1) X` (fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
         >> fs[GSYM STAR_ASSOC]
         >> fs[REF_def, SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC, HCOND_EXTRACT]
         >> imp_res_tac UNIQUE_CELLS
         >> rw[])
      >> rw[]
      >> fs[GSYM STAR_ASSOC]
      >> imp_res_tac STATE_UPDATE_HPROP_ARRAY
      >> pop_assum(qspec_then `LUPDATE res n av` ASSUME_TAC)
      >> fs[with_same_ffi])
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac store_lookup_CELL_st2heap
  \\ pop_assum(fn x => ALL_TAC)
  \\ pop_assum(qspec_then `[]` ASSUME_TAC)
  \\ fs [with_same_refs, with_same_ffi] \\ rw [do_app_def]
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ rw[with_same_ffi,EVAL ``sub_exn_v``]
  \\ metis_tac[REFS_PRED_FRAME_append, GSYM APPEND_ASSOC]
QED

Theorem EvalM_R_Marray_update_handle:
   !vname loc TYPE EXC_TYPE H get_arr set_arr e rexp env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (Handle (App Aupdate [App Opderef [Var (Short vname)]; nexp; xexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[evaluate_def]
  \\ first_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ first_x_assum(qspec_then `s.refs ++ refs' ++ refs''` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_3 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k3`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [nexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`if n < LENGTH av then s.clock else k3`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1`
  \\ fs[]
  \\ imp_res_tac do_app_Opderef_REF
  \\ pop_assum(qspec_then`refs'++refs''`assume_tac) \\ fs[]
  \\ fs[Once STAR_COMM]
  \\ fs[GSYM STAR_ASSOC]
  \\ fs[Once (GSYM with_same_refs)]
  \\ imp_res_tac STATE_APPEND_JUNK
  \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC]))
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[do_app_def]
      >> fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
      >> EXTRACT_PURE_FACTS_TAC
      >> rw[]
      >> imp_res_tac LIST_REL_LENGTH
      >> fs[GSYM STAR_ASSOC]
      >> imp_res_tac store_lookup_CELL_st2heap
      >> pop_assum(fn x => ALL_TAC)
      >> pop_assum(qspec_then `[]` ASSUME_TAC)
      >> fs[ABS_NUM_EQ]
      >> imp_res_tac st2heap_CELL_MEM
      >> imp_res_tac store2heap_IN_LENGTH
      >> fs[store_assign_def, store_v_same_type_def]
      >> imp_res_tac store2heap_IN_EL
      >> fs[]
      >> rw[]
      >> qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      >> fs[MONAD_def, Marray_update_def, Mupdate_eq]
      >> fs[REFS_PRED_FRAME_def]
      >> rw[state_component_equality]
      >> fs[Once (GSYM with_same_refs)]
      >> pop_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      >> pop_assum(qspec_then`refs'++refs''` ASSUME_TAC)
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
         >> pop_assum(fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
         >> fs[GSYM STAR_ASSOC]
         >> qpat_x_assum `(GC * H1) X` (fn x => PURE_REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
         >> fs[GSYM STAR_ASSOC]
         >> fs[REF_def, SEP_EXISTS_THM, SEP_CLAUSES, GSYM STAR_ASSOC, HCOND_EXTRACT]
         >> imp_res_tac UNIQUE_CELLS
         >> rw[])
      >> rw[]
      >> fs[GSYM STAR_ASSOC]
      >> imp_res_tac STATE_UPDATE_HPROP_ARRAY
      >> pop_assum(qspec_then `LUPDATE res n av` ASSUME_TAC)
      >> fs[with_same_ffi])
  \\ rw[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac store_lookup_CELL_st2heap
  \\ pop_assum(fn x => ALL_TAC)
  \\ pop_assum(qspec_then `[]` ASSUME_TAC)
  \\ fs [with_same_refs]
  \\ fs[lookup_cons_def,EVAL ``sub_exn_v``]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ fs[with_same_ffi]
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]
QED

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

Theorem EvalM_R_Marray_alloc:
   !vname loc TYPE EXC_TYPE H get_arr set_arr n x env nexp xexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (App Opassign [Var (Short vname); App Aalloc [nexp; xexp]])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_alloc set_arr n x))
   ((λrefs. RARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[evaluate_def]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`(*if n < LENGTH av then s.clock else*) k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[]
  \\ rw[do_app_def]
  \\ rw[store_alloc_def]
  \\ rw[with_same_ffi]
  \\ qpat_x_assum `REFS_PRED H1 st s` (fn x => PURE_REWRITE_RULE[REFS_PRED_def, RARRAY_def, RARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ fs[Once (GSYM with_same_refs)]
  \\ fs[GSYM STAR_ASSOC]
  \\ imp_res_tac REF_EXISTS_LOC
  \\ rw[]
  \\ imp_res_tac store_assign_REF_st2heap
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ fs[]
  \\ Q.PAT_ABBREV_TAC `loc = LENGTH junk + L`
  \\ Q.PAT_ABBREV_TAC `srefs = A ++ [Varray X]`
  \\ fs[MONAD_def, Marray_alloc_def]
  \\ rw[REFS_PRED_FRAME_def, state_component_equality]
  \\ fs[RARRAY_def, RARRAY_REL_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ qexists_tac `REPLICATE n res`
  \\ qexists_tac `Loc loc`
  \\ qpat_x_assum `Abbrev X` (fn x => fs[PURE_REWRITE_RULE[markerTheory.Abbrev_def] x])
  \\ imp_res_tac st2heap_REF_MEM
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ fs[with_same_refs, with_same_ffi]
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
  \\ simp[STAR_ASSOC, Once STAR_COMM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ sg `(Loc l ~~> arv' * H st * F' * GC) (st2heap p s)`
  >-(fs[GSYM STAR_ASSOC]
     \\ fs[Once STAR_COMM]
     \\ fs[GSYM STAR_ASSOC]
     \\ ntac 2 (pop_assum (fn x => ALL_TAC))
     \\ pop_assum(fn x => MATCH_MP HPROP_TO_GC_L x |> ASSUME_TAC)
     \\ metis_tac[STAR_ASSOC, STAR_COMM])
  \\ fs[GSYM STAR_ASSOC]
  \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_REF) x |> ASSUME_TAC)
  \\ first_x_assum(qspec_then `Loc loc` ASSUME_TAC)
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ pop_assum(qspec_then `refs' ++ refs''` ASSUME_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
QED

(* Fixed-size arrays *)
Theorem EvalM_F_Marray_length:
   !vname loc TYPE EXC_TYPE H get_arr x env.
    nsLookup env.v (Short vname) = SOME loc ==>
    EvalM ro env st (App Alength [Var (Short vname)])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs [evaluate_def]
  \\ fs[REFS_PRED_def, ARRAY_REL_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_x_assum (fn x => MATCH_MP do_app_Alength_ARRAY x |> ASSUME_TAC)
  \\ fs[with_same_refs, with_same_ffi]
  \\ qexists_tac `st`
  \\ qexists_tac `s.clock` \\ fs [with_same_clock]
  \\ pop_assum (fn x => fs[x])
  \\ fs[MONAD_def, Marray_length_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[REFS_PRED_FRAME_same]
QED

Theorem EvalM_F_Marray_sub_subscript:
   !vname loc TYPE EXC_TYPE H get_arr e env n nexp.
   EXC_TYPE e ^Conv_Subscript ==>
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
   Eval env nexp (NUM n) ==>
   EvalM ro env st (App Asub [Var (Short vname); nexp])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_x_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum (fn x => MATCH_MP ARRAY_EXISTS_LOC x |> ASSUME_TAC)
  \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ last_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[]
  \\ rw[evaluate_def]
  \\ first_x_assum (fn x => MATCH_MP do_app_Asub_ARRAY x |> ASSUME_TAC)
  \\ first_x_assum (qspec_then `refs'` assume_tac) \\ fs[]
  \\ Cases_on `n < LENGTH av`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def, Msub_eq]
     \\ fs[LIST_REL_EL_EQN, with_same_ffi]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ rw[with_same_ffi]
  \\ qexists_tac `st`
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq, REFS_PRED_FRAME_append]
QED

Theorem EvalM_F_Marray_sub_handle:
   !vname loc TYPE EXC_TYPE H get_arr e rexp env n nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   EvalM ro env st (Handle (App Asub [Var (Short vname); nexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr e n))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ first_x_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum (fn x => MATCH_MP ARRAY_EXISTS_LOC x |> ASSUME_TAC)
  \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rw[evaluate_def]
  \\ last_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ first_x_assum (qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ pop_assum(strip_assume_tac o RW[eval_rel_def])
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [nexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`if n < LENGTH av then s.clock else k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[]
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum (fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ first_x_assum(qspec_then `refs'` ASSUME_TAC)
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ first_x_assum (fn x => MATCH_MP do_app_Asub_ARRAY x |> ASSUME_TAC)
  \\ first_x_assum (qspec_then `[]` assume_tac) \\ fs[]
  \\ Cases_on `n < LENGTH av`
  >-(fs[]
     \\ fs[MONAD_def, Marray_sub_def, Msub_eq]
     \\ fs[LIST_REL_EL_EQN, with_same_ffi]
     \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append])
  \\ fs[with_same_refs]
  \\ fs[lookup_cons_def]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ fs[with_same_ffi]
  \\ fs[MONAD_def, Marray_sub_def, Msub_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rw[REFS_PRED_FRAME_append]
QED

Theorem EvalM_F_Marray_update_subscript:
   !vname loc TYPE EXC_TYPE H get_arr set_arr e env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
   EXC_TYPE e ^Conv_Subscript ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (App Aupdate [Var (Short vname); nexp; xexp])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[evaluate_def]
  \\ pop_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP ARRAY_EXISTS_LOC x |> STRIP_ASSUME_TAC)
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ fs[eval_rel_def]
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[]
  \\ rw[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ rw[]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP (GEN_ALL store_lookup_CELL_st2heap) x |> ASSUME_TAC)
  \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ fs[]
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
      \\ qexists_tac `Rval [Conv NONE []]`
      \\ drule EL_APPEND1 \\ disch_then (qspec_then `refs' ++ refs''` assume_tac)
      \\ reverse(rw[] \\ fs[])
      >-(ntac 2 (qpat_x_assum `_ = _` (fn x => fs [x])))
      \\ qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      \\ fs[MONAD_def, Marray_update_def, Mupdate_eq]
      \\ fs[REFS_PRED_FRAME_def]
      \\ rw[state_component_equality]
      \\ fs[Once (GSYM with_same_refs)]
      \\ pop_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC)
      \\ fs[ARRAY_REL_def, SEP_CLAUSES, SEP_EXISTS_THM]
      \\ qexists_tac `LUPDATE res n av`
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[EVERY2_LUPDATE_same]
      \\ fs[GSYM STAR_ASSOC]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_ARRAY) x |> ASSUME_TAC)
      \\ pop_assum(qspec_then `LUPDATE res n av` ASSUME_TAC)
      \\ fs[])
  \\ fs[with_same_ffi]
  \\ qexists_tac `st`
  \\ fs[MONAD_def,Marray_update_def,Mupdate_exn_eq,EVAL ``sub_exn_v``]
  \\ metis_tac[REFS_PRED_FRAME_append, GSYM APPEND_ASSOC]
QED

Theorem EvalM_F_Marray_update_handle:
   !vname loc TYPE EXC_TYPE H get_arr set_arr e rexp env n x xexp nexp.
   nsLookup env.v (Short vname) = SOME loc ==>
   lookup_cons (Short "Subscript") env = SOME (0,^Stamp_Subscript) ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   Eval env nexp (NUM n) ==>
   Eval env rexp (EXC_TYPE e) ==>
   Eval env xexp (TYPE x) ==>
   EvalM ro env st (Handle (App Aupdate [Var (Short vname); nexp; xexp])
              [(Pcon (SOME (Short("Subscript"))) [], Raise rexp)])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_update get_arr set_arr e n x))
   ((λrefs. ARRAY_REL TYPE loc (get_arr refs) * H refs),p:'ffi ffi_proj)
Proof
  rw[EvalM_def]
  \\ fs[Eval_def, NUM_def, INT_def]
  \\ rw[evaluate_def]
  \\ pop_assum(fn x => SIMP_RULE bool_ss [REFS_PRED_def, ARRAY_REL_def] x |> ASSUME_TAC)
  \\ fs[SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP ARRAY_EXISTS_LOC x |> STRIP_ASSUME_TAC)
  \\ rw[]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ last_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ fs[]
  \\ last_x_assum(qspec_then `s.refs ++ (refs' ++ refs'')` STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_3 x |> STRIP_ASSUME_TAC)
  \\ fs[eval_rel_def]
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`s.clock`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k3`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [nexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`if n < LENGTH av then s.clock else k3`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[]
  \\ simp[do_app_def]
  \\ fs[ARRAY_def, SEP_EXISTS_THM, SEP_CLAUSES]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[GSYM STAR_ASSOC]
  \\ first_assum(fn x => MATCH_MP (GEN_ALL store_lookup_CELL_st2heap) x |> ASSUME_TAC)
  \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ fs[]
  \\ fs[Once (GSYM with_same_refs)]
  \\ first_x_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
  \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC o (PURE_REWRITE_RULE[GSYM STAR_ASSOC, GC_STAR_GC]))
  \\ Cases_on `n < LENGTH av`
  >-(
      rw[]
      \\ first_assum(fn x => MATCH_MP st2heap_CELL_MEM x |> ASSUME_TAC)
      \\ first_assum(fn x => MATCH_MP store2heap_IN_LENGTH x |> ASSUME_TAC)
      \\ fs[store_assign_def, store_v_same_type_def]
      \\ first_assum(fn x => MATCH_MP store2heap_IN_EL x |> ASSUME_TAC)
      \\ fs[]
      \\ qexists_tac `set_arr (LUPDATE x n (get_arr st)) st`
      \\ fs[MONAD_def, Marray_update_def, Mupdate_eq]
      \\ fs[REFS_PRED_FRAME_def]
      \\ rw[state_component_equality]
      \\ fs[Once (GSYM with_same_refs)]
      \\ pop_assum(fn x => MATCH_MP STATE_APPEND_JUNK x |> ASSUME_TAC)
      \\ pop_assum(qspec_then`refs'++refs''` ASSUME_TAC)
      \\ fs[ARRAY_REL_def, SEP_CLAUSES, SEP_EXISTS_THM]
      \\ qexists_tac `LUPDATE res n av`
      \\ EXTRACT_PURE_FACTS_TAC
      \\ fs[EVERY2_LUPDATE_same, with_same_ffi]
      \\ fs[GSYM STAR_ASSOC]
      \\ first_x_assum(fn x => MATCH_MP (GEN_ALL STATE_UPDATE_HPROP_ARRAY) x |> ASSUME_TAC)
      \\ pop_assum(qspec_then `LUPDATE res n av` ASSUME_TAC)
      \\ fs[])
  \\ fs[with_same_refs, with_same_ffi]
  \\ fs[lookup_cons_def, EVAL ``sub_exn_v``]
  \\ fs[same_type_def,namespaceTheory.id_to_n_def,same_ctor_def]
  \\ rw[pat_bindings_def]
  \\ rw[pmatch_def]
  \\ fs[MONAD_def, Marray_update_def, Mupdate_exn_eq]
  \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC, REFS_PRED_FRAME_append]
QED

(* TODO: implement support for 2d arrays *)
val ARRAY2D_def = Define `
  ARRAY2D av l = SEP_EXISTS fl. ARRAY av fl * &(fl = FLAT l)`;

val RARRAY2D_def = Define `
  RARRAY2D rv l = SEP_EXISTS av. REF rv av * ARRAY2D av l`;

(* TODO: implement support for n-dimensional arrays? *)

(* translation of cases and cons terms *)

Theorem IMP_EvalM_Mat_cases:
   !st a (r1:'b) env exp r2 y.
      Eval env exp (a r1) /\
      (case y of
       | INL (vars,exp) =>
                   (ALL_DISTINCT (pats_bindings (MAP Pvar vars) []) /\
                    (!v. a r1 v ==>
                         ?name vals t.
                           v = Conv NONE vals /\
                           LENGTH vals = LENGTH vars /\
                           EvalM ro (write_list (ZIP (vars,vals)) env) st exp r2 ^H))
       | INR ps => ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
                   good_cons_env ps env /\
                   (!v. a r1 v ==>
                        ?name vals t vars exp.
                          v = Conv (SOME t) vals /\
                          MEM (name,vars,exp,t) ps /\
                          LENGTH vals = LENGTH vars /\
                          EvalM ro (write_list (ZIP (vars,vals)) env) st exp r2 H))
      ==>
      EvalM ro env st (Mat exp (Mat_cases y)) r2 H
Proof
  rpt gen_tac \\ Cases_on `y`
  THEN1
   (Cases_on `x`
    \\ fs [EvalM_def,EXISTS_MEM,EXISTS_PROD,Eval_def]
    \\ rpt strip_tac
    \\ last_x_assum (qspec_then `s.refs` strip_assume_tac)
    \\ first_x_assum drule \\ strip_tac
    \\ rveq \\ fs []
    \\ `REFS_PRED_FRAME ro H (st,s) (st,s with refs := s.refs ⧺ refs')` by
          fs [REFS_PRED_FRAME_append]
    \\ drule REFS_PRED_FRAME_imp
    \\ disch_then drule \\ strip_tac
    \\ first_x_assum drule
    \\ strip_tac
    \\ imp_res_tac evaluate_empty_state_IMP
    \\ fs [eval_rel_def]
    \\ drule evaluate_set_clock \\ fs []
    \\ disch_then (qspec_then `ck` strip_assume_tac)
    \\ rename [`evaluate (s with clock := ck5)`]
    \\ fs [evaluate_def]
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs []
    \\ qexists_tac `s2`
    \\ qexists_tac `ck5` \\ fs []
    \\ imp_res_tac REFS_PRED_FRAME_trans
    \\ fs [Mat_cases_def]
    \\ fs [evaluate_def,pmatch_def,pat_bindings_def]
    \\ drule pmatch_list_MAP_Pvar
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
    \\ fs [GSYM write_list_thm])
  \\ fs [Eval_def,EXISTS_MEM,EXISTS_PROD,EvalM_def]
  \\ rpt strip_tac
  \\ last_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ first_x_assum drule \\ strip_tac
  \\ `REFS_PRED_FRAME ro H (st,s) (st,s with refs := s.refs ⧺ refs')` by
        fs [REFS_PRED_FRAME_append]
  \\ drule REFS_PRED_FRAME_imp
  \\ disch_then drule \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ imp_res_tac evaluate_empty_state_IMP
  \\ fs [eval_rel_def]
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ rename [`evaluate (s with clock := ck5)`]
  \\ fs [evaluate_def]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ qexists_tac `s2`
  \\ qexists_tac `ck5` \\ fs []
  \\ conj_tac THEN1 (imp_res_tac REFS_PRED_FRAME_trans)
  \\ fs [Mat_cases_def]
  \\ drule (evaluate_match_MAP |> GEN_ALL)
  \\ qpat_x_assum `MEM _ y` (assume_tac o REWRITE_RULE [MEM_SPLIT])
  \\ fs [] \\ fs [ALL_DISTINCT_APPEND]
  \\ `set l1 ⊆ set l1 ∪ {(name,vars,exp',t)} ∪ set l2` by fs [SUBSET_DEF,IN_UNION]
  \\ disch_then drule \\ fs []
  \\ disch_then drule \\ fs []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ disch_then (fn th => rewrite_tac [th]) \\ fs []
  \\ fs [evaluate_def,pmatch_def,pat_bindings_def]
  \\ fs [good_cons_env_def,lookup_cons_def]
  \\ `same_type t t /\ same_ctor t t` by (Cases_on `t` \\ EVAL_TAC) \\ fs []
  \\ drule pmatch_list_MAP_Pvar
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ fs [GSYM write_list_thm]
QED

(*
 * Run
 *)
val EvalSt_def = Define `
  EvalSt env st exp P H =
    !(s: unit semanticPrimitives$state). REFS_PRED H st s ==>
    ?s2 res st2 ck.
      evaluate (s with clock := ck) env [exp] = (s2, Rval [res]) /\
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
  \\ pop_assum(fn x => ALL_TAC)
  \\ sg `!n. n < LENGTH s.refs ==> (Mem n (EL n s.refs)) IN st2heap p (s with refs := refs')`
  >-(
      rw[]
      \\ imp_res_tac LENGTH_Mem_IN_store2heap
      \\ fs[STAR_def]
      \\ fs[SPLIT_def]
      \\ last_x_assum(fn x => ASSUME_TAC (ONCE_REWRITE_RULE[EQ_SYM_EQ] x))
      \\ rw[])
  \\ sg `!n. n < LENGTH s.refs ==> EL n s.refs = EL n refs'`
  >-(
      rw[]
      \\ first_x_assum(qspec_then `n` imp_res_tac)
      \\ fs[st2heap_def, Mem_NOT_IN_ffi2heap]
      \\ imp_res_tac store2heap_IN_EL
      \\ fs[])
  \\ Cases_on `s.refs`
  >-(fs[])
  \\ sg `LENGTH (h::t) <= LENGTH refs'`
  >-(
      last_x_assum(qspec_then `LENGTH s.refs - 1` ASSUME_TAC)
      \\ `LENGTH s.refs - 1 < LENGTH (h::t)` by rw[]
      \\ fs[st2heap_def, Mem_NOT_IN_ffi2heap]
      \\ imp_res_tac store2heap_IN_LENGTH
      \\ `LENGTH s.refs - 1 = LENGTH t` by rw[]
      \\ fs[])
  \\ imp_res_tac (SPEC_ALL IS_PREFIX_THM |> EQ_IMP_RULE |> snd)
  \\ imp_res_tac IS_PREFIX_APPEND
  \\ rw[]);

Theorem EvalSt_to_Eval:
   EvalSt env st exp P ((\s. emp),p) ==> Eval env exp P
Proof
  rw[EvalSt_def, Eval_def]
  \\ fs[REFS_PRED_def, SEP_CLAUSES, SAT_GC]
  \\ first_x_assum(qspecl_then [`empty_state with refs := refs`]
        STRIP_ASSUME_TAC)
  \\ fs[state_component_equality]
  \\ fs[REFS_PRED_FRAME_def, SEP_CLAUSES, eval_rel_def]
  \\ rw[PULL_EXISTS]
  \\ ASSUME_TAC (ISPEC ``empty_state with refs := refs``
       REFS_PRED_FRAME_partial_frame_rule)
  \\ fs(TypeBase.updates_of ``:'a state``)
  \\ first_x_assum drule \\ rw[]
  \\ qexists_tac `res` \\ fs []
  \\ qexists_tac `junk` \\ fs []
  \\ qexists_tac `ck` \\ fs []
  \\ fs[state_component_equality]
QED

val handle_mult_def = Define `
  handle_mult [] exp1 ename = exp1 /\
  handle_mult (_:string list) exp1 ename =
    Handle exp1 [(Pvar "e",(Con (SOME (Short ename)) [Var (Short "e")]))]`;

val evaluate_handle_mult_Rval = Q.prove(
  `!cons_names exp1 ename res s s2 env.
     evaluate s env [exp1] = (s2, Rval res) ==>
     evaluate s env [handle_mult cons_names exp1 ename] = (s2, Rval res)`,
  Cases
  \\ rw[handle_mult_def]
  \\ rw[evaluate_def]);

val evaluate_handle_mult_Rabort = Q.prove(
  `!cons_names exp1 ename res s s2 env.
     evaluate s env [exp1] = (s2, Rerr (Rabort res)) ==>
     evaluate s env [handle_mult cons_names exp1 ename] =
       (s2, Rerr (Rabort res))`,
  Cases
  \\ rw[handle_mult_def]
  \\ rw[evaluate_def]);

val EVERY_CONJ_1 = GSYM EVERY_CONJ |> SPEC_ALL |> EQ_IMP_RULE
                     |> fst |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO];

(* EvalM_to_EvalSt *)

val handle_all_def = Define `
  handle_all exp ename =
    Handle exp [(Pvar "e",(Con (SOME (Short ename)) [Var (Short "e")]))]`;

val evaluate_handle_all_Rval = Q.prove(
  `!exp1 ename res s s2 env.
     evaluate s env [exp1] = (s2, Rval res) ==>
     evaluate s env [handle_all exp1 ename] = (s2, Rval res)`,
  Cases
  \\ rw[handle_all_def]
  \\ rw[evaluate_def]);

val evaluate_handle_all_Rabort = Q.prove(
  `!exp1 ename res s s2 env.
     evaluate s env [exp1] = (s2, Rerr (Rabort res)) ==>
     evaluate s env [handle_all exp1 ename] = (s2, Rerr (Rabort res))`,
  Cases
  \\ rw[handle_all_def]
  \\ rw[evaluate_def]);

val evaluate_Success_CONS = Q.prove(
  `evaluate s env [e] = (s', Rval [v]) ==>
  lookup_cons (Short "Success") env = SOME (1,TypeStamp "Success" exc_stamp) ==>
  evaluate s env [Con (SOME (Short "Success")) [e]] = (s', Rval [Conv (SOME (TypeStamp "Success" exc_stamp)) [v]])`,
  rw[]
  \\ rw[evaluate_def]
  \\ fs[lookup_cons_def]
  \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
  \\ fs[namespaceTheory.id_to_n_def]
  \\ rw[evaluate_def]
  \\ every_case_tac \\ fs []);

val evaluate_Success_CONS_err = Q.prove(
  `evaluate s env [e] = (s', Rerr v) ==>
  lookup_cons (Short "Success") env = SOME (1,TypeStamp "Success" exc_stamp) ==>
  evaluate s env [Con (SOME (Short "Success")) [e]] = (s', Rerr v)`,
  rw[]
  \\ rw[evaluate_def]
  \\ fs[lookup_cons_def]
  \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
  \\ fs[namespaceTheory.id_to_n_def]
  \\ every_case_tac \\ fs []);

(* For the dynamic store initialisation *)
(* It is not possible to use register_type here... *)
val EXC_TYPE_aux_def = Define `
       (EXC_TYPE_aux stamp a b (Failure x_2) v ⇔
        ∃v2_1. v = Conv (SOME (TypeStamp "Failure" stamp)) [v2_1]
                        ∧ b x_2 v2_1) ∧
       (EXC_TYPE_aux stamp a b (Success x_1) v ⇔
        ∃v1_1. v = Conv (SOME (TypeStamp "Success" stamp)) [v1_1]
                        ∧ a x_1 v1_1)`;

Theorem EvalM_to_EvalSt:
    ∀exc_stamp TYPE EXN_TYPE x exp H init_state env.
   EvalM T env init_state exp (MONAD TYPE EXN_TYPE x) H ⇒
   lookup_cons (Short "Success") env = SOME (1, TypeStamp "Success" exc_stamp) ⇒
   lookup_cons (Short "Failure") env = SOME (1, TypeStamp "Failure" exc_stamp) ⇒
   EvalSt env init_state
     (handle_all (Con (SOME (Short "Success")) [exp]) "Failure")
     (EXC_TYPE_aux exc_stamp TYPE EXN_TYPE (run x init_state)) H
Proof
  rw[EvalM_def, EvalSt_def]
  \\ first_x_assum drule \\ rw[]
  \\ Cases_on `res`
  (* res is an Rval *)
  >-(
      imp_res_tac evaluate_sing \\ rveq \\ fs []
      \\ IMP_RES_TAC evaluate_Success_CONS
      \\ first_x_assum (fn x => MATCH_MP evaluate_handle_all_Rval x |> ASSUME_TAC)
      \\ first_x_assum (qspec_then `"Failure"` ASSUME_TAC)
      \\ asm_exists_tac \\ fs []
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
  \\ qexists_tac `s2`
  \\ qexists_tac `Conv (SOME (TypeStamp "Failure" exc_stamp)) [a]`
  \\ qexists_tac `r`
  \\ qexists_tac `ck`
  \\ rw[handle_all_def]
  \\ rw[evaluate_def]
  \\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def,
          write_def,lookup_cons_def,PULL_EXISTS,pat_bindings_def,pmatch_def]
  \\ every_case_tac \\ fs []
  \\ rw[EXC_TYPE_aux_def, run_def]
QED

Theorem EvalSt_Let_Fun:
   EvalSt (write vname (Closure env xv fexp) env) st exp P H ==>
   EvalSt env st (Let (SOME vname) (Fun xv fexp) exp) P H
Proof
  rw[EvalSt_def]
  \\ last_x_assum imp_res_tac
  \\ rw[evaluate_def]
  \\ rw[namespaceTheory.nsOptBind_def]
  \\ fs[write_def, merge_env_def]
  \\ metis_tac[]
QED

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

Theorem EvalSt_Letrec_Fun:
   !funs env exp st P H.
  (ALL_DISTINCT (MAP (\(x,y,z). x) funs)) ==>
  EvalSt <|v := (build_rec_env funs env env.v); c := env.c|> st exp P H ==>
  EvalSt env st (Letrec funs exp) P H
Proof
  rw[EvalSt_def]
  \\ qpat_x_assum `!s. A` imp_res_tac
  \\ rw[evaluate_def]
  \\ `<|v := build_rec_env funs env env.v; c := env.c|> =
      env with v := build_rec_env funs env env.v` by fs[sem_env_component_equality]
  \\ fs[]
  \\ metis_tac[]
QED

Theorem merge_env_bind_empty:
   merge_env <| v := Bind [] []; c := Bind [] [] |> env  = env
Proof
  rw[merge_env_def]
  \\ Cases_on `env`
  \\ Cases_on `n`
  \\ Cases_on `n0`
  \\ rw[namespaceTheory.nsAppend_def, sem_env_component_equality]
QED

Theorem Bind_list_to_write:
   merge_env <|v := Bind ((vname, v)::binds) []; c := Bind [] []|> env =
  write vname v (merge_env <|v := Bind binds []; c := Bind [] []|> env)
Proof
  rw[merge_env_def, write_def]
  \\ Cases_on `env`
  \\ rw[]
  \\ Cases_on `n`
  \\ rw[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def]
QED

val evaluate_Var_IMP = Q.prove(
 `evaluate s1 env [Var (Short name)] = (s2, Rval [v]) ==>
  nsLookup env.v (Short name) = SOME v`,
  rw[evaluate_def] \\ every_case_tac \\ fs []);

val evaluate_Var_same_state = Q.prove(
 `evaluate s1 env [Var (Short name)] = (s2, res) <=>
  evaluate s1 env [Var (Short name)] = (s2, res) /\ s2 = s1`,
  EQ_TAC \\ rw[evaluate_def] \\ every_case_tac \\ fs []);

Theorem EvalSt_Opref:
   !exp get_ref_exp get_ref loc_name TYPE st_name env H P st.
    Eval env get_ref_exp (TYPE (get_ref st)) ==>
    (!loc. EvalSt (write loc_name loc env) st exp P
      ((\st. REF_REL TYPE loc (get_ref st) * H st),p)) ==>
    EvalSt env st
      (Let (SOME loc_name) (App Opref [get_ref_exp]) exp) P (H,p)
Proof
  rw[EvalSt_def]
  \\ rw[evaluate_def]
  \\ fs[Eval_def]
  \\ fs[PULL_EXISTS]
  \\ last_x_assum (qspec_then `s.refs` strip_assume_tac)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> ASSUME_TAC)
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x1 x2 x3. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ fs [eval_rel_def]
  \\ drule evaluate_set_clock
  \\ pop_assum kall_tac
  \\ disch_then (qspec_then `s.clock` strip_assume_tac) \\ fs []
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ rw[state_component_equality,with_same_ffi]
  \\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ refs'))`, `s with refs := s.refs ++ refs' ++ [Refv res]`] ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      pop_assum (fn x => ALL_TAC)
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
  \\ qpat_x_assum `evaluate _ env [get_ref_exp] = _` assume_tac
  \\ drule evaluate_set_clock \\ fs []
  \\ disch_then (qspec_then `ck` strip_assume_tac)
  \\ qexists_tac `ck1` \\ fs [with_same_ffi]
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
  \\ qpat_x_assum `A ==> R` imp_res_tac
  \\ fs[GSYM STAR_ASSOC, GC_STAR_GC]
  \\ first_x_assum(fn x => PURE_ONCE_REWRITE_RULE[STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
  \\ fs[]
QED

val EQ_def = Define `EQ x y <=> x = y`;

Theorem EvalSt_AllocEmpty:
   !exp get_ref loc_name TYPE st_name env H P st.
     EQ (get_ref st) [] ==>
     (!loc.
       EvalSt (write loc_name loc env) st exp P
         ((\st. RARRAY_REL TYPE loc (get_ref st) * H st),p)) ==>
     EvalSt env st
       (Let (SOME loc_name) (App Opref [App AallocEmpty [Con NONE []]]) exp)
         P (H,p)
Proof
  rw[EvalSt_def,evaluate_def]
  \\ fs[PULL_EXISTS]
  \\ fs[do_con_check_def, build_conv_def]
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ simp[with_same_ffi]
  \\ last_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ [Varray []]))`, `s with refs := s.refs ++ [Varray []; Refv (Loc (LENGTH s.refs))]`] ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      pop_assum (fn x => ALL_TAC)
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
  \\ fs[merge_env_def, write_def]
  \\ ho_match_mp_tac (METIS_PROVE []
       ``(?x4 x1 x2 x3. P x1 x2 x3 x4) ==> (?x1 x2 x3 x4. P x1 x2 x3 x4)``)
  \\ qexists_tac `ck` \\ fs []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ fs []
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
  \\ fs[]
QED

Theorem EvalSt_Alloc:
   !exp nexp n xexp x get_farray loc_name TYPE env H P st.
     EQ (get_farray st) (REPLICATE n x) ==>
     Eval env nexp (\v. v = Litv (IntLit (&n))) ==>
     Eval env xexp (TYPE x) ==>
     (!loc.
        EvalSt (write loc_name loc env) st exp P
          ((\st. ARRAY_REL TYPE loc (get_farray st) * H st),p)) ==>
     EvalSt env st (Let (SOME loc_name) (App Aalloc [nexp; xexp]) exp) P (H,p)
Proof
  rw[EvalSt_def,evaluate_def]
  \\ fs[PULL_EXISTS]
  \\ fs[Eval_def]
  \\ first_x_assum(qspec_then `s.refs` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP x |> STRIP_ASSUME_TAC)
  \\ rw[evaluate_def]
  \\ first_x_assum(qspec_then `s.refs ++ refs'` STRIP_ASSUME_TAC)
  \\ first_x_assum(fn x => MATCH_MP evaluate_empty_state_IMP_2 x |> STRIP_ASSUME_TAC)
  \\ rw[do_app_def,store_alloc_def,namespaceTheory.nsOptBind_def]
  \\ fs[with_same_ffi]
  \\ first_x_assum(qspecl_then [`Loc (LENGTH (s.refs ++ refs' ++ refs''))`, `s with refs := s.refs ++ refs' ++ refs'' ++ [Varray (REPLICATE n res)]`] STRIP_ASSUME_TAC)
  \\ fs[]
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      pop_assum (fn x => ALL_TAC)
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
  \\ fs[eval_rel_def]
  \\ qpat_x_assum`evaluate _ _ [nexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`ck`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k2`strip_assume_tac)
  \\ qpat_x_assum`evaluate _ _ [xexp] = _`assume_tac
  \\ drule evaluate_set_clock
  \\ disch_then(qspec_then`k2`mp_tac)
  \\ impl_tac >- rw[]
  \\ disch_then(qx_choose_then`k1`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ck"]))
  \\ qexists_tac`k1` \\ fs[with_same_ffi]
  \\ fs[REFS_PRED_FRAME_def]
  \\ qexists_tac `st2` \\ rw []
  >-(rw[state_component_equality])
  \\ first_x_assum(qspec_then `F' * GC` STRIP_ASSUME_TAC)
  \\ first_assum(fn x => let val a = concl x |> dest_imp |> fst in sg `^a` end)
  >-(
      pop_assum (fn x => ALL_TAC)
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
  \\ pop_assum(fn x => ALL_TAC)
  \\ first_x_assum(fn x => REWRITE_RULE[Once STAR_COMM] x |> ASSUME_TAC)
  \\ fs[STAR_ASSOC]
  \\ first_x_assum(fn x => MATCH_MP GC_ABSORB_R x |> ASSUME_TAC)
  \\ fs[]
QED

Theorem Eval_lookup_var:
   !env vname xv x TYPE. nsLookup env.v (Short vname) = SOME xv ==>
  (Eval env (Var (Short vname)) (TYPE x) <=> TYPE x xv)
Proof
  rw[Eval_def,eval_rel_def,evaluate_def,state_component_equality]
QED

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

Theorem H_STAR_emp:
   H * emp = H
Proof
simp[SEP_CLAUSES]
QED

Theorem H_STAR_TRUE:
   (H * &T = H) /\ (&T * H = H)
Proof
fs[SEP_CLAUSES]
QED

Theorem PreImp_PRECONDITION_T_SIMP:
   PreImp T a /\ PRECONDITION T <=> a
Proof
  fs[PreImp_def, PRECONDITION_def]
QED

Theorem IF_T:
  (if T then x else y) = x:'a
Proof
SIMP_TAC std_ss []
QED

Theorem IF_F:
  (if F then x else y) = y:'a
Proof
SIMP_TAC std_ss []
QED

Theorem IMP_EQ_T:
  a ==> (a <=> T)
Proof
fs []
QED

Theorem BETA_PAIR_THM:
  (\(x, y). f x y) (x, y) = (\x y. f x y) x y
Proof
fs[]
QED

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
