(*
  Proof of correctness of a really simple array-init program.
*)

open preamble HolKernel Parse boolLib bossLib stringLib numLib intLib
     panLangTheory panPtreeConversionTheory panSemTheory;
open panHoareTheory;

val _ = new_theory "initArray";

(* copied from panConcreteExampleScript *)

fun read_file fname = let
    val s = TextIO.openIn fname
    fun get ss = case TextIO.inputLine s of
        SOME str => get (str :: ss)
      | NONE => rev ss
  in concat (get []) end

fun parse_pancake_file fname =
  let
    val str = stringLib.fromMLstring (read_file fname)
    val thm = EVAL ``parse_funs_to_ast ^str``
    val r = rhs (concl thm)
  in
    if sumSyntax.is_inl r
    then (fst (sumSyntax.dest_inl r), thm)
    else failwith ("parse_pancake_file: failed to EVAL")
  end

val fname = "../examples/init_array.pnk"

val (ast, _) = parse_pancake_file "../examples/init_array.pnk"

Definition the_code_def:
  the_code = FEMPTY |++ (MAP (I ## SND) (^ast))
End

Theorem lookup_init_array = EVAL ``FLOOKUP (the_code) «init_array»``

val init_array_loop =
  lookup_init_array |> concl |> find_term (can (match_term ``Seq (While _ _) _``))

Definition w_count_def:
  w_count i x = (if ~ (i < x) then []
    else GENLIST (\j. i + n2w j) (w2n (x - i)))
End

Theorem w_count_cons:
  i < x ==> w_count i x = i :: w_count (i + 1w) x
Proof
  simp [w_count_def]
  \\ disch_tac
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED]
  \\ simp [listTheory.GENLIST_CONS, wordsTheory.WORD_LEFT_ADD_DISTRIB]
  \\ simp [combinTheory.o_DEF, wordsTheory.n2w_SUC]
  \\ rw []
  >- (
    strip_tac
    \\ full_simp_tac bool_ss [wordsTheory.WORD_SUB_INTRO]
    \\ fs [wordsTheory.WORD_EQ_SUB_ZERO]
  )
  >- (
    (* requires some rules about inequalities and 1w *)
    cheat
  )
QED

Definition while_then_def:
  while_then C B X = Seq (While C B) X
End

Definition clock_after_def:
  clock_after s1 s2 = (s2.clock < s1.clock)
End

Theorem evaluate_while_then_imp:
  evaluate (while_then C B X, st1) = (res, st2) ==>
  (? res1 step_st. evaluate (If C (Seq Tick B) Break, st1) = (res1, step_st) /\
    (case res1 of
        | NONE => (evaluate (while_then C B X, step_st) = (res, st2) /\
            clock_after st1 step_st)
        | SOME Continue => (evaluate (while_then C B X, step_st) = (res, st2) /\
            clock_after st1 step_st)
        | SOME Break => evaluate (X, step_st) = (res, st2)
        | _ => (res1, step_st) = (res, st2)
    ))
Proof
  simp [evaluate_def]
  \\ simp [while_then_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [GSYM while_then_def]
  \\ pairarg_tac \\ fs []
  \\ fs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
  \\ fs [CaseEq "bool"]
  \\ simp [evaluate_def]
  \\ pairarg_tac \\ fs []
  \\ rename [`evaluate (_, dec_clock _) = (_, step_st)`]
  \\ reverse (qsuff_tac `clock_after st1 step_st`)
  >- (
    imp_res_tac evaluate_clock
    \\ fs [clock_after_def, dec_clock_def]
  )
  \\ fs [CaseEq "option", CaseEq "result"] \\ rw []
  \\ simp [while_then_def, EVAL ``evaluate (panLang$Seq _ _, _)``]
QED

Theorem clock_after_induct:
  (! s. (! step_st. clock_after s step_st ==> P step_st) ==> P s) ==>
  ! s. P s
Proof
  rw []
  \\ measureInduct_on `s.clock`
  \\ fs [clock_after_def]
QED

Theorem neq_NONE_IMP:
  (x <> NONE) ==> (?y. x = SOME y)
Proof
  Cases_on `x` \\ fs []
QED

Triviality init_array_loop_correct:
  ! st1 res st2. panSem$evaluate (^init_array_loop, st1) = (res, st2) ==>
  local_word st1.locals «i» <> NONE /\
  local_word st1.locals «base_addr» <> NONE /\
  local_word st1.locals «len» <> NONE /\
  set (MAP (\i. (THE (local_word st1.locals «base_addr») + (i * 8w)))
        (w_count (THE (local_word st1.locals «i»)) (THE (local_word st1.locals «len»))))
    SUBSET st1.memaddrs
  ==>
  res <> NONE /\
  (res <> SOME TimeOut ==> (case res of SOME (Return (ValWord i)) => i = 0w | _ => F) /\
  (?n. st2 =
    let i = THE (local_word st1.locals «i»);
        addr = THE (local_word st1.locals «base_addr»);
        len = THE (local_word st1.locals «len»);
        m2 = st1.memory =++ (MAP (\i. (addr + (i * 8w), Word i))
          (w_count i len))
    in (empty_locals st1 with <| memory := m2; clock := st1.clock - n |>)
  ))
Proof
  ho_match_mp_tac clock_after_induct
  \\ simp [GSYM while_then_def]
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ dxrule evaluate_while_then_imp
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ fs [evaluate_def, eval_def]
  \\ gs [GSYM optionTheory.IS_SOME_EQ_NOT_NONE |> REWRITE_RULE [optionTheory.IS_SOME_EXISTS],
    val_word_of_eq_SOME]
  \\ rename [`word_cmp Less i_v len_v`]
  \\ reverse (Cases_on `word_cmp Less i_v len_v`) \\ fs []
  >- (
    gvs [evaluate_def]
    \\ fs [shape_of_def, size_of_shape_def]
    \\ fs [asmTheory.word_cmp_def, w_count_def, miscTheory.UPDATE_LIST_THM]
    \\ simp [panSemTheory.state_component_equality]
    \\ qexists_tac `0`
    \\ gvs [empty_locals_def]
  )
  >- (
    gvs [evaluate_def, eval_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [CaseEq "bool" |> Q.GEN `x` |> Q.ISPEC `cl = 0n`] \\ gvs []
    \\ gs [dec_clock_def]
    \\ fs [pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def]
    \\ fs [asmTheory.word_cmp_def]
    \\ drule_then assume_tac w_count_cons
    \\ gvs [is_valid_value_def, shape_of_def]
    \\ first_x_assum (drule_then drule)
    \\ simp [finite_mapTheory.FLOOKUP_UPDATE]
    \\ simp [empty_locals_def, miscTheory.UPDATE_LIST_THM]
    \\ rw [] \\ fs []
    \\ irule_at Any EQ_REFL
  )
QED

Theorem init_array_correct:
  st1.code = the_code ==>
  panSem$evaluate (Call NONE (Label «init_array») [Const base; Const len], st1) = (res, st2) /\
  (set (MAP (\i. base + (8w * i)) (w_count 0w len)) SUBSET st1.memaddrs) ==>
  res <> NONE /\
  (res <> SOME TimeOut ==> (case res of SOME (Return (ValWord i)) => i = 0w | _ => F) /\
  ?n. st2 = ((empty_locals st1) with <|
    memory := st1.memory =++ (MAP (\i. (base + (i * 8w), Word i)) (w_count 0w len));
    clock := st1.clock - n |>))
Proof
  simp [evaluate_def, eval_def, lookup_code_def,
        REWRITE_RULE [GSYM while_then_def] lookup_init_array]
  \\ simp [shape_of_def]
  \\ rpt disch_tac
  \\ fs [CaseEq "bool"]
  \\ fs [evaluate_def, eval_def]
  \\ pairarg_tac \\ fs []
  \\ dxrule (REWRITE_RULE [GSYM while_then_def] init_array_loop_correct)
  \\ simp [FLOOKUP_FUPDATE_LIST, FLOOKUP_UPDATE, dec_clock_def]
  \\ gvs [CaseEq "option", CaseEq "result"]
  \\ simp [empty_locals_def]
  \\ rw []
  \\ simp [panSemTheory.state_component_equality]
  \\ irule_at Any EQ_REFL
QED

val hoare_simp_rules =
    [DROP_DROP_T, FLOOKUP_UPDATE, res_var_def, FLOOKUP_FUPDATE_LIST,
        shape_of_def, size_of_shape_def, empty_locals_def, dec_clock_def,
        Cong option_case_cong, Cong panSemTheory.result_case_cong,
        PULL_EXISTS, eval_def, panPropsTheory.exp_shape_def]

val rev_hoare_simp = let
    val rev_hoare_v = ``rev_hoare``
    fun conv t = let
        val (f, _) = strip_comb t
      in (if same_const rev_hoare_v f
        then RAND_CONV (SIMP_CONV (srw_ss ()) hoare_simp_rules)
        else if is_abs f
        then (BETA_CONV THENC conv)
        else if boolSyntax.is_conj t
        then BINOP_CONV conv
        else ALL_CONV) t
      end
  in CONV_TAC conv end

val rev_hoare_tac = MAP_FIRST match_mp_tac
        (CONJUNCTS hoare_logic_rev_rules @ [eval_logic_rev])
    \\ rev_hoare_simp

Theorem bool_case_eq_specs =
    CONJ (bool_case_eq |> Q.GEN `t` |> Q.SPEC `v`)
        (bool_case_eq |> Q.GEN `f` |> Q.SPEC `v`)


Theorem init_array_Hoare_correct:
  hoare_logic G
    (\s ls.
        the_code ⊑ s.code /\
        local_word s.locals «base_addr» <> NONE /\
        local_word s.locals «len» <> NONE /\
        let base = THE (local_word s.locals «base_addr») in
        let len = THE (local_word s.locals «len») in
        set (MAP (\i. (base + (i * 8w))) (w_count 0w len)) SUBSET s.memaddrs /\
        (!m. Q (SOME TimeOut) m s.ffi) /\
        (!n. Q (SOME (Return (ValWord 0w)))
            (s.memory =++ (MAP (\i. (base + (i * 8w), Word i)) (w_count 0w len))) s.ffi)
    )
    (TailCall (Label «init_array») [Var «base_addr»; Var «len»])
    (\res s ls. Q res s.memory s.ffi)
Proof
  irule hoare_logic_rev_init
  \\ qspec_then `the_code` irule hoare_logic_TailCall_rev_code
  \\ simp [lookup_init_array]
  \\ qspec_then `\s ls.
    local_word s.locals «i» <> NONE /\
    local_word s.locals «base_addr» <> NONE /\
    local_word s.locals «len» <> NONE /\
    let i = THE (local_word s.locals «i»);
        addr = THE (local_word s.locals «base_addr»);
        len = THE (local_word s.locals «len»);
        m2 = s.memory =++ (MAP (\i. (addr + (i * 8w), Word i))
          (w_count i len))
    in
    set (MAP (\i. (addr + (i * 8w))) (w_count i len)) SUBSET s.memaddrs /\
    (Q (SOME (Return (ValWord 0w))) m2 s.ffi) /\ (!m. Q (SOME TimeOut) m s.ffi)`
    (REWRITE_TAC o single) (GSYM annot_While_def)
  \\ rpt rev_hoare_tac
  \\ conj_tac
  >- (
    rw ([logic_imp_def] @ hoare_simp_rules)
    \\ imp_res_tac neq_NONE_IMP \\ gs []
    \\ imp_res_tac neq_NONE_IMP \\ gs [val_word_of_eq_SOME]
    \\ simp [pan_op_def, wordLangTheory.word_op_def, flatten_def,
        asmTheory.word_cmp_def, bool_case_eq_specs]
    \\ gvs []
    \\ rw []
    >- (
      fs [w_count_def, miscTheory.UPDATE_LIST_THM]
    )
    \\ fs [w_count_cons, mem_stores_def, mem_store_def, miscTheory.UPDATE_LIST_THM]
    \\ simp [shape_of_def]
  )
  \\ rpt rev_hoare_tac
  \\ rw ([logic_imp_def] @ hoare_simp_rules)
  \\ imp_res_tac neq_NONE_IMP \\ gs []
  \\ imp_res_tac neq_NONE_IMP \\ gs [val_word_of_eq_SOME]
  \\ simp [shape_of_def]
QED

val _ = export_theory ();
