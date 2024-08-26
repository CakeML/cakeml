(*
  A program logic for pancake in the Hoare/Floyd style.
*)

open preamble panLangTheory panPropsTheory panSemTheory;
local open alignmentTheory
           miscTheory
           wordLangTheory
           ffiTheory in end;

val _ = new_theory "panHoare";
val _ = set_grammar_ancestry [
  "panLang", "panSem", "ffi" ]


Type trip[local] = ``: (('a, 'ffi) state -> bool) # 'a prog #
        ('a result -> ('a, 'ffi) state -> bool)``

Datatype:
  hoare_context = <|
      ffi_rely          :    io_event list ->
                             (ffiname # word8 list # word8 list) ->
                             ('ffi oracle_result) -> bool
    ; ffi_guarantee     :    io_event list ->
                             (ffiname # word8 list # word8 list) -> bool
    ; termination       :    bool
    ; triples           :    (('a, 'ffi) trip) list
    ; future_triples    :    (('a, 'ffi) trip) list
  |>
End

Definition val_word_of_def[simp]:
  val_word_of (Val (Word w)) = SOME w /\
  val_word_of _ = NONE
End

Theorem val_word_of_eq_SOME:
  !v. (val_word_of v = SOME w) <=> (v = ValWord w)
Proof
  ho_match_mp_tac val_word_of_ind \\ simp [val_word_of_def]
QED

Theorem val_word_of_neq_NONE:
  !v. val_word_of v <> NONE ==> (?w. v = ValWord w)
Proof
  ho_match_mp_tac val_word_of_ind \\ simp [val_word_of_def]
QED

Overload local_word = ``\locs nm. OPTION_BIND (FLOOKUP locs nm) val_word_of``

Definition tick_context_def:
  tick_context context = if NULL context.future_triples then context
    else (context with <| triples := context.future_triples ++ context.triples;
        future_triples := [] |>)
End

(* should this be presented syntactically via Inductive? *)
Definition eval_logic_def:
  eval_logic G P exp v Q = (!s. P s ==> ?x. eval s exp = SOME x /\
    Q (s with locals := (s.locals |+ (v, x))))
End

Theorem eval_logic_elim = hd (RES_CANON eval_logic_def)

Definition opt_op_precond_def:
  opt_op_precond P f Q = (!s. P s ==> ?x. f s = SOME x /\ Q x s)
End

Theorem opt_op_precond_elim = hd (RES_CANON opt_op_precond_def)

Definition res_any_def:
  res_any nm P s = (!prev. P (s with locals := res_var s.locals (nm, prev)))
End

Theorem res_any_drop_update:
  res_any nm P (s with locals := (locs |+ (nm, v))) = res_any nm P (s with locals := locs)
Proof
  simp [res_any_def]
  \\ AP_TERM_TAC
  \\ simp [FUN_EQ_THM]
  \\ Cases
  \\ simp [res_var_def]
QED

Theorem res_any_same:
  (res_any nm P (s with locals := s.locals) ==> P s) /\
  (res_any nm P s ==> P s)
Proof
  qsuff_tac `(s with locals := res_var s.locals (nm, FLOOKUP s.locals nm)) = s`
  >- (
    simp [res_any_def] \\ metis_tac []
  )
  \\ simp [panSemTheory.state_component_equality]
  \\ Cases_on `FLOOKUP s.locals nm`
  \\ simp [res_var_def, DOMSUB_NOT_IN_DOM, FUPDATE_ELIM, TO_FLOOKUP]
QED

Inductive hoare_logic:

[hoare_logic_weaken_pre:]
  (! P Q R.
    (!s. P s ==> Q s) /\
    hoare_logic G Q p R ==>
    hoare_logic G P p R
  )

[hoare_logic_strengthen_post:]
  (! P Q R.
    (!res s. Q res s /\ res <> SOME Error ==> R res s) /\
    hoare_logic G P p Q ==>
    hoare_logic G P p R
  )


[hoare_logic_equiv:]
  (! P Q R.
    (!s r s1. P s /\ evaluate (p, s) = (r, s1) ==>
        ?s2. evaluate (p2, s) = (r, s2) /\
        (r <> SOME Error ==> s2.ffi = s1.ffi /\ (R r s2 ==> R r s1))) /\
    hoare_logic G Q p2 R ==>
    hoare_logic G (\s. P s /\ Q s) p R
  )

[hoare_logic_Skip:]
  ( !P.
    hoare_logic G (P NONE) Skip P
  )

[hoare_logic_Break:]
  ( !P.
    hoare_logic G (P (SOME Break)) Break P
  )

[hoare_logic_Continue:]
  ( !P.
    hoare_logic G (P (SOME Continue)) Continue P
  )

[hoare_logic_Dec:]
  (
    ! P Q R.
    eval_logic G P e v Q /\
    hoare_logic G Q p (\res s. res_any v (R res) s)
    ==>
    hoare_logic G P (Dec v e p) R
  )

[hoare_logic_Assign:]
  ( ! P Q.
    eval_logic G P e v (Q NONE) ==>
    hoare_logic G (\s. P s /\
            OPTION_MAP shape_of (FLOOKUP s.locals v) =
            SOME (panProps$exp_shape (FMAP_MAP2 (shape_of o SND) s.locals) e))
        (Assign v e) Q
  )

[hoare_logic_Seq:]
  (
    ! P Q R.
    hoare_logic G P p1 (\r s. if r = NONE then Q s else R r s) /\
    hoare_logic G Q p2 R ==>
    hoare_logic G P (Seq p1 p2) R
  )

[hoare_logic_If:]
  (
    ! P Q1 Q2 R.
    eval_logic G P cond_exp cond_nm (\s. local_word s.locals cond_nm <> NONE /\
        if local_word s.locals cond_nm <> SOME 0w
        then res_any cond_nm Q1 s else res_any cond_nm Q2 s) /\
    hoare_logic G Q1 p1 R /\
    hoare_logic G Q2 p2 R ==>
    hoare_logic G (\s. FLOOKUP s.locals cond_nm = NONE /\ P s) (If cond_exp p1 p2) R
  )

[hoare_logic_While:]
  (
    ! Q.
    eval_logic G P e cond_nm (\s. local_word s.locals cond_nm <> NONE /\
        res_any cond_nm (if local_word s.locals cond_nm = SOME 0w
          then R NONE else if s.clock = 0 then (R (SOME TimeOut) o empty_locals)
          else (Q o dec_clock)) s) /\
    hoare_logic G Q p (\r s. case r of NONE => P s | SOME Break => R NONE s
            | SOME Continue => P s | _ => R r s) ==>
    hoare_logic G P (While e p) R
  )

[hoare_logic_TailCall:]
  ( !vshs prog Q.
    ALL_DISTINCT (MAP FST vshs) /\
    hoare_logic G Q prog (\res s. case res of
            | SOME (Return r) => R res (empty_locals s)
            | SOME (FinalFFI fres) => R res (empty_locals s)
            | SOME (Exception eid exn) => R res (empty_locals s)
            | _ => F)
    ==>
    hoare_logic G (\s. FLOOKUP s.code nm = SOME (vshs, prog) /\
        (case OPT_MMAP (FLOOKUP s.locals) var_nms of
            NONE => F
          | SOME vs => MAP shape_of vs = MAP SND vshs /\
                (if s.clock = 0 then R (SOME TimeOut) (empty_locals s)
                    else Q (dec_clock s with locals := (FEMPTY |++ ZIP (MAP FST vshs, vs))))))
        (Call NONE (Label nm) (MAP Var var_nms)) R
  )

(* where do we stash the locals??
[hoare_logic_RetCall:]
  ( !ret_shape.
    hoare_logic G (Call NONE (Label nm) (MAP Var var_nms))
        (\ret s. case ret of
            | Return retv => shape_of retv = ret_shape /\ R NONE (
    ==>
    hoare_logic G ..
        (Call (SOME (SOME ret, NONE)) (Label nm) (MAP Var var_nms)) R
*)

[hoare_logic_ExtCall:]
  (
    hoare_logic G
    (\s.
        (case local_word s.locals ptr1_nm of NONE => F | SOME p1 =>
        (case local_word s.locals len1_nm of NONE => F | SOME l1 =>
        (case local_word s.locals ptr2_nm of NONE => F | SOME p2 =>
        (case local_word s.locals len2_nm of NONE => F | SOME l2 =>
        (case read_bytearray p1 (w2n l1) (mem_load_byte s.memory s.memaddrs s.be)
            of NONE => F | SOME bs1 =>
        (case read_bytearray p2 (w2n l2) (mem_load_byte s.memory s.memaddrs s.be)
            of NONE => F | SOME bs2 =>
        (let ffi_nm = ExtCall (explode f) in
        (if explode f = ""
            then R NONE (s with memory := write_bytearray p2 bs2 s.memory s.memaddrs s.be)
            else (G.ffi_guarantee s.ffi.io_events (ffi_nm, bs1, bs2) /\
            (! rv. G.ffi_rely s.ffi.io_events (ffi_nm, bs1, bs2) rv ==>
                (case rv of
                    | Oracle_final res =>
                        R (SOME (FinalFFI (Final_event ffi_nm bs1 bs2 res))) (empty_locals s)
                    | Oracle_return ffi l => LENGTH l = LENGTH bs2 /\
                    let ev = IO_event ffi_nm bs1 (ZIP (bs2, l)) in
                    R NONE (s with <| memory := write_bytearray p2 l s.memory s.memaddrs s.be;
                        ffi := s.ffi with <| ffi_state := ffi; io_events := s.ffi.io_events ++ [ev] |> |>)))
        ))))))))))
    (ExtCall f (Var ptr1_nm) (Var len1_nm) (Var ptr2_nm) (Var len2_nm)) R
  )

End

val eval_ind_rule =
  evaluate_ind |> Q.SPEC `UNCURRY P` |> REWRITE_RULE [UNCURRY_DEF] |> Q.GEN `P`

Theorem evaluate_While_inv_final:
  evaluate (While e p, s) = (res, s') ==>
  (! s. P s ==> (?w. eval s e = SOME (ValWord w)) /\
    (! w r s'. eval s e = SOME (ValWord w) /\ w <> 0w /\ s.clock > 0 /\
        evaluate (p, dec_clock s) = (r, s') /\ (r = NONE \/ r = SOME Continue) ==>
    P s')) ==>
  P s ==>
  (? fs. evaluate (While e p, fs) = (res, s') /\
  P fs /\
  (~ (eval fs e <> SOME (ValWord 0w) /\ fs.clock > 0 /\
          (FST (evaluate (p, dec_clock fs)) IN {NONE; SOME Continue}))
  ))
Proof
  ntac 2 strip_tac
  \\ last_x_assum mp_tac
  \\ measureInduct_on `s.clock`
  \\ reverse (Cases_on `eval s e <> SOME (ValWord 0w) /\ s.clock > 0 /\
        FST (evaluate (p, dec_clock s)) IN {NONE; SOME Continue}`)
  >- metis_tac []
  \\ disch_then (assume_tac o ONCE_REWRITE_RULE [evaluate_def])
  \\ disch_tac
  \\ last_x_assum (drule_then assume_tac)
  \\ last_x_assum (qspec_then `SND (evaluate (p, dec_clock s))` mp_tac)
  \\ gs [CaseEq "bool", UNCURRY_eq_pair, CaseEq "option", CaseEq "result"]
  \\ imp_res_tac evaluate_clock
  \\ gvs [dec_clock_def]
QED

Definition events_meet_guarantee_def:
  events_meet_guarantee g evs =
  (!i. i < LENGTH evs ==>
    case (EL i evs) of IO_event ffi_nm const_bs upd_bs =>
    g (TAKE i evs) (ffi_nm, const_bs, MAP FST upd_bs)
  )
End

Theorem events_meet_guarantee_snoc:
  events_meet_guarantee g (evs ++ [ev]) =
  (events_meet_guarantee g evs /\
    (case ev of IO_event ffi_nm const_bs upd_bs =>
        g evs (ffi_nm, const_bs, MAP FST upd_bs)))
Proof
  simp [events_meet_guarantee_def, GSYM ADD1, prim_recTheory.LESS_THM]
  \\ simp [DISJ_IMP_THM, FORALL_AND_THM, EL_APPEND]
  \\ simp [CONJ_COMM, TAKE_APPEND]
  \\ simp (RES_CANON arithmeticTheory.SUB_EQ_0)
QED

Definition ffi_rely_guarantee_def:
  ffi_rely_guarantee r g ffi =
  (! evs2 ffi_nm const_bs upd_bs.
    g (ffi.io_events ++ evs2) (ffi_nm, const_bs, upd_bs) ==>
    let st = FOLDL (\st ev. case ev of
        IO_event ffi_nm const_bs upd_bs => (case ffi.oracle ffi_nm st const_bs (MAP FST upd_bs) of
            Oracle_return st' _ => st')) ffi.ffi_state evs2 in
    r (ffi.io_events ++ evs2) (ffi_nm, const_bs, upd_bs)
        (ffi.oracle ffi_nm st const_bs upd_bs))
End

Theorem ffi_rely_guarantee_step:
  ffi_rely_guarantee r g ffi ==>
    g ffi.io_events (ffi_nm, const_bs, upd_bs) ==>
    r ffi.io_events (ffi_nm, const_bs, upd_bs)
        (ffi.oracle ffi_nm ffi.ffi_state const_bs upd_bs) /\
    (!st bs2. ffi.oracle ffi_nm ffi.ffi_state const_bs upd_bs =
            Oracle_return st bs2 /\ LENGTH bs2 = LENGTH upd_bs ==>
        ffi_rely_guarantee r g (ffi with <| ffi_state := st;
                io_events := ffi.io_events ++ [IO_event ffi_nm const_bs (ZIP (upd_bs, bs2))] |>))
Proof
  rw [ffi_rely_guarantee_def]
  >- (
    first_x_assum (qspec_then `[]` mp_tac)
    \\ simp []
  )
  >- (
    full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ last_x_assum drule
    \\ simp [MAP_ZIP]
  )
QED

Overload ffi_g_ok[local] = ``\G ffi.
    ffi_rely_guarantee G.ffi_rely G.ffi_guarantee ffi``;

Overload ffi_g_imp[local] = ``\G s s'.
    events_meet_guarantee G.ffi_guarantee s.ffi.io_events ==>
    events_meet_guarantee G.ffi_guarantee s'.ffi.io_events
    ``;

Triviality empty_locals_eq_IMP:
  empty_locals s = empty_locals s2 ==>
  ?l. s = (s2 with locals := l)
Proof
  simp [state_component_equality, empty_locals_def]
QED

Theorem hoare_logic_sound:

  ! P p Q.
  hoare_logic G P p Q ==>
  (! s res s'. evaluate (p, s) = (res, s') ==> P s ==>
    ffi_g_ok G s.ffi ==>
    res <> SOME Error /\ Q res s' /\ ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'
  )

Proof

  ho_match_mp_tac (Q.SPEC `G` hoare_logic_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)

  >- (
    metis_tac []
  )
  >- (
    metis_tac []
  )
  >- (
    fs [] \\ metis_tac []
  )
  >- (
    gs [evaluate_def]
  )
  >- (
    gs [evaluate_def]
  )
  >- (
    gs [evaluate_def]
  )
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [res_any_def]
  )
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gvs []
    \\ imp_res_tac eval_exp_shape
    \\ fs [is_valid_value_def]
    \\ gvs []
  )
  >- (
    fs [evaluate_def]
    \\ pairarg_tac \\ fs []
    \\ first_x_assum (drule_then (drule_then assume_tac))
    \\ fs [CaseEq "bool"] \\ gvs []
    \\ metis_tac []
  )

  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ fs [FLOOKUP_UPDATE]
    \\ imp_res_tac val_word_of_neq_NONE
    \\ gs []
    \\ imp_res_tac (Q.prove (`(if P then x else y) ==> (P \/ ~ P)`, metis_tac []))
    \\ gs []
    \\ first_x_assum (drule_then irule)
    \\ fs [res_any_drop_update]
    \\ imp_res_tac res_any_same
  )
  >- (
    dxrule evaluate_While_inv_final
    \\ disch_then (qspec_then `\s'. P s' /\ ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'` mp_tac)
    \\ impl_tac \\ fs []
    >- (
      (* prove invariant preserved *)
      rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ drule_then (drule_then assume_tac) eval_logic_elim
      \\ fs [FLOOKUP_UPDATE]
      \\ imp_res_tac val_word_of_neq_NONE
      \\ gs [res_any_drop_update]
      \\ imp_res_tac res_any_same
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ first_x_assum (drule_then drule)
      \\ simp [dec_clock_def]
    )
    \\ simp [PULL_EXISTS]
    \\ gen_tac
    \\ Cases_on `P fs` \\ fs []
    \\ dxrule_then (drule_then assume_tac) eval_logic_elim
    \\ fs [FLOOKUP_UPDATE]
    \\ imp_res_tac val_word_of_neq_NONE
    \\ gs [res_any_drop_update]
    \\ imp_res_tac res_any_same
    \\ ONCE_REWRITE_TAC [evaluate_def]
    \\ rw [] \\ gs [empty_locals_def]
    \\ gs [UNCURRY_eq_pair]
    \\ last_x_assum (drule_then assume_tac)
    \\ gs [CaseEq "option", dec_clock_def, CaseEq "result"]
  )

  >- (
    (* TailCall *)
    fs []
    \\ qpat_x_assum `case _ of NONE => F | _ => _` mp_tac
    \\ TOP_CASE_TAC
    \\ strip_tac
    \\ gs [evaluate_def, eval_def]
    \\ fs [OPT_MMAP_MAP_o, o_DEF, eval_def, Q.ISPEC `FLOOKUP _` ETA_THM]
    \\ fs [lookup_code_def, Q.ISPEC `MAP shape_of _` EQ_SYM_EQ]
    \\ gs [MAP_EQ_EVERY2]
    \\ fs [CaseEq "bool"]
    \\ gvs [] \\ simp [empty_locals_def]
    \\ fs [CaseEq "prod"]
    \\ first_x_assum drule
    \\ simp [dec_clock_def]
    \\ fs [CaseEq "option", CaseEq "result"] \\ gvs []
    \\ simp [empty_locals_def]
  )

  >- (
    (* ExtCall *)
    fs [evaluate_def, ffiTheory.call_FFI_def, eval_def]
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
    \\ Cases_on `explode f = ""`
    \\ fs []
    >- (
      gvs []
      \\ qsuff_tac `!s t. Q NONE s /\ s = t ==> Q NONE t`
      \\ TRY (disch_then (drule_then irule))
      \\ simp [panSemTheory.state_component_equality]
    )
    \\ drule_then drule ffi_rely_guarantee_step
    \\ strip_tac
    \\ first_x_assum drule
    \\ fs [CaseEq "ffi_result", CaseEq "oracle_result", CaseEq "bool"] \\ gvs []
    \\ rw []
    \\ simp [events_meet_guarantee_snoc, MAP_ZIP, empty_locals_def]
  )

QED


Theorem evaluate_add_Dec:
  evaluate (p, s) = (r, s1) /\
  ~ MEM nm (FLAT (MAP var_exp (panProps$exps_of p))) /\
  ~ MEM nm (panProps$assigns_of p) /\
  FLOOKUP s.locals nm = NONE /\
  (r <> SOME Error ==> eval s e <> NONE) ==>
  ?s2.
  evaluate (Dec nm e p, s) = (r, s2) /\ (r <> SOME Error ==> s2 = s1)
Proof
  simp [evaluate_def]
  \\ Cases_on `eval s e` \\ simp []
  \\ rw []
  \\ drule_then (qspec_then `nm` mp_tac) evaluate_locals_not_assigned
  \\ drule_all update_locals_not_vars_evaluate_eq
  \\ disch_then (qspec_then `THE (eval s e)` mp_tac)
  \\ rw []
  \\ simp [res_var_def]
  \\ rw [] \\ gs []
  \\ simp [DOMSUB_NOT_IN_DOM, FUPDATE_ELIM, TO_FLOOKUP]
  \\ simp [panSemTheory.state_component_equality]
QED


Theorem evaluate_ExtCall_add_Decs:
  evaluate (ExtCall f ptr1_e len1_e ptr2_e len2_e, s) = (r, s1) /\
  MAP (FLOOKUP s.locals) [ptr1_nm; len1_nm; ptr2_nm; len2_nm] = [NONE; NONE; NONE; NONE] /\
  ALL_DISTINCT [ptr1_nm; len1_nm; ptr2_nm; len2_nm] /\
  DISJOINT (set [ptr1_nm; len1_nm; ptr2_nm; len2_nm])
        (set (FLAT (MAP var_exp ((panProps$exps_of p) ++ [ptr1_e; len1_e; ptr2_e; len2_e])))) /\
  DISJOINT (set [ptr1_nm; len1_nm; ptr2_nm; len2_nm]) (set (panProps$assigns_of p))
  ==>
  ?s2.
  evaluate (Dec ptr1_nm ptr1_e (Dec len1_nm len1_e (Dec ptr2_nm ptr2_e (Dec len2_nm len2_e
    (ExtCall f (Var ptr1_nm) (Var len1_nm) (Var ptr2_nm) (Var len2_nm))))), s) = (r, s2) /\
  (r <> SOME Error ==> s2 = s1)
Proof
  rw []
  \\ drule_then (qspecl_then [`len2_nm`, `len2_e`] mp_tac) evaluate_add_Dec
  \\ simp [panPropsTheory.exps_of_def, panPropsTheory.assigns_of_def]
  \\ impl_tac >- ( rw [] \\ fs [evaluate_def, AllCaseEqs ()] )
  \\ rw []
  \\ dxrule_then (qspecl_then [`ptr2_nm`, `ptr2_e`] mp_tac) evaluate_add_Dec
  \\ simp [panPropsTheory.exps_of_def, panPropsTheory.assigns_of_def]
  \\ impl_tac >- ( rw [] \\ fs [evaluate_def, AllCaseEqs ()] )
  \\ rw []
  \\ dxrule_then (qspecl_then [`len1_nm`, `len1_e`] mp_tac) evaluate_add_Dec
  \\ simp [panPropsTheory.exps_of_def, panPropsTheory.assigns_of_def]
  \\ impl_tac >- ( rw [] \\ fs [evaluate_def, AllCaseEqs ()] )
  \\ rw []
  \\ dxrule_then (qspecl_then [`ptr1_nm`, `ptr1_e`] mp_tac) evaluate_add_Dec
  \\ simp [panPropsTheory.exps_of_def, panPropsTheory.assigns_of_def]
  \\ impl_tac >- ( rw [] \\ fs [evaluate_def, AllCaseEqs ()] )
  \\ rw []
  \\ fs [EVAL ``evaluate (Dec nm e p, s)``]
  \\ fs [AllCaseEqs (), UNCURRY_eq_pair]
  \\ gvs []
  \\ simp [PULL_EXISTS]
  \\ qpat_x_assum `evaluate (ExtCal _ _ _ _ _, _) = _` mp_tac
  \\ simp [evaluate_def, update_locals_not_vars_eval_eq_alt, eval_def, FLOOKUP_UPDATE]
  \\ rw []
  \\ fs [AllCaseEqs ()]
  \\ gvs []
  \\ simp [FLOOKUP_UPDATE]
QED

Theorem hoare_logic_ExtCall_add_Decs:
    ALL_DISTINCT [ptr1_nm; len1_nm; ptr2_nm; len2_nm] /\
    DISJOINT (set [ptr1_nm; len1_nm; ptr2_nm; len2_nm])
       (set (FLAT (MAP var_exp (panProps$exps_of p ++ [ptr1_e; len1_e; ptr2_e; len2_e])))) /\
    DISJOINT (set [ptr1_nm; len1_nm; ptr2_nm; len2_nm])
       (set (panProps$assigns_of p)) /\
    hoare_logic G P
       (Dec ptr1_nm ptr1_e (Dec len1_nm len1_e (Dec ptr2_nm ptr2_e (Dec len2_nm len2_e
           (ExtCall f (Var ptr1_nm) (Var len1_nm) (Var ptr2_nm) (Var len2_nm)))))) R ==>
    hoare_logic G (\s. MAP (FLOOKUP s.locals) [ptr1_nm; len1_nm; ptr2_nm; len2_nm] =
             [NONE; NONE; NONE; NONE] /\ P s)
        (ExtCall f ptr1_e len1_e ptr2_e len2_e) R
Proof
  rpt strip_tac
  \\ ho_match_mp_tac hoare_logic_equiv
  \\ first_x_assum (irule_at Any)
  \\ rw []
  \\ drule evaluate_ExtCall_add_Decs
  \\ disch_then (drule_at (Pat `ALL_DISTINCT _`))
  \\ fs []
  \\ metis_tac []
QED

Theorem eval_logic_Const:
  eval_logic G (\s. Q (s with locals := s.locals |+ (v_nm, ValWord c))) (Const c) v_nm Q
Proof
  simp [eval_logic_def, eval_def]
QED




