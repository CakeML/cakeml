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

Overload fcopy[local] = ``\nm locs_from locs_to. res_var locs_to (nm, FLOOKUP locs_from nm)``

Definition tick_context_def:
  tick_context context = if NULL context.future_triples then context
    else (context with <| triples := context.future_triples ++ context.triples;
        future_triples := [] |>)
End

Definition eval_logic_def:
  eval_logic G P exp v Q = (! s ls. P s ls ==> ?x. eval s exp = SOME x /\
    Q s (((HD ls) |+ (v, x)) :: DROP 1 ls))
End

Theorem eval_logic_elim = hd (RES_CANON eval_logic_def)
Theorem eval_logic_intro = last (RES_CANON eval_logic_def)

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
    (!s ls. P s ls ==> Q s ls) /\
    hoare_logic G Q p R ==>
    hoare_logic G P p R
  )

[hoare_logic_strengthen_post:]
  (! P Q R.
    (!res s ls. Q res s ls /\ res <> SOME Error ==> R res s ls) /\
    hoare_logic G P p Q ==>
    hoare_logic G P p R
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

[hoare_logic_Return:]
  ( !P.
    eval_logic G P e (strlit "return-val")
        (\s ls. case FLOOKUP (HD ls) (strlit "return-val") of
            | NONE => F
            | SOME v => size_of_shape (shape_of v) <= 32 /\
                Q (SOME (Return v)) (empty_locals s) (DROP 1 ls)) ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (Return e) Q
  )

[hoare_logic_Raise:]
  ( !P.
    eval_logic G P e (strlit "exn-val")
        (\s ls. case FLOOKUP (HD ls) (strlit "exn-val") of
            | NONE => F
            | SOME v => (case FLOOKUP s.eshapes eid of
                | NONE => F
                | SOME sh => shape_of v = sh /\ size_of_shape sh <= 32 /\
                    Q (SOME (Exception eid v)) (empty_locals s) (DROP 1 ls))) ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (Raise eid e) Q
  )

[hoare_logic_Tick:]
  ( !P.
    hoare_logic G (\s ls. if s.clock = 0 then P (SOME TimeOut) (empty_locals s) ls
        else P NONE (dec_clock s) ls) Tick P
  )

[hoare_logic_Store:]
  ( !P Q R.
    eval_logic G P addr_e (strlit "addr") Q /\
    eval_logic G Q val_e (strlit "val") (\s ls.
        case local_word (HD ls) (strlit "addr") of
        | NONE => F
        | SOME addr =>
        (case FLOOKUP (HD ls) (strlit "val") of
        | NONE => F
        | SOME v =>
        (case mem_stores addr (flatten v) s.memaddrs s.memory of
        | NONE => F
        | SOME m => R NONE (s with memory := m) (DROP 1 ls)))) ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (Store addr_e val_e) R
  )

[hoare_logic_StoreByte:]
  ( !P Q R.
    eval_logic G P addr_e (strlit "addr") Q /\
    eval_logic G Q val_e (strlit "val") (\s ls.
        case local_word (HD ls) (strlit "addr") of
        | NONE => F
        | SOME addr =>
        (case local_word (HD ls) (strlit "val") of
        | NONE => F
        | SOME b =>
        (case mem_store_byte s.memory s.memaddrs s.be addr (w2w b) of
        | NONE => F
        | SOME m => R NONE (s with memory := m) (DROP 1 ls)))) ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (StoreByte addr_e val_e) R
  )

[hoare_logic_Dec:]
  (
    ! P Q R.
    eval_logic G P e v
        (\s ls. Q (s with locals := fcopy v (HD ls) s.locals)
            (fcopy v s.locals FEMPTY :: DROP 1 ls)) /\
    hoare_logic G Q p
        (\res s ls. R res (s with locals := fcopy v (HD ls) s.locals) (DROP 1 ls))
    ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (Dec v e p) R
  )

[hoare_logic_Assign:]
  ( ! P Q.
    eval_logic G P e v
        (\s ls. Q NONE (s with locals := fcopy v (HD ls) s.locals) (DROP 1 ls)) ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls) /\
            OPTION_MAP shape_of (FLOOKUP s.locals v) =
            SOME (panProps$exp_shape (FMAP_MAP2 (shape_of o SND) s.locals) e))
        (Assign v e) Q
  )

[hoare_logic_Seq:]
  (
    ! P Q R.
    hoare_logic G P p1 (\r s ls. if r = NONE then Q s ls else R r s ls) /\
    hoare_logic G Q p2 R ==>
    hoare_logic G P (Seq p1 p2) R
  )

[hoare_logic_If:]
  (
    ! P Q1 Q2 R.
    eval_logic G P cond_exp (strlit "condition") (\s ls.
        case local_word (HD ls) (strlit "condition") of
        | NONE => F
        | SOME w => if w <> 0w then Q1 s (DROP 1 ls) else Q2 s (DROP 1 ls)) /\
    hoare_logic G Q1 p1 R /\
    hoare_logic G Q2 p2 R ==>
    hoare_logic G (\s ls. P s (FEMPTY :: ls)) (If cond_exp p1 p2) R
  )

[hoare_logic_While:]
  (
    ! Inv P Q G e p R.
    (!s ls. Inv s ls ==> P s (FEMPTY :: ls)) /\
    eval_logic G P e (strlit "condition") (\s ls.
        case local_word (HD ls) (strlit "condition") of
        | NONE => F
        | SOME w => if w = 0w then R NONE s (DROP 1 ls)
          else if s.clock = 0 then R (SOME TimeOut) (empty_locals s) (DROP 1 ls)
          else Q (dec_clock s) (DROP 1 ls)) /\
    hoare_logic G Q p (\r s ls. case r of NONE => Inv s ls | SOME Break => R NONE s ls
            | SOME Continue => Inv s ls | _ => R r s ls) ==>
    hoare_logic G Inv (While e p) R
  )

[hoare_logic_TailCall:]
  ( !vshs prog P Q.
    ALL_DISTINCT (MAP FST vshs) /\
    eval_logic G P (Struct args) (strlit "args_struct")
        (\s ls. case FLOOKUP (HD ls) (strlit "args_struct") of
            | SOME (Struct vs) => LIST_REL (\vsh x. SND vsh = shape_of x) vshs vs /\
                (if s.clock = 0 then R (SOME TimeOut) (empty_locals s) (DROP 1 ls)
                    else Q (dec_clock s with locals := (FEMPTY |++ ZIP (MAP FST vshs, vs))) ls)
            | _ => F)
    /\
    hoare_logic G Q prog (\res s ls. R res (empty_locals s) (DROP 1 ls) /\
        (case res of
            | SOME (Return r) => T
            | SOME (FinalFFI fres) => T
            | SOME (Exception eid exn) => T
            | SOME TimeOut => T
            | _ => F))
    ==>
    hoare_logic G (\s ls. FLOOKUP s.code nm = SOME (vshs, prog) /\ P s (FEMPTY :: ls))
        (TailCall (Label nm) args) R
  )

[hoare_logic_GenCall:]
  (
    hoare_logic G P (TailCall (Label nm) args)
        (\res s ls. case res of
            | SOME (Return retv) => (case ret of
                | NONE => R NONE (s with locals := HD ls) (DROP 1 ls)
                | SOME ret_nm => (case FLOOKUP (HD ls) ret_nm of
                    | SOME prev_retv => shape_of retv = shape_of prev_retv /\
                        R NONE (s with locals := (HD ls |+ (ret_nm, retv))) (DROP 1 ls)
                | NONE => F)
            )
            | SOME (FinalFFI _) => R res s (DROP 1 ls)
            | SOME (Exception _ _) => R res s (DROP 1 ls)
            | SOME TimeOut => R res s (DROP 1 ls)
            | _ => F)
    ==>
    hoare_logic G (\s ls. P s (s.locals :: ls))
        (Call (SOME (ret, NONE)) (Label nm) args) R
  )

[hoare_logic_GenCall_Handler:]
  ( !Q.
    hoare_logic G P (TailCall (Label nm) args)
        (\res s ls. case res of
            | SOME (Return retv) => (case ret of
                | NONE => R NONE (s with locals := HD ls) (DROP 1 ls)
                | SOME ret_nm => (case FLOOKUP (HD ls) ret_nm of
                    | SOME prev_retv => shape_of retv = shape_of prev_retv /\
                        R NONE (s with locals := (HD ls |+ (ret_nm, retv))) (DROP 1 ls)
                | NONE => F)
            )
            | SOME (FinalFFI _) => R res s (DROP 1 ls)
            | SOME TimeOut => R res s (DROP 1 ls)
            | SOME (Exception raised_eid exc_val) => if raised_eid = eid
                then (FLOOKUP s.eshapes eid = SOME (shape_of exc_val) /\
                    (case FLOOKUP (HD ls) exc_var of SOME prev => shape_of exc_val = shape_of prev
                        | _ => F) /\
                    Q (s with locals := (HD ls |+ (exc_var, exc_val))) (DROP 1 ls))
                else R res s (DROP 1 ls)
            | _ => F)
    /\
    hoare_logic G Q hprog R
    ==>
    hoare_logic G (\s ls. P s (s.locals :: ls))
        (Call (SOME (ret, (SOME (eid, exc_var, hprog)))) (Label nm) args) R
  )


[hoare_logic_ExtCall:]
  ( ! Q.
    eval_logic G Q (Struct [ptr1_e; len1_e; ptr2_e; len2_e]) (strlit "args_struct")
        (\s ls. case FLOOKUP (HD ls) (strlit "args_struct") of
            | SOME (Struct args) =>
            (case val_word_of (EL 0 args) of NONE => F | SOME p1 =>
            (case val_word_of (EL 1 args) of NONE => F | SOME l1 =>
            (case val_word_of (EL 2 args) of NONE => F | SOME p2 =>
            (case val_word_of (EL 3 args) of NONE => F | SOME l2 =>
            (case read_bytearray p1 (w2n l1) (mem_load_byte s.memory s.memaddrs s.be)
                of NONE => F | SOME bs1 =>
            (case read_bytearray p2 (w2n l2) (mem_load_byte s.memory s.memaddrs s.be)
                of NONE => F | SOME bs2 =>
            (let ffi_nm = ExtCall (explode f) in
            (if explode f = ""
            then R NONE (s with memory := write_bytearray p2 bs2 s.memory s.memaddrs s.be)
                (DROP 1 ls)
            else (G.ffi_guarantee s.ffi.io_events (ffi_nm, bs1, bs2) /\
            (! rv. G.ffi_rely s.ffi.io_events (ffi_nm, bs1, bs2) rv ==>
                (case rv of
                    | Oracle_final res =>
                        R (SOME (FinalFFI (Final_event ffi_nm bs1 bs2 res)))
                            (empty_locals s) (DROP 1 ls)
                    | Oracle_return ffi l => LENGTH l = LENGTH bs2 /\
                    let ev = IO_event ffi_nm bs1 (ZIP (bs2, l)) in
                    R NONE (s with <| memory := write_bytearray p2 l s.memory s.memaddrs s.be;
                            ffi := s.ffi with <| ffi_state := ffi; io_events := s.ffi.io_events ++ [ev] |> |>)
                        (DROP 1 ls))))
            ))))))))
            | _ => F
        )
    ==>
    hoare_logic G (\s ls. Q s (FEMPTY :: ls))
        (ExtCall f ptr1_e len1_e ptr2_e len2_e) R
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

  ! G P p Q.
  hoare_logic G P p Q ==>
  (! s ls res s'. evaluate (p, s) = (res, s') ==> P s ls ==>
    ffi_g_ok G s.ffi ==>
    res <> SOME Error /\ Q res s' ls /\ ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'
  )

Proof

  ho_match_mp_tac hoare_logic_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)

  >~ [`Dec _ _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [FLOOKUP_UPDATE, res_var_def]
    \\ first_x_assum (drule_then drule)
    \\ rw []
    \\ fs [FLOOKUP_UPDATE, FLOOKUP_pan_res_var_thm]
  )

  >~ [`Assign _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gvs []
    \\ imp_res_tac eval_exp_shape
    \\ fs [is_valid_value_def, FLOOKUP_UPDATE, res_var_def]
    \\ gvs []
  )

  >~ [`panLang$Return _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gvs [FLOOKUP_UPDATE, empty_locals_def]
  )

  >~ [`Raise _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gvs [FLOOKUP_UPDATE, empty_locals_def]
    \\ gvs [CaseEq "option"]
  )

  >~ [`Tick`]
  >- (
    fs [evaluate_def]
    \\ gvs [CaseEq "bool", empty_locals_def, dec_clock_def]
  )


  >~ [`Store _ _`]
  >- (
    fs [evaluate_def]
    \\ rpt (dxrule_then (drule_then assume_tac) eval_logic_elim \\ fs [])
    \\ gvs [FLOOKUP_UPDATE, CaseEq "v", CaseEq "word_lab", CaseEq "option"]
  )

  >~ [`StoreByte _ _`]
  >- (
    fs [evaluate_def]
    \\ rpt (dxrule_then (drule_then assume_tac) eval_logic_elim \\ fs [])
    \\ gvs [FLOOKUP_UPDATE, CaseEq "v", CaseEq "word_lab", CaseEq "option"]
  )

  >~ [`Seq _ _`]
  >- (
    fs [evaluate_def]
    \\ pairarg_tac \\ fs []
    \\ first_x_assum (drule_then (drule_then assume_tac))
    \\ fs [CaseEq "bool"] \\ gvs []
    \\ metis_tac []
  )

  >~ [`If _ _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ fs [FLOOKUP_UPDATE]
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
    \\ imp_res_tac (Q.prove (`(if P then x else y) ==> (P \/ ~ P)`, metis_tac []))
    \\ fs []
    \\ first_x_assum (drule_then irule)
    \\ fs []
  )

  >~ [`While _ _`]
  >- (
    dxrule evaluate_While_inv_final
    \\ disch_then (qspec_then `\s'. P' s' (FEMPTY :: ls) /\
        ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'` mp_tac)
    \\ impl_tac \\ fs []
    >- (
      (* prove invariant preserved *)
      rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ dxrule_then drule eval_logic_elim
      \\ fs [FLOOKUP_UPDATE, PULL_EXISTS]
      \\ rpt gen_tac
      \\ TOP_CASE_TAC
      \\ fs [val_word_of_eq_SOME]
      \\ rw [dec_clock_def] \\ res_tac \\ gs []
    )
    \\ simp [PULL_EXISTS]
    \\ gen_tac
    \\ Cases_on `P' fs (FEMPTY :: ls)` \\ fs []
    \\ dxrule_then drule eval_logic_elim
    \\ simp [FLOOKUP_UPDATE, PULL_EXISTS]
    \\ rpt gen_tac
    \\ TOP_CASE_TAC
    \\ fs [val_word_of_eq_SOME]
    \\ ONCE_REWRITE_TAC [evaluate_def]
    \\ fs [empty_locals_def, dec_clock_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ first_x_assum (drule_then (qspec_then `ls` mp_tac))
    \\ rw [] \\ fs []
    \\ gs [CaseEq "option", CaseEq "result"] \\ gvs []
  )

  >~ [`evaluate (Call (SOME (ret, NONE)) (Label nm) args, s)`]
  >- (
    fs []
    \\ Cases_on `evaluate (TailCall (Label nm) args, s)`
    \\ first_x_assum (drule_then drule)
    \\ fs [evaluate_def]
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod", CaseEq "bool"]
    \\ gs [CaseEq "result", CaseEq "option"] \\ gvs []
    \\ simp [empty_locals_def]
    \\ TOP_CASE_TAC \\ fs [is_valid_value_def]
    \\ fs [CaseEq "bool"]
    \\ gvs [set_var_def]
  )

  >~ [`evaluate (Call (SOME (ret, SOME (exc_id, exc_var, hprog))) (Label nm) args, s)`]
  >- (
    fs []
    \\ Cases_on `evaluate (TailCall (Label nm) args, s)`
    \\ first_x_assum (drule_then drule)
    \\ fs [evaluate_def]
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod", CaseEq "bool"]
    \\ gvs [CaseEq "result", CaseEq "option", empty_locals_def]
    >- (
      (* return case *)
      TOP_CASE_TAC \\ fs [is_valid_value_def]
      \\ fs [CaseEq "bool"]
      \\ gvs [set_var_def]
    )
    >- (
      (* exn case *)
      fs [CaseEq "bool"] \\ gvs []
      \\ imp_res_tac evaluate_invariants
      \\ fs [CaseEq "option", dec_clock_def] \\ gs []
      \\ TOP_CASE_TAC \\ fs [is_valid_value_def]
      \\ disch_tac \\ gs [CaseEq "bool"]
      \\ fs [set_var_def]
      \\ first_x_assum (drule_then drule)
      \\ simp []
    )
  )

  >~ [`TailCall _ _`]
  >- (
    fs []
    \\ dxrule_then drule eval_logic_elim
    \\ simp [eval_def, Q.ISPEC `eval _` ETA_THM]
    \\ fs [evaluate_def, eval_def, CaseEq "option", lookup_code_def] \\ gvs []
    \\ simp [FLOOKUP_UPDATE]
    \\ fs [CaseEq "bool", CaseEq "prod"] \\ gvs [empty_locals_def]
    \\ disch_tac
    \\ first_x_assum (drule_then drule)
    \\ fs [dec_clock_def]
    \\ fs [CaseEq "result", CaseEq "option"] \\ gvs []
  )

  >~ [`ExtCall _ _`]
  >- (
    fs [evaluate_def, ffiTheory.call_FFI_def, eval_def]
    \\ dxrule_then drule eval_logic_elim
    \\ simp [eval_def, FLOOKUP_UPDATE]
    \\ simp [PULL_EXISTS]
    \\ TOP_CASE_TAC
    \\ gvs []
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
    \\ gvs []
    \\ Cases_on `explode f = ""` \\ fs []
    >- (
      gvs []
      \\ disch_tac
      \\ qsuff_tac `!s t ls. Q NONE s ls /\ s = t ==> Q NONE t ls`
      \\ TRY (disch_then (drule_then irule))
      \\ simp [panSemTheory.state_component_equality]
    )
    \\ strip_tac
    \\ drule_then drule ffi_rely_guarantee_step
    \\ strip_tac
    \\ first_x_assum drule
    \\ fs [CaseEq "ffi_result", CaseEq "oracle_result", CaseEq "bool"] \\ gvs []
    \\ rw []
    \\ simp [events_meet_guarantee_snoc, MAP_ZIP, empty_locals_def]
  )

  \\ gs [evaluate_def]
  \\ metis_tac []

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

Definition logic_imp_def:
  logic_imp P Q = (!s ls. P s ls ==> Q s ls)
End

Theorem hoare_logic_weaken_imp =
    REWRITE_RULE [GSYM logic_imp_def] hoare_logic_weaken_pre

Definition annot_While_def:
  annot_While
    (Inv : (('a, 'ffi) state -> (mlstring |-> 'a v) list -> bool))
    (c : 'a panLang$exp) (b : 'a panLang$prog) =
    panLang$While c b
End

Theorem hoare_logic_annot_While:
  logic_imp Inv (\s ls. P s (FEMPTY :: ls)) /\
  eval_logic G P e (strlit "condition") (\s ls.
        case local_word (HD ls) (strlit "condition") of
        | NONE => F
        | SOME w => if w = 0w then R NONE s (DROP 1 ls)
          else if s.clock = 0 then R (SOME TimeOut) (empty_locals s) (DROP 1 ls)
          else Q (dec_clock s) (DROP 1 ls)) /\
  hoare_logic G Q p (\r s ls. case r of NONE => Inv s ls | SOME Break => R NONE s ls
        | SOME Continue => Inv s ls | _ => R r s ls) ==>
  hoare_logic G Inv (annot_While Inv e p) R
Proof
  rw [annot_While_def, logic_imp_def]
  \\ qspec_then `Inv` irule hoare_logic_While
  \\ rpt (first_assum (irule_at Any))
  \\ simp []
QED




Definition exp_args_def:
  exp_args (Struct xs) = xs /\
  exp_args (Field ix e) = [e] /\
  exp_args (Load sh addr) = [addr] /\
  exp_args (LoadByte addr) = [addr] /\
  exp_args (Op bop xs) = xs /\
  exp_args (Panop pop xs) = xs /\
  exp_args (Cmp cmp x y) = [x; y] /\
  exp_args (Shift sh_type x n) = [x] /\
  exp_args _ = []
End

Definition eval_args_def:
  eval_args s vs (Const w) = SOME (ValWord w) /\
  eval_args s vs (Var v) = FLOOKUP s.locals v /\
  eval_args s vs (Label fname) =
    OPTION_MAP (\_. ValLabel fname) (FLOOKUP s.code fname) /\
  eval_args s vs (Struct es) = SOME (Struct vs) /\
  eval_args s vs (Field index e) = (case LLOOKUP vs 0 of
    | SOME (Struct vs2) => LLOOKUP vs2 index
    | _ => NONE) /\
  eval_args s (vs : ('a v) list) (Load shape addr) = OPTION_BIND (LLOOKUP vs 0)
    (\v. OPTION_BIND (val_word_of v) (\w. mem_load shape w s.memaddrs s.memory)) /\
  eval_args s (vs : ('a v) list) (LoadByte addr) = OPTION_BIND (LLOOKUP vs 0)
    (\v. OPTION_BIND (val_word_of v)
        (OPTION_MAP (ValWord o w2w) o mem_load_byte s.memory s.memaddrs s.be)) /\
  eval_args s vs (Op op es) = OPTION_BIND (OPT_MMAP val_word_of vs)
    (OPTION_MAP ValWord o word_op op) /\
  eval_args s vs (Panop pop es) = OPTION_BIND (OPT_MMAP val_word_of vs)
    (OPTION_MAP ValWord o pan_op pop) /\
  eval_args s vs (Cmp cmp e1 e2) = OPTION_MAP
    (\ws. ValWord (if OPTREL (word_cmp cmp) (LLOOKUP ws 0) (LLOOKUP ws 1) then 1w else 0w))
    (OPT_MMAP val_word_of vs) /\
  eval_args s vs (Shift sh e n) = OPTION_BIND (LLOOKUP vs 0)
    (\v. OPTION_BIND (val_word_of v) (\w. OPTION_MAP ValWord (word_sh sh w n))) /\
  eval_args s vs BaseAddr = SOME (ValWord s.base_addr)
End

Triviality eval_args_thm_helper:
  OPT_MMAP val_word_of xs = (if EVERY (\x. case x of (ValWord _) => T | _ => F) xs
    then SOME (MAP (\x. case x of (ValWord w) => w) xs) else NONE)
Proof
  Induct_on `xs` \\ simp []
  \\ Cases \\ simp []
  \\ Cases_on `w` \\ simp []
  \\ rpt (TOP_CASE_TAC \\ fs [])
QED

Theorem eval_args_thm:
  eval s exp = OPTION_BIND (OPT_MMAP (eval s) (exp_args exp)) (\vs. eval_args s vs exp)
Proof
  Cases_on `exp`
  \\ simp [eval_def, exp_args_def, eval_args_def, Q.ISPEC `eval _` ETA_THM]
  >~ [`word_op _`]
  >- (
    TOP_CASE_TAC \\ simp []
    \\ simp [eval_args_thm_helper]
    \\ rw []
  )
  >~ [`pan_op _`]
  >- (
    TOP_CASE_TAC \\ simp []
    \\ simp [eval_args_thm_helper]
    \\ rw []
  )
  \\ simp [eval_def, exp_args_def, eval_args_def, Q.ISPEC `eval _` ETA_THM]
  \\ every_case_tac \\ simp [miscTheory.LLOOKUP_THM]
QED

Theorem eval_logic_args:
  eval_logic G P (Struct (exp_args exp)) (strlit "args_struct")
    (\s ls. case FLOOKUP (HD ls) (strlit "args_struct") of
        | SOME (Struct vs) => (case eval_args s vs exp of
            | SOME v => Q s ((HD (DROP 1 ls) |+ (v_nm, v)) :: DROP 2 ls)
            | NONE => F)
        | _ => F) ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) exp v_nm Q
Proof
  rw []
  \\ rw [eval_logic_def, eval_args_thm]
  \\ dxrule_then drule eval_logic_elim
  \\ rw []
  \\ fs [eval_def, CaseEq "option", FLOOKUP_UPDATE, Q.ISPEC `eval _` ETA_THM]
  \\ gvs []
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_Const:
  eval_logic G (\s ls. Q s ((HD ls |+ (v_nm, ValWord c)) :: DROP 1 ls))
    (Const c) v_nm Q
Proof
  simp [eval_logic_def, eval_def]
QED

Theorem eval_logic_Var:
  eval_logic G (\s ls. case FLOOKUP s.locals v of
        NONE => F | SOME x => Q s ((HD ls |+ (v_nm, x)) :: DROP 1 ls))
    (Var v) v_nm Q
Proof
  rw [eval_logic_def, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_Label:
  eval_logic G (\s ls. case FLOOKUP s.code lab of
        NONE => F | SOME _ => Q s ((HD ls |+ (v_nm, ValLabel lab)) :: DROP 1 ls))
    (Label lab) v_nm Q
Proof
  rw [eval_logic_def, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_Struct_CONS:
  eval_logic G P exp (strlit "field") Q /\
  eval_logic G Q (Struct exps) (strlit "struct")
    (\s ls. case
            (FLOOKUP (HD ls) (strlit "field"), FLOOKUP (HD ls) (strlit "struct")) of
        | (SOME fld, SOME (Struct xs)) => R s ((HD (DROP 1 ls) |+ (v_nm, Struct (fld :: xs))) :: DROP 2 ls)
        | _ => F)
  ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) (Struct (exp :: exps)) v_nm R
Proof
  rw []
  \\ irule eval_logic_intro \\ rw []
  \\ rpt (dxrule_then drule eval_logic_elim \\ rw [])
  \\ fs [eval_def, FLOOKUP_UPDATE, CaseEq "option"]
  \\ gvs []
QED

Theorem eval_logic_Struct_NIL:
  eval_logic G (\s ls. Q s ((HD ls |+ (v_nm, Struct [])) :: DROP 1 ls)) (Struct []) v_nm Q
Proof
  simp [eval_logic_def, eval_def]
QED

Theorem eval_logic_Field:
  eval_logic G P str_e (strlit "struct")
    (\s ls. case FLOOKUP (HD ls) (strlit "struct") of
        | SOME (Struct xs) => ix < LENGTH xs /\
            Q s ((HD (DROP 1 ls) |+ (v_nm, EL ix xs)) :: DROP 2 ls)
        | _ => F)
  ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) (Field ix str_e) v_nm Q
Proof
  rw [] \\ irule eval_logic_intro \\ rw []
  \\ rpt (dxrule_then drule eval_logic_elim \\ rw [])
  \\ fs [FLOOKUP_UPDATE, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_Load:
  eval_logic G P addr_e (strlit "addr")
    (\s ls. case FLOOKUP (HD ls) (strlit "addr") of
        | SOME (ValWord x) => (case mem_load shape x s.memaddrs s.memory of
            | SOME v => Q s ((HD (DROP 1 ls) |+ (v_nm, v)) :: DROP 2 ls)
            | _ => F)
        | _ => F)
  ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) (Load shape addr_e) v_nm Q
Proof
  rw [] \\ irule eval_logic_intro \\ rw []
  \\ rpt (dxrule_then drule eval_logic_elim \\ rw [])
  \\ fs [FLOOKUP_UPDATE, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_LoadByte:
  eval_logic G P addr_e (strlit "addr")
    (\s ls. case FLOOKUP (HD ls) (strlit "addr") of
        | SOME (ValWord x) => (case mem_load_byte s.memory s.memaddrs s.be x of
            | SOME v => Q s ((HD (DROP 1 ls) |+ (v_nm, ValWord (w2w v))) :: DROP 2 ls)
            | _ => F)
        | _ => F)
  ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) (LoadByte addr_e) v_nm Q
Proof
  rw [] \\ irule eval_logic_intro \\ rw []
  \\ rpt (dxrule_then drule eval_logic_elim \\ rw [])
  \\ fs [FLOOKUP_UPDATE, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_Cmp:
  eval_logic G P x_e (strlit "lhs_expr") P1 /\
  eval_logic G P1 y_e (strlit "rhs_expr")
    (\s ls. case (FLOOKUP (HD ls) (strlit "lhs_expr"), FLOOKUP (HD ls) (strlit "rhs_expr")) of
        | (SOME (ValWord x), SOME (ValWord y)) => Q s ((HD (DROP 1 ls) |+ (v_nm, ValWord (if word_cmp cmp x y then 1w else 0w))) :: DROP 2 ls)
        | _ => F)
  ==>
  eval_logic G (\s ls. P s (FEMPTY :: ls)) (Cmp cmp x_e y_e) v_nm Q
Proof
  rw [] \\ irule eval_logic_intro \\ rw []
  \\ rpt (dxrule_then drule eval_logic_elim \\ rw [])
  \\ fs [FLOOKUP_UPDATE, eval_def]
  \\ every_case_tac \\ fs []
QED

Theorem eval_logic_gen:
  eval_logic G (\s ls. case eval s expr of NONE => F
        | SOME v => Q s ((HD ls |+ (v_nm, v)) :: DROP 1 ls))
    expr v_nm Q
Proof
  rw [eval_logic_def]
  \\ every_case_tac \\ fs []
QED

Theorem hoare_logic_TailCall_code:
  ! code.
    FLOOKUP code nm = SOME (vshs, prog) /\
    ALL_DISTINCT (MAP FST vshs) /\
    eval_logic G P (Struct args) (strlit "args_struct")
        (\s ls. case FLOOKUP (HD ls) (strlit "args_struct") of
            | SOME (Struct vs) => LIST_REL (\vsh x. SND vsh = shape_of x) vshs vs /\
                (if s.clock = 0 then R (SOME TimeOut) (empty_locals s) (DROP 1 ls)
                    else Q (dec_clock s with locals := (FEMPTY |++ ZIP (MAP FST vshs, vs))) ls)
            | _ => F)
    /\
    hoare_logic G Q prog (\res s ls. R res (empty_locals s) (DROP 1 ls) /\
        (case res of
            | SOME (Return r) => T
            | SOME (FinalFFI fres) => T
            | SOME (Exception eid exn) => T
            | SOME TimeOut => T
            | _ => F))
    ==>
    hoare_logic G (\s ls. code SUBMAP s.code /\ P s (FEMPTY :: ls))
        (TailCall (Label nm) args) R
Proof
  rw []
  \\ irule hoare_logic_weaken_pre
  \\ irule_at Any hoare_logic_TailCall
  \\ rpt (first_assum (irule_at Any))
  \\ rw []
  \\ imp_res_tac FLOOKUP_SUBMAP
QED


val _ = export_theory();


