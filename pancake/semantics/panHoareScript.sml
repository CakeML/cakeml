(*
  A program logic for pancake in the Hoare/Floyd style.
*)

open preamble panLangTheory panPropsTheory;
local open alignmentTheory
           miscTheory
           wordLangTheory
           ffiTheory in end;

val _ = new_theory "panHoare";
val _ = set_grammar_ancestry [
  "panLang", "panSem", "ffi" ]



Datatype:
  hoare_context = <|
      exceptions_ok     :    eid -> bool
    ; ffi_rely          :    io_event list ->
                             (ffiname # word8 list # word8 list) ->
                             ('ffi oracle_result) -> bool
    ; ffi_guarantee     :    io_event list ->
                             (ffiname # word8 list # word8 list) -> bool
    ; termination       :    bool
    ; triples           :    mlstring |-> ((('a, 'ffi) state -> bool) # (('a, 'ffi) state -> bool))
  |>
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

Inductive hoare_logic:

[hoare_logic_weaken_pre:]
  (! Q.
    (!s. P s ==> Q s) /\
    hoare_logic G Q p R ==>
    hoare_logic G P p R
  )

[hoare_logic_equiv:]
  (! Q.
    (!s r s1. P s /\ evaluate (p, s) = (r, s1) ==>
        ?s2. evaluate (p2, s) = (r, s2) /\ empty_locals s2 = empty_locals s1 /\
            (((r = NONE) \/ (r = SOME Break) \/ (r = SOME Continue)) ==> s1 = s2)) /\
    hoare_logic G Q p2 R ==>
    hoare_logic G (\s. P s /\ Q s) p R
  )

[hoare_logic_Skip:]
  (
    hoare_logic G P Skip P
  )

[hoare_logic_Dec:]
  (
    ! Q.
    eval_logic G P e v Q /\
    (!prev. hoare_logic G Q p
        (\s. R (s with locals := res_var s.locals (v, prev))))
    ==>
    hoare_logic G P (Dec v e p) R
  )

[hoare_logic_Assign:]
  (
    eval_logic G P e v Q ==>
    hoare_logic G (\s. P s /\
            OPTION_MAP shape_of (FLOOKUP s.locals v) =
            SOME (exp_shape (FMAP_MAP2 (shape_of o SND) s.locals) e))
        (Assign v e) Q
  )

[hoare_logic_Seq:]
  (
    ! Q.
    hoare_logic G P p1 Q /\
    hoare_logic G Q p2 R ==>
    hoare_logic G P (Seq p1 p2) R
  )

[hoare_logic_While:]
  (
    ! Q.
    eval_logic_word G P e (\x s. if x = 0w then R s else Q (dec_clock s)) /\
    hoare_logic G Q p P ==>
    hoare_logic G P (While e p) R
  )

(* [hoare_logic_TailCall:]
  (
    ! Q1 Q2 Q3.
    eval_logic G P target ...
    eval_logic G ... (Struct args) ...
    opt_op_precond ... (\s. case target_v of ValLabel f =>
        lookup_code s.code fname args_v
      | _ => NONE) ...
    hoare_logic

    hoare_logic G Q p P ==>
    hoare_logic G P (Call NONE target args) R
  )

[hoare_logic_ExtCall:]
  ( ! Q1 Q2 Q3 Q4.
    eval_logic_word G P ptr1 Q1 /\
    (!x1. eval_logic_word G (Q1 x1) len1 (Q2 x1)) /\
    (!x1 x2. eval_logic_word G (Q2 x1 x2) ptr2 (Q3 x1 x2)) /\
    (!x1 x2 x3. eval_logic_word G (Q3 x1 x2 x3) len2 (Q4 x1 x2 x3)) /\
    (! p1 sz1 p2 sz2. opt_op_precond (Q4 p1 sz1 p2 sz2)
        (\s. read_bytearray p1 (w2n sz1) (mem_load_byte s.memory s.memaddrs s.be))
        (Q5 p1 sz1 p2 sz2)) /\
    (! p1 sz1 p2 sz2 b1. opt_op_precond (Q5 p1 sz1 p2 sz2 b1)
        (\s. read_bytearray p2 (w2n sz2) (mem_load_byte s.memory s.memaddrs s.be))
        (\b2 s. let ffi_nm = ExtCall (explode f) in
            if explode f = "" then R s else
            G.ffi_guarantee s.ffi.io_events (ffi_nm, b1, b2) /\
            (! rv. G.ffi_rely s.ffi.io_events (ffi_nm, b1, b2) rv ==>
                (case rv of Oracle_final _ => F
                    | Oracle_return ffi l => LENGTH l = LENGTH b2 /\
                    let ev = IO_event ffi_nm b1 (ZIP (b2, l)) in
                    R (s with <| memory := write_bytearray p2 l s.memory s.memaddrs s.be;
                        ffi := s.ffi with <| ffi_state := ffi; io_events := s.ffi.io_events ++ [ev] |> |>)
    )))) ==>
    hoare_logic G P (ExtCall f ptr1 len1 ptr2 len2) R
  )
*)

End

val eval_ind_rule =
  evaluate_ind |> Q.SPEC `UNCURRY P` |> REWRITE_RULE [UNCURRY_DEF] |> Q.GEN `P`

Theorem evaluate_While_inv_final:
  (! s. P s ==> (?w. eval s e = SOME (ValWord w)) /\
    (! w r s'. eval s e = SOME (ValWord w) ==> w <> 0w ==>
        evaluate (p, dec_clock s) = (r, s') ==>
        (r = SOME TimeOut /\ Q s' \/ (r = NONE /\ P s' /\ Q (empty_locals s'))))) ==>
  ! s res s'.
  evaluate (While e p, s) = (res, s') ==>
  P s /\ Q (empty_locals s) ==>
  (res = SOME TimeOut /\ Q s') \/
  (res = NONE /\ P s' /\ eval s' e = SOME (ValWord 0w))
Proof
  disch_tac \\ gen_tac
  \\ measureInduct_on `s.clock`
  \\ rpt GEN_TAC
  \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ rpt disch_tac
  \\ fs []
  \\ last_x_assum drule
  \\ rpt disch_tac
  \\ gs []
  \\ fs [CaseEq "bool"]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gs []
  \\ last_x_assum (drule_at (Pat `evaluate (While _ _, _) = _`))
  \\ fs [dec_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs []
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

Theorem mem_store_byte_same:
  mem_load_byte m dm be ptr = SOME b ==>
  mem_store_byte m dm be ptr b = SOME m
Proof
  rw [mem_load_byte_def]
  \\ gvs [CaseEq "word_lab", get_byte_def]
  \\ simp [mem_store_byte_def, set_byte_def]
  \\ cheat
QED

Theorem write_bytearray_same:
  ! sz ptr m x y bs.
  read_bytearray ptr sz (mem_load_byte m x y) = SOME bs ==>
  write_bytearray ptr bs m x y = m
Proof
  Induct \\ simp [read_bytearray_def, write_bytearray_def]
  \\ rw []
  \\ fs [CaseEq "option"]
  \\ gvs [write_bytearray_def]
  \\ simp [mem_store_byte_same]
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
    (res = SOME TimeOut \/ (res = NONE /\
        Q s' /\ ffi_g_ok G s'.ffi)) /\
    (ffi_g_imp G s s')
  )

Proof

  ho_match_mp_tac (Q.SPEC `G` hoare_logic_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  >- (
    metis_tac []
  )

  >- (
    fs []
    \\ res_tac \\ res_tac \\ fs []
    \\ imp_res_tac empty_locals_eq_IMP
    \\ gvs []
  )

  >- (
    gs [evaluate_def]
  )
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gs []
    \\ (pairarg_tac \\ fs [])
    \\ first_x_assum (drule_then drule)
    \\ rw []
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
    \\ gvs []
    \\ first_x_assum (drule_then (drule_then assume_tac))
    \\ metis_tac []
  )
  >- (
    dxrule_at (Pat `evaluate (While _ _, _) = _`) evaluate_While_inv_final
    \\ disch_then (qspec_then `ffi_g_imp G s` mp_tac)
    \\ disch_then (qspec_then `\s'. P s' /\ ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'` mp_tac)
    \\ impl_tac \\ fs []
    >- (
      simp [empty_locals_def]
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ drule_then (drule_then assume_tac) eval_logic_word_elim
      \\ fs []
      \\ rw []
      \\ first_x_assum drule
      \\ gs [dec_clock_def]
    )
    \\ strip_tac
    \\ fs []
    \\ drule_then (drule_then assume_tac) eval_logic_word_elim
    \\ gs []
  )

  >- (
    (* ExtCall *)
    fs [eval_logic_word_def, eval_logic_def]
    \\ rpt (last_x_assum (drule_then strip_assume_tac)
        \\ fs [eval_logic_word_elim_helper])
    \\ gvs []
    \\ last_x_assum mp_tac
    \\ simp [opt_op_precond_def]
    \\ disch_then (drule_then strip_assume_tac)
    \\ last_x_assum mp_tac
    \\ simp [opt_op_precond_def]
    \\ disch_then (drule_then strip_assume_tac)
    \\ fs [evaluate_def, ffiTheory.call_FFI_def]
    \\ Cases_on `explode f = ""` \\ fs []
    >- (
      drule write_bytearray_same \\ simp []
      \\ rw [] \\ fs []
      \\ qmatch_goalsub_abbrev_tac `Q s2`
      \\ qsuff_tac `s2 = s` \\ fs []
      \\ fs [Abbr `s2`]
      \\ simp [panSemTheory.state_component_equality]
    )
    \\ dxrule_then drule ffi_rely_guarantee_step
    \\ strip_tac
    \\ first_x_assum drule
    \\ fs [CaseEq "ffi_result", CaseEq "oracle_result", CaseEq "bool"] \\ gvs []
    \\ rw []
    \\ simp [events_meet_guarantee_snoc, MAP_ZIP]
  )

QED

Theorem hoare_logic_rules = LIST_CONJ (tl (BODY_CONJUNCTS hoare_logic_rules))


Theorem eval_logic_Const:
  eval_logic G (Q (ValWord c)) (Const c) Q
Proof
  simp [eval_logic_def, eval_def]
QED




