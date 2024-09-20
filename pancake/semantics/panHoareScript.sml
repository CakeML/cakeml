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


Type prop[local] =
    ``: (('a, 'ffi) state -> (mlstring |-> 'a v) list -> bool)``

Type trips[local] = ``: num # 'a panLang$prog #
        ((('a, 'ffi) prop # ('a result option -> ('a, 'ffi) prop)) set)``;

Datatype:
  hoare_context = <|
      ffi_rely          :    io_event list ->
                             (ffiname # word8 list # word8 list) ->
                             ('ffi oracle_result) -> bool
    ; ffi_guarantee     :    io_event list ->
                             (ffiname # word8 list # word8 list) -> bool
    ; termination       :    bool
    ; triples           :    (('a, 'ffi) trips) list
  |>
End

Definition word_of_def[simp]:
  word_of (Word w) = SOME w /\
  word_of _ = NONE
End

Theorem word_of_eq_SOME:
  !v. (word_of v = SOME w) <=> (v = Word w)
Proof
  ho_match_mp_tac word_of_ind \\ simp [word_of_def]
QED

Definition val_of_def[simp]:
  val_of (Val v) = SOME v /\
  val_of _ = NONE
End

Theorem val_of_eq_SOME:
  !v. (val_of v = SOME x) <=> (v = Val x)
Proof
  ho_match_mp_tac val_of_ind \\ simp [val_of_def]
QED

Overload val_word_of = ``\v. OPTION_BIND (val_of v) word_of``

Theorem neq_NONE_IMP:
  !v. v <> NONE ==> (?x. v = SOME x)
Proof
  Cases_on `v` \\ simp []
QED

Overload local_word = ``\locs nm. OPTION_BIND (FLOOKUP locs nm) val_word_of``

Definition eval_logic_def:
  eval_logic G P exp Q = (! s ls. P s ls ==> ?x. eval s exp = SOME x /\
    Q x s ls)
End

Theorem eval_logic_elim = hd (RES_CANON eval_logic_def)
Theorem eval_logic_intro = last (RES_CANON eval_logic_def)

Definition opt_op_precond_def:
  opt_op_precond P f Q = (!s. P s ==> ?x. f s = SOME x /\ Q x s)
End

Theorem opt_op_precond_elim = hd (RES_CANON opt_op_precond_def)

Definition is_continuing_result_def[simp]:
  is_continuing_result NONE = T /\
  is_continuing_result (SOME Continue) = T /\
  is_continuing_result _ = F
End

Definition is_fcall_result_def[simp]:
  is_fcall_result (SOME (Return _)) = T /\
  is_fcall_result (SOME (Exception _ _)) = T /\
  is_fcall_result (SOME (FinalFFI _)) = T /\
  is_fcall_result (SOME TimeOut) = T /\
  is_fcall_result _ = F
End

Definition result_return_val_def[simp]:
  result_return_val (SOME (Return v)) = (SOME v) /\
  result_return_val _ = NONE
End

Definition result_exception_val_def[simp]:
  result_exception_val eid (SOME (Exception raised_eid v)) =
    (if raised_eid = eid then SOME v else NONE) /\
  result_exception_val _ _ = NONE
End

(* Provide a way of specifying the invariant to use at a While loop. *)
Definition annot_While_def:
  annot_While
    (Inv : (('a, 'ffi) state -> (mlstring |-> 'a v) list -> bool))
    (c : 'a panLang$exp) (b : 'a panLang$prog) =
    panLang$While c b
End

Definition logic_imp_def:
  logic_imp P Q = (!s ls. P s ls ==> Q s ls)
End

Inductive hoare_logic:

[hoare_logic_weaken_pre_imp:]
  (! P Q R.
    logic_imp P Q /\
    hoare_logic G Q p R ==>
    hoare_logic G P p R
  )

[hoare_logic_strengthen_post:]
  (! P Q R.
    (!res s ls. Q res s ls /\ res <> SOME Error ==> R res s ls) /\
    hoare_logic G P p Q ==>
    hoare_logic G P p R
  )

[hoare_logic_use_context_triple:]
  (! P p Q PQs.
    MEM (0n, p, PQs) G.triples /\ (P, Q) ∈ PQs ==>
    hoare_logic G P p Q
  )

[hoare_logic_triple_induction:]
  (! P p Q PQs.
    (!P2 Q2. (P2, Q2) ∈ PQs ==>
        hoare_logic (G with triples := (1, p, PQs) :: G.triples) P2 p Q2) /\
    (P, Q) ∈ PQs ==>
    hoare_logic G P p Q
  )

[hoare_logic_equiv:]
  (! P Q R.
    (!s r s1. P s /\ evaluate (p, s) = (r, s1) ==>
        ?s2. evaluate (p2, s) = (r, s2) /\
        (r <> SOME Error ==> s2.ffi = s1.ffi /\ (!ls. R r s2 ls ==> R r s1 ls))) /\
    hoare_logic G Q p2 R ==>
    hoare_logic G (\s ls. P s /\ Q s ls) p R
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
    eval_logic G P e
        (\v s ls. size_of_shape (shape_of v) <= 32 /\
            Q (SOME (Return v)) (empty_locals s) ls) ==>
    hoare_logic G P (Return e) Q
  )

[hoare_logic_Raise:]
  (
    eval_logic G P e
        (\v s ls. case FLOOKUP s.eshapes eid of
                | NONE => F
                | SOME sh => shape_of v = sh /\ size_of_shape sh <= 32 /\
                    Q (SOME (Exception eid v)) (empty_locals s) ls) ==>
    hoare_logic G P (Raise eid e) Q
  )

[hoare_logic_Tick:]
  ( !P.
    hoare_logic G (\s ls. if s.clock = 0
        then P (SOME TimeOut) (empty_locals s) ls
        else P NONE (dec_clock s) ls) Tick P
  )

[hoare_logic_Store:]
  ( !P R.
    eval_logic G P (Struct [addr_e; val_e]) (\args s ls.
        case args of Struct [ValWord addr; v] =>
            (case mem_stores addr (flatten v) s.memaddrs s.memory of
            | NONE => F
            | SOME m => R NONE (s with memory := m) ls)
        | _ => F) ==>
    hoare_logic G P (Store addr_e val_e) R
  )

[hoare_logic_StoreByte:]
  ( !P R.
    eval_logic G P (Struct [addr_e; val_e]) (\args s ls.
        case args of Struct [ValWord addr; ValWord b] =>
            (case mem_store_byte s.memory s.memaddrs s.be addr (w2w b) of
            | NONE => F
            | SOME m => R NONE (s with memory := m) ls)
        | _ => F) ==>
    hoare_logic G P (StoreByte addr_e val_e) R
  )

[hoare_logic_Dec:]
  (
    ! P Q R.
    eval_logic G P e
        (\x s ls. Q (s with locals := s.locals |+ (v, x)) (s.locals :: ls)) /\
    hoare_logic G Q p
        (\res s ls. R res (s with locals := res_var s.locals
                (v, (FLOOKUP (HD ls) v))) (DROP 1 ls))
    ==>
    hoare_logic G P (Dec v e p) R
  )

[hoare_logic_Assign:]
  ( ! P Q.
    eval_logic G P e
        (\x s ls. OPTION_MAP shape_of (FLOOKUP s.locals v) = SOME (shape_of x) /\
            Q NONE (s with locals := s.locals |+ (v, x)) ls) ==>
    hoare_logic G P (Assign v e) Q
  )

[hoare_logic_Seq:]
  (
    ! P Q R.
    hoare_logic G P p1 (\r s ls. if r = NONE then Q s ls else R r s ls) /\
    hoare_logic G Q p2 R
    ==>
    hoare_logic G P (Seq p1 p2) R
  )

[hoare_logic_If:]
  (
    ! P Q1 Q2 R.
    eval_logic G P cond_exp (\c s ls. val_word_of c <> NONE /\
                if c <> ValWord 0w then Q1 s ls else Q2 s ls) /\
    hoare_logic G Q1 p1 R /\
    hoare_logic G Q2 p2 R
    ==>
    hoare_logic G P (If cond_exp p1 p2) R
  )

[hoare_logic_annot_While:]
  (
    ! Inv P Q e p R.
    logic_imp Inv P /\
    eval_logic G P e (\v s ls.
        val_word_of v <> NONE /\
        if v = ValWord 0w then R NONE s ls
        else if s.clock = 0 then R (SOME TimeOut) (empty_locals s) ls
        else Q (dec_clock s) ls) /\
    hoare_logic G Q p
        (\r s ls. if is_continuing_result r then Inv s ls
            else R (if r = SOME Break then NONE else r) s ls)
    ==>
    hoare_logic G Inv (annot_While Inv e p) R
  )

[hoare_logic_TailCall:]
  ( !vshs prog P Q.
    ALL_DISTINCT (MAP FST vshs) /\
    eval_logic G P (Struct args) (\vs s ls. case vs of
            | Struct vs => LIST_REL (\vsh x. SND vsh = shape_of x) vshs vs /\
                (if s.clock = 0 then R (SOME TimeOut) (empty_locals s) ls
                    else Q (dec_clock s with locals := (FEMPTY |++ ZIP (MAP FST vshs, vs))) ls)
            | _ => F) /\
    hoare_logic (G with triples := MAP (PRE ## I) G.triples)
        Q prog
        (\res s ls. R res (empty_locals s) ls /\
            (is_fcall_result res))
    ==>
    hoare_logic G (\s ls. FLOOKUP s.code nm = SOME (vshs, prog) /\ P s ls)
        (TailCall (Label nm) args) R
  )

[hoare_logic_TailCall_normalise:]
  ( ! P Q nm arg_nms args.
    ALL_DISTINCT arg_nms /\
    LENGTH arg_nms = LENGTH args /\
    eval_logic G P (Struct args) (\v s ls. case v of
            | Struct vs => Q (s with locals := s.locals |++ ZIP (arg_nms, vs)) (s.locals :: ls)
            | _ => F) /\
    hoare_logic G Q (TailCall (Label nm) (MAP Var arg_nms)) (\res s ls. R res s (DROP 1 ls))
    ==>
    hoare_logic G P (TailCall (Label nm) args) R
  )

[hoare_logic_GenCall_normalise:]
  (
    hoare_logic G P (TailCall (Label nm) args)
        (\res s ls. case result_return_val res of
            | SOME retv => (case ret of
                | NONE => R NONE (s with locals := HD ls) (DROP 1 ls)
                | SOME ret_nm => (case FLOOKUP (HD ls) ret_nm of
                    | SOME prev_retv => shape_of retv = shape_of prev_retv /\
                        R NONE (s with locals := (HD ls |+ (ret_nm, retv))) (DROP 1 ls)
                    | NONE => F)
            )
            | NONE => is_fcall_result res /\ R res s (DROP 1 ls))
    ==>
    hoare_logic G (\s ls. P s (s.locals :: ls))
        (Call (SOME (ret, NONE)) (Label nm) args) R
  )

[hoare_logic_GenCall_Handler_normalise:]
  ( !Q.
    hoare_logic G P (TailCall (Label nm) args)
        (\res s ls. case (result_return_val res, result_exception_val eid res) of
            | (SOME retv, _) => (case ret of
                | NONE => R NONE (s with locals := HD ls) (DROP 1 ls)
                | SOME ret_nm => (case FLOOKUP (HD ls) ret_nm of
                    | SOME prev_retv => shape_of retv = shape_of prev_retv /\
                        R NONE (s with locals := (HD ls |+ (ret_nm, retv))) (DROP 1 ls)
                    | NONE => F)
            )
            | (NONE, SOME exc_val) => FLOOKUP s.eshapes eid = SOME (shape_of exc_val) /\
                    (case FLOOKUP (HD ls) exc_var of SOME prev => shape_of exc_val = shape_of prev
                        | _ => F) /\
                    Q (s with locals := (HD ls |+ (exc_var, exc_val))) (DROP 1 ls)
            | _ => R res s (DROP 1 ls)) /\
    hoare_logic G Q hprog R
    ==>
    hoare_logic G (\s ls. P s (s.locals :: ls))
        (Call (SOME (ret, (SOME (eid, exc_var, hprog)))) (Label nm) args) R
  )

[hoare_logic_ExtCall:]
  ( ! Q.
    eval_logic G Q (Struct [ptr1_e; len1_e; ptr2_e; len2_e])
        (\v s ls. case v of
            | Struct args =>
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
            then R NONE (s with memory := write_bytearray p2 bs2 s.memory s.memaddrs s.be) ls
            else (G.ffi_guarantee s.ffi.io_events (ffi_nm, bs1, bs2) /\
            (! rv. G.ffi_rely s.ffi.io_events (ffi_nm, bs1, bs2) rv ==>
                (case rv of
                    | Oracle_final res =>
                        R (SOME (FinalFFI (Final_event ffi_nm bs1 bs2 res)))
                            (empty_locals s) ls
                    | Oracle_return ffi l => LENGTH l = LENGTH bs2 /\
                    let ev = IO_event ffi_nm bs1 (ZIP (bs2, l)) in
                    R NONE (s with <| memory := write_bytearray p2 l s.memory s.memaddrs s.be;
                            ffi := s.ffi with <| ffi_state := ffi; io_events := s.ffi.io_events ++ [ev] |> |>)
                        ls)))
            ))))))))
            | _ => F
        )
    ==>
    hoare_logic G Q (ExtCall f ptr1_e len1_e ptr2_e len2_e) R
  )

End

Theorem hoare_logic_weaken_pre = hoare_logic_weaken_pre_imp
    |> REWRITE_RULE [logic_imp_def]

Theorem hoare_logic_While = hoare_logic_annot_While
    |> REWRITE_RULE [annot_While_def, logic_imp_def]

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

Definition hoare_evaluate_def:
  hoare_evaluate G P p Q =
  (! s ls res s'. evaluate (p, s) = (res, s') /\ P s ls /\
    ffi_g_ok G s.ffi
    ==>
    res <> SOME Error /\ Q res s' ls /\ ffi_g_ok G s'.ffi /\ ffi_g_imp G s s'
  )
End

Triviality hoare_evaluate_intro = List.last (RES_CANON (hoare_evaluate_def))
Triviality hoare_evaluate_dest = MATCH_MP EQ_IMPLIES (SPEC_ALL hoare_evaluate_def)
Triviality hoare_evaluate_dest_conj = Q.GEN `P` hoare_evaluate_dest
  |> Q.SPEC `\s ls. P1 s ls /\ P2 s ls` |> SIMP_RULE std_ss [GSYM CONJ_ASSOC]

Triviality hoare_evaluate_triples:
  hoare_evaluate (G with triples := t) = hoare_evaluate G
Proof
  simp [FUN_EQ_THM, hoare_evaluate_def]
QED

Triviality hoare_evaluate_weaken_pre:
  hoare_evaluate G P p Q /\
  (!s ls. P' s ls ==> P s ls) ==>
  hoare_evaluate G P' p Q
Proof
  simp [hoare_evaluate_def]
  \\ metis_tac []
QED

Triviality hoare_evaluate_name_pre:
  (!s ls. P s ls ==> hoare_evaluate G (\s2 ls2. s2 = s /\ ls2 = ls) p Q) ==>
  hoare_evaluate G P p Q
Proof
  simp [hoare_evaluate_def]
  \\ metis_tac []
QED

val EVERY_mono_he_tac =
  dxrule_at_then Any irule MONO_EVERY
  \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ rpt (first_x_assum (drule_then strip_assume_tac))
  \\ dxrule_then irule hoare_evaluate_weaken_pre
  \\ fs []

val he_dest_simp_tac =
  drule_then drule hoare_evaluate_dest \\ simp []
  \\ disch_then drule \\ simp []


Triviality hoare_logic_triple_ind:
  (!P2 Q2. (P2, Q2) ∈ PQs ==> hoare_evaluate G (\s ls. P2 s ls /\
        (∀P3 Q3. (P3, Q3) ∈ PQs ==>
            hoare_evaluate G (\s2 ls. P3 s2 ls /\ s2.clock + 1 ≤ s.clock) p Q3) /\
        EVERY (\(m, p, PQs). ∀P Q. (P, Q) ∈ PQs ==>
            hoare_evaluate G (\s2 ls. P s2 ls ∧ m + s2.clock ≤ s.clock) p Q) G.triples)
    p Q2) ==>
  !n P Q.
  (P, Q) ∈ PQs /\
  EVERY (\(m, p, PQs). ∀P Q. (P, Q) ∈ PQs ==>
    hoare_evaluate G (\s ls. P s ls ∧ m + s.clock ≤ n) p Q) G.triples
  ==>
  hoare_evaluate G (\s ls. P s ls ∧ s.clock ≤ n) p Q
Proof
  disch_tac
  \\ Induct
  >- (
    rw []
    \\ irule hoare_evaluate_weaken_pre
    \\ first_x_assum (drule_then (irule_at Any))
    \\ simp []
    \\ simp [hoare_evaluate_def]
  )
  >- (
    rw []
    \\ fs []
    \\ irule hoare_evaluate_weaken_pre
    \\ last_x_assum (drule_then (irule_at Any))
    \\ rw []
    >- (
      irule hoare_evaluate_weaken_pre
      \\ first_x_assum (drule_then (irule_at Any))
      \\ simp []
      \\ EVERY_mono_he_tac
    )
    >- EVERY_mono_he_tac
  )
QED

Triviality hoare_logic_sound_ind:
  ! G P p Q.
  hoare_logic G P p Q ==>
  hoare_evaluate G (\s ls. P s ls /\
        EVERY (\(n, p, PQs). ! P Q. (P, Q) IN PQs ==>
                hoare_evaluate G (\s2 ls. P s2 ls /\ s2.clock + n <= s.clock) p Q)
            G.triples)
    p Q
Proof

  ho_match_mp_tac hoare_logic_ind
  \\ rw []
  \\ irule hoare_evaluate_intro
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs []

  >~ [`MEM (0, _) _.triples`]
  >- (
    dxrule_then drule (hd (RES_CANON EVERY_MEM))
    \\ simp []
    \\ disch_then drule
    \\ disch_tac
    \\ he_dest_simp_tac
  )

  >~ [`_ with triples := (_ :: _)`]
  >- (
    fs [hoare_evaluate_triples]
    \\ irule hoare_evaluate_dest
    \\ qpat_assum `evaluate_ = _` (irule_at Any)
    \\ irule_at Any hoare_logic_triple_ind
    \\ qpat_assum `(_, _) ∈ _` (irule_at Any)
    \\ simp []
    \\ irule_at Any arithmeticTheory.LESS_EQ_REFL
    \\ simp []
  )

  >~ [`_ /\ evaluate _ = _ ==> _`]
  >- (
    first_x_assum (drule_then drule)
    \\ disch_tac \\ fs []
    \\ he_dest_simp_tac
    \\ disch_tac \\ fs []
    \\ gs []
  )

  >~ [`Dec _ _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [res_var_def]
    \\ he_dest_simp_tac
    \\ rw []
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
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ fs [eval_def]
    \\ gvs [FLOOKUP_UPDATE, CaseEq "v", CaseEq "word_lab", CaseEq "option"]
  )

  >~ [`StoreByte _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ fs [eval_def]
    \\ gvs [FLOOKUP_UPDATE, CaseEq "v", CaseEq "word_lab", CaseEq "option"]
    \\ every_case_tac \\ fs []
  )

  >~ [`Seq _ _`]
  >- (
    fs [evaluate_def, UNCURRY_eq_pair]
    \\ he_dest_simp_tac
    \\ disch_tac
    \\ fs [CaseEq "bool"] \\ gvs []
    \\ he_dest_simp_tac
    \\ impl_tac \\ fs []
    \\ EVERY_mono_he_tac
    \\ imp_res_tac evaluate_clock
    \\ simp []
  )

  >~ [`If _ _ _`]
  >- (
    fs [evaluate_def]
    \\ drule_then (drule_then assume_tac) eval_logic_elim
    \\ gs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
    \\ imp_res_tac (Q.prove (`(if P then x else y) ==> (P \/ ~ P)`, metis_tac []))
    \\ fs []
    \\ drule_then drule hoare_evaluate_dest \\ simp []
    \\ disch_then drule
    \\ simp []
  )

  >~ [`annot_While _ _ _`]
  >- (
    fs [annot_While_def]
    \\ dxrule evaluate_While_inv_final
    \\ disch_then (qspec_then `\s'. P' s' ls /\
        ffi_g_ok G s'.ffi /\ ffi_g_imp G s s' /\ s'.clock <= s.clock` mp_tac)
    \\ impl_tac \\ fs []
    >- (
      fs [logic_imp_def]
      (* prove invariant preserved *)
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ dxrule_then drule eval_logic_elim
      \\ disch_tac \\ fs []
      \\ ntac 2 (imp_res_tac neq_NONE_IMP \\ fs [])
      \\ fs [word_of_eq_SOME, val_of_eq_SOME, GSYM AND_IMP_INTRO]
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ qpat_x_assum `_ \/ _` mp_tac
      \\ fs []
      \\ he_dest_simp_tac
      \\ imp_res_tac evaluate_clock
      \\ fs [dec_clock_def]
      \\ impl_tac \\ fs [] \\ TRY EVERY_mono_he_tac
      \\ rw [] \\ fs []
    )
    \\ simp [PULL_EXISTS, GSYM AND_IMP_INTRO]
    \\ rpt (gen_tac ORELSE disch_tac)
    \\ qpat_x_assum `_ \/ _` mp_tac
    \\ dxrule_then drule eval_logic_elim
    \\ simp [FLOOKUP_UPDATE, PULL_EXISTS]
    \\ rpt gen_tac
    \\ fs [Once evaluate_def]
    \\ rpt disch_tac
    \\ gs [CaseEq "v", CaseEq "word_lab", CaseEq "bool", UNCURRY_eq_pair] \\ gvs [empty_locals_def]
    \\ he_dest_simp_tac
    \\ fs [dec_clock_def]
    \\ impl_tac \\ TRY EVERY_mono_he_tac
    \\ gs [CaseEq "option", CaseEq "result"] \\ gvs []
  )

  >~ [`evaluate (Call (SOME (ret, NONE)) (Label nm) args, s)`]
  >- (
    Cases_on `evaluate (TailCall (Label nm) args, s)`
    \\ he_dest_simp_tac
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
    Cases_on `evaluate (TailCall (Label nm) args, s)`
    \\ he_dest_simp_tac
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
      \\ he_dest_simp_tac
      \\ impl_tac \\ fs []
      \\ imp_res_tac evaluate_clock
      \\ EVERY_mono_he_tac
    )
  )

  >~ [`TailCall (Label nm) (MAP Var arg_nms)`]
  >- (
    dxrule_then drule eval_logic_elim
    \\ simp [PULL_EXISTS]
    \\ gen_tac
    \\ simp [eval_def, Q.ISPEC `eval _` ETA_THM]
    \\ every_case_tac \\ fs []
    \\ disch_tac \\ fs []
    \\ simp [eval_def]
    \\ dxrule hoare_evaluate_dest
    \\ simp []
    \\ disch_then (drule_at (Pat `P' _ _`))
    \\ fs [evaluate_def, eval_def, OPT_MMAP_MAP_o, o_DEF]
    \\ imp_res_tac pan_commonPropsTheory.opt_mmap_length_eq
    \\ simp [Q.ISPEC `FLOOKUP _` ETA_THM,
        pan_commonPropsTheory.opt_mmap_some_eq_zip_flookup]
    \\ fs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
    \\ gvs []
    \\ gs [lookup_code_def]
    \\ fs [CaseEq "prod", CaseEq "bool", empty_locals_def, CaseEq "option"]
    \\ gvs [dec_clock_def]
  )

  >~ [`TailCall _ _`]
  >- (
    dxrule_then drule eval_logic_elim
    \\ simp [eval_def, Q.ISPEC `eval _` ETA_THM]
    \\ fs [evaluate_def, eval_def, CaseEq "option", lookup_code_def] \\ gvs []
    \\ fs [CaseEq "bool", CaseEq "prod"] \\ gvs [empty_locals_def]
    \\ disch_tac
    \\ he_dest_simp_tac
    \\ fs [dec_clock_def]
    \\ impl_tac
    \\ fs [EVERY_MAP, hoare_evaluate_triples] \\ TRY EVERY_mono_he_tac
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
      \\ match_mp_tac (Q.prove (`!s t ls. s = t ==> Q NONE s ls ==> Q NONE t ls`, metis_tac []))
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

  \\ gs [evaluate_def, logic_imp_def]
  \\ TRY (drule_then irule hoare_evaluate_dest)
  \\ TRY he_dest_simp_tac
  \\ simp []

QED

Theorem hoare_logic_sound:
  hoare_logic G P p Q /\
  EVERY (\(n, p, PQs). !P Q. (P, Q) ∈ PQs ==> hoare_evaluate G P p Q) G.triples ==>
  hoare_evaluate G P p Q
Proof
  rw []
  \\ drule hoare_logic_sound_ind
  \\ rw []
  \\ dxrule_then irule hoare_evaluate_weaken_pre
  \\ rw []
  \\ EVERY_mono_he_tac
QED




(* Embed the Dijstra-style back-propagation (weakest precond order) of the
   Hoare logic into an explicit constant that forces introduction steps of
   the logic to be performed in the right order. The intermediate condition
   `Q` will be discovered by solving the current goal, and fed onwards. *)
Definition rev_hoare_def:
  rev_hoare cont cur_goal = (?Q. cont Q /\ cur_goal Q)
End

Theorem rev_hoare_intro = hd (tl (RES_CANON rev_hoare_def))
    |> REWRITE_RULE [PULL_FORALL, AND_IMP_INTRO]




Theorem eval_logic_rev:
  cont (\s ls. case eval s expr of NONE => F | SOME v => Q v s ls)
  ==>
  rev_hoare cont (\P. eval_logic G P expr Q)
Proof
  rw [rev_hoare_def, eval_logic_def]
  \\ first_assum (irule_at Any)
  \\ rw []
  \\ every_case_tac \\ fs []
QED

val rev_hoare_tm = SPEC_ALL rev_hoare_def |> concl |> dest_eq |> fst |> strip_comb |> fst
val hoare_logic_tm = SPEC_ALL hoare_logic_Skip |> concl |> strip_comb |> fst
val eval_logic_tm = SPEC_ALL eval_logic_def |> concl |> dest_eq |> fst |> strip_comb |> fst

Triviality hoare_logic_to_rev:
  hoare_logic G P f Q ==> cont P ==> rev_hoare cont (\P. hoare_logic G P f Q)
Proof
  simp [rev_hoare_def] \\ metis_tac []
QED

fun get_precond tm = let
    val (f, xs) = strip_comb tm
  in
    if is_var f then SOME (hd xs)
    else if same_const f eval_logic_tm
    then SOME (hd (tl xs))
    else if same_const f hoare_logic_tm
    then SOME (hd (tl xs))
    else NONE
  end

fun has_precond tm = can valOf (get_precond tm)

fun conjs_to_rev_hoare tm [] = tm
  | conjs_to_rev_hoare tm (ltm :: ltms) = let
    val p = valOf (get_precond ltm)
    val rh = conjs_to_rev_hoare tm ltms
  in list_mk_icomb (rev_hoare_tm, [mk_abs (p, rh), mk_abs (p, ltm)])
  end

fun hoare_logic_rule_to_rev_form thm = let
    val thm1 = thm |> REWRITE_RULE [PULL_EXISTS] |> SPEC_ALL
    val assms = fst (strip_imp (concl thm1))
    val thm2 = UNDISCH_ALL thm1
    val thm3 = MATCH_MP hoare_logic_to_rev thm2
    val thm4 = foldl (uncurry DISCH) thm3 assms
        |> REWRITE_RULE [PULL_EXISTS, AND_IMP_INTRO]
    val (lhs, rhs) = dest_imp (concl thm4)
    val (logs, others) = partition has_precond (strip_conj lhs)
    val (cont :: other_logs) = rev logs
    val rh = conjs_to_rev_hoare (list_mk_conj (others @ [cont])) other_logs
    val gl = mk_imp (rh, rhs)
  in prove (gl,
    disch_then (strip_assume_tac o REWRITE_RULE [rev_hoare_def])
    \\ match_mp_tac (GEN_ALL thm4)
    \\ full_simp_tac bool_ss []
    \\ rpt (first_assum (irule_at Any))
    \\ full_simp_tac bool_ss []
  ) end

Theorem hoare_logic_rev_init:
  rev_hoare (\Q. logic_imp P Q) (\Q. hoare_logic G Q f R) ==>
  hoare_logic G P f R
Proof
  rw [rev_hoare_def, logic_imp_def]
  \\ drule_then irule hoare_logic_weaken_pre
  \\ fs []
QED

Theorem hoare_logic_rev_rules = LIST_CONJ (map hoare_logic_rule_to_rev_form
  [hoare_logic_Skip, hoare_logic_Break, hoare_logic_Continue,
    hoare_logic_Return, hoare_logic_Raise, hoare_logic_Tick,
    hoare_logic_Store, hoare_logic_StoreByte, hoare_logic_Dec,
    hoare_logic_Assign, hoare_logic_Seq, hoare_logic_If,
    hoare_logic_annot_While, hoare_logic_GenCall_normalise,
    hoare_logic_GenCall_Handler_normalise, hoare_logic_ExtCall])

Theorem hoare_logic_TailCall_code:
  ! code.
    FLOOKUP code nm = SOME (vshs, prog) /\
    ALL_DISTINCT (MAP FST vshs) ==>
    eval_logic G P (Struct args) (\vs s ls. case vs of
            | Struct vs => LIST_REL (\vsh x. SND vsh = shape_of x) vshs vs /\
                (if s.clock = 0 then R (SOME TimeOut) (empty_locals s) ls
                    else Q (dec_clock s with locals := (FEMPTY |++ ZIP (MAP FST vshs, vs))) ls)
            | _ => F) /\
    hoare_logic (G with triples := MAP (PRE ## I) G.triples)
        Q prog
        (\res s ls. R res (empty_locals s) ls /\
            (is_fcall_result res))
    ==>
    hoare_logic G (\s ls. code SUBMAP s.code /\ P s ls)
        (TailCall (Label nm) args) R
Proof
  rw []
  \\ irule hoare_logic_weaken_pre
  \\ irule_at Any hoare_logic_TailCall
  \\ rpt (first_assum (irule_at Any))
  \\ rw []
  \\ imp_res_tac FLOOKUP_SUBMAP
QED

Theorem hoare_logic_TailCall_rev_code = hoare_logic_rule_to_rev_form
        (UNDISCH (SPEC_ALL hoare_logic_TailCall_code))
    |> DISCH_ALL
    |> Q.GEN `code`

Theorem hoare_logic_TailCall_norm_args_code:
  ! code.
  FLOOKUP code nm = SOME (vshs, prog) /\
  ALL_DISTINCT (MAP FST vshs) /\
  LENGTH vshs = LENGTH args ==>
  eval_logic G P (Struct args) (\v s ls. case v of
        | Struct vs => Q (s with locals := s.locals |++ ZIP (MAP FST vshs, vs)) (s.locals :: ls)
        | _ => F) /\
  hoare_logic G Q (TailCall (Label nm) (MAP Var (MAP FST vshs))) (\res s ls. R res s (DROP 1 ls))
  ==>
  hoare_logic G P (TailCall (Label nm) args) R
Proof
  rw []
  \\ irule hoare_logic_TailCall_normalise
  \\ rpt (first_assum (irule_at Any))
  \\ simp []
QED

Theorem hoare_logic_TailCall_norm_args_rev_code = hoare_logic_rule_to_rev_form
        (UNDISCH (SPEC_ALL hoare_logic_TailCall_norm_args_code))
    |> DISCH_ALL
    |> Q.GEN `code`

Theorem hoare_logic_image_triple_induction:
  (!x. P x ==>
    hoare_logic (G with triples := (1, f, IMAGE (\x. (Q x, R x)) {x | P x}) :: G.triples) (Q x) f (R x))
  ==>
  !x. P x ==> hoare_logic G (Q x) f (R x)
Proof
  rw []
  \\ irule hoare_logic_triple_induction
  \\ qexists_tac `IMAGE (\x. (Q x, R x)) {x | P x}`
  \\ simp [PULL_EXISTS]
  \\ metis_tac []
QED

Theorem hoare_logic_use_context_triple_rev = hoare_logic_rule_to_rev_form
    hoare_logic_use_context_triple

val _ = export_theory();


