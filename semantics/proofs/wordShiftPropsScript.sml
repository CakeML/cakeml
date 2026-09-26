(*
  Typing and evaluation of word shifts with computed shift amounts.
*)
Theory wordShiftProps
Ancestors
  ast semanticPrimitives typeSystem evaluate
Libs
  preamble

Theorem type_op_shift:
  type_op (Arith (Shift sh) (WordT sz)) ts t ⇔
  ts = [t_of (WordT sz); t_of (WordT sz)] ∧ t = t_of (WordT sz)
Proof
  Cases_on `sh` >> Cases_on `sz` >>
  simp [type_op_def, LENGTH_EQ_NUM_compute] >>
  rw [EQ_IMP_THM] >> gvs []
QED

Theorem do_app_word8_shift:
  do_app st (Arith (Shift sh) (WordT W8))
    [Litv (Word8 w); Litv (Word8 n)] =
  SOME (st, Rval (Litv (Word8 (shift8_lookup sh w (w2n n)))))
Proof
  Cases_on `st` >>
  simp [do_app_def, do_arith_def, check_type_def, the_Litv_Word8_def]
QED

Theorem do_app_word64_shift:
  do_app st (Arith (Shift sh) (WordT W64))
    [Litv (Word64 w); Litv (Word64 n)] =
  SOME (st, Rval (Litv (Word64 (shift64_lookup sh w (w2n n)))))
Proof
  Cases_on `st` >>
  simp [do_app_def, do_arith_def, check_type_def, the_Litv_Word64_def]
QED

Theorem evaluate_word8_shift_add:
  evaluate st env
    [App (Arith (Shift sh) (WordT W8))
      [Lit (Word8 w);
       App (Arith Add (WordT W8)) [Lit (Word8 n); Lit (Word8 m)]]] =
  (st, Rval [Litv (Word8 (shift8_lookup sh w (w2n (n + m))))])
Proof
  simp [evaluate_def, do_app_def, do_arith_def, check_type_def,
        the_Litv_Word8_def, state_component_equality]
QED

Theorem evaluate_word64_shift_add:
  evaluate st env
    [App (Arith (Shift sh) (WordT W64))
      [Lit (Word64 w);
       App (Arith Add (WordT W64)) [Lit (Word64 n); Lit (Word64 m)]]] =
  (st, Rval [Litv (Word64 (shift64_lookup sh w (w2n (n + m))))])
Proof
  simp [evaluate_def, do_app_def, do_arith_def, check_type_def,
        the_Litv_Word64_def, state_component_equality]
QED

Theorem shift_type_errors:
  (¬type_op (Arith (Shift sh) IntT) ts t) ∧
  do_app st (Arith (Shift sh) (WordT W8)) [Litv (Word8 w)] = NONE ∧
  do_app st (Arith (Shift sh) (WordT W8))
    [Litv (Word8 w); Litv (Word64 n)] = NONE ∧
  do_app st (Arith (Shift sh) (WordT W64))
    [Litv (Word64 n); Litv (IntLit i)] = NONE
Proof
  Cases_on `st` >>
  simp [type_op_def, do_app_def, do_arith_def, check_type_def,
        the_Litv_Word8_def]
QED

Theorem shift_boundaries:
  MAP (λsh. shift8_lookup sh 129w 0) [Lsl; Lsr; Asr; Ror] =
    [129w; 129w; 129w; 129w] ∧
  MAP (λsh. shift8_lookup sh 129w 1) [Lsl; Lsr; Asr; Ror] =
    [2w; 64w; 192w; 192w] ∧
  MAP (λsh. shift8_lookup sh 129w 8) [Lsl; Lsr; Asr; Ror] =
    [0w; 0w; 255w; 129w] ∧
  MAP (λsh. shift8_lookup sh 129w (w2n (255w:word8)))
    [Lsl; Lsr; Asr; Ror] = [0w; 0w; 255w; 3w] ∧
  MAP (λsh. shift64_lookup sh 0x8000000000000001w 0)
    [Lsl; Lsr; Asr; Ror] =
    [0x8000000000000001w; 0x8000000000000001w;
     0x8000000000000001w; 0x8000000000000001w] ∧
  MAP (λsh. shift64_lookup sh 0x8000000000000001w 1)
    [Lsl; Lsr; Asr; Ror] =
    [2w; 0x4000000000000000w; 0xC000000000000000w; 0xC000000000000000w] ∧
  MAP (λsh. shift64_lookup sh 0x8000000000000001w 64)
    [Lsl; Lsr; Asr; Ror] =
    [0w; 0w; 0xFFFFFFFFFFFFFFFFw; 0x8000000000000001w] ∧
  MAP (λsh. shift64_lookup sh 0x8000000000000001w
    (w2n (0xFFFFFFFFFFFFFFFFw:word64)))
    [Lsl; Lsr; Asr; Ror] = [0w; 0w; 0xFFFFFFFFFFFFFFFFw; 3w]
Proof
  EVAL_TAC
QED
