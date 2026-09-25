(*
  Derives a machine-code Hoare triple for the ag32 implementation of
  the return FFI primitive. The derivation uses ag32_decompilerLib,
  which is why it cannot live in ag32_progScript.
*)
Theory ag32_ffi_returnSpec
Ancestors
  set_sep prog ag32 temporal_state ag32_memory ag32_prog
  ag32_targetProof[qualified]
Libs
  preamble decompilerLib ag32_decompilerLib

val return_SPEC = let (* manually prove SPEC for return *)
  val dfn'Jump_fSnd_PC =
    ``(dfn'Jump (fSnd,x,Reg r) s).PC``
    |> SIMP_CONV (srw_ss()) [dfn'Jump_def,ag32Theory.ALU_def,LET_THM,
                             ag32Theory.ri2word_def]
  val SPEC_Jump_fSnd =
    ANY_AG32_SPEC_LEMMA
    |> SIMP_RULE std_ss []
    |> Q.SPEC `Encode (Jump (fSnd,0w,Reg 0w))`
    |> SIMP_RULE (srw_ss()) [ag32_targetProofTheory.Decode_Encode,dfn'Jump_MEM,
                     Run_def,dfn'Jump_fSnd_PC]
  val code_def = ag32_ffi_return_code_def
  val code_tm = code_def |> SPEC_ALL |> concl |> dest_eq |> snd
  val xs = listSyntax.dest_list code_tm |> fst |> map term_to_string |> butlast
  val thms = map derive_spec xs |> map (#1 o fst)
  val th = SPEC_COMPOSE_RULE (thms @ [SPEC_Jump_fSnd])
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``aS (ag32_ffi_return s) * aD md * ~aP``
  val lemma = prove(goal,
    fs [ag32_ffi_return_def,SEP_IMP_def,SEP_HIDE_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ metis_tac []);
  val th = MP th lemma
  in th end;

Theorem ag32_ffi_return_SPEC = return_SPEC
