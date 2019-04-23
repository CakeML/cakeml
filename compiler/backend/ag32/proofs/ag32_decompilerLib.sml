(*
  A decompiler that extracts a low-level shallow embedding from
  deeply embedded ag32 code.
*)
structure ag32_decompilerLib :> ag32_decompilerLib =
struct

open preamble
open set_sepTheory progTheory ag32Theory temporal_stateTheory
open ag32_memoryTheory ag32_progTheory
open decompilerLib

fun calculate_length_and_jump th =
  let val q = rand(concl th) in
  let val v = find_term (aconv ``aPC (p + 4w)``) q in (th,4,SOME 4) end
  handle e =>
  let val v = find_term (can (match_term ``aPC (p + n2w n)``)) q
  in (th,4,SOME (0 + (numSyntax.int_of_term o rand o rand o rand) v)) end
  handle e =>
  let val v = find_term (can (match_term ``aPC (p - n2w n)``)) q
  in (th,4,SOME (0 - (numSyntax.int_of_term o rand o rand o rand) v)) end
  handle e => (th,4,failwith "calculate_length_and_jump") end

fun derive_spec s = let
  val tm = Term [QUOTE s]
  val th = SPEC ``Encode ^tm`` ANY_AG32_SPEC
           |> SIMP_RULE (srw_ss()) [ag32_targetProofTheory.Decode_Encode,
                Run_def,dfn'Normal_MEM,
                dfn'Normal_PC,dfn'Jump_MEM,
                dfn'LoadMEM_PC,
                dfn'LoadMEMByte_PC,
                dfn'Shift_PC,
                dfn'LoadConstant_PC,
                dfn'LoadMEM_MEM,
                dfn'JumpIfNotZero_PC,
                dfn'JumpIfZero_PC,
                dfn'LoadMEMByte_MEM,
                dfn'StoreMEMByte_PC,
                dfn'Shift_MEM,
                dfn'Interrupt_MEM,
                dfn'Interrupt_PC,
                dfn'JumpIfNotZero_MEM,dfn'JumpIfZero_MEM,
                dfn'LoadConstant_MEM,alignmentTheory.aligned_numeric]
            |> UNDISCH_ALL
            |> CONV_RULE (RAND_CONV (UNBETA_CONV ``s.PC``))
            |> MATCH_MP SPEC_AG32_FIX_POST_PC
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
            |> DISCH_ALL
            |> CONV_RULE FIX_WORD32_ARITH_CONV
            |> REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND]
  in if can (find_term is_cond) (concl th) then let
       val (t,_,_) = find_term is_cond (concl th) |> dest_cond
       val intro_precond = progTheory.SPEC_MOVE_COND
                           |> REWRITE_RULE [GSYM precond_def] |> GSYM
       val lemma1 =
         DISCH t th
           |> SIMP_RULE std_ss [alignmentTheory.aligned_numeric,SEP_CLAUSES]
           |> REWRITE_RULE [intro_precond]
       val lemma2 =
         DISCH (mk_neg t) th
           |> SIMP_RULE std_ss [alignmentTheory.aligned_numeric,SEP_CLAUSES]
           |> REWRITE_RULE [intro_precond]
       in (calculate_length_and_jump lemma1,
           SOME (calculate_length_and_jump lemma2)) end
     else (calculate_length_and_jump th, NONE) end;

fun FUNPOW_Next_from_SPEC code_def th = let
  val (cst,code_tm) = code_def |> SPEC_ALL |> concl |> dest_eq
  val th = MATCH_MP SPEC_SUBSET_CODE th
           |> Q.SPEC `(code_set p (MAP Encode ^code_tm))`
           |> REWRITE_RULE [GSYM code_def]
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,fs [code_set_def,code_def])
  val th1 = MP th lemma
              |> SIMP_RULE std_ss [LET_THM,SPEC_MOVE_COND]
              |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
              |> UNDISCH_ALL
              |> Q.INST [`p`|->`s.PC`]
  val th1 = CONV_RULE (RAND_CONV (MOVE_OUT_CONV ``aS``)
                       THENC RAND_CONV (MOVE_OUT_CONV ``aD``)) th1
  val th1 = CONV_RULE (helperLib.PRE_CONV (MOVE_OUT_CONV ``aS``)
                       THENC helperLib.PRE_CONV (MOVE_OUT_CONV ``aD``)) th1
  val th1 = th1 |> REWRITE_RULE [GSYM STAR_ASSOC]
                |> ONCE_REWRITE_RULE [STAR_COMM]
  val th1 = MATCH_MP SPEC_IMP_FUNPOW_Next th1
              |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  in th1 end

val ag32_ffi_return_SPEC = let (* manually prove SPEC for return *)
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

fun ag32_decompile code_def = let
  val input_tm = ``(s:ag32_state,md:word32 set)``
  val ag32_tools =
    (derive_spec, fn _ => fail(), TRUTH,
     aPC_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator): decompiler_tools
  val (cst,code_tm) = code_def |> SPEC_ALL |> concl |> dest_eq
  val name = fst (dest_const cst)
  val name = substring(name,0,size(name)-5) ^ "_decomp"
  val code = listSyntax.dest_list code_tm |> fst |> map term_to_string
  val (res,defs) = decompile_io_strings ag32_tools name
                     (SOME (input_tm,input_tm)) code
  val res = res |> SIMP_RULE std_ss [LET_THM]
                |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  in (res,defs) end;

end
