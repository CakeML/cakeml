open HolKernel boolLib bossLib ml_translatorLib word_preludeTheory mipsTheory
val _ = new_theory"mlMips"
val _ = translation_extends"word_prelude"

open wordsLib wordsTheory fcpTheory bitTheory lcsymtacs
val _ = numLib.prefer_num()

(* TODO: move lots of this stuff to word_prelude? *)


(* TODO: we need a better representation of words... push the polymorphism into CakeML? ... *)
(* Follow the EmitML version of wordsTheory and carry the size along with the value *)
(* look at w2w_itself_def etc. and how it's used in basis_emitScript.sml *)
(* alternatively: copy the FCP construction in CakeML *)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:30``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:30``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:32``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:32``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:33``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:33``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:34``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:64``,beta|->``:34``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:34``,beta|->``:64``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:34``,beta|->``:64``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:30``,beta|->``:64``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:30``,beta|->``:64``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:33``,beta|->``:32``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:33``,beta|->``:32``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:65``,beta|->``:64``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:65``,beta|->``:64``]word_extract_def)
val res = translate (INST_TYPE[alpha|->``:16``,beta|->``:32``]w2w_def)
val res = translate (INST_TYPE[alpha|->``:16``,beta|->``:32``]word_extract_def)

val res = translate (INST_TYPE[alpha|->``:16``,beta|->``:64``]w2w_def)

val res = translate SIGN_EXTEND_def

val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:16``,beta|->``:32``]sw2sw_def))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:16``,beta|->``:33``]sw2sw_def))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:32``,beta|->``:64``]sw2sw_def))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:64``,beta|->``:65``]sw2sw_def))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:16``,beta|->``:65``]sw2sw_def))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:16``,beta|->``:64``]sw2sw_def))

val res = word_concat_def
  |> SIMP_RULE (srw_ss()) [word_join_def,LET_THM]
  |> SIMP_RULE (srw_ss()) [GSYM WORD_w2w_OVER_BITWISE,w2w_w2w,w2w_LSL]
  |> INST_TYPE[alpha|->``:34``,beta|->``:30``,gamma|->``:64``]
  |> SIMP_RULE (srw_ss()) []
  |> CONV_RULE(QUANT_CONV(QUANT_CONV(RAND_CONV(SIMP_CONV(srw_ss()++WORD_EXTRACT_ss)[]))))
  |> translate

val res = word_concat_def
  |> SIMP_RULE (srw_ss()) [word_join_def,LET_THM]
  |> SIMP_RULE (srw_ss()) [GSYM WORD_w2w_OVER_BITWISE,w2w_w2w,w2w_LSL]
  |> INST_TYPE[alpha|->``:16``,beta|->``:16``,gamma|->``:32``]
  |> SIMP_RULE (srw_ss()) []
  |> CONV_RULE(QUANT_CONV(QUANT_CONV(RAND_CONV(SIMP_CONV(srw_ss()++WORD_EXTRACT_ss)[]))))
  |> translate

val word_bit_thm = Q.prove(
   `!w:'a word b. word_bit b w = (b < dimindex(:'a) /\ BIT b (w2n w))`,
   Cases
   THEN simp [wordsTheory.word_bit_n2w, DECIDE ``0 < n ==> (a <= n - 1 <=> a < n)``]
   )
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:64``]word_bit_thm))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:33``]word_bit_thm))
val res = translate (SIMP_RULE(srw_ss())[](INST_TYPE[alpha|->``:65``]word_bit_thm))

val res = translate NotWordValue_def
val res = translate GPR_def

(* TODO: raise'exception needs more thought: we want raise'exception to really correspond
to raising an exception in CakeML, which means it needs special treatment.
alternatively, raise'exception could take an extra argument with the default value to use instead of ARB
alternatively, maybe all uses are for the unit type anyway?  *)

val res = translate (SIMP_RULE(srw_ss())[oneTheory.one](INST_TYPE[alpha|->``:unit``]raise'exception_def))
val res = translate ExceptionCode_def
val res = translate SignalException_def

val res = translate write'GPR_def

val res = translate dfn'ADDI_def
val res = translate dfn'ADDIU_def
val res = translate dfn'ANDI_def
val res = translate dfn'DADDI_def
val res = translate dfn'DADDIU_def
val res = translate dfn'LUI_def
val res = translate dfn'ORI_def
(*
print_find"word_lt"
word_lt_def
want integer_wordTheory variant of lt?
val res = translate dfn'SLTI_def
*)

(*
114 instructions required
val res = translate Run_def
*)
val _ = export_theory()
