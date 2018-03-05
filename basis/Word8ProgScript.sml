open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word64ProgTheory

val _ = new_theory "Word8Prog";

val _ = translation_extends "Word64Prog";

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val () = generate_sigs := true;

val _ = append_dec ``Dtabbrev unknown_loc [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`
val _ = trans "andb" `word_and:word8->word8->word8`;

val sigs = module_signatures ["fromInt", "toInt", "andb"];

val _ = ml_prog_update (close_module (SOME sigs));

(* if any more theorems get added here, probably should create Word8ProofTheory *)

open ml_translatorTheory

val WORD_UNICITY_R = Q.store_thm("WORD_UNICITY_R[xlet_auto_match]",
`!f fv fv'. WORD (f :word8) fv ==> (WORD f fv' <=> fv' = fv)`, fs[WORD_def]);

val WORD_UNICITY_L = Q.store_thm("WORD_UNICITY_L[xlet_auto_match]",
`!f f' fv. WORD (f :word8) fv ==> (WORD f' fv <=> f = f')`, fs[WORD_def]);

val n2w_UNICITY = Q.store_thm("n2w_UNICITY[xlet_auto_match]",
 `!n1 n2.n1 <= 255 ==> ((n2w n1 :word8 = n2w n2 /\ n2 <= 255) <=> n1 = n2)`,
 rw[] >> eq_tac >> fs[])

val WORD_n2w_UNICITY_L = Q.store_thm("WORD_n2w_UNICITY[xlet_auto_match]",
 `!n1 n2 f. n1 <= 255 /\ WORD (n2w n1 :word8) f ==>
   (WORD (n2w n2 :word8) f /\ n2 <= 255 <=> n1 = n2)`,
 rw[] >> eq_tac >> rw[] >> imp_res_tac WORD_UNICITY_L >>
`n1 MOD 256 = n1` by fs[] >> `n2 MOD 256 = n2` by fs[] >> fs[])

val _ = overload_on("WORD8",``WORD:word8 -> v -> bool``);

val _ = export_theory()
