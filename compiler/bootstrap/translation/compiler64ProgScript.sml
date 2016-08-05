open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open std_preludeTheory;

val _ = new_theory "compiler64Prog"

(* temporary *)
val _ = translation_extends "std_prelude";

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``] else []

  val def = def |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

(* Attempts at translating bvp_to_word things *)
open data_to_wordTheory

val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val wcomp_simp = SIMP_RULE std_ss [word_2comp_def]

val _ = translate adjust_set_def

val _ = translate (make_header_def |> SIMP_RULE std_ss [word_lsl_n2w]|> conv64_RHS)

val shift_left_def = Define`
  shift_left (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_left (a << 32) (n - 32)
  else if n > 16 then shift_left (a << 16) (n - 16)
  else if n > 8 then shift_left (a << 8) (n - 8)
  else shift_left (a << 1) (n - 1)`

val shift_left_rwt = Q.prove(
  `!a n. a << n = shift_left a n`,
  completeInduct_on `n`
  \\ rw [Once shift_left_def]
  \\ qpat_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val shift_right_def = Define`
  shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_right (a >>> 32) (n - 32)
  else if n > 16 then shift_right (a >>> 16) (n - 16)
  else if n > 8 then shift_right (a >>> 8) (n - 8)
  else shift_right (a >>> 1) (n - 1)`

val shift_right_rwt = Q.prove(
  `!a n. a >>> n = shift_right a n`,
  completeInduct_on `n`
  \\ rw [Once shift_right_def]
  \\ qpat_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val _ = translate (shift_left_def |> conv64)
val _ = translate (shift_right_def |> spec64 |> CONV_RULE fcpLib.INDEX_CONV)

val _ = translate (tag_mask_def |> conv64_RHS |> we_simp |> conv64_RHS |> SIMP_RULE std_ss [shift_left_rwt] |> SIMP_RULE std_ss [Once (GSYM shift_left_rwt),word_2comp_def] |> conv64)

val _ = translate (encode_header_def |> conv64_RHS)

(* Manually inlined: shift_def, bytes_in_word *)
val inline_simp = SIMP_RULE std_ss [shift_def,bytes_in_word_def]

(* TODO: the wordLang datatype translations run into some weird errors with their no_closures proofs, better investigate that *)
val _ = translate (StoreEach_def |> inline_simp |> conv64)

val _ = translate (all_ones_def |> conv64_RHS |> we_simp |> SIMP_RULE std_ss [shift_left_rwt,shift_right_rwt] |> wcomp_simp |> conv64 |> wcomp_simp |> conv64)

val _ = translate (maxout_bits_def |> SIMP_RULE std_ss [word_lsl_n2w] |> conv64)

val _ = translate (ptr_bits_def  |> conv64)

val _ = translate (real_addr_def |> inline_simp |> conv64_RHS |> SIMP_RULE std_ss [LET_THM])

val _ = translate (real_offset_def |> inline_simp |> conv64)
val _ = translate (real_byte_offset_def |> inline_simp |> conv64)
val _ = translate (GiveUp_def |> wcomp_simp |> conv64)

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``]

val assign_rw = prove(``
  (i < 0 ⇒ n2w (Num (4 * (0 -i))) = n2w (Num (ABS (4*(0-i))))) ∧
  (¬(i < 0) ⇒ n2w (Num (4 * i)) = n2w (Num (ABS (4*i))))``,
  rw[]
  >-
    (`0 ≤ 4* -i` by intLib.COOPER_TAC>>
    fs[GSYM integerTheory.INT_ABS_EQ_ID])
  >>
    `0 ≤ 4*i` by intLib.COOPER_TAC>>
    fs[GSYM integerTheory.INT_ABS_EQ_ID])

(* TODO: word_mul should maybe target a real op ? *)

val _ = translate (assign_def |> SIMP_RULE std_ss [assign_rw] |> inline_simp |> conv64 |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO,shift_left_rwt] |> SIMP_RULE std_ss [word_mul_def])

val assign_side = prove(``
  ∀a b c d e f g. assign_side a b c d e f g ⇔ T``,
  simp[fetch "-" "assign_side_def"]>>
  (* Needs to check len args > 0 in SetGlobalsPtr case*)
  cheat) |> update_precondition

(*
metis_tac fails, probably because the induction thm doesn't match up somewhere...

val _ = translate (comp_def |> conv64 |> wcomp_simp |> conv64)
*)

open word_simpTheory

(* TODO: This method of forcing defs to be instantiated at :64 isn't very neat. find_def_for_const should instead use some way of finding (and automatically instantiating) type variables that are FCPs *)

val _ = translate (spec64 compile_exp_def)

val _ = export_theory();
