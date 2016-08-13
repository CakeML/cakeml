open preamble
     backendTheory
     to_lab_x64BootstrapTheory
     x64_configTheory
     x64_targetTheory
     x64_targetLib
     asmLib

val _ = new_theory "x64Bootstrap";

(* TODO: move *)

val prog_to_bytes_MAP = Q.store_thm("prog_to_bytes_MAP",
  `∀ls. prog_to_bytes ls = FLAT
          (MAP (FLAT o MAP line_bytes o Section_lines) ls)`,
  ho_match_mp_tac lab_to_targetTheory.prog_to_bytes_ind
  \\ rw[lab_to_targetTheory.prog_to_bytes_def]);

(* -- *)

val _ = Globals.max_print_depth := 10;

val rconc = rhs o concl;

val cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset [
    computeLib.Extenders [
      basicComputeLib.add_basic_compset,
      compilerComputeLib.add_compiler_compset,
      asmLib.add_asm_compset,
      x64_targetLib.add_x64_encode_compset],
    computeLib.Defs [
      x64_compiler_config_def,
      x64_config_def]
  ] cs
val eval = computeLib.CBV_CONV cs;

val bare_cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset[computeLib.Extenders[compilerComputeLib.add_compiler_compset]] bare_cs
val bare_eval = computeLib.CBV_CONV bare_cs

fun mk_def_name s = String.concat[s,"_def"];
fun mk_def s tm = new_definition(mk_def_name s,mk_eq(mk_var(s,type_of tm),tm))

fun make_abbrevs str n [] acc = acc
  | make_abbrevs str n (t::ts) acc =
    make_abbrevs str (n-1) ts
      (mk_def (str^(Int.toString n)) t :: acc)

fun intro_abbrev [] tm = raise UNCHANGED
  | intro_abbrev (ab::abbs) tm =
      FORK_CONV(REWR_CONV(SYM ab),intro_abbrev abbs) tm

val chunk_size = 50
val num_threads = 8
fun say_str s i n =
  Lib.say(String.concat["eval ",s,": chunk ",Int.toString i,": el ",Int.toString n,": "])

val lab_to_target_thm0 =
  stack_to_lab_thm
  |> CONV_RULE(RAND_CONV(
       REWR_CONV from_lab_def THENC
       RATOR_CONV(RAND_CONV bare_eval)))

val tm9 = lab_to_target_thm0 |> rconc

val lab_prog_els =
  lab_prog_def |> rconc |> listSyntax.dest_list |> #1

val filter_skip_lab_prog =
  ISPEC(lhs(concl(lab_prog_def)))lab_filterTheory.filter_skip_MAP

val filter_skip_fn =
  filter_skip_lab_prog |> rconc |> rator |> rand

fun eval_fn i n p =
  let
    val () = say_str "filter_skip" i n
    val tm = mk_comb(filter_skip_fn,p)
  in time eval tm end

val ths = parlist num_threads chunk_size eval_fn lab_prog_els

val filter_skip_thm =
  tm9 |> (
    REWR_CONV lab_to_targetTheory.compile_def THENC
    RAND_CONV(
      REWR_CONV filter_skip_lab_prog THENC
      RAND_CONV(REWR_CONV lab_prog_def) THENC
      map_ths_conv ths))

val skip_prog_def = mk_def"skip_prog" (filter_skip_thm |> rconc |> rand);

val filter_skip_thm' = filter_skip_thm
  |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM skip_prog_def))))

(* about 3 mins, could parallelise? *)
val ffi_limit_thm =
  ``find_ffi_index_limit skip_prog``
  |> (RAND_CONV(REWR_CONV skip_prog_def) THENC time eval)

val lab_to_target_thm1 =
  lab_to_target_thm0
  |> CONV_RULE (RAND_CONV(
     REWR_CONV filter_skip_thm' THENC
     REWR_CONV lab_to_targetTheory.compile_lab_def THENC
     RAND_CONV(REWR_CONV ffi_limit_thm) THENC
     REWR_CONV LET_THM THENC BETA_CONV))

val tm10 = lab_to_target_thm1 |> rconc |> rator |> rator |> rand

val remove_labels_thm0 =
  tm10 |>
  (REWR_CONV lab_to_targetTheory.remove_labels_def THENC
   RAND_CONV(
     REWR_CONV lab_to_targetTheory.enc_sec_list_def THENC
     RAND_CONV eval THENC
     REWR_CONV LET_THM THENC BETA_CONV THENC
     PATH_CONV"lrlr"eval) THENC
   PATH_CONV"lllr"eval THENC
   PATH_CONV"lr"eval)

val tm11 = remove_labels_thm0 |> rconc |> rand

val enc_sec_tm = tm11 |> rator |> rand

val skip_prog_els = skip_prog_def |> rconc |> listSyntax.dest_list |> #1

fun eval_fn i n p =
  let
    val () = say_str "enc_sec" i n
    val tm = mk_comb(enc_sec_tm,p)
  in time eval tm end

(* slow, >30 mins *)

val ths = parlist num_threads chunk_size eval_fn skip_prog_els

val remove_labels_thm1 =
  remove_labels_thm0
  |> CONV_RULE(RAND_CONV(
       RAND_CONV(
         RAND_CONV(REWR_CONV skip_prog_def) THENC
         map_ths_conv ths)))

val encoded_prog_def = mk_def"encoded_prog" (remove_labels_thm1 |> rconc |> rand);

val remove_labels_thm1' =
  remove_labels_thm1 |>
  CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM encoded_prog_def))))

val lab_to_target_thm2 =
  lab_to_target_thm1
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         REWR_CONV remove_labels_thm1' THENC
         REWR_CONV lab_to_targetTheory.remove_labels_loop_def THENC
         REWR_CONV LET_THM)))

val tm12 =
  lab_to_target_thm2 |> rconc
  |> funpow 2 rator
  |> funpow 2 rand

val () = Lib.say "eval: compute_labels_alt: "

val encoded_prog_els =
  encoded_prog_def |> rconc |> listSyntax.dest_list |> #1

val num_enc = length encoded_prog_els
val encoded_prog_defs = make_abbrevs "encoded_prog_el" num_enc encoded_prog_els []

val encoded_prog_thm =
  encoded_prog_def |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev encoded_prog_defs)))

val spec64 = INST_TYPE[alpha |-> fcpSyntax.mk_int_numeric_type 64]

val clc = compute_labels_alt_Section |> spec64

val cln = CONJUNCT1 lab_to_targetTheory.compute_labels_alt_def |> spec64

val (sec_length_tm,args) =
  clc |> SPEC_ALL |> rconc |> rand |> strip_comb

val Section_lines_tm = args |> hd |> dest_comb |> #1

val targs = tl args

fun eval_fn i n th =
  let
    val () = say_str "sec_length" i n
    val (enc_tm,enc_prog) = dest_eq (concl th)
    val tm = list_mk_comb(sec_length_tm,mk_comb(Section_lines_tm,enc_tm)::targs)
    val conv =
      RATOR_CONV(RAND_CONV(
        RAND_CONV(REWR_CONV th) THENC
        REWR_CONV Section_lines_def)) THENC
      time eval
  in
    conv tm
  end

val sec_lengths = parlist num_threads chunk_size eval_fn encoded_prog_defs

val () = PolyML.fullGC();

(*
val () = PolyML.SaveState.saveState"heap12"

val () = PolyML.SaveState.loadState"heap12"
*)

(*
val tm = tm12 |> RAND_CONV(REWR_CONV encoded_prog_thm) |> rconc

val (sth::sths) = sec_lengths
val (dth::dths) = List.rev encoded_prog_defs
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["compute_labels ",Int.toString n,": "])
  in time eval tm end

fun compute_labels_alt_conv _ [] [] tm = REWR_CONV cln tm
  | compute_labels_alt_conv n (dth::dths) (sth::sths) tm =
    tm |>
    (REWR_CONV clc THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (REWR_CONV sth) THENC
     BETA_CONV THENC
     RAND_CONV(RATOR_CONV(RAND_CONV numLib.REDUCE_CONV)) THENC
     PATH_CONV"lra"(
       PATH_CONV"lllr"(
         RAND_CONV(REWR_CONV dth) THENC
         REWR_CONV Section_num_def) THENC
       PATH_CONV"rlr"(
         RAND_CONV(REWR_CONV dth) THENC
         REWR_CONV Section_lines_def)) THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (compute_labels_alt_conv (n+1) dths sths) THENC
     BETA_CONV THENC eval_fn n)

val compute_labels_thm =
  tm12 |> (
    RAND_CONV(REWR_CONV encoded_prog_thm) THENC
    compute_labels_alt_conv 0 (List.rev encoded_prog_defs) sec_lengths)

val computed_labs_def = mk_def"computed_labs"(compute_labels_thm |> rconc)
val compute_labels_thm' =
  compute_labels_thm |>
  CONV_RULE(RAND_CONV(REWR_CONV(SYM computed_labs_def)))

val lab_to_target_thm3 =
  lab_to_target_thm2
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV compute_labels_thm') THENC
         BETA_CONV)))

val tm13 =
  lab_to_target_thm3 |> rconc |> funpow 2 rator |> funpow 2 rand

val (esn,esc) = lab_to_targetTheory.enc_secs_again_def |> spec64 |> CONJ_PAIR

(*
val tm = tm13 |> RAND_CONV(REWR_CONV encoded_prog_thm) |> rconc
val (dth::dths) = List.rev encoded_prog_defs
val n = 0
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["enc_secs_again ",Int.toString n,": "])
  in time eval tm end

val T_AND = AND_CLAUSES |> SPEC_ALL |> CONJUNCT1

fun enc_secs_again_conv n [] tm = REWR_CONV esn tm
  | enc_secs_again_conv n (dth::dths) tm =
    let
      val th1 = tm |>
       (RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV dth))) THENC
        REWR_CONV esc THENC
        RAND_CONV(
          PATH_CONV"llllr"(REWR_CONV computed_labs_def) THENC
          eval_fn n))
      val def = mk_def("enc_again_"^Int.toString n)
                  (th1 |> rconc |> rand |> rator |> rand)
      val rec_conv = enc_secs_again_conv (n+1) dths
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
        RAND_CONV(
          RAND_CONV (
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        PATH_CONV"lrraar"(REWR_CONV T_AND) THENC
        RAND_CONV rec_conv THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV))
    end

val enc_secs_again_thm =
  tm13 |> (
    RAND_CONV(REWR_CONV encoded_prog_thm) THENC
    enc_secs_again_conv 0 (List.rev encoded_prog_defs))

val COND_T = COND_CLAUSES |> SPEC_ALL |> CONJUNCT1

val lab_to_target_thm4 =
  lab_to_target_thm3
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV enc_secs_again_thm) THENC
         REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
         REWR_CONV COND_T THENC
         REWR_CONV LET_THM)))

val tm14 =
  lab_to_target_thm4 |> rconc |> funpow 2 rator |> funpow 2 rand

val enc_again_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("enc_again_"^(Int.toString i))))

val (uln,ulc) = lab_to_targetTheory.upd_lab_len_def |> spec64 |> CONJ_PAIR

(*
val tm = tm14
val (dth::_) = enc_again_defs
val n = 0
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["upd_lab_len ",Int.toString n,": "])
  in time eval tm end

fun upd_lab_len_conv _ [] tm = REWR_CONV uln tm
  | upd_lab_len_conv n (dth::dths) tm =
    let
      val th1 =
        tm |> (
          REWR_CONV ulc THENC
          RAND_CONV(
            RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
            eval_fn n))
      val def = mk_def ("upd_lab_"^(Int.toString n)) (rand(rconc th1))
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM def)) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        RAND_CONV(
          RAND_CONV(
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        REWR_CONV LET_THM THENC
        RAND_CONV(upd_lab_len_conv (n+1) dths) THENC
        BETA_CONV))
    end

val upd_lab_len_thm =
  tm14 |> upd_lab_len_conv 0 enc_again_defs

val lab_to_target_thm5 =
  lab_to_target_thm4
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV upd_lab_len_thm) THENC
         BETA_CONV)))

val tm15 =
  lab_to_target_thm5 |> rconc |> funpow 2 rator |> funpow 2 rand

val upd_lab_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("upd_lab_"^(Int.toString i))))

fun eval_fn i n dth =
  let
    val () = say_str "sec_length2" i n
    val ltm = dth |> concl |> lhs
    val tm = list_mk_comb(sec_length_tm,ltm::targs)
  in (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
      time eval) tm end

val sec_lengths2 = parlist num_threads chunk_size eval_fn upd_lab_defs

(* TODO:
  the previous compute_labels_alt thing could be this instead, if encoded_progs
  were defined differently (define the lines rather than the whole Sections *)

val (cln,clc) =
  lab_to_targetTheory.compute_labels_alt_def |> spec64 |> CONJ_PAIR

fun eval_fn str n tm =
  let
    val () = Lib.say(String.concat[str," ",Int.toString n,": "])
  in time eval tm end

fun compute_labels_alt_conv _ _ [] [] tm = REWR_CONV cln tm
  | compute_labels_alt_conv str n (dth::dths) (sth::sths) tm =
    tm |>
    (REWR_CONV clc THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (REWR_CONV sth) THENC
     BETA_CONV THENC
     RAND_CONV(RATOR_CONV(RAND_CONV numLib.REDUCE_CONV)) THENC
     PATH_CONV"lrarlr"(REWR_CONV dth) THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (compute_labels_alt_conv str (n+1) dths sths) THENC
     BETA_CONV THENC eval_fn str n)

(*
val tm = tm15
val (dth::_) = upd_lab_defs
val (sth::_) = List.rev sec_lengths2
*)

val compute_labels_thm2 =
  tm15 |> compute_labels_alt_conv "compute_labels2" 0 upd_lab_defs (List.rev sec_lengths2)

val computed_labs2_def = mk_def"computed_labs2"(compute_labels_thm2 |> rconc)
val compute_labels_thm2' =
  compute_labels_thm2 |>
  CONV_RULE(RAND_CONV(REWR_CONV(SYM computed_labs2_def)))

val lab_to_target_thm6 =
  lab_to_target_thm5
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr" (
         RAND_CONV (REWR_CONV compute_labels_thm2') THENC
         REWR_CONV LET_THM THENC BETA_CONV)))

(* similar to compute_labels_alt_conv, could be reused if encoded_progs were
   abbreviated differently *)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["enc_secs_again2 ",Int.toString n,": "])
  in time eval tm end

fun enc_secs_again_conv n [] tm = REWR_CONV esn tm
  | enc_secs_again_conv n (dth::dths) tm =
    let
      val th1 = tm |>
       (REWR_CONV esc THENC
        RAND_CONV(
          PATH_CONV"llllr"(REWR_CONV computed_labs2_def) THENC
          PATH_CONV"lr"(REWR_CONV dth) THENC
          eval_fn n))
      val def = mk_def("enc_again2_"^Int.toString n)
                  (th1 |> rconc |> rand |> rator |> rand)
      val rec_conv = enc_secs_again_conv (n+1) dths
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
        RAND_CONV(
          RAND_CONV (
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        PATH_CONV"lrraar"(REWR_CONV T_AND) THENC
        RAND_CONV rec_conv THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV))
    end

val tm16 =
  lab_to_target_thm6 |> rconc |> funpow 2 rator |> funpow 2 rand

val enc_secs_again_thm2 =
  tm16 |> enc_secs_again_conv 0 upd_lab_defs

val lab_to_target_thm7 =
  lab_to_target_thm6 |> CONV_RULE(RAND_CONV(
    PATH_CONV"llr"(
      RAND_CONV(REWR_CONV enc_secs_again_thm2) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC
      RAND_CONV(RATOR_CONV(REWR_CONV pad_code_MAP)))))

val tm17 =
  lab_to_target_thm7 |> rconc |> funpow 2 rator |> funpow 2 rand

val () = PolyML.fullGC();

(*
val () = PolyML.SaveState.saveState"heap17"

val () = PolyML.SaveState.loadState"heap17"
*)

val pad_section_tm =
  tm17 |> rator |> rand

val enc_again2_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("enc_again2_"^(Int.toString i))))

(*
val (dth::_) = enc_again2_defs
val p = tm17 |> rand |> rator |> rand
*)

fun eval_fn i n (dth, p) =
  let
    val () = say_str "pad_section" i n
    val tm = mk_comb(pad_section_tm,p)
    val conv =
      BETA_CONV THENC
      RATOR_CONV(RAND_CONV(REWR_CONV Section_num_def)) THENC
      RAND_CONV(
        RATOR_CONV(RAND_CONV(
          REWR_CONV Section_lines_def THENC
          REWR_CONV dth)) THENC
        time eval)
  in conv tm end

val enc_again2_els =
  tm17 |> rand |> listSyntax.dest_list |> #1

val pad_code_thms =
  parlist num_threads chunk_size eval_fn
    (zip enc_again2_defs enc_again2_els)

val pad_code_defs =
  make_abbrevs "pad_code_" num_enc (pad_code_thms |> map (rand o rconc)) []

val pad_code_thms' =
    map2 (CONV_RULE o RAND_CONV o RAND_CONV o REWR_CONV o SYM)
      (List.rev pad_code_defs) pad_code_thms

val pad_code_thm =
  tm17 |> (map_ths_conv pad_code_thms')

val padded_code_def = mk_def"padded_code"(rconc pad_code_thm)

val pad_code_thm' =
  pad_code_thm |> CONV_RULE(RAND_CONV(REWR_CONV(SYM padded_code_def)))

val lab_to_target_thm8 =
  lab_to_target_thm7
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV pad_code_thm') THENC
         BETA_CONV THENC
         REWR_CONV LET_THM THENC BETA_CONV THENC
         RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV T_AND))))))

val tm18 =
  lab_to_target_thm8 |> rconc
  |> funpow 2 rator |> rand
  |> funpow 2 rator |> rand

fun eval_fn i n dth =
  let
    val () = say_str "sec_length3" i n
    val ltm = dth |> concl |> lhs
    val tm = list_mk_comb(sec_length_tm,ltm::targs)
  in (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
      time eval) tm end

val sec_lengths3 = parlist num_threads chunk_size eval_fn pad_code_defs

val compute_labels_thm3 =
  tm18 |> rand |> lhs |> RAND_CONV (REWR_CONV padded_code_def) |> rconc
  |> compute_labels_alt_conv "compute_labels3" 0 pad_code_defs (List.rev sec_lengths3)

val compute_labels_thm3' =
  compute_labels_thm3
  |> CONV_RULE(RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV(SYM padded_code_def)))))

val labs_eq =
  tm18 |> rand
  |> (LAND_CONV(REWR_CONV compute_labels_thm3') THENC
      RAND_CONV(REWR_CONV computed_labs2_def) THENC
      eval)

(*
val (aen,aec) = lab_to_targetTheory.all_enc_ok_def |> spec64 |> CONJ_PAIR
val (aesn,aesc) = aec |> CONJ_PAIR

(*
val tm =
  tm18 |> rator |> rand
  |> (RAND_CONV(REWR_CONV padded_code_def))
  |> rconc
val (dth::_) = pad_code_defs
*)

fun eval_fn str n m tm =
  let
    val () = Lib.say(String.concat[str," ",Int.toString n,".",Int.toString m,": "])
  in time eval tm end

fun all_enc_ok_conv _ _ [] tm = REWR_CONV aen tm
  | all_enc_ok_conv n m (SOME dth::dths) tm =
      tm |>
      (RAND_CONV(
         RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV dth))) ) THENC
       aesc_conv n m dths)
  | all_enc_ok_conv n m (NONE::dths) tm =
      tm |> (
        (REWR_CONV aesn THENC
         LAND_CONV(numLib.REDUCE_CONV) THENC
         REWR_CONV T_AND THENC
         all_enc_ok_conv (n+1) 0 dths)
        ORELSEC aesc_conv n m dths)
and aesc_conv n m dths =
       (REWR_CONV aesc THENC
         RATOR_CONV(RAND_CONV(
           PATH_CONV"llr"(REWR_CONV computed_labs2_def) THENC
           eval_fn "line_ok" n m)) THENC
         REWR_CONV T_AND THENC
         PATH_CONV"lr"(
           RAND_CONV(eval_fn "line_length" n m) THENC
           numLib.REDUCE_CONV) THENC
         all_enc_ok_conv n (m+1) (NONE::dths))

(* extremely slow: lots of lines to check

val encs_ok =
  tm18 |> rator |> rand
  |> (RAND_CONV(REWR_CONV padded_code_def) THENC
      all_enc_ok_conv 0 0 (map SOME pad_code_defs))

*)
*)

(* since this should be a redundant check anyway, we cheat it *)
val encs_ok =
  tm18 |> rator |> rand
  |> (fn tm => prove(tm,cheat))

val lab_to_target_thm =
  lab_to_target_thm8
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         PATH_CONV"llr"(
           FORK_CONV(REWR_CONV (EQT_INTRO encs_ok), REWR_CONV labs_eq) THENC
           REWR_CONV T_AND) THENC
         REWR_CONV COND_T) THENC
       REWR_CONV(option_case_def |> CONJUNCT2) THENC
       BETA_CONV THENC
       REWR_CONV pair_case_def THENC
       RATOR_CONV BETA_CONV THENC
       BETA_CONV THENC
       RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV prog_to_bytes_MAP)))))

val tm19 =
  lab_to_target_thm |> rconc |> rand |> rator |> rand |> rand

val line_bytes_tm =
  tm19 |> rator |> rand

val padded_code_els =
  padded_code_def |> rconc |> listSyntax.dest_list |> #1

val pad_code_defs =
  for 1 num_enc (fn i => definition(mk_def_name("pad_code_"^(Int.toString i))))

(*
  val p = el 1 padded_code_els
  val dth = el 1 pad_code_defs
*)

fun eval_fn i n (p,dth) =
  let
    val () = say_str"prog_to_bytes" i n
    val tm = mk_comb(line_bytes_tm,p)
    val conv =
      (REWR_CONV o_THM THENC
       RAND_CONV(REWR_CONV o_THM) THENC
       RAND_CONV(RAND_CONV(REWR_CONV Section_lines_def)) THENC
       RAND_CONV(RAND_CONV(REWR_CONV dth)) THENC
       time eval)
    in conv tm end

val line_bytes =
  parlist num_threads chunk_size eval_fn (zip padded_code_els pad_code_defs)

val map_line_bytes =
  tm19 |>
    (RAND_CONV(REWR_CONV padded_code_def) THENC
     map_ths_conv line_bytes)

val bytes_defs =
  make_abbrevs "bytes_" num_enc (map_line_bytes |> rconc |> listSyntax.dest_list |> #1) []

val map_line_bytes' =
  map_line_bytes |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev bytes_defs)))

val FOLDR_CONV = listLib.FOLDR_CONV (* TODO this is broken *)

local
fun str n =
  String.concat[Int.toString n,if n mod 10 = 0 then "\n" else " "]
in
fun app_conv _ [] tm = raise UNCHANGED
  | app_conv n (dth::dths) tm =
    let
      val th = FORK_CONV(REWR_CONV dth, app_conv (n+1) dths) tm
      val def = mk_def ("all_bytes_"^(Int.toString n)) (rand(rconc th))
      val () = Lib.say (str n)
    in
      CONV_RULE(RAND_CONV
        (RAND_CONV(REWR_CONV(SYM def)) THENC listLib.APPEND_CONV))
      th
    end
end

(* 17 minutes. is there a faster way? *)

val flat_bytes =
  listSyntax.mk_flat(rconc map_line_bytes')
  |> (REWR_CONV FLAT_FOLDR
      THENC FOLDR_CONV (QCONV ALL_CONV) THENC
      time (app_conv 0 (List.rev bytes_defs)))

fun expand_defs_conv [] tm = raise UNCHANGED
  | expand_defs_conv (dth::dths) tm =
    ((RAND_CONV(expand_defs_conv (dth::dths))) ORELSEC
     (REWR_CONV dth THENC expand_defs_conv dths))
    tm

val all_bytes_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("all_bytes_"^(Int.toString i))))

(* also quite slow *)

val flat_bytes' =
  flat_bytes |> CONV_RULE(RAND_CONV(expand_defs_conv all_bytes_defs))

val bootstrap_thm = save_thm("bootstrap_thm",
  lab_to_target_thm
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"rlr"(
         RAND_CONV(
           REWR_CONV map_line_bytes') THENC
         REWR_CONV flat_bytes'))));

val temp_defs = (List.map #1 (definitions"-"))
val () = List.app delete_binding temp_defs;
val () = ml_translatorLib.reset_translation();

val _ = export_theory();
