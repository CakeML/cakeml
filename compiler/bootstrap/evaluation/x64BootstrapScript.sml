open preamble bootstrapLib
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

val () = Globals.max_print_depth := 10;
val () = ml_translatorLib.reset_translation();

val cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset [
    computeLib.Extenders [
      basicComputeLib.add_basic_compset,
      compilerComputeLib.add_compiler_compset,
      asmLib.add_asm_compset,
      x64_targetLib.add_x64_encode_compset],
    computeLib.Defs [x64_configTheory.x64_compiler_config_def]
  ] cs
val eval = computeLib.CBV_CONV cs;

val bare_cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset[computeLib.Extenders[compilerComputeLib.add_compiler_compset]] bare_cs
val bare_eval = computeLib.CBV_CONV bare_cs

val chunk_size = 50
val num_threads = 8
fun say_str s i n = ()
(*
  Lib.say(String.concat["eval ",s,": chunk ",Int.toString i,": el ",Int.toString n,": "])
*)

(*
  val lab_prog_def =
    let
      val (ls,ty) = to_lab_x64BootstrapTheory.lab_prog_def |> rconc |> listSyntax.dest_list
      val ls' = listSyntax.mk_list(List.take(List.drop(ls,2000),40),ty)
    in mk_thm([],``lab_prog = ^ls'``) end
*)

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
  in (*time*) eval tm end

val ths = time_with_size thms_size "filter_skip (par)" (parlist num_threads chunk_size eval_fn) lab_prog_els;

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

(* could parallelise? *)
val ffi_limit_thm =
  ``find_ffi_index_limit skip_prog``
  |> (RAND_CONV(REWR_CONV skip_prog_def) THENC timez "ffi_limit" eval)

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
   PATH_CONV"llr"eval)

val tm11 = remove_labels_thm0 |> rconc |> rand

val enc_sec_tm = tm11 |> rator |> rand

val skip_prog_els = skip_prog_def |> rconc |> listSyntax.dest_list |> #1

fun eval_fn i n p =
  let
    val () = say_str "enc_sec" i n
    val tm = mk_comb(enc_sec_tm,p)
  in (*time*) eval tm end

(* evaluate encoder (can be slow?) *)

val ths = time_with_size thms_size "enc_sec (par)" (parlist num_threads chunk_size eval_fn) skip_prog_els;

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

val encoded_prog_els =
  encoded_prog_def |> rconc |> listSyntax.dest_list |> #1

val encoded_prog_lines = encoded_prog_els |> map rand

val num_enc = length encoded_prog_els
val encoded_prog_defs = make_abbrevs "encoded_prog_el" num_enc encoded_prog_lines []

val Section_encoded_prog_defs =
  map2 AP_TERM (map rator encoded_prog_els) (List.rev encoded_prog_defs)

val encoded_prog_thm =
  encoded_prog_def |>
      CONV_RULE(RAND_CONV(intro_abbrev Section_encoded_prog_defs))

(*
val ls = encoded_prog_def |> rconc |> listSyntax.dest_list |> #1
fun test n = (rconc (el n Section_encoded_prog_defs)) = (el n ls)
val fails = List.filter (not o test) (List.tabulate(3292,fn i => i+1))
*)

val spec64 = INST_TYPE[alpha |-> fcpSyntax.mk_int_numeric_type 64]

val (cln,clc) =
  lab_to_targetTheory.compute_labels_alt_def |> spec64 |> CONJ_PAIR

fun compute_labels_alt_rule [] th = th |> CONV_RULE (RAND_CONV (REWR_CONV cln))
  | compute_labels_alt_rule (dth::dths) th =
    let
      val th1 = th |> CONV_RULE (
        RAND_CONV (
          REWR_CONV clc THENC
          RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC eval) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          RAND_CONV eval))
    in compute_labels_alt_rule dths th1 end

(*
val (dth::dths) = List.rev encoded_prog_defs
*)

val compute_labels_thm =
  tm12 |> timez "compute_labels" (fn tm =>
    let
      val th = RATOR_CONV(RAND_CONV(REWR_CONV encoded_prog_thm)) tm
    in compute_labels_alt_rule (List.rev encoded_prog_defs) th end)

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

val (dth::dths) = dths
val n = n+1
val tm = rand (rconc it)
*)

val (COND_T,COND_F) = COND_CLAUSES |> SPEC_ALL |> CONJ_PAIR;

val (T_AND::AND_T::_) = AND_CLAUSES |> SPEC_ALL |> CONJUNCTS;

val [ela1,ela2,ela3,ela4] = CONJUNCTS lab_to_targetTheory.enc_lines_again_def;

val add_pos_conv = PATH_CONV "lllr" numLib.REDUCE_CONV;

(*
val Label_tm  = ela2 |> SPEC_ALL |> concl |> lhs |> rator |> rand |> rator |> rand |> repeat rator;
val Asm_tm    = ela3 |> SPEC_ALL |> concl |> lhs |> rator |> rand |> rator |> rand |> repeat rator;
val LabAsm_tm = ela4 |> SPEC_ALL |> concl |> lhs |> rator |> rand |> rator |> rand |> repeat rator;

fun enc_lines_again_rule labs_def =
let
  fun f th = let
    val ls = th |> rconc |> rator |> rand
  in if listSyntax.is_nil ls then
    CONV_RULE(RAND_CONV (REWR_CONV ela1 THENC RATOR_CONV(RAND_CONV eval))) th
  else let
    val tm = listSyntax.dest_cons ls |> #1 |> repeat rator
    val th =
      if same_const Label_tm tm then
        CONV_RULE(RAND_CONV (REWR_CONV ela2 THENC add_pos_conv)) th
      else if same_const Asm_tm tm then
        CONV_RULE(RAND_CONV (REWR_CONV ela3 THENC add_pos_conv)) th
      else
      let
        val _ = assert (same_const LabAsm_tm) tm
        val th = CONV_RULE(RAND_CONV (
          REWR_CONV ela4 THENC
          RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV labs_def)) THENC eval) THENC
          REWR_CONV LET_THM THENC BETA_CONV THENC
          RATOR_CONV(RATOR_CONV(RAND_CONV eval)))) th
        val tm = th |> rconc |> rator |> rator |> rand
      in
        if same_const T tm then
        CONV_RULE(RAND_CONV (REWR_CONV COND_T THENC add_pos_conv)) th
        else (assert (same_const F) tm;
        CONV_RULE(RAND_CONV (REWR_CONV COND_F THENC
         RAND_CONV eval THENC REWR_CONV LET_THM THENC BETA_CONV THENC
         RAND_CONV eval THENC REWR_CONV LET_THM THENC BETA_CONV THENC
         add_pos_conv THENC
         RAND_CONV(RAND_CONV(RAND_CONV eval THENC REWR_CONV AND_T)))) th)
      end
    in
      f th
    end
  end
in f end
*)

(*
fun enc_lines_again_rule labs_def =
let
  fun f th =
    let
      val (th,b) =
        (* Asm *)
        (CONV_RULE(RAND_CONV (REWR_CONV ela3 THENC add_pos_conv)) th,true)
        handle HOL_ERR _ =>
        (* Label *)
        (CONV_RULE(RAND_CONV (REWR_CONV ela2 THENC add_pos_conv)) th,true)
        handle HOL_ERR _ =>
        (* LabAsm *)
        let
          val th = CONV_RULE(RAND_CONV (
            REWR_CONV ela4 THENC
            RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV labs_def)) THENC eval) THENC
            let_CONV THENC
            RATOR_CONV(RATOR_CONV(RAND_CONV eval)))) th
        in
          (* no offset update *)
          (CONV_RULE(RAND_CONV (REWR_CONV COND_T THENC add_pos_conv)) th,true)
          handle HOL_ERR _ =>
          (* offset update *)
          (CONV_RULE(RAND_CONV (REWR_CONV COND_F THENC
           RAND_CONV eval THENC let_CONV THENC
           RAND_CONV eval THENC let_CONV THENC
           add_pos_conv THENC
           RAND_CONV(RAND_CONV(RAND_CONV eval THENC REWR_CONV AND_T)))) th,true)
        end
        handle HOL_ERR _ =>
        (* nil *)
        (CONV_RULE(RAND_CONV (REWR_CONV ela1 THENC RATOR_CONV(RAND_CONV eval))) th,false)
    in if b then f th else th end
in f end

fun enc_lines_again_conv labs_def = enc_lines_again_rule labs_def o REFL
*)

(*
fun enc_lines_again_conv labs_def tm = tm |> (
  IFC
  ((REWR_CONV ela3 THENC add_pos_conv) ORELSEC
   (REWR_CONV ela2 THENC add_pos_conv) ORELSEC
   (REWR_CONV ela4 THENC
    RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV labs_def)) THENC eval) THENC
    let_CONV THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
    ((REWR_CONV COND_T THENC add_pos_conv) ORELSEC
     (REWR_CONV COND_F THENC
      RAND_CONV eval THENC let_CONV THENC
      RAND_CONV eval THENC let_CONV THENC
      add_pos_conv THENC
      RAND_CONV(RAND_CONV(RAND_CONV eval THENC REWR_CONV AND_T))))))
  (enc_lines_again_conv labs_def)
  (REWR_CONV ela1 THENC RATOR_CONV(RAND_CONV eval)))
*)

(*
fun enc_lines_again_conv labs_def tm = tm |> (
  IFC
  ((REWR_CONV ela3) ORELSEC
   (REWR_CONV ela2) ORELSEC
   (REWR_CONV ela4 THENC
    RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV labs_def)) THENC eval) THENC
    let_CONV THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
    ((REWR_CONV COND_T) ORELSEC
     (REWR_CONV COND_F THENC
      RAND_CONV eval THENC let_CONV THENC
      RAND_CONV eval THENC let_CONV))))
  (enc_lines_again_conv labs_def)
  (REWR_CONV ela1 THENC eval))
*)

(*
fun enc_lines_again_conv tm = tm |> (
  IFC
  ((REWR_CONV ela3) ORELSEC
   (REWR_CONV ela2) ORELSEC
   (REWR_CONV ela4 THENC
    RAND_CONV eval THENC let_CONV THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
    ((REWR_CONV COND_T) ORELSEC
     (REWR_CONV COND_F THENC
      RAND_CONV eval THENC let_CONV THENC
      RAND_CONV eval THENC let_CONV))))
  (enc_lines_again_conv)
  (REWR_CONV ela1 THENC eval))
*)

(*
fun enc_lines_again_conv tm = tm |> (
  IFC
  ((REWR_CONV ela3) ORELSEC
   (REWR_CONV ela2) ORELSEC
   (REWR_CONV ela4 THENC
    RAND_CONV eval THENC let_CONV THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
    COND_CONV THENC
    TRY_CONV
    (RAND_CONV eval THENC let_CONV THENC
     RAND_CONV eval THENC let_CONV)))
  (enc_lines_again_conv)
  (REWR_CONV ela1 THENC eval))
*)

(*
fun enc_lines_again_conv tm = tm |> (
  IFC
  ((REWR_CONV ela3) ORELSEC
   (REWR_CONV ela2) ORELSEC
   (REWR_CONV ela4 THENC
    RAND_CONV eval THENC let_CONV THENC
    RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
    COND_CONV THENC REPEATC let_CONV))
  (enc_lines_again_conv)
  (REWR_CONV ela1 THENC eval))
*)

fun enc_secs_again_conv str ela_conv n [] tm = REWR_CONV esn tm
  | enc_secs_again_conv str ela_conv n (dth::dths) tm =
    let
      val th1 = tm |>
       (REWR_CONV esc THENC
        RAND_CONV(
          RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
          ela_conv))
      val def = mk_def(str^Int.toString n)
                  (th1 |> rconc |> rand |> rator |> rand)
      val () = print (String.concat[Int.toString n," "])
      val rec_conv = enc_secs_again_conv str ela_conv (n+1) dths
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        let_CONV THENC
        RAND_CONV rec_conv THENC
        let_CONV THENC
        RAND_CONV(REWR_CONV T_AND)))
    end

val enc_secs_again_thm =
  tm13 |> timez "enc_secs_again" (
    RAND_CONV(REWR_CONV encoded_prog_thm) THENC
    enc_secs_again_conv
      "enc_again_"
      (* (enc_lines_again_conv computed_labs_def) *)
      (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC eval)
      0
      (List.rev encoded_prog_defs))

(*
val encoded_prog_thm_prefix =
  let
    val (car,cdr) = dest_comb (concl encoded_prog_thm)
    val (ls,ty) = listSyntax.dest_list cdr
    val ls' = List.take(ls,10)
  in mk_thm([],mk_comb(car,listSyntax.mk_list(ls',ty))) end
val encoded_prog_defs_prefix =
  List.take(List.rev encoded_prog_defs,10)

(* rule using exceptions *)
val enc_secs_again_thm =
  tm13 |> timez "enc_secs_again" (
    RAND_CONV(REWR_CONV encoded_prog_thm_prefix) THENC
    enc_secs_again_conv
      "enc_again_" (enc_lines_again_conv computed_labs_def) 0
      encoded_prog_defs_prefix)
2m15s

(* custom conv *)
val enc_secs_again_thm =
  tm13 |> timez "enc_secs_again" (
    RAND_CONV(REWR_CONV encoded_prog_thm_prefix) THENC
    enc_secs_again_conv
      "enc_again_" (enc_lines_again_conv computed_labs_def) 0
      encoded_prog_defs_prefix)
2m17s

(* custom conv with IFC *)
val enc_secs_again_thm =
  tm13 |> timez "enc_secs_again" (
    RAND_CONV(REWR_CONV encoded_prog_thm_prefix) THENC
    enc_secs_again_conv
      "enc_again_" (enc_lines_again_conv computed_labs_def) 0
      encoded_prog_defs_prefix)
2m18s

val enc_secs_again_thm =
  tm13 |> timez "enc_secs_again" (
    RAND_CONV(REWR_CONV encoded_prog_thm_prefix) THENC
    enc_secs_again_conv
      "enc_again_"
      (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC eval)
      0
      encoded_prog_defs_prefix)
14.4s

val (dth::dths) = encoded_prog_defs_prefix
val tm = tm13 |> RAND_CONV(REWR_CONV encoded_prog_thm_prefix) |> rconc
val th1 = tm |> (REWR_CONV esc THENC (RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV dth)))))
val tm = th1 |> rconc |> rand

val test1 =
  time (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC eval) tm
1.1s

val th = REFL tm

(* rule with exceptions *)
val test2 =
  time (enc_lines_again_conv computed_labs_def) tm
17.1s
val check = rconc test1 = rconc test2

(* custom conv with IFC *)
val test3 =
  time (enc_lines_again_conv computed_labs_def) tm
30.6s
val check = rconc test1 = rconc test3

(* custom conv with IFC and delayed leaves *)
val test4 =
  time (enc_lines_again_conv computed_labs_def) tm
31.3s
val check = rconc test1 = rconc test4

(* custom conv with labs expanded *)
val test5 =
  time (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC enc_lines_again_conv) tm
21.2s
val check = rconc test1 = rconc test5

(* custom conv with labs expanded using COND_CONV *)
val test6 =
  time (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC enc_lines_again_conv) tm
19.4s
val check = rconc test1 = rconc test6

(* custom conv with labs expanded using COND_CONV and deferring all computations *)
val test7 =
  time (PATH_CONV "llllr" (REWR_CONV computed_labs_def) THENC enc_lines_again_conv) tm
19.6s
val check = rconc test1 = rconc test7

*)

(*
  drop 2000 take 5 = 3.8s
  drop 2000 take 10 = 3.9s
  drop 2000 take 20 = 4.5s
  drop 2000 take 40 = 8.0s
*)

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

val [lul1,lul2,lul3,lul4] = CONJUNCTS lab_to_targetTheory.lines_upd_lab_len_def;

val add_pos_conv = PATH_CONV "llr" numLib.REDUCE_CONV

fun lines_upd_lab_len_rule th =
  CONV_RULE(RAND_CONV (REWR_CONV lul1 THENC RATOR_CONV(RAND_CONV eval))) th
  handle HOL_ERR _ =>
  let
    val th =
    CONV_RULE(RAND_CONV (REWR_CONV lul2 THENC
      RAND_CONV eval THENC REWR_CONV LET_THM THENC BETA_CONV THENC
      add_pos_conv)) th
    handle HOL_ERR _ =>
    CONV_RULE(RAND_CONV (REWR_CONV lul3 THENC add_pos_conv)) th
    handle HOL_ERR _ =>
    CONV_RULE(RAND_CONV (REWR_CONV lul4 THENC add_pos_conv)) th
  in lines_upd_lab_len_rule th end

val lines_upd_lab_len_conv = lines_upd_lab_len_rule o REFL

(*
val tm = tm14
val (dth::_) = enc_again_defs
val n = 0
*)

fun upd_lab_len_conv _ [] tm = REWR_CONV uln tm
  | upd_lab_len_conv n (dth::dths) tm =
    let
      val th1 =
        tm |> (
          REWR_CONV ulc THENC
          RAND_CONV(
            RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
            lines_upd_lab_len_conv))
      val def = mk_def ("upd_lab_"^(Int.toString n)) (rand(rator(rand(rconc th1))))
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
        REWR_CONV LET_THM THENC
        RAND_CONV(upd_lab_len_conv (n+1) dths) THENC
        BETA_CONV))
    end

val upd_lab_len_thm =
  tm14 |> timez "upd_lab_len" (upd_lab_len_conv 0 enc_again_defs)

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

val compute_labels_thm2 =
  tm15 |> timez "compute_labels2" (compute_labels_alt_rule upd_lab_defs o REFL)

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

val tm16 =
  lab_to_target_thm6 |> rconc |> funpow 2 rator |> funpow 2 rand

val enc_secs_again_thm2 =
  tm16 |> timez "enc_secs_again2" (enc_secs_again_conv
    "enc_again2_"
    (*(enc_lines_again_conv computed_labs2_def)*)
    (PATH_CONV "llllr" (REWR_CONV computed_labs2_def) THENC eval)
    0
    upd_lab_defs)

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
  for 0 (num_enc-1) (fn i => definition(mk_def_name("enc_again2_"^(Int.toString i))));

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
      RATOR_CONV(RAND_CONV(REWR_CONV labLangTheory.Section_num_def)) THENC
      RAND_CONV(
        RATOR_CONV(RAND_CONV(
          REWR_CONV labLangTheory.Section_lines_def THENC
          REWR_CONV dth)) THENC
        (*time*) eval)
  in conv tm end

val enc_again2_els =
  tm17 |> rand |> listSyntax.dest_list |> #1

val pad_code_thms =
  time_with_size thms_size "pad_section" (parlist num_threads chunk_size eval_fn)
    (zip enc_again2_defs enc_again2_els);

val pad_code_defs =
  make_abbrevs "pad_code_" num_enc (pad_code_thms |> map (rand o rconc)) [];

val pad_code_thms' =
    map2 (CONV_RULE o RAND_CONV o RAND_CONV o REWR_CONV o SYM)
      (List.rev pad_code_defs) pad_code_thms;

val pad_code_thm =
  tm17 |> (map_ths_conv pad_code_thms')

val padded_code_def = mk_def"padded_code"(rconc pad_code_thm);

val pad_code_thm' =
  pad_code_thm |> CONV_RULE(RAND_CONV(REWR_CONV(SYM padded_code_def)))

val lab_to_target_thm8 =
  lab_to_target_thm7
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV pad_code_thm') THENC
         BETA_CONV THENC
         RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV T_AND))))))

val tm18 =
  lab_to_target_thm8 |> rconc
  |> funpow 2 rator |> rand
  |> funpow 2 rator |> rand

val sec_ok_light_tm =
  tm18 |> rator |> rand

val line_ok_light_tm =
  lab_to_targetTheory.sec_ok_light_def
  |> ISPEC(rand sec_ok_light_tm)
  |> SPEC_ALL |> rconc |> rator |> rand

val padded_code_els =
  (padded_code_def |> rconc |> listSyntax.dest_list |> #1);

(*
fun abbrev_lines i th =
  let
    val prefix = String.concat["l",Int.toString i,"_"]
    val lines = th |> rconc |> listSyntax.dest_list |> #1
    val line_defs = make_abbrevs prefix (List.length lines) lines []
  in
    (line_defs,
     CONV_RULE(RAND_CONV(intro_abbrev (List.rev line_defs))) th)
  end

val line_defs_padded_code_defs =
  time (mapi abbrev_lines) pad_code_defs
*)

(*
fun prove_sec_ok i (p,d) =
  let
    val () = Lib.say(String.concat["sec_ok: ",Int.toString i,"\n"])
    fun eval_fn i n tm =
      mk_comb(line_ok_light_tm,tm) |> eval
    val ths = parlist num_threads chunk_size eval_fn
      (d |> rconc |> listSyntax.dest_list |> #1)
    val next_th = ref ths
    fun el_conv _ = case !next_th of h::t => h before next_th := t
    val conv = (
      REWR_CONV lab_to_targetTheory.sec_ok_light_def THENC
      RAND_CONV (REWR_CONV d) THENC
      listLib.ALL_EL_CONV el_conv)
  in
    time conv (mk_comb(sec_ok_light_tm, p))
  end
*)

fun eval_fn i n (p,d) =
  let
    val () = say_str"sec_ok" i n
    val conv = (
      REWR_CONV lab_to_targetTheory.sec_ok_light_def THENC
      RAND_CONV (REWR_CONV d) THENC
      listLib.ALL_EL_CONV eval)
    val tm = mk_comb(sec_ok_light_tm, p)
  in
    (*time*) conv tm
  end

(*
  val p = el 5 padded_code_els
  val d = el 5 pad_code_defs
*)

val pad_code_els_defs = zip padded_code_els pad_code_defs;

val secs_ok = time_with_size thms_size "sec_ok (par)" (parlist num_threads chunk_size eval_fn) pad_code_els_defs;

val all_secs_ok =
  time_with_size (term_size o concl) "all_secs_ok" (listLib.join_EVERY sec_ok_light_tm)
    (rev_itlist (cons o EQT_ELIM) secs_ok [])

(*
val tm =
  tm18 |> rator |> rand
  |> (RAND_CONV(REWR_CONV padded_code_def))
  |> rconc
val (dth::_) = pad_code_defs
*)

val encs_ok =
  tm18
  |> (RAND_CONV(REWR_CONV padded_code_def) THENC
      REWR_CONV (EQT_INTRO all_secs_ok))

val lab_to_target_thm =
  lab_to_target_thm8
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         PATH_CONV"llr"(
           REWR_CONV encs_ok) THENC
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
  for 1 num_enc (fn i => definition(mk_def_name("pad_code_"^(Int.toString i))));

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
       RAND_CONV(RAND_CONV(REWR_CONV labLangTheory.Section_lines_def)) THENC
       RAND_CONV(RAND_CONV(REWR_CONV dth)) THENC
       (*time*) eval)
    in conv tm end

val line_bytes =
  time_with_size thms_size "prog_to_bytes (par)" (parlist num_threads chunk_size eval_fn) (zip padded_code_els pad_code_defs);

val map_line_bytes =
  tm19 |>
    (RAND_CONV(REWR_CONV padded_code_def) THENC
     map_ths_conv line_bytes);

val bytes_defs =
  make_abbrevs "bytes_" num_enc (map_line_bytes |> rconc |> listSyntax.dest_list |> #1) [];

val map_line_bytes' =
  map_line_bytes |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev bytes_defs)));

local
fun str n =
  String.concat[Int.toString n,if n mod 10 = 0 then "\n" else " "]
in
fun app_conv _ [] tm = raise UNCHANGED
  | app_conv n (dth::dths) tm =
    let
      val th = FORK_CONV(REWR_CONV dth, app_conv (n+1) dths) tm
      val def = mk_def ("all_bytes_"^(Int.toString n)) (rand(rconc th))
      (* val () = Lib.say (str n) *)
    in
      CONV_RULE(RAND_CONV
        (RAND_CONV(REWR_CONV(SYM def)) THENC listLib.APPEND_CONV))
      th
    end
end

(* 36 minutes. is there a faster way? *)

val flat_bytes =
  listSyntax.mk_flat(rconc map_line_bytes')
  |> (REWR_CONV FLAT_FOLDR
      THENC listLib.FOLDR_CONV (QCONV ALL_CONV) THENC
      timez "flat_bytes" (app_conv 0 (List.rev bytes_defs)));

fun expand_defs_conv [] tm = raise UNCHANGED
  | expand_defs_conv (dth::dths) tm =
    ((RAND_CONV(expand_defs_conv (dth::dths))) ORELSEC
     (REWR_CONV dth THENC expand_defs_conv dths))
    tm

val all_bytes_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("all_bytes_"^(Int.toString i))));

(* also quite slow, 32 mins *)

val flat_bytes' =
  flat_bytes |> timez "expand_defs" (CONV_RULE(RAND_CONV(expand_defs_conv all_bytes_defs)));

val bootstrap_thm = save_thm("bootstrap_thm",
  lab_to_target_thm
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"rlr"(
         RAND_CONV(
           REWR_CONV map_line_bytes') THENC
         REWR_CONV flat_bytes'))));

val temp_defs = (List.map #1 (definitions"-"))
val () = List.app delete_binding temp_defs;

val stack_mb = 1000
val heap_mb = 1000
val filename = "cake.S"

val (bytes_tm,ffi_limit_tm) =
  bootstrap_thm |> rconc
  |> optionSyntax.dest_some
  |> pairSyntax.dest_pair

val () = Lib.say"Writing output: "

val () = time (
  x64_exportLib.write_cake_S stack_mb heap_mb
    (numSyntax.int_of_term ffi_limit_tm)
    bytes_tm ) filename

val _ = export_theory();
