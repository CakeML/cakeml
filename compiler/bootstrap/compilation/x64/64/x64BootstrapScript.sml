open preamble to_lab_x64BootstrapTheory compilationLib

val _ = new_theory "x64Bootstrap";

val () = ml_translatorLib.reset_translation();

(*
  val lab_prog_def =
    let
      val (ls,ty) = to_lab_x64BootstrapTheory.lab_prog_def |> rconc |> listSyntax.dest_list
      val ls' = listSyntax.mk_list(List.take(List.drop(ls,2000),40),ty)
    in mk_thm([],``lab_prog = ^ls'``) end
*)

val stack_mb = 1000
val heap_mb = 1000
val filename = "cake.S"

val bootstrap_thm =
  compilationLib.cbv_to_bytes_x64
    x64_backend_config_def
    stack_to_lab_thm lab_prog_def
    heap_mb stack_mb "cake_code" "cake_data" "cake_config" filename;

val cake_compiled = save_thm("cake_compiled", bootstrap_thm);

(* avoid saving the long list of bytes in the Theory.sml file
   they can only be found in the exported cake.S file *)
val _ = Theory.delete_binding "cake_code_def";

val _ = export_theory();

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
