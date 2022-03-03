(*
  Encoding of compiler state
*)
open preamble backend_enc_decTheory x64BootstrapTheory;

val _ = new_theory "x64_config_enc";

val confs = LIST_CONJ
  [to_dataBootstrapTheory.flat_conf_def,
   to_dataBootstrapTheory.bvl_conf_def,
   to_dataBootstrapTheory.bvi_conf_def]

val encode_backend_config_cake_config_lemma =
  “encode_backend_config cake_config”
  |> (SIMP_CONV (srw_ss()) [cake_config_def,confs,encode_backend_config_def] THENC EVAL);

Definition config_enc_str_def:
  config_enc_str = ^(encode_backend_config_cake_config_lemma |> concl |> rand)
End

Theorem encode_backend_config_cake_config =
  encode_backend_config_cake_config_lemma
  |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM config_enc_str_def)));

val _ = let
  val filename = "config_enc_str.txt"
  val str = config_enc_str_def |> concl |> rand |> stringSyntax.fromHOLstring
  val n = size str
  fun nice_size_str n =
    if n < 1024 then int_to_string n ^ " bytes" else
    if n < 1024 * 1024 then int_to_string (n div 1024) ^ " kilobytes" else
      int_to_string (n div (1024 * 1024)) ^ " megabytes"
  val _ = print ("Writing " ^ nice_size_str n ^ " to " ^ filename ^ " .. ")
  val f = TextIO.openOut filename
  val _ = TextIO.output(f,str)
  val _ = TextIO.closeOut f
  val _ = print "done.\n"
  in () end;

val _ = export_theory();
