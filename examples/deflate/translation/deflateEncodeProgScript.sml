(*
  Encoding program for the Deflate Encoder
*)
open preamble basis miscTheory lispProgTheory listTheory arithmeticTheory;
open deflateTheory deflateTableTheory rleTheory huffmanTheory LZSSTheory mlstringTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;

open mlstringTheory;

val _ = new_theory "deflateEncodeProg";

val _ = translation_extends "lispProg";

val _ = show_assums := true;

(* Standard functions *)
val res = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate REPLICATE;
val res = translate REVERSE_DEF;
val res = translate FOLDL;
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate BUTLASTN_def;
val res = translate FLAT;
val res = translate SNOC;
val res = translate GENLIST;
val res = translate IS_PREFIX;
val res = translate (PAD_RIGHT |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate (PAD_LEFT |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate ALOOKUP_def;
val res = translate AFUPDKEY_def;
val res = translate LUPDATE_DEF;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate QSORT_DEF;
val res = translate oEL_def;

(* DeflateTable *)
val res = translate dist_table_def;
val res = translate len_table_def;
val res = translate find_level_in_table_def;
val res = translate (find_level_in_len_table_def |> REWRITE_RULE [EVAL “HD len_table”]);
val res = translate (find_level_in_dist_table_def |> REWRITE_RULE [EVAL “HD dist_table”]);
val res = translate find_code_in_table_def;

(* Huffman *)
val res = translate get_freq_def;
val res = translate get_frequencies_def;
val res = translate sort_frequencies_def;
val res = translate convert_frequencies_def;
val res = translate create_tree_def;
val res = translate build_huffman_tree_def;
val res = translate get_huffman_codes_def;
val res = translate encode_single_huff_val_def;
val res = translate encode_huff_def;
val res = translate find_decode_match_def;
val res = translate huff_enc_dyn_def;
val res = translate gen_zero_codes_def;
val res = translate fill_assoc_list_def;
val res = translate complete_assoc_list_def;
val res = translate len_from_codes_def;
val res = translate all_lens_def;
val res = translate bl_count_aux_def;
val res = translate bl_count_def;
val res = translate next_code_aux_def;
val res = translate next_code_def;
val res = translate tbl2n_def;
val res = translate inv_tbl2n_def;
val res = translate pad0_def;
val res = translate canonical_codes_aux_def;
val res = translate canonical_codes_def;
val res = translate unique_huff_tree_def;

(* Run Length Encoding *)
val res = translate rle_table_def;
val res = translate rle0_table_def;
val res = translate (add_repetition_def |> REWRITE_RULE [EVAL “HD rle0_table”, GSYM sub_check_def]);
val res = translate find_repeat_def;
val res = translate (encode_rle_aux_def |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate encode_rle_def;
val res = translate decode_repeating_def;
val res = translate (decode_rle_aux_def |> REWRITE_RULE [GSYM sub_check_def]);

Triviality decode_rle_aux_ind:
  decode_rle_aux_ind
Proof
  once_rewrite_tac [fetch "-" "decode_rle_aux_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = decode_rle_aux_ind |> update_precondition;

val res = translate decode_rle_def;

(* LZSS *)
val res = translate matchLength_def;
val res = translate getMatch_def;
val res = translate (LZmatch_def |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate (LZcomp_def |> REWRITE_RULE [GSYM sub_check_def]);

Triviality lzcomp_ind:
  lzcomp_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "lzcomp_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = lzcomp_ind |> update_precondition;

val res = translate LZSS_compress_def;
val res = translate resolveLenDist_def;
val res = translate LZdecompress_def;
val res = translate LZSS_decompress_def;

(* Deflate *)
val res = translate fixed_len_tree_def;
val res = translate fixed_dist_tree_def;
val res = translate clen_position_def;
val res = translate encode_clen_pos_def;
val res = translate trim_zeroes_end_def;
val res = translate encode_clen_alph_def;
val res = translate find_LZSS_val_def;
val res = translate split_len_dist_def;
val res = translate (encode_LZSS_table_def |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate encode_LZSS_def;
val res = translate deflate_encoding_def;
val res = translate encode_uncompressed_def;
val res = translate encode_fixed_def;
val res = translate (encode_dynamic_def |> REWRITE_RULE [GSYM sub_check_def]);
val res = translate encode_block_def;
val res = translate decode_LZSS_table_def;
val res = translate decode_LZSS_lendist_def;
val res = translate decode_LZSS_def;
val res = translate decode_check_end_block_def;
val res = translate deflate_decoding_def;
val res = translate read_dyn_header_def;
val res = translate read_clen_def;
val res = translate recreate_clen_def;
val res = translate decode_clen_def;
val res = translate read_literals_def;
val res = translate decode_uncompressed_def;
val res = translate decode_fixed_def;
val res = translate decode_dynamic_def;
val res = translate decode_block_def;
val res = translate bl2s_def;
val res = translate s2bl_def;
val res = translate deflate_encode_def;
val res = translate deflate_decode_def;
val res = translate deflate_encode_main_def;
val res = translate deflate_decode_main_def;

Definition main_function_def:
  main_function (s:mlstring) = List [implode (deflate_encode_main (explode s))]
End

val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring app_list”
        orelse failwith "The main_function has the wrong type.\n";

val _ = res |> DISCH_ALL |> concl |> can $ find_term $ can $ match_term “PRECONDITION” |> not
        orelse failwith "The main_function has an unproved pre/side-condition.\n";

val main = process_topdecs
  `print_app_list (main_function (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition deflateEncode_prog_def:
  deflateEncode_prog = ^prog
End

val _ = export_theory();
