(*
  Define the format of the compiler-generated output file for ag32
*)
open preamble exportTheory mlstringTheory

val () = new_theory "export_ag32";

Definition ag32_export_def:
  ag32_export (ffi_names:string list) bytes (data:word32 list)
      (syms: (mlstring # num # num) list) exp ret pk =
    SmartAppend
     (split16 (words_line (strlit".data_word ") word_to_string) data)
     (split16 (words_line (strlit".code_byte ") byte_to_string) bytes)
End

val _ = export_theory ();
