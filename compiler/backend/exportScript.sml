(*
  Some common helper functions for writing the final byte list ->
  string exporter.
*)
open preamble mlstringTheory mlvectorTheory mlintTheory;

val _ = new_theory "export";

val split16_def = tDefine "split16" `
  (split16 f [] = Nil) /\
  (split16 f xs =
     let xs1 = TAKE 16 xs in
     let xs2 = DROP 16 xs in
       SmartAppend (f xs1) (split16 f xs2))`
  (WF_REL_TAC `measure (LENGTH o SND)`
   \\ fs [listTheory.LENGTH_DROP]);

val preamble_tm =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["/* Preprocessor to get around Mac OS, Windows, and Linux differences in naming and calling conventions */";
       "";
       "#if defined(__APPLE__)";
       "# define cdecl(s) _##s";
       "#else";
       "# define cdecl(s) s";
       "#endif";
       "";
       "#if defined(__APPLE__)";
       "# define wcdecl(s) _##s";
       "#elif defined(__WIN32)";
       "# define wcdecl(s) windows_##s";
       "#else";
       "# define wcdecl(s) s";
       "#endif";
       "";
       "#if defined(__APPLE__)";
       "# define makesym(name,base,len)";
       "#elif defined(__WIN32)";
       "# define makesym(name,base,len)";
       "#else";
       ".macro _makesym name, base, len";
       ".local \\name";
       ".set \\name, cake_main+\\base";
       ".size \\name, \\len";
       ".type \\name, function";
       ".endm";
       "# define makesym(name,base,len) _makesym name, base, len";
       "#endif";
       "";
       "#define DATA_BUFFER_SIZE    65536";
       "#define CODE_BUFFER_SIZE  5242880";
       "";
       "     .file        \"cake.S\"";
       ""])`` |> EVAL |> rconc;
val preamble_def = Define`preamble = ^preamble_tm`;

val data_section_def = Define`data_section word_directive =
     MAP (\n. strlit (n ++ "\n"))
       ["     .data";
        "     .p2align 3";
        "cdecl(cml_heap): " ++ word_directive ++ " 0";
        "cdecl(cml_stack): " ++ word_directive ++ " 0";
        "cdecl(cml_stackend): " ++ word_directive ++ " 0";
        "     .p2align 3";
        "cake_bitmaps:"]`;

Definition data_buffer_def:
  data_buffer =
     MAP (\n. strlit (n ++ "\n"))
       ["     .globl cdecl(cake_bitmaps_buffer_begin)";
        "cdecl(cake_bitmaps_buffer_begin):";
        "#if defined(EVAL)";
        "     .space DATA_BUFFER_SIZE";
        "#endif";
        "     .globl cdecl(cake_bitmaps_buffer_end)";
        "cdecl(cake_bitmaps_buffer_end):"]
End

Definition code_buffer_def:
  code_buffer =
     MAP (\n. strlit (n ++ "\n"))
       ["     .globl cdecl(cake_codebuffer_begin)";
        "cdecl(cake_codebuffer_begin):";
        "#if defined(EVAL)";
        "     .space CODE_BUFFER_SIZE";
        "#endif";
        "     .p2align 12";
        "     .globl cdecl(cake_codebuffer_end)";
        "cdecl(cake_codebuffer_end):";
        "     .space 4096"]
End

val comm_strlit_def = Define `comm_strlit = strlit ","`;
val newl_strlit_def = Define `newl_strlit = strlit "\n"`;

val comma_cat_def = Define `
  comma_cat f x =
    case x of
    | [] => [newl_strlit]
    | [x] => [f x; newl_strlit]
    | (x::xs) => f x :: comm_strlit :: comma_cat f xs`;

val words_line_def = Define`
  words_line word_directive to_string ls =
    List (word_directive :: comma_cat to_string ls)`;

val word_to_string_def = Define`
  word_to_string w = toString(w2n w)`;

val byte_to_string_def = Define `
  byte_to_string (b:word8) =
    strlit ("0x" ++ [EL (w2n b DIV 16) "0123456789ABCDEF"]
                 ++ [EL (w2n b MOD 16) "0123456789ABCDEF"])`;

val all_bytes_def = Define `
  all_bytes = Vector (GENLIST (\n. byte_to_string (n2w n)) 256)`;

val all_bytes_eq = save_thm("all_bytes_eq",EVAL ``all_bytes``);

Theorem byte_to_string_eq:
   !b. byte_to_string b = sub all_bytes (w2n b)
Proof
  Cases_on `b` \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [all_bytes_def,mlvectorTheory.sub_def]
  \\ full_simp_tac std_ss [w2n_n2w,EVAL ``dimword (:8)``]
  \\ full_simp_tac std_ss [listTheory.EL_GENLIST]
QED

(* gas allows 0-9a-zA-Z_$. in labels as long as the first is _A-Za-z *)
(* we prefix labels and reserve $; . is special *)

val escape_sym_char_def = Define`
  escape_sym_char ch = let code = ORD ch in
    if code >= 0x61 /\ code <= 0x7A \/ code >= 0x41 /\ code <= 0x5A \/
       code >= 0x30 /\ code <= 0x39 \/ code = 0x5F then str ch else
    «$» ^ toString(code) ^ «_»`

val emit_symbol_def = Define`
  emit_symbol (ix,appl) (name,start,len) = (ix + 1, misc$Append appl (misc$List
      [«    makesym(cml_» ^ concat (MAP escape_sym_char (explode name)) ^
      «_» ^ toString(ix) ^ «, » ^ toString(start) ^ «, » ^
      toString(len) ^ «)\n»]))`

val emit_symbols_def = Define `
  emit_symbols ls = SND $ FOLDL emit_symbol (0, misc$Nil) ls`;

val _ = export_theory ();
