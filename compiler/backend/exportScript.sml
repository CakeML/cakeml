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
       "     .file        \"cake.S\"";
       ""])`` |> EVAL |> rconc;
val preamble_def = Define`preamble = ^preamble_tm`;

val space_line_def = Define`
  space_line n = concat[strlit"     .space 1024 * 1024 * "; toString (n:num); strlit "\n"]`;

val data_section_def = Define`data_section word_directive heap_space stack_space =
     MAP (\n. strlit (n ++ "\n"))
       ["/* Data section -- modify the numbers to change stack/heap size */";
        "";
        "     .bss";
        "     .p2align 3";
        "cake_heap:"] ++ [space_line heap_space] ++
     MAP (\n. strlit (n ++ "\n"))
       ["     .p2align 3";
        "cake_stack:"] ++ [space_line stack_space] ++
      MAP (\n. (strlit (n ++ "\n")))
       ["     .p2align 3";
        "cake_end:";
        "";
        "     .data";
        "     .p2align 3";
        "cdecl(argc): " ++ word_directive ++ " 0";
        "cdecl(argv): " ++ word_directive ++ " 0";
        "     .p2align 3";
        "cake_bitmaps:"]`;

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

val _ = export_theory ();
