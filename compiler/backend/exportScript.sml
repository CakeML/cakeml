(*
  Some common helper functions for writing the final byte list ->
  string exporter.
*)
open preamble mlstringTheory mlvectorTheory mlintTheory;

val _ = new_theory "export";

Definition split16_def:
  (split16 f [] = Nil) /\
  (split16 f xs =
     let xs1 = TAKE 16 xs in
     let xs2 = DROP 16 xs in
       SmartAppend (f xs1) (split16 f xs2))
Termination
  WF_REL_TAC `measure (LENGTH o SND)`
   \\ fs [listTheory.LENGTH_DROP]
End

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
       "# define wcml(s) s";
       "#elif defined(__WIN32)";
       "# define wcml(s) windows_##s";
       "#else";
       "# define wcml(s) s";
       "#endif";
       "";
       "#if defined(__APPLE__)";
       ".macro _makesym name, base, len";
       ".set \\name, cake_main+\\base";
       ".endm";
       "# define makesym(name,base,len) _makesym name, base, len";
       "#elif defined(__WIN32)";
       ".macro _makesym name, base, len";
       ".set \\name, cake_main+\\base";
       ".endm";
       "# define makesym(name,base,len) _makesym name, base, len";
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
Definition preamble_def:
  preamble = ^preamble_tm
End

Definition data_section_def:
  data_section word_directive ret =
     MAP (\n. strlit (n ++ "\n"))
       (["     .data";
        "     .p2align 3";
        "cdecl(cml_heap): " ++ word_directive ++ " 0";
        "cdecl(cml_stack): " ++ word_directive ++ " 0";
        "cdecl(cml_stackend): " ++ word_directive ++ " 0"] ++
        (if ret then
          ["ret_base: " ++ word_directive ++ " 0";
           "ret_stack: " ++ word_directive ++ " 0";
           "ret_stackend: " ++ word_directive ++ " 0";
           "can_enter: " ++ word_directive ++ " 0"]
         else []) ++
        ["     .p2align 3";
        "cake_bitmaps:"])
End

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

Definition comm_strlit_def:
  comm_strlit = strlit ","
End
Definition newl_strlit_def:
  newl_strlit = strlit "\n"
End

Definition comma_cat_def:
  comma_cat f x =
    case x of
    | [] => [newl_strlit]
    | [x] => [f x; newl_strlit]
    | (x::xs) => f x :: comm_strlit :: comma_cat f xs
End

Definition words_line_def:
  words_line word_directive to_string ls =
    List (word_directive :: comma_cat to_string ls)
End

Definition word_to_string_def:
  word_to_string w = toString(w2n w)
End

Definition byte_to_string_def:
  byte_to_string (b:word8) =
    strlit ("0x" ++ [EL (w2n b DIV 16) "0123456789ABCDEF"]
                 ++ [EL (w2n b MOD 16) "0123456789ABCDEF"])
End

Definition all_bytes_def:
  all_bytes = Vector (GENLIST (\n. byte_to_string (n2w n)) 256)
End

Theorem all_bytes_eq =
  EVAL ``all_bytes``

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

Definition escape_sym_char_def:
  escape_sym_char ch = let code = ORD ch in
    if code >= 0x61 /\ code <= 0x7A \/ code >= 0x41 /\ code <= 0x5A \/
       code >= 0x30 /\ code <= 0x39 \/ code = 0x5F then str ch else
    «$» ^ toString(code) ^ «_»
End

Definition get_sym_label_def:
  get_sym_label (ix,appl) (name,start,len) =
    let label =
      «cml_» ^ concat (MAP escape_sym_char (explode name)) ^
      «_» ^ toString(ix) in
    (ix + 1, appl ++ [(name,label,start,len)])
End

Definition get_sym_labels_def:
  get_sym_labels syms =
    SND $ FOLDL get_sym_label (0, []) syms
End

Definition emit_symbol_def:
  emit_symbol appl (name,label,start,len) =
    misc$Append appl (misc$List
      [«    makesym(» ^ label ^ «, » ^ toString(start) ^ «, » ^
      toString(len) ^ «)\n»])
End

Definition emit_symbols_def:
  emit_symbols lsyms =
    FOLDL emit_symbol misc$Nil lsyms
End

val _ = export_theory ();
