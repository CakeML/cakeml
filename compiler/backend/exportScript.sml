open preamble mlstringTheory mlvectorTheory;

(* Some common helper functions for writing the final byte list -> string exporter *)
val _ = new_theory "export";

val byte_to_string_def = Define `
  byte_to_string (b:word8) =
    strlit ("0x" ++ [EL (w2n b DIV 16) "0123456789ABCDEF"]
                 ++ [EL (w2n b MOD 16) "0123456789ABCDEF"])`;

val all_bytes_def = Define `
  all_bytes = Vector (GENLIST (\n. byte_to_string (n2w n)) 256)`;

val all_bytes_eq = save_thm("all_bytes_eq",EVAL ``all_bytes``);

val byte_to_string_eq = store_thm("byte_to_string_eq",
  ``!b. byte_to_string b = sub all_bytes (w2n b)``,
  Cases_on `b` \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [all_bytes_def,mlvectorTheory.sub_def]
  \\ full_simp_tac std_ss [w2n_n2w,EVAL ``dimword (:8)``]
  \\ full_simp_tac std_ss [listTheory.EL_GENLIST]);

val byte_strlit_def = Define `byte_strlit = strlit "\t.byte "`;
val comm_strlit_def = Define `comm_strlit = strlit ","`;
val newl_strlit_def = Define `newl_strlit = strlit "\n"`;

val comma_cat_def = Define `
  comma_cat x =
    case x of
    | [] => [newl_strlit]
    | [x] => [byte_to_string x; newl_strlit]
    | (x::xs) => byte_to_string x :: comm_strlit :: comma_cat xs`

val bytes_row_def = Define `
  bytes_row xs = List (byte_strlit :: comma_cat xs)`;

val split16_def = tDefine "split16" `
  (split16 [] = Nil) /\
  (split16 xs =
     let xs1 = TAKE 16 xs in
     let xs2 = DROP 16 xs in
       SmartAppend (bytes_row xs1) (split16 xs2))`
  (WF_REL_TAC `measure LENGTH`
   \\ fs [listTheory.LENGTH_DROP]);

val num_to_str_def = Define `
  num_to_str n = if n < 10 then [CHR (48 + n)]
                 else (num_to_str (n DIV 10)) ++ ([CHR (48 + (n MOD 10))])`;

val num_to_str_ind = fetch "-" "num_to_str_ind";

val _ = export_theory ();
