open preamble

val _ = new_theory"json";

(*
* This module contains a data type for representing JSON objects, and related
* functions. A JSON object can be an array of objects, a string, an int, a bool
* or null, or it can be an object enclosed in {}, in which case it can be viewed
* as a key-value store of names (strings) and JSON objects.
*)
val _ = Datatype`
  obj =
     Object (( string # obj ) list)
   | Array (obj list)
   | String string
   | Int int
   | Bool bool
   | Null`;

val num_to_str_def = Define `
  num_to_str n = if n < 10 then [CHR (48 + n)]
                 else (num_to_str (n DIV 10)) ++ ([CHR (48 + (n MOD 10))])`;

val int_to_str_def = Define `
  int_to_str i = if i < 0
                then "-" ++ (num_to_str (Num (-i)))
                else num_to_str (Num i)`;

val concat_with_def = Define`
  (concat_with [] c acc = acc) /\
  (concat_with [s:string] c acc = acc ++ s) /\
  (concat_with (s::ss) c acc = concat_with ss c (acc ++ s ++ c))`;

val json_to_string_def = tDefine "json_to_string" `
  (json_to_string (Object mems) =
    "{ " ++ (concat_with (MAP mem_to_string mems) ", " "") ++ " }")
  /\
  (json_to_string (Array obs) =
    "[ " ++ (concat_with (MAP json_to_string obs) ", " "") ++ " ]")
  /\
  (json_to_string (String s) = "'" ++ s ++ "'")
  /\
  (json_to_string (Int i) = int_to_str i)
  /\
  (json_to_string (Bool b) = if b then "true" else "false")
  /\
  (json_to_string (Null) = "null")
  /\
  (mem_to_string (n, ob) = "'" ++ n ++ "': " ++ (json_to_string ob))`
  cheat;

val _ = export_theory();
