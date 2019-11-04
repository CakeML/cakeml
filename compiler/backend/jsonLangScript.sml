(*
  This module contains a datatype for representing JSON objects, and
  related functions. A JSON object can be an array of objects, a
  string, an int, a bool or null, or it can be an object enclosed
  in {}, in which case it can be viewed as a key-value store of names
  (strings) and JSON objects.
*)
open preamble mlintTheory

val _ = new_theory"jsonLang";

val _ = Datatype`
  obj =
     Object (( string # obj ) list)
   | Array (obj list)
   | String string
   | Int int
   | Bool bool
   | Null`;

Overload "++"[local] = ``Append``

val concat_with_def = Define`
  (concat_with [] c acc = acc) /\
  (concat_with [s] c acc = acc ++ s) /\
  (concat_with (s::ss) c acc = concat_with ss c (acc ++ s ++ c))`;

(* To output a string in the JSON such that, if the string would be printed
* directly, it should look like the corresponding CakeML value. *)
val escape_def = Define`
  (escape "" = "")
  /\
  (* Output two backslashes in the JSON, followed by an "n", which will be
  * printed as "\n". *)
  (escape (#"\n"::s) = #"\\":: #"\\" :: #"n" ::escape s)
  /\
  (* Output four backslashes in the JSON, which will be printed as "\\". *)
  (escape (#"\\"::s) = #"\\":: #"\\" :: #"\\":: #"\\" ::escape s)
  /\
  (escape (#"\""::s) = #"\\":: #"\"" ::escape s)
  /\
  (escape (h::s) = h::escape s)`;

val obj_size_def = fetch "-" "obj_size_def"

val json_to_string_def = tDefine "json_to_string" `
  (json_to_string obj =
    case obj of
       | Object mems => List "{" ++ (concat_with (MAP mem_to_string mems) (List ",") (List "")) ++ List "}"
       | Array obs => List "[" ++ (concat_with (MAP json_to_string obs) (List ",") (List "")) ++ List "]"
       | String s => List "\"" ++ List (escape s) ++ List "\""
       | Int i => List (explode (toString i))
       | Bool b => if b then List "true" else List "false"
       | Null => List "null")
  /\
  (mem_to_string (n, ob) = List "\"" ++ List n ++ List "\":" ++ (json_to_string ob))`
  (WF_REL_TAC `measure (\x. case x of
       | INL obj => obj_size obj
       | INR p => obj2_size p)` \\ rw []
   THEN1 (Induct_on `obs` \\ fs [] \\ rw [obj_size_def] \\ fs [])
   THEN1 (Induct_on `mems` \\ fs [] \\ rw [obj_size_def] \\ fs []
          \\ rw [obj_size_def]));

val _ = export_theory();
