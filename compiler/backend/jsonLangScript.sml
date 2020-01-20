(*
  This module contains a datatype for representing JSON objects, and
  related functions. A JSON object can be an array of objects, a
  string, an int, a bool or null, or it can be an object enclosed
  in {}, in which case it can be viewed as a key-value store of names
  (strings) and JSON objects.
*)
open preamble mlintTheory mlstringTheory

val _ = new_theory"jsonLang";

val _ = Datatype`
  obj =
     Object ((mlstring # obj ) list)
   | Array (obj list)
   | String mlstring
   | Int int
   | Bool bool
   | Null`;

Overload "++"[local] = ``Append``

val concat_with_def = Define`
  (concat_with [] c = List []) /\
  (concat_with [s] c = s) /\
  (concat_with (s::ss) c = s ++ (c ++ concat_with ss c))`;

val printable_def = Define`
  printable c <=> ORD c >= 32 /\ ORD c < 127 /\ c <> #"\"" /\ c <> #"\\"`;

val encode_str_def = Define`
  encode_str s =
  let s2 = explode s in
  if EVERY printable s2 then s
  else concat (MAP (\c. if printable c then implode [c]
    else concat [strlit "\\"; toString (ORD c)]) s2)`;

val obj_size_def = fetch "-" "obj_size_def"

val json_to_mlstring_def = tDefine "json_to_mlstring" `
  (json_to_mlstring obj =
    case obj of
        | Object mems => List [strlit "{"] ++
                concat_with (MAP mem_to_string mems) (List [strlit ","]) ++
                List [strlit "}"]
        | Array obs => List [strlit "["] ++
                concat_with (MAP json_to_mlstring obs) (List [strlit ","]) ++
                List [strlit "]"]
       | String s => List ([strlit "\""; encode_str s; strlit "\""])
       | Int i => List [toString i]
       | Bool b => if b then List [strlit "true"] else List [strlit "false"]
       | Null => List [strlit "null"])
  /\
  (mem_to_string n_obj = let (n, obj) = n_obj in
        List [strlit "\""; n; strlit "\":"] ++ json_to_mlstring obj)`
  (WF_REL_TAC `measure (\x. case x of
       | INL obj => obj_size obj
       | INR p => obj2_size p)` \\ rw []
   THEN1 (Induct_on `obs` \\ fs [] \\ rw [obj_size_def] \\ fs [])
   THEN1 (Induct_on `mems` \\ fs [] \\ rw [obj_size_def] \\ fs []
          \\ rw [obj_size_def]));

val _ = export_theory();
