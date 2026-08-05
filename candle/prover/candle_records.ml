(* Record syntax in Candle. *)

(* Records are declared as part of datatypes. It is possible to mix classic
 * datatype constructors and record constructors freely.
 *)
type thing =
  | Aa of int
  | Bb of { integer: int; boolean: bool; a_string: string }
;;

(* Records support pattern matching. It is possible to do partial matches. *)
let m1 t =
  match t with
  | Aa n -> n
  | Bb {integer} -> integer;;

(* Pattern matching on records works in the outermost pattern. Nested record
 * patterns are not supported.
 *)
let Bb { a_string } = Bb { a_string = "5"; boolean = false; integer = 1 };;

(* Records are constructed with this syntax: *)
let x = Bb { a_string = "1"; boolean = false; integer = 2 };;
let y = Aa 5;;

(* Records can be updated using 'with'. This updates the record 'x': *)
let z = Bb { x with boolean = true; integer = 3; };;

(* Record projection is done with dots, using the name of the constructor and
 * the name of the field: *)
let s = z.Bb.a_string;;

print (s ^ "\n");;
print (Int.toString (m1 x) ^ " " ^ Int.toString (m1 y) ^ "\n");;
print (a_string ^ "\n");;

module Mod = struct
  type blob = Cc of { cc: bool };;
  let x = Cc { cc = true };;
end;;

(* It's possible to use records with qualified constructors:
 * - Mod.x is to access the value x,
 * - Mod.Cc is for the record constructor in Cc in Mod, and
 * - cc is the field in the record Cc: *)
print "cc=";;
print (if Mod.x.Mod.Cc.cc then "true\n" else "false\n");;

(* Limitations:
 * - It is not possible to name the matched fields in record pattern matches
 * - Record constructors are present in all record-related syntax. This is
 *   because records are implemented as a syntax extension in the Candle parser,
 *   and the parser does not know what names belong to what records.
 *)
