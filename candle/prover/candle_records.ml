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

(* Records can be updated using 'with': *)
let z = { x with boolean = true; integer = 3; };;

(* Record projection is done with a dot: *)
let s = z.a_string;;

print (s ^ "\n");;
print (Int.toString (m1 x) ^ " " ^ Int.toString (m1 y) ^ "\n");;
print (a_string ^ "\n");;

(* Limitations:
 * - It is not possible to name the matched fields in record pattern matches
 * - Record field names are unique: while it is possible to use the same field
 *   name in two records, the latter definition will overwrite the formers
 *   accessor functions.
 *)
