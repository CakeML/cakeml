(*
  Inserts set_grammar_ancestry calls
*)

exception Ready;

val space = String.translate (fn _ => " ") "val _ = set_grammar_ancestry [";

fun break_at max s [] = [s]
  | break_at max s (x::xs) =
      if size (s ^ ", " ^ x) < max then
        break_at max (s ^ ", " ^ x) xs
      else if xs = [] then [s] else
        s ^ ",\n" :: break_at max (space ^ x) xs;

val esc = str (chr 27)
val red = esc ^ "[31m"
val green = esc ^ "[32m"
val reset = esc ^ "[0m"
fun make_red s = red ^ s ^ reset;
fun make_green s = green ^ s ^ reset;

(*
val filename = "/home/myreen/cakeml-set-grammar-ancestry/semantics/fpSemScript.sml"
*)
fun process_file filename = let
  (* read file *)
  val f = TextIO.openIn filename
  fun read_all f x =
    case f x of NONE => [] | SOME y => y :: read_all f x
  val xs = read_all TextIO.inputLine f
  val _ = TextIO.closeIn f
  (* check if it has set_grammar_ancestry *)
  val needle = "set_grammar_ancestry"
  val _ = List.all (fn line => not (String.isSubstring needle line)) xs
          orelse raise Ready
  (* split file at new_theory *)
  fun split_at_first p [] acc = raise Ready
    | split_at_first p (x::xs) acc =
        if p x then (rev acc, x::xs) else split_at_first p xs (x::acc)
  val needle = "new_theory"
  val (ys,zs) = split_at_first (String.isSubstring needle) xs []
  (* pick out theories from header *)
  fun is_ident_char c =
    c = #"_" orelse
    (#"0" <= c andalso c <= #"9") orelse
    (#"a" <= c andalso c <= #"z") orelse
    (#"A" <= c andalso c <= #"Z")
  val words = concat ys
  val words = String.tokens (not o is_ident_char) words
  val words = List.filter (String.isSuffix "Theory") words
  val words = List.map (fn s => String.substring(s,0,size s - size "Theory")) words
  val words = List.map (fn s => "\"" ^ s ^ "\"") words
  (* make set_grammar_ancestry line *)
  val line = "val _ = set_grammar_ancestry [" ^ hd words
  val lines = break_at 80 line (tl words)
  val res = String.concat (lines @ ["];\n\n"])
  (* prepare output *)
  val output = ys @ [res] @ zs
  val f = TextIO.openOut filename
  val _ = TextIO.output (f, String.concat output)
  val _ = TextIO.closeOut f
  val _ = print (filename ^ " -- " ^ make_green "updated\n")
  in () end handle Ready => print (filename ^ " -- skipped\n")
                 | _ => print (filename ^ " -- " ^ make_red "FAILED\n");

fun main () = let
  val args = CommandLine.arguments ()
  val () = List.app process_file args
  in () end;
