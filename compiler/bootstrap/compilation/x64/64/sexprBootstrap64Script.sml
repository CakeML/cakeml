(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 64-bit version of the compiler.
*)
Theory sexprBootstrap64
Ancestors
  compiler64Prog
Libs
  preamble mlstringSyntax astToSexprLib

val filename = "cake-sexpr-64"

val _ = ((write_ast_to_file filename) o rhs o concl) compiler64_prog_def;

(* The following code can be used to generared sexp with EVAL. This code is very slow.

val _ = (max_print_depth := 10);

val dec_tms =
  compiler64_prog_def |> concl |> rhs |> listSyntax.dest_list |> fst

fun dec_sexps () = let
  val f = TextIO.openIn filename
  fun r () =
    case TextIO.inputLine f of
      NONE => []
    | SOME line => line :: r ()
  val lines = r ()
  val _ = TextIO.closeIn f
  in butlast (tl lines) end

val _ = (length dec_tms = length (dec_sexps())) orelse failwith "wrong length"

Definition str_to_dec_def:
  str_to_dec s =
    case parse_sexp (MAP (λx. (x,ARB)) s) of
    | NONE => NONE
    | SOME x => SOME (*sexpdec*) x
End

Definition dec_to_str_def:
  dec_to_str d = print_sexp (decsexp d)
End

val _ = let
  val f = TextIO.openOut(filename ^ "-correct")
  val _ = TextIO.output(f,"(\n")
  val n = ref 0
  fun output_d d =
    mk_comb(“dec_to_str”,d) |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring
    |> (fn s => (n := (!n)+1; print (int_to_string (!n)); print "\n"; s ^ "\n"))
    |> curry TextIO.output f
  val _ = List.app output_d dec_tms
  val _ = TextIO.output(f,")\n")
  val _ = TextIO.closeOut f
  in () end

(* code that can be handy when testing *)

val write = print

val dec_tms =
  compiler64_prog_def |> concl |> rhs |> listSyntax.dest_list |> fst
  |> el 44

  ast_to_exp “Dtype (Locs UNKNOWNpt UNKNOWNpt) [([],"ast_lop",[("Or",[]); ("And",[])])]”

val filename1 = "cake-sexpr-64"
val filename2 = "cake-sexpr-64-correct"

fun trim s =
  if String.isPrefix " "  s then trim (String.substring(s,1,String.size s - 1)) else
  if String.isSuffix " "  s then trim (String.substring(s,0,String.size s - 1)) else
  if String.isSuffix "\n" s then trim (String.substring(s,0,String.size s - 1)) else s

fun str_repl s t str =
  if String.isSubstring s str then
    let
      val l = String.size s
      fun find_index i =
        if String.substring(str,i,l) = s then i else find_index (i+1)
      val i = find_index 0
      val m = String.size str
      val str1 = String.substring(str,0,i)
      val str2 = String.substring(str,i+l,m-(i+l))
    in str_repl s t (str1 ^ t ^ str2) end
  else str

fun linesFrom filename = let
  val f = TextIO.openIn filename
  fun r () =
    case TextIO.inputLine f of
      NONE => []
    | SOME line => str_repl " )" ")" (trim line) :: r ()
  val lines = r ()
  val _ = TextIO.closeIn f
  in lines end

val l1 = length (linesFrom filename1)
val l2 = length (linesFrom filename2)

  zip (linesFrom filename1) (linesFrom filename2)
  |> mapi (fn i => fn (x,y) => (i,x,y))
  |> filter (fn (n,x,y) => x <> y)
  |> length

*)

