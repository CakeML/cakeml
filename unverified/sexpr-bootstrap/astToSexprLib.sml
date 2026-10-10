structure astToSexprLib =
struct

local

open HolKernel boolLib

datatype sexp = Atom of string | Expr of sexp list

(* mlint$toString *)
fun int_to_str tm =
  let val i = intSyntax.int_of_term tm in
    (if Arbint.< (i, Arbint.zero) then "~" else "") ^
    Arbnum.toString (Arbint.toNat (Arbint.abs i))
  end

(* num_to_str o w2n *)
fun word_to_str tm =
  Arbnum.toString (Arbnum.mod (wordsSyntax.dest_word_literal tm,
                               Arbnum.pow (Arbnum.two, wordsSyntax.size_of tm)))

(* string$isSpace *)
fun is_space c = c = #" " orelse (#"\t" <= c andalso c <= #"\r")

(* mlstring$char_escaped *)
fun char_escaped #"\t" = "\\t"
  | char_escaped #"\n" = "\\n"
  | char_escaped #"\\" = "\\\\"
  | char_escaped #"\"" = "\\\""
  | char_escaped c = String.str c

(* mlsexp$is_safe_char *)
fun is_safe_char c =
  not (c = #"(" orelse c = #")" orelse c = #"\"" orelse c = #"\000" orelse
       is_space c)

(* mlsexp$make_str_safe *)
fun make_str_safe "" = "\"\""
  | make_str_safe s =
      if CharVector.all is_safe_char s then s
      else "\"" ^ String.translate char_escaped s ^ "\""

(* Converts a term into an s-expression. *)
fun from_term tm =
  if mlstringSyntax.is_mlstring_literal tm then
    Atom (mlstringSyntax.dest_mlstring tm)
  else if intSyntax.is_int_literal tm then Atom (int_to_str tm)
  else if wordsSyntax.is_word_literal tm then Atom (word_to_str tm)
  else if stringSyntax.is_char_literal tm then
    Atom (String.str (stringSyntax.fromHOLchar tm))
  else if listSyntax.is_list tm then
    Expr (map from_term (fst (listSyntax.dest_list tm)))
  else if pairSyntax.is_pair tm then
    Expr (map from_term (pairSyntax.spine_pair tm))
  else
    let
      val (c, args) = strip_comb tm
      val name = Atom (fst (dest_const c))
    in
      if null args then name else Expr (name :: map from_term args)
    end

(* Passes the printed s-expression to out, piece by piece. *)
fun output_sexp out =
  let
    fun pr (Atom s) = out (make_str_safe s)
      | pr (Expr l) = (out "("; prs l; out ")")
    and prs [] = ()
      | prs [x] = pr x
      | prs (x::xs) = (pr x; out " "; prs xs)
  in pr end

in

(* entry points ***************************************************************)

fun ast_to_string tm =
  let
    val acc = ref []
    val _ = output_sexp (fn s => acc := s :: !acc) (from_term tm)
  in String.concat (List.rev (!acc)) end

fun write_ast_to_file filename tm =
  let
    val sexp = from_term tm
    val out = TextIO.openOut filename
  in
    output_sexp (fn s => TextIO.output (out, s)) sexp;
    TextIO.closeOut out
  end

end

end
