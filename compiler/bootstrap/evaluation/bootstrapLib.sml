structure bootstrapLib = struct

open preamble

(* TODO: move all this to preamble? *)

infix 8 $
fun op $ (f,x) = f x

val rconc = rhs o concl;

fun time_with_size size_fn name eval_fn x =
  let
    val () = Lib.say(String.concat["eval ",name,": "])
    val r = time eval_fn x
    val z = size_fn r
    val () = Lib.say(String.concat["size ",name,": ",Int.toString z,"\n"])
  in r end

val sum = foldl (op+) 0
fun thms_size ls = sum (map (term_size o rconc) ls)

fun timez x y = time_with_size (term_size o rconc) x y

fun mk_def_name s = String.concat[s,"_def"];
fun mk_def s tm = new_definition(mk_def_name s,mk_eq(mk_var(s,type_of tm),tm))

fun make_abbrevs str n [] acc = acc
  | make_abbrevs str n (t::ts) acc =
    make_abbrevs str (n-1) ts
      (mk_def (str^(Int.toString n)) t :: acc)

fun intro_abbrev [] tm = raise UNCHANGED
  | intro_abbrev (ab::abbs) tm =
      FORK_CONV(REWR_CONV(SYM ab),intro_abbrev abbs) tm

end
