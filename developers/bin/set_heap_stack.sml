val cake = "cake.S"
val heap = "2000"
val stack = "2000"
val pat = ".space 1024 * 1024 * "

fun replace_suffix str pat rep =
  let
    val (pre,t) = Substring.position pat (Substring.full str)
    val (_,i,_) = Substring.base t
  in
    if i = size str then NONE
    else SOME ((Substring.string pre) ^ pat ^ rep ^ "\n")
  end;

fun find_replace_suffix ins pat rep acc = 
  case TextIO.inputLine ins of NONE => acc
    | SOME s => (case replace_suffix s pat rep of SOME s => s::acc
                   | NONE => find_replace_suffix ins pat rep (s::acc))

val ins = TextIO.openIn cake;
val pre = find_replace_suffix ins pat heap [];
val mid = find_replace_suffix ins pat stack [];
val suf = TextIO.inputAll ins;
val _ = TextIO.closeIn ins;

val outs = TextIO.openOut cake;
val _ = app (fn l => TextIO.output (outs,l)) (rev pre);
val _ = app (fn l => TextIO.output (outs,l)) (rev mid);
val _ = TextIO.output (outs,suf);
val _ = TextIO.closeOut outs;
