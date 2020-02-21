(*
  Pretty prints the CakeML code of the Candle kernel.
  The output is produced in a file called kernel_ml.txt.
*)
open HolKernel boolLib bossLib
open ml_translatorLib ml_monad_translatorTheory ml_hol_kernelProgTheory astPP

val _ = new_theory"ppKernel"

val pat = ``Dmod "Kernel" _``
val decls = ml_hol_kernelProgTheory.candle_code_def |> concl |> rand
            |> find_term (can (match_term pat)) |> rand

fun equalityprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([l,r],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [App Opapp [Var(Short"=");^l];^r]``
  end
val _ = add_astPP("equalityprinter",``App Equality [x;y]``,equalityprinter)

fun refprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([a],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [Var(Short"ref");^a]``
  end
val _ = add_astPP("refprinter",``App Opref [x]``,refprinter)

fun assignprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([l,r],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [App Opapp [Var(Short":=");^l];^r]``
  end
val _ = add_astPP("assignprinter",``App Opassign [x;y]``,assignprinter)

fun derefprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([a],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [Var(Short"!");^a]``
  end
val _ = add_astPP("derefprinter",``App Opderef [x]``,derefprinter)

fun plusprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([l,r],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [App Opapp [Var(Short"+");^l];^r]``
  end
val _ = add_astPP("plusprinter",``App (Opn Plus) [x;y]``,plusprinter)

fun implodeprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([a],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [Var(Long"String" (Short "implode"));^a]``
  end
val _ = add_astPP("implodeprinter",``App Implode [x]``,implodeprinter)

fun explodeprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([a],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [Var(Long"String" (Short "explode"));^a]``
  end
val _ = add_astPP("explodeprinter",``App Explode [x]``,explodeprinter)

fun chltprinter _ _ sysp _ gs d t =
  let
    fun sys g d = sysp {gravs=g,depth=d,binderp=false}
    val (_,ls) = dest_comb t
    val ([l,r],_) = listSyntax.dest_list ls
  in
    sys gs d ``App Opapp [App Opapp [Var(Short"<");^l];^r]``
  end
val _ = add_astPP("chltprinter",``App (Chopb Lt) [x;y]``,chltprinter)

val _ = enable_astPP()

val _ = set_trace "pp_avoids_symbol_merges" 0

val f = TextIO.openOut("kernel_ml.txt")

fun appthis tm = let
  val () = TextIO.output(f,term_to_string tm)
  val () = TextIO.output(f,"\n")
in () end

val _ = app appthis (fst(listSyntax.dest_list decls))

val _ = TextIO.closeOut f

val _ = disable_astPP()

val _ = export_theory()
