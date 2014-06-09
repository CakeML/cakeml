open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory

fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |> rand |> rator |> rand
      end;


val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
val past2 = rhs(concl elab) |> rand |> rator |> rand

fun strip t = #2 (dest_comb t);

fun arglist t =
  let val v = t |> strip |> strip;
  in
    pairSyntax.strip_pair (hd(#1(listSyntax.dest_list v)))
  end;

fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types
    val (str,brk) = (#add_string ppfns, #add_break ppfns);
  in
    printFunc sys d t Top str brk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun tletrecPrint sys d t Top str brk =
  let
    open Portable smpp
    val (x::y::[z]) = arglist t
  in
    str "fun" >> brk (1,0) >>
    sys (Top,Top,Top) (d-1) x >> brk (1,0) >>
    sys (Top,Top,Top) (d-1) y >> brk (1,0) >>
    str "=" >> brk (1,0) >> sys (Top,Top,Top) (d-1) z
  end;

temp_add_user_printer ("tletrecprint", ``Tdec (Dletrec x)``, genPrint tletrecPrint);

fun tletvalPrint sys d t Top str brk =
  let
    open Portable smpp
    val (l,r) = dest_comb (strip t);
  in
    str "val" >> brk (1,0) >>
    sys (Top,Top,Top) (d-1) (strip l) >> 
    str " = " >> brk (1,0) >> sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("tletvalprint", ``Tdec (Dlet x y)``,genPrint tletvalPrint);

fun pvarPrint sys d t Top str brk =
    sys (Top,Top,Top) (d-1) (strip t)

temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

fun pconPrint sys d t Top str brk =
  let
    open Portable smpp
    val terms = #1(listSyntax.dest_list (strip t))
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >> (printTerms xs)
  in
    str "(" >> printTerms terms >>str ")"
  end;
    
temp_add_user_printer ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
temp_add_user_printer ("conprint", ``Con NONE x``,genPrint pconPrint);

fun litPrint


fullEval ``"val (x,y,z) = (1,2,3);"``
fullEval ``"val x = (2,(),true);"``

"val x = let val y = 2 in y + 1 end;"

val p = `` "val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f 3 end;"``
val asts = eval ``get_all_asts ^(p)``
"val it = case f x of true => 1;"
"val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f end 3;"
