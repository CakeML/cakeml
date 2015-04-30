open HolKernel boolLib bossLib x64_heapTheory pred_setTheory pred_setSyntax listSyntax helperLib wordsTheory wordsSyntax numSyntax fooTheory listTheory lcsymtacs x64_code_evalTheory intSimps

val _ = new_theory"x64_repl"

val _ = Globals.max_print_depth := 15

val INSERT_TO_UNION = prove(
  ``$INSERT x = $UNION {x}``,
  REWRITE_TAC[FUN_EQ_THM,Once INSERT_SING_UNION])

val add_conv =
  PURE_REWRITE_CONV[
    equal_code_def,
    print_code_def,
    bignum_code_def,
    lex_code_def,
    alloc_code_def,
    error_code_def,
    install_and_run_code_def,
    word_add_n2w] THENC
  SIMP_CONV (pure_ss ++ ARITH_ss) []

val th1 =
  x64_repl_implementation_def
  |> Q.SPEC`0w`
  |> PURE_ONCE_REWRITE_RULE[INSERT_TO_UNION]
  |> PURE_ONCE_REWRITE_RULE[WORD_ADD_0]
  |> PURE_ONCE_REWRITE_RULE[UNION_EMPTY]

val tm1 =
  th1 |> concl |> rhs |> list_dest dest_union
  |> all_distinct

val tm2 =
  tm1 |> List.filter (not o is_insert) |> map add_conv

val cs = intSimps.int_compset()
val () = wordsLib.add_words_compset true cs
val () = computeLib.add_thms[bc_compileTheory.bc_compile_rev_eval] cs
val weval = computeLib.CBV_CONV cs

val tm3 =
  List.find(can (find_term (same_const``bootstrap_code``)))tm1
  |> valOf
  |> (ONCE_REWRITE_CONV [bootstrap_code_eq] THENC
      REWRITE_CONV [x64_code_EQ_bc_compile,bc_compileTheory.bc_compile_rev_thm])

val tm4 = tm3 |> time (CONV_RULE(RAND_CONV  weval))

val rwth = prove(``({(x,y)} = {(x,b)}) ⇔ (y = b)``, rw[])
val thb = tm4 |> CONV_RULE(REWR_CONV rwth)

val th2 =
  x64_repl_implementation_def
  |> Q.SPEC`0w`
  |> PURE_REWRITE_RULE[INSERT_UNION_EQ,UNION_EMPTY,GSYM UNION_ASSOC]
  |> PURE_ONCE_REWRITE_RULE[WORD_ADD_0]
  |> PURE_REWRITE_RULE tm2
  |> PURE_REWRITE_RULE[INSERT_UNION_EQ,UNION_EMPTY,GSYM UNION_ASSOC]

val th3 =
  th2 |> PURE_ONCE_REWRITE_RULE[thb]

val tm5 =
  th3 |> concl |> rhs |> list_dest dest_insert

val _ = if is_empty (last tm5) then () else failwith"not empty"

val tm6 =
  tm5 |> butlast |> all_distinct

(*
val check2 =
  tm5 |> List.filter (not o is_insert) |> map add_conv

val check3 =
  List.find(can (find_term (same_const``bootstrap_code``)))tm5
*)

val cs = tm6

fun n2w_to_int tm =
  let
    val tm = if is_w2w tm then rhs(concl(EVAL tm)) else tm
    val tm = if is_numeral (rand tm) then tm else
               rhs(concl(RAND_CONV(EVAL) tm))
    fun aux tm = tm |> dest_n2w |> fst |> int_of_term
    val n = aux tm
  in
    if n < 256 then n else
      tm |> (ONCE_REWRITE_CONV [GSYM n2w_mod] THENC EVAL)
         |> concl |> rand |> aux
  end

fun int_to_hex x =
  String.concat["0x",Arbnum.toHexString (Arbnum.fromInt x)]

fun commas [] = ""
  | commas [x] = x
  | commas (x::y) = String.concat[x,", ",commas y]

val int_list_to_hex = commas o (map int_to_hex)

fun int_list_to_foo x =
  String.concat["\t.byte\t",int_list_to_hex x,"\n"]

val filename = "wrapper/asm_code.s"

fun write_code_to_file filename cs = let
  val vs = map (pairSyntax.dest_pair) cs
  val vs = map (fn (x,y) => (n2w_to_int x, map n2w_to_int (fst (dest_list y)))) vs
  val vs = sort (fn (x,_) => fn (y:int,_) => x <= y) vs
  fun del_repetations (x::y::xs) = if x = y then del_repetations (x::xs) else
                                            x :: del_repetations (y::xs)
    | del_repetations zs = zs
  val vs = del_repetations vs
  fun no_duplicates (x::y::xs) =
        if fst x = fst y then failwith"duplicate" else no_duplicates (y::xs)
    | no_duplicates _ = true
  val _ = no_duplicates vs
  fun no_holes i [] = true
    | no_holes i ((j,c)::xs) =
       if i = j then no_holes (i + (length c)) xs
                else (print("hole at "^(Int.toString i)^"\n");
                      no_holes (fst(hd xs)) xs)
  val _ = no_holes 0 vs
  val vs = map snd vs
  val ws = flatten vs
  val _ = print ("Exporting " ^ int_to_string (length ws) ^ "-byte binary ... ")
  val t = TextIO.openOut(filename)
  fun produce_output xs = let
    val str = int_list_to_foo xs
    in TextIO.output(t,str) end
  fun split8 (x1::x2::x3::x4::x5::x6::x7::x8::xs) = let
      val _ = produce_output (x1::x2::x3::x4::x5::x6::x7::x8::[])
      in split8 xs end
    | split8 xs = produce_output xs
  val _ = split8 ws
  val _ = TextIO.closeOut(t)
  val _ = print ("done.\n")
  in () end;

val _ = write_code_to_file filename cs;

val _ = export_theory()
