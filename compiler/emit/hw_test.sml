open HolKernel boolLib bossLib
open test_compilerLib ml_translatorLib hw_bytecodeML

fun text_to_file lines filename = let
  val t = TextIO.openOut(filename)
  val _ = print ("\nWriting file: " ^ filename ^ "\n\n")
  val _ = map (fn s => (print s ; TextIO.output(t,s))) lines
  val _ = TextIO.closeOut(t)
  val _ = print ("\n")
  in () end;

fun digit_to_hex i =
  if i < 10 then implode [chr (ord #"0" + i)] else
  if i < 16 then implode [chr (ord #"a" + (i-10))] else
  raise Fail "digit_to_hex"

fun int_to_hex i 0 = ""
  | int_to_hex i n = int_to_hex (i div 16) (n-1) ^ digit_to_hex (i mod 16)

fun int_to_file filename xs = let
  fun take n [] = []
    | take 0 xs = []
    | take n xs = hd xs :: take (n-1) (tl xs)
  fun drop n [] = []
    | drop 0 xs = xs
    | drop n xs = drop (n-1) (tl xs)
  fun split n [] = []
    | split n xs = let
    val (ys1,ys2) = (take 8 xs, drop 8 xs)
    in (n,ys1) :: split (n+8) ys2 end
  val ys = split 0 xs
  fun format_line (n,zs) = let
    val s = int_to_hex n 4 ^ " "
    in foldl (fn (x,y) => y ^ " " ^ x) s (map (fn n => int_to_hex n 2)
zs) ^ "\n" end
  val lines = map format_line ys
  in text_to_file lines filename end;

val w2i = valOf o numML.toInt o wordsML.w2n

fun mk_test_ds f =
  int_to_file (f^".txt") o map (w2i o hw_encode) o full_hwml o
  bc_state_code o fst o prep_decs_exp inits

fun mk_test f e = mk_test_ds f ([],e)

val tr_exp = rand o rator o concl o hol2deep

val _ = mk_test "hwt0" (tr_exp ``42:num``)

val _ = mk_test "hwt1" (tr_exp ``1+1:num``)

val _ = mk_test "hwt2" (tr_exp ``let x = F in if ¬x then 0 else 1``)

val t = Define `test = EL 3 (QSORT (\m n. m <= n) [3;5;1;9;8;5;4:num])`;
val _ = reset_translation ()
val _ = translate listTheory.APPEND;
val _ = translate sortingTheory.PART_DEF;
val _ = translate sortingTheory.PARTITION_DEF;
val _ = translate sortingTheory.QSORT_DEF;
val _ = translate listTheory.HD;
val _ = translate listTheory.TL;
val _ = translate listTheory.EL;
val _ = translate t
val _ = finalise_translation ();
val ds = dest_list I (get_decls())
val _ = mk_test_ds "hwt3" (ds,``Var "test"``)

val t = Define `test = HD [1;0:num]`
val _ = reset_translation()
val _ = translate listTheory.HD
val _ = translate t
val _ = finalise_translation ()
val ds = dest_list I (get_decls())
val _ = mk_test_ds "hwt4" (ds, ``Var "test"``)

val t = Define `test = EL 4 ([1;2;3] ++ [4;5;6])`
val _ = reset_translation()
val _ = translate listTheory.APPEND
val _ = translate listTheory.HD
val _ = translate listTheory.TL;
val _ = translate listTheory.EL;
val _ = translate t
val _ = finalise_translation ()
val ds = dest_list I (get_decls())
val _ = mk_test_ds "hwt5" (ds, ``Var "test"``)
