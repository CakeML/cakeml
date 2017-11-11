open preamble;

val _ = new_theory "cfFFIType"

(*

This file defines a tyep (abbreviation) that behaves like the
following type:

val _ = Datatype `
  ffi = Str string
      | Num num
      | Cons ffi ffi
      | List (ffi list)
      | Stream (num llist)
      | Seq (num -> ffi)

The type is missing a cases thm and an ind thm.

*)

val _ = Datatype `
  inner_ffi = iNum num
            | iStr string
            | iStream (num llist)`

val _ = type_abbrev("ffi",``:num -> inner_ffi``)

(* constructors *)

val Num_def = zDefine `
  ((Num i):ffi) =
    \n. if n = 0 then iNum 0 else iNum i`

val Str_def = zDefine `
  ((Str i):ffi) =
    \n. if n = 0 then iNum 1 else iStr i`

val Cons_def = zDefine `
  ((Cons (x:ffi) (y:ffi)):ffi) =
    \n. if n = 0 then iNum 2 else
          let n = n - 1 in
            if EVEN n then x (n DIV 2) else y (n DIV 2)`

val List_def = zDefine `
  ((List (xs:ffi list)):ffi) =
    \n. if n = 0 then iNum 3 else FOLDR Cons (Num 0) xs (n-1) `

val Stream_def = zDefine `
  ((Stream i):ffi) =
    \n. if n = 0 then iNum 4 else iStream i`

val factor_count_def = Define `
  factor_count k n =
    if k <= 1 then 0n else
    if n = 0n then 0 else
    if n MOD k = 0 then 1 + factor_count k (n DIV k) else 0`

val Seq_def = zDefine `
  ((Seq (f:num -> ffi)):ffi) =
    \n. if n = 0 then iNum 5 else
          let n = n - 1 in
            f (factor_count 2 n) (factor_count 3 n)`;

(* injectivity *)

val Num_11 = store_thm("Num_11[simp]",
  ``!n1 n2. Num n1 = Num n2 <=> n1 = n2``,
  fs [Num_def,FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `1` mp_tac) \\ fs []);

val Str_11 = store_thm("Str_11[simp]",
  ``!n1 n2. Str n1 = Str n2 <=> n1 = n2``,
  fs [Str_def,FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `1` mp_tac) \\ fs []);

val Cons_11 = store_thm("Cons_11[simp]",
  ``!x1 x2 y1 y2. Cons x1 x2 = Cons y1 y2 <=> x1 = y1 /\ x2 = y2``,
  fs [Cons_def,FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (pop_assum (qspec_then `2 * x + 1` mp_tac) \\ fs []
    \\ fs [FUN_EQ_THM,EVEN_DOUBLE]
    \\ once_rewrite_tac [MULT_COMM]
    \\ simp [MULT_DIV,DIV_MULT] \\ rw [])
  THEN1
   (pop_assum (qspec_then `2 * x + 2` mp_tac) \\ fs []
    \\ fs [FUN_EQ_THM,EVEN_DOUBLE]
    \\ once_rewrite_tac [MULT_COMM]
    \\ simp [MULT_DIV,DIV_MULT] \\ rw []
    \\ fs [EVEN_ODD,GSYM ADD1,ODD_DOUBLE]));

val Cons_NOT_Num = prove(
  ``Cons x y <> Num z``,
  fs [FUN_EQ_THM] \\ qexists_tac `0` \\ fs [Cons_def,Num_def]);

val List_11 = store_thm("List_11[simp]",
  ``!xs ys. List xs = List ys <=> xs = ys``,
  rw [] \\ eq_tac \\ rw []
  \\ fs [List_def,FUN_EQ_THM]
  \\ pop_assum (mp_tac o Q.GEN `n` o Q.SPEC `n+1`)
  \\ fs [GSYM FUN_EQ_THM]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ qspec_tac (`ys`,`ys`)
  \\ Induct_on `xs` \\ Cases_on `ys` \\ fs [Cons_NOT_Num]);

val Stream_11 = store_thm("Stream_11[simp]",
  ``!n1 n2. Stream n1 = Stream n2 <=> n1 = n2``,
  fs [Stream_def,FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `1` mp_tac) \\ fs []);

val factor_count_2 = prove(
  ``!m n. factor_count 2 (2 ** m * 3 ** n) = m``,
  Induct \\ once_rewrite_tac [factor_count_def] \\ fs []
  \\ fs [EXP,ADD1] \\ once_rewrite_tac [MULT_COMM] \\ fs [MULT_DIV]);

val factor_count_3 = prove(
  ``!m n. factor_count 3 (3 ** m * 2 ** n) = m``,
  Induct \\ once_rewrite_tac [factor_count_def] \\ fs []
  \\ fs [EXP,ADD1] \\ once_rewrite_tac [MULT_COMM] \\ fs [MULT_DIV]
  \\ rw [] \\ pop_assum mp_tac \\ fs []
  \\ Induct_on `n` \\ fs [EXP]
  \\ once_rewrite_tac [GSYM (MATCH_MP MOD_TIMES2 (DECIDE ``0<3n``))]
  \\ Cases_on `2 ** n MOD 3` \\ fs []
  \\ Cases_on `n'` \\ fs []
  \\ Cases_on `n''` \\ fs []
  \\ `2 ** n MOD 3 < 3` by fs []
  \\ rev_full_simp_tac bool_ss [] \\ fs [ADD1]);

val Seq_11 = store_thm("Seq_11[simp]",
  ``Seq f1 = Seq f2 <=> f1 = f2``,
  eq_tac \\ rw [] \\ fs [FUN_EQ_THM,Seq_def] \\ rw []
  \\ pop_assum (qspec_then `2 ** x * 3 ** x' + 1` mp_tac)
  \\ fs [factor_count_3,factor_count_2]
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs [factor_count_3,factor_count_2]);

(* distinctness *)

val ffi_distinct = prove(
  ``ALL_DISTINCT [Num n; Str s; Cons x y; List l; Stream ll; Seq f]``,
  rw [] \\ fs [FUN_EQ_THM] \\ qexists_tac `0`
  \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def])
  |> SIMP_RULE std_ss [ALL_DISTINCT,MEM,GSYM CONJ_ASSOC] |> GEN_ALL
  |> curry save_thm "ffi_distinct[simp]";

(* destructors *)

val destNum_def = new_specification("destNum_def",["destNum"],prove(``
  ?destNum.
    (!n. destNum (Num n) = SOME n) /\
    (!s. destNum (Str s) = NONE) /\
    (!x y. destNum (Cons x y) = NONE) /\
    (!l. destNum (List l) = NONE) /\
    (!ll. destNum (Stream ll) = NONE) /\
    (!f. destNum (Seq f) = NONE)``,
  qexists_tac `\f. if f 0 = iNum 0 then SOME (@n. Num n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]));
val _ = export_rewrites ["destNum_def"];

val destStr_def = new_specification("destStr_def",["destStr"],prove(``
  ?destStr.
    (!n. destStr (Num n) = NONE) /\
    (!s. destStr (Str s) = SOME s) /\
    (!x y. destStr (Cons x y) = NONE) /\
    (!l. destStr (List l) = NONE) /\
    (!ll. destStr (Stream ll) = NONE) /\
    (!f. destStr (Seq f) = NONE)``,
  qexists_tac `\f. if f 0 = iNum 1 then SOME (@n. Str n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]));
val _ = export_rewrites ["destStr_def"];

val destStr_o_Str = Q.store_thm("destStr_o_Str[simp]",
  `destStr o Str = SOME`, rw[FUN_EQ_THM]);

val destCons_def = new_specification("destCons_def",["destCons"],prove(``
  ?destCons.
    (!n. destCons (Num n) = NONE) /\
    (!s. destCons (Str s) = NONE) /\
    (!x y. destCons (Cons x y) = SOME (x,y)) /\
    (!l. destCons (List l) = NONE) /\
    (!ll. destCons (Stream ll) = NONE) /\
    (!f. destCons (Seq f) = NONE)``,
  qexists_tac `\f. if f 0 = iNum 2 then SOME (@n. Cons (FST n) (SND n) = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]
  \\ `!n. FST n = x ∧ SND n = y <=> n = (x,y)` by fs [FORALL_PROD]
  \\ asm_rewrite_tac [] \\ fs []));
val _ = export_rewrites ["destCons_def"];

val destList_def = new_specification("destList_def",["destList"],prove(``
  ?destList.
    (!n. destList (Num n) = NONE) /\
    (!s. destList (Str s) = NONE) /\
    (!x y. destList (Cons x y) = NONE) /\
    (!l. destList (List l) = SOME l) /\
    (!ll. destList (Stream ll) = NONE) /\
    (!f. destList (Seq f) = NONE)``,
  qexists_tac `\f. if f 0 = iNum 3 then SOME (@n. List n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]));
val _ = export_rewrites ["destList_def"];

val destStream_def = new_specification("destStream_def",["destStream"],prove(``
  ?destStream.
    (!n. destStream (Num n) = NONE) /\
    (!s. destStream (Str s) = NONE) /\
    (!x y. destStream (Cons x y) = NONE) /\
    (!l. destStream (List l) = NONE) /\
    (!ll. destStream (Stream ll) = SOME ll) /\
    (!f. destStream (Seq f) = NONE)``,
  qexists_tac `\f. if f 0 = iNum 4 then SOME (@n. Stream n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]));
val _ = export_rewrites ["destStream_def"];

val destSeq_def = new_specification("destSeq_def",["destSeq"],prove(``
  ?destSeq.
    (!n. destSeq (Num n) = NONE) /\
    (!s. destSeq (Str s) = NONE) /\
    (!x y. destSeq (Cons x y) = NONE) /\
    (!l. destSeq (List l) = NONE) /\
    (!ll. destSeq (Stream ll) = NONE) /\
    (!f. destSeq (Seq f) = SOME f)``,
  qexists_tac `\f. if f 0 = iNum 5 then SOME (@n. Seq n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Seq_def]));
val _ = export_rewrites ["destSeq_def"];

val _ = export_theory()
