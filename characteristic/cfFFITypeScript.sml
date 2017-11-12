open preamble;

val _ = new_theory "cfFFIType"

(*

This file defines a type (abbreviation) that behaves like the
following type:

  ffi = Str string
      | Num num
      | Cons ffi ffi
      | List (ffi list)
      | Stream (num llist)
      | Fun (ffi_inner -> ffi)

  ffi_inner = iStr string
            | iNum num
            | iCons ffi_inner ffi_inner
            | iList (ffi_inner list)
            | iStream (num llist)

The type is missing a cases thm and an ind thm.

*)

val _ = Datatype `
  ffi_inner = iStr string
            | iNum num
            | iCons ffi_inner ffi_inner
            | iList (ffi_inner list)
            | iStream (num llist)`

val _ = type_abbrev("ffi",``:ffi_inner -> ffi_inner``)

(* constructors *)

val Num_def = zDefine `
  ((Num i):ffi) =
    \n. if n = iNum 0 then iNum 0 else iNum i`

val Str_def = zDefine `
  ((Str i):ffi) =
    \n. if n = iNum 0 then iNum 1 else iStr i`

val Cons_def = zDefine `
  ((Cons (x:ffi) (y:ffi)):ffi) =
    \n. if n = iNum 0 then iNum 2 else
          case n of
          | iCons (iNum 0) m => x m
          | iCons (iNum 1) m => y m
          | _ => iNum 0`

val List_def = zDefine `
  ((List (xs:ffi list)):ffi) =
    \n. if n = iNum 0 then iNum 3 else
        if n = iNum 1 then iNum (LENGTH xs) else
          case n of
          | iCons (iNum k) m => EL k xs m
          | _ => iNum 0`

val Stream_def = zDefine `
  ((Stream i):ffi) =
    \n. if n = iNum 0 then iNum 4 else iStream i`

val Fun_def = zDefine `
  ((Fun (f:ffi_inner -> ffi)):ffi) =
    \n. if n = iNum 0 then iNum 5 else
          case n of
          | iCons x y => f x y
          | _ => iNum 0`;

(*

val factor_count_def = Define `
  factor_count k n =
    if k <= 1 then 0n else
    if n = 0n then 0 else
    if n MOD k = 0 then 1 + factor_count k (n DIV k) else 0`

val Fun_def = zDefine `
  ((Fun (f:num -> ffi)):ffi) =
    \n. if n = 0 then iNum 5 else
          let n = n - 1 in
            f (factor_count 2 n) (factor_count 3 n)`;
*)

(* injectivity *)

val Num_11 = store_thm("Num_11[simp]",
  ``!n1 n2. Num n1 = Num n2 <=> n1 = n2``,
  fs [Num_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []);

val Str_11 = store_thm("Str_11[simp]",
  ``!n1 n2. Str n1 = Str n2 <=> n1 = n2``,
  fs [Str_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []);

val Cons_11 = store_thm("Cons_11[simp]",
  ``!x1 x2 y1 y2. Cons x1 x2 = Cons y1 y2 <=> x1 = y1 /\ x2 = y2``,
  fs [Cons_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (pop_assum (qspec_then `iCons (iNum 0) x` mp_tac) \\ fs [])
  THEN1 (pop_assum (qspec_then `iCons (iNum 1) x` mp_tac) \\ fs []));

val List_11 = store_thm("List_11[simp]",
  ``!xs ys. List xs = List ys <=> xs = ys``,
  fs [List_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [LIST_EQ_REWRITE] \\ rw []
  THEN1 (pop_assum (qspec_then `iNum 1` mp_tac) \\ fs [])
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ qmatch_goalsub_rename_tac `EL i _ j`
  \\ first_x_assum (qspec_then `iCons (iNum i) j` mp_tac) \\ fs []);

val Stream_11 = store_thm("Stream_11[simp]",
  ``!n1 n2. Stream n1 = Stream n2 <=> n1 = n2``,
  fs [Stream_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []);

val Fun_11 = store_thm("Fun_11[simp]",
  ``Fun f1 = Fun f2 <=> f1 = f2``,
  eq_tac \\ rw [] \\ fs [FUN_EQ_THM,Fun_def] \\ rw []
  \\ qmatch_goalsub_rename_tac `f1 i j`
  \\ first_x_assum (qspec_then `iCons i j` mp_tac) \\ fs []);

(* distinctness *)

val ffi_distinct = prove(
  ``ALL_DISTINCT [Num n; Str s; Cons x y; List l; Stream ll; Fun f]``,
  rw [] \\ fs [FUN_EQ_THM] \\ qexists_tac `iNum 0`
  \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def])
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
    (!f. destNum (Fun f) = NONE)``,
  qexists_tac `\f. if f (iNum 0) = iNum 0 then SOME (@n. Num n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]));
val _ = export_rewrites ["destNum_def"];

val destStr_def = new_specification("destStr_def",["destStr"],prove(``
  ?destStr.
    (!n. destStr (Num n) = NONE) /\
    (!s. destStr (Str s) = SOME s) /\
    (!x y. destStr (Cons x y) = NONE) /\
    (!l. destStr (List l) = NONE) /\
    (!ll. destStr (Stream ll) = NONE) /\
    (!f. destStr (Fun f) = NONE)``,
  qexists_tac `\f. if f (iNum 0) = iNum 1 then SOME (@n. Str n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]));
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
    (!f. destCons (Fun f) = NONE)``,
  qexists_tac `\f. if f (iNum 0) = iNum 2
                   then SOME (@n. Cons (FST n) (SND n) = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]
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
    (!f. destList (Fun f) = NONE)``,
  qexists_tac `\f. if f (iNum 0) = iNum 3 then SOME (@n. List n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]));
val _ = export_rewrites ["destList_def"];

val destStream_def = new_specification("destStream_def",["destStream"],prove(``
  ?destStream.
    (!n. destStream (Num n) = NONE) /\
    (!s. destStream (Str s) = NONE) /\
    (!x y. destStream (Cons x y) = NONE) /\
    (!l. destStream (List l) = NONE) /\
    (!ll. destStream (Stream ll) = SOME ll) /\
    (!f. destStream (Fun f) = NONE)``,
  qexists_tac `\f. if f (iNum 0) = iNum 4 then SOME (@n. Stream n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]));
val _ = export_rewrites ["destStream_def"];

val destFun_def = new_specification("destFun_def",["destFun"],prove(``
  ?destFun.
    (!n. destFun (Num n) = NONE) /\
    (!s. destFun (Str s) = NONE) /\
    (!x y. destFun (Cons x y) = NONE) /\
    (!l. destFun (List l) = NONE) /\
    (!ll. destFun (Stream ll) = NONE) /\
    (!f. destFun (Fun f) = SOME f)``,
  qexists_tac `\f. if f (iNum 0) = iNum 5 then SOME (@n. Fun n = f) else NONE`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,Fun_def]));
val _ = export_rewrites ["destFun_def"];

val _ = map delete_binding ["Num_def","Str_def",
          "Cons_def","List_def","Stream_def","Fun_def"]

val _ = export_theory()
