(*
  Defines a type that can be used for embedding different FFI models
  for parts of the FFI state.
*)
open preamble;

val _ = new_theory "cfFFIType"

(*

This file defines a type that behaves like the following one:

  ffi = Str string
      | Num num
      | Cons ffi ffi
      | List (ffi list)
      | Stream (num llist)
      | Fun (ffi_inner -> ffi)
      | Inner ffi_inner

  ffi_inner = iStr string
            | iNum num
            | iCons ffi_inner ffi_inner
            | iList (ffi_inner list)
            | iStream (num llist)

The ffi type is missing an nchotomy thm and an induction thm, but the
important injectivity (suffix: "_11") are here.

*)

val _ = Datatype `
  ffi_inner = iStr string
            | iNum num
            | iCons ffi_inner ffi_inner
            | iList (ffi_inner list)
            | iStream (num llist)`

val _ = Datatype `
  ffi = FFI_TYPE (ffi_inner -> ffi_inner)`

val ffi_app_def = Define `
  ffi_app x n = case x of FFI_TYPE f => f n`;

(* constructors *)

val Num_def = zDefine `
  ((Num i):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 0 else iNum i)`

val Str_def = zDefine `
  ((Str i):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 1 else iStr i)`

val Cons_def = zDefine `
  ((Cons (x:ffi) (y:ffi)):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 2 else
                    case n of
                    | iCons (iNum 0) m => ffi_app x m
                    | iCons (iNum 1) m => ffi_app y m
                    | _ => iNum 0)`

val List_def = zDefine `
  ((List (xs:ffi list)):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 3 else
                  if n = iNum 1 then iNum (LENGTH xs) else
                    case n of
                    | iCons (iNum k) m => ffi_app (EL k xs) m
                    | _ => iNum 0)`

val Stream_def = zDefine `
  ((Stream i):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 4 else iStream i)`

val Fun_def = zDefine `
  ((Fun (f:ffi_inner -> ffi)):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 5 else
                    case n of
                    | iCons x y => ffi_app (f x) y
                    | _ => iNum 0)`;

val Inner_def = zDefine `
  ((Inner i):ffi) =
    FFI_TYPE (\n. if n = iNum 0 then iNum 6 else i)`;

(* injectivity *)

Theorem Num_11[simp]:
   !n1 n2. Num n1 = Num n2 <=> n1 = n2
Proof
  fs [Num_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []
QED

Theorem Str_11[simp]:
   !n1 n2. Str n1 = Str n2 <=> n1 = n2
Proof
  fs [Str_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []
QED

Theorem Cons_11[simp]:
   !x1 x2 y1 y2. Cons x1 x2 = Cons y1 y2 <=> x1 = y1 /\ x2 = y2
Proof
  rpt Cases
  \\ fs [Cons_def,FUN_EQ_THM,ffi_app_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (pop_assum (qspec_then `iCons (iNum 0) x` mp_tac) \\ fs [])
  THEN1 (pop_assum (qspec_then `iCons (iNum 1) x` mp_tac) \\ fs [])
QED

Theorem List_11[simp]:
   !xs ys. List xs = List ys <=> xs = ys
Proof
  fs [List_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ fs [LIST_EQ_REWRITE] \\ rw []
  THEN1 (pop_assum (qspec_then `iNum 1` mp_tac) \\ fs [])
  \\ Cases_on `EL x xs`
  \\ Cases_on `EL x ys`
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `iCons (iNum x) x'` mp_tac)
  \\ fs [ffi_app_def]
QED

Theorem Stream_11[simp]:
   !n1 n2. Stream n1 = Stream n2 <=> n1 = n2
Proof
  fs [Stream_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []
QED

Theorem Fun_11[simp]:
   Fun f1 = Fun f2 <=> f1 = f2
Proof
  eq_tac \\ rw [] \\ fs [FUN_EQ_THM,Fun_def] \\ rw []
  \\ Cases_on `f1 x`
  \\ Cases_on `f2 x`
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ first_x_assum (qspec_then `iCons x x'` mp_tac) \\ fs [ffi_app_def]
QED

Theorem Inner_11[simp]:
   !n1 n2. Inner n1 = Inner n2 <=> n1 = n2
Proof
  fs [Inner_def,FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
  \\ pop_assum (qspec_then `iNum 1` mp_tac) \\ fs []
QED

(* distinctness *)

val ffi_distinct = prove(
  ``ALL_DISTINCT [Num n; Str s; Cons x y; List l; Stream ll; Fun f; Inner i]``,
  rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Stream_def,
               Fun_def,Inner_def,FUN_EQ_THM]
  \\ qexists_tac `iNum 0` \\ fs [])
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
    (!f. destNum (Fun f) = NONE) /\
    (!i. destNum (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 0
                    then SOME (@n. Num n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destNum_def"];

val destStr_def = new_specification("destStr_def",["destStr"],prove(``
  ?destStr.
    (!n. destStr (Num n) = NONE) /\
    (!s. destStr (Str s) = SOME s) /\
    (!x y. destStr (Cons x y) = NONE) /\
    (!l. destStr (List l) = NONE) /\
    (!ll. destStr (Stream ll) = NONE) /\
    (!f. destStr (Fun f) = NONE) /\
    (!i. destStr (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 1
                    then SOME (@n. Str n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destStr_def"];

Theorem destStr_o_Str[simp]:
   destStr o Str = SOME
Proof
rw[FUN_EQ_THM]
QED

val destCons_def = new_specification("destCons_def",["destCons"],prove(``
  ?destCons.
    (!n. destCons (Num n) = NONE) /\
    (!s. destCons (Str s) = NONE) /\
    (!x y. destCons (Cons x y) = SOME (x,y)) /\
    (!l. destCons (List l) = NONE) /\
    (!ll. destCons (Stream ll) = NONE) /\
    (!f. destCons (Fun f) = NONE) /\
    (!i. destCons (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 2
                    then SOME (@n. Cons (FST n) (SND n) = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]
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
    (!f. destList (Fun f) = NONE) /\
    (!i. destList (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 3
                    then SOME (@n. List n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destList_def"];

val destStream_def = new_specification("destStream_def",["destStream"],prove(``
  ?destStream.
    (!n. destStream (Num n) = NONE) /\
    (!s. destStream (Str s) = NONE) /\
    (!x y. destStream (Cons x y) = NONE) /\
    (!l. destStream (List l) = NONE) /\
    (!ll. destStream (Stream ll) = SOME ll) /\
    (!f. destStream (Fun f) = NONE) /\
    (!i. destStream (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 4
                    then SOME (@n. Stream n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destStream_def"];

val destFun_def = new_specification("destFun_def",["destFun"],prove(``
  ?destFun.
    (!n. destFun (Num n) = NONE) /\
    (!s. destFun (Str s) = NONE) /\
    (!x y. destFun (Cons x y) = NONE) /\
    (!l. destFun (List l) = NONE) /\
    (!ll. destFun (Stream ll) = NONE) /\
    (!f. destFun (Fun f) = SOME f) /\
    (!i. destFun (Inner i) = NONE)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 5
                    then SOME (@n. Fun n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destFun_def"];

val destInner_def = new_specification("destInner_def",["destInner"],prove(``
  ?destInner.
    (!n. destInner (Num n) = NONE) /\
    (!s. destInner (Str s) = NONE) /\
    (!x y. destInner (Cons x y) = NONE) /\
    (!l. destInner (List l) = NONE) /\
    (!ll. destInner (Stream ll) = NONE) /\
    (!f. destInner (Fun f) = NONE) /\
    (!i. destInner (Inner i) = SOME i)``,
  qexists_tac `(\f. if ffi_app f (iNum 0) = iNum 6
                    then SOME (@n. Inner n = f) else NONE)`
  \\ rw [] \\ fs [Num_def,Str_def,Cons_def,List_def,Inner_def,
                  Stream_def,Fun_def,ffi_app_def]));
val _ = export_rewrites ["destInner_def"];

val dest_iStr_def = Define`
  dest_iStr (iStr s) = s`;
val _ = export_rewrites ["dest_iStr_def"];

(* clean up *)

val _ = map delete_binding ["ffi_app_def","Num_def","Str_def",
          "Cons_def","List_def","Stream_def","Fun_def","Inner_def"];

val _ = delete_const "ffi_app";

val _ = export_theory()
