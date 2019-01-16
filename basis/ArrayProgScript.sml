(*
  A module about Arrays for the CakeML standard basis library.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word8ArrayProgTheory

val _ = new_theory"ArrayProg"

val _ = translation_extends"Word8ArrayProg"

val () = ml_prog_update (open_module "Array");

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a"] "array" (Atapp [Atvar "'a"] (Short "array"))`` I);

val () = append_decs
   ``[mk_binop "array" Aalloc;
      mk_unop "arrayEmpty" AallocEmpty;
      mk_binop "sub" Asub;
      mk_unop "length" Alength;
      Dlet unknown_loc (Pvar "update")
       (Fun "x" (Fun "y" (Fun "z"
         (App Aupdate [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``;

val array_fromList = process_topdecs
  `fun fromList l =
    let fun f arr l i =
       case l of
          [] => arr
        | (h::t) => (update arr i h; f arr t (i + 1))
    in
      case l of
        [] => arrayEmpty ()
      | h::t => f (array (List.length l) h) t 1
    end`;

val _ = append_prog array_fromList;

val array_tabulate = process_topdecs
  `fun tabulate n f =
    let fun u arr x =
        if x = n then arr
        else (update arr x (f x); u arr (x + 1))
    in
      if n = 0 then
        arrayEmpty ()
      else
        u (array n (f 0)) 1
    end`;

val _ = append_prog array_tabulate;

(*val array_vector = process_topdecs
  `fun vector arr = Vector.tabulate (length arr) (fn i => sub arr i)`*)

val array_copy = process_topdecs
  `fun copy_aux src dst di max n =
    if n = max
      then ()
    else (update dst di (sub src n); copy_aux src dst (di + 1) max (n + 1))

  fun copy src dst di =
    copy_aux src dst di (length src) 0`

val _ = append_prog array_copy;

val array_copyVec = process_topdecs
  `fun copyVec_aux src dst di max n =
    if n = max
        then ()
    else (update dst (di + n) (Vector.sub src n); copyVec_aux src dst di max (n + 1))

  fun copyVec src dst di =
    copyVec_aux src dst di (Vector.length src) 0`

val _ = append_prog array_copyVec;

val array_app = process_topdecs
  `fun app_aux f arr max n =
    if n = max
      then ()
    else (f (sub arr n); app_aux f arr max (n + 1))

  fun app f arr =
    app_aux f arr (length arr) 0`

val _ = append_prog array_app;

val array_appi = process_topdecs
  `fun appi_aux f arr max n =
    if n = max
      then ()
    else (f n (sub arr n); app_aux f arr max (n + 1))

  fun appi f arr =
    appi_aux f arr (length arr) 0`

val _ = append_prog array_appi;

val array_modify = process_topdecs
  `fun modify_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f (sub arr n)); modify_aux f arr max (n + 1))

  fun modify f arr =
    modify_aux f arr (length arr) 0`

val _ = append_prog array_modify;

val array_modifyi = process_topdecs
  `fun modifyi_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f n (sub arr n)); modifyi_aux f arr max (n + 1))

  fun modifyi f arr =
    modifyi_aux f arr (length arr) 0`

val _ = append_prog array_modifyi;

val array_foldli = process_topdecs
  `fun foldli_aux f init arr max n =
    if n = max
      then init
    else foldli_aux f (f n (sub arr n) init ) arr max (n + 1)

  fun foldli f init arr =
    foldli_aux f init arr (length arr) 0`

val _ = append_prog array_foldli;

val array_foldl = process_topdecs
  `fun foldl_aux f init arr max n =
    if n = max
      then init
    else foldl_aux f (f (sub arr n) init ) arr max (n + 1)

  fun foldl f init arr =
    foldl_aux f init arr (length arr) 0`

val _ = append_prog array_foldl;

val array_foldri = process_topdecs
  `fun foldri_aux f init arr n =
    if n = 0
      then init
    else foldri_aux f (f (n - 1) (sub arr (n - 1)) init) arr (n - 1)

  fun foldri f init arr =
    foldri_aux f init arr (length arr)`

val _ = append_prog array_foldri;

val array_foldr = process_topdecs
  `fun foldr_aux f init arr n =
    if n = 0
      then init
    else foldr_aux f (f (sub arr (n - 1)) init) arr (n - 1)

  fun foldr f init arr =
    foldr_aux f init arr (length arr)`

val _ = append_prog array_foldr;

val array_find = process_topdecs
  `fun find_aux f arr max n =
    if n = max
      then None
    else (if f (sub arr n)
        then Some(sub arr n)
      else find_aux f arr max (n + 1))

  fun find f arr =
    find_aux f arr (length arr) 0`

val _ = append_prog array_find;

(* Parser bug, see Issue #25 *)
val array_findi_aux =
``[(Dletrec unknown_loc
[("findi_aux","f",
 Fun "arr"
   (Fun "max"
      (Fun "n"
         (Let (SOME "a")
            (App Opapp
               [App Opapp [Var (Short "="); Var (Short "n")];
                Var (Short "max")])
            (If (Var (Short "a")) (Con (SOME (Short "None")) [])
               (Let (SOME "b")
                  (App Opapp
                     [App Opapp
                        [Var (Short "sub"); Var (Short "arr")];
                      Var (Short "n")])
                  (Let (SOME "c")
                     (App Opapp
                        [App Opapp
                           [Var (Short "f"); Var (Short "n")];
                         Var (Short "b")])
                     (If (Var (Short "c"))
                        (Let (SOME "d")
                           (App Opapp
                              [App Opapp
                                 [Var (Short "sub");
                                  Var (Short "arr")];
                               Var (Short "n")])
                           (Con (SOME (Short "Some"))
                              [Con NONE [Var (Short "n");
                               Var (Short "d")]]))
                        (Let (SOME "e")
                           (App Opapp
                              [App Opapp
                                 [Var (Short "+");
                                  Var (Short "n")];
                               Lit (IntLit 1)])
                           (App Opapp
                              [App Opapp
                                 [App Opapp
                                    [App Opapp
                                       [Var (Short "findi_aux");
                                        Var (Short "f")];
                                     Var (Short "arr")];
                                  Var (Short "max")];
                               Var (Short "e")]))))))))))])]``

val array_findi = process_topdecs
  `fun findi f arr =
    findi_aux f arr (length arr) 0`

val _ = append_prog array_findi_aux;
val _ = append_prog array_findi;

val array_exists = process_topdecs
  `fun exists_aux f arr max n =
    if n = max
      then False
    else (if f (sub arr n)
      then True
    else exists_aux f arr max (n + 1))

  fun exists f arr =
    exists_aux f arr (length arr) 0`

val _ = append_prog array_exists;

val array_all = process_topdecs
  `fun all_aux f arr max n =
    if n = max
      then True
    else (if f (sub arr n)
      then all_aux f arr max (n + 1)
    else False)

  fun all f arr =
    all_aux f arr (length arr) 0`

val _ = append_prog array_all;

val array_collate = process_topdecs
  `fun collate_aux f a1 a2 max ord n =
    if n = max
      then ord
    else (if f (sub a1 n) (sub a2 n) = Equal
        then collate_aux f a1 a2 max ord (n + 1)
      else f (sub a1 n) (sub a2 n))

  fun collate f a1 a2 =
    if (length a1) < (length a2)
      then collate_aux f a1 a2 (length a1) Less 0
    else if (length a2) < (length a1)
      then collate_aux f a1 a2 (length a2) Greater 0
    else collate_aux f a1 a2 (length a2) Equal 0`

val _ = append_prog array_collate;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
