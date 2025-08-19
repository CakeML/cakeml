(*
  Pure functions for the Vector module.
*)
Theory mlvector
Libs
  preamble
Ancestors
  misc mllist regexp_compiler

Theorem vector_nchotomy =
  regexp_compilerTheory.vector_nchotomy

Theorem sub_def =
  regexp_compilerTheory.sub_def

Theorem length_def =
  regexp_compilerTheory.length_def

Definition tabulate_def:
  tabulate n f = Vector (GENLIST f n)
End

Definition toList_aux_def:
  toList_aux vec n =
  if length(vec) <= n
    then []
  else sub vec n::toList_aux vec (n + 1)
Termination
  wf_rel_tac `measure (\(vec, n). length(vec) - n)`
End

val toList_aux_ind = theorem"toList_aux_ind";

Definition toList_def:
  toList vec = toList_aux vec 0
End

Triviality toList_aux_thm:
  !vec n. toList_aux vec n = case vec of Vector vs => DROP n vs
Proof
  ho_match_mp_tac toList_aux_ind \\
  rw [] \\
  ONCE_REWRITE_TAC [toList_aux_def] \\
  IF_CASES_TAC THEN1
    (Cases_on `vec` \\ fs [length_def]) \\
  fs [] \\
  Cases_on `vec` \\
  fs [sub_def, length_def, DROP_EL_CONS]
QED

Theorem toList_thm:
   !ls. toList (Vector ls) = ls
Proof
  rw [toList_def, toList_aux_thm]
QED

Theorem length_toList:
   LENGTH (toList vec) = length vec
Proof
  Induct_on `vec` >> rw[length_def, toList_thm]
QED

Theorem toList_11[simp]:
  (toList l = toList l') = (l = l')
Proof
  Induct_on `l` >> Induct_on `l'` >> fs[toList_thm]
QED

Theorem EL_toList:
  EL n (toList l) = sub l n
Proof
  Induct_on `l` >> fs[sub_def,toList_thm]
QED

Theorem toList_fromList[simp]:
   (toList(fromList l) = l) /\ (fromList(toList v) = v)
Proof
  Cases_on `v` >> fs[toList_thm,fromList_def]
QED

Definition update_def:
  update vec i x = Vector (LUPDATE x i (toList(vec)))
End

Theorem update_thm:
   !vec i x. sub (update vec i x) i = if i < length vec then x
    else sub vec i
Proof
  Cases \\
  rw [update_def, toList_thm, EL_LUPDATE, length_def, sub_def]
QED



Definition concat_def:
  concat l = Vector (FLAT (MAP toList l))
End

Definition map_def:
  map vec f = Vector (MAP f (toList vec))
End

Definition mapi_def:
  mapi vec f = Vector (MAPi f (toList vec))
End


Triviality less_than_length_thm:
  !xs n. (n < LENGTH xs) ==> (?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH ys = n))
Proof
  rw[] \\
  qexists_tac`TAKE n xs` \\
  rw[] \\
  qexists_tac`HD (DROP n xs)` \\
  qexists_tac`TL (DROP n xs)` \\
  Cases_on`DROP n xs` \\ fs[] \\
  metis_tac[TAKE_DROP,APPEND_ASSOC,CONS_APPEND]
QED

Definition foldli_aux_def:
  (foldli_aux f e vec n 0 = e) /\
  (foldli_aux f e vec n (SUC len) = foldli_aux f (f n (sub vec n) e) vec (n + 1) len)
End

Definition foldli_def:
  foldli f e vec = foldli_aux f e vec 0 (length vec)
End

Triviality foldli_aux_thm:
  !f e vec n len. (n + len = length vec) ==>
    (foldli_aux f e vec n len = mllist$foldli_aux f e n (DROP n (toList vec)))
Proof
  Cases_on `vec` \\ Induct_on `len` \\
  rw [foldli_aux_def, toList_thm, length_def, sub_def]
  >-(rw [DROP_LENGTH_TOO_LONG, mllistTheory.foldli_aux_def])
  \\ rw [DROP_EL_CONS, mllistTheory.foldli_aux_def, ADD1]
QED

Theorem foldli_thm:
   !f e vec. foldli f e vec = mllist$foldli f e (toList vec)
Proof
  rw [foldli_def, mllistTheory.foldli_def, foldli_aux_thm]
QED

Definition foldl_aux_def:
  (foldl_aux f e vec n 0 = e) /\
  (foldl_aux f e vec n (SUC len) = foldl_aux f (f e (sub vec n)) vec (n + 1) len)
End

Definition foldl_def:
  foldl f e vec = foldl_aux f e vec 0 (length vec)
End

Triviality foldl_aux_thm:
  !f e vec x len. (x + len = length vec) ==>
    (foldl_aux f e vec x len = FOLDL f e (DROP x (toList vec)))
Proof
  Induct_on `len` \\ Cases_on `vec` \\
  rw [foldl_aux_def, DROP_LENGTH_TOO_LONG, length_def, toList_thm] \\
  rw [length_def, sub_def, toList_thm] \\
  `x < LENGTH l` by decide_tac \\
  drule less_than_length_thm \\
  rw [] \\
  rw [] \\
  `LENGTH ys + 1 = LENGTH (ys ++ [z])` by (fs [] \\ NO_TAC) \\ ASM_REWRITE_TAC [DROP_LENGTH_APPEND]\\
  simp_tac std_ss [GSYM APPEND_ASSOC, APPEND, EL_LENGTH_APPEND, NULL, HD,
        FOLDL,  DROP_LENGTH_APPEND]
QED

Theorem foldl_thm:
   !f e vec. foldl f e vec = FOLDL f e (toList vec)
Proof
  rw [foldl_aux_thm, foldl_def]
QED



Definition foldri_aux_def:
  (foldri_aux f e vec 0 = e) /\
  (foldri_aux f e vec (SUC len) = foldri_aux f (f len (sub vec len) e) vec len)
End

Definition foldri_def:
  foldri f e vec = foldri_aux f e vec (length vec)
End


Triviality foldri_aux_thm:
  !f e vec len. len <= length vec ==>
    (foldri_aux f e vec len = FOLDRi f e (TAKE len (toList vec)))
Proof
  Induct_on `len` \\ rw[foldri_aux_def] \\
  Cases_on `vec` \\ fs[length_def, toList_thm, sub_def] \\
  rw [ADD1, TAKE_SUM, TAKE1_DROP, FOLDRi_APPEND]
QED

Theorem foldri_thm:
   !f e vec. foldri f e vec = FOLDRi f e (toList vec)
Proof
  Cases_on `vec` \\
  rw [foldri_aux_thm, foldri_def, toList_thm, length_def]
QED



Definition foldr_aux_def:
  (foldr_aux f e vec 0 = e) /\
  (foldr_aux f e vec (SUC len) = foldr_aux f (f (sub vec len) e) vec len)
End

Definition foldr_def:
  foldr f e vec = foldr_aux f e vec (length vec)
End

Triviality foldr_aux_thm:
  !f e vec len. len <= length vec ==>
    (foldr_aux f e vec len = FOLDR f e (TAKE len (toList vec)))
Proof
  Induct_on `len` \\ rw[foldr_aux_def] \\
  Cases_on `vec` \\ fs[length_def, toList_thm, sub_def] \\
  rw [ADD1, TAKE_SUM, TAKE1_DROP, FOLDR_APPEND]
QED

Theorem foldr_thm:
   !f e vec. foldr f e vec = FOLDR f e (toList vec)
Proof
  Cases_on `vec` \\
  rw[foldr_def, foldr_aux_thm, length_def, toList_thm]
QED


Definition findi_aux_def:
  (findi_aux f vec n 0 = NONE) /\
  (findi_aux f vec n (SUC len) =
  if f n (sub vec n)
    then SOME(n, (sub vec n))
  else findi_aux f vec (n + 1) len)
End

Definition findi_def:
  findi f vec = findi_aux f vec 0 (length vec)
End



Definition find_aux_def:
  (find_aux f vec n 0 = NONE) /\
  (find_aux f vec n (SUC len) =
  if f (sub vec n)
    then SOME(sub vec n)
  else find_aux f vec (n + 1) len)
End

Definition find_def:
  find f vec = find_aux f vec 0 (length vec)
End

Triviality find_aux_thm:
  !f vec n len. (n + len = length vec) ==> (find_aux f vec n len = FIND f (DROP n (toList vec)))
Proof
  Induct_on `len` \\ Cases_on `vec` \\ rw [find_aux_def, sub_def, length_def,
  toList_thm, FIND_def, INDEX_FIND_def] \\
  rw[DROP_LENGTH_NIL, INDEX_FIND_def] THEN1
  (qexists_tac`(0, EL n l)` \\ rw [DROP_EL_CONS, INDEX_FIND_def]) \\
  rw [DROP_EL_CONS, INDEX_FIND_def, index_find_thm]
QED

Theorem find_thm:
   !f vec. find f vec = FIND f (toList vec)
Proof
  rw [find_aux_thm, find_def]
QED



Definition exists_aux_def:
  (exists_aux f vec n 0 = F) /\
  (exists_aux f vec n (SUC len) =
    if f (sub vec n)
      then T
    else exists_aux f vec (n + 1) len)
End

Definition exists_def:
  exists f vec = exists_aux f vec 0 (length vec)
End

Theorem exists_aux_thm[local]:
  !f vec n len.
    n + len = length vec ==>
    exists_aux f vec n len = EXISTS f (DROP n (toList vec))
Proof
  Induct_on `len` \\ Cases_on `vec` \\
  rw[toList_thm, length_def, sub_def, exists_aux_def] \\
  rw [DROP_EL_CONS]
QED

Theorem exists_thm:
   !f vec. exists f vec = EXISTS f (toList vec)
Proof
  Cases_on `vec` \\
  rw [exists_def, exists_aux_thm]
QED

Definition all_aux_def:
  (all_aux f vec n 0 = T) /\
  (all_aux f vec n (SUC len) =
    if f (sub vec n)
      then all_aux f vec (n + 1) len
    else F)
End

Definition all_def: all f vec = all_aux f vec 0 (length vec)
End

Theorem all_aux_thm[local]:
  !f vec n len.
    n + len = length vec ==>
    all_aux f vec n len = EVERY f (DROP n (toList vec))
Proof
  Induct_on `len` \\ Cases_on `vec` \\
  rw[toList_thm, length_def, sub_def, all_aux_def] \\
  rw [DROP_EL_CONS]
QED

Theorem all_thm:
   !f vec. all f vec = EVERY f (toList vec)
Proof
  Cases_on `vec` \\ rw[all_def, all_aux_thm]
QED

Definition collate_aux_def:
  (collate_aux f vec1 vec2 n ord 0 = ord) /\
  (collate_aux f vec1 vec2 n ord (SUC len) =
    if f (sub vec1 n) (sub vec2 n) = EQUAL
      then collate_aux f vec1 vec2 (n + 1) ord len
    else f (sub vec1 n) (sub vec2 n))
End

Definition collate_def:
  collate f vec1 vec2 =
  if (length vec1) < (length vec2)
    then collate_aux f vec1 vec2 0 LESS (length vec1)
  else if (length vec2) < (length vec1)
    then collate_aux f vec1 vec2 0 GREATER (length vec2)
  else collate_aux f vec1 vec2 0 EQUAL (length vec2)
End

Theorem collate_aux_less_thm[local]:
  !f vec1 vec2 n len.
    n + len = length vec1 /\ length vec1 < length vec2 ==>
    collate_aux f vec1 vec2 n Less len =
    mllist$collate f (DROP n (toList vec1)) (DROP n (toList vec2))
Proof
  Cases_on ‘vec1’ \\ Cases_on ‘vec2’ \\ Induct_on ‘len’ \\
  rw [collate_aux_def, mllistTheory.collate_def, length_def, toList_thm,
      sub_def, DROP_EL_CONS]
QED

Theorem collate_aux_equal_thm[local]:
  !f vec1 vec2 n len.
    n + len = length vec2 /\ length vec1 = length vec2 ==>
    collate_aux f vec1 vec2 n Equal len =
    mllist$collate f (DROP n (toList vec1)) (DROP n (toList vec2))
Proof
  Cases_on ‘vec1’ \\ Cases_on ‘vec2’ \\ Induct_on ‘len’ \\
  rw [collate_aux_def, mllistTheory.collate_def, length_def, toList_thm,
      sub_def]
  >- rw [DROP_LENGTH_TOO_LONG, mllistTheory.collate_def] \\
  fs [DROP_EL_CONS, mllistTheory.collate_def]
QED

Theorem collate_aux_greater_thm[local]:
  !f vec1 vec2 n len.
    n + len = length vec2 /\ length vec2 < length vec1 ==>
    collate_aux f vec1 vec2 n Greater len =
      mllist$collate f (DROP n (toList vec1)) (DROP n (toList vec2))
Proof
  Cases_on ‘vec1’ \\ Cases_on ‘vec2’ \\ Induct_on ‘len’ \\
  rw [collate_aux_def, mllistTheory.collate_def, length_def, toList_thm,
      sub_def, DROP_EL_CONS]
QED

Theorem collate_thm:
  !f vec1 vec2.
    collate f vec1 vec2 = mllist$collate f (toList vec1) (toList vec2)
Proof
  rw [collate_def, collate_aux_greater_thm, collate_aux_equal_thm,
      collate_aux_less_thm]
QED
