open preamble

val _ = new_theory"vector"

val _ = Datatype`vector = Vector ('a list)`;


val tabulate_def = Define`
  tabulate n f = Vector (GENLIST f n)`;




val toList_aux_def = tDefine "toList_aux"`
  toList_aux vec n =
  if length(vec) <= n
    then []
  else sub vec n::toList_aux vec (n + 1)`
(wf_rel_tac `measure (\(vec, n). length(vec) - n)`)

val toList_aux_ind = theorem"toList_aux_ind";

val toList_def = Define`toList vec = toList_aux vec 0`;

val toList_aux_thm = Q.prove (
  `!vec n. toList_aux vec n = case vec of Vector vs => DROP n vs`,
  ho_match_mp_tac toList_aux_ind \\
  rw [] \\
  ONCE_REWRITE_TAC [toList_aux_def] \\
  IF_CASES_TAC THEN1
    (Cases_on `vec` \\
    fs [length_def, DROP_NIL]) \\
  fs [] \\ 
  Cases_on `vec` \\ 
  fs [sub_def, length_def, DROP_EL_CONS]
);

val toList_thm = Q.store_thm (
  "toList_thm",
  `!ls. toList (Vector ls) = ls`,  
  rw [toList_def, toList_aux_thm]
)



val update_def = Define`
  update vec i x = Vector (LUPDATE x i (toList(vec)))`;

val update_thm = Q.store_thm (
  "update_thm",
  `!vec i x. sub (update vec i x) i = if i < length vec then x
    else sub vec i`,
  Cases \\
  rw [update_def, toList_thm, EL_LUPDATE, length_def, sub_def]
);




val concat_def = Define`
  concat l = Vector (FLAT (MAP toList l))`;



val map_proof_def = Define`
  map vec f = tabulate (length vec) (\n. f (sub vec n))`;

val mapi_proof_def = Define`
  mapi vec f = tabulate (length vec) (\n. f n (sub vec n))`;

val map_def = Define`
  map vec f = fromList (MAP f (toList vec))`;

val list_mapi_def = Define `
  (list_mapi f [] n = []) /\
  (list_mapi f (h::t) n = (f h n)::(list_mapi f t (n + 1)))`

val mapi_def = Define`
  mapi vec f = fromList (list_mapi f (toList vec) 0)`;


val map_thm = Q.store_thm (
  "map_thm",
  `!vec f. map vec f = map_proof vec f`,
  Cases \\
  rw [map_proof_def, tabulate_def, sub_def, tabulate_def, length_def, GENLIST_EL_MAP, map_def]
  rw  [toList_thm, fromList_def]
);





val foldli_aux_def = tDefine "foldli_aux"`
  foldli_aux f e vec (max: num) n =
    if max <= n
      then e
    else foldli_aux f (f n e (sub vec n)) vec max (n + 1)`
(wf_rel_tac `measure (\(f, e, vec, max, n). max - n)`);

val foldli_def = Define`
  foldli f e vec = foldli_aux f e vec (length vec) 0`;


val foldl_aux_def = tDefine "foldl_aux"`
  foldl_aux f e vec (max: num) n =
    if max <= n
      then e
    else foldl_aux f (f e (sub vec n)) vec max (n + 1)`
(wf_rel_tac `measure (\(f, e, vec, max, n). max - n)`);

val foldl_def = Define`
  foldl f e vec = foldl_aux f e vec (length vec) 0`;



val foldri_aux_def = tDefine "foldri_aux"`
  foldri_aux f e vec (n: num) =
    if n = 0
      then f e 0
    else foldri_aux f (f n e (sub vec n)) vec (n - 1)`
(wf_rel_tac `measure (\(f, e, vec, n). n)`);

val foldri_def = Define`
  foldri f e vec = foldri_aux f e vec ((length vec) - 1)`;

val foldr_aux_def = tDefine "foldr_aux"`
  foldr_aux f e vec (n: num) =
    if n = 0
      then e
    else foldr_aux f (f e (sub vec n)) vec (n - 1)`
(wf_rel_tac `measure (\(f, e, vec, n). n)`);

val foldr_def = Define`
  foldl f e vec = foldr_aux f e vec ((length vec) - 1)`;




val findi_aux_def = tDefine "findi_aux"`
  findi_aux f vec max n =
    if max <= n
      then NONE
    else if f n (sub vec n)
      then SOME(sub vec n)
    else findi_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val findi_def = Define `
  findi f vec = findi_aux f vec (length vec) 0`;


val find_aux_def = tDefine "find_aux"`
  find_aux f vec max n =
    if max <= n
      then NONE
    else if f (sub vec n)
      then SOME(sub vec n)
    else find_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val find_def = Define `
  find f vec = find_aux f vec (length vec) 0`;


val exists_aux_def = tDefine "exists_aux"`
  exists_aux f vec max n =
    if max <= n
      then F
    else if f (sub vec n)
      then T
    else exists_aux f vec max (n + 1)`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val exists_def = Define`
  exists f vec = exists_aux f vec (length vec) 0`;


val all_aux_def = tDefine "all_aux"`
  all_aux f vec max n =
    if max <= n
      then T
    else if f (sub vec n)
      then all_aux f vec max (n + 1)
    else F`
(wf_rel_tac `measure (\(f, vec, max, n). max - n)`);

val all_def = Define`
  all f vec = all_aux f vec (length vec) 0`;


val collate_aux_def = tDefine "collate_aux"`
  collate_aux f vec1 vec2 max ord n =
    if max <= n
      then ord
    else if f (sub vec1 n) (sub vec2 n) = EQUAL
      then collate_aux f vec1 vec2 max ord (n + 1)
    else
      f (sub vec1 n) (sub vec2 n)`
(wf_rel_tac `measure (\(f, vec1, vec2, max, ord, n). max - n)`);

val collate_def = Define`
  collate f vec1 vec2 =
  if (length vec1) < (length vec2)
    then collate_aux f vec1 vec2 (length vec1) GREATER 0
  else if (length vec2) < (length vec1)
    then collate_aux f vec1 vec2 (length vec2) LESS 0
  else collate_aux f vec1 vec2 (length vec2) EQUAL 0`;


val _ = export_theory()
