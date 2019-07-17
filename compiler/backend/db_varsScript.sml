(*
  Defines a datatype that is handy when keeping track of which dB vars
  are live when traversing a language using dB vars.
*)
open preamble;

val _ = new_theory "db_vars";

val _ = Datatype `
  db_var_set = Empty
             | Var num
             | Shift num db_var_set
             | Union db_var_set db_var_set`;

val mk_Union_def = Define `
  mk_Union t1 t2 =
    if t1 = Empty then t2 else
    if t2 = Empty then t1 else
      Union t1 t2`;

Theorem mk_Union_Empty[simp]:
   mk_Union Empty A = A ∧ mk_Union A Empty = A
Proof
  rw[mk_Union_def]
QED

val list_mk_Union_def = Define `
  (list_mk_Union [] = Empty) /\
  (list_mk_Union (x::xs) = mk_Union x (list_mk_Union xs))`;

Theorem FOLDR_mk_Union_UNZIP:
   FOLDR (λ(x,l) (ts,frees). (x::ts, mk_Union l frees)) ([], A) l =
   let (ts, fvs) = UNZIP l in
     (ts, list_mk_Union (fvs ++ [A]))
Proof
  Induct_on `l` >> simp[list_mk_Union_def] >>
  rename1 `UNZIP ll` >> Cases_on `UNZIP ll` >> full_simp_tac(srw_ss())[FORALL_PROD]
QED

val db_to_set_acc_def = Define `
  (db_to_set_acc (n:num) (Empty:db_var_set) s = s) /\
  (db_to_set_acc n (Var v) s =
     if v < n then s else insert (v - n) () s) /\
  (db_to_set_acc n (Shift k d) s = db_to_set_acc (n+k) d s) /\
  (db_to_set_acc n (Union v1 v2) s =
     db_to_set_acc n v1 (db_to_set_acc n v2 s))`;

Theorem wf_db_to_set_acc:
   ∀s n a. wf a ⇒ wf (db_to_set_acc n s a)
Proof
  Induct \\ EVAL_TAC \\ rw[wf_insert]
QED

val db_to_set_def = Define `
  db_to_set db = db_to_set_acc 0 db LN`;

Theorem wf_db_to_set:
   ∀db. wf (db_to_set db)
Proof
  rw[db_to_set_def,wf_db_to_set_acc,wf_def]
QED

val vars_to_list_def = Define `
  vars_to_list db = MAP FST (toAList (db_to_set db))`

val vars_from_list_def = Define `
  vars_from_list vs = FOLDL (\s1 v. Union (Var v) s1) Empty vs`;

val vars_flatten_def = Define `
  vars_flatten db = vars_from_list (vars_to_list db)`;

val has_var_def = Define `
  (has_var n Empty <=> F) /\
  (has_var n (Var v) <=> (n = v)) /\
  (has_var n (Shift k d) <=> has_var (n + k) d) /\
  (has_var n (Union d1 d2) <=> has_var n d1 \/ has_var n d2)`;
val _ = export_rewrites["has_var_def"];

Theorem has_var_mk_Union[simp]:
   has_var n (mk_Union l1 l2) <=> has_var n l1 \/ has_var n l2
Proof
  SRW_TAC [] [mk_Union_def,has_var_def]
QED

Theorem has_var_list_mk_Union[simp]:
   !ls. has_var n (list_mk_Union ls) <=> EXISTS (has_var n) ls
Proof
  Induct \\ fs [list_mk_Union_def,has_var_mk_Union,has_var_def]
QED

Theorem lookup_db_to_set_acc:
   !d n k s.
     lookup n (db_to_set_acc k d s) =
       if has_var (n + k) d then SOME () else lookup n s
Proof
  Induct \\ fs [has_var_def,db_to_set_acc_def,AC ADD_COMM ADD_ASSOC]
  \\ SRW_TAC [] [] \\ fs [lookup_insert]
  \\ SRW_TAC [] [] \\ `F` by DECIDE_TAC
QED

Theorem lookup_db_to_set:
   has_var n d = (lookup n (db_to_set d) = SOME ())
Proof
  fs [lookup_db_to_set_acc,db_to_set_def,lookup_def]
QED

Theorem lookup_db_to_set_Shift:
   lookup n (db_to_set (Shift k s)) = lookup (n+k) (db_to_set s)
Proof
  rw[db_to_set_def,db_to_set_acc_def]
  \\ rw[lookup_db_to_set_acc,lookup_def]
QED

Theorem MEM_vars_to_list:
   MEM n (vars_to_list d) = has_var n d
Proof
  fs [vars_to_list_def,MEM_MAP,EXISTS_PROD,MEM_toAList]
  \\ fs [lookup_db_to_set]
QED

val has_var_FOLDL_Union = Q.prove(
  `!vs n s. has_var n (FOLDL (\s1 v. Union (Var v) s1) s vs) <=>
             MEM n vs \/ has_var n s`,
  Induct \\ fs [] \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []);

Theorem MEM_vars_from_list:
   !vs n. has_var n (vars_from_list vs) <=> MEM n vs
Proof
  fs [vars_from_list_def,has_var_FOLDL_Union]
QED

Theorem has_var_vars_flatten[simp]:
   has_var n (vars_flatten d) = has_var n d
Proof
  fs [vars_flatten_def,MEM_vars_from_list,MEM_vars_to_list]
QED

Theorem ALL_DISTINCT_vars_to_list:
   ALL_DISTINCT (vars_to_list d)
Proof
  fs [vars_to_list_def,ALL_DISTINCT_MAP_FST_toAList]
QED

val _ = export_theory();
