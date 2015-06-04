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

val list_mk_Union_def = Define `
  (list_mk_Union [] = Empty) /\
  (list_mk_Union (x::xs) = mk_Union x (list_mk_Union xs))`;

val db_to_set_acc_def = Define `
  (db_to_set_acc (n:num) (Empty:db_var_set) s = s) /\
  (db_to_set_acc n (Var v) s =
     if v < n then s else insert (v - n) () s) /\
  (db_to_set_acc n (Shift k d) s = db_to_set_acc (n+k) d s) /\
  (db_to_set_acc n (Union v1 v2) s =
     db_to_set_acc n v1 (db_to_set_acc n v2 s))`;

val db_to_set_def = Define `
  db_to_set db = db_to_set_acc 0 db LN`;

val vars_to_list_def = Define `
  vars_to_list db = MAP FST (toAList (db_to_set db))`

val has_var_def = Define `
  (has_var n Empty <=> F) /\
  (has_var n (Var v) <=> (n = v)) /\
  (has_var n (Shift k d) <=> has_var (n + k) d) /\
  (has_var n (Union d1 d2) <=> has_var n d1 \/ has_var n d2)`;

val lookup_db_to_set_acc = prove(
  ``!d n k s.
      lookup n (db_to_set_acc k d s) =
        if has_var (n + k) d then SOME () else lookup n s``,
  Induct \\ fs [has_var_def,db_to_set_acc_def,AC ADD_COMM ADD_ASSOC]
  \\ SRW_TAC [] [] \\ fs [lookup_insert]
  \\ SRW_TAC [] [] \\ `F` by DECIDE_TAC)

val lookup_db_to_set = prove(
  ``has_var n d = (lookup n (db_to_set d) = SOME ())``,
  fs [lookup_db_to_set_acc,db_to_set_def,lookup_def]);

val MEM_vars_to_list = store_thm("MEM_vars_to_list",
  ``MEM n (vars_to_list d) = has_var n d``,
  fs [vars_to_list_def,MEM_MAP,EXISTS_PROD,MEM_toAList]
  \\ fs [lookup_db_to_set]);

val ALL_DISTINCT_vars_to_list = store_thm("ALL_DISTINCT_vars_to_list",
  ``ALL_DISTINCT (vars_to_list d)``,
  fs [vars_to_list_def,ALL_DISTINCT_MAP_FST_toAList]);

val _ = export_theory();
