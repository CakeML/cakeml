open preamble closLangTheory clos_freeTheory;

val _ = new_theory "clos_annotate";

(* TODO: move *)
val tlookup_def = Define `
  tlookup m k = case lookup m k of NONE => 0:num | SOME k => k`;

(* shift renames variables to use only those in the annotations *)

val get_var_def = Define `
  get_var m l i v =
    if v < l then v else l + tlookup (v - l) i`;

val new_env_def = Define `
  (new_env n [] = LN) /\
  (new_env n (x::xs) = insert x (n:num) (new_env (n+1) xs))`;

val shift_def = tDefine "shift" `
  (shift [] (m:num) (l:num) (i:num num_map) = []) /\
  (shift ((x:closLang$exp)::y::xs) m l i =
     let c1 = shift [x] m l i in
     let c2 = shift (y::xs) m l i in
       (c1 ++ c2:closLang$exp list)) /\
  (shift [Var v] m l i =
     [Var (get_var m l i v)]) /\
  (shift [If x1 x2 x3] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m l i in
     let c3 = shift [x3] m l i in
       ([If (HD c1) (HD c2) (HD c3)])) /\
  (shift [Let xs x2] m l i =
     let c1 = shift xs m l i in
     let c2 = shift [x2] m (l + LENGTH xs) i in
       ([Let c1 (HD c2)])) /\
  (shift [Raise x1] m l i =
     let (c1) = shift [x1] m l i in
       ([Raise (HD c1)])) /\
  (shift [Tick x1] m l i =
     let c1 = shift [x1] m l i in
       ([Tick (HD c1)])) /\
  (shift [Op op xs] m l i =
     let c1 = shift xs m l i in
       ([Op op c1])) /\
  (shift [App loc_opt x1 xs2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift xs2 m l i in
       ([App loc_opt (HD c1) c2])) /\
  (shift [Fn loc vs num_args x1] m l i =
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = shift [x1] k num_args (new_env 0 live) in
       ([Fn loc vars num_args (HD c1)])) /\
  (shift [Letrec loc vs fns x1] m l i =
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let new_i = new_env 0 live in
     let fns_len = LENGTH fns in
     let cs = MAP (\(n,x). let c = shift [x] k (n + fns_len) new_i in
                             (n,HD c)) fns in
     let c1 = shift [x1] m (l + LENGTH fns) i in
       ([Letrec loc vars cs (HD c1)])) /\
  (shift [Handle x1 x2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m (l+1) i in
       ([Handle (HD c1) (HD c2)])) /\
  (shift [Call dest xs] m l i =
     let c1 = shift xs m l i in
       ([Call dest c1]))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val shift_ind = theorem "shift_ind";

val shift_LENGTH_LEMMA = store_thm("shift_LENGTH_LEMMA",
  ``!xs m l i. LENGTH (shift xs m l i) = LENGTH xs``,
  recInduct shift_ind \\ REPEAT STRIP_TAC
  \\ fs [shift_def,LET_DEF,ADD1,AC ADD_COMM ADD_ASSOC])

val shift_SING = prove(
  ``!ys. (shift [x] m l i = ys) ==> ?y. ys = [y]``,
  fs [] \\ MP_TAC (Q.SPEC `[x]` shift_LENGTH_LEMMA |> SPEC_ALL)
  \\ Cases_on `shift [x] m l i` \\ fs [LENGTH_NIL])
  |> SIMP_RULE std_ss [];

val shift_CONS = store_thm("cEval_CONS",
  ``shift ((x:closLang$exp)::xs) m l i =
      let c1 = shift [x] m l i in
      let c2 = shift xs m l i in
        (HD c1 :: c2:closLang$exp list)``,
  Cases_on `xs` \\ fs [shift_def,LET_DEF,SING_HD,shift_LENGTH_LEMMA]);

(* main function *)

val annotate_def = Define `
  annotate env_size xs = shift (FST (free xs)) 0 env_size LN`;

val _ = export_theory();
