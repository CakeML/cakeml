open preamble closLangTheory clos_freeTheory;

val _ = new_theory "clos_annotate";

(* shift renames variables to use only those in the annotations *)

val get_var_def = Define `
  get_var m l i v =
    if v < l then v else l + tlookup (v - l) i`;

val shifted_env_def = Define `
  (shifted_env n [] = LN) /\
  (shifted_env n (x::xs) = insert x (n:num) (shifted_env (n+1) xs))`;

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
  (shift [Fn loc vs_opt num_args x1] m l i =
     let k = m + l in
     let vs = case vs_opt of NONE => [] | SOME vs => vs in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = shift [x1] k num_args (shifted_env 0 live) in
       ([Fn loc (SOME vars) num_args (HD c1)])) /\
  (shift [Letrec loc vsopt fns x1] m l i =
     let vs = case vsopt of NONE => [] | SOME x => x in
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let new_i = shifted_env 0 live in
     let fns_len = LENGTH fns in
     let cs = MAP (\(n,x). let c = shift [x] k (n + fns_len) new_i in
                             (n,HD c)) fns in
     let c1 = shift [x1] m (l + LENGTH fns) i in
       ([Letrec loc (SOME vars) cs (HD c1)])) /\
  (shift [Handle x1 x2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m (l+1) i in
       ([Handle (HD c1) (HD c2)])) /\
  (shift [Call ticks dest xs] m l i =
     let c1 = shift xs m l i in
       ([Call ticks dest c1]))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val shift_ind = theorem "shift_ind";

val shift_LENGTH_LEMMA = store_thm("shift_LENGTH_LEMMA",
  ``!xs m l i. LENGTH (shift xs m l i) = LENGTH xs``,
  recInduct shift_ind \\ REPEAT STRIP_TAC
  \\ fs [shift_def,LET_DEF,ADD1,AC ADD_COMM ADD_ASSOC])

val shift_SING = store_thm("shift_SING",
  ``!ys. (shift [x] m l i = ys) ==> ?y. ys = [y]``,
  fs [] \\ MP_TAC (Q.SPEC `[x]` shift_LENGTH_LEMMA |> SPEC_ALL)
  \\ Cases_on `shift [x] m l i` \\ fs [LENGTH_NIL])
  |> SIMP_RULE std_ss [];

val shift_CONS = store_thm("shift_CONS",
  ``shift ((x:closLang$exp)::xs) m l i =
      let c1 = shift [x] m l i in
      let c2 = shift xs m l i in
        (HD c1 :: c2:closLang$exp list)``,
  Cases_on `xs` \\ fs [shift_def,LET_DEF,SING_HD,shift_LENGTH_LEMMA]);

val HD_shift = store_thm("HD_shift[simp]",
  ``[HD (shift [x] m l i)] = shift [x] m l i``,
  STRIP_ASSUME_TAC shift_SING \\ fs []);

(* main functions *)

val annotate_def = Define `
  annotate xs = shift (FST (free xs)) 0 0 LN`;

val compile_def = Define `
  compile prog =
    let exps = MAP (\(_,_,exp). exp) prog in
    let new_exps = annotate exps in
      MAP (\((n,args,_),e). (n,args,e)) (ZIP (prog, new_exps))`;

val _ = export_theory();
