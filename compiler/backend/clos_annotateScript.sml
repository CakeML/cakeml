(*
  A compiler phase that annotates code that creates closures with
  (minimal) live variable annotations. Such live variable annotations
  are required for closure conversion, which is implemented in
  the clos_to_bvl phase of the compiler.
*)
open preamble closLangTheory db_varsTheory;

val _ = new_theory "clos_annotate";
val _ = set_grammar_ancestry ["closLang","db_vars","misc"]

(* alt_free calculates free variable annotations, and replaces unused lets with dummies *)

Definition const_0_def:
  const_0 t = Op t (IntOp (Const 0)) []
End

Definition no_overlap_def:
  (no_overlap 0 l <=> T) ∧
  (no_overlap (SUC n) l <=>
     if has_var n l then F else no_overlap n l)
End

Definition alt_free_def:
  (alt_free [] = ([],Empty)) /\
  (alt_free ((x:closLang$exp)::y::xs) =
     let (c1,l1) = alt_free [x] in
     let (c2,l2) = alt_free (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (alt_free [Var t v] = ([Var t v], Var v)) /\
  (alt_free [If t x1 x2 x3] =
     let (c1,l1) = alt_free [x1] in
     let (c2,l2) = alt_free [x2] in
     let (c3,l3) = alt_free [x3] in
       ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (alt_free [Let t xs x2] =
     let m = LENGTH xs in
     let (c2,l2) = alt_free [x2] in
       if no_overlap m l2 /\ EVERY pure xs then
         ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
       else
         let (c1,l1) = alt_free xs in
           ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (alt_free [Raise t x1] =
     let (c1,l1) = alt_free [x1] in
       ([Raise t (HD c1)],l1)) /\
  (alt_free [Tick t x1] =
     let (c1,l1) = alt_free [x1] in
       ([Tick t (HD c1)],l1)) /\
  (alt_free [Op t op xs] =
     let (c1,l1) = alt_free xs in
       ([Op t op c1],l1)) /\
  (alt_free [App t loc_opt x1 xs2] =
     let (c1,l1) = alt_free [x1] in
     let (c2,l2) = alt_free xs2 in
       ([App t loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (alt_free [Fn t loc _ num_args x1] =
     let (c1,l1) = alt_free [x1] in
     let l2 = Shift num_args l1 in
       ([Fn t loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
  (alt_free [Letrec t loc _ fns x1] =
     let m = LENGTH fns in
     let (c2,l2) = alt_free [x1] in
   (*  if no_overlap m l2 then
         ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
       else  *)
     let res = MAP (\(n,x). let (c,l) = alt_free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
       ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (alt_free [Handle t x1 x2] =
     let (c1,l1) = alt_free [x1] in
     let (c2,l2) = alt_free [x2] in
       ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (alt_free [Call t ticks dest xs] =
     let (c1,l1) = alt_free xs in
       ([Call t ticks dest c1],l1))
End

Definition alt_free_sing_def:
  (alt_free_sing (Var t v) = (Var t v, Var v)) /\
  (alt_free_sing (If t x1 x2 x3) =
     let (c1,l1) = alt_free_sing x1 in
     let (c2,l2) = alt_free_sing x2 in
     let (c3,l3) = alt_free_sing x3 in
       (If t c1 c2 c3,mk_Union l1 (mk_Union l2 l3))) /\
  (alt_free_sing (Let t xs x2) =
     let m = LENGTH xs in
     let (c2,l2) = alt_free_sing x2 in
       if no_overlap m l2 /\ EVERY pure xs then
         (Let t (REPLICATE m (const_0 t)) c2, Shift m l2)
       else
         let (c1,l1) = alt_free_list xs in
           (Let t c1 c2,mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (alt_free_sing (Raise t x1) =
     let (c1,l1) = alt_free_sing x1 in
       (Raise t c1,l1)) /\
  (alt_free_sing (Tick t x1) =
     let (c1,l1) = alt_free_sing x1 in
       (Tick t c1,l1)) /\
  (alt_free_sing (Op t op xs) =
     let (c1,l1) = alt_free_list xs in
       (Op t op c1,l1)) /\
  (alt_free_sing (App t loc_opt x1 xs2) =
     let (c1,l1) = alt_free_sing x1 in
     let (c2,l2) = alt_free_list xs2 in
       (App t loc_opt c1 c2,mk_Union l1 l2)) /\
  (alt_free_sing (Fn t loc _ num_args x1) =
     let (c1,l1) = alt_free_sing x1 in
     let l2 = Shift num_args l1 in
       (Fn t loc (SOME (vars_to_list l2)) num_args c1,l2)) /\
  (alt_free_sing (Letrec t loc _ fns x1) =
     let m = LENGTH fns in
     let (c2,l2) = alt_free_sing x1 in
   (*  if no_overlap m l2 then
         ([Let t (REPLICATE m (const_0 t)) (HD c2)], Shift m l2)
       else  *)
     let res = alt_free_letrec m fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
       (Letrec t loc (SOME (vars_to_list l1)) c1 c2,
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (alt_free_sing (Handle t x1 x2) =
     let (c1,l1) = alt_free_sing x1 in
     let (c2,l2) = alt_free_sing x2 in
       (Handle t c1 c2,mk_Union l1 (Shift 1 l2))) /\
  (alt_free_sing (Call t ticks dest xs) =
     let (c1,l1) = alt_free_list xs in
       (Call t ticks dest c1,l1)) ∧

  (alt_free_list [] = ([],Empty)) ∧
  (alt_free_list ((x:closLang$exp)::xs) =
     let (c1,l1) = alt_free_sing x in
     let (c2,l2) = alt_free_list xs in
       (c1 :: c2,mk_Union l1 l2)) ∧

  (alt_free_letrec m [] = []) ∧
  (alt_free_letrec m ((n,x)::rest) =
     let (c,l) = alt_free_sing x in
       ((n,c),Shift (n + m) l) :: alt_free_letrec m rest)
Termination
  WF_REL_TAC `measure $ λx. case x of INL e => exp_size e
                                    | INR (INL es) => list_size exp_size es
                                    | INR (INR (_,fns)) => list_size (pair_size (λx. x) exp_size) fns`
End

Theorem alt_free_sing_eq:
  (∀e. alt_free [e] = (λ(e,dbs). [e], dbs) $ alt_free_sing e) ∧
  (∀es. alt_free es = alt_free_list es) ∧
  (∀m fns. EVERY (λ(n,e). alt_free [e] = (λ(e,dbs). [e], dbs) $ alt_free_sing e) fns ∧
           alt_free_letrec m fns =
           MAP (λ(n,x). let (c,l) = alt_free_sing x in
                          ((n,c),Shift (n + m) l)) fns)
Proof
  ho_match_mp_tac alt_free_sing_ind >> reverse $ rw[alt_free_def, alt_free_sing_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt (TOP_CASE_TAC >> gvs[])
  >- (Cases_on `es` >> gvs[alt_free_def, alt_free_sing_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY] >> rw[] >>
  gvs [EVERY_MEM]
  >- (
    ntac 2 AP_TERM_TAC >>
    rw[MAP_EQ_f] >> PairCases_on `x` >>
    last_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
  >- (
    rw[MAP_EQ_f] >> PairCases_on `x` >>
    last_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
  >- (
    AP_THM_TAC >> ntac 2 AP_TERM_TAC >>
    rw[MAP_EQ_f] >> PairCases_on `x` >>
    last_x_assum drule >> rpt (pairarg_tac >> gvs[])
    )
QED

Triviality alt_free_LENGTH_LEMMA:
  !xs. (case alt_free xs of (ys,s1) => (LENGTH xs = LENGTH ys))
Proof
  recInduct alt_free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [alt_free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ rw []
QED

Theorem alt_free_LENGTH:
   !xs ys l. (alt_free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL alt_free_LENGTH_LEMMA) \\ fs []
QED

Theorem alt_free_SING:
   (alt_free [x] = (ys,l)) ==> ?y. ys = [y]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC alt_free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_FST_alt_free:
   LENGTH (FST (alt_free fns)) = LENGTH fns
Proof
  Cases_on `alt_free fns` \\ fs [] \\ IMP_RES_TAC alt_free_LENGTH
QED

Theorem HD_FST_alt_free:
   [HD (FST (alt_free [x1]))] = FST (alt_free [x1])
Proof
  Cases_on `alt_free [x1]` \\ fs []
  \\ imp_res_tac alt_free_SING \\ fs[]
QED

Theorem alt_free_CONS:
   FST (alt_free (x::xs)) = HD (FST (alt_free [x])) :: FST (alt_free xs)
Proof
  Cases_on `xs` \\ fs [alt_free_def,SING_HD,LENGTH_FST_alt_free,LET_DEF]
  \\ Cases_on `alt_free [x]` \\ fs []
  \\ Cases_on `alt_free (h::t)` \\ fs [SING_HD]
  \\ IMP_RES_TAC alt_free_SING \\ fs []
QED

(* shift renames variables to use only those in the annotations *)

Definition get_var_def:
  get_var m l i v =
    if v < l then v else l + zlookup i (v - l)
End

Definition shifted_env_def:
  (shifted_env n [] = LN) /\
  (shifted_env n (x::xs) = insert x (n:num) (shifted_env (n+1) xs))
End

Definition shift_def:
  (shift [] (m:num) (l:num) (i:num num_map) = []) /\
  (shift ((x:closLang$exp)::y::xs) m l i =
     let c1 = shift [x] m l i in
     let c2 = shift (y::xs) m l i in
       (c1 ++ c2:closLang$exp list)) /\
  (shift [Var t v] m l i =
     [Var t (get_var m l i v)]) /\
  (shift [If t x1 x2 x3] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m l i in
     let c3 = shift [x3] m l i in
       ([If t (HD c1) (HD c2) (HD c3)])) /\
  (shift [Let t xs x2] m l i =
     let c1 = shift xs m l i in
     let c2 = shift [x2] m (l + LENGTH xs) i in
       ([Let t c1 (HD c2)])) /\
  (shift [Raise t x1] m l i =
     let (c1) = shift [x1] m l i in
       ([Raise t (HD c1)])) /\
  (shift [Tick t x1] m l i =
     let c1 = shift [x1] m l i in
       ([Tick t (HD c1)])) /\
  (shift [Op t op xs] m l i =
     let c1 = shift xs m l i in
       ([Op t op c1])) /\
  (shift [App t loc_opt x1 xs2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift xs2 m l i in
       ([App t loc_opt (HD c1) c2])) /\
  (shift [Fn t loc vs_opt num_args x1] m l i =
     let k = m + l in
     let vs = case vs_opt of NONE => [] | SOME vs => vs in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = shift [x1] k num_args (shifted_env 0 live) in
       ([Fn t loc (SOME vars) num_args (HD c1)])) /\
  (shift [Letrec t loc vsopt fns x1] m l i =
     let vs = case vsopt of NONE => [] | SOME x => x in
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let new_i = shifted_env 0 live in
     let fns_len = LENGTH fns in
     let cs = MAP (\(n,x). let c = shift [x] k (n + fns_len) new_i in
                             (n,HD c)) fns in
     let c1 = shift [x1] m (l + LENGTH fns) i in
       ([Letrec t loc (SOME vars) cs (HD c1)])) /\
  (shift [Handle t x1 x2] m l i =
     let c1 = shift [x1] m l i in
     let c2 = shift [x2] m (l+1) i in
       ([Handle t (HD c1) (HD c2)])) /\
  (shift [Call t ticks dest xs] m l i =
     let c1 = shift xs m l i in
       ([Call t ticks dest c1]))
End

Definition shift_sing_def:
  (shift_sing (Var t v) m l i =
     Var t (get_var m l i v)) /\
  (shift_sing (If t x1 x2 x3) m l i =
     let c1 = shift_sing x1 m l i in
     let c2 = shift_sing x2 m l i in
     let c3 = shift_sing x3 m l i in
       (If t c1 c2 c3)) /\
  (shift_sing (Let t xs x2) m l i =
     let c1 = shift_list xs m l i in
     let c2 = shift_sing x2 m (l + LENGTH xs) i in
       (Let t c1 c2)) /\
  (shift_sing (Raise t x1) m l i =
     let (c1) = shift_sing x1 m l i in
       (Raise t c1)) /\
  (shift_sing (Tick t x1) m l i =
     let c1 = shift_sing x1 m l i in
       (Tick t c1)) /\
  (shift_sing (Op t op xs) m l i =
     let c1 = shift_list xs m l i in
       (Op t op c1)) /\
  (shift_sing (App t loc_opt x1 xs2) m l i =
     let c1 = shift_sing x1 m l i in
     let c2 = shift_list xs2 m l i in
       (App t loc_opt c1 c2)) /\
  (shift_sing (Fn t loc vs_opt num_args x1) m l i =
     let k = m + l in
     let vs = case vs_opt of NONE => [] | SOME vs => vs in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = shift_sing x1 k num_args (shifted_env 0 live) in
       (Fn t loc (SOME vars) num_args c1)) /\
  (shift_sing (Letrec t loc vsopt fns x1) m l i =
     let vs = case vsopt of NONE => [] | SOME x => x in
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let new_i = shifted_env 0 live in
     let fns_len = LENGTH fns in
     let cs = shift_letrec fns_len k new_i fns in
     let c1 = shift_sing x1 m (l + LENGTH fns) i in
       (Letrec t loc (SOME vars) cs c1)) /\
  (shift_sing (Handle t x1 x2) m l i =
     let c1 = shift_sing x1 m l i in
     let c2 = shift_sing x2 m (l+1) i in
       (Handle t c1 c2)) /\
  (shift_sing (Call t ticks dest xs) m l i =
     let c1 = shift_list xs m l i in
       (Call t ticks dest c1)) ∧

  (shift_list [] (m:num) (l:num) (i:num num_map) = []) /\
  (shift_list ((x:closLang$exp)::xs) m l i =
     let c1 = shift_sing x m l i in
     let c2 = shift_list xs m l i in
       (c1 :: c2:closLang$exp list)) ∧

  (shift_letrec fns_len k new_i [] = []) ∧
  (shift_letrec fns_len k new_i ((n,x)::rest) =
     let c = shift_sing x k (n + fns_len) new_i in
       (n,c) :: shift_letrec fns_len k new_i rest)
Termination
  WF_REL_TAC `measure $ λx. case x of INL (e,_,_,_) => exp_size e
                                    | INR (INL (es,_,_,_)) => list_size exp_size es
                                    | INR (INR (_,_,_,l)) => list_size (pair_size (λx. x) exp_size) l`
End

Theorem shift_sing_eq:
  (∀e m l i. shift [e] m l i = [shift_sing e m l i]) ∧
  (∀es m l i. shift es m l i = shift_list es m l i) ∧
  (∀fns_len k new_i fns.
     EVERY (λ(n,e). shift [e] k (n + fns_len) new_i =
                    [shift_sing e k (n + fns_len) new_i]) fns ∧
     shift_letrec fns_len k new_i fns =
       MAP (λ(n,x). let c = shift_sing x k (n + fns_len) new_i in
                      (n,c)) fns)
Proof
  ho_match_mp_tac shift_sing_ind >> reverse $ rw[shift_def, shift_sing_def]
  >- (Cases_on `es` >> gvs[shift_def, shift_sing_def]) >>
  rw[MAP_EQ_f] >> pairarg_tac >> gvs[] >>
  gvs [EVERY_MEM] >> res_tac >> fs []
QED

Theorem shift_LENGTH_LEMMA:
   !xs m l i. LENGTH (shift xs m l i) = LENGTH xs
Proof
  recInduct shift_ind \\ REPEAT STRIP_TAC
  \\ fs [shift_def,LET_DEF,ADD1,AC ADD_COMM ADD_ASSOC]
QED

Theorem shift_SING = Q.prove(`
  !ys. (shift [x] m l i = ys) ==> ?y. ys = [y]`,
  fs [] \\ MP_TAC (Q.SPEC `[x]` shift_LENGTH_LEMMA |> SPEC_ALL)
  \\ Cases_on `shift [x] m l i` \\ fs [LENGTH_NIL])
  |> SIMP_RULE std_ss [];

Theorem shift_CONS:
   shift ((x:closLang$exp)::xs) m l i =
      let c1 = shift [x] m l i in
      let c2 = shift xs m l i in
        (HD c1 :: c2:closLang$exp list)
Proof
  Cases_on `xs` \\ fs [shift_def,LET_DEF,SING_HD,shift_LENGTH_LEMMA]
QED

Theorem HD_shift[simp]:
  LENGTH (shift [x] m l i) = 1 ∧
  [HD (shift [x] m l i)] = shift [x] m l i
Proof
  STRIP_ASSUME_TAC shift_SING \\ fs []
QED

(* main functions *)

Definition annotate_def:
  annotate arity xs = shift (FST (alt_free xs)) 0 arity LN
End

Definition compile_def:
  compile prog =
    MAP (λ(n,args,exp). (n,args, HD (annotate args [exp]))) prog
End

Definition compile_inc_def:
  compile_inc (e,aux) = (annotate 0 e,clos_annotate$compile aux)
End

(* cv versions *)

Definition annotate_sing_def:
  annotate_sing arity x = shift_sing (FST (alt_free_sing x)) 0 arity LN
End

Definition annotate_list_def:
  annotate_list arity xs = shift_list (FST (alt_free_list xs)) 0 arity LN
End

Theorem annotate_sing_eq:
  annotate arity [e] = [annotate_sing arity e] ∧
  annotate arity es = annotate_list arity es
Proof
  simp[annotate_def, annotate_sing_def, annotate_list_def] >>
  simp[alt_free_sing_eq, shift_sing_eq] >>
  pairarg_tac >> gvs[shift_sing_def]
QED

Theorem compile_eq:
  compile prog =
    MAP (λ(n,args,exp). (n,args, annotate_sing args exp)) prog
Proof
  simp[compile_def, annotate_sing_eq]
QED

Theorem compile_inc_eq:
  compile_inc (e,aux) = (annotate_list 0 e, clos_annotate$compile aux)
Proof
  simp[compile_inc_def, annotate_sing_eq]
QED

val _ = export_theory();
