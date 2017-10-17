open preamble data_cseTheory dataSemTheory dataPropsTheory numposrepTheory sptreeTheory ConseqConv;

val _ = new_theory "data_cseProof";
val _ = temp_bring_to_front_overload"get_vars"{Name="get_vars",Thy="dataSem"};
val _ = temp_bring_to_front_overload"cut_env"{Name="cut_env",Thy="dataSem"};

val map_maybe_head = Q.prove(
`!f x t. map_maybe f (x::t) =
case f x of
  | NONE => map_maybe f t
  | (SOME l) => l :: map_maybe f t`,
rw[map_maybe_def]
);

val lookup_foldr_l1 = Q.prove(
`!x k l. ~(MEM k l) ==> (lookup k (FOLDR (\arg ac. insert arg () ac) x l) = lookup k x)`,
Induct_on `l` >- rw[] >>
rw[lookup_insert]
);

val cache_member_invalidate = Q.prove(
`!cache n. ~(num_set_member n (cache_varset (cache_invalidate_simple n cache)))`,
  Cases_on `cache` >>
  Induct_on `l` >-
  (
    rw[cache_invalidate_simple_def] >>
    rw[map_maybe_def] >>
    rw[cache_varset_def] >>
    rw[num_set_member_def] >>
    rw[lookup_def]
  ) >>
  rw[] >>
  Cases_on `h` >>
  qabbrev_tac `aargs = r` >> first_x_assum kall_tac >>
  rw[cache_invalidate_simple_def] >>
  Induct_on `aargs` >-
  (
    rw[map_maybe_def] >>
    fs[cache_invalidate_simple_def]
  ) >>
  GEN_TAC >>
  Cases_on `h` >>
  rw[map_maybe_head] >-
  fs[map_maybe_head] >-
  fs[map_maybe_head] >>
  rw[cache_varset_def] >>
  fs[num_set_member_def] >>
  ASSUME_TAC lookup_foldr_l1 >>
  res_tac >>
  asm_rewrite_tac [] >>
  rw[lookup_union] >>
  rw[lookup_delete] >>
  fs[cache_varset_def] >>
  fs[map_maybe_head] >>
  CASE_TAC >>
  fs[]
);

val member_toAList_insert = Q.prove(
`! x n s. MEM (n, x) (toAList (insert n x s))`,
rw[MEM_toAList, lookup_insert]
);

val member_num_set_toList_insert = Q.prove(
`!x n s. MEM n (num_set_toList (insert n x s))`,
once_rewrite_tac[num_set_toList_def] >>
once_rewrite_tac[o_THM] >>
rw[] >>
rw[MEM_MAP, EXISTS_PROD] >>
metis_tac[member_toAList_insert]
);

val toAList_domain_thm = Q.prove(
`!x t. MEM x (MAP FST (toAList t)) = (x IN (domain t))`,
rw[toAList_domain]
);

val size_foldi_l1 = Q.prove(
`!n i s. n + size s = foldi (\k v a. 1n + a) i n s`,
Induct_on `s` >>
rw[size_def, foldi_def] >-
(
  last_x_assum (qspecl_then [`n`, `i + 2 * sptree$lrnext i`] (ASSUME_TAC o GSYM)) >> fs[] >>
  last_assum (qspecl_then [`n + size s`,  `i + sptree$lrnext i`] (ASSUME_TAC o GSYM)) >> fs[]
) >-
(
    last_x_assum (qspecl_then [`n`, `i + 2 * sptree$lrnext i`] (ASSUME_TAC o GSYM)) >> fs[] >>
    last_assum (qspecl_then [`n + (size s + 1)`, `i + sptree$lrnext i`] (ASSUME_TAC o GSYM)) >> fs[]
)
);

val size_foldi = save_thm("size_foldi_l1",
                          size_foldi_l1
                              |> Q.SPEC `0`
                              |> SIMP_RULE (srw_ss()) []);

val length_sum_map = Q.prove(
`!l. LENGTH l = SUM (MAP (\_ . 1) l)`,
Induct_on `l` >> rw[LENGTH, SUM, MAP]
);

val foldi_cons_k = Q.prove(
`!i c ac s.foldi (\n v a. c::a) i (c::ac) s = c::foldi (\n v a. c::a) i ac s`,
Induct_on `s` >> rw[foldi_def]
);

val length_toAList_size_l = Q.prove(
`!i s j l k.
  LENGTH (foldi (\k v a. (k,v)::a) j l s) + k = foldi (\k v a. 1 + a) i (LENGTH l + k) s`,
  rewrite_tac[length_sum_map, MAP] >>
  Induct_on `s` >> rw[foldi_def] >-
    (last_x_assum (qspecl_then [`i + 2*sptree$lrnext i`, `j + 2 * sptree$lrnext j`, `l`] (ASSUME_TAC o GSYM) ) >> fs[]) >>
  last_x_assum (qspecl_then [`i + 2*sptree$lrnext i`, `j + 2*sptree$lrnext j`, `l`, `k`] (ASSUME_TAC o GSYM)) >> fs[] >>
  rewrite_tac[ADD_ASSOC] >>
  once_rewrite_tac[ADD_COMM] >>
  rewrite_tac[ADD_ASSOC] >>
  rw[Once ADD_COMM] >>
  last_x_assum (qspecl_then [`sptree$lrnext i + i`, `j + sptree$lrnext j`, `(foldi (λk v a. (k,v)::a) (j + 2 * sptree$lrnext j) l s)`, `1 + k`] (ASSUME_TAC o GSYM) ) >> fs[] >>
  rw[MAP_foldi, foldi_cons_k]
);

val length_toAList_size_l1 = length_toAList_size_l
        |> Q.SPECL [`i`, `s`, `j`, `[]`, `0`]
        |> SIMP_RULE list_ss []
        |> GEN_ALL;
val length_toAList_size = Q.prove(
`!s. LENGTH (toAList s) = size s`,
rewrite_tac[size_foldi, toAList_def, length_toAList_size_l1, Once ADD_COMM]
);
val length_num_set_toList_size = Q.prove(
`!s. LENGTH (num_set_toList s) = size s`,
rw[num_set_toList_def, length_toAList_size]);

val mul_div2 = Q.prove(
`!a. (2 * a DIV 2 = a)`,
Induct_on `a` >> rw [MULT_SUC, ADD_DIV_RWT]);
val mul_suc_div2 = Q.prove(
`!a. (2 * a + 1) DIV 2 = a`,
Induct_on `a` >> rw [MULT_SUC, ADD_DIV_RWT, mul_div2]
);
val odd_double = Q.prove(
`!x. ~(EVEN (2 * x + 1))`,
Induct_on `x` >> rw[MULT_SUC, EVEN_ADD, EVEN_DOUBLE]);

val size_zero_lookup = Q.prove(
`!s. (size s = 0) <=> (!x. lookup x s = NONE)`,
Induct_on `s` >-
fs[lookup_def] >-
fs[lookup_def] >-
(
  Cases_on `size s = 0` >> Cases_on `size s' = 0` >> fs[] >> fs[] >-
  (
    full_simp_tac std_ss [size_def, lookup_def] >>
    rw[]
  ) >-
  (
    rw[lookup_def] >>
    EXISTS_TAC ``2 * x + 1: num`` >>
    full_simp_tac arith_ss [odd_double, mul_div2] >>
    Cases_on `lookup x s'` >> fs[]
  ) >>
  (
    rw[lookup_def] >>
    EXISTS_TAC ``2 * x + 2: num`` >>
    full_simp_tac arith_ss [EVEN_ADD, EVEN_DOUBLE, mul_suc_div2] >>
    Cases_on `lookup x s` >> fs[]
  )
) >>
rw[size_def] >>
exists_tac ``0:num`` >>
rw[lookup_def]
);

val size_zero_domain = Q.prove(
`!s. (size s = 0) <=> (!x. x ∉ domain s)`,
rw[] >>
Cases_on `size s = 0` >-
(
  CCONTR_TAC >>
  fs[domain_lookup] >>
  imp_res_tac size_zero_lookup >>
  fs[]
) >>
rw[] >>
Induct_on `s` >-
fs[size_def] >-
fs[size_def] >-
(rw[] >> metis_tac []) >>
rw[] >> metis_tac []
);


val num_set_toList_insert_singleton = Q.prove(
`!s n. (size s = 0) ==> (num_set_toList (insert n () s) = [n])`,
rw[] >>
`MEM n (num_set_toList (insert n () s))` by rw[member_num_set_toList_insert] >>
`size (insert n () s) = 1` by fs[size_insert, size_zero_domain] >>
`LENGTH (num_set_toList (insert n () s)) = 1` by rw[size_insert, length_num_set_toList_size] >>
Cases_on `num_set_toList (insert n () s)` >- fs[] >>
Cases_on `t` >> fs[]
);
val num_set_toList_empty = Q.prove(
`!s. (num_set_toList s = []) = (size s = 0)`,
rw[GSYM length_num_set_toList_size]
);

val state_rel_def = Define `
state_rel (s1:'ffi dataSem$state) (t1:'ffi dataSem$state) (cache:cache) <=>
s1.code = t1.code /\ s1.clock = t1.clock /\
s1.space = t1.space /\
s1.ffi = t1.ffi /\
s1.refs = t1.refs /\
s1.global = t1.global /\
s1.handler = t1.handler /\
LENGTH s1.stack = LENGTH t1.stack /\
(!x. lookup x s1.locals = lookup x t1.locals) /\
(!op args. (cache_lookup op args cache = SOME v) ==> (


      do_app op xs s1 = Rval (v, some_s)))
`;

val state_rel_ID = Q.prove(
`!s live. state_rel s s live`,
fs [state_rel_def]);

(* copied and barely adapted from dataLive *)
(* val evaluate_compile_A = Q.prove( *)
(* `!c s1 res s2 l2 t1 l1 d. *)
(* (evaluate (c, s1) = (res, s2)) /\ *)
(* state_rel s1 t1 l1 /\ *)
(* (compile_A c l2 = (d, l1)) /\ (res <> SOME (Rerr (Rabort Rtype_error))) /\ *)
(* (!s3. (jump_exc s1 = SOME s3) ==> *)
(*   ?t3. (jump_exc t1 = SOME t3) /\ state_rel s3 t3 empty_cache /\ *)
(*   (t3.handler = s3.handler) /\ *)
(*   (LENGTH t3.stack = LENGTH s3.stack)) ==> *)
(*     ?t2. (evaluate (d, t1) = (res, t2)) /\ *)
(*     state_rel s2 t2 (case res of NONE => l2 | _ => empty_cache)`, *)
(* ); *)

val pair_if = Q.prove(
`((a,b) = if c then (a1, b1) else (a2, b2)) =
((a = if c then a1 else a2) /\ (b = if c then b1 else b2))`,
rw[]
);

val evaluate_compile_A = Q.prove(
`!c s1 res s2 l2 t1 l1 d.
(evaluate (c, s1) = (res, s2)) /\
state_rel s1 t1 l1 /\
(compile_A c l2 = (d, l1)) /\ (res <> SOME (Rerr (Rabort Rtype_error))) /\
(!s3. (jump_exc s1 = SOME s3) ==>
  ?t3. (jump_exc t1 = SOME t3) /\ state_rel s3 t3 empty_cache /\
  (t3.handler = s3.handler) /\
  (LENGTH t3.stack = LENGTH s3.stack)) ==>
    ?t2. (evaluate (d, t1) = (res, t2)) /\
    state_rel s2 t2 (case res of NONE => l2 | _ => empty_cache)`,
once_rewrite_tac [EQ_SYM_EQ] >>
recInduct evaluate_ind >>
rpt STRIP_TAC >-
    (* Skip *)
  fs[compile_A_def, evaluate_def] >-
    (* Move *)
  (
    fs[state_rel_def, compile_A_def, evaluate_def, get_var_def] >>
    Cases_on `lookup src t1.locals` >>
    fs [set_var_def, lookup_insert]
  ) >-
  (
  (* Assign *)
    fs[state_rel_def, compile_A_def, evaluate_def, get_var_def] >>
    Cases_on `is_pure op` >-
    (
      fs[]
        cheat
      full_simp_tac list_ss []
      rev_full_simp_tac list_ss []
    )
  )
);

(* val cache_member_memoize = Q.prove( *)
(* `!cache op args n. *)
(* (cache_lookup op args cache = NONE) *)
(* ==> *)
(* (cache_lookup op args (cache_memoize op args n cache) = SOME n)`, *)
(*   Cases_on `cache` >> Induct_on `l` >- *)
(*     rw[cache_memoize_def, map_combine_def, map_alter_def, cache_memoize1_def, cache_lookup_def, num_set_toList_insert_singleton, num_set_head_may_def] >> *)
(*   fs[cache_memoize_def, map_combine_def] >> *)
(*   Cases_on `h` >> *)
(*   fs[map_alter_def, cache_memoize1_def] >> *)
(*   rw[] >- *)
(*     ( *)
(*     rw[cache_lookup_def] >> *)
(*     rw[cache_memoize2_def] >> *)
(*     Cases_on `r` >- ( *)
(*       rw[map_combine_def, Once map_alter_def] >> *)
(*       rw[cache_memoize2_def] >> *)
(*       rw[cache_lookup_def] >> *)
(*       rw[num_set_head_may_def, num_set_toList_insert_singleton] *)
(*     ) >> *)
(*     Cases_on `h` >> *)
(*     rw[map_combine_def, map_alter_def] >> *)
(*     rw[cache_memoize2_def] >> *)
(*     rw[cache_lookup_def] >> *)
(*     rw[num_set_head_may_def] >> *)
(*     `size r = 0` by *)
(*     ( *)
(*       fs[cache_lookup_def, num_set_head_may_def] >> *)
(*       Cases_on `num_set_toList r` >> rw[num_set_toList_def, toAList_def, foldi_def] >> *)
(*       `LENGTH (num_set_toList r) = 0` by fs [] >> *)
(*       rw[length_num_set_toList_size] >> *)
(*       ASSUME_TAC length_num_set_toList_size >> *)
(*       asm_rewrite_tac[GSYM length_num_set_toList_size] >> *)
(*       fs[] *)
(*     ) >> *)
(*     `size (insert n () r) = 1` by ( *)
(*       fs[size_insert] >> *)
(*       rw[] >> *)
(*       imp_res_tac size_zero_domain >> fs[] *)
(*       ) >> *)
(*     imp_res_tac num_set_toList_insert_singleton >> *)
(*     rw[] *)
(*     ) >> *)
(*     (* ntac 3 (first_x_assum kall_tac) >> *) *)
(*     (* wrong! loop begins here! *) *)
(*     Induct_on `t` >- *)
(*       rw[map_combine_def, map_alter_def, cache_memoize2_def, num_set_head_may_def, num_set_toList_insert_singleton] >> *)
(*     Cases_on `h` >> *)
(*     rw[map_alter_def, cache_memoize2_def] >> *)
(*     `size r' = 0` by ( *)
(*       fs[cache_lookup_def, num_set_head_may_def] >> *)
(*       rev_full_simp_tac std_ss [] >> *)
(*       Cases_on `num_set_toList x` >- ( *)
(*         fs[] *)
(*         rw[length_num_set_toList_size] >> *)
(*         ASSUME_TAC length_num_set_toList_size >> *)
(*         asm_rewrite_tac[GSYM length_num_set_toList_size] >> *)
(*         fs[] *)
(*       ) >> *)
(*       fs[] *)
(*     ) >> *)
(*     rw[num_set_head_may_def] *)
(*     imp_res_tac num_set_toList_insert_singleton >> *)
(*     fs[] *)
(*     (* loop ends here *) *)
(* ); *)

(* val cache_lookup_none = Q.prove( *)

(* ); *)


val _ = export_theory();
