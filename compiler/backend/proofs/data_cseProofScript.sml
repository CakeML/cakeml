open preamble data_cseTheory dataSemTheory dataPropsTheory numposrepTheory sptreeTheory ConseqConv;

val _ = new_theory "data_cseProof";
val _ = temp_bring_to_front_overload"get_vars"{Name="get_vars",Thy="dataSem"};
val _ = temp_bring_to_front_overload"cut_env"{Name="cut_env",Thy="dataSem"};

val state_rel_def = Define `
state_rel (s1:'ffi dataSem$state) (t1:'ffi dataSem$state) (live:num_set) <=>
          s1.code = t1.code /\ s1.clock = t1.clock /\ s1.space = t1.space /\
s1.ffi = t1.ffi /\ s1.refs = t1.refs /\ s1.global = t1.global /\
s1.handler = t1.handler /\ (LENGTH s1.stack = LENGTH t1.stack) /\
(T)`;
val cache_invariant = Define`
cache_invariant (Cache entries) = T`

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

val size_foldi = save_thm("size_foldi_l1", size_foldi_l1 |> Q.SPEC `0` |> SIMP_RULE (srw_ss()) []);

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
Induct_on `s` >-
fs[LENGTH, toAList_def, foldi_def, length_sum_map] >-
fs[LENGTH, toAList_def, foldi_def, length_sum_map] >-
  (
  rw[foldi_def] >>
  last_x_assum (qspecl_then [`i + 2*sptree$lrnext i`, `j + 2 * sptree$lrnext j`, `l`] (ASSUME_TAC o GSYM) ) >> fs[]
  ) >>
rw[foldi_def] >>
last_x_assum (qspecl_then [`i + 2*sptree$lrnext i`, `j + 2*sptree$lrnext j`, `l`, `k`] (ASSUME_TAC o GSYM)) >> fs[] >>
rewrite_tac[ADD_ASSOC] >>
once_rewrite_tac[ADD_COMM] >>
rewrite_tac[ADD_ASSOC] >>
rw[Once ADD_COMM] >>
last_x_assum (qspecl_then [`sptree$lrnext i + i`, `j + sptree$lrnext j`, `(foldi (λk v a. (k,v)::a) (j + 2 * sptree$lrnext j) l s)`, `1 + k`] (ASSUME_TAC o GSYM) ) >> fs[] >>
fs[] >>
rw[MAP_foldi] >>
rw[foldi_cons_k]
);

val length_toAList_size_l1 = save_thm("tmp", length_toAList_size_l
        |> Q.SPECL [`i`, `s`, `j`, `[]`, `0`]
        |> SIMP_RULE list_ss []
        |> GEN_ALL);

val length_toAList_size = Q.prove(
`!s. LENGTH (toAList s) = size s`,
rewrite_tac[size_foldi, toAList_def, length_toAList_size_l1, Once ADD_COMM]
);


val cache_member_memoize = Q.prove(
`!cache op args n.
(cache_lookup op args cache = NONE)
==>
(cache_lookup op args (cache_memoize op args n cache) = SOME n)`,
Cases_on `cache` >>
Induct_on `l` >-
  (
  rw[cache_memoize_def] >>
  rw[map_combine_def] >>
  rw[map_alter_def] >>
  rw[cache_memoize1_def] >>
  rw[cache_lookup_def] >>
  rw[num_set_head_may_def] >>
  first_x_assum kall_tac >>
  `MEM n (num_set_toList (insert n () LN))` by rw[member_num_set_toList_insert] >>
  rw[num_set_toList_def]
  CASE_TAC >> fs[num_set_toList_def] >>
  `h = n \/ h <> n` by decide_tac >> simp[] >>

  (* `MAP FST (toAList (insert n () LN)) = [n]` by *)
  (* ( *)
  (*   Induct_on `n` >- *)
  (*   ( *)
  (*     rw[Once insert_def] >> *)
  (*     rw[toAList_def] >> *)
  (*     rw[foldi_def] *)
  (*   ) >> *)
  (*   ( *)
  (*     rw[Once insert_def] >> *)
  (*     rw[toAList_def] >> *)
  (*     rw[foldi_def] >> *)
  (*     `n = 1` by ( *)
  (*       ASSUME_TAC DIV_0_IMP_LT >> res_tac >> *)
  (*       full_simp_tac std_ss [] >> *)
  (*       `n = 0 \/ n = 1` by (decide_tac ) >- fs[EVEN] *)
  (*     ) >> *)
  (*     full_simp_tac std_ss [] >> *)
  (*     rw[Once lrnext_def] *)
  (*   ) *)
  (* ) *)
)
);

val cache_lookup_none = Q.prove(

);


val _ = export_theory();
