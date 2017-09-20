open preamble data_cseTheory dataSemTheory dataPropsTheory;

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
`!cache n. ~(num_set_member n (cache_varset (cache_invalidate_simple cache n)))`,
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


val _ = export_theory();
