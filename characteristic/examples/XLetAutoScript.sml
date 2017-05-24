open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory

val _ = new_theory "XLetAuto";

val star_congr = Q.store_thm("star_congr",
`!H:heap. (P * Q) H <=> ?H1 H2. SPLIT H (H1, H2) /\ P H1 /\ Q H2`,
strip_tac >> EQ_TAC >> fs[set_sepTheory.STAR_def] >> instantiate);

val SPLIT_congr = Q.store_thm("SPLIT_congr",
`SPLIT H (H1, H2) /\ (?H3 H4. SPLIT H1 (H3, H4) /\ P H1 H2 H3 H4) <=>
(?H3 H4. SPLIT H (H1, H2) /\  SPLIT H1 (H3, H4) /\ P H1 H2 H3 H4)`,
EQ_TAC >-(rw[])>> rw[] >> rw[] >> instantiate);

(* Some theorems used for simplication and matching *)
val int_num_convert_add = Q.store_thm("int_num_convert_add",
`!(x:num) (y:num).(&x) + &y = &(x+y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_times = Q.store_thm("int_num_convert_times",
`!(x:num) (y:num).(&x) * &y = &(x*y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_le = Q.store_thm("int_num_convert_le",
`!(x:num) (y:num). (&x <= &y) = (x <= y)`, rw[]);
val int_num_convert_less = Q.store_thm("int_num_convert_less",
`!(x:num) (y:num). (&x < &y) = (x < y)`, rw[]);
val int_num_convert_ge = Q.store_thm("int_num_convert_ge",
`!(x:num) (y:num). (&x >= &y) = (x >= y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_great = Q.store_thm("int_num_convert_great",
`!(x:num) (y:num). (&x > &y) = (x > y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_eq = Q.store_thm("int_num_convert_eq",
`!(x:num) (y:num). (&x = &y) = (x = y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_subs = Q.store_thm("int_num_convert_subs",
`!(x:num) (y:num). (&x - &y = &z) <=> (x - y = z) /\ y <= x`,
rw[] >> intLib.ARITH_TAC);

val empty_list_thm = Q.store_thm("empty_list_thm",
`(!l. LENGTH l = 0 <=> l = []) /\ (!l. 0 = LENGTH l <=> l = [])`,
CONJ_TAC >> rw[LENGTH_NIL] >> `0 = LENGTH l <=> LENGTH l = 0` by rw[] >> rw[LENGTH_NIL]);


(* Unicity results for the value pointed to by a heap pointer *)
val ARRAY_PTR_UNICITY = Q.store_thm("ARRAY_PTR_UNICITY",
`ARRAY a av1 h ==> ARRAY a av2 h = (av1 = av2)`,
rw[cfHeapsBaseTheory.ARRAY_def] >>
fs[cfHeapsBaseTheory.cell_def] >>
fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
fs[set_sepTheory.STAR_def] >>
fs[set_sepTheory.cond_def] >>
fs[set_sepTheory.SPLIT_def] >>
rw[] >> metis_tac[]
);

val REF_UNICITY = Q.store_thm("REF_UNICITY",
`REF r v1 H ==> REF r v2 H = (v1 = v2)`,
rw[cfHeapsBaseTheory.REF_def] >>
fs[cfHeapsBaseTheory.cell_def] >>
fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
fs[set_sepTheory.STAR_def] >>
fs[set_sepTheory.cond_def] >>
fs[set_sepTheory.SPLIT_def] >>
rw[] >> metis_tac[]
);

(* REPLICATE congruence rules *)
val APPEND_LENGTH_INEQ = Q.store_thm("APPEND_LENGTH_INEQ",
`!l1 l2. LENGTH(l1) <= LENGTH(l1++l2) /\ LENGTH(l2) <= LENGTH(l1++l2)`,
Induct >-(strip_tac >> rw[]) >> rw[]);

val REPLICATE_APPEND_RIGHT = Q.prove(
`a++b = REPLICATE n x ==> ?n'. b = REPLICATE n' x`,
strip_tac >>
`b = DROP (LENGTH a) (a++b)` by simp[GSYM DROP_LENGTH_APPEND] >>
`b = DROP (LENGTH a) (REPLICATE n x)` by POP_ASSUM (fn thm => metis_tac[thm]) >>
`b = REPLICATE (n - (LENGTH a)) x` by POP_ASSUM (fn thm => metis_tac[thm, DROP_REPLICATE]) >>
instantiate);

val REPLICATE_APPEND_LEFT = Q.prove(
`a++b = REPLICATE n x ==> ?n'. a = REPLICATE n' x`,
strip_tac >>
`?n'. b = REPLICATE n' x` by metis_tac[REPLICATE_APPEND_RIGHT] >>
`n >= n'` by rw[]
>-(
    `n' = LENGTH(REPLICATE n' x) /\ n = LENGTH (REPLICATE n x)` by metis_tac[LENGTH_REPLICATE] >>
    `LENGTH(REPLICATE n' x) <= LENGTH(REPLICATE n x)` by metis_tac[APPEND_LENGTH_INEQ] >>
  rw[] ) >>
rw[] >> `REPLICATE n x = REPLICATE (n-n') x ++ REPLICATE n' x` by simp[REPLICATE_APPEND] >>
fs[] >> qexists_tac `n-n'` >> rw[]);

val REPLICATE_APPEND_EXISTS_lem = Q.prove(
`!a b x n. a++b = REPLICATE n x <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n`,
rw[] >> EQ_TAC
  >-(strip_tac >>
     qexists_tac `LENGTH a` >>
     qexists_tac `LENGTH b` >>
     rw[] >-(metis_tac[REPLICATE_APPEND_LEFT, LENGTH_REPLICATE])
     >-(metis_tac[REPLICATE_APPEND_RIGHT, LENGTH_REPLICATE]) >>
`LENGTH(a++b) = n` by metis_tac[LENGTH_REPLICATE] >>
rw[]) >>
rpt strip_tac >>
rw[REPLICATE_APPEND]);

val REPLICATE_APPEND_EXISTS = Q.store_thm("REPLICATE_APPEND_EXISTS",
`!a b x n. a++b = REPLICATE n x <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n /\ LENGTH a = p /\ LENGTH b = q`,
rw[] >> EQ_TAC
  >-(rw[REPLICATE_APPEND_EXISTS_lem]
       >-(rw[LENGTH_REPLICATE])
       >-(rw[LENGTH_REPLICATE]) >>
       rw[LENGTH_REPLICATE]) >>
  rw[REPLICATE_APPEND_EXISTS_lem] >>
  instantiate);

val REPLICATE_APPEND_EXISTS_SYM = Q.store_thm("REPLICATE_APPEND_EXISTS",
`!a b x n. REPLICATE n x = a ++ b <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n /\ LENGTH a = p /\ LENGTH b = q`,
rw[] >> EQ_TAC >-(metis_tac[REPLICATE_APPEND_EXISTS]) >> metis_tac[REPLICATE_APPEND_EXISTS]);

val REPLICATE_APPEND_EQ = Q.store_thm("REPLICATE_APPEND_EQ",
`!x n n1 n2. REPLICATE n x = REPLICATE n1 x ++ REPLICATE n2 x <=> n = n1 + n2`,
rw[] >> EQ_TAC
>-(rw[] >> MP_TAC (SPECL [``REPLICATE n1 x``, ``REPLICATE n2 x``, ``x``, ``n:num``] REPLICATE_APPEND_EXISTS_SYM) >> rw[LENGTH_REPLICATE]) >>
rw[GSYM REPLICATE_APPEND]);

val LIST_REL_RIGHT_congr_recip = Q.prove(
`!R. LIST_REL R (a ++ b) x ==> ?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b'`,
rpt strip_tac >>
qexists_tac `TAKE (LENGTH a) x` >>
qexists_tac `DROP (LENGTH a) x` >>
rw[] >>
(mp_tac ((Thm.INST [``P:'a->'b->bool`` |-> ``R:'a->'b->bool``] LIST_REL_APPEND_IMP) |> SPECL [``a:'a list``, ``TAKE (LENGTH a) x:'b list``, ``b:'a list``, ``DROP (LENGTH a) x:'b list``]) >>
SIMP_TAC list_ss [] >>
`LENGTH a <= LENGTH x` by rw[APPEND_LENGTH_INEQ]
>-(
   `LENGTH a <= LENGTH (a ++ b)` by rw[] >>
   `LENGTH (a ++ b) = LENGTH x` by metis_tac[LIST_REL_LENGTH] >>
   metis_tac[LIST_REL_LENGTH]
) >>
rw[]));

val LIST_REL_RIGHT_congr_imp = Q.prove(`!R. (?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b') ==> LIST_REL R (a ++ b) x`,
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_RIGHT_congr = Q.store_thm("LIST_REL_RIGHT_congr",
`!R. LIST_REL R (a ++ b) x <=> ?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b'`,
metis_tac[LIST_REL_RIGHT_congr_recip, LIST_REL_RIGHT_congr_imp]);


val LIST_REL_LEFT_congr_recip = Q.prove(
`!R. LIST_REL R x (a ++ b) ==> ?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b'`,
rpt strip_tac >>
qexists_tac `TAKE (LENGTH a) x` >>
qexists_tac `DROP (LENGTH a) x` >>
rw[] >>
(mp_tac ((Thm.INST [``P:'a->'b->bool`` |-> ``R:'a->'b->bool``] LIST_REL_APPEND_IMP) |> SPECL [``TAKE (LENGTH a) x:'a list``, ``a:'b list``, ``DROP (LENGTH a) x:'a list``, ``b:'b list``]) >>
SIMP_TAC list_ss [] >>
`LENGTH a <= LENGTH x` by rw[APPEND_LENGTH_INEQ]
>-(
   `LENGTH a <= LENGTH (a ++ b)` by rw[] >>
   `LENGTH (a ++ b) = LENGTH x` by metis_tac[LIST_REL_LENGTH] >>
   metis_tac[LIST_REL_LENGTH]
) >>
rw[]
));

val LIST_REL_LEFT_congr_imp = Q.prove(
`!R. (?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b') ==> LIST_REL R x (a ++ b)`,
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_LEFT_congr = Q.store_thm("LIST_REL_LEFT_congr",
`!R. LIST_REL R x (a ++ b) <=> ?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b'`,
metis_tac[LIST_REL_LEFT_congr_recip, LIST_REL_LEFT_congr_imp]);

(* Congruence rules to rewrite the refinement invariants *)
fun eqtype_unicity_thm_tac x =
  let
      val assum = MP (SPEC ``abs:'a -> v -> bool`` EqualityType_def |> EQ_IMP_RULE |> fst) x
  in
      MP_TAC assum
  end;

val EQTYPE_UNICITY_R = Q.store_thm("EQ_UNICITY_R",
`!abs x y1 y2. EqualityType abs ==> abs x y1 ==> (abs x y2 <=> y2 = y1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

val EQTYPE_UNICITY_L = Q.store_thm("EQ_UNICITY_R",
`!abs x1 x2 y. EqualityType abs ==> abs x1 y ==> (abs x2 y <=> x2 = x1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

fun generate_refin_invariant_thms conj_eq_type_thms =
  let
      fun thm_strip_conj th =
	let
	    val (th1, r_conj) = (CONJUNCT1 th, CONJUNCT2 th)
	    val conjuncts = thm_strip_conj r_conj
	in
	    th1::conjuncts
	end
	handle _ => [th]
      fun get_ref_inv th = concl th |> dest_comb |> snd
      fun get_types ref_inv =
	let
	    val [t1,t'] = type_of ref_inv |> dest_type |> snd
	    val [t2, _] = dest_type t' |> snd
	in
	    (t1, t2)
	end
      fun gen_left_rule eq_type_thm =
	let
	    val ref_inv = get_ref_inv eq_type_thm
	    val (t1, t2) = get_types ref_inv
	    val th1 = Thm.INST_TYPE [``:'a`` |-> t1, ``:'b`` |-> t2] EQTYPE_UNICITY_L
	    val th2 = SPEC ref_inv th1
	    val (x1, x2, y) = (mk_var("x1", t1), mk_var("x2", t1), mk_var("y", t2))
	    val th3 = SPECL [x1, x2, y] th2
	    val th4 = MP th3 eq_type_thm
	    val th5 = GENL [x1, x2, y] th4
	in
	    th4
	end
      fun gen_right_rule eq_type_thm =
	let
	    val ref_inv = get_ref_inv eq_type_thm
	    val (t1, t2) = get_types ref_inv
	    val th1 = Thm.INST_TYPE [``:'a`` |-> t1, ``:'b`` |-> t2] EQTYPE_UNICITY_R
	    val th2 = SPEC ref_inv th1
	    val (x, y1, y2) = (mk_var("x", t1), mk_var("y1", t2), mk_var("y2", t2))
	    val th3 = SPECL [x, y1, y2] th2
	    val th4 = MP th3 eq_type_thm
	    val th5 = GENL [x, y1, y2] th4
	in
	    th5
	end
      val eq_type_thms = List.concat(List.map thm_strip_conj conj_eq_type_thms)
      val left_rules = List.map gen_left_rule eq_type_thms
      val right_rules = List.map gen_right_rule eq_type_thms
  in
      List.concat [left_rules, right_rules]
  end;


val RECONSTRUCT_INT = Q.store_thm("RECONSTRUCT_INT", `v = (Litv (IntLit i)) <=> INT i v`, rw[INT_def]);
val RECONSTRUCT_NUM = Q.store_thm("RECONSTRUCT_NUM", `v = (Litv (IntLit (&n))) <=> NUM n v`, rw[NUM_def, INT_def]);
val RECONSTRUCT_BOOL = Q.store_thm("RECONSTRUCT_BOOL", `v = Boolv b <=> BOOL b v`, rw[BOOL_def]);

val NUM_INT_EQ = Q.store_thm("NUM_INT_EQ",
`(!x y v. INT x v ==> (NUM y v <=> x = &y)) /\
(!x y v. NUM y v ==> (INT x v <=> x = &y)) /\
(!x v w. INT (&x) v ==> (NUM x w <=> w = v)) /\
(!x v w. NUM x v ==> (INT (&x) w <=> w = v))`,
fs[INT_def, NUM_def] >> metis_tac[]);

val LIST_APPEND_REPLICATE_EQ = Q.store_thm("LIST_APPEND_REPLICATE_EQ",
`a ++ b = REPLICATE n x <=>
a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\ LENGTH a + LENGTH b = n`,
cheat);

val extract_th1 = Q.prove(`(?s. (REF r v * H) s) ==> ((REF r v * H) ==>> (REF r v' * H')
								    <=> (v' = v /\ H ==>> H'))`, cheat);
val extract_th2 = Q.prove(`(?s. (ARRAY a av * H) s) ==> ((ARRAY a av * H) ==>> (ARRAY a av' * H')
									 <=> (av' = av /\ H ==>> H'))`, cheat);

val refin_invariant_thms = NUM_INT_EQ::(generate_refin_invariant_thms [EqualityType_NUM_BOOL]);

(* Build the inverse defs for the refinement invariants *)
val refin_invariant_defs = [NUM_def, INT_def, BOOL_def, UNIT_TYPE_def];
val refin_invariant_invert_defs = (List.map GSYM refin_invariant_defs)
				  @ [RECONSTRUCT_BOOL, RECONSTRUCT_INT, RECONSTRUCT_NUM];
val refin_inv_rewrite_thms = List.concat [refin_invariant_thms, refin_invariant_invert_defs]

val rewrite_thms = [integerTheory.INT_ADD,
		  int_num_convert_times,
		  int_num_convert_ge,
		  int_num_convert_great,
		  int_num_convert_eq,
		  int_num_convert_less,
		  int_num_convert_le,
		  int_num_convert_subs,
		  LENGTH_NIL,
		  LENGTH_NIL_SYM,
		  REPLICATE_APPEND_EQ,
		  LIST_APPEND_REPLICATE_EQ
		  
];
val match_thms = List.concat [rewrite_thms, refin_inv_rewrite_thms];
val extract_thms = [extract_th1, extract_th2];
val ri_expand_thms = refin_invariant_defs;
val ri_retract_thms = refin_inv_rewrite_thms;
val rw_thms = rewrite_thms;
val rw_intro_thms = refin_inv_rewrite_thms;
val xlet_auto_match_thms = (extract_thms, ri_expand_thms, ri_retract_thms, rw_thms, rw_intro_thms);

val _ = export_theory ();
