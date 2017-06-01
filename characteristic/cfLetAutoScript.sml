open preamble ml_translatorTheory cfTacticsLib set_sepTheory cfHeapsBaseTheory
     mlcharioProgTheory mlfileioProgTheory mlcommandLineProgTheory stdoutFFITheory stderrFFITheory
     stdinFFITheory rofsFFITheory commandLineFFITheory
	      
val _ = new_theory "cfLetAuto";

(* Rewrite rules for the int_of_num & operator*)
val INT_OF_NUM_ADD = Q.store_thm("INT_OF_NUM_ADD",
`!(x:num) (y:num).(&x) + &y = &(x+y)`, rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_TIMES = Q.store_thm("INT_OF_NUM_TIMES",
`!(x:num) (y:num).(&x) * &y = &(x*y)`, rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_LE = Q.store_thm("INT_OF_NUM_LE",
`!(x:num) (y:num). (&x <= &y) = (x <= y)`, rw[]);
val INT_OF_NUM_LESS = Q.store_thm("INT_OF_NUM_LESS",
`!(x:num) (y:num). (&x < &y) = (x < y)`, rw[]);
val INT_OF_NUM_GE = Q.store_thm("INT_OF_NUM_GE",
`!(x:num) (y:num). (&x >= &y) = (x >= y)`, rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_GREAT = Q.store_thm("INT_OF_NUM_GREAT",
`!(x:num) (y:num). (&x > &y) = (x > y)`, rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_EQ = Q.store_thm("INT_OF_NUM_EQ",
`!(x:num) (y:num). (&x = &y) = (x = y)`, rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_SUBS = Q.store_thm("INT_OF_NUM_SUBS",
`!(x:num) (y:num) (z:num). (&x - &y = &z) <=> (x - y = z) /\ y <= x`,
rw[] >> intLib.ARITH_TAC);
val INT_OF_NUM_SUBS_2 = Q.store_thm("INT_OF_NUM_SUBS_2",
`!(x:num) (y:num). y <= x ==> (&x - &y = &(x - y))`,
rw[] >> fs[int_arithTheory.INT_NUM_SUB]);

(* Predicates stating that a heap is valid *)
val UNIQUE_PTRS_def =
    Define `UNIQUE_PTRS s = !l xv xv' H H'. (l ~~>> xv * H) s /\ (l ~~>> xv' * H') s ==> xv' = xv`;

val VALID_FFI_HEAP_def =
    Define `VALID_FFI_HEAP s =
	     !s1 u1 ns1 s2 u2 ns2 H1 H2.
		(?pn. MEM pn ns1 /\ MEM pn ns2) ==>
		   (IO s1 u1 ns1 * H1) s /\ (IO s2 u2 ns2 * H2) s ==>
			s2 = s1 /\ u2 = u1 /\ ns2 = ns1`;

val VALID_HEAP_def =
    Define `VALID_HEAP s = (UNIQUE_PTRS s /\ VALID_FFI_HEAP s)`;

val HCOND_EXTRACT = Q.store_thm("HCOND_EXTRACT",
`((&A * H) s <=> A /\ H s) /\ ((H * &A) s <=> H s /\ A) /\ ((H * &A * H') s <=> (H * H') s /\ A)`,
rw[] >-(fs[STAR_def, STAR_def, cond_def, SPLIT_def])
>-(fs[STAR_def, STAR_def, cond_def, SPLIT_def]) >>
fs[STAR_def, STAR_def, cond_def, SPLIT_def] >> EQ_TAC >-(rw [] >-(instantiate) >> rw[]) >> rw[]);

(* Unicity results for pointers *)
val UNIQUE_REFS = Q.store_thm("UNIQUE_REFS",
`!s r xv xv' H H'. UNIQUE_PTRS s ==> (r ~~> xv * H) s /\ (r ~~> xv' * H') s ==> xv' = xv`,
rw[UNIQUE_PTRS_def] >> fs[REF_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
`!A H1 H2. (&A * H1 * H2) s <=> A /\ (H1 * H2) s` by metis_tac[HCOND_EXTRACT, STAR_COMM] >>
POP_ASSUM (fn x => fs[x]) >> rw[] >> LAST_X_ASSUM (fn x => IMP_RES_TAC x) >> fs[]);

val UNIQUE_ARRAYS = Q.store_thm("UNIQUE_ARRAYS",
`!s a av av' H H'. UNIQUE_PTRS s ==> (ARRAY a av * H) s /\ (ARRAY a av' * H') s ==> av' = av`,
rw[UNIQUE_PTRS_def] >> fs[ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
`!A H1 H2. (&A * H1 * H2) s <=> A /\ (H1 * H2) s` by metis_tac[HCOND_EXTRACT, STAR_COMM] >>
POP_ASSUM (fn x => fs[x]) >> rw[] >> LAST_X_ASSUM (fn x => IMP_RES_TAC x) >> fs[]);

val UNIQUE_W8ARRAYS = Q.store_thm("UNIQUE_W8ARRAYS",
`!s a av av' H H'. UNIQUE_PTRS s ==> (W8ARRAY a av * H) s /\ (W8ARRAY a av' * H') s ==> av' = av`,
rw[UNIQUE_PTRS_def] >> fs[W8ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
`!A H1 H2. (&A * H1 * H2) s <=> A /\ (H1 * H2) s` by metis_tac[HCOND_EXTRACT, STAR_COMM] >>
POP_ASSUM (fn x => fs[x]) >> rw[] >> LAST_X_ASSUM (fn x => IMP_RES_TAC x) >> fs[]);

val UNIQUE_REFS_EXT = Q.store_thm("UNIQUE_REFS_EXT",
`!s r xv xv' H H'. VALID_HEAP s ==> (r ~~> xv * H) s /\ (r ~~> xv' * H') s ==> xv' = xv`,
rw[VALID_HEAP_def] >> IMP_RES_TAC UNIQUE_REFS);

val UNIQUE_ARRAYS_EXT = Q.store_thm("UNIQUE_ARRAYS_EXT",
`!s a av av' H H'. VALID_HEAP s ==> (ARRAY a av * H) s /\ (ARRAY a av' * H') s ==> av' = av`,
rw[VALID_HEAP_def] >> IMP_RES_TAC UNIQUE_ARRAYS);

val UNIQUE_W8ARRAYS_EXT = Q.store_thm("UNIQUE_W8ARRAYS_EXT",
`!s a av av' H H'. VALID_HEAP s ==> (W8ARRAY a av * H) s /\ (W8ARRAY a av' * H') s ==> av' = av`,
rw[VALID_HEAP_def] >> IMP_RES_TAC UNIQUE_W8ARRAYS);

(* Unicity results for ffi parts*)
fun instantiate_valid_ffi_heap_assum th (g as (asl, w)) =
  let
      val filter = Term.match_term ``(IO s u ns * H) h``
      val [(tm_s1, ty_s1), (tm_s2, ty_s2)] = mapfilter filter asl
      fun inst_type ty_s = List.map (fn {redex = x, residue = y} => (Term.inst ty_s x |-> y))
      val tm_s1 = inst_type ty_s1 tm_s1
      val tm_s2 = inst_type ty_s2 tm_s2
      fun find_inst tm_s =
	let
	    val s = Term.subst tm_s ``s:ffi``
	    val u = Term.subst tm_s ``u:tvarN -> word8 list -> ffi -> (word8 list # ffi) option``
	    val ns = Term.subst tm_s ``ns:tvarN list``
	    val H = Term.subst tm_s ``H:hprop``
	in
	    (s, u, ns, H)
	end
      val (s1, u1, ns1, H1) = find_inst tm_s1
      val (s2, u2, ns2, H2) = find_inst tm_s2
  in
      ASSUME_TAC (SPECL [s1, u1, ns1, s2, u2, ns2, H1, H2] th) g
  end;

val UNIQUE_STDOUT = Q.store_thm("UNIQUE_STDOUT",
`!s. VALID_HEAP s ==> !out1 out2 H1 H2. (STDOUT out1 * H1) s /\ (STDOUT out2 * H2) s ==> out2 = out1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[STDOUT_def, IOx_def, stdout_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[]);

val UNIQUE_STDERR = Q.store_thm("UNIQUE_STDERR",
`!s. VALID_HEAP s ==> !err1 err2 H1 H2. (STDERR err1 * H1) s /\ (STDERR err2 * H2) s ==> err2 = err1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[STDERR_def, IOx_def, stderr_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[]);

val UNIQUE_STDIN = Q.store_thm("UNIQUE_STDIN",
`!s H1 H2 in1 in2 b1 b2.
VALID_HEAP s ==> (STDIN in1 b1 * H1) s /\ (STDIN in2 b2 * H2) s ==> in2 = in1 /\ b2 = b1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def]
>-(
    fs[STDIN_def, IOx_def, stdin_ffi_part_def] >>
    fs[GSYM STAR_ASSOC] >>
    LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
    fs[]
) >>
fs[STDIN_def] >>
fs[SEP_CLAUSES, SEP_EXISTS_THM] >>
`(W8ARRAY read_state_loc [w; if b1 then 1w else 0w] * (IOx stdin_ffi_part in1 * H1)) s` by metis_tac[STAR_ASSOC, STAR_COMM] >>
`(W8ARRAY read_state_loc [w'; if b2 then 1w else 0w] * (IOx stdin_ffi_part in2 * H2)) s` by metis_tac[STAR_ASSOC, STAR_COMM] >>
IMP_RES_TAC UNIQUE_W8ARRAYS >>
rw[] >>
Cases_on `b1` >> (Cases_on `b2` >> fs[]));

val UNIQUE_ROFS = Q.store_thm("UNIQUE_ROFS",
`!s fs1 fs2 H1 H2. VALID_HEAP s ==> (ROFS fs1 * H1) s /\ (ROFS fs2 * H2) s ==> fs2 = fs1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[ROFS_def, IOx_def, rofs_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV (list_ss) []) x |> ASSUME_TAC) >>
`(∃pn. pn = "open" ∨ pn = "fgetc" ∨ pn = "close" ∨ pn = "isEof") = T` by (rw[] >> metis_tac[]) >>
fs[]);

val UNIQUE_COMMANDLINE = Q.store_thm("UNIQUE_COMMANDLINE",
`!s cl1 cl2 H1 H2. VALID_HEAP s ==>
(COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[COMMANDLINE_def, IOx_def, commandLine_ffi_part_def, encode_def, encode_list_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[] >>
POP_ASSUM IMP_RES_TAC >>
sg `!l1 l2. (MAP Str l1 = MAP Str l2) ==> l2 = l1`
>-(
    Induct_on `l2` >-(rw[])>>
    rw[] >> fs[] >>
    Cases_on `l1` >-(fs[])>>  fs[]
) >>
fs[]);

(* Theorems and rewrites for REPLICATE and LIST_REL *)
val APPEND_LENGTH_INEQ = Q.store_thm("APPEND_LENGTH_INEQ",
`!l1 l2. LENGTH(l1) <= LENGTH(l1++l2) /\ LENGTH(l2) <= LENGTH(l1++l2)`,
Induct >-(strip_tac >> rw[]) >> rw[]);

val REPLICATE_APPEND_RIGHT = Q.prove(
`a++b = REPLICATE n x ==> b = REPLICATE (LENGTH b) x`,
strip_tac >>
`b = DROP (LENGTH a) (a++b)` by simp[GSYM DROP_LENGTH_APPEND] >>
`b = DROP (LENGTH a) (REPLICATE n x)` by POP_ASSUM (fn thm => metis_tac[thm]) >>
`b = REPLICATE (n - (LENGTH a)) x` by POP_ASSUM (fn thm => metis_tac[thm, DROP_REPLICATE]) >>
fs[LENGTH_REPLICATE]);

val REPLICATE_APPEND_LEFT = Q.prove(
`a++b = REPLICATE n x ==> a = REPLICATE (LENGTH a) x`,
strip_tac >> `b = REPLICATE (LENGTH b) x` by metis_tac[REPLICATE_APPEND_RIGHT] >>
`LENGTH b <= n` by metis_tac[APPEND_LENGTH_INEQ, LENGTH_REPLICATE] >>
`REPLICATE n x = REPLICATE (n-(LENGTH b)) x ++ REPLICATE (LENGTH b) x` by simp[REPLICATE_APPEND] >>
POP_ASSUM (fn x => fs[x]) >> POP_ASSUM (fn x => ALL_TAC) >>
`a ++ REPLICATE (LENGTH b) x = REPLICATE (n − LENGTH b) x ++ REPLICATE (LENGTH b) x` by metis_tac[] >>
fs[LENGTH_REPLICATE]);

val REPLICATE_APPEND_DECOMPOSE = Q.store_thm("REPLICATE_APPEND_DECOMPOSE",
`a ++ b = REPLICATE n x <=>
a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\ LENGTH a + LENGTH b = n`,
EQ_TAC >-(rw[] >-(metis_tac[REPLICATE_APPEND_LEFT]) >-(metis_tac[REPLICATE_APPEND_RIGHT]) >> metis_tac [LENGTH_REPLICATE, LENGTH_APPEND]) >> metis_tac[REPLICATE_APPEND]);

val REPLICATE_APPEND_DECOMPOSE_SYM = save_thm("REPLICATE_APPEND_DECOMPOSE_SYM",
CONV_RULE(PATH_CONV "lr" SYM_CONV) REPLICATE_APPEND_DECOMPOSE);

val REPLICATE_PLUS_ONE = Q.store_thm("REPLICATE_PLUS_ONE",
`REPLICATE (n + 1) x = x::REPLICATE n x`,
`n+1 = SUC n` by rw[] >> rw[REPLICATE]);

val LIST_REL_DECOMPOSE_RIGHT_recip = Q.prove(
`!R. LIST_REL R (a ++ b) x ==> LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x)`,
strip_tac >> strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
`LENGTH (a ++ b) = LENGTH x` by (MATCH_MP_TAC LIST_REL_LENGTH >> rw[]) >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV list_ss []) x |> ASSUME_TAC) >>
`LENGTH a <= LENGTH x` by bossLib.DECIDE_TAC >>
metis_tac[LENGTH_TAKE, LIST_REL_APPEND_IMP]);

val LIST_REL_DECOMPOSE_RIGHT_imp = Q.prove(
`!R. LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x) ==> LIST_REL R (a ++ b) x`,
rpt strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_DECOMPOSE_RIGHT = Q.store_thm("LIST_REL_DECOMPOSE_RIGHT",
`!R. LIST_REL R (a ++ b) x <=> LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x)`,
strip_tac >> metis_tac[LIST_REL_DECOMPOSE_RIGHT_recip, LIST_REL_DECOMPOSE_RIGHT_imp]);

val LIST_REL_DECOMPOSE_LEFT_recip = Q.prove(
`!R. LIST_REL R x (a ++ b) ==> LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b`,
strip_tac >> strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
`LENGTH x = LENGTH (a ++ b)` by (MATCH_MP_TAC LIST_REL_LENGTH >> rw[]) >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV list_ss []) x |> ASSUME_TAC) >>
`LENGTH a <= LENGTH x` by bossLib.DECIDE_TAC >>
metis_tac[LENGTH_TAKE, LIST_REL_APPEND_IMP]);

val LIST_REL_DECOMPOSE_LEFT_imp = Q.prove(
`!R. LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b ==> LIST_REL R x (a ++ b)`,
rpt strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_DECOMPOSE_LEFT = Q.store_thm("LIST_REL_DECOMPOSE_LEFT",
`!R. LIST_REL R x (a ++ b) <=> LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b`,
strip_tac >> metis_tac[LIST_REL_DECOMPOSE_LEFT_recip, LIST_REL_DECOMPOSE_LEFT_imp]);

val HEAD_TAIL = Q.store_thm("HEAD_TAIL",
`l <> [] ==> HD l :: TL l = l`,
Cases_on `l:'a list` >> rw[listTheory.TL, listTheory.HD]);

val HEAD_TAIL_DECOMPOSE_RIGHT = Q.store_thm("HEAD_TAIL_DECOMPOSE_RIGHT",
`x::a = b <=> b <> [] /\ x = HD b /\ a = TL b`,
rw[] >> EQ_TAC
>-(Cases_on `b:'a list` >-(rw[]) >>  rw[listTheory.TL, listTheory.HD, HEAD_TAIL]) >>
rw[HEAD_TAIL]);

val HEAD_TAIL_DECOMPOSE_LEFT = Q.store_thm("HEAD_TAIL_DECOMPOSE_LEFT",
`b = x::a <=> b <> [] /\ x = HD b /\ a = TL b`,
rw[] >> EQ_TAC
>-(Cases_on `b:'a list` >-(rw[]) >>  rw[listTheory.TL, listTheory.HD, HEAD_TAIL]) >>
rw[HEAD_TAIL]);
	 
(* Theorems used as rewrites for the refinement invariants *)
fun eqtype_unicity_thm_tac x =
  let
      val assum = MP (SPEC ``abs:'a -> v -> bool`` EqualityType_def |> EQ_IMP_RULE |> fst) x
  in
      MP_TAC assum
  end;

val EQTYPE_UNICITY_R = Q.store_thm("EQTYPE_UNICITY_R",
`!abs x y1 y2. EqualityType abs ==> abs x y1 ==> (abs x y2 <=> y2 = y1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

val EQTYPE_UNICITY_L = Q.store_thm("EQTYPE_UNICITY_L",
`!abs x1 x2 y. EqualityType abs ==> abs x1 y ==> (abs x2 y <=> x2 = x1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

(* Theorems to use LIST_REL A "as a" refinement invariant *)
val InjectiveRel_def = Define `
InjectiveRel A = !x1 y1 x2 y2. A x1 y1 /\ A x2 y2 ==> (x1 = x2 <=> y1 = y2)`;

val EQTYPE_INJECTIVEREL = Q.prove(`EqualityType A ==> InjectiveRel A`,
rw[InjectiveRel_def, EqualityType_def]);

val LIST_REL_INJECTIVE_REL = Q.store_thm("LIST_REL_INJECTIVE_REL",
`!A. InjectiveRel A ==> InjectiveRel (LIST_REL A)`,
rpt strip_tac >> SIMP_TAC list_ss [InjectiveRel_def] >> Induct_on `x1`
>-(
    rpt strip_tac >>
    fs[LIST_REL_NIL] >>
    EQ_TAC >>
    rw[LIST_REL_NIL] >>
    fs[LIST_REL_NIL]
) >>
rpt strip_tac >> fs[LIST_REL_def] >>
Cases_on `x2` >-(fs[LIST_REL_NIL]) >>
Cases_on `y2` >-(fs[LIST_REL_NIL]) >>
rw[] >> fs[LIST_REL_def] >>
EQ_TAC >> (rw[] >-(metis_tac[InjectiveRel_def]) >> metis_tac[]));

val LIST_REL_INJECTIVE_EQTYPE = Q.store_thm("LIST_REL_INJECTIVE_EQTYPE",
`!A. EqualityType A ==> InjectiveRel (LIST_REL A)`,
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_REL]);

val LIST_REL_UNICITY_RIGHT = Q.store_thm("LIST_REL_UNICITY_RIGHT",
`EqualityType A ==> LIST_REL A a b ==> (LIST_REL A a b' <=> b' = b)`,
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_EQTYPE, InjectiveRel_def]);

val LIST_REL_UNICITY_LEFT = Q.store_thm("LIST_REL_UNICITY_LEFT",
`EqualityType A ==> LIST_REL A a b ==> (LIST_REL A a' b <=> a' = a)`,
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_EQTYPE, InjectiveRel_def]);

(* Some theorems for rewrite rules with the refinement invariants *)
val RECONSTRUCT_INT = Q.store_thm("RECONSTRUCT_INT", `v = (Litv (IntLit i)) <=> INT i v`, rw[INT_def]);
val RECONSTRUCT_NUM = Q.store_thm("RECONSTRUCT_NUM", `v = (Litv (IntLit (&n))) <=> NUM n v`, rw[NUM_def, INT_def]);
val RECONSTRUCT_BOOL = Q.store_thm("RECONSTRUCT_BOOL", `v = Boolv b <=> BOOL b v`, rw[BOOL_def]);

val NUM_INT_EQ = Q.store_thm("NUM_INT_EQ",
`(!x y v. INT x v ==> (NUM y v <=> x = &y)) /\
(!x y v. NUM y v ==> (INT x v <=> x = &y)) /\
(!x v w. INT (&x) v ==> (NUM x w <=> w = v)) /\
(!x v w. NUM x v ==> (INT (&x) w <=> w = v))`,
fs[INT_def, NUM_def] >> metis_tac[]);

(* Some rules used to simplify arithmetic equations (not happy with that: write a conversion instead? *)

val NUM_EQ_lem = Q.prove(`!(a1:num) (a2:num) (b:num). b <= a1 ==> b <= a2 ==> (a1 = a2 <=> a1 - b = a2 - b)`, rw[]);

val NUM_EQ_SIMP1 = Q.store_thm("NUM_EQ_SIMP1",
`a1 + (NUMERAL n1)*b = a2 + (NUMERAL n2)*b <=>
a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b = a2 + (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b`,
  rw[MIN_DEF]
>-(
   `b*NUMERAL n1 <= a1 + b*NUMERAL n1` by rw[] >>
   `b*NUMERAL n1 <= a2 + b*NUMERAL n2` by (
      rw[] >>
      `b*NUMERAL n2 <= a2 + b*NUMERAL n2` by rw[] >>
      `b*NUMERAL n1 <= b*NUMERAL n2` by rw[] >>
      bossLib.DECIDE_TAC
   ) >>
   qspecl_then [`a1 + b * NUMERAL n1`, `a2 + b * NUMERAL n2`, `b * NUMERAL n1`] assume_tac NUM_EQ_lem >>
   POP_ASSUM (fn x => rw[x]) >>
   `b * (NUMERAL n2 - NUMERAL n1) = b * NUMERAL n2 - b * NUMERAL n1` by rw[] >>
   POP_ASSUM (fn x => rw[x]) >>
   `b*NUMERAL n1 <= b* NUMERAL n2` by rw[] >>
   bossLib.DECIDE_TAC
) >>
  `b*NUMERAL n1 <= a2 + b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= a1 + b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= a2 + b*NUMERAL n2` by rw[] >>
  qspecl_then[`a1 + b * NUMERAL n1`, `a2 + b * NUMERAL n2`, `b * NUMERAL n2`]assume_tac NUM_EQ_lem >>
  POP_ASSUM (fn x => rw[x]));

val NUM_EQ_SIMP2 = Q.store_thm("NUM_EQ_SIMP2",
`(NUMERAL n1)*b + a1 = (NUMERAL n2)*b + a2 <=>
(NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]);

val NUM_EQ_SIMP3 = Q.store_thm("NUM_EQ_SIMP3",
`a1 + (NUMERAL n1)*b = (NUMERAL n2)*b + a2 <=>
a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]);

val NUM_EQ_SIMP4 = Q.store_thm("NUM_EQ_SIMP4",
`(NUMERAL n1)*b + a1 = a2 + (NUMERAL n2)*b <=>
(NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]);

val NUM_EQ_SIMP5 = Q.store_thm("NUM_EQ_SIMP5",
`a1 + b = a2 + (NUMERAL n2)*b <=>
a1 + (1 - (MIN 1 (NUMERAL n2)))*b = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b`,
`a1 + b = a1 + 1*b` by rw[] >>
POP_ASSUM (fn x => PURE_REWRITE_TAC [x]) >>
metis_tac[NUM_EQ_SIMP1]);

val NUM_EQ_SIMP6 = Q.store_thm("NUM_EQ_SIMP6",
`a1 + (NUMERAL n1)*b = a2 + b <=>
a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b = a2 + (1 - (MIN 1 (NUMERAL n1)))*b`,
`a2 + b = a2 + 1*b` by rw[] >>
POP_ASSUM (fn x => PURE_REWRITE_TAC [x]) >>
metis_tac[NUM_EQ_SIMP1]);

val NUM_EQ_SIMP7 = Q.store_thm("NUM_EQ_SIMP7",
`b + a1 = (NUMERAL n2)*b + a2 <=>
(1 - (MIN 1 (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]);

val NUM_EQ_SIMP8 = Q.store_thm("NUM_EQ_SIMP8",
`(NUMERAL n1)*b + a1 = b + a2 <=>
(NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b + a1 = (1 - (MIN 1 (NUMERAL n1)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]);

val NUM_EQ_SIMP9 = Q.store_thm("NUM_EQ_SIMP9",
`a1 + b = (NUMERAL n2)*b + a2 <=>
a1 + (1 - (MIN 1 (NUMERAL n2)))*b = (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]);

val NUM_EQ_SIMP10 = Q.store_thm("NUM_EQ_SIMP10",
`b + a1 = a2 + (NUMERAL n2)*b <=>
(1 - (MIN 1 (NUMERAL n2)))*b + a1 = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]);

val NUM_EQ_SIMP11 = Q.store_thm("NUM_EQ_SIMP11",
`a1 + (NUMERAL n1)*b = b + a2 <=>
a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b = (1 - (MIN 1 (NUMERAL n1)))*b + a2`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]);

val NUM_EQ_SIMP12 = Q.store_thm("NUM_EQ_SIMP12",
`(NUMERAL n1)*b + a1 = a2 + b <=>
(NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b + a1 = a2 + (1 - (MIN 1 (NUMERAL n1)))*b`,
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]);

val _ = export_theory();
