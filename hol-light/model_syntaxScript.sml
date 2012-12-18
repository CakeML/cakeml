open HolKernel Parse boolLib bossLib Opentheory arithmeticTheory rich_listTheory;
open stringTheory;
val _ = new_theory"model_syntax"
val BIT0_def = Define `
  (BIT0 0 = 0) /\
  (BIT0 (SUC n) = SUC (SUC (BIT0 n)))`
val member_def = Define`member x y = MEM x y`
val replicate_def = Define `replicate x n = REPLICATE n x`;
val infinite_def = Define `infinite s = ~(FINITE s)`;

val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="model_syntax",Name="BIT0"},name=(["Number","Natural"],"bit0")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="HD"},name=(["Data","List"],"head")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="TL"},name=(["Data","List"],"tail")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="model_syntax",Name="member"},name=(["Data","List"],"member")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="EXISTS"},name=(["Data","List"],"any")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="FILTER"},name=(["Data","List"],"filter")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="MAP"},name=(["Data","List"],"map")}
val _ = OpenTheoryMap.OpenTheory_tyop_name {tyop={Thy="sum",Tyop="sum"},name=(["Data","Sum"],"+")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="sum",Name="INR"},name=(["Data","Sum"],"right")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="sum",Name="INL"},name=(["Data","Sum"],"left")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="sum",Name="OUTR"},name=(["Data","Sum"],"destRight")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="sum",Name="OUTL"},name=(["Data","Sum"],"destLeft")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="model_syntax",Name="replicate"},name=(["Data","List"],"replicate")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="FLAT"},name=(["Data","List"],"concat")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="pred_set",Name="IMAGE"},name=(["Set"],"image")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="combin",Name="I"},name=(["Set"],"fromPredicate")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="pred_set",Name="INTER"},name=(["Set"],"intersect")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="model_syntax",Name="infinite"},name=(["Set"],"infinite")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="pred_set",Name="UNIV"},name=(["Set"],"universe")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="pred_set",Name="DIFF"},name=(["Set"],"difference")};
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="bool",Name="IN"},name=(["Set"],"member")};

fun const_name n =
  if mem (snd n) ["ORD","CHR"] then {Thy="string",Name=snd n}
  else const_name_in_map n handle NotFound => {Thy="model_syntax",Name=snd n}
fun tyop_name n =
  if snd n = "char" then {Thy="string",Tyop=snd n}
  else tyop_name_in_map n handle NotFound => {Thy="model_syntax",Tyop=snd n}
fun fix_name "|-" = "proves"
  | fix_name "===" = "equiv"
  | fix_name s = if String.sub(s,0) = #"_" then ("model_syntax"^s) else s
val _ = Parse.set_fixity "|-" (Parse.Infixr 30);
val _ = Parse.set_fixity "===" (Parse.Infixr 50);
val reader =
{ define_tyop  = define_tyop_in_thy
, define_const = define_const_in_thy fix_name
, axiom        = axiom_in_db
, const_name   = const_name
, tyop_name    = tyop_name
}

val r = ref 0;
fun store (goal,tac) = (r := (!r)+1; store_thm("a_"^(int_to_string (!r)),goal,tac));

val BIT0_THM = prove(
  ``!n. BIT0 n = 2 * n``,
  Induct THEN EVAL_TAC THEN FULL_SIMP_TAC std_ss [ADD1] THEN DECIDE_TAC);
val BIT_SIMP = prove(
  ``(BIT0 = \n. 2 * n) /\ (BIT1 = \n. 2 * n + 1)``,
  SIMP_TAC std_ss [BIT0_THM,FUN_EQ_THM]
  THEN REWRITE_TAC [BIT1,ALT_ZERO,NUMERAL_DEF,BIT2] THEN DECIDE_TAC);
val BIT1_0 = prove(
  ``BIT1 0 = 1``,
  REWRITE_TAC [BIT1,ALT_ZERO,NUMERAL_DEF]);
val TWICE_ZERO = prove(
  ``2 * ZERO = 0``,
  REWRITE_TAC [BIT1,ALT_ZERO,NUMERAL_DEF] THEN SIMP_TAC std_ss []);
val _ = store(
  ``!n. EVEN (BIT0 (BIT1 0) * n)``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]
  THEN SIMP_TAC std_ss [EVEN_DOUBLE]);
val _ = store(
  ``!n. BIT0 (SUC n) = SUC (SUC (BIT0 n))``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]);
val _ = store(
  ``!m n. m + SUC n = SUC (m + n)``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]);
val _ = store(
  ``!m n. SUC m + n = SUC (m + n)``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]);
val _ = store(
  ``BIT0 0 = 0``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]);
val _ = store(
  ``!n. 0 + n = n``,
  SIMP_TAC bool_ss [BIT1,BIT0_def,ADD_CLAUSES]);
val _ = store(
  ``!n. BIT1 n = SUC (BIT0 n)``,
  SIMP_TAC bool_ss [BIT1,BIT0_THM,ADD_CLAUSES] THEN DECIDE_TAC);
val _ = store(
  ``!n. BIT0 (BIT1 0) * n = n + n``,
  SIMP_TAC bool_ss [BIT0_THM,BIT1] THEN FULL_SIMP_TAC std_ss [] THEN DECIDE_TAC);
val _ = store(
  ``!m n. m <= SUC n <=> (m = SUC n) \/ m <= n``,
  DECIDE_TAC);
val _ = store(
  ``!m n. SUC m <= n <=> m < n``,
  DECIDE_TAC);
val _ = store(
  ``!m n p. m * n < m * p <=> m <> 0 /\ n < p``,
  Cases THEN SIMP_TAC std_ss [] THEN DECIDE_TAC);
val _ = store(
  ``!n. EVEN (SUC n) <=> ~EVEN n``,
  SIMP_TAC std_ss [EVEN]);
val _ = store(
  ``!m n. m <= n /\ n <= m <=> (m = n:num)``,
  DECIDE_TAC);
val _ = store(
  ``!m n. ~(m <= n /\ n < m)``,
  DECIDE_TAC);
val _ = store(
  ``!m n. m ** SUC n = m * m ** n``,
  FULL_SIMP_TAC std_ss [EXP]);
val _ = store(
  ``!m. m ** 0 = BIT1 0``,
  ONCE_REWRITE_TAC [EXP,BIT1_0] THEN SIMP_TAC std_ss []);
val _ = store(
  ``!m n. (m ** n = 0) <=> (m = 0) /\ n <> 0``,
  SIMP_TAC std_ss [EXP_EQ_0] THEN DECIDE_TAC);
val _ = store(
  ``!p. (!x. ?!y. p x y) <=> ?f. !x y. p x y <=> (f x = y)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `\x. @y. p x y` THEN METIS_TAC [])
  THEN ASM_SIMP_TAC std_ss []);
val _ = store(
  ``!p. p [] /\ (!h t. p t ==> p (h::t)) ==> !l. p l``,
  NTAC 2 STRIP_TAC THEN Induct THEN FULL_SIMP_TAC std_ss []);
val _ = store(
  ``!p. EVERY p []``,
   SRW_TAC [] []);
val _ = store(
  ``!p h t. EVERY p (h::t) <=> p h /\ EVERY p t``,
   SRW_TAC [] []);
val _ = store(
  ``!p. (!x. p x) <=> !a b. p (a,b)``,
   SRW_TAC [] [pairTheory.FORALL_PROD]);
val _ = store(
  ``!p l. (!x. member x l ==> p x) <=> EVERY p l``,
  SIMP_TAC std_ss [listTheory.EVERY_MEM,member_def]);
val _ = store(
  ``!x h t. member x (h::t) <=> (x = h) \/ member x t``,
  SIMP_TAC std_ss [listTheory.MEM,member_def]);
val _ = store(
  ``!x. ~(member x [])``,
  SIMP_TAC std_ss [listTheory.MEM,member_def]);
val _ = store(
  ``!p g h. ?f. !x. f x = if p x then f (g x) else h x``,
  REPEAT STRIP_TAC THEN Q.EXISTS_TAC `\x. h (WHILE p g x)`
  THEN SIMP_TAC std_ss [Once whileTheory.WHILE] THEN METIS_TAC []);
val _ = store(
  ``!p. (!b. p b) <=> p T /\ p F``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN Cases_on `b` THEN ASM_SIMP_TAC std_ss []);
val _ = store(
  ``!f. MAP f [] = []``,
  SRW_TAC [] [listTheory.MAP]);
val _ = store(
  ``!f h t. MAP f (h::t) = f h::MAP f t``,
  SRW_TAC [] [listTheory.MAP]);
val _ = store(
  ``!p x. x IN I p <=> p x``,
  SIMP_TAC std_ss [boolTheory.IN_DEF]);
val _ = store(
  ``!s t. (!x. x IN s <=> x IN t) <=> (s = t)``,
  SIMP_TAC std_ss [pred_setTheory.EXTENSION]);
val _ = store(``!s x. FINITE (x INSERT s) <=> FINITE s``,
  SRW_TAC [] []);
val _ = store(``!f s. FINITE s ==> FINITE (IMAGE f s)``,
  SRW_TAC [] []);
val _ = store(``!s t. FINITE t /\ s SUBSET t ==> FINITE s``,
  METIS_TAC [pred_setTheory.SUBSET_FINITE]);
val _ = store(``!x. replicate x 0 = []``,
  SIMP_TAC std_ss [replicate_def,REPLICATE]);
val _ = store(``!x n. replicate x (SUC n) = x::replicate x n``,
  SIMP_TAC std_ss [replicate_def,REPLICATE]);
val _ = store(``!h1 h2 t1 t2. (h1::t1 = h2::t2) <=> (h1 = h2) /\ (t1 = t2)``,
  SRW_TAC [] []);
val _ = store(``!h t. h::t <> []``,
  SRW_TAC [] []);
val _ = store(``!l. [] ++ l = l``,
  SIMP_TAC std_ss [listTheory.APPEND]);
val _ = store(``!l h t. h::t ++ l = h::(t ++ l)``,
  SIMP_TAC std_ss [listTheory.APPEND]);
val _ = store(``infinite univ(:num)``,
  SIMP_TAC std_ss [infinite_def,pred_setTheory.INFINITE_NUM_UNIV]);
val _ = store(``!f s.
  (!x y. (f x = f y) ==> (x = y)) /\ infinite s ==> infinite (IMAGE f s)``,
  SIMP_TAC std_ss [infinite_def,pred_setTheory.infinite_num_inj]
  THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `f o f'`
  THEN MATCH_MP_TAC pred_setTheory.INJ_COMPOSE
  THEN Q.EXISTS_TAC `s`
  THEN FULL_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC (srw_ss()) [pred_setTheory.INJ_DEF]);
val _ = store(``!s t. infinite s /\ FINITE t ==> infinite (s DIFF t)``,
  SIMP_TAC std_ss [infinite_def] THEN METIS_TAC [pred_setTheory.FINITE_DIFF_down]);
val _ = store(``!s. infinite s ==> s <> {}``,
  SIMP_TAC std_ss [infinite_def,pred_setTheory.FINITE_EMPTY]);
val _ = store(``!m a b. (!y. measure m y a ==> measure m y b) <=> m a <= m b``,
  REWRITE_TAC [prim_recTheory.measure_thm]
  THEN REPEAT STRIP_TAC THEN Tactical.REVERSE EQ_TAC THEN REPEAT STRIP_TAC
  THEN1 IMP_RES_TAC LESS_LESS_EQ_TRANS
  THEN REWRITE_TAC [GSYM NOT_LESS] THEN CCONTR_TAC
  THEN FULL_SIMP_TAC bool_ss [] THEN RES_TAC
  THEN FULL_SIMP_TAC bool_ss [prim_recTheory.LESS_REFL]);
val _ = store(``!m n. n < m + n <=> 0 < m``,
  DECIDE_TAC);
val _ = store(``!p l x. member x (FILTER p l) <=> member x l /\ p x``,
  SIMP_TAC (srw_ss()) [member_def,listTheory.MEM_FILTER] THEN METIS_TAC []);
val _ = store(``!m n. n <= m + n``,
  DECIDE_TAC);
val _ = store(``!n. 0 < n <=> n <> 0``,
  DECIDE_TAC);
val _ = store(``!m n. m < m + n <=> 0 < n``,
  DECIDE_TAC);
val _ = store(``($o :('b -> 'c) -> ('a -> 'b) -> 'a -> 'c) =
                (\(f :'b -> 'c) (g :'a -> 'b) (x :'a). f (g x))``,
  SIMP_TAC (srw_ss()) [FUN_EQ_THM]);

val thms = Net.listItems (read_article "model_syntax.art" reader) handle e => Raise e

val _ = map (fn th => let
  val v = th |> concl |> dest_imp |> fst
  val name = v |> dest_var |> fst
  val th = MP (INST [v|->T] th) TRUTH
  val th = REWRITE_RULE [member_def,replicate_def,infinite_def] th
  val th = th |> ONCE_REWRITE_RULE [ALT_ZERO,NUMERAL_DEF]
              |> ONCE_REWRITE_RULE [BIT_SIMP]
              |> SIMP_RULE std_ss [TWICE_ZERO]
  in save_thm(name,th) end) thms

val _ = export_theory()
