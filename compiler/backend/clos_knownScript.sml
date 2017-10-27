open preamble closLangTheory;

val _ = new_theory "clos_known";

val _ = set_grammar_ancestry ["closLang", "sptree", "misc"]

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* -----------------------------------------------------------------

  This compiler transformation turns App NONEs into APP SOMEs.
  An App can carry a `SOME loc` if:
   1) the closure value that is used there was created with location loc;
   2) the closure value exepcts the number of arguments it gets here.

  This part of the compiler makes two passes. The first pass tracks
  which closure values flow into which globals. The second pass tracks
  closure values (with help of the result of the first pass) and
  switches App NONEs into App SOMEs wherever possible.

   ----------------------------------------------------------------- *)

val _ = Datatype `
  val_approx =
    Clos num num                (* location in code table, arity *)
  | Tuple num (val_approx list) (* conses or tuples *)
  | Int int                     (* used to index tuples *)
  | Other                       (* unknown *)
  | Impossible`                 (* value 'returned' by Raise *)
val val_approx_size_def = definition "val_approx_size_def"

val merge_def = tDefine "merge" `
  (merge Impossible y = y) ∧
  (merge x Impossible = x) ∧
  (merge (Tuple tg1 xs) (Tuple tg2 ys) =
     if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then Tuple tg1 (MAP2 merge xs ys)
     else Other) ∧
  (merge (Clos m1 n1) (Clos m2 n2) = if m1 = m2 ∧ n1 = n2 then Clos m1 n1
                                     else Other) ∧
  (merge (Int i) (Int j) = if i = j then Int i else Other) ∧
  (merge _ _ = Other)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> Induct_on `xs` >>
   rw[val_approx_size_def] >> simp[] >>
   rename[`MEM x xs`, `MEM y ys`, `SUC (LENGTH xs) = LENGTH ys`,
          `tag + (val_approx1_size xs + _)`, `val_approx_size x < _`] >>
   first_x_assum (qspecl_then [`tag`, `y::TL (TL ys)`, `x`, `y`] mp_tac) >>
   impl_tac >> simp[] >> Cases_on `ys` >> fs[] >> Cases_on `xs` >> fs[] >>
   rename1 `SUC (LENGTH _) = LENGTH ll` >> Cases_on `ll` >> fs[])
val merge_def =
    save_thm("merge_def[simp]", SIMP_RULE (bool_ss ++ ETA_ss) [] merge_def)

(* Avoid MAP2 *)
val merge_tup_def = tDefine "merge_tup" `
  (merge_tup (Impossible,y) = y) ∧
  (merge_tup (x,Impossible) = x) ∧
  (merge_tup (Tuple tg1 xs,Tuple tg2 ys) =
     if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then
       Tuple tg1 (MAP merge_tup (ZIP(xs,ys)))
     else Other) ∧
  (merge_tup (Clos m1 n1,Clos m2 n2) = if m1 = m2 ∧ n1 = n2 then Clos m1 n1
                                     else Other) ∧
  (merge_tup (Int i,Int j) = if i = j then Int i else Other) ∧
  (merge_tup (_,_) = Other)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> Induct_on `xs` >>
   rpt strip_tac>>
   imp_res_tac MEM_ZIP>>fs[]>>
   rw[val_approx_size_def] >> Cases_on`ys`>>fs[]>>
   first_x_assum (first_assum o mp_then (Pos (el 2)) mp_tac) >>
   simp[] >> rename[`_ < (tag:num) + (_ + _)`] >>
   disch_then (qspec_then `tag` mp_tac) >> simp[])

(* TODO: this function seems to throw the translator into an infinite loop
val merge_tup_pmatch = Q.store_thm("merge_tup_pmatch",`!tup.
  merge_tup tup =
    case tup of
      (Impossible,y) => y
    | (x,Impossible) => x
    | (Tuple tg1 xs,Tuple tg2 ys) =>
      if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then Tuple tg1 (MAP merge_tup (ZIP(xs,ys)))
      else Other
    | (Clos m1 n1,Clos m2 n2) => if m1 = m2 ∧ n1 = n2 then Clos m1 n1
                                 else Other
    | (Int i,Int j) => if i = j then Int i else Other
    | _ => Other`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[merge_tup_def] >> metis_tac []);
 *)

val merge_alt = Q.store_thm("merge_alt",`
  ∀x y.merge x y = merge_tup (x,y)`,
  HO_MATCH_MP_TAC (fetch "-" "merge_ind")>>rw[merge_tup_def,MAP2_MAP]>>
  match_mp_tac LIST_EQ>>rw[EL_ZIP,EL_MAP]>>
  first_x_assum match_mp_tac>>metis_tac[MEM_EL])

val known_op_def = Define `
  (known_op (Global n) as g =
   if NULL as then
     dtcase lookup n g of
       | NONE => (Other,g)
       | SOME x => (x,g)
   else (Other,g)) /\
  (known_op (SetGlobal n) as g =
     dtcase as of
     | [] => (Other,g)
     | (a::xs) =>
       dtcase lookup n g of
       | NONE => (Other,insert n a g)
       | SOME other => (Other,insert n (merge other a) g)) /\
  (known_op (Cons tg) as g = (Tuple tg as,g)) /\
  (known_op (Const i) as g = (Int i,g)) /\
  (known_op El as g =
     dtcase as of
     | [Tuple _ xs; Int i] =>
         if 0 <= i /\ i < &LENGTH xs
         then (EL (Num i) xs,g)
         else (Other,g)
     | Impossible::xs => (Impossible,g)
     | _ :: Impossible :: xs => (Impossible,g)
     | _ => (Other,g)) /\
(known_op op as g = (Other,g))`

val known_op_pmatch = Q.store_thm("known_op_pmatch",`!op as g.
known_op op as g =
  case op of
    Global n =>
     if NULL as then
       case lookup n g of
         | NONE => (Other,g)
         | SOME x => (x,g)
     else (Other,g)
  | SetGlobal n =>
    (case as of
     | [] => (Other,g)
     | (a::xs) =>
       case lookup n g of
       | NONE => (Other,insert n a g)
       | SOME other => (Other,insert n (merge other a) g))
  | Cons tg => (Tuple tg as,g)
  | Const i => (Int i,g)
  | El =>
    (case as of
     | [Tuple _ xs; Int i] =>
         if 0 <= i /\ i < &LENGTH xs
         then (EL (Num i) xs,g)
         else (Other,g)
     | Impossible::xs => (Impossible,g)
     | _ :: Impossible :: xs => (Impossible,g)
     | _ => (Other,g))
  | _ => (Other,g)`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[known_op_def])

val EL_MEM_LEMMA = Q.prove(
  `!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs`,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);

val dest_Clos_def = Define `
  (dest_Clos (Clos n a) = SOME (n,a)) /\
  (dest_Clos _ = NONE)`;
val _ = export_rewrites["dest_Clos_def"];

val clos_gen_def = Define`
  (clos_gen n i [] = []) ∧
  (clos_gen n i ((x,_)::xs) = Clos (n+2*i) x::clos_gen n (i+1) xs)`

val _ = Datatype`globalOpt = gO_Int int | gO_NullTuple num | gO_None`

val isGlobal_def = Define`
  (isGlobal (Global _) ⇔ T) ∧
  (isGlobal _ ⇔ F)
`
val isGlobal_pmatch = Q.store_thm("isGlobal_pmatch",`!op.
  isGlobal op =
  case op of
    Global _ => T
    | _ => F`,
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[isGlobal_def])

val gO_destApx_def = Define`
  (gO_destApx (Int i) = gO_Int i) ∧
  (gO_destApx (Tuple tag args) = if NULL args then gO_NullTuple tag
                                 else gO_None) ∧
  (gO_destApx _ = gO_None)
`;

val known_def = tDefine "known" `
  (known [] vs (g:val_approx spt) = ([],g)) /\
  (known ((x:closLang$exp)::y::xs) vs g =
     let (e1,g) = known [x] vs g in
     let (e2,g) = known (y::xs) vs g in
       (e1 ++ e2,g)) /\
  (known [Var t v] vs g =
     ([(Var t v,any_el v vs Other)],g)) /\
  (known [If t x1 x2 x3] vs g =
     let (e1,g) = known [x1] vs g in
     let (e2,g) = known [x2] vs g in
     let (e3,g) = known [x3] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
     let (e3,a3) = HD e3 in
       ([(If t e1 e2 e3), merge a2 a3],g)) /\
  (known [Let t xs x2] vs g =
     let (e1,g) = known xs vs g in
     let (e2,g) = known [x2] (MAP SND e1 ++ vs) g in
     let (e2,a2) = HD e2 in
       ([(Let t (MAP FST e1) e2, a2)],g)) /\
  (known [Raise t x1] vs g =
     let (e1,g) = known [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Raise t e1,Impossible)],g)) /\
  (known [Tick t x1] vs g =
     let (e1,g) = known [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Tick t e1,a1)],g)) /\
  (known [Handle t x1 x2] vs g =
     let (e1,g) = known [x1] vs g in
     let (e2,g) = known [x2] (Other::vs) g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
       ([(Handle t e1 e2,merge a1 a2)],g)) /\
  (known [Call t ticks dest xs] vs g =
     let (e1,g) = known xs vs g in
       ([(Call t ticks dest (MAP FST e1),Other)],g)) /\
  (known [Op t op xs] vs g =
     let (e1,g) = known xs vs g in
     let (a,g) = known_op op (REVERSE (MAP SND e1)) g in
     let e =
         if isGlobal op then
           dtcase gO_destApx a of
               gO_None => Op t op (MAP FST e1)
             | gO_Int i => Op t (Const i) []
             | gO_NullTuple tag => Op t (Cons tag) []
         else Op t op (MAP FST e1)
     in
       ([(e,a)],g)) /\
  (known [App t loc_opt x xs] vs g =
     let (e2,g) = known xs vs g in
     let (e1,g) = known [x] vs g in
     let (e1,a1) = HD e1 in
     let new_loc_opt =
         dtcase loc_opt of
           | SOME _ => loc_opt
           | _ => dtcase dest_Clos a1 of
                    | NONE => NONE
                    | SOME (loc,arity) => if arity = LENGTH xs
                                          then SOME loc else NONE
     in
       ([(App t new_loc_opt e1 (MAP FST e2),Other)],g)) /\
  (known [Fn t loc_opt ws_opt num_args x1] vs g =
     let (e1,g) = known [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD e1 in
       ([(Fn t loc_opt NONE num_args body,
          dtcase loc_opt of
          | SOME loc => Clos loc num_args
          | NONE => Other)],g)) /\
  (known [Letrec t loc_opt _ fns x1] vs g =
     let clos = dtcase loc_opt of
                   NONE => REPLICATE (LENGTH fns) Other
                |  SOME n => clos_gen n 0 fns in
     (* The following ignores SetGlobal within fns, but it shouldn't
        appear there, and missing it just means this opt will do less. *)
     let new_fns = MAP (\(num_args,x).
                    let new_vs = REPLICATE num_args Other ++ clos ++ vs in
                    let res = known [x] new_vs g in
                      (num_args,FST (HD (FST res)))) fns in
     let (e1,g) = known [x1] (clos ++ vs) g in
     let (e1,a1) = HD e1 in
       ([(Letrec t loc_opt NONE new_fns e1,a1)],g))`
 (WF_REL_TAC `measure (exp3_size o FST)`
  \\ REPEAT STRIP_TAC
  \\ fs [GSYM NOT_LESS]
  \\ IMP_RES_TAC EL_MEM_LEMMA
  \\ IMP_RES_TAC exp1_size_lemma
  \\ DECIDE_TAC);

val compile_def = Define `
  compile F exp = exp /\
  compile T exp =
    let (_,g) = known [exp] [] LN in
    let (e,_) = known [exp] [] g in
      FST (HD e)`

val known_LENGTH = Q.store_thm(
  "known_LENGTH",
  `∀es vs g. LENGTH (FST (known es vs g)) = LENGTH es`,
  ho_match_mp_tac (fetch "-" "known_ind") >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]))

val known_LENGTH_EQ_E = Q.store_thm(
  "known_LENGTH_EQ_E",
  `known es vs g0 = (alist, g) ⇒ LENGTH alist = LENGTH es`,
  metis_tac[FST, known_LENGTH]);

val known_sing = Q.store_thm(
  "known_sing",
  `∀e vs g. ∃e' a g'. known [e] vs g = ([(e',a)], g')`,
  rpt strip_tac >> Cases_on `known [e] vs g` >>
  rename1 `known [e] vs g = (res,g')` >>
  qspecl_then [`[e]`, `vs`, `g`] mp_tac known_LENGTH >> simp[] >>
  Cases_on `res` >> simp[LENGTH_NIL] >> metis_tac[pair_CASES])

val known_sing_EQ_E = Q.store_thm(
  "known_sing_EQ_E",
  `∀e vs g0 all g. known [e] vs g0 = (all, g) ⇒ ∃e' apx. all = [(e',apx)]`,
  metis_tac[PAIR_EQ, known_sing]);

(*

  TEST 1

  let fun f x = f x in f end

  val f = ``Letrec (SOME 200) NONE [(1,App NONE (Var 1) [Var 0])] (Var 0)``
  val ev = EVAL ``compile T ^f``

  TEST 2

  let
    val f = fn k => (get_global 60) (k + 1)
    val g = set_global 60 f
  in f 4 end

  val f = ``Fn (SOME 900) NONE 1 (App NONE (Op (Global 60) []) [Op Add [Var 0; Op (Const 1) []]])``
  val g = ``closLang$Op (SetGlobal 60) [Var 0]``
  val exp = ``Let [^f] (Let [^g] (App NONE (Var 1) [Op (Const 4) []]))``
  val ev = EVAL ``compile T ^exp``

  TEST 2A

  let
    val f = fn k => k + 1
    val g = set_global 60 f
  in
    get_global 60 3
  end

  val f = ``Fn (SOME 900) NONE 1 (Op Add [Var 0; Op (Const 1) []])``
  val g = ``closLang$Op (SetGlobal 60) [Var 0]``
  val exp = ``Let [^f] (Let [^g] (App NONE
                                      (Op (Global 60) [])
                                      [Op (Const 3) []]))``
  val ev = EVAL ``compile T ^exp``


  TEST 2B (* works nicely *)

  let
    val f = fn k => k + 1
    val g = set_global 60 f
    val h = set_global 62 (get_global 60)
  in
    h
  end

  val h = ``closLang$Op (SetGlobal 62) [Op (Global 60) []]``
  val exp = ``Let [^f] (Let [^g] (Let [^h] (Var 0)))``

  val ev1 = EVAL ``known [^exp] [] LN``

  TEST 2C
    (* is ghastly; the g-map will never pick up a good value for global 62 *)

  let
    val f = fn k => k + 1
    val h = fn k => set_global 62 (get_global 60)
    val g = set_global 60 f
  in
    h 1
  end

  val h = ``Fn (SOME 800) NONE 1
               (closLang$Op (SetGlobal 62) [Op (Global 60) []])``
  val exp = ``Let [^f] (Let [^h]
                (Let [^g] (App NONE (Var 1) [Op (Const 1) []])))``

  val ev1 = EVAL ``known [^exp] [] LN``
  val ev2 = EVAL ``known [^exp] [] ^(#2 (dest_pair (rhs (concl ev1))))``


  TEST 3

  let val xy =
        let val f = fn k => k + 1
            val g = fn k => k - 1
            in (f,g) end
  in #1 xy 4 end


  val f = ``Fn (SOME 800) NONE 1 (Op Add [Var 0; Op (Const 1) []])``
  val g = ``Fn (SOME 900) NONE 1 (Op Sub [Var 0; Op (Const 1) []])``
  val xy = ``Let [^f;^g] (Op (Cons 0) [Var 0; Var 1])``
  val app = ``Let [^xy] (App NONE (Op El [Var 0; Op (Const 0) []]) [Op (Const 4) []])``
  val ev = EVAL ``compile T ^app``

*)

val _ = export_theory();
