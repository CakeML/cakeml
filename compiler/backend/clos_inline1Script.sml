open preamble closLangTheory;

val _ = new_theory "clos_inline";

val _ = set_grammar_ancestry ["closLang", "sptree", "misc", "backend_common"]

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* This definition is written to exit as soon as possible. *)
val is_small_aux_def = tDefine "is_small_aux" `
  (is_small_aux n [] = n) /\
  (is_small_aux n (x::y::xs) =
     if n = 0n then n else
       let n = is_small_aux n [x] in if n = 0 then n else
         is_small_aux n (y::xs)) /\
  (is_small_aux n [Var t v] = n) /\
  (is_small_aux n [If t x1 x2 x3] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n [x1] in if n = 0 then 0 else
     let n = is_small_aux n [x2] in if n = 0 then 0 else
       is_small_aux n [x3]) /\
  (is_small_aux n [Let t xs x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n xs in if n = 0 then 0 else
       is_small_aux n [x2]) /\
  (is_small_aux n [Raise t x1] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n [x1]) /\
  (is_small_aux n [Handle t x1 x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n [x1] in if n = 0 then 0 else
       is_small_aux n [x2]) /\
  (is_small_aux n [Op t op xs] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n xs) /\
  (is_small_aux n [Tick t x] = is_small_aux n [x]) /\
  (is_small_aux n [Call t ticks dest xs] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n xs) /\
  (is_small_aux n [Fn t loc_opt ws_opt num_args x1] =
     let n = n - 1 in if n = 0 then 0 else
       is_small_aux n [x1]) /\
  (is_small_aux n [Letrec t loc_opt ws_opt fns x1] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n (MAP SND fns) in if n = 0 then 0 else
       is_small_aux n [x1]) /\
  (is_small_aux n [App t loc_opt x1 xs] =
     let n = n - 1 in if n = 0 then 0 else
     let n = is_small_aux n [x1] in if n = 0 then 0 else
       is_small_aux n xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp [] \\ rpt strip_tac
   \\ `exp3_size (MAP SND fns) <= exp1_size fns`
      by (Induct_on `fns` \\ simp [exp_size_def] \\ Cases \\ simp [exp_size_def])
   \\ simp []);

val is_small_def = Define `
  is_small limit e = ~(is_small_aux limit [e] = 0)`;

val is_rec_def = tDefine "is_rec" `
  (is_rec n [] = F) /\
  (is_rec n (x::y::xs) =
     if is_rec n [x] then T else
       is_rec n (y::xs)) /\
  (is_rec n [Var t v] = F) /\
  (is_rec n [If t x1 x2 x3] =
     if is_rec n [x1] then T else
     if is_rec n [x2] then T else
       is_rec n [x3]) /\
  (is_rec n [Let t xs x2] =
     if is_rec n xs then T else
       is_rec n [x2]) /\
  (is_rec n [Raise t x1] = is_rec n [x1]) /\
  (is_rec n [Handle t x1 x2] =
     if is_rec n [x1] then T else
       is_rec n [x2]) /\
  (is_rec n [Op t op xs] = is_rec n xs) /\
  (is_rec n [Tick t x] = is_rec n [x]) /\
  (is_rec n [Call t ticks dest xs] = is_rec n xs) /\
  (is_rec n [Fn t loc_opt ws_opt num_args x1] =
     is_rec n [x1]) /\
  (is_rec n [Letrec t loc_opt ws_opt fns x1] =
     if is_rec n (MAP SND fns) then T else
       is_rec n [x1]) /\
  (is_rec n [App t loc_opt x1 xs] =
     if loc_opt = SOME n then T else
     if is_rec n [x1] then T else
       is_rec n xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp [] \\ rpt strip_tac
   \\ `exp3_size (MAP SND fns) <= exp1_size fns`
      by (Induct_on `fns` \\ simp [exp_size_def] \\ Cases \\ simp [exp_size_def])
   \\ simp []);

val must_inline_def = Define `
  must_inline name limit e =
    if is_small limit e then ~(is_rec name [e]) else F`

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
    Clos num num (exp option)     (* location in code table, arity, function body *)
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
  (merge (Clos m1 n1 e1) (Clos m2 n2 e2) = if m1 = m2 ∧ n1 = n2 then Clos m2 n2 e2
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
  (merge_tup (Clos m1 n1 e1,Clos m2 n2 e2) = if m1 = m2 ∧ n1 = n2 then Clos m2 n2 e2
                                     else Other) ∧
  (merge_tup (Int i,Int j) = if i = j then Int i else Other) ∧
  (merge_tup (_,_) = Other)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> Induct_on `xs` >>
   rpt strip_tac>>
   imp_res_tac MEM_ZIP>>fs[]>>
   rw[val_approx_size_def] >> Cases_on`ys`>>fs[]>>
   first_x_assum (first_assum o mp_then.mp_then (mp_then.Pos (el 2)) mp_tac) >>
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
  (dest_Clos (Clos n a e) = SOME (n,a,e)) /\
  (dest_Clos _ = NONE)`;
val _ = export_rewrites["dest_Clos_def"];

val clos_gen_def = Define`
  (clos_gen n i [] = []) ∧
  (clos_gen n i ((a,e)::xs) = Clos (n+2*i) a NONE::clos_gen n (i+1) xs)`

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

val mk_Ticks_def = Define `
  (mk_Ticks t tc 0 e = e) /\
  (mk_Ticks t tc (SUC n) e = Tick (t§tc) (mk_Ticks t (tc + 1) n e))`;

val known_def = tDefine "known" `
  (known limit [] vs (g:val_approx spt) = ([],g)) /\
  (known limit ((x:closLang$exp)::y::xs) vs g =
     let (e1,g) = known limit [x] vs g in
     let (e2,g) = known limit (y::xs) vs g in
       (e1 ++ e2,g)) /\
  (known limit [Var t v] vs g =
     ([(Var t v,any_el v vs Other)],g)) /\
  (known limit [If t x1 x2 x3] vs g =
     let (e1,g) = known limit [x1] vs g in
     let (e2,g) = known limit [x2] vs g in
     let (e3,g) = known limit [x3] vs g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
     let (e3,a3) = HD e3 in
       ([(If t e1 e2 e3), merge a2 a3],g)) /\
  (known limit [Let t xs x2] vs g =
     let (e1,g) = known limit xs vs g in
     let (e2,g) = known limit [x2] (MAP SND e1 ++ vs) g in
     let (e2,a2) = HD e2 in
       ([(Let t (MAP FST e1) e2, a2)],g)) /\
  (known limit [Raise t x1] vs g =
     let (e1,g) = known limit [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Raise t e1,Impossible)],g)) /\
  (known limit [Tick t x1] vs g =
     let (e1,g) = known limit [x1] vs g in
     let (e1,a1) = HD e1 in
       ([(Tick t e1,a1)],g)) /\
  (known limit [Handle t x1 x2] vs g =
     let (e1,g) = known limit [x1] vs g in
     let (e2,g) = known limit [x2] (Other::vs) g in
     let (e1,a1) = HD e1 in
     let (e2,a2) = HD e2 in
       ([(Handle t e1 e2,merge a1 a2)],g)) /\
  (known limit [Call t ticks dest xs] vs g =
     let (e1,g) = known limit xs vs g in
       ([(Call t ticks dest (MAP FST e1),Other)],g)) /\
  (known limit [Op t op xs] vs g =
     let (e1,g) = known limit xs vs g in
     let (a,g) = known_op op (REVERSE (MAP SND e1)) g in
     let e =
         if isGlobal op then
           dtcase gO_destApx a of
             | gO_None => Op t op (MAP FST e1)
             | gO_Int i => Op t (Const i) []
             | gO_NullTuple tag => Op t (Cons tag) []
         else Op t op (MAP FST e1)
     in
       ([(e,a)],g)) /\
  (known limit [App t loc_opt x xs] vs g =
     let (e2,g) = known limit xs vs g in
     let (e1,g) = known limit [x] vs g in
     let (e1,a1) = HD e1 in
     let (new_loc_opt, body_opt) =
         dtcase loc_opt of
           | SOME _ => (loc_opt, NONE)
           | _ => dtcase dest_Clos a1 of
                    | NONE => (NONE, NONE)
                    | SOME (loc,arity,body_opt) => if arity = LENGTH xs
                                                   then (SOME loc, body_opt)
                                                   else (NONE, NONE)
     in
       if SND limit = 0n then ([(App t new_loc_opt e1 (MAP FST e2),Other)],g)
       else
       dtcase body_opt of 
          | NONE => ([(App t new_loc_opt e1 (MAP FST e2),Other)],g)
          | SOME body => 
             if pure x then
               let (ebody,g) = known ((I ## (\d. d - 1)) limit) [body] (MAP SND e2 ++ vs) g in
               let (ebody,abody) = HD ebody
               in
                 ([(Let (t§0) (MAP FST e2) (mk_Ticks t 1 (LENGTH xs) ebody),abody)],g)
             else
               let (ebody,g) = known ((I ## (\d. d - 1)) limit) [body] (SNOC a1 (MAP SND e2) ++ vs) g in
               let (ebody,abody) = HD ebody
               in
                 ([(Let (t§0) (SNOC e1 (MAP FST e2)) (mk_Ticks t 1 (LENGTH xs) ebody),abody)],g)) /\
  (known limit [Fn t loc_opt ws_opt num_args x1] vs g =
     let (e1,g) = known limit [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD e1 in
       ([(Fn t loc_opt NONE num_args body,
          dtcase loc_opt of
          | SOME loc => Clos loc num_args (if must_inline loc (FST limit) body
                                           then SOME body else NONE)
          | NONE => Other)],g)) /\
  (known limit [Letrec t loc_opt _ fns x1] vs g =
     let clos = dtcase loc_opt of
                   NONE => REPLICATE (LENGTH fns) Other
                |  SOME n => clos_gen n 0 fns in
     (* The following ignores SetGlobal within fns, but it shouldn't
        appear there, and missing it just means this opt will do less. *)
     let new_fns = MAP (\(num_args,x).
                    let new_vs = REPLICATE num_args Other ++ clos ++ vs in
                    let res = known limit [x] new_vs g in
                      (num_args,FST (HD (FST res)))) fns in
     let (e1,g) = known limit [x1] (clos ++ vs) g in
     let (e1,a1) = HD e1 in
       ([(Letrec t loc_opt NONE new_fns e1,a1)],g))`
 (wf_rel_tac `inv_image (measure I LEX measure I)
                        (\((_, depth_limit), xs, vs, g). (depth_limit, exp3_size xs))`
  \\ simp [] \\ rpt strip_tac
  \\ imp_res_tac exp1_size_lemma
  \\ decide_tac);


val compile_def = Define `
  compile F exp = exp /\
  compile T exp =
    let (_,g) = known (0,0) [exp] [] LN in
    let (_,g) = known (0,0) [exp] [] g in
    let (e,g) = known (100,3) [exp] [] g in
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

  TEST 0.1

  let
    val f = fn k => 1
  in f 6 end

  val t = ``SourceLoc 0 0 0 0``
  val f = ``Fn None (SOME 900) NONE 1 (Op None (Const 1) [])``
  val exp = ``Let None [^f] (App ^t NONE (Var None 0) [Op None (Const 6) []])``

  val ev = EVAL ``compile T ^exp``

  TEST 0.2

  let
    val app = fn f x => f x
    val f = fn x = x + 1
  in app f 10 end

  val t1 = ``SourceLoc 1 1 1 1``
  val t2 = ``SourceLoc 2 2 2 2``
  val app = ``Fn None (SOME 100) NONE 2 (App ^t1 NONE (Var None 0) [Var None 1])``
  val f = ``Fn None (SOME 200) NONE 1 (Op None Add [Var None 0; Op None (Const 1) []])``
  val exp = ``Let None [^app] (Let None [^f] (App ^t2 NONE (Var None 1) [Var None 0; Op None (Const 10) []]))``

  val ev = EVAL ``compile T ^exp``


  TEST 1

  let fun f x = f x in f end

  val f = ``Letrec None (SOME 200) NONE [(1,App None NONE (Var None 1) [Var None 0])] (Var None 0)``
  val ev = EVAL ``compile T ^f``


  TEST 2

  let
    val f = fn k => (get_global 60) (k + 1)
    val g = set_global 60 f
  in f 4 end

  val t1 = ``SourceLoc 1 1 1 1``
  val t2 = ``SourceLoc 2 2 2 2``
  val f = ``Fn None (SOME 900) NONE 1 (App ^t1 NONE (Op None (Global 60) []) [Op None Add [Var None 0; Op None (Const 1) []]])``
  val g = ``closLang$Op None (SetGlobal 60) [Var None 0]``
  val exp = ``Let None [^f] (Let None [^g] (App ^t2 NONE (Var None 1) [Op None (Const 4) []]))``

  val kn = EVAL ``(I ## sptree$toList) (known (100,2) [^exp] [] LN)``
  val ev = EVAL ``compile T ^exp``

  TEST 2A

  let
    val f = fn k => k + 1
    val g = set_global 60 f
  in
    get_global 60 3
  end

  val t1 = ``SourceLoc 1 1 1 1``
  val f = ``Fn None (SOME 900) NONE 1 (Op None Add [Var None 0; Op None (Const 1) []])``
  val g = ``closLang$Op None (SetGlobal 60) [Var None 0]``
  val exp = ``Let None [^f] (Let None [^g]
                (App ^t1 NONE (Op None (Global 60) []) [Op None (Const 3) []]))``

  val ev = EVAL ``compile T ^exp``


  TEST 2B (* works nicely *)

  let
    val f = fn k => k + 1
    val g = set_global 60 f
    val h = set_global 62 (get_global 60)
  in
    h
  end

  val h = ``closLang$Op None (SetGlobal 62) [Op None (Global 60) []]``
  val exp = ``Let None [^f] (Let None [^g] (Let None [^h] (Var None 0)))``

  val ev1 = EVAL ``known (0, 0) [^exp] [] LN``

  TEST 2C
    (* is ghastly; the g-map will never pick up a good value for global 62 *)

  let
    val f = fn k => k + 1
    val h = fn k => set_global 62 (get_global 60)
    val g = set_global 60 f
  in
    h 1
  end

  val h = ``Fn None (SOME 800) NONE 1
               (closLang$Op None (SetGlobal 62) [Op None (Global 60) []])``
  val exp = ``Let None [^f] (Let None [^h]
                (Let None [^g] (App None NONE (Var None 1) [Op None (Const 1) []])))``

  val ev1 = EVAL ``known (0, 0) [^exp] [] LN``
  val ev2 = EVAL ``known (0, 0) [^exp] [] ^(#2 (dest_pair (rhs (concl ev1))))``


  TEST 3

  let val xy =
        let val f = fn k => k + 1
            val g = fn k => k - 1
            in (f,g) end
  in #1 xy 4 end


  val t = ``SourceLoc 0 0 0 0``
  val f = ``Fn None (SOME 800) NONE 1 (Op None Add [Var None 0; Op None (Const 1) []])``
  val g = ``Fn None (SOME 900) NONE 1 (Op None Sub [Var None 0; Op None (Const 1) []])``
  val xy = ``Let None [^f;^g] (Op None (Cons 0) [Var None 0; Var None 1])``
  val app = ``Let None [^xy] (App ^t NONE (Op None El [Op None (Const 0) []; Var None 0]) [Op None (Const 4) []])``

  val ev = EVAL ``compile T ^app``

*)

val _ = export_theory();
