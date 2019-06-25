(*
  This complicated compiler phase tracks where closure values flow
  in a program. It attempts to annotate function applications with the
  (numeric) names of the called closures (annotations lead to better
  code in clos_to_bvl). If the code for the applied closure is
  statically known and small enough, then this compiler phase can
  inline the body of the called closure. The function inlining is
  recurisve and controlled using configurable parameters.
*)
open preamble closLangTheory;
open db_varsTheory clos_ticksTheory clos_letopTheory clos_fvsTheory;

val _ = new_theory "clos_known";

(* val _ = set_grammar_ancestry ["closLang", "sptree", "misc", "backend_common"] *)

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* This definition is written to short-circuit,
   i.e. exit as soon as possible. *)
val get_size_sc_aux_def = tDefine "get_size_sc_aux" `
  (get_size_sc_aux n [] = n) /\
  (get_size_sc_aux n (x::y::xs) =
     if n = 0n then n else
       let n = get_size_sc_aux n [x] in if n = 0 then n else
         get_size_sc_aux n (y::xs)) /\
  (get_size_sc_aux n [Var t v] = n - 1) /\
  (get_size_sc_aux n [If t x1 x2 x3] =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
     let n = get_size_sc_aux n [x2] in if n = 0 then 0 else
       get_size_sc_aux n [x3]) /\
  (get_size_sc_aux n [Let t xs x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux n xs in if n = 0 then 0 else
       get_size_sc_aux n [x2]) /\
  (get_size_sc_aux n [Raise t x1] =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux n [x1]) /\
  (get_size_sc_aux n [Handle t x1 x2] =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
       get_size_sc_aux n [x2]) /\
  (get_size_sc_aux n [Op t op xs] =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux n xs) /\
  (get_size_sc_aux n [Tick t x] = get_size_sc_aux n [x]) /\
  (get_size_sc_aux n [Call t ticks dest xs] =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux n xs) /\
  (get_size_sc_aux n [Fn t loc_opt ws_opt num_args x1] =
     let n = n - 1 in if n = 0 then 0 else
       get_size_sc_aux n [x1]) /\
  (get_size_sc_aux n [Letrec t loc_opt ws_opt fns x1] =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux n (MAP SND fns) in if n = 0 then 0 else
       get_size_sc_aux n [x1]) /\
  (get_size_sc_aux n [App t loc_opt x1 xs] =
     let n = n - 1 in if n = 0 then 0 else
     let n = get_size_sc_aux n [x1] in if n = 0 then 0 else
       get_size_sc_aux n xs)`
  (WF_REL_TAC `measure (exp3_size o SND)`
   \\ simp [] \\ rpt strip_tac
   \\ `exp3_size (MAP SND fns) <= exp1_size fns`
      by (Induct_on `fns` \\ simp [exp_size_def] \\ Cases \\ simp [exp_size_def])
   \\ simp []);

val get_size_sc_def = Define `
  get_size_sc limit e =
    let n = get_size_sc_aux (limit + 1) [e] in
      if n = 0 then NONE else SOME (limit + 1 - n)
`;

val get_size_aux_def = tDefine "get_size_aux" `
  (get_size_aux [] = 0n) /\
  (get_size_aux (x::y::xs) =
     get_size_aux [x] + get_size_aux (y::xs)) /\
  (get_size_aux [Var t v] = 1) /\
  (get_size_aux [If t x1 x2 x3] =
     1 + get_size_aux [x1] + get_size_aux [x2] + get_size_aux [x3]) /\
  (get_size_aux [Let t xs x2] =
     1 + get_size_aux xs + get_size_aux [x2]) /\
  (get_size_aux [Raise t x1] =
     1 + get_size_aux [x1]) /\
  (get_size_aux [Handle t x1 x2] =
     1 + get_size_aux [x1] + get_size_aux [x2]) /\
  (get_size_aux [Op t op xs] =
     1 + get_size_aux xs) /\
  (get_size_aux [Tick t x] =
     get_size_aux [x]) /\
  (get_size_aux [Call t ticks dest xs] =
     1 + get_size_aux xs) /\
  (get_size_aux [Fn t loc_opt ws_opt num_args x1] =
     1 + get_size_aux [x1]) /\
  (get_size_aux [Letrec t loc_opt ws_opt fns x1] =
     1 + get_size_aux (MAP SND fns) + get_size_aux [x1]) /\
  (get_size_aux [App t loc_opt x1 xs] =
     1 + get_size_aux [x1] + get_size_aux xs)`
  (WF_REL_TAC `measure exp3_size`
   \\ simp [] \\ rpt strip_tac
   \\ `exp3_size (MAP SND fns) <= exp1_size fns`
      by (Induct_on `fns` \\ simp [exp_size_def] \\ Cases \\ simp [exp_size_def])
   \\ simp []);

val get_size_aux_ind = theorem "get_size_aux_ind";

val get_size_def = Define `get_size e = get_size_aux [e]`;

Theorem get_size_sc_aux_correct:
   !xs limit n. get_size_sc_aux limit xs = limit - get_size_aux xs
Proof
  `!xs limit n. get_size_sc_aux limit xs = n ==> n = limit - get_size_aux xs` suffices_by metis_tac []
  \\ ho_match_mp_tac get_size_aux_ind
  \\ simp [get_size_sc_aux_def, get_size_aux_def]
QED

Theorem get_size_sc_SOME:
   !exp limit n. get_size_sc limit exp = SOME n ==> get_size exp = n
Proof
  simp [get_size_sc_def, get_size_def, get_size_sc_aux_correct]
QED

val free_def = tDefine "free" `
  (free [] = ([],Empty)) /\
  (free ((x:closLang$exp)::y::xs) =
     let (c1,l1) = free [x] in
     let (c2,l2) = free (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (free [Var t v] = ([Var t v], Var v)) /\
  (free [If t x1 x2 x3] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
     let (c3,l3) = free [x3] in
       ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (free [Let t xs x2] =
     let (c1,l1) = free xs in
     let (c2,l2) = free [x2] in
       ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (free [Raise t x1] =
     let (c1,l1) = free [x1] in
       ([Raise t (HD c1)],l1)) /\
  (free [Tick t x1] =
     let (c1,l1) = free [x1] in
       ([Tick t (HD c1)],l1)) /\
  (free [Op t op xs] =
     let (c1,l1) = free xs in
       ([Op t op c1],l1)) /\
  (free [App t loc_opt x1 xs2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free xs2 in
       ([App t loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (free [Fn t loc _ num_args x1] =
     let (c1,l1) = free [x1] in
     let l2 = Shift num_args l1 in
       ([Fn t loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
  (free [Letrec t loc _ fns x1] =
     let m = LENGTH fns in
     let res = MAP (\(n,x). let (c,l) = free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
     let (c2,l2) = free [x1] in
       ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (free [Handle t x1 x2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
       ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (free [Call t ticks dest xs] =
     let (c1,l1) = free xs in
       ([Call t ticks dest c1],l1))`
 (WF_REL_TAC `measure exp3_size`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val free_ind = theorem "free_ind";

(*
val free_LENGTH_LEMMA = Q.prove(
  `!xs. (case free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

Theorem free_LENGTH:
   !xs ys l. (free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC free_LENGTH_LEMMA \\ fs []
QED

Theorem free_SING:
   (free [x] = (ys,l)) ==> ?y. ys = [y]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_FST_free:
   LENGTH (FST (free fns)) = LENGTH fns
Proof
  Cases_on `free fns` \\ fs [] \\ IMP_RES_TAC free_LENGTH
QED

Theorem HD_FST_free:
   [HD (FST (free [x1]))] = FST (free [x1])
Proof
  Cases_on `free [x1]` \\ fs []
  \\ imp_res_tac free_SING \\ fs[]
QED

Theorem free_CONS:
   FST (free (x::xs)) = HD (FST (free [x])) :: FST (free xs)
Proof
  Cases_on `xs` \\ fs [free_def,SING_HD,LENGTH_FST_free,LET_DEF]
  \\ Cases_on `free [x]` \\ fs []
  \\ Cases_on `free (h::t)` \\ fs [SING_HD]
\\ IMP_RES_TAC free_SING \\ fs []
QED
*)

val closed_def = Define `
  closed x = isEmpty (db_to_set (SND (free [x])))`

val contains_closures_def = tDefine "contains_closures" `
  (contains_closures [] = F) /\
  (contains_closures (x::y::xs) =
    if contains_closures [x] then T else
      contains_closures (y::xs)) /\
  (contains_closures [Var t v] = F) /\
  (contains_closures [If t x1 x2 x3] =
     if contains_closures [x1] then T else
     if contains_closures [x2] then T else
       contains_closures [x3]) /\
  (contains_closures [Let t xs x2] =
     if contains_closures xs then T else
       contains_closures [x2]) /\
  (contains_closures [Raise t x1] = contains_closures [x1]) /\
  (contains_closures [Handle t x1 x2] =
     if contains_closures [x1] then T else
       contains_closures [x2]) /\
  (contains_closures [Op t op xs] = contains_closures xs) /\
  (contains_closures [Tick t x] = contains_closures [x]) /\
  (contains_closures [Call t ticks dest xs] = contains_closures xs) /\
  (contains_closures [Fn t loc_opt ws_opt num_args x1] = T) /\
  (contains_closures [Letrec t loc_opt ws_opt fns x1] = T) /\
  (contains_closures [App t loc_opt x1 xs] =
     if contains_closures [x1] then T else
       contains_closures xs)`
  (wf_rel_tac `measure exp3_size`);

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
    ClosNoInline num num        (* location in code table, arity *)
  | Clos num num exp num        (* loc, arity, body, body size *)
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
  (merge (ClosNoInline m1 n1) (ClosNoInline m2 n2) =
     if m1 = m2 ∧ n1 = n2
       then ClosNoInline m1 n1 else Other) ∧
  (merge (Clos m1 n1 e1 s1) (Clos m2 n2 e2 s2) =
     if m1 = m2 ∧ n1 = n2 /\ e1 = e2 /\ s1 = s2
       then Clos m1 n1 e1 s1 else Other) ∧
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
    save_thm("merge_def[simp,compute]",
             SIMP_RULE (bool_ss ++ ETA_ss) [] merge_def)

(* Avoid MAP2 *)
val merge_tup_def = tDefine "merge_tup" `
  (merge_tup (Impossible,y) = y) ∧
  (merge_tup (x,Impossible) = x) ∧
  (merge_tup (Tuple tg1 xs,Tuple tg2 ys) =
     if LENGTH xs = LENGTH ys ∧ tg1 = tg2 then
       Tuple tg1 (MAP merge_tup (ZIP(xs,ys)))
     else Other) ∧
  (merge_tup (ClosNoInline m1 n1,ClosNoInline m2 n2) =
     if m1 = m2 ∧ n1 = n2
       then ClosNoInline m1 n1 else Other) ∧
  (merge_tup (Clos m1 n1 e1 s1,Clos m2 n2 e2 s2) =
     if m1 = m2 ∧ n1 = n2 /\ e1 = e2 /\ s1 = s2
       then Clos m1 n1 e1 s1 else Other) ∧
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
Theorem merge_tup_pmatch:
  !tup.
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
    | _ => Other
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[merge_tup_def] >> metis_tac []
QED
 *)

Theorem merge_alt:
    ∀x y.merge x y = merge_tup (x,y)
Proof
  HO_MATCH_MP_TAC (fetch "-" "merge_ind")>>rw[merge_tup_def,MAP2_MAP]>>
  match_mp_tac LIST_EQ>>rw[EL_ZIP,EL_MAP]>>
  first_x_assum match_mp_tac>>metis_tac[MEM_EL]
QED

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
       | NONE => (Other, insert n a g)
       | SOME other => (Other, insert n (merge other a) g)) /\
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

Theorem known_op_pmatch:
  !op as g.
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
       dtcase lookup n g of
       | NONE => (Other, insert n a g)
       | SOME other => (Other, insert n (merge other a) g))
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
  | _ => (Other,g)
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[known_op_def]
QED

val EL_MEM_LEMMA = Q.prove(
  `!xs i x. i < LENGTH xs /\ (x = EL i xs) ==> MEM x xs`,
  Induct \\ fs [] \\ REPEAT STRIP_TAC \\ Cases_on `i` \\ fs []);

val clos_approx_def = Define `
  clos_approx max_size loc num_args body =
    dtcase get_size_sc max_size body of
      | NONE => ClosNoInline loc num_args
      | SOME body_size => Clos loc num_args body body_size
`;

val clos_gen_noinline_def = Define`
  (clos_gen_noinline n i [] = []) /\
  (clos_gen_noinline n i ((a,e)::xs) =
    ClosNoInline (n+2*i) a::clos_gen_noinline n (i+1) xs)`;

val _ = Datatype `globalOpt = gO_Int int | gO_NullTuple num | gO_None`

val isGlobal_def = Define`
  (isGlobal (Global _) ⇔ T) ∧
  (isGlobal _ ⇔ F)`;

Theorem isGlobal_pmatch:
  !op.
  isGlobal op =
  case op of
    Global _ => T
    | _ => F
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[isGlobal_def]
QED

val gO_destApx_def = Define`
  (gO_destApx (Int i) = gO_Int i) ∧
  (gO_destApx (Tuple tag args) = if NULL args then gO_NullTuple tag
                                 else gO_None) ∧
  (gO_destApx _ = gO_None)`;

val mk_Ticks_def = tDefine "mk_Ticks" `
  mk_Ticks t tc n e =
    if n = 0n then e else mk_Ticks t (tc + 1) (n - 1) (Tick (t§tc) e)`
  (wf_rel_tac `measure (FST o SND o SND)`);

val _ = Datatype `
  inliningDecision = inlD_Nothing
                   | inlD_Annotate num
                   | inlD_LetInline exp
`;

val _ = Datatype`
  config = <| inline_max_body_size : num
            ; inline_factor : num (* As in 'Inline expansion: when and how?' by Manuel Serrano *)
            ; initial_inline_factor : num
            ; val_approx_spt : val_approx spt (* TODO: this could replace the explicit g argument in known_def *)
            |>`;

val default_inline_factor_def = Define`default_inline_factor = 8n`;
val default_max_body_size_def = Define`
  default_max_body_size max_app inline_factor = (max_app + 1n) * inline_factor`;

val mk_config_def = Define`
  mk_config max_body_size inline_factor = <|
      inline_max_body_size := max_body_size
    ; inline_factor := inline_factor
    ; initial_inline_factor := inline_factor
    ; val_approx_spt := LN
  |>`;

val default_config_def = Define`
  default_config max_app = mk_config (default_max_body_size max_app default_inline_factor) default_inline_factor`;

val dec_inline_factor_def = Define `
  dec_inline_factor c = c with inline_factor := c.inline_factor DIV 2`;

val reset_inline_factor_def = Define `
  reset_inline_factor c = c with inline_factor := c.initial_inline_factor`;

val decide_inline_def = Define `
  decide_inline c fapx app_lopt app_arity =
    dtcase fapx of
      | ClosNoInline loc arity =>
          if app_lopt = NONE /\ app_arity = arity
            then inlD_Annotate loc
            else inlD_Nothing
      | Clos loc arity body body_size =>
          if app_lopt = NONE /\ app_arity = arity then
            (if body_size < c.inline_factor * (1 + app_arity) /\
                ~contains_closures [body] /\
                closed (Fn None NONE NONE app_arity body)
                (* Consider moving these checks to the point where Clos approximations
                   are created, and bake them into the val_approx_val relation. *)
               then inlD_LetInline body
               else inlD_Annotate loc)
          else inlD_Nothing
      | _ => inlD_Nothing
`;

Theorem decide_inline_LetInline:
   !c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==> 0 < c.inline_factor
Proof
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]
  \\ spose_not_then assume_tac \\ fs []
QED

val known_def = tDefine "known" `
  (known c [] vs (g:val_approx spt) = ([],g)) /\
  (known c ((x:closLang$exp)::y::xs) vs g =
     let (eas1,g) = known c [x] vs g in
     let (eas2,g) = known c (y::xs) vs g in
       (eas1 ++ eas2,g)) /\
  (known c [Var t v] vs g =
     ([(Var t v,any_el v vs Other)],g)) /\
  (known c [If t x1 x2 x3] vs g =
     let (ea1,g) = known c [x1] vs g in
     let (ea2,g) = known c [x2] vs g in
     let (ea3,g) = known c [x3] vs g in
     let (e1,a1) = HD ea1 in
     let (e2,a2) = HD ea2 in
     let (e3,a3) = HD ea3 in
       ([(If t e1 e2 e3), merge a2 a3],g)) /\
  (known c [Let t xs x2] vs g =
     let (ea1,g) = known c xs vs g in
     let (ea2,g) = known c [x2] (MAP SND ea1 ++ vs) g in
     let (e2,a2) = HD ea2 in
       ([(Let t (MAP FST ea1) e2, a2)],g)) /\
  (known c [Raise t x1] vs g =
     let (ea1,g) = known c [x1] vs g in
     let (e1,a1) = HD ea1 in
       ([(Raise t e1,Impossible)],g)) /\
  (known c [Tick t x1] vs g =
     let (ea1,g) = known c [x1] vs g in
     let (e1,a1) = HD ea1 in
       ([(Tick t e1,a1)],g)) /\
  (known c [Handle t x1 x2] vs g =
     let (ea1,g) = known c [x1] vs g in
     let (ea2,g) = known c [x2] (Other::vs) g in
     let (e1,a1) = HD ea1 in
     let (e2,a2) = HD ea2 in
       ([(Handle t e1 e2,merge a1 a2)],g)) /\
  (known c [Call t ticks dest xs] vs g =
     let (ea1,g) = known c xs vs g in
       ([(Call t ticks dest (MAP FST ea1),Other)],g)) /\
  (known c [Op t op xs] vs g =
     let (ea1,g) = known c xs vs g in
     let (a,g) = known_op op (REVERSE (MAP SND ea1)) g in
     let e =
         (if isGlobal op then
           dtcase gO_destApx a of
             | gO_None => Op t op
             | gO_Int i => Op t (Const i)
             | gO_NullTuple tag => Op t (Cons tag)
          else Op t op) (MAP FST ea1)
     in
       ([(e,a)],g)) /\
  (known c [App t loc_opt x xs] vs g =
     let (ea2,g) = known c xs vs g in
     let (ea1,g) = known c [x] vs g in
     let (e1,a1) = HD ea1
     in
       dtcase decide_inline c a1 loc_opt (LENGTH xs) of
         | inlD_Nothing => ([(App t loc_opt e1 (MAP FST ea2), Other)], g)
         | inlD_Annotate new_loc => ([(App t (SOME new_loc) e1 (MAP FST ea2), Other)], g)
         | inlD_LetInline body =>
             let (eabody,_) = known (dec_inline_factor c) [body] (MAP SND ea2) g in
             let (ebody, abody) = HD eabody in
               if pure x then
                 (* We don't have to evaluate x *)
                 ([(Let (t§0) (MAP FST ea2)
                              (mk_Ticks t 1 (LENGTH xs) ebody), abody)], g)
               else
                 (* We need to evaluate x for its side-effects,
                    but we must do so after evaluating the args. *)
                 ([(Let (t§0) (SNOC e1 (MAP FST ea2))
                              (mk_Ticks t 1 (LENGTH xs) ebody), abody)], g)) /\
  (known c [Fn t loc_opt ws_opt num_args x1] vs g =
     let (ea1,g) = known c [x1] (REPLICATE num_args Other ++ vs) g in
     let (body,a1) = HD ea1 in
       ([(Fn t loc_opt NONE num_args body,
          dtcase loc_opt of
            | SOME loc => clos_approx c.inline_max_body_size loc num_args x1
            | NONE => Other)], g)) /\
  (known c [Letrec t loc_opt _ fns x1] vs g =
     let clos = dtcase loc_opt of
                   NONE => REPLICATE (LENGTH fns) Other
                |  SOME loc => clos_gen_noinline loc 0 fns in
     (* The following ignores SetGlobal within fns, but it shouldn't
        appear there, and missing it just means this opt will do less. *)
     let new_fns = MAP (\(num_args,x).
                    let new_vs = REPLICATE num_args Other ++ clos ++ vs in
                    let res = known c [x] new_vs g in
                      (num_args,FST (HD (FST res)))) fns in
     let (ea1,g) = known c [x1] (clos ++ vs) g in
     let (e1,a1) = HD ea1 in
       ([(Letrec t loc_opt NONE new_fns e1,a1)],g))`
 (wf_rel_tac `inv_image (measure I LEX measure I)
                        (\(c, xs, vs, g). (c.inline_factor, exp3_size xs))`
  \\ simp [dec_inline_factor_def] \\ rpt strip_tac
  THEN1 (imp_res_tac exp1_size_lemma \\ decide_tac)
  \\ imp_res_tac decide_inline_LetInline \\ fs []);

val known_ind = theorem "known_ind";

Theorem known_LENGTH:
   ∀limit es vs g. LENGTH (FST (known limit es vs g)) = LENGTH es
Proof
  recInduct known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >>
  rw [] >> CASE_TAC >> CASE_TAC >> fs [] >>
  rpt (pairarg_tac >> fs [])
QED

Theorem known_LENGTH_EQ_E:
   known limit es vs g0 = (alist, g) ⇒ LENGTH alist = LENGTH es
Proof
  metis_tac[FST, known_LENGTH]
QED

Theorem known_sing:
   ∀limit e vs g. ∃e' a g'. known limit [e] vs g = ([(e',a)], g')
Proof
  rpt strip_tac >> Cases_on `known limit [e] vs g` >>
  rename1 `known limit [e] vs g = (res,g')` >>
  qspecl_then [`limit`, `[e]`, `vs`, `g`] mp_tac known_LENGTH >> simp[] >>
  Cases_on `res` >> simp[LENGTH_NIL] >> metis_tac[pair_CASES]
QED

Theorem known_sing_EQ_E:
   ∀limit e vs g0 all g. known limit [e] vs g0 = (all, g) ⇒ ∃e' apx. all = [(e',apx)]
Proof
  metis_tac[PAIR_EQ, known_sing]
QED

val compile_def = Define `
  compile NONE exps = (NONE, exps) /\
  compile (SOME c) exps =
    let exps = clos_fvs$compile exps in
    let (es, g) = known c exps [] LN in
    let es1 = remove_ticks (MAP FST es) in
    let es2 = let_op es1 in
      (SOME (c with val_approx_spt := g), es2)`;

(*

(* Trace starting points *)
val t0 = ``SourceLoc 0 0 0 0``;
val t1 = ``SourceLoc 1 1 1 1``;

(* The numerical constant 1 *)
val const1 = ``Op None (Const 1) []``;
val const2 = ``Op None (Const 2) []``;


(* fn f x => f x *)
val apply = ``Fn None (SOME 0) NONE 2 (App ^t0 NONE (Var None 0) [Var None 1])``;

(* fn x => x + 1 *)
val succ = ``Fn None (SOME 2) NONE 1 (Op None Add [Var None 0; ^const1])``;

(* -------------------------------*)

(* (fn f x => f x) (fn x => x + 1) 2 *)
val example_direct = ``App ^t1 NONE ^apply [^succ; ^const2]``;

val inline_direct = ``clos_known$compile T ^example_direct``;
EVAL inline_direct;

val exp = ``Let None [^const1; ^const2] (Op None Add [Var None 0; Var None 1])``

EVAL ``clos_letop$let_op [^exp]``;

(*-------------------------------*)

(*
let apply = fn f x => f x
    succ = fn x => x + 1
in
  apply succ 1
end
*)
val example_local = ``Let None [^apply; ^succ] (App ^t1 NONE (Var None 0) [Var None 1; ^const1])``;
val inlined_local = EVAL ``clos_known$compile T ^example_local``;

val inline_local = ``clos_known$compile T ^example_local``;
EVAL inline_local;

(*-------------------------------*)

(* fun apply <f,x> = f x *)
val sg_apply = ``Op None (SetGlobal 0) [^apply]``;
val g_apply = ``Op None (Global 0) []``;

(* fun succ <x> = x + 1 *)
val sg_succ = ``Op None (SetGlobal 1) [^succ]``;
val g_succ = ``Op None (Global 1) []``;

(*
let _ = SetGlobal 0 (fn f x => f x)
    _ = SetGlobal 1 (fn x => x + 1)
in
  (Global 0) (Global 1) 1
end
*)
val example_global = ``Let None [^sg_apply; ^sg_succ] (App ^t1 NONE ^g_apply [^g_succ; ^const1])``;

val inline_global = ``clos_known$compile T ^example_global``;

EVAL inline_global;

EVAL ``known (100,0) [^apply] [] LN``;
EVAL ``known (100,0) [^succ] [] LN``;

EVAL ``known (0,0) [^example_global] [] LN``;

EVAL ``
    let exp = ^example_local in
    let (_,g1) = known (0,0) [exp] [] LN in
    let (e1,g1') = known (0,0) [exp] [] g1 in
    let (e2,g2) = known (0,0) [FST (HD e1)] [] LN in
    (e1, e2, g1, g1')
``


    let (e2,_) = known (100,2) [FST (HD e1)] [] g2 in
      FST (HD e2)

*)

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
