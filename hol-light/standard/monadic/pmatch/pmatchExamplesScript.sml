open HolKernel boolLib bossLib lcsymtacs
open ml_translatorLib ml_translatorTheory
open deepMatchesLib deepMatchesSyntax deepMatchesTheory
open holKernelTheory

val _ = new_theory"pmatchExamples"

(* stolen from deepMatchesLib.sml TODO *)

val PAIR_EQ_COLLAPSE = prove (
``(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))``,
Cases_on `x` THEN SIMP_TAC std_ss [] THEN METIS_TAC[])

val pabs_elim_ss =
    simpLib.conv_ss
      {name  = "PABS_ELIM_CONV",
       trace = 2,
       key   = SOME ([],``UNCURRY (f:'a -> 'b -> bool)``),
       conv  = K (K pairTools.PABS_ELIM_CONV)}

val elim_fst_snd_select_ss =
    simpLib.conv_ss
      {name  = "ELIM_FST_SND_SELECT_CONV",
       trace = 2,
       key   = SOME ([],``$@ (f:'a -> bool)``),
       conv  = K (K ELIM_FST_SND_SELECT_CONV)}

fun rc_ss gl = list_ss ++ simpLib.merge_ss
 (gl @
  [pabs_elim_ss,
   pairSimps.paired_forall_ss,
   pairSimps.paired_exists_ss,
   pairSimps.gen_beta_ss,
   elim_fst_snd_select_ss,
   simpLib.rewrites [
     pairTheory.EXISTS_PROD,
     pairTheory.FORALL_PROD,
     PMATCH_ROW_EQ_NONE,
     PMATCH_ROW_COND_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]])

(* -- *)

(*
pure:
  raconv_def -- a lot of redundancy in standard repr
  type_of_def -- one nested case
  dest_var,comb,abs,eq / is_eq -- catch all

monadic:
  mk_comb -- deep nesting (with string literal)
  TRANS_def -- very deep nesting
  MK_COMB_def -- very deep nesting
  ABS_def -- very deep nesting
  BETA_def -- deep nesting, catch all
  EQ_MP_def -- very deep nesting
*)

fun btotal f x = f x handle HOL_ERR _ => false

fun PMATCH_CATCHALL_INTRO_CONV tm = let
  val (x,xs) = dest_PMATCH tm
  fun no_common_el xs ys = not (exists (fn x => mem x ys) xs);
  fun is_indep_pmrach_row tm = let
    val (x,y,z) = dest_PMATCH_ROW tm
    val (x1,x2) = pairSyntax.dest_pabs x
    val (y1,y2) = pairSyntax.dest_pabs y
    val (z1,z2) = pairSyntax.dest_pabs z
    val _ = if y2 = T then () else fail()
    val _ = if y1 = x1 andalso x1 = z1 then () else fail()
    in (no_common_el (free_vars z1) (free_vars z2),(z2,tm)) end
  val ys = map is_indep_pmrach_row xs
  val fixed = filter (not o fst) ys |> map (snd o snd)
  val other = filter fst ys |> map snd
  fun insert x y [] = [(x,[y])]
    | insert x y ((k,ys)::rest) =
        if aconv k x then (k,y::ys)::rest else (k,ys)::insert x y rest
  fun partition [] res = res
    | partition ((x,y)::xs) res = partition xs (insert x y res)
  val parts = partition other []
  val parts = map (fn (x,ys) => (x,ys,length ys)) parts
  fun max [] = 0
    | max (x::xs) = let
    val m = max xs
    in if m < x then x else m end
  val m = max (map #3 parts)
  val t = #1 (first (fn (x,y,l) => m = l) parts)
  val fixed_left = filter (fn (x,y,z) => not (aconv x t)) parts |> map #2
  val v = variant (free_vars t) (mk_var("v",type_of x))
  val last_row = mk_PMATCH_ROW (mk_abs(v,v),mk_abs(v,T),mk_abs(v,t))
  val l = listSyntax.mk_list(fixed @ flatten fixed_left @ [last_row],
                             type_of last_row)
  val l1 = listSyntax.mk_list(xs,type_of last_row)
  val gv = genvar (type_of x)
  val goal = mk_forall(gv,mk_eq(mk_PMATCH gv l1,mk_PMATCH gv l))
  (* set_goal ([],goal) *)
  val lemma = prove(goal,
    gen_tac >>
    SIMP_TAC (rc_ss[]) [PMATCH_EVAL, PMATCH_ROW_COND_def] >>
    BasicProvers.EVERY_CASE_TAC >>
    FULL_SIMP_TAC (rc_ss[]) [] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    FULL_SIMP_TAC (rc_ss[]) [] >>
    fs[] >> rw[] >>
    spose_not_then strip_assume_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    FULL_SIMP_TAC (rc_ss[]) [] >>
    rpt (
      first_assum(fn th =>
        let val t = find_term(btotal(is_var o rhs o dest_neg))(concl th) in
          Cases_on `^(rhs(dest_neg t))` >> fs[]
        end)))
  in SPEC x lemma end

val raconv_PMATCH = save_thm("raconv_PMATCH",
  CONV_RULE
  ((funpow 3 (RAND_CONV o funpow 2 ABS_CONV)
     (PMATCH_INTRO_CONV THENC PMATCH_CATCHALL_INTRO_CONV)
    THENC PMATCH_INTRO_CONV THENC PMATCH_CATCHALL_INTRO_CONV)
   |> (STRIP_QUANT_CONV o RAND_CONV))
  raconv_def)

(* PMATCH_INTRO_CONV fails because it doesn't know about :term *)
val t = dest_var_def |> SPEC_ALL |> concl |> rhs
val t' = convert_case t
val go = mk_eq(t,t')
(* set_goal([],go) *)
val th = prove(go,
  rpt(CASE_TAC >> FULL_SIMP_TAC (rc_ss[]) [PMATCH_EVAL, PMATCH_ROW_COND_def]) >>
  fs[])

val dest_var_PMATCH = save_thm("dest_var_PMATCH",
  CONV_RULE
    ((REWR_CONV th THENC PMATCH_CATCHALL_INTRO_CONV)
     |> (STRIP_QUANT_CONV o RAND_CONV))
  dest_var_def)

(*
val type_of_PMATCH = save_thm("type_of_PMATCH",
  type_of_def
*)

val _ = export_theory()
