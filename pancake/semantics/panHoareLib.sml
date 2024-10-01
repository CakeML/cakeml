(*
Tactics for driving the Hoare logic.
*)

structure panHoareLib = struct

local open Parse boolLib bossLib stringLib numLib intLib
     panLangTheory panPtreeConversionTheory panSemTheory
     panHoareTheory
in end

open Term Tactic Tactical Rewrite HolKernel boolSyntax Drule bossLib



(* -------------------------------------------- *)
(* Parsing of pancake concrete programs         *)

(* largely copied from panConcreteExampleScript *)
(* -------------------------------------------- *)


fun read_file fname = let
    val s = TextIO.openIn fname
    fun get ss = case TextIO.inputLine s of
        SOME str => get (str :: ss)
      | NONE => rev ss
  in concat (get []) end

fun parse_pancake_file fname =
  let
    val str = stringLib.fromMLstring (read_file fname)
    val thm = EVAL ``parse_funs_to_ast ^str``
    val r = rhs (concl thm)
  in
    if sumSyntax.is_inl r
    then (fst (sumSyntax.dest_inl r), thm)
    else failwith ("parse_pancake_file: failed to EVAL")
  end


structure Syntax = struct

val monop = HolKernel.syntax_fns1 "panHoare"
val binop = HolKernel.syntax_fns2 "panHoare"
val triop = HolKernel.syntax_fns3 "panHoare"
val quop = HolKernel.syntax_fns4 "panHoare"



val (hoare_tm,mk_hoare,dest_hoare,is_hoare) = quop "hoare_logic"
val (rev_tm,mk_rev,dest_rev,is_rev) = binop "rev_hoare"


val hoare_context_ty = fst (dom_rng (type_of hoare_tm))


end


(* ---------------------------------- *)
(* Tactic for driving the Hoare logic *)
(* ---------------------------------- *)


(* simplifying rewrites *)

local
open panHoareTheory rich_listTheory panSemTheory alistTheory finite_mapTheory
in

val hoare_simp_rules =
    [DROP_DROP_T, FLOOKUP_UPDATE, res_var_def, FLOOKUP_FUPDATE_LIST,
        FLOOKUP_res_var,
        shape_of_def, panLangTheory.size_of_shape_def, empty_locals_def, dec_clock_def,
        Cong optionTheory.option_case_cong, Cong panSemTheory.result_case_cong,
        boolTheory.PULL_EXISTS, eval_def, panPropsTheory.exp_shape_def]

val hoare_simp_ex_rules =
    [option_case_F_exists, boolTheory.PULL_EXISTS, v_case_F_exists, wl_case_F_exists,
        to_option_bind]

val the_hoare_logic_rev_rules = CONJUNCTS hoare_logic_rev_rules

end

(* rule-driven tactic *)
val rev_hoare_step_tac = MAP_FIRST match_mp_tac
        (the_hoare_logic_rev_rules @ [panHoareTheory.eval_logic_rev])
    \\ simp hoare_simp_rules
    \\ csimp hoare_simp_ex_rules


fun goal_tac (gtac : term -> tactic) : tactic =
  (fn (asms, gl) => gtac gl (asms, gl))

fun do_hide_abbrev nm tm (asms, gl) = let
    val fvs = free_varsl (gl :: asms)
    val v = variant fvs (mk_var (nm, type_of tm))
    val v_name = fst (dest_var v)
    val v_def = variant fvs (mk_var (v_name ^ "_def", bool))
    val v_def_name = fst (dest_var v_def)
    val tac = markerLib.ABBREV_TAC (mk_eq (v, tm))
        \\ pop_assum (markerLib.hide_tac v_def_name)
  in tac (asms, gl) end

fun unabbrev_hidden_tac var = FIRST_ASSUM (fn assm => let
    val (nm, tm) = markerLib.dest_hide (concl assm)
    val (v2, _) = boolSyntax.dest_eq (rand tm)
  in if dest_var v2 = dest_var var
    then markerLib.use_hidden_assum nm
        (fn t => REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] t])
    else NO_TAC
    end)
val hide_abbrev_cont_tac = goal_tac (fn goal => let
    val err = mk_HOL_ERR "panHoare" "hide_abbrev_pre_tac"
    val (cont, _) = Syntax.dest_rev goal
    val _ = if is_var cont then raise (err "cont already a variable") else ()
  in do_hide_abbrev "cont" cont end)

val unabbr_cont_tac = goal_tac (fn goal => case strip_comb goal of
    (v, [arg]) => if is_var v
    then (unabbrev_hidden_tac v \\ BETA_TAC)
    else NO_TAC | _ => NO_TAC)

val hide_abbrev_gamma_upd_tac = goal_tac (fn goal => let
    val g_upds = TypeBase.updates_of Syntax.hoare_context_ty
        |> map (fst o strip_comb o lhs o snd o boolSyntax.strip_forall o concl)
    val g_upd = find_term (fn t => case strip_comb t of
        (f, [_, _]) => exists (same_const f) g_upds
        | _ => false) goal
  in do_hide_abbrev "Γ" g_upd end)

val acc_abbrev_gamma_tac = goal_tac (fn goal => let
    val accs = TypeBase.accessors_of Syntax.hoare_context_ty
        |> map (fst o strip_comb o lhs o snd o boolSyntax.strip_forall o concl)
    fun is_acc_app t = case strip_comb t of
        (f, [x]) => is_var x andalso exists (same_const f) accs
      | _ => false
    val ts = HolKernel.find_terms is_acc_app goal
  in if null ts then NO_TAC else FIRST_ASSUM (fn assm => let
    val (nm, tm) = markerLib.dest_hide (concl assm)
    val (v2, _) = boolSyntax.dest_eq (rand tm)
    fun matches t = aconv v2 (rand t)
  in case List.find matches ts of
    NONE => NO_TAC
  | SOME t => markerLib.use_hidden_assum nm (fn thm =>
    REWRITE_TAC [REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] thm] t])
  end) end)


val rev_hoare_tac = FIRST
  [hide_abbrev_cont_tac, unabbr_cont_tac, hide_abbrev_gamma_upd_tac,
    rev_hoare_step_tac]


(*

TODO: write a gadget that replaces the assumption "FLOOKUP locs addr = SOME (ValWord x''')"
with "FLOOKUP locs addr = SOME (ValWord addr_v)",
that is, gets rid of the tedious x'''' var names and replaces them with ones that come
from the local name

val name_flookup_tac = ASSUM_LIST (fn asms => let
    fun renames_of thm = let
        val (lhs, rhs) = dest_eq (concl thm)
        val (_, nm) = finite_mapSyntax.dest_flookup lhs
        val nm_s = stringSyntax.fromHOLstring (mlstringSyntax.dest_strlit nm)
        val xs = find_terms is_var rhs
        val ren_xs = filter (fn t => not (String.isPrefix nm_s (fst (dest_var t)))) xs
      in map (fn x => (nm_s, x)) ren_xs end
        handle HOL_ERR _ => []
    val renames = List.concat (map renames_of asms)
in FIRST_MAP (fn (nm_s,  end)

*)


end

