open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfAppTheory cfTheory

open cmlPEGTheory gramTheory cmlPtreeConversionTheory
     grammarTheory lexer_funTheory lexer_implTheory

fun parse nt sem s = let
    val s_t = stringSyntax.lift_string bool s
    val t = (rhs o concl o EVAL) ``lexer_fun ^s_t``
    val ttoks = rhs (concl (EVAL ``MAP TK ^t``))
    val evalth = EVAL ``peg_exec cmlPEG (nt (mkNT ^nt) I) ^t [] done failed``
    val r = rhs (concl evalth)

    fun diag(s,t) = let
        fun pp pps (s,t) =
          (PP.begin_block pps PP.CONSISTENT 0;
           PP.add_string pps s;
           PP.add_break pps (1,2);
           pp_term pps t;
           PP.end_block pps)
    in
        print (PP.pp_to_string 79 pp (s,t) ^ "\n")
    end
    fun die (s,t) = (diag (s,t); raise Fail "Failed")
in
  if same_const (rator r) ``Result`` then
    if optionSyntax.is_some (rand r) then let
      val pair = rand (rand r)
      val remaining_input = pair |> rator |> rand
      val res = pair |> rand |> rator |> rand
    in
      if listSyntax.is_nil remaining_input then let
        (* val _ = diag ("EVAL to: ", res) *)
        val fringe_th = EVAL ``ptree_fringe ^res``
        val fringe_t = rhs (concl fringe_th)
        (* val _ = diag ("fringe = ", fringe_t) *)
      in
        if aconv fringe_t ttoks then let
          val ptree_res =
              case Lib.total mk_comb(sem,res) of
                  NONE => optionSyntax.mk_none bool
                | SOME t =>
                  let
                    val rt = rhs (concl (EVAL t))
                  in
                    if optionSyntax.is_some rt then
                      rand rt
                    else die ("Sem. failure", rt)
                  end
          (* val _ = diag ("Semantics ("^term_to_string sem^") to ", ptree_res) *)
        in
          ptree_res
        end
        else die ("Fringe not preserved!", ttoks)
      end
      else die ("REMANING INPUT:", pair)
    end
    else die ("FAILED:", r)
  else die ("NO RESULT:", r)
end

fun pick_name str =
  if str = "<" then "lt" else
  if str = ">" then "gt" else
  if str = "<=" then "le" else
  if str = ">=" then "ge" else
  if str = "=" then "eq" else
  if str = "~" then "uminus" else
  if str = "+" then "plus" else
  if str = "-" then "minus" else
  if str = "*" then "times" else
  if str = "!" then "deref" else
  if str = ":=" then "assign" else str (* name is fine *)

(*------------------------------------------------------------------*)

fun naryFun_repack_conv tm =
  let
    val (base_case, rec_case) = CONJ_PAIR (GSYM naryFun_def)
    val Fun_pat = ``Fun _ _``
    val conv =
        if can (match_term Fun_pat) tm then
          (RAND_CONV naryFun_repack_conv) THENC
          (REWR_CONV rec_case)
        else
          REWR_CONV base_case
  in conv tm
  end

val naryClosure_repack_conv =
  (RAND_CONV naryFun_repack_conv) THENC (REWR_CONV (GSYM naryClosure_def))

fun dest_naryFun tm =
  case strip_comb tm of
      (f, [args, body]) =>
      if #Name (dest_thy_const f) <> "naryFun" then fail ()
      else (args, body)
    | _ => fail ()

fun EVAL_PAT pat tm =
  if can (match_term pat) tm then
    EVAL tm
  else
    NO_CONV tm

fun EVAL_PAT_TAC pat =
  CONV_TAC (DEPTH_CONV (EVAL_PAT pat))

fun compose_n n conv =
  if n <= 0 then I else conv o (compose_n (n-1) conv)

fun hnf_conv tm =
    let val (f, xs) = strip_comb tm in
      if is_abs f then
        ((compose_n (length xs - 1) RATOR_CONV) BETA_CONV
         THENC hnf_conv) tm
      else
        REFL tm
    end

val hnf =
    TRY (CONV_TAC hnf_conv)

fun conv_head thm (g as (_, w)) =
  let val (_, args) = strip_comb w
      val (_, args') = strip_comb ((lhs o concl) (SPEC_ALL thm))
      val extra_args_nb = (length args) - (length args')
      val tac =
          if extra_args_nb < 0 then FAIL_TAC "conv_head"
          else CONV_TAC ((compose_n extra_args_nb RATOR_CONV) (REWR_CONV thm))
  in tac g
  end

fun cf_get_precondition t = rand (rator t)

(* xx *)
val cf_defs = [cf_let_def, cf_app_def]

val xlocal =
  FIRST [
    first_assum MATCH_ACCEPT_TAC,
    (HO_MATCH_MP_TAC app_local \\ fs [] \\ NO_TAC),
    (fs (local_is_local :: cf_defs) \\ NO_TAC)
  ] (* todo: is_local_pred *)

fun xpull_check_not_needed (g as (_, w)) =
  let val H = cf_get_precondition w
  in hpullable_rec H; ALL_TAC g end

fun xpull_core (g as (_, w)) =
  if is_sep_imp w orelse is_sep_imppost w then
    hpull g
  else
    hclean g

val xpull =
  xpull_core \\ rpt strip_tac THEN1 (TRY xlocal)

fun xtac thm =
    hnf \\ conv_head thm \\ hnf \\ irule local_elim \\ hnf

fun constant_printer s _ _ _ (ppfns:term_pp_types.ppstream_funs) _ _ _ =
  let
    open Portable term_pp_types smpp
    val str = #add_string ppfns
  in str s end

val _ = add_user_printer ("extend_env_ellipsis", ``extend_env _ _ _``,
                          constant_printer "(…)")

val _ = add_user_printer ("extend_env_rec_ellipsis",
                          ``extend_env_rec _ _ _ _ _``,
                          constant_printer "(…)")

(*------------------------------------------------------------------*)

val initial_prog = EVAL ``basis_program`` |> concl |> rand
val initial_st = ml_progLib.add_prog initial_prog pick_name ml_progLib.init_state

fun fetch_v name st =
  let val env = ml_progLib.get_env st
      val name = stringLib.fromMLstring name
      val evalth = EVAL ``lookup_var_id (Short ^name) ^env``
  in (optionLib.dest_some o rhs o concl) evalth end

fun fetch_def name st =
  let val v = fetch_v name st
      val v_defs = ml_progLib.get_v_defs st
      val opt_thm = List.find (fn thm => (lhs o concl) thm = v) v_defs
  in valOf opt_thm end

(*------------------------------------------------------------------*)

val lnull = parse ``nTopLevelDecs`` ``ptree_TopLevelDecs``
  "fun lnull l = case l of [] => true | x::xs => false"

val st = ml_progLib.add_prog lnull pick_name initial_st

val lnull_spec = Q.prove (
  `!lv a l.
     app (p:'ffi ffi_proj) ^(fetch_v "lnull" st) [lv]
       (cond (LIST_TYPE a l lv))
       (\bv. cond (BOOL (l = []) bv))`,

  rpt strip_tac \\ fs [fetch_def "lnull" st] \\
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV (GSYM letrec_pull_params_repack))) \\
  xpull \\
  irule app_rec_of_cf THEN1 EVAL_TAC \\ EVAL_PAT_TAC ``find_recfun _ _`` \\
  fs [] \\

  fs [cf_def] \\ xtac cf_mat_def \\ EVAL_PAT_TAC ``exp2v _ _`` \\ fs [] \\

  strip_tac THEN1 cheat (* nvm that for the moment *) \\
  fs [PMATCH_ROW_of_pat_def] \\
  (* - first row:
         + pat = Pcon (SOME (Short "nil") [])
         + pat_bindings pat [] = []
         therefore, insts can be replaced by ()
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(uv: unit). P []) (\_. T) (\(uv: unit). Q []))
     - second row:
         + pat = Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"]
         + pat_bindings pat [] = ["xs"; "x"]
         therefore, insts can be replaced by (vx, vxs)
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(vx, vxs). P [vx; vxs]) (\_. T) (\(vx, vxs). Q [vx; vxs]))
  *)
  cheat
)
