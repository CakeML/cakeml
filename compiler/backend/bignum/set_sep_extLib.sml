(*
  General separation logic tactics.
*)
structure set_sep_extLib =
struct

local

open HolKernel Parse boolLib bossLib pairSyntax listTheory
open set_sep_extTheory

val STAR_AC_CONV = helperLib.STAR_AC_CONV
val list_mk_star = helperLib.list_mk_star

val plucki = Portable.plucki


val lib_name = "set_sep_extLib"

val ERR  = mk_HOL_ERR lib_name
val WRAP = wrap_exn lib_name

fun IS_ERR fname e =
  Feedback.top_structure_of e = lib_name andalso
  Feedback.top_function_of e = fname

in

(******************************************************************************)

val s1     = HolKernel.syntax_fns1 "set_sep"
val s2     = HolKernel.syntax_fns2 "set_sep"
val s2_ext = HolKernel.syntax_fns2 "set_sep_ext"

val (fun2set_tm, mk_fun2set, dest_fun2set, is_fun2set) = s1 "fun2set"
val (star_tm, mk_star, dest_star, is_star) = s2 "STAR"
val (sep_imp_tm, mk_sep_imp, dest_sep_imp, is_sep_imp) = s2 "SEP_IMP"
val (sep_wand_tm, mk_sep_wand, dest_sep_wand, is_sep_wand) = s2_ext "SEP_WAND"
val (ones_tm, mk_ones, dest_ones, is_ones) = s2_ext "ones"

val list_mk_star = list_mk_lbinop (curry mk_star)
val strip_star = HolKernel.strip_binop dest_star

(* Destructs “(A * ...) (fun2set (f, df))” ([“A”, ...], “f”, “df”). *)
fun dest_star_fun2set tm = let
  val (p, f2s) = dest_comb tm
  val (f, df)  = dest_pair (dest_fun2set f2s)
in (strip_star p, f, df) end

(******************************************************************************)

(* Returns the bag intersection of its arguments. *)
fun bag_inter [] _ = []
  | bag_inter (x :: xs) ys =
      case Lib.total (Lib.pluck (aconv x)) ys of
        SOME (_, ys') => x :: bag_inter xs ys'
      | NONE => bag_inter xs ys

(* Returns a bag where each element in ys is removed from xs. *)
fun bag_diff xs ys =
  foldl (fn (y, xs) => snd (Lib.pluck (aconv y) xs)) xs ys
  handle HOL_ERR _ =>
    raise ERR "bag_diff" "ys not a sub-bag of xs (up to alpha-conversion)"

(******************************************************************************)

(* Applies c to “p” in “p (fun2set _)”. *)
fun SEP_FUN2SET_CONV c tm =
  if is_comb tm andalso is_fun2set (rand tm) then RATOR_CONV c tm
  else raise ERR "SEP_FUN2SET_CONV" "not of shape “p (fun2set _)”"

(* Proves that t = t' by normalizing with c. *)
fun NORM_EQ (c: conv) t t' =
  TRANS (QCONV c t) (SYM (QCONV c t'))

(* Proves that f rearranges separating conjunctions correctly. *)
fun REARRANGE_STAR_CONV (f: term list -> term list) t =
  NORM_EQ STAR_AC_CONV t (list_mk_star (f (strip_star t)))
  handle e => raise WRAP "REARRANGE_STAR_CONV" e

(*
   Pulls the separating conjuncts tms to the right in tm.
   Fails if not every term in tms occurs as a separating conjunct in tm.
   The flag group determines whether the terms should be grouped into one term.
   Examples:
   > PULL_STAR_CONV false [“B:(α -> bool) -> bool”, “A:(α -> bool) -> bool”]
       “(A:(α -> bool) -> bool) * B * C”
   val it = ⊢ A * B * C = C * B * A: thm
   > PULL_STAR_CONV true [“B:(α -> bool) -> bool”, “A:(α -> bool) -> bool”]
       “(A:(α -> bool) -> bool) * B * C”
   val it = ⊢ A * B * C = C * (B * A)
*)
fun PULL_STAR_CONV (group: bool) to_pull tm = let
  val parts = strip_star tm
  val rest = bag_diff parts to_pull
    handle e => raise WRAP "PULL_STAR_CONV" e
  val to_pull' = if group then [list_mk_star to_pull] else to_pull
in REARRANGE_STAR_CONV (K (rest @ to_pull')) tm end

(******************************************************************************)


(* Free vars of tm not in FVs, ignoring "_"-prefixed (wildcard) vars *)
fun check_no_new_fvs err what FVs tm = let
  val tm_fvs =
    filter (not o String.isPrefix "_" o fst o dest_var) (free_vars tm)
  val new_fvs = op_set_diff aconv tm_fvs FVs
in
  if not $ null new_fvs
    then err ("Parsing " ^ what ^ " resulted in new free variables \
               \(prefix with _ to allow): " ^
              String.concatWith ", " (map term_to_string new_fvs))
end

(*
val discharge = NONE
val qa = ‘base’
val qi = ‘LENGTH xs’
val (g as (asl ,w)) = top_goal ()
val c = Context.snapshot ()
*)

(* Tries to read the location qa at qi.
   Requires a fun2set assumption mentioning ‘ones <qa>’
   If discharge is SOME tac, it tries to prove that the access is in-bounds
   with tac, failing if it doesn't succeed.
   If discharge is NONE, it generates a subgoal instead. *)
fun read_ones_at_core
  (discharge : tactic option) (qa: term quotation) (qi: term quotation) : tactic
  =
  fn (g as (asl, w)) => fn c => let
  fun err msg = raise ERR "read_ones_at_core" msg
  (* Compute free variables for parsing *)
  val fvsl = free_varsl (w::asl)
  (* Parse index as number *)
  val tmi = typed_parse_in_context_in c numSyntax.num fvsl qi
    handle HOL_ERR herr =>
      err ("failed to parse index as num: " ^ message_of herr)
  val _ = check_no_new_fvs err "the index" fvsl tmi
  (* Find (... * ...) (fun2set (_, _)) in assumptions *)
  val f2s =
    case filter (can dest_star_fun2set) asl of
      [f2s] => f2s
    | []    => err "could not find fun2set"
    | _     => err "multiple fun2set in assumptions are currently unsupported"
  val dom_ty = #1 (dom_rng $ type_of $ #2 (dest_star_fun2set f2s))
  (* Parse base as word *)
  val tma = typed_parse_in_context_in c dom_ty fvsl qa
    handle HOL_ERR herr => err (
      "failed to parse base as " ^ type_to_string dom_ty ^ ": " ^
       message_of herr)
  val _ = check_no_new_fvs err "the base" fvsl tma
  (* Find ‘ones <qa> _’ in f2s *)
  fun is_ones_tma tm = is_ones tm andalso aconv (#1 (dest_ones tm)) tma
  val ones =
    case filter is_ones_tma (#1 (dest_star_fun2set f2s)) of
      [ones] => ones
    | []     =>
        err $ concat
          ["could not find ones with base ", term_to_string tma, " in fun2set"]
    | _      =>
        err $ concat
          ["multiple matches for ones with base ", term_to_string tma,
           " are currently unsupported"]
  (* Instantiate read_el_addr *)
  val pulled =
    CONV_RULE (SEP_FUN2SET_CONV (PULL_STAR_CONV false [ones])) (ASSUME f2s)
  val read_i = SPEC tmi $ MATCH_MP read_el_addr pulled
  (* Deal with sidecondition, based on discharge *)
  val in_bounds = fst $ dest_imp_only $ concl read_i
  val full_tac =
    case discharge of
      NONE => SUBGOAL_THEN in_bounds (strip_assume_tac o MP read_i)
    | SOME tac => let
      val in_bounds_thm = TAC_PROOF_in c ((asl, in_bounds), tac)
        handle HOL_ERR _ =>
          err "failed to show that access is in-bounds. \
                   \Hint: use read_ones_at and manually prove the subgoal."
      in strip_assume_tac (MP read_i in_bounds_thm) end
in
  full_tac g c
end
handle e as HOL_ERR herr =>
  if IS_ERR "read_ones_at_core" herr
  then raise e
  else raise WRAP "read_ones_at_core" e

val read_ones_at = read_ones_at_core NONE
val read_ones_at_auto = let
  val tac = asm_simp_tac arith_ss [LENGTH, LENGTH_MAP, LENGTH_SNOC]
  in read_ones_at_core (SOME tac) end

(** (Dusty) Basement **********************************************************)

(*
   Pulls shared separating conjuncts to the right.
   Example:
   > PULL_SHARED_CONV “A * B * A ==>> A * A * C * B”
   val it = ⊢ ... ⇔ A * B * A ==>> C * (A * B * A): thm
 *)
fun PULL_SHARED_CONV tm = let
  (* Compute shared terms, accounting for duplicates *)
  val (l, r)   = dest_sep_imp tm
  val shared   = bag_inter (strip_star l) (strip_star r)
in BINOP_CONV (PULL_STAR_CONV true shared) tm end

val PULL_SHARED_TAC = CONV_TAC (CHANGED_CONV PULL_SHARED_CONV)



end
end
