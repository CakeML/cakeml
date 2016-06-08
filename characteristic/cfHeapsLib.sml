structure cfHeapsLib :> cfHeapsLib =
struct

open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv
open cfHeapsTheory

(** Prove an "easy" goal about sets, involving UNION, DISJOINT,... Useful after
    unfolding the definitions of heap predicates. *)

val SPLIT_TAC = fs [SPLIT_def,SPLIT3_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,
                    IN_INSERT,UNION_DEF,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY,
                    IN_DEF,IN_UNION,IN_INTER,IN_DIFF]
                \\ metis_tac []

(** Normalization of STAR *)

val rew_heap_thms =
  [AC STAR_COMM STAR_ASSOC, SEP_CLAUSES, STARPOST_emp,
   SEP_IMPPOST_def, STARPOST_def, cond_eq_def]

val rew_heap = full_simp_tac bool_ss rew_heap_thms
val rew_heap_AC = full_simp_tac bool_ss [AC STAR_COMM STAR_ASSOC]

(** hpull *)

fun dest_sep_imp tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMP_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_cell tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) cell_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun SEP_IMP_conv convl convr t =
  let val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
      val rew_t = MATCH_MP (MATCH_MP SEP_IMP_rew (convl l)) (convr r)
  in REWR_CONV rew_t t
  end

fun find_map f [] = NONE
  | find_map f (x :: xs) =
    (case f x of
         NONE => find_map f xs
       | SOME y => SOME y)

fun rearrange_star_conv tm rest =
  let val rearranged = list_mk_star (rest @ [tm]) ``:hprop`` in
    fn t => prove (mk_eq (t, rearranged), rew_heap_AC)
  end


fun hpull_one_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
    val ls = list_dest dest_star l
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) ls in
        SEP_IMP_conv (rearrange_star_conv tm rest) REFL
      end
    fun pull tm =
      let val (c, args) = strip_comb tm in
        if is_const c andalso #Name (dest_thy_const c) = "cond" then
          SOME (
            THEN_CONSEQ_CONV
              (rearrange_conv tm)
              (CONSEQ_REWRITE_CONV ([], [hpull_prop, hpull_prop_single], [])
                CONSEQ_CONV_STRENGTHEN_direction)
          )
        else if is_const c andalso #Name (dest_thy_const c) = "SEP_EXISTS" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hpull_exists_single], [])
                CONSEQ_CONV_STRENGTHEN_direction,
              REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
            ]
          )
        else
          NONE
      end
  in
    case find_map pull ls of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hpull_setup_conv =
  (* remove ``emp`` in the left heap, pull SEP_EXISTS *)
  QCONV (SEP_IMP_conv (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES])) REFL)

fun hpull g =
  (TRY (DEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hpull_setup_conv)) \\
    REDEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hpull_one_conseq_conv)) g
  handle HOL_ERR _ => FAIL_TAC "hpull" g

(* test goals:
  g `(A * cond P * (SEP_EXISTS x. G x) * cond Q :hprop) ==>> Z`;
  g `(A * emp * cond P * (SEP_EXISTS x. emp * G x) * cond Q :hprop) ==>> Z`;
*)

(** hsimpl_cancel *)

fun hsimpl_cancel_one_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
    val ls = list_dest dest_star l
    val rs = list_dest dest_star r
    val is = intersect ls rs
    fun rearrange_conv tm1 tm2 =
      let
        val ls' = filter (fn tm' => tm' <> tm1) ls
        val rs' = filter (fn tm' => tm' <> tm2) rs
        val convl = rearrange_star_conv tm1 ls'
        val convr = rearrange_star_conv tm2 rs'
      in SEP_IMP_conv convl convr
      end
    fun cell_loc tm =
      SOME (fst (dest_cell tm)) handle _ => NONE
    fun find_matching_cells () =
      find_map (fn tm1 =>
        Option.mapPartial (fn loc =>
          find_map (fn tm2 =>
            Option.mapPartial (fn loc' =>
              if loc = loc' then SOME (tm1, tm2) else NONE
            ) (cell_loc tm2)
          ) rs
        ) (cell_loc tm1)
      ) ls

    val frame_thms = [
      SEP_IMP_FRAME,
      SEP_IMP_frame_single_l,
      SEP_IMP_frame_single_r
    ]
    val frame_cell_thms = [
      SEP_IMP_cell_frame,
      SEP_IMP_cell_frame_single_l,
      SEP_IMP_cell_frame_single_r
    ]
  in
    (case is of
         tm :: _ =>
         THEN_CONSEQ_CONV
           (rearrange_conv tm tm)
           (CONSEQ_REWRITE_CONV ([], frame_thms, [])
              CONSEQ_CONV_STRENGTHEN_direction)
       | [] =>
         case find_matching_cells () of
             SOME (tm1, tm2) =>
             THEN_CONSEQ_CONV
               (rearrange_conv tm1 tm2)
               (CONSEQ_REWRITE_CONV ([], frame_cell_thms, [])
                  CONSEQ_CONV_STRENGTHEN_direction)
           | NONE => raise UNCHANGED)
      t
  end

fun hsimpl_cancel g =
    REDEPTH_CONSEQ_CONV_TAC
      (STRENGTHEN_CONSEQ_CONV hsimpl_cancel_one_conseq_conv) g
    handle HOL_ERR _ => FAIL_TAC "hsimpl_cancel" g

(* test goal:
  g `(A:hprop * B * C * l ~~> v * D) ==>> (B * Z * l ~~> v' * Y * D * A)`;
*)

(** hsimpl *)

fun hsimpl_step_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t
    val rs = list_dest dest_star r
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) rs in
        SEP_IMP_conv REFL (rearrange_star_conv tm rest)
      end
    fun simpl tm =
      let val (c, args) = strip_comb tm in
        if is_const c andalso #Name (dest_thy_const c) = "cond" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hsimpl_prop, hsimpl_prop_single], [])
                CONSEQ_CONV_STRENGTHEN_direction
            ]
          )
        else if is_const c andalso #Name (dest_thy_const c) = "SEP_EXISTS" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hsimpl_exists_single], [])
                CONSEQ_CONV_STRENGTHEN_direction,
              REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
            ]
          )
        else
          NONE
      end
  in
    case find_map simpl rs of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hsimpl_steps =
    REDEPTH_CONSEQ_CONV_TAC
      (STRENGTHEN_CONSEQ_CONV hsimpl_step_conseq_conv)

(* test goal:
  g `Z ==>> (A * cond P * (SEP_EXISTS x. G x) * cond Q :hprop)`;
  e rew_heap;
*)

(** hsimpl *)

(* Quantifiers Heuristic parameters.
   (not sure if it is super useful as it is now)
*)
val sep_qp = combine_qps [
      instantiation_qp [
        SEP_IMP_REFL,
        hsimpl_gc
      ]
    ]

val hsimpl_setup_conv =
  SEP_IMP_conv
      (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))
      (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))

val hsimpl =
  TRY (DEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hsimpl_setup_conv)) \\
  TRY hpull \\
  QUANT_INSTANTIATE_TAC [sep_qp] \\
  rpt (hsimpl_cancel ORELSE (hsimpl_steps \\ QUANT_INSTANTIATE_TAC [sep_qp])) \\
  fs [hsimpl_gc, SEP_IMP_REFL]

(* test goal:
  g `(A:hprop * B * C * l ~~> v * l' ~~> u * D) ==>> (B * Z * l ~~> v' * l' ~~> u' * Y * cond Q * D * A)`;
*)
end
