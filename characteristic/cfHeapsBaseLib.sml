structure cfHeapsBaseLib :> cfHeapsBaseLib =
struct

open preamble
open set_sepTheory helperLib ConseqConv
open evarsConseqConvLib
open cfHeapsBaseTheory cfTacticsBaseLib
open cfHeapsBaseSyntax

infix 3 THEN_DCC
infix 3 ORELSE_DCC

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

val SEP_CLAUSES = LIST_CONJ [SEP_CLAUSES, STARPOST_def, cond_eq_def]

val heap_clean_conv =
  SIMP_CONV bool_ss [SEP_CLAUSES] THENC
  DEPTH_CONV (REWR_CONV SEP_F_to_cond)

(*------------------------------------------------------------------*)
(** Auxiliary functions *)

fun SEP_IMP_conv convl convr t =
  let val (l, r) = dest_sep_imp t
      val rew_t = MATCH_MP (MATCH_MP SEP_IMP_rew (convl l)) (convr r)
  in UNCHANGED_CONV (REWR_CONV rew_t) t
  end

fun rearrange_star_conv tm rest =
  let val rearranged = list_mk_star (rest @ [tm]) ``:hprop`` in
    fn t => ml_translatorLib.auto_prove "rearrange_star_conv"
              (mk_eq (t, rearranged), rew_heap_AC)
  end

(** hpullable *)

val hpullable_error = ERR "hpullable" "need to first call xpull"

(* [hpullable_rec H] raises an error if the heap predicate [H]
   contains existentials or non-empty pure facts. *)

fun hpullable_rec tm =
  let val hs = list_dest dest_star tm in
    app (fn h =>
      if is_cond h orelse is_sep_exists h then
        raise hpullable_error
      else ()) hs
  end

(* [hpullable t] applies to a term of the form [H ==>> H'], and raises
   an error if [H] contains extractible quantifiers or facts *)

fun hpullable tm =
  let val (l, _) = dest_sep_imp tm
  in hpullable_rec l end

(** hpull *)

fun hpull_one_conseq_conv_core t =
  let
    val (l, r) = dest_sep_imp t
    val ls = list_dest dest_star l
    fun rearrange_conv tm =
      let val rest = filter (not o aconv tm) ls in
        SEP_IMP_conv (rearrange_star_conv tm rest) REFL
      end
    fun pull tm =
      if is_cond tm then
        SOME (
          THEN_CONSEQ_CONV
            (rearrange_conv tm)
            (CONSEQ_TOP_REWRITE_CONV ([], [hpull_prop, hpull_prop_single], [])
              CONSEQ_CONV_STRENGTHEN_direction)
        )
      else if is_sep_exists tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hpull_exists_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
          ]
        )
      else
        NONE
  in
    case find_map pull ls of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hpull_setup_conv =
  (* cleanup the left heap a bit (remove ``emp``, pull SEP_EXISTS,...) *)
  SEP_IMP_conv (QCONV heap_clean_conv) REFL

val hpull_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV hpull_setup_conv THEN_DCC
  STRENGTHEN_CONSEQ_CONV hpull_one_conseq_conv_core

val hpull_conseq_conv =
  STRENGTHEN_CONSEQ_CONV hpull_setup_conv THEN_DCC
  REDEPTH_CONSEQ_CONV (STRENGTHEN_CONSEQ_CONV hpull_one_conseq_conv_core)

val hpull_one = CONSEQ_CONV_TAC hpull_one_conseq_conv
val hpull = CONSEQ_CONV_TAC hpull_conseq_conv

(* test goals:
  g `(A * cond P * (SEP_EXISTS x. G x) * cond Q :hprop) ==>> Z`;
  e (CONSEQ_CONV_TAC hpull_one_conseq_conv \\ strip_tac);
  e (CONSEQ_CONV_TAC hpull_one_conseq_conv \\ strip_tac);
  e (CONSEQ_CONV_TAC hpull_one_conseq_conv \\ strip_tac);

  g `(A * cond P * (SEP_EXISTS x. G x) * cond Q :hprop) ==>> Z`;
  e (CONSEQ_CONV_TAC hpull_conseq_conv);

  g `(A * emp * cond P * (SEP_EXISTS x. emp * G x) * cond Q :hprop) ==>> Z`;
  e (CONSEQ_CONV_TAC hpull_conseq_conv);

  g `(A * emp) ==>> Z`;
  e (CONSEQ_CONV_TAC hpull_conseq_conv);
*)

(** hsimpl_cancel *)

fun hsimpl_cancel_one_conseq_conv_core t =
  let
    val (l, r) = dest_sep_imp t
    val ls = list_dest dest_star l
    val rs = list_dest dest_star r
    val is = op_intersect aconv ls rs
    fun rearrange_conv tm1 tm2 =
      let
        val ls' = filter (not o aconv tm1) ls
        val rs' = filter (not o aconv tm2) rs
        val convl = rearrange_star_conv tm1 ls'
        val convr = rearrange_star_conv tm2 rs'
      in SEP_IMP_conv convl convr
      end
    fun cell_loc tm =
      SOME (fst (dest_cell tm)) handle _ =>
      SOME (fst (dest_REF tm)) handle _ =>
      SOME (fst (dest_ARRAY tm)) handle _ =>
      SOME (fst (dest_W8ARRAY tm)) handle _ =>
      SOME (#3 (dest_IO tm)) handle _ =>
      NONE
    fun same_cell_kind tm1 tm2 =
      (is_cell tm1 andalso is_cell tm2) orelse
      (is_REF tm1 andalso is_REF tm2) orelse
      (is_ARRAY tm1 andalso is_ARRAY tm2) orelse
      (is_W8ARRAY tm1 andalso is_W8ARRAY tm2) orelse
      (is_IO tm1 andalso is_IO tm2)
    fun find_matching_cells () =
      find_map (fn tm1 =>
        Option.mapPartial (fn loc =>
          find_map (fn tm2 =>
            Option.mapPartial (fn loc' =>
              if loc ~~ loc' andalso same_cell_kind tm1 tm2 then
                SOME (tm1, tm2)
              else NONE
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
      SEP_IMP_cell_frame_single_r,
      SEP_IMP_cell_frame_single,
      SEP_IMP_REF_frame,
      SEP_IMP_REF_frame_single_l,
      SEP_IMP_REF_frame_single_r,
      SEP_IMP_REF_frame_single,
      SEP_IMP_ARRAY_frame,
      SEP_IMP_ARRAY_frame_single_l,
      SEP_IMP_ARRAY_frame_single_r,
      SEP_IMP_ARRAY_frame_single,
      SEP_IMP_W8ARRAY_frame,
      SEP_IMP_W8ARRAY_frame_single_l,
      SEP_IMP_W8ARRAY_frame_single_r,
      SEP_IMP_W8ARRAY_frame_single,
      SEP_IMP_IO_frame,
      SEP_IMP_IO_frame_single_l,
      SEP_IMP_IO_frame_single_r,
      SEP_IMP_IO_frame_single
    ]
  in
    case is of
        tm :: _ =>
        THEN_CONSEQ_CONV
          (rearrange_conv tm tm)
          (CONSEQ_TOP_REWRITE_CONV ([], frame_thms, [])
            CONSEQ_CONV_STRENGTHEN_direction) t

       | [] =>
         case find_matching_cells () of
             SOME (tm1, tm2) =>
             THEN_CONSEQ_CONV
               (rearrange_conv tm1 tm2)
               (CONSEQ_TOP_REWRITE_CONV ([], frame_cell_thms, [])
                  CONSEQ_CONV_STRENGTHEN_direction) t
           | NONE => raise UNCHANGED
  end

val hsimpl_cancel_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV hsimpl_cancel_one_conseq_conv_core

val hsimpl_cancel_conseq_conv =
  REDEPTH_CONSEQ_CONV hsimpl_cancel_one_conseq_conv

val hsimpl_cancel_one = CONSEQ_CONV_TAC hsimpl_cancel_one_conseq_conv
val hsimpl_cancel = CONSEQ_CONV_TAC hsimpl_cancel_conseq_conv

(* test goal:
  g `(v = v' ==>
      (A:hprop * B * C * l ~~> v * l' ~~> w * D) ==>> (l' ~~> z * B * Z * l ~~> v' * Y * D * A))`;
  e strip_tac;

  e hsimpl_cancel_one;
  e hsimpl_cancel_one;
  e hsimpl_cancel_one;
  e (hsimpl_cancel_one \\ strip_tac THEN1 (fs []));
  e hsimpl_cancel_one;

  (* or alternatively *)
  e hsimpl_cancel;
*)

(** hpullr *)

fun hpullr_conseq_conv_core t =
  let
    val (l, r) = dest_sep_imp t
    val rs = list_dest dest_star r
    fun rearrange_conv tm =
      let val rest = filter (not o aconv tm) rs in
        SEP_IMP_conv REFL (rearrange_star_conv tm rest)
      end
    fun simpl tm =
      if is_cond tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hsimpl_prop, hsimpl_prop_single], [])
              CONSEQ_CONV_STRENGTHEN_direction
          ]
        )
      else if is_sep_exists tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hsimpl_exists_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
          ]
        )
      else
        NONE
  in
    case find_map simpl rs of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hpullr_setup_conv =
  SEP_IMP_conv REFL (QCONV heap_clean_conv)

val hpullr_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV hpullr_setup_conv THEN_DCC
  STRENGTHEN_CONSEQ_CONV hpullr_conseq_conv_core

val hpullr_conseq_conv =
  STRENGTHEN_CONSEQ_CONV hpullr_setup_conv THEN_DCC
  REDEPTH_CONSEQ_CONV (STRENGTHEN_CONSEQ_CONV hpullr_conseq_conv_core)

val hpullr_one = CONSEQ_CONV_TAC hpullr_one_conseq_conv
val hpullr = CONSEQ_CONV_TAC hpullr_conseq_conv

(* test goal:
  g `Z ==>> (A * cond P * (SEP_EXISTS x. G x) * cond Q :hprop)`;
  e hpullr_one;
  e (DEPTH_CONSEQ_CONV_TAC hpullr_one_conseq_conv);
  e (DEPTH_CONSEQ_CONV_TAC hpullr_one_conseq_conv);

  (* alternatively *)
  e hpullr;
*)

(** hcancel: hsimpl_cancel + hpullr *)

val SCC = STRENGTHEN_CONSEQ_CONV

val hcancel_setup_conv =
  SEP_IMP_conv
    (QCONV heap_clean_conv)
    (QCONV heap_clean_conv)

val hcancel_conseq_conv =
  EXT_DEPTH_CONSEQ_CONV
    (CONSEQ_CONV_get_context_congruences CONSEQ_CONV_NO_CONTEXT)
    CONSEQ_CONV_default_cache_opt NONE
    true (* redepth *)
    [(true, NONE, K (SCC (REWR_CONV SEP_IMPPOST_unfold))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTv_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTe_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTffi_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTd_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTv_inv_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTe_inv_def))),
     (true, NONE, K (SCC hcancel_setup_conv)),
     (true, NONE, K hsimpl_cancel_conseq_conv),
     (true, NONE, K hpullr_conseq_conv),
     (false, NONE, K (SCC (TRY_CONV LIST_FORALL_SIMP_CONV))),
     (false, NONE, K (SCC (SIMP_CONV bool_ss [hsimpl_gc, SEP_IMP_REFL])))
    ]
    []

val hcancel =
  CONSEQ_CONV_TAC hcancel_conseq_conv

(** hsimpl *)

val hsimpl_conseq_conv =
  EXT_DEPTH_CONSEQ_CONV
    (CONSEQ_CONV_get_context_congruences CONSEQ_CONV_NO_CONTEXT)
    CONSEQ_CONV_default_cache_opt NONE
    true (* redepth *)
    [(true, NONE, K (SCC (REWR_CONV SEP_IMPPOST_unfold))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTv_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTe_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTffi_def))),     
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTd_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTv_inv_def))),
     (true, NONE, K (SCC (REWR_CONV SEP_IMPPOSTe_inv_def))),
     (true, NONE, K (SCC hcancel_setup_conv)),
     (true, NONE, K hpull_conseq_conv),
     (true, NONE, K hsimpl_cancel_conseq_conv),
     (true, NONE, K hpullr_conseq_conv),
     (false, NONE, K (SCC (TRY_CONV LIST_FORALL_SIMP_CONV))),
     (false, NONE, K (SCC (SIMP_CONV bool_ss [hsimpl_gc, SEP_IMP_REFL])))
    ]
    []

val hsimpl =
  CONSEQ_CONV_TAC hsimpl_conseq_conv

(* test goal:
  g `(A:hprop * B * C * l ~~> v * l' ~~> u * D) ==>> (B * Z * l ~~> v' * l' ~~> u' * Y * cond Q * D * A)`;

  e (CONSEQ_CONV_TAC hsimpl_conseq_conv);
  e hsimpl;

  g `emp ==>> emp`;
  e hsimpl
*)

(** sep_imp_instantiate: instantiate existentially quantified
    variables after subterms of the form ``H1 ==>> H2`` where one of
    {H1, H2} is existentially quantified, and not the other.
*)

infix then_ecc

fun sep_imp_instantiate {term, evars} = let
  val ts = strip_conj term
  fun find_inst t = let
    val (H1, H2) = dest_sep_imp t in
    if tmem H1 evars andalso not (tmem H2 evars) then
      {instantiation = [H1 |-> H2], new_evars = []}
    else if tmem H2 evars andalso not (tmem H1 evars) then
      {instantiation = [H2 |-> H1], new_evars = []}
    else fail ()
  end
  fun find_inst' t = SOME (find_inst t) handle HOL_ERR _ => NONE
in
  case find_map find_inst' ts of
      SOME inst => inst
    | NONE => fail ()
end

val hinst_ecc =
  repeat_ecc (instantiate_ecc sep_imp_instantiate) then_ecc
  lift_conseq_conv_ecc (SIMP_CONV bool_ss [hsimpl_gc, SEP_IMP_REFL])

val hinst =
  CONSEQ_CONV_TAC
    (STRENGTHEN_CONSEQ_CONV
      (ecc_conseq_conv hinst_ecc))

end
