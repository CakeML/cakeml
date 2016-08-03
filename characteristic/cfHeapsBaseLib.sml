structure cfHeapsBaseLib :> cfHeapsBaseLib =
struct

open preamble
open set_sepTheory helperLib ConseqConv
open evarsConseqConvLib
open cfHeapsBaseTheory cfTacticsBaseLib

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

(*------------------------------------------------------------------*)
(** Auxiliary functions *)

fun dest_sep_imp tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMP_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_cell tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) cell_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_REF tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) REF_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_ARRAY tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) ARRAY_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_W8ARRAY tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) W8ARRAY_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun is_cell tm = can dest_cell tm
fun is_REF tm = can dest_REF tm
fun is_ARRAY tm = can dest_ARRAY tm
fun is_W8ARRAY tm = can dest_W8ARRAY tm

fun is_sep_imp tm = can dest_sep_imp tm

fun is_sep_imppost tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMPPOST_def
  in can (match_term format) tm end

fun is_cond tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) cond_def
  in can (match_term format) tm end
  
fun is_sep_exists tm = let
  val se = (fst o dest_eq o concl o SPEC_ALL) SEP_EXISTS
  in can (match_term ``^se P``) tm end

fun UNFOLD_SEP_IMPPOST_ccc tm = let
  val _ = if not (is_sep_imppost tm) then fail () else ()
  val th =
      CONSEQ_TOP_REWRITE_CONV ([], [SEP_IMPPOST_def], [])
        CONSEQ_CONV_STRENGTHEN_direction tm
  val cont = (snd o dest_forall, FORALL_CONSEQ_CONV)
in (th, cont) end

fun SEP_IMP_conv convl convr t =
  let val (l, r) = dest_sep_imp t
      val rew_t = MATCH_MP (MATCH_MP SEP_IMP_rew (convl l)) (convr r)
  in UNCHANGED_CONV (REWR_CONV rew_t) t
  end

fun rearrange_star_conv tm rest =
  let val rearranged = list_mk_star (rest @ [tm]) ``:hprop`` in
    fn t => prove (mk_eq (t, rearranged), rew_heap_AC)
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

fun hpull_cont_conseq_conv_core t =
  let
    val (l, r) = dest_sep_imp t
    val ls = list_dest dest_star l
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) ls in
        SEP_IMP_conv (rearrange_star_conv tm rest) REFL
      end
    fun pull tm =
      if is_cond tm then
        SOME (
          THEN_CONSEQ_CONV
            (rearrange_conv tm)
            (CONSEQ_TOP_REWRITE_CONV ([], [hpull_prop, hpull_prop_single], [])
              CONSEQ_CONV_STRENGTHEN_direction),
          (rand, IMP_CONCL_CONSEQ_CONV)
        )
      else if is_sep_exists tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hpull_exists_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
          ],
          (snd o strip_forall, STRIP_FORALL_CONSEQ_CONV)
        )
      else
        NONE
  in
    case find_map pull ls of
        NONE => raise UNCHANGED
      | SOME (cc, cont) => (cc t, cont)
  end

val hpull_setup_conv =
  (* cleanup the left heap a bit (remove ``emp``, pull SEP_EXISTS,...) *)
  SEP_IMP_conv (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES])) REFL

val hpull_one_cont_conseq_conv =
  THEN_CONT_CONSEQ_CONV
    (INPLACE_CONT_CONSEQ_CONV hpull_setup_conv)
    hpull_cont_conseq_conv_core

val hpull_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hpull_one_cont_conseq_conv)

val hpull_cont_conseq_conv =
  THEN_CONT_CONSEQ_CONV
    (INPLACE_CONT_CONSEQ_CONV hpull_setup_conv)
    (LOOP_CONT_CONSEQ_CONV hpull_cont_conseq_conv_core)

val hpull_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hpull_cont_conseq_conv)

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

fun hsimpl_cancel_one_cont_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t
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
      SOME (fst (dest_cell tm)) handle _ =>
      SOME (fst (dest_REF tm)) handle _ =>
      SOME (fst (dest_ARRAY tm)) handle _ =>
      SOME (fst (dest_W8ARRAY tm)) handle _ =>
      NONE
    fun same_cell_kind tm1 tm2 =
      (is_cell tm1 andalso is_cell tm2) orelse
      (is_REF tm1 andalso is_REF tm2) orelse
      (is_ARRAY tm1 andalso is_ARRAY tm2) orelse
      (is_W8ARRAY tm1 andalso is_W8ARRAY tm2)
    fun find_matching_cells () =
      find_map (fn tm1 =>
        Option.mapPartial (fn loc =>
          find_map (fn tm2 =>
            Option.mapPartial (fn loc' =>
              if loc = loc' andalso same_cell_kind tm1 tm2 then
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
      SEP_IMP_W8ARRAY_frame_single
    ]
  in
    case is of
        tm :: _ =>
        (THEN_CONSEQ_CONV
           (rearrange_conv tm tm)
           (CONSEQ_TOP_REWRITE_CONV ([], frame_thms, [])
             CONSEQ_CONV_STRENGTHEN_direction) t,
          (I, I))

       | [] =>
         case find_matching_cells () of
             SOME (tm1, tm2) =>
             (THEN_CONSEQ_CONV
                (rearrange_conv tm1 tm2)
                (CONSEQ_TOP_REWRITE_CONV ([], frame_cell_thms, [])
                   CONSEQ_CONV_STRENGTHEN_direction) t,
              (rand, CONJ2_CONSEQ_CONV))
           | NONE => raise UNCHANGED
  end

val hsimpl_cancel_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hsimpl_cancel_one_cont_conseq_conv)

val hsimpl_cancel_cont_conseq_conv =
  LOOP_CONT_CONSEQ_CONV hsimpl_cancel_one_cont_conseq_conv

val hsimpl_cancel_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hsimpl_cancel_cont_conseq_conv)

val hsimpl_cancel_one = CONSEQ_CONV_TAC hsimpl_cancel_one_conseq_conv
val hsimpl_cancel = CONSEQ_CONV_TAC hsimpl_cancel_conseq_conv

(* test goal:
  g `(A:hprop * B * C * l ~~> v * l' ~~> w * D) ==>> (l' ~~> z * B * Z * l ~~> v' * Y * D * A)`;
  e hsimpl_cancel_one;
  e hsimpl_cancel_one;
  e hsimpl_cancel_one;
  e (hsimpl_cancel_one \\ strip_tac THEN1 cheat);
  e hsimpl_cancel_one;

  (* or alternatively *)
  e hsimpl_cancel;
*)

(** hpullr *)

fun hpullr_cont_conseq_conv_core t =
  let
    val (l, r) = dest_sep_imp t
    val rs = list_dest dest_star r
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) rs in
        SEP_IMP_conv REFL (rearrange_star_conv tm rest)
      end
    fun simpl tm =
      if is_cond tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hsimpl_prop, hsimpl_prop_single], [])
              CONSEQ_CONV_STRENGTHEN_direction
          ],
          (rand, CONJ2_CONSEQ_CONV)
        )
      else if is_sep_exists tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_REWRITE_CONV ([], [hsimpl_exists_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
          ],
          (snd o strip_exists, STRIP_EXISTS_CONSEQ_CONV)
        )
      else
        NONE
  in
    case find_map simpl rs of
        NONE => raise UNCHANGED
      | SOME (cc, cont) => (cc t, cont)
  end

val hpullr_setup_conv =
  SEP_IMP_conv REFL (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))

val hpullr_one_cont_conseq_conv =
  THEN_CONT_CONSEQ_CONV
    (INPLACE_CONT_CONSEQ_CONV hpullr_setup_conv)
    hpullr_cont_conseq_conv_core

val hpullr_one_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hpullr_one_cont_conseq_conv)

val hpullr_cont_conseq_conv =
  THEN_CONT_CONSEQ_CONV
    (INPLACE_CONT_CONSEQ_CONV hpullr_setup_conv)
    (LOOP_CONT_CONSEQ_CONV hpullr_cont_conseq_conv_core)

val hpullr_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hpullr_cont_conseq_conv)
  
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

(** hsimpl *)

val hsimpl_cont_conseq_conv_core =
  EVERY_CONT_CONSEQ_CONV [
    LOOP_CONT_CONSEQ_CONV hpull_cont_conseq_conv,
    LOOP_CONT_CONSEQ_CONV (
      THEN_CONT_CONSEQ_CONV
        (LOOP_CONT_CONSEQ_CONV hsimpl_cancel_cont_conseq_conv)
        (LOOP_CONT_CONSEQ_CONV hpullr_cont_conseq_conv)
    ),
    INPLACE_CONT_CONSEQ_CONV
      (SIMP_CONV bool_ss [hsimpl_gc, SEP_IMP_REFL])
  ]

val hsimpl_setup_conv =
  SEP_IMP_conv
    (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))
    (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))

val hsimpl_cont_conseq_conv =
  EVERY_CONT_CONSEQ_CONV [
    TRY_CONT_CONSEQ_CONV UNFOLD_SEP_IMPPOST_ccc,
    INPLACE_CONT_CONSEQ_CONV hsimpl_setup_conv,
    hsimpl_cont_conseq_conv_core
  ]

val hsimpl_conseq_conv =
  STRENGTHEN_CONSEQ_CONV
    (STEP_CONT_CONSEQ_CONV hsimpl_cont_conseq_conv) THEN_DCC
  STRENGTHEN_CONSEQ_CONV
    (TRY_CONV LIST_FORALL_SIMP_CONV)

val hsimpl_top =
  CONSEQ_CONV_TAC hsimpl_conseq_conv

val hsimpl =
  DEPTH_CONSEQ_CONV_TAC hsimpl_conseq_conv

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

fun sep_imp_instantiate {term, evars} = let
  val ts = strip_conj term
  fun find_inst t = let
    val (H1, H2) = dest_sep_imp t in
    if mem H1 evars andalso not (mem H2 evars) then
      {instantiation = [H1 |-> H2], new_evars = []}
    else if mem H2 evars andalso not (mem H1 evars) then
      {instantiation = [H2 |-> H1], new_evars = []}
    else fail ()
  end
  fun find_inst' t = SOME (find_inst t) handle HOL_ERR _ => NONE
in
  case find_map find_inst' ts of
      SOME inst => inst
    | NONE => fail ()
end

val sep_imp_instantiate_ecc =
    repeat_ecc (instantiate_ecc sep_imp_instantiate)

end
