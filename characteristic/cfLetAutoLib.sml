(*
  Theorems, conversions, solvers used by the xlet_auto tactic.
*)
structure cfLetAutoLib :> cfLetAutoLib =
struct

open preamble ml_progLib cfTacticsLib ml_translatorTheory
     eqSolveRewriteLib Satisfy cfLetAutoTheory

(*********************************************************************************
 *
 * Theorems, conversions, solvers used by the xlet_auto tactic
 * these appear first so they can be skipped easily for debugging
   in which case use these instead:

START REFS

val get_frame_thms = cfLetAutoLib.get_frame_thms
val get_equality_type_thms = cfLetAutoLib.get_equality_type_thms
val get_RI_defs = cfLetAutoLib.get_RI_defs
val get_expand_thms = cfLetAutoLib.get_expand_thms
val get_retract_thms = cfLetAutoLib.get_retract_thms
val get_intro_rewrite_thms = cfLetAutoLib.get_intro_rewrite_thms
val get_rewrite_thms = cfLetAutoLib.get_rewrite_thms
val get_default_simpset = cfLetAutoLib.get_default_simpset
 *
 *********************************************************************************)

(* Auxiliary function for the exporters *)
fun mk_export_f f (thy_name : string) (named_thms : (string * thm) list) =
  f (List.map snd named_thms);

(* Theorems used to compute the frame *)
val FRAME_THMS = ref [REF_HPROP_INJ,
                      ARRAY_HPROP_INJ,
                      W8ARRAY_HPROP_INJ
                     ];

fun add_frame_thms thms = FRAME_THMS := (thms  @ !FRAME_THMS);
fun get_frame_thms () = !FRAME_THMS;

fun new_exporter nm add =
    ThmSetData.new_exporter {
      efns = {add = fn {named_thms,...} => add (map #2 named_thms),
              remove = fn _ => ()},
      settype = nm
    } |> #export

val export = new_exporter "hprop_inj" (mk_export_f add_frame_thms);

fun export_frame_thms slist = List.app export slist;

(* Refinement invariants: definitions *)
val RI_DEFSL = ref ([] : thm list);
fun add_RI_defs defs = (RI_DEFSL := defs @ !RI_DEFSL);
fun get_RI_defs uv = !RI_DEFSL;

(* Theorem generation *)
fun generate_expand_retract_thms ri_defs =
  let
      val ri_l = List.map (fn x => SPEC_ALL x |> concl |> dest_eq |> fst) ri_defs
      fun inst_ri ri =
        let
            val ty = dest_type (type_of ri) |> snd |> List.hd
            val v = mk_var ("v", ty)
            val v' = variant (free_vars ri) v
        in
            mk_comb (ri, v')
        end
        handle HOL_ERR _ => ri
             | Empty => ri
      val inst_ri_l = List.map inst_ri ri_l
      val expandThms = List.map (GEN_ALL o (SIMP_CONV (srw_ss()) (ri_defs @ !RI_DEFSL))) inst_ri_l
      val retractThms = List.map GSYM expandThms
  in
      (expandThms, retractThms)
  end;

(* Theorems to expand or retract the definitions of refinement invariants*)
val RI_EXPAND_THMSL = ref ([UNIT_TYPE_EXPAND] : thm list);
val RI_RETRACT_THMSL = ref ([UNIT_TYPE_RETRACT] : thm list);
fun add_expand_retract_thms expandThms retractThms =
  (RI_EXPAND_THMSL := expandThms @ !RI_EXPAND_THMSL;
   RI_RETRACT_THMSL := retractThms @ !RI_RETRACT_THMSL);

fun get_expand_thms () = !RI_EXPAND_THMSL;
fun get_retract_thms () = !RI_RETRACT_THMSL;

val EXPAND_TAC = FULL_SIMP_TAC (srw_ss()) (get_expand_thms());
val RETRACT_TAC = FULL_SIMP_TAC (srw_ss()) (get_retract_thms());
val REWRITE_RI_TAC = EXPAND_TAC THEN RETRACT_TAC;

(* List of equality types *)
val EQUALITY_TYPE_THMS = ref ([] : thm list);

fun add_equality_type_thms thms =
  (EQUALITY_TYPE_THMS := (List.concat (List.map CONJUNCTS thms))
                         @ !EQUALITY_TYPE_THMS);
fun get_equality_type_thms () = !EQUALITY_TYPE_THMS;

(* Unicity theorems *)
val INTRO_RW_THMS = ref ([NUM_INT_EQ, LIST_REL_UNICITY_RIGHT, LIST_REL_UNICITY_LEFT, EQTYPE_UNICITY_R, EQTYPE_UNICITY_L]);

fun add_intro_rewrite_thms thms = (INTRO_RW_THMS := thms @ !INTRO_RW_THMS);
fun get_intro_rewrite_thms () = !INTRO_RW_THMS;

(* Automatic generation of theorems *)
fun generate_RI_unicity_thms eq_type_thms =
  let
      fun get_ref_inv th = concl th |> dest_comb |> snd
      fun get_types ref_inv =
        let
            fun two_el [x,y] = (x,y)
              | two_el _     = failwith "get_types"
            val (t1,t') = type_of ref_inv |> dest_type |> snd |> two_el
            val (t2, _) = dest_type t' |> snd |> two_el
        in
            (t1, t2)
        end
      fun gen_left_rule eq_type_thm =
        let
            val ref_inv = get_ref_inv eq_type_thm
            val (t1, t2) = get_types ref_inv
            val th1 = Thm.INST_TYPE [alpha |-> t1, beta |-> t2] EQTYPE_UNICITY_L
            val th2 = SPEC ref_inv th1
            val (x1, x2, y) = (mk_var("x1", t1), mk_var("x2", t1), mk_var("y", t2))
            val th3 = SPECL [x1, x2, y] th2
            val th4 = MP th3 eq_type_thm
            val th5 = GEN_ALL th4
        in
            th5
        end
      fun gen_right_rule eq_type_thm =
        let
            val ref_inv = get_ref_inv eq_type_thm
            val (t1, t2) = get_types ref_inv
            val th1 = Thm.INST_TYPE [alpha |-> t1, beta |-> t2] EQTYPE_UNICITY_R
            val th2 = SPEC ref_inv th1
            val (x, y1, y2) = (mk_var("x", t1), mk_var("y1", t2), mk_var("y2", t2))
            val th3 = SPECL [x, y1, y2] th2
            val th4 = MP th3 eq_type_thm
            val th5 = GEN_ALL th4
        in
            th5
        end
      val eq_type_thms = List.concat(List.map CONJUNCTS eq_type_thms)
      val left_rules = List.map gen_left_rule eq_type_thms
      val right_rules = List.map gen_right_rule eq_type_thms
  in
      List.concat [left_rules, right_rules]
  end;

fun export_equality_type_thms_aux thms =
  let
      val thms = List.map (CONV_RULE (PURE_REWRITE_CONV [satTheory.AND_IMP])) thms
      (* val unicity_thms = generate_RI_unicity_thms thms *)
  in
      add_equality_type_thms thms
      (* ; add_intro_rewrite_thms unicity_thms *)
  end;

val export = new_exporter "equality_types"
                        (mk_export_f export_equality_type_thms_aux);

fun export_equality_type_thms slist = List.app export slist;

val _ = export_equality_type_thms_aux [EqualityType_NUM_BOOL,
                                       EqualityType_LIST_TYPE,
                                       EqualityType_PAIR_TYPE];

(* Basic rewrite theorems *)
val RW_THMS = ref [(* Handle the int_of_num operator *)
                    integerTheory.INT_ADD,
                    INT_OF_NUM_TIMES,
                    INT_OF_NUM_LE,
                    INT_OF_NUM_LESS,
                    INT_OF_NUM_GE,
                    INT_OF_NUM_GREAT,
                    INT_OF_NUM_EQ,
                    INT_OF_NUM_SUBS,
                    INT_OF_NUM_SUBS_2,

                    (* Handle lists *)
                    LENGTH_NIL,
                    LENGTH_NIL_SYM,
                    REPLICATE_APPEND_DECOMPOSE,
                    REPLICATE_APPEND_DECOMPOSE_SYM,
                    LIST_REL_DECOMPOSE_RIGHT,
                    LIST_REL_DECOMPOSE_LEFT,
                    LENGTH_REPLICATE,
                    TAKE_LENGTH_ID,
                    DROP_nil,
                    DROP_LENGTH_TOO_LONG,
                    NULL_EQ,
                    (* REPLICATE *)
                    (* REPLICATE_PLUS_ONE *)

                    (*mlbasicsProgTheory.not_def*)

                    (* Arithmetic equations simplification *)
                    NUM_EQ_SIMP1,
                    NUM_EQ_SIMP2,
                    NUM_EQ_SIMP3,
                    NUM_EQ_SIMP4,
                    NUM_EQ_SIMP5,
                    NUM_EQ_SIMP6,
                    NUM_EQ_SIMP7,
                    NUM_EQ_SIMP8,
                    NUM_EQ_SIMP9,
                    NUM_EQ_SIMP10,
                    NUM_EQ_SIMP11,
                    NUM_EQ_SIMP12,
                    MIN_DEF
                   ];
fun add_rewrite_thms thms = (RW_THMS := thms @ !RW_THMS);
fun get_rewrite_thms () = !RW_THMS;

(* Default simpset *)
val DEF_SIMPSET = ref pure_ss;
val _ = (DEF_SIMPSET := srw_ss());

(* TODO: Find a way to export that - like with ThmSetData.new_exporter *)
fun add_simp_frag sf = (DEF_SIMPSET := ((!DEF_SIMPSET) ++ sf));
fun get_default_simpset () = !DEF_SIMPSET;

fun add_refinement_invariants ri_defs =
  let
      val (expandThms, retractThms) = generate_expand_retract_thms ri_defs
      val invertDefs = List.map GSYM ri_defs
  in
      add_RI_defs ri_defs;
      add_expand_retract_thms (expandThms @ ri_defs) (invertDefs @ retractThms)
  end;

val export = new_exporter "refinement_invariants"
                          (mk_export_f add_refinement_invariants);

fun export_refinement_invariants slist = List.app export slist;

(* Don't put UNIT_TYPE in here and use UNIT_TYPE_EXPAND and
   UNIT_TYPE_RETRACT instead - because of the nature of the unit type,
   the automatically generated retract rule for UNIT_TYPE introduces a
   new variable: !u v. v = Conv NONE [] <=> UNIT_TYPE u v *)
val _ = add_refinement_invariants [NUM_def, INT_def, BOOL_def, STRING_TYPE_def];

fun add_match_thms thms =
  let
      (* Partition the theorems between the rewrite theorems and the intro rewrite ones *)
      fun is_intro_rw t =
        let
            val (vars, t') = strip_forall t
            val (imps, t'') = strip_imp t'
        in
            case (vars, imps) of
                ([], []) =>
                (let
                    val (leq, req) = dest_eq t''
                    val lvars = HOLset.addList (empty_varset, free_vars leq)
                    val rvars = HOLset.addList (empty_varset, free_vars req)
                in
                    not (HOLset.isSubset (rvars, lvars))
                end
                 handle HOL_ERR _ => false)
              | _ => is_intro_rw t''
        end

      val (intro_rws, rws) = List.partition (is_intro_rw o concl) thms
  in
      add_intro_rewrite_thms intro_rws;
      add_rewrite_thms rws
  end;

val export = new_exporter "xlet_auto_match"
                                    (mk_export_f add_match_thms);

fun export_match_thms slist = List.app export slist;

(* END REFS *)

(* Store the last iteration of the manipulated app_spec for debugging purposes, if xlet_auto fails *)
val debug_app_spec = ref (REFL T)
fun debug_get_app_spec () = !debug_app_spec
fun debug_set_app_spec app_spec = (debug_app_spec := app_spec)
(* TODO: move *)
(* set_sep syntax *)
val (sep_imp_tm,mk_sep_imp,dest_sep_imp,is_sep_imp) = syntax_fns2 "set_sep" "SEP_IMP";
(* -- *)
(* semanticPrimitives syntax *)
val (sem_env_c_tm,mk_sem_env_c,dest_sem_env_c,is_sem_env_c) = syntax_fns1 "semanticPrimitives" "sem_env_c";
(* -- *)
val set_sep_cond_hprop_tm =
  mk_thy_const{Name="cond",Thy="set_sep",Ty= bool --> cfHeapsBaseSyntax.hprop_ty}
fun mk_cond_hprop tm = mk_comb(set_sep_cond_hprop_tm,tm)

(* TODO: move these to preamble, or Drule? *)
(********************************************************************************************)
(******************** Some conversions used to perform the matching *************************)
(*
   MP_ASSUM:

   (!a in T'. T |= a)      T' |= g
   ===============================
               T |= g
  *)
fun MP_ASSUML thl th =
  let
      val conclList = List.map (fn x => (concl x, x)) thl
      val conclMap = Redblackmap.fromList Term.compare conclList
      val num_hyps = List.length (hyp th)
      val th' = DISCH_ALL th
      fun rec_mp th n =
        if n > 0 then
          let
            val h = concl th |> dest_imp |> fst
            val hyp_th = (Redblackmap.find (conclMap, h) handle NotFound =>
                raise (ERR "MP_ASSUML" ("Could not find the hypothesis: " ^(term_to_string h))))
            val th' = MP th hyp_th
          in
            rec_mp th' (n-1)
          end
        else th
  in
      rec_mp th' num_hyps
  end;

(*
   CONV_ASSUM: use a conversion to rewrite an assumption list so that:
   (!a' in T'. T |= a') /\ (!a in T. T' |= a)
   Returns the list of theorems: !a' in T'. T |= a'
*)
fun CONV_ASSUM sset rws asl =
  let
      val tautl = List.map ASSUME asl |> List.map CONJUNCTS |> List.concat
      fun try_conv th = (CONV_RULE (SIMP_CONV sset rws) th handle HOL_ERR _ => th)
  in
      List.map try_conv tautl
  end;

(**** INTRO_REWRITE: use rewrite rules of the form h1 ==> ... ==> hn ==> PAT <=> y = z ********)
(* INTRO_REWRITE_CONV *)
fun INTRO_REWRITE_CONV thl asl =
    let
        val base_thms = (List.map ASSUME asl) @ thl
        val disj_thl = List.concat (List.map CONJUNCTS thl)
        fun match_on_asl th = mapfilter (MATCH_MP th) base_thms
        fun is_rw_th th = SPEC_ALL th |> concl |> is_eq
        fun generate_rewrites thl =
          let
              val (rewrite_thl, thl') = List.partition is_rw_th thl
              val thl'' = List.concat (mapfilter match_on_asl thl')
          in
              case thl'' of
                  [] => rewrite_thl
                | _ => List.revAppend (generate_rewrites thl'', rewrite_thl)
          end
        val rw_thms = generate_rewrites disj_thl
    in
        SIMP_CONV bool_ss rw_thms
    end;

(* INTRO_REWRITE_TAC *)
fun INTRO_REWRITE_TAC rws (g as (asl, w)) = CONV_TAC (INTRO_REWRITE_CONV rws asl) g;

(* RENAME_SPEC_ALL *)
fun RENAME_SPEC_ALL varsl th =
  let
      val (v, th') = SPEC_VAR th
      val v' = variant varsl v
  in
      if v !~ v' then
          RENAME_SPEC_ALL (v'::varsl) (Thm.INST [v |-> v'] th')
      else
          RENAME_SPEC_ALL (v::varsl) th'
  end
  handle HOL_ERR _ => th;

(************************ Functions ************************************************)

val ERR = mk_HOL_ERR "cfLetAutoLib";

(* TODO: move to semanticPrimitivesSyntax *)
val (build_conv_tm, mk_build_conv, dest_build_conv, is_build_conv) = HolKernel.syntax_fns3 "semanticPrimitives" "build_conv";
(* TODO: move to cfcNormaliseSyntax? *)
val (exp2v_tm, mk_exp2v, dest_exp2v, is_exp2v) = HolKernel.syntax_fns2 "cfNormalise" "exp2v";

(* Manipulation of expressions *)

fun get_value env e =
  cfTacticsLib.reduce_conv (mk_exp2v (env, e))
  |> concl |> rhs |> optionSyntax.dest_some;

(* Rename a variable by adding numbers rather than adding primes - useful for
   xlet_auto, which introduces variables (Postv, Poste, Post) *)

fun dest_suffix s =
  let
      fun is_suffix_char c = Char.isDigit c orelse c = #"'"
      fun rec_dest s1 (c::s2) =
        if is_suffix_char c then rec_dest (c::s1) s2
        else (List.rev (c::s2), s1)
        | rec_dest s [] = failwith "dest_suffix"
  in
      rec_dest [] (List.rev s)
  end;

fun ivariant varsl v =
  let
      val _ = if (not o is_var) v then
                  raise (ERR "variant" "not a variable") else ()
      val varnamesl = (List.map (fst o dest_var) varsl) @
                      (List.map (fst o dest_const) (Term.all_consts ()))
      val varnames_set = HOLset.fromList String.compare varnamesl
      val vname = (fst o dest_var) v
  in
      case HOLset.member (varnames_set, vname) of
          true =>
          let
              val name_pre = (implode o fst o dest_suffix o explode) vname
              val filt_names = List.filter
                        (fn x => String.isPrefix name_pre x) varnamesl
              val l = String.size name_pre
              fun drop s = String.substring (s, l, String.size s - l)
              val suffixes = List.map drop filt_names
              val nums = mapfilter string_to_int suffixes
              val max_s = List.foldr Int.max 0 nums
              val suffix = Int.toString (max_s + 1)
              val new_name = String.concat [name_pre, suffix]
          in
              mk_var (new_name, type_of v)
          end
        | false => v
  end;

(* [dest_post_condition] *)
fun dest_post_condition c =
  if cfHeapsBaseSyntax.is_postv c then
      let
          val (postv_v, postv_pred) = cfHeapsBaseSyntax.dest_postv c
      in
          (SOME postv_v, SOME postv_pred, NONE, NONE, NONE, NONE, NONE, NONE) end
  else if cfHeapsBaseSyntax.is_poste c then
      let
          val (poste_v, poste_pred) = cfHeapsBaseSyntax.dest_poste c
      in
          (NONE, NONE, SOME poste_v, SOME poste_pred, NONE, NONE, NONE, NONE) end
  (* TODO: add postf *)
  else if cfHeapsBaseSyntax.is_postd c then
      let
          val (postd_io, postd_pred) = cfHeapsBaseSyntax.dest_postd c
      in
          (NONE, NONE, NONE, NONE, NONE, NONE, SOME postd_io, SOME postd_pred) end
  else if cfHeapsBaseSyntax.is_postve c then
      let
          val (postv_v, postv_pred, poste_v, poste_pred) = cfHeapsBaseSyntax.dest_postve c
      in
          (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred,
           NONE, NONE, NONE, NONE) end
  else if cfHeapsBaseSyntax.is_postvd c then
      let
          val (postv_v, postv_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_postvd c
      in
          (SOME postv_v, SOME postv_pred, NONE, NONE,
           NONE, NONE, SOME postd_io, SOME postd_pred) end
  else if cfHeapsBaseSyntax.is_posted c then
      let
          val (poste_v, poste_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_posted c
      in
          (NONE, NONE, SOME poste_v, SOME poste_pred,
           NONE, NONE, SOME postd_io, SOME postd_pred) end
  else if cfHeapsBaseSyntax.is_post c then
      let
        val (postv_v, postv_pred, poste_v, poste_pred,
             postf_args, postf_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_post c
      in
          (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred,
           SOME postf_args, SOME postf_pred, SOME postd_io, SOME postd_pred) end
  else
      raise (ERR "rename_dest_post" "Not a heap post-condition");

(* [rename_dest_post] *)
fun rename_dest_post (varsl, c) =
  if cfHeapsBaseSyntax.is_postv c then
      let
          val (postv_v, postv_pred) = cfHeapsBaseSyntax.dest_postv c
          val postv_v' = variant varsl postv_v
          val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
      in
          (SOME postv_v', SOME postv_pred', NONE, NONE, NONE, NONE, NONE, NONE) end
  else if cfHeapsBaseSyntax.is_poste c then
      let
          val (poste_v, poste_pred) = cfHeapsBaseSyntax.dest_poste c
          val poste_v' = variant varsl poste_v
          val poste_pred' = Term.subst [poste_v |-> poste_v']  poste_pred
      in
         (NONE, NONE, SOME poste_v', SOME poste_pred', NONE, NONE, NONE, NONE) end
  (* TODO: add postf *)
  else if cfHeapsBaseSyntax.is_postd c then
      let
          val (postd_io, postd_pred) = cfHeapsBaseSyntax.dest_postd c
          val postd_io' = variant varsl postd_io
          val postd_pred' = Term.subst [postd_io |-> postd_io']  postd_pred
      in
          (NONE, NONE, NONE, NONE, NONE, NONE, SOME postd_io', SOME postd_pred') end
  else if cfHeapsBaseSyntax.is_postve c then
      let
          val (postv_v, postv_pred, poste_v, poste_pred) = cfHeapsBaseSyntax.dest_postve c
          val postv_v' = variant varsl postv_v
          val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
          val poste_v' = variant (postv_v'::varsl) poste_v
          val poste_pred' = Term.subst [poste_v |-> poste_v'] poste_pred
      in
          (SOME postv_v', SOME postv_pred', SOME poste_v', SOME poste_pred',
           NONE, NONE, NONE, NONE) end
  else if cfHeapsBaseSyntax.is_postvd c then
      let
          val (postv_v, postv_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_postvd c
          val postv_v' = variant varsl postv_v
          val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
          val postd_io' = variant (postv_v'::varsl) postd_io
          val postd_pred' = Term.subst [postd_io |-> postd_io'] postd_pred
      in
          (SOME postv_v', SOME postv_pred', NONE, NONE,
           NONE, NONE, SOME postd_io', SOME postd_pred') end
  else if cfHeapsBaseSyntax.is_posted c then
      let
          val (poste_v, poste_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_posted c
          val poste_v' = variant varsl poste_v
          val poste_pred' = Term.subst [poste_v |-> poste_v'] poste_pred
          val postd_io' = variant (poste_v'::varsl) postd_io
          val postd_pred' = Term.subst [postd_io |-> postd_io'] postd_pred
      in
          (NONE, NONE, SOME poste_v', SOME poste_pred',
           NONE, NONE, SOME postd_io', SOME postd_pred') end
  else if cfHeapsBaseSyntax.is_post c then
      let
          val (postv_v, postv_pred, poste_v, poste_pred,
               postf_args, postf_pred, postd_io, postd_pred) = cfHeapsBaseSyntax.dest_post c
          val postv_v' = variant varsl postv_v
          val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
          val poste_v' = variant (postv_v'::varsl) poste_v
          val poste_pred' = Term.subst [poste_v |-> poste_v'] poste_pred
          fun variants ts [] = []
            | variants ts (f::r) =
              let val f' = variant ts f in
                f'::variants (f'::ts) r
              end
          val postf_args' = variants (poste_v'::postv_v'::varsl) postf_args
          val postf_pred' = Term.subst (map2 (curry op |->) postf_args postf_args') postf_pred
          val postd_io' = variant (postf_args'@poste_v'::postv_v'::varsl) postd_io
          val postd_pred' = Term.subst [postd_io |-> postd_io']  postd_pred
      in
        (SOME postv_v', SOME postv_pred', SOME poste_v', SOME poste_pred',
         SOME postf_args', SOME postf_pred', SOME postd_io', SOME postd_pred') end
  else
      raise (ERR "rename_dest_post" "Not a heap post-condition");

(* [rename_dest_exists]
  Deconstructs the existential quantifiers of a heap condition,
  and rename the previsouly bound variables to prevent name conflicts. *)
fun rename_dest_exists (varsl, c) =
  let fun rec_dest varsl lv c =
    if is_sep_exists c then
      let
        val (nv, nc) = dest_sep_exists c
        val nv' = variant varsl nv
        val nc' = Term.subst [nv |-> nv'] nc
        val (nlv, fc) = rec_dest (nv'::varsl) lv nc'
      in
        (nv'::nlv, fc)
      end
    else
      (([]:term list), c)
  in
    rec_dest varsl ([]:term list) c
  end;

(* [dest_pure_fact]
   Deconstructs a pure fact (a heap predicate of the form &P) *)
fun dest_pure_fact p =
  case (dest_term p) of
  COMB dp =>
    (if same_const set_sep_cond_hprop_tm (#1 dp) then (#2 dp)
    else raise (ERR "dest_pure_fact" "Not a pure fact"))
  | _ => raise (ERR "dest_pure_fact" "Not a pure fact");

(* [sort_heap_pred]
   Determines whether a heap predicate is a pure fact or not,
   and adds it to the according list. *)
fun sort_heap_pred hp hpl pfl =
  let
    val pure_pred = dest_pure_fact hp
  in
    (hpl, pure_pred::pfl)
  end
  handle HOL_ERR _ => (hp::hpl, pfl);


(* list_dest_star
   Deconstructs a (star) conjunction of heap conditions.
   Splits the conjuncts between heap conditions and pure facts.
 *)
fun list_dest_star c =
  let fun rec_dest hpl pfl c =
    let
      val (nc1, nc2) = dest_star c
      val (hpl1, pfl1) = rec_dest hpl pfl nc1
      val (hpl2, pfl2) = rec_dest hpl1 pfl1 nc2
    in
      (hpl2, pfl2)
    end
    handle HOL_ERR _ => sort_heap_pred c hpl pfl
  in
    rec_dest ([]:term list) ([]:term list) c
  end;

(* [dest_heap_condition]
  Deconstructs a heap predicate. Needs to be provided a list of terms
  representing variables to avoid name collision
  Returns:
  - the list of existentially quantified variables
  - the list of heap pointers used in the heap predicates
  - the list of heap predicates
  - the list of pure facts *)
fun dest_heap_condition (varsl, c) =
  let
    val (ex_vl, c') = rename_dest_exists (varsl, c)
    val (hpl, pfl) = list_dest_star c'
  in
    (ex_vl, hpl, pfl)
  end;

(* [mk_heap_condition]
   Creates a heap condition of the form:
      (SEP_EXISTS x1...xn. H1 * ... Hk * &P1 * ... * &Pl)
   Parameters:
   - the list of existentially quantified variables
   - the list of heap predicates
   - the list of pure facts
 *)

fun mk_heap_condition (ex_vl, hpl, pfl) =
  let
    val c1 = list_mk_star hpl cfHeapsBaseSyntax.hprop_ty
    val hprop_pfl = List.map (fn x => mk_comb (set_sep_cond_hprop_tm, x)) pfl
    val c2 = list_mk_star (c1::hprop_pfl) cfHeapsBaseSyntax.hprop_ty
    val c3 = List.foldr mk_sep_exists c2 ex_vl
  in
    c3
  end;

(* [mk_post_condition]
   Creates a heap post condition.
   Parameters:
   - the optional postv value
   - the optional postv predicate
   - the optional poste value
   - the optional poste predicate
*)
fun mk_post_condition (postv_v, postv_pred, poste_v, poste_pred, postf_args, postf_pred, postd_io, postd_pred) =
  case (postv_v, postv_pred, poste_v, poste_pred, postf_args, postf_pred, postd_io, postd_pred) of
      (SOME postv_v, SOME postv_pred, NONE, NONE, NONE, NONE, NONE, NONE) => cfHeapsBaseSyntax.mk_postv (postv_v, postv_pred)
   |  (NONE, NONE, SOME poste_v, SOME poste_pred, NONE, NONE, NONE, NONE) => cfHeapsBaseSyntax.mk_poste (poste_v, poste_pred)
   |  (NONE, NONE, NONE, NONE, NONE, NONE, SOME postd_io, SOME postd_pred) => cfHeapsBaseSyntax.mk_postd (postd_io, postd_pred)
   |  (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred, NONE, NONE, NONE, NONE) =>
        cfHeapsBaseSyntax.mk_postve (postv_v, postv_pred, poste_v, poste_pred)
   |  (SOME postv_v, SOME postv_pred, NONE, NONE, NONE, NONE, SOME postd_io, SOME postd_pred) =>
        cfHeapsBaseSyntax.mk_postvd (postv_v, postv_pred, postd_io, postd_pred)
   |  (NONE, NONE, SOME poste_v, SOME poste_pred, NONE, NONE, SOME postd_io, SOME postd_pred) =>
        cfHeapsBaseSyntax.mk_posted (poste_v, poste_pred, postd_io, postd_pred)
   |  (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred, SOME postf_args, SOME postf_pred, SOME postd_io, SOME postd_pred) =>
        cfHeapsBaseSyntax.mk_post (postv_v, postv_pred, poste_v, poste_pred,
                                   postf_args, postf_pred, postd_io, postd_pred)
   (* TODO: add postf *)
   | _  => raise (ERR "mk_heap_post_condition" "Not valid parameters")

(******** Get the post-condition given by the app specification ***********)
(* [find_spec]
   Finds a proper specification for the application in the goal.
   The code has been taken from xspec (cfTactics) *)
fun find_spec g =
  let
    val (asl, w) = (xapp_prepare_goal g) |> #1 |> List.hd
    val (ffi_ty, f) = (goal_app_infos w)
  in
  case xspec_in_asl f asl of
      SOME (k, a) =>
      (print
      ("Using a " ^ (spec_kind_toString k) ^
       " specification from the assumptions\n");
      cf_spec ffi_ty k (ASSUME a))
   | NONE =>
       case xspec_in_db f of
          SOME (thy, name, k, thm) =>
          (print ("Using " ^ (spec_kind_toString k) ^
          " specification " ^ name ^
          " from theory " ^ thy ^ "\n");
          cf_spec ffi_ty k thm)
       | NONE =>
          raise ERR "find_spec" ("Could not find a specification for " ^
                             fst (dest_const f))
  end;

(* [rename_dest_foralls]
   Removes the forall operators from a term. Renames the  bound
   variables so that they are fresh regarding a given list
   of assumptions *)
fun rename_dest_foralls (asl, spec) =
  let
    val fvl = free_varsl asl
    fun rec_remove fvl spec =
      if not (is_forall spec) then (([]:term list), spec)
      else
      let
        val (x, spec') = dest_forall spec
        val x' = variant fvl x
        val subst_spec = Term.subst [x |-> x'] spec'
        val (xl, fspec) = rec_remove (x'::fvl) subst_spec
      in
        (x'::xl, fspec)
      end
  in
    rec_remove fvl spec
  end;

(* [xlet_find_spec]
   Find the app specification to use given a goal to prove *)
fun xlet_find_spec g =
  let
    (* Find the specification *)
    val dummy_spec = `POSTv (v:v). &T`
    val g' = xlet dummy_spec g |> #1 |> List.hd
  in
    SPEC_ALL(find_spec g')
  end;

(* [xlet_dest_app_spec] *)
fun xlet_dest_app_spec asl let_pre specH =
  let
      (* Get the parameters and pre/post-conditions written in the specification *)
      val (_, noquant_spec_tm) = rename_dest_foralls ((let_pre::asl), (concl specH))
      val impsl_spec = list_dest dest_imp noquant_spec_tm
      val app_asl = List.take (impsl_spec, (List.length impsl_spec)-1)
      val app_spec = List.last impsl_spec
  in
      (app_asl, app_spec)
  end;


(* [xlet_subst_parameters]
   The app specification is supposed to be quantified over all the "unknwn" variables.
*)
fun xlet_subst_parameters env app_info asl let_pre app_spec  =
  let
      (* Retrieve the list of free variables *)
      val fvset = FVL ((concl app_spec)::app_info::let_pre::asl) empty_varset
      val fvl = HOLset.listItems fvset

      (* Retrieve the type variables *)
      val asl_atoms = all_atomsl (app_info::let_pre::asl) empty_tmset
      val asl_typevars =
          HOLset.foldr (fn (a, ts) => HOLset.addList(ts, type_vars (type_of a)))
                       (HOLset.empty Type.compare) asl_atoms
      val spec_atoms = all_atoms (concl (DISCH_ALL app_spec))
      val spec_typevars =
          HOLset.foldr (fn (a, ts) => HOLset.addList(ts, type_vars (type_of a)))
                       (HOLset.empty Type.compare) spec_atoms
      val redundant_typevars = HOLset.intersection(asl_typevars, spec_typevars)
                                                       |> HOLset.listItems
      val all_typevars = HOLset.union(asl_typevars, spec_typevars)
                                         |> HOLset.listItems
      val all_typevars_names = HOLset.addList (HOLset.empty String.compare,
                                                   List.map dest_vartype all_typevars)
      val red_typevars_names = List.map dest_vartype redundant_typevars

      (* Substitute the redundant type variables *)
      fun rename_typevar varnames name i =
        let
            val name' = name ^(Int.toString i)
        in
            if HOLset.member(varnames, name') then rename_typevar varnames name (i+1)
            else name'
        end
      fun rename_typevars varnames (vn::vars) =
        let
            val (varnames', pairs) = rename_typevars varnames vars
            val vn' = rename_typevar varnames' vn 0
            val varnames'' = HOLset.add(varnames', vn')
        in
            (varnames'', (vn, vn')::pairs)
        end
        | rename_typevars varnames [] = (varnames, [])
      val (_, new_type_names) = rename_typevars all_typevars_names red_typevars_names
      val type_subst = List.map (fn (x, y) => (mk_vartype x |-> mk_vartype y)) new_type_names
      val app_spec = Thm.INST_TYPE type_subst app_spec

      (* Find the parameters given to the function *)
      val (app_info', parameters) = dest_comb app_info
      val (params_expr_list, _) = listSyntax.dest_list parameters
      val params_tm_list = List.map (get_value env) params_expr_list

      (* NOT SURE if proper way: rewrite the values to prevent conflicts with the
         parameters found by xapp_spec *)
      val asl_thms = List.map ASSUME asl
      val params_tm_list = List.map (fn x => QCONV (SIMP_CONV bool_ss asl_thms) x
                                |> concl |> dest_eq |> snd) params_tm_list
      (*************************************************)

      (* Find the app variable *)
      val (app_info'', app_var) = dest_comb app_info'
      val app_value = get_value env app_var

      (* TODO: evaluate the app variable *)

      (* Find the ffi variable *)
      val ffi = dest_comb app_info'' |> snd

      (* Get the parameters written in the specification *)
      val inst_app_spec = RENAME_SPEC_ALL fvl app_spec
      val app_spec1 = concl inst_app_spec |> list_dest dest_imp |> List.last
      val app_spec2 = dest_comb app_spec1 |> fst
      val app_spec3 = dest_comb app_spec2 |> fst
      val (app_spec4, spec_parameters) = dest_comb app_spec3
      val (spec_params_tm_list, _) = listSyntax.dest_list spec_parameters

      (* Get the app variable written in the specification *)
      val (app_spec5, spec_app_var) = dest_comb app_spec4
      val (spec_params_tm_list, params_tm_list) =
          if is_var spec_app_var then
              (spec_app_var::spec_params_tm_list, app_value::params_tm_list)
          else (spec_params_tm_list, params_tm_list)

      (* And the ffi variable written in the specification *)
      val spec_ffi = dest_comb app_spec5 |> snd

      (* Match the parameters *)
      fun create_subst l1 l2 =
        (case (l1, l2) of
             (e1::l1', e2::l2') =>
             let
                 val tys1 = match_type (type_of e1) (type_of e2)
                 val (tms2, tys2) = create_subst l1' l2'
             in
                 ((e1, e2)::tms2, List.concat [tys1, tys2])
             end
           | ([], []) => ([], [])
           | _ => failwith "create_subst")
      val (tm_pairs, ty_subst) = create_subst (spec_ffi::spec_params_tm_list) (ffi::params_tm_list)
      val params_subst = List.map (fn (x, y) => (Term.inst ty_subst x |-> y)) tm_pairs

      (* Perform the substitution in the app specification *)
      val typed_app_spec = Thm.INST_TYPE ty_subst inst_app_spec
      val subst_app_spec = Thm.INST params_subst typed_app_spec
  in
      subst_app_spec
  end;

(*
   Analyses a theorem of the form:
   HPROP_INJ A B EQ
   Returns: (A, B, EQ)
*)
val (hprop_inj_tm,mk_hprop_inj,dest_hprop_inj,is_hprop_inj) = syntax_fns3 "cfLetAuto" "HPROP_INJ"
fun convert_extract_thm th =
    let
        val c = strip_forall (concl th) |> snd
    in
    dest_hprop_inj c
    end
    handle HOL_ERR _ => raise (ERR "hprop_extract_pattern"
                ("not a valid heap extraction theorem: " ^(thm_to_string th)))

(* Some auxiliary definitions for the match_heap_conditions function *)
fun mk_sep_imp_hprop (t1,t2) =
  mk_sep_imp (assert (equal cfHeapsBaseSyntax.hprop_ty o type_of) t1,t2)

(* Convert equations to substitutions *)
fun convert_eqs_to_subs eqs =
  let
      val eql = list_dest dest_conj eqs |> List.map dest_eq
      val tsubst = List.map (fn (x, y) => (x |-> y)) eql
  in
      tsubst
  end;

(*
   Rename the variable(s) introduced by POSTv/POSTe/POST.
   Use the name of the shallow embedding if it is a variable, or its type if it is
   a constant.
*)
val type_to_name =
    [
      (equal intSyntax.int_ty, "iv"),
      (equal numSyntax.num, "nv"),
      (equal bool, "bv"),
      (equal oneSyntax.one_ty, "uv"),
      (listSyntax.is_list_type, "lv"),
      (equal stringSyntax.string_ty, "sv"),
      (equal mlstringSyntax.mlstring_ty, "sv"),
      (can dom_rng, "fv"),
      (K true, "v")
    ];

val x = mk_var("x",alpha);
val RI = mk_var("RI",alpha --> semanticPrimitivesSyntax.v_ty --> bool)

fun rename_post_variables ri_thms asl post_condition =
  let
      val ri_terms = mapfilter (snd o dest_comb o concl) ri_thms
      val ri_set = HOLset.fromList Term.compare ri_terms
      val varset = FVL asl empty_varset
      val varsl = HOLset.listItems varset
      val (v_o, vpred_o, e_o, epred_o, f_o, fpred_o, d_o, dpred_o) = dest_post_condition post_condition

      (* Rename the exception *)
      val (e_o', epred_o') =
          case (e_o, epred_o) of
              (SOME e, SOME pred) =>
              let
                  val n_e = ivariant varsl e
                  val n_pred = Term.subst [e |-> n_e] pred
              in
                  (SOME n_e, SOME n_pred)
              end
            | _ => (e_o, epred_o)

      (* Rename the ressource *)
      val (v_o', vpred_o') =
          case (v_o, vpred_o) of
              (SOME v, SOME H) =>
              (let
                  (* Find the predicate giving information about the type of v *)
                  val preds = list_dest dest_star H
                  val pat = mk_cond_hprop(list_mk_comb(RI,[x,v]))
                  val sgl = HOLset.add (empty_varset, v)
                  fun get_shallow p =
                    let
                        val (tms, tys) = match_terml [] sgl pat p
                        val (tms', tys') = norm_subst ((tms, empty_varset), (tys, []))
                        val apply_subst = (Term.subst tms') o (Term.inst tys')
                        val RI = apply_subst RI
                        val shallow = apply_subst x
                    in
                        (* Check that RI is a refinement invariant *)
                        if HOLset.member (ri_set, RI) then shallow else failwith ""
                    end
                  val shallow = tryfind get_shallow preds
              in
                  case is_var shallow of
                      true =>
                      let
                          val x_name = (fst o dest_var) shallow
                          val v_name = String.concat [x_name, "v"]
                          val n_var = ivariant varsl (mk_var(v_name, semanticPrimitivesSyntax.v_ty))
                          val n_pred = Term.subst [v |-> n_var] H
                      in
                          (SOME n_var, SOME n_pred)
                      end
                    | false =>
                      let
                          val s_t = type_of shallow
                          fun name_from_type (t,_) = t s_t
                          val v_name = #2 (Lib.first name_from_type type_to_name)
                          val n_var = ivariant varsl (mk_var(v_name, semanticPrimitivesSyntax.v_ty))
                          val n_pred = Term.subst [v |-> n_var] H
                      in
                          (SOME n_var, SOME n_pred)
                      end
              end
               handle HOL_ERR _ =>
                      let
                          val n_var = ivariant varsl v
                          val n_pred = Term.subst [v |-> n_var] H
                      in
                          (SOME n_var, SOME n_pred)
                      end)

            | _ => (v_o, vpred_o)

      (* Rename ffi-divergence *)
      val (f_o', fpred_o') =
          case (f_o,fpred_o) of
              (SOME f, SOME pred) =>
              let
                 fun ivariants varsl [] = []
                   | ivariants varsl (h::r) =
                     ivariant varsl h::ivariants (h::varsl) r
                  val n_f = ivariants varsl f
                  val n_pred = Term.subst (map2 (curry op |->) f n_f) pred
              in
                  (SOME n_f, SOME n_pred)
              end
            | x => x

      (* Rename the io lazy list *)
      val (d_o', dpred_o') =
          case (d_o, dpred_o) of
              (SOME d, SOME pred) =>
              let
                  val n_d = ivariant varsl d
                  val n_pred = Term.subst [d |-> n_d] pred
              in
                  (SOME n_d, SOME n_pred)
              end
            | _ => (d_o, dpred_o)
  in
      mk_post_condition (v_o', vpred_o', e_o', epred_o', f_o', fpred_o', d_o', dpred_o')
  end
  handle HOL_ERR _ => raise (ERR "rename_post_variables" "");

(************************************************************************************
 *
 * Match heap preconditions
 *
 ************************************************************************************)
(* [match_heap_conditions] *)
fun match_heap_conditions hcond sub_hcond =
  let
      val extract_thms = get_frame_thms ()

      (* Retrieve the extraction triplets *)
      val extr_triplets = mapfilter convert_extract_thm extract_thms
      val extr_pairs = List.map (fn (c, w, r) => (mk_sep_imp_hprop (c, w), r)) extr_triplets

      (* Decompose the heap conditions *)
      val hc_hpl = list_dest dest_star hcond |> List.filter (fn x => not (same_const cfHeapsBaseSyntax.emp_tm x))
      val shc_hpl = list_dest dest_star sub_hcond |>
                              List.filter (fn x => (not (same_const cfHeapsBaseSyntax.emp_tm x)))

      (* Perfom the matching *)
      fun try_match obj pat_pair =
        let
            val tsubst = match_term (fst pat_pair) obj |> fst
            val eqs = Term.subst tsubst (snd pat_pair)
        in
            convert_eqs_to_subs eqs
        end

      (* Interior loop *)
      fun match_loop_int h1 [] = raise ERR "match_loop_int" "Empty"
        | match_loop_int h1 (h2::hl2) =
          if h1 ~~ h2 then ([], hl2)
          else
              (let
                  val result = tryfind (try_match (mk_sep_imp_hprop (h1, h2))) extr_pairs
              in
                  (result, hl2)
              end
               handle HOL_ERR _ =>
                      let val (results, hl2') = match_loop_int h1 hl2 in (results, h2::hl2') end)

      (* Exterior loop *)
      fun match_loop_ext (h1::hl1) hl2 =
        (let
            val (res1, hl2') = match_loop_int h1 hl2
            val (results, hl1', hl2'') = match_loop_ext hl1 hl2'
        in
            (List.revAppend(res1, results), hl1', hl2'')
        end
         handle HOL_ERR _ =>
                let val (results, hl1', hl2') = match_loop_ext hl1 hl2 in (results, h1::hl1', hl2') end)
        | match_loop_ext [] hl2 = ([], [], hl2)
  in
      match_loop_ext hc_hpl shc_hpl
  end;

(* [match_hconds] : match two pre-conditions in order to extract a frame *)
fun match_hconds rewrite_thms avoid_tms let_pre app_spec =
  let
      val sset = get_default_simpset ()

      val app_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
                          dest_comb |> fst |> dest_comb |> snd
      val rw_app_pre = (QCONV (SIMP_CONV sset rewrite_thms) app_pre |> concl |> dest_eq |> snd)
      val rw_let_pre = (QCONV (SIMP_CONV sset rewrite_thms) let_pre |> concl |> dest_eq |> snd)
      val (substsl, _, _) = match_heap_conditions let_pre app_pre
      val filt_subst =
          List.filter (fn {redex = x, residue = y} => not (HOLset.member (avoid_tms, x))) substsl
      val used_subst = List.map (fn {redex = x, residue = y} => x) filt_subst

      (* Instantiate the variables *)
      val (vars_subst, terms_subst) =
          List.partition (fn {redex = x, residue = y} => is_var x) filt_subst
      val app_spec1 = Thm.INST vars_subst app_spec

      (* And add the other equalities as new hypotheses *)
      val terms_eqs = List.map (fn {redex = x, residue = y} => mk_eq(x, y)) terms_subst
      val app_spec2 = List.foldr (fn (eq, th) => ADD_ASSUM eq th) app_spec1 terms_eqs
      val app_spec3 = List.foldr (fn (eq, th) => DISCH eq th) app_spec2 terms_eqs
      val app_spec4 = PURE_REWRITE_RULE [AND_IMP_INTRO] app_spec3
  in
      (app_spec4, used_subst)
  end;

(*************** Heuristics *****************************************)

(* For each hypothesis of the app spec the list of possible substitutions
   which make it match with one of the assumptions
*)
fun find_possible_instantiations tmsl0 tmsl1  =
  let
      (* Retrieve the known variables *)
      val knwn_vars = FVL tmsl0 empty_varset

      (* Retrieve the type variables present in tmsl0 *)
      val atoms = all_atomsl tmsl0 empty_tmset
      val knwn_typevarset =
          HOLset.foldr (fn (a, ts) => HOLset.addList(ts, type_vars (type_of a)))
                       (HOLset.empty Type.compare) atoms
      val knwn_typevars = HOLset.listItems knwn_typevarset

      (* Match every term of tmsl0 against every term of tmsl1 *)
      (*val tms_net = List.foldr (fn (x, net) => Net.insert (x, x) net) Net.empty tmsl0 *)
      fun find_insts tm =
        let
            val pos_matches = (*Net.match tm tms_net*) tmsl0
            fun match_aux a =
                let
                    val ((tms, tm_id), (tys, ty_id)) =
                        raw_match knwn_typevars knwn_vars tm a ([], [])
                    val tms' = tms @ (List.map (fn x => x |-> x)
                        (HOLset.listItems (HOLset.difference (tm_id, knwn_vars))))
                    val ty_id_set = HOLset.fromList Type.compare ty_id
                    val tys' = tys @ (List.map (fn x => x |-> x)
                        (HOLset.listItems (HOLset.difference (ty_id_set, knwn_typevarset))))
                in
                    (tms', tys')
                end
            val pos_insts = mapfilter match_aux pos_matches
        in
            pos_insts
        end

      val pos_insts = List.map find_insts tmsl1
  in
      pos_insts
  end;

fun find_possible_instantiations_from_eqs tmsl0 tmsl1 = let
    (* Retrieve the known variables *)
    val knwn_vars = FVL tmsl0 empty_varset

    (* Retrieve the type variables present in tmsl0 *)
    val atoms = all_atomsl tmsl0 empty_tmset
    val knwn_typevarset =
        HOLset.foldr (fn (a, ts) => HOLset.addList(ts, type_vars (type_of a)))
                     (HOLset.empty Type.compare) atoms
    val knwn_typevars = HOLset.listItems knwn_typevarset

    (* Find valid equalities *)
    fun is_not_schematic tm = let
        val vs = free_vars tm
    in not(List.exists (fn x => not(HOLset.member(knwn_vars,x))) vs) end

    fun find_eq tm =
      if (not o is_eq) tm then failwith ""
      else let
          val (tm1,tm2) = dest_eq tm
      in if is_not_schematic tm1 then (tm1,tm2)
         else if is_not_schematic tm2 then (tm2, tm1)
         else failwith ""
      end
    val eqs = mapfilter find_eq tmsl1

    (* Match the equalities *)
    fun find_insts (tm1,tm2) = let
        val ((tms, tm_id), (tys, ty_id)) =
            raw_match knwn_typevars knwn_vars tm2 tm1  ([], [])
        val tms' = tms @ (List.map (fn x => x |-> x)
                         (HOLset.listItems (HOLset.difference (tm_id, knwn_vars))))
        val ty_id_set = HOLset.fromList Type.compare ty_id
        val tys' = tys @ (List.map (fn x => x |-> x)
                         (HOLset.listItems (HOLset.difference (ty_id_set, knwn_typevarset))))
      in
          [(tms', tys')]
      end

      val pos_insts = mapfilter find_insts eqs |> List.filter (not o List.null)
in
    pos_insts
end;

fun find_possible_instantiations_from_spec asl context_pre app_spec = let
    (* Retrieve the list of hypothesis to satisfy *)
    val app_spec_hyps = concl app_spec |> dest_imp |> fst |> list_dest dest_conj

    (* Retrieve the precondition given by the spec *)
    val spec_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
                          dest_comb |> fst |> dest_comb |> snd

    (* Compare the two pre-conditions *)
    val (_, context_pres, spec_pres) = match_heap_conditions context_pre spec_pre

    (* Compute the instantiations *)
    val tmsl0 = append asl context_pres
    val tmsl1 = append app_spec_hyps spec_pres
    val pos_insts = (find_possible_instantiations tmsl0 tmsl1)
                    @(find_possible_instantiations_from_eqs tmsl0 tmsl1)
in pos_insts end;

(* Add a substitution to a map of substitutions *)
(* TODO: would be more efficient to compute the compatibility between all
   possible substs, then find a subset of substs satisfying a given criteria,
   and finally compute the union of those substs *)
fun add_tms ({redex = (x:term), residue = y}, tm_map) =
  case Redblackmap.peek (tm_map, x) of
      SOME y' => (case Term.compare (y,y') of EQUAL => tm_map | _ => failwith "")
    | NONE => Redblackmap.insert (tm_map, x, y)

fun add_tmsl tmsl tm_map = List.foldr add_tms tm_map tmsl

fun add_tys ({redex = x, residue = y}, ty_map) =
  case Redblackmap.peek (ty_map, x) of
      SOME y' => (case Type.compare (y,y') of EQUAL => ty_map | _ => failwith "")
    | NONE => Redblackmap.insert (ty_map, x, y)

fun add_tysl tysl ty_map = List.foldr add_tys ty_map tysl

(* Find an instantiation such that all the hypothesis are satisfied
   - not efficient *)
fun instantiations_union pos_insts =
  let
      (* Recursive (and exhaustive) search *)
      fun rec_search (tm_map, ty_map) (insts::pos_insts) =
        let
            fun rec_search_i (inst::insts) pos_insts =
              (let
                  val tm_map' = add_tmsl (fst inst) tm_map
                  val ty_map' = add_tysl (snd inst) ty_map
              in
                  rec_search (tm_map', ty_map') pos_insts
              end
              handle HOL_ERR _ => rec_search_i insts pos_insts)
              | rec_search_i [] pos_insts = failwith ""
        in
            rec_search_i insts pos_insts
        end
        | rec_search (tm_map, ty_map) [] = (tm_map, ty_map)

      val (tm_inst, ty_inst) = rec_search (Redblackmap.mkDict Term.compare,
                                        Redblackmap.mkDict Type.compare)
                                       pos_insts

      (* Convert the maps to proper substitutions *)
      val tm_subst = List.map (op |->) (Redblackmap.listItems tm_inst)
      val ty_subst = List.map (op |->) (Redblackmap.listItems ty_inst)

  in
      (tm_subst, ty_subst)
  end;

(* A heuristic solver based on unification - succeeds only if it can find a
   substitution such that all the hypothesis are satisfied *)
fun unification_solver asl context_pre app_spec =
  let
      val pos_insts = find_possible_instantiations_from_spec asl context_pre app_spec
      val (tm_subst, ty_subst) = instantiations_union pos_insts
  in
      (tm_subst, ty_subst)
  end;

(* Find an instantiation by giving priority to the substitutions instantiating
   the highest number of variables, and by possibly ignoring some hypothesis *)
fun max_instantiations_union pos_insts =
  let
      val filt_pos_insts = List.filter (not o List.null) pos_insts
      fun compare_f insts1 insts2 =
        (List.length (List.hd insts1 |> fst)) >
        (List.length (List.hd insts2 |> fst))
      val sorted_pos_insts = sort compare_f filt_pos_insts

      (* Recursive search *)
      fun add_pos_inst (tm_map, ty_map) (inst::insts) = ((let
          val tm_map' = add_tmsl (fst inst) tm_map
          val ty_map' = add_tysl (snd inst) ty_map
      in (tm_map', ty_map') end)
      handle HOL_ERR _ => add_pos_inst (tm_map, ty_map) insts)
        | add_pos_inst (tm_map, ty_map) [] = (tm_map, ty_map)

      fun rec_search maps pos_insts =
        List.foldl (fn (i,m) => add_pos_inst m i) maps pos_insts

      val (tm_inst, ty_inst) = rec_search (Redblackmap.mkDict Term.compare,
                                        Redblackmap.mkDict Type.compare)
                                          sorted_pos_insts

      (* Convert the maps to proper substitutions *)
      val tm_subst = List.map (op |->) (Redblackmap.listItems tm_inst)
      val ty_subst = List.map (op |->) (Redblackmap.listItems ty_inst)
  in
      (tm_subst, ty_subst)
  end;

(* A solver which performs unification on as much hypothesis as possible -
   succeeds if it can find a substitution such that all variables and types are
   instantiated *)
fun unif_heuristic_solver asl context_pre app_spec =
  let
      val pos_insts = find_possible_instantiations_from_spec asl context_pre app_spec
      val (tms, tys) = max_instantiations_union pos_insts

      (* Check that all unknown variables are instantiated *)
      val knwn_vars = FVL asl empty_varset
      val unkwn_vars = HOLset.difference (
                        FVL [concl app_spec |> dest_imp |> fst] empty_varset,
                        knwn_vars)
  in
      if HOLset.numItems unkwn_vars = List.length tms then (tms, tys)
      else raise (ERR "default_heuristic_solver"
                      "unable to find an instantiation of all the variables")
  end;

fun default_heuristic_solver asl context_pre app_spec =
  let val inst = unification_solver asl context_pre app_spec in inst end
  handle HOL_ERR _ => unif_heuristic_solver asl context_pre app_spec;

val heuristic_solver = ref default_heuristic_solver;

fun set_heuristic_solver solver = heuristic_solver := solver;
fun get_heuristic_solver () = !heuristic_solver;

val USE_HEURISTICS = ref true;
fun use_heuristics b = USE_HEURISTICS := true;
fun using_heuristics () = !USE_HEURISTICS;

(************* Some simplification functions ************************)

(* [find_equality_types]
   Search through the assumptions list for possible equality types, prove that those are indeed equality types if possible *)
fun find_equality_types asl eqTypeThms =
  let
      (* Get the potential equalityTypes *)
      fun get_pot_EqualityType t =
        let
            val (t', xv) = dest_comb t
            val eqType = dest_comb t' |> fst
        in
            if type_of xv = semanticPrimitivesSyntax.v_ty then eqType else failwith ""
        end
      val pot_eqTypes = mapfilter get_pot_EqualityType asl

      (* Get the assumptions of the form `EqualityType A` *)
      fun isEqTypeHyp a =
        (same_const ((fst o dest_comb) a) ml_translatorSyntax.EqualityType handle HOL_ERR _ => false)
      val eqType_asl = List.filter isEqTypeHyp asl
      val eqType_asl_thms = List.map ASSUME eqType_asl

      (* thmsNet : links every theorem conclusion to the theorem itself *)
      val eqTypeThms = List.map SPEC_ALL eqTypeThms
      fun get_last_concl th = concl th |> list_dest dest_imp |> List.last |> dest_comb |> snd
      val thmsNet = List.foldr (fn (th, n) =>
                                   let val th_concl = get_last_concl th in
                                       Net.insert (th_concl, (th_concl, th)) n end) Net.empty (eqType_asl_thms @ eqTypeThms)

      (* For each potential equality type P present in the asl, try to prove that P is an EqualityType *)
      val thmsNet = ref thmsNet
      fun prove_EqualityType t =
        let
            (* Match t with the theorems net *)
            val concl_matches = Net.match t (!thmsNet)

            (* Finish the matching and perform the instantiations *)
            fun match_th_concl (cth, th) =
              let
                  (* Perform the matching *)
                  val (tms, tys) = Term.match_term cth t
                  val (tms, tys) = Term.norm_subst ((tms, empty_tmset), (tys, []))
                  val th' = Thm.INST tms (Thm.INST_TYPE tys th)
              in
                  th'
              end
            val matched_thms = mapfilter match_th_concl concl_matches

            (* Transform each theorem into a list of subgoals *)
            fun get_subgoal_list th =
              let
                  val imps = (list_dest dest_imp (concl th))
                  val subgoals = List.take (imps, List.length imps - 1)
                  val intermEqTypes = List.map (snd o dest_comb) subgoals
              in
                  (intermEqTypes, th)
              end
            val sg_thms = mapfilter get_subgoal_list matched_thms

            (* For each theorem, try to prove the subgoals *)
            fun prove_subgoals (intermEqTypes, th) =
              let
                  val proved_subgoals = List.map prove_EqualityType intermEqTypes
                  val proved_thm = List.foldl (fn (hyp, th) => MP th hyp) th proved_subgoals
                  val proved_thm = assert (List.null o hyp) proved_thm
              in
                  proved_thm
              end
            val proved_thm = tryfind prove_subgoals sg_thms
        in
            thmsNet := Net.insert (concl proved_thm, (concl proved_thm, proved_thm)) (!thmsNet);
            proved_thm
        end
      val final_thms = mapfilter prove_EqualityType pot_eqTypes

      (* Remove redundancy in the theorems *)
      val final_thms_map = List.foldr (fn (th, m) => Redblackmap.insert (m, concl th, th)) (Redblackmap.mkDict Term.compare) final_thms
  in
      List.map snd (Redblackmap.listItems final_thms_map)
  end;


(* [inst_refinement_invariants] : find instantiations for the quantified refinement invariants *)
fun inst_refinement_invariants eq_type_thms asl app_spec =
  let
      (* Retrieve information from the assumptions list *)
      fun is_eqtype_clause t =
        let
            val P = dest_comb (concl t) |> fst
        in
            same_const ml_translatorSyntax.EqualityType P
        end
        handle HOL_ERR _ => false

      val eq_types_thmsl = List.concat (List.map (fn th =>
                        List.filter is_eqtype_clause (CONJUNCTS th))
                                eq_type_thms)
      val eq_types_set = HOLset.addList (empty_tmset, List.map
                        (fn x => snd(dest_comb (concl x))) eq_types_thmsl)

      (* Find the known and unknown variables *)
      val knwn_vars = FVL asl empty_varset
      val unkwn_vars = HOLset.difference (FVL [concl app_spec] empty_varset, knwn_vars)

      (* Destroy the conjunctions in the hypotheses of the app specification *)
      val clauses = concl app_spec |> dest_imp |> fst |> list_dest dest_conj

      (* Find the polymorphic types *)
      fun extract_eqtype t =
        let
      val A = ml_translatorSyntax.dest_EqualityType t
            val ty = type_of A |> dest_type |> snd |> List.hd
        in
            if not(HOLset.member (knwn_vars, A)) then (A, ty) else failwith ""
        end
      val eq_types = mapfilter extract_eqtype clauses

      (* Find the hyp clauses giving information about those types *)
      fun find_related A ty =
        let
            val x = mk_var("x", ty)
            val mterm = mk_comb(mk_comb(A, x), mk_var("v",semanticPrimitivesSyntax.v_ty))
            val matchf = match_terml [] (HOLset.add (empty_varset, A)) mterm
            val related_clauses = mapfilter (fn t => (matchf t; t)) clauses
        in
            related_clauses
        end
      val related_clauses = List.map (fn (A, ty) => (A, find_related A ty)) eq_types

      (* Compare with the assumptions list *)
      fun match_with_asl A clause =
        let
            val varsl =
                List.filter (fn v => HOLset.member(knwn_vars, v)) (free_vars clause)
            val varset = HOLset.addList(empty_varset, varsl)
            val masl = mapfilter (Term.match_terml [] varset clause) asl
        in
            masl
        end
      val substs = List.map (fn (A, clauses) =>
                                (A, List.concat(List.map
                                  (match_with_asl A) clauses))) related_clauses

      (* Analyse the possible substitutions and instantiate if possible *)
      fun keep_substitution A (tm_subst, ty_subst) =
        let
            val A' = Term.subst tm_subst (Term.inst ty_subst A)
        in
            HOLset.member (eq_types_set, A')
        end
      val filt_substs_ll =
          List.map (fn (A, sl) => List.filter (keep_substitution A) sl) substs
      val filt_substs = List.concat filt_substs_ll

      (* Perform the substitutions *)
      fun perform_subst ((tm_subst, ty_subst), spec) =
        Thm.INST tm_subst (Thm.INST_TYPE ty_subst spec)
      val app_spec' = List.foldr perform_subst app_spec filt_substs

      (* For every A, remove the `EqualityType A` predicate if A is instantiated *)
      val conv_f = SIMP_CONV bool_ss eq_types_thmsl
      val app_spec'' = CONV_RULE (RATOR_CONV (RAND_CONV conv_f)) app_spec'
  in
      app_spec''
  end
  handle HOL_ERR _ => app_spec;

(* [simplify_spec] : simplify an app specification by instantiating the quantified variables
   in a safe manner *)
fun simplify_spec let_pre asl app_spec =
  let
      val sset = get_default_simpset()
      val asl_thms = List.map ASSUME asl

      val knwn_vars = FVL (let_pre::asl) empty_varset

      (* Perform the simplification *)
      val compos_conv = (INTRO_REWRITE_CONV (get_intro_rewrite_thms()) asl)
                         THENC (SIMP_CONV sset asl_thms)
                         THENC (SIMP_CONV (list_ss ++ SQI_ss) [])
                         THENC (ELIM_UNKWN_CONV knwn_vars)
      val (app_spec1, changed) =
          (CONV_RULE (CHANGED_CONV (RATOR_CONV (RAND_CONV compos_conv))) app_spec, true)
    handle HOL_ERR _ => (app_spec, false)

      (* Perform substitutions *)
      val conjuncts = (concl app_spec1 |> dest_imp |> fst |> list_dest dest_conj
                       handle HOL_ERR _ => [])
      val equalities = mapfilter (fn x => dest_eq x) conjuncts
      fun can_be_subst x y =
        is_var x andalso not(HOLset.member(knwn_vars, x))
        andalso not (List.exists (aconv x) (free_vars y))
      fun subst_f (x, y) =
        (if can_be_subst x y then (x |-> y)
         else if can_be_subst y x then (y |-> x)
         else failwith "")
      val instList = mapfilter subst_f equalities
      val app_spec2 = Thm.INST instList app_spec1
  in
      if changed orelse not (List.null instList)
      then app_spec2
      else raise (ERR "simplify_spec" "unchanged")
  end;

exception XLET_ERR of string * string * thm;

fun XLET_ERR_MSG (fname, msg, app_spec) =
  (fname ^": " ^msg ^"\n Using specification: \n" ^(thm_to_string app_spec));

(* Quantifies the variables in app_spec and returns a XLET_ERR -
   use this function to prevent the ffi to be quantified: prettier and performance
   is not an issue... *)
fun generate_XLET_ERR fname msg asl let_pre app_spec =
  let
      val knwn_vars = FVL (let_pre::asl) empty_varset
      val unkwn_vars = HOLset.difference(FVL [concl app_spec] empty_varset, knwn_vars)
      val quant_app_spec = GENL (HOLset.listItems unkwn_vars) app_spec
  in
      XLET_ERR (fname, msg, quant_app_spec)
  end;

(* [xlet_simp_spec] *)
fun xlet_simp_spec asl app_info let_pre app_spec =
  let
      val rw_thms = get_rewrite_thms ()
      val sset = get_default_simpset ()

      (* Perform rewrites and simplifications on the assumptions *)
      val rw_asl = CONV_ASSUM list_ss (markerTheory.Abbrev_def::((get_retract_thms()) @ rw_thms)) asl
      val rw_asl_concl = List.map concl rw_asl
      (* Find the refinement invariants used in the assumptions *)
      val local_equality_types_thms = find_equality_types rw_asl_concl (get_equality_type_thms())
      val rw_asl = local_equality_types_thms @ rw_asl
      val rw_asl_concl = (List.map concl local_equality_types_thms) @ rw_asl_concl
      val all_rw_thms = List.revAppend (rw_asl, rw_thms)

      (* Add the rewritten asl in the assumptions of the app spec *)
      val app_spec1 = List.foldr (fn (x, y) => ADD_ASSUM x y) app_spec rw_asl_concl

      (* Replace the ==> by /\ in the app specification, remove the quantifiers *)
      val app_spec2 = PURE_REWRITE_RULE [AND_IMP_INTRO] app_spec1
      val norm_app_spec = SPEC_ALL app_spec2

      (* Get rid of the constants *)
      val constElimConv = (SIMP_CONV sset (AND_IMP_INTRO::((get_expand_thms())@rw_thms)))
                              THENC (SIMP_CONV sset (AND_IMP_INTRO::((get_retract_thms())@rw_thms)))
      val norm_app_spec' = CONV_RULE (RATOR_CONV constElimConv) norm_app_spec

      (* Recursive modifications *)
      fun rec_simplify used_subst app_spec =
        let
            (* Match the pre-conditions *)
            val (app_spec1, new_subst) = match_hconds all_rw_thms used_subst let_pre app_spec

            (* Update the used substitutions (prevents loopings) *)
            val used_subst' = HOLset.addList (used_subst, new_subst)

            (* Instantiate the refinement invariants and get rid of the constants *)
            val app_spec2 = inst_refinement_invariants local_equality_types_thms (let_pre::rw_asl_concl) app_spec1
                                                 |> CONV_RULE (RATOR_CONV constElimConv)

            (* Perform the simplification *)
            val app_spec3 = (rec_simplify used_subst'
                        (simplify_spec let_pre rw_asl_concl app_spec2) handle HOL_ERR _ => app_spec2)
        in
            app_spec3
        end

      val simp_app_spec = rec_simplify empty_tmset norm_app_spec'
                                       (* Get rid of T ==> _ and some other expressions *)
                |> PURE_REWRITE_RULE [ConseqConvTheory.IMP_CLAUSES_TX]

      (* Check that all variables have been instantiated *)
      fun all_instantiated asl let_pre app_info app_spec =
        let
            val app_spec_fvs = FVL [concl app_spec] empty_varset
            val original_fvs = FVL (app_info::let_pre::asl) empty_varset
        in
            HOLset.isSubset (app_spec_fvs, original_fvs)
        end

      (* Use heuristics if necessary *)
      (* val (ext_asl, context_pre, app_spec) = ((rw_asl_concl@asl),let_pre,simp_app_spec) *)
      fun heuristic_inst ext_asl context_pre app_spec =
        if not(all_instantiated ext_asl let_pre app_info app_spec)
           andalso using_heuristics()
        then
            let
                val _ = print "xlet_auto : using heuristics\n"

                val solver = get_heuristic_solver()
                val (tm_subst, ty_subst) = solver ext_asl context_pre app_spec
                val ty_app_spec = Thm.INST_TYPE ty_subst app_spec
                val tm_subst' =
                    List.map (fn {redex = x, residue = y} =>
                                 (Term.inst ty_subst x |-> y)) tm_subst
                val subst_app_spec = Thm.INST tm_subst' ty_app_spec
            in
                subst_app_spec
            end handle HOL_ERR _ => app_spec
        else app_spec (* instantiation is re-tested below *)

      (* To perform the matching, we give both the rewritten asl and the original asl to match against- in some situations, it might be too expensive *)
      val hsimp_app_spec = heuristic_inst (rw_asl_concl@asl) let_pre simp_app_spec

       (* Modify the post-condition inside the app_spec *)
      fun simplify_app_post app_spec =
        let
            val b_conv =
                (* Start by simplifying what can be *)
                (SIMP_CONV sset all_rw_thms)
                (* Expand and retract the refinement invariants *)
                THENC (SIMP_CONV bool_ss (get_expand_thms()))
                THENC (SIMP_CONV bool_ss (get_retract_thms()))

            val f_conv = if is_imp (concl app_spec) then RAND_CONV (RAND_CONV b_conv)
                         else RAND_CONV b_conv
        in
            CONV_RULE f_conv app_spec
        end

      (* Modify the hypothesis inside the app_spec *)
      fun simplify_app_hypothesis app_spec =
        if (is_imp (concl app_spec)) then
            let
                val b_conv = (SIMP_CONV sset all_rw_thms)
                                 THENC (PURE_REWRITE_CONV (get_retract_thms()))
                val f_conv = RATOR_CONV (RAND_CONV b_conv)
            in
                CONV_RULE f_conv app_spec
            end
        else app_spec

      val hsimp_app_spec' = (simplify_app_hypothesis o simplify_app_post) hsimp_app_spec

      (* Compute the frame *)
      val app_pre = concl (UNDISCH_ALL hsimp_app_spec') |> list_dest dest_imp |> List.last |>
                          dest_comb |> fst |> dest_comb |> snd
      val rw_app_pre = (QCONV (SIMP_CONV list_ss all_rw_thms) app_pre |> concl |> dest_eq |> snd)
      val rw_let_pre = (QCONV (SIMP_CONV list_ss all_rw_thms) let_pre |> concl |> dest_eq |> snd)
      val (vars_subst, frame_hpl, rest) = match_heap_conditions let_pre app_pre
      val () = if List.null rest then () else
               raise (generate_XLET_ERR "xlet_simp_spec" "cannot extract the frame" asl let_pre hsimp_app_spec')

      (* Replace the assumptions in the spec by the original asl *)
      val final_spec = MP_ASSUML ((List.map ASSUME asl)@rw_asl) hsimp_app_spec'

      (* For debugging purposes *)
      val _ = debug_set_app_spec final_spec

      (* Have all the variables been instantiated? *)
      val _ = if all_instantiated asl let_pre app_info final_spec then final_spec
              else raise (generate_XLET_ERR "xlet_simp_spec" "cannot instantiate the variables" asl let_pre final_spec)

      (*
      val _ = if (not o HOLset.isSubset) (FVL [concl final_spec] empty_varset,
                                          FVL (app_info::let_pre::asl) empty_varset)
              then raise (generate_XLET_ERR "xlet_simp_spec" "cannot instantiate the variables" asl let_pre final_spec)
              else ()
      *)
  in
      (final_spec, frame_hpl)
  end
  handle HOL_ERR{message = msg, origin_function = fname,
                 origin_structure  = sname} => raise (ERR "xlet_simp_spec" msg);

(* [xlet_mk_post_conditions] *)
fun xlet_mk_post_condition asl frame_hpl app_spec =
  let
      (* Find the currently free variables (to prevent name conflicts) *)
      val fvl = FVL asl empty_varset |> HOLset.listItems

      (* Retrieve the post_condition *)
      val app_post = concl (UNDISCH_ALL app_spec) |> dest_comb |> snd

      (* Decompose the app post-condition *)
      val (post_postv_vo, post_postv_po, post_poste_vo, post_poste_po,
           post_postf_argso, post_postf_po, post_postd_ioo, post_postd_po) =
          rename_dest_post (fvl, app_post)

      (* Filter the heap predicates from the let pre-condition *)
      fun mk_post_cond_aux pred_opt =
        (case pred_opt of
             SOME pred =>
             let
                 val (post_ex_vl, post_hpl, post_pfl) =
                     dest_heap_condition (fvl, pred)
                 val let_heap_condition =
                     mk_heap_condition ((List.concat [post_ex_vl]),
                                        (List.concat [post_hpl, frame_hpl]),
                                        (List.concat [post_pfl]))
             in
                 SOME let_heap_condition
             end
           | NONE => NONE)
      val post_postv_po' = mk_post_cond_aux post_postv_po
      val post_poste_po' = mk_post_cond_aux post_poste_po
      val post_postf_po' = mk_post_cond_aux post_postf_po

      (* Construct the post-condition *)
      val let_heap_condition =
          mk_post_condition (post_postv_vo, post_postv_po', post_poste_vo, post_poste_po',
                             post_postf_argso, post_postf_po', post_postd_ioo, post_postd_po)

      (* Retrieve the assumptions defining equalities between variables and terms *)
      fun transf_vt_eq a =
          let
              val (lt, rt) = dest_eq a
          in
              if is_var lt andalso (not o is_var) rt then ASSUME (mk_eq (rt, lt))
              else if is_var rt andalso (not o is_var) lt then ASSUME a
              else failwith "transf_vt_eq"
          end
      val eqs = mapfilter transf_vt_eq asl

      (* Perform rewrites on the post-conditions *)
      val rw_conv = (PURE_REWRITE_CONV (get_retract_thms())) THENC
                                (PURE_REWRITE_CONV eqs)
      val rw_let_heap_condition =
          (rw_conv let_heap_condition |> concl |> dest_eq |> snd
           handle UNCHANGED => let_heap_condition)
  in
      let_heap_condition
  end;

(* [xlet_app_auto] *)
fun xlet_app_auto app_info env let_pre opt_app_spec (g as (asl, w)) =
  let
      (* Find the specification  *)
      val app_spec =
          case opt_app_spec of
              SOME spec => spec
            | NONE => xlet_find_spec g |> DISCH_ALL |> GEN_ALL

      (* Substitute the paramaters *)
      val subst_app_spec =
          xlet_subst_parameters env app_info asl let_pre app_spec

      (* Perform the matching *)
      val (final_app_spec, frame_hpl) =
          xlet_simp_spec asl app_info let_pre subst_app_spec

      (* Compute the let post-condition *)
      val let_post_condition =
          xlet_mk_post_condition ((concl final_app_spec)::(frame_hpl@asl))
                                 frame_hpl final_app_spec

      (* Rename the variable introduced by POSTv/POSTe/POST *)
      val ri_thms = get_equality_type_thms ()
      val let_post_condition' =
          rename_post_variables ri_thms asl let_post_condition
  in
      (* Return *)
      print ("Post condition: " ^(term_to_string let_post_condition') ^ "\n");
      (final_app_spec, let_post_condition')
  end;

(* [xlet_expr_con]
   Construct the post-condition for an expression of the form:
   `let x = Conv ... ... in ... end` *)
fun xlet_expr_con let_expr_args asl w env pre post =
  let
      (* Create a new variable for the Postv abstraction *)
      val nvar_ = mk_var("v",semanticPrimitivesSyntax.v_ty)
      val varsl = free_varsl (w :: asl)
      val nvar = variant varsl nvar_

      (* Compute the value of the expression *)
      val xx = let_expr_args
      val con_name = el 1 xx
      val con_args = el 2 xx
      val (con_args_exprs, _) = listSyntax.dest_list con_args
      val con_args_tms = List.map (get_value env) con_args_exprs
      val con_args_list_tm = listSyntax.mk_list (con_args_tms,
                                                 semanticPrimitivesSyntax.v_ty)
      val con_tm = mk_build_conv (mk_sem_env_c env,con_name,con_args_list_tm)
                                 |> cfTacticsLib.reduce_conv |> concl |> rhs
                                 |> optionSyntax.dest_some

      (* Build the post-condition *)
      val nvar_eqn = mk_eq(nvar,con_tm)
      val post_condition =
        cfHeapsBaseSyntax.mk_postv(nvar,helperLib.mk_star(mk_cond_hprop nvar_eqn,pre))

      (* Apply some conversions to the post condition *)

      (* Retrieve the assumptions defining equalities between variables and terms *)
      fun transf_vt_eq a =
        let
            val (lt, rt) = dest_eq a
        in
            if is_var lt andalso (not o is_var) rt then ASSUME (mk_eq (rt, lt))
            else if is_var rt andalso (not o is_var) lt then ASSUME a
            else failwith "transf_vt_eq"
        end
      val eqs = mapfilter transf_vt_eq asl

      (* Perform rewrites on the post-conditions *)
      val rw_conv = (PURE_REWRITE_CONV (get_retract_thms())) THENC
                                        (PURE_REWRITE_CONV eqs)
      val rw_post_condition =
          (rw_conv post_condition |> concl |> dest_eq |> snd
           handle UNCHANGED => post_condition)
  in
      rw_post_condition
  end;

(* [xlet_expr_auto] *)
fun xlet_expr_auto let_expr env pre post (g as (asl, w))   =
  let
      val (let_expr_op, let_expr_args) = strip_comb let_expr
  in
      if same_const let_expr_op cf_con_tm then
        let
            val let_post_condition =
                xlet_expr_con let_expr_args asl w env pre post

            (* Rename the variable introduced by POSTv/POSTe/POST *)
            val ri_thms = get_equality_type_thms ()
            val let_post_condition' =
                rename_post_variables ri_thms asl let_post_condition
        in
            (* Return *)
            print ("Post condition: " ^(term_to_string let_post_condition') ^ "\n");
            let_post_condition'
        end
      else
          raise (ERR "xlet_expr_auto" "expression not handled")
  end;

(* Auxiliary functions to test that a given term is of the given form (the standard is_cf_con,... don't work in the cases I need them) *)
fun is_cf_con_aux let_expr =
  same_const cf_con_tm (let_expr |> strip_comb |> #1)
  handle HOL_ERR _ => false;

fun is_cf_app_aux let_expr =
  same_const cf_app_tm (let_expr |> strip_comb |> #1)
  handle HOL_ERR _ => false;

(* [xlet_find_auto] *)
fun xlet_find_auto (g as (asl, w)) =
  if is_cf_let w then
      let
          val (goal_op, goal_args) = strip_comb w
          val let_expr = List.nth (goal_args, 1)
          val env = List.nth (goal_args, 3)
          val pre = List.nth (goal_args, 4)
          val post = List.nth (goal_args, 5)
      in
          if is_cf_con_aux let_expr then
              xlet_expr_auto let_expr env pre post g
          else if is_cf_app_aux let_expr then
              let val (_, c) =
                      xlet_app_auto let_expr env pre NONE g
              in c end
              handle XLET_ERR err =>
                     (print (XLET_ERR_MSG err);
                      raise ERR "xlet_find_auto" "unable to find the post-condition")
          else
              raise (ERR "xlet_find_auto" "Not handled yet")
      end
  else
      raise (ERR "xlet_find_auto" "Not a cf_let expression");

(* [xlet_auto_spec] *)
fun xlet_auto_spec (opt_spec : thm option) (g as (asl, w)) =
   if is_cf_let w then
      let
          val (goal_op, goal_args) = strip_comb w
          val let_expr = List.nth (goal_args, 1)
          val env = List.nth (goal_args, 3)
          val pre = List.nth (goal_args, 4)
          val post = List.nth (goal_args, 5)
      in
          if is_cf_con_aux let_expr then
              let val c = xlet_expr_auto let_expr env pre post g
              in xlet `^c` g end
          else if is_cf_app_aux let_expr then
              let val (H, c) =
                      xlet_app_auto let_expr env pre opt_spec g
              in (xlet `^c` THEN_LT (NTH_GOAL (xapp_spec H) 1)) g end
              handle XLET_ERR err =>
                     (print (XLET_ERR_MSG err);
                      raise ERR "xlet_auto" "unable to find the post-condition")
          else
              raise (ERR "xlet_auto_spec" "Not handled yet")
      end
  else
      raise (ERR "xlet_auto_spec" "Not a cf_let expression");

(* [xlet_auto] *)
fun xlet_auto (g as (asl, w)) =
  xlet_auto_spec NONE g
  handle HOL_ERR {origin_structure = _, origin_function = fname, message = msg}
         => raise (ERR "xlet_auto" msg);

end

(******** DEBUG ********)

(*
val (g as (asl, w)) = top_goal();
val (goal_op, goal_args) = strip_comb w;
val let_expr = List.nth (goal_args, 1);
val env = List.nth (goal_args, 3);
val pre = List.nth (goal_args, 4);
val post = List.nth (goal_args, 5);
val (app_info, env, let_pre) = (let_expr, env, pre);

(* Find the specification *)
val app_spec = xlet_find_spec g |> DISCH_ALL |> GEN_ALL;

(* Apply the parameters given in the let expression *)
val subst_app_spec = xlet_subst_parameters env app_info asl let_pre app_spec;
val app_spec = subst_app_spec

(* Perform the simplification (xlet_simp) *)
xlet_simp_spec asl app_info let_pre app_spec

val (final_app_spec, frame_hpl) =
          xlet_simp_spec asl app_info let_pre subst_app_spec

xlet_app_auto app_info env let_pre NONE g
xlet_auto g


val (postv_v, postv_pred, poste_v, poste_pred) = (post_postv_vo, post_postv_po', post_poste_vo, post_poste_po');
val (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred) = (postv_v, postv_pred, poste_v, poste_pred);
val (postv_v, postv_abs, poste_v, poste_abs) = (postv_v, postv_pred, poste_v, poste_pred);
*)
