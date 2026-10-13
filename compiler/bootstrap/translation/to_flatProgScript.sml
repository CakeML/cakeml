(*
  Translate backend phases up to and including flatLang.
*)
Theory to_flatProg[no_sig_docs]
Ancestors
  ml_translator decProg source_to_flat[qualified]
  source_to_source[qualified] source_lift_consts[qualified]
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = translation_extends "decProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_flatProg");

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

(* TODO:
 *   - This is a discrepancy between HOL's standard libraries and mllist.
 *     Probably the compiler should be using the mllist versions?
 *)
val res = translate EL;
val list_el_side = Q.prove(
  `!n xs. list_el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "list_el_side_def"]
  THEN fs[CONTAINER_def])
  |> update_precondition;

(* -- *)

val res = translate listTheory.REV_DEF;
val res = translate listTheory.TAKE_def;
val res = translate listTheory.DROP_def;

val res = translate sumTheory.ISL;
val res = translate sumTheory.ISR;

val res = translate source_to_flatTheory.alloc_tags1_def;
val res = translate (DefnBase.one_line_ify NONE namespaceTheory.nsMap_def);
val res = translate source_to_flatTheory.alloc_tags_def;
val res = translate source_to_flatTheory.alloc_env_ref_def;
val res = translate (source_to_flatTheory.glob_alloc_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

val res = translate source_to_flatTheory.compile_decs_def;
val res = translate source_to_flatTheory.compile_prog_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_flat_compile_prog";

(* ------------------------------------------------------------------------- *)
(* source_dce                                                                *)
(* ------------------------------------------------------------------------- *)

val res = translate source_dceTheory.open_free_dec_def;

Theorem IN_FDOM_FLOOKUP[local]:
  x ∈ FDOM f ⇔ IS_SOME (FLOOKUP f x)
Proof
  rw [FLOOKUP_DEF]
QED

val res = translate (source_dceTheory.is_used_def |> REWRITE_RULE [IN_FDOM_FLOOKUP]);

val res = translate source_dceTheory.add_name_def;

val res = translate (source_dceTheory.free_vars_def |> RW (!extra_preprocessing));

Theorem source_dce_free_vars_ind[local]:
  source_dce_free_vars_ind
Proof
  once_rewrite_tac [fetch "-" "source_dce_free_vars_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac source_dceTheory.free_vars_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs []
QED

val _ = source_dce_free_vars_ind |> update_precondition;

(* without the tuple patterns, which the translator cannot handle here *)
Theorem union_names_eq[local]:
  (union_names x y = (FUNION (FST x) (FST y), union_longs (SND x) (SND y))) ∧
  (union_longs (Names []) l = l) ∧
  (union_longs (Names ((mn,s)::xs)) l =
     union_longs (Names xs) (insert_mod l mn (union_names s (lookup_mod l mn))))
Proof
  PairCases_on ‘x’ \\ PairCases_on ‘y’ \\ simp [source_dceTheory.union_names_def]
QED

val res = translate_no_ind union_names_eq;

Theorem source_dce_union_names_ind[local]:
  source_dce_union_names_ind
Proof
  once_rewrite_tac [fetch "-" "source_dce_union_names_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac source_dceTheory.union_names_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = source_dce_union_names_ind |> update_precondition;

val res = translate source_dceTheory.update_names_def;

val res = translate source_dceTheory.can_remove_def;
val res = translate source_dceTheory.prune_pat_def;

Theorem source_dce_prune_pat_ind[local]:
  source_dce_prune_pat_ind
Proof
  once_rewrite_tac [fetch "-" "source_dce_prune_pat_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ qsuff_tac ‘(∀p used. P0 used p) ∧ ∀ps used. P1 used ps’
  >- metis_tac []
  \\ ho_match_mp_tac (TypeBase.induction_of “:ast$pat”)
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs []
QED

val _ = source_dce_prune_pat_ind |> update_precondition;

val res = translate source_dceTheory.prune_dec_def;
val res = translate source_dceTheory.strip_mod_def;

val res = translate source_dceTheory.dce_decs_def;

Theorem source_dce_dce_decs_ind[local]:
  source_dce_dce_decs_ind
Proof
  once_rewrite_tac [fetch "-" "source_dce_dce_decs_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac source_dceTheory.dce_decs_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs []
QED

val _ = source_dce_dce_decs_ind |> update_precondition;

val res = translate source_dceTheory.has_Denv_dec_def;

(* ------------------------------------------------------------------------- *)
(* source_lift_consts                                                        *)
(* ------------------------------------------------------------------------- *)

(* The translator supports finite maps only at the key types set up in
   decProg, so the helpers that are polymorphic in the key are translated
   at the key type the pass uses: mlstring. *)

val res = translate source_lift_constsTheory.delete_all_def;
val res = translate source_lift_constsTheory.bind_all_def;
val res = translate source_lift_constsTheory.rename_var_def;
val res = translate (FUPDATE_LIST_THM |> INST_TYPE [alpha |-> “:mlstring”]);

(* maps_disjoint compares finite maps, which the translator cannot do;
   it is implemented by a check over the underlying mlmap instead. *)

Definition mlmap_disjoint_def:
  mlmap_disjoint m1 m2 = mlmap$all (λk v. IS_NONE (mlmap$lookup m2 k)) m1
End

val mlmap_disjoint_v_thm = translate mlmap_disjoint_def;

Theorem mlmap_disjoint_thm[local]:
  mlmap$map_ok m1 ∧ mlmap$map_ok m2 ⇒
  (mlmap_disjoint m1 m2 ⇔
   source_lift_consts$maps_disjoint (mlmap$to_fmap m1) (mlmap$to_fmap m2))
Proof
  rw [mlmap_disjoint_def, mlmapTheory.all_thm, mlmapTheory.lookup_thm,
      source_lift_constsTheory.maps_disjoint_def,
      source_lift_constsTheory.str_empty_def, Once EQ_SYM_EQ,
      GSYM DRESTRICT_EQ_FEMPTY, IN_DISJOINT, FLOOKUP_DEF]
  \\ metis_tac []
QED

Theorem IMP_maps_disjoint_v[local]:
  (MAP_TYPE a UNIT_TYPE --> MAP_TYPE a b --> BOOL) mlmap_disjoint v ⇒
  (FMAP_TYPE cmp a UNIT_TYPE --> FMAP_TYPE cmp a b --> BOOL)
    source_lift_consts$maps_disjoint v
Proof
  rw [Arrow_def, AppReturns_def, MapProgTheory.FMAP_TYPE_def]
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac
  \\ gvs [mlmap_disjoint_thm]
  \\ metis_tac []
QED

val _ = add_user_proved_v_thm
  (MATCH_MP IMP_maps_disjoint_v
     (mlmap_disjoint_v_thm
      |> INST_TYPE [alpha |-> “:mlstring”, beta |-> “:unit”]
      |> INST [“a:mlstring -> v -> bool” |-> “STRING_TYPE”,
               “b:unit -> v -> bool” |-> “UNIT_TYPE”])
   |> INST [“cmp:mlstring -> mlstring -> ordering” |->
            “mlstring$fast_compare”]);

(* the translator expects the single lift_exp clause to have variable
   arguments *)

Theorem lift_exp_eq[local] =
  CONJ (DefnBase.one_line_ify NONE
          (CONJUNCT1 source_lift_constsTheory.lift_exp_def))
       (CONJUNCT2 source_lift_constsTheory.lift_exp_def);

val res = translate lift_exp_eq;

(* the translator's preprocessing turns λ(f,x,e). (f,x) into a case *)
Theorem case_triple_eq[local]:
  (λx. case x of (a,b,c) => (a,b)) = (λ(f,x,e). (f,x))
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

(* keeps the large case hypotheses out of the assumptions *)
Theorem source_lift_consts_lift_exp_ind[local]:
  source_lift_consts_lift_exp_ind
Proof
  once_rewrite_tac [fetch "-" "source_lift_consts_lift_exp_ind_def"]
  \\ rpt gen_tac
  \\ disch_then $ fn th =>
       ho_match_mp_tac source_lift_constsTheory.lift_exp_ind
       \\ rpt strip_tac
       \\ FIRST (map match_mp_tac (CONJUNCTS th))
  \\ rpt strip_tac
  \\ gvs [case_triple_eq]
QED

val _ = source_lift_consts_lift_exp_ind |> update_precondition;

val res = translate source_lift_constsTheory.compile_dec_def;

(* ------------------------------------------------------------------------- *)
(* source_to_source                                                          *)
(* ------------------------------------------------------------------------- *)

val res = translate source_to_sourceTheory.compile_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_source_compile";

val res = translate source_to_sourceTheory.inc_compile_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_source_inc_compile";

(* ------------------------------------------------------------------------- *)
(* sptree                                                                    *)
(* ------------------------------------------------------------------------- *)

val res = translate sptreeTheory.subspt_eq;

(* ------------------------------------------------------------------------- *)
(* flat_pattern                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = translate flatLangTheory.SmartIf_PMATCH
val _ = translate pattern_compTheory.is_True_def
val _ = translate pattern_compTheory.is_Any_def
val _ = translate pattern_compTheory.take_until_Any_def
val _ = translate pattern_compTheory.comp_def

val res = translate flat_patternTheory.enc_num_to_name_def;

val res = translate (flat_patternTheory.sum_string_ords_def |> RW [GSYM sub_check_def]);
val res = translate flat_patternTheory.dec_name_to_num_def;

val res = translate rich_listTheory.COUNT_LIST_compute;

val res = translate flat_patternTheory.compile_dec_def;

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

val res = translate flat_ticksTheory.remove_ticks_exp_def;
val res = translate flat_ticksTheory.remove_ticks_decs_def;

val res = translate source_to_flatTheory.compile_flat_def;

val res = translate source_to_flatTheory.compile_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_flat_compile";

val res = translate source_to_flatTheory.inc_compile_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_flat_inc_compile";

(* ------------------------------------------------------------------------- *)

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
