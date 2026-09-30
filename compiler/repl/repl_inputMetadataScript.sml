(*
  Concrete input metadata derived from the generated initialization program.
  These lookups identify the datatype family and reference slots; they do not
  by themselves prove constructor-signature closure or the joint certificate.
*)
Theory repl_inputMetadata
Ancestors
  astProg repl_init_types repl_inputInvariant envRel ml_prog primTypes
  infer_cv inferSound backend_cv
  typeSystem semanticPrimitives
Libs
  preamble cv_transLib ml_progLib[qualified] astSyntax[qualified]
  semanticPrimitivesSyntax[qualified]

(* Fail rather than silently omit any non-Dtype registration declaration. *)
val ast_type_names = ast_type_decs_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map (fn dec => dec |> astSyntax.dest_Dtype |> snd
       |> listSyntax.dest_list |> fst
       |> map (fn td => td |> pairSyntax.strip_pair |> el 2))
  |> List.concat;

val ast_type_lookups = map (fn name => EVAL
  ``nsLookup (FST repl_prog_types).inf_t (Long «Ast» (Short ^name))``)
  ast_type_names;

val ast_type_ids = ListPair.map (fn (name,th) => let
  val ty = th |> concl |> rand |> optionSyntax.dest_some
    |> pairSyntax.dest_pair |> snd
  val _ = match_term ``typeSystem$Tapp args ti`` ty
  in pairSyntax.mk_pair (name,rand ty) end)
  (ast_type_names,ast_type_lookups);

Definition repl_ast_type_ids_def:
  repl_ast_type_ids =
    ^(listSyntax.mk_list (ast_type_ids, ``:mlstring # num``))
End

Theorem repl_ast_type_lookups = LIST_CONJ ast_type_lookups;

Theorem repl_ast_registration_coverage =
  ``MAP FST repl_ast_type_ids =
    FLAT (MAP (\dec. case dec of
      Dtype locs tds => MAP (\(tvs,tn,ctors). tn) tds
    | _ => []) ast_type_decs)`` |> EVAL |> EQT_ELIM;

Theorem repl_ast_type_ids_distinct =
  ``ALL_DISTINCT (MAP SND repl_ast_type_ids)`` |> EVAL |> EQT_ELIM;

Theorem repl_ast_root_type_ids =
  ``ALOOKUP repl_ast_type_ids «dec» = SOME repl_dec_type_id``
  |> EVAL |> EQT_ELIM;

val option_type_lookup = EVAL
  ``nsLookup (FST repl_prog_types).inf_t (Short «option»)``;
val option_type = option_type_lookup |> concl |> rand
  |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd;
val _ = match_term ``typeSystem$Tapp args ti`` option_type;

Definition repl_option_type_id_def:
  (repl_option_type_id:num) = ^(rand option_type)
End

Theorem repl_option_type_lookup = option_type_lookup
  |> REWRITE_RULE [GSYM repl_option_type_id_def];

Definition repl_input_datatype_ids_def:
  repl_input_datatype_ids = set (MAP SND repl_ast_type_ids) UNION
    {Tbool_num; Tlist_num; repl_sum_type_id; repl_option_type_id}
End

(* Every family entry originates in a declaration, including empty types.
   Constructor lookups resolve its field types and runtime stamps. Closure is
   proved separately from allocation; these positive lookups cannot prove it. *)
val ast_type_groups = ast_type_decs_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map (fn dec => dec |> astSyntax.dest_Dtype |> snd
       |> listSyntax.dest_list |> fst)
  |> List.concat;

val prelude_type_groups = ast_prefix_prog_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> List.filter astSyntax.is_Dtype
  |> map (fn dec => dec |> astSyntax.dest_Dtype |> snd
       |> listSyntax.dest_list |> fst)
  |> List.concat
  |> List.filter (fn td => let
       val name = td |> pairSyntax.strip_pair |> el 2
       in aconv name ``«option»`` orelse aconv name ``«sum»`` end);
val _ = if length prelude_type_groups = 2 then ()
  else failwith "Expected exactly the option and sum prelude declarations";

val primitive_type_groups = prim_types_program_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> List.filter astSyntax.is_Dtype
  |> map (fn dec => dec |> astSyntax.dest_Dtype |> snd
       |> listSyntax.dest_list |> fst)
  |> List.concat;

val input_type_groups =
  map (fn td => (SOME ``«Ast»``,td)) ast_type_groups @
  map (fn td => (NONE,td)) (prelude_type_groups @ primitive_type_groups);

fun input_name NONE name = ``Short ^name : (mlstring,mlstring) id``
  | input_name (SOME mn) name = ``Long ^mn (Short ^name)``;

val input_ctor_type_facts = ref ([]:thm list);
val input_ctor_value_facts = ref ([]:thm list);
val input_catalogue_entries = map (fn (mn,td) => let
  val [tvs,tn,ctors] = pairSyntax.strip_pair td
  val type_id = EVAL
    ``nsLookup (ienv_to_tenv (FST repl_prog_types)).t ^(input_name mn tn)``
    |> concl |> rand |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
    |> rand
  val signatures = ctors |> listSyntax.dest_list |> fst
    |> map (fn ctor => let
      val (cn,fields) = pairSyntax.dest_pair ctor
      val name = input_name mn cn
      val type_th = EVAL
        ``nsLookup (ienv_to_tenv (FST repl_prog_types)).c ^name``
      val [params,field_types,ctor_type_id] = type_th |> concl |> rand
        |> optionSyntax.dest_some |> pairSyntax.strip_pair
      val value_th = EVAL ``nsLookup repl_prog_env.c ^name``
      val (arity,stamp) = value_th |> concl |> rand
        |> optionSyntax.dest_some |> pairSyntax.dest_pair
      val (stamp_name,stamp_num) = semanticPrimitivesSyntax.dest_TypeStamp stamp
      val _ = if aconv params tvs andalso aconv ctor_type_id type_id andalso
        aconv stamp_name cn andalso
        numSyntax.int_of_term arity = length (fst (listSyntax.dest_list fields))
        then () else failwith "Input constructor registration/lookup mismatch"
      val _ = input_ctor_type_facts := type_th :: !input_ctor_type_facts
      val _ = input_ctor_value_facts := value_th :: !input_ctor_value_facts
      in pairSyntax.list_mk_pair [cn,stamp_num,params,field_types] end)
  val signature_set = pred_setSyntax.prim_mk_set
    (signatures, ``:mlstring # num # mlstring list # typeSystem$t list``)
  in pairSyntax.mk_pair (type_id,signature_set) end) input_type_groups;

Definition repl_input_catalogue_entries_def:
  repl_input_catalogue_entries =
    ^(listSyntax.mk_list (input_catalogue_entries,
      ``:num # (mlstring # num # mlstring list # typeSystem$t list) set``))
End

Definition repl_input_catalogue_def:
  repl_input_catalogue = FEMPTY |++ repl_input_catalogue_entries
End

Theorem repl_input_constructor_types =
  LIST_CONJ (rev (!input_ctor_type_facts));
Theorem repl_input_constructor_values =
  LIST_CONJ (rev (!input_ctor_value_facts));

Theorem repl_input_catalogue_keys_distinct =
  ``ALL_DISTINCT (MAP FST repl_input_catalogue_entries)`` |> EVAL |> EQT_ELIM;

Theorem repl_input_catalogue_domain:
  FDOM repl_input_catalogue = repl_input_datatype_ids
Proof
  simp [repl_input_catalogue_def, FDOM_FUPDATE_LIST] >>
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  simp [repl_input_datatype_ids_def, repl_ast_type_ids_def,
    repl_sum_type_id_def, repl_option_type_id_def, Tbool_num_def,
    Tlist_num_def, LIST_TO_SET] >>
  SET_TAC []
QED

(* The callback slot is recorded but unused by the current REPL proof. *)
val input_slot_names_types =
  [(``Long «Repl» (Short «isEOF»)`` , ``Tbool``),
   (``Long «Repl» (Short «nextInput»)`` , ``repl_input_type``),
   (``Long «Repl» (Short «errorMessage»)`` , ``Tstring``),
   (``Long «Repl» (Short «exn»)`` , ``Texn``),
   (``Long «Repl» (Short «readNextString»)`` , ``Tfn (Ttup []) (Ttup [])``)];

val input_ref_rewrites = List.concat (map BODY_CONJUNCTS
  [repl_moduleProgTheory.isEOF_def, repl_moduleProgTheory.nextInput_def,
   repl_moduleProgTheory.errorMessage_def, repl_moduleProgTheory.exn_def,
   repl_moduleProgTheory.Repl_readNextString_v_def])
  @ [LENGTH] @ (DB.find "refs_def" |> map (#1 o #2));

val input_slot_facts = map (fn (name,ty) => let
  val type_th = EVAL
    ``nsLookup (ienv_to_tenv (FST repl_prog_types)).v ^name =
        SOME (0,Tref ^ty)`` |> EQT_ELIM
  val value_th = EVAL ``nsLookup repl_prog_env.v ^name``
    |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) input_ref_rewrites THENC EVAL))
  val (is_ref,loc) = value_th |> concl |> rand |> optionSyntax.dest_some
    |> semanticPrimitivesSyntax.dest_Loc
  val _ = if aconv is_ref T then () else failwith "Input slot is not a reference"
  in (pairSyntax.mk_pair (loc,ty),type_th,value_th) end)
  input_slot_names_types;

Definition repl_input_slot_entries_def:
  repl_input_slot_entries =
    ^(listSyntax.mk_list (map #1 input_slot_facts, ``:num # typeSystem$t``))
End

Definition repl_input_slots_def:
  repl_input_slots = FEMPTY |++ repl_input_slot_entries
End

Theorem repl_input_slot_types = LIST_CONJ (map #2 input_slot_facts);
Theorem repl_input_slot_values = LIST_CONJ (map #3 input_slot_facts);

Theorem repl_input_slot_locations_distinct =
  ``ALL_DISTINCT (MAP FST repl_input_slot_entries)`` |> EVAL |> EQT_ELIM;

Theorem repl_input_slot_types_closed =
  ``EVERY (\(loc,ty). check_freevars 0 [] ty) repl_input_slot_entries``
  |> EVAL |> EQT_ELIM;

(* Checked inference checkpoints for the actual initialization partitions. *)
val prefix_decs = ast_prefix_prog_def |> concl |> rand
  |> listSyntax.dest_list |> fst;
fun has_input_type dec =
  astSyntax.is_Dtype dec andalso
  (dec |> astSyntax.dest_Dtype |> snd |> listSyntax.dest_list |> fst
   |> List.exists (fn td => let
        val name = td |> pairSyntax.strip_pair |> el 2
        in aconv name ``«option»`` orelse aconv name ``«sum»`` end));
val (_,prelude_count) = List.foldl (fn (dec,(index,last_input)) =>
  (index+1,if has_input_type dec then index+1 else last_input))
  (0,0) prefix_decs;
val prelude_decs = List.take (prefix_decs,prelude_count);
val _ = if prelude_count > 0 andalso List.all astSyntax.is_Dtype prelude_decs
  then () else failwith "Expected an initial datatype-only prelude seed";

Definition repl_input_prelude_prog_def:
  repl_input_prelude_prog = ^(listSyntax.mk_list (prelude_decs, ``:ast$dec``))
End

Definition repl_input_basis_candle_prog_def:
  repl_input_basis_candle_prog =
    ^(listSyntax.mk_list (List.drop (prefix_decs,prelude_count), ``:ast$dec``))
End

Theorem repl_input_prefix_partition =
  ``ast_prefix_prog = repl_input_prelude_prog ++ repl_input_basis_candle_prog``
  |> PURE_REWRITE_CONV [ast_prefix_prog_def, repl_input_prelude_prog_def,
       repl_input_basis_candle_prog_def, APPEND, REFL_CLAUSE] |> EQT_ELIM;

(* Derive checked initialization stages from their inferred environments. *)
fun input_infer_stage name initial program = let
  val result = cv_eval ``infertype_prog_inc ^initial ^program``
  val success = result |> concl |> rand
  val _ = match_term ``M_success _`` success
  val types_tm = rand success
  val types_def = new_definition (name ^ "_def",
    mk_eq (mk_var (name,type_of types_tm),types_tm))
  val _ = computeLib.add_persistent_funs [name ^ "_def"]
  val types_const = types_def |> concl |> lhs
  val _ = save_thm (name ^ "_thm",result
    |> CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM types_def)))))
  val _ = cv_trans_deep_embedding EVAL types_def
  in types_const end;

val _ = cv_trans_deep_embedding EVAL repl_input_prelude_prog_def;
val _ = cv_trans_deep_embedding EVAL repl_input_basis_candle_prog_def;
val _ = cv_trans_deep_embedding EVAL ast_type_decs_def;
val _ = cv_trans_deep_embedding EVAL ast_pp_decs_def;
val _ = cv_trans_deep_embedding EVAL repl_moduleProgTheory.repl_suffix_def;

val prelude_types = input_infer_stage "repl_input_prelude_types"
  ``(infer$init_config,start_type_id)`` ``repl_input_prelude_prog``;
val before_ast_types = input_infer_stage "repl_input_before_ast_types"
  prelude_types ``repl_input_basis_candle_prog``;

val ast_types = input_infer_stage "repl_input_ast_types"
  before_ast_types ``ast_type_decs``;

val ast_module_types = input_infer_stage "repl_input_ast_module_types"
  before_ast_types ``[Dmod «Ast» (ast_type_decs ++ ast_pp_decs)]``;
val final_types = input_infer_stage "repl_input_final_types"
  ast_module_types ``repl_suffix``;

Theorem repl_input_stage_final_types:
  repl_input_final_types = repl_prog_types
Proof
  rewrite_tac [DB.fetch "repl_inputMetadata" "repl_input_final_types_def",
    repl_prog_types_def]
QED

(* Keep the local pretty-printer inference result for module exports. *)
val input_ast_pp_start = ast_types;
val input_ast_pp_initial = EVAL
  ``infer$init_infer_state <|next_id := SND ^input_ast_pp_start|>``
  |> concl |> rhs;
val input_ast_pp_inference = cv_eval
  ``infer_ds (FST ^input_ast_pp_start) ast_pp_decs ^input_ast_pp_initial``
  |> SIMP_RULE (srw_ss()) [infer_cvTheory.IMP_infer_d_pre,
       inferPropsTheory.t_wfs_FEMPTY];
val (input_ast_pp_result,input_ast_pp_state) = input_ast_pp_inference
  |> concl |> rhs |> pairSyntax.dest_pair;
val _ = if can (match_term ``M_success _``) input_ast_pp_result then ()
  else failwith "Expected successful inference of the actual Ast pretty-printers";
val input_ast_pp_local = rand input_ast_pp_result;

Definition input_ast_pp_ienv_def:
  input_ast_pp_ienv = ^input_ast_pp_local
End

Definition input_ast_pp_infer_state_def:
  input_ast_pp_infer_state = ^input_ast_pp_state
End

Theorem input_ast_pp_inference_thm = input_ast_pp_inference
  |> PURE_REWRITE_RULE [GSYM input_ast_pp_ienv_def, GSYM input_ast_pp_infer_state_def];

Definition input_ast_pp_tenv_def:
  input_ast_pp_tenv = ienv_to_tenv input_ast_pp_ienv
End

Theorem input_ast_pp_allocation_interval:
  set_ids (^input_ast_pp_initial).next_id input_ast_pp_infer_state.next_id = {}
Proof
  simp [input_ast_pp_infer_state_def]
QED


(* Syntax checks connect actual generated declarations to Prog execution. *)
Theorem repl_input_syntax_ok =
  cv_eval ``prog_syntax_ok repl_prog`` |> EQT_ELIM;

Theorem repl_input_prefix_syntax_ok:
  prog_syntax_ok ast_prefix_prog
Proof
  irule ml_progTheory.prog_syntax_ok_isPREFIX >>
  qexists_tac `repl_prog` >>
  rewrite_tac [repl_input_syntax_ok, rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `[Dmod «Ast» (ast_type_decs ++ ast_pp_decs)] ++ repl_suffix` >>
  rewrite_tac [repl_moduleProgTheory.repl_prog_partition,
    astProgTheory.ast_prog_partition, APPEND_ASSOC]
QED
