(*
  Translate the backend from flatLang to target code.
*)
Theory from_flatProg[no_sig_docs]
Ancestors
  ml_translator from_closProg flat_to_clos[qualified]
  clos_mti[qualified] clos_number[qualified]
  clos_known[qualified] clos_call[qualified]
  clos_annotate[qualified]
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = translation_extends "from_closProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_flatProg");

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
(* flat_to_clos                                                              *)
(* ------------------------------------------------------------------------- *)

val r = translate flat_to_closTheory.dest_pat_pmatch;
val r = translate flat_to_closTheory.arg1_pmatch;
val r = translate flat_to_closTheory.arg2_pmatch;
val r = translate flat_to_closTheory.dest_nop_def;

val _ = patternMatchesSyntax.temp_enable_pmatch();

val _ = translate flat_to_closTheory.CopyWord_checked_def;

Theorem flat_to_clos_copyword_checked_total[local]:
  ∀trace source_array alloc_new.
    flat_to_clos_copyword_checked_side trace source_array alloc_new ⇔ T
Proof
  rpt gen_tac
  \\ Cases_on `alloc_new`
  \\ simp [DB.fetch "-" "flat_to_clos_copyword_checked_side_def"]
QED

val _ = update_precondition flat_to_clos_copyword_checked_total;

val r = translate flat_to_closTheory.compile_def;

val r = translate flat_to_closTheory.compile_decs_def;

val r = translate (EVAL “clos_interpreter”)

val r = translate clos_interpTheory.can_interpret_op_pmatch;
val _ = temp_delsimps ["NORMEQ_CONV"]

val r = translate (clos_interpTheory.check_size_op_pmatch |> RW [GSYM sub_check_def]);

val r = translate clos_interpTheory.to_constant_op_pmatch;

fun one_line_ify_mutrec def = let
  val ths = CONJUNCTS def |> map SPEC_ALL
  val xs = ths |> map (fn th => (th,(th |> concl |> dest_eq |> fst |> repeat rator
                                        |> dest_const |> fst)))
  fun nub [] = []
    | nub (x::xs) = x :: nub (filter (fn y => y <> x) xs)
  val ys = nub (map snd xs)
  in ys |> map (fn y => map fst (filter (fn (_,x) => x = y) xs) |> LIST_CONJ
                        |> DefnBase.one_line_ify NONE |> GEN_ALL) |> LIST_CONJ
  end

Theorem can_interpret_ind = (DefnBase.lookup_indn “can_interpret” |> valOf |> fst);
Theorem check_size_ind = (DefnBase.lookup_indn “check_size” |> valOf |> fst);

val res = translate_no_ind $ one_line_ify_mutrec (clos_interpTheory.check_size_def |> RW [GSYM sub_check_def]);

Theorem clos_interp_check_size_ind[local]:
  clos_interp_check_size_ind
Proof
  once_rewrite_tac [fetch "-" "clos_interp_check_size_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, sub_check_def]
QED

val res = clos_interp_check_size_ind |> update_precondition;

val r = translate clos_interpTheory.insert_interp_def;

val r = translate flat_to_closTheory.inc_compile_decs_def;

val _ = (length (hyp r) = 0)
        orelse failwith "Unproved side condition: flat_to_clos_inc_compile_decs";

val r = translate clos_interpTheory.clos_interpreter_def;
val r = translate clos_interpTheory.compile_init_def;
val r = translate closLangTheory.has_install_def;
val r = translate clos_interpTheory.attach_interpreter_def;
val r = translate flat_to_closTheory.compile_prog_def;

val _ = (length (hyp r) = 0)
        orelse failwith "Unproved side condition: flat_to_clos_compile_prog";

(* ------------------------------------------------------------------------- *)
(* backend                                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = translate backendTheory.from_flat_def;

(* ------------------------------------------------------------------------- *)

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
