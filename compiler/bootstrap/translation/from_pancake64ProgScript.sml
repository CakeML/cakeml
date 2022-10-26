(*
  Translate the pan_to_target part of the 64-bit compiler.
*)

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory std_preludeTheory;
local open backendTheory in end

val _ = new_theory "from_pancake64Prog"

val _ = translation_extends "to_target64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake64Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

  val def = def |> RW (!extra_preprocessing)
                |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

open panLangTheory;

val _ = register_type “:64 panLang$exp”;

val _ = register_type “:64 panLang$prog”;

val _ = translate $ spec64 exp_ids_def;

open crepLangTheory;

val _ = register_type “:64 crepLang$exp”;

val _ = register_type “:64 crepLang$prog”;

val _ = translate $ spec64 var_cexp_def;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_decs_def;

val _ = translate $ spec64 nested_seq_def;

val lem = Q.prove(‘dimindex(:64) = 64’, EVAL_TAC);

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 stores_def;

val _ = translate $ spec64 store_globals_def;

val _ = translate $ spec64 load_globals_def;

val _ = translate $ spec64 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

val _ = translate $ spec64 seq_assoc_def;

val _ = translate $ spec64 seq_call_ret_def;

val _ = translate $ conv64 ret_to_tail_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ INST_TYPE[gamma|->“:64”] compile_prog_def;

open loopLangTheory;

val _ = register_type “:64 loopLang$exp”;

val _ = register_type “:64 loopLang$prog”;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_seq_def;

open loop_removeTheory;

val _ = translate $ INST_TYPE[alpha|->“:64”, beta|->“:64 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec64 comp_no_loop_def;

val _ = translate $ spec64 comp_with_loop_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec64 comp_exp_def;

val _ = translate $ spec64 find_reg_imm_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ spec64 compile_prog_def;

val _ = translate $ spec64 compile_def;

open pan_to_crepTheory;

val _ = translate $ spec64 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:64 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec64 comp_field_def;

val _ = translate $ spec64 exp_hdl_def;

val _ = register_type “:64 context”;

val _ = translate $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64”] compile_exp_def;

Definition testing_def:
  (compile _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile ctxt (Dec v e p) =
   let (es, sh) = compile_exp ctxt e;
       vmax = ctxt.vmax;
       nvars = GENLIST (λx. vmax + SUC x) (size_of_shape sh);
       nctxt = ctxt with  <|vars := ctxt.vars |+ (v, (sh, nvars));
                            vmax := ctxt.vmax + size_of_shape sh|> in
            if size_of_shape sh = LENGTH es
            then nested_decs nvars es (compile nctxt p)
            else Skip) (* /\
  (compile ctxt (Assign v e) =
   let (es, sh) = compile_exp ctxt e in
   case FLOOKUP ctxt.vars v of
    | SOME (vshp, ns) =>
      if LENGTH ns = LENGTH es
      then if distinct_lists ns (FLAT (MAP var_cexp es))
      then nested_seq (MAP2 Assign ns es)
      else let vmax = ctxt.vmax;
               temps = GENLIST (λx. vmax + SUC x) (LENGTH ns) in
           nested_decs temps es
                       (nested_seq (MAP2 Assign ns (MAP Var temps)))
      else Skip:'a crepLang$prog
    | NONE => Skip) /\
  (compile ctxt (Store ad v) =
   case compile_exp ctxt ad of
    | (e::es',sh') =>
       let (es,sh) = compile_exp ctxt v;
            adv = ctxt.vmax + 1;
            temps = GENLIST (λx. adv + SUC x) (size_of_shape sh) in
            if size_of_shape sh = LENGTH es
            then nested_decs (adv::temps) (e::es)
                 (nested_seq (stores (Var adv) (MAP Var temps) 0w))
            else Skip
    | (_,_) => Skip) /\
  (compile ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
    | (ad::ads, _), (e::es, _) => StoreByte ad e
    | _ => Skip) /\
  (compile ctxt (Return rt) =
   let (ces,sh) = compile_exp ctxt rt in
   if size_of_shape sh = 0 then Return (Const 0w)
   else case ces of
         | [] => Skip
         | e::es => if size_of_shape sh = 1 then (Return e) else
          let temps = GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape sh) in
           if size_of_shape sh = LENGTH (e::es)
           then Seq (nested_decs temps (e::es)
                                 (nested_seq (store_globals 0w (MAP Var temps)))) (Return (Const 0w))
        else Skip) /\
  (compile ctxt (Raise eid excp) =
    case FLOOKUP ctxt.eids eid of
    | SOME n =>
      let (ces,sh) = compile_exp ctxt excp;
          temps = GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape sh) in
       if size_of_shape sh = LENGTH ces
       then Seq (nested_decs temps ces (nested_seq (store_globals 0w (MAP Var temps))))
                (Raise n)
       else Skip
    | NONE => Skip) /\
  (compile ctxt (Seq p p') =
    Seq (compile ctxt p) (compile ctxt p')) /\
  (compile ctxt (If e p p') =
   case compile_exp ctxt e of
    | (ce::ces, _) =>
      If ce (compile ctxt p) (compile ctxt p')
    | _ => Skip) /\
  (compile ctxt (While e p) =
   case compile_exp ctxt e of
   | (ce::ces, _) =>
     While ce (compile ctxt p)
   | _ => Skip) /\
  (compile ctxt Break = Break) /\
  (compile ctxt Continue = Continue) /\
  (compile ctxt (Call rtyp e es) =
   let (cs, sh) = compile_exp ctxt e;
       cexps = MAP (compile_exp ctxt) es;
       args = FLAT (MAP FST cexps) in
    case cs of
    | ce::ces =>
     (case rtyp of
       | NONE => Call NONE ce args
       | SOME (rt, hdl) =>
         (case wrap_rt (FLOOKUP ctxt.vars rt) of
          | NONE =>
            (case hdl of
              | NONE => Call NONE ce args
              | SOME (eid, evar, p) =>
                (case FLOOKUP ctxt.eids eid of
                   | NONE => Call NONE ce args
                   | SOME neid =>
                     let comp_hdl = compile ctxt p;
                        hndlr = Seq (exp_hdl ctxt.vars evar) comp_hdl in
                     Call (SOME (NONE, Skip, (SOME (neid, hndlr)))) ce args))
          | SOME (sh, ns) =>
            (case hdl of
             | NONE => Call (SOME ((ret_var sh ns), (ret_hdl sh ns), NONE)) ce args
             | SOME (eid, evar, p) =>
                (case FLOOKUP ctxt.eids eid of
                  | NONE => Call (SOME ((ret_var sh ns), (ret_hdl sh ns), NONE)) ce args
                  | SOME neid =>
                    let comp_hdl = compile ctxt p;
                        hndlr = Seq (exp_hdl ctxt.vars evar) comp_hdl in
                      Call (SOME ((ret_var sh ns), (ret_hdl sh ns),
                              (SOME (neid, hndlr)))) ce args))))
    | [] => Skip) /\
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
   case (FLOOKUP ctxt.vars ptr1, FLOOKUP ctxt.vars len1,
         FLOOKUP ctxt.vars ptr2, FLOOKUP ctxt.vars len2) of
    | (SOME (One, pc::pcs), SOME (One, lc::lcs),
       SOME (One, pc'::pcs'), SOME (One, lc'::lcs')) => ExtCall f pc lc pc' lc'
    | _ => Skip) /\
  (compile ctxt Tick = Tick) *)
End



val _ = translate $ spec64 compile_def;

val _ = translate $ spec64 mk_ctxt_def;

(* compile, ^mk_ctxt *)
val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

(* ^panLang$exp_ids *)
val _ = translate $ get_eids_def;

(* comp_func, ^make_funcs, ^get_eids *)
val _ = translate $ spec64 compile_prog_def;

open loop_callTheory;

val _ = translate $ spec64 comp_def;

val loop_call_comp_side = Q.prove(
  ‘∀spt prog. (loop_call_comp_side spt prog) ⇔ T’,
  ho_match_mp_tac comp_ind
  \\ rw[]
  \\ simp[Once (fetch "-" "loop_call_comp_side_def")]
  \\ TRY (metis_tac []))
  |> update_precondition;

open loop_liveTheory;

val _ = translate $ spec64 vars_of_exp_def;

val res = translate $ spec64 shrink_def;

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC)
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD])
  |> update_precondition;

val _ = translate $ spec64 mark_all_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 optimise_def;

open crep_to_loopTheory;

val _ = translate $ spec64 prog_if_def;

(* ^prog_if *)
val _ = translate $ spec64 compile_exp_def;

(* ^compile_exp, ^loopLang$nested_seq *)
val _ = translate $ spec64 compile_def;

(* ^compile *)
val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

(* ^comp_func, ^make_funcs, ~loop_live$optimise *)
val _ = translate $ spec64 compile_prog_def;

open pan_to_wordTheory;

(*
   ^pan_simp$compile_prog, pan_to_crep$compile_prog, crep_to_loop$compile_prog,
   ^loop_to_word$compile
*)
val _ = translate $ spec64 compile_prog_def;

(*
open wordLangTheory;

val rws = Q.prove(`
  ($+ = λx y. x + y) ∧
  ($&& = λx y. x && y) ∧
  ($|| = λx y. x || y) ∧
  ($?? = λx y. x ?? y)`,
  fs[FUN_EQ_THM])

val _ = translate (word_op_def |> ONCE_REWRITE_RULE [rws,WORD_NOT_0] |> spec64 |> gconv)

val _ = translate (word_sh_def
  |> INST_TYPE [``:'a``|->``:64``]
  |> REWRITE_RULE [miscTheory.word_ror_eq_any_word64_ror]
  |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt] |> conv64)

open word_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

(* ^SmartSeq *)
val _ = translate $ spec64 Seq_assoc_def;

(* ^Seq_assoc *)
val _ = translate $ spec64 simp_if_def;

val _ = translate $ SIMP_RULE std_ss [lem] $ spec64 $ INST_TYPE[beta|->“:64 word”] const_fp_inst_cs_def;

val _ = translate $ spec64 strip_const_def;

(* ^strip_const, ^wordLang$word_op, ^wordLang$word_sh *)
val _ = translate $ spec64 const_fp_exp_def;

(* ^const_fp_inst_cs, ^const_fp_exp *)
val _ = translate $ spec64 const_fp_loop_def;

(* ^const_fp_loop *)
val _ = translate $ spec64 const_fp_def;

(* ^simp_if, ^const_fp *)
val _ = translate $ spec64 compile_exp_def;
*)

open word_to_wordTheory;

(* #word_simp$compile_exp *)
val _ = translate $ spec64 compile_single_def;

(* ^compile_single *)
val _ = translate $ spec64 full_compile_single_def;

(* ^full_compile_single *)
val _ = translate $ spec64 compile_def;

open backendTheory;

val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word64 list”,
                              gamma|->“:64”,
                              delta|->“:64”] attach_bitmaps_def;

(* attach_bitmaps *)
val _ = translate $ INST_TYPE[alpha|->“:64 word list”,
                              beta|->“:64”] from_lab_def;

(* from_lab *)
val _ = translate $ SIMP_RULE std_ss [dimword_def,lem,backend_commonTheory.word_shift_def]
                  $ SIMP_RULE std_ss [data_to_wordTheory.max_heap_limit_def]
                  $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64 word list”] from_stack_def;

(* from_stack *)
val _ = translate $ spec64 from_word_def;

open pan_to_targetTheory;

(* pan_to_word$compile_prog, ^word_to_word$compile, ^backend$from_word *)
val _ = translate $ spec64 compile_prog_def;
