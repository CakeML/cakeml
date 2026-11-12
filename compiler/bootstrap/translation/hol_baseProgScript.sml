(*
  Translation of standard library functions
*)
Theory hol_baseProg
Ancestors
  ml_translator repl_init_envProg misc int_bitwise multiword byte
  sorting sptree grammar location errorLogMonad bitstring
Libs
  preamble ml_translatorLib MapProgLib

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];

val _ = translation_extends "repl_init_envProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val {Thy,Name,...} = dest_thy_const tm
  val def = DB.fetch Thy (Name ^ "_pmatch") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_def") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_DEF") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_thm") handle HOL_ERR _ =>
            DB.fetch Thy Name
  val insts = match_type (type_of (prim_mk_const {Thy = Thy, Name = Name}))
                         (type_of tm)
  in def |> INST_TYPE insts |> REWRITE_RULE (!extra_preprocessing)
         |> CONV_RULE (DEPTH_CONV BETA_CONV)
         |> REWRITE_RULE [NOT_NIL_AND_LEMMA] end;

val _ = find_def_for_const := def_of_const;
val _ = use_long_names := false;

(* ------------------------------------------------------------------------- *)
(* list and rich_list                                                        *)
(* ------------------------------------------------------------------------- *)

val _ = use_long_names := true;

(* TODO:
 *   - This is a discrepancy between HOL's standard libraries and mllist.
 *     Probably the compiler should be using the mllist versions?
 *)
val res = translate listTheory.EL;
val list_el_side = Q.prove(
  `!n xs. list_el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "list_el_side_def"]
  THEN fs[CONTAINER_def])
  |> update_precondition;

(* -- *)

val res = translate listTheory.REV_DEF;
val res = translate listTheory.TAKE_def;
val res = translate listTheory.DROP_def;

val r = translate_no_ind (INST_TYPE [beta |-> alpha] listTheory.LIST_TO_SET_DEF);

Theorem list_list_to_set_ind[local]:
  list_list_to_set_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "list_list_to_set_ind_def"]
  \\ rpt strip_tac
  \\ qid_spec_tac ‘v4’
  \\ Induct_on ‘v3’
  \\ rpt strip_tac
  \\ first_assum irule
  \\ gvs []
QED

val _ = list_list_to_set_ind |> update_precondition;

val _ = translate rich_listTheory.COUNT_LIST_AUX_def

val _ = translate rich_listTheory.COUNT_LIST_compute

val res = translate $ listTheory.OPT_MMAP_def;
val res = translate $ listTheory.dropWhile_def;

(* ------------------------------------------------------------------------- *)
(* alist, finite_map and misc                                                *)
(* ------------------------------------------------------------------------- *)

val _ = use_long_names := false;

(* Finite maps at the supported key types. *)

val _ = MapProgLib.add_fmap_for_cmp mlstringTheory.TotOrd_fast_compare;
val _ = MapProgLib.add_fmap_for_cmp mlintTheory.TotOrd_int_cmp;
val _ = MapProgLib.add_fmap_for_cmp miscTheory.TotOrd_num_cmp;

val RW = REWRITE_RULE;

val _ = translate (alistTheory.alist_to_fmap_def |> RW [GSYM miscTheory.fmap_update_def]
                                     |> INST_TYPE [alpha|->“:mlstring”]);

val _ = translate (alistTheory.alist_to_fmap_def |> RW [GSYM miscTheory.fmap_update_def]
                                     |> INST_TYPE [alpha|->“:int”]);

val _ = translate (alistTheory.alist_to_fmap_def |> RW [GSYM miscTheory.fmap_update_def]
                                     |> INST_TYPE [alpha|->“:num”]);

val _ = translate (miscTheory.fmap_update_def |> GSYM |> oneline
                                              |> INST_TYPE [alpha|->“:mlstring”]);

val _ = translate (miscTheory.fmap_update_def |> GSYM |> oneline
                                              |> INST_TYPE [alpha|->“:int”]);

val _ = translate (miscTheory.fmap_update_def |> GSYM |> oneline
                                              |> INST_TYPE [alpha|->“:num”]);

val _ = use_long_names := true;

val res = translate (finite_mapTheory.FUPDATE_LIST_THM |> INST_TYPE [alpha |-> “:mlstring”]);
val res = translate $ alistTheory.ADELKEY_def;

val r = translate miscTheory.make_even_def;

val res = translate_no_ind miscTheory.anub_def;

Theorem misc_anub_ind[local]:
  misc_anub_ind (:'a) (:'b)
Proof
  once_rewrite_tac [fetch "-" "misc_anub_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = misc_anub_ind |> update_precondition;

val _ = translate miscTheory.lookup_any_def;
val res = translate miscTheory.the_def;

(* ------------------------------------------------------------------------- *)
(* pair, sum and option                                                      *)
(* ------------------------------------------------------------------------- *)

val res = translate sumTheory.ISL;
val res = translate sumTheory.ISR;
val r = translate optionTheory.IS_NONE_DEF;
val _ = translate pairTheory.PAIR_MAP
val _ = translate optionTheory.OPTION_BIND_def;
val res = translate pairTheory.LEX_DEF;

(* ------------------------------------------------------------------------- *)
(* sptree                                                                    *)
(* ------------------------------------------------------------------------- *)

val r = translate sptreeTheory.list_to_num_set_def;
val res = translate sptreeTheory.subspt_eq;
val res = translate sptreeTheory.inter_eq_def;
val _ = translate sptreeTheory.map_def;
val _ = translate sptreeTheory.difference_def;
val _ = translate sptreeTheory.fromAList_def;

(* ------------------------------------------------------------------------- *)
(* sorting                                                                   *)
(* ------------------------------------------------------------------------- *)

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;

(* ------------------------------------------------------------------------- *)
(* int_bitwise                                                               *)
(* ------------------------------------------------------------------------- *)

(* Signed constants and bit operations are independent of the target width. *)
val _ = translate int_bitwiseTheory.int_not_def;
val _ = translate int_bitwiseTheory.bits_of_num_def;
val _ = translate int_bitwiseTheory.bits_of_int_def;

Theorem int_bitwise_bits_of_int_side[local]:
  ∀i. int_bitwise_bits_of_int_side i
Proof
  rw [fetch "-" "int_bitwise_bits_of_int_side_def",
      int_bitwiseTheory.int_not_def] \\ intLib.COOPER_TAC
QED
val _ = update_precondition int_bitwise_bits_of_int_side;

val _ = translate int_bitwiseTheory.num_of_bits_def;
val _ = translate int_bitwiseTheory.int_of_bits_def;
val _ = translate int_bitwiseTheory.bits_bitwise_def;
val _ = translate int_bitwiseTheory.int_bitwise_def;
Theorem boolean_ops[local]:
  (($/\ : bool -> bool -> bool) = λx y. x /\ y) ∧
  (($\/ : bool -> bool -> bool) = λx y. x \/ y)
Proof
  simp [FUN_EQ_THM]
QED

val _ = translate (int_bitwiseTheory.int_and_def |> SRULE [FUN_EQ_THM]
  |> ONCE_REWRITE_RULE [boolean_ops]);
val _ = translate (int_bitwiseTheory.int_or_def |> SRULE [FUN_EQ_THM] |> ONCE_REWRITE_RULE [boolean_ops]);
val _ = translate (int_bitwiseTheory.int_xor_def |> SRULE [FUN_EQ_THM] |> ONCE_REWRITE_RULE [boolean_ops]);

(* ------------------------------------------------------------------------- *)
(* integer_word, multiword and byte                                          *)
(* ------------------------------------------------------------------------- *)

(* Constant construction converts through both fixed HOL word widths. *)
fun translate_word_conversions ty = let
  val spec = INST_TYPE [alpha |-> ty]
  val conv = GEN_ALL o CONV_RULE wordsLib.WORD_CONV o spec o SPEC_ALL
  val _ = translate (integer_wordTheory.w2i_eq_w2n |> conv)
  val r = translate_no_ind (multiwordTheory.n2mw_def |> conv)
  val pre_tm = hd (hyp r)
  val pre_name = fst (dest_const pre_tm)
  val pre_def = fetch "-" (pre_name ^ "_def")
  val total = prove (pre_tm,
    rw [pre_def] \\ completeInduct_on `v1` \\ last_x_assum irule
    \\ rw [] \\ first_x_assum irule \\ simp [DIV_LT_X])
  val _ = save_thm (pre_name ^ "_total", total)
  val _ = update_precondition total
  val _ = translate (multiwordTheory.i2mw_def |> conv)
  val _ = translate (byteTheory.byte_index_def |> conv)
  val _ = translate (if ty = “:32” then byteTheory.set_byte_32 else byteTheory.set_byte_64)
  val _ = translate (byteTheory.bytes_to_word_def |> conv)
 in () end;
val _ = List.app translate_word_conversions [“:32”,“:64”];

(* ------------------------------------------------------------------------- *)
(* location and grammar                                                      *)
(* ------------------------------------------------------------------------- *)

Theorem locnle:
  locnle x y =
    case (x,y) of
    | (UNKNOWNpt,_) => T
    | (_,EOFpt) => T
    | (POSN x1 x2,POSN y1 y2) => ((x1 < y1) ∨ (x1 = y1) ∧ (x2 ≤ y2))
    | _ => F
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs []
  \\ fs [locationTheory.locnle_def] \\ EVAL_TAC \\ fs []
QED

val _ = translate locnle;

val _ = translate grammarTheory.ptree_head_def

(* ------------------------------------------------------------------------- *)
(* errorLogMonad                                                             *)
(* ------------------------------------------------------------------------- *)

val res = translate $ errorLogMonadTheory.return_def;
val res = translate $ errorLogMonadTheory.bind_def;
val res = translate $ errorLogMonadTheory.log_def;
val res = translate $ errorLogMonadTheory.error_def;

(* ------------------------------------------------------------------------- *)
(* bitstring and numposrep                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = use_long_names := false;

val _ = translate bitstringTheory.zero_extend_def
val _ = translate bitstringTheory.fixwidth_def
val _ = translate bitstringTheory.field_def
val _ = translate bitstringTheory.v2n_def;

Theorem l2n_side:
  ∀b a. a ≠ 0 ⇒ l2n_side a b
Proof
  Induct>>
  rw[Once (fetch"-""l2n_side_def")]
QED

val _ = update_precondition l2n_side;

val v2n_side = Q.prove(`
  v2n_side v ⇔ T`,
  EVAL_TAC>>
  fs[l2n_side]) |> update_precondition;
