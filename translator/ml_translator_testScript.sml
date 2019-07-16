(*
  A collection of functions that have in the past turned out to be tricky to
  translate.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_translator_test";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;
open ml_progLib;

val ZIP2_def = Define `
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:int))`

(* test timing by setting this
val _ = (ml_translatorLib.trace_timing_to
    := SOME "ml_translator_test_timing.txt")
*)

val res = translate ZIP2_def;

val res = translate APPEND;
val res = translate REVERSE_DEF;
val res = translate mllistTheory.tabulate_aux_def;

val res = translate MEMBER_def;

val AEVERY_AUX_def = Define `
  (AEVERY_AUX aux P [] = T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) =
     if MEMBER x aux then AEVERY_AUX aux P xs else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)`;

val res = translate AEVERY_AUX_def;

val res = translate mlstringTheory.strcat_def;
(* val res = translate mlstringTheory.concatWith_aux_def *)

val ADEL_def = Define `
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)`

val res = translate ADEL_def;

val ZIP4_def = Define `
  ZIP4 xs = ZIP2 xs 6`

val res = translate ZIP4_def;

val char_to_byte_def = Define`
  char_to_byte c = (n2w (ORD c) : word8)`;

val res = translate char_to_byte_def;

val res = translate MAP;

(*
val res = translate mlstringTheory.explode_aux_def;

val res = translate mlstringTheory.explode_def;

val string_to_bytes_def = Define`
  string_to_bytes s = MAP char_to_byte (explode s)`;

val res = translate string_to_bytes_def;
*)

val res = translate miscTheory.any_word64_ror_def

val def = Define `bar = []:'a list`
val res = translate def

val def = Define `foo1 = if bar = []:'a list then [] else []:'a list`
val res = translate def

val def = Define `foo2 = 4:num`
val res = translate def

val _ = Datatype`
  foo = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; do_known : bool
            ; do_call : bool |>`
val res = register_type``:foo``

val foo_def = tDefine"foo"`
  foo (k:num) n =
  if n = 0 then []
  else if n ≤ 256n then [k]
  else foo (k+1) (n-256)`
  (WF_REL_TAC `measure SND`\\fs[])

val res = translate foo_def

val _ = Datatype `bar1 = ta | ti`
val _ = Datatype `bar2 = Ta | TI`
val _ = register_type ``:bar1``
val _ = register_type ``:bar2``

val and_pre_def = Define`
  and_pre x ⇔ x <> 0i ∧ 2 / x > 0`;
val or_pre_def = Define`
  or_pre x = if (x = 0) \/ 2 / x > 0 then and_pre x \/ 0 < x else x < 0`
val res =  translate and_pre_def;
val res =  translate or_pre_def;

val _ = register_type ``:'a list``
val _ = Hol_datatype `exn_type = Fail of string | Subscript`
val _ = register_exn_type ``:exn_type``

val _ = (print_asts := true);

(* test no_ind *)

val word64_msb_thm = Q.prove(
  `!w. word_msb (w:word64) =
         ((w && 0x8000000000000000w) = 0x8000000000000000w)`,
  blastLib.BBLAST_TAC);

val res = translate word64_msb_thm;

val res = translate (miscTheory.arith_shift_right_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [wordsTheory.dimindex_64]
                     |> CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV));

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ first_x_assum match_mp_tac \\ wordsLib.WORD_EVAL_TAC \\ rw[])
  |> update_precondition;

val shift_test_def = Define `shift_test (x:word64) y = arith_shift_right x y`

val res = translate shift_test_def;

(* Translation failure with primes *)
val _ = Datatype` idrec = <|v : num; f : 'a|>`;

val _ = Datatype` t = V num | F 'a | D t t`;

val test_def = Define`test ids = D (F ids.f) (V ids.v)`;

val res = translate test_def;

(* Test floating-point support *)

val test_def = Define `test f = fp64_add roundTiesToEven f f`

val res = translate test_def;

(* FMA: *)

val test_def = Define `test f1 f2 f3 = (fp64_mul_add roundTiesToEven) f1 f2 f3`

val res = translate test_def;

(* tricky datatype *)

val _ = register_type ``:'a option``;
val _ = register_type ``:'a list``;
val _ = register_type ``:('a # 'b)``;

val _ = Datatype `
  tt = A1
     | B1 tt
     | C1 (tt option)
     | D1 (tt list)
     | E1 (tt # tt)`

val _ = register_type ``:tt``;

(* test no_ind again *)

val test_def = xDefine "test" `test x = (case x of
  | A1 => [()]
  | B1 x => test x ++ [()]
  | C1 NONE => []
  | C1 (SOME x) => test x ++ REVERSE (test x)
  | D1 tts => (case tts of [] => [(); ()]
        | (tt :: tts) => test (D1 tts) ++ test tt)
  | E1 (x, y) => REVERSE (test x) ++ test y)`
;

val _ = translate_no_ind test_def;

(* registering types inside modules *)

val _ = Datatype `my_type = my_case1 | my_case2 | my_case3`;
val my_fun_def = Define `(my_fun my_case1 = 0n) /\ (my_fun my_case2 = 1n) /\
                         (my_fun my_case3 = 2n)`;

val r = register_type ``:'a option``;

val _ = ml_prog_update (open_module "My_module");
val r = register_type ``:my_type``;
val _ = ml_prog_update (close_module NONE);
val r = translate my_fun_def;

val _ = Datatype `my_type3 = SomE num num | NonE`;

val _ = ml_prog_update (open_module "My_other_module");
val r = register_type ``:my_type3``;
val res3 = translate optionTheory.THE_DEF
val _ = ml_prog_update (close_module NONE);

(* test the abstract translator is working *)

val map_again_def = Define `map_again f [] = []
  /\ map_again f (x :: xs) = f x :: map_again f xs`;

val inc_list_def = Define `inc_list xs = map_again (\x. x + SUC 0) xs`;

val r = abs_translate map_again_def;
val r = abs_translate inc_list_def;
val r = concretise [``map_again``, ``inc_list``];

(* check EqualityType proves for some modestly complex datatypes *)

val _ = Datatype `a_type = AT_Nil | AT_Rec (a_type list) ((a_type # num) list)`;
val _ = Datatype `a_b_type = ABT_Nil
  | ABT_Rec (bool list) ((a_b_type # num) list)`;
val _ = Datatype.Hol_datatype `a_c_type = ACT_Nil
  | ACT_One of 'a | ACT_Two of 'b | ACT_Rec of (a_c_type # num) list`;
val _ = Datatype `simple_type = STA | STB | STC | STX | STY | STZ`;
val _ = Datatype `simple_type2 = ST2A | ST2B | ST2C | ST2X | ST2Y | ST2Z`;

val r = register_type ``:a_type``;
val r = register_type ``:a_b_type``;
val r = register_type ``:('a, 'b) a_c_type``;
val r = register_type ``:simple_type``;
val r = register_exn_type ``:simple_type2``;

val a_inv = get_type_inv ``:a_type``;
val a_b_inv = get_type_inv ``:a_b_type``;
val a_c_inv_num = get_type_inv ``:(num, num) a_c_type``;
val st_inv = get_type_inv ``:simple_type``;
val st2_inv = get_type_inv ``:simple_type2``;

Theorem EqTyp_test_lemmas:
   EqualityType (^a_inv) /\ EqualityType (^a_b_inv)
    /\ EqualityType (^a_c_inv_num) /\ EqualityType (^st_inv)
    /\ EqualityType (^st2_inv)
Proof
  fs (eq_lemmas ())
QED

(* translating within nested local blocks and modules *)

val hidden_f1_def = Define `hidden_f1 xs = REVERSE xs ++ [()]`;
val global_f2_def = Define `global_f2 xs = hidden_f1 xs ++ [()]`;
val hidden_f3_def = Define `hidden_f3 xs = global_f2 (hidden_f1 xs)`;
val module_f4_def = Define `module_f4 xs = hidden_f3 (global_f2 xs)`;
val module_f5_def = Define `module_f5 xs = module_f4 xs`;
val global_f6_def = Define `global_f6 xs = module_f5 xs ++ module_f4 xs`;

val r = translate REVERSE_DEF;
val _ = ml_prog_update open_local_block;
val r = translate hidden_f1_def;
val _ = ml_prog_update open_local_in_block;
val r = translate global_f2_def;
val _ = ml_prog_update (open_module "f4_module");
val _ = ml_prog_update open_local_block;
val r = translate hidden_f3_def;
val _ = ml_prog_update open_local_in_block;
val r = translate module_f4_def;
val _ = ml_prog_update open_local_block;
val _ = ml_prog_update open_local_in_block;
val r = translate module_f5_def;
val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);
val _ = ml_prog_update close_local_block;
val r = translate global_f6_def;

(* translating within nested modules *)

val m1_m2_f_def = Define `m1_m2_f i = SUC 1 + i`;
val m1_m3_f_def = Define `m1_m3_f i = m1_m2_f (SUC i)`;
val m1_f_def = Define `m1_f i = m1_m2_f (m1_m3_f i)`;
val m4_f_def = Define `m4_f i = m1_f i + m1_m3_f (m1_m2_f i)`;
val m4_m5_f_def = Define `m4_m5_f i = m1_f i + m4_f i + m1_m2_f i`;

val _ = ml_prog_update (open_module "m1");
val _ = ml_prog_update (open_module "m2");
val r = translate m1_m2_f_def;
val _ = ml_prog_update (close_module NONE);
val _ = ml_prog_update (open_module "m3");
val r = translate m1_m3_f_def;
val _ = ml_prog_update (close_module NONE);
val r = translate m1_f_def;
val _ = ml_prog_update (close_module NONE);
val _ = ml_prog_update (open_module "m4");
val r = translate m4_f_def;
val _ = ml_prog_update (open_module "m5");
val r = translate m4_m5_f_def;
val _ = ml_prog_update (close_module NONE);
val _ = ml_prog_update (close_module NONE);

(* test support for HOL_STRING_TYPE *)

val _ = use_string_type true;

val str_ex1_def = Define `
  str_ex1 s1 s2 = if LENGTH s1 = 0 then "Hello!" else
                  if EL 0 s1 = #"\n" then s1 else STRCAT s1 s2`;

val res = translate str_ex1_def;

val str_ex1_side_thm = Q.prove(
  `str_ex1_side s1 s2 = T`,
  rw [fetch "-" "str_ex1_side_def",DECIDE ``0 < n <=> n <> 0n``])
  |> update_precondition;

val res = translate MAP;

val str_ex2_def = Define `
  str_ex2 s1 = MAP ORD (str_ex1 s1 "Test")`;

val res = translate str_ex2_def; (* causes warning *)

val str_ex3_def = Define `
  str_ex3 s1 = MAP ORD (EXPLODE (str_ex1 s1 "Test"))`;

val res = translate str_ex3_def; (* doesn't cause warning *)

val str_ex4_def = Define `
  str_ex4 s1 = MAP CHR (str_ex3 s1)`

val res = translate str_ex4_def;

val str_ex4_side_thm = Q.prove(
  `str_ex4_side s1 = T`,
  rw [fetch "-" "str_ex4_side_def",str_ex3_def,MEM_MAP]
  \\ fs [stringTheory.ORD_BOUND])
  |> update_precondition;

val str_ex5_def = Define `
  str_ex5 s1 = if s1 = "Hello" then "There!" else IMPLODE (MAP CHR (str_ex3 s1))`

val res = translate str_ex5_def;

val str_ex5_side_thm = Q.prove(
  `str_ex5_side s1 = T`,
  rw [fetch "-" "str_ex5_side_def",str_ex3_def,MEM_MAP]
  \\ fs [stringTheory.ORD_BOUND])
  |> update_precondition;

val str_ex6_def = Define `
  str_ex6 s <=>
    s <> "before" /\ s <> "div" /\ s <> "mod" /\ s <> "o" ∧
    if s = "" then T else HD s = #" "`

val res = translate str_ex6_def;

val id_to_string_def = Define `
  id_to_string (Short s) = implode s /\
  id_to_string (Long x id) = concat [implode x; implode "."; id_to_string id]`

val res = translate id_to_string_def;

(* more advanced test of HOL_STRING_TYPE *)

(* step 1: reg a type with string inside, StrLit : string -> lit *)
val _ = use_string_type true;
val _ = register_type ``:lit``

(* step 2: translate a function that walks a char list producing datatype with strings *)
val _ = use_string_type false;
val chop_str_def = tDefine "chop_str" `
  chop_str [] = [] /\
  chop_str xs = StrLit (TAKE 5 xs) :: chop_str (DROP 5 xs)`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_DROP]);
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate chop_str_def

(* translate tricky parts of StringProg *)

val _ = use_string_type false;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "string" (Atapp [] (Short "string"))`` I);

fun get_module_prefix () = let
  val mods = ml_progLib.get_open_modules (get_ml_prog_state ())
  in case mods of [] => ""
    | (m :: ms) => m ^ "_"
  end

val _ = translate arithmeticTheory.MIN_DEF
val result = translate (mlstringTheory.extract_def |> REWRITE_RULE [mlstringTheory.implode_def]);

val extract_side_def = definition"extract_side_def";
val extract_side_thm = Q.prove(
  `!s i opt. extract_side s i opt`,
  rw [extract_side_def, arithmeticTheory.MIN_DEF] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val res = translate (mlstringTheory.concatWith_aux_def |> REWRITE_RULE [mlstringTheory.implode_def]);
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["concatWith"];
val result = translate mlstringTheory.concatWith_def;

val result = translate mlstringTheory.str_def;

val _ = ml_prog_update open_local_block;
val result = translate mlstringTheory.translate_aux_def;
val translate_aux_side_def = theorem"translate_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["translate"];
val result = translate mlstringTheory.translate_def;
val translate_side_def = definition"translate_side_def";

val translate_aux_side_thm = Q.prove (
  `!f s n len. n + len = strlen s ==> translate_aux_side f s n len`,
  Induct_on `len` \\ rw[Once translate_aux_side_def]);

val translate_side_thm = Q.prove (
  `!f s. translate_side f s`,
  rw [translate_side_def, translate_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val r = translate mlstringTheory.splitl_aux_def;
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["split"];
val r = translate mlstringTheory.splitl_def;

val _ = ml_prog_update open_local_block;
val res = translate mlstringTheory.tokens_aux_def; (* problem *)
val tokens_aux_side_def = theorem"tokens_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["tokens"];
val result = translate mlstringTheory.tokens_def;
val tokens_side_def = definition"tokens_side_def";

val tokens_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> tokens_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once tokens_aux_side_def]);

val tokens_side_thm = Q.prove (
  `!f s. tokens_side f s`,
  rw [tokens_side_def, tokens_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate mlstringTheory.fields_aux_def;
val fields_aux_side_def = theorem"fields_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["fields"];
val result = translate mlstringTheory.fields_def;
val fields_side_def = definition"fields_side_def";

val fields_aux_side_thm = Q.prove (
  `!f s ss n len. n + len = strlen s ==> fields_aux_side f s ss n len`,
  Induct_on `len` \\ rw [Once fields_aux_side_def]);

val fields_side_thm = Q.prove (
  `!f s. fields_side f s`,
  rw [fields_side_def, fields_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate mlstringTheory.isStringThere_aux_def;
val isStringThere_aux_side_def = theorem"isstringthere_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val isStringThere_aux_side_thm = Q.prove (
  `!s1 s2 s1i s2i len.
     s1i + len ≤ strlen s1 ∧ s2i + len <= strlen s2 ==>
     isstringthere_aux_side s1 s2 s1i s2i len`,
  Induct_on `len` \\ rw [Once isStringThere_aux_side_def]);

val _ = next_ml_names := ["isSubstring"];
val result = translate mlstringTheory.isSubstring_aux_def;
val isSubstring_aux_side_def = theorem"issubstring_aux_side_def";
val isSubstring_aux_side_thm = Q.prove (
  `!s1 s2 lens1 n len.
    (lens1 = strlen s1) ∧ n + len + lens1 ≤ strlen s2 + 1 ==>
    issubstring_aux_side s1 s2 lens1 n len`,
  Induct_on `len` >>
  rw [Once isSubstring_aux_side_def] >>
  irule isStringThere_aux_side_thm >> simp[]);

val _ = next_ml_names := ["isSubstring"];
val result = translate mlstringTheory.isSubstring_def;
val isSubstring_side_def = definition"issubstring_side_def";
val isSubstring_side_thm = Q.prove (
  `!s1 s2. issubstring_side s1 s2`,
  rw [isSubstring_side_def, isSubstring_aux_side_thm]) |> update_precondition

val _ = next_ml_names := ["isSuffix"];
val result = translate mlstringTheory.isSuffix_def;
val isSuffix_side_def = definition"issuffix_side_def";
val isSuffix_thm = Q.prove (
  `!s1 s2. issuffix_side s1 s2`,
  rw[isSuffix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["isPrefix"];
val result = translate mlstringTheory.isPrefix_def;
val isPrefix_side_def = definition"isprefix_side_def";
val isPrefix_thm = Q.prove (
  `!s1 s2. isprefix_side s1 s2`,
  rw[isPrefix_side_def, isStringThere_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate mlstringTheory.compare_aux_def;
val compare_aux_side_def = theorem"compare_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["compare"];
val result = translate mlstringTheory.compare_def;
val compare_side_def = definition"compare_side_def";

val compare_aux_side_thm = Q.prove (
  `!s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once compare_aux_side_def]);

val compare_side_thm = Q.prove (
  `!s1 s2. compare_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition

val _ = next_ml_names := ["<"];
val _ = translate mlstringTheory.mlstring_lt_def;
val _ = next_ml_names := ["<="];
val _ = translate mlstringTheory.mlstring_le_def;
val _ = next_ml_names := [">="];
val _ = translate mlstringTheory.mlstring_ge_def;
val _ = next_ml_names := [">"];
val _ = translate mlstringTheory.mlstring_gt_def;

val _ = ml_prog_update open_local_block;
val result = translate mlstringTheory.collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["collate"];
val result = translate mlstringTheory.collate_def;
val collate_side_def = definition"collate_side_def";

val collate_aux_side_thm = Q.prove (
  `!f s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> collate_aux_side f s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once collate_aux_side_def]);

val collate_side_thm = Q.prove (
  `!f s1 s2. collate_side f s1 s2`,
  rw [collate_side_def, collate_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update close_local_blocks;

(* from IntProg *)
val _ = use_string_type false;

open mlintTheory

val result = translate zero_pad_def

val result = translate toChar_def
val tochar_side_def = definition"tochar_side_def";
val tochar_side = Q.prove(
  `∀x. tochar_side x <=> (~(x < 10) ==> x < 201)`,
  rw[tochar_side_def])
  |> update_precondition;

val result = translate simple_toChars_def

val simple_toChars_side = Q.prove(
  `∀x y z. simple_tochars_side x y z = T`,
  ho_match_mp_tac simple_toChars_ind \\ rw[]
  \\ rw[Once (theorem"simple_tochars_side_def")])
  |> update_precondition;

val _ = save_thm("toChars_ind",
   toChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val result = translate
  (toChars_def |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["toString"];

val toString_v_thm = translate
  (toString_def |> REWRITE_RULE[maxSmall_DEC_def])
val tostring_side = Q.prove(
  `∀x. tostring_side x = T`,
  rw[definition"tostring_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val toString_v_thm = toString_v_thm
  |> DISCH_ALL |> REWRITE_RULE [tostring_side,ml_translatorTheory.PRECONDITION_def]
  |> ml_translatorLib.remove_Eq_from_v_thm;

val Eval_NUM_toString = Q.prove(
  `!v. (INT --> STRING_TYPE) toString v ==>
       (NUM --> STRING_TYPE) num_to_str v`,
  simp [ml_translatorTheory.Arrow_def,
    ml_translatorTheory.AppReturns_def,num_to_str_def,
    ml_translatorTheory.NUM_def,PULL_EXISTS,FORALL_PROD]
  \\ rw [] \\ res_tac)
  |> (fn th => MATCH_MP th toString_v_thm)
  |> add_user_proved_v_thm;

val _ = ml_prog_update open_local_block;

val result = translate fromChar_unsafe_def;
val result = translate fromChars_range_unsafe_def;

val _ = save_thm("fromChars_unsafe_ind",
  fromChars_unsafe_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val result = translate (fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val result = translate fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_side_def = theorem"fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def]
QED

val _ = translate optionTheory.OPTION_MAP_DEF
val _ = translate optionTheory.IS_SOME_DEF
val _ = translate optionTheory.OPTION_MAP2_DEF
val _ = translate combinTheory.o_DEF

val result = translate fromChar_def;
val result = translate fromChars_range_def;

val _ = save_thm("fromChars_ind",
  fromChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val result = translate (fromChars_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["fromString"];
val result = translate fromString_def;
val fromstring_side_def = definition"fromstring_side_def";
val fromchars_side_def = theorem"fromchars_side_def";
val fromchars_range_side_def = theorem"fromchars_range_side_def";

val _ = next_ml_names := ["fromNatString"];
val result = translate fromNatString_def;

val _ = export_theory();
