(*
  A collection of functions that have in the past turned out to be tricky to
  translate.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_translator_test";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;
open ml_progLib;

val _ = register_type “:'a list”;
val _ = register_type “:'a option”;

Datatype:
  a_ty = A1 | B1 (b_ty list) ;
  b_ty = B2 | A2 a_ty
End

val _ = register_type “:a_ty”;

val ty = “:a_ty”;

Definition dest_A2_def:
  dest_A2 (A2 a) = SOME a ∧
  dest_A2 _ = NONE
End

val r = translate dest_A2_def;

Datatype:
  tyAST = tyOp string (tyAST list)
        | tyVar string
        | tyTup (tyAST list)
End

val _ = register_type “:tyAST”;

Overload boolTy = “tyOp "Bool" []”;
Overload intTy = “tyOp "Int" []”
Overload listTy = “λty. tyOp "[]" [ty]”
Overload funTy = “λd r. tyOp "Fun" [d; r]”

Datatype:
  litAST = litInt int | litString string
End

val _ = register_type “:litAST”;

Datatype:
  patAST = patVar string
         | patApp string (patAST list)
         | patTup (patAST list)
         | patLit litAST
         | patUScore
End

val _ = register_type “:patAST”;

Datatype:
  expAST = expVar string
         | expCon string (expAST list)
         | expOp unit (expAST list)
         | expTup (expAST list)
         | expApp expAST expAST
         | expAbs patAST expAST
         | expIf expAST expAST expAST
         | expLit litAST
         | expLet (expdecAST list) expAST
         | expDo (expdostmtAST list) expAST
         | expCase expAST ((patAST # expAST) list);
  expdecAST = expdecTysig string tyAST
            | expdecPatbind patAST expAST
            | expdecFunbind string (patAST list) expAST ;
  expdostmtAST = expdostmtExp expAST
               | expdostmtBind patAST expAST
               | expdostmtLet (expdecAST list)
End

val _ = register_type “:expAST”;

Definition dest_Var_def:
  dest_Var (expdecTysig a b) = SOME (a,b) ∧
  dest_Var _ = NONE
End

val r = translate dest_Var_def;

(* test hiding of functions in local .. in .. end *)

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end;

val _ = (find_def_for_const := def_of_const);

Definition hidden_def:
  hidden x = x + 5:num
End

Definition uses_hidden1_def:
  uses_hidden1 x = hidden x
End

Definition uses_hidden2_def:
  uses_hidden2 x = hidden x * uses_hidden1 x
End

val _ = ml_prog_update open_local_block;
val _ = translate hidden_def;
val _ = ml_prog_update open_local_in_block;
val _ = translate uses_hidden1_def;
val _ = ml_prog_update close_local_blocks;
val _ = clean_v_thms () (* <-- this makes the translator realise that hidden
                               needs to be retranslated; clean_v_thms runs
                               automatically on theory export *)
val _ = translate uses_hidden2_def;

(* test side conditions *)

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

val _ = hol2deep “λx. pure_seq (n+1:num) x”
  |> concl |> find_term (can (match_term “Let NONE”))

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

Datatype:
  exn_type = Fail string | Subscript
End

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

Triviality arith_shift_right_ind:
  arith_shift_right_ind
Proof
  once_rewrite_tac [fetch "-" "arith_shift_right_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ first_x_assum match_mp_tac \\ wordsLib.WORD_EVAL_TAC \\ rw[]
QED

val _ = arith_shift_right_ind |> update_precondition;

val shift_test_def = Define `shift_test (x:word64) y = arith_shift_right x y`

val res = translate shift_test_def;

val _ = res |> hyp |> null orelse fail ();

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

val r = translate_no_ind test_def;

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
Datatype:
  a_c_type = ACT_Nil | ACT_One 'a | ACT_Two 'b | ACT_Rec ((a_c_type # num) list)
End
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
  fs (map (REWRITE_RULE [AND_IMP_INTRO]) (eq_lemmas ()))
QED

(* FIXME: mutually recursive datastructures don't seem to work *)

(* register a type for which EqualityType can't be proven *)

Datatype:
  non_eq_type = Non_Eq_Type (num -> bool) (num list)
End

val r = register_type ``: non_eq_type``;

val part_dummy_v_fun = fetch_v_fun ``: non_eq_type``;

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

val _ = use_string_type true;

val _ = (hol2deep ``"hi"`` |> concl |> rator |> rand |> astSyntax.is_Lit)
        orelse failwith "incorrectly translates string literals";

val r = hol2deep ``\c. STRING c ""``;

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

val _ = export_theory();
