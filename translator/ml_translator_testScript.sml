(*
  A collection of functions that have in the past turned out to be tricky to
  translate.
*)

open HolKernel Parse boolLib bossLib;
open listTheory pairTheory ml_translatorLib ml_translatorTheory;
open ml_progLib blastLib;

val _ = new_theory "ml_translator_test";

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

Definition ZIP2_def:
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:int))
End

(* test timing by setting this
val _ = (ml_translatorLib.trace_timing_to
    := SOME "ml_translator_test_timing.txt")
*)

val res = translate ZIP2_def;

val res = translate APPEND;
val res = translate REVERSE_DEF;
val res = translate mllistTheory.tabulate_aux_def;

val res = translate MEMBER_def;

Definition AEVERY_AUX_def:
  (AEVERY_AUX aux P [] = T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) =
     if MEMBER x aux then AEVERY_AUX aux P xs else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)
End

val res = translate AEVERY_AUX_def;

val res = translate mlstringTheory.strcat_def;
(* val res = translate mlstringTheory.concatWith_aux_def *)

Definition ADEL_def:
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)
End

val res = translate ADEL_def;

Definition ZIP4_def:
  ZIP4 xs = ZIP2 xs 6
End

val res = translate ZIP4_def;

Definition char_to_byte_def:
  char_to_byte c = (n2w (ORD c) : word8)
End

val res = translate char_to_byte_def;

val res = translate MAP;

val _ = hol2deep “λx. pure_seq (n+1:num) x”
  |> concl |> find_term (can (match_term “Let NONE”))

(*
val res = translate mlstringTheory.explode_aux_def;

val res = translate mlstringTheory.explode_def;

Definition string_to_bytes_def:
  string_to_bytes s = MAP char_to_byte (explode s)
End

val res = translate string_to_bytes_def;
*)

val res = translate miscTheory.any_word64_ror_def

Definition bar_def:
  bar = []:'a list
End
val res = translate bar_def

Definition foo1_def:
  foo1 = if bar = []:'a list then [] else []:'a list
End
val res = translate foo1_def

Definition foo2_def:
  foo2 = 4:num
End
val res = translate foo2_def

Datatype:
  foo = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; do_known : bool
            ; do_call : bool |>
End
val res = register_type``:foo``

Definition foo_def:
  foo (k:num) n =
  if n = 0 then []
  else if n ≤ 256n then [k]
  else foo (k+1) (n-256)
Termination
  WF_REL_TAC `measure SND`\\fs[]
End

val res = translate foo_def

Datatype:
  bar1 = ta | ti
End
Datatype:
  bar2 = Ta | TI
End
val _ = register_type ``:bar1``
val _ = register_type ``:bar2``

Definition and_pre_def:
  and_pre x ⇔ x <> 0i ∧ 2 / x > 0
End
Definition or_pre_def:
  or_pre x = if (x = 0) \/ 2 / x > 0 then and_pre x \/ 0 < x else x < 0
End
val res =  translate and_pre_def;
val res =  translate or_pre_def;

val _ = register_type ``:'a list``

Datatype:
  exn_type = Fail string | Subscript
End

val _ = register_exn_type ``:exn_type``

val _ = (print_asts := true);

(* test no_ind *)

Triviality word64_msb_thm:
  !w. word_msb (w:word64) =
         ((w && 0x8000000000000000w) = 0x8000000000000000w)
Proof
  blastLib.BBLAST_TAC
QED

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

Definition shift_test_def:
  shift_test (x:word64) y = arith_shift_right x y
End

val res = translate shift_test_def;

val _ = res |> hyp |> null orelse fail ();

(* Translation failure with primes *)
Datatype:
  idrec = <|v : num; f : 'a|>
End

Datatype:
  t = V num | F 'a | D t t
End

Definition test_def:
  test ids = D (F ids.f) (V ids.v)
End

val res = translate test_def;

(* Test floating-point support *)
Definition test1_def:
  test1 f = fp64_add roundTiesToEven f f
End

val res = translate test1_def;

(* FMA: *)

Definition test2_def:
  test2 f1 f2 f3 = (fp64_mul_add roundTiesToEven) f1 f2 f3
End

val res = translate test2_def;

(* tricky datatype *)

val _ = register_type ``:'a option``;
val _ = register_type ``:'a list``;
val _ = register_type ``:('a # 'b)``;

Datatype:
  tt = A1
     | B1 tt
     | C1 (tt option)
     | D1 (tt list)
     | E1 (tt # tt)
End

val _ = register_type ``:tt``;

(* test no_ind again *)

Definition test3_def:
  test3 x =
  (case x of
   | A1 => [()]
   | B1 x => test3 x ++ [()]
   | C1 NONE => []
   | C1 (SOME x) => test3 x ++ REVERSE (test3 x)
   | D1 tts =>
       (case tts of
        | [] => [(); ()]
        | (tt :: tts) => test3 (D1 tts) ++ test3 tt)
   | E1 (x, y) => REVERSE (test3 x) ++ test3 y)
End

val r = translate_no_ind test3_def;

(* registering types inside modules *)

Datatype:
  my_type = my_case1 | my_case2 | my_case3
End
Definition my_fun_def:
  (my_fun my_case1 = 0n) /\ (my_fun my_case2 = 1n) /\
                         (my_fun my_case3 = 2n)
End

val r = register_type ``:'a option``;

val _ = ml_prog_update (open_module "My_module");
val r = register_type ``:my_type``;
val _ = ml_prog_update (close_module NONE);
val r = translate my_fun_def;

Datatype:
  my_type3 = SomE num num | NonE
End

val _ = ml_prog_update (open_module "My_other_module");
val r = register_type ``:my_type3``;
val res3 = translate optionTheory.THE_DEF
val _ = ml_prog_update (close_module NONE);

(* test the abstract translator is working *)

Definition map_again_def:
  map_again f [] = []
  /\ map_again f (x :: xs) = f x :: map_again f xs
End

Definition inc_list_def:
  inc_list xs = map_again (\x. x + SUC 0) xs
End

val r = abs_translate map_again_def;
val r = abs_translate inc_list_def;
val r = concretise [``map_again``, ``inc_list``];

(* check EqualityType proves for some modestly complex datatypes *)

Datatype:
  a_type = AT_Nil | AT_Rec (a_type list) ((a_type # num) list)
End
Datatype:
  a_b_type = ABT_Nil
  | ABT_Rec (bool list) ((a_b_type # num) list)
End
Datatype:
  a_c_type = ACT_Nil | ACT_One 'a | ACT_Two 'b | ACT_Rec ((a_c_type # num) list)
End
Datatype:
  simple_type = STA | STB | STC | STX | STY | STZ
End
Datatype:
  simple_type2 = ST2A | ST2B | ST2C | ST2X | ST2Y | ST2Z
End

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

Definition hidden_f1_def:
  hidden_f1 xs = REVERSE xs ++ [()]
End
Definition global_f2_def:
  global_f2 xs = hidden_f1 xs ++ [()]
End
Definition hidden_f3_def:
  hidden_f3 xs = global_f2 (hidden_f1 xs)
End
Definition module_f4_def:
  module_f4 xs = hidden_f3 (global_f2 xs)
End
Definition module_f5_def:
  module_f5 xs = module_f4 xs
End
Definition global_f6_def:
  global_f6 xs = module_f5 xs ++ module_f4 xs
End

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

Definition m1_m2_f_def:
  m1_m2_f i = SUC 1 + i
End
Definition m1_m3_f_def:
  m1_m3_f i = m1_m2_f (SUC i)
End
Definition m1_f_def:
  m1_f i = m1_m2_f (m1_m3_f i)
End
Definition m4_f_def:
  m4_f i = m1_f i + m1_m3_f (m1_m2_f i)
End
Definition m4_m5_f_def:
  m4_m5_f i = m1_f i + m4_f i + m1_m2_f i
End

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

Definition str_ex1_def:
  str_ex1 s1 s2 = if LENGTH s1 = 0 then "Hello!" else
                  if EL 0 s1 = #"\n" then s1 else STRCAT s1 s2
End

val res = translate str_ex1_def;

val str_ex1_side_thm = Q.prove(
  `str_ex1_side s1 s2 = T`,
  rw [fetch "-" "str_ex1_side_def",DECIDE ``0 < n <=> n <> 0n``])
  |> update_precondition;

val res = translate MAP;

Definition str_ex2_def:
  str_ex2 s1 = MAP ORD (str_ex1 s1 "Test")
End

val res = translate str_ex2_def; (* causes warning *)

Definition str_ex3_def:
  str_ex3 s1 = MAP ORD (EXPLODE (str_ex1 s1 "Test"))
End

val res = translate str_ex3_def; (* doesn't cause warning *)

Definition str_ex4_def:
  str_ex4 s1 = MAP CHR (str_ex3 s1)
End

val res = translate str_ex4_def;

val str_ex4_side_thm = Q.prove(
  `str_ex4_side s1 = T`,
  rw [fetch "-" "str_ex4_side_def",str_ex3_def,MEM_MAP]
  \\ fs [stringTheory.ORD_BOUND])
  |> update_precondition;

Definition str_ex5_def:
  str_ex5 s1 = if s1 = "Hello" then "There!" else IMPLODE (MAP CHR (str_ex3 s1))
End

val res = translate str_ex5_def;

val str_ex5_side_thm = Q.prove(
  `str_ex5_side s1 = T`,
  rw [fetch "-" "str_ex5_side_def",str_ex3_def,MEM_MAP]
  \\ fs [stringTheory.ORD_BOUND])
  |> update_precondition;

Definition str_ex6_def:
  str_ex6 s <=>
    s <> "before" /\ s <> "div" /\ s <> "mod" /\ s <> "o" ∧
    if s = "" then T else HD s = #" "
End

val res = translate str_ex6_def;

Definition id_to_string_def:
  id_to_string (Short s) = implode s /\
  id_to_string (Long x id) = concat [implode x; implode "."; id_to_string id]
End

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
Definition chop_str_def:
  chop_str [] = [] /\
  chop_str xs = StrLit (TAKE 5 xs) :: chop_str (DROP 5 xs)
Termination
  WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_DROP]
End
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate chop_str_def

val _ = export_theory();
