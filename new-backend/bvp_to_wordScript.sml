open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_to_word";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory sptreeTheory lcsymtacs bviTheory bvpTheory;
open word_langTheory;

(* a compiler from BVP to wordLang *)

val var_adjust_def = Define `
  var_adjust n = 2 * n:num`

val adjust_names_def = Define `
  adjust_names (names:num_set) =
    fromAList (MAP (\(n,x). (var_adjust n,x)) (toAList names))`;

val ret_adjust_def = Define `
  (ret_adjust NONE = NONE) /\
  (ret_adjust (SOME (v,names)) = SOME (var_adjust v, adjust_names names))`;

val arg_var_def = Define `
  arg_var n args = if n < LENGTH args then Var 0 else Var (EL n args)`;

val pCompAssign_def = Define `
  (pCompAssign dest El args names_opt =
     Assign dest (Load (Op ADD [Shift LSL (arg_var 0 args) (Nat 2);
                                arg_var 1 args]))) /\
  (pCompAssign dest x args names_opt =
     (* many of these cases are going to be complicated and really
        need a proof to be even half-correct *)
     ARB)`;

val pComp_def = Define `
  (pComp (Skip:bvp_prog) = Skip:'a word_prog) /\
  (pComp (Move dest src) = Move [(var_adjust dest, var_adjust src)]) /\
  (pComp Tick = Tick) /\
  (pComp (Assign dest op args names_opt) =
     pCompAssign (var_adjust dest) op (MAP var_adjust args)
       (OPTION_MAP adjust_names names_opt)) /\
  (pComp (MakeSpace k names) =
     Seq (Set AllocSize (Const (if k < dimword (:'a) then n2w k else ~0w)))
         (If (Assign 1 (Op UNSIGNED_LESS [Get AllocLeft; Get AllocSize])) 1
           (Call (SOME (1,adjust_names names)) (SOME 0) [] NONE)
           Skip)) /\
  (pComp (Raise n) = Raise (var_adjust n)) /\
  (pComp (Return n) = Return (var_adjust n)) /\
  (pComp (Seq c1 c2) = Seq (pComp c1) (pComp c2)) /\
  (pComp (If g n c1 c2) = If (pComp g) (var_adjust n) (pComp c1) (pComp c2)) /\
  (pComp (Call ret dest args handler) =
     Call (ret_adjust ret) dest (MAP var_adjust args)
       (case handler of
        | NONE => NONE
        | SOME (v,p) => SOME (var_adjust v, pComp p)))`

val _ = export_theory();
