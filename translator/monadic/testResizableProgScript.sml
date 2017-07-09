open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib
open determTheory

val _ = new_theory "testResizableProg";
			
val _ = (use_full_type_names := false);

val _ = register_type ``:cpn``
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``
val _ = register_type ``:'a option``

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

val _ = hide "state";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = Hol_datatype `
 store_refv =
    SrefNum of num
  | SrefNumList of num list`;

val _ = register_type ``:store_refv``;


val _ = Hol_datatype`
  mon_exn = Fail of mlstring`

val STORE_REFV_TYPE_def = theorem "STORE_REFV_TYPE_def";

(* Specific functions *)
(* val Mref_num_def = Define `
Mref_num x = Mref SrefNum x`;

val Mref_num_list_def = Define `
Mred_numList_ref x = Mref SrefNumList x`;

val dref_num_def = Define `
dref_num n = \state. case dref n state of SrefNum x => x`;

val dref_numList_def = Define `
dref_numList n = \state. case dref n state of SrefNumList x => x`;

val Mdref_num_def = Define `
Mdref_num r = \state.
case Mdref r state of (Success (SrefNum x)) => (Success x, state)
| other => (Failure (strlit "ref read error"), state)`;

val Mdref_numList_def = Define `
Mdref_numList r = \state.
case Mdref r state of (Success (SrefNumList x)) => (Success x, state)
| other => (Failure (strlit "ref read error"), state)`; *)

(* val _ = register_exn_type ``:mon_exn``;

val MON_EXN_TYPE_def = theorem"MON_EXN_TYPE_def"; *)

(* General theorems *)

(* COPY/PASTE *)
val evaluate_list_cases = let
  val lemma = evaluate_cases |> CONJUNCTS |> el 2
  in CONJ (``evaluate_list a5 a6 a7 [] (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma])
          (``evaluate_list a5 a6 a7 (x::xs) (a9,Rval a10)``
|> SIMP_CONV (srw_ss()) [Once lemma]) end;
(* COPY/PASTE *)

val _ = Globals.max_print_depth := 40;



val _ = export_theory();
