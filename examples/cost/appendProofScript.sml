(*
  Prove of sum space consumption
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open x64_configProofTheory;
open appendProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "appendProof"

val _ = ParseExtras.temp_tight_equality ()

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val app123_x64_conf = (rand o rator o lhs o concl) app123_thm

val _ = install_naming_overloads "appendProg";
val _ = write_to_file app123_data_prog_def;

val fields = TypeBase.fields_of “:('c,'ffi) dataSem$state”;

Overload state_refs_fupd = (fields |> assoc "refs" |> #fupd);
Overload state_locals_fupd = (fields |> assoc "locals" |> #fupd);
Overload state_stack_max_fupd = (fields |> assoc "stack_max" |> #fupd);
Overload state_safe_for_space_fupd = (fields |> assoc "safe_for_space" |> #fupd);
Overload state_peak_heap_length_fupd = (fields |> assoc "peak_heap_length" |> #fupd);

val _ = export_theory();
