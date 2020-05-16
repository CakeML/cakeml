open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;
open x64_configProofTheory;
open reverseProgTheory;

val _ = new_theory "reverseProof"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val reverse_x64_conf = (rand o rator o lhs o concl) reverse_thm

val _ = install_naming_overloads "reverseProg";
val _ = write_to_file reverse_data_prog_def;

val _ = export_theory();
