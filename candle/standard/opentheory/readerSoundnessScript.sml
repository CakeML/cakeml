(*
  Proves soundness of the OpenTheory article checker. The soundness
  theorem makes the connection to the semantics of HOL explicit.
*)
open preamble readerProofTheory holSoundnessTheory

val _ = new_theory "readerSoundness";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U-> bool``;

Theorem reader_sound:
   reader_main fs init_refs cl = (outp,refs,SOME s)
   ==>
   refs.the_context extends init_ctxt /\
   outp = add_stdout (flush_stdin cl fs) (msg_success s refs.the_context) /\
   !asl c.
      MEM (Sequent asl c) s.thms /\
      is_set_theory ^mem
      ==>
      (thyof refs.the_context, asl) |= c
Proof
 strip_tac
  \\ drule (GEN_ALL reader_proves) \\ rw []
  \\ irule proves_sound \\ fs []
QED

val _ = export_theory ();
