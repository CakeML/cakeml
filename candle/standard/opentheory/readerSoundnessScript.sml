open preamble readerProofTheory holSoundnessTheory

val _ = new_theory "readerSoundness";

val mem = ``mem:'U->'U-> bool``;

val reader_sound = Q.store_thm("reader_sound",
  `(* assumptions on the set theory *)
   is_set_theory ^mem ==>
   (* if the reader completes a successful run (proves everything) *)
   reader_main fs init_refs cl = (T,outp,refs)
   ==>
   ?s ctxt.
     (!asl c. MEM (Sequent asl c) s.thms ==> (thyof ctxt, asl) |= c) /\
     outp = add_stdout fs (msg_success s ctxt) /\
     ctxt extends init_ctxt`,
  rpt strip_tac
  \\ drule (GEN_ALL reader_proves) \\ rw []
  \\ Q.LIST_EXISTS_TAC [`s`,`ctxt`] \\ rw []
  \\ irule proves_sound \\ fs []);

val _ = export_theory ();
