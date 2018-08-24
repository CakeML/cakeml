open preamble readerProofTheory holSoundnessTheory

val _ = new_theory "readerSoundness";

val mem = ``mem:'U->'U-> bool``;

val reader_sound = Q.store_thm("reader_sound",
  `(* assumption about a strong enough set theory (see candle proofs) *)
   is_set_theory ^mem ==>
   (* if the reader completes a successful run (executes all commands *)
   (* in the article file) when started from the initial candle state *)
   reader_main fs init_refs cl = (T,outp,refs)
   ==>
   (* then there is a final state s for the reader and a final context *)
   (* ctxt for the candle kernel, and ...                              *)
   ?s ctxt.
     (* anything on the reader theorem stack in the final state s is a *)
     (* theorem in the prover context ctxt, and ...                    *)
     (!asl c. MEM (Sequent asl c) s.thms ==> (thyof ctxt, asl) |= c) /\
     (* the context ctxt is the result of a series of legal updates to *)
     (* the initial context.                                           *)
     ctxt extends init_ctxt /\
     (* the output consists of a message displaying the context and    *)
     (* the contents of the theorem stack.                             *)
     outp = add_stdout fs (msg_success s ctxt)`,
  rpt strip_tac
  \\ drule (GEN_ALL reader_proves) \\ rw []
  \\ Q.LIST_EXISTS_TAC [`s`,`ctxt`] \\ rw []
  \\ irule proves_sound \\ fs []);

val _ = export_theory ();
