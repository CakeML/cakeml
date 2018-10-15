open preamble readerProofTheory holSoundnessTheory

val _ = new_theory "readerSoundness";

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U-> bool``;

val reader_sound = Q.store_thm("reader_sound",
  `(* assumption about a strong enough set theory (see candle proofs) *)
   is_set_theory ^mem ==>
   (* if the reader completes a successful run (executes all commands *)
   (* in the article file) when started from the initial candle state *)
   reader_main fs init_refs cl = (T,outp,refs,fstate)
   ==>
   (* then there is a final state s for the reader and a final context *)
   (* refs.the_context for the candle kernel, and ...                  *)
   ?s.
     fstate = SOME s /\
     (* anything on the reader theorem stack in the final state s is a *)
     (* theorem in the prover context refs.the_context, and ...        *)
     (!asl c.
        MEM (Sequent asl c) s.thms ==> (thyof refs.the_context, asl) |= c) /\
     (* the context is the result of a series of legal updates to      *)
     (* the initial context.                                           *)
     refs.the_context extends init_ctxt /\
     (* the output consists of a message displaying the context and    *)
     (* the contents of the theorem stack.                             *)
     outp = add_stdout fs (msg_success s refs.the_context)`,
  rpt strip_tac
  \\ drule (GEN_ALL reader_proves) \\ rw []
  \\ rw []
  \\ irule proves_sound \\ fs []);

val _ = export_theory ();
