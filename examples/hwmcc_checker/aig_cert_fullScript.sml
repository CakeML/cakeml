(*
  Verified certificate checker for the Hardware Model Checking Competition.
*)
Theory aig_cert_full
Ancestors
  aig_parse aig_cert_encode aig_to_cnf
Libs
  preamble

Definition main_def:
  main mstr wstr =
  do
    (* parse model and witness *)
    (maig, rest) <- parse_aiger mstr;
    (waig, maps, rest) <- parse_witness wstr;
    (* model *)
    mcounts <<- maig.counts;
    mmax_input <<- mcounts.inputs;
    mmax_latch <<- mmax_input + mcounts.latches;
    mcirc <<- maig.circuit;
    mreset <<- (λl. lookup l maig.reset);
    mnext  <<- (λl. case lookup l maig.next of
                    | SOME lit => lit
                    | NONE => (Base Ff, F));
    mpreds <<- if mcounts.bad = 0 ∧ mcounts.justice = 0 then
                 GENLIST (λk. (Name (mmax_latch + 1 + k), F)) mcounts.outputs
               else maig.bad;
    mcnstrs <<- maig.constraints;
    mlatches <<- GENLIST (λk. 1 + k) mmax_input;
    (* witness *)
    wcounts <<- waig.counts;
    wmax_input <<- wcounts.inputs;
    wmax_latch <<- wmax_input + wcounts.latches;
    (* apply sharing maps to witness *)
    in_map <<- maps.shared_inputs;
    latch_map <<- maps.shared_latches;
    wcirc <<- replace wmax_input mmax_input mmax_latch in_map latch_map
      waig.circuit;
    wreset <<- (λl. lookup l waig.reset);
    wnext  <<- (λl. case lookup l waig.next of
                    | SOME lit => lit
                    | NONE => (Base Ff, F) (* should not happen *));
    wpreds <<- if wcounts.bad = 0 ∧ wcounts.justice = 0 then
                 GENLIST (λk. (Name (wmax_latch + 1 + k), F)) wcounts.outputs
               else waig.bad;
    wcnstrs <<- waig.constraints;
    wlatches <<- GENLIST (λk. 1 + k) wmax_input;
    (* encode certificate conditions as circuits *)
    cert_reset_circ <<-
      encode_is_witness_reset mcirc mreset mcnstrs mlatches wcirc wreset
      wcnstrs wlatches;
    cert_transition_circ <<-
      encode_is_witness_transition mcirc mnext mcnstrs mlatches wcirc
        wnext wcnstrs wlatches;
    cert_property_circ <<-
      encode_is_witness_property mcirc mcnstrs mpreds wcirc wcnstrs wpreds;
    cert_base_circ <<-
      encode_is_witness_base wcirc wreset wcnstrs wpreds wlatches;
    cert_step_circ <<-
      encode_is_witness_step wcirc wnext wcnstrs wpreds wlatches;
    (* encode certificate conditions in conjunctive normal form *)
    cert_reset_cnf <<- aig_to_cnf cert_reset_circ (Named (Ext «reset»));
    cert_transition_cnf <<- aig_to_cnf cert_transition_circ (Named (Ext «transition»));
    cert_property_cnf <<- aig_to_cnf cert_property_circ (Named (Ext «property»));
    cert_base_cnf <<- aig_to_cnf cert_base_circ (Named (Ext «base»));
    cert_step_cnf <<- aig_to_cnf cert_step_circ (Named (Ext «step»));
    return
    (cert_reset_cnf, cert_transition_cnf, cert_property_cnf, cert_base_cnf, cert_step_cnf)
  od
End

(* Testing ********************************************************************)

val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val witness = mlstringSyntax.mlstring_from_file "./examples/06_witness.aig";

val cnf = EVAL “main (explode ^model) (explode ^witness)” |> concl |> rhs;
