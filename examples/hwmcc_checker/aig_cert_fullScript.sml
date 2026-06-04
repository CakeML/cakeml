(*
  Verified certificate checker for the Hardware Model Checking Competition.
*)
Theory aig_cert_full
Ancestors
  mlint (* for num_to_str *)
  aig_parse aig_cert_encode aig_to_cnf
Libs
  preamble

Definition make_cert_cnf_def:
  make_cert_cnf mstr wstr =
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
    mpreds <<-
      MAP not
        (if mcounts.bad = 0 ∧ mcounts.justice = 0 then maig.outputs
         else maig.bad);
    mcnstrs <<- maig.constraints;
    mlatches <<- GENLIST (λk. mmax_input + 1 + k) mcounts.latches;
    (* witness *)
    wcounts <<- waig.counts;
    wmax_input <<- wcounts.inputs;
    wmax_latch <<- wmax_input + wcounts.latches;
    (* apply sharing maps to witness *)
    in_map <<- maps.shared_inputs;
    latch_map <<- maps.shared_latches;
    wcirc <<- replace wmax_input mmax_input mmax_latch in_map latch_map
      waig.circuit;
    (* TODO I think we also need to apply the map to everything else here... *)
    wreset <<- (λl. lookup l waig.reset);
    wnext  <<- (λl. case lookup l waig.next of
                    | SOME lit => lit
                    | NONE => (Base Ff, F) (* should not happen *));
    wpreds <<-
      MAP not
        (if wcounts.bad = 0 ∧ wcounts.justice = 0 then waig.outputs
         else waig.bad);
    wcnstrs <<- waig.constraints;
    wlatches <<- GENLIST (λk. wmax_input + 1 + k) wcounts.latches;
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

Definition lit_to_string_def:
  (lit_to_string (Pos (i: num)) = toString i) ∧
  (lit_to_string (Neg (i: num)) = «-» ^ toString i)
End

Definition clause_to_string_def:
  clause_to_string (clause: num clause) =
  concat (MAP (λn. (lit_to_string n) ^ « ») clause ++ [«0\n»])
End

Definition cnf_to_string_def:
  cnf_to_string (cnf: num clause list, limit: num) =
  let
    clauses   = LENGTH cnf;
    header    =
      concat [«p cnf »; toString limit; « »; toString clauses; «\n»];
    clauses   = concat (MAP clause_to_string cnf)
  in
    header ^ clauses
End

Definition main_def:
  main mstr wstr =
  do
    (reset, transition, property, base, step) <- make_cert_cnf mstr wstr;
    return
      (cnf_to_string reset, cnf_to_string transition,
            cnf_to_string property, cnf_to_string base, cnf_to_string step)
  od
End

(* Testing ********************************************************************)

val coch_dir  = "/home/daniel/code/coch-demo";
val cnf_names = ["reset", "transition", "property", "base", "step"];

fun write_file path s =
  let val os = TextIO.openOut path
  in TextIO.output (os, s); TextIO.closeOut os end;

fun read_file path =
  let val is = TextIO.openIn path
  in TextIO.inputAll is before TextIO.closeIn is end;

(* Generate the five CNF obligations for the example pair and write them out. *)
val model   = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val witness = mlstringSyntax.mlstring_from_file "./examples/06_witness.aig";

val cnfs =
  EVAL “main (explode ^model) (explode ^witness)”
    |> concl |> rhs |> rand |> strip_pair;

val () =
  ListPair.app
    (fn (name, t) =>
       write_file (coch_dir ^ "/" ^ name ^ ".cnf") (mlstringSyntax.dest_mlstring t))
    (cnf_names, cnfs);

(* Check each obligation is UNSAT (LRAT-verified by cake_lpr). *)
fun check_unsat name =
  let
    val out = coch_dir ^ "/" ^ name ^ ".out"
    val cmd = "cd " ^ coch_dir ^ " && ./run-coch.sh " ^ name ^ ".cnf > " ^ out ^ " 2>&1"
    val _   = OS.Process.system cmd
  in
    String.isSubstring "s VERIFIED UNSAT" (read_file out)
  end;

val results = map (fn name => (name, check_unsat name)) cnf_names;

val () = app (fn (name, ok) =>
    print (name ^ ": " ^ (if ok then "UNSAT (verified)" else "*** NOT UNSAT ***") ^ "\n"))
  results;

val () = print ("\nCertificate " ^
  (if List.all #2 results then "ACCEPTED — all obligations UNSAT.\n"
                          else "REJECTED — some obligation is satisfiable.\n"));
