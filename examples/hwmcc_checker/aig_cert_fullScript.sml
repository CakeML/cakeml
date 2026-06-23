(*
  Verified certificate checker for the Hardware Model Checking Competition.
*)
Theory aig_cert_full
Ancestors
  mlint (* for num_to_str *)
  aig_parse aig_cert_encode aig_to_cnf
Libs
  preamble

(* TODO wlatches might have duplicates after applying the shared latches map? *)

Definition make_cert_cnf_def:
  make_cert_cnf mstr wstr =
  do
    (* -- parse model and witness -- *)
    (maig, rest) <- parse_aiger mstr 0;
    (waig, maps, rest) <- parse_aiger_and_symbols wstr 0;
    (* -- model -- *)
    mcounts <<- maig.counts;
    micnt <<- mcounts.inputs;
    mlcnt <<- mcounts.latches;
    mlatch_start <<- micnt + 1;
    mcirc <<- maig.circuit;
    mreset <<- fromAList maig.reset;
    mreset <<- (λl. lookup l mreset);
    mnext <<- fromAList maig.next;
    mnext  <<- (λl. case lookup l mnext of
                    | SOME lit => lit
                    | NONE => (Base Ff, F) (* should not happen *));
    mpreds <<-
      MAP not
        (if mcounts.bad = 0 ∧ mcounts.justice = 0 then maig.outputs
         else maig.bad);
    mcnstrs <<- maig.constraints;
    mlatches <<- GENLIST (λk. mlatch_start + k) mcounts.latches;
    (* -- witness -- *)
    wcounts <<- waig.counts;
    wlatch_start <<- wcounts.inputs + 1;
    iren <<- maps.shared_inputs;
    lren <<- maps.shared_latches;
    wcirc <<- shared_circuit micnt mlcnt iren lren waig.circuit;
    wreset <<- fromAList (shared_latches micnt mlcnt iren lren waig.reset);
    wreset <<- (λl. lookup l wreset);
    wnext_alist <<- shared_latches micnt mlcnt iren lren waig.next;
    wnext <<- fromAList wnext_alist;
    wnext  <<- (λl. case lookup l wnext of
                    | SOME lit => lit
                    | NONE => (Base Ff, F));
    wpreds <<-
      MAP (not ∘ shared_lit micnt mlcnt iren lren)
        (if wcounts.bad = 0 ∧ wcounts.justice = 0 then waig.outputs
         else waig.bad);
    wcnstrs <<- MAP (shared_lit micnt mlcnt iren lren) waig.constraints;
    wlatches <<-
      GENLIST (λk. shared_latch_key micnt mlcnt iren lren (wlatch_start + k))
        wcounts.latches;
    interv <<-
      make_interv micnt mlcnt wicnt wmax_latch iren lren wnext_alist
        (maps.intervened_latches);
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
(*
    cert_liveness_circ <<-
      encode_is_witness_liveness
        mcirc mcnstrs mlive
        wcirc wnext wcnstrs wpreds wlive wlatches interv;
*)
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

Definition make_cert_strings_def:
  make_cert_strings mstr wstr =
  do
    (reset, transition, property, base, step) <- make_cert_cnf mstr wstr;
    return
      (cnf_to_string reset, cnf_to_string transition,
            cnf_to_string property, cnf_to_string base, cnf_to_string step)
  od
End

(* Testing ********************************************************************)

(*
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
  EVAL “make_cert_strings ^model ^witness”
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

val () = app (fn (name, ok) =>
    print (name ^ ": " ^ (if ok then "UNSAT (verified)" else "*** NOT UNSAT ***") ^ "\n"))
  (map (fn name => (name, check_unsat name)) cnf_names);
*)
