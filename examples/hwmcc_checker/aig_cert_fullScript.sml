(*
  Verified certificate checker for the Hardware Model Checking Competition.
*)
Theory aig_cert_full
Ancestors
  listRange
  mlint (* for num_to_str *)
  aig_parse aig_cert_encode aig_to_cnf
Libs
  preamble

(* TODO Move? *)
(* Convert cnf to string  *****************************************************)

(* lifting some constants to avoid unnecessary reallocation *******************)

(* TODO This can be removed once the compiler automatically lifts constants. *)

Definition space_def:
  space = « »
End

Definition clause_end_def:
  clause_end = [«0\n»]
End

(* to_string functions  *******************************************************)

Definition lit_to_string_def:
  (lit_to_string (Pos (i: num)) = toString i) ∧
  (lit_to_string (Neg (i: num)) = «-» ^ toString i)
End

Definition clause_to_string_def:
  clause_to_string (clause: num clause) =
  concat (MAP (λn. (lit_to_string n) ^ space) clause ++ clause_end)
End

Definition cnf_to_string_def:
  cnf_to_string (cnf: num clause list, limit: num) =
  let
    header    = [«p cnf »; toString limit; space; toString (LENGTH cnf); «\n»];
    clauses   = MAP clause_to_string cnf
  in
    concat (header ++ clauses)
End

(* end-to-end processing of model and witness *********************************)

Definition range_inter_def:
  range_inter m n xs = FILTER (λh. m ≤ h ∧ h ≤ n) xs
End

Theorem range_inter_thm:
  range_inter m n xs = ys ⇒ set ys = set [m .. n] ∩ set xs
Proof
  rw [range_inter_def] >> simp [EXTENSION, LIST_TO_SET_FILTER]
QED

Definition parse_and_process_def:
  parse_and_process mstr wstr =
  do
    (maig, rest) <- parse_aiger mstr 0;
    (waig, maps, rest) <- parse_aiger_and_symbols wstr 0;
    (* -- model -- *)
    mcounts <<- maig.counts;
    micnt <<- mcounts.inputs;
    mlcnt <<- mcounts.latches;
    mlatch_start <<- micnt + 1;
    mmax_latch <<- micnt + mlcnt;
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
    mlatches <<- [mlatch_start .. mmax_latch];
    mlatches <<- GENLIST (λk. mlatch_start + k) mcounts.latches;
    mfair <<- MAP not maig.fairness;
    mjust <<- maig.justice;
    mlive <<- MAP (λsignals. mfair ++ (MAP not signals)) mjust;
    (* -- witness -- *)
    wcounts <<- waig.counts;
    wicnt <<- wcounts.inputs;
    wlcnt <<- wcounts.latches;
    wlatch_start <<- wicnt + 1;
    wmax_latch <<- wicnt + wlcnt;
    iren <<- maps.shared_inputs;
    lren <<- maps.shared_latches;
    (iren, lren) <<-
      if isEmpty iren ∧ isEmpty lren then
        default_shared micnt mlcnt wicnt wlcnt
      else (iren, lren);
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
        wlcnt;
    wfair <<- MAP (not ∘ shared_lit micnt mlcnt iren lren) waig.fairness;
    wjust <<- waig.justice;
    wlive <<-
      MAP
        (λsignals.
           wfair ++
           (MAP (not ∘ shared_lit micnt mlcnt iren lren) signals)) wjust;
    interv <<-
      make_interv micnt mlcnt wicnt wmax_latch iren lren wnext_alist
        (maps.intervened_latches);
    interv <<- FLOOKUP interv;
    klatches <<- range_inter mlatch_start mmax_latch wlatches;
    return
      (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches,
       wcirc, wreset, wnext, wpreds, wcnstrs, wlive, wlatches,
       interv, klatches)
  od
End

(* TODO Maybe the constant strings «» should be translated once and
   then reused everywhere (including during encoding)? *)

Definition make_reset_string_def:
  make_reset_string
    (mcirc: (num, num, num) circuit) mreset mcnstrs mlatches
    (wcirc: (num, num, num) circuit) wreset wcnstrs wlatches klatches
  =
  let
    name = «reset»;
    circ =
      encode_is_witness_reset
        mcirc mreset mcnstrs mlatches
        wcirc wreset wcnstrs wlatches klatches;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_transition_string_def:
  make_transition_string
    (mcirc: (num, num, num) circuit) mnext mcnstrs mlatches
    (wcirc: (num, num, num) circuit) wnext wcnstrs wlatches klatches
  =
  let
    name = «transition»;
    circ =
      encode_is_witness_transition
        mcirc mnext mcnstrs mlatches
        wcirc wnext wcnstrs wlatches klatches;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_property_string_def:
  make_property_string
    (mcirc: (num, num, num) circuit) mcnstrs mpreds
    (wcirc: (num, num, num) circuit) wcnstrs wpreds
  =
  let
    name = «property»;
    circ =
      encode_is_witness_property mcirc mcnstrs mpreds wcirc wcnstrs wpreds;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_base_string_def:
  make_base_string
    (wcirc: (num, num, num) circuit) wreset wcnstrs wpreds wlatches
  =
  let
    name = «base»;
    circ =
      encode_is_witness_base wcirc wreset wcnstrs wpreds wlatches;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_step_string_def:
  make_step_string
    (wcirc: (num, num, num) circuit) wnext wcnstrs wpreds wlatches
  =
  let
    name = «step»;
    circ =
      encode_is_witness_step wcirc wnext wcnstrs wpreds wlatches;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_liveness_string_def:
  make_liveness_string
    (mcirc: (num, num, num) circuit) mcnstrs mlive
    (wcirc: (num, num, num) circuit) wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    name = «liveness»;
    circ =
      encode_is_witness_liveness
        mcirc mcnstrs mlive
        wcirc wnext wcnstrs wpreds wlive wlatches interv;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_decrease_string_def:
  make_decrease_string
    (wcirc: (num, num, num) circuit) wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    name = «decrease»;
    circ =
      encode_is_witness_decrease
        wcirc wnext wcnstrs wpreds wlive wlatches interv;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_closure_string_def:
  make_closure_string
    (wcirc: (num, num, num) circuit) wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    name = «closure»;
    circ =
      encode_is_witness_closure
        wcirc wnext wcnstrs wpreds wlive wlatches interv;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

Definition make_consistent_string_def:
  make_consistent_string
    (wcirc: (num, num, num) circuit) wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    name = «consistent»;
    circ =
      encode_is_witness_consistent
        wcirc wnext wcnstrs wpreds wlive wlatches interv;
    cnf = aig_to_cnf circ (Named (Ext name))
  in
    (name, cnf_to_string cnf)
End

(* Testing ********************************************************************)

(*
val coch_dir  = "/home/daniel/code/coch-demo";

fun write_file path s =
  let val os = TextIO.openOut path
  in TextIO.output (os, s); TextIO.closeOut os end;

fun read_file path =
  let val is = TextIO.openIn path
  in TextIO.inputAll is before TextIO.closeIn is end;

(* Generate the five CNF obligations for the example pair and write them out. *)
val model   = mlstringSyntax.mlstring_from_file "./examples/intervention_model.aig";
val witness = mlstringSyntax.mlstring_from_file "./examples/intervention_witness.aig";

fun to_string_pair t =
  let val (a, b) = pairSyntax.dest_pair t
  in (mlstringSyntax.dest_mlstring a, mlstringSyntax.dest_mlstring b) end

val (cnf_names, cnfs) =
  EVAL “make_cert_strings ^model ^witness”
    |> concl |> rhs |> rand |> listSyntax.dest_list |> fst
    |> map to_string_pair |> ListPair.unzip

val () =
  ListPair.app
    (fn (name, cnf) =>
       write_file (coch_dir ^ "/" ^ name ^ ".cnf") cnf)
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
