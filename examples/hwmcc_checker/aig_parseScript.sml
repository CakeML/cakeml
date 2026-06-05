(*
  Parser for the AIGER format.
*)
Theory aig_parse
Ancestors
  sptree errorMonad mlstring aig
Libs
  preamble

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "error";

(* TODO Add intervention default *)

(* Types **********************************************************************)

Datatype:
  counts = <|
    maxvar      : num;
    inputs      : num;
    latches     : num;
    outputs     : num;
    ands        : num;
    bad         : num;
    constraints : num;
    justice     : num;
    fairness    : num;
  |>
End

Datatype:
  aiger = <|
    counts      : counts;
    next        : (num, (num, num, num) lit) alist;
    reset       : (num, (num, num, num) lit) alist;
    outputs     : (num, num, num) lit list;
    bad         : (num, num, num) lit list;
    constraints : (num, num, num) lit list;
    justice     : (num, num, num) lit list list;
    fairness    : (num, num, num) lit list;
    circuit     : (num, num, num) circuit;
  |>
End

(* Keeps track of maps from witness variables to model AIGER literals.

   We use "AIGER literal" to differentiate the literal in AIGER from
   the literal type defined in aigTheory.
   To convert from the former to the latter, see convert_lit_def below.
 *)
Datatype:
  maps = <|
    shared_inputs        : num num_map;
    shared_latches       : num num_map;
    intervened_latches   : num num_map;
  |>
End

(* General parsing functionality **********************************************)

Definition is_char_def:
  is_char s i c =
  if strlen s ≤ i then F
  else strsub s i = c
End

Definition consume_space_def:
  consume_space s i =
  if strlen s ≤ i then i
  else if strsub s i ≠ #" " then i
  else consume_space s (i + 1)
Termination
  wf_rel_tac ‘measure (λ(s,i). strlen s - i)’
End

Theorem consume_space_mono[local]:
  ∀s i. i ≤ consume_space s i
Proof
  recInduct consume_space_ind >> rw[]
  >> rw [Once consume_space_def]
  >> gvs []
QED

Definition consume_line_def:
  consume_line s i =
  if strlen s ≤ i then i
  else if strsub s i = #"\n" then (i + 1)
  else consume_line s (i + 1)
Termination
  wf_rel_tac ‘measure (λ(s,i). strlen s - i)’
End

Theorem consume_line_mono[local]:
  ∀s i. i ≤ consume_line s i
Proof
  recInduct consume_line_ind >> rw[]
  >> rw [Once consume_line_def]
  >> gvs []
QED

Definition expect_char_def:
  expect_char s i c =
  if strlen s ≤ i then
    error (concat [«expected '»; toString c; «' got nothing»], i)
  else
    let c' = strsub s i in
      if c' ≠ c then
        error
          (concat [«expected '»; toString c; «' got '»; toString c'; «'»], i)
      else return (i + 1)
End

Definition parse_number_aux_def:
  parse_number_aux s i acc =
  if strlen s ≤ i then (acc, i)
  else
    let c = strsub s i in
      if ¬isDigit c then (acc, i)
      else parse_number_aux s (i + 1) (10 * acc + (ORD c - ORD #"0"))
Termination
  wf_rel_tac ‘measure (λ(s,i,acc). strlen s - i)’
End

Theorem parse_number_aux_mono[local]:
  ∀s i acc. parse_number_aux s i acc = (res, i') ⇒ i ≤ i'
Proof
  recInduct parse_number_aux_ind >> rw []
  >> pop_assum mp_tac
  >> rw [Once parse_number_aux_def]
  >> gvs []
QED

Definition parse_number_def:
  parse_number s i =
  if strlen s ≤ i then error («expected digit», i)
  else
    let c = strsub s i in
      if ¬isDigit c then
        error (concat [«expected digit, received '»; toString c; «'»], i)
      else
        return (parse_number_aux s (i + 1) (ORD c - ORD #"0"))
End

Theorem parse_number_return_mono[local]:
  parse_number s i = return (res, i') ⇒ i ≤ i'
Proof
  rw [parse_number_def, AllCaseEqs()]
  >> drule parse_number_aux_mono >> simp []
QED

Definition parse_numbers_aux_def:
  parse_numbers_aux s i 0 acc = return (REVERSE acc, i) ∧
  parse_numbers_aux s i (SUC n) acc =
  do
    (number, i) <- parse_number s i;
    i <- expect_char s i #"\n";
    parse_numbers_aux s i n (number::acc)
  od
End

(* Parses n newline-separated numbers. *)
Definition parse_numbers_def:
  parse_numbers s i n = parse_numbers_aux s i n []
End

(* Parses an optional number (= has one leading space), defaulting to 0. *)
Definition parse_opt_number_def:
  parse_opt_number s i =
  if strlen s ≤ i then return (0n, i)
  else if strsub s i ≠ #" " then return (0n, i)
  else parse_number s (i + 1)
End

Definition parse_leb_aux_def:
  parse_leb_aux s i ex n =
  if strlen s ≤ i then error («unexpected end of input», i)
  else
    let c = strsub s i in
    if ORD c ≥ 128 then
      parse_leb_aux s (i + 1) (ex * 128) ((ORD c - 128) * ex + n)
    else return (ORD c * ex + n, (i + 1))
Termination
  wf_rel_tac ‘measure (λ(s,i,acc). strlen s - i)’
End

(* Parses a number encoded in ULEB128 *)
Definition parse_leb_def:
  parse_leb s i = parse_leb_aux s i 1 0
End

(* Parsing the AIGER format ***************************************************)

Definition parse_counts_def:
  parse_counts s i =
  do
    (* aig  *)
    i <- expect_char s i #"a";
    i <- expect_char s i #"i";
    i <- expect_char s i #"g";
    i <- expect_char s i #" ";
    (* M I L O A *)
    (maxvar,i) <- parse_number s i;
    i <- expect_char s i #" ";
    (inputs,i) <- parse_number s i;
    i <- expect_char s i #" ";
    (latches,i) <- parse_number s i;
    i <- expect_char s i #" ";
    (outputs,i) <- parse_number s i;
    i <- expect_char s i #" ";
    (ands,i) <- parse_number s i;
    (*  B C J F\n (optional) *)
    (bad,i) <- parse_opt_number s i;
    (constraints,i) <- parse_opt_number s i;
    (justice,i) <- parse_opt_number s i;
    (fairness,i) <- parse_opt_number s i;
    i <- expect_char s i #"\n";
    assert («invalid maximal variable index», i)
      (maxvar = inputs + latches + ands);
    return
      (<| maxvar := maxvar ; inputs := inputs ; latches := latches;
          outputs := outputs ; ands := ands ;
          bad := bad ; constraints := constraints ;
          justice := justice; fairness := fairness |>,
       i)
  od
End

Definition convert_lit_def:
  convert_lit max_input max_latch lit : (num, num, num) lit =
  let
    v = lit DIV 2;
    v =
      if v = 0 then Base Ff
      else if v ≤ max_input then Base (Input v)
      else if v ≤ max_latch then Base (Latch v)
      else Name v;
    b = (lit MOD 2 = 1)
  in
    (v,b)
End

Definition parse_lit_def:
  parse_lit s i max_input max_latch =
  do
    (lit, i)  <- parse_number s i;
    return (convert_lit max_input max_latch lit, i)
  od
End

Definition parse_literals_aux_def:
  parse_literals_aux s i max_input max_latch 0 acc = return (acc, i) ∧
  parse_literals_aux s i max_input max_latch (SUC n) acc =
  do
    (lit, i) <- parse_lit s i max_input max_latch;
    i <- expect_char s i #"\n";
    parse_literals_aux s i max_input max_latch n (lit::acc)
  od
End

(* Returns the parsed literals in reversed order. *)
Definition parse_literals_def:
  parse_literals s i max_input max_latch n =
    parse_literals_aux s i max_input max_latch n []
End

Definition parse_justices_aux_def:
  parse_justices_aux s i max_input max_latch [] acc = return (acc, i) ∧
  parse_justices_aux s i max_input max_latch (n::ns) acc =
  do
    (row, i) <- parse_literals s i max_input max_latch n;
    parse_justices_aux s i max_input max_latch ns (row::acc)
  od
End

(* Returns the parsed justice lists in reversed order.

   Since a justice property consists of a list of literals, we first parse
   the lengths of these lists for each of the j justice properties,
   after which we can parse the literals. *)
Definition parse_justices_def:
  parse_justices s i max_input max_latch n =
  do
    (sizes, i) <- parse_numbers s i n;
    parse_justices_aux s i max_input max_latch sizes []
  od
End

Definition parse_latches_aux_def:
  parse_latches_aux s i max_input max_latch 0 latch next reset =
    return ((next, reset), i) ∧
  parse_latches_aux s i max_input max_latch (SUC n) latch next reset =
  do
    (next_lit, i)  <- parse_lit s i max_input max_latch;
    (reset_lit, i) <- parse_opt_number s i;
    i <- expect_char s i #"\n";
    next <<- (latch, next_lit)::next;
    reset <<-
      if reset_lit = 2 * latch then reset
      else (latch, (convert_lit max_input max_latch reset_lit))::reset;
    parse_latches_aux s i max_input max_latch n (latch + 1) next reset
  od
End

Definition parse_latches_def:
  parse_latches s i max_input max_latch n =
    parse_latches_aux s i max_input max_latch n (max_input + 1) [] []
End

Definition parse_ands_aux_def:
  parse_ands_aux s i max_input max_latch 0 lhs ands = return (ands, i) ∧
  parse_ands_aux s i max_input max_latch (SUC n) lhs ands =
  do
    (delta0, i) <- parse_leb s i;
    (delta1, i) <- parse_leb s i;
    rhs0 <<- 2 * lhs  - delta0;
    rhs1 <<- rhs0     - delta1;
    rhs0 <<- convert_lit max_input max_latch rhs0;
    rhs1 <<- convert_lit max_input max_latch rhs1;
    ands <<- (lhs, [rhs0; rhs1])::ands;
    parse_ands_aux s i max_input max_latch n (lhs + 1) ands
  od
End

Definition parse_ands_def:
  parse_ands s i max_input max_latch n =
   parse_ands_aux s i max_input max_latch n (max_latch + 1) []
End

Definition parse_aiger_def:
  parse_aiger s i =
  do
    (counts, i) <- parse_counts s i;
    max_input <<- counts.inputs;
    max_latch <<- max_input + counts.latches;
    ((next, reset), i) <- parse_latches s i max_input max_latch counts.latches;
    (outputs, i) <- parse_literals s i max_input max_latch counts.outputs;
    (bad, i) <- parse_literals s i max_input max_latch counts.bad;
    (constraints, i) <-
      parse_literals s i max_input max_latch counts.constraints;
    (justice, i) <- parse_justices s i max_input max_latch counts.justice;
    (fairness, i) <- parse_literals s i max_input max_latch counts.fairness;
    (circuit, i) <- parse_ands s i max_input max_latch counts.ands;
    return
      (<| counts := counts; next := next; reset := reset; outputs := outputs;
          bad := bad; constraints := constraints; justice := justice;
          fairness := fairness; circuit := circuit |>, i)
  od
End

(* Parsing the maps ***********************************************************)

(*
  The witness circuit can contain maps that determine the inputs and
  latches shared with the model, and the interventions required for checking
  liveness.
  These are stored either as comments or as part of the symbol table.
  For now, we only support the symbol table, falling back to a default
  if needed.

  For shared inputs/latches, the default mapping is an empty map, i.e., the
  identity map.
*)

Definition insert_if_def:
  insert_if b k v m = if b then insert k v m else m
End

Definition parse_entry_def:
  parse_entry s i latch_start kind shared_is shared_ls interv =
  do
    (pos, i) <- parse_number s i;
    i <<- consume_space s i;
    if strlen s ≤ i then error («unexpected EOF while parsing symbol table», i)
    else
      let op = strsub s i; i = i + 1 in
        if op = #"=" ∨ op = #"<" then
          do
            (lit, i) <- parse_number s (consume_space s i);
            assert («input or latch mapped to negative literal», i)
             (if kind = #"i" ∨ kind = #"l" then lit MOD 2 = 0 else T);
            assert («intervention maps something other than latches», i)
              (if op = #"<" then kind = #"l" else T);
            return (
              if is_char s i #"\n" then
                let
                  interv    = insert_if (op = #"<")
                    (latch_start + pos) lit interv;
                  shared_is = insert_if (kind = #"i" ∧ op = #"=")
                    (1 + pos) (lit DIV 2) shared_is;
                  shared_ls = insert_if (kind = #"l" ∧ op = #"=")
                    (latch_start + pos) (lit DIV 2) shared_ls;
                in ((shared_is, shared_ls, interv), consume_line s i)
              else ((shared_is, shared_ls, interv), consume_line s i))
          od
        else return ((shared_is, shared_ls, interv), consume_line s i)
  od
End

Theorem parse_entry_mono[local]:
  parse_entry s i latch_start kind shared_is shared_ls interv =
  return ((shared_is', shared_ls', interv'), i') ⇒
  i ≤ i'
Proof
  simp [parse_entry_def, oneline bind_def]
  >> TOP_CASE_TAC
  >> rpt (pairarg_tac >> gvs [])
  >> drule_then assume_tac parse_number_return_mono
  >> IF_CASES_TAC >> gvs []
  >> rename1 ‘consume_space s i₂ + 1’
  >> qmatch_goalsub_abbrev_tac ‘parse_number s (consume_space s (i₃ + 1))’
  >> qmatch_goalsub_abbrev_tac ‘parse_number s i₄’
  >> ‘i₂ ≤ i₃’ by simp [Abbr ‘i₃’, consume_space_mono]
  >> ‘i₃ ≤ i₄’ by
    (qspecl_then [‘s’, ‘i₃ + 1’] assume_tac consume_space_mono
     >> simp [Abbr ‘i₄’])
  >> reverse IF_CASES_TAC
  >-
   (‘i₃ ≤ consume_line s (i₃ + 1)’ by
      (qspecl_then [‘s’, ‘i₃ + 1’] assume_tac consume_line_mono >> simp [])
    >> simp [])
  >> TOP_CASE_TAC
  >> rpt (pairarg_tac >> gvs [AllCaseEqs()])
  >> rw []
  >> imp_res_tac parse_number_return_mono
  >> rename1 ‘consume_line s i₅’
  >> qspecl_then [‘s’, ‘i₅’] assume_tac consume_line_mono >> simp []
QED

Definition parse_symbol_table_aux_def:
  parse_symbol_table_aux s i latch_start shared_is shared_ls interv =
  if strlen s ≤ i then return ((shared_is, shared_ls, interv), i)
  else
    let c = strsub s i in
      if c = #"c" then
        (* c\n marks the beginning of the comment section *)
        if is_char s (i + 1) #"\n" then
          return ((shared_is, shared_ls, interv), i)
        else
          parse_symbol_table_aux s (consume_line s i) latch_start
            shared_is shared_ls interv
      else if c = #"i" ∨ c = #"l" then
        case parse_entry s (i + 1) latch_start c shared_is shared_ls interv of
        | error err => error err
        | return ((shared_is, shared_ls, interv), i) =>
            parse_symbol_table_aux s i latch_start shared_is shared_ls interv
      else
        parse_symbol_table_aux s (consume_line s i)
          latch_start shared_is shared_ls interv
Termination
  wf_rel_tac ‘measure (λ(s,i,ls,sis,sls,iv). strlen s - i)’
  >> rw []
  >> imp_res_tac parse_entry_mono >> gvs []
  >> rename1 ‘consume_line s i’
  >-
   (‘i < consume_line s i’ by
      (simp [Once consume_line_def]
       >> IF_CASES_TAC
       >> ‘i + 1 ≤ consume_line s (i + 1)’ suffices_by simp []
       >> simp [consume_line_mono])
    >> simp [])
  >> ‘i < consume_line s i’ by
    (simp [Once consume_line_def]
     >> ‘i + 1 ≤ consume_line s (i + 1)’ suffices_by simp []
     >> simp [consume_line_mono])
  >> simp []
End

Definition parse_symbol_table_def:
  parse_symbol_table s i latch_start =
  do
    ((shared_is, shared_ls, interv), i) <-
      parse_symbol_table_aux s i latch_start LN LN LN;
    return
      (<| shared_inputs := shared_is; shared_latches := shared_ls;
          intervened_latches := interv |>, i)
  od
End

Definition parse_aiger_and_symbols_def:
  parse_aiger_and_symbols s i =
  do
    (aiger, i) <- parse_aiger s i;
    counts <<- aiger.counts;
    latch_start <<- counts.inputs + 1;
    (maps, i) <- parse_symbol_table s i latch_start;
    return (aiger, maps, i)
  od
End

(* Applying the map for shared inputs/latched *********************************)

(* {i,l}ren is short for {input,latch}renaming *)

Definition shared_lit_def:
  shared_lit iren lren (v, b) =
  let
    v =
      case v of
      | Base (Input i) =>
        (case lookup i iren of NONE => v | SOME i => Base (Input i))
      | Base (Latch l) =>
        (case lookup l lren of NONE => v | SOME l => Base (Latch l))
      | _ => v
  in
    (v, b)
End

(* Applies the shared map for input and latches to next and reset. *)
Definition shared_latches_def:
  shared_latches iren lren (lm: (num, (num, num, num) lit) alist) =
  MAP
    ((λl. case lookup l lren of NONE => l | SOME l => l) ##
     shared_lit iren lren) lm
End

Definition shared_circuit_def:
  shared_circuit iren lren (circuit: (num, num, num) circuit) =
    MAP (I ## MAP (shared_lit iren lren)) circuit
End

(* Testing ********************************************************************)
(*
val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val [maig, midx] =
  EVAL “parse_aiger ^model 0” |> concl |> rhs |> rand |> strip_pair;

val witness = mlstringSyntax.mlstring_from_file "./examples/06_witness.aig";
val [waig, wmaps, midx] =
  EVAL “parse_aiger_and_symbols ^witness 0”
    |> concl |> rhs |> rand |> strip_pair;

val witness' =
  EVAL “shared_circuit
        ^(wmaps).shared_inputs ^(wmaps).shared_latches
        ^waig.circuit”
    |> concl |> rhs
*)
