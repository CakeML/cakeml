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
    next        : (num, num, num) lit num_map;
    reset       : (num, num, num) lit num_map;
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

Definition consume_space_def:
  consume_space [] = [] ∧
  consume_space (c::rest) =
  if c = #" " then consume_space rest else (c::rest)
End

Theorem consume_space_mono[local]:
  ∀str. consume_space str = str' ⇒ LENGTH str' ≤ LENGTH str
Proof
  Induct >> rw [consume_space_def] >> simp []
QED

Definition consume_line_def:
  consume_line [] = [] ∧
  consume_line (c::rest) =
  if c = #"\n" then rest else consume_line rest
End

Theorem consume_line_mono[local]:
  ∀str. LENGTH (consume_line str) ≤ LENGTH str
Proof
  Induct >> rw [consume_line_def]
QED

Definition is_char_def:
  is_char c [] = F ∧
  is_char c (c'::rest) = (c' = c)
End

Definition expect_char_def:
  expect_char (c: char) [] =
  error (concat [«expected '»; toString c; «' got nothing»], []) ∧
  expect_char c (c'::rest) =
  if c' ≠ c then
    error (concat [«expected '»; toString c; «' got '»; toString c'; «'»], rest)
  else return rest
End

Definition parse_number_aux_def:
  parse_number_aux [] acc = (acc, []) ∧
  parse_number_aux (c::rest) acc =
  if ¬isDigit c then (acc, c::rest)
  else parse_number_aux rest (10 * acc + (ORD c - ORD #"0"))
End

Definition parse_number_def:
  parse_number [] = error («expected digit», []) ∧
  parse_number (c::rest) =
  if ¬isDigit c then error («expected digit», c::rest)
  else return (parse_number_aux rest (ORD c - ORD #"0"))
End

Theorem parse_number_aux_mono[local]:
  ∀str acc.
    parse_number_aux str acc = (res, rest) ⇒ LENGTH rest ≤ LENGTH str
Proof
  Induct >> rw [parse_number_aux_def] >> simp []
  >> last_x_assum drule >> simp []
QED

Theorem parse_number_return_mono[local]:
  parse_number str = return (res, rest) ⇒ LENGTH rest ≤ LENGTH str
Proof
  Cases_on ‘str’
  >> rw [parse_number_def, AllCaseEqs()]
  >> drule parse_number_aux_mono >> simp []
QED

Definition parse_numbers_aux_def:
  parse_numbers_aux 0 acc str = return (REVERSE acc, str) ∧
  parse_numbers_aux (SUC n) acc str =
  do
    (number, rest) <- parse_number str;
    rest <- expect_char #"\n" rest;
    parse_numbers_aux n (number::acc) rest
  od
End

(* Parses newline-separated numbers. *)
Definition parse_numbers_def:
  parse_numbers j str = parse_numbers_aux j [] str
End

(* Parses an optional number (= has one leading space), defaulting to 0. *)
Definition parse_opt_number_def:
  parse_opt_number (#" "::rest) =
    do
      (n, rest) <- parse_number rest;
      return (n, rest)
    od ∧
  parse_opt_number str = return (0n, str)
End

Definition parse_leb_aux_def:
  parse_leb_aux [] ex n = error («unexpected end of input», []) ∧
  parse_leb_aux (c::rest) ex n =
    if ORD c ≥ 128 then
      parse_leb_aux rest (ex * 128) ((ORD c - 128) * ex + n)
    else return (ORD c * ex + n, rest)
End

(* Parses a number encoded in ULEB128 *)
Definition parse_leb_def:
  parse_leb str = parse_leb_aux str 1 0
End

(* Parsing the AIGER format ***************************************************)

Definition parse_counts_def:
  parse_counts str =
  do
    (* aig  *)
    rest <- expect_char #"a" str;
    rest <- expect_char #"i" rest;
    rest <- expect_char #"g" rest;
    rest <- expect_char #" " rest;
    (* M I L O A *)
    (maxvar,rest) <- parse_number rest;
    rest <- expect_char #" " rest;
    (inputs,rest) <- parse_number rest;
    rest <- expect_char #" " rest;
    (latches,rest) <- parse_number rest;
    rest <- expect_char #" " rest;
    (outputs,rest) <- parse_number rest;
    rest <- expect_char #" " rest;
    (ands,rest) <- parse_number rest;
    (*  B C J F\n (optional) *)
    (bad,rest) <- parse_opt_number rest;
    (constraints,rest) <- parse_opt_number rest;
    (justice,rest) <- parse_opt_number rest;
    (fairness,rest) <- parse_opt_number rest;
    rest <- expect_char #"\n" rest;
    assert («invalid maximal variable index», rest)
      (maxvar = inputs + latches + ands);
    return
      (<| maxvar := maxvar ; inputs := inputs ; latches := latches;
          outputs := outputs ; ands := ands ;
          bad := bad ; constraints := constraints ;
          justice := justice; fairness := fairness |>,
       rest)
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
  parse_lit max_input max_latch str =
  do
    (lit, rest)  <- parse_number str;
    return (convert_lit max_input max_latch lit, rest)
  od
End

(* Returns the parsed literals in reversed order. *)
Definition parse_literals_def:
  parse_literals max_input max_latch 0 acc str = return (acc, str) ∧
  parse_literals max_input max_latch (SUC n) acc str =
  do
    (lit, rest) <- parse_lit max_input max_latch str;
    rest <- expect_char #"\n" rest;
    parse_literals max_input max_latch n (lit::acc) rest
  od
End

Definition parse_justices_aux_def:
  parse_justices_aux max_input max_latch [] acc str = return (acc, str) ∧
  parse_justices_aux max_input max_latch (s::ss) acc str =
  do
    (row, rest) <- parse_literals max_input max_latch s [] str;
    parse_justices_aux max_input max_latch ss (row::acc) rest
  od
End

(* Returns the parsed justice lists in reversed order.

   Since a justice property consists of a list of literals, we first parse
   the lengths of these lists for each of the j justice properties,
   after which we can parse the literals. *)
Definition parse_justices_def:
  parse_justices max_input max_latch j str =
  do
    (sizes, rest) <- parse_numbers j str;
    parse_justices_aux max_input max_latch sizes [] rest
  od
End

Definition parse_latches_def:
  parse_latches max_input max_latch 0 latch next reset str =
    return ((next, reset), str) ∧
  parse_latches max_input max_latch (SUC n) latch next reset str =
  do
    (next_lit, rest)  <- parse_lit max_input max_latch str;
    (reset_lit, rest) <- parse_opt_number rest;
    rest <- expect_char #"\n" rest;
    next <<- insert latch next_lit next;
    reset <<-
      if reset_lit = 2 * latch then reset
      else insert latch (convert_lit max_input max_latch reset_lit) reset;
    parse_latches max_input max_latch n (latch + 1) next reset rest
  od
End

Definition parse_ands_def:
  parse_ands max_input max_latch 0 lhs ands str = return (ands, str) ∧
  parse_ands max_input max_latch (SUC n) lhs ands str =
  do
    (delta0, rest) <- parse_leb str;
    (delta1, rest) <- parse_leb rest;
    rhs0 <<- 2 * lhs  - delta0;
    rhs1 <<- rhs0     - delta1;
    rhs0 <<- convert_lit max_input max_latch rhs0;
    rhs1 <<- convert_lit max_input max_latch rhs1;
    ands <<- (lhs, [rhs0; rhs1])::ands;
    parse_ands max_input max_latch n (lhs + 1) ands rest
  od
End

Definition parse_aiger_def:
  parse_aiger str =
  do
    (counts, rest) <- parse_counts str;
    max_input <<- counts.inputs;
    max_latch <<- max_input + counts.latches;
    ((next, reset), rest) <-
      parse_latches max_input max_latch counts.latches (max_input + 1)
        LN LN rest;
    (outputs, rest) <-
      parse_literals max_input max_latch counts.outputs [] rest;
    (bad, rest) <-
      parse_literals max_input max_latch counts.bad [] rest;
    (constraints, rest) <-
      parse_literals max_input max_latch counts.constraints [] rest;
    (justice, rest) <-
      parse_justices max_input max_latch counts.justice rest;
    (fairness, rest) <-
      parse_literals max_input max_latch counts.fairness [] rest;
    (circuit, rest) <-
      parse_ands max_input max_latch counts.ands (max_latch + 1) [] rest;
    return
      (<| counts := counts; next := next; reset := reset; outputs := outputs;
          bad := bad; constraints := constraints; justice := justice;
          fairness := fairness; circuit := circuit |>, rest)
  od
End

(* Parsing the maps *******************************************************)

(*
  The witness circuit can contain maps that determine the shared inputs and
  latches, and the interventions.
  These are stored either as comments (MAPPING or INTERVENTION), or as part of
  the symbol table.
  If the maps are not present in the file, a default mapping is chosen.

  The priority order is as follows:
  1. comment, 2. symbol table, 3. default mapping

  For shared inputs/latches, the default encoding in Certifaiger should
  correspond to what merge_circuit does already.
*)

Definition insert_if_def:
  insert_if b k v m = if b then insert k v m else m
End

Definition parse_entry_def:
  parse_entry kind shared_is shared_ls interv rest =
  do
    (pos, rest) <- parse_number rest;
    rest <<- consume_space rest;
    case rest of
    | (op::rest) =>
        if op = #"=" ∨ op = #"<" then
          do
            (lit, rest) <- parse_number (consume_space rest);
            return (
              if is_char #"\n" rest then
                let
                  interv    = insert_if (op = #"<") pos lit interv;
                  shared_is = insert_if (kind = #"i" ∧ op = #"=") pos lit
                    shared_is;
                  shared_ls = insert_if (kind = #"l" ∧ op = #"=") pos lit
                    shared_ls;
                in ((shared_is, shared_ls, interv), consume_line rest)
              else ((shared_is, shared_ls, interv), consume_line rest))
          od
        else return ((shared_is, shared_ls, interv), consume_line rest)
    | _ => error («unexpected EOF while parsing symbol table», rest)
  od
End

Theorem parse_entry_mono[local]:
  parse_entry kind shared_is shared_ls interv rest =
  return ((shared_is', shared_ls', interv'), rest')
  ⇒
  LENGTH rest' ≤ LENGTH rest
Proof
  rw [parse_entry_def, oneline bind_def, AllCaseEqs(), PULL_EXISTS]
  >> rpt (pairarg_tac >> gvs [AllCaseEqs()])
  >> imp_res_tac parse_number_return_mono
  >> imp_res_tac consume_space_mono
  >> rename [‘consume_line rest₃’]
  >> qspec_then ‘rest₃’ assume_tac consume_line_mono >> gvs []
  >> rename1 ‘parse_number (consume_space rest₄)’
  >> Cases_on ‘consume_space rest₄’
  >> imp_res_tac consume_space_mono >> gvs []
QED

Definition parse_symbol_table_aux_def:
  parse_symbol_table_aux shared_is shared_ls interv str =
  case str of
  | c::rest =>
      if c = #"c" then
        (* c\n marks the beginning of the comment section *)
        (case rest of
         | (#"\n"::_) => return ((shared_is, shared_ls, interv), str)
         | _ => parse_symbol_table_aux shared_is shared_ls interv (consume_line rest))
      else if c = #"i" ∨ c = #"l" then
        case parse_entry c shared_is shared_ls interv rest of
        | error err => error err
        | return ((shared_is, shared_ls, interv), str') =>
            parse_symbol_table_aux shared_is shared_ls interv str'
      else
        parse_symbol_table_aux shared_is shared_ls interv (consume_line rest)
  | _ => return ((shared_is, shared_ls, interv), str)
Termination
  wf_rel_tac ‘measure (λ(sis,sls,iv,str). LENGTH str)’
  >> rw [consume_line_def]
  >> imp_res_tac parse_entry_mono >> gvs []
  >> rename1 ‘consume_line rest’
  >> qspec_then ‘rest’ assume_tac consume_line_mono >> gvs []
End

Definition parse_symbol_table_def:
  parse_symbol_table str =
  do
    ((shared_is, shared_ls, interv), rest) <-
      parse_symbol_table_aux LN LN LN str;
    return
      (<| shared_inputs := shared_is; shared_latches := shared_ls;
          intervened_latches := interv |>, rest)
  od
End

Definition parse_witness_def:
  parse_witness str =
  do
    (aiger, rest) <- parse_aiger str;
    (maps, rest) <- parse_symbol_table rest;
    return (aiger, maps, rest)
  od
End

(* Applying the map for shared inputs/latched *********************************)

Definition replace_lits_def:
  replace_lits wmax_input mmax_input mmax_latch in_map latch_map [] = [] ∧
  replace_lits wmax_input mmax_input mmax_latch in_map latch_map (lit::rest) =
  let
    rest = replace_lits wmax_input mmax_input mmax_latch in_map latch_map rest;
    (v,b) = lit;
  in
    case v of
    | Name _ => lit::rest
    | Base Ff => lit::rest
    | Base (Input i) =>
      (case lookup (i - 1) in_map of
       | NONE => lit::rest
       | SOME i =>
         (let (mv, mb) = convert_lit mmax_input mmax_latch i in
            (mv, b ≠ mb)::rest))  (* xor of model and witness polarities *)
    | Base (Latch l) =>
      (case lookup (l - wmax_input - 1) latch_map of
       | NONE => lit::rest
       | SOME l =>
         (let (mv, mb) = convert_lit mmax_input mmax_latch l in
            (mv, b ≠ mb)::rest))
End

Definition replace_def:
  replace wmax_input mmax_input mmax_latch in_map latch_map
    (circuit: (num, num, num) circuit) =
  MAP (I ## replace_lits wmax_input mmax_input mmax_latch in_map latch_map)
    circuit
End

(* Testing ********************************************************************)

val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val [maig, mrest] =
  EVAL “parse_aiger (explode ^model)” |> concl |> rhs |> rand |> strip_pair;

val witness = mlstringSyntax.mlstring_from_file "./examples/06_witness.aig";
val [waig, wmaps, wrest] =
  EVAL “parse_witness (explode ^witness)” |> concl |> rhs |> rand |> strip_pair;

val witness' =
  EVAL “replace
        ^(waig).counts.inputs ^(maig).counts.inputs
        (^(maig).counts.inputs + ^(maig).counts.latches)
        ^(wmaps).shared_inputs ^(wmaps).shared_latches
        ^waig.circuit”
    |> concl |> rhs
