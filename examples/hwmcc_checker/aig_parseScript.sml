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

(* TODO Are counts part of the circuit, or just an implementation detail? *)
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

(* General parsing functionality **********************************************)

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

val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val aig = EVAL “parse_aiger (explode ^model)” |> concl |> rhs;

val model = mlstringSyntax.mlstring_from_file "./examples/06_witness.aig";
val aig = EVAL “parse_aiger (explode ^model)” |> concl |> rhs;
