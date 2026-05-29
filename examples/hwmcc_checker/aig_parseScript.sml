(*
  Parser for the AIGER format.
*)
Theory aig_parse
Ancestors
  mlstring errorMonad
Libs
  preamble

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "error";

Datatype:
  aig_header = <| maxvar : num; inputs : num; latches : num;
                  outputs : num; ands : num; bad : num;
                  constraints : num; justice : num; fairness : num |>
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
  if ¬isDigit c then error («expected digit», rest)
  else return (parse_number_aux rest (ORD c - ORD #"0"))
End

Definition expect_char_def:
  expect_char (c: char) [] =
  error (concat [«expected '»; toString c; «' got nothing»], []) ∧
  expect_char c (c'::rest) =
  if c' ≠ c then
    error (concat [«expected '»; toString c; «' got '»; toString c'; «'»], rest)
  else return rest
End

Definition parse_aig_def:
  parse_aig str =
  do
    rest <- expect_char #"a" str;
    rest <- expect_char #"i" rest;
    rest <- expect_char #"g" rest;
    expect_char #" " rest;
  od
End

Definition parse_opt_number_def:
  parse_opt_number (#" "::rest) =
    do
      (n, rest) <- parse_number rest;
      return (SOME n, rest)
    od ∧
  parse_opt_number str = return (NONE, str)
End

Definition get_num_def:
  get_num NONE = 0n ∧
  get_num (SOME n) = n
End

Definition parse_header_def:
  parse_header str =
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
          bad := get_num bad ; constraints := get_num constraints ;
          justice := get_num justice; fairness := get_num fairness |>,
       rest)
  od
End

Definition parse_latch_def:
  parse_latch str =
  do
    (next, rest) <- parse_number str;
    (reset, rest) <- parse_opt_number rest;
    return ((next, reset), rest)
  od
End

val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val aig = EVAL “parse_header (explode ^model)” |> concl |> rhs;
