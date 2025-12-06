(*
  Module for parsing and pretty-printing s-expressions.
*)
Theory SexpProg
Ancestors
  mlsexp
  ml_translator
  std_prelude  (* OPTION_TYPE *)
  mlbasicsProg  (* Fail_exn *)
  TextIOProg
  TextIOProof
Libs
  preamble
  ml_translatorLib  (* translation_extends, register_type, .. *)
  basisFunctionsLib  (* add_cakeml *)
  cfLib (* x-tactics *)

(*--------------------------------------------------------------*
   Translation
 *--------------------------------------------------------------*)

val _ = translation_extends "TextIOProg";

val _ = register_type “:mlsexp$sexp”;
val _ = register_type “:mlsexp$token”;

Quote add_cakeml:
  fun read_string_aux input acc =
    case TextIO.b_input1 input of
      None => raise Fail "read_string_aux: unterminated string literal"
    | Some c =>
        if c = #"\"" then String.implode (List.rev acc) else
        if c = #"\\" then
          (case TextIO.b_input1 input of
             None => read_string_aux input acc (* causes error: unterminated string *)
           | Some e =>
               (if e = #"\\" then read_string_aux input (#"\""::acc) else
                if e = #"0"  then read_string_aux input (#"\000"::acc) else
                if e = #"n"  then read_string_aux input (#"\n"::acc) else
                if e = #"r"  then read_string_aux input (#"\""::acc) else
                if e = #"t"  then read_string_aux input (#"\""::acc) else
                  raise Fail "read_string_aux: unrecognised escape"))
        else
          read_string_aux input (c::acc)
End

Quote add_cakeml:
  fun read_string input = read_string_aux input []
End

Quote add_cakeml:
  fun read_symbol_aux input acc =
    case TextIO.b_input1 input of
      None => String.implode (List.rev acc)
    | Some c =>
        if c = #")" orelse Char.isSpace c
        then String.implode (List.rev acc)
        else read_symbol_aux input (c::acc)
End

Quote add_cakeml:
  fun read_symbol input = read_symbol input []
End

Quote add_cakeml:
  fun lex_aux depth input acc =
    case TextIO.b_input1 input of
      None => if depth = 0 then acc
              else raise Fail "lex_aux: missing closing parenthesis"
    | Some c =>
        if Char.isSpace c then lex_aux depth input acc
        else if c = #"(" then lex_aux (depth + 1) input (OPEN::acc)
        else if c = #")" then
          (if depth = 0 then raise Fail "lex_aux: too many closing parenthesis"
           else if depth = 1 then CLOSE::acc
           else lex_aux (depth - 1) input (CLOSE::acc))
        else if c = #"\"" then
          let val s = read_string input in
            if depth = 0 then [SYMBOL s]
            else lex_aux depth input ((SYMBOL s)::acc) end
        else
          let val s = read_symbol input in
            if depth = 0 then [SYMBOL s]
            else lex_aux depth input ((SYMBOL s)::acc) end
End

Quote add_cakeml:
  fun lex input = lex_aux 0 input []
End

val r = translate mlsexpTheory.parse_aux_def;

Quote add_cakeml:
  fun parse input = parse_aux (lex input) [] []
End

(*--------------------------------------------------------------*
   Prove equivalence to mlsexp
 *--------------------------------------------------------------*)

val st = get_ml_prog_state ();

Theorem lex_aux_spec:
  ∀s depth depthv acc accv p is fs fd.
    NUM depth depthv ∧ LIST_TYPE MLSEXP_TOKEN_TYPE acc accv ⇒
    app (p:'ffi ffi_proj) lex_aux_v [depthv; is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (case lex_aux depth s acc of
       | INL (msg, rest) =>
         POSTe exn. SEP_EXISTS k.
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(Fail_exn msg exn)
       | INR (toks, rest) =>
         POSTv tokvs. SEP_EXISTS k.
           STDIO (forwardFD fs fd k) *
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(LIST_TYPE MLSEXP_TOKEN_TYPE toks tokvs))
Proof
  cheat
  (* rpt strip_tac *)
  (* \\ xcf "lex_aux" st *)
  (* \\ xlet ‘POSTv chv. SEP_EXISTS k. *)
  (*            STDIO (forwardFD fs fd k) * *)
  (*            INSTREAM_STR fd is (TL s) (forwardFD fs fd k) * *)
  (*            &OPTION_TYPE CHAR (oHD s) chv’ *)
  (* >- (xapp_spec b_input1_spec_str) *)
  (* \\ Cases_on ‘s’ \\ gvs [OPTION_TYPE_def] *)
  (* \\ xmatch *)
  (* >- *)
  (*  (xlet_auto >- xsimpl *)
  (*   \\ xif \\ simp [lex_aux_def] *)
  (*   >- (xvar \\ xsimpl \\ qexists ‘k’ \\ xsimpl) *)
  (*   \\ xlet_auto >- (xcon \\ xsimpl) *)
  (*   \\ xraise *)
  (*   \\ xsimpl \\ qexists ‘k’ \\ xsimpl *)
  (*   \\ simp [Fail_exn_def]) *)
  (* \\ xlet_auto >- xsimpl *)
  (* \\ xif *)
  (* >- *)
  (*  (xsimpl *)
  (*   \\ xapp) *)
  (* \\ cheat *)
QED

Theorem lex_spec:
  app (p:'ffi ffi_proj) lex_v [is]
    (STDIO fs * INSTREAM_STR fd is s fs)
    (case lex s of
     | INL (msg, rest) =>
       POSTe exn. SEP_EXISTS k.
         INSTREAM_STR fd is rest (forwardFD fs fd k) *
         &(Fail_exn msg exn)
     | INR (toks, rest) =>
       POSTv tokvs. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_STR fd is rest (forwardFD fs fd k) *
         &(LIST_TYPE MLSEXP_TOKEN_TYPE toks tokvs))
Proof
  xcf "lex" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ cheat
QED
