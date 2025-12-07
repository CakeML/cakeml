(*
  Module for parsing and pretty-printing s-expressions.
*)
Theory SexpProg
Ancestors
  mlsexp
  ml_translator
  std_prelude  (* OPTION_TYPE *)
  mlbasicsProg  (* Fail_exn *)
  fsFFIProps  (* forwardFD_o *)
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
    case TextIO.b_peekChar input of
      None => String.implode (List.rev acc)
    | Some c =>
        if c = #")" orelse Char.isSpace c
        then String.implode (List.rev acc)
        (* Consume c *)
        else (TextIO.b_input1 input; read_symbol_aux input (c::acc))
End

Quote add_cakeml:
  fun read_symbol input = read_symbol_aux input []
End

Quote add_cakeml:
  fun lex_aux depth input acc =
    case TextIO.b_input1 input of
      None => if depth = 0 then acc
              else raise Fail "lex_aux: missing closing parenthesis"
    | Some c =>
        if Char.isSpace c then lex_aux depth input acc
        else if c = #"(" then lex_aux (depth + 1) input (Open::acc)
        else if c = #")" then
          (if depth = 0 then raise Fail "lex_aux: too many closing parenthesis"
           else if depth = 1 then Close::acc
           else lex_aux (depth - 1) input (Close::acc))
        else if c = #"\"" then
          let val s = read_string input in
            if depth = 0 then [Symbol s]
            else lex_aux depth input ((Symbol s)::acc) end
        else
          let val s = read_symbol input in
            if depth = 0 then [Symbol s]
            else lex_aux depth input ((Symbol s)::acc) end
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

Definition read_string_aux_post_def:
  read_string_aux_post s acc fs is fd =
    (case read_string_aux s acc of
     | INL (msg, rest) =>
         POSTe exn. SEP_EXISTS k.
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(Fail_exn msg exn)
     | INR (slit, rest) =>
         POSTv slitv. SEP_EXISTS k.
           STDIO (forwardFD fs fd k) *
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(STRING_TYPE slit slitv))
End

(* Can be used in read_string_aux_spec to finish proofs about base cases.
 * k indicates how much we moved forward (passed to forwardFD) *)
fun read_string_aux_base_tac k =
  (simp [read_string_aux_post_def, read_string_aux_def] \\ xsimpl
   \\ qexists k \\ xsimpl \\ simp [Fail_exn_def]);

(* Useful when finishing up recursive cases. Takes care of instantiating k in
 * forward fs fd k. *)
val STDIO_forwardFD_INSTREAM_STR_tac =
  (xsimpl
   \\ rpt strip_tac \\ simp [forwardFD_o]
   \\ qmatch_goalsub_abbrev_tac ‘forwardFD fs fd kpx’
   \\ qexists ‘kpx’ \\ xsimpl);

Theorem read_string_aux_spec[local]:
  ∀s acc accv p is fs fd.
    LIST_TYPE CHAR acc accv ⇒
    app (p:'ffi ffi_proj) read_string_aux_v [is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (read_string_aux_post s acc fs is fd)
Proof
  ho_match_mp_tac read_string_aux_ind
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘read_string_aux_post s₁’
  \\ xcf "read_string_aux" st
  (* [] *)
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
             STDIO (forwardFD fs fd k) *
             INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
             &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xlet_autop \\ xraise
    \\ read_string_aux_base_tac ‘k’)
  (* c::rest *)
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
             STDIO (forwardFD fs fd k) *
             INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
             &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xlet_autop
    \\ xif
    >- (* c = " *)
     (xlet_autop
      \\ xapp \\ xsimpl
      \\ first_assum $ irule_at (Pos hd)
      \\ rpt strip_tac
      \\ read_string_aux_base_tac ‘k’)
    \\ xlet_autop
    \\ xif (* c = \ *)
    >-
     (rename [‘read_string_aux_post (STRING _ s)’]
      \\ xlet ‘POSTv chv. SEP_EXISTS k₁.
                 STDIO (forwardFD fs fd (k + k₁)) *
                 INSTREAM_STR fd is (TL s) (forwardFD fs fd (k + k₁)) *
                 &OPTION_TYPE CHAR (oHD s) chv’
      >-
       (xapp_spec b_input1_spec_str
        \\ qexistsl [‘emp’, ‘s’, ‘forwardFD fs fd k’, ‘fd’]
        \\ simp [forwardFD_o] \\ xsimpl)
      \\ Cases_on ‘s’ \\ gvs [OPTION_TYPE_def]
      >- (* Nothing after \ *)
       (xmatch \\ xapp
        \\ first_assum $ irule_at (Pos hd)
        \\ qexistsl [‘forwardFD fs fd (k + k₁)’, ‘fd’, ‘emp’]
        \\ simp [read_string_aux_post_def, read_string_aux_def]
        \\ STDIO_forwardFD_INSTREAM_STR_tac)
      \\ xmatch
      (* escape characters *)
      \\ ntac 5 (
        xlet_autop
        \\ xif
        >-
         (xlet_autop
          \\ gvs []
          \\ xapp
          \\ simp [LIST_TYPE_def]
          \\ qexistsl [‘emp’, ‘forwardFD fs fd (k + k₁)’, ‘fd’]
          \\ simp [read_string_aux_post_def, read_string_aux_def]
          \\ ntac 2 CASE_TAC
          \\ STDIO_forwardFD_INSTREAM_STR_tac))
      (* unrecognised escape *)
      \\ xlet_autop \\ xraise
      \\ read_string_aux_base_tac ‘k + k₁’)
  (* simply push c and recurse *)
  \\ xlet_autop
  \\ gvs []
  \\ xapp
  \\ simp [LIST_TYPE_def]
  \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
  \\ simp [read_string_aux_post_def, read_string_aux_def]
  \\ ntac 2 CASE_TAC
  \\ STDIO_forwardFD_INSTREAM_STR_tac)
QED

Theorem read_string_spec:
  app (p:'ffi ffi_proj) read_string_v [is]
    (STDIO fs * INSTREAM_STR fd is s fs)
    (case read_string s of
     | INL (msg, rest) =>
         POSTe exn. SEP_EXISTS k.
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(Fail_exn msg exn)
     | INR (slit, rest) =>
         POSTv slitv. SEP_EXISTS k.
           STDIO (forwardFD fs fd k) *
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
           &(STRING_TYPE slit slitv))
Proof
  xcf "read_string" st
  \\ xlet_autop \\ xapp
  \\ simp [read_string_aux_post_def, read_string_def]
  \\ qexistsl [‘emp’, ‘s’, ‘fs’, ‘fd’, ‘[]’]
  \\ simp [LIST_TYPE_def] \\ xsimpl
QED

Theorem read_symbol_aux_spec[local]:
  ∀s acc accv p is fs fd.
    LIST_TYPE CHAR acc accv ⇒
    app (p:'ffi ffi_proj) read_symbol_aux_v [is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (case read_symbol_aux s acc of
       | (slit, rest) =>
           POSTv slitv. SEP_EXISTS k.
             STDIO (forwardFD fs fd k) *
             INSTREAM_STR fd is rest (forwardFD fs fd k) *
             &(STRING_TYPE slit slitv))
Proof
  Induct
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘read_symbol_aux s₁’
  \\ xcf "read_symbol_aux" st
  >- (* [] *)
   (xlet ‘POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is s₁ (forwardFD fs fd k) *
            &(OPTION_TYPE CHAR (oHD s₁) chv)’
    >- (xapp_spec b_peekChar_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xlet_autop \\ xapp
    \\ first_assum $ irule_at (Pos hd)
    \\ simp [read_symbol_aux_def]
    \\ xsimpl \\ rpt strip_tac
    \\ qexists ‘k’ \\ xsimpl)
  >- (* c::cs *)
   (xlet ‘POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is s₁ (forwardFD fs fd k) *
            &(OPTION_TYPE CHAR (oHD s₁) chv)’
    >- (xapp_spec b_peekChar_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xlet_autop
    \\ rename [‘read_symbol_aux (h::s)’]
    \\ xlet ‘POSTv b.
               STDIO (forwardFD fs fd k) *
               INSTREAM_STR fd is (h::s) (forwardFD fs fd k) *
               &BOOL (h = #")" ∨ isSpace h) b’
    >-
     (xlog
      \\ IF_CASES_TAC >- (xsimpl \\ gvs [])
      \\ xapp
      \\ first_assum $ irule_at (Pos hd)
      \\ xsimpl)
    \\ simp [read_symbol_aux_def]
    \\ xif
    >-
     (xlet_autop \\ xapp
      \\ first_assum $ irule_at (Pos hd)
      \\ xsimpl \\ rpt strip_tac \\ qexists ‘k’ \\ xsimpl)
    \\ xlet ‘POSTv chv. SEP_EXISTS k₁.
               STDIO (forwardFD fs fd (k + k₁)) *
               INSTREAM_STR fd is s (forwardFD fs fd (k + k₁)) *
               &OPTION_TYPE CHAR (SOME h) chv’
    >-
     (xapp_spec b_input1_spec_str
      \\ qexistsl [‘emp’, ‘h::s’, ‘forwardFD fs fd k’, ‘fd’]
      \\ xsimpl \\ rpt strip_tac \\ simp [forwardFD_o]
      \\ qmatch_goalsub_abbrev_tac ‘forwardFD _ _ (_ + k₁)’
      \\ qexists ‘k₁’ \\ xsimpl)
    \\ xlet_autop
    \\ xapp
    \\ qexistsl [‘emp’, ‘forwardFD fs fd (k + k₁)’, ‘fd’, ‘h::acc’]
    \\ simp [LIST_TYPE_def]
    \\ CASE_TAC
    \\ STDIO_forwardFD_INSTREAM_STR_tac)
QED

Theorem read_symbol_spec:
  app (p:'ffi ffi_proj) read_symbol_v [is]
    (STDIO fs * INSTREAM_STR fd is s fs)
    (case read_symbol s of
     | (slit, rest) =>
         POSTv slitv. SEP_EXISTS k.
           STDIO (forwardFD fs fd k) *
           INSTREAM_STR fd is rest (forwardFD fs fd k) *
          &(STRING_TYPE slit slitv))
Proof
  xcf "read_symbol" st
  \\ xlet_autop \\ xapp
  \\ simp [read_symbol_def]
  \\ qexistsl [‘emp’, ‘s’, ‘fs’, ‘fd’, ‘[]’]
  \\ simp [LIST_TYPE_def] \\ xsimpl
QED

Definition lex_aux_post_def:
  lex_aux_post depth s acc fs is fd =
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
End

val MLSEXP_TOKEN_TYPE_def = theorem "MLSEXP_TOKEN_TYPE_def";

(* Analogous to read_string_aux_base_tac *)
fun lex_aux_base_tac k =
  (simp [lex_aux_post_def, lex_aux_def] \\ xsimpl
   \\ qexists k \\ xsimpl
   \\ simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def, Fail_exn_def]);

Theorem lex_aux_spec:
  ∀ depth s acc depthv accv p is fs fd.
    NUM depth depthv ∧ LIST_TYPE MLSEXP_TOKEN_TYPE acc accv ⇒
    app (p:'ffi ffi_proj) lex_aux_v [depthv; is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (lex_aux_post depth s acc fs is fd)
Proof
  ho_match_mp_tac lex_aux_ind
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘lex_aux_post _ s₁’
  \\ xcf "lex_aux" st
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
            &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch \\ xlet_autop
    \\ xif
    >- (xvar \\ lex_aux_base_tac ‘k’)
    \\ xlet_autop
    \\ xraise \\ lex_aux_base_tac ‘k’)

  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
            &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ rename [‘lex_aux_post _ (STRING c s)’]
    \\ xmatch
    \\ xlet_autop
    \\ xif >-
     (last_x_assum $ drule_all_then assume_tac
      \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
      \\ simp [lex_aux_post_def, lex_aux_def]
      \\ ntac 2 CASE_TAC
      \\ STDIO_forwardFD_INSTREAM_STR_tac)
    \\ xlet_autop
    \\ xif >-
     (ntac 3 xlet_autop
      \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
      \\ gvs [lex_aux_post_def, lex_aux_def]
      \\ conj_tac >- (simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def])
      \\ ntac 2 CASE_TAC
      \\ STDIO_forwardFD_INSTREAM_STR_tac)
    \\ xlet_autop
    \\ xif >-
     (xlet_autop
      \\ xif >- (xlet_autop \\ xraise \\ lex_aux_base_tac ‘k’)
      \\ xlet_autop
      \\ xif >- (xlet_autop \\ xcon \\ lex_aux_base_tac ‘k’)
      \\ ntac 3 xlet_autop
      \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
      \\ gvs [lex_aux_post_def, lex_aux_def]
      \\ conj_tac >- (simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def])
      \\ ntac 2 CASE_TAC
      \\ STDIO_forwardFD_INSTREAM_STR_tac)
    \\ xlet_autop
    \\ xif >-
     (simp [lex_aux_post_def, lex_aux_def, isSpace_def]
      \\ namedCases_on ‘mlsexp$read_string s’ ["l", "r"]
      >-
       (namedCases_on ‘l’ ["msg rest"]
        \\ xlet ‘POSTe exn. SEP_EXISTS k.
                   INSTREAM_STR fd is rest (forwardFD fs fd k) *
                 &(Fail_exn msg exn)’
        >-
         (xapp
          \\ qexistsl [‘emp’, ‘s’, ‘forwardFD fs fd k’, ‘fd’]
          \\ simp []
          \\ STDIO_forwardFD_INSTREAM_STR_tac)
        \\ simp [] \\ xsimpl)
      \\ namedCases_on ‘r’ ["slit rest"]
      \\ xlet ‘POSTv slitv. SEP_EXISTS k.
                 STDIO (forwardFD fs fd k) *
                 INSTREAM_STR fd is rest (forwardFD fs fd k) *
                 &(STRING_TYPE slit slitv)’
      >-
       (xapp
        \\ qexistsl [‘emp’, ‘s’, ‘forwardFD fs fd k’, ‘fd’]
        \\ simp []
        \\ STDIO_forwardFD_INSTREAM_STR_tac)
      \\ xlet_autop
      \\ xif
      >-
       (ntac 2 xlet_autop \\ xcon
        \\ simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def]
        \\ STDIO_forwardFD_INSTREAM_STR_tac)
      \\ ntac 2 xlet_autop \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
      \\ simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def, lex_aux_post_def]
      \\ ntac 2 CASE_TAC
      \\ STDIO_forwardFD_INSTREAM_STR_tac)
    \\ simp [lex_aux_post_def, lex_aux_def]
    \\ namedCases_on ‘read_symbol (STRING c s)’ ["sym rest"]
    \\ xlet ‘POSTv slitv. SEP_EXISTS k.
               STDIO (forwardFD fs fd k) *
               INSTREAM_STR fd is rest (forwardFD fs fd k) *
               &(STRING_TYPE slit slitv)’
    >- (xapp \\ qexistsl [‘emp’, ‘c::s’, ‘forwardFD fs fd k’, ‘fd’]
        \\ simp []
        \\ xsimpl
        \\ cheat (* TODO unprovable; need to use peek in lex_aux *) )
    \\ cheat)
QED
