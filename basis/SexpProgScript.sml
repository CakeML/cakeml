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

Theorem read_string_aux_spec:
  ∀s acc accv p is fs fd.
    LIST_TYPE CHAR acc accv ⇒
    app (p:'ffi ffi_proj) read_string_aux_v [is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (read_string_aux_post s acc fs is fd)
Proof
  Induct
  \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘read_string_aux_post s₁’
  \\ xcf "read_string_aux" st
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
             STDIO (forwardFD fs fd k) *
             INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
             &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch
    \\ xlet_autop
    \\ xraise
    \\ simp [read_string_aux_post_def, read_string_aux_def] \\ xsimpl
    \\ qexists ‘k’ \\ xsimpl
    \\ simp [Fail_exn_def])
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
             STDIO (forwardFD fs fd k) *
             INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
             &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch
    \\ xlet_autop
    \\ xif
    >-
     (xlet_autop
      \\ xapp \\ xsimpl
      \\ first_assum $ irule_at (Pos hd)
      \\ rpt strip_tac
      \\ simp [read_string_aux_post_def, read_string_aux_def] \\ xsimpl
      \\ qexists ‘k’ \\ xsimpl)
    \\ xlet_autop
    \\ xif
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
      >-
       (xmatch \\ xapp
        \\ first_assum $ irule_at (Pos hd)
        \\ qexistsl [‘forwardFD fs fd (k + k₁)’, ‘fd’, ‘emp’]
        \\ conj_tac >- xsimpl
        \\ simp [read_string_aux_post_def, read_string_aux_def]
        \\ xsimpl
        \\ rpt strip_tac \\ simp [forwardFD_o]
        \\ qmatch_goalsub_abbrev_tac ‘forwardFD fs fd kpx’
        \\ qexists ‘kpx’ \\ xsimpl)
      \\ xmatch
      \\ xlet_autop
      \\ xif
      >- cheat
       (* (xlet_autop *)
       (*  \\ xapp *)
       (*  \\ qexistsl [‘emp’, ‘forwardFD fs fd (k + k₁)’, ‘fd’, ‘#"\""::acc’] *)
       (*  \\ simp [LIST_TYPE_def] *)
       (*  \\ conj_tac >- (cheat) *)
       (*  \\ simp [read_string_aux_post_def, read_string_aux_def] *)
       (*  \\ cheat *)
         (* ) *)
      \\ cheat)
   \\ cheat)
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

(* Solve goals of the form

   lex_aux_post ... (forwardFD fs fd k) is fd *+ emp ==+>
   lex_aux_post ... fs is fd *+ GC

   This usually comes up as part of a recursive call. *)
val lex_aux_SEP_IMPPOST_tac =
  (simp [lex_aux_post_def, lex_aux_def, isSpace_def]
   \\ ntac 2 CASE_TAC
   \\ simp [forwardFD_o]
   \\ xsimpl \\ rpt strip_tac
   \\ qmatch_goalsub_abbrev_tac ‘forwardFD fs fd kpx’
   \\ qexists ‘kpx’ \\ xsimpl);

(* Finish up the goal when we are returning.
   Should be preceeded by an x-tactic (xraise, xcon, ...) *)
val lex_aux_ret_tac =
  (simp [lex_aux_post_def, lex_aux_def] \\ xsimpl
   \\ qexists ‘k’ \\ xsimpl
   \\ simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def, Fail_exn_def]);

Theorem lex_aux_spec:
  ∀s depth depthv acc accv p is fs fd.
    NUM depth depthv ∧ LIST_TYPE MLSEXP_TOKEN_TYPE acc accv ⇒
    app (p:'ffi ffi_proj) lex_aux_v [depthv; is; accv]
      (STDIO fs * INSTREAM_STR fd is s fs)
      (lex_aux_post depth s acc fs is fd)
Proof
  Induct
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
    \\ xmatch
    \\ xlet_autop
    \\ xif
    >-
     (xvar
      \\ simp [lex_aux_post_def, lex_aux_def] \\ xsimpl
      >- (qexists ‘k’ \\ xsimpl))
    \\ xlet_autop
    \\ xraise \\ lex_aux_ret_tac)
  >-
   (xlet ‘POSTv chv. SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_STR fd is (TL s₁) (forwardFD fs fd k) *
            &OPTION_TYPE CHAR (oHD s₁) chv’
    >- (xapp_spec b_input1_spec_str)
    \\ unabbrev_all_tac \\ gvs [OPTION_TYPE_def]
    \\ xmatch
    \\ xlet_autop
    \\ xif >-
     (last_x_assum $ drule_all_then assume_tac
      \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’]
      \\ xpull >- xsimpl
      \\ lex_aux_SEP_IMPPOST_tac)
    \\ xlet_autop
    \\ xif >-
     (ntac 3 xlet_autop
      \\ xapp
      \\ qexistsl [‘emp’, ‘forwardFD fs fd k’, ‘fd’, ‘depth + 1’, ‘OPEN::acc’]
      \\ simp []
      \\ conj_tac >- (simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def])
      \\ xpull >- xsimpl
      \\ lex_aux_SEP_IMPPOST_tac)
    \\ xlet_autop
    \\ xif >-
     (xlet_autop
      \\ xif >- (xlet_autop \\ xraise \\ lex_aux_ret_tac)
      \\ xlet_autop
      \\ xif >- (xlet_autop \\ xcon \\ lex_aux_ret_tac)
      \\ ntac 3 xlet_autop
      \\ xapp
      \\ qexistsl
           [‘emp’, ‘forwardFD fs fd k’, ‘fd’, ‘depth - 1’, ‘CLOSE::acc’]
      \\ simp []
      \\ conj_tac >- (simp [LIST_TYPE_def, MLSEXP_TOKEN_TYPE_def])
      \\ xpull >- xsimpl
      \\ lex_aux_SEP_IMPPOST_tac)
    \\ xlet_autop
    \\ xif >-
     (cheat)
    \\ cheat)
QED
