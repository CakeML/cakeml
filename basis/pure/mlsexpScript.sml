(*
  Definition of a simple mlstring-based s-expression, includes
  parsing and pretty printing for these s-expressions.
*)
Theory mlsexp
Ancestors
  mlstring
Libs
  preamble

(*--------------------------------------------------------------*
   Definition of s-expression
 *--------------------------------------------------------------*)

Datatype:
  sexp = Atom mlstring | Expr (sexp list)
End

(*--------------------------------------------------------------*
   Lexing + parsing
 *--------------------------------------------------------------*)

Datatype:
  token = OPEN | CLOSE | SYMBOL mlstring
End

(* Functions may not consume the entire input (string), so they always return
   the rest of the string, independent of success or failure. *)
Type result[local,pp] = “:(α # string) + (β # string)”

Definition read_string_aux_def:
  read_string_aux [] acc =
    INL («read_string_aux: unterminated string literal», []) ∧
  read_string_aux (c::rest) acc =
    if c = #"\"" then INR (implode (REVERSE acc), rest) else
    if c = #"\\" then
      (case rest of
       | [] => read_string_aux rest acc (* causes error: unterminated string *)
       | (e::rest) =>
           (if e = #"\\" then read_string_aux rest (#"\\"::acc) else
            if e = #"\"" then read_string_aux rest (#"\""::acc) else
            if e = #"0"  then read_string_aux rest (#"\000"::acc) else
            if e = #"n"  then read_string_aux rest (#"\n"::acc) else
            if e = #"r"  then read_string_aux rest (#"\r"::acc) else
            if e = #"t"  then read_string_aux rest (#"\t"::acc) else
              INL («read_string_aux: unrecognised escape», rest)))
    else
      read_string_aux rest (c::acc)
End

(* Returns the string until a closing quote, and the rest of the input.
   Fails with an error message if closing quotes are missing or an
   unrecognised escape sequence occurs. *)
Definition read_string_def:
  read_string (input: string) : (mlstring, mlstring) result =
    read_string_aux input []
End

Theorem read_string_aux_length:
  ∀input acc.
    read_string_aux input acc = INR (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  ho_match_mp_tac read_string_aux_ind \\ rw[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac[read_string_aux_def]
  \\ EVERY_CASE_TAC
  \\ rpt strip_tac \\ res_tac \\ gvs[]
QED

Theorem read_string_length:
  read_string input = INR (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  rw[read_string_def] \\ imp_res_tac read_string_aux_length
QED

(* Returns the string until a closing parenthesis or whitespace, and the
   rest of the input.

   See usage in lex_aux as to why a "non-aux function" is exposing an
   accumulator. *)
Definition read_symbol_def:
  read_symbol [] acc =
    (implode (REVERSE acc), []) ∧
  read_symbol (c::cs) acc =
    if c = #")" ∨ isSpace c then (implode (REVERSE acc), (c::cs))
    else read_symbol cs (c::acc)
End

Theorem read_symbol_length:
  ∀input acc.
    read_symbol input acc = (s, rest) ⇒ LENGTH rest ≤ LENGTH input
Proof
  Induct
  \\ simp[read_symbol_def]
  \\ rw[read_symbol_def] \\ res_tac \\ gvs[]
QED

(* By tracking the depth, we can ensure we only lex one S-expression at a
   time. *)
Definition lex_aux_def:
  lex_aux depth [] acc : (mlstring, token list) result =
    (if depth = 0:num then INR (acc, [])
     else INL («lex_aux: missing closing parenthesis», [])) ∧
  lex_aux depth (c::cs) acc =
    if isSpace c then lex_aux depth cs acc
    else if c = #"(" then lex_aux (depth + 1) cs (OPEN::acc)
    else if c = #")" then
      (if depth = 0 then INL («lex_aux: too many closing parenthesis», cs)
       else if depth = 1 then INR (CLOSE::acc, cs)
       else lex_aux (depth - 1) cs (CLOSE::acc))
    else if c = #"\"" then
      case read_string cs of
      | INL (msg, rest) => INL (msg, rest)
      | INR (s, rest) =>
          if depth = 0 then INR ([SYMBOL s], rest)
          else lex_aux depth rest ((SYMBOL s)::acc)
    else
      (* We know that c is not a closing parenthesis or a space, so read_symbol
         (c::cs) [] is equivalent to read_symbol cs [c].

         The choice is an implementation detail relevant in the context of
         streams: If we interpret the input string as a stream and use the
         latter version of the call, the case split can be seen as consuming the
         first character.  If we insist on the former version, the case split
         can only peek at (not consume) c, and we must add calls to consume c in
         the other branches. *)
      case read_symbol cs [c] of
      | (s, rest) =>
          if depth = 0 then INR ([SYMBOL s], rest)
          else lex_aux depth rest ((SYMBOL s)::acc)
Termination
  wf_rel_tac ‘measure $ (λ(_, input, _). LENGTH input)’ \\ rw[]
  \\ imp_res_tac read_string_length \\ fs[]
  \\ fs[Once read_symbol_def]
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac read_symbol_length \\ fs[]
End

(* Tokenizes (at most) one S-expression, and returns the rest of the input.
   Fails with an error message if parentheses are unbalanced or
   read_string fails on a string literal. *)
Definition lex_def:
  lex (input: string) : (mlstring, token list) result =
    lex_aux 0 input []
End

Theorem test_lex[local]:
  lex " 1 2   3 " = INR ([SYMBOL «1»]," 2   3 ") ∧
  lex "\"\n \" 2" = INR ([SYMBOL «\n »]," 2") ∧
  lex " (1 2) 3 " = INR ([CLOSE; SYMBOL «2»; SYMBOL «1»; OPEN]," 3 ") ∧
  lex " (1 2) ) " = INR ([CLOSE; SYMBOL «2»; SYMBOL «1»; OPEN]," ) ") ∧
  lex " (1 2    " = INL («lex_aux: missing closing parenthesis», "") ∧
  lex " ) (1 2) " = INL («lex_aux: too many closing parenthesis», " (1 2) ")
Proof
  EVAL_TAC
QED

Definition parse_aux_def:
  parse_aux [] xs s = xs ∧
  parse_aux (CLOSE::rest) xs s = parse_aux rest [] (xs::s) ∧
  parse_aux (OPEN::rest) xs s =
    (case s of
     | [] => parse_aux rest xs s
     | (y::ys) => parse_aux rest ((Expr xs)::y) ys) ∧
  parse_aux ((SYMBOL sy)::rest) xs s = parse_aux rest ((Atom sy)::xs) s
End

(* Parses (at most) one S-expression, and returns the rest of the input.
   Fails exactly when lexing fails. *)
Definition parse_def:
  parse (input: string) : (mlstring, sexp) result =
    case lex input of
    | INL (msg, rest) => INL (msg, rest)
    | INR (rev_toks, rest) =>
        case parse_aux rev_toks [] [] of
        | [] => INL («parse: empty input», rest)
        | (v::_) => INR (v, rest)
End

Theorem test_parse[local]:
  parse " 1 2 3 " = INR (Atom «1»," 2 3 ") ∧
  parse "(1 2 3)" = INR (Expr [Atom «1»; Atom «2»; Atom «3»],"") ∧
  parse "(()) ()" = INR (Expr [Expr []]," ()")
Proof
  EVAL_TAC
QED

(* Function for parsing in the style of the Standard ML basis library. *)
Definition fromString_def:
  fromString (input: mlstring) : sexp option =
    case parse (explode input) of
    | INL _ => NONE
    | INR (se, _) => SOME se
End

(*--------------------------------------------------------------*
   Pretty printing of str_tree
 *--------------------------------------------------------------*)

Datatype:
  str_tree = Str mlstring
           | Trees (str_tree list)
           | GrabLine str_tree
End

Datatype:
  pretty = Parenthesis pretty
         | String mlstring
         | Append pretty bool pretty
         | Size num pretty
End

Definition newlines_def:
  newlines [] = String (strlit "") ∧
  newlines [x] = x ∧
  newlines (x::xs) = Append x T (newlines xs)
End

Definition v2pretty_def:
  (v2pretty v =
     case v of
     | Str s => String s
     | GrabLine w => Size 100000 (v2pretty w)
     | Trees l => Parenthesis (newlines (vs2pretty l))) ∧
  (vs2pretty vs =
     case vs of
     | [] => []
     | (v::vs) => v2pretty v :: vs2pretty vs)
End

Definition get_size_def:
  get_size (Size n x) = n ∧
  get_size (Append x _ y) = get_size x + get_size y + 1 ∧
  get_size (Parenthesis x) = get_size x + 2 ∧
  get_size _ = 0
End

Definition get_next_size_def:
  get_next_size (Size n x) = n ∧
  get_next_size (Append x _ y) = get_next_size x ∧
  get_next_size (Parenthesis x) = get_next_size x + 2 ∧
  get_next_size _ = 0
End

Definition annotate_def:
  annotate (String s) = Size (strlen s) (String s) ∧
  annotate (Parenthesis b) =
    (let b = annotate b in
       Size (get_size b + 2) (Parenthesis b)) ∧
  annotate (Append b1 n b2) =
    (let b1 = annotate b1 in
     let b2 = annotate b2 in
       (* Size (get_size b1 + get_size b2 + 1) *) (Append b1 n b2)) ∧
  annotate (Size n b) = Size n (annotate b)
End

Definition remove_all_def:
  remove_all (Parenthesis v) = Parenthesis (remove_all v) ∧
  remove_all (String v1) = String v1 ∧
  remove_all (Append v2 _ v3) = Append (remove_all v2) F (remove_all v3) ∧
  remove_all (Size v4 v5) = remove_all v5
End

Definition smart_remove_def:
  smart_remove i k (Size n b) =
    (if k + n < 70 then remove_all b else smart_remove i k b) ∧
  smart_remove i k (Parenthesis v) = Parenthesis (smart_remove (i+1) (k+1) v) ∧
  smart_remove i k (String v1) = String v1 ∧
  smart_remove i k (Append v2 b v3) =
    let n2 = get_size v2 in
    let n3 = get_next_size v3 in
      if k + n2 + n3 < 50 then
        Append (smart_remove i k v2) F (smart_remove i (k+n2) v3)
      else
        Append (smart_remove i k v2) T (smart_remove i i v3)
End

Definition flatten_def:
  flatten indent (Size n p) s = flatten indent p s ∧
  flatten indent (Parenthesis p) s =
    strlit "(" :: flatten (concat [indent; strlit "   "]) p (strlit ")" :: s) ∧
  flatten indent (String t) s = t :: s ∧
  flatten indent (Append p1 b p2) s =
    flatten indent p1 ((if b then indent else strlit " ") :: flatten indent p2 s)
End

Definition v2strs_def:
  v2strs end v = flatten (strlit "\n") (smart_remove 0 0 (annotate (v2pretty v))) [end]
End

Theorem test1_v2strs[local]:
  concat (v2strs (strlit "")
                 (Trees [Str (strlit "hello");
                         Str (strlit "there")])) =
  strlit "(hello there)"
Proof
  EVAL_TAC
QED

Theorem test2_v2strs[local]:
  concat (v2strs (strlit "")
                 (Trees [Str (strlit "test");
                         GrabLine (Str (strlit "hi"));
                         GrabLine (Str (strlit "there"))])) =
  strlit "(test\n   hi\n   there)"
Proof
  EVAL_TAC
QED

(*--------------------------------------------------------------*
   Pretty printing of sexp
 *--------------------------------------------------------------*)

Definition is_safe_char_def:
  is_safe_char c ⇔ ~MEM c "()\"\000" ∧ ¬isSpace c
End

Definition str_every_def:
  str_every p n s =
    if n = 0 then T else
      p (strsub s (n-1)) ∧ str_every p (n-1:num) s
End

Definition make_str_safe_def:
  make_str_safe s =
    if s = strlit "" then strlit "\"\"" else
    if str_every is_safe_char (strlen s) s then s else escape_str s
End

Definition sexp2tree_def:
  sexp2tree (Atom s) = Str (make_str_safe s) ∧
  sexp2tree (Expr l) = Trees (sexp2trees l) ∧
  sexp2trees [] = [] ∧
  sexp2trees (v::vs) = sexp2tree v :: sexp2trees vs
End

Definition sexp_to_app_list_def:
  sexp_to_app_list (Atom s) = List [make_str_safe s] ∧
  sexp_to_app_list (Expr l) =
    Append (List [strlit "("])
           (Append (sexps_to_app_list l) (List [strlit ")"])) ∧
  sexps_to_app_list [] = List [] ∧
  sexps_to_app_list (v::vs) =
    if NULL vs then sexp_to_app_list v
    else Append (sexp_to_app_list v)
                (Append (List [strlit " "]) (sexps_to_app_list vs))
End

Definition sexp_to_string_def:
  sexp_to_string s = concat (append (sexp_to_app_list s))
End

Definition sexp_to_pretty_string_def:
  sexp_to_pretty_string s = concat (v2strs (strlit "\n") (sexp2tree s))
End

(*--------------------------------------------------------------*
   Proofs relating parsing with pretty prniting
 *--------------------------------------------------------------*)

Definition to_tokens_def:
  to_tokens (Atom a)  = [SYMBOL a] ∧
  to_tokens (Expr xs) = [OPEN] ++ FLAT (MAP (λx. to_tokens x) xs) ++ [CLOSE]
End

Theorem parse_aux_to_tokens_lemma[local]:
  ∀x xs s rest.
    parse_aux (REVERSE (to_tokens x) ++ rest) xs s =
    parse_aux rest (x::xs) s
Proof
  ho_match_mp_tac to_tokens_ind \\ rpt strip_tac
  >- fs [to_tokens_def,parse_aux_def]
  \\ fs [to_tokens_def,parse_aux_def]
  \\ qsuff_tac
     ‘∀rest ys s.
        parse_aux (REVERSE (FLAT (MAP (λx. to_tokens x) xs)) ++ rest) ys s =
        parse_aux rest (xs ++ ys) s’
  >-
   (strip_tac
    \\ full_simp_tac std_ss [SF ETA_ss, GSYM APPEND_ASSOC]
    \\ simp [parse_aux_def])
  \\ Induct_on ‘xs’ using SNOC_INDUCT >- fs []
  \\ fs [SF DNF_ss, SNOC_APPEND]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem parse_aux_to_tokens_thm:
  parse_aux (REVERSE (to_tokens x)) [] [] = [x]
Proof
  CONV_TAC (PATH_CONV "lrl" (ONCE_REWRITE_CONV [GSYM APPEND_NIL |> cj 1]))
  \\ rewrite_tac [parse_aux_to_tokens_lemma] \\ fs [parse_aux_def]
QED

Theorem str_every_thm:
  ∀P i m. str_every P i m ∧ i ≤ strlen m ⇒ ∀k. k < i ⇒ P $ EL k (explode m)
Proof
  Induct_on ‘i’\\ fs []
  \\ simp [Once str_every_def] \\ rw []
  \\ last_x_assum drule \\ gvs []
  \\ ‘k = i ∨ k < i’ by decide_tac
  \\ fs [] \\ Cases_on ‘m’ \\ gvs [strsub_def]
QED

Theorem read_symbol_thm:
  ∀t s acc.
    EVERY is_safe_char t ∧ (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ⇒
    read_symbol (t ++ s) acc = (implode (REVERSE acc ++ t), s)
Proof
  Induct
  >- (rw [] \\ Cases_on ‘s’ \\ gvs [read_symbol_def])
  \\ gvs [] \\ rw []
  \\ gvs [read_symbol_def]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND, AllCaseEqs()]
  \\ gvs [is_safe_char_def]
QED

Theorem read_string_aux_thm:
  ∀xs s acc.
    read_string_aux (STRCAT (STRCAT (CONCAT (MAP char_escaped xs)) "\"") s) acc =
    INR (implode (REVERSE acc ++ xs), s)
Proof
  Induct
  \\ simp [read_string_def,read_string_aux_def]
  \\ gvs [char_escaped_def,char_escape_seq_def]
  \\ rw [] \\ gvs []
  \\ gvs [read_string_aux_def]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
QED

Theorem lex_aux_make_str_safe:
  ∀m s ts depth.
    (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ∧
    (depth = 0 ⇒ ts = []) ⇒
    lex_aux depth (STRCAT (case make_str_safe m of strlit x => x) s) ts =
    if depth = 0 then INR (SYMBOL m::ts,s)
    else lex_aux depth s (SYMBOL m::ts)
Proof
  rpt gen_tac
  \\ simp [make_str_safe_def]
  \\ IF_CASES_TAC \\ fs []
  >-
   (simp [Once lex_aux_def, EVAL “isSpace #"\""”]
    \\ simp [Once read_string_def]
    \\ simp [Once read_string_aux_def, implode_def])
  \\ IF_CASES_TAC \\ fs []
  >-
   (dxrule str_every_thm \\ simp []
    \\ Cases_on ‘m’ \\ gvs []
    \\ rpt strip_tac
    \\ rename [‘lex_aux depth (STRCAT input s) ts’]
    \\ ‘EVERY is_safe_char input’ by gvs [EVERY_EL]
    \\ qpat_x_assum ‘∀_._’ kall_tac
    \\ Cases_on ‘input’ \\ gvs []
    \\ gvs [lex_aux_def,is_safe_char_def]
    \\ DEP_REWRITE_TAC [read_symbol_thm]
    \\ simp [implode_def])
  \\ simp [escape_str_def,implode_def]
  \\ simp [Once lex_aux_def, EVAL “isSpace #"\""”]
  \\ simp [read_string_def,read_string_aux_thm]
QED

Theorem flatten_acc:
  ∀x indent s. flatten indent x s = flatten indent x [] ++ s
Proof
  Induct
  \\ once_rewrite_tac [flatten_def]
  \\ simp_tac std_ss []
  \\ rpt $ pop_assum $ once_rewrite_tac o single
  \\ fs []
QED

Theorem lex_aux_spaces:
  ∀t rest ts depth.
    EVERY isSpace t ⇒
    lex_aux depth (t ++ rest) ts = lex_aux depth rest ts
Proof
  Induct \\ rw [] \\ simp [Once lex_aux_def]
QED

Theorem lex_aux_sexp2tree:
  (∀x s ts depth m n indent.
     (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ∧
     (depth = 0 ⇒ ts = []) ∧
     indent ≠ strlit "" ∧ EVERY isSpace (explode indent) ⇒
     lex_aux depth
             (STRCAT
              (explode
               (concat
                (flatten indent
                         (smart_remove m n (annotate (v2pretty (sexp2tree x))))
                         []))) s) ts =
     (if depth = 0 then INR (REVERSE (to_tokens x) ++ ts,s)
      else lex_aux depth s (REVERSE (to_tokens x) ++ ts)) ∧
     lex_aux depth
             (STRCAT
              (explode
               (concat
                (flatten indent
                         (remove_all (annotate (v2pretty (sexp2tree x))))
                         []))) s) ts =
     (if depth = 0 then INR (REVERSE (to_tokens x) ++ ts,s)
      else lex_aux depth s (REVERSE (to_tokens x) ++ ts))) ∧
  (∀xs s ts depth indent m n.
     (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ∧ depth ≠ 0 ∧
     indent ≠ strlit "" ∧ EVERY isSpace (explode indent) ⇒
     lex_aux depth
             (STRCAT
              (explode
               (concat
                (flatten indent
                  (smart_remove m n (annotate (newlines (vs2pretty (sexp2trees xs)))))
                  []))) s) ts =
     (lex_aux depth s (REVERSE (FLAT (MAP to_tokens xs)) ++ ts)) ∧
     lex_aux depth
             (STRCAT
              (explode
               (concat
                (flatten indent
                  (remove_all (annotate (newlines (vs2pretty (sexp2trees xs)))))
                  []))) s) ts =
     (lex_aux depth s (REVERSE (FLAT (MAP to_tokens xs)) ++ ts)))
Proof
  Induct
  >-
   (simp [sexp2tree_def]
    \\ simp [v2strs_def,v2pretty_def]
    \\ simp [annotate_def,to_tokens_def]
    \\ simp [smart_remove_def,remove_all_def, flatten_def]
    \\ rpt strip_tac
    \\ drule_all lex_aux_make_str_safe
    \\ Cases_on ‘make_str_safe m’ \\ simp []
     \\ disch_then $ qspec_then ‘m’ mp_tac \\ simp [])
  >-
   (rpt gen_tac \\ strip_tac
    \\ simp [sexp2tree_def]
    \\ once_rewrite_tac [v2pretty_def]
    \\ simp [annotate_def,remove_all_def,smart_remove_def]
    \\ conj_tac
    THENL [IF_CASES_TAC, all_tac]
    \\ simp [flatten_def,concat_def]
    \\ Cases_on ‘indent’ \\ gvs [concat_def]
    \\ simp [Once lex_aux_def, EVAL “isSpace #"("”]
    \\ once_rewrite_tac [flatten_acc] \\ fs []
    \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ gvs [SF DNF_ss]
    \\ qabbrev_tac ‘new_indent = strlit (STRCAT s' "   ")’
    \\ rpt $ first_x_assum $ qspecl_then [‘")"++s’,
              ‘OPEN::ts’,‘depth + 1’,‘new_indent’] mp_tac
    \\ ‘new_indent ≠ «» ∧ EVERY isSpace (explode new_indent)’ by
      (gvs [Abbr‘new_indent’] \\ EVAL_TAC)
    \\ simp []
    \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ rpt strip_tac
    \\ simp [Once lex_aux_def,EVAL “isSpace #")"”]
    \\ simp [to_tokens_def,REVERSE_APPEND]
    \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC, SF ETA_ss])
  >-
   (simp [sexp2tree_def]
    \\ simp [v2pretty_def]
    \\ simp [newlines_def,annotate_def,smart_remove_def,
             remove_all_def,flatten_def,concat_def])
  \\ Cases_on ‘xs’ \\ fs []
  \\ simp [REVERSE_APPEND,sexp2tree_def]
  \\ once_rewrite_tac [v2pretty_def |> cj 2] \\ simp []
  \\ once_rewrite_tac [v2pretty_def |> cj 2] \\ simp []
  \\ simp [newlines_def]
  \\ simp [annotate_def,remove_all_def,smart_remove_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ conj_tac
  THENL [IF_CASES_TAC, all_tac]
  \\ simp [Once flatten_def]
  \\ once_rewrite_tac [flatten_acc]
  \\ gvs [concat_def]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ gvs [SF DNF_ss]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ last_x_assum $ DEP_REWRITE_TAC o single
  \\ last_x_assum $ DEP_REWRITE_TAC o single
  \\ simp []
  \\ Cases_on ‘indent’
  \\ rename [‘EVERY isSpace (explode (strlit t))’]
  \\ (conj_tac >- (gvs [EVAL “isSpace #" "”] \\ Cases_on ‘t’ \\ fs []))
  \\ simp [Once lex_aux_def, EVAL “isSpace #" "”]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ gvs [sexp2tree_def,lex_aux_spaces]
  \\ gvs [v2pretty_def |> cj 2 |> Q.SPEC ‘_ :: _’ |> SRULE []]
  \\ simp [REVERSE_APPEND]
QED

Theorem lex_aux_sexp_to_list:
  (∀x s ts depth.
     (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ∧
     (depth = 0 ⇒ ts = []) ⇒
     lex_aux depth (explode (concat (append (sexp_to_app_list x))) ++ s) ts =
     if depth = 0 then
       INR (REVERSE (to_tokens x) ++ ts, s)
     else
       lex_aux depth s (REVERSE (to_tokens x) ++ ts)) ∧
  (∀xs s ts depth.
     (s ≠ "" ⇒ isSpace (HD s) ∨ HD s = #")") ∧ depth ≠ 0 ⇒
     lex_aux depth (explode (concat (append (sexps_to_app_list xs))) ++ s) ts =
     lex_aux depth s (REVERSE (FLAT (MAP (λx. to_tokens x) xs)) ++ ts))
Proof
  Induct
  >-
   (fs [to_tokens_def]
    \\ simp [sexp_to_app_list_def,concat_def]
    \\ rpt strip_tac
    \\ drule_all lex_aux_make_str_safe
    \\ disch_then $ qspec_then ‘m’ assume_tac
    \\ simp [])
  >-
   (simp [sexp_to_app_list_def,concat_def] \\ fs [concat_def]
    \\ rw [] \\ simp [Once lex_aux_def, EVAL “isSpace #"("”]
    \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ last_x_assum $ DEP_REWRITE_TAC o single
    \\ fs [] \\ simp [Once lex_aux_def, EVAL “isSpace #")"”]
    \\ simp [to_tokens_def] \\ fs [REVERSE_APPEND]
    \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC])
  >-
   (simp [sexp_to_app_list_def])
  \\ simp [sexp_to_app_list_def] \\ rw []
  >- gvs [NULL_EQ]
  \\ fs [concat_def]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ last_x_assum $ DEP_REWRITE_TAC o single
  \\ fs [EVAL “isSpace #" "”]
  \\ simp [Once lex_aux_def, EVAL “isSpace #" "”]
  \\ fs [REVERSE_APPEND]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
QED

Theorem parse_sexp_to_string:
  ∀s x.
    (s ≠ "" ⇒ isSpace (HD s)) ⇒
    parse (explode (sexp_to_string x) ++ s) = INR (x, s)
Proof
  fs [sexp_to_string_def,parse_def,lex_def]
  \\ rpt strip_tac
  \\ DEP_REWRITE_TAC [cj 1 lex_aux_sexp_to_list] \\ fs []
  \\ simp [parse_aux_to_tokens_thm]
QED

Theorem parse_sexp_to_pretty_string:
  ∀s x.
    parse (explode (sexp_to_pretty_string x) ++ s) = INR (x, "\n" ++ s)
Proof
  fs [sexp_to_pretty_string_def,parse_def,lex_def,v2strs_def]
  \\ rpt strip_tac
  \\ once_rewrite_tac [flatten_acc] \\ simp []
  \\ gvs [concat_append]
  \\ simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ DEP_REWRITE_TAC [lex_aux_sexp2tree |> cj 1 |> cj 1]
  \\ simp [parse_aux_to_tokens_thm] \\ EVAL_TAC
QED

Theorem fromString_sexp_to_string:
  fromString (sexp_to_string x) = SOME x
Proof
  fs [fromString_def,AllCaseEqs(),PULL_EXISTS]
  \\ qspec_then ‘[]’ mp_tac parse_sexp_to_string \\ fs []
QED

Theorem fromString_sexp_to_pretty_string:
  fromString (sexp_to_pretty_string x) = SOME x
Proof
  fs [fromString_def,AllCaseEqs(),PULL_EXISTS]
  \\ qspec_then ‘[]’ mp_tac parse_sexp_to_pretty_string \\ fs []
QED
