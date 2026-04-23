(*
  A parser for CP problems based on sexpressions
*)
Theory cp_parse
Libs
  preamble
Ancestors
  cp mlsexp result_monad

(*
  Tentatively, we will have everything live in a big s-expression with
    either 2 or 3 elements.

(
  // the first element is a list of all the bounds
  (
    (...)
    (...)
    (...)
  )
  // the second one is a list of all the constraints
  (
    (...)
    (...)
    (...)
  )
  // the third (if it exists) indicates the variable to minimize/maximize
  (min x) | (max x)
)
*)

(* Parsing all the bounds *)
Definition sexp_bnd_def:
  sexp_bnd e =
    case e of
      Expr [Atom v; Atom lb; Atom ub] =>
        (case (mlint$fromString lb, mlint$fromString ub) of
          (SOME lb, SOME ub) => return (v,lb,ub)
        | _ => fail (strlit "unable to parse integer bounds\n"))
    | _ => fail (strlit "invalid bound sexpression\n")
End

Definition sexp_bnds_def:
  (sexp_bnds [] = return []) ∧
  (sexp_bnds (e::es) =
    do
      x <- sexp_bnd e;
      xs <- sexp_bnds es;
      return (x::xs)
    od)
End

(*--------------------------------------------------------------*
   Generic helpers: integers, int/varc lists, table wildcards,
   comparison operators, reify tuples, array indices, linear terms
 *--------------------------------------------------------------*)

Definition sexp_varc_def:
  (sexp_varc (Atom v) =
  case mlint$fromString v of
    NONE => return (INL v)
  | SOME i => return ((INR i):mlstring varc)) ∧
  (sexp_varc _ =
    fail (strlit "invalid sexpression at var/const position\n"))
End

Definition sexp_varcs_def:
  (sexp_varcs [] = return []) ∧
  (sexp_varcs (e::es) =
     do
      x <- sexp_varc e;
      xs <- sexp_varcs es;
      return (x::xs)
    od)
End

Definition sexp_varc_list_def:
  sexp_varc_list e =
  case e of
    Expr es => sexp_varcs es
  | _ => fail (strlit "expected s-expression list of vars/ints\n")
End

Definition sexp_int_def:
  sexp_int e =
  case e of
    Atom s =>
    (case mlint$fromString s of
       SOME (i:int) => return i
     | NONE => fail (strlit "expected integer, got: " ^ s ^ strlit "\n"))
  | _ => fail (strlit "expected integer atom\n")
End

Definition sexp_ints_def:
  (sexp_ints [] = return []) ∧
  (sexp_ints (e::es) =
    do
      x <- sexp_int e;
      xs <- sexp_ints es;
      return (x::xs)
    od)
End

Definition sexp_int_list_def:
  sexp_int_list e =
  case e of
    Expr es => sexp_ints es
  | _ => fail (strlit "expected s-expression list of integers\n")
End

Definition sexp_cmpop_kw_def:
  sexp_cmpop_kw s =
       if s = strlit "equals"        then SOME Equal
  else if s = strlit "not_equals"    then SOME NotEqual
  else if s = strlit "greater_equal" then SOME GreaterEqual
  else if s = strlit "greater_than"  then SOME GreaterThan
  else if s = strlit "less_equal"    then SOME LessEqual
  else if s = strlit "less_than"     then SOME LessThan
  else NONE
End

Definition sexp_cmpop_sym_def:
  sexp_cmpop_sym s =
       if s = strlit "="  then return Equal
  else if s = strlit "!=" then return NotEqual
  else if s = strlit ">=" then return GreaterEqual
  else if s = strlit ">"  then return GreaterThan
  else if s = strlit "<=" then return LessEqual
  else if s = strlit "<"  then return LessThan
  else fail (strlit "unknown comparison symbol: " ^ s ^ strlit "\n")
End

Definition sexp_reify_cmp_def:
  sexp_reify_cmp e =
  case e of
    Expr [Ze; Atom cs; ve] =>
    do
      Z <- sexp_varc Ze;
      c <- sexp_cmpop_sym cs;
      v <- sexp_int ve;
      return ((Z,c,v) : mlstring reify_cmp)
    od
  | _ => fail (strlit "invalid reify tuple; expected (Z cmp v)\n")
End

(* Returns (stem, reif_flag) where reif_flag is
     NONE    → no reification (bare constraint)
     SOME F  → one-sided (_if)
     SOME T  → full (_iff) *)
Definition strip_reif_suffix_def:
  strip_reif_suffix (ms:mlstring) =
    if isSuffix (strlit "_iff") ms
    then (substring ms 0 (strlen ms - strlen (strlit "_iff")), SOME T)
    else if isSuffix (strlit "_if") ms
    then (substring ms 0 (strlen ms - strlen (strlit "_if")), SOME F)
    else (ms, NONE)
End

(* Given a reif_flag and the raw args, optionally peel off the head Zc
   tuple and produce a reify value together with the remaining args. *)
Definition peel_reif_def:
  peel_reif (reif_flag : bool option) rest =
    case reif_flag of
      NONE => return ((NONE : mlstring reify), rest)
    | SOME b =>
      (case rest of
         zc_e::rest' =>
         (do
            zc <- sexp_reify_cmp zc_e;
            return (SOME (if b then INR zc else INL zc), rest')
          od)
       | [] => fail (strlit "reified constraint missing reify tuple\n"))
End


(*--------------------------------------------------------------*
   Per-family parsers
 *--------------------------------------------------------------*)

(* Atom → prim_unop / prim_binop constructor, NONE if unrecognised. *)
Definition sexp_prim_unop_def:
  sexp_prim_unop s =
       if s = strlit "neg" then SOME Negative
  else if s = strlit "abs" then SOME Abs
  else NONE
End

Definition sexp_prim_binop_def:
  sexp_prim_binop s =
       if s = strlit "plus"  then SOME Plus
  else if s = strlit "minus" then SOME Minus
  else if s = strlit "max"   then SOME Max
  else if s = strlit "min"   then SOME Min
  else NONE
End

(* Unary prim: op X = Y *)
Definition sexp_unop_body_def:
  sexp_unop_body uop rest =
    case rest of
      [Xe; Ye] =>
      (do
         X <- sexp_varc Xe;
         Y <- sexp_varc Ye;
         return (Prim (Unop uop X Y))
       od)
    | _ => fail (strlit "unary op expects 2 args: op X = Y\n")
End

(* Binary prim: X op Y = Z *)
Definition sexp_binop_body_def:
  sexp_binop_body bop rest =
    case rest of
      [Xe; Ye; Ze] =>
      (do
         X <- sexp_varc Xe;
         Y <- sexp_varc Ye;
         Z <- sexp_varc Ze;
         return (Prim (Binop bop X Y Z))
       od)
    | _ => fail (strlit "binary op expects 3 args: X op Y = Z\n")
End

(* Comparison prim with optional reification: strip _if/_iff, parse stem as
   cmpop. Since prim_dispatch is the last branch in the top-level dispatch,
   an unrecognised stem means the constraint name is simply unsupported. *)
Definition sexp_cmpop_body_def:
  sexp_cmpop_body ctype rest =
    case strip_reif_suffix ctype of (stem, reif_flag) =>
    case sexp_cmpop_kw stem of
      NONE => fail (strlit "unsupported constraint: " ^ ctype ^ strlit "\n")
    | SOME cmp =>
      do
        pr <- peel_reif reif_flag rest;
        case pr of (zr, rest') =>
          case rest' of
            [Xe; Ye] =>
            (do
               X <- sexp_varc Xe;
               Y <- sexp_varc Ye;
               return (Prim (Cmpop zr cmp X Y))
             od)
          | _ => fail (strlit "comparison expects 2 args: X Y\n")
      od
End

(* Primitive: neg, abs (unary); plus, minus, max, min (binary);
   equals/not_equals/greater_*/less_* (comparison with optional reif). *)
Definition sexp_prim_dispatch_def:
  sexp_prim_dispatch ctype rest =
    case sexp_prim_unop ctype of
      SOME uop => sexp_unop_body uop rest
    | NONE =>
    case sexp_prim_binop ctype of
      SOME bop => sexp_binop_body bop rest
    | NONE => sexp_cmpop_body ctype rest
End

(* Linear: stems prefixed with "lin_", embedded comparison keyword, optional reif. *)
Definition sexp_iclin_pairs_def:
  (sexp_iclin_pairs [] = return []) ∧
  (sexp_iclin_pairs [_] =
    fail (strlit "linear term has odd number of entries\n")) ∧
  (sexp_iclin_pairs (c::x::es) =
    do
      ci <- sexp_int c;
      xi <- sexp_varc x;
      rest <- sexp_iclin_pairs es;
      return ((ci,xi)::rest)
    od)
End

Definition sexp_iclin_term_def:
  sexp_iclin_term e =
    case e of
      Expr es => sexp_iclin_pairs es
    | _ => fail (strlit "expected linear term as s-expression list\n")
End

Definition sexp_linear_dispatch_def:
  sexp_linear_dispatch cmp_kw rest =
  case strip_reif_suffix cmp_kw of (stem, reif_flag) =>
  case sexp_cmpop_kw stem of
    NONE => fail (strlit "unknown linear comparison: " ^ stem ^ strlit "\n")
  | SOME cmp =>
    do
      pr <- peel_reif reif_flag rest;
      case pr of (zr, rest') =>
        case rest' of
          [cXs_e; Ye] =>
          (do
             cXs <- sexp_iclin_term cXs_e;
             Y <- sexp_varc Ye;
             return (Linear (Lin zr cmp cXs Y))
           od)
        | _ => fail (strlit "linear constraint expects (c1 X1 ... cn Xn) Y after optional reif\n")
    od
End

(* Lex: stems of the form lex_<cmp>. Takes two varc lists, no reif.
  TODO: not yet supported *)
Definition sexp_lex_dispatch_def:
  sexp_lex_dispatch cmp_kw rest =
    case sexp_cmpop_kw cmp_kw of
      NONE => fail (strlit "unknown lex comparison: " ^ cmp_kw ^ strlit "\n")
    | SOME cmp =>
      (case rest of
         [Xs_e; Ys_e] =>
         (do
            Xs <- sexp_varc_list Xs_e;
            Ys <- sexp_varc_list Ys_e;
            return (Lexicographical (Lex cmp Xs Ys))
          od)
       | _ => fail (strlit "lex_<cmp> expects 2 args: (X1 ... Xn) (Y1 ... Ym)\n"))
End

(* Extensional: table — rows and wildcard-aware entries. *)
Definition sexp_table_entry_def:
  sexp_table_entry e =
  case e of
    Atom s =>
    (if s = strlit "*" then return NONE
     else case mlint$fromString s of
            SOME (i:int) => return (SOME i)
          | NONE => fail (strlit "expected integer or * in table, got: " ^ s ^ strlit "\n"))
  | _ => fail (strlit "expected integer atom or * in table row\n")
End

Definition sexp_table_row_entries_def:
  (sexp_table_row_entries [] = return []) ∧
  (sexp_table_row_entries (e::es) =
    do
      x <- sexp_table_entry e;
      xs <- sexp_table_row_entries es;
      return (x::xs)
    od)
End

Definition sexp_table_row_def:
  sexp_table_row e =
    case e of
      Expr es => sexp_table_row_entries es
    | _ => fail (strlit "expected table row as s-expression list\n")
End

Definition sexp_table_rows_aux_def:
  (sexp_table_rows_aux [] = return []) ∧
  (sexp_table_rows_aux (e::es) =
    do
      r <- sexp_table_row e;
      rs <- sexp_table_rows_aux es;
      return (r::rs)
    od)
End

Definition sexp_table_rows_def:
  sexp_table_rows e =
    case e of
      Expr es => sexp_table_rows_aux es
    | _ => fail (strlit "expected table body as s-expression list of rows\n")
End

(* Table body: rows (X1 ... Xn) *)
Definition sexp_table_body_def:
  sexp_table_body rest =
    case rest of
      [rows_e; Xs_e] =>
      (do
         rows <- sexp_table_rows rows_e;
         Xs <- sexp_varc_list Xs_e;
         return (Extensional (Table rows Xs))
       od)
    | _ => fail (strlit "table expects 2 args: rows (X1 ... Xn)\n")
End

(* Extensional: table (for now). Returns NONE when ctype is not an
   extensional constraint, so the top-level dispatcher can fall through. *)
Definition sexp_extensional_dispatch_def:
  sexp_extensional_dispatch ctype rest =
    if ctype = strlit "table" then SOME (sexp_table_body rest)
    else NONE
End

(* Array: element, element_2d, array_max, array_min. *)

(* (Y offset) → array index *)
Definition sexp_array_ind_def:
  sexp_array_ind e =
  case e of
    Expr [Ye; offe] =>
    do
      Y <- sexp_varc Ye;
      off <- sexp_int offe;
      return ((Y,off) : mlstring array_ind)
    od
  | _ => fail (strlit "invalid array index; expected (Y offset)\n")
End

(* List of rows, each a list of varcs (for element_2d). *)
Definition sexp_varc_rows_aux_def:
  (sexp_varc_rows_aux [] = return []) ∧
  (sexp_varc_rows_aux (e::es) =
    do
      r <- sexp_varc_list e;
      rs <- sexp_varc_rows_aux es;
      return (r::rs)
    od)
End

Definition sexp_varc_rows_def:
  sexp_varc_rows e =
    case e of
      Expr es => sexp_varc_rows_aux es
    | _ => fail (strlit "expected 2D body as s-expression list of rows\n")
End

(* Atom → ArrayMax / ArrayMin constructor (both share (Xs Y) shape), NONE otherwise. *)
Definition sexp_array_aggr_def:
  sexp_array_aggr s =
       if s = strlit "array_max" then SOME ArrayMax
  else if s = strlit "array_min" then SOME ArrayMin
  else NONE
End

(* element: (X0 ... Xn-1) (Y off) Z *)
Definition sexp_element_body_def:
  sexp_element_body rest =
    case rest of
      [Xs_e; Yi_e; Ze] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Yi <- sexp_array_ind Yi_e;
         Z <- sexp_varc Ze;
         return (Array (Element Xs Yi Z))
       od)
    | _ => fail (strlit "element expects 3 args: (X0 ... Xn-1) (Y off) Z\n")
End

(* element_2d: ((row1)(row2)...) (Y1 off1) (Y2 off2) Z *)
Definition sexp_element_2d_body_def:
  sexp_element_2d_body rest =
    case rest of
      [Xss_e; Y1i_e; Y2i_e; Ze] =>
      (do
         Xss <- sexp_varc_rows Xss_e;
         Y1i <- sexp_array_ind Y1i_e;
         Y2i <- sexp_array_ind Y2i_e;
         Z <- sexp_varc Ze;
         return (Array (Element2D Xss Y1i Y2i Z))
       od)
    | _ => fail (strlit "element_2d expects 4 args: ((row1)(row2)...) (Y1 off1) (Y2 off2) Z\n")
End

(* array_max / array_min: (X1 ... Xn) Y, with the chosen constructor passed in. *)
Definition sexp_array_aggr_body_def:
  sexp_array_aggr_body cons rest =
    case rest of
      [Xs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         return (Array (cons Xs Y))
       od)
    | _ => fail (strlit "array aggregate expects 2 args: (X1 ... Xn) Y\n")
End

(* Array: returns NONE when ctype isn't an array constraint so the top-level
   dispatcher can fall through. *)
Definition sexp_array_dispatch_def:
  sexp_array_dispatch ctype rest =
    if ctype = strlit "element" then SOME (sexp_element_body rest)
    else if ctype = strlit "element_2d" then SOME (sexp_element_2d_body rest)
    else case sexp_array_aggr ctype of
           SOME cons => SOME (sexp_array_aggr_body cons rest)
         | NONE => NONE
End

(* Counting: all_different, nvalue, count, among — each has a distinct shape. *)

(* all_different: (X1 ... Xn) *)
Definition sexp_all_different_body_def:
  sexp_all_different_body rest =
    case rest of
      [Xs_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         return (Counting (AllDifferent Xs))
       od)
    | _ => fail (strlit "all_different expects 1 arg: (X1 ... Xn)\n")
End

(* nvalue: (X1 ... Xn) Y *)
Definition sexp_nvalue_body_def:
  sexp_nvalue_body rest =
    case rest of
      [Xs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         return (Counting (NValue Xs Y))
       od)
    | _ => fail (strlit "nvalue expects 2 args: (X1 ... Xn) Y\n")
End

(* count: (X1 ... Xn) Y Z *)
Definition sexp_count_body_def:
  sexp_count_body rest =
    case rest of
      [Xs_e; Ye; Ze] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         Z <- sexp_varc Ze;
         return (Counting (Count Xs Y Z))
       od)
    | _ => fail (strlit "count expects 3 args: (X1 ... Xn) Y Z\n")
End

(* among: (X1 ... Xn) (i1 ... im) Y *)
Definition sexp_among_body_def:
  sexp_among_body rest =
    case rest of
      [Xs_e; iSs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         iSs <- sexp_int_list iSs_e;
         Y <- sexp_varc Ye;
         return (Counting (Among Xs iSs Y))
       od)
    | _ => fail (strlit "among expects 3 args: (X1 ... Xn) (i1 ... im) Y\n")
End

(* Counting: returns NONE when ctype isn't a counting constraint so the
   top-level dispatcher can fall through. *)
Definition sexp_counting_dispatch_def:
  sexp_counting_dispatch ctype rest =
         if ctype = strlit "all_different" then SOME (sexp_all_different_body rest)
    else if ctype = strlit "nvalue"        then SOME (sexp_nvalue_body rest)
    else if ctype = strlit "count"         then SOME (sexp_count_body rest)
    else if ctype = strlit "among"         then SOME (sexp_among_body rest)
    else NONE
End

(* Logical: and, or share the (Xs) Y shape; parity is deferred. *)

(* Atom → And / Or constructor, NONE otherwise. *)
Definition sexp_logical_cons_def:
  sexp_logical_cons s =
       if s = strlit "and" then SOME And
  else if s = strlit "or"  then SOME Or
  else NONE
End

Definition sexp_logical_body_def:
  sexp_logical_body cons rest =
    case rest of
      [Xs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         return (Logical (cons Xs Y))
       od)
    | _ => fail (strlit "logical expects 2 args: (X1 ... Xn) Y\n")
End

Definition sexp_logical_dispatch_def:
  sexp_logical_dispatch ctype rest =
    case sexp_logical_cons ctype of
      SOME cons => SOME (sexp_logical_body cons rest)
    | NONE => NONE
End

(* Channeling: inverse ((X1 ... Xn) offx) ((Y1 ... Ym) offy). *)

(* (list offset) s-expression → (varc list, int) *)
Definition sexp_off_list_def:
  sexp_off_list e =
  case e of
    Expr [Xs_e; offe] =>
    do
      Xs <- sexp_varc_list Xs_e;
      off <- sexp_int offe;
      return ((Xs,off) : mlstring varc list # int)
    od
  | _ => fail (strlit "expected (list offset)\n")
End

Definition sexp_inverse_body_def:
  sexp_inverse_body rest =
    case rest of
      [A_e; B_e] =>
      (do
         a <- sexp_off_list A_e;
         b <- sexp_off_list B_e;
         return (Channeling (Inverse a b))
       od)
    | _ => fail (strlit "inverse expects 2 grouped args: ((X1 ... Xn) offx) ((Y1 ... Ym) offy)\n")
End

Definition sexp_channeling_dispatch_def:
  sexp_channeling_dispatch ctype rest =
    if ctype = strlit "inverse" then SOME (sexp_inverse_body rest)
    else NONE
End

(* Misc: circuit. *)
Definition sexp_circuit_body_def:
  sexp_circuit_body rest =
    case rest of
      [Xs_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         return (Misc (Circuit Xs))
       od)
    | _ => fail (strlit "circuit expects 1 arg: (X1 ... Xn)\n")
End

Definition sexp_misc_dispatch_def:
  sexp_misc_dispatch ctype rest =
    if ctype = strlit "circuit" then SOME (sexp_circuit_body rest)
    else NONE
End

(* Top-level dispatch *)
Definition strip_prefix_def:
  strip_prefix (pre:mlstring) (s:mlstring) =
    if isPrefix pre s
    then SOME (substring s (strlen pre) (strlen s - strlen pre))
    else NONE
End

Definition sexp_constraint_dispatch_def:
  sexp_constraint_dispatch ctype rest =
    case strip_prefix (strlit "lin_") ctype of
      SOME cmp_kw => sexp_linear_dispatch cmp_kw rest
    | NONE =>
    case sexp_extensional_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_array_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_counting_dispatch ctype rest of
      SOME res => res
    | NONE =>
    (*
    case strip_prefix (strlit "lex_") ctype of
      SOME cmp_kw => sexp_lex_dispatch cmp_kw rest
    | NONE =>
    case sexp_logical_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_channeling_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_misc_dispatch ctype rest of
      SOME res => res
    | NONE => *)
    sexp_prim_dispatch ctype rest
End

Definition sexp_constraint_def:
  sexp_constraint e =
  case e of
    Expr (Atom name :: Atom ctype :: rest) =>
    (do
       c <- sexp_constraint_dispatch ctype rest;
       return ((name,c) : mlstring # mlstring constraint)
     od)
  | _ => fail (strlit "invalid constraint sexpression; expected (name ctype args...)\n")
End

Definition sexp_constraints_def:
  (sexp_constraints [] = return []) ∧
  (sexp_constraints (e::es) =
    do
      x <- sexp_constraint e;
      xs <- sexp_constraints es;
      return (x::xs)
    od)
End

Definition sexp_obj_def:
  (sexp_obj [] = return NoObjective) ∧
  (sexp_obj [Expr [Atom x; Atom y]] =
    if x = strlit "minimize"
    then return (Minimize y)
    else
    if x = strlit "maximize"
    then return (Maximize y)
    else fail (strlit "invalid objective sexpression\n")) ∧
  (sexp_obj _ = fail (strlit "invalid objective sexpression\n"))
End

Definition sexp_cp_inst_def:
  sexp_cp_inst e =
  case e of
    Expr (Expr bnds::Expr constraints::mopt) =>
    do
      bb <- sexp_bnds bnds;
      cs <- sexp_constraints constraints;
      obj <- sexp_obj mopt;
      return ((bb,cs,obj):cp_inst)
    od
  | _ => fail (strlit "invalid sexpression for top-level CP instance\n")
End

Definition parse_cp_inst_def:
  parse_cp_inst s =
    case fromString s of
      NONE => fail (strlit "sexp parse failure\n")
    | SOME se => sexp_cp_inst se
End

(*--------------------------------------------------------------*
   EVAL tests — each theorem asserts the parser returned the expected
   tag (INR for positive, INL for negative) via EVAL_TAC.
 *--------------------------------------------------------------*)

(* Convenient to parse a list of sexpressions for tests *)
Definition fromStringL_def:
  fromStringL s =
    sexp_CASE
    (THE (fromString s)) ARB I
End

Theorem test_bnds:
  (* multi-var happy path *)
  sexp_bnds (fromStringL (strlit "((A 0 10) (B 0 10) (C 0 10))")) =
    INR [(«A»,0,10); («B»,0,10); («C»,0,10)] ∧
  (* negative bounds *)
  sexp_bnds (fromStringL (strlit "((X -5 5) (Y -100 -1))")) =
    INR [(«X»,-5,5); («Y»,-100,-1)] ∧
  (* empty list is fine *)
  sexp_bnds (fromStringL (strlit "()")) = INR [] ∧
  (* wrong arity on a single bound sexpression *)
  sexp_bnds (fromStringL (strlit "((X 0))")) =
    INL (strlit "invalid bound sexpression\n") ∧
  (* non-integer bound atom *)
  sexp_bnds (fromStringL (strlit "((X zero 10))")) =
    INL (strlit "unable to parse integer bounds\n") ∧
  (* nested Expr in a bound position is invalid *)
  sexp_bnds (fromStringL (strlit "((X (0) 10))")) =
    INL (strlit "invalid bound sexpression\n")
Proof
  EVAL_TAC
QED

Theorem test_linear:
  sexp_constraint_dispatch (strlit"lin_equals")
    (fromStringL (strlit "((1 A 2 B) I)")) =
    INR (Linear (Lin NONE Equal [(1,INL «A»); (2,INL «B»)] (INL «I»))) ∧
  sexp_constraint_dispatch (strlit"lin_not_equals_if")
    (fromStringL (strlit "((zz >= 5) (1 A 2 B) I)")) =
    (INR
     (Linear
        (Lin (SOME (INL (INL «zz»,GreaterEqual,5))) NotEqual
           [(1,INL «A»); (2,INL «B»)] (INL «I»)))) ∧
  sexp_constraint_dispatch (strlit"lin_greater_equal_iff")
    (fromStringL (strlit "((zz = 5) (1 A 2 B) 5)")) =
    (INR
     (Linear
        (Lin (SOME (INR (INL «zz»,Equal,5))) GreaterEqual
           [(1,INL «A»); (2,INL «B»)] (INR 5))))
Proof
  EVAL_TAC
QED

Theorem test_table:
  sexp_constraint_dispatch (strlit"table")
    (fromStringL (strlit "(((1 2) (3 4) (5 6)) (A B))")) =
    INR (Extensional
           (Table [[SOME 1; SOME 2]; [SOME 3; SOME 4]; [SOME 5; SOME 6]]
                  [INL «A»; INL «B»])) ∧
  sexp_constraint_dispatch (strlit"table")
    (fromStringL (strlit "(((1 *) (* 2)) (A B))")) =
    INR (Extensional
           (Table [[SOME 1; NONE]; [NONE; SOME 2]]
                  [INL «A»; INL «B»])) ∧
  (* mixed var/const in the value list *)
  sexp_constraint_dispatch (strlit"table")
    (fromStringL (strlit "(((7)) (3))")) =
    INR (Extensional (Table [[SOME 7]] [INR 3])) ∧
  (* empty body (no rows) is still well-formed *)
  sexp_constraint_dispatch (strlit"table")
    (fromStringL (strlit "(() (A))")) =
    INR (Extensional (Table [] [INL «A»])) ∧
  (* wrong arity *)
  sexp_constraint_dispatch (strlit"table")
    (fromStringL (strlit "(((1 2)))")) =
    INL (strlit "table expects 2 args: rows (X1 ... Xn)\n")
Proof
  EVAL_TAC
QED

Theorem test_array:
  (* element: Xs is the array, (Y off) the indexed variable + offset, Z the result *)
  sexp_constraint_dispatch (strlit"element")
    (fromStringL (strlit "((A B C) (I 0) Z)")) =
    INR (Array (Element [INL «A»; INL «B»; INL «C»] (INL «I», 0) (INL «Z»))) ∧
  (* element with non-zero offset and mixed consts *)
  sexp_constraint_dispatch (strlit"element")
    (fromStringL (strlit "((10 20 30) (I 1) Z)")) =
    INR (Array (Element [INR 10; INR 20; INR 30] (INL «I», 1) (INL «Z»))) ∧
  (* element_2d: 2-row grid *)
  sexp_constraint_dispatch (strlit"element_2d")
    (fromStringL (strlit "(((1 2 3) (4 5 6)) (I 0) (J 0) Z)")) =
    INR (Array (Element2D
                  [[INR 1; INR 2; INR 3]; [INR 4; INR 5; INR 6]]
                  (INL «I», 0) (INL «J», 0) (INL «Z»))) ∧
  (* array_max aggregate *)
  sexp_constraint_dispatch (strlit"array_max")
    (fromStringL (strlit "((A B C) Y)")) =
    INR (Array (ArrayMax [INL «A»; INL «B»; INL «C»] (INL «Y»))) ∧
  (* array_min aggregate *)
  sexp_constraint_dispatch (strlit"array_min")
    (fromStringL (strlit "((A B C) Y)")) =
    INR (Array (ArrayMin [INL «A»; INL «B»; INL «C»] (INL «Y»))) ∧
  (* element wrong arity *)
  sexp_constraint_dispatch (strlit"element")
    (fromStringL (strlit "((A B C) (I 0))")) =
    INL (strlit "element expects 3 args: (X0 ... Xn-1) (Y off) Z\n") ∧
  (* array_max wrong arity *)
  sexp_constraint_dispatch (strlit"array_max")
    (fromStringL (strlit "((A B C))")) =
    INL (strlit "array aggregate expects 2 args: (X1 ... Xn) Y\n") ∧
  (* bad array index shape (missing offset) *)
  sexp_constraint_dispatch (strlit"element")
    (fromStringL (strlit "((A B C) (I) Z)")) =
    INL (strlit "invalid array index; expected (Y offset)\n")
Proof
  EVAL_TAC
QED

Theorem test_counting:
  (* all_different *)
  sexp_constraint_dispatch (strlit"all_different")
    (fromStringL (strlit "((A B C))")) =
    INR (Counting (AllDifferent [INL «A»; INL «B»; INL «C»])) ∧
  (* nvalue with a constant entry in the list *)
  sexp_constraint_dispatch (strlit"nvalue")
    (fromStringL (strlit "((A 3 C) Y)")) =
    INR (Counting (NValue [INL «A»; INR 3; INL «C»] (INL «Y»))) ∧
  (* count *)
  sexp_constraint_dispatch (strlit"count")
    (fromStringL (strlit "((A B C) 7 Z)")) =
    INR (Counting (Count [INL «A»; INL «B»; INL «C»] (INR 7) (INL «Z»))) ∧
  (* among with a literal integer set *)
  sexp_constraint_dispatch (strlit"among")
    (fromStringL (strlit "((A B C) (1 2 3) Y)")) =
    INR (Counting (Among [INL «A»; INL «B»; INL «C»] [1; 2; 3] (INL «Y»))) ∧
  (* all_different wrong arity *)
  sexp_constraint_dispatch (strlit"all_different")
    (fromStringL (strlit "((A B C) Y)")) =
    INL (strlit "all_different expects 1 arg: (X1 ... Xn)\n") ∧
  (* among wrong arity *)
  sexp_constraint_dispatch (strlit"among")
    (fromStringL (strlit "((A B) (1 2))")) =
    INL (strlit "among expects 3 args: (X1 ... Xn) (i1 ... im) Y\n") ∧
  (* among with a non-integer in the value set *)
  sexp_constraint_dispatch (strlit"among")
    (fromStringL (strlit "((A B) (1 foo 3) Y)")) =
    INL (strlit "expected integer, got: foo\n")
Proof
  EVAL_TAC
QED

Theorem test_prim:
  (* unary *)
  sexp_constraint_dispatch (strlit"neg")
    (fromStringL (strlit "(X Y)")) =
    INR (Prim (Unop Negative (INL «X») (INL «Y»))) ∧
  sexp_constraint_dispatch (strlit"abs")
    (fromStringL (strlit "(X Y)")) =
    INR (Prim (Unop Abs (INL «X») (INL «Y»))) ∧
  (* binary (incl. a mixed var/const arg) *)
  sexp_constraint_dispatch (strlit"plus")
    (fromStringL (strlit "(A B C)")) =
    INR (Prim (Binop Plus (INL «A») (INL «B») (INL «C»))) ∧
  sexp_constraint_dispatch (strlit"minus")
    (fromStringL (strlit "(A 3 C)")) =
    INR (Prim (Binop Minus (INL «A») (INR 3) (INL «C»))) ∧
  sexp_constraint_dispatch (strlit"max")
    (fromStringL (strlit "(A B C)")) =
    INR (Prim (Binop Max (INL «A») (INL «B») (INL «C»))) ∧
  sexp_constraint_dispatch (strlit"min")
    (fromStringL (strlit "(A B C)")) =
    INR (Prim (Binop Min (INL «A») (INL «B») (INL «C»))) ∧
  (* bare comparison *)
  sexp_constraint_dispatch (strlit"equals")
    (fromStringL (strlit "(X Y)")) =
    INR (Prim (Cmpop NONE Equal (INL «X») (INL «Y»))) ∧
  sexp_constraint_dispatch (strlit"not_equals")
    (fromStringL (strlit "(X 7)")) =
    INR (Prim (Cmpop NONE NotEqual (INL «X») (INR 7))) ∧
  (* one-sided reified (_if) *)
  sexp_constraint_dispatch (strlit"greater_than_if")
    (fromStringL (strlit "((zz >= 5) X Y)")) =
    INR (Prim (Cmpop (SOME (INL (INL «zz»,GreaterEqual,5)))
                     GreaterThan (INL «X») (INL «Y»))) ∧
  (* full reified (_iff) *)
  sexp_constraint_dispatch (strlit"less_equal_iff")
    (fromStringL (strlit "((zz = 5) X Y)")) =
    INR (Prim (Cmpop (SOME (INR (INL «zz»,Equal,5)))
                     LessEqual (INL «X») (INL «Y»))) ∧
  (* fallback: unrecognised ctype *)
  sexp_constraint_dispatch (strlit"weird")
    (fromStringL (strlit "(X Y)")) =
    INL (strlit "unsupported constraint: weird\n") ∧
  (* fallback keeps the full original name, including any _if/_iff suffix *)
  sexp_constraint_dispatch (strlit"weird_if")
    (fromStringL (strlit "((zz = 1) X Y)")) =
    INL (strlit "unsupported constraint: weird_if\n")
Proof
  EVAL_TAC
QED

Theorem test_cp_inst:
  (* full instance: bounds + constraints + minimize objective *)
  parse_cp_inst (strlit
    "(((X 0 10) (Y 0 10)) ((c1 plus X Y X) (c2 equals X 3)) (minimize X))") =
    INR ([(«X»,0,10); («Y»,0,10)],
         [(«c1», Prim (Binop Plus (INL «X») (INL «Y») (INL «X»)));
          («c2», Prim (Cmpop NONE Equal (INL «X») (INR 3)))],
         Minimize «X») ∧
  (* no objective (only 2 top-level entries) *)
  parse_cp_inst (strlit "(() ())") =
    INR ([], [], NoObjective) ∧
  (* maximize *)
  parse_cp_inst (strlit
    "(((A 0 5)) ((c all_different (A))) (maximize A))") =
    INR ([(«A»,0,5)],
         [(«c», Counting (AllDifferent [INL «A»]))],
         Maximize «A») ∧
  (* constraint-level error propagates through cp_inst *)
  parse_cp_inst (strlit "(() ((c unknown X Y)))") =
    INL (strlit "unsupported constraint: unknown\n") ∧
  (* malformed objective wrapper *)
  parse_cp_inst (strlit "(() () minimize X)") =
    INL (strlit "invalid objective sexpression\n") ∧
  (* top-level sexpression must be an Expr of bounds/constraints/obj *)
  parse_cp_inst (strlit "foo") =
    INL (strlit "invalid sexpression for top-level CP instance\n") ∧
  (* malformed s-expression (unbalanced parens) → parse failure *)
  parse_cp_inst (strlit "(()") =
    INL (strlit "sexp parse failure\n")
Proof
  EVAL_TAC
QED


