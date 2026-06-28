(*
  A parser for CP problems based on sexpressions
*)
Theory cp_parse
Libs
  preamble
Ancestors
  cp mlsexp result_monad

(*
  We have everything live in a big s-expression with
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
  // the third (if it exists) indicates the variable to minimize/maximize, or
  // it is the keyword "enumerate", which means to enumerate over all the
  // variables specified in the bounds
  (minimize x) | (maximize x) | enumerate
)
*)

(* Shared combinator: parse every element of an s-expression list with `f`,
   short-circuiting on the first error.
   `msg` is the error for a non-list sexp. *)
Definition sexp_list_of_def:
  sexp_list_of msg f e =
    case e of
      Expr es => result_mmap f es
    | _ => fail msg
End

(* Parsing all the bounds *)
Definition sexp_bnd_def:
  sexp_bnd e =
    case e of
      Expr [Atom v; Atom lb; Atom ub] =>
        (case (mlint$fromString lb, mlint$fromString ub) of
          (SOME lb, SOME ub) => return (v,lb,ub)
        | _ => fail («unable to parse integer bounds\n»))
    | _ => fail («invalid bound sexpression\n»)
End

Definition sexp_bnds_def:
  sexp_bnds es = result_mmap sexp_bnd es
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
    fail («invalid sexpression at var/const position\n»))
End

Definition sexp_varc_list_def:
  sexp_varc_list e =
    sexp_list_of («expected s-expression list of vars/ints\n») sexp_varc e
End

Definition sexp_int_def:
  sexp_int e =
  case e of
    Atom s =>
    (case mlint$fromString s of
       SOME (i:int) => return i
     | NONE => fail («expected integer, got: » ^ s ^ «\n»))
  | _ => fail («expected integer atom\n»)
End

Definition sexp_int_list_def:
  sexp_int_list e =
    sexp_list_of («expected s-expression list of integers\n») sexp_int e
End

Definition sexp_cmpop_kw_def:
  sexp_cmpop_kw s =
       if s = «equals»        then SOME Equal
  else if s = «not_equals»    then SOME NotEqual
  else if s = «greater_equal» then SOME GreaterEqual
  else if s = «greater_than»  then SOME GreaterThan
  else if s = «less_equal»    then SOME LessEqual
  else if s = «less_than»     then SOME LessThan
  else NONE
End

Definition sexp_cmpop_sym_def:
  sexp_cmpop_sym s =
       if s = «=»  then return Equal
  else if s = «!=» then return NotEqual
  else if s = «>=» then return GreaterEqual
  else if s = «>»  then return GreaterThan
  else if s = «<=» then return LessEqual
  else if s = «<»  then return LessThan
  else fail («unknown comparison symbol: » ^ s ^ «\n»)
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
  | _ => fail («invalid reify tuple; expected (Z cmp v)\n»)
End

(* Returns (stem, reif_flag) where reif_flag is
     NONE    → no reification (bare constraint)
     SOME F  → one-sided (_if)
     SOME T  → full (_iff) *)
Definition strip_reif_suffix_def:
  strip_reif_suffix (ms:mlstring) =
    if isSuffix («_iff») ms
    then (substring ms 0 (strlen ms - strlen («_iff»)), SOME T)
    else if isSuffix («_if») ms
    then (substring ms 0 (strlen ms - strlen («_if»)), SOME F)
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
       | [] => fail («reified constraint missing reify tuple\n»))
End


(*--------------------------------------------------------------*
   Per-family parsers
 *--------------------------------------------------------------*)

(* Atom → prim_unop / prim_binop constructor, NONE if unrecognised. *)
Definition sexp_prim_unop_def:
  sexp_prim_unop s =
       if s = «neg» then SOME Negative
  else if s = «abs» then SOME Abs
  else NONE
End

Definition sexp_prim_binop_def:
  sexp_prim_binop s =
       if s = «plus»  then SOME Plus
  else if s = «minus» then SOME Minus
  else if s = «max»   then SOME Max
  else if s = «min»   then SOME Min
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
    | _ => fail («unary op expects 2 args: op X = Y\n»)
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
    | _ => fail («binary op expects 3 args: X op Y = Z\n»)
End

(* Comparison prim with optional reification: strip _if/_iff, parse stem as
   cmpop. Since prim_dispatch is the last branch in the top-level dispatch,
   an unrecognised stem means the constraint name is simply unsupported. *)
Definition sexp_cmpop_body_def:
  sexp_cmpop_body ctype rest =
    case strip_reif_suffix ctype of (stem, reif_flag) =>
    case sexp_cmpop_kw stem of
      NONE => fail («unsupported constraint: » ^ ctype ^ «\n»)
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
          | _ => fail («comparison expects 2 args: X Y\n»)
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
    fail («linear term has odd number of entries\n»)) ∧
  (sexp_iclin_pairs (c::x::es) =
    do
      ci <- sexp_int c;
      Xi <- sexp_varc x;
      rest <- sexp_iclin_pairs es;
      return ((ci,Xi)::rest)
    od)
End

Definition sexp_iclin_term_def:
  sexp_iclin_term e =
    case e of
      Expr es => sexp_iclin_pairs es
    | _ => fail («expected linear term as s-expression list\n»)
End

Definition sexp_linear_dispatch_def:
  sexp_linear_dispatch cmp_kw rest =
  case strip_reif_suffix cmp_kw of (stem, reif_flag) =>
  case sexp_cmpop_kw stem of
    NONE => fail («unknown linear comparison: » ^ stem ^ «\n»)
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
        | _ => fail («linear constraint expects (c1 X1 ... cn Xn) Y after optional reif\n»)
    od
End

(* Lex: stems of the form lex_<cmp>, with optional reif suffix (_if/_iff).
   Reified variants peel a leading cond tuple, then two varc lists. *)
Definition sexp_lex_dispatch_def:
  sexp_lex_dispatch cmp_kw rest =
  case strip_reif_suffix cmp_kw of (stem, reif_flag) =>
  case sexp_cmpop_kw stem of
    NONE => fail («unknown lex comparison: » ^ stem ^ «\n»)
  | SOME cmp =>
    do
      pr <- peel_reif reif_flag rest;
      case pr of (zr, rest') =>
        case rest' of
          [Xs_e; Ys_e] =>
          (do
             Xs <- sexp_varc_list Xs_e;
             Ys <- sexp_varc_list Ys_e;
             return (Lexicographical (Lex zr cmp Xs Ys))
           od)
        | _ => fail («lex_<cmp> expects 2 args: (X1 ... Xn) (Y1 ... Ym) after optional reif\n»)
    od
End

(* Extensional: table — rows and wildcard-aware entries. *)
Definition sexp_table_entry_def:
  sexp_table_entry e =
  case e of
    Atom s =>
    (if s = «*» then return NONE
     else case mlint$fromString s of
            SOME (i:int) => return (SOME i)
          | NONE => fail («expected integer or * in table, got: » ^ s ^ «\n»))
  | _ => fail («expected integer atom or * in table row\n»)
End

Definition sexp_table_row_def:
  sexp_table_row e =
    sexp_list_of («expected table row as s-expression list\n») sexp_table_entry e
End

Definition sexp_table_rows_def:
  sexp_table_rows e =
    sexp_list_of («expected table body as s-expression list of rows\n»)
      sexp_table_row e
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
    | _ => fail («table expects 2 args: rows (X1 ... Xn)\n»)
End

(* Regular (NFA) body: (X1 ... Xn) nstates ((edges_0)...(edges_{S-1})) (f1 ... fk)
   where edges_q is a list of (symbol target) pairs out of state q. *)
Definition sexp_num_def:
  sexp_num e =
  case e of
    Atom s =>
    (case mlint$fromString s of
       SOME (i:int) =>
         (if i < 0 then fail («expected nonnegative integer, got: » ^ s ^ «\n»)
          else return (Num i))
     | NONE => fail («expected nonnegative integer, got: » ^ s ^ «\n»))
  | _ => fail («expected nonnegative integer atom\n»)
End

Definition sexp_num_list_def:
  sexp_num_list e =
    sexp_list_of («expected s-expression list of nats\n») sexp_num e
End

Definition sexp_reg_edge_def:
  sexp_reg_edge e =
  case e of
    Expr [sym_e; tgt_e] =>
    (do
       sym <- sexp_int sym_e;
       tgt <- sexp_num tgt_e;
       return (sym,tgt)
     od)
  | _ => fail («regular edge expects (symbol target)\n»)
End

Definition sexp_reg_edges_def:
  sexp_reg_edges e =
    sexp_list_of («expected list of regular edges\n») sexp_reg_edge e
End

Definition sexp_reg_trans_def:
  sexp_reg_trans e =
    sexp_list_of («expected per-state list of regular edge lists\n»)
      sexp_reg_edges e
End

Definition sexp_regular_body_def:
  sexp_regular_body rest =
    case rest of
      [vars_e; nstates_e; trans_e; finals_e] =>
      (do
         Xs <- sexp_varc_list vars_e;
         nstates <- sexp_num nstates_e;
         trans <- sexp_reg_trans trans_e;
         finals <- sexp_num_list finals_e;
         return (Extensional (Regular Xs nstates trans finals))
       od)
    | _ => fail («regular expects 4 args: (X1 ... Xn) nstates ((edges)...) (f1 ... fk)\n»)
End

(* Extensional: table, regular. Returns NONE when ctype is not an
   extensional constraint, so the top-level dispatcher can fall through. *)
Definition sexp_extensional_dispatch_def:
  sexp_extensional_dispatch ctype rest =
    if ctype = «table» then SOME (sexp_table_body rest)
    else if ctype = «regular» then SOME (sexp_regular_body rest)
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
  | _ => fail («invalid array index; expected (Y offset)\n»)
End

(* List of rows, each a list of varcs (for element_2d). *)
Definition sexp_varc_rows_def:
  sexp_varc_rows e =
    sexp_list_of («expected 2D body as s-expression list of rows\n»)
      sexp_varc_list e
End

(* Atom → ArrayMax / ArrayMin constructor (both share (Xs Y) shape), NONE otherwise. *)
Definition sexp_array_aggr_def:
  sexp_array_aggr s =
       if s = «array_max» then SOME ArrayMax
  else if s = «array_min» then SOME ArrayMin
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
    | _ => fail («element expects 3 args: (X0 ... Xn-1) (Y off) Z\n»)
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
    | _ => fail («element_2d expects 4 args: ((row1)(row2)...) (Y1 off1) (Y2 off2) Z\n»)
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
    | _ => fail («array aggregate expects 2 args: (X1 ... Xn) Y\n»)
End

(* Array: returns NONE when ctype isn't an array constraint so the top-level
   dispatcher can fall through. *)
Definition sexp_array_dispatch_def:
  sexp_array_dispatch ctype rest =
    if ctype = «element» then SOME (sexp_element_body rest)
    else if ctype = «element_2d» then SOME (sexp_element_2d_body rest)
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
    | _ => fail («all_different expects 1 arg: (X1 ... Xn)\n»)
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
    | _ => fail («nvalue expects 2 args: (X1 ... Xn) Y\n»)
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
    | _ => fail («count expects 3 args: (X1 ... Xn) Y Z\n»)
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
    | _ => fail («among expects 3 args: (X1 ... Xn) (i1 ... im) Y\n»)
End

(* in: (X1 ... Xn) Y -- Y is in Xs *)
Definition sexp_in_body_def:
  sexp_in_body rest =
    case rest of
      [Xs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         return (Counting (In Xs Y))
       od)
    | _ => fail («in expects 2 args: (X1 ... Xn) Y\n»)
End

(* at_most_one: (X1 ... Xn) val -- at most one Xi equals val *)
Definition sexp_at_most_one_body_def:
  sexp_at_most_one_body rest =
    case rest of
      [Xs_e; Ye] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         Y <- sexp_varc Ye;
         return (Counting (AtMostOne Xs Y))
       od)
    | _ => fail («at_most_one expects 2 args: (X1 ... Xn) val\n»)
End

(* Counting: returns NONE when ctype isn't a counting constraint so the
   top-level dispatcher can fall through. *)
(* all_equal: (X1 ... Xn) — vars grouped in one sublist, as for all_different *)
Definition sexp_all_equal_body_def:
  sexp_all_equal_body rest =
    case rest of
      [Xs_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         return (Counting (AllEqual Xs))
       od)
    | _ => fail («all_equal expects 1 arg: (X1 ... Xn)\n»)
End

(* all_different_except: (X1 ... Xn) (e1 ... em) *)
Definition sexp_all_different_except_body_def:
  sexp_all_different_except_body rest =
    case rest of
      [Xs_e; iS_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         iS <- sexp_int_list iS_e;
         return (Counting (AllDifferentExcept Xs iS))
       od)
    | _ => fail («all_different_except expects 2 args: (X1 ... Xn) (e1 ... em)\n»)
End

(* symmetric_all_different: (X1 ... Xn) start *)
Definition sexp_symmetric_all_different_body_def:
  sexp_symmetric_all_different_body rest =
    case rest of
      [Xs_e; start_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         start <- sexp_int start_e;
         return (Counting (SymmetricAllDifferent (Xs,start)))
       od)
    | _ => fail («symmetric_all_different expects 2 args: (X1 ... Xn) start\n»)
End

(* global_cardinality: (X1 ... Xn) (v1 ... vm) (C1 ... Cm); clsd via keyword.
   gac/bounds variants share one model (bounds lists arrive value-sorted). *)
Definition sexp_global_cardinality_body_def:
  sexp_global_cardinality_body clsd rest =
    case rest of
      [Xs_e; vs_e; Cs_e] =>
      (do
         Xs <- sexp_varc_list Xs_e;
         vs <- sexp_int_list vs_e;
         Cs <- sexp_varc_list Cs_e;
         return (Counting (GlobalCardinality Xs vs Cs clsd))
       od)
    | _ => fail («global_cardinality expects 3 args: (X1 ... Xn) (v1 ... vm) (C1 ... Cm)\n»)
End

Definition sexp_counting_dispatch_def:
  sexp_counting_dispatch ctype rest =
         if ctype = «all_different» then SOME (sexp_all_different_body rest)
    else if ctype = «all_equal»     then SOME (sexp_all_equal_body rest)
    else if ctype = «all_different_except» then SOME (sexp_all_different_except_body rest)
    else if ctype = «symmetric_all_different» then SOME (sexp_symmetric_all_different_body rest)
    else if ctype = «nvalue»        then SOME (sexp_nvalue_body rest)
    else if ctype = «count»         then SOME (sexp_count_body rest)
    else if ctype = «among»         then SOME (sexp_among_body rest)
    else if ctype = «in»            then SOME (sexp_in_body rest)
    else if ctype = «at_most_one»   then SOME (sexp_at_most_one_body rest)
    else if ctype = «gacglobalcardinality»          then SOME (sexp_global_cardinality_body F rest)
    else if ctype = «gacglobalcardinalityclosed»     then SOME (sexp_global_cardinality_body T rest)
    else if ctype = «boundsglobalcardinality»        then SOME (sexp_global_cardinality_body F rest)
    else if ctype = «boundsglobalcardinalityclosed»  then SOME (sexp_global_cardinality_body T rest)
    else NONE
End

(* Logical: and, or, parity all share the (Xs) Y shape. *)

(* Atom → And / Or / Parity constructor, NONE otherwise. *)
Definition sexp_logical_cons_def:
  sexp_logical_cons s =
       if s = «and»    then SOME And
  else if s = «or»     then SOME Or
  else if s = «parity» then SOME Parity
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
    | _ => fail («logical expects 2 args: (X1 ... Xn) Y\n»)
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
  | _ => fail («expected (list offset)\n»)
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
    | _ => fail («inverse expects 2 grouped args: ((X1 ... Xn) offx) ((Y1 ... Ym) offy)\n»)
End

Definition sexp_channeling_dispatch_def:
  sexp_channeling_dispatch ctype rest =
    if ctype = «inverse» then SOME (sexp_inverse_body rest)
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
    | _ => fail («circuit expects 1 arg: (X1 ... Xn)\n»)
End

(* a list of integer rows: ((c11 ... c1n) (c21 ... c2n) ...) *)
Definition sexp_int_rows_def:
  sexp_int_rows e =
    sexp_list_of («expected s-expression list of integer rows\n») sexp_int_list e
End

(* knapsack: ((c11 ... c1n) ...) (X1 ... Xn) (t1 ... tm) -- each row cs with
   target t asserts the linear equation sum(cs_i * Xs_i) = t *)
Definition sexp_knapsack_body_def:
  sexp_knapsack_body rest =
    case rest of
      [css_e; Xs_e; ts_e] =>
      (do
         css <- sexp_int_rows css_e;
         Xs <- sexp_varc_list Xs_e;
         Ts <- sexp_varc_list ts_e;
         return (Misc (Knapsack css Xs Ts))
       od)
    | _ => fail («knapsack expects 3 args: ((c11 ...) ...) (X1 ... Xn) (t1 ... tm)\n»)
End

Definition sexp_misc_dispatch_def:
  sexp_misc_dispatch ctype rest =
    if ctype = «circuit» then SOME (sexp_circuit_body rest)
    else if ctype = «knapsack» then SOME (sexp_knapsack_body rest)
    else NONE
End

(* Top-level dispatch *)
Definition strip_prefix_def:
  strip_prefix (pre:mlstring) (s:mlstring) =
    if isPrefix pre s
    then SOME (substring s (strlen pre) (strlen s - strlen pre))
    else NONE
End

(* scheduling: disjunctive / disjunctive2d / cumulative *)
Definition sexp_disjunctive_body_def:
  sexp_disjunctive_body strct rest =
    case rest of
      [xs_e; ws_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         Ws <- sexp_varc_list ws_e;
         return (Scheduling (Disjunctive Xs Ws strct))
       od)
    | _ => fail («disjunctive expects 2 args: (x1 ... xn) (w1 ... wn)\n»)
End

Definition sexp_disjunctive2d_body_def:
  sexp_disjunctive2d_body strct rest =
    case rest of
      [xs_e; ys_e; ws_e; hs_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         Ys <- sexp_varc_list ys_e;
         Ws <- sexp_varc_list ws_e;
         Hs <- sexp_varc_list hs_e;
         return (Scheduling (Disjunctive2D Xs Ys Ws Hs strct))
       od)
    | _ => fail («disjunctive2d expects 4 args: (x1 ... xn) (y1 ... yn) (w1 ... wn) (h1 ... hn)\n»)
End

Definition sexp_cumulative_body_def:
  sexp_cumulative_body rest =
    case rest of
      [xs_e; ws_e; hs_e; cap_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         Ws <- sexp_varc_list ws_e;
         Hs <- sexp_varc_list hs_e;
         cap <- sexp_varc cap_e;
         return (Scheduling (Cumulative Xs Ws Hs cap))
       od)
    | _ => fail («cumulative expects 4 args: (x1 ... xn) (w1 ... wn) (h1 ... hn) cap\n»)
End

Definition sexp_scheduling_dispatch_def:
  sexp_scheduling_dispatch ctype rest =
    if ctype = «disjunctive»               then SOME (sexp_disjunctive_body F rest)
    else if ctype = «disjunctive_strict»   then SOME (sexp_disjunctive_body T rest)
    else if ctype = «disjunctive2d»        then SOME (sexp_disjunctive2d_body F rest)
    else if ctype = «disjunctive2d_strict» then SOME (sexp_disjunctive2d_body T rest)
    else if ctype = «cumulative»           then SOME (sexp_cumulative_body rest)
    else NONE
End

Definition sexp_increasing_body_def:
  sexp_increasing_body strct desc rest =
    case rest of
      [xs_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         return (Sorting (Increasing Xs strct desc))
       od)
    | _ => fail («increasing expects 1 arg: (x1 ... xn)\n»)
End

Definition sexp_sort_body_def:
  sexp_sort_body rest =
    case rest of
      [xs_e; ys_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         Ys <- sexp_varc_list ys_e;
         return (Sorting (Sort Xs Ys))
       od)
    | _ => fail («sort expects 2 args: (x1 ... xn) (y1 ... yn)\n»)
End

Definition sexp_argsort_body_def:
  sexp_argsort_body rest =
    case rest of
      [xs_e; ps_e; off_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         Ps <- sexp_varc_list ps_e;
         off <- sexp_int off_e;
         return (Sorting (ArgSort Xs Ps off))
       od)
    | _ => fail («arg_sort expects 3 args: (x1 ... xn) (p1 ... pn) offset\n»)
End

Definition sexp_sorting_dispatch_def:
  sexp_sorting_dispatch ctype rest =
    if ctype = «increasing»               then SOME (sexp_increasing_body F F rest)
    else if ctype = «strictly_increasing» then SOME (sexp_increasing_body T F rest)
    else if ctype = «decreasing»          then SOME (sexp_increasing_body F T rest)
    else if ctype = «strictly_decreasing» then SOME (sexp_increasing_body T T rest)
    else if ctype = «sort»                then SOME (sexp_sort_body rest)
    else if ctype = «arg_sort»            then SOME (sexp_argsort_body rest)
    else NONE
End

(* value_precede chain (v1 ... vn) and vars (x1 ... xm) *)
Definition sexp_value_precede_body_def:
  sexp_value_precede_body rest =
    case rest of
      [vs_e; xs_e] =>
      (do
         vs <- sexp_int_list vs_e;
         Xs <- sexp_varc_list xs_e;
         return (Lexicographical (ValuePrecede vs Xs))
       od)
    | _ => fail («value_precede expects 2 args: (v1 ... vn) (x1 ... xm)\n»)
End

(* seq_precede_chain: the implicit chain 1,2,3,… over vars (x1 ... xn) *)
Definition sexp_seq_precede_chain_body_def:
  sexp_seq_precede_chain_body rest =
    case rest of
      [xs_e] =>
      (do
         Xs <- sexp_varc_list xs_e;
         return (Lexicographical (SeqPrecedeChain Xs))
       od)
    | _ => fail («seq_precede_chain expects 1 arg: (x1 ... xn)\n»)
End

Definition sexp_precede_dispatch_def:
  sexp_precede_dispatch ctype rest =
    if ctype = «value_precede»          then SOME (sexp_value_precede_body rest)
    else if ctype = «seq_precede_chain» then SOME (sexp_seq_precede_chain_body rest)
    else NONE
End

Definition sexp_constraint_dispatch_def:
  sexp_constraint_dispatch ctype rest =
    case strip_prefix («lin_») ctype of
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
    case strip_prefix («lex_») ctype of
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
    | NONE =>
    case sexp_scheduling_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_sorting_dispatch ctype rest of
      SOME res => res
    | NONE =>
    case sexp_precede_dispatch ctype rest of
      SOME res => res
    | NONE =>
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
  | _ => fail («invalid constraint sexpression; expected (name ctype args...)\n»)
End

Definition sexp_constraints_def:
  sexp_constraints es = result_mmap sexp_constraint es
End

Definition sexp_prob_type_def:
  (sexp_prob_type vs [] = return Decision) ∧
  (sexp_prob_type vs [Expr [Atom x]] =
      if x = «enumerate»
      then return (Enumerate vs)
      else fail («invalid problem type sexpression\n»)) ∧
  (sexp_prob_type vs [Expr [Atom x; Atom y]] =
    if x = «minimize»
    then return (Minimize y)
    else
    if x = «maximize»
    then return (Maximize y)
    else fail («invalid problem type sexpression\n»)) ∧
  (sexp_prob_type _ _ = fail («invalid problem type sexpression\n»))
End

Definition sexp_cp_inst_def:
  sexp_cp_inst e =
  case e of
    Expr (Expr bnds::Expr constraints::mopt) =>
    do
      (bb:(mlstring, int # int) alist) <- sexp_bnds bnds;
      (cs:(mlstring # mlstring constraint) list) <- sexp_constraints constraints;
      (pty:mlstring prob_type) <- sexp_prob_type (MAP FST bb) mopt;
      return ((bb,cs,pty ):cp_inst)
    od
  | _ => fail («invalid sexpression for top-level CP instance\n»)
End

Definition parse_cp_inst_def:
  parse_cp_inst s =
    case fromString s of
      NONE => fail («sexp parse failure\n»)
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
  sexp_bnds (fromStringL («((A 0 10) (B 0 10) (C 0 10))»)) =
    INR [(«A»,0,10); («B»,0,10); («C»,0,10)] ∧
  (* negative bounds *)
  sexp_bnds (fromStringL («((X -5 5) (Y -100 -1))»)) =
    INR [(«X»,-5,5); («Y»,-100,-1)] ∧
  (* empty list is fine *)
  sexp_bnds (fromStringL («()»)) = INR [] ∧
  (* wrong arity on a single bound sexpression *)
  sexp_bnds (fromStringL («((X 0))»)) =
    INL («invalid bound sexpression\n») ∧
  (* non-integer bound atom *)
  sexp_bnds (fromStringL («((X zero 10))»)) =
    INL («unable to parse integer bounds\n») ∧
  (* nested Expr in a bound position is invalid *)
  sexp_bnds (fromStringL («((X (0) 10))»)) =
    INL («invalid bound sexpression\n»)
Proof
  EVAL_TAC
QED

Theorem test_linear:
  sexp_constraint_dispatch («lin_equals»)
    (fromStringL («((1 A 2 B) I)»)) =
    INR (Linear (Lin NONE Equal [(1,INL «A»); (2,INL «B»)] (INL «I»))) ∧
  sexp_constraint_dispatch («lin_not_equals_if»)
    (fromStringL («((zz >= 5) (1 A 2 B) I)»)) =
    (INR
     (Linear
        (Lin (SOME (INL (INL «zz»,GreaterEqual,5))) NotEqual
           [(1,INL «A»); (2,INL «B»)] (INL «I»)))) ∧
  sexp_constraint_dispatch («lin_greater_equal_iff»)
    (fromStringL («((zz = 5) (1 A 2 B) 5)»)) =
    (INR
     (Linear
        (Lin (SOME (INR (INL «zz»,Equal,5))) GreaterEqual
           [(1,INL «A»); (2,INL «B»)] (INR 5))))
Proof
  EVAL_TAC
QED

Theorem test_lex:
  sexp_constraint_dispatch («lex_greater_than»)
    (fromStringL («((A B) (C D))»)) =
    INR (Lexicographical
      (Lex NONE GreaterThan [INL «A»; INL «B»] [INL «C»; INL «D»])) ∧
  sexp_constraint_dispatch («lex_greater_than_if»)
    (fromStringL («((zz >= 5) (A B) (C D))»)) =
    INR (Lexicographical
      (Lex (SOME (INL (INL «zz»,GreaterEqual,5))) GreaterThan
        [INL «A»; INL «B»] [INL «C»; INL «D»])) ∧
  sexp_constraint_dispatch («lex_less_equal_iff»)
    (fromStringL («((zz = 5) (A B) (C D))»)) =
    INR (Lexicographical
      (Lex (SOME (INR (INL «zz»,Equal,5))) LessEqual
        [INL «A»; INL «B»] [INL «C»; INL «D»]))
Proof
  EVAL_TAC
QED

Theorem test_table:
  sexp_constraint_dispatch («table»)
    (fromStringL («(((1 2) (3 4) (5 6)) (A B))»)) =
    INR (Extensional
           (Table [[SOME 1; SOME 2]; [SOME 3; SOME 4]; [SOME 5; SOME 6]]
                  [INL «A»; INL «B»])) ∧
  sexp_constraint_dispatch («table»)
    (fromStringL («(((1 *) (* 2)) (A B))»)) =
    INR (Extensional
           (Table [[SOME 1; NONE]; [NONE; SOME 2]]
                  [INL «A»; INL «B»])) ∧
  (* mixed var/const in the value list *)
  sexp_constraint_dispatch («table»)
    (fromStringL («(((7)) (3))»)) =
    INR (Extensional (Table [[SOME 7]] [INR 3])) ∧
  (* empty body (no rows) is still well-formed *)
  sexp_constraint_dispatch («table»)
    (fromStringL («(() (A))»)) =
    INR (Extensional (Table [] [INL «A»])) ∧
  (* wrong arity *)
  sexp_constraint_dispatch («table»)
    (fromStringL («(((1 2)))»)) =
    INL («table expects 2 args: rows (X1 ... Xn)\n»)
Proof
  EVAL_TAC
QED

Theorem test_regular:
  (* DFA: 2 states, vars A B, accept in state 1 *)
  sexp_constraint_dispatch («regular»)
    (fromStringL («((A B) 2 (((1 1)) ((1 1))) (1))»)) =
    INR (Extensional (Regular [INL «A»; INL «B»] 2 [[(1,1)]; [(1,1)]] [1])) ∧
  (* NFA: multi-target edge, mixed var/const, empty edge list for a state,
     multiple finals *)
  sexp_constraint_dispatch («regular»)
    (fromStringL («((A 3) 3 (((1 1) (1 2)) () ((0 0))) (1 2))»)) =
    INR (Extensional (Regular [INL «A»; INR 3] 3
           [[(1,1); (1,2)]; []; [(0,0)]] [1; 2])) ∧
  (* empty automaton body is well-formed *)
  sexp_constraint_dispatch («regular»)
    (fromStringL («(() 1 () ())»)) =
    INR (Extensional (Regular [] 1 [] [])) ∧
  (* wrong arity *)
  sexp_constraint_dispatch («regular»)
    (fromStringL («((A) 2)»)) =
    INL («regular expects 4 args: (X1 ... Xn) nstates ((edges)...) (f1 ... fk)\n»)
Proof
  EVAL_TAC
QED

Theorem test_scheduling:
  (* disjunctive, non-strict: tasks (A B C) with variable widths (W1 2 1) *)
  sexp_constraint_dispatch («disjunctive»)
    (fromStringL («((A B C) (W1 2 1))»)) =
    INR (Scheduling (Disjunctive [INL «A»; INL «B»; INL «C»]
           [INL «W1»; INR 2; INR 1] F)) ∧
  (* disjunctive_strict sets the strict flag *)
  sexp_constraint_dispatch («disjunctive_strict»)
    (fromStringL («((A B) (1 1))»)) =
    INR (Scheduling (Disjunctive [INL «A»; INL «B»] [INR 1; INR 1] T)) ∧
  (* disjunctive2d, non-strict: x,y positions and w,h sizes *)
  sexp_constraint_dispatch («disjunctive2d»)
    (fromStringL («((A B) (C D) (2 2) (3 1))»)) =
    INR (Scheduling (Disjunctive2D [INL «A»; INL «B»] [INL «C»; INL «D»]
           [INR 2; INR 2] [INR 3; INR 1] F)) ∧
  (* disjunctive2d_strict *)
  sexp_constraint_dispatch («disjunctive2d_strict»)
    (fromStringL («((A) (B) (1) (1))»)) =
    INR (Scheduling (Disjunctive2D [INL «A»] [INL «B»] [INR 1] [INR 1] T)) ∧
  (* cumulative: tasks (A), widths (1), heights (1), capacity 5 *)
  sexp_constraint_dispatch («cumulative»)
    (fromStringL («((A) (1) (1) 5)»)) =
    INR (Scheduling (Cumulative [INL «A»] [INR 1] [INR 1] (INR 5)))
Proof
  EVAL_TAC
QED

Theorem test_sorting:
  (* increasing: non-strict, non-descending *)
  sexp_constraint_dispatch («increasing»)
    (fromStringL («((A B C))»)) =
    INR (Sorting (Increasing [INL «A»; INL «B»; INL «C»] F F)) ∧
  (* strictly_increasing sets the strict flag *)
  sexp_constraint_dispatch («strictly_increasing»)
    (fromStringL («((A B))»)) =
    INR (Sorting (Increasing [INL «A»; INL «B»] T F)) ∧
  (* decreasing sets the descending flag *)
  sexp_constraint_dispatch («decreasing»)
    (fromStringL («((A B C))»)) =
    INR (Sorting (Increasing [INL «A»; INL «B»; INL «C»] F T)) ∧
  (* strictly_decreasing sets both flags *)
  sexp_constraint_dispatch («strictly_decreasing»)
    (fromStringL («((A B))»)) =
    INR (Sorting (Increasing [INL «A»; INL «B»] T T)) ∧
  (* sort: Ys is a non-decreasing permutation of Xs *)
  sexp_constraint_dispatch («sort»)
    (fromStringL («((A B C) (X Y Z))»)) =
    INR (Sorting (Sort [INL «A»; INL «B»; INL «C»] [INL «X»; INL «Y»; INL «Z»])) ∧
  (* arg_sort: Ps are the offset-shifted stable sorted indices *)
  sexp_constraint_dispatch («arg_sort»)
    (fromStringL («((A B C) (P Q R) 1)»)) =
    INR (Sorting (ArgSort [INL «A»; INL «B»; INL «C»] [INL «P»; INL «Q»; INL «R»] 1))
Proof
  EVAL_TAC
QED

Theorem test_precede:
  (* value_precede: chain (1 2) over vars (A B C) *)
  sexp_constraint_dispatch («value_precede»)
    (fromStringL («((1 2) (A B C))»)) =
    INR (Lexicographical (ValuePrecede [1; 2] [INL «A»; INL «B»; INL «C»])) ∧
  (* seq_precede_chain over vars (A B C) *)
  sexp_constraint_dispatch («seq_precede_chain»)
    (fromStringL («((A B C))»)) =
    INR (Lexicographical (SeqPrecedeChain [INL «A»; INL «B»; INL «C»])) ∧
  (* wrong arity is rejected *)
  sexp_constraint_dispatch («seq_precede_chain»)
    (fromStringL («((A) (B))»)) =
    INL («seq_precede_chain expects 1 arg: (x1 ... xn)\n»)
Proof
  EVAL_TAC
QED

Theorem test_array:
  (* element: Xs is the array, (Y off) the indexed variable + offset, Z the result *)
  sexp_constraint_dispatch («element»)
    (fromStringL («((A B C) (I 0) Z)»)) =
    INR (Array (Element [INL «A»; INL «B»; INL «C»] (INL «I», 0) (INL «Z»))) ∧
  (* element with non-zero offset and mixed consts *)
  sexp_constraint_dispatch («element»)
    (fromStringL («((10 20 30) (I 1) Z)»)) =
    INR (Array (Element [INR 10; INR 20; INR 30] (INL «I», 1) (INL «Z»))) ∧
  (* element_2d: 2-row grid *)
  sexp_constraint_dispatch («element_2d»)
    (fromStringL («(((1 2 3) (4 5 6)) (I 0) (J 0) Z)»)) =
    INR (Array (Element2D
                  [[INR 1; INR 2; INR 3]; [INR 4; INR 5; INR 6]]
                  (INL «I», 0) (INL «J», 0) (INL «Z»))) ∧
  (* array_max aggregate *)
  sexp_constraint_dispatch («array_max»)
    (fromStringL («((A B C) Y)»)) =
    INR (Array (ArrayMax [INL «A»; INL «B»; INL «C»] (INL «Y»))) ∧
  (* array_min aggregate *)
  sexp_constraint_dispatch («array_min»)
    (fromStringL («((A B C) Y)»)) =
    INR (Array (ArrayMin [INL «A»; INL «B»; INL «C»] (INL «Y»))) ∧
  (* element wrong arity *)
  sexp_constraint_dispatch («element»)
    (fromStringL («((A B C) (I 0))»)) =
    INL («element expects 3 args: (X0 ... Xn-1) (Y off) Z\n») ∧
  (* array_max wrong arity *)
  sexp_constraint_dispatch («array_max»)
    (fromStringL («((A B C))»)) =
    INL («array aggregate expects 2 args: (X1 ... Xn) Y\n») ∧
  (* bad array index shape (missing offset) *)
  sexp_constraint_dispatch («element»)
    (fromStringL («((A B C) (I) Z)»)) =
    INL («invalid array index; expected (Y offset)\n»)
Proof
  EVAL_TAC
QED

Theorem test_counting:
  (* all_different *)
  sexp_constraint_dispatch («all_different»)
    (fromStringL («((A B C))»)) =
    INR (Counting (AllDifferent [INL «A»; INL «B»; INL «C»])) ∧
  (* nvalue with a constant entry in the list *)
  sexp_constraint_dispatch («nvalue»)
    (fromStringL («((A 3 C) Y)»)) =
    INR (Counting (NValue [INL «A»; INR 3; INL «C»] (INL «Y»))) ∧
  (* count *)
  sexp_constraint_dispatch («count»)
    (fromStringL («((A B C) 7 Z)»)) =
    INR (Counting (Count [INL «A»; INL «B»; INL «C»] (INR 7) (INL «Z»))) ∧
  (* among with a literal integer set *)
  sexp_constraint_dispatch («among»)
    (fromStringL («((A B C) (1 2 3) Y)»)) =
    INR (Counting (Among [INL «A»; INL «B»; INL «C»] [1; 2; 3] (INL «Y»))) ∧
  (* in *)
  sexp_constraint_dispatch («in»)
    (fromStringL («((A B C) X)»)) =
    INR (Counting (In [INL «A»; INL «B»; INL «C»] (INL «X»))) ∧
  (* at_most_one *)
  sexp_constraint_dispatch («at_most_one»)
    (fromStringL («((A B C) V)»)) =
    INR (Counting (AtMostOne [INL «A»; INL «B»; INL «C»] (INL «V»))) ∧
  (* all_different wrong arity *)
  sexp_constraint_dispatch («all_different»)
    (fromStringL («((A B C) Y)»)) =
    INL («all_different expects 1 arg: (X1 ... Xn)\n») ∧
  (* among wrong arity *)
  sexp_constraint_dispatch («among»)
    (fromStringL («((A B) (1 2))»)) =
    INL («among expects 3 args: (X1 ... Xn) (i1 ... im) Y\n») ∧
  (* among with a non-integer in the value set *)
  sexp_constraint_dispatch («among»)
    (fromStringL («((A B) (1 foo 3) Y)»)) =
    INL («expected integer, got: foo\n»)
Proof
  EVAL_TAC
QED

Theorem test_prim:
  (* unary *)
  sexp_constraint_dispatch («neg»)
    (fromStringL («(X Y)»)) =
    INR (Prim (Unop Negative (INL «X») (INL «Y»))) ∧
  sexp_constraint_dispatch («abs»)
    (fromStringL («(X Y)»)) =
    INR (Prim (Unop Abs (INL «X») (INL «Y»))) ∧
  (* binary (incl. a mixed var/const arg) *)
  sexp_constraint_dispatch («plus»)
    (fromStringL («(A B C)»)) =
    INR (Prim (Binop Plus (INL «A») (INL «B») (INL «C»))) ∧
  sexp_constraint_dispatch («minus»)
    (fromStringL («(A 3 C)»)) =
    INR (Prim (Binop Minus (INL «A») (INR 3) (INL «C»))) ∧
  sexp_constraint_dispatch («max»)
    (fromStringL («(A B C)»)) =
    INR (Prim (Binop Max (INL «A») (INL «B») (INL «C»))) ∧
  sexp_constraint_dispatch («min»)
    (fromStringL («(A B C)»)) =
    INR (Prim (Binop Min (INL «A») (INL «B») (INL «C»))) ∧
  (* bare comparison *)
  sexp_constraint_dispatch («equals»)
    (fromStringL («(X Y)»)) =
    INR (Prim (Cmpop NONE Equal (INL «X») (INL «Y»))) ∧
  sexp_constraint_dispatch («not_equals»)
    (fromStringL («(X 7)»)) =
    INR (Prim (Cmpop NONE NotEqual (INL «X») (INR 7))) ∧
  (* one-sided reified (_if) *)
  sexp_constraint_dispatch («greater_than_if»)
    (fromStringL («((zz >= 5) X Y)»)) =
    INR (Prim (Cmpop (SOME (INL (INL «zz»,GreaterEqual,5)))
                     GreaterThan (INL «X») (INL «Y»))) ∧
  (* full reified (_iff) *)
  sexp_constraint_dispatch («less_equal_iff»)
    (fromStringL («((zz = 5) X Y)»)) =
    INR (Prim (Cmpop (SOME (INR (INL «zz»,Equal,5)))
                     LessEqual (INL «X») (INL «Y»))) ∧
  (* fallback: unrecognised ctype *)
  sexp_constraint_dispatch («weird»)
    (fromStringL («(X Y)»)) =
    INL («unsupported constraint: weird\n») ∧
  (* fallback keeps the full original name, including any _if/_iff suffix *)
  sexp_constraint_dispatch («weird_if»)
    (fromStringL («((zz = 1) X Y)»)) =
    INL («unsupported constraint: weird_if\n»)
Proof
  EVAL_TAC
QED

Theorem test_logical:
  (* and: three-variable list *)
  sexp_constraint_dispatch («and»)
    (fromStringL («((A B C) D)»)) =
    INR (Logical (And [INL «A»; INL «B»; INL «C»] (INL «D»))) ∧
  (* and: empty Xs list is well-formed *)
  sexp_constraint_dispatch («and»)
    (fromStringL («(() D)»)) =
    INR (Logical (And [] (INL «D»))) ∧
  (* or: mixed var/const in Xs, const result *)
  sexp_constraint_dispatch («or»)
    (fromStringL («((A 3) C)»)) =
    INR (Logical (Or [INL «A»; INR 3] (INL «C»))) ∧
  (* parity: four-variable list *)
  sexp_constraint_dispatch («parity»)
    (fromStringL («((A B C D) Y)»)) =
    INR (Logical (Parity [INL «A»; INL «B»; INL «C»; INL «D»] (INL «Y»))) ∧
  (* and: wrong arity — missing Y *)
  sexp_constraint_dispatch («and»)
    (fromStringL («((A B C))»)) =
    INL («logical expects 2 args: (X1 ... Xn) Y\n») ∧
  (* or: wrong arity — extra arg *)
  sexp_constraint_dispatch («or»)
    (fromStringL («((A B) C D)»)) =
    INL («logical expects 2 args: (X1 ... Xn) Y\n»)
Proof
  EVAL_TAC
QED

Theorem test_channeling:
  (* basic inverse: zero offsets, length-3 lists *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («(((A B C) 0) ((P Q R) 0))»)) =
    INR (Channeling (Inverse ([INL «A»; INL «B»; INL «C»],0)
                              ([INL «P»; INL «Q»; INL «R»],0))) ∧
  (* non-zero matching offsets *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («(((A B) 1) ((P Q) 1))»)) =
    INR (Channeling (Inverse ([INL «A»; INL «B»],1)
                              ([INL «P»; INL «Q»],1))) ∧
  (* asymmetric offsets (offx ≠ offy) *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («(((X Y Z) 0) ((U V W) 1))»)) =
    INR (Channeling (Inverse ([INL «X»; INL «Y»; INL «Z»],0)
                              ([INL «U»; INL «V»; INL «W»],1))) ∧
  (* wrong arity — only one grouped arg *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («(((A B C) 0))»)) =
    INL («inverse expects 2 grouped args: ((X1 ... Xn) offx) ((Y1 ... Ym) offy)\n») ∧
  (* malformed first group — three atoms instead of (list offset) *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («((A B C) ((P Q R) 0))»)) =
    INL («expected (list offset)\n») ∧
  (* non-integer offset *)
  sexp_constraint_dispatch («inverse»)
    (fromStringL («(((A B C) foo) ((P Q R) 0))»)) =
    INL («expected integer, got: foo\n»)
Proof
  EVAL_TAC
QED

Theorem test_cp_inst:
  (* full instance: bounds + constraints + minimize objective *)
  parse_cp_inst («(((X 0 10) (Y 0 10)) ((c1 plus X Y X) (c2 equals X 3)) (minimize X))») =
    INR ([(«X»,0,10); («Y»,0,10)],
         [(«c1», Prim (Binop Plus (INL «X») (INL «Y») (INL «X»)));
          («c2», Prim (Cmpop NONE Equal (INL «X») (INR 3)))],
         Minimize «X») ∧
  (* enumeration *)
  parse_cp_inst («(((X 0 10) (Y 0 10)) ((c1 plus X Y X) (c2 equals X 3)) (enumerate))») =
    INR ([(«X»,0,10); («Y»,0,10)],
         [(«c1», Prim (Binop Plus (INL «X») (INL «Y») (INL «X»)));
          («c2», Prim (Cmpop NONE Equal (INL «X») (INR 3)))],
         Enumerate [«X»;«Y»]) ∧
  (* no objective (only 2 top-level entries) *)
  parse_cp_inst («(() ())») =
    INR ([], [], Decision) ∧
  (* maximize *)
  parse_cp_inst («(((A 0 5)) ((c all_different (A))) (maximize A))») =
    INR ([(«A»,0,5)],
         [(«c», Counting (AllDifferent [INL «A»]))],
         Maximize «A») ∧
  (* constraint-level error propagates through cp_inst *)
  parse_cp_inst («(() ((c unknown X Y)))») =
    INL («unsupported constraint: unknown\n») ∧
  (* malformed objective wrapper *)
  parse_cp_inst («(() () minimize X)») =
    INL («invalid problem type sexpression\n») ∧
  (* top-level sexpression must be an Expr of bounds/constraints/obj *)
  parse_cp_inst («foo») =
    INL («invalid sexpression for top-level CP instance\n») ∧
  (* malformed s-expression (unbalanced parens) → parse failure *)
  parse_cp_inst («(()») =
    INL («sexp parse failure\n»)
Proof
  EVAL_TAC
QED

