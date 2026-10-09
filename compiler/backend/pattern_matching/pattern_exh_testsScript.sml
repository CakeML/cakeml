(*
  Test cases for the exhaustiveness checker of the pattern-match compiler.

  Each theorem states whether a list of pattern rows is exhaustive, and must
  be provable by EVAL_TAC.  The tests use the following imaginary datatypes;
  a constructor is written tag/arity, and a sibling list records the
  tag/arity pairs of every constructor of the datatype.

    bool    True/0  False/1                sibs = [(0,0);(1,0)]
    colour  Red/0   Green/1  Blue/2        sibs = [(0,0);(1,0);(2,0)]
    list    Nil/0   Cons/2                 sibs = [(0,0);(1,2)]
    option  None/0  Some/1                 sibs = [(0,0);(1,1)]
    tree    Leaf/0  Node/3                 sibs = [(0,0);(1,3)]
    wrap    Wrap/1                         sibs = [(0,1)]

  Tuples are Cons NONE, references are Ref, and Any is a wildcard.

  Recall what exhaustiveness means here (exh_rows_thm in pattern_exhTheory):

    match refs rows v <> NONE /\ exh_rows rows
    ==> match refs rows v <> SOME MatchFailure

  So only well-typed values matter: match walks every row and returns NONE
  as soon as any row yields PTypeFailure, hence all of the rows constrain
  the value simultaneously.  At any position the set of possible tag/arity
  pairs is therefore the intersection, over all rows that reach that
  position with a Cons (SOME (t,sibs)) ps pattern, of
  {(t,LENGTH ps)} UNION sibs, where sibs = NONE means "everything"
  (is_sibling x NONE = T).
*)
Theory pattern_exh_tests
Ancestors
  pattern_common pattern_semantics pattern_exh ast
Libs
  preamble

(* ------------------------------------------------------------------ *
   Abbreviations, at the SML level so that the theorem statements are
   fully concrete and EVAL_TAC has nothing to unfold.

   rows [p1;...;pn] builds [(p1,0);...;(pn,n-1)] : (pat # num) list.
   The right-hand sides are irrelevant to exhaustiveness, so they are
   numbered automatically and kept out of the theorem statements.
 * ------------------------------------------------------------------ *)

val bsib  = “(SOME [(0,0);(1,0)])       : (num # num) list option”;
val csib  = “(SOME [(0,0);(1,0);(2,0)]) : (num # num) list option”;
val lsib  = “(SOME [(0,0);(1,2)])       : (num # num) list option”;
val osib  = “(SOME [(0,0);(1,1)])       : (num # num) list option”;
val tsib  = “(SOME [(0,0);(1,3)])       : (num # num) list option”;
val wsib  = “(SOME [(0,1)])             : (num # num) list option”;

val any = “Any”;

val tt = “Cons (SOME (0,^bsib)) []”;                   (* True   *)
val ff = “Cons (SOME (1,^bsib)) []”;                   (* False  *)

val red   = “Cons (SOME (0,^csib)) []”;
val green = “Cons (SOME (1,^csib)) []”;
val blue  = “Cons (SOME (2,^csib)) []”;

val nil_p = “Cons (SOME (0,^lsib)) []”;                (* []     *)
fun cons_p x xs = “Cons (SOME (1,^lsib)) [^x; ^xs]”;   (* x::xs  *)

val none_p = “Cons (SOME (0,^osib)) []”;
fun some_p x = “Cons (SOME (1,^osib)) [^x]”;

val leaf_p = “Cons (SOME (0,^tsib)) []”;
fun node_p l x r = “Cons (SOME (1,^tsib)) [^l; ^x; ^r]”;

fun wrap_p x = “Cons (SOME (0,^wsib)) [^x]”;

fun pair_p x y = “Cons NONE [^x; ^y]”;
fun triple_p x y z = “Cons NONE [^x; ^y; ^z]”;

fun lit_p l = “pattern_semantics$Lit ^l”;
val zero = lit_p “IntLit 0”;
val one  = lit_p “IntLit 1”;

fun ref_p x = “Ref ^x”;
fun or_p x y = “Or ^x ^y”;

fun rows ps =
  let
    fun f i [] = []
      | f i (p::ps) = pairSyntax.mk_pair (p, numSyntax.term_of_int i) :: f (i+1) ps
  in
    listSyntax.mk_list (f 0 ps, pairSyntax.mk_prod (type_of any, numSyntax.num))
  end;


(* ------------------------------------------------------------------ *
   A. baseline: cases the checker has always accepted
 * ------------------------------------------------------------------ *)

Theorem test_any:
  exh_rows ^(rows [any])
Proof
  EVAL_TAC
QED

(* case () of () => .. *)
Theorem test_unit:
  exh_rows ^(rows [“Cons NONE []”])
Proof
  EVAL_TAC
QED

(* case p of (_,_) => .. *)
Theorem test_tuple_wild:
  exh_rows ^(rows [pair_p any any])
Proof
  EVAL_TAC
QED

(* case b of True => .. | False => .. *)
Theorem test_bool:
  exh_rows ^(rows [tt, ff])
Proof
  EVAL_TAC
QED

(* colour, with the rows out of order and one of them duplicated *)
Theorem test_colour_unordered:
  exh_rows ^(rows [blue, red, blue, green])
Proof
  EVAL_TAC
QED

(* case n of 1 => .. | _ => .. *)
Theorem test_lit_then_any:
  exh_rows ^(rows [one, any])
Proof
  EVAL_TAC
QED

(* case n of 1 | _ => .. *)
Theorem test_or_with_any:
  exh_rows ^(rows [or_p one any])
Proof
  EVAL_TAC
QED

(* the same tag at two different arities are two distinct siblings *)
Theorem test_same_tag_two_arities:
  exh_rows ^(rows [“Cons (SOME (0,(SOME [(0,0);(0,1)]):(num#num) list option)) []”,
                   “Cons (SOME (0,(SOME [(0,0);(0,1)]):(num#num) list option)) [Any]”])
Proof
  EVAL_TAC
QED

(* a single-constructor type, e.g. a record *)
Theorem test_single_ctor:
  exh_rows ^(rows [“Cons (SOME (0,(SOME [(0,2)]):(num#num) list option)) [Any;Any]”])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   B. the sibling information is not on the first row
 * ------------------------------------------------------------------ *)

(* the first row carries no sibling info; the second row pins the type down *)
Theorem test_sibs_on_later_row:
  exh_rows ^(rows [“Cons (SOME (0,NONE)) []”, ff])
Proof
  EVAL_TAC
QED

(* the sibling info is only available below a tuple *)
Theorem test_sibs_below_tuple:
  exh_rows ^(rows [“Cons NONE [Cons (SOME (0,NONE)) []]”, “Cons NONE [^ff]”])
Proof
  EVAL_TAC
QED

(* an empty sibling list: the row's own tag is the only well-typed value *)
Theorem test_empty_sibs:
  exh_rows ^(rows [“Cons (SOME (0,(SOME []):(num#num) list option)) []”])
Proof
  EVAL_TAC
QED

(* an extra row at an arity the type does not have is harmless *)
Theorem test_wrong_arity_row:
  exh_rows ^(rows [wrap_p any, “Cons (SOME (0,^wsib)) [Any;Any]”])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   C. nested constructors
 * ------------------------------------------------------------------ *)

(* case xs of [] => .. | [_] => .. | _::_::_ => .. *)
Theorem test_list_three_cases:
  exh_rows ^(rows [nil_p,
                   cons_p any nil_p,
                   cons_p any (cons_p any any)])
Proof
  EVAL_TAC
QED

(* case x of NONE => .. | SOME [] => .. | SOME (_::_) => .. *)
Theorem test_option_of_list:
  exh_rows ^(rows [none_p,
                   some_p nil_p,
                   some_p (cons_p any any)])
Proof
  EVAL_TAC
QED

(* three levels of option *)
Theorem test_option_cubed:
  exh_rows ^(rows [none_p,
                   some_p none_p,
                   some_p (some_p none_p),
                   some_p (some_p (some_p any))])
Proof
  EVAL_TAC
QED

(* case t of Leaf                     => ..
           | Node (Leaf,_,_)          => ..
           | Node (Node _,_,Leaf)     => ..
           | Node (Node _,_,Node _)   => .. *)
Theorem test_tree:
  exh_rows ^(rows [leaf_p,
                   node_p leaf_p any any,
                   node_p (node_p any any any) any leaf_p,
                   node_p (node_p any any any) any (node_p any any any)])
Proof
  EVAL_TAC
QED

(* case xs of [] => .. | true::_ => .. | false::[] => .. | false::_::_ => .. *)
Theorem test_list_of_bool:
  exh_rows ^(rows [nil_p,
                   cons_p tt any,
                   cons_p ff nil_p,
                   cons_p ff (cons_p any any)])
Proof
  EVAL_TAC
QED

(* nested tuples: ((T,_),_) | ((F,T),_) | ((F,F),_) *)
Theorem test_nested_tuples:
  exh_rows ^(rows [pair_p (pair_p tt any) any,
                   pair_p (pair_p ff tt) any,
                   pair_p (pair_p ff ff) any])
Proof
  EVAL_TAC
QED

(* a single-constructor type nested inside itself *)
Theorem test_single_ctor_nested:
  exh_rows ^(rows [wrap_p (wrap_p any)])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   D. multi-column matrices, encoded as tuples
 * ------------------------------------------------------------------ *)

(* (T,_) | (_,T) | (F,F) *)
Theorem test_bool_pair_diag:
  exh_rows ^(rows [pair_p tt any,
                   pair_p any tt,
                   pair_p ff ff])
Proof
  EVAL_TAC
QED

(* (T,T) | (T,F) | (F,_) *)
Theorem test_bool_pair_split:
  exh_rows ^(rows [pair_p tt tt,
                   pair_p tt ff,
                   pair_p ff any])
Proof
  EVAL_TAC
QED

(* ([],_) | (_,[]) | (_::_,_::_) *)
Theorem test_list_pair:
  exh_rows ^(rows [pair_p nil_p any,
                   pair_p any nil_p,
                   pair_p (cons_p any any) (cons_p any any)])
Proof
  EVAL_TAC
QED

(* all nine colour pairs, in scrambled order *)
Theorem test_colour_pair_full:
  exh_rows ^(rows [pair_p green blue,
                   pair_p blue red,
                   pair_p red red,
                   pair_p blue blue,
                   pair_p green red,
                   pair_p red blue,
                   pair_p blue green,
                   pair_p green green,
                   pair_p red green])
Proof
  EVAL_TAC
QED

(* (T,_,_) | (F,T,_) | (F,F,T) | (F,F,F) *)
Theorem test_bool_triple:
  exh_rows ^(rows [triple_p tt any any,
                   triple_p ff tt any,
                   triple_p ff ff tt,
                   triple_p ff ff ff])
Proof
  EVAL_TAC
QED

(* only the second column is discriminated, the rest are wildcards *)
Theorem test_wide_tuple_one_column:
  exh_rows ^(rows [“Cons NONE [Any; ^tt; Any; Any]”,
                   “Cons NONE [Any; ^ff; Any; Any]”])
Proof
  EVAL_TAC
QED

(* a literal column does not prevent exhaustiveness via another column:
     case (n,b) of (1,_) => .. | (_,True) => .. | (_,False) => .. *)
Theorem test_lit_column_ignored:
  exh_rows ^(rows [pair_p one any,
                   pair_p any tt,
                   pair_p any ff])
Proof
  EVAL_TAC
QED

(* column 1 is covered by rows 2 and 3; row 1 only narrows column 2's type *)
Theorem test_coverage_from_other_rows:
  exh_rows ^(rows [pair_p any “Cons (SOME (0,NONE)) []”,
                   pair_p tt any,
                   pair_p ff any])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   E. Or-patterns
 * ------------------------------------------------------------------ *)

(* case b of True | False => .. *)
Theorem test_or_bool:
  exh_rows ^(rows [or_p tt ff])
Proof
  EVAL_TAC
QED

(* case c of Red | Green => .. | Blue => .. *)
Theorem test_or_colour:
  exh_rows ^(rows [or_p red green, blue])
Proof
  EVAL_TAC
QED

(* an Or inside a constructor argument *)
Theorem test_or_in_argument:
  exh_rows ^(rows [wrap_p (or_p red green), wrap_p blue])
Proof
  EVAL_TAC
QED

(* case xs of [] | _::_ => .. *)
Theorem test_or_list:
  exh_rows ^(rows [or_p nil_p (cons_p any any)])
Proof
  EVAL_TAC
QED

(* the whole diagonal matrix squeezed into a single Or row *)
Theorem test_or_whole_matrix:
  exh_rows ^(rows [or_p (pair_p tt any)
                        (or_p (pair_p any tt) (pair_p ff ff))])
Proof
  EVAL_TAC
QED

(* an Or in one column, constructors in the other *)
Theorem test_or_column:
  exh_rows ^(rows [pair_p (or_p red green) any,
                   pair_p blue tt,
                   pair_p blue ff])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   F. references
 * ------------------------------------------------------------------ *)

Theorem test_ref_any:
  exh_rows ^(rows [ref_p any])
Proof
  EVAL_TAC
QED

(* case r of ref True => .. | ref False => .. *)
Theorem test_ref_bool:
  exh_rows ^(rows [ref_p tt, ref_p ff])
Proof
  EVAL_TAC
QED

Theorem test_ref_in_tuple:
  exh_rows ^(rows [pair_p (ref_p any) any])
Proof
  EVAL_TAC
QED

Theorem test_ref_nested:
  exh_rows ^(rows [ref_p (pair_p any (ref_p any))])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   G. robustness: redundant rows, rows after a wildcard
 * ------------------------------------------------------------------ *)

Theorem test_duplicate_rows:
  exh_rows ^(rows [tt, tt, ff, tt])
Proof
  EVAL_TAC
QED

Theorem test_rows_after_any:
  exh_rows ^(rows [any, tt])
Proof
  EVAL_TAC
QED

Theorem test_redundant_last_row:
  exh_rows ^(rows [nil_p,
                   cons_p any any,
                   cons_p nil_p nil_p])
Proof
  EVAL_TAC
QED


(* ------------------------------------------------------------------ *
   N. rows that must NOT be reported exhaustive.

   Each of these has a concrete uncovered value, so reporting any of
   them exhaustive would falsify exh_rows_thm.  They all hold for the
   current checker and must keep holding after any rewrite.
 * ------------------------------------------------------------------ *)

Theorem test_not_empty:
  ~exh_rows ^(rows [])
Proof
  EVAL_TAC
QED

(* False is uncovered *)
Theorem test_not_missing_ctor:
  ~exh_rows ^(rows [tt])
Proof
  EVAL_TAC
QED

(* there are infinitely many integers *)
Theorem test_not_literals:
  ~exh_rows ^(rows [zero, one])
Proof
  EVAL_TAC
QED

(* no sibling information anywhere, so any tag at all is possible *)
Theorem test_not_no_sibs:
  ~exh_rows ^(rows [“Cons (SOME (0,NONE)) []”, “Cons (SOME (1,NONE)) []”])
Proof
  EVAL_TAC
QED

(* tag 5 is not a constructor of the type, so it covers nothing in it *)
Theorem test_not_bogus_tag:
  ~exh_rows ^(rows [“Cons (SOME (5,^bsib)) []”])
Proof
  EVAL_TAC
QED

(* both columns are individually full, the matrix is not: (T,F) uncovered *)
Theorem test_not_bool_pair:
  ~exh_rows ^(rows [pair_p tt tt, pair_p ff ff])
Proof
  EVAL_TAC
QED

(* (F,F) uncovered *)
Theorem test_not_bool_pair_diag:
  ~exh_rows ^(rows [pair_p tt any, pair_p any tt])
Proof
  EVAL_TAC
QED

(* one row short of test_bool_pair_diag: (F,F) uncovered *)
Theorem test_not_bool_pair_almost:
  ~exh_rows ^(rows [pair_p tt any,
                    pair_p any tt,
                    pair_p ff tt])
Proof
  EVAL_TAC
QED

(* _::_::_ uncovered *)
Theorem test_not_list:
  ~exh_rows ^(rows [nil_p, cons_p any nil_p])
Proof
  EVAL_TAC
QED

(* (_::_,_::_) uncovered *)
Theorem test_not_list_pair:
  ~exh_rows ^(rows [pair_p nil_p any,
                    pair_p (cons_p any any) nil_p])
Proof
  EVAL_TAC
QED

(* SOME (_::_) uncovered *)
Theorem test_not_option_of_list:
  ~exh_rows ^(rows [none_p, some_p nil_p])
Proof
  EVAL_TAC
QED

(* ref False uncovered *)
Theorem test_not_ref:
  ~exh_rows ^(rows [ref_p tt])
Proof
  EVAL_TAC
QED

(* Blue uncovered *)
Theorem test_not_or:
  ~exh_rows ^(rows [or_p red green])
Proof
  EVAL_TAC
QED

(* Node (Node _,_,Node _) uncovered *)
Theorem test_not_tree:
  ~exh_rows ^(rows [leaf_p,
                    node_p leaf_p any any,
                    node_p (node_p any any any) any leaf_p])
Proof
  EVAL_TAC
QED
