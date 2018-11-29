(* Code to recall that some partial functions (of type 'a -> 'b option)
can be represented as sorted alists, and derive a fast conversion on
applications of those functions. *)

signature alist_treeLib = sig

include Abbrev

(* Syntax *)
val alookup_tm : term;
val option_choice_tm : term;
val repr_tm : term;

(* The repr set type *)
type 'a alist_reprs

(*
   Representations of partial functions using sorted trees.
   Requires a relation R and a theorem that shows
   it is irreflexive and transitive. The destructor maps terms
   of the domain type to some type that can be sorted in ML.
   The conversion must prove R x y for any x, y where x is
   sorted before y by the destructor and comparison.
*)
val mk_alist_reprs : thm -> conv -> (term -> 'a)
    -> (('a * 'a) -> order) -> 'a alist_reprs

(*
   The representation set contains representations of various
   partial functions, initially none.
*)
val peek_functions_in_rs : 'a alist_reprs -> term list

(*
   Adds a function's representation.

   Requires a theorem f = rhs with a valid rhs.
   A valid rhs is:
     - ALOOKUP xs
     - a function g in the repr set.
     - option_choice_f of two valid rhs values
*)
val add_alist_repr : 'a alist_reprs -> thm -> unit

(*
   Converts f x to a concrete value (SOME y/NONE)
   for functions f in the repr set.
*)
val reprs_conv : 'a alist_reprs -> conv

end

