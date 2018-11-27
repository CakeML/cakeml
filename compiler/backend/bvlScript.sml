(*
  The BVL intermediate language. This language is a simple first-order
  functional language without closures.
*)
open preamble closLangTheory backend_commonTheory

val _ = new_theory "bvl";
val _ = set_grammar_ancestry [
   "closLang", (* for op *) "backend_common" (* for tags *)
]

(* BVL = bytecode-value language *)

(* BVL aims to be the point where the old and new CakeML compiler
   backend start. It's an interface point as the following diagram
   illustrates.
                                    bytecode → x86 machine code
                                  ↗
   CakeML → ... → IL → ... → BVL                  ARM
                                  ↘              ↗ x86
                                    (new backend) → MIPS
                                                  ↘ js.asm(?)
                                                     ...
*)

(* --- Syntax of BVL --- *)

(* All operations that are uninteresting from a control-flow
   and binding perspective are lumped together in closLang$op. *)

(* There are only a handful of "interesting" operations. *)

(* BVL uses De Bruijn indices so there is no need for a variable name
   in the let-expression. *)

(* The optional number in the call expression below is the label to
   which the call will target. If that component is NONE, then the
   target address is read from the end of the argument list, i.e. in
   case of NONE, the last exp in the argument list must evaluate
   to a CodePtr. This first number in the Call expression is how
   many additional ticks the Call should do. *)

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (num option) (exp list)
      | Op closLang$op (exp list) `

val Bool_def = Define`
  Bool b = Op (Cons (bool_to_tag b)) []`;

val mk_tick_def = Define `
  mk_tick n e = FUNPOW Tick n e : bvl$exp`;

val _ = export_theory();
