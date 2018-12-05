(*
  The BVI intermediate language. This language is very similar to BVL.
  One of the more notable differences is that exception handling is
  now bundled together with function calls: exceptions can only be
  caught at the point of function calls.
*)
open preamble closLangTheory;

val _ = new_theory "bvi";
val _ = set_grammar_ancestry ["closLang" (* for op *)]

(* BVI = bytecode-value intermediate language *)

(* BVI is a stepping stone on the way from BVL to dataLang. BVI is almost
   identical to BVL. The main differences are:

    - The Handle (exception) construct from BVL has been merged into
      the Call construct. The reason we want to do this is that we
      want each function in BVI (and the following intermediate
      languages) to only operate within one stack frame. The execution
      of the body of the Handle construct is to execute in a separate
      stack frame. To keep things simple and uniform, we merge all
      stack-frame creation into the Call construct. Note that BVL and
      BVI have no concept of stack frames. However, the next language,
      dataLang, does have stack frames. BVI is a nice high-level language
      where the Handle construct can cleanly be eliminated.

    - Each creation of a number constant must only produce constants
      that will fit into a machine word. The previous language, BVL,
      allows any size of integer to be constructed immediately. In
      BVI, we compile creation of very large constants into creation
      of small constants, and plug these together using +, - and *.

    - BVI also doesn't have the 'globals' state component from BVL.
      BVI implements the globals using a (dynamically extended) wide
      reference. *)


(* --- Syntax of BVI --- *)

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Tick exp
      | Call num (num option) (exp list) (exp option)
      | Op op (exp list) `

val _ = export_theory();
