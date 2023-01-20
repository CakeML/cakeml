(*
  The MultiRet intermediate language. This language is similar to BVL,
  but with two notable differences: (1) this language allows for
  multi-value returns from function calls; and (2) exceptions can only
  be caught at the point of function calls.
*)
open preamble closLangTheory;

val _ = new_theory "multiretLang";
val _ = set_grammar_ancestry ["closLang" (* for op *)]

(* MultiRetLang is a stepping stone on the way from BVL to
   dataLang. MultiRetLang is almost identical to BVL. The main
   differences are:

    - MultiRetLang language supports returning multiple values
      simultaneuosly (without) tupling them up in a Block. The
      returned values are returned in registers.

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


(* --- Syntax --- *)

Datatype:
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Tick exp
      | Call num (num option) (exp list) (* handler: *) (exp option)
      | Op op (exp list)
      (* multi-value returns and calls: *)
      | Return (exp list)
      | LetCall (* decrement by tick count: *) num
                 (* how many return values: *) num
                    (* destination of call: *) num
                              (* arguments: *) (exp list)
                             (* RHS of let: *) exp
      | TailCall (* same as above, minus the last exp: *) num num num (exp list)
End

val _ = export_theory();
