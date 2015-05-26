open HolKernel Parse boolLib bossLib

val _ = new_theory "closLang";

(* compilation from this language removes closures *)

val _ = Datatype `
  op = Global num    (* load global var with index *)
     | AllocGlobal   (* make space for a new global *)
     | SetGlobal num (* assign a value to a global *)
     | Cons num      (* construct a Block with given tag *)
     | El            (* read Block field index *)
     | LengthBlock   (* get length of Block *)
     | Length        (* get length of reference *)
     | LengthByte    (* get length of byte array *)
     | RefByte       (* makes a byte array *)
     | RefArray      (* makes an array by replicating a value *)
     | DerefByte     (* loads a byte from a byte array *)
     | UpdateByte    (* updates a byte array *)
     | FromList num  (* convert list to packed Block *)
     | ToList        (* convert packed Block to list *)
     | Const int     (* integer *)
     | TagEq num     (* check whether Block's tag is eq *)
     | IsBlock       (* is it a Block value? *)
     | Ref           (* makes a reference *)
     | Deref         (* loads a value from a reference *)
     | Update        (* updates a reference *)
     | Label num     (* constructs a CodePtr *)
     | PrintC char   (* prints a character *)
     | Equal         (* structural equality *)
     | Add           (* + over the integers *)
     | Sub           (* - over the integers *)
     | Mult          (* * over the integers *)
     | Div           (* div over the integers *)
     | Mod           (* mod over the integers *)
     | Less          (* < over the integers *)
     | LessEq        (* <= over the integers *)
     | Greater       (* > over the integers *)
     | GreaterEq     (* >= over the integers *) `

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (exp list)
      | App (num option) exp (exp list)
      | Fn num (num list) num exp
      | Letrec num (num list) ((num # exp) list) exp
      | Op op (exp list) `

val _ = export_theory()
