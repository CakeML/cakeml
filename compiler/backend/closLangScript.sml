open preamble;

val _ = new_theory "closLang";

(* compilation from this language removes closures *)

val max_app_def = Define `
  max_app = 3:num`;

val _ = Datatype `
  op = Global num    (* load global var with index *)
     | SetGlobal num (* assign a value to a global *)
     | AllocGlobal   (* make space for a new global *)
     | GlobalsPtr    (* get pointer to globals array *)
     | SetGlobalsPtr (* set pointer to globals array *)
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
     | TagLenEq num num (* check Block's tag and length *)
     | TagEq num     (* check Block's tag *)
     | BlockCmp      (* do two blocks have the same tag and length? *)
     | IsBlock       (* is it a Block value? *)
     | Ref           (* makes a reference *)
     | Deref         (* loads a value from a reference *)
     | Update        (* updates a reference *)
     | Label num     (* constructs a CodePtr *)
     | FFI num       (* calls the FFI *)
     | Equal         (* structural equality (non-recursive in BVL) *)
     | Const int     (* integer *)
     | Add           (* + over the integers *)
     | Sub           (* - over the integers *)
     | Mult          (* * over the integers *)
     | Div           (* div over the integers *)
     | Mod           (* mod over the integers *)
     | Less          (* < over the integers *)
     | LessEq        (* <= over the integers *)
     | Greater       (* > over the integers *)
     | GreaterEq     (* >= over the integers *)
     | WordOp word_size opw
     | WordShift word_size shift num
     | WordFromInt
     | WordToInt`

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (exp list)
      | App (num option) exp (exp list)
      | Fn (num option) (num list option) num exp
      | Letrec (num option) (num list option) ((num # exp) list) exp
      | Op op (exp list) `;

val exp_size_def = definition"exp_size_def";

val exp1_size_lemma = store_thm("exp1_size_lemma",
  ``!fns n x. MEM (n,x) fns ==> exp_size x < exp1_size fns``,
  Induct \\ fs [FORALL_PROD,exp_size_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ SRW_TAC [] [] \\ DECIDE_TAC);

val _ = export_theory()
