(*
  The closLang intermediate language. This language is the last
  intermediate language that has closure values. This language is
  designed for optimisation of function calls.
*)
Theory closLang
Ancestors
  ast[qualified] backend_common mlstring fpSem
Libs
  preamble

(* compilation from this language removes closures *)

Datatype:
  const = ConstCons num (const list)
        | ConstInt int
        | ConstStr mlstring
        | ConstWord64 word64
End

Datatype:
  const_part = Con num (num list)
             | Int int
             | Str mlstring
             | W64 word64
End

Datatype:
  int_op
     = Const int          (* integer *)
     | Add                (* + over the integers *)
     | Sub                (* - over the integers *)
     | Mult               (* * over the integers *)
     | Div                (* div over the integers *)
     | Mod                (* mod over the integers *)
     | Less               (* < over the integers *)
     | LessEq             (* <= over the integers *)
     | Greater            (* > over the integers *)
     | GreaterEq          (* >= over the integers *)
     | LessConstSmall num (* checks < const for small ints *)
End

Datatype:
  word_op
     = WordOpw word_size opw
     | WordShift word_size shift num
     | WordTest word_size ast$test
     | WordFromInt
     | WordToInt
     | WordFromWord bool
     | FP_cmp fp_cmp
     | FP_uop fp_uop
     | FP_bop fp_bop
     | FP_top fp_top
End

Datatype:
  block_op
     = Cons num          (* construct a Block with given tag *)
     | ElemAt num        (* same as El but for constant index *)
     | TagLenEq num num  (* check Block's tag and length *)
     | LenEq num         (* check Block's length *)
     | TagEq num         (* check Block's tag *)
     | LengthBlock       (* get length of Block *)
     | BoolTest ast$test (* tests for bools *)
     | BoolNot           (* boolean not *)
     | BoundsCheckBlock  (* check that vector index is within bounds *)
     | ConsExtend num    (* construct a Block with given tag. The first three
                            arguments should be a block followed by two numbers
                            indicating the first element, and how many, should be
                            copied into the end of the new block. The fourth
                            argument is the total size of the new block. *)
     | FromList num      (* convert list to packed Block *)
     | ListAppend        (* appends two lists *)
     | Constant const    (* produces a constant value *)
     | Equal             (* structural equality *)
     | EqualConst const_part (* equal to integer/string/word constant *)
     | Build (const_part list)  (* implementation of Constant above *)
End

Datatype:
  glob_op
     = Global num    (* load global var with index *)
     | SetGlobal num (* assign a value to a global *)
     | AllocGlobal   (* make space for a new global *)
     | GlobalsPtr    (* get pointer to globals array *)
     | SetGlobalsPtr (* set pointer to globals array *)
End

Datatype:
  mem_op
     = Ref           (* makes a reference/array *)
     | Update        (* updates a reference/array *)
     | El            (* read index from block of reference/array *)
     | Length        (* get length of reference *)
     | LengthByte    (* get length of byte array *)
     | RefByte bool  (* makes a byte array, T = immutable/compare-by-contents *)
     | RefArray      (* makes an array by replicating a value *)
     | DerefByte     (* loads a byte from a byte array *)
     | UpdateByte    (* updates a byte array *)
     | ConcatByteVec (* concatenate list of byte vectors *)
     | CopyByte bool (* copy a slice of a byte array, T means target should be allocated *)
     | FromListByte  (* convert list of chars to ByteVector *)
     | ToListByte    (* convert ByteVector to list of chars *)
     | LengthByteVec (* get length of ByteVector *)
     | DerefByteVec  (* load a byte from a ByteVector *)
     | XorByte       (* xor a btye vector into a byte array *)
     | BoundsCheckArray
     | BoundsCheckByte bool (* T = loose (<=) bound *)
     | ConfigGC
End

Datatype:
  op = Label num     (* constructs a CodePtr *)
     | FFI mlstring    (* calls the FFI *)
     | IntOp int_op
     | WordOp word_op
     | BlockOp block_op
     | GlobOp glob_op
     | MemOp mem_op
     | Install       (* installs new code at runtime *)
     | ThunkOp thunk_op
End

Datatype:
  exp = Var tra num
      | If tra exp exp exp
      | Let tra (exp list) exp
      | Raise tra exp
      | Handle tra exp exp
      | Tick tra exp
      | Call tra num (* ticks *) num (* loc *) (exp list) (* args *)
      | App tra (num option) exp (exp list)
      | Fn mlstring (num option) (num list option) num exp
      | Letrec (mlstring list) (num option) (num list option) ((num # exp) list) exp
      | Op tra op (exp list)
End

val exp_size_def = definition"exp_size_def";

Definition has_install_def:
  has_install ((Var t n):closLang$exp) = F ∧
  has_install (If t e1 e2 e3) = (has_install e1 ∨ has_install e2 ∨ has_install e3) ∧
  has_install (Let t es e) = (has_install e ∨ has_install_list es) ∧
  has_install (Op t p es) = (p = Install ∨ has_install_list es) ∧
  has_install (Raise t e) = has_install e ∧
  has_install (Tick t e) = has_install e ∧
  has_install (Fn _ _ _ _ e) = has_install e ∧
  has_install (Handle t e1 e2) = (has_install e1 ∨ has_install e2) ∧
  has_install (Call _ _ _ es) = has_install_list es ∧
  has_install (App _ _ e es) = (has_install e ∨ has_install_list es) ∧
  has_install (Letrec _ _ _ fns e) = (has_install_list (MAP SND fns) ∨ has_install e) ∧
  has_install_list [] = F ∧
  has_install_list (x::xs) = (has_install x ∨ has_install_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL e => closLang$exp_size e
                                    | INR es => list_size closLang$exp_size es’
  \\ rw []
  \\ qsuff_tac ‘list_size exp_size (MAP SND fns) ≤ list_size (pair_size (λx. x) exp_size) fns’
  >- fs []
  \\ Induct_on ‘fns’ \\ fs []
  \\ fs [list_size_def,FORALL_PROD]
  \\ rw [] \\ fs [basicSizeTheory.pair_size_def]
End

Theorem exp1_size_lemma:
  !fns n x. MEM (n,x) fns ==> exp_size x < exp1_size fns
Proof
  Induct \\ fs [FORALL_PROD,exp_size_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ SRW_TAC [] [] \\ DECIDE_TAC
QED

Definition pure_op_def:
  pure_op op ⇔
    case op of
      FFI _ => F
    | GlobOp (SetGlobal _) => F
    | GlobOp AllocGlobal => F
    | MemOp (RefByte _) => F
    | MemOp RefArray => F
    | MemOp UpdateByte => F
    | MemOp (CopyByte F) => F
    | MemOp XorByte => F
    | MemOp Ref => F
    | MemOp Update => F
    | Install => F
    | ThunkOp _ => F
    | _ => T
End

(* pure e means e can neither raise an exception nor side-effect the state *)
Definition pure_def:
  (pure (Var _ _) ⇔ T)
    ∧
  (pure (If _ e1 e2 e3) ⇔ pure e1 ∧ pure e2 ∧ pure e3)
    ∧
  (pure (Let _ es e2) ⇔ EVERY pure es ∧ pure e2)
    ∧
  (pure (Raise _ _) ⇔ F)
    ∧
  (pure (Handle _ e1 e2) ⇔ pure e1)
    ∧
  (pure (Tick _ _) ⇔ F)
    ∧
  (pure (Call _ _ _ _) ⇔ F)
    ∧
  (pure (App _ _ _ _) ⇔ F)
    ∧
  (pure (Fn _ _ _ _ _) ⇔ T)
    ∧
  (pure (Letrec _ _ _ _ x) ⇔ pure x)
    ∧
  (pure (Op _ opn es) ⇔ EVERY pure es ∧ pure_op opn)
End

(* used in proofs about closLang, BVL, BVI and dataLang *)
Definition assign_get_code_label_def:
  (assign_get_code_label (closLang$Label x) = {x}) ∧
  (assign_get_code_label x = {})
End

Type clos_prog = ``: closLang$exp list # (num # num # closLang$exp) list``

Type clos_cc = ``:'c -> clos_prog -> (word8 list # word64 list # 'c) option``
