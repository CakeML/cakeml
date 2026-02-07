(*
  Definition of CakeML abstract syntax (AST).
*)
Theory ast
Ancestors
  integer[qualified] words[qualified] string[qualified] mlstring[qualified] namespace
  location[qualified]

(* Literal constants *)
Datatype:
  lit =
    IntLit int
  | Char char
  | StrLit mlstring
  | Word8 word8
  | Word64 word64
  | Float64 word64
End

Datatype:
  shift = Lsl | Lsr | Asr | Ror
End

Datatype:
  arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
End

(* Module names *)
Type modN = “:mlstring”

(* Variable names *)
Type varN = “:mlstring”

(* Constructor names (from datatype definitions) *)
Type conN = ``: mlstring``

(* Type names *)
Type typeN = ``: mlstring``

(* Type variable names *)
Type tvarN = ``: mlstring``

Datatype:
  word_size = W8 | W64
End

Datatype:
  thunk_mode = Evaluated | NotEvaluated
End

Datatype:
  thunk_op =
    AllocThunk thunk_mode
  | UpdateThunk thunk_mode
  | ForceThunk
End

Datatype:
  opb = Lt | Gt | Leq | Geq
End

Datatype:
  test = Equal | Compare opb | AltCompare opb
End

Datatype:
  prim_type = BoolT
            | IntT
            | CharT
            | StrT
            | WordT word_size
            | Float64T
End

Datatype:
  op =
  (* primitive operations for the primitive types: +, -, and, sqrt, etc. *)
    Arith arith prim_type
  (* conversions between primitive types: char<->int, word<->double, word<->int *)
  | FromTo prim_type prim_type
  (* Operations on words *)
  | Shift word_size shift num
  | Equality
  | Test test prim_type
  (* Function application *)
  | Opapp
  (* Reference operations *)
  | Opassign
  | Opref
  | Opderef
  (* Word8Array operations *)
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  (* string/bytearray conversions *)
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  | XorAw8Str_unsafe
  (* String operations *)
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vlength
  (* Array operations *)
  | Aalloc
  | AallocEmpty
  | AallocFixed
  | Asub
  | Alength
  | Aupdate
  (* Unsafe vector/array accesses *)
  | Vsub_unsafe
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  (* thunk operations *)
  | ThunkOp thunk_op
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI mlstring
  (* Evaluate new code in a given env *)
  | Eval
  (* Get the identifier of an env object *)
  | Env_id
End

(* Define operator classes, that allow to group their behavior later *)
Datatype:
 op_class =
    EvalOp (* Eval primitive *)
  | FunApp (* function application *)
  | Force (* forcing a thunk *)
  | Simple (* arithmetic operation, no finite-precision/reals *)
End

Definition getOpClass_def[simp]:
 getOpClass op =
 case op of
  | Opapp => FunApp
  | Eval => EvalOp
  | ThunkOp t => (if t = ForceThunk then Force else Simple)
  | _ => Simple
End

(* Types used in type annotations *)
Datatype:
 ast_t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Atvar tvarN
  (* Function type *)
  | Atfun ast_t ast_t
  (* Tuple type *)
  | Attup (ast_t list)
  (* Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) *)
  | Atapp (ast_t list) ((modN, typeN) id)
End

(* Patterns *)
Datatype:
 pat =
    Pany
  | Pvar varN
  | Plit lit
  (* Constructor applications.
     A Nothing constructor indicates a tuple pattern. *)
  | Pcon (((modN, conN) id) option) (pat list)
  | Pref pat
  (* Pattern alias. *)
  | Pas pat varN
  | Ptannot pat ast_t
End

(* Short circuiting logical operations *)
Datatype:
  lop = Andalso | Orelse
End

(* Expressions *)
Datatype:
 exp =
    Raise exp
  | Handle exp ((pat # exp) list)
  | Lit lit
  (* Constructor application.
     A Nothing constructor indicates a tuple pattern. *)
  | Con (((modN, conN)id)option) (exp list)
  | Var ((modN, varN) id)
  | Fun varN exp
  (* Application a primitive operator to arguments.
     Includes function application. *)
  | App op (exp list)
  (* Logical operations (and, or) *)
  | Log lop exp exp
  | If exp exp exp
  (* Pattern matching *)
  | Mat exp ((pat # exp) list)
  (* A let expression
     A Nothing value for the binding indicates that this is a
     sequencing expression, that is: (e1; e2). *)
  | Let (varN option) exp exp
  (* Local definition (potentially) mutually recursive
     functions.
     The first varN is the function's name, and the second varN
     is its parameter. *)
  | Letrec ((varN # varN # exp) list) exp
  | Tannot exp ast_t
  (* Location annotated expressions, not expected in source programs *)
  | Lannot exp locs
End

Type type_def = ``: ( tvarN list # typeN # (conN # ast_t list) list) list``

(* Declarations *)
Datatype:
 dec =
  (* Top-level bindings
   * The pattern allows several names to be bound at once *)
    Dlet locs pat exp
  (* Mutually recursive function definition *)
  | Dletrec locs ((varN # varN # exp) list)
  (* Type definition
     Defines several data types, each which has several
     named variants, which can in turn have several arguments.
   *)
  | Dtype locs type_def
  (* Type abbreviations *)
  | Dtabbrev locs (tvarN list) typeN ast_t
  (* New exceptions *)
  | Dexn locs conN (ast_t list)
  (* Module *)
  | Dmod modN (dec list)
  (* Local: local part, visible part *)
  | Dlocal (dec list) (dec list)
  (* Store current lexical env in an env value *)
  | Denv tvarN
End

(* Accumulates the bindings of a pattern *)
Definition pat_bindings_def:
  pat_bindings Pany already_bound = already_bound ∧
  pat_bindings (Pvar n) already_bound = n::already_bound ∧
  pat_bindings (Plit l) already_bound = already_bound ∧
  pat_bindings (Pcon v0 ps) already_bound = pats_bindings ps already_bound ∧
  pat_bindings (Pref p) already_bound = pat_bindings p already_bound ∧
  pat_bindings (Pas p i) already_bound = pat_bindings p (i::already_bound) ∧
  pat_bindings (Ptannot p v1) already_bound = pat_bindings p already_bound ∧
  pats_bindings [] already_bound = already_bound ∧
  pats_bindings (p::ps) already_bound =
  pats_bindings ps (pat_bindings p already_bound)
End

Definition every_exp_def[simp]:
  (every_exp p (Raise e) ⇔
             p (Raise e) ∧ every_exp p e) ∧
  (every_exp p (Handle e pes) ⇔
             p (Handle e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (ast$Lit l) ⇔
             p (ast$Lit l)) ∧
  (every_exp p (Con cn es) ⇔
             p (Con cn es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Var v) ⇔
             p (Var v)) ∧
  (every_exp p (Fun x e) ⇔
             p (Fun x e) ∧ every_exp p e) ∧
  (every_exp p (App op es) ⇔
             p (App op es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Log lop e1 e2) ⇔
             p (Log lop e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (If e1 e2 e3) ⇔
             p (If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3) ∧
  (every_exp p (Mat e pes) ⇔
             p (Mat e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (Let x e1 e2) ⇔
             p (Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (Tannot e a) ⇔
             p (Tannot e a) ∧ every_exp p e) ∧
  (every_exp p (Lannot e a) ⇔
             p (Lannot e a) ∧ every_exp p e) ∧
  (every_exp p (Letrec funs e) ⇔
             p (Letrec funs e) ∧ every_exp p e ∧ EVERY (λ(n,v,e). every_exp p e) funs)
End

Definition Seqs_def:
  Seqs [] = Con NONE [] ∧
  Seqs (x::xs) = Let NONE x (Seqs xs)
End

Definition Apps_def:
  Apps f [] = f ∧
  Apps f (x::xs) = Apps (App Opapp [f; x]) xs
End

Definition Funs_def:
  Funs [] e = e ∧
  Funs (x::xs) e = Fun x (Funs xs e)
End
