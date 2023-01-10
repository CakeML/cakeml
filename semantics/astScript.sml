(*
  Definition of CakeML abstract syntax (AST).
*)
open HolKernel Parse boolLib bossLib;
open namespaceTheory fpSemTheory fpValTreeTheory realOpsTheory;

val _ = numLib.prefer_num();

local open integerTheory wordsTheory stringTheory namespaceTheory locationTheory in end;
val _ = new_theory "ast"
val _ = set_grammar_ancestry ["integer", "words", "string", "namespace", "location"];

(* Literal constants *)
Datatype:
  lit =
    IntLit int
  | Char char
  | StrLit string
  | Word8 word8
  | Word64 word64
End

(* Built-in binary operations *)
Datatype:
  opn = Plus | Minus | Times | Divide | Modulo
End

Datatype:
  opb = Lt | Gt | Leq | Geq
End

Datatype:
  opw = Andw | Orw | Xor | Add | Sub
End

Datatype:
  shift = Lsl | Lsr | Asr | Ror
End

(* Module names *)
Type modN = “:string”

(* Variable names *)
Type varN = “:string”

(* Constructor names (from datatype definitions) *)
Type conN = ``: string``

(* Type names *)
Type typeN = ``: string``

(* Type variable names *)
Type tvarN = ``: string``

Datatype:
  word_size = W8 | W64
End

Datatype:
  op =
  (* Operations on integers *)
    Opn opn
  | Opb opb
  (* Operations on words *)
  | Opw word_size opw
  | Shift word_size shift num
  | Equality
  (* FP operations *)
  | FP_cmp fp_cmp
  | FP_uop fp_uop
  | FP_bop fp_bop
  | FP_top fp_top
  (* Floating-point <-> word translations *)
  | FpFromWord
  | FpToWord
  (* Real ops for verification *)
  | Real_cmp real_cmp
  | Real_uop real_uop
  | Real_bop real_bop
  (* Translation from floating-points to reals for verification *)
  | RealFromFP
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
  (* Word/integer conversions *)
  | WordFromInt word_size
  | WordToInt word_size
  (* string/bytearray conversions *)
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  (* Char operations *)
  | Ord
  | Chr
  | Chopb opb
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
  (* Unsafe array accesses *)
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI string
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
  | Simple (* arithmetic operation, no finite-precision/reals *)
  | Icing (* 64-bit floating-points *)
  | Reals (* real numbers *)
End
Definition getOpClass_def[simp]:
 getOpClass op =
 case op of
   FP_cmp _ => Icing
  | FP_top _ => Icing
  | FP_bop _ => Icing
  | FP_uop _ => Icing
  | Real_cmp _ => Reals
  | Real_bop _ => Reals
  | Real_uop _ => Reals
  | RealFromFP => Reals
  | Opapp => FunApp
  | Eval => EvalOp
  | _ => Simple
End

Definition isFpBool_def:
  isFpBool op = case op of FP_cmp _ => T | _ => F
End

(* Logical operations *)
Datatype:
 lop = And | Or
End

(* Types *)
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
  (* Floating-point optimisations *)
  | FpOptimise fp_opt exp
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
  (every_exp p (FpOptimise sc e) ⇔
             p (FpOptimise sc e) ∧ every_exp p e) ∧
  (every_exp p (Letrec funs e) ⇔
             p (Letrec funs e) ∧ every_exp p e ∧ EVERY (λ(n,v,e). every_exp p e) funs)
Termination
  WF_REL_TAC ‘measure $ exp_size o SND’
End

val _ = export_theory()
