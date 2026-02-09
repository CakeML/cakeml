(*
  The first intermediate language flatLang. It removes modules and
  resolves all global scoping. Each value definition gets allocated a
  slot in a global variable store, and each type and exception gets a
  unique global identifier. It removes andalso and orelse and
  replaces them with if, and removes the AallocEmpty primitive op and
  replaces it with an alloc call with 0.

  The AST of flatLang differs from the source language by having two
  variable reference forms, one to reference local bindings (still by
  name) and one to reference global bindings (by index). At the top
  level, modules and let recs are gone. Top-level lets and letrecs no
  longer bind names (or have patterns). Constructor names are replaced
  with numbers, and type and exception definitions record the arities
  of the constructors rather than the types. Type annotations are
  also gone.
*)
Theory flatLang
Ancestors
  ast backend_common
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

(* Copied from the semantics, but with AallocEmpty missing. GlobalVar ops have
 * been added, also TagLenEq and El for pattern match compilation. *)
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
 (* Opderef -- replaced by El, later in this list *)
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
  (* String operations *)
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vsub_unsafe
  | Vlength
  (* Array operations *)
  | Aalloc
  | AallocFixed
  | Asub
  | Alength
  | Aupdate
  (* Unsafe array operations *)
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  | Aw8xor_unsafe
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI mlstring
  (* Allocate the given number of new global variables *)
  | GlobalVarAlloc num
  (* Initialise given global variable *)
  | GlobalVarInit num
  (* Get the value of the given global variable *)
  | GlobalVarLookup num
  (* Evaluate some declarations *)
  | Eval
  (* for pattern match compilation *)
  | TagLenEq num num
  | LenEq num
  | El num
  (* No-op step for a single value *)
  | Id
  (* Thunk *)
  | ThunkOp ast$thunk_op
End

Type ctor_id = ``:num``
(* NONE represents the exception type *)
Type type_id = ``:num option``
Type type_group_id = ``:(num # (ctor_id # num) list) option``

Datatype:
  pat =
  | Pany
  | Pvar varN
  | Plit lit
  | Pcon ((ctor_id # type_group_id) option) (pat list)
  | Pas pat varN
  | Pref pat
End

Definition pat_bindings_def:
  (pat_bindings Pany already_bound = already_bound) ∧
  (pat_bindings (Pvar n) already_bound = n::already_bound) ∧
  (pat_bindings (Plit l) already_bound = already_bound) ∧
  (pat_bindings (Pcon _ ps) already_bound = pats_bindings ps already_bound) ∧
  (pat_bindings (Pas p i) already_bound = pat_bindings p (i::already_bound)) ∧
  (pat_bindings (Pref p) already_bound = pat_bindings p already_bound) ∧
  (pats_bindings [] already_bound = already_bound) ∧
  (pats_bindings (p::ps) already_bound = pats_bindings ps (pat_bindings p already_bound))
End

Datatype:
  exp =
    Raise tra exp
  | Handle tra exp ((pat # exp) list)
  | Lit tra lit
  | Con tra ((ctor_id # type_id) option) (exp list)
  | Var_local tra varN
  | Fun varN varN exp
  | App tra op (exp list)
  | If tra exp exp exp
  | Mat tra exp ((pat # exp) list)
  | Let tra (varN option) exp exp
  | Letrec varN ((varN # varN # exp) list) exp
End

val exp_size_def = definition"exp_size_def";

Theorem exp6_size_APPEND[simp]:
   flatLang$exp6_size (e ++ e2) = exp6_size e + exp6_size e2
Proof
  Induct_on`e`>>simp[exp_size_def]
QED

Theorem exp6_size_REVERSE[simp]:
   flatLang$exp6_size (REVERSE es) = exp6_size es
Proof
  Induct_on`es`>>simp[exp_size_def]
QED

Theorem exp6_size:
  exp6_size xs = LENGTH xs + SUM (MAP exp_size xs)
Proof
  Induct_on `xs` \\ simp [exp_size_def]
QED

Theorem exp1_size:
  exp1_size xs = LENGTH xs + SUM (MAP exp2_size xs)
Proof
  Induct_on `xs` \\ simp [exp_size_def]
QED

Theorem exp3_size:
  exp3_size xs = LENGTH xs + SUM (MAP exp5_size xs)
Proof
  Induct_on `xs` \\ simp [exp_size_def]
QED

Theorem exp_size_MAP:
   (!xs. exp6_size (MAP SND xs) < exp3_size xs + 1) /\
   (!xs. exp6_size (MAP (SND o SND) xs) < exp1_size xs + 1)
Proof
  conj_tac
  >-
   (Induct
    \\ rw [exp_size_def]
    \\ PairCases_on `h` \\ fs [exp_size_def])
  \\ Induct
  \\ rw [exp_size_def]
  \\ PairCases_on `h` \\ fs [exp_size_def]
QED

Theorem exp_size_MEM:
   (!xs x. MEM x xs ==> exp_size x < exp6_size xs) /\
   (!xs x. MEM x xs ==> exp_size (SND (SND x)) < exp1_size xs) /\
   (!xs x. MEM x xs ==> exp_size (SND x) < exp3_size xs)
Proof
  conj_tac
  >-
   (Induct
    \\ rw [exp_size_def]
    \\ res_tac
    \\ decide_tac)
  \\ conj_tac
  \\ Induct
  \\ rw [exp_size_def]
  \\ PairCases_on `h` \\ fs [exp_size_def]
  \\ res_tac
  \\ decide_tac
QED

Datatype:
 dec =
    Dlet exp
End

Definition bool_id_def:
  bool_id = 0n
End

Definition Bool_def:
  Bool t b = Con t (SOME (backend_common$bool_to_tag b, SOME bool_id)) []
End

Definition SmartIf_def:
  SmartIf t e p q =
    case e of
      Con _ (SOME (tag, SOME id)) [] =>
        if id = bool_id then
          if tag = backend_common$true_tag then p
          else if tag = backend_common$false_tag then q
          else If t e p q
        else If t e p q
    | _ => If t e p q
End

Theorem SmartIf_PMATCH:
  !t e p q.
    SmartIf t e p q =
      pmatch e of
        Con _ (SOME (tag, SOME id)) [] =>
          if id = bool_id then
            if tag = backend_common$true_tag then p
            else if tag = backend_common$false_tag then q
            else If t e p q
          else If t e p q
      | _ => If t e p q
Proof
  rpt strip_tac
  \\ CONV_TAC (RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ rw [SmartIf_def]
QED
