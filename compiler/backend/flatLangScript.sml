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

open preamble astTheory backend_commonTheory

val _ = new_theory "flatLang";

val _ = set_grammar_ancestry ["ast", "backend_common"];

(* Copied from the semantics, but with AallocEmpty missing. GlobalVar ops have
 * been added, also TagLenEq and El for pattern match compilation. *)
val _ = Datatype `
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
  | Asub
  | Alength
  | Aupdate
  (* Unsafe array operations *)
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
  | El num`;

Type ctor_id = ``:num``
(* NONE represents the exception type *)
Type type_id = ``:num option``

val _ = Datatype `
  pat =
  | Pany
  | Pvar varN
  | Plit lit
  | Pcon ((ctor_id # type_id) option) (pat list)
  | Pref pat`;

Definition pat_bindings_def:
  (pat_bindings Pany already_bound = already_bound) ∧
  (pat_bindings (Pvar n) already_bound = n::already_bound) ∧
  (pat_bindings (Plit l) already_bound = already_bound) ∧
  (pat_bindings (Pcon _ ps) already_bound = pats_bindings ps already_bound) ∧
  (pat_bindings (Pref p) already_bound = pat_bindings p already_bound) ∧
  (pats_bindings [] already_bound = already_bound) ∧
  (pats_bindings (p::ps) already_bound = pats_bindings ps (pat_bindings p already_bound))
End

val _ = Datatype`
  exp =
    Raise tra exp
  | Handle tra exp ((pat # exp) list)
  | Lit tra lit
  | Con tra ((ctor_id # type_id) option) (exp list)
  | Var_local tra varN
  | Fun tra varN exp
  | App tra op (exp list)
  | If tra exp exp exp
  | Mat tra exp ((pat # exp) list)
  | Let tra (varN option) exp exp
  | Letrec tra ((varN # varN # exp) list) exp`;

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

val _ = Datatype`
 dec =
    Dlet exp
  (* The first number is the identity for the type. The sptree maps arities to
   * how many constructors have that arity *)
  | Dtype num (num spt)
  (* The first number is the identity of the exception. The second number is the
   * constructor's arity *)
  | Dexn num num`;

val bool_id_def = Define `
  bool_id = 0n`;

val Bool_def = Define`
  Bool t b = Con t (SOME (backend_common$bool_to_tag b, SOME bool_id)) []`;

val _ = export_theory ();
