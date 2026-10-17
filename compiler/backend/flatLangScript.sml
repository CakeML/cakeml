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

(* Most ops are inherited from ast$op via the Src wrapper.
 * GlobalVar ops, TagLenEq, LenEq, El, and Id are flatLang-specific. *)
Datatype:
 op =
    Src ast$op
  (* Allocate the given number of new global variables *)
  | GlobalVarAlloc num
  (* Initialise given global variable *)
  | GlobalVarInit num
  (* Get the value of the given global variable *)
  | GlobalVarLookup num
  (* for pattern match compilation *)
  | TagLenEq num num
  | LenEq num
  | El num
  (* No-op step for a single value *)
  | Id
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
  (pat_bindings Pany = []) ∧
  (pat_bindings (Pvar n) = [n]) ∧
  (pat_bindings (Plit l) = []) ∧
  (pat_bindings (Pcon _ ps) = pats_bindings ps) ∧
  (pat_bindings (Pas p i) = pat_bindings p ++ [i]) ∧
  (pat_bindings (Pref p) = pat_bindings p) ∧
  (pats_bindings [] = []) ∧
  (pats_bindings (p::ps) = pats_bindings ps ++ pat_bindings p)
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
  (* evaluate the body, then consume one clock tick *)
  | Tick tra exp
End

val exp_size_def = definition"exp_size_def"

Theorem pat_size_eq = #2 (TypeBase.size_of “:flatLang$pat”)

Theorem exp_size_eq = #2 (TypeBase.size_of “:flatLang$exp”)

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
