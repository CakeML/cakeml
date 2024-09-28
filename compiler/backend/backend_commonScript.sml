(*
  Definitions that are common for many parts of the compiler backend.
*)

open preamble

val _ = new_theory "backend_common";

val _ = set_grammar_ancestry ["arithmetic", "integer", "words"];

(* Small general definition *)
Definition small_enough_int_def:
  small_enough_int i <=> -268435457 <= i /\ i <= 268435457:int
End

val _ = numLib.temp_prefer_num();

(* these must match what the prim_types_program generates *)

val _ = Define `bind_tag      = 0`;
val _ = Define `chr_tag       = 1`;
val _ = Define `div_tag       = 2`;
val _ = Define `subscript_tag = 3`;

val _ = Define `false_tag = 0`;
val _ = Define `true_tag  = 1`;

val _ = Define `nil_tag   = 0`;
val _ = Define `cons_tag  = 0`;

val _ = Define `none_tag  = 0`;
val _ = Define `some_tag  = 0`;

val _ = Define `tuple_tag = 0`;

val _ = Define`closure_tag = 30:num`
val _ = Define`partial_app_tag = 31:num`
val _ = Define`clos_tag_shift tag = if tag < 30 then tag:num else tag+2`

(* Trace of an expression through the compiler, for exploring transformations *)
val _ = Datatype`
  tra =
    | SourceLoc num (* start-row *) num (* start-col *) num (* end-row *) num (* end-col *)
    | Cons tra num
    | Union tra tra
    | None (* Dead trace, do not make traces at all *)`

(* The code below replaces "Cons" in hol output with the chosen symbol *)
val _ = set_fixity "▷" (Infixl 480);
Overload "▷" = ``backend_common$Cons``

(* An "orphan" expression is one that originates directly from a declaration.
* This happens in source_to_mod, and in con_to_dec. It is an orphan because
* declarations don't come annotated with their source program locations right
* now point (but they might in the future).
* This is a trace that can be used as a basis for traces for orphan expressions.
* It's structure guarantees it will not conflict with any trace originating from
* source, since the always start with four Cons, indicating source position. *)
Definition orphan_trace_def:
  orphan_trace = SourceLoc 2 2 1 1
End

(* Create new Cons trace, unless original trace is `None`, indicating traces are
* turned off. *)
Definition mk_cons_def:
  mk_cons tr n =
    case tr of
       | None => None
       | _    => Cons tr n
End

val _ = set_fixity "§" (Infixl 480);
Overload "§" = ``backend_common$mk_cons``

(* Create new Cons trace, unless any of the original traces are `None`,
* indicating traces are turned off. *)
Definition mk_union_def:
  mk_union tr1 tr2 =
    case tr1 of
       | None => None
       | _    => case tr2 of
                  | None  => None
                  | _     => Union tr1 tr2
End

Definition bool_to_tag_def:
  bool_to_tag b = if b then true_tag else false_tag
End

Definition stack_num_stubs_def:
  stack_num_stubs = 5n
End

Definition word_num_stubs_def:
  word_num_stubs = stack_num_stubs + 1 (* raise *) + 1 (* store consts *)
End

Definition data_num_stubs_def:
  data_num_stubs = word_num_stubs + (* general: *) 30 + (* bignum: *) 23
End

Definition bvl_num_stubs_def:
  bvl_num_stubs = data_num_stubs + 8 + (* dummy to make it a multiple of 3 *) 1
End

Definition bvl_to_bvi_namespaces_def:
  bvl_to_bvi_namespaces = 3n
End

Theorem data_num_stubs_EVEN:
  EVEN data_num_stubs
Proof
  EVAL_TAC
QED

Theorem bvl_num_stub_MOD:
  bvl_num_stubs MOD bvl_to_bvi_namespaces = 0
Proof
  EVAL_TAC
QED

(* shift values, per dimindex(:α) *)
Definition word_shift_def:
  word_shift (:'a) =
    (* this could be defined as LOG 2 (dimindex(:'a)) - 3, but I want
       to be sure that LOG doesn't unnecessarily end up in the
       generated CakeML code *)
    if dimindex (:'a) = 32 then 2 else 3:num
End

val _ = export_theory();
