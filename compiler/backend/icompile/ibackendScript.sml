(*
  Defines a new incremental backend which is
  meant to be syntactically equal to backend but allows
  compiling program in a part-by-part manner
*)

open preamble
     backendTheory

val _ = new_theory"ibackend";

(*
  High-level idea:

  We'll define incremental compilation in three steps:

  1) init_icompile:

    This should initialize incremental compilation by running
    the CakeML compiler to insert all of its initial stubs.

  2) icompile:

    This should run incremental compilation on a chunk of
    input source program.

  3) finalize_icompile:

    This should "finalize" compilation by inserting the main
    entry point of the whole program.

  Initially, we'll attempt to syntactically simulate to_lab
*)

(* TODO: fill the "ARBs" in, the types might be wrong *)
Definition init_icompile_def:
  init_icompile (c: 'a config) =
    ARB:
      (inc_config #
       'a word list #
       'a sec list)
End

(* incrementally compile a chunk of source program *)
Definition icompile_def:
  icompile (asm_conf: 'a asm_config)
    (c: inc_config) (prog : ast$dec list) =
    ARB:
      (inc_config #
       'a word list #
       'a sec list)
End

(* end icompilation, ready for assembly *)
Definition end_icompile_def:
  end_icompile (asm_conf: 'a asm_config)
    (c: inc_config) =
    ARB:
      (inc_config #
       'a word list #
       'a sec list)
End

(* Virtual fold of icompile over a list of source programs
    and accumulate its output.
   In reality, we run this as separate compile steps *)
Definition fold_icompile_def:
  fold_icompile (asm_conf: 'a asm_config)
    (c: inc_config) (progs : (ast$dec list) list) =
    ARB:
      (inc_config #
       'a word list #
       'a sec list)
End

(* final theorem should give us a syntactic equality

  TODO: not sure what to do with "names" output of to_lab *)
Theorem icompile_eq:
  init_icompile (c:'a config) = (ic, bm, ip) ∧
  fold_icompile (asm_c:'a asm_config) ic progs = (ic', bm', ip') ∧
  end_icompile asm_c ic' = (ic'', bm'', ip'') ⇒
  to_lab c (FLAT prog) = (
    bm ++ bm' ++ bm'',
    inc_config_to_config asm_c ic'',
    ip ++ ip' ++ ip'',
    ARB
  )
Proof
  cheat
QED

val _ = export_theory();
