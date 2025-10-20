(*
  Using the CakeML translator to produce a verified deep embedding of the
  simple BST implementation.
*)
Theory simple_bstProg
Ancestors
  simple_bst
Libs
  preamble ml_progLib ml_translatorLib


(*
  To translate a HOL function to CakeML, call translate on its definition. For
  example, let us start by translating the singleton function from
  simple_bstTheory.

  The necessary datatypes (('a,'b) btree in this case) will be automatically
  translated first.

  The result is a certificate theorem indicating that the CakeML value
  (singleton_v) that results from running the generated code for declaring the
  CakeML version of the singleton function refines the HOL function singleton.
*)

val res = translate singleton_def;

(*
  The translator maintains state, containing the entire current translated program.
  For each top-level declaration in this program, the translator also defines a
  constant representing the state of the CakeML semantics after this
  As a side effect of calling translate, the program is appended to the state.

  Let us look at the code in the current program.
*)

(* TODO: this is too cumbersome! *)
fun get_current_prog() =
let
  val state = get_ml_prog_state()
  val state_thm =
    state |> ml_progLib.remove_snocs
          |> ml_progLib.clean_state
          |> get_thm
  val current_prog =
    state_thm
    |> concl
    |> strip_comb |> #2
    |> el 3
in current_prog end
(*
  get_current_prog()
*)

(*
  To print in concrete syntax:
  astPP.enable_astPP();
  To remove this pretty-printing:
  astPP.disable_astPP();
*)

val res = translate insert_def;

val res = translate lookup_def;

(*
val res = translate member_def;
*)

(* TODO: use of certificate theorem to show something about the generated code? *)

