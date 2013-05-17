open repl_computeLib
val _ = new_theory"repl_funExamples"

fun run_print_save name input = let
  val _ = print"\n"
  val thm = time EVAL ``repl_fun ^input``
  val _ = print(thm_to_string thm)
  val _ = print"\n"
in save_thm(name,thm) end

val input = ``"val x = true; val y = 2;"``
val _ = run_print_save "ex1" input

val input = ``"fun f x = x + 3; f 2;"``
val _ = run_print_save "ex2" input

val input = ``"datatype foo = C of int | D of bool; fun f x = case x of (C i) => i+1 | D _ => 0; f (C (3));"``
val _ = run_print_save "ex3" input

val input = ``"fun f n = if n = 0 then 1 else n * f (n-1); f 0;"``
val _ = run_print_save "ex4" input

(* intermediate steps:
  val s = ``initial_repl_fun_state``
  val bs = ``initial_bc_state``

  val (tokens,rest_of_input) = time EVAL ``lex_until_toplevel_semicolon ^input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair

    val ast_top = time EVAL ``mmlParse$parse_top ^tokens`` |> concl |> rhs |> rand

    val es = EVAL ``^s.relaborator_state`` |> concl |> rhs
    val top = time EVAL ``elaborate_top ^es ^ast_top`` |> concl |> rhs |> rand

    val is = EVAL ``^s.rinferencer_state`` |> concl |> rhs
    val res = time EVAL ``infertype_top ^is ^top``

  val (code,new_s) = time EVAL ``parse_elaborate_infertype_compile ^tokens ^s`` |> concl |> rhs |> rand |> pairSyntax.dest_pair

  val bs = time EVAL ``install_code ^code ^bs`` |> concl |> rhs

  (*
    val bc_evaln_def = Define`
      (bc_evaln 0 bs = SOME bs) ∧
      (bc_evaln (SUC n) bs = OPTION_BIND (bc_eval1 bs) (bc_evaln n))`
    val bs = time EVAL ``bc_evaln 50 ^bs`` |> concl |> rhs |> rand
  *)

  val new_bs = time EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

  val (new_bs,res) = time EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs |> pairSyntax.dest_pair

  val input = rest_of_input
  val s = new_s
  val bs = new_bs
*)

val _ = export_theory()
