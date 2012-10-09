open test_compilerLib bytecode_testerLib benchmarkTheory ml_translatorLib listSyntax bytecode_x64ML

val _ = translation_extends "benchmark"

val decls = rhs(concl(benchmark_decls))
fun get_tm tm = rand(rator(concl(hol2deep tm)))

val init_s = repl_state_cs_fupd
  (compiler_state_next_label_fupd (fn _ => numML.fromInt 0) o
    (compiler_state_inst_length_fupd (fn _ => bc_length_x64)))
  init_repl_state

exception M0 of bc_inst
exception M1 of bc_stack_op

fun int_to_term i = intSyntax.term_of_int(Arbint.fromInt(valOf(intML.toInt i)))
fun num_to_term n = numSyntax.term_of_int(valOf(numML.toInt n))
val stack_op_to_term =  let
fun f (PushInt i) = ``PushInt ^(int_to_term i)``
  | f (Load n) = ``Load ^(num_to_term n)``
  | f Sub = ``Sub``
  | f Add = ``Add``
  | f Less = ``Less``
  | f Mult = ``Mult``
  | f Pop = ``Pop``
  | f (Pops n) = ``Pops ^(num_to_term n)``
  | f (El n) = ``El ^(num_to_term n)``
  | f (Store n) = ``Store ^(num_to_term n)``
  | f (Cons (n1,n2)) = ``Cons ^(num_to_term n1) ^(num_to_term n2)``
  | f (Shift (n1,n2)) = ``Shift ^(num_to_term n1) ^(num_to_term n2)``
  | f x = raise M1 x
in f end
val bc_inst_to_term = let
fun f Ref = ``Ref``
  | f (Stack sop) = ``Stack ^(stack_op_to_term sop)``
  | f (Call n) = ``Call ^(num_to_term n)``
  | f (JumpNil n) = ``JumpNil ^(num_to_term n)``
  | f (Jump n) = ``Jump ^(num_to_term n)``
  | f CallPtr = ``CallPtr``
  | f Return = ``Return``
  | f Update = ``Update``
  | f x = raise M0 x
in f end
fun code_to_term c = mk_list(List.map bc_inst_to_term c,``:bc_inst``)

val ([fib_dec,fact_dec],dec_ty) = dest_list decls
val fib_tm = get_tm ``fib 40``
val fact_tm = get_tm ``fact 5000``
val fib_code = fdi init_s fib_tm [fib_dec]
val fib_code_tm = code_to_term fib_code
val fact_code = fdi init_s fact_tm [fact_dec]
val fact_code_tm = code_to_term fact_code
val res = run_bytecode 1 fact_code_tm
val res = run_bytecode 1 fib_code_tm

(*
fibp 40;
val it = 165580141: int
> Profile.results();
val it =
   [("fib", {n = 1, gc = 0.000, sys = 0.003, usr = 4.700, real = 4.755})]:
   (string * call_info) list
>
ramana@lois >iler/emit % hol

Vim input /tmp/vimhol0
date '+#define NOW "%Y-%m-%d %H:%M:%S"' > wrapper.h
gcc -O1 wrapper.c asm_exec.s -o bytecode_tester
/bin/rm -f wrapper.h
Bytecode tester (built 2012-04-16 16:51:44)
Starting 1 runs ...

  Resulting stack:
    stack[0] = 165580141
    stack[1] = 70227707955216

  Heap:  5 bytes used
  Stack: 2 items left on stack
  Time:  8.700 seconds for 1 runs

factorial:
Vim input /tmp/vimhol0
date '+#define NOW "%Y-%m-%d %H:%M:%S"' > wrapper.h
gcc -O1 wrapper.c asm_exec.s -o bytecode_tester
/bin/rm -f wrapper.h
Bytecode tester (built 2012-04-16 16:59:05)
Starting 1 runs ...

  Resulting stack:
    stack[0] = 0
    stack[1] = 70114038050832

  Heap:  5 bytes used
  Stack: 2 items left on stack
  Time:  0.000 seconds for 1 runs
*)
