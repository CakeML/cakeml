signature bytecode_testerLib =
sig

    include Abbrev

    val run_bytecode   : int -> term -> unit  (* input 1: number of repetitions
                                                 input 2: list of bytecode instrs
                                                 output: printed to the screen *)

end
