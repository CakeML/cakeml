signature basis_ffiLib = sig

  include Abbrev

  (* arguments to prove_sem_thm:
      - name of main function
      - name to use for code definition
      - whole_prog_spec thm              *)
  val prove_sem_thm : string -> string -> thm -> thm

end
