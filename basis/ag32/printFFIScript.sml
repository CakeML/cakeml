open preamble cfHeapsBaseTheory

val _ = new_theory"printFFI"

(* Specification of the FFI for printing on Silver.

   The FFI state is the list of chars printed so far. This is not strictly
   necessary (they could be retrieved from the trace of FFI calls and their
   arguments), but makes for more meaningful CF specifications.
*)

val ffi_print_def = Define`
  ffi_print (str: word8 list) unused ls =
    if LENGTH str < 64 ∧ NULL unused
    then SOME (FFIreturn unused (ls++(MAP (CHR o w2n) str)))
    else NONE`;

val ffi_print_length = Q.store_thm("ffi_print_length",`
  ffi_print (conf:word8 list) (bytes:word8 list) x = SOME (FFIreturn bytes' x')
  ==> LENGTH bytes' = LENGTH bytes`,
  Cases_on `x` \\ rw[ffi_print_def]);

val print_ffi_part_def = Define`
  print_ffi_part = (Str,destStr,[("print",ffi_print)])`;

val _ = export_theory();
