signature encodeLib =
sig
  datatype arch = Compare | All | ARMv7 | ARMv8 | x86_64 | MIPS | RISCV
  val encodings : arch list -> Term.term Abbrev.quotation list -> unit
end
