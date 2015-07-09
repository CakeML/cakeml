open preamble asmTheory;

val _ = new_theory "labLang";

val () = Parse.temp_type_abbrev ("reg", ``:num``)

(* A label refers to either a section name or a local label definition
   within the current section. *)

val () = Datatype `
  lab = Lab num num`

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

val () = Datatype `
  asm_with_lab = Jump lab
               | JumpCmp cmp reg ('a reg_imm) lab
               | Call lab
               | LocValue reg lab
               (* following have no label, but have similar semantics *)
               | CallFFI num
               | ClearCache
               | Halt`;

val () = Datatype `
  line = Label num num num
       | Asm ('a asm) (word8 list) num
       | LabAsm ('a asm_with_lab) ('a word) (word8 list) num`

(* A section consists a name (num) and a list of assembly lines. *)

val () = Datatype `
  sec = Section num (('a line) list)`

(* A full assembly program consists of a list of sections. *)

(* TODO: this needs to be copied elsewhere until HOL issue #168 is closed *)
val () = Parse.temp_type_abbrev ("prog", ``:('a sec) list``);

val _ = export_theory();
