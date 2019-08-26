(*
  The labLang intermediate language is a target-neutral assembly
  language at the bottom end of the compielr backend.
*)
open preamble asmTheory;

val _ = new_theory "labLang";

Type reg = ``:num``

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
               | CallFFI string
               | Install
               | Halt`;

val _ = Datatype`
  asm_or_cbw = Asmi ('a asm) | Cbw reg reg`; (* Either an asm inst/jumpreg or code-buffer-write *)

val () = Datatype `
  line = Label num num num (* section number, label number, length *)
       | Asm ('a asm_or_cbw) (word8 list) num (* instruction, encoded instruction, length *)
       | LabAsm ('a asm_with_lab) ('a word) (word8 list) num`
                                  (* position, encoded instruction, length *)

(* A section consists a name (num) and a list of assembly lines. *)

val () = Datatype `
  sec = Section num (('a line) list)`

val Section_num_def = Define`Section_num (Section k _) = k`;
val Section_lines_def = Define`Section_lines (Section _ lines) = lines`;
val _ = export_rewrites["Section_num_def","Section_lines_def"];

(* A full assembly program consists of a list of sections. *)

Type prog = ``:('a sec) list``

val _ = export_theory();
