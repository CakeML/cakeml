(*
  The labLang intermediate language is a target-neutral assembly
  language at the bottom end of the compielr backend.
*)
Theory labLang
Ancestors
  asm
Libs
  preamble

Type reg = ``:num``

(* A label refers to either a section name or a local label definition
   within the current section. *)

Datatype:
  lab = Lab num num
End

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

Datatype:
  asm_with_lab = Jump lab
               | JumpCmp cmp reg ('a reg_imm) lab
               | Call lab
               | LocValue reg lab
               (* following have no label, but have similar semantics *)
               | CallFFI mlstring
               | Install
               | Halt
End

Datatype:
  asm_or_cbw = Asmi ('a asm) | Cbw reg reg | ShareMem memop reg ('a addr)
End
 (* Either an asm inst/jumpreg or code-buffer-write *)

Datatype:
  line = Label num num num (* section number, label number, length *)
       | Asm ('a asm_or_cbw) (word8 list) num (* instruction, encoded instruction, length *)
       | LabAsm ('a asm_with_lab) ('a word) (word8 list) num
End
                                  (* position, encoded instruction, length *)

(* A section consists a name (num) and a list of assembly lines. *)

Datatype:
  sec = Section num (('a line) list)
End

Definition Section_num_def[simp]:
  Section_num (Section k _) = k
End
Definition Section_lines_def[simp]:
  Section_lines (Section _ lines) = lines
End

(* A full assembly program consists of a list of sections. *)

Type prog = ``:('a sec) list``
