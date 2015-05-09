open HolKernel Parse boolLib bossLib;
open asmTheory wordsTheory wordsLib sptreeTheory;

val _ = new_theory "asm_lang";


(* -- SYNTAX -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)

(* A label refers to either a section name or a local label definition
   within the current section. *)

val () = Datatype `
  lab = Local num | Section num`

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

val () = Datatype `
  asm_with_lab = Jump lab
               | JumpCmp cmp reg ('a reg_imm) lab
               | Call lab
               | Loc reg lab`;

val () = Datatype `
  asm_line = Label num num
           | Asm ('a asm) (word8 list) num
           | LabAsm ('a asm_with_lab) ('a word) (word8 list) num`

(* A section consists a name (num) and a list of assembly lines. *)

val () = Datatype `
  sec = Section num (('a asm_line) list)`

(* A full assmebly program consists of a list of sections. *)

val () = Parse.temp_type_abbrev ("asm_prog", ``:('a sec) list``);


(* -- BASIC FUNCTIONS -- *)

val asm_line_labs_def = Define `
  (asm_line_labs pos [] acc = (acc,pos)) /\
  (asm_line_labs pos ((Label k l)::xs) acc =
     asm_line_labs (pos+l) xs (insert (k+1) (pos+l) acc)) /\
  (asm_line_labs pos ((Asm _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc) /\
  (asm_line_labs pos ((LabAsm _ _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc)`

val sec_labs_def = Define `
  sec_labs pos (Section k lines) =
    asm_line_labs pos lines (insert 0 pos LN)`;

val sec_name_def = Define `
  sec_name (Section k _) = k`;

val all_labels_def = Define `
  (all_labels pos [] = LN) /\
  (all_labels pos (s::rest) =
     let (labs,new_pos) = sec_labs pos s in
     let rest_labs = all_labels new_pos rest in
       insert (sec_name s) labs rest_labs)`

(* TODO:
    - basic assmeble function
    - repeat
       1. compute labels
       2. update code
       3. update length annotations
      until step 3 has no effect.
*)

val _ = export_theory();
