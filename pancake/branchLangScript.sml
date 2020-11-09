(*
  Abstract syntax for branchLang:
  an assembly-like language for
  implementing brach tables
*)

open preamble
     stringTheory

val _ = new_theory "branchLang";

Type offset = “:num”
Type offsetVal = “:num”

Datatype:
  lab = Lab num
      | AddLabels lab lab
      | AddOffset lab offset
End

Datatype:
  instr = Jump lab
        | CallFFI string
        | UpdateOff offset offsetVal
End

Datatype:
  line = Label lab
       | Instruction instr
End

Type prog = “:line list”


(*
       y = x * 4;                  /* multiply by branch instruction length (e.g. 4 )               */
       goto next + y;              /* branch into 'table' of branch instructions                    */
 /* start of branch table */
 next: goto codebad;               /* x= 0  (invalid)                                               */
       goto codeone;               /* x= 1                                                          */
       goto codetwo;               /* x= 2                                                          */
 ... rest of branch table
 codebad:                          /* deal with invalid input                                       */
*)


val _ = export_theory();
