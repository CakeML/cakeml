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

(* update this in the evening *)
Datatype:
  lab = Lab num
      | AddLabels lab lab
      | AddOffset lab offset
End

Datatype:
  instr = Jump lab
        | CallFFI string
        (* | UpdateOff offset offsetVal *)
End

Datatype:
  line = Label lab
       | Instruction instr
End

Type action_impl = “:line list”


(* instructions for timing control *)

Type clkVar = “:num”
Type clkVal = “:num”

Type fname = “:num”

Datatype:
  prog = SetOffset offset offsetVal
       | SetClock  clkVar clkVal
       | GetTime
       | ResetClock clkVar
       | CallTask fname
End

(* this would be clear once we design time-to-branch compiler *)

Datatype:
  abc = CallFSM fname (* or prog *)
End


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
