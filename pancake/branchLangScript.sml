(*
  Abstract syntax for branchLang
*)

open preamble
     stringTheory

val _ = new_theory "branchLang";

(* merge it later with labLang *)

(*
  a local label definition for the time being,
  add label for a section later
*)

Datatype:
  lab = Lab num
End

Datatype:
  instr = Jump lab
        | AddOffset lab offset
          (* could also use JumpCmp or add ops explicitly *)
        | CallFFI string
End

Datatype:
  line = Label lab
       | Instruction instr
End

Type prog = line list

(*
 ... validate x                    /* transform x to 0 (invalid) or 1,2,3, according to value..)    */
       y = x * 4;                  /* multiply by branch instruction length (e.g. 4 )               */
       goto next + y;              /* branch into 'table' of branch instructions                    */
 /* start of branch table */
 next: goto codebad;               /* x= 0  (invalid)                                               */
       goto codeone;               /* x= 1                                                          */
       goto codetwo;               /* x= 2                                                          */
 ... rest of branch table
 codebad:                          /* deal with invalid input                                       */

*)


(*
     = [(0%nat,
        [Tm (Output 1%nat)
           [CndLe (EClock (CVar "x")) (ELit 1);
           CndLe (ELit 1) (EClock (CVar "x"));
           CndLe (EClock (CVar "x")) (ELit 2)] [] 1%nat
	   [(2, CVar "x")]]);
       (1%nat,
       [Tm (Output 0%nat)
          [CndLe (EClock (CVar "x")) (ELit 2);
          CndLe (ELit 2) (EClock (CVar "x"));
	  CndLe (ELit 0) (ELit 1)]
          [CVar "x"] 0%nat [(1, CVar "x")]])]
     : program

*)

val _ = export_theory();
