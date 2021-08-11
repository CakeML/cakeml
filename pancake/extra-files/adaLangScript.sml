(*
  The abstract syntax of Ada language
*)

open preamble
     mlstringTheory
     asmTheory (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "adaLang";


(* strong typing  *)
(* compiler does the type check *)
(* Abstraction  *)
(* name equivalence *)
(* subtypes *)


(* documenting Ada types for the time being *)

val _ = Datatype `
  enumlit_type = Ident string      (* defining_identifier *)
               | CharLit  char    (* defining_character_literal  *)
`

val _ = Datatype `
  integer_type = Signed
               | Modular
`

val _ = Datatype `
  disc_type = Enum string       (* types name: defining_identifier *)
                   enumlit_type (* should have atleast on literarl*)
                   (enumlit_type list)
            | Int integer_type
`

val _ = Datatype `
  fixed_type = Decimal
             | Ordinary
`


val _ = Datatype `
  real_type = Float
            | Fixed fixed_type
`

val _ = Datatype `
  scaler_type = Discrete disc_type
              | Real real_type
`



val _ = Datatype `
  elem_type = Scaler scaler_type
            | Access
`

val _ = Datatype `
  comp_type = Array
            | Record
            | Protected
            | Task
`


val _ = Datatype `
  ada_type = Elementary  elem_type
           | Composite comp_type
`
(*

(* from https://en.wikibooks.org/wiki/Ada_Programming/Type_System *)

val _ = Datatype `
  predef_types = Integer
                | Float  (* weak implementation requirement *)
                | Duration (* A fixed point type used for timing. It represents a period of time in seconds *)
                | Character
                | WideCharacter
                | WideWideCharacter
                | String  (* has different varaints *)
                | WideString
                | WideWideString
                | Boolean
                | Address  (* An address in memory*)
                | StorageOffset  (* helps in providing address arithmetic *)
                | StorageElement (* a byte *)
                | StorageArray



`



val _ = Datatype `
  sub_predef_types = Natural (* of Integer *)
                   | Positive (* of Integer *)
                   | StorageCount  (* of StorageOffset, cannot be negative  *)


`

*)

val _ = export_theory();
