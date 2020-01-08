(*
  The abstract syntax of Pancake language
*)

open preamble
     mlstringTheory
     asmTheory (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type counter = ``:int``

Type imm = ``:int``

Type taskname = ``:mlstring``

(* parameters passed to task objects at their creation time *)
Type disc_t = ``:varname # 'a word option``

(*
val _ = Datatype `
  task_discrim = TaskDisc (('a disc_t) list)`
*)

val _ = Datatype `
  task_items = EntryDecl (funname -> (varname list))
             | AspectClause  (* not sure right now *)
`


val _ = Datatype `
  exp = Const ('a word)
      | Var varname
      | Load exp
      | LoadByte exp
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num`

val _ = Datatype `
  ret = Tail
      | Ret varname
      | Handle varname varname prog; (* ret var, excp var *)

  prog = Skip
       | Assign    varname ('a exp)
       | Store     ('a exp) varname
       | StoreByte ('a exp) varname
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall varname funname (('a exp) list)
       | Raise ('a exp)
       | Return ('a exp)
       | Tick
       | TaskSpec taskname (('a disc_t) list) (task_items list)
       | TaskBody taskname (* shoud have a declarative part *) prog
  (* instructions for timed automata *)
       | Start
    (* | Start counter gaurd imm *)
       | Stop
`;




(* information_corner:

  In Ada, The full declaration of a task type consists of its specification and its body;

  the specification contains:

   1. The type name

   2. A discriminant part
      this defines the discrete or access parameters that can be passed
      to instances of the task type at their creation time

   3. A list of interfaces
      this defines the interfaces that are supported (implemented) by the task

   4. A visible part
      this defines the task type’s entries and representation (aspect) clauses
      which are visible to the user of the task type; it also includes the discriminant part

  5.  A private part
      this defines the task type’s entries and representation (aspect) clauses, which are invisible to
      the user of the task type


task_type_declaration ::=
 task type defining_identifier [known_discriminant_part]
   [is  [new  interface_list with] task_definition];

task_definition ::=
    {task_item}
[ private
    {task_item ]
end [task_identifier];

task_item ::= entry_declaration | aspect_clause
The task body is declared as follows:


task_body ::=
 task body defining_identifier is
   declarative_part
 begin
   handled_sequence_of_statements
 end [task_identifier];

Examples:

task type Controller;
-- this task type has no entries; no other task can
-- communicate directly with tasks created from this type

task type Agent(Param: Integer);
-- this task type has no entries but task objects can be
-- passed an integer parameter at their creation time

task type Garage_Attendant(Pump : Pump_Number := 1) is
  -- objects of this task type will allow communication
  -- via two entries;
  -- the number of the pump the attendant is to serve
  -- is passed at task creation time; if no value
  -- is passed, a default of 1 will be used
  entry Serve_Leaded(G : Gallons);
  entry Serve_Unleaded(G : Gallons);
end Garage_Attendant;

task type Cashier is
  -- this task type has a single entry with two 'in'
  -- parameters and one 'out' parameter
  entry Pay(Owed : Money; Paid : Money; Change : out Money);
end Cashier;

task type Telephone_Operator is
  entry Directory_Enquiry(Person : in Name;
      Addr : in Address; Num : out Number);
  end Telephone_Operator;

task type Colour_Printer is new Printer_Interface with
  entry Print(File_Name : String);
end Colour_Printer;
*)


Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Overload shift = “backend_common$word_shift”

val _ = export_theory();
