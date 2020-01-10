(*
  The abstract syntax of Pancake language
*)

open preamble
     mlstringTheory
     asmTheory (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *)
     (* timeTheory *) ;

val _ = new_theory "extrapanLang";

Type shift = ``:ast$shift``

Type varname = ``:mlstring``

Type funname = ``:mlstring``


val _ = Datatype `
  top = TimeOps `  (* ... define later from Ada.Real_time *)

val _ = Datatype `
  exp = Const ('a word)
      | Var varname
      | Load exp
      | LoadByte exp
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
      | ConstTime time
      | OpTime top (time list) (* time list instead of exp list for simplicity *)
      | GetClock
   (* | VarTime varname *)`


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
`;


Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


(* from Add manual: Time_Unit is an implementation-defined real number *)

val _ = Define `
 time_unit:real = ARB`

(*
  Values of the type Time_Span represent length of real time duration.
  The set of values of this type corresponds one-to-one with an implementation-defined
  range of mathematical integers. *)

Type time_span = ``:num``

(* extra info:
   The Time_Span value corresponding to the integer I represents
   the real-time duration I*Time_Unit *)

(* The Time value I represents the half-open real time interval
   that starts with E+I*Time_Unit and is limited by E+(I+1)*Time_Unit *)

(* half_open_interval a b = {x | a ≤ x ∧ x < b} *)

val _ = Define `
 time_value e i = {x | (e + i * time_unit) <= x /\ x < (e + (i+1) * time_unit)}`


(* Time_First and Time_Last are the smallest and largest values of the Time type, respectively.
   Similarly, Time_Span_First and Time_Span_Last are the smallest and largest values
   of the Time_Span type, respectively *)

val _ = Define `
 time_first:time = ARB`

val _ = Define `
 time_last:time = ARB`

val _ = Define `
 time_span_first:time = ARB`

val _ = Define `
 time_span_last:time = ARB`


(*
  A value of type Seconds_Count represents an elapsed time, measured in seconds, since the epoch. *)

Type sec_count = ``:num``


Overload shift = “backend_common$word_shift”

val _ = export_theory();
