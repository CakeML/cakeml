(*
  Abstract syntax for Pancake language.
  Pancake is an imperative language with
  instructions for conditionals, While loop,
  memory load and store, functions,
  and foreign function calls.
*)

open preamble
     mlstringTheory
     asmTheory             (* for binop and cmp *)
     backend_commonTheory; (* for overloading the shift operation *)

val _ = new_theory "panLang";

Type shift = ``:ast$shift``

Type sname = ``:mlstring``

Type varname = ``:mlstring``

Type funname = ``:mlstring``

Type eid     = ``:mlstring``

Type decname = ``:mlstring``

Type index = ``:num``

Datatype:
  shape = One
        | Comb (shape list)
End

Datatype:
  panop = (* Div | *)Mul (* | Mod*)
End

Datatype:
  exp = Const ('a word)
      | Var varname
      | Label funname
   (* | GetAddr decname *)
      | Struct (exp list)
      | Field index exp
      | Load shape exp (* exp: start addr of value with given shape *)
      | LoadByte exp
      | Op binop (exp list)
      | Panop panop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
      | BaseAddr
      | BytesInWord
End

Datatype:
  opsize = Op8 | OpW | Op32
End

Datatype:
  prog = Skip
       | Dec varname ('a exp) prog
       | Assign    varname ('a exp)  (* dest, source *)
       | Store     ('a exp) ('a exp) (* dest, source *)
       | StoreByte ('a exp) ('a exp) (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ((varname option # ((eid # varname # prog) option)) option) ('a exp) (('a exp) list)
       | DecCall varname shape ('a exp) ('a exp list) prog
       | ExtCall funname ('a exp) ('a exp) ('a exp) ('a exp)
         (* FFI name, conf_ptr, conf_len, array_ptr, array_len *)
       | Raise eid ('a exp)
       | Return ('a exp)
       | ShMemLoad opsize varname ('a exp)
       | ShMemStore opsize ('a exp) ('a exp)
       | Tick
       | Annot mlstring mlstring
End

Datatype:
  decl = Function mlstring ((mlstring # shape) list) ('a prog)
       | Global   mlstring ('a exp)
End
(*
Datatype:
  handler = Handle eid varname ('a prog)
End

Datatype:
  ret = Tail | Ret varname ('a handler option)
End
*)

Overload TailCall = “Call NONE”
Overload AssignCall = “\s h. Call (SOME (SOME s , h))”
Overload StandAloneCall = “\h. Call (SOME (NONE , h))”

(*
Datatype:
  decl = Decl decname string
       | Func funname (shape option) shape ('a prog)
End
*)

Theorem MEM_IMP_shape_size:
   !shapes a. MEM a shapes ==> (shape_size a < 1 + shape1_size shapes)
Proof
  Induct >> fs [] >>
  rpt strip_tac >> rw [fetch "-" "shape_size_def"] >>
  res_tac >> decide_tac
QED


Definition size_of_shape_def:
  size_of_shape One = 1 /\
  size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)
Termination
  wf_rel_tac `measure shape_size` >>
  fs [MEM_IMP_shape_size]
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED


Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End

Definition with_shape_def:
  (with_shape [] _ = []) ∧
  (with_shape (sh::shs) e =
     TAKE (size_of_shape sh) e :: with_shape shs (DROP (size_of_shape sh) e))
End

Definition exp_ids_def:
  (exp_ids Skip = ([]:mlstring list)) ∧
  (exp_ids (Raise e _) = [e]) ∧
  (exp_ids (Dec _ _ p) = exp_ids p) ∧
  (exp_ids (Seq p q) = exp_ids p ++ exp_ids q) ∧
  (exp_ids (If _ p q) = exp_ids p ++ exp_ids q) ∧
  (exp_ids (While _ p) = exp_ids p) ∧
  (exp_ids (Call (SOME (_ , (SOME (e ,  _ , ep)))) _ _) = e::exp_ids ep) ∧
  (exp_ids (DecCall _ _ _ _ p) = exp_ids p) ∧
  (exp_ids _ = [])
End

(* defining here for insead of in pan_to_crep for pan_simpProof*)
Definition remove_dup:
  (remove_dup [] = []) ∧
  (remove_dup (x::xs) =
   if MEM x xs then remove_dup xs
   else x::remove_dup xs)
End

Definition size_of_eids_def:
  size_of_eids prog =
  let eids = FLAT (MAP (exp_ids o SND o SND) prog) in
   LENGTH (remove_dup eids)
End

(*
  for time_to_pancake compiler:
*)

(* optimise this function *)
Definition assigns_def:
  (assigns [] n = Skip) ∧
  (assigns (v::vs) n =
    Seq (Assign v n) (assigns vs n))
End


Definition decs_def:
  (decs [] p = p) /\
  (decs ((v,e)::es) p =
    Dec v e (decs es p))
End


Definition var_exp_def:
  (var_exp (Const w) = ([]:mlstring list)) ∧
  (var_exp (Var v) = [v]) ∧
  (var_exp (Label f) = []) ∧
  (var_exp (Struct es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Field i e) = var_exp e) ∧
  (var_exp (Load sh e) = var_exp e) ∧
  (var_exp (LoadByte e) = var_exp e) ∧
  (var_exp (Op bop es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Panop op es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Cmp c e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (var_exp (Shift sh e num) = var_exp e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End


Definition destruct_def:
  (destruct (Struct es) = es) /\
  (destruct _ = [])
End

Definition load_op_def:
  load_op Op8 = Load8 ∧
  load_op OpW = Load ∧
  load_op Op32 = Load32
End

Definition store_op_def:
  store_op Op8 = Store8 ∧
  store_op OpW = Store ∧
  store_op Op32 = Store32
End

val _ = export_theory();
