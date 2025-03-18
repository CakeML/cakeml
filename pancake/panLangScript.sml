(*
  Abstract syntax for Pancake language.
  Pancake is an imperative language with
  instructions for conditionals, While loop,
  memory load and store, functions,
  and foreign function calls.
*)
Theory panLang
Ancestors
  mlstring
  asm (* for binop and cmp *)
  backend_common  (* for overloading the shift operation *)
Libs
  preamble


(* for overloading the shift operation *)

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
  varkind = Local | Global
End

Datatype:
  exp = Const ('a word)
      | Var varkind varname
      | Struct (exp list)
      | Field index exp
      | Load shape exp (* exp: start addr of value with given shape *)
      | Load32 exp
      | LoadByte exp
      | Op binop (exp list)
      | Panop panop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
      | BaseAddr
      | TopAddr
      | BytesInWord
End

Datatype:
  opsize = Op8 | OpW | Op32 | Op16
End

Datatype:
  prog = Skip
       | Dec varname ('a exp) prog
       | Assign varkind varname ('a exp)  (* dest, source *)
       | Store     ('a exp) ('a exp) (* dest, source *)
       | Store32   ('a exp) ('a exp) (* dest, source *)
       | StoreByte ('a exp) ('a exp) (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call (((varkind # varname) option # ((eid # varname # prog) option)) option) funname (('a exp) list)
       | DecCall varname shape funname ('a exp list) prog
       | ExtCall funname ('a exp) ('a exp) ('a exp) ('a exp)
         (* FFI name, conf_ptr, conf_len, array_ptr, array_len *)
       | Raise eid ('a exp)
       | Return ('a exp)
       | ShMemLoad opsize varkind varname ('a exp)
       | ShMemStore opsize ('a exp) ('a exp)
       | Tick
       | Annot mlstring mlstring
End

Datatype:
  fun_decl =
  <| name        : mlstring
   ; export      : bool
   ; params      : (varname # shape) list
   ; body        : 'a prog
  |>
End

Datatype:
  decl = Function ('a fun_decl)
       | Decl shape mlstring ('a exp)
End

Overload TailCall = “Call NONE”
Overload AssignCall = “\s h. Call (SOME (SOME s , h))”
Overload StandAloneCall = “\h. Call (SOME (NONE , h))”

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

Definition size_of_eids_def:
  size_of_eids prog =
  let eids = FLAT (MAP (λp. case p of Decl _ _ _ => [] | Function fi => exp_ids fi.body) prog) in
   LENGTH (nub eids)
End

(*
  for time_to_pancake compiler:

Definition Assigns_def:
  (Assigns [] n = Skip) ∧
  (Assigns (v::vs) n =
    Seq (Assign v n) (Assigns vs n))
End

Definition Decs_def:
  (Decs [] p = p) /\
  (Decs ((v,e)::es) p =
    Dec v e (Decs es p))
End

*)

Definition var_exp_def:
  (var_exp (Const w) = ([]:mlstring list)) ∧
  (var_exp (Var Local v) = [v]) ∧
  (var_exp (Var Global v) = []) ∧
  (var_exp (Struct es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Field i e) = var_exp e) ∧
  (var_exp (Load sh e) = var_exp e) ∧
  (var_exp (Load32 e) = var_exp e) ∧
  (var_exp (LoadByte e) = var_exp e) ∧
  (var_exp (Op bop es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Panop op es) = FLAT (MAP var_exp es)) ∧
  (var_exp (Cmp c e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (var_exp (Shift sh e num) = var_exp e) ∧
  (var_exp BaseAddr = []) ∧
  (var_exp TopAddr = []) ∧
  (var_exp BytesInWord = [])
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition global_var_exp_def:
  (global_var_exp (Const w) = ([]:mlstring list)) ∧
  (global_var_exp (Var Local v) = []) ∧
  (global_var_exp (Var Global v) = [v]) ∧
  (global_var_exp (Struct es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Field i e) = global_var_exp e) ∧
  (global_var_exp (Load sh e) = global_var_exp e) ∧
  (global_var_exp (LoadByte e) = global_var_exp e) ∧
  (global_var_exp (Op bop es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Panop op es) = FLAT (MAP global_var_exp es)) ∧
  (global_var_exp (Cmp c e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_exp (Shift sh e num) = global_var_exp e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition load_op_def:
  load_op Op8 = Load8 ∧
  load_op Op16 = Load16 ∧
  load_op OpW = Load ∧
  load_op Op32 = Load32
End

Definition store_op_def:
  store_op Op8 = Store8 ∧
  store_op Op16 = Store16 ∧
  store_op OpW = Store ∧
  store_op Op32 = Store32
End

Definition is_function_def:
  is_function(Function _) = T ∧
  is_function _ = F
End

Definition functions_def:
  functions [] = [] ∧
  functions(Function fi::fs) =
  (fi.name,fi.params,fi.body)::functions fs ∧
  functions(Decl _ _ _::fs) = functions fs
End

Definition fun_ids_def:
  (fun_ids (Dec _ _ p) = fun_ids p) ∧
  (fun_ids (Seq p q) = fun_ids p ++ fun_ids q) ∧
  (fun_ids (If _ p q) = fun_ids p ++ fun_ids q) ∧
  (fun_ids (While _ p) = fun_ids p) ∧
  (fun_ids (Call (SOME (_ , (SOME (_ ,  _ , ep)))) nm _) = nm::fun_ids ep) ∧
  (fun_ids (Call _ nm _) = [nm]) ∧
  (fun_ids (DecCall _ _ nm _ p) = nm::fun_ids p) ∧
  (fun_ids _ = [])
End

Definition free_var_ids_def:
  (free_var_ids (Dec vn e p) = var_exp e ++ FILTER ($≠ vn) (free_var_ids p)) ∧
  (free_var_ids (Seq p q) = free_var_ids p ++ free_var_ids q) ∧
  (free_var_ids (If g p q) = var_exp g ++ free_var_ids p ++ free_var_ids q) ∧
  (free_var_ids (While g p) = var_exp g ++ free_var_ids p) ∧
  (free_var_ids (Assign vk v e) =
   if vk = Local then
     v::var_exp e
   else
     var_exp e
  ) ∧
  (free_var_ids (Store e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (free_var_ids (Store32 e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (free_var_ids (StoreByte e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (free_var_ids (Raise eid e) = var_exp e) ∧
  (free_var_ids (Return e) = var_exp e) ∧
  (free_var_ids (ExtCall fn e1 e2 e3 e4) = var_exp e1 ++ var_exp e2 ++ var_exp e3 ++ var_exp e4) ∧
  (free_var_ids (ShMemLoad os vk v e) =
   if vk = Local then
     v::var_exp e
   else
     var_exp e) ∧
  (free_var_ids (ShMemStore os e1 e2) = var_exp e1 ++ var_exp e2) ∧
  (free_var_ids (panLang$Call (SOME (NONE , SOME (_ ,  vn , ep))) _ args) =
   vn::free_var_ids ep ++
   FLAT (MAP var_exp args)) ∧
  (free_var_ids (panLang$Call (SOME (SOME(vk,vn) , SOME (_ ,  en , ep))) _ args) =
   (if vk = Local then [vn] else []) ++
   en::free_var_ids ep ++
   FLAT (MAP var_exp args)) ∧
  (free_var_ids (panLang$Call (SOME (SOME(vk,vn) , NONE)) _ args) =
   (if vk = Local then [vn] else []) ++
   FLAT (MAP var_exp args)) ∧
  (free_var_ids (panLang$Call (SOME (NONE , NONE)) _ args) =
   FLAT (MAP var_exp args)) ∧
  (free_var_ids (panLang$Call NONE _ args) = FLAT (MAP var_exp args)) ∧
  (free_var_ids (DecCall vn _ _ args p) = vn::free_var_ids p ++ FLAT (MAP var_exp args)) ∧
  (free_var_ids _ = [])
End
