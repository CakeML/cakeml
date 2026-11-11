(*
  Abstract syntax of Crepe language
  Crepe: instructions are similar to that of
  Pancake, but we flatten locals from
  struct-layout to word-layout
*)
Theory crepLang
Ancestors
  mlstring
  asm (* for binop and cmp *)
  backend_common (* for overloading the shift operation *)
  panLang (* for primop *)
Libs
  preamble


Type shift = ``:ast$shift``

Type varname = ``:num``

Type funname = ``:mlstring``

Datatype:
  crepop = (* Div | *)Mul (*| Mod*)
End

Datatype:
  exp = Const int
      | Var varname
      | Load exp
      | Load32 exp
      | LoadByte exp
      | LoadGlob  (5 word)
      | Op binop (exp list)
      | Crepop crepop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp exp
      | BaseAddr
      | TopAddr
End

Datatype:
  prog = Skip
       | Dec varname exp prog
       | Assign    varname  exp   (* dest, source *)
       | Primitive (varname list) panLang$primop (varname list)
         (* Since pan_to_crep invents variable names already, we use variables
            on the RHS (instead of expressions) to piggy-back off of that. *)
       | Store     exp exp   (* dest, source *)
       | Store32 exp exp   (* dest, source *)
       | StoreByte exp exp   (* dest, source *)
       | StoreGlob (5 word) exp   (* dest, source *)
       | Seq prog prog
       | If    exp prog prog
       | While exp prog
       | Break num
       | Continue num
       | Call (((varname list) # ((int # prog) option)) option)
              funname (exp list)
       | ExtCall funname varname varname varname varname
       | Raise int
       | Return (exp list)
       | ShMem memop varname exp
       | Tick;
End

(* NONE is Tail *)
(* SOME (((varname option) # prog # ((int # prog) option))) is Ret *)
(* (int # prog) is handler *)

(* we can make return varaiable an option, but then might not be able to
   compile to loopLang *)

Definition load_shape_def:
  (load_shape aw a 0 e = []) ∧
  (load_shape aw a (SUC i) e =
     if a = 0 then (Load e) :: load_shape aw (a + &(arch_bytes aw)) i e
     else (Load (Op Add [e; Const a])) :: load_shape aw (a + &(arch_bytes aw)) i e)
End

Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End


Definition stores_def:
  (stores aw ad [] a = []) /\
  (stores aw ad (e::es) a =
     if a = 0 then Store ad e :: stores aw ad es (a + &(arch_bytes aw))
     else Store (Op Add [ad; Const a]) e :: stores aw ad es (a + &(arch_bytes aw)))
End

Definition nested_decs_def:
  (nested_decs [] [] p = p) /\
  (nested_decs (n::ns) (e::es) p = Dec n e (nested_decs ns es p)) /\
  (nested_decs [] _ p = Skip) /\
  (nested_decs _ [] p = Skip)
End

Definition store_globals_def:
  (store_globals ad [] = []) ∧
  (store_globals ad (e::es) =
   StoreGlob ad e :: store_globals (ad+1w) es)
End


Definition load_globals_def:
  (load_globals _ 0 = []) ∧
  (load_globals ad (SUC n) = (LoadGlob ad) :: load_globals (ad+1w) n)
End


Definition assign_ret_def:
  assign_ret ns =
    nested_seq (MAP2 Assign ns (load_globals 0w (LENGTH ns)))
End


Definition var_cexp_def:
  (var_cexp (Const w) = ([]:num list)) ∧
  (var_cexp (Var v) = [v]) ∧
  (var_cexp (Load e) = var_cexp e) ∧
  (var_cexp (Load32 e) = var_cexp e) ∧
  (var_cexp (LoadByte e) = var_cexp e) ∧
  (var_cexp (LoadGlob a) = []) ∧
  (var_cexp (Op bop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Crepop cop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Cmp c e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp (Shift sh e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp BaseAddr = []) ∧
  (var_cexp TopAddrl = [])
Termination
  wf_rel_tac `measure (\e. exp_size e)`
End

Definition assigned_free_vars_def:
  (assigned_free_vars Skip = ([]:num list)) ∧
  (assigned_free_vars (Dec n e p) = (FILTER ($≠ n) $ assigned_free_vars p)) ∧
  (assigned_free_vars (Assign n e) = [n]) ∧
  (assigned_free_vars (Primitive lhss pop rhss) = lhss) ∧
  (assigned_free_vars (Seq p p') = assigned_free_vars p ++ assigned_free_vars p') ∧
  (assigned_free_vars (If e p p') = assigned_free_vars p ++ assigned_free_vars p') ∧
  (assigned_free_vars (While e p) = assigned_free_vars p) ∧
  (assigned_free_vars (Call (SOME (rts, (SOME (_, p)))) e es) =
     rts ++ assigned_free_vars p) ∧
  (assigned_free_vars (Call (SOME (rts, NONE)) e es) = rts) ∧
  (assigned_free_vars (ShMem op r ad) = [r]) ∧
  (assigned_free_vars _ = [])
End

Definition assigned_vars_def:
  (assigned_vars Skip = ([]:num list)) ∧
  (assigned_vars (Dec n e p) = (n::assigned_vars p)) ∧
  (assigned_vars (Assign n e) = [n]) ∧
  (assigned_vars (Primitive lhss pop rhss) = lhss) ∧
  (assigned_vars (Seq p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (If e p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (While e p) = assigned_vars p) ∧
  (assigned_vars (Call (SOME (rts, (SOME (_, p)))) e es) =
     rts ++  assigned_vars p) ∧
  (assigned_vars (Call (SOME (rts, NONE)) e es) = rts) ∧
  (assigned_vars (ShMem op r ad) = [r]) ∧
  (assigned_vars _ = [])
End

(*
Definition declared_vars_def:
  (declared_vars Skip l = l) ∧
  (declared_vars (Dec n e p) l = insert n () (declared_vars p l)) ∧
  (declared_vars (Seq p q) l = declared_vars q (declared_vars p l)) ∧
  (declared_vars (If e p q) l = declared_vars q (declared_vars p l)) ∧
  (declared_vars (While e p) l = declared_vars p l) ∧
  (declared_vars (Call (Ret _ rp NONE) _ _) l = declared_vars rp l) ∧
  (declared_vars (Call (Ret _ rp (SOME (Handle w ep))) _ _) l =
            declared_vars ep (declared_vars rp l))  ∧
  (declared_vars _ l = l)
End
*)

Definition exps_def:
  (exps (Const w) = [Const w]) ∧
  (exps (Var v) = [Var v]) ∧
  (exps (Load e) = exps e) ∧
  (exps (Load32 e) = exps e) ∧
  (exps (LoadByte e) = exps e) ∧
  (exps (LoadGlob a) = [LoadGlob a]) ∧
  (exps (Op bop es) = FLAT (MAP exps es)) ∧
  (exps (Crepop pop es) = FLAT (MAP exps es)) ∧
  (exps (Cmp c e1 e2) = exps e1 ++ exps e2) ∧
  (exps (Shift sh e1 e2) = exps e1 ++ exps e2) ∧
  (exps BaseAddr = [BaseAddr]) ∧
  (exps TopAddr = [TopAddr])
End

Overload shift = “backend_common$word_shift”
