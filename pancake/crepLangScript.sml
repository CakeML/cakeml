(*
  Abstract syntax of Crepe language
  Crepe: instrctuons are similar to that of
  Pancake, but we flatten locals from
  struct-layout to word-layout
*)

open preamble
     mlstringTheory
     asmTheory            (* for binop and cmp *)
     backend_commonTheory (* for overloading the shift operation *);

val _ = new_theory "crepLang";

Type shift = ``:ast$shift``

Type varname = ``:num``

Type funname = ``:mlstring``

Datatype:
  exp = Const ('a word)
      | Var varname
      | Label funname
      | Load exp
      | LoadByte exp
      | LoadGlob  (5 word)
      | Op binop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp num
End

Datatype:
  prog = Skip
       | Dec varname ('a exp) prog
       | Assign    varname  ('a exp)   (* dest, source *)
       | Store     ('a exp) ('a exp)   (* dest, source *)
       | StoreByte ('a exp) ('a exp)   (* dest, source *)
       | StoreGlob (5 word) ('a exp)   (* dest, source *)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break
       | Continue
       | Call ret ('a exp) (('a exp) list)
       | ExtCall funname varname varname varname varname
       | Raise ('a word)
       | Return ('a exp)
       | Tick;

  ret = Tail | Ret (varname option) prog (handler option);

  handler = Handle ('a word) prog
End

(* we can make return varaiable an option, but then might not be able to
   compile to loopLang *)

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Definition load_shape_def:
  (load_shape a 0 e = []) ∧
  (load_shape a (SUC i) e =
     if a = 0w then (Load e) :: load_shape (a + byte$bytes_in_word) i e
     else (Load (Op Add [e; Const a])) :: load_shape (a + byte$bytes_in_word) i e)
End

Definition nested_seq_def:
  (nested_seq [] = Skip) /\
  (nested_seq (e::es) = Seq e (nested_seq es))
End


Definition stores_def:
  (stores ad [] a = []) /\
  (stores ad (e::es) a =
     if a = 0w then Store ad e :: stores ad es (a + byte$bytes_in_word)
     else Store (Op Add [ad; Const a]) e :: stores ad es (a + byte$bytes_in_word))
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
  (var_cexp (Label f) = []) ∧
  (var_cexp (Load e) = var_cexp e) ∧
  (var_cexp (LoadByte e) = var_cexp e) ∧
  (var_cexp (LoadGlob a) = []) ∧
  (var_cexp (Op bop es) = FLAT (MAP var_cexp es)) ∧
  (var_cexp (Cmp c e1 e2) = var_cexp e1 ++ var_cexp e2) ∧
  (var_cexp (Shift sh e num) = var_cexp e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End

Definition assigned_vars_def:
  (assigned_vars Skip = ([]:num list)) ∧
  (assigned_vars (Dec n e p) = (n::assigned_vars p)) ∧
  (assigned_vars (Assign n e) = [n]) ∧
  (assigned_vars (Seq p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (If e p p') = assigned_vars p ++ assigned_vars p') ∧
  (assigned_vars (While e p) = assigned_vars p) ∧
  (assigned_vars (Call (Ret NONE rp (SOME (Handle _ p))) e es) =
     assigned_vars rp ++ assigned_vars p) ∧
  (assigned_vars (Call (Ret NONE rp NONE) e es) = assigned_vars rp) ∧
  (assigned_vars (Call (Ret (SOME rt) rp (SOME (Handle _ p))) e es) =
     rt :: assigned_vars rp ++ assigned_vars p) ∧
  (assigned_vars (Call (Ret (SOME rt) rp NONE) e es) = rt :: assigned_vars rp) ∧
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
  (exps (Label f) = [Label f]) ∧
  (exps (Load e) = exps e) ∧
  (exps (LoadByte e) = exps e) ∧
  (exps (LoadGlob a) = [LoadGlob a]) ∧
  (exps (Op bop es) = FLAT (MAP exps es)) ∧
  (exps (Cmp c e1 e2) = exps e1 ++ exps e2) ∧
  (exps (Shift sh e num) = exps e)
Termination
  wf_rel_tac `measure (\e. exp_size ARB e)` >>
  rpt strip_tac >>
  imp_res_tac MEM_IMP_exp_size >>
  TRY (first_x_assum (assume_tac o Q.SPEC `ARB`)) >>
  decide_tac
End


Definition acc_vars_def:
  (acc_vars Skip l = l) ∧
  (acc_vars (Dec n e p) l = acc_vars p (list_insert (n::var_cexp e) l)) ∧
  (acc_vars (Assign n e) l = list_insert (n::var_cexp e) l) ∧
  (acc_vars (Store e1 e2) l = list_insert (var_cexp e1 ++ var_cexp e2) l) ∧
  (acc_vars (StoreByte e1 e2) l = list_insert (var_cexp e1 ++ var_cexp e2) l) ∧
  (acc_vars (StoreGlob _ e) l = list_insert (var_cexp e) l) ∧
  (acc_vars (Seq p q) l = acc_vars p (acc_vars q l)) ∧
  (acc_vars (If e p q) l = acc_vars p (acc_vars q (list_insert (var_cexp e) l))) ∧
  (acc_vars (While e p) l = acc_vars p (list_insert (var_cexp e) l)) ∧
  (acc_vars (Return e) l  = list_insert (var_cexp e) l) ∧
  (acc_vars (ExtCall f v1 v2 v3 v4) l  = list_insert [v1; v2; v3; v4] l) ∧
  (acc_vars (Call Tail trgt args) l = list_insert (FLAT (MAP var_cexp (trgt::args))) l) ∧
  (acc_vars (Call (Ret NONE rp NONE) trgt args) l =
   let nl = list_insert (FLAT (MAP var_cexp (trgt::args))) l in
      acc_vars rp nl) ∧
  (acc_vars (Call (Ret NONE rp (SOME (Handle w ep))) trgt args) l =
   let nl = list_insert (FLAT (MAP var_cexp (trgt::args))) l in
      acc_vars rp (acc_vars ep nl)) ∧
  (acc_vars (Call (Ret (SOME rv) rp NONE) trgt args) l =
   let nl = list_insert (rv :: FLAT (MAP var_cexp (trgt::args))) l in
      acc_vars rp nl) ∧
  (acc_vars (Call (Ret (SOME rv) rp (SOME (Handle w ep))) trgt args) l =
   let nl = list_insert (rv :: FLAT (MAP var_cexp (trgt::args))) l in
      acc_vars rp (acc_vars ep nl)) ∧
  (acc_vars _ l = l)
End

Overload shift = “backend_common$word_shift”

val _ = export_theory();
