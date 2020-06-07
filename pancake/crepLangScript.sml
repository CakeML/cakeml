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

Type eid = ``:num``

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
       | Raise eid
       | Return ('a exp)
       | Tick;

  ret = Tail | Ret varname prog (handler option);

  handler = Handle eid prog
End

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


Overload shift = “backend_common$word_shift”

val _ = export_theory();
