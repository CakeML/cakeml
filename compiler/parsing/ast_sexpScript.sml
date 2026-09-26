(*
  Definitions to convert between the CakeML AST and s-expressions.
*)
Theory ast_sexp
Ancestors
  ast mlsexp mlint
Libs
  preamble

val _ = temp_enable_monadsyntax ()
val _ = temp_enable_monad "option"

(* l❲0❳ = HD l seems to be included in the simpset, meaning that EL_MEM
   cannot trigger in some cases. *)
Theorem HD_MEM[local]:
  0 < LENGTH ls ⇒ MEM (HD ls) ls
Proof
  Cases_on ‘ls’ >> rw []
QED

(* type -> s-expression *******************************************************)

(** types used, but not defined, by ast ***************************************)

Definition from_option_def:
  (from_option f NONE     = Atom «NONE») ∧
  (from_option f (SOME x) = Expr [Atom «SOME»; f x])
End

Definition from_int_pair_def:
  from_int_pair (a, b) =
    Expr [Atom (mlint$toString a); Atom (mlint$toString b)]
End

Definition from_id_def:
  (from_id (Short n)  = Expr [Atom «Short»; Atom n]) ∧
  (from_id (Long m i) = Expr [Atom «Long»; Atom m; from_id i])
End

(** types defined by ast ******************************************************)

Definition from_lit_def:
  (from_lit (IntLit i)  = Expr [Atom «IntLit» ; Atom (mlint$toString i)]) ∧
  (from_lit (Char c)    = Expr [Atom «Char»   ; Atom (chr_to_str c)]) ∧
  (from_lit (StrLit s)  = Expr [Atom «StrLit» ; Atom s]) ∧
  (from_lit (Word8 w)   = Expr [Atom «Word8»  ; Atom (num_to_str (w2n w))]) ∧
  (from_lit (Word64 w)  = Expr [Atom «Word64» ; Atom (num_to_str (w2n w))]) ∧
  (from_lit (Float64 w) = Expr [Atom «Float64»; Atom (num_to_str (w2n w))])
End

Definition from_shift_def:
  (from_shift Lsl = Atom «Lsl») ∧
  (from_shift Lsr = Atom «Lsr») ∧
  (from_shift Asr = Atom «Asr») ∧
  (from_shift Ror = Atom «Ror»)
End

Definition from_arith_def:
  (from_arith Add  = Atom «Add») ∧
  (from_arith Sub  = Atom «Sub») ∧
  (from_arith Mul  = Atom «Mul») ∧
  (from_arith Div  = Atom «Div») ∧
  (from_arith Mod  = Atom «Mod») ∧
  (from_arith Neg  = Atom «Neg») ∧
  (from_arith And  = Atom «And») ∧
  (from_arith Xor  = Atom «Xor») ∧
  (from_arith Or   = Atom «Or») ∧
  (from_arith Not  = Atom «Not») ∧
  (from_arith Abs  = Atom «Abs») ∧
  (from_arith Sqrt = Atom «Sqrt») ∧
  (from_arith FMA  = Atom «FMA») ∧
  (from_arith (Shift s) = Expr [Atom «Shift»; from_shift s])
End


Definition from_word_size_def:
  (from_word_size W8  = Atom «W8») ∧
  (from_word_size W64 = Atom «W64»)
End

Definition from_thunk_mode_def:
  (from_thunk_mode Evaluated    = Atom «Evaluated») ∧
  (from_thunk_mode NotEvaluated = Atom «NotEvaluated»)
End

Definition from_thunk_op_def:
  (from_thunk_op (AllocThunk m)  =
     Expr [Atom «AllocThunk»; from_thunk_mode m]) ∧
  (from_thunk_op (UpdateThunk m) =
     Expr [Atom «UpdateThunk»; from_thunk_mode m]) ∧
  (from_thunk_op ForceThunk      = Atom «ForceThunk»)
End

Definition from_opb_def:
  (from_opb Lt  = Atom «Lt») ∧
  (from_opb Gt  = Atom «Gt») ∧
  (from_opb Leq = Atom «Leq») ∧
  (from_opb Geq = Atom «Geq»)
End

Definition from_test_def:
  (from_test Equal          = Atom «Equal») ∧
  (from_test (Compare c)    = Expr [Atom «Compare»; from_opb c]) ∧
  (from_test (AltCompare c) = Expr [Atom «AltCompare»; from_opb c])
End

Definition from_prim_type_def:
  (from_prim_type BoolT     = Atom «BoolT») ∧
  (from_prim_type IntT      = Atom «IntT») ∧
  (from_prim_type CharT     = Atom «CharT») ∧
  (from_prim_type StrT      = Atom «StrT») ∧
  (from_prim_type (WordT w) = Expr [Atom «WordT»; from_word_size w]) ∧
  (from_prim_type Float64T  = Atom «Float64T»)
End

Definition from_op_def:
  (from_op (Arith a t)         =
     Expr [Atom «Arith»; from_arith a; from_prim_type t]) ∧
  (from_op (FromTo t1 t2)      =
     Expr [Atom «FromTo»; from_prim_type t1; from_prim_type t2]) ∧
  (from_op Equality            = Atom «Equality») ∧
  (from_op (Test x t)          =
     Expr [Atom «Test»; from_test x; from_prim_type t]) ∧
  (from_op Opapp               = Atom «Opapp») ∧
  (from_op Opassign            = Atom «Opassign») ∧
  (from_op Opref               = Atom «Opref») ∧
  (from_op Opderef             = Atom «Opderef») ∧
  (from_op Aw8alloc            = Atom «Aw8alloc») ∧
  (from_op Aw8sub              = Atom «Aw8sub») ∧
  (from_op Aw8length           = Atom «Aw8length») ∧
  (from_op Aw8update           = Atom «Aw8update») ∧
  (from_op Aw8subBit           = Atom «Aw8subBit») ∧
  (from_op Aw8updateBit        = Atom «Aw8updateBit») ∧
  (from_op CopyStrStr          = Atom «CopyStrStr») ∧
  (from_op CopyStrAw8          = Atom «CopyStrAw8») ∧
  (from_op CopyAw8Str          = Atom «CopyAw8Str») ∧
  (from_op CopyAw8Aw8          = Atom «CopyAw8Aw8») ∧
  (from_op XorAw8Str_unsafe    = Atom «XorAw8Str_unsafe») ∧
  (from_op Implode             = Atom «Implode») ∧
  (from_op Explode             = Atom «Explode») ∧
  (from_op Strsub              = Atom «Strsub») ∧
  (from_op Strlen              = Atom «Strlen») ∧
  (from_op Strcat              = Atom «Strcat») ∧
  (from_op VfromList           = Atom «VfromList») ∧
  (from_op Vsub                = Atom «Vsub») ∧
  (from_op Vlength             = Atom «Vlength») ∧
  (from_op Aalloc              = Atom «Aalloc») ∧
  (from_op AallocEmpty         = Atom «AallocEmpty») ∧
  (from_op AallocFixed         = Atom «AallocFixed») ∧
  (from_op Asub                = Atom «Asub») ∧
  (from_op Alength             = Atom «Alength») ∧
  (from_op Aupdate             = Atom «Aupdate») ∧
  (from_op Vsub_unsafe         = Atom «Vsub_unsafe») ∧
  (from_op Asub_unsafe         = Atom «Asub_unsafe») ∧
  (from_op Aupdate_unsafe      = Atom «Aupdate_unsafe») ∧
  (from_op Aw8sub_unsafe       = Atom «Aw8sub_unsafe») ∧
  (from_op Aw8update_unsafe    = Atom «Aw8update_unsafe») ∧
  (from_op Aw8subBit_unsafe    = Atom «Aw8subBit_unsafe») ∧
  (from_op Aw8updateBit_unsafe = Atom «Aw8updateBit_unsafe») ∧
  (from_op (ThunkOp t)         = Expr [Atom «ThunkOp»; from_thunk_op t]) ∧
  (from_op ListAppend          = Atom «ListAppend») ∧
  (from_op ConfigGC            = Atom «ConfigGC») ∧
  (from_op (FFI s)             = Expr [Atom «FFI»; Atom s]) ∧
  (from_op Eval                = Atom «Eval») ∧
  (from_op Env_id              = Atom «Env_id»)
End

Definition from_ast_t_def:
  (from_ast_t (Atvar n)     = Expr [Atom «Atvar»; Atom n]) ∧
  (from_ast_t (Atfun t1 t2) =
     Expr [Atom «Atfun»; from_ast_t t1; from_ast_t t2]) ∧
  (from_ast_t (Attup ts)    = Expr [Atom «Attup»; Expr (from_ast_ts ts)]) ∧
  (from_ast_t (Atapp ts i)  =
     Expr [Atom «Atapp»; Expr (from_ast_ts ts); from_id i]) ∧
  (from_ast_ts []           = []) ∧
  (from_ast_ts (t::ts)      = from_ast_t t :: from_ast_ts ts)
End

Definition from_pat_def:
  (from_pat Pany          = Atom «Pany») ∧
  (from_pat (Pvar n)      = Expr [Atom «Pvar»; Atom n]) ∧
  (from_pat (Plit l)      = Expr [Atom «Plit»; from_lit l]) ∧
  (from_pat (Pcon io ps)  =
     Expr [Atom «Pcon»; from_option from_id io; Expr (from_pats ps)]) ∧
  (from_pat (Pref p)      = Expr [Atom «Pref»; from_pat p]) ∧
  (from_pat (Pas p n)     = Expr [Atom «Pas»; from_pat p; Atom n]) ∧
  (from_pat (Ptannot p t) = Expr [Atom «Ptannot»; from_pat p; from_ast_t t]) ∧
  (from_pats []           = []) ∧
  (from_pats (p::ps)      = from_pat p :: from_pats ps)
End

Definition from_lop_def:
  (from_lop Andalso = Atom «Andalso») ∧
  (from_lop Orelse  = Atom «Orelse»)
End

Definition from_locs_def:
  (from_locs NoLocs = Atom «NoLocs») ∧
  (from_locs (Locs p1 p2) =
     Expr [Atom «Locs»; from_int_pair p1; from_int_pair p2])
End

Definition from_exp_def:
  (from_exp (Raise e)       = Expr [Atom «Raise»; from_exp e]) ∧
  (from_exp (Handle e pes)  =
     Expr [Atom «Handle»; from_exp e; Expr (from_pes pes)]) ∧
  (from_exp (Lit l)         = Expr [Atom «Lit»; from_lit l]) ∧
  (from_exp (Con io es)     =
     Expr [Atom «Con»; from_option from_id io; Expr (from_exps es)]) ∧
  (from_exp (Ident i)       = Expr [Atom «Ident»; from_id i]) ∧
  (from_exp (Fun x e)       = Expr [Atom «Fun»; Atom x; from_exp e]) ∧
  (from_exp (App oper es)   =
     Expr [Atom «App»; from_op oper; Expr (from_exps es)]) ∧
  (from_exp (Log lo e1 e2)  =
     Expr [Atom «Log»; from_lop lo; from_exp e1; from_exp e2]) ∧
  (from_exp (If e1 e2 e3)   =
     Expr [Atom «If»; from_exp e1; from_exp e2; from_exp e3]) ∧
  (from_exp (Mat e pes)     =
     Expr [Atom «Mat»; from_exp e; Expr (from_pes pes)]) ∧
  (from_exp (Let vo e1 e2)  =
     Expr [Atom «Let»; from_option Atom vo; from_exp e1; from_exp e2]) ∧
  (from_exp (Letrec funs e) =
     Expr [Atom «Letrec»; Expr (from_funs funs); from_exp e]) ∧
  (from_exp (Tannot e t)    = Expr [Atom «Tannot»; from_exp e; from_ast_t t]) ∧
  (from_exp (Lannot e l)    = Expr [Atom «Lannot»; from_exp e; from_locs l]) ∧
  (from_exp (Open ms e)     =
     Expr [Atom «Open»; Expr (MAP Atom ms); from_exp e]) ∧
  (from_exps []             = []) ∧
  (from_exps (e::es)        = from_exp e :: from_exps es) ∧
  (from_pes []              = []) ∧
  (from_pes ((p,e)::pes)    = Expr [from_pat p; from_exp e] :: from_pes pes) ∧
  (from_funs []             = []) ∧
  (from_funs ((f,x,e)::funs) =
     Expr [Atom f; Atom x; from_exp e] :: from_funs funs)
End

Definition from_ctor_def:
  from_ctor (cn, ts) = Expr [Atom cn; Expr (from_ast_ts ts)]
End

Definition from_tdef_def:
  from_tdef (tvs, tn, ctors) =
    Expr [Expr (MAP Atom tvs); Atom tn; Expr (MAP from_ctor ctors)]
End

Definition from_type_def_def:
  from_type_def tds = Expr (MAP from_tdef tds)
End

Definition from_dec_def:
  (from_dec (Dlet l p e) =
     Expr [Atom «Dlet»; from_locs l; from_pat p; from_exp e]) ∧
  (from_dec (Dletrec l funs) =
     Expr [Atom «Dletrec»; from_locs l; Expr (from_funs funs)]) ∧
  (from_dec (Dtype l tds) =
     Expr [Atom «Dtype»; from_locs l; from_type_def tds]) ∧
  (from_dec (Dtabbrev l tvs tn t) =
     Expr [Atom «Dtabbrev»; from_locs l; Expr (MAP Atom tvs); Atom tn;
           from_ast_t t]) ∧
  (from_dec (Dexn l cn ts) =
     Expr [Atom «Dexn»; from_locs l; Atom cn; Expr (from_ast_ts ts)]) ∧
  (from_dec (Dmod mn ds) =
     Expr [Atom «Dmod»; Atom mn; Expr (from_decs ds)]) ∧
  (from_dec (Dlocal lds ds) =
     Expr [Atom «Dlocal»; Expr (from_decs lds); Expr (from_decs ds)]) ∧
  (from_dec (Denv n) = Expr [Atom «Denv»; Atom n]) ∧
  (from_dec (Dopen l ms) =
     Expr [Atom «Dopen»; from_locs l; Expr (MAP Atom ms)]) ∧
  (from_decs [] = []) ∧
  (from_decs (d::ds) = from_dec d :: from_decs ds)
End

(* s-expression -> type *******************************************************)

Definition dest_atom_def:
  (dest_atom (Atom s) = SOME s) ∧
  (dest_atom _ = NONE)
End

Definition dest_expr_def:
  dest_expr (Expr ls) = SOME ls ∧
  dest_expr _         = NONE
End

Definition to_int_pair_def:
  to_int_pair sexp =
  do
    ls <- dest_expr sexp;
    assert (LENGTH ls = 2);
    sa <- dest_atom ls❲0❳;
    sb <- dest_atom ls❲1❳;
    a <- mlint$fromString sa;
    b <- mlint$fromString sb;
    return (a, b)
  od
End

Theorem dest_expr_sexp_size:
  dest_expr s = SOME ls ⇒ list_size sexp_size ls < sexp_size s
Proof
  Cases_on ‘s’ >> rw [dest_expr_def]
QED

Theorem dest_expr_sexp_size_MEM:
  dest_expr s = SOME ls ⇒
  ∀a. MEM a ls ⇒ sexp_size a < sexp_size s
Proof
  Cases_on ‘s’ >> rw [dest_expr_def]
  >> drule MEM_list_size
  >> disch_then $ qspec_then ‘sexp_size’ mp_tac
  >> simp []
QED

Definition dest_tagged_def:
  dest_tagged (Expr (Atom tag :: args)) = SOME (tag, args) ∧
  dest_tagged _ = NONE
End

Theorem dest_tagged_sexp_size:
  dest_tagged s = SOME (tag, args) ⇒
  ∀a. MEM a args ⇒ sexp_size a < sexp_size s
Proof
  rw []
  >> gvs [oneline dest_tagged_def]
  >> every_case_tac >> gvs []
  >> drule MEM_list_size
  >> disch_then $ qspec_then ‘sexp_size’ mp_tac
  >> simp []
QED

Definition to_option_def:
  (to_option f (Atom s) = if s = «NONE» then return NONE else fail) ∧
  (to_option f sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (tag = «SOME» ∧ LENGTH args = 1);
     x <- f args❲0❳;
     return (SOME x)
   od)
End

Definition to_id_def:
  to_id sexp =
  do
    (tag, args) <- dest_tagged sexp;
    if tag = «Short» ∧ LENGTH args = 1 then
      do
        n <- dest_atom args❲0❳;
        return (Short n)
      od
    else if tag = «Long» ∧ LENGTH args = 2 then
      do
        m <- dest_atom args❲0❳;
        i <- to_id args❲1❳;
        return (Long m i)
      od
    else fail
  od
Termination
  wf_rel_tac ‘measure sexp_size’ >> rw []
  >> drule dest_tagged_sexp_size >> simp [EL_MEM]
End

(** types defined by ast ******************************************************)

Definition to_lit_def:
  to_lit sexp =
  do
    (tag, args) <- dest_tagged sexp;
    assert (LENGTH args = 1);
    s <- dest_atom args❲0❳;
    if tag = «IntLit» then
      do
        i <- mlint$fromString s;
        return (IntLit i)
      od
    else if tag = «Char» then
      do
        assert (strlen s = 1);
        return (Char (strsub s 0))
      od
    else if tag = «StrLit» then
      return (StrLit s)
    else if tag = «Word8» then
      do
        n <- fromNatString s;
        assert (n < dimword (:8));
        return (Word8 (n2w n))
      od
    else if tag = «Word64» then
      do
        n <- fromNatString s;
        assert (n < dimword (:64));
        return (Word64 (n2w n))
      od
    else if tag = «Float64» then
      do
        n <- fromNatString s;
        assert (n < dimword (:64));
        return (Float64 (n2w n))
      od
    else fail
  od
End

Definition to_shift_def:
  (to_shift (Atom s) =
     if s = «Lsl» then return Lsl
     else if s = «Lsr» then return Lsr
     else if s = «Asr» then return Asr
     else if s = «Ror» then return Ror
     else fail) ∧
  (to_shift _ = fail)
End

Definition to_arith_def:
  (to_arith (Atom s) =
     if s = «Add» then return Add
     else if s = «Sub» then return Sub
     else if s = «Mul» then return Mul
     else if s = «Div» then return Div
     else if s = «Mod» then return Mod
     else if s = «Neg» then return Neg
     else if s = «And» then return And
     else if s = «Xor» then return Xor
     else if s = «Or» then return Or
     else if s = «Not» then return Not
     else if s = «Abs» then return Abs
     else if s = «Sqrt» then return Sqrt
     else if s = «FMA» then return FMA
     else fail) ∧
  (to_arith sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (tag = «Shift» ∧ LENGTH args = 1);
     s <- to_shift args❲0❳;
     return (Shift s)
   od)
End

Definition to_word_size_def:
  (to_word_size (Atom s) =
     if s = «W8» then return W8
     else if s = «W64» then return W64
     else fail) ∧
  (to_word_size _ = fail)
End

Definition to_thunk_mode_def:
  (to_thunk_mode (Atom s) =
     if s = «Evaluated» then return Evaluated
     else if s = «NotEvaluated» then return NotEvaluated
     else fail) ∧
  (to_thunk_mode _ = fail)
End

Definition to_thunk_op_def:
  (to_thunk_op (Atom s) =
     if s = «ForceThunk» then return ForceThunk else fail) ∧
  (to_thunk_op sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (LENGTH args = 1);
     m <- to_thunk_mode args❲0❳;
     if tag = «AllocThunk» then return (AllocThunk m)
     else if tag = «UpdateThunk» then return (UpdateThunk m)
     else fail
   od)
End

Definition to_opb_def:
  (to_opb (Atom s) =
     if s = «Lt» then return Lt
     else if s = «Gt» then return Gt
     else if s = «Leq» then return Leq
     else if s = «Geq» then return Geq
     else fail) ∧
  (to_opb _ = fail)
End

Definition to_test_def:
  (to_test (Atom s) =
     if s = «Equal» then return Equal else fail) ∧
  (to_test sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (LENGTH args = 1);
     c <- to_opb args❲0❳;
     if tag = «Compare» then return (Compare c)
     else if tag = «AltCompare» then return (AltCompare c)
     else fail
   od)
End

Definition to_prim_type_def:
  (to_prim_type (Atom s) =
     if s = «BoolT» then return BoolT
     else if s = «IntT» then return IntT
     else if s = «CharT» then return CharT
     else if s = «StrT» then return StrT
     else if s = «Float64T» then return Float64T
     else fail) ∧
  (to_prim_type sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (tag = «WordT» ∧ LENGTH args = 1);
     w <- to_word_size args❲0❳;
     return (WordT w)
   od)
End

Definition to_op_def:
  (to_op (Atom s) =
     if s = «Equality» then return Equality
     else if s = «Opapp» then return Opapp
     else if s = «Opassign» then return Opassign
     else if s = «Opref» then return Opref
     else if s = «Opderef» then return Opderef
     else if s = «Aw8alloc» then return Aw8alloc
     else if s = «Aw8sub» then return Aw8sub
     else if s = «Aw8length» then return Aw8length
     else if s = «Aw8update» then return Aw8update
     else if s = «Aw8subBit» then return Aw8subBit
     else if s = «Aw8updateBit» then return Aw8updateBit
     else if s = «CopyStrStr» then return CopyStrStr
     else if s = «CopyStrAw8» then return CopyStrAw8
     else if s = «CopyAw8Str» then return CopyAw8Str
     else if s = «CopyAw8Aw8» then return CopyAw8Aw8
     else if s = «XorAw8Str_unsafe» then return XorAw8Str_unsafe
     else if s = «Implode» then return Implode
     else if s = «Explode» then return Explode
     else if s = «Strsub» then return Strsub
     else if s = «Strlen» then return Strlen
     else if s = «Strcat» then return Strcat
     else if s = «VfromList» then return VfromList
     else if s = «Vsub» then return Vsub
     else if s = «Vlength» then return Vlength
     else if s = «Aalloc» then return Aalloc
     else if s = «AallocEmpty» then return AallocEmpty
     else if s = «AallocFixed» then return AallocFixed
     else if s = «Asub» then return Asub
     else if s = «Alength» then return Alength
     else if s = «Aupdate» then return Aupdate
     else if s = «Vsub_unsafe» then return Vsub_unsafe
     else if s = «Asub_unsafe» then return Asub_unsafe
     else if s = «Aupdate_unsafe» then return Aupdate_unsafe
     else if s = «Aw8sub_unsafe» then return Aw8sub_unsafe
     else if s = «Aw8update_unsafe» then return Aw8update_unsafe
     else if s = «Aw8subBit_unsafe» then return Aw8subBit_unsafe
     else if s = «Aw8updateBit_unsafe» then return Aw8updateBit_unsafe
     else if s = «ListAppend» then return ListAppend
     else if s = «ConfigGC» then return ConfigGC
     else if s = «Eval» then return Eval
     else if s = «Env_id» then return Env_id
     else fail) ∧
  (to_op sexp =
   do
     (tag, args) <- dest_tagged sexp;
     if tag = «Arith» ∧ LENGTH args = 2 then
       do
         a <- to_arith args❲0❳;
         t <- to_prim_type args❲1❳;
         return (Arith a t)
       od
     else if tag = «FromTo» ∧ LENGTH args = 2 then
       do
         t1 <- to_prim_type args❲0❳;
         t2 <- to_prim_type args❲1❳;
         return (FromTo t1 t2)
       od
     else if tag = «Test» ∧ LENGTH args = 2 then
       do
         x <- to_test args❲0❳;
         t <- to_prim_type args❲1❳;
         return (Test x t)
       od
     else if tag = «ThunkOp» ∧ LENGTH args = 1 then
       do
         t <- to_thunk_op args❲0❳;
         return (ThunkOp t)
       od
     else if tag = «FFI» ∧ LENGTH args = 1 then
       do
         s <- dest_atom args❲0❳;
         return (FFI s)
       od
     else fail
   od)
End

Definition to_ast_t_def:
  (to_ast_t sexp =
   do
     (tag, args) <- dest_tagged sexp;
     if tag = «Atvar» ∧ LENGTH args = 1 then
       do
         n <- dest_atom args❲0❳;
         return (Atvar n)
       od
     else if tag = «Atfun» ∧ LENGTH args = 2 then
       do
         t1 <- to_ast_t args❲0❳;
         t2 <- to_ast_t args❲1❳;
         return (Atfun t1 t2)
       od
     else if tag = «Attup» ∧ LENGTH args = 1 then
       do
         ls <- dest_expr args❲0❳;
         ts <- to_ast_ts ls;
         return (Attup ts)
       od
     else if tag = «Atapp» ∧ LENGTH args = 2 then
       do
         ls <- dest_expr args❲0❳;
         ts <- to_ast_ts ls;
         i <- to_id args❲1❳;
         return (Atapp ts i)
       od
     else fail
   od) ∧
  (to_ast_ts [] = return []) ∧
  (to_ast_ts (s::ss) =
   do
     t <- to_ast_t s;
     ts <- to_ast_ts ss;
     return (t::ts)
   od)
Termination
  wf_rel_tac ‘measure (λx. case x of
                            | INL s => sexp_size s
                            | INR ss => list_size sexp_size ss)’
  >> rw []
  >> imp_res_tac dest_tagged_sexp_size
  >> imp_res_tac dest_expr_sexp_size
  >> gvs [EL_MEM, HD_MEM]
  >> irule LESS_TRANS
  >> first_assum $ irule_at (Pos hd)
  >> simp [HD_MEM]
End

Definition to_pat_def:
  (to_pat (Atom s) =
     if s = «Pany» then return Pany else fail) ∧
  (to_pat sexp =
   do
     (tag, args) <- dest_tagged sexp;
     if tag = «Pvar» ∧ LENGTH args = 1 then
       do
         n <- dest_atom args❲0❳;
         return (Pvar n)
       od
     else if tag = «Plit» ∧ LENGTH args = 1 then
       do
         l <- to_lit args❲0❳;
         return (Plit l)
       od
     else if tag = «Pcon» ∧ LENGTH args = 2 then
       do
         io <- to_option to_id args❲0❳;
         ls <- dest_expr args❲1❳;
         ps <- to_pats ls;
         return (Pcon io ps)
       od
     else if tag = «Pref» ∧ LENGTH args = 1 then
       do
         p <- to_pat args❲0❳;
         return (Pref p)
       od
     else if tag = «Pas» ∧ LENGTH args = 2 then
       do
         p <- to_pat args❲0❳;
         n <- dest_atom args❲1❳;
         return (Pas p n)
       od
     else if tag = «Ptannot» ∧ LENGTH args = 2 then
       do
         p <- to_pat args❲0❳;
         t <- to_ast_t args❲1❳;
         return (Ptannot p t)
       od
     else fail
   od) ∧
  (to_pats [] = return []) ∧
  (to_pats (s::ss) =
   do
     p <- to_pat s;
     ps <- to_pats ss;
     return (p::ps)
   od)
Termination
  wf_rel_tac ‘measure (λx. case x of
                            | INL s => sexp_size s
                            | INR ss => list_size sexp_size ss)’
  >> rw []
  >> imp_res_tac dest_tagged_sexp_size
  >> imp_res_tac dest_expr_sexp_size
  >> gvs [HD_MEM]
  >> irule LESS_TRANS
  >> first_assum $ irule_at (Pos hd)
  >> simp [EL_MEM]
End

Definition to_lop_def:
  (to_lop (Atom s) =
     if s = «Andalso» then return Andalso
     else if s = «Orelse» then return Orelse
     else fail) ∧
  (to_lop _ = fail)
End

Definition to_locs_def:
  (to_locs (Atom s) =
     if s = «NoLocs» then return NoLocs else fail) ∧
  (to_locs sexp =
   do
     (tag, args) <- dest_tagged sexp;
     assert (tag = «Locs» ∧ LENGTH args = 2);
     p1 <- to_int_pair args❲0❳;
     p2 <- to_int_pair args❲1❳;
     return (Locs p1 p2)
   od)
End

Definition to_exp_def:
  (to_exp sexp =
   do
     (tag, args) <- dest_tagged sexp;
     if tag = «Raise» ∧ LENGTH args = 1 then
       do
         e <- to_exp args❲0❳;
         return (Raise e)
       od
     else if tag = «Handle» ∧ LENGTH args = 2 then
       do
         e <- to_exp args❲0❳;
         ls <- dest_expr args❲1❳;
         pes <- to_pes ls;
         return (Handle e pes)
       od
     else if tag = «Lit» ∧ LENGTH args = 1 then
       do
         l <- to_lit args❲0❳;
         return (Lit l)
       od
     else if tag = «Con» ∧ LENGTH args = 2 then
       do
         io <- to_option to_id args❲0❳;
         ls <- dest_expr args❲1❳;
         es <- to_exps ls;
         return (Con io es)
       od
     else if tag = «Ident» ∧ LENGTH args = 1 then
       do
         i <- to_id args❲0❳;
         return (Ident i)
       od
     else if tag = «Fun» ∧ LENGTH args = 2 then
       do
         x <- dest_atom args❲0❳;
         e <- to_exp args❲1❳;
         return (Fun x e)
       od
     else if tag = «App» ∧ LENGTH args = 2 then
       do
         oper <- to_op args❲0❳;
         ls <- dest_expr args❲1❳;
         es <- to_exps ls;
         return (App oper es)
       od
     else if tag = «Log» ∧ LENGTH args = 3 then
       do
         lo <- to_lop args❲0❳;
         e1 <- to_exp args❲1❳;
         e2 <- to_exp args❲2❳;
         return (Log lo e1 e2)
       od
     else if tag = «If» ∧ LENGTH args = 3 then
       do
         e1 <- to_exp args❲0❳;
         e2 <- to_exp args❲1❳;
         e3 <- to_exp args❲2❳;
         return (If e1 e2 e3)
       od
     else if tag = «Mat» ∧ LENGTH args = 2 then
       do
         e <- to_exp args❲0❳;
         ls <- dest_expr args❲1❳;
         pes <- to_pes ls;
         return (Mat e pes)
       od
     else if tag = «Let» ∧ LENGTH args = 3 then
       do
         vo <- to_option dest_atom args❲0❳;
         e1 <- to_exp args❲1❳;
         e2 <- to_exp args❲2❳;
         return (Let vo e1 e2)
       od
     else if tag = «Letrec» ∧ LENGTH args = 2 then
       do
         ls <- dest_expr args❲0❳;
         funs <- to_funs ls;
         e <- to_exp args❲1❳;
         return (Letrec funs e)
       od
     else if tag = «Tannot» ∧ LENGTH args = 2 then
       do
         e <- to_exp args❲0❳;
         t <- to_ast_t args❲1❳;
         return (Tannot e t)
       od
     else if tag = «Lannot» ∧ LENGTH args = 2 then
       do
         e <- to_exp args❲0❳;
         l <- to_locs args❲1❳;
         return (Lannot e l)
       od
     else if tag = «Open» ∧ LENGTH args = 2 then
       do
         ls <- dest_expr args❲0❳;
         ms <- OPT_MMAP dest_atom ls;
         e <- to_exp args❲1❳;
         return (Open ms e)
       od
     else fail
   od) ∧
  (to_exps [] = return []) ∧
  (to_exps (s::ss) =
   do
     e <- to_exp s;
     es <- to_exps ss;
     return (e::es)
   od) ∧
  (to_pes [] = return []) ∧
  (to_pes (s::ss) =
   do
     ls <- dest_expr s;
     assert (LENGTH ls = 2);
     p <- to_pat ls❲0❳;
     e <- to_exp ls❲1❳;
     pes <- to_pes ss;
     return ((p, e)::pes)
   od) ∧
  (to_funs [] = return []) ∧
  (to_funs (s::ss) =
   do
     ls <- dest_expr s;
     assert (LENGTH ls = 3);
     f <- dest_atom ls❲0❳;
     x <- dest_atom ls❲1❳;
     e <- to_exp ls❲2❳;
     funs <- to_funs ss;
     return ((f, x, e)::funs)
   od)
Termination
  wf_rel_tac ‘measure (λx. case x of
                            | INL s => sexp_size s
                            | INR (INL ss) => list_size sexp_size ss
                            | INR (INR (INL ss)) => list_size sexp_size ss
                            | INR (INR (INR ss)) => list_size sexp_size ss)’
  >> rw []
  >> imp_res_tac dest_tagged_sexp_size
  >> imp_res_tac dest_expr_sexp_size
  >> imp_res_tac dest_expr_sexp_size_MEM
  >> gvs [EL_MEM, HD_MEM]
  >> irule LESS_TRANS
  >> first_assum $ irule_at (Pos hd)
  >> simp [EL_MEM, HD_MEM]
End

Definition to_ctor_def:
  to_ctor sexp =
  do
    ls <- dest_expr sexp;
    assert (LENGTH ls = 2);
    cn <- dest_atom ls❲0❳;
    tls <- dest_expr ls❲1❳;
    ts <- to_ast_ts tls;
    return (cn, ts)
  od
End

Definition to_tdef_def:
  to_tdef sexp =
  do
    ls <- dest_expr sexp;
    assert (LENGTH ls = 3);
    tvls <- dest_expr ls❲0❳;
    tvs <- OPT_MMAP dest_atom tvls;
    tn <- dest_atom ls❲1❳;
    cls <- dest_expr ls❲2❳;
    ctors <- OPT_MMAP to_ctor cls;
    return (tvs, tn, ctors)
  od
End

Definition to_type_def_def:
  to_type_def sexp =
  do
    ls <- dest_expr sexp;
    OPT_MMAP to_tdef ls
  od
End

Definition to_dec_def:
  (to_dec sexp =
   do
     (tag, args) <- dest_tagged sexp;
     if tag = «Dlet» ∧ LENGTH args = 3 then
       do
         l <- to_locs args❲0❳;
         p <- to_pat args❲1❳;
         e <- to_exp args❲2❳;
         return (Dlet l p e)
       od
     else if tag = «Dletrec» ∧ LENGTH args = 2 then
       do
         l <- to_locs args❲0❳;
         ls <- dest_expr args❲1❳;
         funs <- to_funs ls;
         return (Dletrec l funs)
       od
     else if tag = «Dtype» ∧ LENGTH args = 2 then
       do
         l <- to_locs args❲0❳;
         tds <- to_type_def args❲1❳;
         return (Dtype l tds)
       od
     else if tag = «Dtabbrev» ∧ LENGTH args = 4 then
       do
         l <- to_locs args❲0❳;
         tvls <- dest_expr args❲1❳;
         tvs <- OPT_MMAP dest_atom tvls;
         tn <- dest_atom args❲2❳;
         t <- to_ast_t args❲3❳;
         return (Dtabbrev l tvs tn t)
       od
     else if tag = «Dexn» ∧ LENGTH args = 3 then
       do
         l <- to_locs args❲0❳;
         cn <- dest_atom args❲1❳;
         tls <- dest_expr args❲2❳;
         ts <- to_ast_ts tls;
         return (Dexn l cn ts)
       od
     else if tag = «Dmod» ∧ LENGTH args = 2 then
       do
         mn <- dest_atom args❲0❳;
         ls <- dest_expr args❲1❳;
         ds <- to_decs ls;
         return (Dmod mn ds)
       od
     else if tag = «Dlocal» ∧ LENGTH args = 2 then
       do
         lls <- dest_expr args❲0❳;
         lds <- to_decs lls;
         ls <- dest_expr args❲1❳;
         ds <- to_decs ls;
         return (Dlocal lds ds)
       od
     else if tag = «Denv» ∧ LENGTH args = 1 then
       do
         n <- dest_atom args❲0❳;
         return (Denv n)
       od
     else if tag = «Dopen» ∧ LENGTH args = 2 then
       do
         l <- to_locs args❲0❳;
         ls <- dest_expr args❲1❳;
         ms <- OPT_MMAP dest_atom ls;
         return (Dopen l ms)
       od
     else fail
   od) ∧
  (to_decs [] = return []) ∧
  (to_decs (s::ss) =
   do
     d <- to_dec s;
     ds <- to_decs ss;
     return (d::ds)
   od)
Termination
  wf_rel_tac ‘measure (λx. case x of
                            | INL s => sexp_size s
                            | INR ss => list_size sexp_size ss)’
  >> rw []
  >> imp_res_tac dest_tagged_sexp_size
  >> imp_res_tac dest_expr_sexp_size
  >> irule LESS_TRANS
  >> first_assum $ irule_at (Pos hd)
  >> gvs [EL_MEM, HD_MEM]
End
