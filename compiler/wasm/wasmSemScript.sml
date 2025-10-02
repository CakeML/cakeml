(*
  CWasm Functional Bigstep semantics
*)

Theory      wasmSem
Ancestors   wasmLang wasm_sem_common ancillaryOps option arithmetic
Libs        wordsLib

Datatype: state =
  <|
    clock   : num;
    stack   : value list;
    locals  : value list;
    globals : value list;
    memory  : word8 list;
    types   : functype list;
    funcs   : func list;
    func_tables : num list ;
  |>
End

(**************************************)
(*                                    *)
(*     Helper/ancillary functions     *)
(*                                    *)
(**************************************)

(* Returns the result type of a block-y isntr *)
Definition resulttype_of_blocktype_def:
   resulttype_of_blocktype  BlkNil : resulttype = NONE ∧
   resulttype_of_blocktype (BlkVal ty)          = SOME ty
End

Definition init_val_of_def:
  init_val_of (Tnum Int W32:valtype) : value = I32 0w ∧
  init_val_of (Tnum Int W64) = I64 0w
End

Definition nonzero_def:
  nonzero (I32 n:value) : bool option = SOME (n ≠ 0w) ∧
  nonzero (I64 n) = NONE
End

(************************)
(*   Stack operations   *)
(************************)

Definition pop_def:
  pop (s:state) : (value # state) option =
    case s.stack of
    | [] => NONE
    | (x::ss) => SOME (x, s with stack := ss)
End

Definition pop_n_def:
  pop_n n s =
    if LENGTH s.stack < n then NONE else
      SOME (TAKE n s.stack, s with stack := DROP n s.stack)
End

Definition push_def:
  push (x:value) (s:state) = s with stack := x :: s.stack
End


Definition dest_i32_def:
  dest_i32 (I32 w:value) : word32 option = SOME w ∧
  dest_i32 _ = NONE
End

Definition pop_i32_def:
  pop_i32 (s:state) : (word32 # state) option =
    case s.stack of
    | []                          => NONE
    | x::stk => case x of (I32 w) => SOME (w, s with stack := stk)
                          | _     => NONE
End



Definition fix_clock_def:
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)
End

Triviality fix_clock_def':
  fix_clock s x =
  case x of (res,s1) =>
  (res,s1 with clock := MIN s.clock s1.clock)
Proof
  Cases_on‘x’
  >>rw[fix_clock_def]
QED

Triviality fix_clock_IMP:
  (fix_clock s x = (res,s1) ==> s1.clock <= s.clock) ∧
  ((res,s1) = fix_clock s x ==> s1.clock <= s.clock)
Proof
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

Definition inst_size'_def:
  inst_size' (If    _ bt be         ) = 2 + list_size inst_size' bt + list_size inst_size' be ∧
  inst_size' (Block _ b             ) = 1 + list_size inst_size' b ∧
  inst_size' (Loop  _ b             ) = 1 + list_size inst_size' b ∧
  inst_size' (CallIndirect       _ _) = 2 ∧
  inst_size' (ReturnCallIndirect _ _) = 2 ∧
  inst_size' _ = 1
End


(**********************************)
(*   pops leave clock unchanged   *)
(**********************************)

Theorem pop_clock:
  pop s = SOME (x,s1) ⇒ s1.clock = s.clock
Proof
  gvs [pop_def,AllCaseEqs()] \\ rw [] \\ simp []
QED

Theorem pop_n_clock:
  pop_n n s = SOME (x,s1) ⇒ s1.clock = s.clock
Proof
  gvs [pop_n_def,AllCaseEqs()] \\ rw [] \\ simp []
QED

Theorem pop_i32_clock:
  pop_i32 s = SOME (w,s1) ⇒ s1.clock = s.clock
Proof
  gvs[pop_i32_def, AllCaseEqs()] \\ rw[] \\ simp[]
QED

Definition lookup_func_tables_def:
  lookup_func_tables tbls n (w:word32) =
    case oEL n tbls of
    | NONE => NONE
    | SOME tbl => oEL (w2n w) tbl
End

Definition set_local_def:
  set_local n x (s:state) =
    if n < LENGTH s.locals then
      SOME (s with locals := LUPDATE x n s.locals)
    else NONE
End

Definition set_global_def:
  set_global n x (s:state) =
    if n < LENGTH s.globals then
      SOME (s with globals := LUPDATE x n s.globals)
    else NONE
End





(*********************************************************************************)
(*                                                                               *)
(*     Instruction semantics (hierarchically lower) - starting with Numerics     *)
(*                                                                               *)
(*********************************************************************************)

(* How a instr/op relates its operand and result *)
Inductive u_op_rel:
  (∀w. u_op_rel (Popcnt W32) (I32 w) (I32 $ popcnt w)) ∧
  (∀w. u_op_rel (Clz    W32) (I32 w) (I32 $ clz    w)) ∧
  (∀w. u_op_rel (Ctz    W32) (I32 w) (I32 $ ctz    w))
  ∧
  (∀w. u_op_rel (Popcnt W64) (I64 w) (I64 $ popcnt w)) ∧
  (∀w. u_op_rel (Clz    W64) (I64 w) (I64 $ clz    w)) ∧
  (∀w. u_op_rel (Ctz    W64) (I64 w) (I64 $ ctz    w))
  ∧
  (∀w. u_op_rel (Extend8s  W32) (I32 w) (I32 $ extend8s  w)) ∧
  (∀w. u_op_rel (Extend16s W32) (I32 w) (I32 $ extend16s w))
  ∧
  (∀w. u_op_rel (Extend8s  W64  ) (I64 w) (I64 $ extend8s  w)) ∧
  (∀w. u_op_rel (Extend16s W64  ) (I64 w) (I64 $ extend16s w)) ∧
  (∀w. u_op_rel  Extend32s        (I64 w) (I64 $ extend32s w)) ∧
  (∀w. u_op_rel (ExtendI32_ sign) (I32 w) (I64 $ sext sign $ w))
End

(* The relation is deterministic *)
Theorem u_op_rel_det:
  ∀ op x r1 r2. u_op_rel op x r1 ∧
                u_op_rel op x r2 ⇒ r1 = r2
Proof
  Cases >> Cases
  >> once_rewrite_tac [u_op_rel_cases]
  >> simp[AllCaseEqs()]
QED

(* ASKMM ASKYK *)
(* declaring a function that returns a result via (Axiom of) choice *)
Definition do_una_def:
  do_una op x = some res. u_op_rel op x res
End

(* iff between the relational & functional *)
Theorem do_una_thm:
  do_una op v = SOME res ⇔ u_op_rel op v res
Proof
  rw [do_una_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ fs []
  \\ metis_tac [u_op_rel_det]
QED

(* derive _eq & _cases for the functional via the relational *)
Theorem do_una_eq    = REWRITE_RULE [GSYM do_una_thm] u_op_rel_rules;
Theorem do_una_cases = REWRITE_RULE [GSYM do_una_thm] u_op_rel_cases;



Inductive b_op_rel:
  (∀ l r. b_op_rel (Add Int W32) (I32 l) (I32 r) (I32 $ l + r) )∧
  (∀ l r. b_op_rel (Sub Int W32) (I32 l) (I32 r) (I32 $ l - r) )∧
  (∀ l r. b_op_rel (Mul Int W32) (I32 l) (I32 r) (I32 $ l * r) )
  ∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Div_ Unsigned W32) (I32 n) (I32 d) (I32 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Rem_ Unsigned W32) (I32 n) (I32 d) (I32 $ n // d) )
  ∧
  (∀ l r. b_op_rel (And W32) (I32 l) (I32 r) (I32 $ l && r) )∧
  (∀ l r. b_op_rel (Or  W32) (I32 l) (I32 r) (I32 $ l || r) )∧
  (∀ l r. b_op_rel (Xor W32) (I32 l) (I32 r) (I32 $ l ⊕ r) )
  ∧
  (∀ w n. n <+ 32w ⇒ b_op_rel (Rotl          W32) (I32 w) (I32 n) (I32 $ w ⇆  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ b_op_rel (Rotr          W32) (I32 w) (I32 n) (I32 $ w ⇄  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ b_op_rel (Shl           W32) (I32 w) (I32 n) (I32 $ w <<  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ b_op_rel (Shr_   Signed W32) (I32 w) (I32 n) (I32 $ w >>  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ b_op_rel (Shr_ Unsigned W32) (I32 w) (I32 n) (I32 $ w >>> (w2n n)) )
  ∧
  (∀ l r. b_op_rel (Add Int W64) (I64 l) (I64 r) (I64 $ l + r) )∧
  (∀ l r. b_op_rel (Mul Int W64) (I64 l) (I64 r) (I64 $ l - r) )∧
  (∀ l r. b_op_rel (Sub Int W64) (I64 l) (I64 r) (I64 $ l * r) )
  ∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Div_ Unsigned W64) (I64 n) (I64 d) (I64 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Rem_ Unsigned W64) (I64 n) (I64 d) (I64 $ n // d) )
  ∧
  (∀ l r. b_op_rel (And W64) (I64 l) (I64 r) (I64 $ l && r) )∧
  (∀ l r. b_op_rel (Or  W64) (I64 l) (I64 r) (I64 $ l || r) )∧
  (∀ l r. b_op_rel (Xor W64) (I64 l) (I64 r) (I64 $ l ⊕ r) )
  ∧
  (∀ w n. n <+ 64w ⇒ b_op_rel (Rotl          W64) (I64 w) (I64 n) (I64 $ w ⇆  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ b_op_rel (Rotr          W64) (I64 w) (I64 n) (I64 $ w ⇄  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ b_op_rel (Shl           W64) (I64 w) (I64 n) (I64 $ w <<  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ b_op_rel (Shr_   Signed W64) (I64 w) (I64 n) (I64 $ w >>  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ b_op_rel (Shr_ Unsigned W64) (I64 w) (I64 n) (I64 $ w >>> (w2n n)) )
  ∧
  (* integer_words$word_rem *)
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Div_   Signed W32) (I32 n) (I32 d) (I32 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Rem_   Signed W32) (I32 n) (I32 d) (I32 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Div_   Signed W64) (I64 n) (I64 d) (I64 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ b_op_rel (Rem_   Signed W64) (I64 n) (I64 d) (I64 $ n // d) )
End

Theorem b_op_rel_det:
  ∀op x y r1 r2.  b_op_rel op x y r1 ∧
                  b_op_rel op x y r2 ⇒ r1 = r2
Proof
  once_rewrite_tac [b_op_rel_cases] \\ simp [] \\ rw [] \\ simp []
QED

Definition do_bin_def:
  do_bin b v1 v2 = some res. b_op_rel b v1 v2 res
End

Theorem do_bin_thm:
  do_bin b v1 v2 = SOME res ⇔ b_op_rel b v1 v2 res
Proof
  rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [b_op_rel_det]
QED

Theorem do_bin_eq    = REWRITE_RULE [GSYM do_bin_thm] b_op_rel_rules;
Theorem do_bin_cases = REWRITE_RULE [GSYM do_bin_thm] b_op_rel_cases;



Inductive cmp_op_rel:
  (* TODO check semantics of these ops *)
  (∀l r. cmp_op_rel (Eq Int W32) (I32 l) (I32 r) (b2v (l =  r)) )∧
  (∀l r. cmp_op_rel (Ne Int W32) (I32 l) (I32 r) (b2v (l <> r)) )
  ∧
  (∀l r. cmp_op_rel (Lt_  Unsigned  W32) (I32 l) (I32 r) (b2v (l <+  r)) )∧
  (∀l r. cmp_op_rel (Gt_  Unsigned  W32) (I32 l) (I32 r) (b2v (l >+  r)) )∧
  (∀l r. cmp_op_rel (Le_  Unsigned  W32) (I32 l) (I32 r) (b2v (l <=+ r)) )∧
  (∀l r. cmp_op_rel (Ge_  Unsigned  W32) (I32 l) (I32 r) (b2v (l >=+ r)) )
  ∧
  (∀l r. cmp_op_rel (Eq Int W64) (I64 l) (I64 r) (b2v (l =  r)) )∧
  (∀l r. cmp_op_rel (Ne Int W64) (I64 l) (I64 r) (b2v (l <> r)) )
  ∧
  (∀l r. cmp_op_rel (Lt_  Unsigned  W64) (I64 l) (I64 r) (b2v (l <+  r)) )∧
  (∀l r. cmp_op_rel (Gt_  Unsigned  W64) (I64 l) (I64 r) (b2v (l >+  r)) )∧
  (∀l r. cmp_op_rel (Le_  Unsigned  W64) (I64 l) (I64 r) (b2v (l <=+ r)) )∧
  (∀l r. cmp_op_rel (Ge_  Unsigned  W64) (I64 l) (I64 r) (b2v (l >=+ r)) )
  ∧
  (∀l r. cmp_op_rel (Lt_    Signed  W32) (I32 l) (I32 r) (b2v (l <  r)) )∧
  (∀l r. cmp_op_rel (Gt_    Signed  W32) (I32 l) (I32 r) (b2v (l >  r)) )∧
  (∀l r. cmp_op_rel (Le_    Signed  W32) (I32 l) (I32 r) (b2v (l <= r)) )∧
  (∀l r. cmp_op_rel (Ge_    Signed  W32) (I32 l) (I32 r) (b2v (l >= r)) )
  ∧
  (∀l r. cmp_op_rel (Lt_    Signed  W64) (I64 l) (I64 r) (b2v (l <  r)) )∧
  (∀l r. cmp_op_rel (Gt_    Signed  W64) (I64 l) (I64 r) (b2v (l >  r)) )∧
  (∀l r. cmp_op_rel (Le_    Signed  W64) (I64 l) (I64 r) (b2v (l <= r)) )∧
  (∀l r. cmp_op_rel (Ge_    Signed  W64) (I64 l) (I64 r) (b2v (l >= r)) )
End

Theorem cmp_op_rel_det:
  ∀ c x y r1 r2.  cmp_op_rel c x y r1 ∧
                  cmp_op_rel c x y r2 ⇒ r1 = r2
Proof
  once_rewrite_tac [cmp_op_rel_cases]
  \\ simp []
  \\ rw []
QED

Definition do_cmp_def:
  do_cmp c v1 v2 = some res. cmp_op_rel c v1 v2 res
End

Theorem do_cmp_thm:
  do_cmp c v1 v2 = SOME res ⇔ cmp_op_rel c v1 v2 res
Proof
  rw [do_cmp_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [cmp_op_rel_det]
QED

Theorem do_cmp_eq    = REWRITE_RULE [GSYM do_cmp_thm] cmp_op_rel_rules;
Theorem do_cmp_cases = REWRITE_RULE [GSYM do_cmp_thm] cmp_op_rel_cases;



Inductive convert_op_rel:
  ∀ w. convert_op_rel WrapI64 (I64 w) (I32 $ w2w w)
End

Theorem convert_op_rel_det:
  ∀ c x r1 r2.  convert_op_rel c x r1 ∧
                convert_op_rel c x r2 ⇒ r1 = r2
Proof
  once_rewrite_tac [convert_op_rel_cases] \\ simp [] \\ rw []
QED

Definition do_cvt_def:
  do_cvt c v = some res. convert_op_rel c v res
End

Theorem do_cvt_thm:
  do_cvt c v = SOME res ⇔ convert_op_rel c v res
Proof
  rw [do_cvt_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ fs []
  \\ metis_tac [convert_op_rel_det]
QED

Theorem do_cvt_eq    = REWRITE_RULE [GSYM do_cvt_thm] convert_op_rel_rules;
Theorem do_cvt_cases = REWRITE_RULE [GSYM do_cvt_thm] convert_op_rel_cases;



(**************************)
(*   Top level numerics   *)
(**************************)

Definition num_stk_op_def:
  num_stk_op (N_const32 Int w)     stk  = SOME (I32  w       :: stk) ∧
  num_stk_op (N_const64 Int w)     stk  = SOME (I64  w       :: stk) ∧
  num_stk_op (N_eqz W32) (I32 w :: stk) = SOME (b2v (w = 0w) :: stk) ∧
  num_stk_op (N_eqz W64) (I64 w :: stk) = SOME (b2v (w = 0w) :: stk) ∧
 (num_stk_op (N_unary   op) (v   ::stk) = case do_una op v   of NONE=>NONE| SOME x => SOME $ x::stk)∧
 (num_stk_op (N_binary  op) (l::r::stk) = case do_bin op l r of NONE=>NONE| SOME x => SOME $ x::stk)∧
 (num_stk_op (N_compare op) (l::r::stk) = case do_cmp op l r of NONE=>NONE| SOME x => SOME $ x::stk)∧
 (num_stk_op (N_convert op) (v   ::stk) = case do_cvt op v   of NONE=>NONE| SOME x => SOME $ x::stk)∧
  num_stk_op _ _ = NONE
End



(****************************)
(*     Memories - loads     *)
(****************************)

Inductive load_op_rel:
  (∀i ofs a m v  . load 4 i ofs m = (v       ,T) ⇒ load_op_rel i (Load Int W32           ofs a) m (I32 v)            )∧
  (∀i ofs a m v s. load 1 i ofs m = (v:word8 ,T) ⇒ load_op_rel i (LoadNarrow I8x16 s W32 ofs a) m (I32 $ sext s $ v) )∧
  (∀i ofs a m v s. load 2 i ofs m = (v:word16,T) ⇒ load_op_rel i (LoadNarrow I16x8 s W32 ofs a) m (I32 $ sext s $ v) )
  ∧
  (∀i ofs a m v  . load 8 i ofs m = (v       ,T) ⇒ load_op_rel i (Load Int W64           ofs a) m (I64 v)            )∧
  (∀i ofs a m v s. load 1 i ofs m = (v:word8 ,T) ⇒ load_op_rel i (LoadNarrow I8x16 s W64 ofs a) m (I64 $ sext s $ v) )∧
  (∀i ofs a m v s. load 2 i ofs m = (v:word16,T) ⇒ load_op_rel i (LoadNarrow I16x8 s W64 ofs a) m (I64 $ sext s $ v) )∧
  (∀i ofs a m v s. load 4 i ofs m = (v:word32,T) ⇒ load_op_rel i (LoadNarrow32     s     ofs a) m (I64 $ sext s $ v) )
End

Theorem load_op_rel_det:
  ∀i op m r1 r2. load_op_rel i op m r1 ∧
                 load_op_rel i op m r2 ⇒ r1 = r2
Proof
  once_rewrite_tac [load_op_rel_cases]
  \\ simp [] \\ rw []
    >> gvs []
QED

Definition do_ld_def:
  do_ld i op m = some res. load_op_rel i op m res
End

Theorem do_ld_thm:
  do_ld i op m = SOME res ⇔ load_op_rel i op m res
Proof
  rw [do_ld_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [load_op_rel_det]
QED

Theorem do_ld_eq    = REWRITE_RULE [GSYM do_ld_thm] load_op_rel_rules;
Theorem do_ld_cases = REWRITE_RULE [GSYM do_ld_thm] load_op_rel_cases;



(*****************************)
(*     Memories - stores     *)
(*****************************)

Inductive store_op_rel:
  (∀x i ofs a m m'. store      x         i ofs m = (m',T) ⇒ store_op_rel (I32 x) i (Store        Int  W32 ofs a) m m')∧
  (∀x i ofs a m m'. store (w2w x:word8 ) i ofs m = (m',T) ⇒ store_op_rel (I32 x) i (StoreNarrow I8x16 W32 ofs a) m m')∧
  (∀x i ofs a m m'. store (w2w x:word16) i ofs m = (m',T) ⇒ store_op_rel (I32 x) i (StoreNarrow I16x8 W32 ofs a) m m')
  ∧
  (∀x i ofs a m m'. store      x         i ofs m = (m',T) ⇒ store_op_rel (I64 x) i (Store        Int  W64 ofs a) m m')∧
  (∀x i ofs a m m'. store (w2w x:word8 ) i ofs m = (m',T) ⇒ store_op_rel (I64 x) i (StoreNarrow I8x16 W64 ofs a) m m')∧
  (∀x i ofs a m m'. store (w2w x:word16) i ofs m = (m',T) ⇒ store_op_rel (I64 x) i (StoreNarrow I16x8 W64 ofs a) m m')∧
  (∀x i ofs a m m'. store (w2w x:word32) i ofs m = (m',T) ⇒ store_op_rel (I64 x) i (StoreNarrow32         ofs a) m m')
End

Theorem store_op_rel_det:
  ∀x i op m r1 r2.  store_op_rel x i op m r1 ∧
                    store_op_rel x i op m r2 ⇒ r1 = r2
Proof
  once_rewrite_tac [store_op_rel_cases]
  \\ simp [] \\ rw []
    >> fs []
QED

Definition do_st_def:
  do_st x i op m = some res. store_op_rel x i op m res
End

Theorem do_st_thm:
  do_st x i op m = SOME res ⇔ store_op_rel x i op m res
Proof
  rw [do_st_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ fs []
  \\ metis_tac [store_op_rel_det]
QED

Theorem do_st_eq    = REWRITE_RULE [GSYM do_st_thm] store_op_rel_rules;
Theorem do_st_cases = REWRITE_RULE [GSYM do_st_thm] store_op_rel_cases;





(*******************************)
(*                             *)
(*     Top level Semantics     *)
(*                             *)
(*******************************)

Overload inv[local] = “λ s. (RInvalid,s)”

Definition exec_def:
  (exec (Unreachable:instr) (s:state) = (RTrap,s) : result # state
  ) ∧
  (exec Nop s = (RNormal,s)
  ) ∧
  (exec (Block bt body) s =
    let orig_stk = s.stack in
    let (res, s) = exec_list body (s with stack := [])
    in
    case res of
    | RBreak (SUC l) => (RBreak l, s)
    | RBreak 0 => ( case (bt,s.stack) of
                    | (BlkNil  , _   ) => (RNormal, s with stack :=     orig_stk)
                    | (BlkVal _, v::_) => (RNormal, s with stack := v:: orig_stk)
                    | (_,_)            => inv s)
    | RNormal  => ( case (bt,s.stack) of
                    | (BlkNil  , [] ) => (RNormal, s with stack :=     orig_stk)
                    | (BlkVal _, [v]) => (RNormal, s with stack := v:: orig_stk)
                    | ( _      , _  ) => inv s)
    | _ => (res,s)
  ) ∧
  (exec (Loop bt body) s =
    let orig_stk = s.stack                          in
    let s1       = s with stack := []               in
    let (res, s) = fix_clock s1 (exec_list body s1) in
    let s_tick   = s with clock := s.clock - 1
    in
    case res of
    | RBreak (SUC l) => (RBreak l, s)
    | RBreak 0 => if s.clock = 0 then (RTimeout,s) else
                  ( case (bt,s.stack) of
                    | (BlkNil  , _ )   => exec (Loop bt body)  s_tick
                    | (BlkVal _, v::_) => exec (Loop bt body) (s_tick with stack := v:: orig_stk)
                    | (_,_)            => inv s
                  )
    | RNormal =>  if s.clock = 0 then (RTimeout,s) else
                  ( case (bt,s.stack) of
                    | (BlkNil  , [ ]) => exec (Loop bt body)  s_tick
                    | (BlkVal _, [v]) => exec (Loop bt body) (s_tick with stack := v:: orig_stk)
                    | (_,_)           => inv s
                  )
    | _ => (res, s)
  ) ∧
  (exec (If bt bl br) s =
    case pop s     of NONE => inv s | SOME (c,s) =>
    case nonzero c of NONE => inv s | SOME t     =>
      exec (Block bt (if t then bl else br)) s
  ) ∧
  (exec (Br w) s =   (RBreak (w2n w), s)
  ) ∧
  (exec (BrIf w) s =
    case pop s     of NONE => inv s | SOME (c,s) =>
    case nonzero c of NONE => inv s | SOME t     =>
      if t then (RBreak (w2n w), s) else (RNormal, s)
  ) ∧
  (exec (BrTable table default) s =
    case pop s      of NONE => inv s | SOME (x,s) =>
    case dest_i32 x of NONE => inv s | SOME w     =>
      (RBreak (case oEL (w2n w) table of NONE => w2n default | SOME i => w2n i), s)
  ) ∧
  (exec Return s =   (RReturn, s)
  ) ∧
  (exec (ReturnCall fi) s =
    case oEL (w2n fi) s.funcs      of NONE => inv s | SOME f          =>
    case oEL (w2n f.ftype) s.types of NONE => inv s | SOME (ins,outs) =>
    let np = LENGTH ins in
    let nr = LENGTH outs in
    case pop_n np s of NONE => inv s | SOME (args,s) =>
    let init_locals = args ++ MAP init_val_of ins in
    if s.clock = 0 then (RTimeout,s) else
    let s_call = s with <|clock:= s.clock - 1; stack:=[]; locals:=init_locals|> in
    (* real WASM treats the body as wrapped in a Block *)
    let (res, s1) = fix_clock s_call (exec_list f.body s_call) in
      case res of
      | RNormal =>
          if LENGTH s1.stack ≠ nr then (RInvalid,s1) else
            (RReturn, s with stack := s1.stack)
      | RReturn =>
          if LENGTH s1.stack < nr then (RInvalid,s1) else
            (RReturn, s with stack := TAKE nr s1.stack)
      | RBreak _ => (RInvalid, s1)
      | _ => (res, s1)
  ) ∧
  (exec (ReturnCallIndirect n ft) s =
    case pop s                                        of NONE=>inv s| SOME (x,s) =>
    case dest_i32 x                                   of NONE=>inv s| SOME w     =>
    case lookup_func_tables [s.func_tables] (w2n n) w of NONE=>inv s| SOME fi    =>
    case oEL fi s.funcs                               of NONE=>inv s| SOME f     =>
      exec (ReturnCall (n2w fi)) s
  ) ∧
  (exec (Call fi) s =
    case oEL (w2n fi) s.funcs      of NONE => inv s | SOME f          =>
    case oEL (w2n f.ftype) s.types of NONE => inv s | SOME (ins,outs) =>
    let np = LENGTH ins in
    let nr = LENGTH outs in
    case pop_n np s of NONE => inv s | SOME (args,s) =>
    let init_locals = args ++ MAP init_val_of ins in
    if s.clock = 0 then (RTimeout,s) else
    let s_call = s with <|clock:= s.clock - 1; stack:=[]; locals:=init_locals|> in
    (* real WASM treats the body as wrapped in a Block *)
    let (res, s1) = fix_clock s_call (exec_list f.body s_call) in
      case res of
      | RNormal =>
          if LENGTH s1.stack ≠ nr then (RInvalid,s1) else
            (RNormal, s with stack := s1.stack ++ s.stack)
      | RReturn =>
          if LENGTH s1.stack < nr then (RInvalid,s1) else
            (RNormal, s with stack := TAKE nr s1.stack ++ s.stack)
      | RBreak _ => (RInvalid, s1)
      | _ => (res, s1)
  ) ∧
  (exec (CallIndirect n ft) s =
    case pop s      of NONE => inv s | SOME (x,s) =>
    case dest_i32 x of NONE => inv s | SOME w     =>
    (* TODO we removed one layer of indirection *)
    (* we only use one func table *)
    case lookup_func_tables [s.func_tables] (w2n n) w of NONE => inv s | SOME fi =>
      exec (Call (n2w fi)) s
  ) ∧
  (****************)
  (*   Numerics   *)
  (****************)
  (exec (Numeric op) s =
    case num_stk_op op s.stack of NONE => inv s | SOME stk =>
      (RNormal, s with stack := stk)
  ) ∧
  (*******************)
  (*   Parametrics   *)
  (*******************)
  (exec (Parametric Drop) s =
    case pop s of NONE => inv s | SOME (_,s) =>
      (RNormal, s)
  ) ∧
  (exec (Parametric Select) s =
    case pop s     of NONE => inv s | SOME (c   ,s) =>
    case pop s     of NONE => inv s | SOME (val2,s) =>
    case pop s     of NONE => inv s | SOME (val1,s) =>
    case nonzero c of NONE => inv s | SOME b        =>
      (RNormal, push (if b then val1 else val2) s)
  ) ∧
  (*****************)
  (*   Variables   *)
  (*****************)
  (exec (Variable $ LocalGet n) s =
    case oEL (w2n n) s.locals of NONE => inv s | SOME x =>
      (RNormal, push x s)
  ) ∧
  (exec (Variable $ LocalSet n) s =
    case pop s                 of NONE => inv s | SOME (x,s) =>
    case set_local (w2n n) x s of NONE => inv s | SOME s     =>
      (RNormal,s)
  ) ∧
  (exec (Variable $ LocalTee n) s =
    case pop s                 of NONE => inv s | SOME (x,_) =>
    case set_local (w2n n) x s of NONE => inv s | SOME s     =>
      (RNormal,s)
  ) ∧
  (exec (Variable $ GlobalGet n) s =
    case oEL (w2n n) s.globals of NONE => inv s | SOME x =>
      (RNormal, push x s)
  ) ∧
  (exec (Variable $ GlobalSet n) s =
    case pop s                  of NONE => inv s | SOME (x,s) =>
    case set_global (w2n n) x s of NONE => inv s | SOME s     =>
      (RNormal,s)
  ) ∧
  (**********************)
  (*   Memory - loads   *)
  (**********************)
  (exec (MemRead op) s =
    case pop_i32 s           of NONE =>  inv   s  | SOME (i,s) =>
    case do_ld i op s.memory of NONE => (RTrap,s) | SOME v     =>
      (RNormal, s with stack := v :: s.stack)
  ) ∧
  (***********************)
  (*   Memory - stores   *)
  (***********************)
  (exec (MemWrite op) s = (* TODO: fix *)
    case pop s                 of NONE =>  inv   s  | SOME (x,s) =>
    case pop_i32 s             of NONE =>  inv   s  | SOME (i,s) =>
    case do_st x i op s.memory of NONE => (RTrap,s) | SOME  m'   =>
      (RNormal, s with memory := m')
  ) ∧
  (exec_list ([]:instr list) (s:state) = (RNormal, s)
  ) ∧
  (exec_list (b::bs) s =
    let (res,s) = fix_clock s (exec b s) in
    case res of
    | RNormal => exec_list bs s
    | _       => (res,s)
  )
Termination
  WF_REL_TAC ‘inv_image (measure I LEX measure I) $ λx. case x of
               | INL (i ,s) => (s.clock, inst_size' i)
               | INR (is,s) => (s.clock, list_size inst_size' is)’
  \\ gvs [inst_size'_def]
  \\ rw [SF ETA_ss]
  \\ imp_res_tac pop_clock
  \\ imp_res_tac pop_n_clock
  \\ imp_res_tac pop_i32_clock
  \\ imp_res_tac fix_clock_IMP
  \\ gvs [fix_clock_def]
End





Triviality pop_clock:
  pop s = SOME (r,s1) ⇒ s1.clock = s.clock
Proof
  rw [oneline pop_def, AllCaseEqs()] \\ fs []
QED

Triviality pop_n_clock:
  ∀n s. pop_n n s = SOME (r,s1) ⇒ s1.clock = s.clock
Proof
  Induct \\ gvs [pop_n_def] \\ rw [] \\ gvs []
QED

Triviality fix_clock_leq:
  fix_clock s input = (output,s1) ⇒ s1.clock ≤ s.clock
Proof
  Cases_on ‘input’ \\ rw [fix_clock_def] \\ fs []
QED

Theorem exec_clock_thm:
  (∀e s res s1. exec e s = (res,s1) ⇒ s1.clock ≤ s.clock) ∧
  (∀e s res s1. exec_list e s = (res,s1) ⇒ s1.clock ≤ s.clock)
Proof
  ho_match_mp_tac exec_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once exec_def,AllCaseEqs()] \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac fix_clock_leq
  \\ imp_res_tac pop_clock
  \\ imp_res_tac pop_n_clock
  \\ imp_res_tac pop_i32_clock
  \\ gvs [oneline nonzero_def,AllCaseEqs(),push_def,set_local_def,set_global_def]
QED

Triviality fix_clock_exec:
  fix_clock s (exec e s) = exec e s ∧
  fix_clock s (exec_list es s) = exec_list es s
Proof
  Cases_on ‘exec e s’
  \\ Cases_on ‘exec_list es s’
  \\ imp_res_tac exec_clock_thm
  \\ fs [fix_clock_def,fetch "-" "state_component_equality",MIN_DEF]
QED

Theorem exec_def[allow_rebind] = exec_def |> REWRITE_RULE [fix_clock_exec];
Theorem exec_ind[allow_rebind] = exec_ind |> REWRITE_RULE [fix_clock_exec];
