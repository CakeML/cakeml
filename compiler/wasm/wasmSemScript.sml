(*
  WebAssembly (Wasm) semantics
*)
open preamble wasmLangTheory;
open miscOpsTheory;
open wordsTheory wordsLib;
(* open integer_wordsTheory;
integer_words$word_rem *)

val _ = new_theory "wasmSem";

Type memory = “:word8 list”
Overload b2w[local] = “λ (b:bool). if b then 1w:α word else 0w”

Definition sext_def:
  sext   Signed = sw2sw ∧
  sext Unsigned = w2w
End

Datatype: value
  = I32 word32
  | I64 word64
End


Datatype:
  state =
  <|
    clock   : num;
    stack   : value list;
    locals  : value list;
    globals : value list;
    memory  : word8 list;
    types   : (valtype list # valtype list) list;
    funcs   : func list;
    func_tables : num list ;
  |>
End

Datatype:
  result = (* TODO document *)
    RNormal
  | RBreak num
  | RReturn
  | RTrap
  | RInvalid (* failures from "Assert: due to validation ..." *)
  | RTimeout
End

(* TODO fix *)
(* Returns the function type for tb *)
Definition tb_tf_def:
  tb_tf types (Tbf n) = oEL n types
End

(* QQ what is T_i32? *)
Definition init_val_of_def:
  init_val_of T_i32 = I32 0w ∧
  init_val_of T_i64 = I64 0w
End

Definition nonzero_def:
  nonzero (I32 n) = SOME (n ≠ 0w) ∧
  nonzero (I64 n) = NONE
End

Definition pop_def:
  pop s =
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
  push x s = s with stack := x :: s.stack
End

Definition dest_i32_def:
  dest_i32 (I32 w) = SOME w ∧
  dest_i32 _ = NONE
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

(********************)
(*                  *)
(*     Numerics     *)
(*                  *)
(********************)

Inductive unary_op_rel:
  (∀ w. unary_op_rel (Popcnt    W32) (I32 w) (I32 $ popcnt w)) ∧
  (∀ w. unary_op_rel (Clz       W32) (I32 w) (I32 $ clz    w)) ∧
  (∀ w. unary_op_rel (Ctz       W32) (I32 w) (I32 $ ctz    w)) ∧

  (∀ w. unary_op_rel (Popcnt    W64) (I64 w) (I64 $ popcnt w)) ∧
  (∀ w. unary_op_rel (Clz       W64) (I64 w) (I64 $ clz    w)) ∧
  (∀ w. unary_op_rel (Ctz       W64) (I64 w) (I64 $ ctz    w)) ∧


  (∀ w. unary_op_rel (Extend8s  W32) (I32 w) (I32 $ sw2sw $ (w2w w):word8 )) ∧
  (∀ w. unary_op_rel (Extend16s W32) (I32 w) (I32 $ sw2sw $ (w2w w):word16)) ∧

  (∀ w. unary_op_rel (Extend8s  W64  ) (I64 w) (I64 $ sw2sw $ (w2w w):word8 )) ∧
  (∀ w. unary_op_rel (Extend16s W64  ) (I64 w) (I64 $ sw2sw $ (w2w w):word16)) ∧
  (∀ w. unary_op_rel  Extend32_s       (I64 w) (I64 $ sw2sw $ (w2w w):word32)) ∧
  (∀ w. unary_op_rel (ExtendI32_ sign) (I32 w) (I64 $ sext sign $ w))
End

Theorem unary_op_rel_det:
  ∀ op v r1 r2. unary_op_rel op v r1 ∧ unary_op_rel op v r2 ==> r1 = r2
Proof
  (* once_rewrite_tac [unary_op_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
  cheat
QED

Definition do_una_def:
  do_una op v = some res. unary_op_rel op v res
End

Theorem do_una_thm:
  do_una op v = SOME res ⇔ unary_op_rel op v res
Proof cheat
  (* rw [do_una_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED

Theorem do_una_eq    = REWRITE_RULE [GSYM do_una_thm] unary_op_rel_rules;
Theorem do_una_cases = REWRITE_RULE [GSYM do_una_thm] unary_op_rel_cases;


Inductive binop_rel:
  (∀ l r. binop_rel (Add Int W32) (I32 l) (I32 r) (I32 $ l + r) )∧
  (∀ l r. binop_rel (Sub Int W32) (I32 l) (I32 r) (I32 $ l - r) )∧
  (∀ l r. binop_rel (Mul Int W32) (I32 l) (I32 r) (I32 $ l * r) )∧

  (∀ n d. d ≠ 0w ⇒ binop_den (Div_ Unsigned W32) (I32 n) (I32 d) (I32 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ binop_den (Rem_ Unsigned W32) (I32 n) (I32 d) (I32 $ n // d) )∧

  (∀ l r. binop_rel (And W32) (I32 l) (I32 r) (I32 $ l && r) )∧
  (∀ l r. binop_rel (Or  W32) (I32 l) (I32 r) (I32 $ l || r) )∧
  (∀ l r. binop_rel (Xor W32) (I32 l) (I32 r) (I32 $ l ⊕ r) )∧

  (∀ w n. n <+ 32w ⇒ binop_rel (Rotl          W32) (I32 w) (I32 n) (I32 $ w ⇆  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ binop_rel (Rotr          W32) (I32 w) (I32 n) (I32 $ w ⇄  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ binop_rel (Shw           W32) (I32 w) (I32 n) (I32 $ w <<  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ binop_rel (Shn_   Signed W32) (I32 w) (I32 n) (I32 $ w >>  (w2n n)) )∧
  (∀ w n. n <+ 32w ⇒ binop_rel (Shn_ Unsigned W32) (I32 w) (I32 n) (I32 $ w >>> (w2n n)) )∧


  (∀ l r. binop_rel (Add Int W64) (I64 l) (I64 r) (I64 $ l + r) )∧
  (∀ l r. binop_rel (Mul Int W64) (I64 l) (I64 r) (I64 $ l - r) )∧
  (∀ l r. binop_rel (Sub Int W64) (I64 l) (I64 r) (I64 $ l * r) )∧

  (∀ n d. d ≠ 0w ⇒ binop_rel (Div_ Unsigned W64) (I64 n) (I64 d) (I64 $ n // d) )∧
  (∀ n d. d ≠ 0w ⇒ binop_rel (Rem_ Unsigned W64) (I64 n) (I64 d) (I64 $ n // d) )∧

  (∀ l r. binop_rel (And W64) (I64 l) (I64 r) (I64 $ l && r) )∧
  (∀ l r. binop_rel (Or  W64) (I64 l) (I64 r) (I64 $ l || r) )∧
  (∀ l r. binop_rel (Xor W64) (I64 l) (I64 r) (I64 $ l ⊕ r) )∧

  (∀ w n. n <+ 64w ⇒ binop_rel (Rotl          W64) (I64 w) (I64 n) (I64 $ w ⇆  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ binop_rel (Rotr          W64) (I64 w) (I64 n) (I64 $ w ⇄  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ binop_rel (Shl           W64) (I64 w) (I64 n) (I64 $ w <<  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ binop_rel (Shr_   Signed W64) (I64 w) (I64 n) (I64 $ w >>  (w2n n)) )∧
  (∀ w n. n <+ 64w ⇒ binop_rel (Shr_ Unsigned W64) (I64 w) (I64 n) (I64 $ w >>> (w2n n)) )∧

  (* integer_words$word_rem *)
  (∀ n d. d ≠ 0w ⇒ binop_den (Div_   Signed W32) (I32 n) (I32 d) (I32 $ n // d) )∧ (* TODO *)
  (∀ n d. d ≠ 0w ⇒ binop_den (Rem_   Signed W32) (I32 n) (I32 d) (I32 $ n // d) )∧ (* TODO *)
  (∀ n d. d ≠ 0w ⇒ binop_rel (Div_   Signed W64) (I64 n) (I64 d) (I64 $ n // d) )∧ (* TODO *)
  (∀ n d. d ≠ 0w ⇒ binop_rel (Rem_   Signed W64) (I64 n) (I64 d) (I64 $ n // d) ) (* TODO *)
End

Theorem binop_rel_det:
  ∀b v1 v2 r1 r2. binop_rel b v1 v2 r1 ∧ binop_rel b v1 v2 r2 ⇒ r1 = r2
Proof
  cheat
  (* once_rewrite_tac [binop_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
QED

Definition do_bin_def:
  do_bin b v1 v2 = some res. binop_rel b v1 v2 res
End

Theorem do_bin_thm:
  do_bin b v1 v2 = SOME res ⇔ binop_rel b v1 v2 res
Proof
  cheat
  (* rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED

(* INVARIANT - changes to ops shouldn't break this *)
Theorem do_bin_eq = REWRITE_RULE [GSYM do_bin_thm] binop_rel_rules;
Theorem do_bin_cases = REWRITE_RULE [GSYM do_bin_thm] binop_rel_cases;

Inductive compare_op_rel:

  (∀ l r. compare_op_rel (Eq Int W32) (I32 l) (I32 r) (I32 $ b2w (l =  r)) )∧
  (∀ l r. compare_op_rel (Ne Int W32) (I32 l) (I32 r) (I32 $ b2w (l <> r)) )∧

  (∀ l r. compare_op_rel (Lt_  Unsigned  W32) (I32 l) (I32 r) (I32 $ b2w (l <+  r)) )∧ (* TODO check in HOL i *)
  (∀ l r. compare_op_rel (Gt_  Unsigned  W32) (I32 l) (I32 r) (I32 $ b2w (l >+  r)) )∧
  (∀ l r. compare_op_rel (Le_  Unsigned  W32) (I32 l) (I32 r) (I32 $ b2w (l <=+ r)) )∧
  (∀ l r. compare_op_rel (Ge_  Unsigned  W32) (I32 l) (I32 r) (I32 $ b2w (l >=+ r)) )∧

  (∀ l r. compare_op_rel (Eq Int W64) (I64 l) (I64 r) (I64 $ b2w (l =  r)) )∧
  (∀ l r. compare_op_rel (Ne Int W64) (I64 l) (I64 r) (I64 $ b2w (l <> r)) )∧

  (∀ l r. compare_op_rel (Lt_  Unsigned  W64) (I64 l) (I64 r) (I64 $ b2w (l <+  r)) )∧
  (∀ l r. compare_op_rel (Gt_  Unsigned  W64) (I64 l) (I64 r) (I64 $ b2w (l >+  r)) )∧
  (∀ l r. compare_op_rel (Le_  Unsigned  W64) (I64 l) (I64 r) (I64 $ b2w (l <=+ r)) )∧
  (∀ l r. compare_op_rel (Ge_  Unsigned  W64) (I64 l) (I64 r) (I64 $ b2w (l >=+ r)) )∧



  (∀ l r. compare_op_rel (Lt_    Signed  W32) (I32 l) (I32 r) (I32 $ b2w (l <  r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Gt_    Signed  W32) (I32 l) (I32 r) (I32 $ b2w (l >  r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Le_    Signed  W32) (I32 l) (I32 r) (I32 $ b2w (l <= r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Ge_    Signed  W32) (I32 l) (I32 r) (I32 $ b2w (l >= r)) )∧ (* TODO *)

  (∀ l r. compare_op_rel (Lt_    Signed  W64) (I64 l) (I64 r) (I64 $ b2w (l <  r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Gt_    Signed  W64) (I64 l) (I64 r) (I64 $ b2w (l >  r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Le_    Signed  W64) (I64 l) (I64 r) (I64 $ b2w (l <= r)) )∧ (* TODO *)
  (∀ l r. compare_op_rel (Ge_    Signed  W64) (I64 l) (I64 r) (I64 $ b2w (l >= r)) )  (* TODO *)
End

Theorem compare_op_rel_det:
  ∀ c v1 v2 r1 r2. compare_op_rel c v1 v2 r1 ∧ compare_op_rel c v1 v2 r2 ==> r1 = r2
Proof
  cheat
  (* once_rewrite_tac [compare_op_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
QED


Definition do_cmp_def:
  do_cmp c v1 v2 = some res. compare_op_rel c v1 v2 res
End

Theorem do_cmp_thm:
  do_cmp c v1 v2 = SOME res ⇔ compare_op_rel c v1 v2 res
Proof
  cheat
  (* rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED

(* INVARIANT - changes to ops shouldn't break this *)
Theorem do_cmp_eq    = REWRITE_RULE [GSYM do_cmp_thm] compare_op_rel_rules;
Theorem do_cmp_cases = REWRITE_RULE [GSYM do_cmp_thm] compare_op_rel_cases;


Inductive convert_op_rel:
  ∀ w. convert_op_rel WrapI64 (I64 w) (I32 $ w2w w)
End

Definition convert_op_def:
  do_cvt c v = some res. convert_op_rel c v res
End

Theorem convert_op_rel_det:
  ∀ c v r1 r2. convert_op_rel c v r1 ∧ convert_op_rel c v r2 ==> r1 = r2
Proof
  cheat
  (* once_rewrite_tac [convert_op_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
QED


Definition do_cvt_def:
  do_cvt c v = some res. convert_op_rel c v res
End

Theorem do_cvt_thm:
  do_cvt c v = SOME res ⇔ convert_op_rel c v res
Proof
  cheat
  (* rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED

(* INVARIANT - changes to ops shouldn't break this *)
Theorem do_cvt_eq    = REWRITE_RULE [GSYM do_cvt_thm] convert_op_rel_rules;
Theorem do_cvt_cases = REWRITE_RULE [GSYM do_cvt_thm] convert_op_rel_cases;


Definition num_stk_op_def:
  num_stk_op (N_const32 Int w) stack = SOME (I32 w :: stack) ∧
  num_stk_op (N_const64 Int w) stack = SOME (I64 w :: stack) ∧
  num_stk_op (N_eqz W32) (I32 w ::stack) = SOME (I32 (b2w (w = 0w)) :: stack) ∧
  num_stk_op (N_eqz W64) (I64 w ::stack) = SOME (I64 (b2w (w = 0w)) :: stack) ∧
 (num_stk_op (N_unary   op) (v   ::stack) = case do_una op v   of NONE=>NONE| SOME x => SOME (x::stack))∧
 (num_stk_op (N_binary  op) (l::r::stack) = case do_bin op l r of NONE=>NONE| SOME x => SOME (x::stack))∧
 (num_stk_op (N_compare op) (l::r::stack) = case do_cmp op l r of NONE=>NONE| SOME x => SOME (x::stack))∧
 (num_stk_op (N_convert op) (v   ::stack) = case do_cvt op v   of NONE=>NONE| SOME x => SOME (x::stack))
End



Inductive load_op_rel:
  (∀ ofs al m v. load 4 ofs al m = (v,T) ⇒ load_op_rel (Load Int W32 ofs al) m (I32 v) )∧
  (* Why does the following case need the type annotation for v, but not the preceeding case??? *)
  (∀ ofs al m v s. load 1 ofs al m = (v:word8 ,T) ⇒ load_op_rel (LoadNarrow I8x16 s W32 ofs al) m (I32 $ sext s $ v) )∧
  (∀ ofs al m v s. load 2 ofs al m = (v:word16,T) ⇒ load_op_rel (LoadNarrow I16x8 s W32 ofs al) m (I32 $ sext s $ v) )∧

  (∀ ofs al m v. load 8 ofs al m = (v,T) ⇒ load_op_rel (Load Int W64 ofs al) m (I64 v) )∧

  (∀ ofs al m v s. load 1 ofs al m = (v:word8 ,T) ⇒ load_op_rel (LoadNarrow I8x16 s W64 ofs al) m (I64 $ sext s $ v) )∧
  (∀ ofs al m v s. load 2 ofs al m = (v:word16,T) ⇒ load_op_rel (LoadNarrow I16x8 s W64 ofs al) m (I64 $ sext s $ v) )∧
  (∀ ofs al m v s. load 4 ofs al m = (v:word32,T) ⇒ load_op_rel (LoadNarrow32     s     ofs al) m (I64 $ sext s $ v) )
End

Theorem load_op_rel_det:
  ∀ op m r1 r2. load_op_rel op m r1 ∧ load_op_rel op m r2 ==> r1 = r2
Proof
  cheat
  (* once_rewrite_tac [load_op_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
QED


Definition do_ld_def:
  do_ld op m = some res. load_op_rel op m res
End

Theorem do_ld_thm:
  do_ld op m = SOME res ⇔ load_op_rel op m res
Proof
  cheat
  (* rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED

(* INVARIANT - changes to ops shouldn't break this *)
Theorem do_ld_eq    = REWRITE_RULE [GSYM do_ld_thm] load_op_rel_rules;
Theorem do_ld_cases = REWRITE_RULE [GSYM do_ld_thm] load_op_rel_cases;

(* Parser complains there's a free variable in the RHS *)
(* Inductive store_op_rel:
  (∀ ofs al x m m'. store       x          ofs al m = (m':memory,T) ⇒ store_op rel (Store        Int  W32 ofs al) (I32 x) m m')
  (* (∀ ofs al x m m'. store ((w2w x):word8 ) ofs al m = (m',T) ⇒ store_op rel (StoreNarrow I8x16 W32 ofs al) (I32 x) m m')∧
  (∀ ofs al x m m'. store ((w2w x):word16) ofs al m = (m',T) ⇒ store_op rel (StoreNarrow I16x8 W32 ofs al) (I32 x) m m')∧

  (∀ ofs al x m m'. store       x          ofs al m = (m',T) ⇒ store_op rel (Store        Int  W64 ofs al) (I64 x) m m')∧
  (∀ ofs al x m m'. store ((w2w x):word8 ) ofs al m = (m',T) ⇒ store_op rel (StoreNarrow I8x16 W64 ofs al) (I64 x) m m')∧
  (∀ ofs al x m m'. store ((w2w x):word16) ofs al m = (m',T) ⇒ store_op rel (StoreNarrow I16x8 W64 ofs al) (I64 x) m m')∧
  (∀ ofs al x m m'. store ((w2w x):word32) ofs al m = (m',T) ⇒ store_op rel (StoreNarrow32         ofs al) (I64 x) m m') *)
End *)

(* Theorem store_op_rel_det:
  ∀ op m r1 r2. store_op_rel op m r1 ∧ store_op_rel op m r2 ==> r1 = r2
Proof
  cheat
  (* once_rewrite_tac [store_op_rel_cases] \\ simp [] \\ rw [] \\ simp [] *)
QED *)


(* Definition do_st_def:
  do_st op m = some res. store_op_rel op m res
End *)

(* Theorem do_st_thm:
  do_st op m = SOME res ⇔ store_op_rel op m res
Proof
  cheat
  (* rw [do_bin_def] \\ DEEP_INTRO_TAC some_intro
  \\ fs [] \\ metis_tac [binop_rel_det] *)
QED *)

(* INVARIANT - changes to ops shoustn't break this *)
(* Theorem do_st_eq    = REWRITE_RULE [GSYM do_st_thm] store_op_rel_rules;
Theorem do_st_cases = REWRITE_RULE [GSYM do_st_thm] store_op_rel_cases; *)


(* Definition mem_op_def:
  mem_op ()


End *)

Definition exec_load_def:
  exec_load res_t size_ext addr memory = ARB
End

Definition exec_store_def:
  exec_store res_t size_ext addr memory = ARB
End

Definition exec_def:
  (exec Unreachable s = (RTrap,s)) ∧
  (exec Nop s = (RNormal,s)) ∧
  (exec Drop s =
    case pop s of NONE => (RInvalid, s) | SOME (_,s) => (RNormal, s)) ∧
  (exec Select s =
    case pop s of NONE => (RInvalid, s) | SOME (c,s) =>
    case pop s of NONE => (RInvalid, s) | SOME (val2,s) =>
    case pop s of NONE => (RInvalid, s) | SOME (val1,s) =>
    case nonzero c of NONE => (RInvalid, s) | SOME b =>
    (RNormal, push (if b then val1 else val2) s)
  ) ∧
  (exec (Block tb b) s =
    case tb_tf s.types tb of NONE => (RInvalid,s) | SOME (mts,nts) =>
    let m = LENGTH mts in
    let n = LENGTH nts in
    if LENGTH s.stack < m then (RInvalid,s) else
    let stack0 = s.stack in
    let s1 = s with stack:=TAKE m stack0 in
    let (res, s) = exec_list b s1 in
    case res of
      RBreak 0 =>
      if LENGTH s.stack < n then (RInvalid,s) else
      (RNormal, (s with stack := (TAKE n s.stack) ++ (DROP m stack0)))
    | RBreak (SUC l) => (RBreak l, s)
    | RNormal =>
      if LENGTH s.stack ≠ n then (RInvalid,s) else
      (RNormal, (s with stack := s.stack ++ (DROP m stack0)))
    | _ => (res, s)
  ) ∧
  (exec (Loop tb b) s =
    case tb_tf s.types tb of NONE => (RInvalid,s) | SOME (mts,nts) =>
    let m = LENGTH mts in
    let n = LENGTH nts in
    if LENGTH s.stack < m then (RInvalid,s) else
    let stack0 = s.stack in
    let s1 = s with stack:=TAKE m stack0 in
    let (res, s) = fix_clock s1 (exec_list b s1) in
    case res of
      RBreak 0 =>
      if LENGTH s.stack < n then (RInvalid,s) else
      if s.clock = 0 then (RTimeout,s) else
        exec (Loop tb b) (s with <| stack := (TAKE n s.stack) ++ (DROP m stack0);
                                    clock := s.clock - 1|>)
    | RBreak (SUC l) => (RBreak l, s)
    | RNormal =>
      if LENGTH s.stack ≠ n then (RInvalid,s) else
      (RNormal, (s with stack := s.stack ++ (DROP m stack0)))
    | _ => (res, s)
  ) ∧
  (exec (If tb bl br) s =
    case pop s of NONE => (RInvalid,s) | SOME (c,s) =>
    case nonzero c of NONE => (RInvalid,s) | SOME t =>
    exec (Block tb (if t then bl else br)) s
  ) ∧
  (exec (Br n) s = (RBreak n, s)) ∧
  (exec (BrIf n) s =
    case pop s of NONE => (RInvalid,s) | SOME (c,s) =>
    case nonzero c of NONE => (RInvalid,s) | SOME t =>
    if t then (RBreak n, s) else (RNormal, s)
  ) ∧
  (exec (BrTable table default) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    (RBreak (case oEL (w2n w) table of NONE => default | SOME i => i), s)
  ) ∧
  (exec Return s = (RReturn, s)) ∧
  (exec (Call fi) s =
    case oEL fi s.funcs of NONE => (RInvalid,s) | SOME f =>
    let np = LENGTH (FST f.type) in
    let nr = LENGTH (SND f.type) in
    case pop_n np s of NONE => (RInvalid,s) | SOME (args,s) =>
    let init_locals = args ++ MAP init_val_of f.types_of_locals in
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
  (exec (CallIndirect n tf) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    (* TODO we removed one layer of indirection *)
    (* we only use one func table *)
    case lookup_func_tables s.func_tables n w of NONE => (RInvalid,s) | SOME fi =>
    case oEL fi s.funcs of NONE => (RInvalid,s) | SOME f =>
    if f.type ≠ tf then (RInvalid,s) else
      exec (Call fi) s) ∧
  (exec (LocalGet n) s =
    case oEL n s.locals of NONE => (RInvalid,s) | SOME x =>
    (RNormal, push x s)
  ) ∧
  (exec (LocalSet n) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case set_local n x s of NONE => (RInvalid,s) | SOME s =>
      (RNormal,s)) ∧
  (exec (LocalTee n) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,_) =>
    case set_local n x s of NONE => (RInvalid,s) | SOME s =>
      (RNormal,s)) ∧
  (exec (GlobalGet n) s =
    case oEL n s.globals of NONE => (RInvalid,s) | SOME x =>
    (RNormal, push x s)
  ) ∧
  (exec (GlobalSet n) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case set_global n x s of NONE => (RInvalid,s) | SOME s =>
      (RNormal,s)) ∧
  (exec (OLoad res_t size_ext off) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    case exec_load res_t size_ext (w + off) s.memory of NONE => (RTrap,s) | SOME y =>
    (RNormal, push y s)
  ) ∧
  (exec (OStore res_t size off) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    case exec_store res_t size (w + off) s.memory of NONE => (RTrap,s) | SOME m =>
    (RNormal, s with memory := m)
  ) ∧
  (* (exec (MemRead op) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    case do_ld

  ) ∧ *)
  (exec (Numeric op) s =
    case num_stk_op op s.stack of NONE => (RInvalid,s) | SOME stack1 =>
    (RNormal, s with stack := stack1)) ∧
  (exec (ReturnCall fi) s =
    case oEL fi s.funcs of NONE => (RInvalid,s) | SOME f =>
    let np = LENGTH (FST f.type) in
    let nr = LENGTH (SND f.type) in
    case pop_n np s of NONE => (RInvalid,s) | SOME (args,s) =>
    let init_locals = args ++ MAP init_val_of f.types_of_locals in
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
  (exec (ReturnCallIndirect n tf) s =
    case pop s of NONE => (RInvalid,s) | SOME (x,s) =>
    case dest_i32 x of NONE => (RInvalid,s) | SOME w =>
    case lookup_func_tables s.func_tables n w of NONE => (RInvalid,s) | SOME fi =>
    case oEL fi s.funcs of NONE => (RInvalid,s) | SOME f =>
    if f.type ≠ tf then (RInvalid,s) else
      exec (ReturnCall fi) s) ∧
  (exec_list [] s = (RNormal, s)) ∧
  (exec_list (b::bs) s =
    let (res,s) = fix_clock s (exec b s) in
    case res of
      RNormal => exec_list bs s
    | _ => (res,s))
Termination
  WF_REL_TAC ‘inv_image (measure I LEX measure I) $ λx. case x of
               | INL (i,s) => (s.clock, inst_size' i)
               | INR (is,s) => (s.clock, list_size inst_size' is)’
  \\ gvs [inst_size'_def]
  \\ rw [SF ETA_ss]
  \\ imp_res_tac pop_clock
  \\ imp_res_tac pop_n_clock
  \\ imp_res_tac fix_clock_IMP
  \\ gvs [fix_clock_def]
End

val _ = export_theory();
