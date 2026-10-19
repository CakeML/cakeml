(*
  Tests for wordLang common subexpression elimination.
*)
Theory word_cse_test[no_sig_docs]
Ancestors
  word_cse
Libs
  preamble

(* tests *)

Definition Seqs_def:
  (Seqs [] = wordLang$Skip) /\
  (Seqs [x] = x) /\
  (Seqs (x::y::xs) = Seq x (Seqs (y::xs)))
End

Theorem test_latest_name_used[local]:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (Binop Add 11 1 (Reg 1)));
          Inst (Arith (Binop Add 13 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Move 0 [(9,7)];
          Move 0 [(11,9)];
          Move 0 [(13,11)]]
Proof
  EVAL_TAC
QED

Theorem test_get_set[local]:
  word_common_subexp_elim $
    Seqs [Get 1 NextFree;
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Set NextFree (Var 7);
          Get 9 NextFree;
          Inst (Arith (Binop Add 11 1 (Reg 1)));
          Get 33 NextFree;
          Get 35 NextFree;
          Get 37 NextFree]
  =
    Seqs [Get 1 NextFree;
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          Set NextFree (Var 7);
          Move 1 [(9,7)];
          Move 0 [(11,9)];
          Move 1 [(33,11)];
          Move 1 [(35,33)];
          Move 1 [(37,35)]]
Proof
  EVAL_TAC
QED

Theorem test_pattern_match_and_cons[local]:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Shift Lsr 301 297 (Imm 9)));
          OpCurrHeap Add 305 301;
          Inst (Mem Load 309 (Addr 305 8));
          Move 0 [(313,297)];
          Inst (Arith (Shift Lsr 317 313 (Imm 9)));
          OpCurrHeap Add 321 317;
          Inst (Mem Load 325 (Addr 321 16));
          Move 0 [(329,313)];
          Inst (Arith (Shift Lsr 333 329 (Imm 9)));
          OpCurrHeap Add 337 333;
          Inst (Mem Load 341 (Addr 337 24));
          Get 345 NextFree;
          Inst (Const 349 0x200000003);
          Move 0 [(353,345)];
          Inst (Mem Store 349 (Addr 353 0));
          Move 0 [(357,353)];
          Inst (Mem Store 325 (Addr 357 8));
          Move 0 [(361,357)];
          Inst (Mem Store 341 (Addr 361 16));
          Move 0 [(365,361)];
          OpCurrHeap Sub 369 365;
          Inst (Arith (Shift Lsl 373 369 (Imm 9)));
          Inst (Arith (Binop Or 377 373 (Imm 5)));
          Move 0 [(381,365)];
          Inst (Arith (Binop Add 385 381 (Imm 24)));
          Set NextFree (Var 385);
          Get 389 NextFree;
          Inst (Const 393 0x200000003);
          Move 0 [(397,389)];
          Inst (Mem Store 393 (Addr 397 0));
          Move 0 [(401,397)];
          Inst (Mem Store 309 (Addr 401 8));
          Move 0 [(405,401)];
          Inst (Mem Store 377 (Addr 405 16));
          Move 0 [(409,405)];
          OpCurrHeap Sub 413 409;
          Inst (Arith (Shift Lsl 417 413 (Imm 9)));
          Inst (Arith (Binop Or 421 417 (Imm 5)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24)));
          Set NextFree (Var 429);
          Move 0 [(2,421)]; Return 273 [2]]
  =
    Seqs [Inst (Arith (Shift Lsr 301 297 (Imm 9)));
          OpCurrHeap Add 305 301;
          Inst (Mem Load 309 (Addr 305 8));
          Move 0 [(313,297)];
          Move 0 [(317,301)];
          Move 0 [(321,305)];
          Inst (Mem Load 325 (Addr 321 16));
          Move 0 [(329,313)];
          Move 0 [(333,317)];
          Move 0 [(337,321)];
          Inst (Mem Load 341 (Addr 337 24));
          Get 345 NextFree;
          Inst (Const 349 0x200000003);
          Move 0 [(353,345)];
          Inst (Mem Store 349 (Addr 353 0));
          Move 0 [(357,353)];
          Inst (Mem Store 325 (Addr 357 8));
          Move 0 [(361,357)];
          Inst (Mem Store 341 (Addr 361 16));
          Move 0 [(365,361)];
          OpCurrHeap Sub 369 365;
          Inst (Arith (Shift Lsl 373 369 (Imm 9)));
          Inst (Arith (Binop Or 377 373 (Imm 5)));
          Move 0 [(381,365)];
          Inst (Arith (Binop Add 385 381 (Imm 24)));
          Set NextFree (Var 385);
          Move 1 [(389,385)];
          Inst (Const 393 0x200000003);
          Move 0 [(397,389)];
          Inst (Mem Store 393 (Addr 397 0));
          Move 0 [(401,397)];
          Inst (Mem Store 309 (Addr 401 8));
          Move 0 [(405,401)];
          Inst (Mem Store 377 (Addr 405 16));
          Move 0 [(409,405)];
          OpCurrHeap Sub 413 409;
          Inst (Arith (Shift Lsl 417 413 (Imm 9)));
          Inst (Arith (Binop Or 421 417 (Imm 5)));
          Move 0 [(425,409)];
          Inst (Arith (Binop Add 429 425 (Imm 24)));
          Set NextFree (Var 429);
          Move 0 [(2,421)];
          Return 273 [2]]
Proof
  EVAL_TAC
QED

(* Loads from the same canonical address at the same width are CSE'd (and a
   chain hanging off the loaded value then CSEs too); a different width is a
   different fact; any store invalidates all load facts but no register
   facts. *)
Theorem test_load_cse[local]:
  word_common_subexp_elim $
    Seqs [Inst (Mem Load 9 (Addr 7 0));
          Inst (Arith (Shift Lsr 11 9 (Imm 29)));
          Inst (Mem Load 13 (Addr 7 0));
          Inst (Arith (Shift Lsr 15 13 (Imm 29)));
          Inst (Mem Load8 17 (Addr 7 0));
          Inst (Mem Store 15 (Addr 7 0));
          Inst (Mem Load 19 (Addr 7 0))]
  =
    Seqs [Inst (Mem Load 9 (Addr 7 0));
          Inst (Arith (Shift Lsr 11 9 (Imm 29)));
          Move 0 [(13,9)];
          Move 0 [(15,11)];
          Inst (Mem Load8 17 (Addr 7 0));
          Inst (Mem Store 15 (Addr 7 0));
          Inst (Mem Load 19 (Addr 7 0))]
Proof
  EVAL_TAC
QED

(* Set CurrHeap conservatively resets all knowledge (it is not emitted by
   data_to_word, so a finer treatment is not worth its proof cost): nothing
   after it is CSE'd. *)
Theorem test_set_currheap[local]:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          OpCurrHeap Add 3 1;
          Set CurrHeap (Var 7);
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          OpCurrHeap Add 5 1]
  =
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          OpCurrHeap Add 3 1;
          Set CurrHeap (Var 7);
          Inst (Arith (Binop Add 9 1 (Reg 1)));
          OpCurrHeap Add 5 1]
Proof
  EVAL_TAC
QED

(* A repeated LocValue of the same label is CSE'd to a Move. *)
Theorem test_locvalue[local]:
  word_common_subexp_elim $
    Seqs [LocValue 7 100; LocValue 9 100]
  =
    Seqs [LocValue 7 100; Move 0 [(9,7)]]
Proof
  EVAL_TAC
QED

(* LongMul clobbers both outputs (7 and 9), so the value previously stored in
   9 is invalidated and the later Add is NOT replaced by a Move from 9. *)
Theorem test_multi_output_invalidation[local]:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (LongMul 7 9 3 5));
          Inst (Arith (Binop Add 11 1 (Reg 1)))]
  =
    Seqs [Inst (Arith (Binop Add 9 1 (Reg 1)));
          Inst (Arith (LongMul 7 9 3 5));
          Inst (Arith (Binop Add 11 1 (Reg 1)))]
Proof
  EVAL_TAC
QED

(* An instruction that reads the register it writes is not stored as a fact,
   so the second Add (reading the NEW 7) is not replaced by a Move. *)
Theorem test_self_read_not_cse[local]:
  word_common_subexp_elim $
    Seqs [Inst (Arith (Binop Add 7 7 (Imm 1)));
          Inst (Arith (Binop Add 9 7 (Imm 1)))]
  =
    Seqs [Inst (Arith (Binop Add 7 7 (Imm 1)));
          Inst (Arith (Binop Add 9 7 (Imm 1)))]
Proof
  EVAL_TAC
QED

(* Facts valid after both arms of an If survive the join: the Add fact
   (holder 7) is used both inside the first arm and after the join. *)
Theorem test_if_merge[local]:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0)
             (Inst (Arith (Binop Add 9 1 (Reg 1))))
             (Move 0 [(11,7)]);
          Inst (Arith (Binop Add 13 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0) (Move 0 [(9,7)]) (Move 0 [(11,7)]);
          Move 0 [(13,7)]]
Proof
  EVAL_TAC
QED

(* An arm that clobbers a tracked register resets its branch knowledge, so
   nothing survives the join and the trailing Add is not CSE'd. *)
Theorem test_if_merge_clobber[local]:
  word_common_subexp_elim $
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0)
             (Move 0 [(7,3)])
             Skip;
          Inst (Arith (Binop Add 9 1 (Reg 1)))]
  =
    Seqs [Inst (Const 1 0);
          Inst (Arith (Binop Add 7 1 (Reg 1)));
          If Equal 1 (Imm 0) (Move 0 [(7,3)]) Skip;
          Inst (Arith (Binop Add 9 1 (Reg 1)))]
Proof
  EVAL_TAC
QED

val _ = Theory.delete_const "Seqs";
