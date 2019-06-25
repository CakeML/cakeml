(*
  This compiler phase introduces the implementation of the memory
  allocator and its garbage collector. It traverses the given code and
  replaces all calls to Alloc by calls to code that it inserts into
  the compiled program. the inserted code is a stackLang
  implementation of the garbage collector.
*)
open preamble stackLangTheory data_to_wordTheory;

val _ = new_theory "stack_alloc";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val memcpy_code_def = Define `
  memcpy_code =
    While NotEqual 0 (Imm 0w)
      (list_Seq [load_inst 1 2;
                 add_bytes_in_word_inst 2;
                 sub_1_inst 0;
                 store_inst 1 3;
                 add_bytes_in_word_inst 3])`

val clear_top_inst_def = Define `
  clear_top_inst i n =
    Seq (left_shift_inst i (dimindex(:'a) - n - 1))
        (right_shift_inst i (dimindex(:'a) - n - 1)):'a stackLang$prog`;

val word_gc_move_code_def = Define `
  word_gc_move_code conf =
    If Test 5 (Imm (1w:'a word)) Skip
      (list_Seq
        [move 0 5;
         Get 1 CurrHeap;
         right_shift_inst 0 (shift_length conf);
         left_shift_inst 0 (word_shift (:'a));
         add_inst 0 1; (* here 0 is ptr_to_addr conf old w *)
         load_inst 1 0; (* here 1 is m (ptr_to_addr conf old w) *)
         If Test 1 (Imm 3w)
           (list_Seq [right_shift_inst 1 2;
                      left_shift_inst 1 (shift_length conf);
                      clear_top_inst 5 (small_shift_length conf - 1);
                      or_inst 5 1])
           (list_Seq [(* get len+1w *)
                      right_shift_inst 1 (dimindex (:'a) - conf.len_size);
                      add_1_inst 1;
                      (* store len+1w for later *)
                      move 6 1;
                      (* memcpy *)
                      move 2 0;
                      move 0 1;
                      memcpy_code;
                      (* compute original header_addr *)
                      move 0 6;
                      left_shift_inst 0 (word_shift (:'a));
                      sub_inst 2 0;
                      (* store i << 2 into header_addr *)
                      move 0 4;
                      left_shift_inst 0 2;
                      store_inst 0 2;
                      (* compute update_addr conf i w, where i in 4 and w in 5 *)
                      move 1 4;
                      clear_top_inst 5 (small_shift_length conf - 1);
                      left_shift_inst 1 (shift_length conf);
                      or_inst 5 1;
                      (* add to i in 4 *)
                      add_inst 4 6])])`

val word_gc_move_list_code_def = Define `
  word_gc_move_list_code conf =
    While NotEqual 7 (Imm (0w:'a word))
      (list_Seq [load_inst 5 8;
                 sub_1_inst 7;
                 word_gc_move_code conf;
                 store_inst 5 8;
                 add_bytes_in_word_inst 8])`

val word_gc_move_loop_code_def = Define `
  word_gc_move_loop_code conf =
    While NotEqual 3 (Reg 8)
     (list_Seq [load_inst 7 8;
                If Test 7 (Imm 4w)
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_bytes_in_word_inst 8;
                             word_gc_move_list_code conf])
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_1_inst 7;
                             left_shift_inst 7 (word_shift (:'a));
                             add_inst 8 7])]):'a stackLang$prog`

(* 7 is w, 8 is index into stack, 5 is input to word_gc_move_code *)
val word_gc_move_bitmap_code_def = Define `
  word_gc_move_bitmap_code conf =
    While NotLower 7 (Imm 2w)
     (If Test 7 (Imm 1w)
        (list_Seq [right_shift_inst 7 1;
                   add_bytes_in_word_inst 8])
        (list_Seq [StackLoadAny 5 8;
                   right_shift_inst 7 1;
                   word_gc_move_code conf;
                   StackStoreAny 5 8;
                   add_bytes_in_word_inst 8]))`

(* 9 is w, 8 is index into stack *)
val word_gc_move_bitmaps_code_def = Define `
  (word_gc_move_bitmaps_code conf):'a stackLang$prog =
    While NotTest 0 (Reg 0)
      (list_Seq [BitmapLoad 7 9;
                 word_gc_move_bitmap_code conf;
                 BitmapLoad 0 9;
                 add_1_inst 9;
                 right_shift_inst 0 (dimindex (:'a) - 1)])`

(* 9 is w, 8 is index into stack *)
val word_gc_move_roots_bitmaps_code_def = Define `
  (word_gc_move_roots_bitmaps_code conf):'a stackLang$prog =
    While NotTest 9 (Reg 9)
      (list_Seq [move 0 9;
                 sub_1_inst 9;
                 add_bytes_in_word_inst 8;
                 word_gc_move_bitmaps_code conf;
                 StackLoadAny 9 8])`

val word_gen_gc_move_code_def = Define `
  word_gen_gc_move_code conf =
    If Test 5 (Imm (1w:'a word)) Skip
      (list_Seq
        [move 0 5;
         Get 1 CurrHeap;
         right_shift_inst 0 (shift_length conf);
         left_shift_inst 0 (word_shift (:'a));
         add_inst 0 1; (* here 0 is ptr_to_addr conf old w *)
         load_inst 1 0; (* here 1 is m (ptr_to_addr conf old w) *)
         If Test 1 (Imm 3w)
           (list_Seq [right_shift_inst 1 2;
                      left_shift_inst 1 (shift_length conf);
                      clear_top_inst 5 (small_shift_length conf - 1);
                      or_inst 5 1])
           (list_Seq [(* put header in 6 *)
                      move 6 1;
                      (* get len+1w *)
                      right_shift_inst 1 (dimindex (:'a) - conf.len_size);
                      add_1_inst 1;
                      const_inst 2 28w;
                      and_inst 6 2;
                      If Equal 6 (Imm 8w)
                        (list_Seq [
                          Set (Temp 0w) 3;
                          Set (Temp 1w) 4;
                          Get 3 (Temp 2w); (* ib *)
                          Get 4 (Temp 3w); (* pb *)
                          (* store len+1w for later *)
                          move 6 1;
                          left_shift_inst 1 (word_shift (:'a));
                          sub_inst 4 6;
                          sub_inst 3 1;
                          Set (Temp 2w) 3; (* new ib *)
                          Set (Temp 3w) 4; (* new pb *)
                          (* memcpy *)
                          move 2 0;
                          move 4 0;
                          move 0 6;
                          memcpy_code;
                          (* compute original header_addr *)
                          Get 0 (Temp 3w); (* fixed? *)
                          left_shift_inst 0 2;
                          store_inst 0 4;
                          (* compute update_addr conf i w, where w in 5 *)
                          Get 1 (Temp 3w);
                          clear_top_inst 5 (small_shift_length conf - 1);
                          left_shift_inst 1 (shift_length conf);
                          or_inst 5 1;
                          Get 3 (Temp 0w);
                          Get 4 (Temp 1w)])
                        (list_Seq [
                          (* store len+1w for later *)
                          move 6 1;
                          (* memcpy *)
                          move 2 0;
                          move 0 1;
                          memcpy_code;
                          (* compute original header_addr *)
                          move 0 6;
                          left_shift_inst 0 (word_shift (:'a));
                          sub_inst 2 0;
                          (* store i << 2 into header_addr *)
                          move 0 4;
                          left_shift_inst 0 2;
                          store_inst 0 2;
                          (* compute update_addr conf i w, where i in 4 and w in 5 *)
                          move 1 4;
                          clear_top_inst 5 (small_shift_length conf - 1);
                          left_shift_inst 1 (shift_length conf);
                          or_inst 5 1;
                          (* add to i in 4 *)
                          add_inst 4 6])])]) :'a stackLang$prog`;

val word_gen_gc_partial_move_code_def = Define `
  word_gen_gc_partial_move_code conf =
    (* uses 0,1,2,6 as temps *)
    If Test 5 (Imm (1w:'a word)) Skip
      (list_Seq
        [move 0 5;
         Get 6 (Temp 0w);
         right_shift_inst 0 (shift_length conf);
         left_shift_inst 0 (word_shift (:'a));
         Get 1 (Temp 1w);
         If Lower 0 (Reg 6) Skip
          (Seq (Get 6 (Temp 1w))
          (If NotLower 0 (Reg 1) Skip (list_Seq [
             Get 1 CurrHeap;
             add_inst 0 1; (* here 0 is ptr_to_addr conf old w *)
             load_inst 1 0; (* here 1 is m (ptr_to_addr conf old w) *)
             If Test 1 (Imm 3w)
               (list_Seq [right_shift_inst 1 2;
                          left_shift_inst 1 (shift_length conf);
                          clear_top_inst 5 (small_shift_length conf - 1);
                          or_inst 5 1])
               (list_Seq [(* put header in 6 *)
                          move 6 1;
                          (* get len+1w *)
                          right_shift_inst 1 (dimindex (:'a) - conf.len_size);
                          add_1_inst 1;
                          (* store len+1w for later *)
                          move 6 1;
                          (* memcpy *)
                          move 2 0;
                          move 0 1;
                          memcpy_code;
                          (* compute original header_addr *)
                          move 0 6;
                          left_shift_inst 0 (word_shift (:'a));
                          sub_inst 2 0;
                          (* store i << 2 into header_addr *)
                          move 0 4;
                          left_shift_inst 0 2;
                          store_inst 0 2;
                          (* compute update_addr conf i w, where i in 4 and w in 5 *)
                          move 1 4;
                          clear_top_inst 5 (small_shift_length conf - 1);
                          left_shift_inst 1 (shift_length conf);
                          or_inst 5 1;
                          (* add to i in 4 *)
                          add_inst 4 6])])))]) :'a stackLang$prog`;

val word_gen_gc_move_bitmap_code_def = Define `
  word_gen_gc_move_bitmap_code conf =
    While NotLower 7 (Imm 2w)
     (If Test 7 (Imm 1w)
        (list_Seq [right_shift_inst 7 1;
                   add_bytes_in_word_inst 8])
        (list_Seq [StackLoadAny 5 8;
                   right_shift_inst 7 1;
                   word_gen_gc_move_code conf;
                   StackStoreAny 5 8;
                   add_bytes_in_word_inst 8]))`

val word_gen_gc_partial_move_bitmap_code_def = Define `
  word_gen_gc_partial_move_bitmap_code conf =
    While NotLower 7 (Imm 2w)
     (If Test 7 (Imm 1w)
        (list_Seq [right_shift_inst 7 1;
                   add_bytes_in_word_inst 8])
        (list_Seq [StackLoadAny 5 8;
                   right_shift_inst 7 1;
                   word_gen_gc_partial_move_code conf;
                   StackStoreAny 5 8;
                   add_bytes_in_word_inst 8]))`

(* 9 is w, 8 is index into stack *)
val word_gen_gc_move_bitmaps_code_def = Define `
  (word_gen_gc_move_bitmaps_code conf):'a stackLang$prog =
    While NotTest 0 (Reg 0)
      (list_Seq [BitmapLoad 7 9;
                 word_gen_gc_move_bitmap_code conf;
                 BitmapLoad 0 9;
                 add_1_inst 9;
                 right_shift_inst 0 (dimindex (:'a) - 1)])`

(* 9 is w, 8 is index into stack *)
val word_gen_gc_partial_move_bitmaps_code_def = Define `
  (word_gen_gc_partial_move_bitmaps_code conf):'a stackLang$prog =
    While NotTest 0 (Reg 0)
      (list_Seq [BitmapLoad 7 9;
                 word_gen_gc_partial_move_bitmap_code conf;
                 BitmapLoad 0 9;
                 add_1_inst 9;
                 right_shift_inst 0 (dimindex (:'a) - 1)])`

(* 9 is w, 8 is index into stack *)
val word_gen_gc_move_roots_bitmaps_code_def = Define `
  (word_gen_gc_move_roots_bitmaps_code conf):'a stackLang$prog =
    While NotTest 9 (Reg 9)
      (list_Seq [move 0 9;
                 sub_1_inst 9;
                 add_bytes_in_word_inst 8;
                 word_gen_gc_move_bitmaps_code conf;
                 StackLoadAny 9 8])`

(* 9 is w, 8 is index into stack *)
val word_gen_gc_partial_move_roots_bitmaps_code_def = Define `
  (word_gen_gc_partial_move_roots_bitmaps_code conf):'a stackLang$prog =
    While NotTest 9 (Reg 9)
      (list_Seq [move 0 9;
                 sub_1_inst 9;
                 add_bytes_in_word_inst 8;
                 word_gen_gc_partial_move_bitmaps_code conf;
                 StackLoadAny 9 8])`

val word_gen_gc_move_list_code_def = Define `
  word_gen_gc_move_list_code conf =
    While NotEqual 7 (Imm (0w:'a word))
      (list_Seq [load_inst 5 8;
                 sub_1_inst 7;
                 word_gen_gc_move_code conf;
                 store_inst 5 8;
                 add_bytes_in_word_inst 8])`

val word_gen_gc_partial_move_list_code_def = Define `
  word_gen_gc_partial_move_list_code conf =
    While NotEqual 7 (Imm (0w:'a word))
      (list_Seq [load_inst 5 8;
                 sub_1_inst 7;
                 word_gen_gc_partial_move_code conf;
                 store_inst 5 8;
                 add_bytes_in_word_inst 8])`

val word_gen_gc_move_data_code_def = Define `
  word_gen_gc_move_data_code conf =
    While NotEqual 3 (Reg 8)
     (list_Seq [load_inst 7 8;
                If Test 7 (Imm 4w)
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_bytes_in_word_inst 8;
                             word_gen_gc_move_list_code conf])
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_1_inst 7;
                             left_shift_inst 7 (word_shift (:'a));
                             add_inst 8 7])]):'a stackLang$prog`

val word_gen_gc_partial_move_ref_list_code_def = Define `
  word_gen_gc_partial_move_ref_list_code conf =
    While NotEqual 9 (Reg 8)
     (list_Seq [load_inst 7 8;
                right_shift_inst 7 (dimindex (:α) - conf.len_size);
                add_bytes_in_word_inst 8;
                word_gen_gc_partial_move_list_code conf]):'a stackLang$prog`

val word_gen_gc_partial_move_data_code_def = Define `
  word_gen_gc_partial_move_data_code conf =
    While NotEqual 3 (Reg 8)
     (list_Seq [load_inst 7 8;
                If Test 7 (Imm 4w)
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_bytes_in_word_inst 8;
                             word_gen_gc_partial_move_list_code conf])
                  (list_Seq [right_shift_inst 7 (dimindex (:α) - conf.len_size);
                             add_1_inst 7;
                             left_shift_inst 7 (word_shift (:'a));
                             add_inst 8 7])]):'a stackLang$prog`

val word_gen_gc_move_refs_code_def = Define `
  word_gen_gc_move_refs_code conf =
    (* r2a in 8, r1a in 0 and Temp 4w *)
    While NotEqual 0 (Reg 8)
     (list_Seq [load_inst 7 8;
                right_shift_inst 7 (dimindex (:α) - conf.len_size);
                add_bytes_in_word_inst 8;
                word_gen_gc_move_list_code conf;
                Get 0 (Temp 4w)]):'a stackLang$prog`

val word_gen_gc_move_loop_code_def = Define `
  word_gen_gc_move_loop_code conf =
    (* 7 is 0w iff pbx = pb and pax = pa, 1 is pbx (Temp 4w), 2 is pb,
       8 is pax, 3 is pa *)
    While NotTest 7 (Reg 7)
      (If Equal 1 (Reg 2)
         (* case: pax <> pa, i.e. move_data *)
         (list_Seq [word_gen_gc_move_data_code conf;
                    Get 5 (Temp 2w);
                    Get 7 (Temp 4w);
                    move 1 7;
                    move 2 5;
                    sub_inst 7 5])
         (* case: pbx <> pb i.e. move_refs *)
         (list_Seq [move 0 1;
                    Set (Temp 6w) 8;
                    move 8 2;
                    Set (Temp 5w) 8;
                    word_gen_gc_move_refs_code conf;
                    move 7 8; (* pbx' *)
                    Get 1 (Temp 5w); (* pb *)
                    Get 2 (Temp 5w);
                    Set (Temp 4w) 2;
                    Get 2 (Temp 2w); (* pb' *)
                    move 3 3; (* pa' *)
                    move 4 4; (* i' *)
                    move 7 1;
                    sub_inst 7 2; (* pbx' - pa' *)
                    Get 8 (Temp 6w); (* pax *)
                    move 5 8; (* pax - pa' *)
                    sub_inst 5 3;
                    or_inst 7 5]))`

val word_gc_partial_or_full_def = Define `
  word_gc_partial_or_full gen_sizes partial_code full_code =
    dtcase gen_sizes of
    | [] => list_Seq ([Get 8 TriggerGC; Get 7 EndOfHeap; sub_inst 7 8] ++ full_code)
    | _ => list_Seq
             [Get 8 TriggerGC;
              Get 7 EndOfHeap;
              sub_inst 7 8;
              If NotLower 7 (Reg 1)
                (list_Seq partial_code)
                (list_Seq full_code)]`;

val SetNewTrigger_def = Define `
  SetNewTrigger (endh:num) (ib:num) gs =
    list_Seq [const_inst 1 ((get_gen_size gs):'a word);
              Get 7 AllocSize;
              move 4 endh;
              sub_inst 4 ib;
              If Lower 1 (Reg 7)
                (If Lower 4 (Reg 7)
                   (Set TriggerGC endh)
                   (If Test 7 (Imm (if dimindex (:'a) = 32 then 3w else 7w))
                     (Seq (add_inst 7 ib) (Set TriggerGC 7))
                     (Set TriggerGC endh)))
                (If Lower 4 (Reg 1)
                   (Set TriggerGC endh)
                   (Seq (add_inst 1 ib) (Set TriggerGC 1)))]`

val word_gc_code_def = Define `
  word_gc_code conf =
    dtcase conf.gc_kind of
    | None =>
        (list_Seq
              [Set AllocSize 1;
               Get 2 CurrHeap;
               Set NextFree 2;
               Set TriggerGC 2;
               Set EndOfHeap 2;
               If Test 1 (Reg 1) Skip (Seq (const_inst 1 1w) (Halt 1))])
    | Simple =>
        (list_Seq
              [Set AllocSize 1;
               Set NextFree 0;
               const_inst 1 0w;
               move 2 1;
               Get 3 OtherHeap;
               move 4 1;
               Get 5 Globals;
               move 6 1;
               move 8 1;
               word_gc_move_code conf;
               Set Globals 5;
               const_inst 7 0w;
               StackLoadAny 9 8;
               move 8 7;
               word_gc_move_roots_bitmaps_code conf;
               Get 8 OtherHeap;
               word_gc_move_loop_code conf;
               Get 0 CurrHeap;
               Get 1 OtherHeap;
               Get 2 HeapLength;
               add_inst 2 1;
               Set CurrHeap 1;
               Set OtherHeap 0;
               Get 0 NextFree;
               Set NextFree 8;
               Set EndOfHeap 2;
               Set TriggerGC 2;
               Get 1 AllocSize;
               sub_inst 2 8;
               If Lower 2 (Reg 1) (Seq (const_inst 1 1w) (Halt 1)) Skip ])
    | Generational gen_sizes =>
        (word_gc_partial_or_full gen_sizes
              (* gen_gc_partial *)
              [Set AllocSize 1;
               Set NextFree 0;
               Get 4 GenStart;
               Get 5 EndOfHeap;
               Get 2 CurrHeap;
               Set (Temp 0w) 4;
               sub_inst 5 2;
               Set (Temp 1w) 5;
               Get 7 HeapLength;
               Get 5 Globals;
               Get 3 OtherHeap;
               right_shift_inst 4 (shift (:'a));
               move 6 3;
               word_gen_gc_partial_move_code conf;
               Set Globals 5;
               const_inst 8 0w;
               StackLoadAny 9 8;
               word_gen_gc_partial_move_roots_bitmaps_code conf;
               Get 8 CurrHeap;
               Get 9 HeapLength;
               add_inst 9 8;
               Get 8 EndOfHeap;
               word_gen_gc_partial_move_ref_list_code conf;
               Get 8 OtherHeap;
               word_gen_gc_partial_move_data_code conf;
               Get 2 OtherHeap;
               move 0 3;
               sub_inst 0 2;
               right_shift_inst 0 (shift (:'a));
               Get 3 GenStart;
               Get 1 CurrHeap;
               add_inst 3 1;
               memcpy_code;
               Get 0 NextFree;
               Set NextFree 3;
               Get 8 EndOfHeap;
               Get 2 TriggerGC;
               SetNewTrigger 8 3 gen_sizes;
               const_inst 1 0w;
               Set (Temp 0w) 1;
               Set (Temp 1w) 1;
               Get 1 AllocSize;
               sub_inst 8 3;
               Get 7 CurrHeap;
               sub_inst 3 7;
               Set GenStart 3 (* There is no need for a memory check here
                                 because the partial collector is guaranteed
                                 to get to a state where there is enough
                                 memory for the allocation. In contrast,
                                 the full collector below can hit a state
                                 where there is not enough memory, and so it
                                 can Halt execution. *)]
              (* gen_gc_full *)
              [Set AllocSize 1;
               Set NextFree 0;
               const_inst 1 (0w:'a word);
               move 2 1;
               Get 3 OtherHeap;
               Get 4 HeapLength;
               add_inst 4 3;
               Set (Temp 0w) 4;
               Set (Temp 1w) 4;
               Set (Temp 2w) 4;
               Set (Temp 4w) 4;
               Set (Temp 5w) 4;
               Set (Temp 6w) 4;
               Get 4 HeapLength;
               right_shift_inst 4 (shift (:'a));
               Set (Temp 3w) 4;
               move 4 1;
               Get 5 Globals;
               move 6 1;
               move 8 1;
               word_gen_gc_move_code conf;
               Set Globals 5;
               const_inst 7 0w;
               StackLoadAny 9 8;
               move 8 7;
               word_gen_gc_move_roots_bitmaps_code conf;
               Get 2 (Temp 2w);
               Get 8 OtherHeap;
               move 7 3;
               sub_inst 7 8;
               Get 1 (Temp 6w);
               move 6 2;
               sub_inst 6 1;
               or_inst 7 6;
               word_gen_gc_move_loop_code conf;
               Get 0 CurrHeap;
               Get 1 OtherHeap;
               Get 2 (Temp 2w);
               Set CurrHeap 1;
               Set OtherHeap 0;
               Get 0 NextFree;
               Set NextFree 3;
               Set EndOfHeap 2;
               move 8 3;
               sub_inst 8 1;
               Set GenStart 8;
               SetNewTrigger 2 3 gen_sizes;
               const_inst 1 0w;
               Set (Temp 0w) 1;
               Set (Temp 1w) 1;
               Set (Temp 2w) 1;
               Set (Temp 3w) 1;
               Set (Temp 4w) 1;
               Set (Temp 5w) 1;
               Set (Temp 6w) 1;
               Get 1 AllocSize;
               Get 2 TriggerGC;
               sub_inst 2 3;
               If Lower 2 (Reg 1) (Seq (const_inst 1 1w) (Halt 1)) Skip ])
                 :'a stackLang$prog`

val stubs_def = Define `
  stubs conf = [(gc_stub_location,Seq (word_gc_code conf) (Return 0 0))]`

(* compiler *)

local
val next_lab_quotation = `
  next_lab (p:'a stackLang$prog) aux =
    dtcase p of
    | Seq p1 p2 => next_lab p1 (next_lab p2 aux)
    | If _ _ _ p1 p2 => next_lab p1 (next_lab p2 aux)
    | While _ _ _ p => next_lab p aux
    | Call NONE _ NONE => aux
    | Call NONE _ (SOME (_,_,l2)) => MAX aux (l2 + 1)
    | Call (SOME (p,_,_,l2)) _ NONE => next_lab p (MAX aux (l2 + 1))
    | Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) =>
          next_lab p (next_lab p' ((MAX (MAX l2 l3 + 1) aux)))
    | _ => aux`
in
val next_lab_def = Define next_lab_quotation;

Theorem next_lab_pmatch = Q.prove(
  `∀p aux.` @
    (next_lab_quotation |>
     map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq)),
   rpt strip_tac
   >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
   >> rpt strip_tac
   >> rw[Once next_lab_def]
   >> every_case_tac >> fs[]);
end

local
val comp_quotation = `
  comp n m p =
    dtcase p of
    | Seq p1 p2 =>
        let (q1,m) = comp n m p1 in
        let (q2,m) = comp n m p2 in
          (Seq q1 q2,m)
    | If c r ri p1 p2 =>
        let (q1,m) = comp n m p1 in
        let (q2,m) = comp n m p2 in
          (If c r ri q1 q2,m)
    | While c r ri p1 =>
        let (q1,m) = comp n m p1 in
          (While c r ri q1,m)
    | Call NONE dest exc => (Call NONE dest NONE,m)
    | Call (SOME (p1,lr,l1,l2)) dest exc =>
        let (q1,m) = comp n m p1 in
         (dtcase exc of
          | NONE => (Call (SOME (q1,lr,l1,l2)) dest NONE,m)
          | SOME (p2,k1,k2) =>
              let (q2,m) = comp n m p2 in
                (Call (SOME (q1,lr,l1,l2)) dest (SOME (q2,k1,k2)),m))
    | Alloc k => (Call (SOME (Skip,0,n,m)) (INL gc_stub_location) NONE,m+1)
    | _ => (p,m) `
in
val comp_def = Define comp_quotation

Theorem comp_pmatch = Q.prove(
  `∀n m p.` @
    (comp_quotation |>
     map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
         | aq => aq)),
   rpt strip_tac
   >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
   >> rpt strip_tac
   >> rw[Once comp_def,pairTheory.ELIM_UNCURRY] >> every_case_tac >> fs[]);
end
val prog_comp_def = Define `
  prog_comp (n,p) = (n,FST (comp n (next_lab p 1) p))`

val compile_def = Define `
  compile c prog = stubs c ++ MAP prog_comp prog`;

val _ = export_theory();
