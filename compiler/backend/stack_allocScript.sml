open preamble stackLangTheory data_to_wordTheory;

val _ = new_theory "stack_alloc";

(* implementation of alloc and the GC *)

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
                      clear_top_inst 5 (shift_length conf - 1);
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
                      clear_top_inst 5 (shift_length conf - 1);
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

val word_gc_code_def = Define `
  word_gc_code conf =
    (list_Seq [Set AllocSize 1;
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
               Get 1 AllocSize;
               sub_inst 2 8;
               If Lower 2 (Reg 1) (Seq (const_inst 1 1w) (Halt 1)) Skip ])`

val stubs_def = Define `
  stubs conf = [(gc_stub_location,Seq (word_gc_code conf) (Return 0 0))]`

(* compiler *)

val next_lab_def = Define `
  next_lab (p:'a stackLang$prog) =
    case p of
    | Seq p1 p2 => MAX (next_lab p1) (next_lab p2)
    | If _ _ _ p1 p2 => MAX (next_lab p1) (next_lab p2)
    | While _ _ _ p => next_lab p
    | Call NONE _ NONE => 1
    | Call NONE _ (SOME (_,_,l2)) => l2 + 1
    | Call (SOME (p,_,_,l2)) _ NONE => MAX (next_lab p) (l2 + 1)
    | Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) => MAX (MAX (next_lab p) (next_lab p')) (MAX l2 l3 + 1)
    | _ => 1`

val comp_def = Define `
  comp n m p =
    case p of
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
         (case exc of
          | NONE => (Call (SOME (q1,lr,l1,l2)) dest NONE,m)
          | SOME (p2,k1,k2) =>
              let (q2,m) = comp n m p2 in
                (Call (SOME (q1,lr,l1,l2)) dest (SOME (q2,k1,k2)),m))
    | Alloc k => (Call (SOME (Skip,0,n,m)) (INL gc_stub_location) NONE,m+1)
    | _ => (p,m) `

val prog_comp_def = Define `
  prog_comp (n,p) = (n,FST (comp n (next_lab p) p))`

val compile_def = Define `
  compile c prog = stubs c ++ MAP prog_comp prog`;

val _ = export_theory();
