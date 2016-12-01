open preamble wordLangTheory dataLangTheory word_to_wordTheory;
local open bvl_to_bviTheory in end

val _ = new_theory "data_to_word";

val _ = Datatype `
  config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *) |>`

val adjust_var_def = Define `
  adjust_var n = 2 * n + 2:num`;

val adjust_set_def = Define `
  adjust_set (names:'a num_map) =
    (fromAList ((0,()):: MAP (\(n,k). (adjust_var n,())) (toAList names))):num_set`

val Unit_def = Define`Unit = Const 2w`;

val GiveUp_def = Define `
  GiveUp = Seq (Assign 1 (Const (-1w)))
               (Alloc 1 (adjust_set (LN:num_set))) :'a wordLang$prog`

val BignumHalt_def = Define `
  BignumHalt r = If Test r (Imm 1w) Skip GiveUp`;

val make_header_def = Define `
  make_header conf tag len =
    let l = dimindex (:'a) - conf.len_size in
      (n2w len << l || tag << 2 || 3w:'a word)`

val tag_mask_def = Define `
  tag_mask conf =
    let l = dimindex (:'a) - conf.len_size in
      (l-1 '' 2) (~0w:'a word)`

val encode_header_def = Define `
  encode_header (conf:data_to_word$config) tag len =
    if tag < 2 ** (dimindex (:'a) - conf.len_size - 2) /\
       tag < dimword (:'a) DIV 16 /\
       len < 2 ** (dimindex (:'a) - 4) /\
       len < 2 ** conf.len_size
    then SOME ((make_header conf (n2w tag) len):'a word)
    else NONE`

val list_Seq_def = Define `
  (list_Seq [] = wordLang$Skip) /\
  (list_Seq [x] = x) /\
  (list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))`

val shift_def = Define `
  shift (:'a) = if dimindex (:'a) = 32 then 2 else 3n`;

val StoreEach_def = Define `
  (StoreEach v [] offset = Skip) /\
  (StoreEach v (x::xs) (offset:'a word) =
     Seq (Store (Op Add [Var v; Const offset]) x)
         (StoreEach v xs (offset + bytes_in_word)))`

val small_shift_length_def = Define `
  small_shift_length conf = conf.len_bits + conf.tag_bits + 1`;

val shift_length_def = Define `
  shift_length conf = 1 + conf.pad_bits + conf.len_bits + conf.tag_bits + 1`;

val max_heap_limit_def = Define `
  max_heap_limit (:'a) c =
    MIN (dimword (:'a) DIV 2 ** shift_length c)
        (dimword (:'a) DIV 2 ** (shift (:'a) + 1))`

val all_ones_def = Define `
  all_ones m n = if m <= n then 0w else (m - 1 '' n) (~0w)`;

val maxout_bits_def = Define `
  maxout_bits n rep_len k =
    if n < 2 ** rep_len then n2w n << k else all_ones (k + rep_len) k`

val ptr_bits_def = Define `
  ptr_bits conf tag len =
    (maxout_bits tag conf.tag_bits (1 + conf.len_bits) ||
     maxout_bits len conf.len_bits 1)`

val real_addr_def = Define `
  (real_addr (conf:data_to_word$config) r): 'a wordLang$exp =
    let k = shift (:'a) in
      if k <= conf.pad_bits + 1 then
        Op Add [Lookup CurrHeap;
                Shift Lsr (Var r) (Nat (shift_length conf - k))]
      else
        Op Add [Lookup CurrHeap;
                Shift Lsl (Shift Lsr (Var r)
                  (Nat (shift_length conf))) (Nat k)]`

val real_offset_def = Define `
  (real_offset (conf:data_to_word$config) r): 'a wordLang$exp =
     Op Add [Const bytes_in_word;
             if dimindex (:'a) = 32 then Var r else Shift Lsl (Var r) (Nat 1)]`

val real_byte_offset_def = Define`
  real_byte_offset r : 'a wordLang$exp =
    Op Add [Const bytes_in_word;
            Shift Lsr (Var r) (Nat 2)]`;

val _ = Datatype`
  word_op_type = Bitwise binop | Carried binop`;

val lookup_word_op_def = Define`
  (lookup_word_op Andw = Bitwise And) ∧
  (lookup_word_op Orw = Bitwise Or) ∧
  (lookup_word_op Xor = Bitwise Xor) ∧
  (lookup_word_op Add = Carried Add) ∧
  (lookup_word_op Sub = Carried Sub)`;
val _ = export_rewrites["lookup_word_op_def"];

val FromList_location_def = Define`
  FromList_location = word_num_stubs`;
val FromList1_location_def = Define`
  FromList1_location = FromList_location+1`;
val RefByte_location_def = Define`
  RefByte_location = FromList1_location+1`;
val RefArray_location_def = Define`
  RefArray_location = RefByte_location+1`;
val Replicate_location_def = Define `
  Replicate_location = RefArray_location+1`;
val AnyArith_location_def = Define `
  AnyArith_location = Replicate_location+1`;
val Add_location_def = Define `
  Add_location = AnyArith_location+1`;
val Sub_location_def = Define `
  Sub_location = Add_location+1`;
val Mul_location_def = Define `
  Mul_location = Sub_location+1`;
val Div_location_def = Define `
  Div_location = Mul_location+1`;
val Mod_location_def = Define `
  Mod_location = Div_location+1`;
val Compare1_location_def = Define `
  Compare1_location = Mod_location+1`;
val Compare_location_def = Define `
  Compare_location = Compare1_location+1`;
val Equal1_location_def = Define `
  Equal1_location = Compare_location+1`;
val Equal_location_def = Define `
  Equal_location = Equal1_location+1`;

val FromList_location_eq = save_thm("FromList_location_eq",
  ``FromList_location`` |> EVAL);
val FromList1_location_eq = save_thm("FromList1_location_eq",
  ``FromList1_location`` |> EVAL);
val RefByte_location_eq = save_thm("RefByte_location_eq",
  ``RefByte_location`` |> EVAL);
val RefArray_location_eq = save_thm("RefArray_location_eq",
  ``RefArray_location`` |> EVAL);
val Replicate_location_eq = save_thm("Replicate_location_eq",
  ``Replicate_location`` |> EVAL);
val AnyArith_location_eq = save_thm("AnyArith_location_eq",
  ``AnyArith_location`` |> EVAL);
val Add_location_eq = save_thm("Add_location_eq",
  ``Add_location`` |> EVAL);
val Sub_location_eq = save_thm("Sub_location_eq",
  ``Sub_location`` |> EVAL);
val Mul_location_eq = save_thm("Mul_location_eq",
  ``Mul_location`` |> EVAL);
val Div_location_eq = save_thm("Div_location_eq",
  ``Div_location`` |> EVAL);
val Mod_location_eq = save_thm("Mod_location_eq",
  ``Mod_location`` |> EVAL);
val Compare1_location_eq = save_thm("Compare1_location_eq",
  ``Compare1_location`` |> EVAL);
val Compare_location_eq = save_thm("Compare_location_eq",
  ``Compare_location`` |> EVAL);
val Equal1_location_eq = save_thm("Equal1_location_eq",
  ``Equal1_location`` |> EVAL);
val Equal_location_eq = save_thm("Equal_location_eq",
  ``Equal_location`` |> EVAL);

val AllocVar_def = Define `
  AllocVar (limit:num) (names:num_set) =
    list_Seq [Assign 1 (Shift Lsr (Var 1) (Nat 2));
              If Lower 1 (Imm (n2w limit))
                (Assign 1 (Shift Lsl (Op Add [Var 1; Const 1w]) (Nat (shift (:'a)))))
                (Assign 1 (Const (-1w:'a word)));
              Assign 3 (Op Sub [Lookup EndOfHeap; Lookup NextFree]);
              If Lower 3 (Reg 1) (Alloc 1 (adjust_set names)) Skip]`;

val MakeBytes_def = Define `
  MakeBytes n =
    list_Seq [Assign n (Shift Lsr (Var n) (Nat 2));
              Assign n (Op Or [Var n; Shift Lsl (Var n) (Nat 8)]);
              Assign n (Op Or [Var n; Shift Lsl (Var n) (Nat 16)]);
              if dimindex (:'a) = 32 then Skip else
                Assign n (Op Or [Var n; Shift Lsl (Var n) (Nat 32)])]
                   :'a wordLang$prog`

val SmallLsr_def = Define `
  SmallLsr e n = if n = 0 then e else Shift Lsr e (Nat n)`;

val RefByte_code_def = Define`
  RefByte_code c =
      let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
      let h = Op Add [Shift Lsr (Var 2) (Nat 2); Const (bytes_in_word - 1w)] in
      let x = SmallLsr h (dimindex (:'a) - 63) in
      let y = Shift Lsl h (Nat (dimindex (:'a) - shift (:'a) - c.len_size)) in
        list_Seq
          [BignumHalt 2;
           Assign 1 x;
           AllocVar limit (fromList [();()]);
           (* compute length *)
           Assign 5 (Shift Lsr h (Nat (shift (:'a))));
           Assign 6 (Shift Lsl (Var 5) (Nat 2));
           (* adjust end of heap *)
           Assign 1 (Op Sub [Lookup EndOfHeap;
                       Shift Lsl (Op Add [Var 5; Const 1w]) (Nat (shift (:'a)))]);
           Set EndOfHeap (Var 1);
           (* 3 := return value *)
           Assign 3 (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
               (Nat (shift_length c − shift (:'a))); Const (1w:'a word)]);
           (* compute header *)
           Assign 5 (Op Or [y; Const 0b10111w]);
           (* compute repeated byte *)
           MakeBytes 4;
           (* store header *)
           Store (Var 1) 5;
           Call NONE (SOME Replicate_location)
              (* ret_loc, addr, v, n, ret_val *)
              [0;1;4;6;3] NONE]`;

val Maxout_bits_code_def = Define `
  Maxout_bits_code rep_len k dest n =
    If Lower n (Imm (n2w (2 ** rep_len)))
      (Assign dest (Op Or [Var dest; Shift Lsl (Var n) (Nat k)]))
      (Assign dest (Op Or [Var dest; Const (all_ones (k + rep_len) k)]))`

val Make_ptr_bits_code_def = Define `
  Make_ptr_bits_code c tag len dest =
    list_Seq [Assign dest (Op Or
       [Const 1w; Shift Lsl (Op Sub [Lookup NextFree; Lookup CurrHeap])
           (Nat (shift_length c − shift (:'a)))]);
        Maxout_bits_code c.tag_bits (1 + c.len_bits) dest tag;
        Maxout_bits_code c.len_bits 1 dest len] :'a wordLang$prog`

val FromList_code_def = Define `
  FromList_code c =
    let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
    let h = Shift Lsl (Var 2) (Nat (dimindex (:'a) - c.len_size - 2)) in
      If Equal 2 (Imm 0w)
        (list_Seq [Assign 6 (Op Add [Var 6; Const (2w:'a word)]);
                   Return 0 6])
        (list_Seq
          [BignumHalt 2;
           Assign 1 (Var 2); AllocVar limit (fromList [();();()]);
           Assign 1 (Lookup NextFree);
           Assign 5 (Op Or [h; Const 3w; Var 6]);
           Assign 7 (Shift Lsr (Var 2) (Nat 2));
           Assign 9 (Shift Lsr (Var 6) (Nat 4));
           Make_ptr_bits_code c 9 7 3;
           Call NONE (SOME FromList1_location) [0;1;4;2;3;5] NONE])`;

val FromList1_code_def = Define `
  FromList1_code c =
    (* 0 = return address
       2 = address to write to
       4 = where to lookup what to write
       6 = how many left to write
       8 = value to be returned
      10 = first thing to write *)
    list_Seq
      [Store (Var 2) 10;
       Assign 2 (Op Add [Var 2; Const bytes_in_word]);
       If Equal 6 (Imm 0w)
         (list_Seq
            [Set NextFree (Var 2);
             Return 0 8])
         (list_Seq
            [Assign 4 (real_addr c 4);
             Assign 10 (Load (Op Add [Var 4; Const bytes_in_word]));
             Assign 4 (Load (Op Add [Var 4; Const (2w * bytes_in_word)]));
             Assign 6 (Op Sub [Var 6; Const 4w]);
             Call NONE (SOME FromList1_location) [0;2;4;6;8;10] NONE])]`;

val RefArray_code_def = Define `
  RefArray_code c =
      let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
        list_Seq
          [BignumHalt 2;
           Move 0 [(1,2)];
           AllocVar limit (fromList [();()]);
           Assign 1 (Op Sub [Lookup EndOfHeap;
           Shift Lsl (Op Add [(Shift Lsr (Var 2) (Nat 2)); Const 1w])
                   (Nat (shift (:'a)))]);
           Set EndOfHeap (Var 1);
           (* 3 := return value *)
           Assign 3 (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
               (Nat (shift_length c − shift (:'a))); Const (1w:'a word)]);
           (* compute header *)
           Assign 5 (Op Or [Shift Lsl (Var 2)
                              (Nat (dimindex (:'a) − c.len_size - 2));
                            Const (make_header c 2w 0)]);
           (* store header *)
           Store (Var 1) 5;
           Call NONE (SOME Replicate_location)
              (* ret_loc, addr, v, n, ret_val *)
              [0;1;4;2;3] NONE]`;

val Replicate_code_def = Define `
  Replicate_code =
    (* 0 = return address
       2 = address to write to
       4 = what to write at each location
       6 = how many left to write
       8 = value to be returned *)
    If Equal 6 (Imm 0w) (Return 0 8)
      (list_Seq [Assign 2 (Op Add [Var 2; Const (bytes_in_word)]);
                 Store (Var 2) 4;
                 Assign 6 (Op Sub [Var 6; Const 4w]);
                 Call NONE (SOME Replicate_location) [0;2;4;6;8] NONE])`;

val AnyArith_code_def = Define `
  AnyArith_code c = GiveUp`;

val Add_code_def = Define `
  Add_code = Seq (Assign 6 (Const 0w))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)`;

val Sub_code_def = Define `
  Sub_code = Seq (Assign 6 (Const 4w))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)`;

val Mul_code_def = Define `
  Mul_code = Seq (Assign 6 (Const 8w))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)`;

val Div_code_def = Define `
  Div_code = Seq (Assign 6 (Const 12w))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)`;

val Mod_code_def = Define `
  Mod_code = Seq (Assign 6 (Const 16w))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)`;

val Compare1_code_def = Define `
  Compare1_code =
    (* l is 2, a1 is 4, a2 is 6 *)
    If Equal 2 (Imm 0w)
      (Seq (Assign 2 (Const 1w)) (Return 0 2))
      (list_Seq
         [Assign 8 (Load (Var 4));
          Assign 9 (Load (Var 6));
          If Equal 8 (Reg 9)
            (list_Seq
               [Assign 2 (Op Sub [Var 2; Const 1w]);
                Assign 4 (Op Sub [Var 4; Const bytes_in_word]);
                Assign 6 (Op Sub [Var 6; Const bytes_in_word]);
                Call NONE (SOME Compare1_location) [0;2;4;6] NONE])
            (If Lower 8 (Reg 9)
              (Seq (Assign 2 (Const 0w)) (Return 0 2))
              (Seq (Assign 2 (Const 2w)) (Return 0 2)))])`

val Compare_code_def = Define `
  Compare_code c =
    (* this code can assume that the arguments (2 and 4) are not both
       small numbers *)
    If Test 2 (Imm 1w) (* 1st arg is small number, means that 2nd must be bigum *)
      (list_Seq [Assign 1 (Load (real_addr c 4)); (* loads header of 2nd arg *)
                 If Test 1 (Imm 16w)
                   (Seq (Assign 2 (Const 0w)) (Return 0 2))
                   (Seq (Assign 2 (Const 2w)) (Return 0 2))])
   (If Test 4 (Imm 1w) (* 2nd arg is small number: 1st must be bigum *)
      (list_Seq [Assign 1 (Load (real_addr c 2)); (* loads header of 1st arg *)
                 If Test 1 (Imm (16w:'a word))
                   (Seq (Assign 2 (Const 2w)) (Return 0 2))
                   (Seq (Assign 2 (Const 0w)) (Return 0 2))])
      (list_Seq [Assign 11 (real_addr c 2);
                 Assign 1 (Load (Var 11)); (* loads header of 1st arg *)
                 Assign 13 (real_addr c 4);
                 Assign 3 (Load (Var 13)); (* loads header of 2nd arg *)
                 Assign 6 (Shift Lsr (Var 1) (Nat ((dimindex(:'a) − c.len_size))));
                 Assign 8 (Shift Lsr (Var 3) (Nat ((dimindex(:'a) − c.len_size))));
                 If Equal 1 (Reg 3) (* headers are the same *)
                   (list_Seq
                     [Assign 2 (Op Add [Var 11;Shift Lsl (Var 6)(Nat(shift (:'a)))]);
                      Assign 4 (Op Add [Var 13;Shift Lsl (Var 6)(Nat(shift (:'a)))]);
                      If Test 1 (Imm 16w)
                       (Call NONE (SOME Compare1_location) [0;6;2;4] NONE)
                       (Call NONE (SOME Compare1_location) [0;6;4;2] NONE)])
                   (* headers are not the same *)
                   (If Test 1 (Imm 16w)
                      (If Test 3 (Imm 16w)
                         (If Lower 6 (Reg 8)
                            (Seq (Assign 2 (Const 0w)) (Return 0 2))
                            (Seq (Assign 2 (Const 2w)) (Return 0 2)))
                         (Seq (Assign 2 (Const 2w)) (Return 0 2)))
                      (If Test 3 (Imm 16w)
                         (Seq (Assign 2 (Const 0w)) (Return 0 2))
                         (If Lower 6 (Reg 8)
                            (Seq (Assign 2 (Const 2w)) (Return 0 2))
                            (Seq (Assign 2 (Const 0w)) (Return 0 2)))))]))`;

val Equal1_code_def = Define `
  Equal1_code c = Skip`;

val Equal_code_def = Define `
  Equal_code c = Skip`;

val get_names_def = Define `
  (get_names NONE = LN) /\
  (get_names (SOME x) = x)`;

val LoadWord64_def = Define `
  LoadWord64 c i j =
    Assign i (Load (Op Add [real_addr c j; Const bytes_in_word]))`;

val LoadBignum_def = Define`
  LoadBignum c header word1 k = list_Seq [
    Assign word1 (real_addr c k);
    Assign header (Load (Var word1));
    Assign word1 (Load (Op Add [Var word1; Const bytes_in_word]))]`;

val WriteWord64_def = Define ` (* also works for storing bignums of length 1 *)
  WriteWord64 c (header:'a word) dest i =
    list_Seq [Assign 1 (Op Sub [Lookup EndOfHeap; Const (bytes_in_word * 2w)]);
              Store (Op Add [Var 1; Const bytes_in_word]) i;
              Assign 3 (Const header);
              Store (Var 1) 3;
              Set EndOfHeap (Var 1);
              Assign (adjust_var dest)
                (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                          (Nat (shift_length c − shift (:'a)));
                        Const 1w])]`;

val ShiftVar_def = Define `
  ShiftVar sh v n =
    if n = 0 then Var v else
    if dimindex (:'a) <= n then
      if sh = Asr then Shift sh (Var v) (Nat (dimindex (:'a) - 1)) else Const 0w
    else (Shift sh (Var v) (Nat n)):'a wordLang$exp`

val _ = temp_overload_on("FALSE_CONST",``Const (n2w 18:'a word)``)
val _ = temp_overload_on("TRUE_CONST",``Const (n2w 2:'a word)``)

val assign_def = Define `
  assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (op:closLang$op)
    (args:num list) (names:num_set option) =
    case op of
    | Const i =>
        (* bvl_to_bvi compilation ensures that all literal
           constants fit into a machine word *)
        if i < 0
        then (Assign (adjust_var dest) (Const (0w - n2w (Num (4 * (0 - i))))),l)
        else (Assign (adjust_var dest) (Const (n2w (Num (4 * i)))),l)
    | GlobalsPtr => (Assign (adjust_var dest) (Lookup Globals),l)
    | SetGlobalsPtr =>
      if args = []
      then (Skip,l)
      else (Seq (Set Globals (Var (adjust_var (HD args))))
                            (Assign (adjust_var dest) Unit),l)
    | ToList => (Skip,l)
    | Global _ => (Skip,l)
    | SetGlobal _ => (Skip,l)
    | AllocGlobal => (Skip,l)
    | El => (case args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           real_offset c (adjust_var v2)])),l)
             | _ => (Skip,l))
    | Deref => (case args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           real_offset c (adjust_var v2)])),l)
             | _ => (Skip,l))
    | DerefByte =>
      (case args of
       | [v1;v2] =>
         (list_Seq [
            Assign 1 (Op Add [real_addr c (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
            Inst (Mem Load8 3 (Addr 1 0w));
            Assign (adjust_var dest) (Shift Lsl (Var 3) (Nat 2))
          ], l)
       | _ => (Skip,l))
    | Update => (case args of
             | [v1;v2;v3] =>
                 (Seq (Store (Op Add [real_addr c (adjust_var v1);
                                      real_offset c (adjust_var v2)])
                             (adjust_var v3))
                      (Assign (adjust_var dest) Unit),l)
             | _ => (Skip,l))
    | UpdateByte => (case args of
      | [v1;v2;v3] => (list_Seq [
          Assign 1 (Op Add [real_addr c (adjust_var v1);
                            real_byte_offset (adjust_var v2)]);
          Assign 3 (Shift Lsr (Var (adjust_var v3)) (Nat 2));
          Inst (Mem Store8 3 (Addr 1 0w));
          Assign (adjust_var dest) Unit], l)
      | _ => (Skip,l))
    | Cons tag => if LENGTH args = 0 then
                    if tag < dimword (:'a) DIV 16 then
                      (Assign (adjust_var dest) (Const (n2w (16 * tag + 2))),l)
                    else (GiveUp,l) (* tag is too big to be represented *)
                  else
                    (case encode_header c (4 * tag) (LENGTH args) of
                     | NONE => (GiveUp,l)
                     | SOME (header:'a word) => (list_Seq
                        [Assign 1 (Op Sub [Lookup EndOfHeap;
                            Const (bytes_in_word * n2w (LENGTH args + 1))]);
                         Set EndOfHeap (Var 1);
                         Assign 3 (Const header);
                         StoreEach 1 (3::MAP adjust_var args) 0w;
                         Assign (adjust_var dest)
                           (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                                     (Nat (shift_length c − shift (:'a)));
                                   Const (1w ||
                                           (small_shift_length c − 1 -- 0)
                                              (ptr_bits c tag (LENGTH args)))])],l))
    | Ref => (case encode_header c 2 (LENGTH args) of
              | NONE => (GiveUp,l)
              | SOME (header:'a word) => (list_Seq
                 [Assign 1 (Op Sub [Lookup EndOfHeap;
                     Const (bytes_in_word * n2w (LENGTH args + 1))]);
                  Set EndOfHeap (Var 1);
                  Assign 3 (Const header);
                  StoreEach 1 (3::MAP adjust_var args) 0w;
                  Assign (adjust_var dest)
                    (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                              (Nat (shift_length c − shift (:'a)));
                            Const 1w])],l))
    | RefByte =>
      (case args of
       | [v1;v2] =>
         (MustTerminate
            (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
               (SOME RefByte_location)
                  [adjust_var v1; adjust_var v2] NONE) :'a wordLang$prog,l+1)
       | _ => (Skip,l))
    | RefArray =>
      (case args of
       | [v1;v2] =>
         (MustTerminate
            (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
               (SOME RefArray_location)
                  [adjust_var v1; adjust_var v2] NONE) :'a wordLang$prog,l+1)
       | _ => (Skip,l))
    | FromList tag =>
      (if encode_header c (4 * tag) 0 = (NONE:'a word option) then (GiveUp,l) else
       case args of
       | [v1;v2] =>
         (MustTerminate (list_Seq [
            Assign 1 (Const (n2w (16 * tag)));
            (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
               (SOME FromList_location)
                  [adjust_var v1; adjust_var v2; 1] NONE) :'a wordLang$prog]),l+1)
       | _ => (Skip,l))
    | Label n => (LocValue (adjust_var dest) (2 * n + bvl_num_stubs),l)
    | Equal => (case args of
               | [v1;v2] => (list_Seq [
                   Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op And [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (If Equal 1 (Reg 3) Skip
                       (Seq (MustTerminate
                          (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                                (SOME Equal_location) [1;3] NONE))
                          (Assign 3 (Const 1w))));
                   (If Equal 1 (Reg 3)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
               | _ => (Skip,l))
    | Less => (case args of
               | [v1;v2] => (list_Seq [
                   Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op Or [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (Seq (MustTerminate
                          (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                                (SOME Compare_location) [1;3] NONE))
                          (Assign 3 (Const 1w)));
                   (If Less 1 (Reg 3)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
               | _ => (Skip,l))
    | LessEq => (case args of
               | [v1;v2] => (list_Seq [
                   Assign 1 (Var (adjust_var v1));
                   Assign 3 (Var (adjust_var v2));
                   Assign 5 (Op Or [Var 1; Var 3]);
                   If Test 5 (Imm 1w) Skip
                     (Seq (MustTerminate
                          (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                                (SOME Compare_location) [1;3] NONE))
                          (Assign 3 (Const 1w)));
                   (If NotLess 3 (Reg 1)
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST))],l+1)
               | _ => (Skip,l))
    | LengthBlock => (case args of
               | [v1] => (If Test (adjust_var v1) (Imm 1w)
                           (Assign (adjust_var dest) (Const 0w))
                           (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = Shift Lsr header (Nat k) in
                                 (Shift Lsl len (Nat 2)))),l)
               | _ => (Skip,l))
    | Length => (case args of
               | [v1] => (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = Shift Lsr header (Nat k) in
                                 (Shift Lsl len (Nat 2))),l)
               | _ => (Skip,l))
    | LengthByte => (
        case args of
          | [v1] =>
            (Assign (adjust_var dest)
               (let addr = real_addr c (adjust_var v1) in
                let header = Load addr in
                let k = dimindex(:'a) - shift(:'a) - c.len_size in
                let fakelen = Shift Lsr header (Nat k) in
                let len = Op Sub [fakelen; Const (bytes_in_word-1w)] in
                  (Shift Lsl len (Nat 2))),l)
          | _ => (Skip,l))
    | IsBlock => (case args of
               | [v1] => (If Test (adjust_var v1) (Imm 1w)
                           (If Test (adjust_var v1) (Imm 2w)
                             (Assign (adjust_var dest) FALSE_CONST)
                             (Assign (adjust_var dest) TRUE_CONST))
                           (Seq (Assign 1 (Load (real_addr c (adjust_var v1))))
                             (If Test 1 (Imm 8w)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST))),l)
               | _ => (Skip,l))
    | BlockCmp => (case args of
                   | [v1;v2] => (list_Seq
                       [Assign 1 (Var (adjust_var v1));
                        If Test (adjust_var v1) (Imm 1w) Skip
                          (Assign 1 (Load (real_addr c (adjust_var v1))));
                        Assign 3 (Var (adjust_var v2));
                        If Test (adjust_var v2) (Imm 1w) Skip
                          (Assign 3 (Load (real_addr c (adjust_var v2))));
                        If Equal 1 (Reg 3)
                          (Assign (adjust_var dest) TRUE_CONST)
                          (Assign (adjust_var dest) FALSE_CONST)],l)
               | _ => (Skip,l))
    | TagLenEq tag len => (case args of
               | [v1] => (if len = 0 then
                           if tag < dimword (:'a) DIV 16 then
                             (If Equal (adjust_var v1) (Imm (n2w (16 * tag + 2)))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest) FALSE_CONST),l)
                           else (Assign (adjust_var dest) FALSE_CONST,l)
                         else
                           case encode_header c (4 * tag) len of
                           | NONE => (Assign (adjust_var dest) FALSE_CONST,l)
                           | SOME h =>
                             (list_Seq
                               [Assign 1 (Const 0w);
                                If Test (adjust_var v1) (Imm 1w) Skip
                                  (Assign 1 (Load (real_addr c (adjust_var v1))));
                                If Equal 1 (Imm h)
                                  (Assign (adjust_var dest) TRUE_CONST)
                                  (Assign (adjust_var dest) FALSE_CONST)],l))
               | _ => (Skip,l))
    | TagEq tag => (if tag < dimword (:'a) DIV 16 then
               case args of
               | [v1] => (list_Seq
                   [Assign 1 (Var (adjust_var v1));
                    If Test (adjust_var v1) (Imm 1w) Skip
                      (Assign 1 (let v = adjust_var v1 in
                                 let h = Load (real_addr c v) in
                                   Op And [h; Const (tag_mask c || 2w)]));
                    If Equal 1 (Imm (n2w (16 * tag + 2)))
                      (Assign (adjust_var dest) TRUE_CONST)
                      (Assign (adjust_var dest) FALSE_CONST)],l)
               | _ => (Skip,l)
                    else (Assign (adjust_var dest) FALSE_CONST,l))
    | Add => (case args of
              | [v1;v2] => (list_Seq
                  [(* perform addition *)
                   Inst (Arith (AddOverflow 1 (adjust_var v1)
                                              (adjust_var v2) 3));
                   (* or together bits of overflow flag, and the two inputs *)
                   Assign 3 (Op Or [Var 3; Var (adjust_var v1); Var (adjust_var v2)]);
                   (* if the least significant bit is set, then bignum is needed *)
                   If Test 3 (Imm 1w) Skip
                    (MustTerminate
                      (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                        (SOME Add_location) [adjust_var v1; adjust_var v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | Sub => (case args of
              | [v1;v2] => (list_Seq
                  [(* perform subtraction *)
                   Inst (Arith (SubOverflow 1 (adjust_var v1)
                                              (adjust_var v2) 3));
                   (* or together bits of overflow flag, and the two inputs *)
                   Assign 3 (Op Or [Var 3; Var (adjust_var v1); Var (adjust_var v2)]);
                   (* if the least significant bit is set, then bignum is needed *)
                   If Test 3 (Imm 1w) Skip
                    (MustTerminate
                      (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                        (SOME Sub_location) [adjust_var v1; adjust_var v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | Mult => (case args of
              | [v1;v2] => (list_Seq
                  [MustTerminate
                    (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                      (SOME Mul_location) [adjust_var v1; adjust_var v2] NONE);
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | Div => (case args of
              | [v1;v2] => (list_Seq
                  [MustTerminate
                    (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                      (SOME Div_location) [adjust_var v1; adjust_var v2] NONE);
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | Mod => (case args of
              | [v1;v2] => (list_Seq
                  [MustTerminate
                    (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                      (SOME Mod_location) [adjust_var v1; adjust_var v2] NONE);
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | WordOp W8 opw =>
      (case args of
        | [v1;v2] =>
           (Assign (adjust_var dest)
            (case lookup_word_op opw of
             | Bitwise op => Op op [Var (adjust_var v1); Var (adjust_var v2)]
             | Carried op => let k = Nat (dimindex(:'a)-10) in
               Shift Lsr (Shift Lsl
                 (Op op [Var (adjust_var v1); Var (adjust_var v2)]) k) k), l)
        | _ => (Skip,l))
    | WordOp W64 opw =>
      (case args of
       | [v1;v2] =>
         let len = if dimindex(:'a) < 64 then 2 else 1 in
         (case encode_header c 3 len of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) => (list_Seq [
                Assign 1 (Op Sub [Lookup EndOfHeap; Const (bytes_in_word * n2w (len+1))]);
                if len = 1 then
                  (Assign 3
                     (Op (case opw of Andw => And
                                    | Orw => Or
                                    | Xor => Xor
                                    | Add => Add
                                    | Sub => Sub)
                       [Load (Op Add [real_addr c (adjust_var v1); Const bytes_in_word]);
                        Load (Op Add [real_addr c (adjust_var v2); Const bytes_in_word])]))
                else
                (case lookup_word_op opw of
                 | Bitwise op => list_Seq [
                     Assign 3 (Op op
                      [Load (Op Add [real_addr c (adjust_var v1); Const bytes_in_word]);
                       Load (Op Add [real_addr c (adjust_var v2); Const bytes_in_word])]);
                     Assign 5 (Op op
                       [Load (Op Add [real_addr c (adjust_var v1); Const (bytes_in_word <<1)]);
                        Load (Op Add [real_addr c (adjust_var v2); Const (bytes_in_word <<1)])]);
                     Store (Op Add [Var 1; Const (bytes_in_word <<1)]) 5]
                 | Carried Add => GiveUp (* TODO: 32bit *)
                 | Carried Sub => GiveUp (* TODO: 32bit *));
                Store (Op Add [Var 1; Const bytes_in_word]) 3;
                Assign 3 (Const header);
                Store (Var 1) 3;
                Set EndOfHeap (Var 1);
                Assign (adjust_var dest)
                  (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                            (Nat (shift_length c − shift (:'a)));
                          Const 1w])], l))
       | _ => (Skip,l))
    | WordShift W8 sh n => (case args of
      | [v1] =>
        (Assign (adjust_var dest)
           (case sh of
            | Lsl =>
              Shift Lsr
                (Shift Lsl (Var (adjust_var v1)) (Nat (dimindex(:'a) - 10 + (MIN n 8))))
                (Nat (dimindex(:'a) - 10))
            | Lsr =>
              Shift Lsl
                (Shift Lsr (Var (adjust_var v1)) (Nat ((MIN n 8)+2)))
                (Nat 2)
            | Asr =>
              Shift Lsl
                (Shift Lsr
                   (Shift Asr
                      (Shift Lsl (Var (adjust_var v1)) (Nat (dimindex(:'a) - 10)))
                      (Nat (MIN n 8)))
                   (Nat (dimindex(:'a) - 8)))
                (Nat 2))
        ,l)
      | _ => (Skip,l))
    | WordShift W64 sh n => (case args of
       | [v1] =>
         let len = if dimindex(:'a) < 64 then 2 else 1 in
         (case encode_header c 3 len of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
                (if len = 1 then
                  list_Seq [
                    LoadWord64 c 3 (adjust_var v1);
                    Assign 3
                     (ShiftVar (case sh of Lsl => Lsl | Lsr => Lsr | Asr => Asr)
                        3 n);
                    WriteWord64 c header dest 3]
                 else GiveUp (* TODO: 32bit *)), l)
       | _ => (Skip,l))
    | WordFromInt => (case args of
      | [v1] =>
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (case encode_header c 3 len of
         | NONE => (GiveUp,l)
         | SOME (header:'a word) =>
           (if len = 1 then
             Seq
               (* put the word value into 3 *)
               (If Test (adjust_var v1) (Imm 1w)
                   (* smallnum case *)
                    (Assign 3 (Shift Asr (Var (adjust_var v1)) (Nat 2)))
                   (* bignum case *)
                   (Seq
                     (LoadBignum c 1 3 (adjust_var v1))
                     (If Test 1 (Imm 16w) Skip
                        (Assign 3 (Op Sub [Const 0w; Var 3])))))
               (WriteWord64 c header dest 3)
            else GiveUp (* TODO: 32bit *), l))
      | _ => (Skip, l))
    | WordToInt =>
     (case args of
      | [v] =>
         if dimindex(:'a) = 64 then
           case encode_header c 3 1 of
           | NONE => (GiveUp,l)
           | SOME header =>
             (list_Seq [LoadWord64 c 3 (adjust_var v);
                        Assign 1 (Shift Lsr (Var 3) (Nat 61));
                        If Equal 1 (Imm 0w)
                          (Assign (adjust_var dest) (Shift Lsl (Var 3) (Nat 2)))
                          (WriteWord64 c header dest 3)], l)
         else (GiveUp (* TODO: 32bit *) ,l)
      | _ => (Skip, l))
    | FFI ffi_index =>
      (case args of
       | [v] =>
        let addr = real_addr c (adjust_var v) in
        let header = Load addr in
        let k = dimindex(:'a) - shift(:'a) - c.len_size in
        let fakelen = Shift Lsr header (Nat k) in
        (list_Seq [
          Assign 1 (Op Add [addr; Const bytes_in_word]);
          Assign 3 (Op Sub [fakelen; Const (bytes_in_word-1w)]);
          FFI ffi_index 1 3 (adjust_set (case names of SOME names => names | NONE => LN));
          Assign (adjust_var dest) Unit]
        , l)
       | _ => (Skip,l))
    | _ => (Skip:'a wordLang$prog,l)`;

val comp_def = Define `
  comp c (secn:num) (l:num) (p:dataLang$prog) =
    case p of
    | Skip => (Skip:'a wordLang$prog,l)
    | Tick => (Tick,l)
    | Raise n => (Raise (adjust_var n),l)
    | Return n => (Return 0 (adjust_var n),l)
    | Move n1 n2 => (Move 0 [(adjust_var n1 ,adjust_var n2)],l)
    | Seq p1 p2 =>
        let (q1,l1) = comp c secn l p1 in
        let (q2,l2) = comp c secn l1 p2 in
          (Seq q1 q2,l2)
    | If n p1 p2 =>
        let (q1,l1) = comp c secn l p1 in
        let (q2,l2) = comp c secn l1 p2 in
          (If Equal (adjust_var n) (Imm 2w) q1 q2,l2)
    | MakeSpace n names =>
        let k = dimindex (:'a) DIV 8 in
        let w = n2w (n * k) in
        let w = if w2n w = n * k then w else ~0w in
          (Seq (Assign 1 (Op Sub [Lookup EndOfHeap; Lookup NextFree]))
               (If Lower 1 (Imm w)
                 (Seq (Assign 1 (Const w)) (Alloc 1 (adjust_set names)))
                Skip),l)
    | Assign dest op args names => assign c secn l dest op args names
    | Call ret target args handler =>
        case ret of
        | NONE => (Call NONE target (0::MAP adjust_var args) NONE,l)
        | SOME (n,names) =>
            let ret = SOME (adjust_var n, adjust_set names, Skip, secn, l) in
              case handler of
              | NONE => (Call ret target (MAP adjust_var args) NONE, l+1)
              | SOME (n,p) =>
                  let (q1,l1) = comp c secn (l+2) p in
                  let handler = SOME (adjust_var n, q1, secn, l+1) in
                    (Call ret target (MAP adjust_var args) handler, l1)`

val compile_part_def = Define `
  compile_part c (n,arg_count,p) = (n,arg_count+1n,FST (comp c n 1 p))`

val stubs_def = Define`
  stubs (:α) data_conf = [
    (FromList_location,4n,(FromList_code data_conf):α wordLang$prog );
    (FromList1_location,6n,FromList1_code data_conf);
    (RefByte_location,3n,RefByte_code data_conf);
    (RefArray_location,3n,RefArray_code data_conf);
    (Replicate_location,5n,Replicate_code);
    (AnyArith_location,4n,AnyArith_code data_conf);
    (Add_location,3n,Add_code);
    (Sub_location,3n,Sub_code);
    (Mul_location,3n,Mul_code);
    (Div_location,3n,Div_code);
    (Mod_location,3n,Mod_code);
    (Compare1_location,4n,Compare1_code);
    (Compare_location,3n,Compare_code data_conf);
    (Equal1_location,4n,Equal1_code data_conf);
    (Equal_location,3n,Equal_code data_conf)
  ]`;

val check_stubs_length = Q.store_thm("check_stubs_length",
  `word_num_stubs + LENGTH (stubs (:α) c) = data_num_stubs`,
  EVAL_TAC);

val compile_def = Define `
  compile data_conf word_conf asm_conf prog =
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) prog in
      word_to_word$compile word_conf (asm_conf:'a asm_config) p`;

val _ = export_theory();
