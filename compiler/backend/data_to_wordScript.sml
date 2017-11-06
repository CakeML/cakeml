open preamble wordLangTheory dataLangTheory word_to_wordTheory multiwordTheory
     word_bignumTheory;
local open bvl_to_bviTheory backend_commonTheory in end

val _ = new_theory "data_to_word";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = Datatype `
  (* this configuration is used in data_to_wordProof and stack_alloc *)
  gc_kind =
    None
  | Simple
  | Generational (num list) (* sizes of generations, smallest first *)`

val _ = Datatype `
  config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *)
            ; has_div : bool (* Div available in target *)
            ; has_longdiv : bool (* LongDiv available in target *)
            ; has_fp_ops : bool (* can compile floating-point ops *)
            ; gc_kind : gc_kind (* GC settings *) |>`

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
val LongDiv1_location_def = Define `
  LongDiv1_location = Equal_location+1`;
val LongDiv_location_def = Define `
  LongDiv_location = LongDiv1_location+1`;
val MemCopy_location_def = Define `
  MemCopy_location = LongDiv_location+1`;
val ByteCopy_location_def = Define `
  ByteCopy_location = MemCopy_location+1`;
val ByteCopyAdd_location_def = Define `
  ByteCopyAdd_location = ByteCopy_location+1`;
val ByteCopySub_location_def = Define `
  ByteCopySub_location = ByteCopyAdd_location+1`;
val ByteCopyNew_location_def = Define `
  ByteCopyNew_location = ByteCopySub_location+1`;
val Bignum_location_def = Define `
  Bignum_location = ByteCopyNew_location+1`;

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
val LongDiv1_location_eq = save_thm("LongDiv1_location_eq",
  ``LongDiv1_location`` |> EVAL);
val LongDiv_location_eq = save_thm("LongDiv_location_eq",
  ``LongDiv_location`` |> EVAL);
val MemCopy_location_eq = save_thm("MemCopy_location_eq",
  ``MemCopy_location`` |> EVAL);
val Bignum_location_eq = save_thm("Bignum_location_eq",
  ``Bignum_location`` |> EVAL);
val ByteCopy_location_eq = save_thm("ByteCopy_location_eq",
  ``ByteCopy_location`` |> EVAL);
val ByteCopyAdd_location_eq = save_thm("ByteCopyAdd_location_eq",
  ``ByteCopyAdd_location`` |> EVAL);
val ByteCopySub_location_eq = save_thm("ByteCopySub_location_eq",
  ``ByteCopySub_location`` |> EVAL);
val ByteCopyNew_location_eq = save_thm("ByteCopyNew_location_eq",
  ``ByteCopyNew_location`` |> EVAL);

val AllocVar_def = Define `
  AllocVar (limit:num) (names:num_set) =
    list_Seq [Assign 1 (Shift Lsr (Var 1) (Nat 2));
              If Lower 1 (Imm (n2w limit))
                (Assign 1 (Shift Lsl (Op Add [Var 1; Const 1w]) (Nat (shift (:'a)))))
                (Assign 1 (Const (-1w:'a word)));
              Assign 3 (Op Sub [Lookup TriggerGC; Lookup NextFree]);
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

val WriteLastByte_aux_def = Define`
  WriteLastByte_aux offset a b n p =
    If Equal n (Imm offset) Skip
      (Seq (Inst (Mem Store8 b (Addr a offset))) p)`;

val WriteLastBytes_def = Define`
  WriteLastBytes a b n =
    WriteLastByte_aux (0w:'a word) a b n (
      WriteLastByte_aux 1w a b n (
        WriteLastByte_aux 2w a b n (
          WriteLastByte_aux 3w a b n (
            if dimindex(:'a) = 32 then Skip else
            WriteLastByte_aux 4w a b n (
              WriteLastByte_aux 5w a b n (
                WriteLastByte_aux 6w a b n (
                  WriteLastByte_aux 7w a b n Skip)))))))`;

val RefByte_code_def = Define`
  RefByte_code c =
      let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
      let h = Op Add [Shift Lsr (Var 2) (Nat 2); Const (bytes_in_word - 1w)] in
      let x = SmallLsr h (dimindex (:'a) - 63) in
      let y = Shift Lsl h (Nat (dimindex (:'a) - shift (:'a) - c.len_size)) in
        list_Seq
          [BignumHalt 2;
           Assign 1 x;
           AllocVar limit (fromList [();();()]);
           (* compute length *)
           Assign 5 (Shift Lsr h (Nat (shift (:'a))));
           Assign 7 (Shift Lsl (Var 5) (Nat 2));
           Assign 9 (Lookup NextFree);
           (* adjust end of heap *)
           Assign 1 (Op Add [Var 9;
                             Shift Lsl (Var 5) (Nat (shift (:'a)))]);
           Set NextFree (Op Add [Var 1; Const bytes_in_word]);
           (* 3 := return value *)
           Assign 3 (Op Or [Shift Lsl (Op Sub [Var 9; Lookup CurrHeap])
               (Nat (shift_length c − shift (:'a))); Const (1w:'a word)]);
           (* compute header *)
           Assign 5 (Op Or [Op Or [y; Const 7w]; Var 6]);
           (* compute repeated byte *)
           MakeBytes 4;
           (* store header *)
           Store (Var 9) 5;
           (* return for empty byte array *)
           If Equal 7 (Imm 0w) (Return 0 3)
           (list_Seq [
             (* write last word of byte array *)
             Assign 11 (Op And [Shift Lsr (Var 2) (Nat 2);
                                Const (bytes_in_word - 1w)]);
             If Equal 11 (Imm 0w) Skip
             (list_Seq [
               (* Assign 9 (Op Add [Var 9; Const bytes_in_word]); *)
               Assign 13 (Const 0w);
               Store (Var 1) 13;
               WriteLastBytes 1 4 11;
               Assign 7 (Op Sub [Var 7; Const 4w])]);
             (* write rest of byte array *)
             Call NONE (SOME Replicate_location)
              (* ret_loc, addr, v, n, ret_val *)
              [0;9;4;7;3] NONE])]:'a wordLang$prog`;

val Maxout_bits_code_def = Define `
  Maxout_bits_code rep_len k dest n =
    If Lower n (Imm (n2w (2 ** rep_len)))
      (Assign dest (Op Or [Var dest; Shift Lsl (Var n) (Nat k)]))
      (Assign dest (Op Or [Var dest; Const (all_ones (k + rep_len) k)]))
         :'a wordLang$prog`

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
           Call NONE (SOME FromList1_location) [0;1;4;2;3;5] NONE]):'a wordLang$prog`;

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
             Call NONE (SOME FromList1_location) [0;2;4;6;8;10] NONE])]
      :'a wordLang$prog`;

val RefArray_code_def = Define `
  RefArray_code c =
      let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
        list_Seq
          [BignumHalt 2;
           Move 0 [(1,2)];
           AllocVar limit (fromList [();()]);
           Assign 1 (Shift Lsl (Op Add [(Shift Lsr (Var 2) (Nat 2)); Const 1w])
                      (Nat (shift (:'a))));
           Set TriggerGC (Op Sub [Lookup TriggerGC; Var 1]);
           Assign 1 (Op Sub [Lookup EndOfHeap; Var 1]);
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
              [0;1;4;2;3] NONE]
        :'a wordLang$prog`;

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
                 Call NONE (SOME Replicate_location) [0;2;4;6;8] NONE])
      :'a wordLang$prog`;

val AddNumSize_def = Define `
  AddNumSize c src =
    If Equal (adjust_var src) (Imm 0w) Skip
      (If Test (adjust_var src) (Imm 1w)
         (Assign 1 (Op Add [Var 1; Const 4w]))
       (Assign 1 (Op Add [Var 1;
         (Shift Lsl (Shift Lsr
            (Load (real_addr c (adjust_var src)))
               (Nat (dimindex (:'a) - c.len_size))) (Nat 2))]))):'a wordLang$prog`

val AnyHeader_def = Define `
  AnyHeader c r a t1 (* header *) t2 (* pointer *) t3 (* payload *) =
    If Equal r (Imm (0w:'a word))
      (list_Seq [Assign 7 (Const 0w);
                 Set (Temp t1) (Var r);
                 Set (Temp t2) (Var r);
                 Set (Temp t3) (Var r)])
   (If NotTest r (Imm 1w)
      (list_Seq
        [Assign 7 (real_addr c r);
         Set (Temp t2) (Op Add [Var 7; Const bytes_in_word]);
         Set (Temp t1) (Op Add
           [Shift Lsl (Shift Lsr (Load (Var 7)) (Nat ((dimindex (:'a)) - c.len_size))) (Nat 1);
            Op And [Const 1w; Shift Lsr (Load (Var 7)) (Nat 4)]]);
         Set (Temp t3) (Const 0w)])
   (If NotLess r (Imm 0w)
      (list_Seq
        [Set (Temp t1) (Const 2w);
         Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
         Set (Temp t3) (Shift Lsr (Var r) (Nat 2));
         Assign 7 (Const 0w)])
      (list_Seq
        [Set (Temp t1) (Const 3w);
         Set (Temp t2) (Lookup (if a then OtherHeap else NextFree));
         Set (Temp t3) (Op Sub [Const 0w; Shift Asr (Var r) (Nat 2)]);
         Assign 7 (Const 0w)])))`

val ShiftVar_def = Define `
  ShiftVar sh v n =
    if sh = Ror then
      (let m = if n < dimindex (:'a) then n else n MOD (dimindex (:'a)) in
         if m = 0 then Var v else Shift sh (Var v) (Nat m))
    else if n = 0 then Var v
    else if dimindex (:'a) <= n then
      if sh = Asr then Shift sh (Var v) (Nat (dimindex (:'a) - 1)) else Const 0w
    else (Shift sh (Var v) (Nat n)):'a wordLang$exp`

val AnyArith_code_def = Define `
  AnyArith_code c = list_Seq [
      (* perform allocation *)
      Assign 1 (Const 4w);
      AddNumSize c 0;
      AddNumSize c 1;
      Set (Temp 29w) (Var 1);
      AllocVar (2 ** c.len_size) (fromList [();();()]);
      (* convert smallnums to bignum if necessary *)
      AnyHeader c 2 F 0w 31w 12w;
      AnyHeader c 4 T 1w 30w 11w;
      Get 1 (Temp 11w);
      Store (Lookup OtherHeap) 1;
      Get 1 (Temp 12w);
      Store (Lookup NextFree) 1;
      Get 1 (Temp 29w);
      Assign 2 (Lookup NextFree);
      Set (Temp 29w) (Var 2);
      Set (Temp 3w) (Shift Lsr (Var 6) (Nat 2));
      Assign 3 (Const 0w);
      (* zero out result array *)
      Call (SOME (0,fromList [()],Skip,AnyArith_location,1))
        (SOME Replicate_location) [2;3;1;0] NONE;
      (* perform bignum calculation *)
      Set (Temp 29w) (Op Add [Lookup (Temp 29w); Const bytes_in_word]);
      Call (SOME (1,fromList [()],Skip,AnyArith_location,2))
        (SOME Bignum_location) [] NONE;
      (* convert bignum to smallnum if possible without loss of info *)
      Get 1 (Temp 10w);
      If Test 1 (Reg 1) (Return 0 1) Skip;
      Assign 3 (Load (Op Add [Lookup NextFree; Const bytes_in_word]));
      If Equal 1 (Imm 2w)
        (Seq (Assign 5 (Shift Lsr (Var 3) (Nat (dimindex (:'a) - 3))))
             (If Test 5 (Reg 5)
                (Seq (Assign 1 (Shift Lsl (Var 3) (Nat 2)))
                     (Return 0 1))
                Skip))
        (If Equal 1 (Imm 3w)
          (Seq (Assign 5 (Shift Lsr (Op Sub [Var 3; Const 1w])
                            (Nat (dimindex (:'a) - 3))))
               (If Test 5 (Reg 5)
                  (Seq (Assign 1 (Op Sub [Const 0w; Shift Lsl (Var 3) (Nat 2)]))
                       (Return 0 1))
                  Skip))
          (Assign 5 (Const 0w)));
      (* return the bignum *)
      Assign 5 (Lookup NextFree);
      Assign 6 (ShiftVar Lsr 1 1);
      Assign 8 (Op And [Var 1; Const 1w]);
      Assign 7 (Op Or [Const 0b1111w;
                       ShiftVar Lsl 6 (dimindex (:'a) − c.len_size);
                       ShiftVar Lsl 8 4]);
      Store (Var 5) 7;
      Assign 1 (Op Sub [Var 5; Lookup CurrHeap]);
      Assign 1 (Op Or [ShiftVar Lsl 1 (shift_length c − shift (:'a)); Const 1w]);
      Set NextFree (Op Add [Var 5; Const bytes_in_word;
                            ShiftVar Lsl 6 (shift (:'a))]);
      Return 0 1]:'a wordLang$prog`;

val Add_code_def = Define `
  Add_code = Seq (Assign 6 (Const (n2w (4 * 0))))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)
             :'a wordLang$prog`;

val Sub_code_def = Define `
  Sub_code = Seq (Assign 6 (Const (n2w (4 * 1))))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)
             :'a wordLang$prog`;

val Mul_code_def = Define `
  Mul_code = Seq (Assign 6 (Const (n2w (4 * 4))))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)
             :'a wordLang$prog`;

val Div_code_def = Define `
  Div_code = Seq (Assign 6 (Const (n2w (4 * 5))))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)
             :'a wordLang$prog`;

val Mod_code_def = Define `
  Mod_code = Seq (Assign 6 (Const (n2w (4 * 6))))
                 (Call NONE (SOME AnyArith_location) [0;2;4;6] NONE)
             :'a wordLang$prog`;

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
  Equal1_code =
    list_Seq [
      If Equal 2 (Imm 0w)
        (Seq (Assign 2 (Const 1w)) (Return 0 2)) Skip;
      Assign 1 (Load (Var 4));
      Assign 3 (Load (Var 6));
      Call (SOME (5,list_insert [0;2;4;6] LN,Skip,Equal1_location,1))
        (SOME Equal_location) [1;3] NONE;
      If Equal 5 (Imm 1w) Skip (Return 0 5);
      Assign 2 (Op Sub [Var 2; Const 1w]);
      Assign 4 (Op Add [Var 4; Const bytes_in_word]);
      Assign 6 (Op Add [Var 6; Const bytes_in_word]);
      Call NONE (SOME Equal1_location) [0;2;4;6] NONE]`;

val Equal_code_def = Define `
  Equal_code c =
    list_Seq [
      If Equal 2 (Reg 4)
        (Seq (Assign 2 (Const (1w:'a word))) (Return 0 2)) Skip;
      Assign 1 (Op And [Var 2; Var 4]);
      If Test 1 (Imm 1w)
        (Seq (Assign 2 (Const 0w)) (Return 0 2)) Skip;
      Assign 20 (real_addr c 2);
      Assign 40 (real_addr c 4);
      Assign 21 (Load (Var 20));
      Assign 41 (Load (Var 40));
      If Test 21 (Imm 0b1100w) (list_Seq
          [Assign 1 (Op And [Var 21; Const (tag_mask c ‖ 2w)]);
           If Equal 1 (Imm (n2w (16 * closure_tag + 2)))
             (Seq (Assign 2 (Const 1w)) (Return 0 2)) Skip;
           If Equal 1 (Imm (n2w (16 * partial_app_tag + 2)))
             (Seq (Assign 2 (Const 1w)) (Return 0 2)) Skip;
           If Equal 21 (Reg 41)
             Skip (Seq (Assign 2 (Const 0w)) (Return 0 2));
           Assign 6 (ShiftVar Lsr 21 ((dimindex(:'a) − c.len_size)));
           Assign 20 (Op Add [Var 20; Const bytes_in_word]);
           Assign 40 (Op Add [Var 40; Const bytes_in_word]);
           Call NONE (SOME Equal1_location) [0;6;20;40] NONE])
        Skip;
      If Equal 21 (Reg 41) Skip
        (Seq (Assign 2 (Const 0w)) (Return 0 2));
      If Test 21 (Imm 4w)
        (Seq (Assign 2 (Const 0w)) (Return 0 2)) Skip;
      Assign 1 (Op And [Var 21; Const 24w]);
      If Equal 1 (Imm 16w)
        (Seq (Assign 2 (Const 0w)) (Return 0 2)) Skip;
      Assign 6 (ShiftVar Lsr 21 ((dimindex(:'a) − c.len_size)));
      Assign 2 (Op Add [Var 20; ShiftVar Lsl 6 (shift (:'a))]);
      Assign 4 (Op Add [Var 40; ShiftVar Lsl 6 (shift (:'a))]);
      Call NONE (SOME Compare1_location) [0;6;2;4] NONE]`;

val LongDiv_code_def = Define `
  LongDiv_code c =
    if c.has_longdiv then
      list_Seq [Inst (Arith (LongDiv 1 3 2 4 6));
                Set (Temp 28w) (Var 3);
                Return 0 1]
    else
      Seq (Assign 10 (Const (0w:'a word)))
     (Seq (Assign 11 (Const (n2w (dimindex (:'a)))))
          (Call NONE (SOME LongDiv1_location) [0;11;6;10;10;4;2] NONE))`;

val LongDiv1_code_def = Define `
  LongDiv1_code c =
    if c.has_longdiv then Skip else
    (* the following code is based on multiwordTheory.single_div_loop_def *)
      If Test 2 (Reg 2)
        (Seq (Set (Temp 28w) (Var 10):'a wordLang$prog) (Return 0 8))
        (list_Seq [Assign 6 (Op Or [ShiftVar Lsr 6 1;
                                    ShiftVar Lsl 4 (dimindex (:'a) - 1)]);
                   Assign 4 (ShiftVar Lsr 4 1);
                   Assign 8 (ShiftVar Lsl 8 1);
                   Assign 2 (Op Sub [Var 2; Const (1w:'a word)]);
                   If Lower 12 (Reg 4)
                     (Call NONE (SOME LongDiv1_location)
                       [0;2;4;6;8;10;12] NONE) Skip;
                   If Equal 12 (Reg 4)
                     (If Lower 10 (Reg 6)
                        (Call NONE (SOME LongDiv1_location)
                           [0;2;4;6;8;10;12] NONE) Skip) Skip;
                   Assign 8 (Op Add [Var 8; Const 1w]);
                   Assign 16 (Op Xor [Var 6; Const (-1w)]);
                   Assign 14 (Op Xor [Var 4; Const (-1w)]);
                   Assign 1 (Const 1w);
                   Inst (Arith (AddCarry 10 10 16 1));
                   Inst (Arith (AddCarry 12 12 14 1));
                   Call NONE (SOME LongDiv1_location) [0;2;4;6;8;10;12] NONE])`;

val get_names_def = Define `
  (get_names NONE = LN) /\
  (get_names (SOME x) = x)`;

val LoadWord64_def = Define `
  LoadWord64 c i j =
    Assign i (Load (Op Add [real_addr c j; Const bytes_in_word])):'a wordLang$prog`;

val LoadBignum_def = Define`
  LoadBignum c header word1 k = list_Seq [
    Assign word1 (real_addr c k);
    Assign header (Load (Var word1));
    Assign word1 (Load (Op Add [Var word1; Const bytes_in_word]))]
      :'a wordLang$prog`;

val WriteWord64_def = Define ` (* also works for storing bignums of length 1 *)
  WriteWord64 c (header:'a word) dest i =
    list_Seq [Assign 1 (Lookup NextFree);
              Store (Op Add [Var 1; Const bytes_in_word]) i;
              Assign 3 (Const header);
              Store (Var 1) 3;
              Set NextFree (Op Add [Var 1; Const (2w * bytes_in_word)]);
              Assign (adjust_var dest)
                (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                          (Nat (shift_length c − shift (:'a)));
                        Const 1w])]:'a wordLang$prog`;

val WriteWord64_on_32_def = Define `
  WriteWord64_on_32 c (header:'a word) dest i1 i2 =
    list_Seq [Assign 1 (Lookup NextFree);
              Store (Op Add [Var 1; Const bytes_in_word]) i2;
              Store (Op Add [Var 1; Const (2w * bytes_in_word)]) i1;
              Assign 3 (Const header);
              Store (Var 1) 3;
              Set NextFree (Op Add [Var 1; Const (3w * bytes_in_word)]);
              Assign (adjust_var dest)
                (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                          (Nat (shift_length c − shift (:'a)));
                        Const 1w])]:'a wordLang$prog`;

val WriteWord32_on_32_def = Define `
  WriteWord32_on_32 c header dest i1 =
     list_Seq
       [Assign 1 (Lookup NextFree);
        Store (Op Add [Var 1; Const bytes_in_word]) i1;
        Assign 3 (Const header); Store (Var 1) 3;
        Set NextFree (Op Add [Var 1; Const (2w * bytes_in_word)]);
        Assign (adjust_var dest)
          (Op Or
             [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                (Nat (shift_length c − shift (:α))); Const (1w:'a word)])]`

val WordOp64_on_32_def = Define `
  WordOp64_on_32 (opw:opw) =
    case opw of
    | Andw => list_Seq [Assign 29 (Const 0w);
                        Assign 27 (Const 0w);
                        Assign 33 (Op And [Var 13; Var 23]);
                        Assign 31 (Op And [Var 11; Var 21])]
    | Orw =>  list_Seq [Assign 29 (Const 0w);
                        Assign 27 (Const 0w);
                        Assign 33 (Op Or [Var 13; Var 23]);
                        Assign 31 (Op Or [Var 11; Var 21])]
    | Xor =>  list_Seq [Assign 29 (Const 0w);
                        Assign 27 (Const 0w);
                        Assign 33 (Op Xor [Var 13; Var 23]);
                        Assign 31 (Op Xor [Var 11; Var 21])]
    | Add =>  list_Seq [Assign 29 (Const 0w);
                        Assign 27 (Const 0w);
                        Inst (Arith (AddCarry 33 13 23 29));
                        Inst (Arith (AddCarry 31 11 21 29))]
    | Sub =>  list_Seq [Assign 29 (Const 1w);
                        Assign 27 (Op Xor [Const (-1w); Var 23]);
                        Inst (Arith (AddCarry 33 13 27 29));
                        Assign 27 (Op Xor [Const (-1w); Var 21]);
                        Inst (Arith (AddCarry 31 11 27 29))]`

val WordShift64_on_32_def = Define `
  WordShift64_on_32 sh n = list_Seq
    (* inputs in 11 and 13, writes results in 31 and 33 *)
    (if sh = Ror then
      (let n = n MOD 64 in
        (if n < 32 then
           [Assign 33 (Op Or [ShiftVar Lsl 11 (32 - n);
                              ShiftVar Lsr 13 n]);
            Assign 31 (Op Or [ShiftVar Lsl 13 (32 - n);
                              ShiftVar Lsr 11 n])]
         else
           [Assign 33 (Op Or [ShiftVar Lsl 13 (64 - n);
                              ShiftVar Lsr 11 (n - 32)]);
            Assign 31 (Op Or [ShiftVar Lsl 11 (64 - n);
                              ShiftVar Lsr 13 (n - 32)])]))
    else
      if n < 32 then
        (case sh of
         | Lsl => [Assign 33 (ShiftVar sh 13 n);
                   Assign 31 (Op Or [ShiftVar Lsr 13 (32 - n);
                                     ShiftVar sh 11 n])]
         | Lsr => [Assign 33 (Op Or [ShiftVar Lsl 11 (32 - n);
                                     ShiftVar sh 13 n]);
                   Assign 31 (ShiftVar sh 11 n)]
         | Asr => [Assign 33 (Op Or [ShiftVar Lsl 11 (32 - n);
                                     ShiftVar Lsr 13 n]);
                   Assign 31 (ShiftVar sh 11 n)]
         | Ror => [])
      else
        (case sh of
         | Lsl => [Assign 33 (Const 0w); Assign 31 (ShiftVar sh 13 (n - 32))]
         | Lsr => [Assign 33 (ShiftVar sh 11 (n - 32)); Assign 31 (Const 0w)]
         | Asr => [Assign 33 (ShiftVar sh 11 (n - 32));
                   Assign 31 (ShiftVar sh 11 32)]
         | Ror => []))`;

val bignum_words_def = Define `
  bignum_words c i =
    let (sign,payload) = i2mw i in
      dtcase encode_header c (if sign then 7 else 3) (LENGTH payload) of
      | NONE => NONE
      | SOME h => SOME (h :: payload)`

val Smallnum_def = Define `
  Smallnum i =
    if i < 0 then 0w - n2w (Num (4 * (0 - i))) else n2w (Num (4 * i))`;

val _ = temp_overload_on("FALSE_CONST",``Const (n2w 2:'a word)``)
val _ = temp_overload_on("TRUE_CONST",``Const (n2w 18:'a word)``)

val MemEqList_def = Define `
  (MemEqList a [] = Assign 1 TRUE_CONST :'a wordLang$prog) /\
  (MemEqList a (w::ws) =
     Seq (Assign 5 (Load (Op Add [Var 3; Const a])))
         (If Equal 5 (Imm w) (MemEqList (a + bytes_in_word) ws) Skip))`;

val get_gen_size_def = Define `
  (get_gen_size [] = bytes_in_word * (-1w):'a word) /\
  (get_gen_size (x::xs) =
     if w2n (bytes_in_word:'a word) * x < dimword (:'a)
     then bytes_in_word * n2w x
     else bytes_in_word * (-1w))`;
val fp_cmp_inst_def = Define `
  fp_cmp_inst FP_Less = FPLess 3 0 1 /\
  fp_cmp_inst FP_LessEqual = FPLessEqual 3 0 1 /\
  fp_cmp_inst FP_Greater = FPLess 3 1 0 /\
  fp_cmp_inst FP_GreaterEqual = FPLessEqual 3 1 0 /\
  fp_cmp_inst FP_Equal = FPEqual 3 0 1`;

val fp_bop_inst_def = Define `
  fp_bop_inst FP_Add = FPAdd 0 0 1 /\
  fp_bop_inst FP_Sub = FPSub 0 0 1 /\
  fp_bop_inst FP_Mul = FPMul 0 0 1 /\
  fp_bop_inst FP_Div = FPDiv 0 0 1`

val fp_uop_inst_def = Define `
  fp_uop_inst FP_Neg = FPNeg 0 0 /\
  fp_uop_inst FP_Abs = FPAbs 0 0 /\
  fp_uop_inst FP_Sqrt = FPSqrt 0 0`

local val assign_quotation = `
  assign (c:data_to_word$config) (secn:num) (l:num) (dest:num) (op:closLang$op)
    (args:num list) (names:num_set option) =
    dtcase op of
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
    | Global _ => (Skip,l)
    | SetGlobal _ => (Skip,l)
    | AllocGlobal => (Skip,l)
    | El => (dtcase args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           real_offset c (adjust_var v2)])),l)
             | _ => (Skip,l))
    | Deref => (dtcase args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c (adjust_var v1);
                                           real_offset c (adjust_var v2)])),l)
             | _ => (Skip,l))
    | DerefByte =>
      (dtcase args of
       | [v1;v2] =>
         (list_Seq [
            Assign 1 (Op Add [real_addr c (adjust_var v1);
                              real_byte_offset (adjust_var v2)]);
            Inst (Mem Load8 3 (Addr 1 0w));
            Assign (adjust_var dest) (Shift Lsl (Var 3) (Nat 2))
          ], l)
       | _ => (Skip,l))
    | Update => (dtcase args of
             | [v1;v2;v3] =>
                 (Seq (Store (Op Add [real_addr c (adjust_var v1);
                                      real_offset c (adjust_var v2)])
                             (adjust_var v3))
                      (Assign (adjust_var dest) Unit),l)
             | _ => (Skip,l))
    | UpdateByte => (dtcase args of
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
                    (dtcase encode_header c (4 * tag) (LENGTH args) of
                     | NONE => (GiveUp,l)
                     | SOME (header:'a word) => (list_Seq
                        [Assign 1 (Lookup NextFree);
                         Assign 3 (Const header);
                         StoreEach 1 (3::MAP adjust_var args) 0w;
                         Assign (adjust_var dest)
                           (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                                     (Nat (shift_length c − shift (:'a)));
                                   Const (1w ||
                                           (small_shift_length c − 1 -- 0)
                                              (ptr_bits c tag (LENGTH args)))]);
                         Set NextFree (Op Add [Var 1;
                           Const (bytes_in_word * n2w (LENGTH args + 1))])],l))
    | ConsExtend tag =>
        (dtcase args of
         | (old::start::len::tot::rest) =>
          (dtcase encode_header c (4 * tag) 0 of
             NONE => (GiveUp,l)
           | SOME header =>
              let limit = MIN (2 ** c.len_size) (dimword (:'a) DIV 16) in
              let h = Shift Lsl (Var (adjust_var tot))
                        (Nat (dimindex (:'a) - c.len_size - 2)) in
                (list_Seq
                  [BignumHalt (adjust_var tot);
                   Assign 1 (Var (adjust_var tot));
                   AllocVar limit (list_insert args (get_names names));
                   Assign 1 (Lookup NextFree);
                   Assign 5 (Op Or [h; Const header]);
                   Assign 7 (Shift Lsr (Var (adjust_var tot)) (Nat 2));
                   Assign 9 (Const (n2w tag));
                   StoreEach 1 (5::MAP adjust_var rest) 0w;
                   Make_ptr_bits_code c 9 7 3;
                   Set NextFree (Op Add [Var 1; Const bytes_in_word;
                     Shift Lsl (Var 7) (Nat (shift (:'a)))]);
                   Assign 15 (Var (adjust_var len));
                   Assign 13 (Op Add [Var 1;
                     Const (bytes_in_word * n2w (LENGTH rest + 1))]);
                   Assign 11 (Op Add [real_addr c (adjust_var old);
                     Const bytes_in_word;
                     ShiftVar Lsl (adjust_var start) (shift (:'a) - 2)]);
                   If Test 15 (Reg 15) (Assign (adjust_var dest) (Var 3)) (list_Seq [
                     MustTerminate
                       (Call (SOME (adjust_var dest,adjust_set (get_names names),
                             Skip,secn,l))
                          (SOME MemCopy_location) [15;11;13;3] NONE)])]),l+1)
         | _ => (Skip,l))
    | Ref => (dtcase encode_header c 2 (LENGTH args) of
              | NONE => (GiveUp,l)
              | SOME (header:'a word) => (list_Seq
                 [Set TriggerGC (Op Sub [Lookup TriggerGC;
                     Const (bytes_in_word * n2w (LENGTH args + 1))]);
                  Assign 1 (Op Sub [Lookup EndOfHeap;
                     Const (bytes_in_word * n2w (LENGTH args + 1))]);
                  Set EndOfHeap (Var 1);
                  Assign 3 (Const header);
                  StoreEach 1 (3::MAP adjust_var args) 0w;
                  Assign (adjust_var dest)
                    (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                              (Nat (shift_length c − shift (:'a)));
                            Const 1w])],l))
    | RefByte immutable =>
      (dtcase args of
       | [v1;v2] =>
         (Seq
           (Assign 1 (Const (if immutable then 0w else 16w))) (* n.b. this would have been better done with Set Temp *)
           (MustTerminate
             (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
                (SOME RefByte_location)
                   [adjust_var v1; adjust_var v2; 1] NONE) :'a wordLang$prog),l+1)
       | _ => (Skip,l))
    | CopyByte alloc_new =>
      (dtcase args of
       | [v1;v2;v3;v4;v5] (* alloc_new is F *) =>
           (MustTerminate
             (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
                (SOME ByteCopy_location)
                   [adjust_var v1; adjust_var v2; adjust_var v3;
                    adjust_var v4; adjust_var v5] NONE) :'a wordLang$prog,l+1)
       | [v1;v2;v3] (* alloc_new is T *) =>
           (MustTerminate
             (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
                (SOME ByteCopyNew_location)
                   [adjust_var v1; adjust_var v2;
                    adjust_var v3] NONE) :'a wordLang$prog,l+1)
       | _ => (Skip,l))
    | RefArray =>
      (dtcase args of
       | [v1;v2] =>
         (MustTerminate
            (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
               (SOME RefArray_location)
                  [adjust_var v1; adjust_var v2] NONE) :'a wordLang$prog,l+1)
       | _ => (Skip,l))
    | FromList tag =>
      (if encode_header c (4 * tag) 0 = (NONE:'a word option) then (GiveUp,l) else
       dtcase args of
       | [v1;v2] =>
         (MustTerminate (list_Seq [
            Assign 1 (Const (n2w (16 * tag)));
            (Call (SOME (adjust_var dest,adjust_set (get_names names),Skip,secn,l))
               (SOME FromList_location)
                  [adjust_var v1; adjust_var v2; 1] NONE) :'a wordLang$prog]),l+1)
       | _ => (Skip,l))
    | Label n => (LocValue (adjust_var dest) n,l)
    | LessConstSmall i =>
       (dtcase args of
        | [v1] => (If Less (adjust_var v1) (Imm (n2w (4 * i)))
                    (Assign (adjust_var dest) TRUE_CONST)
                    (Assign (adjust_var dest) FALSE_CONST),l)
        | _ => (Skip,l))
    | BoundsCheckByte leq =>
     (dtcase args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let extra = (if dimindex (:'a) = 32 then 2 else 3) in
                                let k = dimindex (:'a) - c.len_size - extra in
                                let kk = (if dimindex (:'a) = 32 then 3w else 7w) in
                                  Op Sub [Shift Lsr header (Nat k); Const kk]);
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              (if leq then If NotLower 1 (Reg 3) else
                                           If Lower 3 (Reg 1))
                                 (Assign (adjust_var dest) TRUE_CONST)
                                 (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip,l))
    | BoundsCheckArray =>
      (dtcase args of
      | [v1;v2] => (list_Seq [Assign 1
                               (let addr = real_addr c (adjust_var v1) in
                                let header = Load addr in
                                let k = dimindex (:'a) - c.len_size in
                                  Shift Lsr header (Nat k));
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip,l))
    | BoundsCheckBlock =>
      (dtcase args of
      | [v1;v2] => (list_Seq [If Test (adjust_var v1) (Imm 1w)
                               (Assign 1 (Const 0w))
                               (Assign 1
                                 (let addr = real_addr c (adjust_var v1) in
                                  let header = Load addr in
                                  let k = dimindex (:'a) - c.len_size in
                                    Shift Lsr header (Nat k)));
                              Assign 3 (ShiftVar Ror (adjust_var v2) 2);
                              If Lower 3 (Reg 1)
                               (Assign (adjust_var dest) TRUE_CONST)
                               (Assign (adjust_var dest) FALSE_CONST)],l)
      | _ => (Skip,l))
    | Equal => (dtcase args of
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
    | Less => (dtcase args of
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
    | LessEq => (dtcase args of
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
    | LengthBlock => (dtcase args of
               | [v1] => (If Test (adjust_var v1) (Imm 1w)
                           (Assign (adjust_var dest) (Const 0w))
                           (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = Shift Lsr header (Nat k) in
                                 (Shift Lsl len (Nat 2)))),l)
               | _ => (Skip,l))
    | Length => (dtcase args of
               | [v1] => (Assign (adjust_var dest)
                              (let addr = real_addr c (adjust_var v1) in
                               let header = Load addr in
                               let k = dimindex (:'a) - c.len_size in
                               let len = Shift Lsr header (Nat k) in
                                 (Shift Lsl len (Nat 2))),l)
               | _ => (Skip,l))
    | LengthByte => (
        dtcase args of
          | [v1] =>
            (Assign (adjust_var dest)
               (let addr = real_addr c (adjust_var v1) in
                let header = Load addr in
                let k = dimindex(:'a) - shift(:'a) - c.len_size in
                let fakelen = Shift Lsr header (Nat k) in
                let len = Op Sub [fakelen; Const (bytes_in_word-1w)] in
                  (Shift Lsl len (Nat 2))),l)
          | _ => (Skip,l))
    | TagLenEq tag len => (dtcase args of
               | [v1] => (if len = 0 then
                           if tag < dimword (:'a) DIV 16 then
                             (If Equal (adjust_var v1) (Imm (n2w (16 * tag + 2)))
                                (Assign (adjust_var dest) TRUE_CONST)
                                (Assign (adjust_var dest) FALSE_CONST),l)
                           else (Assign (adjust_var dest) FALSE_CONST,l)
                         else
                           dtcase encode_header c (4 * tag) len of
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
               dtcase args of
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
    | Add => (dtcase args of
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
    | Sub => (dtcase args of
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
    | Mult => (dtcase args of
              | [v1;v2] => (list_Seq
                  [Assign 1 (ShiftVar Lsr (adjust_var v1) 1);
                   Inst (Arith (LongMul 3 1 1 (adjust_var v2)));
                   Assign 3 (Op Or [Var 3;
                               Op And [Const 1w;
                                 Op Or [Var (adjust_var v1); Var (adjust_var v2)]]]);
                   Assign 1 (ShiftVar Lsr 1 1);
                   If Equal 3 (Imm 0w) Skip
                     (MustTerminate
                       (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                        (SOME Mul_location) [adjust_var v1; adjust_var v2] NONE));
                   Move 2 [(adjust_var dest,1)]],l+1)
              | _ => (Skip,l))
    | Div => (dtcase args of
              | [v1;v2] => (list_Seq [
           Assign 1 (Op Or [Var (adjust_var v1); Var (adjust_var v2)]);
           Assign 1 (Op Or [Var 1; ShiftVar Lsr 1 (dimindex (:'a)-1)]);
           If Test 1 (Imm (1w:'a word))
             (if c.has_div then
                list_Seq [Inst (Arith (Div 1 (adjust_var v1) (adjust_var v2)));
                          Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
              else if c.has_longdiv then
                list_Seq [Assign 1 (Const 0w);
                          Inst (Arith (LongDiv 1 3 1 (adjust_var v1)(adjust_var v2)));
                          Assign (adjust_var dest) (ShiftVar Lsl 1 2)]
              else
                list_Seq
                  [Assign 1 (Const 0w);
                   MustTerminate
                    (Call (SOME (1,adjust_set (get_names names),Skip,secn,l+1))
                      (SOME LongDiv_location)
                        [1; adjust_var v1; adjust_var v2] NONE);
                   Assign (adjust_var dest) (ShiftVar Lsl 1 2)])
             (list_Seq
                [MustTerminate
                   (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                      (SOME Div_location) [adjust_var v1; adjust_var v2] NONE);
                 Move 2 [(adjust_var dest,1)]])],l + 2)
                  | _ => (Skip,l))
    | Mod => (dtcase args of
              | [v1;v2] => (list_Seq [
           Assign 1 (Op Or [Var (adjust_var v1); Var (adjust_var v2)]);
           Assign 1 (Op Or [Var 1; ShiftVar Lsr 1 (dimindex (:'a)-1)]);
           If Test 1 (Imm (1w:'a word))
             (if c.has_div then
                list_Seq [Inst (Arith (Div 1 (adjust_var v1) (adjust_var v2)));
                          Inst (Arith (LongMul 3 1 1 (adjust_var v2)));
                          Assign (adjust_var dest)
                            (Op Sub [Var (adjust_var v1); Var 1])]
              else if c.has_longdiv then
                list_Seq [Assign 1 (Const 0w);
                          Inst (Arith (LongDiv 1 3 1 (adjust_var v1)(adjust_var v2)));
                          Move 2 [(adjust_var dest,3)]]
              else
                list_Seq
                  [Assign 1 (Const 0w);
                   MustTerminate
                    (Call (SOME (1,adjust_set (get_names names),Skip,secn,l+1))
                      (SOME LongDiv_location)
                        [1; adjust_var v1; adjust_var v2] NONE);
                   Get (adjust_var dest) (Temp 28w)])
             (list_Seq
                [MustTerminate
                   (Call (SOME (1,adjust_set (get_names names),Skip,secn,l))
                      (SOME Mod_location) [adjust_var v1; adjust_var v2] NONE);
                 Move 2 [(adjust_var dest,1)]])],l + 2)
                  | _ => (Skip,l))
    | WordOp W8 opw =>
      (dtcase args of
        | [v1;v2] =>
           (Assign (adjust_var dest)
            (dtcase lookup_word_op opw of
             | Bitwise op => Op op [Var (adjust_var v1); Var (adjust_var v2)]
             | Carried op => let k = Nat (dimindex(:'a)-10) in
               Shift Lsr (Shift Lsl
                 (Op op [Var (adjust_var v1); Var (adjust_var v2)]) k) k), l)
        | _ => (Skip,l))
    | WordOp W64 opw =>
      (dtcase args of
       | [v1;v2] =>
       (if dimindex(:'a) = 64 then
         (dtcase encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
                (Seq (Assign 3
                  (Op (dtcase opw of
                          Andw => And
                        | Orw => Or
                        | Xor => Xor
                        | Add => Add
                        | Sub => Sub)
                         [Load
                            (Op Add
                               [real_addr c (adjust_var v1);
                                Const bytes_in_word]);
                          Load
                            (Op Add
                               [real_addr c (adjust_var v2);
                                Const bytes_in_word])]))
                   (WriteWord64 c header dest 3),l))
        else
         (dtcase encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w * bytes_in_word)]));
               WordOp64_on_32 opw;
               WriteWord64_on_32 c header dest 33 31],l)))
       | _ => (Skip,l))
    | WordShift W8 sh n => (dtcase args of
      | [v1] =>
        (Assign (adjust_var dest)
           (dtcase sh of
            | Lsl =>
              Shift Lsr
                (Shift Lsl (Var (adjust_var v1)) (Nat(dimindex(:'a)-10+(MIN n 8))))
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
                (Nat 2)
            | Ror =>
              (let n = n MOD 8 in
                 Op Or
                  [Shift Lsl (ShiftVar Lsr (adjust_var v1) (n + 2)) (Nat 2);
                   Shift Lsr (ShiftVar Lsl (adjust_var v1)
                     ((dimindex (:'a) - 2) - n)) (Nat (dimindex (:'a) - 10))])),l)
      | _ => (Skip,l))
    | WordShift W64 sh n => (dtcase args of
       | [v1] =>
         let len = if dimindex(:'a) < 64 then 2 else 1 in
         (dtcase encode_header c 3 len of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (if len = 1 then
               list_Seq
                 [LoadWord64 c 3 (adjust_var v1);
                  Assign 3 (ShiftVar sh 3 n);
                  WriteWord64 c header dest 3]
             else
               list_Seq [
                 Assign 15 (real_addr c (adjust_var v1));
                 Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
                 Assign 13 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
                 WordShift64_on_32 sh n;
                 WriteWord64_on_32 c header dest 33 31],l))
       | _ => (Skip,l))
    | WordFromInt => (dtcase args of
      | [v1] =>
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (dtcase encode_header c 3 len of
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
            else If Test (adjust_var v1) (Imm 1w)
              (list_Seq [
                Assign 3 (Shift Asr (Var (adjust_var v1)) (Nat 2));
                Assign 5 (Shift Asr (Var (adjust_var v1)) (Nat 31));
                WriteWord64_on_32 c header dest 3 5
              ])
              GiveUp (* TODO: 32bit bignum *)), l)
      | _ => (Skip, l))
   | WordToInt =>
     (dtcase args of
      | [v] =>
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (dtcase encode_header c 3 len of
           | NONE => (GiveUp,l)
           | SOME header =>
             if len = 1 then
               (list_Seq [LoadWord64 c 3 (adjust_var v);
                          Assign 1 (Shift Lsr (Var 3) (Nat 61));
                          If Equal 1 (Imm 0w)
                            (Assign (adjust_var dest) (Shift Lsl (Var 3) (Nat 2)))
                            (WriteWord64 c header dest 3)], l)
             else
              (dtcase encode_header c 3 1 of
               | NONE => (GiveUp,l)
               | SOME header1 =>
                 (list_Seq [
                  Assign 15 (real_addr c (adjust_var v));
                  Assign 13 (Load (Op Add [Var 15; Const bytes_in_word]));
                  Assign 11 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
                  If NotEqual 13 (Imm 0w)
                    (WriteWord64_on_32 c header dest 13 11)
                    (list_Seq [
                      Assign 1 (Shift Lsr (Var 11) (Nat 29));
                      If Equal 1 (Imm 0w)
                        (Assign (adjust_var dest) (Shift Lsl (Var 11) (Nat 2)))
                        (WriteWord32_on_32 c header1 dest 11)])],l)))
      | _ => (Skip, l))
    | FFI ffi_index =>
      (dtcase args of
       | [v1; v2] =>
        let addr1 = real_addr c (adjust_var v1) in
        let header1 = Load addr1 in
        let k = dimindex(:'a) - shift(:'a) - c.len_size in
        let fakelen1 = Shift Lsr header1 (Nat k) in
        let addr2 = real_addr c (adjust_var v2) in
        let header2 = Load addr2 in
        let fakelen2 = Shift Lsr header2 (Nat k) in
        (list_Seq [
          Assign 1 (Op Add [addr1; Const bytes_in_word]);
          Assign 3 (Op Sub [fakelen1; Const (bytes_in_word-1w)]);
          Assign 5 (Op Add [addr2; Const bytes_in_word]);
          Assign 7 (Op Sub [fakelen2; Const (bytes_in_word-1w)]);
          FFI ffi_index 1 3 5 7 (adjust_set (dtcase names of SOME names => names | NONE => LN));
          Assign (adjust_var dest) Unit]
        , l)
       | _ => (Skip,l))
    | EqualInt i => (dtcase args of
       | [v] =>
           (if -&(dimword (:'a) DIV 8) <= i /\ i < &(dimword (:'a) DIV 8)
            then (If Equal (adjust_var v) (Imm (Smallnum i))
                    (Assign (adjust_var dest) TRUE_CONST)
                    (Assign (adjust_var dest) FALSE_CONST),l)
            else (dtcase bignum_words c i of
                 | NONE => (Assign (adjust_var dest) FALSE_CONST,l)
                 | SOME words =>
                     If Test (adjust_var v) (Imm 1w)
                       (Assign (adjust_var dest) FALSE_CONST)
                       (list_Seq
                          [Assign 1 FALSE_CONST;
                           Assign 3 (real_addr c (adjust_var v));
                           MemEqList 0w words;
                           Assign (adjust_var dest) (Var 1)]),l))
       | _ => (Skip,l))
    | FP_cmp fpc => (dtcase args of
       | [v1;v2] =>
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
           ((list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const bytes_in_word]));
               Assign 5 (Load (Op Add
                           [real_addr c (adjust_var v2); Const bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (FPMovFromReg 1 5 5));
               Inst (FP (fp_cmp_inst fpc));
               Assign (adjust_var dest) (Op Add [ShiftVar Lsl 3 4; Const 2w])],l))
        else
           ((list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w * bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (FPMovFromReg 1 23 21));
               Inst (FP (fp_cmp_inst fpc));
               Assign (adjust_var dest) (Op Add [ShiftVar Lsl 3 4; Const 2w])],l)))
       | _ => (Skip,l))
    | FP_bop fpb => (dtcase args of
       | [v1;v2] =>
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
         (dtcase encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const bytes_in_word]));
               Assign 5 (Load (Op Add
                           [real_addr c (adjust_var v2); Const bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (FPMovFromReg 1 5 5));
               Inst (FP (fp_bop_inst fpb));
               Inst (FP (FPMovToReg 3 5 0));
               WriteWord64 c header dest 3],l))
        else
         (dtcase encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 17 (real_addr c (adjust_var v2));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
               Assign 21 (Load (Op Add [Var 17; Const bytes_in_word]));
               Assign 23 (Load (Op Add [Var 17; Const (2w * bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (FPMovFromReg 1 23 21));
               Inst (FP (fp_bop_inst fpb));
               Inst (FP (FPMovToReg 5 3 0));
               WriteWord64_on_32 c header dest 5 3],l)))
       | _ => (Skip,l))
    | FP_uop fpu => (dtcase args of
       | [v1] =>
       (if ~c.has_fp_ops then (GiveUp,l) else
        if dimindex(:'a) = 64 then
         (dtcase encode_header c 3 1 of
          | NONE => (GiveUp,l)
          | SOME (header:'a word) =>
            (list_Seq [
               Assign 3 (Load (Op Add
                           [real_addr c (adjust_var v1); Const bytes_in_word]));
               Inst (FP (FPMovFromReg 0 3 3));
               Inst (FP (fp_uop_inst fpu));
               Inst (FP (FPMovToReg 3 5 0));
               WriteWord64 c header dest 3],l))
        else
         (dtcase encode_header c 3 2 of
          | NONE => (GiveUp,l)
          | SOME header =>
            (list_Seq [
               Assign 15 (real_addr c (adjust_var v1));
               Assign 11 (Load (Op Add [Var 15; Const bytes_in_word]));
               Assign 13 (Load (Op Add [Var 15; Const (2w * bytes_in_word)]));
               Inst (FP (FPMovFromReg 0 13 11));
               Inst (FP (fp_uop_inst fpu));
               Inst (FP (FPMovToReg 5 3 0));
               WriteWord64_on_32 c header dest 5 3],l)))
       | _ => (Skip,l))
    | _ => (Skip:'a wordLang$prog,l)`;

val assign_pmatch_lemmas = [
  Q.prove(`
   (case args of
       [v1;v2] => y v1 v2
     | _ => z) = (dtcase args of
       [v1;v2] => y v1 v2
     | _ => z)`,
   CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
   >> fs[]),
  Q.prove(`
   (case args of
       (old::start::len::tot::rest) => y old start len tot rest
     | _ => z) = (dtcase args of
       (old::start::len::tot::rest) => y old start len tot rest
     | _ => z)`,
   CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
   >> fs[]),
  Q.prove(`
   (case args of
      [v1;v2;v3] => y v1 v2 v3
    | _ => z) = (dtcase args of
      [v1;v2;v3] => y v1 v2 v3
    | _ => z)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case args of
    | [v1;v2;v3;v4;v5] => y1 v1 v2 v3 v4 v5
    | [v1;v2;v3] => y2 v1 v2 v3
    | _ => z) = (dtcase args of
    | [v1;v2;v3;v4;v5] => y1 v1 v2 v3 v4 v5
    | [v1;v2;v3] => y2 v1 v2 v3
    | _ => z)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case opt of
      NONE => y
    | SOME x => z x) = (dtcase opt of
      NONE => y
    | SOME x => z x)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case args of
      [v1] => y v1
    | _ => z) = (dtcase args of
      [v1] => y v1
    | _ => z)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case op of
      Bitwise op => y op
    | Carried op => z op) = (dtcase op of
      Bitwise op => y op
    | Carried op => z op)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case op of
      Bitwise op => y op
    | Carried Add => z
    | Carried Sub => x) = (dtcase op of
      Bitwise op => y op
    | Carried Add => z
    | Carried Sub => x)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case a of
      Lsl => x
    | Lsr => y
    | Asr => z) = (dtcase a of
      Lsl => x
    | Lsr => y
    | Asr => z)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case opw of
      Andw => And
    | Orw => Or
    | Xor => Xor
    | Add => Add
    | Sub => Sub) = (dtcase opw of
      Andw => And
    | Orw => Or
    | Xor => Xor
    | Add => Add
    | Sub => Sub)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[]),
  Q.prove(`
   (case opt of
        SOME x => y x
      | NONE => z) = (dtcase opt of
        SOME x => y x
      | NONE => z)`,
  CONV_TAC(RATOR_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV))
  >> fs[])]

in
val assign_def = Define assign_quotation

val assign_pmatch = Q.store_thm("assign_pmatch", `∀c secn l dest op args names.` @
  (assign_quotation |>
   map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
       | aq => aq)),
  rpt strip_tac
  >> Ho_Rewrite.PURE_REWRITE_TAC assign_pmatch_lemmas
  >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
  >> ASSUME_TAC(Q.SPEC `op` (fetch "closLang" "op_nchotomy") )
  >> Cases_on `op` >> fs []
  >> fs[assign_def]
  >> Cases_on `w` >> fs[]
  >> every_case_tac >> fs []);
end

val comp_def = Define `
  comp c (secn:num) (l:num) (p:dataLang$prog) =
    dtcase p of
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
          (If Equal (adjust_var n) (Imm 18w) q1 q2,l2)
    | MakeSpace n names =>
        let k = dimindex (:'a) DIV 8 in
        let w = n2w (n * k) in
        let w = if w2n w = n * k then w else ~0w in
          (Seq (Assign 1 (Op Sub [Lookup TriggerGC; Lookup NextFree]))
               (If Lower 1 (Imm w)
                 (Seq (Assign 1 (Const w)) (Alloc 1 (adjust_set names)))
                Skip),l)
    | Assign dest op args names => assign c secn l dest op args names
    | Call ret target args handler =>
        dtcase ret of
        | NONE => (Call NONE target (0::MAP adjust_var args) NONE,l)
        | SOME (n,names) =>
            let ret = SOME (adjust_var n, adjust_set names, Skip, secn, l) in
              dtcase handler of
              | NONE => (Call ret target (MAP adjust_var args) NONE, l+1)
              | SOME (n,p) =>
                  let (q1,l1) = comp c secn (l+2) p in
                  let handler = SOME (adjust_var n, q1, secn, l+1) in
                    (Call ret target (MAP adjust_var args) handler, l1)`

val compile_part_def = Define `
  compile_part c (n,arg_count,p) = (n,arg_count+1n,FST (comp c n 1 p))`

val MemCopy_code_def = Define `
  MemCopy_code =
    If Test 2 (Reg 2) (Return 0 8)
        (list_Seq [Assign 1 (Load (Var 4));
                   Assign 2 (Op Sub [Var 2; Const 4w]);
                   Assign 4 (Op Add [Var 4; Const bytes_in_word]);
                   Store (Var 6) 1;
                   Assign 6 (Op Add [Var 6; Const bytes_in_word]);
                   Call NONE (SOME MemCopy_location) [0;2;4;6;8] NONE])
      :'a wordLang$prog`;

val ByteCopy_code_def = Define `
  ByteCopy_code c = list_Seq
     [Assign 4 (ShiftVar Lsr 4 2);
      Assign 6 (ShiftVar Lsr 6 2);
      Assign 10 (ShiftVar Lsr 10 2);
      Assign 1 Unit;
      Assign 2 (Op Add [real_addr c 2; Const bytes_in_word; Var 4]);
      Assign 8 (Op Add [real_addr c 8; Const bytes_in_word; Var 10]);
      If Lower 4 (Reg 10)
        (list_Seq [Assign 3 (Op Sub [Var 6; Const 1w]);
                   Assign 2 (Op Add [Var 2; Var 3]);
                   Assign 8 (Op Add [Var 8; Var 3]);
                   Call NONE (SOME ByteCopySub_location) [0;6;2;8;1] NONE])
        (Call NONE (SOME ByteCopyAdd_location) [0;6;2;8;1] NONE)]
     :'a wordLang$prog`;

val ByteCopyAdd_code_def = Define`
  ByteCopyAdd_code =
  If Lower 2 (Imm 4w) (* n <+ 4w *)
    (
      If Lower 2 (Imm 2w) (* n <+ 2w *)
      (
        If Equal 2 (Imm 0w) (Return 0 8) (* n = 0w *)
        (
          list_Seq[
            Inst (Mem Load8 1 (Addr 4 0w));
            Inst (Mem Store8 1(Addr 6 0w));
            Return 0 8
          ]
        )
      )
      (list_Seq [
        Inst (Mem Load8 1 (Addr 4 0w));
        Inst (Mem Load8 3 (Addr 4 1w));
        If Equal 2 (Imm 2w)
          (list_Seq [
            Inst (Mem Store8 1 (Addr 6 0w));
            Inst (Mem Store8 3 (Addr 6 1w));
            Return 0 8
          ])
          (list_Seq [
            Inst (Mem Load8 5 (Addr 4 2w));
            Inst (Mem Store8 1 (Addr 6 0w));
            Inst (Mem Store8 3 (Addr 6 1w));
            Inst (Mem Store8 5 (Addr 6 2w));
            Return 0 8
          ])
      ])
    )
    (list_Seq [
     Inst (Mem Load8 1 (Addr 4 0w));
     Inst (Mem Load8 3 (Addr 4 1w));
     Inst (Mem Load8 5 (Addr 4 2w));
     Inst (Mem Load8 7 (Addr 4 3w));
     Inst (Mem Store8 1 (Addr 6 0w));
     Inst (Mem Store8 3 (Addr 6 1w));
     Inst (Mem Store8 5 (Addr 6 2w));
     Inst (Mem Store8 7 (Addr 6 3w));
     Assign 9 (Op Sub [Var 2; Const 4w]);
     Assign 11 (Op Add [Var 4; Const 4w]);
     Assign 13 (Op Add [Var 6; Const 4w]);
     Call NONE (SOME ByteCopyAdd_location) [0;9;11;13;8] NONE
    ])`

val ByteCopySub_code_def = Define`
  ByteCopySub_code =
  If Lower 2 (Imm 4w) (* n <+ 4w *)
    (
      If Lower 2 (Imm 2w) (* n <+ 2w *)
      (
        If Equal 2 (Imm 0w) (Return 0 8) (* n = 0w *)
        (
          list_Seq[
            Inst (Mem Load8 1 (Addr 4 0w));
            Inst (Mem Store8 1(Addr 6 0w));
            Return 0 8
          ]
        )
      )
      (list_Seq [
        Inst (Mem Load8 1 (Addr 4 0w));
        Inst (Mem Load8 3 (Addr 4 (-1w)));
        If Equal 2 (Imm 2w)
          (list_Seq [
            Inst (Mem Store8 1 (Addr 6 0w));
            Inst (Mem Store8 3 (Addr 6 (-1w)));
            Return 0 8
          ])
          (list_Seq [
            Inst (Mem Load8 5 (Addr 4 (-2w)));
            Inst (Mem Store8 1 (Addr 6 0w));
            Inst (Mem Store8 3 (Addr 6 (-1w)));
            Inst (Mem Store8 5 (Addr 6 (-2w)));
            Return 0 8
          ])
      ])
    )
    (list_Seq [
     Inst (Mem Load8 1 (Addr 4 0w));
     Inst (Mem Load8 3 (Addr 4 (-1w)));
     Inst (Mem Load8 5 (Addr 4 (-2w)));
     Inst (Mem Load8 7 (Addr 4 (-3w)));
     Inst (Mem Store8 1 (Addr 6 0w));
     Inst (Mem Store8 3 (Addr 6 (-1w)));
     Inst (Mem Store8 5 (Addr 6 (-2w)));
     Inst (Mem Store8 7 (Addr 6 (-3w)));
     Assign 9 (Op Sub [Var 2; Const 4w]);
     Assign 11 (Op Sub [Var 4; Const 4w]);
     Assign 13 (Op Sub [Var 6; Const 4w]);
     Call NONE (SOME ByteCopySub_location) [0;9;11;13;8] NONE
    ])`

val ByteCopyNew_code_def = Define `
  ByteCopyNew_code c = Skip :'a wordLang$prog`;

val stubs_def = Define`
  stubs (:α) data_conf = [
    (FromList_location,4n,(FromList_code data_conf):α wordLang$prog );
    (FromList1_location,6n,FromList1_code data_conf);
    (RefByte_location,4n,RefByte_code data_conf);
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
    (Equal1_location,4n,Equal1_code);
    (Equal_location,3n,Equal_code data_conf);
    (LongDiv1_location,7n,LongDiv1_code data_conf);
    (LongDiv_location,4n,LongDiv_code data_conf);
    (MemCopy_location,5n,MemCopy_code);
    (ByteCopy_location,6n,ByteCopy_code data_conf);
    (ByteCopyAdd_location,5n,ByteCopyAdd_code);
    (ByteCopySub_location,5n,ByteCopySub_code);
    (ByteCopyNew_location,4n,ByteCopyNew_code data_conf)
  ] ++ generated_bignum_stubs Bignum_location`;

val check_stubs_length = Q.store_thm("check_stubs_length",
  `word_num_stubs + LENGTH (stubs (:α) c) = data_num_stubs`,
  EVAL_TAC);

val check_LongDiv_location = Q.store_thm("check_LongDiv_location",
  `LongDiv_location = word_bignum$div_location`,
  EVAL_TAC);

val compile_def = Define `
  compile data_conf word_conf asm_conf prog =
    let data_conf = (data_conf with has_fp_ops := (1 < asm_conf.fp_reg_count)) in
    let p = stubs (:α) data_conf ++ MAP (compile_part data_conf) prog in
      word_to_word$compile word_conf (asm_conf:'a asm_config) p`;

val _ = export_theory();
