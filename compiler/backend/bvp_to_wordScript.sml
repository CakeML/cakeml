open preamble wordLangTheory bvpTheory word_to_wordTheory;
local open bvl_to_bviTheory in end

val _ = new_theory "bvp_to_word";

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

val make_header_def = Define `
  make_header conf tag len =
    let l = dimindex (:'a) - conf.len_size in
      (n2w len << l || tag << 2 || 3w:'a word)`

val tag_mask_def = Define `
  tag_mask conf =
    let l = dimindex (:'a) - conf.len_size in
      (l-1 '' 2) (~0w:'a word)`

val encode_header_def = Define `
  encode_header (conf:bvp_to_word$config) tag len =
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

val shift_length_def = Define `
  shift_length conf = 1 + conf.pad_bits + conf.len_bits + conf.tag_bits + 1`;

val max_heap_limit_def = Define `
  max_heap_limit (:'a) c =
    MIN (dimword (:'a) DIV 2 ** shift_length c)
        (dimword (:'a) DIV 2 ** (shift (:'a) + 1))`

val all_ones_def = Define `
  all_ones m n = (m - 1 -- n) (~0w)`

val maxout_bits_def = Define `
  maxout_bits n rep_len k =
    if n < 2 ** rep_len then n2w n << k else all_ones (k + rep_len) k`

val ptr_bits_def = Define `
  ptr_bits conf tag len =
    (maxout_bits tag conf.tag_bits (1 + conf.len_bits) ||
     maxout_bits len conf.len_bits 1)`

val real_addr_def = Define `
  (real_addr (conf:bvp_to_word$config) r): 'a wordLang$exp =
    let k = shift (:'a) in
   (* if k <= conf.pad_bits + 1 then
        Op Add [Lookup CurrHeap;
                Shift Lsr (Var r) (Nat (shift_length conf - k))]
      else *)
        Op Add [Lookup CurrHeap;
                Shift Lsl (Shift Lsr (Var r)
                  (Nat (shift_length conf))) (Nat k)]`

val real_offset_def = Define `
  (real_offset (conf:bvp_to_word$config) r): 'a wordLang$exp =
     Op Add [Const bytes_in_word;
             if dimindex (:'a) = 32 then Var r else Shift Lsl (Var r) (Nat 1)]`

val real_byte_offset_def = Define`
  real_byte_offset r : 'a wordLang$exp =
    Op Add [Const bytes_in_word;
            Shift Lsr (Var r) (Nat 2)]`;

val _ = temp_overload_on("FALSE_CONST",``Const (n2w 18)``)
val _ = temp_overload_on("TRUE_CONST",``Const (n2w 2)``)

val _ = Datatype`
  word_op_type = Bitwise binop | Carried binop`;

val lookup_word_op_def = Define`
  (lookup_word_op Andw = Bitwise And) ∧
  (lookup_word_op Orw = Bitwise Or) ∧
  (lookup_word_op Xor = Bitwise Xor) ∧
  (lookup_word_op Add = Carried Add) ∧
  (lookup_word_op Sub = Carried Sub)`;
val _ = export_rewrites["lookup_word_op_def"];

val assign_def = Define `
  assign (c:bvp_to_word$config) (secn:num) (l:num) (dest:num) (op:closLang$op)
    (args:num list) (names:num_set option) =
    case op of
    | Const i =>
        (* bvl_to_bvi compilation ensures that all literal
           constants fit into a machine word *)
        if i < 0
        then (Assign (adjust_var dest) (Const (0w - n2w (Num (4 * (0 - i))))),l)
        else (Assign (adjust_var dest) (Const (n2w (Num (4 * i)))),l)
    | GlobalsPtr => (Assign (adjust_var dest) (Lookup Globals),l)
    | SetGlobalsPtr => (Seq (Set Globals (Var (adjust_var (HD args))))
                            (Assign (adjust_var dest) Unit),l)
    | ToList => (Skip,l)
    | Global _ => (Skip,l)
    | SetGlobal _ => (Skip,l)
    | AllocGlobal => (Skip,l)
    (* TODO: FromList *)
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
      | _ => (GiveUp,l))
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
                                           (shift_length c − 1 -- 0)
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
    (* TODO: RefByte *)
    (* TODO: RefArray *)
    | Label n => (LocValue (adjust_var dest) (2 * n + bvl_to_bvi$num_stubs) 0,l)
    | Equal => (case args of
               | [v1;v2] =>
                 let retf = Assign (adjust_var dest) FALSE_CONST in
                 let rett = Assign (adjust_var dest) TRUE_CONST in
                 (If Equal (adjust_var v1) (Reg (adjust_var v2)) rett
                    (If Test (adjust_var v1) (Imm 1w) retf
                       (Seq (Assign 1 (Load (real_addr c (adjust_var v1))))
                          (If Test 1 (Imm 4w) retf
                             (If Test 1 (Imm 16w)
                               (let a1 = real_addr c (adjust_var v1) in
                                let a2 = real_addr c (adjust_var v2) in
                                list_Seq [
                                  Assign 1 (Load (Op Add [a1; Const bytes_in_word]));
                                  Assign 3 (Load (Op Add [a2; Const bytes_in_word]));
                                  If Equal 1 (Reg 3)
                                    (if dimindex (:'a) < 64 then
                                       list_Seq [
                                         Assign 1 (Load (Op Add [a1; Const (bytes_in_word <<1)]));
                                         Assign 3 (Load (Op Add [a2; Const (bytes_in_word <<1)]));
                                         If Equal 1 (Reg 3) rett retf]
                                     else rett)
                                    retf])
                               retf))))
                 ,l)
                | _ => (Skip,l))
    | Less => (case args of
               | [v1;v2] => (If Less (adjust_var v1) (Reg (adjust_var v2))
                              (Assign (adjust_var dest) TRUE_CONST)
                              (Assign (adjust_var dest) FALSE_CONST),l)
               | _ => (Skip,l))
    | LessEq => (case args of
               | [v1;v2] => (If Less (adjust_var v2) (Reg (adjust_var v1))
                              (Assign (adjust_var dest) FALSE_CONST)
                              (Assign (adjust_var dest) TRUE_CONST),l)
               | _ => (Skip,l))
    | Greater => (case args of
               | [v1;v2] => (If Less (adjust_var v2) (Reg (adjust_var v1))
                              (Assign (adjust_var dest) TRUE_CONST)
                              (Assign (adjust_var dest) FALSE_CONST),l)
               | _ => (Skip,l))
    | GreaterEq => (case args of
               | [v1;v2] => (If Less (adjust_var v1) (Reg (adjust_var v2))
                              (Assign (adjust_var dest) FALSE_CONST)
                              (Assign (adjust_var dest) TRUE_CONST),l)
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
              | [v1;v2] =>
                  (Seq (Assign 1 (Op Or [Var (adjust_var v1);
                                         Var (adjust_var v2)]))
                       (If Test 1 (Imm (~0w << (dimindex (:'a) - 2)))
                          (Assign (adjust_var dest)
                             (Op Add [Var (adjust_var v1);
                                      Var (adjust_var v2)]))
                          GiveUp),l)
              | _ => (Skip,l))
    | Sub => (case args of
              | [v1;v2] =>
                  (Seq (Assign 1 (Op Or [Var (adjust_var v1);
                                         Var (adjust_var v2)]))
                       (If Test 1 (Imm (~0w << (dimindex (:'a) - 2)))
                          (Assign (adjust_var dest)
                             (Op Sub [Var (adjust_var v1);
                                      Var (adjust_var v2)]))
                          GiveUp),l)
              | _ => (Skip,l))
    (* TODO: Mult *)
    (* TODO: Div *)
    (* TODO: Mod *)
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
                 | Carried Add => GiveUp (* TODO: implement *)
                 | Carried Sub => GiveUp (* TODO: implement *));
                Store (Op Add [Var 1; Const bytes_in_word]) 3;
                Assign 3 (Const header);
                Store (Var 1) 3;
                Set EndOfHeap (Var 1);
                Assign (adjust_var dest)
                  (Op Or [Shift Lsl (Op Sub [Var 1; Lookup CurrHeap])
                            (Nat (shift_length c − shift (:'a)));
                          Const 1w])], l))
       | _ => (Skip,l))
    (* TODO: semantics of WordShift needs to limit n to the word size
    | WordShift W8 sh n => (case args of
      | [v1] =>
        (Assign (adjust_var dest)
           (case sh of
            | Lsl =>
              Shift Lsr
                (Shift Lsl (Var (adjust_var v1)) (Nat (dimindex(:'a) - 10 + n)))
                (Nat (dimindex(:'a) - 10))
            | Lsr =>
              Shift Lsl
                (Shift Lsr (Var (adjust_var v1)) (Nat (n+2)))
                (Nat 2)
            | Asr =>
              Shift Lsl
                (Shift Lsr
                   (Shift Asr
                      (Shift Lsl (Var (adjust_var v1)) (Nat (dimindex(:'a) - 10)))
                      (Nat n))
                   (Nat (dimindex(:'a) - 8)))
                (Nat 2))
        ,l)
      | _ => (GiveUp,l)) *)
    (* TODO: WordShift W64 *)
    (* TODO:
    | WordFromInt => (case args of
      | [v1] =>
        let len = if dimindex(:'a) < 64 then 2 else 1 in
        (case encode_header c 3 len of
         | NONE => (GiveUp,l)
         | SOME (header:'a word) => ...)
      | _ => (Skip, l)) *)
    (* TODO: WordToInt *)
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
       | _ => (GiveUp,l))
    | _ => (GiveUp:'a wordLang$prog,l)`;

val comp_def = Define `
  comp c (secn:num) (l:num) (p:bvp$prog) =
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
  stubs (:α) = [
    (20n,1n,Skip:α wordLang$prog); (* TODO: FromList *)
    (22n,1n,Skip:α wordLang$prog); (* TODO: RefByte *)
    (24n,1n,Skip:α wordLang$prog)  (* TODO: RefArray *)
  ]`;

val compile_def = Define `
  compile bvp_conf word_conf asm_conf prog =
    let p = stubs (:α) ++ MAP (compile_part bvp_conf) prog in
      word_to_word$compile word_conf (asm_conf:'a asm_config) p`;

val _ = export_theory();
