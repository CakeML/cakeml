open preamble wordLangTheory bvpTheory word_to_wordTheory;

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

val encode_header_def = Define `
  encode_header (conf:bvp_to_word$config) tag len =
    if tag < 2 ** (dimindex (:'a) - conf.len_size - 3) /\
       len < 2 ** conf.len_size then
      SOME (n2w tag << (conf.len_size + 3) + (n2w len << 2):'a word)
    else NONE`

val list_Seq_def = Define `
  (list_Seq [] = wordLang$Skip) /\
  (list_Seq [x] = x) /\
  (list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))`

val shift_def = Define `
  shift (:'a) = if dimindex (:'a) = 32 then 2 else 3n`;

val next_free_addr_def = Define `
  next_free_addr n =
    Op Add [Shift Lsl (Var n) (Nat (shift (:'a)));
            Lookup CurrHeap] :'a exp`

val StoreEach_def = Define `
  (StoreEach v [] offset = Skip) /\
  (StoreEach v (x::xs) (offset:'a word) =
     Seq (Store (Op Add [Var v; Const offset]) x)
         (StoreEach v xs (offset + bytes_in_word)))`

val shift_length_def = Define `
  shift_length conf = 1 + conf.pad_bits + conf.len_bits + conf.tag_bits + 1`;

val real_addr_def = Define `
  (real_addr (conf:bvp_to_word$config) r): 'a wordLang$exp =
    let k = shift (:'a) in
      if k <= conf.pad_bits + 1 then
        Op Add [Lookup CurrHeap;
                Shift Lsr (Var r) (Nat (shift_length conf - k))]
      else
        Op Add [Lookup CurrHeap;
                Shift Lsl (Shift Lsr (Var r) (Nat (shift_length conf))) (Nat k)]`

val real_offset_def = Define `
  (real_offset (conf:bvp_to_word$config) r): 'a wordLang$exp =
     if dimindex (:'a) = 32 then Var r else Shift Lsl (Var r) (Nat 1)`

val assign_def = Define `
  assign (c:bvp_to_word$config) (n:num) (l:num) (dest:num) (op:closLang$op)
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
    | El => (case args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c v1; real_offset c v2])),l)
             | _ => (Skip,l))
    | Deref => (case args of
             | [v1;v2] => (Assign (adjust_var dest)
                            (Load (Op Add [real_addr c v1; real_offset c v2])),l)
             | _ => (Skip,l))
    | Update => (case args of
             | [v1;v2;v3] =>
                 (Seq (Store (Op Add [real_addr c v1; real_offset c v2]) v3)
                      (Assign (adjust_var dest) Unit),l)
             | _ => (Skip,l))
    | Cons tag => if LENGTH args = 0 then
                    if 16 * tag < dimword (:'a) then
                      (Assign (adjust_var dest) (Const (n2w (16 * tag + 2))),l)
                    else (GiveUp,l) (* tag is too big to be represented *)
                  else
                    (case encode_header c (4 * tag) (LENGTH args) of
                     | NONE => (GiveUp,l)
                     | SOME (header:'a word) => (list_Seq
                        [Assign 5 (Lookup NextFree);
                         Assign 1 (next_free_addr 5);
                         Assign 3 (Const header);
                         StoreEach 1 (3::args) 0w;
                         Set NextFree (Op Add [Var 1;
                           Const (n2w (LENGTH args))])],l))
    | _ => (GiveUp,l)
    | _ => (GiveUp:'a wordLang$prog,l)`;

val comp_def = Define `
  comp c (n:num) (l:num) (p:bvp$prog) =
    case p of
    | Skip => (Skip:'a wordLang$prog,l)
    | Tick => (Tick,l)
    | Raise n => (Raise (adjust_var n),l)
    | Return n => (Return 0 (adjust_var n),l)
    | Move n1 n2 => (Move 0 [(adjust_var n1 ,adjust_var n2)],l)
    | Seq p1 p2 =>
        let (q1,l1) = comp c n l p1 in
        let (q2,l2) = comp c n l1 p2 in
          (Seq q1 q2,l2)
    | If n p1 p2 =>
        let (q1,l1) = comp c n l p1 in
        let (q2,l2) = comp c n l1 p2 in
          (If Equal (adjust_var n) (Imm 2w) q1 q2,l2)
    | MakeSpace n names =>
        let k = dimindex (:'a) DIV 8 in
        let w = n2w (n * k) in
        let w = if w2n w = n * k then w else ~0w in
          (Seq (Assign 1 (Op Sub [Lookup EndOfHeap; Lookup NextFree]))
               (If Lower 1 (Imm w)
                 (Seq (Assign 1 (Const w)) (Alloc 1 (adjust_set names)))
                Skip),l)
    | Assign dest op args names => assign c n l dest op args names
    | Call ret target args handler =>
        case ret of
        | NONE => (Call NONE target (0::MAP adjust_var args) NONE,l)
        | SOME (n,names) =>
            let ret = SOME (adjust_var n, adjust_set names, Skip, n, l) in
              case handler of
              | NONE => (Call ret target (MAP adjust_var args) NONE, l+1)
              | SOME (n,p) =>
                  let (q1,l1) = comp c n (l+2) p in
                  let handler = SOME (adjust_var n, q1, n, l+1) in
                    (Call ret target (MAP adjust_var args) handler, l1)`

val compile_part_def = Define `
  compile_part c (n,arg_count,p) = (n,arg_count+1n,FST (comp c n 1 p))`

val compile_def = Define `
  compile bvp_conf word_conf asm_conf prog =
    let p = MAP (compile_part bvp_conf) prog in
      word_to_word$compile word_conf (asm_conf:'a asm_config) p`;

val _ = export_theory();
