open preamble wordLangTheory bvpTheory;

val _ = new_theory "bvp_to_word";

val _ = Datatype `
  config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *) |>`

val adjust_var_def = Define `
  adjust_var n = 2 * n + 2:num`;

val adjust_set_def = Define `
  adjust_set (names:num_set) =
    (fromAList ((0,()):: MAP (\(n,k). (adjust_var n,k)) (toAList names))):num_set`

val assign_def = Define `
  assign (c:config) (n:num) (l:num) (dest:num) (op:closLang$op)
    (args:num list) (names:num_set option) =
    case op of
    | Const i =>
        (* bvl_to_bvi compilation ensures that all literal
           constants fit into a machine word *)
        if i < 0
        then (Assign (adjust_var dest) (Const (0w - n2w (Num (4 * (0 - i))))),l)
        else (Assign (adjust_var dest) (Const (n2w (Num (4 * i)))),l)
    | _ => (Skip:'a wordLang$prog,l)`;

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
  compile c prog = MAP (compile_part c) prog`;

val _ = export_theory();
