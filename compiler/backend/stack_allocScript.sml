open preamble stackLangTheory bvp_to_wordTheory;

val _ = new_theory "stack_alloc";

val stubs_def = Define `
  stubs (c:bvp_to_word$config) =
    [(10n,Skip:'a stackLang$prog)]`

val max_lab_def = Define `
  max_lab (p:'a stackLang$prog) =
    case p of
    | Seq p1 p2 => MAX (max_lab p1) (max_lab p2)
    | If _ _ _ p1 p2 => MAX (max_lab p1) (max_lab p2)
    | Call NONE _ NONE => 0
    | Call NONE _ (SOME (_,_,l2)) => l2
    | Call (SOME (_,_,_,l2)) _ NONE => l2
    | Call (SOME (_,_,_,l2)) _ (SOME (_,_,l3)) => MAX l2 l3
    | _ => 0`

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
    | Call NONE dest exc => (Call NONE dest NONE,m)
    | Call (SOME (p1,lr,l1,l2)) dest exc =>
        let (q1,m) = comp n m p1 in
         (case exc of
          | NONE => (Call (SOME (q1,lr,l1,l2)) dest NONE,m)
          | SOME (p2,k1,k2) =>
              let (q2,m) = comp n m p2 in
                (Call (SOME (q1,lr,l1,l2)) dest (SOME (q2,k1,k2)),m))
    | Alloc n => (Call (SOME (Skip,0,n,m)) (INL 10) NONE,m+1)
    | _ => (p,m) `

val prog_comp_def = Define `
  prog_comp (n,p) = (n,FST (comp n (max_lab p) p))`

val compile_def = Define `
  compile c prog = stubs c ++ MAP prog_comp prog`;

val _ = export_theory();
