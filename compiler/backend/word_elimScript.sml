open preamble sptreeTheory wordLangTheory flat_elimTheory

val _ = new_theory "word_elim";


val findWordLoc_def = Define `
    (findWordLoc (name:num, _, _) = name)
`

val findWordRef_def = Define `
    (findWordRef (MustTerminate p) = findWordRef p) ∧
    (findWordRef (Call ret target _ handler) = union
        (case target of | NONE => LN | SOME n => (insert n () LN))
            (union
                (case ret of
                    | NONE => LN
                    | SOME (_,_,ret_handler,l1,_) =>
                        insert l1 () (findWordRef (ret_handler)))
                (case handler of
                    | NONE => LN
                    | SOME (_,ex_handler,_,_) => findWordRef (ex_handler)))
    ) ∧
    (findWordRef (Seq p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (If _ _ _ p1 p2) = union (findWordRef p1) (findWordRef p2)) ∧
    (findWordRef (LocValue _ n) = insert n () LN) ∧
    (findWordRef _ = LN)
`

val findWordRef_ind = theorem "findWordRef_ind";

val analyseWordCode_def = Define`
    (analyseWordCode [] = LN:num_set num_map) ∧
    (analyseWordCode ((n, args, prog)::t) =
        insert n (findWordRef prog) (analyseWordCode t))
`

val removeWordCode_def = Define `
    removeWordCode reachable l =
        FILTER (\ x . IS_SOME (lookup (FST x) reachable)) l
`

val removeWordProg_def = Define `
    removeWordProg (n:num) code =
        let t = analyseWordCode code in
        let reachable = closure_spt (insert n () (LN:num_set)) t in
        removeWordCode reachable code
`


val _ = export_theory();
