open preamble sptreeTheory reg_allocTheory

val _ = new_theory "linear_scan"

val _ = Datatype`
  live_tree = StartLive (num list)
            | EndLive (num list)
            | Branch live_tree live_tree
            | Seq live_tree live_tree`


val numset_list_insert_def = Define`
  (numset_list_insert [] t = t) ∧
  (numset_list_insert (x::xs) t = numset_list_insert xs (insert x () t))`

val is_subset_def = Define`
    is_subset s1 s2 <=> (domain s1) SUBSET (domain s2)
`

val is_subset_compute_def = Define`
    is_subset_compute s1 s2 <=> EVERY (\(x,y). lookup x s2 <> NONE) (toAList s1)
`

val get_live_tree_def = Define`
    (
      get_live_tree (reg_alloc$Delta wr rd) =
        Seq (EndLive rd) (StartLive wr)
    ) /\ (
      get_live_tree (reg_alloc$Set cutset) =
        let cutlist = MAP FST (toAList cutset) in
        EndLive cutlist
    ) /\ (
      get_live_tree (reg_alloc$Branch optcutset ct1 ct2) =
        let lt1 = get_live_tree ct1 in
        let lt2 = get_live_tree ct2 in
        case optcutset of
        | SOME cutset =>
            let cutlist = MAP FST (toAList cutset) in
            Seq (EndLive cutlist) (Branch lt1 lt2)
        | NONE => (Branch lt1 lt2)
    ) /\ (
      get_live_tree (reg_alloc$Seq ct1 ct2) =
        let lt2 = get_live_tree ct2 in
        let lt1 = get_live_tree ct1 in
        Seq lt1 lt2
    )`

val check_live_tree_def = Define`
    (
      check_live_tree f (StartLive l) live flive =
        case check_partial_col f l live flive of
        | NONE => NONE
        | SOME _ =>
        let live_out = numset_list_delete l live in
        let flive_out = numset_list_delete (MAP f l) flive in
        SOME (live_out, flive_out)
    ) /\ (
      check_live_tree f (EndLive l) live flive =
        check_partial_col f l live flive
    ) /\ (
      check_live_tree f (Branch lt1 lt2) live flive =
        case check_live_tree f lt1 live flive of
        | NONE => NONE
        | SOME (live1, flive1) =>
        case check_live_tree f lt2 live flive of
        | NONE => NONE
        | SOME (live2, flive2) =>
        check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1
    ) /\ (
      check_live_tree f (Seq lt1 lt2) live flive =
        case check_live_tree f lt2 live flive of
        | NONE => NONE
        | SOME (live2, flive2) =>
          check_live_tree f lt1 live2 flive2
    )`


val _ = export_theory ();
