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

val numset_list_insert_nottailrec_def = Define`
  (numset_list_insert_nottailrec [] t = t) ∧
  (numset_list_insert_nottailrec (x::xs) t = insert x () (numset_list_insert_nottailrec xs t))`

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

val fix_endlive_def = Define`
    (
      fix_endlive (StartLive l) live =
        (StartLive l, numset_list_delete l live)
    ) /\ (
      fix_endlive (EndLive l) live =
        (EndLive (FILTER (\x. lookup x live = NONE) l), numset_list_insert l live)
    ) /\ (
      fix_endlive (Branch lt1 lt2) live =
        let (lt1', live1) = fix_endlive lt1 live in
        let (lt2', live2) = fix_endlive lt2 live in
        (Branch lt1' lt2', numset_list_insert (MAP FST (toAList (difference live2 live1))) live1)
    ) /\ (
      fix_endlive (Seq lt1 lt2) live =
        let (lt2', live2) = fix_endlive lt2 live in
        let (lt1', live1) = fix_endlive lt1 live2 in
        (Seq lt1' lt2', live1)
    )
`

val check_endlive_fixed_def = Define`
    (
      check_endlive_fixed (StartLive l) live =
        (T, numset_list_delete l live)
    ) /\ (
      check_endlive_fixed (EndLive l) live =
        (EVERY (\x. lookup x live = NONE) l, numset_list_insert l live)
    ) /\ (
      check_endlive_fixed (Branch lt1 lt2) live =
        let (r1, live1) = check_endlive_fixed lt1 live in
        let (r2, live2) = check_endlive_fixed lt2 live in
        (r1 /\ r2, numset_list_insert (MAP FST (toAList (difference live2 live1))) live1)
    ) /\ (
      check_endlive_fixed (Seq lt1 lt2) live =
        let (r2, live2) = check_endlive_fixed lt2 live in
        let (r1, live1) = check_endlive_fixed lt1 live2 in
        (r1 /\ r2, live1)
    )`

val check_endlive_fixed_forward_def = Define`
    (
      check_endlive_fixed_forward (StartLive l) live =
        (T, numset_list_insert l live)
    ) /\ (
      check_endlive_fixed_forward (EndLive l) live =
        (EVERY (\x. lookup x live = SOME ()) l, numset_list_delete l live)
    ) /\ (
      check_endlive_fixed_forward (Branch lt1 lt2) live =
        let (r1, live1) = check_endlive_fixed_forward lt1 live in
        let (r2, live2) = check_endlive_fixed_forward lt2 live in
        (r1 /\ r2, numset_list_insert (MAP FST (toAList (difference live2 live1))) live1)
    ) /\ (
      check_endlive_fixed_forward (Seq lt1 lt2) live =
        let (r1, live1) = check_endlive_fixed_forward lt1 live in
        let (r2, live2) = check_endlive_fixed_forward lt2 live1 in
        (r1 /\ r2, live2)
    )`


val check_live_tree_forward_def = Define`
    (
      check_live_tree_forward f (StartLive l) live flive =
        check_partial_col f l live flive
    ) /\ (
      check_live_tree_forward f (EndLive l) live flive =
        let live_out = numset_list_delete l live in
        let flive_out = numset_list_delete (MAP f l) flive in
        SOME (live_out, flive_out)
    ) /\ (
      check_live_tree_forward f (Branch lt1 lt2) live flive =
        case check_live_tree_forward f lt1 live flive of
        | NONE => NONE
        | SOME (live1, flive1) =>
        case check_live_tree_forward f lt2 live flive of
        | NONE => NONE
        | SOME (live2, flive2) =>
        check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1
    ) /\ (
      check_live_tree_forward f (Seq lt1 lt2) live flive =
        case check_live_tree_forward f lt1 live flive of
        | NONE => NONE
        | SOME (live1, flive1) =>
          check_live_tree_forward f lt2 live1 flive1
    )`

val get_live_backward_def = Define`
    (
      get_live_backward (StartLive l) live =
        numset_list_delete l live
    ) /\ (
      get_live_backward (EndLive l) live =
        numset_list_insert l live
    ) /\ (
      get_live_backward (Branch lt1 lt2) live =
        let live1 = get_live_backward lt1 live in
        let live2 = get_live_backward lt2 live in
        numset_list_insert (MAP FST (toAList (difference live2 live1))) live1
    ) /\ (
      get_live_backward (Seq lt1 lt2) live =
        get_live_backward lt1 (get_live_backward lt2 live)
    )`

val fix_domination_def = Define`
    fix_domination lt =
        let live = get_live_backward lt LN in
        if live = LN then lt
        else Seq (StartLive (MAP FST (toAList live))) lt
`

val fix_live_tree_def = Define`
    fix_live_tree lt = fix_domination (FST (fix_endlive lt LN))
`


val _ = export_theory ();
