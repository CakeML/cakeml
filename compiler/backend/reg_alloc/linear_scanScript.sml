(*
  A linear-scan register allocator.
*)
open preamble sptreeTheory reg_allocTheory libTheory
open state_transformerTheory ml_monadBaseLib ml_monadBaseTheory

val _ = new_theory "linear_scan"

val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = Datatype`
  live_tree = Writes (num list)
            | Reads (num list)
            | Branch live_tree live_tree
            | Seq live_tree live_tree`


val numset_list_insert_def = Define`
  (numset_list_insert [] t = t) ∧
  (numset_list_insert (x::xs) t = numset_list_insert xs (insert x () t))`

val numset_list_insert_nottailrec_def = Define`
  (numset_list_insert_nottailrec [] t = t) ∧
  (numset_list_insert_nottailrec (x::xs) t = insert x () (numset_list_insert_nottailrec xs t))`

val get_live_tree_def = Define`
    (
      get_live_tree (reg_alloc$Delta wr rd) =
        Seq (Reads rd) (Writes wr)
    ) /\ (
      get_live_tree (reg_alloc$Set cutset) =
        let cutlist = MAP FST (toAList cutset) in
        Reads cutlist
    ) /\ (
      get_live_tree (reg_alloc$Branch optcutset ct1 ct2) =
        let lt1 = get_live_tree ct1 in
        let lt2 = get_live_tree ct2 in
        case optcutset of
        | SOME cutset =>
            let cutlist = MAP FST (toAList cutset) in
            Seq (Reads cutlist) (Branch lt1 lt2)
        | NONE => (Branch lt1 lt2)
    ) /\ (
      get_live_tree (reg_alloc$Seq ct1 ct2) =
        let lt2 = get_live_tree ct2 in
        let lt1 = get_live_tree ct1 in
        Seq lt1 lt2
    )`

val check_live_tree_def = Define`
    (
      check_live_tree f (Writes l) live flive =
        case check_partial_col f l live flive of
        | NONE => NONE
        | SOME _ =>
        let livein = numset_list_delete l live in
        let flivein = numset_list_delete (MAP f l) flive in
        SOME (livein, flivein)
    ) /\ (
      check_live_tree f (Reads l) live flive =
        check_partial_col f l live flive
    ) /\ (
      check_live_tree f (Branch lt1 lt2) live flive =
        case check_live_tree f lt1 live flive of
        | NONE => NONE
        | SOME (livein1, flivein1) =>
        case check_live_tree f lt2 live flive of
        | NONE => NONE
        | SOME (livein2, flivein2) =>
        check_partial_col f (MAP FST (toAList (difference livein2 livein1))) livein1 flivein1
    ) /\ (
      check_live_tree f (Seq lt1 lt2) live flive =
        case check_live_tree f lt2 live flive of
        | NONE => NONE
        | SOME (livein2, flivein2) =>
          check_live_tree f lt1 livein2 flivein2
    )`

val get_live_backward_def = Define`
    (
      get_live_backward (Writes l) live =
        numset_list_delete l live
    ) /\ (
      get_live_backward (Reads l) live =
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
        else Seq (Writes (MAP FST (toAList live))) lt
`

val numset_list_add_if_def = Define`
    (
      numset_list_add_if [] (v:int) s P = s
    ) /\ (
      numset_list_add_if (x::xs) v s P =
        case lookup x s of
        | (SOME v') =>
            if P v v' then numset_list_add_if xs v (insert x v s) P
            else numset_list_add_if xs v s P
        | NONE =>
            numset_list_add_if xs v (insert x v s) P
    )
`

val numset_list_add_if_lt_def = Define`
    numset_list_add_if_lt l (v:int) s = numset_list_add_if l v s $<=
`

val numset_list_add_if_gt_def = Define`
    numset_list_add_if_gt l (v:int) s = numset_list_add_if l v s (\a b. b <= a)
`

val size_of_live_tree_def = Define`
    (
      size_of_live_tree (Writes l) =
        1 : int
    ) /\ (
      size_of_live_tree (Reads l) =
        1 : int
    ) /\ (
      size_of_live_tree (Branch lt1 lt2) =
        size_of_live_tree lt1 + size_of_live_tree lt2
    ) /\ (
      size_of_live_tree (Seq lt1 lt2) =
        size_of_live_tree lt1 + size_of_live_tree lt2
    )
`

val get_intervals_def = Define`
    (
      get_intervals (Writes l) (n : int) int_beg int_end =
        (n-1, numset_list_add_if_lt l n int_beg, numset_list_add_if_gt l n int_end)
    ) /\ (
      get_intervals (Reads l) (n : int) int_beg int_end =
        (n-1, int_beg, numset_list_add_if_gt l n int_end)
    ) /\ (
      get_intervals (Branch lt1 lt2) (n : int) int_beg int_end =
        let (n2, int_beg2, int_end2) = get_intervals lt2 n int_beg int_end in
        get_intervals lt1 n2 int_beg2 int_end2
    ) /\ (
      get_intervals (Seq lt1 lt2) (n : int) int_beg int_end =
        let (n2, int_beg2, int_end2) = get_intervals lt2 n int_beg int_end in
        get_intervals lt1 n2 int_beg2 int_end2
    )
`

(* compute the same thing as `get_intervals` (as says the `get_intervals_withlive_beg_eq_get_intervals_beg` theorem),
 * but has the following invariant: !r. r IN domain live ==> r NOTIN domain beg_in (as stated by the `get_intervals_withlive_live_intbeg` theorem *)
val get_intervals_withlive_def = Define`
    (
      get_intervals_withlive (Writes l) (n : int) int_beg int_end live =
        (n-1, numset_list_add_if_lt l n int_beg, numset_list_add_if_gt l n int_end)
    ) /\ (
      get_intervals_withlive (Reads l) (n : int) int_beg int_end live =
        (n-1, numset_list_delete l int_beg, numset_list_add_if_gt l n int_end)
    ) /\ (
      get_intervals_withlive (Branch lt1 lt2) (n : int) int_beg int_end live =
        let (n2, int_beg2, int_end2) = get_intervals_withlive lt2 n int_beg int_end live in
        let (n1, int_beg1, int_end1) = get_intervals_withlive lt1 n2 (difference int_beg2 live) int_end2 live in
        (n1, difference int_beg1 (union (get_live_backward lt1 live) (get_live_backward lt2 live)), int_end1)
    ) /\ (
      get_intervals_withlive (Seq lt1 lt2) (n : int) int_beg int_end live =
        let (n2, int_beg2, int_end2) = get_intervals_withlive lt2 n int_beg int_end live in
        let (n1, int_beg1, int_end1) = get_intervals_withlive lt1 n2 int_beg2 int_end2 (get_live_backward lt2 live) in
        (n1, int_beg1, int_end1)
    )
`

val check_number_property_def = Define`
  (
    check_number_property (P : int -> num_set -> bool) (Writes l) n live =
        let n_out = n-1 in
        let live_out = numset_list_delete l live in
        P n_out live_out
  ) /\ (
    check_number_property P (Reads l) n live =
        let n_out = n-1 in
        let live_out = numset_list_insert l live in
        P n_out live_out
  ) /\ (
    check_number_property P (Branch lt1 lt2) n live =
        let r2 = check_number_property P lt2 n live in
        let r1 = check_number_property P lt1 (n-(size_of_live_tree lt2)) live in
        r1 /\ r2
  ) /\ (
    check_number_property P (Seq lt1 lt2) n live =
        let r2 = check_number_property P lt2 n live in
        let r1 = check_number_property P lt1 (n-size_of_live_tree lt2) (get_live_backward lt2 live) in
        r1 /\ r2
  )
`

val check_number_property_strong_def = Define`
  (
    check_number_property_strong (P : int -> num_set -> bool) (Writes l) n live =
        let n_out = n-1 in
        let live_out = numset_list_delete l live in
        P n_out live_out
  ) /\ (
    check_number_property_strong P (Reads l) n live =
        let n_out = n-1 in
        let live_out = numset_list_insert l live in
        P n_out live_out
  ) /\ (
    check_number_property_strong P (Branch lt1 lt2) n live =
        let r2 = check_number_property_strong P lt2 n live in
        let r1 = check_number_property_strong P lt1 (n-(size_of_live_tree lt2)) live in
        r1 /\ r2 /\ P (n - (size_of_live_tree (Branch lt1 lt2))) (get_live_backward (Branch lt1 lt2) live)
  ) /\ (
    check_number_property_strong P (Seq lt1 lt2) n live =
        let r2 = check_number_property_strong P lt2 n live in
        let r1 = check_number_property_strong P lt1 (n-size_of_live_tree lt2) (get_live_backward lt2 live) in
        r1 /\ r2
  )
`

val check_startlive_prop_def = Define`
  (
    check_startlive_prop (Writes l) n beg end ndef =
        !r. MEM r l ==> (option_CASE (lookup r beg) ndef (\x.x) <= n /\
                        (?v. lookup r end = SOME v /\ n <= v))
  ) /\ (
    check_startlive_prop (Reads l) n beg end ndef =
        T
  ) /\ (
    check_startlive_prop (Branch lt1 lt2) n beg end ndef =
        let r2 = check_startlive_prop lt2 n beg end ndef in
        let r1 = check_startlive_prop lt1 (n-(size_of_live_tree lt2)) beg end ndef in
        r1 /\ r2
  ) /\ (
    check_startlive_prop (Seq lt1 lt2) n beg end ndef =
        let r2 = check_startlive_prop lt2 n beg end ndef in
        let r1 = check_startlive_prop lt1 (n-size_of_live_tree lt2) beg end ndef in
        r1 /\ r2
  )`

val live_tree_registers_def = Define`
    (live_tree_registers (Writes l) = set l) /\
    (live_tree_registers (Reads l) = set l) /\
    (live_tree_registers (Branch lt1 lt2) = live_tree_registers lt1 UNION live_tree_registers lt2) /\
    (live_tree_registers (Seq lt1 lt2) = live_tree_registers lt1 UNION live_tree_registers lt2)
`

val interval_intersect_def = Define`
    interval_intersect (l1:int, r1:int) (l2, r2) = (l1 <= r2 /\ l2 <= r1)
`

val point_inside_interval_def = Define`
    point_inside_interval (l:int, r:int) n = (l <= n /\ n <= r)
`

val check_intervals_def = Define`
    check_intervals f int_beg int_end = !r1 r2.
      r1 IN domain int_beg /\ r2 IN domain int_beg /\
      interval_intersect (THE (lookup r1 int_beg), THE (lookup r1 int_end)) (THE (lookup r2 int_beg), THE (lookup r2 int_end)) /\
      f r1 = f r2
      ==>
      r1 = r2
`

val get_intervals_ct_aux_def = Define`
    (
      get_intervals_ct_aux (reg_alloc$Delta wr rd) (n : int) int_beg int_end live =
        (n-2, numset_list_add_if_lt wr n int_beg, numset_list_add_if_gt rd (n-1) (numset_list_add_if_gt wr n int_end), numset_list_insert rd (numset_list_delete wr live))
    ) /\ (
      get_intervals_ct_aux (reg_alloc$Set cutset) (n : int) int_beg int_end live =
        (n-1, int_beg, numset_list_add_if_gt (MAP FST (toAList cutset)) n int_end, union cutset live)
    ) /\ (
      get_intervals_ct_aux (reg_alloc$Branch optcutset ct1 ct2) (n : int) int_beg int_end live =
        let (n2, int_beg2, int_end2, live2) = get_intervals_ct_aux ct2 n int_beg int_end live in
        let (n1, int_beg1, int_end1, live1) = get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live in
        case optcutset of
        | NONE => (n1, int_beg1, int_end1, union live1 live2)
        | SOME cutset => (n1-1, int_beg1, numset_list_add_if_gt (MAP FST (toAList cutset)) n1 int_end1, union cutset (union live1 live2))
    ) /\ (
      get_intervals_ct_aux (reg_alloc$Seq ct1 ct2) (n : int) int_beg int_end live =
        let (n2, int_beg2, int_end2, live2) = get_intervals_ct_aux ct2 n int_beg int_end live in
        get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2
    )
`

val get_intervals_ct_def = Define`
    get_intervals_ct ct =
        let (n, int_beg, int_end, live) = get_intervals_ct_aux ct 0 LN LN LN in
        let listlive = MAP FST (toAList live) in
        (n-1, numset_list_add_if_lt listlive n int_beg, numset_list_add_if_gt listlive n int_end)
`

val _ = Datatype `
  linear_scan_state =
    <| active: (int # num) list (* interval end # reg *)
     ; colorpool: num list
     ; phyregs: num_set
     ; colornum: num
     ; colormax: num
     ; stacknum: num
     |>`

val _ = Datatype `
  linear_scan_hidden_state =
    <| colors : num list
     ; int_beg : int list
     ; int_end : int list
     ; sorted_regs : num list
     ; sorted_moves : (num # (num # num)) list
     |>`

val accessors = define_monad_access_funs ``:linear_scan_hidden_state``;

val colors_accessors = el 1 accessors;
val int_beg_accessors = el 2 accessors;
val int_end_accessors = el 3 accessors;
val sorted_regs_accessors = el 4 accessors;
val sorted_moves_accessors = el 5 accessors;

val (colors,get_colors_def,set_colors_def) = colors_accessors;
val (int_beg,get_int_beg_def,set_int_beg_def) = int_beg_accessors;
val (int_end,get_int_end_def,set_int_end_def) = int_end_accessors;
val (sorted_regs,get_sorted_regs_def,set_sorted_regs_def) = sorted_regs_accessors;
val (sorted_moves,get_sorted_moves_def,set_sorted_moves_def) = sorted_moves_accessors;

(*
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;
*)

val exn_functions = define_monad_exception_functions ``:state_exn`` ``:linear_scan_hidden_state``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

val arr_manip = define_MFarray_manip_funs [colors_accessors, int_beg_accessors, int_end_accessors, sorted_regs_accessors, sorted_moves_accessors] sub_exn update_exn;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

val colors_manip = el 1 arr_manip;
val int_beg_manip = el 2 arr_manip;
val int_end_manip = el 3 arr_manip;
val sorted_regs_manip = el 4 arr_manip;
val sorted_moves_manip = el 5 arr_manip;

val colors_accessor = save_thm("colors_accessor",accessor_thm colors_manip);
val int_beg_accessor = save_thm("int_beg_accessor",accessor_thm int_beg_manip);
val int_end_accessor = save_thm("int_end_accessor",accessor_thm int_end_manip);
val sorted_regs_accessor = save_thm("sorted_regs_accessor",accessor_thm sorted_regs_manip);
val sorted_moves_accessor = save_thm("sorted_moves_accessor",accessor_thm sorted_moves_manip);

val colors_length_def = fetch "-" "colors_length_def";
val colors_sub_def    = fetch "-" "colors_sub_def";
val update_colors_def = fetch "-" "update_colors_def";

val int_beg_length_def = fetch "-" "int_beg_length_def";
val int_beg_sub_def    = fetch "-" "int_beg_sub_def";
val update_int_beg_def = fetch "-" "update_int_beg_def";

val int_end_length_def = fetch "-" "int_end_length_def";
val int_end_sub_def    = fetch "-" "int_end_sub_def";
val update_int_end_def = fetch "-" "update_int_end_def";

val sorted_regs_length_def = fetch "-" "sorted_regs_length_def";
val sorted_regs_sub_def    = fetch "-" "sorted_regs_sub_def";
val update_sorted_regs_def = fetch "-" "update_sorted_regs_def";

val sorted_moves_length_def = fetch "-" "sorted_moves_length_def";
val sorted_moves_sub_def    = fetch "-" "sorted_moves_sub_def";
val update_sorted_moves_def = fetch "-" "update_sorted_moves_def";

val numset_list_add_if_lt_monad_def = Define`
  (
    numset_list_add_if_lt_monad [] v =
      return ()
  ) /\ (
    numset_list_add_if_lt_monad (r::rs) v =
      do
        begr <- int_beg_sub r;
        if 0 < begr then
          do
            update_int_beg r v;
            numset_list_add_if_lt_monad rs v;
          od
        else if v <= begr then
          do
            update_int_beg r v;
            numset_list_add_if_lt_monad rs v;
          od
        else
          numset_list_add_if_lt_monad rs v
      od
  )
`

val numset_list_add_if_gt_monad_def = Define`
  (
    numset_list_add_if_gt_monad [] v =
      return ()
  ) /\ (
    numset_list_add_if_gt_monad (r::rs) v =
      do
        begr <- int_end_sub r;
        if 0 < begr then
          do
            update_int_end r v;
            numset_list_add_if_gt_monad rs v;
          od
        else if begr <= v then
          do
            update_int_end r v;
            numset_list_add_if_gt_monad rs v;
          od
        else
          numset_list_add_if_gt_monad rs v
      od
  )
`

val get_intervals_ct_monad_aux_def = Define`
    (
      get_intervals_ct_monad_aux (reg_alloc$Delta wr rd) (n : int) live =
        do
          numset_list_add_if_lt_monad wr n;
          numset_list_add_if_gt_monad wr n;
          numset_list_add_if_gt_monad rd (n-1);
          return (n-2, numset_list_insert rd (numset_list_delete wr live));
        od
    ) /\ (
      get_intervals_ct_monad_aux (reg_alloc$Set cutset) (n : int) live =
        do
          numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n;
          return (n-1, union cutset live);
        od
    ) /\ (
      get_intervals_ct_monad_aux (reg_alloc$Branch optcutset ct1 ct2) (n : int) live =
        do
          (n2, live2) <- get_intervals_ct_monad_aux ct2 n live;
          (n1, live1) <- get_intervals_ct_monad_aux ct1 n2 live;
          case optcutset of
          | NONE => return (n1, union live1 live2)
          | SOME cutset =>
            do
              numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n1;
              return (n1-1, union cutset (union live1 live2));
            od
        od
    ) /\ (
      get_intervals_ct_monad_aux (reg_alloc$Seq ct1 ct2) (n : int) live =
        do
          (n2, live2) <- get_intervals_ct_monad_aux ct2 n live;
          get_intervals_ct_monad_aux ct1 n2 live2;
        od
    )
`

val get_intervals_ct_monad_def = Define`
    get_intervals_ct_monad ct =
      do
        (n, live) <- get_intervals_ct_monad_aux ct 0 LN;
        numset_list_add_if_lt_monad (MAP FST (toAList live)) n;
        numset_list_add_if_gt_monad (MAP FST (toAList live)) n;
        return (n-1)
      od
`

val remove_inactive_intervals_def = tDefine "remove_inactive_intervals" `
    remove_inactive_intervals beg st =
      case st.active of
      | [] => return st
      | (e,r)::activetail => (
        if e < beg then
          do
            col <- colors_sub r;
            let st' = st with
              <| active    := activetail
               ; colorpool updated_by (\l. col::l)
               |> in
            remove_inactive_intervals beg st'
          od
        else
          return st
      )
`(
    WF_REL_TAC `measure (\(_,st). LENGTH (st.active))` >>
    rw []
);

val add_active_interval_def = Define `
  (
    add_active_interval v [] = [v]
  ) /\ (
    add_active_interval (v1 : int#num) (v2::tail) =
        if FST v1 <= FST v2 then
            v1::v2::tail
        else
            v2::(add_active_interval v1 tail)
  )
`

val find_color_in_list_def = Define`
  (
    find_color_in_list [] (forbidden:num_set) = NONE
  ) /\ (
    find_color_in_list (r::rs) forbidden =
        if lookup r forbidden = NONE then
          SOME (r, rs)
        else
          case find_color_in_list rs forbidden of
          | NONE => NONE
          | SOME (col, rest) => SOME (col, r::rest)
  )`

val find_color_in_colornum_def = Define`
    find_color_in_colornum st (forbidden:num_set) =
        if st.colormax <= st.colornum then
          (st, NONE)
        else
          (st with colornum  updated_by ($+1), SOME st.colornum)
`

val find_color_def = Define`
    find_color st (forbidden:num_set) =
        case find_color_in_list st.colorpool forbidden of
        | SOME (col, rest) => (st with colorpool := rest, SOME col)
        | NONE => find_color_in_colornum st forbidden
`

val spill_register_def = Define`
    spill_register st reg =
      do
        update_colors reg st.stacknum;
        return (st with stacknum updated_by $+1);
      od
`

val color_register_def = Define`
    color_register st reg col rend =
      do
        update_colors reg col;
        if is_phy_var reg then
          return (
            st with
              <| active  updated_by add_active_interval (rend, reg)
               ; phyregs updated_by (insert col ())
               |>
          )
        else
          return (st with active  updated_by add_active_interval (rend, reg))
      od
`

val find_last_stealable_def = Define`
  (
    find_last_stealable [] (forbidden:num_set) =
        return NONE
  ) /\ (
    find_last_stealable (x::xs) forbidden =
      do
        recursion <- find_last_stealable xs forbidden;
        case recursion of
        | SOME (steal, rest) => return (SOME (steal, x::rest))
        | NONE => (
            do
              xcol <- colors_sub (SND x);
              if ~(is_phy_var (SND x)) /\ (lookup xcol forbidden = NONE) then
                return (SOME (x, xs))
              else
                return NONE
            od
        )
      od
  )
`

val find_spill_def = Define`
    find_spill st (forbidden:num_set) reg rend force =
      do
        stealable <- find_last_stealable st.active forbidden;
        case stealable of
        | NONE => spill_register st reg
        | SOME ((stealend, stealreg), newactive) =>
          if force \/ rend < stealend then
            do
              stealcolor <- colors_sub stealreg;
              st' <- spill_register (st with active := newactive) stealreg;
              color_register st' reg stealcolor rend;
            od
          else
            spill_register st reg
      od
`

val linear_reg_alloc_step_aux_def = Define`
    linear_reg_alloc_step_aux st (forbidden:num_set) preferred reg rend force =
      (* TODO: this might be slow *)
      let preferred_filtered = FILTER (\c. MEM c st.colorpool) preferred in
      case find_color_in_list preferred_filtered forbidden of
      | SOME (col, _) => color_register (st with colorpool updated_by FILTER ($<> col)) reg col rend
      | NONE => (
        case find_color st forbidden of
        | (st', SOME col) => color_register st' reg col rend
        | (st', NONE) => find_spill st' forbidden reg rend force
      )
`

val linear_reg_alloc_step_pass1_def = Define`
    linear_reg_alloc_step_pass1 forced moves st reg =
      do
        rbeg <- int_beg_sub reg;
        rend <- int_end_sub reg;
        st' <- remove_inactive_intervals rbeg st;
        if is_stack_var reg then
          spill_register st' reg
        else
          do
            forced_forbidden_list <- st_ex_MAP colors_sub (the [] (lookup reg forced));
            let forced_forbidden = fromAList (MAP (\c. (c,())) forced_forbidden_list) in
            if is_phy_var reg then
              if reg < 2*(st'.colormax) then
                let forbidden = union st'.phyregs forced_forbidden in
                linear_reg_alloc_step_aux st' forbidden [] reg rend T
              else
                spill_register st' reg
            else
              do
                moves_preferred <- st_ex_MAP colors_sub (the [] (lookup reg moves));
                linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend F;
              od
          od
        od
`

val linear_reg_alloc_step_pass2_def = Define`
    linear_reg_alloc_step_pass2 forced moves st reg =
      do
        rbeg <- int_beg_sub reg;
        rend <- int_end_sub reg;
        st' <- remove_inactive_intervals rbeg st;
        forced_forbidden_list <- st_ex_MAP colors_sub (the [] (lookup reg forced));
        forced_forbidden <- return (fromAList (MAP (\c. (c,())) forced_forbidden_list));
        moves_preferred <- st_ex_MAP colors_sub (the [] (lookup reg moves));
        if is_phy_var reg then
          let forbidden = union st'.phyregs forced_forbidden in
          do
            linear_reg_alloc_step_aux st' forbidden [] reg rend F;
          od
        else
          linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend F;
      od
`


val linear_reg_alloc_pass1_initial_state_def = Define`
    linear_reg_alloc_pass1_initial_state k =
      <| active    := []
       ; colorpool := []
       ; colornum  := 0
       ; colormax  := k
       ; phyregs   := LN
       ; stacknum  := k
       |>`

val linear_reg_alloc_pass2_initial_state_def = Define`
    linear_reg_alloc_pass2_initial_state k nreg =
      <| active    := []
       ; colorpool := []
       ; colornum  := k
       ; colormax  := k+nreg
       ; phyregs   := LN
       ; stacknum  := k+nreg
       |>`

val find_reg_exchange_def = Define`
  (
    find_reg_exchange [] exch invexch = return (exch, invexch)
  ) /\ (
    find_reg_exchange (r::rs) exch invexch =
      do
        col1 <- colors_sub r;
        let fcol1 = r DIV 2 in
        let col2 = option_CASE (lookup fcol1 invexch) fcol1 (\x.x) in
        let fcol2 = option_CASE (lookup col1 exch) col1 (\x.x) in
        find_reg_exchange rs (insert col1 fcol1 (insert col2 fcol2 exch)) (insert fcol1 col1 (insert fcol2 col2 invexch))
      od
  )`

val MAP_colors_def = Define`
  (
    MAP_colors f 0 = return ()
  ) /\ (
    MAP_colors f (SUC n) =
      do
        col <- colors_sub n;
        update_colors n (f col);
        MAP_colors f n;
      od
  )
`

val apply_reg_exchange_def = Define`
    apply_reg_exchange phyregs =
      do
        (exch, invexch) <- find_reg_exchange phyregs LN LN;
        col_size <- colors_length;
        MAP_colors (\c. option_CASE (lookup c exch) c (\x.x)) col_size;
      od
`

val st_ex_FOLDL_def = Define`
  (
    st_ex_FOLDL f e [] = return e
  ) /\ (
    st_ex_FOLDL f e (x::xs) =
      do
        e' <- f e x;
        st_ex_FOLDL f e' xs;
      od
  )`

(* like st_ex_FILTER, but preserve the order *)
val st_ex_FILTER_good_def = Define`
  (
    st_ex_FILTER_good P [] = return []
  ) /\ (
    st_ex_FILTER_good P (x::xs) =
      do
        Px <- P x;
        if Px then
          do
            filter_xs <- st_ex_FILTER_good P xs;
            return (x::filter_xs)
          od
        else
          st_ex_FILTER_good P xs;
      od
  )`

val edges_to_adjlist_def = Define`
  (
    edges_to_adjlist [] acc = return acc
  ) /\ (
    edges_to_adjlist ((a,b)::abs) acc =
      if a = b then
        edges_to_adjlist abs acc
      else
        do
          bega <- int_beg_sub a;
          begb <- int_beg_sub b;
          if bega < begb \/ (bega = begb /\ a <= b) then
            edges_to_adjlist abs (insert b (a::(the [] (lookup b acc))) acc)
          else
            edges_to_adjlist abs (insert a (b::(the [] (lookup a acc))) acc)
        od
  )
`

val sort_moves_rev_def = Define`
  sort_moves_rev ls =
    QSORT (\p:num,x p',x'. p<p') ls`

val swap_regs_def = Define`
    swap_regs i1 i2 =
      do
        r1 <- sorted_regs_sub i1;
        r2 <- sorted_regs_sub i2;
        update_sorted_regs i1 r2;
        update_sorted_regs i2 r1;
      od
`

val partition_regs_def = tDefine "partition_regs" `
    partition_regs l rpiv begrpiv r =
      if r <= l then
        return l
      else
        do
          reg <- sorted_regs_sub l;
          begreg <- int_beg_sub reg;
          if begreg < begrpiv \/ (begreg = begrpiv /\ reg <= rpiv) then
              partition_regs (l+1) rpiv begrpiv r
          else
            do
              swap_regs l (r-1);
              partition_regs l rpiv begrpiv (r-1);
            od
        od
` (
  WF_REL_TAC `measure (\l,rpiv,begrpiv,r. r-l)`
);

val qsort_regs_def = tDefine "qsort_regs" `
    qsort_regs l r =
      if r <= l+1 then
        return ()
      else
        do
          rpiv <- sorted_regs_sub l;
          begrpiv <- int_beg_sub rpiv;
          m <- partition_regs (l+1) rpiv begrpiv r;
          swap_regs l (m-1);
          (* TODO: this condition is necessary for the termination argument, but useless in practice *)
          if m <= l \/ r < m then
            return ()
          else
            do
              qsort_regs l (m-1);
              qsort_regs m r;
            od
        od
`(
    WF_REL_TAC `measure (\l,r. r-l)`
)

val list_to_sorted_regs_def = Define`
  (
    list_to_sorted_regs [] n =
        return ()
  ) /\ (
    list_to_sorted_regs (r::rs) n =
      do
        update_sorted_regs n r;
        list_to_sorted_regs rs (n+1);
      od
  )`

val sorted_regs_to_list_def = tDefine "sorted_regs_to_list" `
    sorted_regs_to_list n last =
      if last <= n then
        return []
      else
        do
          r <- sorted_regs_sub n;
          l <- sorted_regs_to_list (n+1) last;
          return (r::l);
        od
` (
  WF_REL_TAC `measure (\n,last. last-n)`
);

val swap_moves_def = Define`
    swap_moves i1 i2 =
      do
        r1 <- sorted_moves_sub i1;
        r2 <- sorted_moves_sub i2;
        update_sorted_moves i1 r2;
        update_sorted_moves i2 r1;
      od
`

val partition_moves_def = tDefine "partition_moves" `
    partition_moves l ppiv r =
      if r <= l then
        return l
      else
        do
          move <- sorted_moves_sub l;
          if FST move < ppiv  then
            partition_moves (l+1) ppiv r
          else
            do
              swap_moves l (r-1);
              partition_moves l ppiv (r-1);
            od
        od
` (
  WF_REL_TAC `measure (\l,piv,r. r-l)`
);

val qsort_moves_def = tDefine "qsort_moves" `
    qsort_moves l r =
      if r <= l+1 then
        return ()
      else
        do
          piv <- sorted_moves_sub l;
          m <- partition_moves (l+1) (FST piv) r;
          swap_moves l (m-1);
          (* TODO: this condition is necessary for the termination argument, but useless in practice *)
          if m <= l \/ r < m then
            return ()
          else
            do
              qsort_moves l (m-1);
              qsort_moves m r;
            od
        od
`(
    WF_REL_TAC `measure (\l,r. r-l)`
)


val list_to_sorted_moves_def = Define`
  (
    list_to_sorted_moves [] n =
        return ()
  ) /\ (
    list_to_sorted_moves (r::rs) n =
      do
        update_sorted_moves n r;
        list_to_sorted_moves rs (n+1);
      od
  )`

val sorted_moves_to_list_def = tDefine "sorted_moves_to_list" `
    sorted_moves_to_list n len =
      if len <= n then
        return []
      else
        do
          r <- sorted_moves_sub n;
          l <- sorted_moves_to_list (n+1) len;
          return (r::l);
        od
` (
  WF_REL_TAC `measure (\n,len. len-n)`
);

val linear_reg_alloc_intervals_def = Define`
    linear_reg_alloc_intervals k forced moves reglist_unsorted =
        let lenreg = LENGTH reglist_unsorted in
        let lenmoves = LENGTH moves in
        let st_init_pass1 = linear_reg_alloc_pass1_initial_state k in
        do
          list_to_sorted_regs reglist_unsorted 0;
          qsort_regs 0 lenreg;
          reglist <- sorted_regs_to_list 0 lenreg;
          phyregs <- return (FILTER is_phy_var reglist);
          phyphyregs <- return (FILTER (\r. r < 2*k) phyregs);
          stackphyregs <- return (FILTER (\r. 2*k <= r) phyregs);
          list_to_sorted_moves moves 0;
          qsort_moves 0 lenmoves;
          smoves <- sorted_moves_to_list 0 lenmoves;
          moves_adjlist <- edges_to_adjlist (MAP SND smoves) LN;
          forced_adjlist <- edges_to_adjlist forced LN;
          st_end_pass1 <- st_ex_FOLDL (linear_reg_alloc_step_pass1 forced_adjlist moves_adjlist) st_init_pass1 reglist;
          apply_reg_exchange phyphyregs;
          stacklist <- st_ex_FILTER_good (\r.
            do
              col <- colors_sub r;
              return (is_stack_var r \/ k <= col);
            od
          ) reglist;
          st_init_pass2 <- return (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist));
          stackset <- return (fromAList (MAP (\r. (r,())) stacklist));
          forced_adjlist' <- return (map (FILTER (\r. lookup r stackset <> NONE)) forced_adjlist);
          moves_adjlist' <- return (map (FILTER (\r. lookup r stackset <> NONE)) moves_adjlist);
          st_end_pass2 <- st_ex_FOLDL (linear_reg_alloc_step_pass2 forced_adjlist' moves_adjlist') st_init_pass2 stacklist;
          apply_reg_exchange stackphyregs;
        od
`

val extract_coloration_def = Define`
  (
    extract_coloration invbij [] acc = return acc
  ) /\ (
    extract_coloration invbij (r::rs) acc =
      do
        col <- colors_sub r;
        extract_coloration invbij rs (insert (the 0 (lookup r invbij)) col acc);
      od
  )
`

val _ = Datatype `
  bijection_state =
    <| bij : num num_map
     ; invbij : num num_map
     ; nmax : num
     ; nstack : num
     ; nalloc : num
     |>`

val find_bijection_init_def = Define`
    find_bijection_init =
        <| bij := LN
         ; invbij := LN
         ; nmax := 0
         ; nstack := 3
         ; nalloc := 1
         |>`

val find_bijection_step_def = Define`
    find_bijection_step state r =
      if lookup r state.bij <> NONE then
        state
      else if is_phy_var r then
        state with
          <| bij := insert r r state.bij
           ; invbij := insert r r state.invbij
           ; nmax := MAX r state.nmax
             |>
      else if is_stack_var r then
        state with
          <| bij := insert r state.nstack state.bij
           ; invbij := insert state.nstack r state.invbij
           ; nmax := MAX state.nstack state.nmax
           ; nstack := state.nstack+4
           |>
      else
        state with
          <| bij := insert r state.nalloc state.bij
           ; invbij := insert state.nalloc r state.invbij
           ; nmax := MAX state.nalloc state.nmax
           ; nalloc := state.nalloc+4
           |>
`

val find_bijection_clash_tree_def = Define`
  (
    find_bijection_clash_tree state (Delta wr rd) =
      FOLDL find_bijection_step (FOLDL find_bijection_step state rd) wr
  ) /\ (
    find_bijection_clash_tree state (Set cutset) =
      foldi (\r v acc. find_bijection_step acc r) 0 state cutset
  ) /\ (
    find_bijection_clash_tree state (Branch optcutset ct1 ct2) =
      let state1 = find_bijection_clash_tree state ct1 in
      let state2 = find_bijection_clash_tree state1 ct2 in
        case optcutset of
        | NONE => state2
        | SOME cutset =>
          foldi (\r v acc. find_bijection_step acc r) 0 state2 cutset
  ) /\ (
    find_bijection_clash_tree state (Seq ct1 ct2) =
      let state1 = find_bijection_clash_tree state ct1 in
      find_bijection_clash_tree state1 ct2
  )`

val apply_bijection_def = Define`
    apply_bijection bij (interval : int num_map) =
        foldi (\r i acc. insert (the 0 (lookup r bij)) i acc) 0 LN interval
`

val array_fields_names = ["colors", "int_beg", "int_end", "sorted_regs", "sorted_moves"];
val run_i_linear_scan_hidden_state_def =
  define_run ``:linear_scan_hidden_state``
  array_fields_names
  "i_linear_scan_hidden_state";

val linear_reg_alloc_and_extract_coloration_def = Define`
    linear_reg_alloc_and_extract_coloration ct k forced moves reglist_unsorted invbij nmax =
      do
        get_intervals_ct_monad ct;
        linear_reg_alloc_intervals k forced moves reglist_unsorted;
        extract_coloration invbij reglist_unsorted LN;
      od
`

val size_of_clash_tree_def = Define`
  (
    size_of_clash_tree (Delta wr rd) =
      2i
  ) /\ (
    size_of_clash_tree (Set cutset) =
      1i
  ) /\ (
    size_of_clash_tree (Branch optcutset ct1 ct2) =
      (if IS_SOME optcutset then 1 else 0) + size_of_clash_tree ct1 + size_of_clash_tree ct2
  ) /\ (
    size_of_clash_tree (Seq ct1 ct2) =
      size_of_clash_tree ct1 + size_of_clash_tree ct2
  )`

val run_linear_reg_alloc_intervals_def = Define`
    run_linear_reg_alloc_intervals ct k forced moves reglist_unsorted invbij nmax =
        run_i_linear_scan_hidden_state
          (linear_reg_alloc_and_extract_coloration ct k forced moves reglist_unsorted invbij nmax)
          <| colors := (nmax+1, 0)
           ; int_beg := (nmax+1, 1)
           ; int_end := (nmax+1, 1)
           ; sorted_regs := (nmax+1, 0)
           ; sorted_moves := (LENGTH moves, (0,(0,0)))
           |>
`

val apply_bij_on_clash_tree_def = Define`
  (
    apply_bij_on_clash_tree (Delta wr rd) bij =
      Delta (MAP (\r. the 0n (lookup r bij)) wr) (MAP (\r. the 0n (lookup r bij)) rd)
  ) /\ (
    apply_bij_on_clash_tree (Set cutset) bij =
      Set (foldi (\r _ acc. insert (the 0n (lookup r bij)) () acc) 0 LN cutset)
  ) /\ (
    apply_bij_on_clash_tree (Branch optcutset ct1 ct2) bij =
      Branch (OPTION_MAP (foldi (\r _ acc. insert (the 0n (lookup r bij)) () acc) 0 LN) optcutset) (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij)
  ) /\ (
    apply_bij_on_clash_tree (Seq ct1 ct2) bij =
      Seq (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij)
  )`



val linear_scan_reg_alloc_def = Define`
    linear_scan_reg_alloc k moves ct forced =
        let bijstate = find_bijection_clash_tree find_bijection_init ct in
        let ct' = apply_bij_on_clash_tree ct bijstate.bij in
        let forced' = MAP (\r1,r2. (the 0 (lookup r1 bijstate.bij), the 0 (lookup r2 bijstate.bij))) forced in
        let moves' = MAP (\p,(r1,r2). (p,(the 0 (lookup r1 bijstate.bij), the 0 (lookup r2 bijstate.bij)))) moves in
        let reglist_unsorted = (MAP SND (toAList bijstate.bij)) in
        run_linear_reg_alloc_intervals ct' k forced' moves' reglist_unsorted bijstate.invbij bijstate.nmax (* (0i-((size_of_clash_tree ct') + 1)) *)
`

(*
(* === translation (TODO: move to bootstrap translation) === *)

(* TODO: remove when moved to bootstrap *)
val _ = register_type ``:'a num_map``;
val _ = register_type ``:'a list``;

(*
 *  Set up the monadic translator
 *)

(* The record types used for the monadic state and exceptions *)
val state_type = ``:linear_scan_hidden_state``
val exn_type   = ``:state_exn``;
val _          = register_exn_type exn_type;

val STATE_EXN_TYPE_def = theorem "REG_ALLOC_STATE_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "LINEAR_SCAN_HIDDEN_STATE";

(* Accessor functions are defined (and used) previously together
   with exceptions, etc. *)

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];

val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [
    ("colors", get_colors_def, set_colors_def, colors_length_def, colors_sub_def, update_colors_def),
    ("int_beg", get_int_beg_def, set_int_beg_def, int_beg_length_def, int_beg_sub_def, update_int_beg_def),
    ("int_end", get_int_end_def, set_int_end_def, int_end_length_def, int_end_sub_def, update_int_end_def),
    ("sorted_regs", get_sorted_regs_def, set_sorted_regs_def, sorted_regs_length_def, sorted_regs_sub_def, update_sorted_regs_def),
    ("sorted_moves", get_sorted_moves_def, set_sorted_moves_def, sorted_moves_length_def, sorted_moves_sub_def, update_sorted_moves_def)
];

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialization *)

val _ = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list
            store_hprop_name
            state_type
            exn_ri_def
            [] (* exn_functions *)
            add_type_theories
            store_pinv_def_opt

(* Translate basics -- TODO: remove in bootstrap *)

val res = translate NULL
val res = translate LENGTH
val res = translate MAP
val res = translate FILTER
val res = translate EVEN
val res = translate FST
val res = translate SND
val res = translate HD;
val res = translate TL;
val res = translate K_DEF;
val res = translate LAST_DEF;
val res = translate FRONT_DEF;
val res = translate the_def;
val res = translate MEMBER_def;

val hd_side = prove(
  ``hd_side x <=> x <> []``,
  Cases_on `x` \\ fs [fetch "-" "hd_side_def"])
  |> update_precondition;

val tl_side = prove(
  ``tl_side x <=> x <> []``,
  Cases_on `x` \\ fs [fetch "-" "tl_side_def"])
  |> update_precondition;

val last_side = prove(
  ``!x. last_side x <=> x <> []``,
  Induct \\ simp [Once (fetch "-" "last_side_def")])
  |> update_precondition;

val front_side = prove(
  ``!x. front_side x <=> x <> []``,
  Induct \\ simp [Once (fetch "-" "front_side_def")])
  |> update_precondition;

val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate delete_def;
val res = translate numset_list_delete_def;
val res = translate lookup_def
val res = translate insert_def
val res = translate union_def
val res = translate map_def
val res = translate difference_def;
val res = translate is_stack_var_def
val res = translate is_phy_var_def
val res = translate fromAList_def;
val res = translate sortingTheory.PART_DEF
val res = translate sortingTheory.PARTITION_DEF
val res = translate sortingTheory.QSORT_DEF

val res = translate pairTheory.LEX_DEF
val res = translate lrnext_def
val res = translate foldi_def
val res = translate toAList_def
val res = translate MAX_DEF;
val res = translate FOLDL;

(* Translate linear scan register allocator *)

val map_colors_sub_def = Define `
  (map_colors_sub [] = return []) ∧
  (map_colors_sub (x::xs) =
     do fx <- colors_sub x; fxs <- map_colors_sub xs; return (fx::fxs) od)`

Theorem map_colors_sub_eq:
   map_colors_sub = st_ex_MAP colors_sub
Proof
  once_rewrite_tac [FUN_EQ_THM]
  \\ Induct \\ fs [map_colors_sub_def,st_ex_MAP_def]
QED

val res = m_translate spill_register_def;
val res = m_translate MAP_colors_def;
val res = m_translate st_ex_FOLDL_def;
val res = m_translate map_colors_sub_def;
val res = m_translate remove_inactive_intervals_def;

val res = translate linear_reg_alloc_pass1_initial_state_def
val res = translate linear_reg_alloc_pass2_initial_state_def
val res = translate add_active_interval_def
val res = translate find_color_in_list_def
val res = translate find_color_in_colornum_def
val res = translate find_color_def
val res = m_translate color_register_def
val res = m_translate find_last_stealable_def;
val res = m_translate find_spill_def;
val res = m_translate (linear_reg_alloc_step_aux_def
                       |> REWRITE_RULE [MEMBER_INTRO]);
val res = m_translate (linear_reg_alloc_step_pass1_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);
val res = m_translate (linear_reg_alloc_step_pass2_def
                       |> REWRITE_RULE [GSYM map_colors_sub_eq]);

val res = m_translate find_reg_exchange_def
val res = m_translate apply_reg_exchange_def
val res = translate edges_to_adjlist_impl_def
val res = m_translate st_ex_FILTER_good_def;

val res = translate sort_moves_def;

val res = m_translate (linear_reg_alloc_intervals_def
                       |> REWRITE_RULE [edges_to_adjlist_impl_thm]);

val res = m_translate extract_coloration_def;
val res = translate find_bijection_init_def;
val res = translate find_bijection_step_def;
val res = translate find_bijection_def;
val res = translate apply_bijection_def;

val res = m_translate linear_reg_alloc_intervals_and_extract_coloration_def;
val res = m_translate_run run_linear_reg_alloc_intervals_def;

val res = translate get_live_tree_def;
val res = translate numset_list_insert_def;
val res = translate get_live_backward_def;
val res = translate fix_domination_def;
val res = translate numset_list_add_if_def;
val res = translate numset_list_add_if_lt_def;
val res = translate numset_list_add_if_gt_def;
val res = translate get_intervals_def;
val res = translate linear_scan_reg_alloc_def;

*)
val _ = export_theory ();
