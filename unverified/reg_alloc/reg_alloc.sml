structure reg_alloc = struct
  (* Manual changes:
    - Turn Some into SOME
    - Turn None into NONE
    - Turn List.member/List.genlist/List.foldl into member,genlist and foldl resp.
    - Add the following decls
    - Manually inserted debugging calls into do_reg_alloc
  *)
  fun  foldl v4 v3 v5 =
  case  v5
  of  []  =>  v3
  |   v2::v1 =>  (foldl v4 (v4 v3 v2) v1);
  fun  k v2 =  (fn  v1 => v2);
  fun  max v1 =
    (fn  v2 =>
      if  (v1 < v2)
      then  v2
       else  v1);
  fun  even v1 =
    if  (v1 = 0)
    then  (0 <= 0)
    else  ((even (let val  k = v1 - 1
                   in
                    if  (k < 0)
                    then  0
                     else  k
                   end)) = (0 < 0));
  val filter = List.filter;
  val concat = List.concat;
  val map = List.map
  fun  fst v3 =  case  v3 of  (v2,v1) =>  v2;
  fun  snd v3 =  case  v3 of  (v2,v1) =>  v1;
  fun  member v4 v3 =
    case  v3
    of  []  =>  (0 < 0)
    |   v2::v1 =>  ((v4 = v2) orelse  (member v4 v1));
  fun  snoc v4 v3 =
    case  v3
    of  []  =>  [v4]
    |   v2::v1 =>  (v2::(snoc v4 v1));
  fun  genlist v1 v2 =
    if  (v2 = 0)
    then  []
     else  (snoc (v1 (let val  k = v2 - 1
                       in
                        if  (k < 0)
                        then  0
                         else  k
                       end)) (genlist v1 (let val  k = v2 - 1
                                           in
                                            if  (k < 0)
                                            then  0
                                             else  k
                                           end)));
  fun  part v3 v6 v4 v5 =
    case  v6
    of  []  =>  (v4,v5)
    |   v2::v1 =>  (if  (v3 v2)
                    then  (part v3 v1 (v2::v4) v5)
                    else  (part v3 v1 v4 (v2::v5)));
  fun  partition v1 =  (fn  v2 => part v1 v2 [] [] );
  fun  qsort v7 v8 =
    case  v8
    of  []  =>  []
     |   v6::v5 =>  (let val  v3 = partition (fn  v4 => (v7 v4 v6)) v5
                      in
                       case  v3
                       of  (v2,v1) =>  (qsort v7 v2) @ (v6::(qsort v7 v1))
                     end);

  (* End manual stuff *)
  datatype reg_alloc_tag =  Stemp
  |  Atemp
  |  Fixed of  int;
  datatype 'a sptree_spt =  Bs of  'a sptree_spt *  'a  *  'a sptree_spt
  |  Bn of  'a sptree_spt *  'a sptree_spt
  |  Ls of  'a
   |  Ln;
  datatype reg_alloc_clash_tree =  Seq of  reg_alloc_clash_tree *  reg_alloc_clash_tree
  |  Branch of  unit sptree_spt option *  reg_alloc_clash_tree *  reg_alloc_clash_tree
  |  Set of  unit sptree_spt
  |  Delta of  int list *  int list;
  datatype reg_alloc_algorithm =  Irc
  |  Simple;
  exception  Fail of  char list;
  fun  lookup_1 v7 v8 =
  case  v8
  of  Ln =>  NONE
  |   Ls(v1) =>  (if  (v7 = 0)
  then  (SOME(v1))
  else  NONE)
  |   Bn(v3,v2) =>  (if  (v7 = 0)
  then  NONE
   else  (lookup_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) (if  (even v7)
  then  v3
   else  v2)))
  |   Bs(v6,v5,v4) =>  (if  (v7 = 0)
  then  (SOME(v5))
  else  (lookup_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) (if  (even v7)
  then  v6
   else  v4)));
  fun  insert_1 v7 v8 v9 =
  case  v9
  of  Ln =>  (if  (v7 = 0)
  then  (Ls(v8))
  else  (if  (even v7)
  then  (Bn(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln,Ln))
  else  (Bn(Ln,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln))))
  |   Ls(v1) =>  (if  (v7 = 0)
  then  (Ls(v8))
  else  (if  (even v7)
  then  (Bs(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln,v1,Ln))
  else  (Bs(Ln,v1,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 Ln))))
  |   Bn(v3,v2) =>  (if  (v7 = 0)
  then  (Bs(v3,v8,v2))
  else  (if  (even v7)
  then  (Bn(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v3,v2))
  else  (Bn(v3,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v2))))
  |   Bs(v6,v5,v4) =>  (if  (v7 = 0)
  then  (Bs(v6,v8,v4))
  else  (if  (even v7)
  then  (Bs(insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v6,v5,v4))
  else  (Bs(v6,v5,insert_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v8 v4))));
  fun  lrnext v1 =
  if  (v1 = 0)
  then  1
   else  (2 * (lrnext ((let val  k = v1 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2)));
  fun  foldi v9 v10 v12 v11 =
  case  v11
  of  Ln =>  v12
  |   Ls(v1) =>  (v9 v10 v1 v12)
  |   Bn(v4,v3) =>  (let val  v2 = lrnext v10
   in
    foldi v9 (v10 + v2) (foldi v9 (v10 + (2 * v2)) v12 v4) v3
   end)
  |   Bs(v8,v7,v6) =>  (let val  v5 = lrnext v10
   in
    foldi v9 (v10 + v5) (v9 v10 v7 (foldi v9 (v10 + (2 * v5)) v12 v8)) v6
   end);
  fun  toalist v4 =
    foldi (fn  v3 => (fn  v2 => (fn  v1 => ((v3,v2)::v1)))) 0 [] v4;
  fun  map_1 v7 v8 =
  case  v8
  of  Ln =>  Ln
  |   Ls(v1) =>  (Ls(v7 v1))
  |   Bn(v3,v2) =>  (Bn(map_1 v7 v3,map_1 v7 v2))
  |   Bs(v6,v5,v4) =>  (Bs(map_1 v7 v6,v7 v5,map_1 v7 v4));
  fun  count_list_aux v2 v1 =
  if  (v2 = 0)
  then  v1
   else  (count_list_aux (let val  k = v2 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) (let val  k = v2 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end::v1));
  fun  count_list v1 =  count_list_aux v1 [] ;
  fun  mk_bs v13 =
    (fn  v14 =>
      (fn  v15 =>
        case  v15
        of  Ln =>  (case  v13
        of  Ln =>  (Ls(v14))
        |   (Ls(v1)) =>  (Bs(Ls(v1),v14,Ln))
        |   (Bn(v3,v2)) =>  (Bs(Bn(v3,v2),v14,Ln))
        |   (Bs(v6,v5,v4)) =>  (Bs(Bs(v6,v5,v4),v14,Ln)))
        |   Ls(v7) =>  (Bs(v13,v14,Ls(v7)))
        |   Bn(v9,v8) =>  (Bs(v13,v14,Bn(v9,v8)))
        |   Bs(v12,v11,v10) =>  (Bs(v13,v14,Bs(v12,v11,v10)))));
  fun  mk_bn v13 =
    (fn  v14 =>
      case  v13
      of  Ln =>  (case  v14
      of  Ln =>  Ln
      |   (Ls(v1)) =>  (Bn(Ln,Ls(v1)))
      |   (Bn(v3,v2)) =>  (Bn(Ln,Bn(v3,v2)))
      |   (Bs(v6,v5,v4)) =>  (Bn(Ln,Bs(v6,v5,v4))))
      |   Ls(v7) =>  (Bn(Ls(v7),v14))
      |   Bn(v9,v8) =>  (Bn(Bn(v9,v8),v14))
      |   Bs(v12,v11,v10) =>  (Bn(Bs(v12,v11,v10),v14)));
  fun  delete_1 v7 v8 =
  case  v8
  of  Ln =>  Ln
  |   Ls(v1) =>  (if  (v7 = 0)
  then  Ln
   else  (Ls(v1)))
  |   Bn(v3,v2) =>  (if  (v7 = 0)
  then  (Bn(v3,v2))
  else  (if  (even v7)
  then  (mk_bn (delete_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v3) v2)
  else  (mk_bn v3 (delete_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v2))))
  |   Bs(v6,v5,v4) =>  (if  (v7 = 0)
  then  (Bn(v6,v4))
  else  (if  (even v7)
  then  (mk_bs (delete_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v6) v5 v4)
  else  (mk_bs v6 v5 (delete_1 ((let val  k = v7 - 1
   in
    if  (k < 0)
  then  0
   else  k
   end) div 2) v4))));
  fun  union_1 v25 v26 =
  case  v25
  of  Ln =>  v26
  |   Ls(v7) =>  (case  v26
  of  Ln =>  (Ls(v7))
  |   (Ls(v1)) =>  (Ls(v7))
  |   (Bn(v3,v2)) =>  (Bs(v3,v7,v2))
  |   (Bs(v6,v5,v4)) =>  (Bs(v6,v7,v4)))
  |   Bn(v15,v14) =>  (case  v26
  of  Ln =>  (Bn(v15,v14))
  |   (Ls(v8)) =>  (Bs(v15,v8,v14))
  |   (Bn(v10,v9)) =>  (Bn(union_1 v15 v10,union_1 v14 v9))
  |   (Bs(v13,v12,v11)) =>  (Bs(union_1 v15 v13,v12,union_1 v14 v11)))
  |   Bs(v24,v23,v22) =>  (case  v26
  of  Ln =>  (Bs(v24,v23,v22))
  |   (Ls(v16)) =>  (Bs(v24,v23,v22))
  |   (Bn(v18,v17)) =>  (Bs(union_1 v24 v18,v23,union_1 v22 v17))
  |   (Bs(v21,v20,v19)) =>  (Bs(union_1 v24 v21,v23,union_1 v22 v19)));
  fun  difference v25 v26 =
  case  v25
  of  Ln =>  Ln
  |   Ls(v7) =>  (case  v26
  of  Ln =>  (Ls(v7))
  |   (Ls(v1)) =>  Ln
  |   (Bn(v3,v2)) =>  (Ls(v7))
  |   (Bs(v6,v5,v4)) =>  Ln)
  |   Bn(v15,v14) =>  (case  v26
  of  Ln =>  (Bn(v15,v14))
  |   (Ls(v8)) =>  (Bn(v15,v14))
  |   (Bn(v10,v9)) =>  (mk_bn (difference v15 v10) (difference v14 v9))
  |   (Bs(v13,v12,v11)) =>  (mk_bn (difference v15 v13) (difference v14 v11)))
  |   Bs(v24,v23,v22) =>  (case  v26
  of  Ln =>  (Bs(v24,v23,v22))
  |   (Ls(v16)) =>  (Bn(v24,v22))
  |   (Bn(v18,v17)) =>  (mk_bs (difference v24 v18) v23 (difference v22 v17))
  |   (Bs(v21,v20,v19)) =>  (mk_bn (difference v24 v21) (difference v22 v19)));
  fun  list_remap v12 v13 =
  case  v12
  of  []  =>  (case  v13 of  (v4,v3) =>  (case  v3 of  (v2,v1) =>  (v4,(v2,v1))))
  |   v11::v10 =>  (case  v13
  of  (v9,v8) =>  (case  v8
  of  (v7,v6) =>  (case  (lookup_1 v11 v9)
  of  NONE =>  (list_remap v10 (insert_1 v11 v6 v9,(insert_1 v6 v11 v7,v6 + 1)))
  |   (SOME(v5)) =>  (list_remap v10 (v9,(v7,v6))))));
  fun  mk_bij_aux v11 v12 =
  case  v11
  of  Delta(v2,v1) =>  (list_remap v2 (list_remap v1 v12))
  |   Set(v3) =>  (list_remap (List.map fst (toalist v3)) v12)
  |   Branch(v8,v7,v6) =>  (let val  v5 = mk_bij_aux v6 (mk_bij_aux v7 v12)
  in
    case  v8
  of  NONE =>  v5
  |   SOME(v4) =>  (list_remap (List.map fst (toalist v4)) v5)
  end)
  |   Seq(v10,v9) =>  (mk_bij_aux v10 (mk_bij_aux v9 v12));
  fun  mk_bij v6 =
    let val  v5 = mk_bij_aux v6 (Ln,(Ln,0))
    in
      case  v5 of  (v4,v3) =>  (case  v3 of  (v2,v1) =>  (v4,(v2,v1)))
    end;
  fun  is_phy_var v1 =  (v1 mod 2) = 0;
  fun  sp_default v3 =
    (fn  v2 =>
      case  (lookup_1 v2 v3)
      of  NONE =>  (if  (is_phy_var v2)
      then  (v2 div 2)
      else  v2)
      |   SOME(v1) =>  v1);
  fun  extract_tag v2 =
    case  v2
    of  Fixed(v1) =>  v1
    |   Atemp =>  0
    |   Stemp =>  0;
  fun  fromalist v5 =
  case  v5
  of  []  =>  Ln
  |   v4::v3 =>  (case  v4 of  (v2,v1) =>  (insert_1 v2 v1 (fromalist v3)));
  fun  sort_moves v7 =
    qsort (fn  v6 =>
      (case  v6
      of  (v5,v4) =>  (fn  v3 => (case  v3 of  (v2,v1) =>  (v5 > v2))))) v7;
  fun  smerge v10 v9 =
  case  v10
  of  []  =>  v9
  |   v8::v7 =>  (case  v9
  of  []  =>  (v8::v7)
  |   (v6::v5) =>  (case  v6
  of  (v4,v3) =>  (case  v8
  of  (v2,v1) =>  (if  (v2 >= v4)
  then  ((v2,v1)::(smerge v7 ((v4,v3)::v5)))
  else  ((v4,v3)::(smerge ((v2,v1)::v7) v5))))));
  fun  pair_rename v11 =
    (fn  v9 =>
      (fn  v10 =>
        case  (v9,v10)
        of  (v8,v7) =>  (case  v7
        of  (v6,v5) =>  (case  v5
        of  (v4,v3) =>  (let val  v2 =
          if  (v4 = v8)
          then  v11
           else  v4
            val  v1 =
          if  (v3 = v8)
          then  v11
           else  v3
         in
          (v6,(v2,v1))
        end)))));
  fun  safe_div v2 =
    (fn  v1 =>
      if  (v1 = 0)
      then  0
       else  (v2 div v1));
  fun  lookup_any v4 =
    (fn  v3 =>
      (fn  v2 =>
        case  (lookup_1 v4 v3)
        of  NONE =>  v2
        |   SOME(v1) =>  v1));
  fun  tag_col v2 =
    case  v2
    of  Fixed(v1) =>  v1
    |   Atemp =>  0
    |   Stemp =>  0;
  fun  unbound_colour v3 v4 =
  case  v4
  of  []  =>  v3
  |   v2::v1 =>  (if  (v3 < v2)
  then  v3
   else  (if  (v2 = v3)
  then  (unbound_colour (v3 + 1) v1)
  else  (unbound_colour v3 v1)));
  fun  pri_move_insert v3 =
    (fn  v4 =>
      (fn  v5 =>
        (fn  v2 =>
          case  (lookup_1 v4 v2)
          of  NONE =>  (insert_1 v4 [(v3,v5)] v2)
          |   SOME(v1) =>  (insert_1 v4 ((v3,v5)::v1) v2))));
  fun  undir_move_insert v2 =
    (fn  v3 =>
      (fn  v4 =>
        (fn  v1 => pri_move_insert v2 v3 v4 (pri_move_insert v2 v4 v3 v1))));
  fun  moves_to_sp v9 v8 =
  case  v9
  of  []  =>  v8
  |   v7::v6 =>  (let val  v5 = v7
   in
    case  v5
  of  (v4,v3) =>  (case  v3
  of  (v2,v1) =>  (moves_to_sp v6 (undir_move_insert v4 v2 v1 v8)))
  end);
  fun  resort_moves v2 =  map_1 (fn  v1 => (List.map snd (sort_moves v1))) v2;
  datatype reg_alloc_ira_state =  Recordtypeira_state of  (int *  int list) *  (int *  reg_alloc_tag) *  (int *  int) *  int *  int list *  int list *  int list *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  (int *  int option) *  (int *  bool) *  int list;
  fun  ira_state_adj_ls v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v12;
  fun  ira_state_node_tag v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v11;
  fun  ira_state_degrees v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v10;
  fun  ira_state_dim v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v9;
  fun  ira_state_simp_wl v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v8;
  fun  ira_state_spill_wl v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v7;
  fun  ira_state_freeze_wl v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v6;
  fun  ira_state_avail_moves_wl v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v5;
  fun  ira_state_unavail_moves_wl v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v4;
  fun  ira_state_coalesced v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v3;
  fun  ira_state_move_related v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v2;
  fun  ira_state_stack v13 =
    case  v13
    of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v1;
  fun  ira_state_adj_ls_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v13 v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_node_tag_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v13 v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_degrees_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v13 v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_dim_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v13 v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_simp_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v13 v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_spill_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v13 v7,v6,v5,v4,v3,v2,v1)));
  fun  ira_state_freeze_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v13 v6,v5,v4,v3,v2,v1)));
  fun  ira_state_avail_moves_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v13 v5,v4,v3,v2,v1)));
  fun  ira_state_unavail_moves_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v13 v4,v3,v2,v1)));
  fun  ira_state_coalesced_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v13 v3,v2,v1)));
  fun  ira_state_move_related_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v13 v2,v1)));
  fun  ira_state_stack_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypeira_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v13 v1)));
  datatype reg_alloc_ra_state =  Recordtypera_state of  int list list *  reg_alloc_tag list *  int list *  int *  int list *  int list *  int list *  (int *  (int *  int)) list *  (int *  (int *  int)) list *  int option list *  bool list *  int list;
  fun  ra_state_adj_ls v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v12;
  fun  ra_state_node_tag v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v11;
  fun  ra_state_degrees v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v10;
  fun  ra_state_dim v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v9;
  fun  ra_state_simp_wl v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v8;
  fun  ra_state_spill_wl v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v7;
  fun  ra_state_freeze_wl v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v6;
  fun  ra_state_avail_moves_wl v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v5;
  fun  ra_state_unavail_moves_wl v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v4;
  fun  ra_state_coalesced v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v3;
  fun  ra_state_move_related v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v2;
  fun  ra_state_stack v13 =
    case  v13
    of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  v1;
  fun  ra_state_adj_ls_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v13 v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_node_tag_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v13 v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_degrees_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v13 v10,v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_dim_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v13 v9,v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_simp_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v13 v8,v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_spill_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v13 v7,v6,v5,v4,v3,v2,v1)));
  fun  ra_state_freeze_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v13 v6,v5,v4,v3,v2,v1)));
  fun  ra_state_avail_moves_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v13 v5,v4,v3,v2,v1)));
  fun  ra_state_unavail_moves_wl_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v13 v4,v3,v2,v1)));
  fun  ra_state_coalesced_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v13 v3,v2,v1)));
  fun  ra_state_move_related_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v13 v2,v1)));
  fun  ra_state_stack_fupd v13 =
    (fn  v14 =>
      case  v14
      of  Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1) =>  (Recordtypera_state(v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v13 v1)));
  datatype ( 'a  ,  'b ) ml_monadBase_exc =  Failure of  'b
   |  Success of  'a ;
  fun  reg_alloc_aux alg =
    (fn  sc =>
      (fn  v5 =>
        (fn  v4 =>
          (fn  v3 =>
            (fn  v2 =>
              (fn  v1 =>
                let val  move_related = Array.array ( (snd (snd v1)), (0 < 0))
                    val  coalesced = Array.array ( (snd (snd v1)), NONE)
                    val  degrees = Array.array ( (snd (snd v1)), 0)
                    val  node_tag = Array.array ( (snd (snd v1)), Atemp)
                    val  adj_ls = Array.array ( (snd (snd v1)), [] )
                    val  stack = ref( [] )
                    val  unavail_moves_wl = ref( [] )
                    val  avail_moves_wl = ref( [] )
                    val  freeze_wl = ref( [] )
                    val  spill_wl = ref( [] )
                    val  simp_wl = ref( [] )
                    val  dim = ref( (snd (snd v1)))
                    fun  st_ex_foreach v5 v4 =
                case  v5
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  st_ex_foreach v2 v4
                 end)
                    fun  st_ex_map v5 v6 =
                case  v6
                of  []  =>  []
                 |   v4::v3 =>  (let val  v2 = v5 v4
                    val  v1 = st_ex_map v5 v3
                 in
                  v2::v1
                 end)
                    fun  st_ex_partition v4 v6 v7 v5 =
                case  v6
                of  []  =>  (v7,v5)
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  if  v1
                 then  (st_ex_partition v4 v2 (v3::v7) v5)
                else  (st_ex_partition v4 v2 v7 (v3::v5))
                end)
                    fun  st_ex_filter v4 v6 v5 =
                case  v6
                of  []  =>  v5
                |   v3::v2 =>  (let val  v1 = v4 v3
                 in
                  if  v1
                 then  (st_ex_filter v4 v2 (v3::v5))
                else  (st_ex_filter v4 v2 v5)
                end)
                    val  dec_deg =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( degrees, v2)
                    in
                      Array.update ( degrees, v2, (let val  k = v1 - 1
                     in
                      if  (k < 0)
                    then  0
                     else  k
                     end))
                    end)
                    val  dec_degree =
                  (fn  v3 =>
                    let val  v2 = !( dim)
                    in
                      if  (v3 < v2)
                    then  (let val  v1 = Array.sub ( adj_ls, v3)
                    in
                      st_ex_foreach v1 dec_deg
                     end)
                    else  ()
                    end)
                    val  add_simp_wl =
                  (fn  v2 =>
                    let val  v1 = !( simp_wl)
                    in
                      simp_wl := (v2 @ v1)
                    end)
                    val  add_spill_wl =
                  (fn  v2 =>
                    let val  v1 = !( spill_wl)
                    in
                      spill_wl := (v2 @ v1)
                    end)
                    val  add_freeze_wl =
                  (fn  v2 =>
                    let val  v1 = !( freeze_wl)
                    in
                      freeze_wl := (v2 @ v1)
                    end)
                    val  push_stack =
                  (fn  v4 =>
                    let val  v3 = !( stack)
                        val  v2 = Array.update ( degrees, v4, 0)
                        val  v1 = Array.update ( move_related, v4, (0 < 0))
                    in
                      stack := (v4::v3)
                    end)
                    val  add_unavail_moves_wl =
                  (fn  v2 =>
                    let val  v1 = !( unavail_moves_wl)
                    in
                      unavail_moves_wl := (v2 @ v1)
                    end)
                    val  is_not_coalesced =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( coalesced, v2)
                    in
                      v1 = NONE
                     end)
                    val  split_degree =
                  (fn  v3 =>
                    (fn  v4 =>
                      (fn  v5 =>
                        if  (v5 < v3)
                        then  (let val  v2 = Array.sub ( degrees, v5)
                            val  v1 = is_not_coalesced v5
                         in
                          (v2 < v4) andalso  v1
                         end)
                        else  (0 <= 0))))
                    val  revive_moves =
                  (fn  v16 =>
                    let val  v15 =
                      st_ex_map (fn  v1 => (Array.sub ( adj_ls, v1))) v16
                        val  v14 = !( unavail_moves_wl)
                        val  v13 = !( avail_moves_wl)
                        val  v12 = List.concat v15
                        val  v6 =
                      partition (fn  v11 =>
                        (case  v11
                        of  (v10,v9) =>  (case  v9
                        of  (v8,v7) =>  ((member v8 v12) orelse  (member v7 v12))))) v14
                     in
                      case  v6
                    of  (v5,v4) =>  (let val  v3 = smerge (sort_moves v5) v13
                        val  v2 = avail_moves_wl := v3
                     in
                      unavail_moves_wl := v4
                     end)
                    end)
                    val  unspill =
                  (fn  v13 =>
                    let val  v12 = !( dim)
                        val  v11 = !( spill_wl)
                        val  v10 =
                      st_ex_partition (split_degree v12 v13) v11 [] []
                     in
                      case  v10
                    of  (v9,v8) =>  (let val  v7 = revive_moves v9
                        val  v6 =
                      st_ex_partition (fn  v1 =>
                        (Array.sub ( move_related, v1))) v9 [] []
                     in
                      case  v6
                    of  (v5,v4) =>  (let val  v3 = spill_wl := v8
                        val  v2 = add_simp_wl v4
                     in
                      add_freeze_wl v5
                     end)
                    end)
                    end)
                    val  do_simplify =
                  (fn  v6 =>
                    let val  v5 = !( simp_wl)
                    in
                      if  (List.null v5)
                    then  (0 < 0)
                    else  (let val  v4 = st_ex_foreach v5 dec_degree
                        val  v3 = st_ex_foreach v5 push_stack
                        val  v2 = simp_wl := []
                         val  v1 = unspill v6
                     in
                      0 <= 0
                     end)
                    end)
                    val  inc_deg =
                  (fn  v3 =>
                    (fn  v2 =>
                      let val  v1 = Array.sub ( degrees, v3)
                      in
                        Array.update ( degrees, v3, (v1 + v2))
                      end))
                    val  insert_edge =
                  (fn  v4 =>
                    (fn  v5 =>
                      let val  v3 = Array.sub ( adj_ls, v4)
                          val  v2 = Array.sub ( adj_ls, v5)
                      in
                        if  (member v5 v3)
                      then  ()
                      else  (let val  v1 = Array.update ( adj_ls, v4, (v5::v3))
                      in
                        Array.update ( adj_ls, v5, (v4::v2))
                      end)
                      end))
                    fun  list_insert_edge v5 v4 =
                case  v4
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = insert_edge v5 v3
                 in
                  list_insert_edge v5 v2
                 end)
                    val  is_fixed =
                  (fn  v3 =>
                    let val  v2 = Array.sub ( node_tag, v3)
                    in
                      case  v2
                    of  Fixed(v1) =>  (0 <= 0)
                    |   Atemp =>  (0 < 0)
                    |   Stemp =>  (0 < 0)
                    end)
                    val  do_coalesce_real =
                  (fn  v12 =>
                    (fn  v13 =>
                      (fn  v10 =>
                        (fn  v11 =>
                          let val  v9 =
                            Array.update ( coalesced, v13, (SOME(v12)))
                              val  v8 = !( avail_moves_wl)
                              val  v7 =
                            avail_moves_wl := (List.map (pair_rename v12 v13) v8)
                              val  v6 = !( unavail_moves_wl)
                              val  v5 =
                            unavail_moves_wl := (List.map (pair_rename v12 v13) v6)
                              val  v4 = is_fixed v12
                              val  v3 =
                            if  v4
                             then  (inc_deg v12 (List.length v11))
                            else  ()
                              val  v2 = list_insert_edge v12 v11
                              val  v1 = st_ex_foreach v10 dec_deg
                           in
                            push_stack v13
                           end))))
                    val  is_atemp =
                  (fn  v2 =>
                    let val  v1 = Array.sub ( node_tag, v2)
                    in
                      v1 = Atemp
                     end)
                    val  is_fixed_k =
                  (fn  v3 =>
                    (fn  v4 =>
                      let val  v2 = Array.sub ( node_tag, v4)
                      in
                        case  v2
                      of  Fixed(v1) =>  (v1 < v3)
                      |   Atemp =>  (0 < 0)
                      |   Stemp =>  (0 < 0)
                      end))
                    val  deg_or_inf =
                  (fn  v2 =>
                    (fn  v3 =>
                      let val  v1 = is_fixed_k v2 v3
                       in
                        if  v1
                       then  v2
                       else  (Array.sub ( degrees, v3))
                      end))
                    val  considered_var =
                  (fn  v3 =>
                    (fn  v4 =>
                      let val  v2 = is_atemp v4
                          val  v1 = is_fixed_k v3 v4
                       in
                        v2 orelse  v1
                       end))
                    val  bg_ok =
                  (fn  v27 =>
                    (fn  v28 =>
                      (fn  v29 =>
                        let val  v26 = Array.sub ( adj_ls, v28)
                            val  v25 = Array.sub ( adj_ls, v29)
                            val  v23 =
                          partition (fn  v24 => (member v24 v26)) v25
                         in
                          case  v23
                        of  (v22,v21) =>  (let val  v20 =
                          st_ex_filter (fn  v1 => (considered_var v27 v1)) v22 []
                             val  v19 =
                          st_ex_filter (fn  v2 => (considered_var v27 v2)) v21 []
                             val  v18 =
                          st_ex_map (fn  v3 => (deg_or_inf v27 v3)) v19
                            val  v16 =
                          List.length (List.filter (fn  v17 => (v17 >= v27)) v18)
                        in
                          if  (v16 = 0)
                        then  (let val  x = (v20,v19)
                        in
                          SOME(x)
                        end)
                        else  (let val  v14 =
                          List.filter (fn  v15 =>
                            ((member v15 v25) = (0 < 0))) v26
                            val  v13 =
                          st_ex_filter (fn  v4 => (considered_var v27 v4)) v14 []
                             val  v12 =
                          st_ex_map (fn  v5 => (deg_or_inf (v27 + 1) v5)) v20
                            val  v11 =
                          st_ex_map (fn  v6 => (deg_or_inf v27 v6)) v13
                            val  v10 =
                          List.length (List.filter (fn  v7 =>
                            ((let val  k = v7 - 1
                             in
                              if  (k < 0)
                            then  0
                             else  k
                             end) >= v27)) v12)
                            val  v9 =
                          List.length (List.filter (fn  v8 => (v8 >= v27)) v11)
                        in
                          if  (((v10 + v16) + v9) < v27)
                        then  (let val  x = (v20,v19)
                        in
                          SOME(x)
                        end)
                        else  NONE
                         end)
                        end)
                        end)))
                    val  consistency_ok =
                  (fn  v7 =>
                    (fn  v8 =>
                      if  (v7 = v8)
                      then  (0 < 0)
                      else  (let val  v6 = !( dim)
                      in
                        if  ((v7 >= v6) orelse  (v8 >= v6))
                      then  (0 < 0)
                      else  (let val  v5 = Array.sub ( adj_ls, v8)
                      in
                        if  (member v7 v5)
                      then  (0 < 0)
                      else  (let val  v4 = is_fixed v7
                          val  v3 = is_fixed v8
                          val  v2 = Array.sub ( move_related, v7)
                          val  v1 = Array.sub ( move_related, v8)
                      in
                        (v4 orelse  v2) andalso  ((v3 orelse  v1) andalso  ((v4 = (0 < 0)) orelse  (v3 = (0 < 0))))
                      end)
                      end)
                      end)))
                    val  canonize_move =
                  (fn  v2 =>
                    (fn  v3 =>
                      let val  v1 = is_fixed v3
                       in
                        if  v1
                       then  (v3,v2)
                      else  (v2,v3)
                      end))
                    fun  st_ex_first v14 v15 v16 v17 =
                case  v16
                of  []  =>  (NONE,v17)
                |   v13::v12 =>  (let val  v11 = v13
                 in
                  case  v11
                of  (v10,v9) =>  (case  v9
                of  (v8,v7) =>  (let val  v6 = v14 v8 v7
                 in
                  if  (v6 = (0 < 0))
                then  (st_ex_first v14 v15 v12 v17)
                else  (let val  v5 = canonize_move v8 v7
                 in
                  case  v5
                of  (v4,v3) =>  (let val  v2 = v15 v4 v3
                 in
                  case  v2
                of  NONE =>  (st_ex_first v14 v15 v12 (v13::v17))
                |   SOME(v1) =>  (let val  x = ((v4,v3),(v1,v12))
                in
                  SOME(x)
                end,v17)
                end)
                end)
                end))
                end)
                    val  respill =
                  (fn  v5 =>
                    (fn  v6 =>
                      let val  v4 = Array.sub ( degrees, v6)
                      in
                        if  (v4 < v5)
                      then  ()
                      else  (let val  v3 = !( freeze_wl)
                      in
                        if  (member v6 v3)
                      then  (let val  v2 = add_spill_wl [v6]
                      in
                        freeze_wl := (List.filter (fn  v1 =>
                        ((v1 = v6) = (0 < 0))) v3)
                      end)
                      else  ()
                      end)
                      end))
                    val  do_coalesce =
                  (fn  v20 =>
                    let val  v19 = !( avail_moves_wl)
                        val  v18 =
                      st_ex_first consistency_ok (bg_ok v20) v19 []
                     in
                      case  v18
                    of  (v17,v16) =>  (let val  v15 = add_unavail_moves_wl v16
                     in
                      case  v17
                    of  NONE =>  (let val  v1 = avail_moves_wl := []
                     in
                      0 < 0
                     end)
                    |   SOME(v14) =>  (case  v14
                    of  (v13,v12) =>  (case  v13
                    of  (v11,v10) =>  (case  v12
                    of  (v9,v8) =>  (case  v9
                    of  (v7,v6) =>  (let val  v5 = avail_moves_wl := v8
                        val  v4 = do_coalesce_real v11 v10 v7 v6
                        val  v3 = unspill v20
                        val  v2 = respill v20 v11
                     in
                      0 <= 0
                     end)))))
                    end)
                    end)
                    val  reset_move_related =
                  (fn  v12 =>
                    let val  v11 = !( dim)
                        val  v10 =
                      st_ex_foreach (count_list v11) (fn  v1 =>
                        (Array.update ( move_related, v1, (0 < 0))))
                    in
                      st_ex_foreach v12 (fn  v9 =>
                      (case  v9
                      of  (v8,v7) =>  (case  v7
                      of  (v6,v5) =>  (let val  v4 = is_fixed v6
                          val  v3 = is_fixed v5
                          val  v2 =
                        Array.update ( move_related, v6, (v4 = (0 < 0)))
                      in
                        Array.update ( move_related, v5, (v3 = (0 < 0)))
                      end))))
                    end)
                    val  do_prefreeze =
                  (fn  v21 =>
                    let val  v20 = !( freeze_wl)
                        val  v19 = st_ex_filter is_not_coalesced v20 []
                         val  v18 = !( spill_wl)
                        val  v17 = st_ex_filter is_not_coalesced v18 []
                         val  v16 = spill_wl := v17
                        val  v15 = !( unavail_moves_wl)
                        val  v14 =
                      st_ex_filter (fn  v5 =>
                        (case  v5
                        of  (v4,v3) =>  (case  v3
                        of  (v2,v1) =>  (consistency_ok v2 v1)))) v15 []
                         val  v13 = reset_move_related v14
                        val  v12 = unavail_moves_wl := v14
                        val  v11 =
                      st_ex_partition (fn  v6 =>
                        (Array.sub ( move_related, v6))) v19 [] []
                     in
                      case  v11
                    of  (v10,v9) =>  (let val  v8 = add_simp_wl v9
                        val  v7 = freeze_wl := v10
                     in
                      do_simplify v21
                     end)
                    end)
                    val  do_freeze =
                  (fn  v8 =>
                    let val  v7 = !( freeze_wl)
                    in
                      if  (List.null v7)
                    then  (0 < 0)
                    else  (case  v7
                    of  []  =>  (0 < 0)
                    |   (v6::v5) =>  (let val  v4 = dec_degree v6
                        val  v3 = push_stack v6
                        val  v2 = freeze_wl := v5
                        val  v1 = unspill v8
                     in
                      0 <= 0
                     end))
                    end)
                    fun  st_ex_list_min_cost v10 v9 v7 v8 v5 v6 =
                case  v9
                of  []  =>  (v8,v6)
                |   v4::v3 =>  (if  (v4 < v7)
                then  (let val  v2 = Array.sub ( degrees, v4)
                    val  v1 = safe_div (lookup_any v4 v10 0) v2
                 in
                  if  (v5 > v1)
                then  (st_ex_list_min_cost v10 v3 v7 v4 v1 (v8::v6))
                else  (st_ex_list_min_cost v10 v3 v7 v8 v5 (v4::v6))
                end)
                else  (st_ex_list_min_cost v10 v3 v7 v8 v5 v6))
                    fun  st_ex_list_max_deg v7 v5 v6 v8 v4 =
                case  v7
                of  []  =>  (v6,v4)
                |   v3::v2 =>  (if  (v3 < v5)
                then  (let val  v1 = Array.sub ( degrees, v3)
                in
                  if  (v8 < v1)
                then  (st_ex_list_max_deg v2 v5 v3 v1 (v6::v4))
                else  (st_ex_list_max_deg v2 v5 v6 v8 (v3::v4))
                end)
                else  (st_ex_list_max_deg v2 v5 v6 v8 v4))
                    val  do_spill =
                  (fn  v15 =>
                    (fn  v14 =>
                      let val  v13 = !( spill_wl)
                          val  v12 = !( dim)
                      in
                        case  v13
                      of  []  =>  (0 < 0)
                      |   v11::v10 =>  (let val  v9 = Array.sub ( degrees, v11)
                          val  v8 =
                        case  v15
                        of  NONE =>  (st_ex_list_max_deg v10 v12 v11 v9 [] )
                        |   SOME(v1) =>  (st_ex_list_min_cost v1 v10 v12 v11 (safe_div (lookup_any v11 v1 0) v9) [] )
                      in
                        case  v8
                      of  (v7,v6) =>  (let val  v5 = dec_deg v7
                          val  v4 = push_stack v7
                          val  v3 = spill_wl := v6
                          val  v2 = unspill v14
                       in
                        0 <= 0
                       end)
                      end)
                      end))
                    val  do_step =
                  (fn  v7 =>
                    (fn  v6 =>
                      let val  v5 = do_simplify v6
                       in
                        if  v5
                       then  (0 <= 0)
                      else  (let val  v4 = do_coalesce v6
                       in
                        if  v4
                       then  (0 <= 0)
                      else  (let val  v3 = do_prefreeze v6
                       in
                        if  v3
                       then  (0 <= 0)
                      else  (let val  v2 = do_freeze v6
                       in
                        if  v2
                       then  (0 <= 0)
                      else  (let val  v1 = do_spill v7 v6
                       in
                        v1
                       end)
                      end)
                      end)
                      end)
                      end))
                    fun  rpt_do_step v4 v2 v3 =
                if  (v3 = 0)
                then  ()
                else  (let val  v1 = do_step v4 v2
                 in
                  if  v1
                 then  (rpt_do_step v4 v2 (let val  k = v3 - 1
                 in
                  if  (k < 0)
                then  0
                 else  k
                 end))
                else  ()
                end)
                    fun  remove_colours v10 v9 =
                case  v9
                of  []  =>  []
                 |   v8::v7 =>  (case  v10
                of  []  =>  (v8::v7)
                |   (v6::v5) =>  (let val  v4 = Array.sub ( node_tag, v6)
                    val  v3 =
                  case  v4
                  of  Fixed(v2) =>  (remove_colours v5 (List.filter (fn  v1 =>
                    ((v1 = v2) = (0 < 0))) (v8::v7)))
                  |   Atemp =>  (remove_colours v5 (v8::v7))
                  |   Stemp =>  (remove_colours v5 (v8::v7))
                in
                  v3
                 end))
                    val  assign_atemp_tag =
                  (fn  v11 =>
                    (fn  v10 =>
                      (fn  v9 =>
                        let val  v8 = Array.sub ( node_tag, v9)
                        in
                          case  v8
                        of  Fixed(v1) =>  ()
                        |   Atemp =>  (let val  v7 = Array.sub ( adj_ls, v9)
                            val  v6 = remove_colours v7 v11
                         in
                          case  v6
                        of  []  =>  (Array.update ( node_tag, v9, Stemp))
                        |   v5::v4 =>  (let val  v3 = v10 v9 v6
                         in
                          case  v3
                        of  NONE =>  (Array.update ( node_tag, v9, (Fixed(v5))))
                        |   SOME(v2) =>  (Array.update ( node_tag, v9, (Fixed(v2))))
                        end)
                        end)
                        |   Stemp =>  ()
                        end)))
                    val  assign_atemps =
                  (fn  v11 =>
                    (fn  v9 =>
                      (fn  v10 =>
                        let val  v8 = !( dim)
                            val  v7 = List.filter (fn  v1 => (v1 < v8)) v9
                            val  v6 = genlist (fn  v2 => v2) v11
                            val  v5 = genlist (fn  v3 => v3) v8
                            val  v4 =
                          st_ex_foreach v7 (assign_atemp_tag v6 v10)
                        in
                          st_ex_foreach v5 (assign_atemp_tag v6 v10)
                        end)))
                    val  assign_stemp_tag =
                  (fn  v10 =>
                    (fn  v9 =>
                      let val  v8 = Array.sub ( node_tag, v9)
                      in
                        case  v8
                      of  Fixed(v1) =>  ()
                      |   Atemp =>  ()
                      |   Stemp =>  (let val  v7 = Array.sub ( adj_ls, v9)
                          val  v6 =
                        st_ex_map (fn  v2 => (Array.sub ( node_tag, v2))) v7
                          val  v5 =
                        unbound_colour v10 (qsort (fn  v4 =>
                          (fn  v3 => (v4 <= v3))) (List.map tag_col v6))
                      in
                        Array.update ( node_tag, v9, (Fixed(v5)))
                      end)
                      end))
                    val  assign_stemps =
                  (fn  v4 =>
                    let val  v3 = !( dim)
                        val  v2 = genlist (fn  v1 => v1) v3
                     in
                      st_ex_foreach v2 (assign_stemp_tag v4)
                    end)
                    fun  first_match_col v5 v6 =
                case  v6
                of  []  =>  NONE
                |   v4::v3 =>  (let val  v2 = Array.sub ( node_tag, v4)
                in
                  case  v2
                of  Fixed(v1) =>  (if  (member v1 v5)
                then  (SOME(v1))
                else  (first_match_col v5 v3))
                |   Atemp =>  (first_match_col v5 v3)
                |   Stemp =>  (first_match_col v5 v3)
                end)
                    val  biased_pref =
                  (fn  v7 =>
                    (fn  v8 =>
                      (fn  v6 =>
                        let val  v5 = !( dim)
                        in
                          if  (v8 < v5)
                        then  (let val  v4 = Array.sub ( coalesced, v8)
                            val  v2 =
                          case  (lookup_1 v8 v7)
                          of  NONE =>  []
                           |   SOME(v3) =>  v3
                         in
                          case  v4
                        of  NONE =>  ((first_match_col v6 v2)
                        handle  Subscript =>  NONE)
                        |   SOME(v1) =>  ((first_match_col v6 (v1::v2))
                        handle  Subscript =>  NONE)
                        end)
                        else  NONE
                         end)))
                    fun  clique_insert_edge v4 =
                case  v4
                of  []  =>  ()
                |   v3::v2 =>  (let val  v1 = list_insert_edge v3 v2
                 in
                  clique_insert_edge v2
                 end)
                    fun  extend_clique v5 v4 =
                case  v5
                of  []  =>  v4
                |   v3::v2 =>  (if  (member v3 v4)
                then  (extend_clique v2 v4)
                else  (let val  v1 = list_insert_edge v3 v4
                 in
                  extend_clique v2 (v3::v4)
                end))
                    fun  mk_graph v26 v25 v24 =
                case  v25
                of  Delta(v8,v7) =>  (let val  v6 = List.map v26 v8
                    val  v5 = List.map v26 v7
                    val  v4 = extend_clique v6 v24
                    val  v3 =
                  List.filter (fn  v1 => ((member v1 v6) = (0 < 0))) v4
                    val  v2 = extend_clique v5 v3
                 in
                  v2
                 end)
                |   Set(v11) =>  (let val  v10 =
                  List.map v26 (List.map fst (toalist v11))
                    val  v9 = clique_insert_edge v10
                 in
                  v10
                 end)
                |   Branch(v20,v19,v18) =>  (let val  v17 =
                  mk_graph v26 v19 v24
                    val  v16 = mk_graph v26 v18 v24
                 in
                  case  v20
                of  NONE =>  (let val  v12 = extend_clique v17 v16
                 in
                  v12
                 end)
                |   SOME(v15) =>  (let val  v14 =
                  List.map v26 (List.map fst (toalist v15))
                    val  v13 = clique_insert_edge v14
                 in
                  v14
                 end)
                end)
                |   Seq(v23,v22) =>  (let val  v21 = mk_graph v26 v22 v24
                 in
                  mk_graph v26 v23 v21
                 end)
                    fun  extend_graph v6 v7 =
                case  v7
                of  []  =>  ()
                |   v5::v4 =>  (case  v5
                of  (v3,v2) =>  (let val  v1 = insert_edge (v6 v3) (v6 v2)
                in
                  extend_graph v6 v4
                 end))
                    val  mk_tags =
                  (fn  v7 =>
                    (fn  v6 =>
                      let val  v5 = genlist (fn  v1 => v1) v7
                       in
                        st_ex_foreach v5 (fn  v4 =>
                        (let val  v3 = v6 v4
                            val  v2 = v3 mod 4
                         in
                          if  (v2 = 1)
                        then  (Array.update ( node_tag, v4, Atemp))
                        else  (if  (v2 = 3)
                        then  (Array.update ( node_tag, v4, Stemp))
                        else  (Array.update ( node_tag, v4, (Fixed(v3 div 2)))))
                        end))
                      end))
                    val  init_ra_state =
                  (fn  v11 =>
                    (fn  v9 =>
                      (fn  v10 =>
                        case  (v9,v10)
                        of  (v8,v7) =>  (case  v7
                        of  (v6,v5) =>  (case  v5
                        of  (v4,v3) =>  (let val  v2 =
                          mk_graph (sp_default v6) v11 []
                             val  v1 = extend_graph (sp_default v6) v8
                         in
                          mk_tags v3 (sp_default v4)
                        end))))))
                    val  init_alloc1_heu =
                  (fn  v22 =>
                    (fn  v20 =>
                      (fn  v21 =>
                        let val  v19 = count_list v20
                            val  v18 = st_ex_filter is_atemp v19 []
                             val  v17 =
                          st_ex_foreach v19 (fn  v4 =>
                            (let val  v3 = Array.sub ( adj_ls, v4)
                                val  v2 =
                              st_ex_filter (fn  v1 => (considered_var v21 v1)) v3 []
                             in
                              Array.update ( degrees, v4, (List.length v2))
                            end))
                            val  v16 = avail_moves_wl := (sort_moves v22)
                            val  v15 = reset_move_related v22
                            val  v14 =
                          st_ex_partition (split_degree v20 v21) v18 [] []
                         in
                          case  v14
                        of  (v13,v12) =>  (let val  v11 =
                          st_ex_partition (fn  v5 =>
                            (Array.sub ( move_related, v5))) v13 [] []
                         in
                          case  v11
                        of  (v10,v9) =>  (let val  v8 = spill_wl := v12
                            val  v7 = simp_wl := v9
                            val  v6 = freeze_wl := v10
                         in
                          List.length v18
                         end)
                        end)
                        end)))
                    val  do_alloc1 =
                  (fn  v6 =>
                    (fn  v7 =>
                      (fn  v5 =>
                        let val  v4 = !( dim)
                            val  v3 = init_alloc1_heu v6 v4 v5
                            val  v2 = rpt_do_step v7 v5 v3
                            val  v1 = !( stack)
                        in
                          v1
                         end)))
                    val  extract_color =
                  (fn  v7 =>
                    let val  v6 = toalist v7
                        val  v5 =
                      st_ex_map (fn  v4 =>
                        (case  v4
                        of  (v3,v2) =>  (let val  v1 =
                          Array.sub ( node_tag, v2)
                        in
                          (v3,extract_tag v1)
                        end))) v6
                     in
                      fromalist v5
                     end)
                    val  full_consistency_ok =
                  (fn  v7 =>
                    (fn  v8 =>
                      (fn  v9 =>
                        if  (v8 = v9)
                        then  (0 < 0)
                        else  (let val  v6 = !( dim)
                        in
                          if  ((v8 >= v6) orelse  (v9 >= v6))
                        then  (0 < 0)
                        else  (let val  v5 = Array.sub ( adj_ls, v9)
                        in
                          if  (member v8 v5)
                        then  (0 < 0)
                        else  (let val  v4 = is_fixed_k v7 v8
                            val  v3 = is_fixed_k v7 v9
                            val  v2 = is_atemp v8
                            val  v1 = is_atemp v9
                         in
                          (v4 orelse  v2) andalso  ((v3 orelse  v1) andalso  ((v4 = (0 < 0)) orelse  (v3 = (0 < 0))))
                        end)
                        end)
                        end))))
                    fun apply_col col ls = filter (fn (p,(x,y)) => (col x = col y)) ls
                    val  do_reg_alloc =
                  (fn  v32 =>
                    (fn  v33 =>
                      (fn  v34 =>
                        (fn  v35 =>
                          (fn  v36 =>
                            (fn  v37 =>
                              (fn  v38 =>
                                case  (v33,(v34,(v35,(v36,(v37,v38)))))
                                of  (v31,v30) =>  (case  v30
                                of  (v29,v28) =>  (case  v28
                                of  (v27,v26) =>  (case  v26
                                of  (v25,v24) =>  (case  v24
                                of  (v23,v22) =>  (case  v22
                                of  (v21,v20) =>  (case  v20
                                of  (v19,v18) =>  (let val  v17 =
                                  init_ra_state v25 v23 (v21,(v19,v18))
                                    val  v16 =
                                  List.map (fn  v5 =>
                                    (case  v5
                                    of  (v4,v3) =>  (case  v3
                                    of  (v2,v1) =>  (v4,(sp_default v21 v2,sp_default v21 v1))))) v27
                                    val  v15 =
                                  st_ex_filter (fn  v10 =>
                                    (case  v10
                                    of  (v9,v8) =>  (case  v8
                                    of  (v7,v6) =>  (full_consistency_ok v29 v7 v6)))) v16 []
                                     val  v14 =
                                  do_alloc1 (if  (v32 = Simple)
                                  then  []
                                   else  v15) v31 v29
                                    val  v13 =
                                  assign_atemps v29 v14 (biased_pref (resort_moves (moves_to_sp v15 Ln)))
                                    val  v12 = assign_stemps v29
                                    val  v11 = extract_color v21
                                    val  cols = apply_col (fn x => lookup_1 x v11) v35
                                    val _ = print ("moves: "^Int.toString (length v35)^"\tcoalesceable: "^Int.toString (length v15) ^"\tcoalesced: "^Int.toString (length cols)^"\n")
                                 in
                                  v11
                                 end))))))))))))))
                in
                  (Success(do_reg_alloc alg sc v5 v4 v3 v2 v1))
                handle  e =>  Failure(e)
                end))))));
  fun  reg_alloc v1 =
    (fn  v6 =>
      (fn  v4 =>
        (fn  v5 =>
          (fn  v2 => (fn  v3 => reg_alloc_aux v1 v6 v4 v5 v2 v3 (mk_bij v2))))));
  fun  the v3 =
    (fn  v2 =>
      case  v2
      of  NONE =>  v3
      |   SOME(v1) =>  v1);
  fun  numset_list_delete v3 v4 =
  case  v3
  of  []  =>  v4
  |   v2::v1 =>  (numset_list_delete v1 (delete_1 v2 v4));
  fun  is_stack_var v1 =  (v1 mod 4) = 3;
  fun  is_phy_var_1 v1 =  (v1 mod 2) = 0;
  fun  lex v7 =
    (fn  v8 =>
      (fn  v6 =>
        case  v6
        of  (v5,v4) =>  (fn  v3 =>
          (case  v3
          of  (v2,v1) =>  ((v7 v5 v2) orelse  ((v5 = v2) andalso  (v8 v4 v1)))))));
  datatype linear_scan_linear_scan_state =  Recordtypelinear_scan_state of  (int *  int) list *  int list *  unit sptree_spt *  int *  int *  int;
  fun  linear_scan_state_active v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v6;
  fun  linear_scan_state_colorpool v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v5;
  fun  linear_scan_state_phyregs v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v4;
  fun  linear_scan_state_colornum v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v3;
  fun  linear_scan_state_colormax v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v2;
  fun  linear_scan_state_stacknum v7 =
    case  v7 of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  v1;
  fun  linear_scan_state_active_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v7 v6,v5,v4,v3,v2,v1)));
  fun  linear_scan_state_colorpool_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v6,v7 v5,v4,v3,v2,v1)));
  fun  linear_scan_state_phyregs_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v6,v5,v7 v4,v3,v2,v1)));
  fun  linear_scan_state_colornum_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v6,v5,v4,v7 v3,v2,v1)));
  fun  linear_scan_state_colormax_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v6,v5,v4,v3,v7 v2,v1)));
  fun  linear_scan_state_stacknum_fupd v7 =
    (fn  v8 =>
      case  v8
      of  Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v1) =>  (Recordtypelinear_scan_state(v6,v5,v4,v3,v2,v7 v1)));
  fun  linear_reg_alloc_pass1_initial_state v1 =
    Recordtypelinear_scan_state([] ,[] ,Ln,0,v1,v1);
  fun  linear_reg_alloc_pass2_initial_state v1 =
    (fn  v2 => Recordtypelinear_scan_state([] ,[] ,Ln,v1,v1 + v2,v1 + v2));
  fun  add_active_interval v4 v3 =
  case  v3
  of  []  =>  [v4]
  |   v2::v1 =>  (if  ((fst v4) <= (fst v2))
  then  (v4::v2::v1)
  else  (v2::(add_active_interval v4 v1)));
  fun  find_color_in_list v7 v6 =
  case  v7
  of  []  =>  NONE
  |   v5::v4 =>  (if  ((lookup_1 v5 v6) = NONE)
  then  (let val  x = (v5,v4)
  in
    SOME(x)
  end)
  else  (case  (find_color_in_list v4 v6)
  of  NONE =>  NONE
  |   (SOME(v3)) =>  (case  v3
  of  (v2,v1) =>  (let val  x = (v2,v5::v1)
  in
    SOME(x)
  end))));
  fun  find_color_in_colornum v3 =
    (fn  v2 =>
      if  ((linear_scan_state_colormax v3) <= (linear_scan_state_colornum v3))
      then  (v3,NONE)
      else  (linear_scan_state_colornum_fupd (fn  v1 => (1 + v1)) v3,SOME(linear_scan_state_colornum v3)));
  fun  find_color v5 =
    (fn  v4 =>
      case  (find_color_in_list (linear_scan_state_colorpool v5) v4)
      of  NONE =>  (find_color_in_colornum v5 v4)
      |   SOME(v3) =>  (case  v3
      of  (v2,v1) =>  (linear_scan_state_colorpool_fupd (k v1) v5,SOME(v2))));
  fun  edges_to_adjlist_impl v7 v9 v8 =
  case  v7
  of  []  =>  v8
  |   v6::v5 =>  (case  v6
  of  (v4,v3) =>  (if  (v4 = v3)
  then  (edges_to_adjlist_impl v5 v9 v8)
  else  (let val  v2 = the 0 (lookup_1 v4 v9)
      val  v1 = the 0 (lookup_1 v3 v9)
  in
    if  ((v2 < v1) orelse  ((v2 = v1) andalso  (v4 <= v3)))
  then  (edges_to_adjlist_impl v5 v9 (insert_1 v3 (v4::(the [] (lookup_1 v3 v8))) v8))
  else  (edges_to_adjlist_impl v5 v9 (insert_1 v4 (v3::(the [] (lookup_1 v4 v8))) v8))
  end)));
  fun  sort_moves_rev v7 =
    qsort (fn  v6 =>
      (case  v6
      of  (v5,v4) =>  (fn  v3 => (case  v3 of  (v2,v1) =>  (v5 < v2))))) v7;
  datatype linear_scan_bijection_state =  Recordtypebijection_state of  int sptree_spt *  int sptree_spt *  int *  int *  int;
  fun  bijection_state_bij v6 =
    case  v6 of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  v5;
  fun  bijection_state_invbij v6 =
    case  v6 of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  v4;
  fun  bijection_state_nmax v6 =
    case  v6 of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  v3;
  fun  bijection_state_nstack v6 =
    case  v6 of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  v2;
  fun  bijection_state_nalloc v6 =
    case  v6 of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  v1;
  fun  bijection_state_bij_fupd v6 =
    (fn  v7 =>
      case  v7
      of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  (Recordtypebijection_state(v6 v5,v4,v3,v2,v1)));
  fun  bijection_state_invbij_fupd v6 =
    (fn  v7 =>
      case  v7
      of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  (Recordtypebijection_state(v5,v6 v4,v3,v2,v1)));
  fun  bijection_state_nmax_fupd v6 =
    (fn  v7 =>
      case  v7
      of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  (Recordtypebijection_state(v5,v4,v6 v3,v2,v1)));
  fun  bijection_state_nstack_fupd v6 =
    (fn  v7 =>
      case  v7
      of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  (Recordtypebijection_state(v5,v4,v3,v6 v2,v1)));
  fun  bijection_state_nalloc_fupd v6 =
    (fn  v7 =>
      case  v7
      of  Recordtypebijection_state(v5,v4,v3,v2,v1) =>  (Recordtypebijection_state(v5,v4,v3,v2,v6 v1)));
  val  find_bijection_init = Recordtypebijection_state(Ln,Ln,0,3,1);
  fun  find_bijection_step v2 =
    (fn  v1 =>
      if  (is_phy_var_1 v1)
      then  (bijection_state_bij_fupd (k (insert_1 v1 v1 (bijection_state_bij v2))) (bijection_state_invbij_fupd (k (insert_1 v1 v1 (bijection_state_invbij v2))) (bijection_state_nmax_fupd (k (max v1 (bijection_state_nmax v2))) v2)))
      else  (if  (is_stack_var v1)
      then  (bijection_state_bij_fupd (k (insert_1 v1 (bijection_state_nstack v2) (bijection_state_bij v2))) (bijection_state_invbij_fupd (k (insert_1 (bijection_state_nstack v2) v1 (bijection_state_invbij v2))) (bijection_state_nmax_fupd (k (max (bijection_state_nstack v2) (bijection_state_nmax v2))) (bijection_state_nstack_fupd (k ((bijection_state_nstack v2) + 4)) v2))))
      else  (bijection_state_bij_fupd (k (insert_1 v1 (bijection_state_nalloc v2) (bijection_state_bij v2))) (bijection_state_invbij_fupd (k (insert_1 (bijection_state_nalloc v2) v1 (bijection_state_invbij v2))) (bijection_state_nmax_fupd (k (max (bijection_state_nalloc v2) (bijection_state_nmax v2))) (bijection_state_nalloc_fupd (k ((bijection_state_nalloc v2) + 4)) v2))))));
  fun  apply_bijection v4 =
    (fn  v5 =>
      foldi (fn  v3 =>
        (fn  v2 => (fn  v1 => (insert_1 (the 0 (lookup_1 v3 v4)) v2 v1)))) 0 Ln v5);
  datatype linear_scan_i_linear_scan_hidden_state =  Recordtypei_linear_scan_hidden_state of  (int *  int);
  fun  i_linear_scan_hidden_state_colors v2 =
    case  v2 of  Recordtypei_linear_scan_hidden_state(v1) =>  v1;
  fun  i_linear_scan_hidden_state_colors_fupd v2 =
    (fn  v3 =>
      case  v3
      of  Recordtypei_linear_scan_hidden_state(v1) =>  (Recordtypei_linear_scan_hidden_state(v2 v1)));
  datatype linear_scan_linear_scan_hidden_state =  Recordtypelinear_scan_hidden_state of  int list;
  fun  linear_scan_hidden_state_colors v2 =
    case  v2 of  Recordtypelinear_scan_hidden_state(v1) =>  v1;
  fun  linear_scan_hidden_state_colors_fupd v2 =
    (fn  v3 =>
      case  v3
      of  Recordtypelinear_scan_hidden_state(v1) =>  (Recordtypelinear_scan_hidden_state(v2 v1)));
  fun  run_linear_reg_alloc_intervals v8 =
    (fn  v7 =>
      (fn  v6 =>
        (fn  v5 =>
          (fn  v4 =>
            (fn  v3 =>
              (fn  v2 =>
                (fn  v1 =>
                  let val  colors = Array.array ( (v1 + 1), 0)
                      val  spill_register =
                    (fn  v4 =>
                      (fn  v3 =>
                        let val  v2 =
                          Array.update ( colors, v3, (linear_scan_state_stacknum v4))
                        in
                          linear_scan_state_stacknum_fupd (fn  v1 => (1 + v1)) v4
                         end))
                      fun  map_colors v3 v4 =
                  if  (v4 = 0)
                  then  ()
                  else  (let val  v2 =
                    Array.sub ( colors, (let val  k = v4 - 1
                     in
                      if  (k < 0)
                    then  0
                     else  k
                     end))
                      val  v1 =
                    Array.update ( colors, (let val  k = v4 - 1
                     in
                      if  (k < 0)
                    then  0
                     else  k
                     end), (v3 v2))
                  in
                    map_colors v3 (let val  k = v4 - 1
                   in
                    if  (k < 0)
                  then  0
                   else  k
                   end)
                  end)
                      fun  st_ex_foldl v5 v4 v6 =
                  case  v6
                  of  []  =>  v4
                  |   v3::v2 =>  (let val  v1 = v5 v4 v3
                   in
                    st_ex_foldl v5 v1 v2
                   end)
                      fun  map_colors_sub v5 =
                  case  v5
                  of  []  =>  []
                   |   v4::v3 =>  (let val  v2 = Array.sub ( colors, v4)
                      val  v1 = map_colors_sub v3
                   in
                    v2::v1
                   end)
                      fun  remove_inactive_intervals v8 v9 =
                  case  (linear_scan_state_active v9)
                  of  []  =>  v9
                  |   v7::v6 =>  (case  v7
                  of  (v5,v4) =>  (if  (v5 < v8)
                  then  (let val  v3 = Array.sub ( colors, v4)
                      val  v1 =
                    linear_scan_state_active_fupd (k v6) (linear_scan_state_colorpool_fupd (fn  v2 =>
                      (v3::v2)) v9)
                  in
                    remove_inactive_intervals v8 v1
                   end)
                  else  v9))
                      val  color_register =
                    (fn  v5 =>
                      (fn  v3 =>
                        (fn  v2 =>
                          (fn  v4 =>
                            let val  v1 = Array.update ( colors, v3, v2)
                            in
                              if  (is_phy_var_1 v3)
                            then  (linear_scan_state_active_fupd (add_active_interval (v4,v3)) (linear_scan_state_phyregs_fupd (insert_1 v2 ()) v5))
                            else  (linear_scan_state_active_fupd (add_active_interval (v4,v3)) v5)
                            end))))
                      fun  find_last_stealable v9 v8 =
                  case  v9
                  of  []  =>  NONE
                  |   v7::v6 =>  (let val  v5 = find_last_stealable v6 v8
                   in
                    case  v5
                  of  NONE =>  (let val  v1 = Array.sub ( colors, (snd v7))
                  in
                    if  (((is_phy_var_1 (snd v7)) = (0 < 0)) andalso  ((lookup_1 v1 v8) = NONE))
                  then  (let val  x = (v7,v6)
                  in
                    SOME(x)
                  end)
                  else  NONE
                   end)
                  |   SOME(v4) =>  (case  v4
                  of  (v3,v2) =>  (let val  x = (v3,v7::v2)
                  in
                    SOME(x)
                  end))
                  end)
                      val  find_spill =
                    (fn  v12 =>
                      (fn  v13 =>
                        (fn  v10 =>
                          (fn  v11 =>
                            (fn  v9 =>
                              let val  v8 =
                                find_last_stealable (linear_scan_state_active v12) v13
                               in
                                case  v8
                              of  NONE =>  (spill_register v12 v10)
                              |   SOME(v7) =>  (case  v7
                              of  (v6,v5) =>  (case  v6
                              of  (v4,v3) =>  (if  (v9 orelse  (v11 < v4))
                              then  (let val  v2 = Array.sub ( colors, v3)
                                  val  v1 =
                                spill_register (linear_scan_state_active_fupd (k v5) v12) v3
                               in
                                color_register v1 v10 v2 v11
                               end)
                              else  (spill_register v12 v10))))
                              end)))))
                      val  linear_reg_alloc_step_aux =
                    (fn  v15 =>
                      (fn  v10 =>
                        (fn  v12 =>
                          (fn  v13 =>
                            (fn  v14 =>
                              (fn  v11 =>
                                let val  v8 =
                                  List.filter (fn  v9 =>
                                    (member v9 (linear_scan_state_colorpool v15))) v12
                                 in
                                  case  (find_color_in_list v8 v10)
                                of  NONE =>  (case  (find_color v15 v10)
                                of  (v3,v2) =>  (case  v2
                                of  NONE =>  (find_spill v3 v10 v13 v14 v11)
                                |   (SOME(v1)) =>  (color_register v3 v13 v1 v14)))
                                |   SOME(v7) =>  (case  v7
                                of  (v6,v5) =>  (color_register (linear_scan_state_colorpool_fupd (List.filter (fn  v4 =>
                                  ((v6 = v4) = (0 < 0)))) v15) v13 v6 v14))
                                end))))))
                      val  linear_reg_alloc_step_pass1 =
                    (fn  v9 =>
                      (fn  v10 =>
                        (fn  v14 =>
                          (fn  v11 =>
                            (fn  v13 =>
                              (fn  v12 =>
                                let val  v8 = the 0 (lookup_1 v12 v9)
                                    val  v7 = the 0 (lookup_1 v12 v10)
                                    val  v6 = remove_inactive_intervals v8 v13
                                 in
                                  if  (is_stack_var v12)
                                then  (spill_register v6 v12)
                                else  (let val  v5 =
                                  map_colors_sub (the [] (lookup_1 v12 v14))
                                    val  v3 =
                                  fromalist (List.map (fn  v4 => (v4,())) v5)
                                in
                                  if  (is_phy_var_1 v12)
                                then  (if  (v12 < (2 * (linear_scan_state_colormax v6)))
                                then  (let val  v1 =
                                  union_1 (linear_scan_state_phyregs v6) v3
                                 in
                                  linear_reg_alloc_step_aux v6 v1 [] v12 v7 (0 <= 0)
                                end)
                                else  (spill_register v6 v12))
                                else  (let val  v2 =
                                  map_colors_sub (the [] (lookup_1 v12 v11))
                                in
                                  linear_reg_alloc_step_aux v6 v3 v2 v12 v7 (0 < 0)
                                end)
                                end)
                                end))))))
                      val  linear_reg_alloc_step_pass2 =
                    (fn  v9 =>
                      (fn  v10 =>
                        (fn  v14 =>
                          (fn  v11 =>
                            (fn  v13 =>
                              (fn  v12 =>
                                let val  v8 = the 0 (lookup_1 v12 v9)
                                    val  v7 = the 0 (lookup_1 v12 v10)
                                    val  v6 = remove_inactive_intervals v8 v13
                                    val  v5 =
                                  map_colors_sub (the [] (lookup_1 v12 v14))
                                    val  v4 =
                                  fromalist (List.map (fn  v1 => (v1,())) v5)
                                    val  v3 =
                                  map_colors_sub (the [] (lookup_1 v12 v11))
                                in
                                  if  (is_phy_var_1 v12)
                                then  (let val  v2 =
                                  union_1 (linear_scan_state_phyregs v6) v4
                                 in
                                  linear_reg_alloc_step_aux v6 v2 [] v12 v7 (0 < 0)
                                end)
                                else  (linear_reg_alloc_step_aux v6 v4 v3 v12 v7 (0 < 0))
                                end))))))
                      fun  find_reg_exchange v10 v11 v9 =
                  case  v10
                  of  []  =>  (v11,v9)
                  |   v8::v7 =>  (let val  v6 = Array.sub ( colors, v8)
                      val  v5 = v8 div 2
                      val  v3 =
                    case  (lookup_1 v5 v9)
                    of  NONE =>  v5
                    |   SOME(v4) =>  v4
                      val  v1 =
                    case  (lookup_1 v6 v11)
                    of  NONE =>  v6
                    |   SOME(v2) =>  v2
                   in
                    find_reg_exchange v7 (insert_1 v6 v5 (insert_1 v3 v1 v11)) (insert_1 v5 v6 (insert_1 v1 v3 v9))
                  end)
                      val  apply_reg_exchange =
                    (fn  v7 =>
                      let val  v6 = find_reg_exchange v7 Ln Ln
                       in
                        case  v6
                      of  (v5,v4) =>  (let val  v3 = Array.length ( colors)
                      in
                        map_colors (fn  v2 =>
                        (case  (lookup_1 v2 v5)
                        of  NONE =>  v2
                        |   (SOME(v1)) =>  v1)) v3
                       end)
                      end)
                      fun  st_ex_filter_good v5 v6 =
                  case  v6
                  of  []  =>  []
                   |   v4::v3 =>  (let val  v2 = v5 v4
                   in
                    if  v2
                   then  (let val  v1 = st_ex_filter_good v5 v3
                   in
                    v4::v1
                   end)
                  else  (st_ex_filter_good v5 v3)
                  end)
                      val  linear_reg_alloc_intervals =
                    (fn  v30 =>
                      (fn  v31 =>
                        (fn  v32 =>
                          (fn  v29 =>
                            (fn  v33 =>
                              (fn  v34 =>
                                let val  v28 =
                                  edges_to_adjlist_impl (List.map snd (sort_moves_rev v33)) v30 Ln
                                    val  v27 = edges_to_adjlist_impl v29 v30 Ln
                                    val  v20 =
                                  qsort (fn  v26 =>
                                    (fn  v25 =>
                                      (lex (fn  v22 =>
                                        (fn  v21 => (v22 < v21))) (fn  v24 =>
                                        (fn  v23 => (v24 <= v23))) (the 0 (lookup_1 v26 v30),v26) (the 0 (lookup_1 v25 v30),v25)))) v34
                                    val  v19 = List.filter is_phy_var_1 v20
                                    val  v17 =
                                  List.filter (fn  v18 => (v18 < (2 * v32))) v19
                                    val  v15 =
                                  List.filter (fn  v16 => ((2 * v32) <= v16)) v19
                                    val  v14 =
                                  linear_reg_alloc_pass1_initial_state v32
                                    val  v13 =
                                  st_ex_foldl (linear_reg_alloc_step_pass1 v30 v31 v27 v28) v14 v20
                                    val  v12 = apply_reg_exchange v17
                                    val  v11 =
                                  st_ex_filter_good (fn  v2 =>
                                    (let val  v1 = Array.sub ( colors, v2)
                                    in
                                      (is_stack_var v2) orelse  (v32 <= v1)
                                    end)) v20
                                    val  v10 =
                                  linear_reg_alloc_pass2_initial_state v32 (List.length v11)
                                    val  v9 =
                                  fromalist (List.map (fn  v3 => (v3,())) v11)
                                    val  v8 =
                                  map_1 (List.filter (fn  v4 =>
                                    (((lookup_1 v4 v9) = NONE) = (0 < 0)))) v27
                                    val  v7 =
                                  map_1 (List.filter (fn  v5 =>
                                    (((lookup_1 v5 v9) = NONE) = (0 < 0)))) v28
                                    val  v6 =
                                  st_ex_foldl (linear_reg_alloc_step_pass2 v30 v31 v8 v7) v10 v11
                                 in
                                  apply_reg_exchange v15
                                 end))))))
                      fun  extract_coloration v5 v6 v4 =
                  case  v6
                  of  []  =>  v4
                  |   v3::v2 =>  (let val  v1 = Array.sub ( colors, v3)
                  in
                    extract_coloration v5 v2 (insert_1 (the 0 (lookup_1 v3 v5)) v1 v4)
                  end)
                      val  linear_reg_alloc_intervals_and_extract_coloration =
                    (fn  v3 =>
                      (fn  v4 =>
                        (fn  v6 =>
                          (fn  v2 =>
                            (fn  v7 =>
                              (fn  v9 =>
                                (fn  v5 =>
                                  (fn  v8 =>
                                    let val  v1 =
                                      linear_reg_alloc_intervals v3 v4 v6 v2 v7 v9
                                     in
                                      extract_coloration v5 v9 Ln
                                     end))))))))
                  in
                    (Success(linear_reg_alloc_intervals_and_extract_coloration v8 v7 v6 v5 v4 v3 v2 v1))
                  handle  e =>  Failure(e)
                  end)))))));
  datatype linear_scan_live_tree =  Seq_1 of  linear_scan_live_tree *  linear_scan_live_tree
  |  Branch_1 of  linear_scan_live_tree *  linear_scan_live_tree
  |  Reads of  int list
  |  Writes of  int list;
  fun  get_live_tree v16 =
  case  v16
  of  Delta(v2,v1) =>  (Seq_1(Reads(v1),Writes(v2)))
  |   Set(v4) =>  (let val  v3 = List.map fst (toalist v4)
  in
    Reads(v3)
  end)
  |   Branch(v11,v10,v9) =>  (let val  v8 = get_live_tree v10
      val  v7 = get_live_tree v9
   in
    case  v11
  of  NONE =>  (Branch_1(v8,v7))
  |   SOME(v6) =>  (let val  v5 = List.map fst (toalist v6)
  in
    Seq_1(Reads(v5),Branch_1(v8,v7))
  end)
  end)
  |   Seq(v15,v14) =>  (let val  v13 = get_live_tree v14
      val  v12 = get_live_tree v15
   in
    Seq_1(v12,v13)
  end);
  fun  numset_list_insert v3 v4 =
  case  v3
  of  []  =>  v4
  |   v2::v1 =>  (numset_list_insert v1 (insert_1 v2 () v4));
  fun  get_live_backward v10 v9 =
  case  v10
  of  Writes(v1) =>  (numset_list_delete v1 v9)
  |   Reads(v2) =>  (numset_list_insert v2 v9)
  |   Branch_1(v6,v5) =>  (let val  v4 = get_live_backward v6 v9
      val  v3 = get_live_backward v5 v9
   in
    numset_list_insert (List.map fst (toalist (difference v3 v4))) v4
   end)
  |   Seq_1(v8,v7) =>  (get_live_backward v8 (get_live_backward v7 v9));
  fun  fix_domination v2 =
    let val  v1 = get_live_backward v2 Ln
     in
      if  (v1 = Ln)
    then  v2
     else  (Seq_1(Writes(List.map fst (toalist v1)),v2))
    end;
  fun  numset_list_add_if v5 v7 v6 v4 =
  case  v5
  of  []  =>  v6
  |   v3::v2 =>  (case  (lookup_1 v3 v6)
  of  NONE =>  (numset_list_add_if v2 v7 (insert_1 v3 v7 v6) v4)
  |   (SOME(v1)) =>  (if  (v4 v7 v1)
  then  (numset_list_add_if v2 v7 (insert_1 v3 v7 v6) v4)
  else  (numset_list_add_if v2 v7 v6 v4)));
  fun  numset_list_add_if_lt v3 =
    (fn  v5 =>
      (fn  v4 =>
        numset_list_add_if v3 v5 v4 (fn  v2 => (fn  v1 => (v2 <= v1)))));
  fun  numset_list_add_if_gt v3 =
    (fn  v5 =>
      (fn  v4 =>
        numset_list_add_if v3 v5 v4 (fn  v2 => (fn  v1 => (v1 <= v2)))));
  fun  get_intervals v19 v20 v17 v18 =
  case  v19
  of  Writes(v1) =>  (v20 - 1,(numset_list_add_if_lt v1 v20 v17,numset_list_add_if_gt v1 v20 v18))
  |   Reads(v2) =>  (v20 - 1,(v17,numset_list_add_if_gt v2 v20 v18))
  |   Branch_1(v9,v8) =>  (let val  v7 = get_intervals v8 v20 v17 v18
   in
    case  v7
  of  (v6,v5) =>  (case  v5 of  (v4,v3) =>  (get_intervals v9 v6 v4 v3))
  end)
  |   Seq_1(v16,v15) =>  (let val  v14 = get_intervals v15 v20 v17 v18
   in
    case  v14
  of  (v13,v12) =>  (case  v12 of  (v11,v10) =>  (get_intervals v16 v13 v11 v10))
  end);
  fun  linear_scan_reg_alloc v23 =
    (fn  v24 =>
      (fn  v21 =>
        (fn  v22 =>
          let val  v20 = fix_domination (get_live_tree v21)
              val  v19 = get_intervals v20 0 Ln Ln
           in
            case  v19
          of  (v18,v17) =>  (case  v17
          of  (v16,v15) =>  (let val  v14 =
            foldl find_bijection_step find_bijection_init (List.map fst (toalist v16))
              val  v10 =
            List.map (fn  v13 =>
              (case  v13
              of  (v12,v11) =>  (the 0 (lookup_1 v12 (bijection_state_bij v14)),the 0 (lookup_1 v11 (bijection_state_bij v14))))) v22
              val  v4 =
            List.map (fn  v9 =>
              (case  v9
              of  (v8,v7) =>  (case  v7
              of  (v6,v5) =>  (v8,(the 0 (lookup_1 v6 (bijection_state_bij v14)),the 0 (lookup_1 v5 (bijection_state_bij v14))))))) v24
              val  v3 = apply_bijection (bijection_state_bij v14) v16
              val  v2 = apply_bijection (bijection_state_bij v14) v15
              val  v1 = List.map fst (toalist v3)
          in
            run_linear_reg_alloc_intervals v3 v2 v23 v10 v4 v1 (bijection_state_invbij v14) (bijection_state_nmax v14)
          end))
          end)));
end
