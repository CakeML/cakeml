(* Code to recall that some partial functions (of type 'a -> 'b option)
can be represented as sorted alists, and derive a fast conversion on
applications of those functions. *)

structure alist_treeLib = struct

open preamble alist_treeTheory

(* the repr set object *)
datatype 'a alist_reprs = AList_Reprs of {R_thm: thm, conv: conv,
    dest: term -> 'a, cmp: ('a * 'a) -> order,
    dict: (term, thm) Redblackmap.dict ref}

fun mk_alist_reprs R_thm conv dest cmp
    = AList_Reprs {R_thm = R_thm, conv = conv, cmp = cmp,
        dest = dest, dict = ref (Redblackmap.mkDict Term.compare)}

(* constructing is_insert thms *)

val count_append_tm = ``count_append``;

fun find_key_rec is_last [] = raise Empty
  | find_key_rec is_last (t :: ts) = if listSyntax.is_nil t
  then find_key_rec is_last ts
  else let
    val (f, xs) = strip_comb t
    val do_rev = if is_last then rev else I
  in if same_const f count_append_tm
    then find_key_rec is_last (do_rev (tl xs) @ ts)
    else hd (do_rev (fst (listSyntax.dest_list t))) end

fun hd_key t = find_key_rec false [t] |> pairSyntax.dest_pair |> fst
fun last_key t = find_key_rec true [t] |> pairSyntax.dest_pair |> fst

fun mk_singleton x = listSyntax.mk_list ([x], type_of x)

val err = mk_HOL_ERR "mltree?"

val simp_count_append = SIMP_CONV bool_ss [count_append_HD_LAST, pairTheory.FST]

fun assume_prems thm = if not (is_imp (concl thm)) then thm
  else let
    val thm = CONV_RULE (RATOR_CONV simp_count_append) thm
    val l_asm = fst (dest_imp (concl thm))
    val prem = if l_asm = T then TRUTH else ASSUME l_asm
  in
    assume_prems (MP thm prem)
  end

val is_insert_tm = ``is_insert``
val count_append_tm = ``count_append``

fun do_inst_mp insts mp_thm arg_thm = let
    val (prem, _) = dest_imp (concl mp_thm)
    fun rerr e s = let
        val m = s ^ ": " ^ #message e
      in print ("error in do_inst_mp: " ^ m ^ "\n");
        print_thm mp_thm; print "\n"; print_thm arg_thm; print "\n";
        raise (err "do_inst_mp" m) end
    val (more_insts, ty_insts) = match_term prem (concl arg_thm)
      handle HOL_ERR e => rerr e "match_term"
    val ty_i_thm = INST_TYPE ty_insts mp_thm
    val ithm = INST (more_insts @ insts) ty_i_thm
      handle HOL_ERR e => rerr e "INST"
  in MP ithm arg_thm handle HOL_ERR e => rerr e "MP" end

fun build_insert (dest : term -> 'a) cmp R k x =
  let
    val dest_k = dest k
    fun chk thm = if same_const is_insert_tm (fst (strip_comb (concl thm)))
      then thm
      else (print "Not an insert_tm:\n"; print_thm thm; print "\n";
        raise (err "build_insert" "check"))
    val pp = chk o assume_prems
    fun build t = if listSyntax.is_nil t
      then pp (ISPECL [R, k, x] is_insert_to_empty)
      else if listSyntax.is_cons t then let
        val (xs, _) = listSyntax.dest_list t
        val _ = length xs = 1 orelse raise (err "build_insert" "malformed")
        val v = hd xs
      in case cmp (dest_k, dest (fst (pairSyntax.dest_pair v))) of
          EQUAL => pp (ISPECL [R, k, x, v] is_insert_overwrite)
        | GREATER => pp (ISPECL [R, k, x, t] is_insert_far_right)
        | LESS => pp (ISPECL [R, k, x, t] is_insert_far_left)
      end else let
        val (f, xs) = strip_comb t
        val _ = same_const count_append_tm f
           orelse raise (err "build_insert" "unknown")
        val (n, l, r) = case xs of [n, l, r] => (n, l, r)
           | _ => raise (err "build_insert" "num args")
        fun vsub nm v = [mk_var (nm, type_of v) |-> v]
      in if not (cmp (dest_k, dest (hd_key r)) = LESS)
        then do_inst_mp (vsub "l" l) (SPEC n is_insert_r) (build r)
        else if cmp (dest_k, dest (last_key l)) = GREATER
        then pp (ISPECL [R, n, l, r, k, x] is_insert_centre)
        else do_inst_mp (vsub "r" r) (SPEC n is_insert_l) (build l)
      end
  in build end

fun prove_assum_by_conv conv thm = let
    val (x,y) = dest_imp (concl thm)
    val thm = CONV_RULE ((RATOR_CONV o RAND_CONV) conv) thm
  in MP thm TRUTH handle HOL_ERR e =>
    (print "Failed to prove assum by conv:\n";
      print_term x;
      print "\n  -- reduced to:\n";
      print_term (fst (dest_imp (concl thm)));
      raise HOL_ERR e)
  end

(* balancing count_append trees *)
fun get_depth tm = let
    val (f, xs) = strip_comb tm
  in if same_const f count_append_tm
    then numSyntax.int_of_term (hd xs)
    else if listSyntax.is_cons tm then 1
    else raise (err "get_depth" "unknown")
  end

fun balance iter bias tm = if iter > 1000 then
    (print "error: looping balance\n"; print_term tm;
        raise (err "balance" "looping"))
  else let
    val (f, xs) = strip_comb tm
    val _ = same_const f count_append_tm orelse raise UNCHANGED
    val _ = is_arb (hd xs) orelse bias <> "N" orelse raise UNCHANGED
    val step_conv = (RAND_CONV (balance 0 "N"))
        THENC (RATOR_CONV (RAND_CONV (balance 0 "N")))
    val thm = QCONV step_conv tm
    val tm = rhs (concl thm)
    val l_sz = get_depth (rand (rator tm))
    val r_sz = get_depth (rand tm)
    val reb = if l_sz > (r_sz + 1) orelse (bias = "R" andalso l_sz > r_sz)
        then "R"
        else if r_sz > (l_sz + 1) orelse (bias = "L" andalso r_sz > l_sz)
        then "L" else "N"
    val conv1 = if reb = "R" then RATOR_CONV (RAND_CONV (balance 0 "L"))
        else if reb = "L" then RAND_CONV (balance 0 "R") else ALL_CONV
    val conv2 = if reb = "R" then REWR_CONV balance_r
        else if reb = "L" then REWR_CONV balance_l else ALL_CONV
    val thm = CONV_RULE (QCONV (RHS_CONV (conv1 THENC conv2 THENC step_conv))) thm
    val tm = rhs (concl thm)
    val l_sz = get_depth (rand (rator tm))
    val r_sz = get_depth (rand tm)
    val sz = numSyntax.term_of_int (1 + Int.max (l_sz, r_sz))
    val set = REWR_CONV (set_count |> SPEC sz)
    val final = if Int.abs (l_sz - r_sz) < 2 then set else balance (iter + 1) "N"
  in CONV_RULE (RHS_CONV final) thm end

fun prove_insert R conv dest cmp k x al = let
    val thm = build_insert dest cmp R k x al
    fun prove thm = if not (is_imp (concl thm)) then thm
      else prove (prove_assum_by_conv conv thm)
  in thm |> DISCH_ALL |> prove |> CONV_RULE (RAND_CONV (balance 0 "N")) end

(* making repr theorems *)

val alookup_tm = ``ALOOKUP``;
val option_choice_tm = ``option_choice_f``;

fun is_short_list xs = listSyntax.is_nil xs
    orelse total (listSyntax.is_nil o snd o listSyntax.dest_cons) xs = SOME true

fun mk_insert_repr (AList_Reprs rs) prev_repr k_x = let
    val (k, x) = pairSyntax.dest_pair k_x
    val (R, al) = case strip_comb (concl prev_repr)
      of (_, [R, al, _]) => (R, al)
        | _ => raise (err "mk_insert_repr" "unexpected")
    val insert = prove_insert R (#conv rs) (#dest rs) (#cmp rs) k x al
  in MATCH_MP repr_insert (CONJ prev_repr insert) end

fun mk_repr_step rs tm = let
    val (AList_Reprs inn_rs) = rs
    val (f, xs) = strip_comb tm
    val is_empty = total (optionSyntax.is_none o snd o dest_abs) tm = SOME true
    val is_alookup = same_const alookup_tm f
    val is_short = is_alookup andalso total (is_short_list o hd) xs = SOME true
    val merge_lhs = if same_const option_choice_tm f then [hd xs] else []
    val merge_unknown = exists ((fn t => not (same_const t alookup_tm
        orelse same_const t option_choice_tm)) o fst o strip_comb) merge_lhs
    val merge_alookup_xs = map strip_comb merge_lhs
        |> filter (same_const alookup_tm o fst) |> map (hd o snd)
    val is_insert = exists (fn xs => not (listSyntax.is_nil xs)
        andalso is_short_list xs) merge_alookup_xs
  in if is_empty
    then MATCH_MP (MATCH_MP repr_empty (#R_thm inn_rs)) (REFL tm)
    else if is_short
    then MATCH_MP (ISPEC (hd xs) alist_repr_refl) (#R_thm inn_rs)
        |> prove_assum_by_conv (SIMP_CONV list_ss [sortingTheory.SORTED_DEF])
    else if is_insert
    then mk_insert_repr rs (mk_repr rs (rand tm))
        (fst (listSyntax.dest_cons (hd merge_alookup_xs)))
    else if merge_unknown
    then let
        val l_repr_thm = mk_repr rs (hd xs)
        val l_repr_al = rand (rator (concl l_repr_thm))
        val look = mk_icomb (alookup_tm, l_repr_al)
        val half_repr = list_mk_icomb (option_choice_tm, [look, List.last xs])
        val next_repr = mk_repr rs half_repr
      in MATCH_MP alist_repr_choice_trans_left (CONJ l_repr_thm next_repr) end
    else if not (null merge_lhs) orelse is_alookup
    then CHANGED_CONV (SIMP_CONV bool_ss [alookup_to_option_choice,
                option_choice_f_assoc, alookup_empty_option_choice_f]) tm
    else raise err "mk_repr_step" ("no step for: " ^ Parse.term_to_string f)
  end
and mk_repr_known_step (AList_Reprs inn_rs) tm =
  case Redblackmap.peek (! (#dict inn_rs), tm) of
    SOME thm => thm
  | NONE => mk_repr_step (AList_Reprs inn_rs) tm
and mk_repr rs tm = let
    val thm = mk_repr_known_step rs tm
  in if is_eq (concl thm)
    then mk_repr_known_step rs (rhs (concl thm))
      |> CONV_RULE (RAND_CONV (REWR_CONV (SYM thm)))
    else thm
  end

fun add_alist_repr rs thm = let
    val AList_Reprs inn_rs = rs
    val (f, rhs) = dest_eq (concl thm)
    val repr_thm = case Redblackmap.peek (! (#dict inn_rs), rhs) of
        SOME rhs_thm => if is_eq (concl rhs_thm)
          then TRANS thm rhs_thm
          else thm
      | NONE => (mk_repr rs rhs
        |> CONV_RULE (RAND_CONV (REWR_CONV (SYM thm))))
  in
    #dict inn_rs := Redblackmap.insert (! (#dict inn_rs), f, repr_thm)
  end

fun timeit msg f v = let
    val start = Portable.timestamp ()
    val r = f v
    val time = Portable.timestamp () - start
  in print ("Time to " ^ msg ^ ": " ^ Portable.time_to_string time ^ "\n");
    r end

(* testing *)

fun test_rs () = let
    val _ = load "comparisonTheory";
    val thm1 = DB.fetch "comparison" "good_cmp_Less_irrefl_trans"
    val thm2 = DB.fetch "comparison" "num_cmp_good"
    val R_thm = MATCH_MP thm1 thm2
  in mk_alist_reprs R_thm EVAL numSyntax.int_of_term Int.compare end

fun test_mk_alookup ns = let
    open numSyntax
    val _ = I
    fun f i = ((i * 157) mod 1000)
    fun el i = pairSyntax.mk_pair (term_of_int (f i), term_of_int i)
  in mk_icomb (alookup_tm, listSyntax.mk_list (map el ns, type_of (el 0))) end

fun test_200 rs = let
    val al1 = test_mk_alookup (upto 1 200)
    val al2 = test_mk_alookup [1, 4, 3]
    val merge = list_mk_icomb (option_choice_tm, [al1, al2])
  in mk_repr rs merge end

(*
val rs = test_rs ()
val thm_200 = timeit "build repr" test_200 rs
*)

(* proving and using is_lookup thms *)
val is_lookup_tm = ``is_lookup``;

fun build_lookup (dest : term -> 'a) cmp R k =
  let
    val dest_k = dest k
    fun chk thm = if same_const is_lookup_tm (fst (strip_comb (concl thm)))
      then thm
      else (print "Not a lookup_tm:\n"; print_thm thm; print "\n";
        raise (err "build_lookup" "check"))
    val pp = chk o assume_prems
    fun build t = if listSyntax.is_nil t
      then pp (ISPECL [R, k] is_lookup_empty)
      else if listSyntax.is_cons t then let
        val (xs, _) = listSyntax.dest_list t
        val _ = length xs = 1 orelse raise (err "build_insert" "malformed")
        val (k', v) = pairSyntax.dest_pair (hd xs)
      in case cmp (dest_k, dest k') of
          EQUAL => pp (ISPECL [R, k, k', v] is_lookup_hit)
        | GREATER => pp (ISPECL [R, k, k', v] is_lookup_far_right)
        | LESS => pp (ISPECL [R, k, k', v] is_lookup_far_left)
      end else let
        val (f, xs) = strip_comb t
        val _ = same_const count_append_tm f
           orelse raise (err "build_lookup" "unknown")
        val (n, l, r) = case xs of [n, l, r] => (n, l, r)
           | _ => raise (err "build_lookup" "num args")
        fun vsub nm v = [mk_var (nm, type_of v) |-> v]
      in if not (cmp (dest_k, dest (hd_key r)) = LESS)
        then do_inst_mp (vsub "l" l) (SPEC n is_lookup_r) (build r)
        else if cmp (dest_k, dest (last_key l)) = GREATER
        then pp (ISPECL [R, n, l, r, k] is_lookup_centre)
        else do_inst_mp (vsub "r" r) (SPEC n is_lookup_l) (build l)
      end
  in build end

fun prove_lookup R conv dest cmp k al = let
    val thm = build_lookup dest cmp R k al
    fun prove thm = if not (is_imp (concl thm)) then thm
      else prove (prove_assum_by_conv conv thm)
  in thm |> DISCH_ALL |> prove end

val repr_tm = ``sorted_alist_repr``;

fun repr_prove_lookup conv dest cmp repr_thm k = let
    val (f, xs) = strip_comb (concl repr_thm)
    val f = same_const f repr_tm orelse
        raise (err "repr_prove_lookup" "unexpected")
    val (R, al, f) = case xs of [R, al, f] => (R, al, f)
        | _ => raise (err "repr_prove_lookup" "num args")
    val lookup = prove_lookup R conv dest cmp k al
  in MATCH_MP lookup_repr (CONJ repr_thm lookup) end

fun reprs_conv rs tm = let
    val AList_Reprs inn_rs = rs
    val (f, x) = dest_comb tm handle HOL_ERR _ => raise UNCHANGED
    val repr_thm = case Redblackmap.peek (! (#dict inn_rs), f) of
      NONE => raise UNCHANGED | SOME thm => thm
  in repr_prove_lookup (#conv inn_rs) (#dest inn_rs) (#cmp inn_rs)
    repr_thm x end

fun test_f_def () = new_definition ("f", mk_eq (``f : num -> num option``,
    test_mk_alookup (upto 1 300)));

fun extract_test rs i = mk_comb (``f : num -> num option``,
    numSyntax.term_of_int i)
  |> reprs_conv rs

fun extract_test_1000 rs = let
    val res1 = timeit "add def" (add_alist_repr rs) (test_f_def ())
    val res2 = timeit "map extract" (map (extract_test rs)) (upto 1 1000)
  in res2 end

end

