open preamble BasicProvers stackSemTheory wordSemTheory
     word_to_stackTheory wordPropsTheory stackPropsTheory
     word_allocProofTheory semanticsPropsTheory;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_to_stackProof";

(*TODO: Quantification over t k a c col -- should not affect correctness*)
(*Should be simple to write one for all non-recursive cases*)
val get_vars_code_frame = prove(``
  ∀ls.
  get_vars ls (st with code:=l) =
  get_vars ls st``,
  Induct>>fs[get_vars_def,get_var_def])

(*Move to wordProps so there's no scoping problems..*)
val word_exp_code_frame = prove(``
  ∀(s:('a,'b) wordSem$state) exp. word_exp (s with code:=l) exp =
          word_exp s (exp:'a wordLang$exp)``,
  ho_match_mp_tac wordSemTheory.word_exp_ind>>rw[word_exp_def]
  >-
    (every_case_tac>>fs[mem_load_def])
  >>
    `ws=ws'` by
      (unabbrev_all_tac>>
      fs[MAP_EQ_f])>>
    fs[])

val tac =
    fs[evaluate_def,LET_THM]>>
    qexists_tac`st.permute`>>fs[alloc_def,get_var_def,gc_def,LET_THM,push_env_def,set_store_def,env_to_list_def,pop_env_def,has_space_def,call_env_def,set_var_def,get_var_def,dec_clock_def,jump_exc_def,get_vars_perm,get_vars_code_frame,set_vars_def,word_exp_perm,word_exp_code_frame,mem_store_def]>>
    every_case_tac>>fs[state_component_equality]

val rm_perm = prove(``
  s with permute:= s.permute = s``,fs[state_component_equality])

val size_tac= (fs[wordLangTheory.prog_size_def]>>DECIDE_TAC);

val compile_single_correct = prove(``
  ∀prog st l.
  (!n v. lookup n st.code = SOME v ==>
         lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
  ∃perm'.
    let (res,rst) = evaluate (prog,st with permute := perm') in
      if res = SOME Error then T
      else
        let (res1,rst1) = evaluate (prog,st with code := l) in
          res1 = res ∧
          rst.code = st.code ∧
          rst1 = rst with code := l``,
  (*recInduct doesn't seem to give a nice induction thm*)
  completeInduct_on`prog_size (K 0) (prog:'a wordLang$prog)`>>
  rpt strip_tac>>
  fs[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- tac
  >- tac
  >- cheat
  >- tac
  >- tac
  >- tac
  >- tac
  >- (*Call -- the hard case*)
    cheat
  >- (*Seq, inductive*)
    (fs[evaluate_def,LET_THM,AND_IMP_INTRO]>>
    last_assum(qspecl_then[`p`,`st`,`l`] mp_tac)>>
    discharge_hyps>- size_tac>> rw[]>>
    split_pair_tac>>fs[]
    >- (qexists_tac`perm'`>>rw[]) >>
    split_pair_tac>>fs[]>>
    reverse (Cases_on`res`)>>fs[]
    >- (qexists_tac`perm'`>>fs[])>>
    first_assum(qspecl_then[`p0`,`rst`,`l`] mp_tac)>>
    discharge_hyps>- size_tac>>
    rw[]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'''`>>rw[]>>fs[]) 
  >- cheat
  >- cheat
  >- tac
  >- tac
  >- tac
  >- (tac>>
     Cases_on`call_FFI st.ffi n x'`>>simp[]))

val MEM_TAKE = prove(
  ``!xs n x. MEM x (TAKE n xs) ==> MEM x xs``,
  Induct \\ fs [TAKE_def] \\ rw [] \\ res_tac \\ fs []);

val MEM_LASTN_ALT = prove(
  ``!xs n x. MEM x (LASTN n xs) ==> MEM x xs``,
  fs [LASTN_def] \\ rw [] \\ imp_res_tac MEM_TAKE \\ fs []);

(* TODO: remove LASTN, only use LAST_N *)
val LAST_N_LASTN_eq = store_thm("LAST_N_LASTN_eq[simp]",
  ``∀ls n. LAST_N n ls = LASTN n ls``,
  fs[LAST_N_def,LASTN_def])

val clock_add_0 = store_thm("clock_add_0[simp]",
  ``((t with clock := t.clock + 0) = t:('a,'ffi) stackSem$state) /\
    ((t with clock := t.clock) = t:('a,'ffi) stackSem$state)``,
  fs [stackSemTheory.state_component_equality]);

val DROP_DROP_EQ = store_thm("DROP_DROP_EQ",
  ``!n m xs. DROP m (DROP n xs) = DROP (m + n) xs``,
  Induct \\ fs [] \\ Cases_on `xs` \\ fs []
  \\ rpt strip_tac \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac);

val TAKE_TAKE_MIN = prove(
  ``!xs m n. TAKE n (TAKE m xs) = TAKE (MIN m n) xs``,
  Induct \\ Cases_on `m` \\ Cases_on `n` \\ fs [MIN_DEF]
  \\ rw [] \\ fs [] \\ TRY (`F` by decide_tac)
  \\ `n = 1` by decide_tac \\ fs []);

val TAKE_DROP_EQ = prove(
  ``!xs n m. TAKE m (DROP n xs) = DROP n (TAKE (m + n) xs)``,
  Induct \\ fs [] \\ rw [] \\ fs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC) \\ decide_tac);

val DROP_TAKE_NIL = prove(
  ``DROP n (TAKE n xs) = []``,
  fs [GSYM LENGTH_NIL,LENGTH_TAKE_EQ] >> simp[]);

val TAKE_LUPDATE = store_thm("TAKE_LUPDATE[simp]",
  ``!xs n x i. TAKE n (LUPDATE x i xs) = LUPDATE x i (TAKE n xs)``,
  Induct \\ fs [LUPDATE_def]
  \\ Cases_on `i` \\ fs [LUPDATE_def] \\ rw [LUPDATE_def]);

local
  val DROP_LUPDATE_lemma1 = prove(
    ``!xs n m h. n <= m ==>
                 DROP n (LUPDATE h m xs) = LUPDATE h (m - n) (DROP n xs)``,
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def]
    \\ qmatch_assum_rename_tac `n <= SUC i`
    \\ `n - 1 <= i /\ (SUC i - n = i - (n - 1))` by decide_tac \\ fs [])
  val DROP_LUPDATE_lemma2 = prove(
    ``!xs n m h. m < n ==> DROP n (LUPDATE h m xs) = DROP n xs``,
    Induct \\ fs [LUPDATE_def] \\ rw []
    \\ Cases_on `m` \\ fs [LUPDATE_def]
    \\ qmatch_assum_rename_tac `SUC i < n`
    \\ first_x_assum match_mp_tac \\ decide_tac)
in
  val DROP_LUPDATE = store_thm("DROP_LUPDATE",
    ``!n h m xs.
        DROP n (LUPDATE h m xs) =
        if m < n then DROP n xs else LUPDATE h (m - n) (DROP n xs)``,
    rw [DROP_LUPDATE_lemma2]
    \\ match_mp_tac DROP_LUPDATE_lemma1
    \\ fs [NOT_LESS])
end

val MIN_ADD = prove(
  ``MIN m1 m2 + n = MIN (m1 + n) (m2 + n)``,
  fs [MIN_DEF] \\ decide_tac);

val list_LUPDATE_def = Define `
  (list_LUPDATE [] n ys = ys) /\
  (list_LUPDATE (x::xs) n ys = list_LUPDATE xs (n+1) (LUPDATE x n ys))`

val LENGTH_list_LUPDATE = store_thm("LENGTH_list_LUPDATE[simp]",
  ``!xs n ys. LENGTH (list_LUPDATE xs n ys) = LENGTH ys``,
  Induct \\ fs [list_LUPDATE_def]);

val TAKE_list_LUPDATE = store_thm("TAKE_list_LUPDATE[simp]",
  ``!ys xs n i. TAKE n (list_LUPDATE ys i xs) = list_LUPDATE ys i (TAKE n xs)``,
  Induct \\ fs [list_LUPDATE_def]);

val el_opt_list_LUPDATE_IGNORE = prove(
  ``!xs i n ys.
      i + LENGTH xs <= n ==>
      el_opt n (list_LUPDATE xs i ys) = el_opt n ys``,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `(i+1) + LENGTH xs <= n` by decide_tac \\ res_tac
  \\ `i <> n` by decide_tac \\ fs [el_opt_LUPDATE]);

val DROP_list_LUPDATE = prove(
  ``!ys n m xs.
      n <= m ==>
      DROP n (list_LUPDATE ys m xs) =
      list_LUPDATE ys (m - n) (DROP n xs)``,
  Induct
  \\ fs [list_LUPDATE_def,LENGTH_NIL,PULL_FORALL]
  \\ rpt strip_tac \\ `n <= m + 1` by decide_tac
  \\ rw [] \\ `m + 1 - n = m - n + 1 /\ ~(m < n)` by decide_tac
  \\ fs [DROP_LUPDATE]);

val DROP_list_LUPDATE_IGNORE = prove(
  ``!xs i ys n.
      LENGTH xs + i <= n ==>
      DROP n (list_LUPDATE xs i ys) = DROP n ys``,
  Induct \\ fs [list_LUPDATE_def] \\ rpt strip_tac
  \\ `LENGTH xs + (i+1) <= n /\ i < n` by decide_tac
  \\ fs [DROP_LUPDATE]);

val list_LUPDATE_NIL = store_thm("list_LUPDATE_NIL[simp]",
  ``!xs i. list_LUPDATE xs i [] = []``,
  Induct \\ fs [list_LUPDATE_def,LUPDATE_def]);

val LUPDATE_TAKE_LEMMA = prove(
  ``!xs n w. LUPDATE w n xs = TAKE n xs ++ LUPDATE w 0 (DROP n xs)``,
  Induct \\ Cases_on `n` \\ fs [LUPDATE_def]);

val list_LUPDATE_TAKE_DROP = store_thm("list_LUPDATE_TAKE_DROP",
  ``!xs (ys:'a list) n.
       list_LUPDATE xs n ys = TAKE n ys ++ list_LUPDATE xs 0 (DROP n ys)``,
  Induct \\ simp_tac std_ss [Once list_LUPDATE_def]
  \\ once_rewrite_tac [list_LUPDATE_def] THEN1 fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [DROP_LUPDATE,DROP_DROP_EQ,AC ADD_COMM ADD_ASSOC]
  \\ simp_tac std_ss [Once LUPDATE_TAKE_LEMMA,TAKE_TAKE_MIN] \\ rpt strip_tac
  \\ `MIN (n + 1) n = n`  by (fs [MIN_DEF] \\ decide_tac) \\ fs []
  \\ AP_TERM_TAC \\ fs [TAKE_DROP_EQ,AC ADD_COMM ADD_ASSOC]);

val list_LUPDATE_0_CONS = store_thm("list_LUPDATE_0_CONS[simp]",
  ``!xs x ys y. list_LUPDATE (x::xs) 0 (y::ys) = x :: list_LUPDATE xs 0 ys``,
  fs [list_LUPDATE_def,LUPDATE_def]
  \\ simp_tac std_ss [Once list_LUPDATE_TAKE_DROP] \\ fs []);

val list_LUPDATE_APPEND = store_thm("list_LUPDATE_APPEND",
  ``!xs ys zs.
      LENGTH xs = LENGTH ys ==> (list_LUPDATE xs 0 (ys ++ zs) = xs ++ zs)``,
  Induct \\ Cases_on `ys` \\ fs [list_LUPDATE_def]);

(* move to stackProps? *)

val DIV_ADD_1 = prove(
  ``0 < d ==> (m DIV d + 1 = (m + d) DIV d)``,
  rpt strip_tac
  \\ ASSUME_TAC (ADD_DIV_ADD_DIV |> Q.SPECL [`d`] |> UNDISCH
      |> Q.SPECL [`1`,`m`] |> ONCE_REWRITE_RULE [ADD_COMM]) \\ fs []);

val LENGTH_word_list_lemma = prove(
  ``!xs d. 0 < d ==> (LENGTH (word_list xs d) = (LENGTH xs - 1) DIV d + 1)``,
  recInduct word_list_ind
  \\ rpt strip_tac \\ fs []
  \\ once_rewrite_tac [word_list_def] \\ fs [] \\ rw []
  \\ imp_res_tac ZERO_DIV \\ fs [] \\ res_tac
  \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fs []
  \\ fs [ADD1] \\ fs [NOT_LESS]
  \\ imp_res_tac (ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_EXISTS)
  THEN1 (`LENGTH xs - 1 < d` by decide_tac
         \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fs [])
  \\ imp_res_tac DIV_ADD_1 \\ fs []
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ decide_tac);

val LENGTH_word_list = store_thm("LENGTH_word_list",
  ``!xs d. LENGTH (word_list xs d) =
           if d = 0 then 1 else (LENGTH xs - 1) DIV d + 1``,
  rw [] THEN1 (once_rewrite_tac [word_list_def] \\ fs [])
  \\ match_mp_tac LENGTH_word_list_lemma \\ decide_tac);

(* move to wordProps? *)

val list_rearrange_I = prove(
  ``(list_rearrange I = I)``,
  fs [list_rearrange_def,FUN_EQ_THM]
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF,GENLIST_ID]);

(* state relation *)

(*Convert stackLang stack to a list of frames with the bitmaps "read"*)

(*val abs_stack_def = tDefine "abs_stack" `
  abs_stack xs =
    if xs = [] then NONE else
    if xs = [Word 0w] then SOME [] else
    case read_bitmap xs of
    | NONE => NONE
    | SOME (bs,rs1,rs) =>
        if LENGTH rs < LENGTH bs then NONE else
          let xs1 = TAKE (LENGTH bs) rs in
          let xs2 = DROP (LENGTH bs) rs in
            case abs_stack xs2 of
            | NONE => NONE
            | SOME ys => SOME ((bs,rs1,xs1)::ys)`
 (WF_REL_TAC `measure LENGTH`
  \\ REPEAT STRIP_TAC
  \\ imp_res_tac read_bitmap_LENGTH
  \\ fs [LENGTH_DROP]
  \\ decide_tac)*)

(*Abstracts a stackLang stack w.r.t. to wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel
*)
val abs_stack_def = Define`
  (abs_stack [] [Word 0w] = SOME []) ∧
  (abs_stack [] _ = NONE) ∧
  (abs_stack ((StackFrame l NONE)::xs) stack =
    if stack = [Word 0w] then NONE
    else
    (*Should cover the stack = [] case automatically*)
    case read_bitmap stack of
    | NONE => NONE
    (*read_bitmap reads a bitmap and returns the liveness bits,
      the words read and the rest of the stack*)
    | SOME (bits,ws,rest) =>
        if LENGTH rest < LENGTH bits then NONE else
          let frame = TAKE (LENGTH bits) rest in
          let rest = DROP (LENGTH bits) rest in
            case abs_stack xs rest of
            | NONE => NONE
            | SOME ys => SOME ((NONE,bits,ws,frame)::ys)) ∧
  (abs_stack ((StackFrame l (SOME _))::xs) (w::stack) =
    (*Corresponds to a bitmap for a handler frame*)
    if w ≠ Word 4w then NONE
    else
      (case stack of
      (*Read next 2 elements on the stack for the handler*)
      | loc::hv::stack =>
          (if stack = [Word 0w] then NONE
          else
          case read_bitmap stack of
          | NONE => NONE
          | SOME (bits,ws,rest) =>
          if LENGTH rest < LENGTH bits then NONE else
          let frame = TAKE (LENGTH bits) rest in
          let rest = DROP (LENGTH bits) rest in
            case abs_stack xs rest of
            | NONE => NONE
            | SOME ys => SOME ((SOME(loc,hv),bits,ws,frame)::ys))
      | _ => NONE)) ∧
  (abs_stack _ _ = NONE)`

val index_list_def = Define `
  (index_list [] n = []) /\
  (index_list (x::xs) n = (n + LENGTH xs,x) :: index_list xs n)`

val MAP_FST_def = Define `
  MAP_FST f xs = MAP (\(x,y). (f x, y)) xs`

val adjust_names_def = Define `
  adjust_names n = n DIV 2`;

(*handler_val counts the total number of words in the list of frames*)
val handler_val_def = Define`
  (handler_val [] = 1n) ∧
  (handler_val ((NONE,_,ws,frame)::stack) =
    LENGTH ws+LENGTH frame+handler_val stack) ∧
  (handler_val ((SOME _,_,ws,frame)::stack) =
    (*Handler bitmaps are always size 1
      + 2 more for the pointer and locs
    *)
    3+LENGTH ws+LENGTH frame+handler_val stack)`

(*TODO: Maybe switch to this alternative index_list that goes from
stackLang vars to wordLang vars more directly*)
(*
val index_list_def = Define `
  (index_list [] k = []) /\
  (index_list (x::xs) k = (2*(k+LENGTH xs),x) :: index_list xs k)`
*)

(*Checks for consistency of the values*)
val stack_rel_aux_def = Define`
  (stack_rel_aux k len [] [] ⇔ T) ∧
  (stack_rel_aux k len ((StackFrame l NONE)::xs) ((NONE,bits,_,frame)::stack) ⇔
    filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
    stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len ((StackFrame l (SOME (h1,l1,l2)))::xs) ((SOME(loc,hv),bits,_,frame)::stack) ⇔
      h1 < LENGTH stack ∧
      hv = Word (n2w (len - handler_val (LASTN (h1+1) stack))) ∧
      loc = Loc l1 l2 ∧
      filter_bitmap bits (index_list frame k) = SOME (MAP_FST adjust_names l,[]) ∧
      stack_rel_aux k len xs stack) ∧
  (stack_rel_aux k len _ _ = F)`

(*
val join_stacks_def = Define `
  (join_stacks [] [] = SOME []) /\
  (join_stacks (StackFrame l NONE::st) (x::xs) =
     case join_stacks st xs of
     | NONE => NONE
     | SOME res => SOME ((StackFrame l NONE,[x])::res)) /\
  (join_stacks (StackFrame l (SOME z)::st) (x::y::xs) =
     case join_stacks st xs of
     | NONE => NONE
     | SOME res => SOME ((StackFrame l (SOME z),[x;y])::res)) /\
  (join_stacks _ _ = NONE)`

val abs_length_def = Define `
  (abs_length [] = 0) /\
  (abs_length ((_,rs1,xs1)::zs) = LENGTH rs1 + LENGTH xs1 + abs_length zs)`;

val sum_abs_length_def = Define `
  (sum_abs_length [] = 0) /\
  (sum_abs_length ((_,zs)::joined) = abs_length zs + sum_abs_length joined)`

val handler_val_def = Define `
  handler_val t_stack_length s_handler joined =
    Word (n2w (t_stack_length - sum_abs_length (LASTN s_handler joined)))`

val index_list_def = Define `
  (index_list [] n = []) /\
  (index_list (x::xs) n = (n + LENGTH xs,x) :: index_list xs n)`

val MAP_FST_def = Define `
  MAP_FST f xs = MAP (\(x,y). (f x, y)) xs`

val adjust_names_def = Define `
  adjust_names n = n DIV 2`;

val joined_ok_def = Define `
  (joined_ok k [] len <=> T) /\
  (joined_ok k ((StackFrame l1 NONE,[(bs1,rs1,xs1:'a word_loc list)])::rest) len <=>
     joined_ok k rest len /\
     (filter_bitmap bs1 (index_list xs1 k) =
      SOME (MAP_FST adjust_names l1,[])) (* /\
     (* the following is an experimental alternative to the above *)
     let current_frame = rs1 ++ xs1 in
     let f' = LENGTH xs1 in
     let f = LENGTH rs1 + LENGTH xs1 in
       (f = f' + f' DIV (dimindex (:'a) - 1) + 1) /\
       !n v.
         (lookup n (fromAList l1) = SOME v) <=>
         EVEN n /\ k <= n DIV 2 /\ n DIV 2 < k + f' /\
         (el_opt (f+k-(n DIV 2)) current_frame = SOME v) /\
         (el_opt (f+k-(n DIV 2)) (MAP (K F) rs1 ++ bs1) = SOME T) *)) /\
  (joined_ok k ((StackFrame l (SOME (h1,l1,l2)),
               [(bs1,rs1,xs1);(bs2,rs2,xs2)])::rest) len <=>
     (bs1 = [F;F]) /\ h1 <= LENGTH rest /\
     (xs1 = [handler_val len h1 rest; Loc l1 l2]) /\
     joined_ok k ((StackFrame l NONE,[(bs2,rs2,xs2)])::rest) len) /\
  (joined_ok k _ len <=> F)`

val stack_rel_def = Define `
  stack_rel k s_handler s_stack t_handler t_rest_of_stack t_stack_length <=>
    ?aa joined.
      s_handler <= LENGTH s_stack /\
      (t_handler = SOME (handler_val t_stack_length s_handler joined)) /\
      (abs_stack t_rest_of_stack = SOME aa) /\
      (join_stacks s_stack aa = SOME joined) /\
      joined_ok k joined t_stack_length`
*)

val sorted_env_def = Define `
  sorted_env (StackFrame l _) = SORTED (\x y. FST x > FST y) l`

val stack_rel_def = Define `
  stack_rel k s_handler s_stack t_handler t_rest_of_stack t_stack_length <=>
    s_handler < LENGTH s_stack ∧
    EVERY sorted_env s_stack /\
    ∃stack.
      abs_stack s_stack t_rest_of_stack = SOME stack ∧
      t_handler = SOME(Word (n2w (t_stack_length - handler_val (LASTN (s_handler+1) stack)))) ∧
      stack_rel_aux k t_stack_length s_stack stack`

val gc_fun_ok_def = Define `
  gc_fun_ok (f:'a gc_fun_type) =
    !wl m d s wl1 m1 s1.
      Handler IN FDOM s /\
      (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
      (LENGTH wl = LENGTH wl1) /\
      ~(Handler IN FDOM s1) /\
      (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,s ' Handler)))`

val state_rel_def = Define `
  state_rel k f f' (s:('a,'ffi) wordSem$state) (t:('a,'ffi) stackSem$state) <=>
    (s.clock = t.clock) /\ (s.gc_fun = t.gc_fun) /\ (s.permute = K I) /\
    (t.ffi = s.ffi) /\ t.use_stack /\ t.use_store /\ t.use_alloc /\
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\ 1 < k /\
    (s.store = t.store \\ Handler) /\ gc_fun_ok t.gc_fun /\
    (!n word_prog arg_count.
       (lookup n s.code = SOME (arg_count,word_prog)) ==>
       (lookup n t.code = SOME (word_to_stack$compile_prog word_prog arg_count k))) /\
    (lookup 5 t.code = SOME (raise_stub k)) /\
    good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    t.stack_space + f <= LENGTH t.stack /\ LENGTH t.stack < dimword (:'a) /\
    (if f' = 0 then f = 0 else (f = f' + f' DIV (dimindex (:'a) - 1) + 1)) /\
    let stack = DROP t.stack_space t.stack in
    (*First f things on stack*)
    let current_frame = TAKE f stack in
    let rest_of_stack = DROP f stack in
      stack_rel k s.handler s.stack (FLOOKUP t.store Handler)
        rest_of_stack (LENGTH t.stack) /\
      (!n v.
        (lookup n s.locals = SOME v) ==>
        EVEN n /\
        if n DIV 2 < k then (FLOOKUP t.regs (n DIV 2) = SOME v)
        else (el_opt (f-1 -(n DIV 2 - k)) current_frame = SOME v) /\
             n DIV 2 < k + f')`

(* correctness proof *)

val evaluate_SeqStackFree = prove(
  ``t.use_stack /\ t.stack_space <= LENGTH t.stack ==>
    evaluate (SeqStackFree f p,t) =
    evaluate (Seq (StackFree f) p,t)``,
  fs [SeqStackFree_def] \\ rw [stackSemTheory.evaluate_def]
  THEN1 (`F` by decide_tac) \\ AP_TERM_TAC
  \\ fs [stackSemTheory.state_component_equality]);

val convs_def = LIST_CONJ
  [word_allocTheory.post_alloc_conventions_def,
   word_allocTheory.call_arg_convention_def,
   wordLangTheory.every_var_def,
   wordLangTheory.every_stack_var_def,
   wordLangTheory.every_name_def]

val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``

val LENGTH_write_bitmap = prove(
  ``state_rel k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap (names:num_set) k f'):'a word list) + f' = f)``,
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac);

val evaluate_wLiveAux = prove(
  ``!xs k i t.
      xs <> [] /\ t.stack_space + i + LENGTH xs <= LENGTH t.stack /\
      t.use_stack ==>
      evaluate (wLiveAux xs k i,t) = (NONE,
        t with <| stack := list_LUPDATE (MAP Word xs) (t.stack_space + i) t.stack ;
                  regs := t.regs |+ (k, (Word (LAST xs))) |>)``,
  Induct \\ fs [] \\ Cases_on `xs` \\ fs []
  \\ once_rewrite_tac [wLiveAux_def]
  \\ simp_tac bool_ss [Once wLiveAux_def] \\ fs []
  \\ fs [stackSemTheory.evaluate_def,stackSemTheory.inst_def,
         stackSemTheory.assign_def,stackSemTheory.word_exp_def,LET_DEF,
         stackSemTheory.set_var_def,stackSemTheory.get_var_def]
  \\ rpt strip_tac
  \\ qmatch_assum_rename_tac `s.use_stack`
  \\ `~(LENGTH s.stack < s.stack_space + i)` by decide_tac
  \\ fs [list_LUPDATE_def,FLOOKUP_UPDATE]
  \\ first_x_assum (mp_tac o Q.SPECL [`k`,`i+1`,`s with
   <|regs := s.regs |+ (k, Word h');
     stack := LUPDATE (Word h') (s.stack_space + i) s.stack|>`])
  \\ fs [] \\ match_mp_tac IMP_IMP \\ strip_tac THEN1 decide_tac
  \\ rpt strip_tac \\ fs []
  \\ fs [stackSemTheory.state_component_equality,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`write_bitmap (names:num_set) k f'`,`k`,`0`,`t`]
  |> SIMP_RULE std_ss []
  |> INST_TYPE [beta|->``:'ffi``]

val DROP_list_LUPDATE_lemma =
  MATCH_MP DROP_list_LUPDATE (SPEC_ALL LESS_EQ_REFL) |> SIMP_RULE std_ss []

val bits_to_word_bit = prove(
  ``!bs i.
      i < dimindex (:'a) /\ i < LENGTH bs ==>
      ((bits_to_word bs:'a word) ' i = EL i bs)``,
  Induct \\ fs [] \\ Cases_on `i` \\ fs []
  \\ Cases \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1] \\ rpt strip_tac
  \\ first_x_assum match_mp_tac \\ fs [] \\ decide_tac);

val bits_to_word_miss = prove(
  ``!bs i.
      i < dimindex (:'a) /\ LENGTH bs <= i ==>
      ~((bits_to_word bs:'a word) ' i)``,
  Induct \\ fs [] THEN1 (EVAL_TAC \\ fs [word_0])
  \\ Cases_on `i` \\ fs [] \\ NTAC 2 strip_tac
  \\ `n < dimindex (:'a)` by decide_tac \\ res_tac
  \\ Cases_on `h` \\ fs [bits_to_word_def,word_or_def,fcpTheory.FCP_BETA,
       word_index,word_lsl_def,ADD1]);

val bits_to_word_NOT_0 = prove(
  ``!bs. LENGTH bs <= dimindex (:'a) /\ EXISTS I bs ==>
         (bits_to_word bs <> 0w:'a word)``,
  fs [fcpTheory.CART_EQ] \\ rpt strip_tac
  \\ fs [EXISTS_MEM,MEM_EL]
  \\ Q.EXISTS_TAC `n`   \\ fs []
  \\ `n < dimindex (:'a)` by decide_tac \\ fs [word_0]
  \\ fs [bits_to_word_bit]);

val list_LUPDATE_write_bitmap_NOT_NIL = prove(
  ``8 <= dimindex (:'a) ==>
    (list_LUPDATE (MAP Word (write_bitmap names k f')) 0 xs <>
     [Word (0w:'a word)])``,
  Cases_on `xs` \\ fs [list_LUPDATE_NIL]
  \\ fs [write_bitmap_def,LET_DEF,Once word_list_def]
  \\ strip_tac \\ `~(dimindex (:'a) <= 1)` by decide_tac \\ fs []
  \\ rw [] \\ rpt disj1_tac
  \\ match_mp_tac bits_to_word_NOT_0 \\ fs [LENGTH_TAKE_EQ]
  \\ fs [MIN_LE,MIN_ADD] \\ decide_tac);

val LESS_EQ_LENGTH = prove(
  ``!xs n. n <= LENGTH xs ==> ?xs1 xs2. xs = xs1 ++ xs2 /\ n = LENGTH xs1``,
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct_on `n` \\ fs [LENGTH_NIL] \\ rpt strip_tac
  \\ Cases_on `xs` \\ fs [] \\ res_tac \\ rw []
  \\ Q.LIST_EXISTS_TAC [`h::xs1`,`xs2`] \\ fs []);

val word_or_eq_0 = prove(
  ``((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,
  fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_0]
  \\ metis_tac []);

val shift_shift_lemma = prove(
  ``~(word_msb w) ==> (w ≪ 1 ⋙ 1 = w)``,
  fs [fcpTheory.CART_EQ,word_lsl_def,word_lsr_def,fcpTheory.FCP_BETA,word_msb_def]
  \\ rpt strip_tac \\ Cases_on `i + 1 < dimindex (:α)`
  \\ fs [fcpTheory.FCP_BETA] \\ fs [NOT_LESS]
  \\ `i = dimindex (:'a) - 1` by decide_tac \\ fs []);

val bit_length_bits_to_word = prove(
  ``!qs.
      LENGTH qs + 1 < dimindex (:'a) ==>
      bit_length (bits_to_word (qs ++ [T]):'a word) = LENGTH qs + 1``,
  Induct THEN1
   (fs [] \\ fs [Once bit_length_def] \\ fs [Once bit_length_def]
    \\ fs [bits_to_word_def] \\ EVAL_TAC)
  \\ Cases \\ fs [bits_to_word_def]
  \\ once_rewrite_tac [bit_length_def]
  \\ fs [ADD_CLAUSES]
  \\ rpt strip_tac \\ fs [EVAL ``1w >>> 1``]
  \\ `(LENGTH qs + 1) < dimindex (:'a)` by decide_tac \\ fs []
  \\ `bits_to_word (qs ++ [T]) << 1 <> 0w` by
   (fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_0,word_lsl_def]
    \\ Q.EXISTS_TAC `LENGTH qs + 1`
    \\ fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fs []
    \\ fs [EL_LENGTH_APPEND] \\ decide_tac)
  \\ `bits_to_word (qs ++ [T]) ≪ 1 ⋙ 1 =
      bits_to_word (qs ++ [T]):'a word` by
   (match_mp_tac shift_shift_lemma \\ fs [word_msb_def]
    \\ match_mp_tac bits_to_word_miss \\ fs [] \\ decide_tac)
  \\ fs [ADD1,word_or_eq_0]);

val GENLIST_bits_to_word_alt = prove(
  ``LENGTH (xs ++ ys) <= dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (xs ++ ys):'a word) ' i) (LENGTH xs) = xs``,
  fs [LIST_EQ_REWRITE] \\ rpt strip_tac
  \\ `EL x xs = EL x (xs ++ ys)` by fs [EL_APPEND1]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ match_mp_tac bits_to_word_bit
  \\ fs [] \\ decide_tac);

val GENLIST_bits_to_word = prove(
  ``LENGTH qs' + 1 < dimindex (:'a) ==>
    GENLIST (\i. (bits_to_word (qs' ++ [T]):'a word) ' i) (LENGTH qs') = qs'``,
  rpt strip_tac \\ match_mp_tac GENLIST_bits_to_word_alt
  \\ fs [] \\ decide_tac);

val read_bitmap_word_list = prove(
  ``8 <= dimindex (:'a) ==>
    read_bitmap
      (MAP Word (word_list (qs ++ [T]) (dimindex (:'a) - 1)) ++
        xs:'a word_loc list) =
    SOME (qs,MAP Word (word_list (qs ++ [T]) (dimindex (:'a) - 1)),xs)``,
  completeInduct_on `LENGTH (qs:bool list)` \\ rpt strip_tac \\ fs [PULL_FORALL]
  \\ rw [] \\ once_rewrite_tac [word_list_def]
  \\ `dimindex (:'a) - 1 <> 0` by decide_tac \\ fs []
  \\ Cases_on `LENGTH qs + 1 <= dimindex (:'a) - 1` \\ fs []
  THEN1
   (fs [read_bitmap_def]
    \\ `~word_msb (bits_to_word (qs ++ [T]))` by
     (fs [word_msb_def] \\ match_mp_tac bits_to_word_miss
      \\ fs [] \\ decide_tac) \\ fs []
    \\ `LENGTH qs + 1 < dimindex (:'a)` by decide_tac
    \\ fs [bit_length_bits_to_word,GENLIST_bits_to_word])
  \\ fs [read_bitmap_def]
  \\ `dimindex (:'a) - 1 =
        LENGTH (TAKE (dimindex (:'a) - 1) (qs ++ [T]))` by
    (fs [LENGTH_TAKE_EQ,MIN_DEF] \\ decide_tac)
  \\ `word_msb (bits_to_word (TAKE (dimindex (:'a) - 1)
         (qs ++ [T]) ++ [T]) :'a word)` by
   (fs [word_msb_def]
    \\ (bits_to_word_bit |> SPEC_ALL |> DISCH ``EL i (bs:bool list)``
          |> SIMP_RULE std_ss [] |> MP_CANON |> match_mp_tac) \\ fs []
    \\ reverse (rpt strip_tac) THEN1 decide_tac THEN1 decide_tac
    \\ pop_assum (fn th => simp_tac std_ss [Once th])
    \\ fs [EL_LENGTH_APPEND]) \\ fs []
  \\ `DROP (dimindex (:'a) - 1) (qs ++ [T]) =
      DROP (dimindex (:'a) - 1) qs ++ [T]` by
   (match_mp_tac DROP_APPEND1 \\ fs [NOT_LESS] \\ decide_tac)
  \\ `TAKE (dimindex (:'a) - 1) (qs ++ [T]) =
      TAKE (dimindex (:'a) - 1) qs` by
   (match_mp_tac TAKE_APPEND1 \\ fs [NOT_LESS] \\ decide_tac) \\ fs []
  \\ first_x_assum (mp_tac o Q.SPEC `DROP (dimindex (:'a) - 1) qs`)
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [LENGTH_DROP] \\ decide_tac)
  \\ rpt strip_tac \\ fs []
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV
        [GSYM (Q.SPEC `dimindex (:'a) - 1`
          (INST_TYPE [``:'a``|->``:bool``] TAKE_DROP))]))
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ Q.ABBREV_TAC `ts = TAKE (dimindex (:'a) - 1) qs` \\ fs []
  \\ match_mp_tac GENLIST_bits_to_word_alt \\ fs []
  \\ decide_tac);

val APPEND_LEMMA = prove(
  ``n1 + n2 + n3 <= LENGTH xs ==>
    ?xs2 xs3. (DROP n1 xs = xs2 ++ xs3) /\ n2 = LENGTH xs2``,
  rpt strip_tac
  \\ `n1 <= LENGTH xs` by decide_tac
  \\ Q.PAT_ASSUM `n1 + n2 + n3 <= LENGTH xs` MP_TAC
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [DROP_LENGTH_APPEND]  \\ fs []
  \\ `n2 <= LENGTH xs2` by decide_tac
  \\ imp_res_tac LESS_EQ_LENGTH
  \\ rw [] \\ metis_tac []);

val read_bitmap_write_bitmap = prove(
  ``t.stack_space + f <= LENGTH t.stack /\ 8 <= dimindex (:'a) /\
    (LENGTH (write_bitmap names k f': 'a word list) + f' = f) /\
    (if f' = 0 then f = 0 else f = f' + f' DIV (dimindex (:'a) - 1) + 1) /\
    (1 <= f) ==>
    read_bitmap
      (list_LUPDATE (MAP Word (write_bitmap (names:num_set) k f')) 0
         (DROP t.stack_space t.stack)) =
    SOME (GENLIST (\x. MEM x (MAP (\(r,y). (f'-1) - (r DIV 2 - k)) (toAList names))) f',
          MAP Word (write_bitmap names k f'): 'a word_loc list,
          (DROP (f - f') (DROP t.stack_space t.stack)))``,
  fs [write_bitmap_def,LET_DEF]
  \\ Q.ABBREV_TAC `qs = GENLIST
           (\x. MEM x (MAP (\(r,y). (f'-1) - (r DIV 2 -k) ) (toAList names))) f'`
  \\ rpt strip_tac
  \\ `t.stack_space + (f - f') + f' <= LENGTH t.stack` by
    (`f <> 0` by decide_tac \\ fs [] \\ decide_tac)
  \\ imp_res_tac APPEND_LEMMA
  \\ fs [DROP_LENGTH_APPEND]
  \\ `LENGTH (MAP Word (word_list (qs ++ [T]) (dimindex (:'a) - 1) :'a word list)) =
      LENGTH xs2` by (fs [] \\ decide_tac)
  \\ imp_res_tac list_LUPDATE_APPEND \\ fs [read_bitmap_word_list])
  |> INST_TYPE [beta|->``:'ffi``];

(*
val join_stacks_IMP_LENGTH = prove(
  ``!s aa joined.
      join_stacks s aa = SOME joined ==> (LENGTH joined = LENGTH s)``,
  recInduct (theorem "join_stacks_ind")
  \\ fs [join_stacks_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []);
*)
val abs_stack_IMP_LENGTH = prove(
  ``∀wstack sstack stack.
    abs_stack wstack sstack = SOME stack ⇒ LENGTH stack = LENGTH wstack``,
  recInduct (theorem "abs_stack_ind")
  \\ fs [abs_stack_def,LET_THM] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw [])

val IMP_filter_bitmap_EQ_SOME_NIL = prove(
  ``!xs ys zs.
      (LENGTH xs = LENGTH ys) /\
      zs = MAP FST (FILTER SND (ZIP (ys, xs))) ==>
      (filter_bitmap xs ys = SOME (zs,[]))``,
  Induct \\ Cases_on `ys` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def]);

val LENGTH_index_list = prove(
  ``!l n. LENGTH (index_list l n) = LENGTH l``,
  Induct \\ fs [index_list_def]);

val SORTED_FST_LESS_IMP = prove(
  ``!xs x.
      SORTED (\x y. FST x > FST y:num) (x::xs) ==>
      SORTED (\x y. FST x > FST y) xs /\ ~(MEM x xs) /\
      (!y. MEM y xs ==> FST x > FST y)``,
  Induct \\ fs [SORTED_DEF]
  \\ ntac 3 strip_tac \\ res_tac \\ rpt strip_tac
  \\ rw [] \\ fs [] \\ res_tac \\ decide_tac);

val SORTED_IMP_EQ_LISTS = prove(
  ``!xs ys.
      SORTED (\x y. FST x > FST y:num) ys /\
      SORTED (\x y. FST x > FST y) xs /\
      (!x. MEM x ys <=> MEM x xs) ==>
      (xs = ys)``,
  Induct \\ fs [] \\ Cases_on `ys` \\ fs [] THEN1 metis_tac []
  THEN1 (CCONTR_TAC THEN fs [] THEN metis_tac [])
  \\ ntac 2 strip_tac
  \\ Cases_on `h = h'` \\ fs [] THEN1
   (first_x_assum match_mp_tac
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ metis_tac [])
  \\ Cases_on `FST h > FST h'`
  THEN1
   (first_assum (mp_tac o Q.SPEC `h`)
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ rpt strip_tac \\ fs [] \\ fs []
    \\ res_tac \\ decide_tac)
  THEN1
   (first_assum (mp_tac o Q.SPEC `h'`)
    \\ imp_res_tac SORTED_FST_LESS_IMP
    \\ rpt strip_tac \\ fs [] \\ fs []));

val transitive_key_val_compare = Q.store_thm("transitive_key_val_compare",
  `transitive key_val_compare`,
  fs[transitive_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ imp_res_tac WORD_LESS_EQ_TRANS \\ fs [])

val total_key_val_compare = Q.store_thm("total_key_val_compare",
  `total key_val_compare`,
  fs[total_def,key_val_compare_def,FORALL_PROD,LET_DEF]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ TRY decide_tac
  \\ CCONTR_TAC \\ fs [] \\ TRY decide_tac
  \\ fs [GSYM WORD_NOT_LESS]
  \\ wordsLib.WORD_DECIDE_TAC)

val SORTS_QSORT_key_val_compare = prove(
  ``SORTS QSORT key_val_compare``,
  match_mp_tac QSORT_SORTS >>
  MATCH_ACCEPT_TAC (CONJ transitive_key_val_compare total_key_val_compare))

val MEM_QSORT = SORTS_QSORT_key_val_compare
  |> SIMP_RULE std_ss [SORTS_DEF]
  |> SPEC_ALL |> CONJUNCT1
  |> MATCH_MP MEM_PERM |> GSYM |> GEN_ALL

val EL_index_list = prove(
  ``!xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = (k + LENGTH xs - i - 1, EL i xs))``,
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac);

val EL_index_list2 = prove(``
 ∀xs i. i < LENGTH xs ==>
           (EL i (index_list xs k) = (k + LENGTH xs - (i+1), EL i xs))``,
  Induct \\ fs [index_list_def]
  \\ rpt strip_tac \\ Cases_on `i` \\ fs [] \\ decide_tac);

val SORTED_weaken2 = Q.prove(`
  ∀ls. SORTED R ls ∧
  ALL_DISTINCT ls ∧
  (∀x y. MEM x ls ∧ MEM y ls ∧ x ≠ y ∧ R x y ⇒ R' x y) ⇒
  SORTED R' ls`,
  Induct>>rw[]>>Cases_on`ls`>>fs[SORTED_DEF]>>
  metis_tac[])

val EVEN_GT = prove(``
  ∀a b.
  EVEN a ∧ EVEN b ∧
  a > b ⇒
  a DIV 2 > b DIV 2``,
  fs[EVEN_EXISTS]>>rw[]>>
  fs[MULT_DIV,MULT_COMM]>>
  DECIDE_TAC)

val transitive_GT = prove(``
  transitive ($> : (num->num->bool))``,
  fs[transitive_def]>>DECIDE_TAC)

val env_to_list_K_I_IMP = prove(
  ``!env l oracle.
      env_to_list env (K I) = (l,oracle) ==>
      SORTED (\x y. FST x > FST y) l /\ oracle = K I /\ PERM (toAList env) l``,
  fs [env_to_list_def,LET_DEF,FUN_EQ_THM,list_rearrange_I] \\ rw []
  \\ pop_assum kall_tac
  \\ qspec_then `toAList env` mp_tac (SORTS_QSORT_key_val_compare
        |> REWRITE_RULE [SORTS_DEF])
  \\ Q.SPEC_TAC (`QSORT key_val_compare (toAList env)`,`l`) \\ rw []
  \\ `PERM (MAP FST (toAList env)) (MAP FST l)` by (match_mp_tac PERM_MAP \\ fs [])
  \\ `ALL_DISTINCT (MAP FST l)` by metis_tac [ALL_DISTINCT_MAP_FST_toAList,
         sortingTheory.ALL_DISTINCT_PERM]
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ Induct_on `l` \\ fs []
  \\ Cases_on `l` \\ fs [SORTED_DEF] \\ rw []
  \\ res_tac \\ fs [key_val_compare_def,LET_DEF]
  \\ split_pair_tac \\ fs [] \\ split_pair_tac \\ fs [])

val evaluate_wLive = Q.prove(
  `(∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
   state_rel k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f /\
   (cut_env names s.locals = SOME env) ==>
   ?t5. (evaluate (wLive names (k,f,f'),t) = (NONE,t5)) /\
        state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 /\
        state_rel k f f' s t5 /\
        !i. i < k ==> get_var i t5 = get_var i t`,
  fs [wLive_def] \\ rpt strip_tac
  \\ mp_tac LENGTH_write_bitmap \\ fs [] \\ rpt strip_tac
  \\ mp_tac evaluate_wLiveAux
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (imp_res_tac LENGTH_write_bitmap \\ pop_assum (K all_tac)
    \\ fs [state_rel_def,GSYM LENGTH_NIL]
    \\ `f <> 0:num` by decide_tac
    \\ fs [] \\ rfs[] \\ decide_tac)
  \\ rpt strip_tac \\ fs [] \\ pop_assum (K all_tac)
  \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,
         DECIDE ``i < k ==> i <> k:num``]
  \\ imp_res_tac LENGTH_write_bitmap \\ pop_assum (K all_tac)
  \\ fs [push_env_def,LET_DEF,state_rel_def,env_to_list_def,FUN_EQ_THM,
         FLOOKUP_UPDATE,DECIDE ``i < k ==> i <> k:num``]
  \\ `t.stack_space <= LENGTH t.stack` by decide_tac \\ fs [lookup_def]
  \\ fs [DROP_list_LUPDATE_lemma]
  \\ reverse (rpt strip_tac)
  THEN1
   (res_tac \\ rw [] \\ fs []
    \\ qpat_assum `xx = SOME v` (fn th => once_rewrite_tac [GSYM th])
    \\ match_mp_tac el_opt_list_LUPDATE_IGNORE \\ fs []
    \\ decide_tac)
  THEN1
   (qpat_assum `stack_rel k s.handler s.stack xx yy tt` mp_tac
    \\ match_mp_tac (METIS_PROVE [] ``(b1 = b2) ==> (b1 ==> b2)``)
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ match_mp_tac (GSYM DROP_list_LUPDATE_IGNORE)
    \\ fs [] \\ decide_tac)
  \\ fs [stack_rel_def,stack_rel_aux_def,abs_stack_def]
  \\ fs [list_LUPDATE_write_bitmap_NOT_NIL]
  \\ mp_tac read_bitmap_write_bitmap \\ fs []
  \\ rpt strip_tac \\ pop_assum (K all_tac)
  THEN1 DECIDE_TAC
  THEN1
   (mp_tac (Q.SPEC `env` env_to_list_K_I_IMP)
    \\ fs [env_to_list_def,sorted_env_def,LET_DEF] \\ rw []
    \\ `s.permute 0 = I` by fs [FUN_EQ_THM] \\ fs [])
  \\ `f' + (f - f') + t.stack_space = f + t.stack_space` by decide_tac
  \\ fs [DROP_DROP_EQ,LET_DEF]
  \\ `~(LENGTH t.stack <= t.stack_space) /\
      ~(LENGTH t.stack < t.stack_space + (f - f' + f'))` by decide_tac
  \\ fs [stack_rel_aux_def]
  \\ `(s.handler+1) <= SUC (LENGTH s.stack)` by decide_tac
  \\ `s.permute 0 = I` by fs [FUN_EQ_THM] \\ fs [list_rearrange_I]
  \\ rpt strip_tac
  THEN1
   (imp_res_tac abs_stack_IMP_LENGTH>>
   simp[LASTN_CONS])
  \\ match_mp_tac IMP_filter_bitmap_EQ_SOME_NIL
  \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ match_mp_tac (METIS_PROVE [] ``b1 /\ (b1 ==> b2) ==> b1 /\ b2``)
  \\ strip_tac THEN1 (fs [LENGTH_index_list,LENGTH_TAKE_EQ,MIN_DEF]
                      \\ decide_tac)
  \\ fs [ZIP_GENLIST] \\ rpt strip_tac \\ pop_assum (K all_tac)
  \\ `!x. MEM x (MAP (\(r,y). f + k - r DIV 2) (toAList names)) <=>
          ?n. x = f + k - n DIV 2 /\ n IN domain env` by
   (fs [MEM_MAP,EXISTS_PROD,MEM_toAList,cut_env_def] \\ rw[]
    \\ fs [lookup_inter_alt,domain_lookup,SUBSET_DEF]
    \\ metis_tac []) \\ fs [] \\ pop_assum (K all_tac)
  \\ `(LENGTH ((write_bitmap names k f'): 'a word list) +
      MIN f' (LENGTH t.stack - (f - f' + t.stack_space))) = f` by
     (fs [MIN_DEF] \\ decide_tac) \\ fs [LENGTH_TAKE_EQ]
  \\ fs [MAP_FST_def,adjust_names_def]
  \\ match_mp_tac SORTED_IMP_EQ_LISTS
  \\ rpt strip_tac
  THEN1 (
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> snd
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    REWRITE_TAC[GSYM inv_image_def] >>
    conj_tac >-(
      match_mp_tac transitive_inv_image >>
      ACCEPT_TAC transitive_GT ) >>
    qmatch_abbrev_tac`SORTED R' (QSORT R ls)` >>
    `SORTED R (QSORT R ls)` by (
      match_mp_tac QSORT_SORTED >>
      metis_tac[transitive_key_val_compare,total_key_val_compare] ) >>
    match_mp_tac SORTED_weaken2>>fs[]>>CONJ_ASM1_TAC
    >-
      metis_tac[ALL_DISTINCT_MAP_FST_toAList,QSORT_PERM,ALL_DISTINCT_PERM,ALL_DISTINCT_MAP]
    >>
      simp[MEM_QSORT,Abbr`R`] >>
      simp[Abbr`R'`,inv_image_def,FORALL_PROD,Abbr`ls`,MEM_toAList] >>
      fs[key_val_compare_def,LET_THM]>>
      `∀p v. lookup p env = SOME v ⇒ lookup p s.locals = SOME v` by
        (fs[cut_env_def]>>qpat_assum`A=env` (SUBST_ALL_TAC o SYM)>>
        fs[lookup_inter_EQ])>>
      rw[]>>fs[]>>res_tac>>res_tac>>
      fs[EVEN_GT])
  THEN1 (
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> snd
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    REWRITE_TAC[GSYM inv_image_def] >>
    conj_tac >-(
      match_mp_tac transitive_inv_image >>
      ACCEPT_TAC transitive_GT ) >>
    match_mp_tac (MP_CANON sorted_filter) >>
    conj_tac >- metis_tac[transitive_inv_image,transitive_GT] >>
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> fst
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    conj_tac >- metis_tac[transitive_inv_image,transitive_GT] >>
    simp[MAP_GENLIST,combinTheory.o_DEF] >>
    (sorted_map |> SPEC_ALL |> UNDISCH |> EQ_IMP_RULE |> fst
     |> DISCH_ALL |> MP_CANON |> match_mp_tac) >>
    conj_tac >- ACCEPT_TAC transitive_GT>>
    simp[MAP_GENLIST,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`SORTED R (GENLIST g m)` >>
    `GENLIST g m = GENLIST (λx. k + m - (x + 1)) m` by (
      simp[LIST_EQ_REWRITE,Abbr`g`] >>
      rw[] >>
      qmatch_abbrev_tac`FST (EL x (index_list ls k)) = Z` >>
      `x < LENGTH ls` by ( simp[Abbr`ls`] ) >>
      asm_simp_tac std_ss [EL_index_list] >>
      simp[Abbr`ls`,Abbr`Z`] ) >>
    pop_assum SUBST1_TAC >>
    fs[Abbr`R`]>>
    fs[SORTED_EL_SUC]>>rw[]>>`n < m` by DECIDE_TAC>>
    fs[EL_GENLIST]>>DECIDE_TAC)
  >>
  qpat_abbrev_tac `f'' = f- f' + t.stack_space`>>
  `f' ≤ LENGTH t.stack - f''` by (rw[Abbr`f''`]>>DECIDE_TAC)>>
  `MIN f' (LENGTH t.stack - f'') = f'` by
    (fs[MIN_DEF]>>rw[]>>
    ntac 2 (pop_assum mp_tac)>>
    rpt (pop_assum kall_tac)>>
    DECIDE_TAC)
  \\ fs [MEM_MAP,MEM_FILTER,MEM_GENLIST,PULL_EXISTS,MEM_QSORT,EXISTS_PROD,
      MEM_toAList,cut_env_def] \\ rw [lookup_inter_alt,domain_inter]
  \\ Cases_on `x` \\ fs [GSYM CONJ_ASSOC,LENGTH_write_bitmap] \\
  `0 < f'` by
    (CCONTR_TAC>>`f' = 0` by DECIDE_TAC>>fs[]>>
    DECIDE_TAC)>>
  eq_tac>>rw[]
  >-
    (fs[domain_lookup]>>
    res_tac>>
    `¬ (p_1 DIV 2 < k)` by DECIDE_TAC>>
    HINT_EXISTS_TAC>>fs[]>>
    qabbrev_tac `rn = p_1 DIV 2 -k`>>
    `rn < f'` by fs[Abbr`rn`]>>
    `f' -1 - rn < f'` by DECIDE_TAC>>
    fs[EL_index_list2]>>
    `rn + k  = k +f' - (f' - 1 - rn +1)` by DECIDE_TAC>>
    pop_assum (SUBST_ALL_TAC o SYM)>>
    CONJ_TAC>-
      (fs[Abbr`rn`]>>
      DECIDE_TAC)
    >>
    fs[el_opt_THM,EL_TAKE]>>
    qpat_assum`A=r` (SUBST_ALL_TAC o SYM)>>
    qpat_abbrev_tac`f = LENGTH A + f'`>>
    `f - 1 - rn < f` by DECIDE_TAC>>
    fs[EL_TAKE]>>
    `f -1 - rn + t.stack_space < LENGTH t.stack` by
       DECIDE_TAC>>
    `f' -1 -rn + f'' = f-1 -rn + t.stack_space` by
      (fs[Abbr`f''`,Abbr`f`]>>
      qpat_abbrev_tac `len = LENGTH A`>>
      qpat_abbrev_tac `rnn = f' -1 - rn`>>
      `len + f' - 1 -rn = len + rnn` by
        (fs[Abbr`rnn`]>>
        fs[SUB_RIGHT_SUB]>>
        DECIDE_TAC)>>
      fs[]>>
      DECIDE_TAC)>>
    fs[EL_DROP])
  >>
    `p_1' ∈ domain s.locals` by metis_tac[SUBSET_DEF,domain_lookup]>>
    fs[domain_lookup]>>
    res_tac>>
    `¬ (p_1' DIV 2 < k)` by DECIDE_TAC>>
    HINT_EXISTS_TAC>>fs[]>>
    qabbrev_tac `rn = p_1' DIV 2 -k`>>
    `rn < f'` by fs[Abbr`rn`]>>
    rfs[EL_index_list2]>>
    CONJ_TAC>-
      (fs[SUB_RIGHT_SUB]>>
      `f' - (1 + rn) +1 = f' - rn` by DECIDE_TAC>>
      fs[]>>pop_assum kall_tac>>
      `k + f' - (f' - rn) = k + rn` by DECIDE_TAC>>
      fs[Abbr`rn`]>>pop_assum kall_tac>>
      `k ≤ p_1' DIV 2` by DECIDE_TAC>>
      DECIDE_TAC)
    >>
    fs[el_opt_THM]>>qpat_assum`A=v` (SUBST_ALL_TAC o SYM)>>
    qpat_abbrev_tac`f = LENGTH A + f'`>>
    `f -1 - rn < f` by DECIDE_TAC>>
    fs[EL_TAKE]>>
    `f - 1 - rn + t.stack_space < LENGTH t.stack` by DECIDE_TAC>>
    `f' -1 -rn + f'' = f-1 -rn + t.stack_space` by
      (fs[Abbr`f''`,Abbr`f`]>>
      qpat_abbrev_tac `len = LENGTH A`>>
      qpat_abbrev_tac `rnn = f' -1 - rn`>>
      `len + f' - 1 -rn = len + rnn` by
        (fs[Abbr`rnn`]>>
        fs[SUB_RIGHT_SUB]>>
        fs[SUB_LEFT_ADD]>>
        IF_CASES_TAC>>fs[]>>
        `f' = 1 + rn` by DECIDE_TAC>>
        pop_assum (SUBST_ALL_TAC o SYM)>>
        fs[ADD_SUB])>>
      fs[]>>
      DECIDE_TAC)>>
    fs[EL_DROP])

val push_env_set_store = prove(
  ``push_env env ^nn (set_store AllocSize (Word c) s) =
    set_store AllocSize (Word c) (push_env env ^nn s)``,
  fs [push_env_def,set_store_def,env_to_list_def,LET_DEF])|> INST_TYPE [beta|-> alpha, gamma|->beta];

val state_rel_set_store = prove(
  ``state_rel k 0 0 s5 t5 ==>
    state_rel k 0 0 (set_store AllocSize w s5) (set_store AllocSize w t5)``,
  rpt strip_tac
  \\ `Handler IN FDOM t5.store` by
   (fs [state_rel_def] \\ Cases_on `FLOOKUP t5.store Handler`
    \\ fs [stack_rel_def,LET_DEF,FLOOKUP_DEF])
  \\ fs [state_rel_def,set_store_def,stackSemTheory.set_store_def,LET_DEF,
         FLOOKUP_DEF] \\ REPEAT STRIP_TAC \\ rfs[]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ fs [fmap_EXT,DRESTRICT_DEF,EXTENSION]
  \\ rpt strip_tac  THEN1 (Cases_on `x = Handler` \\ fs [])
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]);

val filter_bitmap_IMP_MAP_SND = prove(
  ``!ys xs l.
      filter_bitmap ys xs = SOME (l,[]) ==>
      filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])``,
  Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []);

val MAP_SND_index_list = prove(
  ``!xs k. MAP SND (index_list xs k) = xs``,
  Induct \\ fs [index_list_def]);

val filter_bitmap_TAKE_LENGTH_IMP = prove(
  ``!h5 x4 l.
      filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[]) ==>
      filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)``,
  Induct \\ Cases_on `x4` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ Cases_on `l` \\ fs [] \\ rw [] \\ res_tac \\ fs []);

val filter_bitmap_lemma = prove(
  ``filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[]) ==>
    filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4)``,
  rpt strip_tac \\ imp_res_tac filter_bitmap_IMP_MAP_SND
  \\ fs [MAP_SND_index_list] \\ imp_res_tac filter_bitmap_TAKE_LENGTH_IMP);

val MAP_SND_MAP_FST = prove(
  ``!xs f. MAP SND (MAP_FST f xs) = MAP SND xs``,
  Induct \\ fs [MAP,MAP_FST_def,FORALL_PROD]);

val read_bitmap_not_empty = prove(``
  read_bitmap stack = SOME a ⇒
  stack ≠ []``,
  rw[]>>CCONTR_TAC>>
  fs[]>>
  fs[read_bitmap_def])

val n2w_lsr_1 = prove(
  ``n < dimword (:'a) ==> n2w n >>> 1 = (n2w (n DIV 2)):'a word``,
  once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr] \\ fs []
  \\ fs [DIV_LT_X] \\ decide_tac);

val handler_bitmap_props = prove(``
  good_dimindex(:'a) ⇒
  read_bitmap (Word (4w:'a word)::stack) =
  SOME ([F;F],[Word 4w],stack)``,
  fs [read_bitmap_def,good_dimindex_def] \\ strip_tac
  \\ `~(word_msb 4w)` by fs [word_msb_def,wordsTheory.word_index] \\ fs []
  \\ `4 < dimword (:'a) /\ 2 < dimword (:'a)` by fs [dimword_def]
  \\ `bit_length 4w = 3` by
   (NTAC 4 (fs [dimword_def,Once bit_length_def,n2w_lsr_1,EVAL ``1w ⋙ 1``]))
  \\ fs [] \\ EVAL_TAC \\ rw [] \\ decide_tac)

val enc_stack_lemma = prove(
  ``∀(wstack:'a stack_frame list) sstack astack.
      good_dimindex(:'a) ∧
      abs_stack wstack sstack = SOME astack ∧
      stack_rel_aux k len wstack astack ⇒
      enc_stack sstack = SOME (enc_stack wstack)``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  fs[enc_stack_def]>>
  rw[]>>
  fs[Once stackSemTheory.enc_stack_def,abs_stack_def]>>
  TRY(qpat_assum`A=SOME stack` mp_tac)>>
  TRY(qpat_assum`A=SOME stack'` mp_tac)>>
  TOP_CASE_TAC>>fs[]
  >-
    (PairCases_on`x`>>fs[read_bitmap_not_empty,LET_THM]>>
    TOP_CASE_TAC>>strip_tac>>
    pop_assum (assume_tac o SYM)>>
    fs[stack_rel_aux_def]>>
    imp_res_tac filter_bitmap_lemma>>
    fs[]>>rfs[]>>
    qpat_assum`A=SOME(enc_stack wstack)` mp_tac>>
    IF_CASES_TAC
    >-
      fs[Once stackSemTheory.enc_stack_def,MAP_SND_MAP_FST]
    >>
    ntac 6 TOP_CASE_TAC>>fs[]>>
    simp[Once stackSemTheory.enc_stack_def,MAP_SND_MAP_FST])
  >>
    (ntac 3 TOP_CASE_TAC>>fs[]>>
    PairCases_on`x`>>fs[LET_THM,handler_bitmap_props]>>
    simp[filter_bitmap_def]>>
    TOP_CASE_TAC>>
    strip_tac>>pop_assum (assume_tac o SYM)>>
    PairCases_on`sstack`>>
    fs[stack_rel_aux_def]>>
    imp_res_tac filter_bitmap_lemma>>
    fs[]>>rfs[]>>
    simp[Once stackSemTheory.enc_stack_def,read_bitmap_not_empty]>>
    qpat_assum`A=SOME(enc_stack wstack)` mp_tac>>
    IF_CASES_TAC
    >-
      fs[Once stackSemTheory.enc_stack_def,MAP_SND_MAP_FST]
    >>
    ntac 6 TOP_CASE_TAC>>fs[]>>
    simp[Once stackSemTheory.enc_stack_def,MAP_SND_MAP_FST]));

val IMP_enc_stack = prove(
  ``state_rel k 0 0 s1 t1 ==>
    (enc_stack (DROP t1.stack_space t1.stack) = SOME (enc_stack s1.stack))``,
  fs [state_rel_def,LET_DEF] \\ rpt strip_tac
  \\ fs [stack_rel_def] \\ imp_res_tac enc_stack_lemma);

val dec_stack_lemma = prove(
  ``enc_stack (DROP t1.stack_space t1.stack) = SOME (enc_stack s1.stack) /\
    (dec_stack x0 s1.stack = SOME x) /\
    stack_rel k s1.handler s1.stack (SOME (t1.store ' Handler))
      (DROP t1.stack_space t1.stack) (LENGTH t1.stack) /\
    (LENGTH (enc_stack s1.stack) = LENGTH x0) ==>
    ?yy. dec_stack x0 (DROP t1.stack_space t1.stack) = SOME yy /\
         (t1.stack_space + LENGTH yy = LENGTH t1.stack) /\
         stack_rel k s1.handler x (SOME (t1.store ' Handler)) yy
            (LENGTH t1.stack)``,
  cheat) |> INST_TYPE [beta|->``:'ffi``,gamma|->``:'ffi``];

val gc_state_rel = prove(
  ``(gc (s1:('a,'ffi) wordSem$state) = SOME s2) /\ state_rel k 0 0 s1 t1 /\ (s1.locals = LN) ==>
    ?t2. gc t1 = SOME t2 /\ state_rel k 0 0 s2 t2``,
  fs [gc_def,LET_DEF]
  \\ Cases_on `s1.gc_fun (enc_stack s1.stack,s1.memory,s1.mdomain,s1.store)` \\ fs []
  \\ PairCases_on `x` \\ fs [] \\ Cases_on `dec_stack x0 s1.stack` \\ fs []
  \\ rw [] \\ fs [stackSemTheory.gc_def]
  \\ `~(LENGTH t1.stack < t1.stack_space)` by
         (fs [state_rel_def] \\ decide_tac)
  \\ imp_res_tac IMP_enc_stack \\ fs [LET_DEF]
  \\ `t1.memory = s1.memory /\ t1.mdomain = s1.mdomain /\
      t1.gc_fun = s1.gc_fun /\ gc_fun_ok s1.gc_fun` by fs [state_rel_def] \\ fs []
  \\ `s1.store = t1.store \\ Handler /\ Handler IN FDOM t1.store` by
   (fs [state_rel_def] \\ Cases_on `FLOOKUP t1.store Handler`
    \\ fs [FLOOKUP_DEF,stack_rel_def,LET_DEF])
  \\ fs [gc_fun_ok_def] \\ res_tac \\ fs []
  \\ mp_tac dec_stack_lemma \\ fs [] \\ rpt strip_tac \\ fs []
  \\ fs [state_rel_def,FLOOKUP_UPDATE,LET_DEF,lookup_def,FLOOKUP_DEF]
  \\ rfs [FLOOKUP_DEF] \\ rw[]
  THEN1 (fs [fmap_EXT,EXTENSION,DOMSUB_FAPPLY_THM] \\ metis_tac [])
  \\ fs [DROP_APPEND,DROP_TAKE_NIL]);

val alloc_alt = prove(
  ``FST (alloc c names (s:('a,'ffi) wordSem$state)) <> SOME (Error:'a result) ==>
    (alloc c names (s:('a,'ffi) wordSem$state) =
     case cut_env names s.locals of
       NONE => (SOME Error,s)
     | SOME env =>
         case gc (set_store AllocSize (Word c)
                    (push_env env ^nn s with locals := LN)) of
           NONE => (SOME Error,s)
         | SOME s' =>
             case pop_env s' of
               NONE => (SOME (Error:'a result),s')
             | SOME s' =>
                 case FLOOKUP s'.store AllocSize of
                   NONE => (SOME Error,s')
                 | SOME w =>
                     case has_space w s' of
                       NONE => (SOME Error,s')
                     | SOME T => (NONE,s')
                     | SOME F =>
                         (SOME NotEnoughSpace,
                          call_env [] s' with stack := []))``,
  fs [alloc_def]
  \\ Cases_on `cut_env names s.locals` \\ fs []
  \\ fs [gc_def,set_store_def,push_env_def,LET_DEF,
         env_to_list_def,pop_env_def]
  \\ BasicProvers.EVERY_CASE_TAC
   \\ fs [state_component_equality] \\ rw []
   \\ fs [state_component_equality] \\ rw []);

val read_bitmap_split = prove(``
  ∀ls a b c.
  read_bitmap ls = SOME(a,b,c) ⇒
  ls = b++c``,
  Induct>>rw[]>>TRY(Cases_on`h`)>>fs[read_bitmap_def]>>
  pop_assum mp_tac>>EVERY_CASE_TAC>>fs[])

val read_bitmap_replace = prove(``
  ∀ls a b c.
  read_bitmap ls = SOME (a,b,c) ⇒
  ∀ls'.
  read_bitmap (b++ls') = SOME (a,b,ls')``,
  ho_match_mp_tac read_bitmap_ind>>rw[]>>fs[read_bitmap_def]>>
  pop_assum mp_tac>> EVERY_CASE_TAC>>fs[read_bitmap_def]>>rw[]>>
  fs[read_bitmap_def])

val map_bitmap_remainder = prove(``
  ∀a b c d e.
  map_bitmap a b c = SOME (d,e) ⇒
  e = DROP (LENGTH a) c``,
  ho_match_mp_tac map_bitmap_ind>>rw[map_bitmap_def]>>
  pop_assum mp_tac >> EVERY_CASE_TAC>>fs[])

val map_bitmap_length = prove(``
  ∀a b c x y.
  map_bitmap a b c = SOME(x,y) ⇒
  LENGTH c = LENGTH x + LENGTH y ∧
  LENGTH x = LENGTH a``,
  Induct>>rw[]>>
  Cases_on`b`>>TRY(Cases_on`h`)>>Cases_on`c`>>
  fs[map_bitmap_def]>>
  TRY(qpat_assum`A=x` (SUBST_ALL_TAC o SYM))>>
  TRY(qpat_assum`A=y` (SUBST_ALL_TAC o SYM))>>
  fs[LENGTH_NIL]>>
  pop_assum mp_tac>>EVERY_CASE_TAC>>rw[]>>res_tac>>
  fs[]>>DECIDE_TAC)

val dec_stack_length = prove(``
  ∀enc orig_stack new_stack.
  dec_stack enc orig_stack = SOME new_stack ⇒
  LENGTH orig_stack = LENGTH new_stack``,
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  fs[stackSemTheory.dec_stack_def,LENGTH_NIL]>>rw[]>>
  pop_assum mp_tac>>EVERY_CASE_TAC>>fs[]>>
  rw [] \\ fs [] \\ cheat)

(*TODO: abs_stack changed
val dec_stack_LIST_REL = prove(``
  ∀enc orig_stack new_stack abs_orig abs_new.
  stackSem$dec_stack enc orig_stack = SOME new_stack ∧
  abs_stack orig_stack = SOME abs_orig
  ⇒
  ∃abs_new.
  abs_stack new_stack = SOME abs_new ∧
  LIST_REL (λ(a,b,c) (x,y,z). a = x ∧ b = y ∧ LENGTH c = LENGTH z) abs_orig abs_new``,
  cheat (*
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  rw[stackSemTheory.dec_stack_def]>>
  pop_assum mp_tac>> simp[Once abs_stack_def]>>
  Cases_on`orig_stack = [Word 0w]`>>fs[read_bitmap_def]
  >-
    (fs[Once bit_length_def]>>Cases_on`ts`>>fs[map_bitmap_def]>>
    Cases_on`enc`>>fs[stackSemTheory.dec_stack_def,read_bitmap_def]>>
    qpat_assum`A=new_stack` (SUBST_ALL_TAC o SYM)>>
    fs[Once abs_stack_def]>>rw[]>>
    match_mp_tac quotient_listTheory.LIST_REL_REFL>>
    fs[FORALL_PROD,FUN_EQ_THM]>>metis_tac[])
  >>
    qpat_assum`A = SOME new_stack` mp_tac>>
    ntac 6 FULL_CASE_TAC>>
    fs[]>>
    imp_res_tac map_bitmap_remainder>>
    FULL_CASE_TAC>>fs[]>>rw[]>>
    qabbrev_tac`ls = q'++q''++x`>>
    simp[Once abs_stack_def]>>
    `ls ≠ [] ∧ ls ≠ [Word 0w]` by cheat>>
    imp_res_tac read_bitmap_replace>>
    pop_assum(qspec_then`q''++x` assume_tac)>>fs[]>>
    rfs[]>>
    imp_res_tac map_bitmap_length>>
    pop_assum(SUBST_ALL_TAC o SYM)>>
    fs[DROP_LENGTH_APPEND]>>
    DECIDE_TAC *))

val gc_stack_shape = prove(``
  gc s = SOME s' ∧
  abs_stack (DROP s.stack_space s.stack) = SOME as
  ⇒
  s.stack_space = s'.stack_space ∧
  LENGTH s.stack = LENGTH s'.stack ∧
  ∃as'.
  abs_stack (DROP s.stack_space s'.stack) = SOME as' ∧
  LIST_REL (λ(a,b,c) (x,y,z). a = x ∧ b = y ∧ LENGTH c = LENGTH z) as as'``,
  fs[stackSemTheory.gc_def,LET_THM]>>
  EVERY_CASE_TAC>>rw[]>>
  `s.stack_space ≤ LENGTH s.stack` by DECIDE_TAC>>
  fs[DROP_TAKE_NIL,DROP_APPEND1]
  >-
    (imp_res_tac dec_stack_length>>fs[]>>DECIDE_TAC)
  >>
  metis_tac[dec_stack_LIST_REL,dec_stack_length])

(*Will need a version of this for SOME ... cases*)
val joined_ok_drop = prove(``
  abs_stack ls = SOME x ∧
  ls ≠ [] ∧ ls ≠ [Word 0w] ∧
  read_bitmap ls = SOME (names, bmap , rest) ∧
  join_stacks (StackFrame l NONE::s3.stack) x = SOME j ∧
  joined_ok k j len ⇒
  ∃y j'.
  abs_stack (DROP (LENGTH names) (DROP (LENGTH bmap) ls)) = SOME y ∧
  join_stacks s3.stack y = SOME j' ∧
  joined_ok k j' len
  ``,
  simp[Once abs_stack_def,LET_THM]>>rw[]>>
  qpat_assum`A=SOME x` mp_tac>>
  ntac 2 FULL_CASE_TAC>>rw[]>>fs[]>>
  imp_res_tac read_bitmap_split>>
  fs[DROP_LENGTH_APPEND,join_stacks_def]>>
  qpat_assum`A=SOME j` mp_tac>>FULL_CASE_TAC>>rw[]>>
  fs[joined_ok_def])
*)

(*TODO: Needs updating for new stack_rel*)
val alloc_IMP_alloc = prove(
  ``(wordSem$alloc c names (s:('a,'ffi) wordSem$state) = (res:'a result option,s1)) /\
    (∀x. x ∈ domain names ⇒ EVEN x /\ k ≤ x DIV 2) /\
    state_rel k f f' s t5 /\
    state_rel k 0 0 (push_env env ^nn s with locals := LN) t5 /\
    (cut_env names s.locals = SOME env) /\
    read_bitmap (DROP t5.stack_space t5.stack) =
    SOME
    (GENLIST (λx.MEM x (MAP (λ(r,y). f' − 1 − (r DIV 2 − k)) (toAList names))) f'
    ,MAP Word (write_bitmap names k f')
    ,DROP (f − f') (DROP t5.stack_space t5.stack)) /\
    res <> SOME Error ==>
    ?t1 res1.
      (stackSem$alloc c t5 = (res1:'a stackSem$result option,t1)) /\
      if res = NONE then
        res1 = NONE /\ state_rel k f f' s1 t1
      else
        res = SOME NotEnoughSpace /\ res1 = SOME (Halt (Word 1w)) /\
        s1.clock = t1.clock /\ s1.ffi = t1.ffi``,
  Cases_on `FST (alloc c names (s:('a,'ffi) wordSem$state)) = SOME (Error:'a result)`
  THEN1 (rpt strip_tac \\ fs [] \\ rfs [])
  \\ fs [alloc_alt, stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fs [push_env_set_store]
  \\ imp_res_tac state_rel_set_store
  \\ pop_assum (mp_tac o Q.SPEC `Word c`) \\ REPEAT STRIP_TAC
  \\ Cases_on `gc (set_store AllocSize (Word c)
                     (push_env env ^nn s with locals := LN))`
  \\ fs [] \\ imp_res_tac gc_state_rel \\ NTAC 3 (POP_ASSUM (K ALL_TAC)) \\ fs []
  \\ pop_assum mp_tac \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [set_store_def,push_env_def]) \\ rpt strip_tac
  \\ fs [] \\ Cases_on `pop_env x` \\ fs []
  \\ Q.MATCH_ASSUM_RENAME_TAC `pop_env s2 = SOME s3`
  \\ `state_rel k f f' s3 t2` by ALL_TAC
  THEN1
    cheat
    (*imp_res_tac gc_s_key_eq>>
    fs[set_store_def]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    imp_res_tac gc_frame>>
    fs[pop_env_def,push_env_def,env_to_list_def,LET_THM]>>
    `opt = NONE` by
      Cases_on`opt`>>fs[s_key_eq_def,s_frame_key_eq_def]>>
    rfs[]>>
    fs[state_rel_def,set_store_def,wordSemTheory.state_component_equality,stackSemTheory.set_store_def,LET_THM]>>
    fs[stack_rel_def]>>
    imp_res_tac gc_stack_shape>>
    fs[]>>ntac 7 (pop_assum kall_tac)>>rfs[]>>
    CONJ_TAC>-
      (qpat_assum`A=SOME aa'''` mp_tac>>
      qpat_abbrev_tac`lss = DROP t2.stack_space t2.stack`>>
      `lss ≠ [] ∧ lss ≠ [Word 0w]` by cheat>>
      simp[Once abs_stack_def]>>
      ntac 4 FULL_CASE_TAC>>fs[]>>strip_tac>>
      qpat_assum`join_stacks A aa''' = B` mp_tac>>
      qpat_assum`joined_ok k joined''' A` mp_tac>>
      pop_assum (mp_tac o SYM)>>
      simp[join_stacks_def]>>
      FULL_CASE_TAC>>fs[]>>rw[]>>
      imp_res_tac read_bitmap_split>>fs[]>>cheat)
      (*need something else to allow dropping a stack frame*)
    >>
    qpat_assum`A = SOME joined'''` mp_tac>>
    Cases_on`aa'''`>>fs[join_stacks_def]>>
    FULL_CASE_TAC>>fs[]>>
    disch_then (assume_tac o SYM)>>
    qpat_assum`joined_ok A B C` mp_tac>>
    PairCases_on`h`>>simp[joined_ok_def]>>
    cheat*)
      (* continue here --
        need to prove that gc doesn't change the shape of the
        stack frame (stackSem) or the var names in env (wordSem) *)
  \\ Cases_on `FLOOKUP s3.store AllocSize` \\ fs []
  \\ Cases_on `has_space x s3` \\ fs []
  \\ `s3.store SUBMAP t2.store` by
    (fs [state_rel_def,SUBMAP_DEF,DOMSUB_FAPPLY_THM] \\ NO_TAC)
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ fs [has_space_def,stackSemTheory.has_space_def]
  \\ EVERY_CASE_TAC
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs [] \\ rw [] \\ fs []
  \\ fs [state_rel_def]);

val get_var_set_var = prove(``
  stackSem$get_var k (set_var k v st) = SOME v``,
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def]>>
  fs[FLOOKUP_UPDATE])

val compile_result_def = Define`
  (compile_result (Result w1 w2) = Result w1) ∧
  (compile_result (Exception w1 w2) = Exception w1) ∧
  (compile_result TimeOut = TimeOut) ∧
  (compile_result NotEnoughSpace = Halt (Word 1w)) ∧
  (compile_result Error = Error)`;
val _ = export_rewrites["compile_result_def"];

val Halt_EQ_compile_result = prove(
  ``(Halt (Word 1w) = compile_result z <=> z = NotEnoughSpace) /\
    (good_dimindex (:'a) ==> Halt (Word (2w:'a word)) <> compile_result z)``,
  Cases_on `z` \\ fs [] \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def]);

val stack_evaluate_add_clock_NONE =
  stackPropsTheory.evaluate_add_clock
  |> Q.SPECL [`p`,`s`,`NONE`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL

val push_locals_def = Define `
  push_locals s = s with <| locals := LN;
    stack := StackFrame (FST (env_to_list s.locals (K I))) NONE :: s.stack |>`

val abs_stack_empty = prove(``
  ∀ls stack.
  abs_stack [] ls = SOME stack ⇒ ls = [Word 0w]``,
  Cases>>fs[abs_stack_def]>>
  Cases_on`h`>>fs[abs_stack_def]>>FULL_CASE_TAC>>fs[])

val LASTN_LENGTH_ID2 = prove(``
  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack``,
  fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID])

val stack_rel_aux_LENGTH = prove(``
  ∀k len xs ys.
  stack_rel_aux k len xs ys ⇒
  LENGTH xs = LENGTH ys``,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>fs[stack_rel_aux_def])

val LASTN_MORE = prove(``
  ∀ls n.
  ¬(n < LENGTH ls) ⇒ LASTN n ls = ls``,
  fs[LASTN_def]>>Induct>>rw[]>>
  Cases_on`n < LENGTH ls`>>
  fs[TAKE_APPEND1,LENGTH_REVERSE]
  >-
    `¬(n < (LENGTH ls))` by DECIDE_TAC
  >>
    res_tac>>
    fs[TAKE_APPEND]>>
    IF_CASES_TAC>>fs[]>>
    DECIDE_TAC)

val stack_rel_aux_LASTN = prove(``
  ∀k len xs ys n.
  stack_rel_aux k len xs ys ⇒
  stack_rel_aux k len (LASTN n xs) (LASTN n ys)``,
  ho_match_mp_tac (theorem "stack_rel_aux_ind")>>
  fs[stack_rel_aux_def]>>rw[]>>
  imp_res_tac stack_rel_aux_LENGTH
  >-
    fs[LASTN_def,stack_rel_aux_def]
  >>
    Cases_on`n ≤ LENGTH xs`>>rfs[LASTN_CONS]>>
    `¬(n < SUC(LENGTH ys))` by DECIDE_TAC>>
    fs[LASTN_MORE,stack_rel_aux_def])

val abs_stack_to_stack_LENGTH = prove(``
  ∀wstack sstack stack.
  abs_stack wstack sstack = SOME stack ⇒
  handler_val stack = LENGTH sstack``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
  fs[abs_stack_def,LET_THM]
  >-
    (pop_assum sym_sub_tac>>fs[handler_val_def])
  >-
    (qpat_assum`A=SOME stack` mp_tac>>
    TOP_CASE_TAC>>rw[]>>fs[handler_val_def])
  >-
    (pop_assum mp_tac>>
    ntac 5 TOP_CASE_TAC>>rw[]>>rfs[]>>
    fs[handler_val_def]>>
    `LENGTH q ≤ LENGTH r'` by DECIDE_TAC>>
    fs[LENGTH_TAKE]>>
    imp_res_tac read_bitmap_split>>
    fs[]>>
    DECIDE_TAC)
  >>
    (pop_assum mp_tac>>
    ntac 8 TOP_CASE_TAC>>rw[]>>rfs[]>>
    fs[handler_val_def]>>
    `LENGTH q ≤ LENGTH r'` by DECIDE_TAC>>
    fs[LENGTH_TAKE]>>
    imp_res_tac read_bitmap_split>>
    fs[]>>
    DECIDE_TAC))

(*Equality theorems available if n ≤ LENGTH ls*)
val LASTN_LENGTH_BOUNDS = prove(``
  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls``,
  fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]>>rw[]>>
  decide_tac)

val LASTN_CONS_ID = prove(``
  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)``,
  rw[]>>EVAL_TAC>>fs[])

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
  -- TODO: should use this to simplify the lemma proof
*)
val abs_stack_prefix_drop = prove(``
  ∀wstack sstack stack h wrest k len.
  h ≤ LENGTH wstack ∧
  LASTN h wstack = wrest ∧
  abs_stack wstack sstack = SOME stack ∧
  stack_rel_aux k len wstack stack ⇒
  let rest = LASTN h stack in
  let srest = LASTN (handler_val rest) sstack in
  abs_stack wrest srest = SOME rest ∧
  stack_rel_aux k len wrest rest``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>
  rpt strip_tac>>fs[LET_THM,abs_stack_def]>>
  TRY(TRY(Cases_on`v10`)>>fs[]>>
    qpat_assum`A=stack` sym_sub_tac>>
    fs[LASTN_def,handler_val_def]>>
    qpat_assum`A=wrest` sym_sub_tac>>
    fs[abs_stack_def,handler_val_def])
  >-
    (qpat_assum`A=SOME stack` mp_tac>>
    ntac 5 TOP_CASE_TAC>>fs[]>>disch_then (assume_tac o SYM)>>
    fs[]>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]>>
    imp_res_tac abs_stack_IMP_LENGTH
    >-
      (fs[LASTN_CONS,stack_rel_aux_def]>>
      res_tac>>
      qpat_assum`A=wrest` sym_sub_tac>>fs[]>>
      imp_res_tac read_bitmap_split>>fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_assum`A=SOME(LASTN h x)` sym_sub_tac>>
      AP_TERM_TAC>>
      qpat_abbrev_tac`length = handler_val A`>>
      Q.ISPECL_THEN [`length`,`DROP(LENGTH q)r'`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      `q'++r' = (q'++TAKE (LENGTH q) r')++DROP (LENGTH q) r'` by fs[]>>
      pop_assum SUBST_ALL_TAC>>
      simp[LASTN_APPEND2])
    >>
      qpat_abbrev_tac`frame = (a,b,c,d)`>>
      `h = LENGTH (frame::x)` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      `LASTN (handler_val (frame::x)) sstack = sstack` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac read_bitmap_split>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`frame`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      qpat_assum`A=wrest` sym_sub_tac>>fs[]>>
      fs[Abbr`frame`,abs_stack_def,LET_THM])
  >>
    qpat_assum`A=SOME stack'` mp_tac>>
    ntac 8 TOP_CASE_TAC>>fs[]>>
    disch_then (assume_tac o SYM)>>
    fs[]>>
    Cases_on`h ≤ LENGTH wstack`>>fs[]>>
    imp_res_tac abs_stack_IMP_LENGTH
    >-
      (PairCases_on`sstack`>>fs[LASTN_CONS,stack_rel_aux_def]>>
      res_tac>>
      qpat_assum`A=wrest` sym_sub_tac>>fs[]>>
      imp_res_tac read_bitmap_split>>fs[]>>
      imp_res_tac abs_stack_to_stack_LENGTH>>
      qpat_assum`A=SOME(LASTN h x)` sym_sub_tac>>
      AP_TERM_TAC>>
      qpat_abbrev_tac`length = handler_val A`>>
      Q.ISPECL_THEN [`length`,`DROP(LENGTH q)r'`] assume_tac LASTN_LENGTH_BOUNDS>>
      fs[LET_THM]>>
      simp[LASTN_CONS]>>
      `q'++r' = (q'++TAKE (LENGTH q) r')++DROP (LENGTH q) r'` by fs[]>>
      pop_assum SUBST_ALL_TAC>>
      simp[LASTN_APPEND2])
    >>
      qpat_abbrev_tac`frame = (a,b,c,d)`>>
      `h = LENGTH (frame::x)` by (fs[]>>DECIDE_TAC)>>
      pop_assum SUBST_ALL_TAC>>
      fs[LASTN_LENGTH_ID]>>
      fs[LASTN_CONS_ID]>>
      qpat_abbrev_tac`ls=a::b::c::d`>>
      `LASTN (handler_val (frame::x)) ls = ls` by
        (match_mp_tac LASTN_MORE>>
        imp_res_tac read_bitmap_split>>
        imp_res_tac abs_stack_to_stack_LENGTH>>
        fs[Abbr`frame`,Abbr`ls`,handler_val_def]>>
        simp[LENGTH_TAKE])>>
      qpat_assum`A=wrest` sym_sub_tac>>fs[]>>
      fs[Abbr`ls`,Abbr`frame`,abs_stack_def,LET_THM])

val abs_stack_len = prove(``
  ∀wstack sstack stack handler.
  abs_stack wstack sstack = SOME stack ⇒
  handler_val (LASTN handler stack) ≤ LENGTH sstack``,
  ho_match_mp_tac (theorem "abs_stack_ind")>>rw[]>>
  fs[abs_stack_def,LET_THM]
  >-
    (pop_assum sym_sub_tac>>fs[LASTN_def,handler_val_def])
  >-
    (pop_assum (mp_tac o SYM)>> TOP_CASE_TAC>>fs[LASTN_def,handler_val_def])
  >-
    (pop_assum mp_tac>>ntac 5 TOP_CASE_TAC>>fs[]>>
    disch_then (assume_tac o SYM)>>
    Cases_on`handler ≤ LENGTH x`
    >-
      (fs[LASTN_CONS]>>
      imp_res_tac read_bitmap_split>>
      fs[]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      DECIDE_TAC)
    >>
      fs[]>>qpat_abbrev_tac`frame = (a,b,c,d)`>>
      `¬(handler < LENGTH (frame::x))` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE,Abbr`frame`,handler_val_def]>>
      imp_res_tac read_bitmap_split>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      `¬(handler < LENGTH x)` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE]>>rw[]>>
      fs[LENGTH_TAKE_EQ]>>IF_CASES_TAC>>
      DECIDE_TAC)
  >>
    pop_assum mp_tac>>
    ntac 8 TOP_CASE_TAC>>fs[]>>
    disch_then (assume_tac o SYM)>>
    Cases_on`handler ≤ LENGTH x`
    >-
      (fs[LASTN_CONS]>>
      imp_res_tac read_bitmap_split>>
      fs[]>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      DECIDE_TAC)
    >>
      fs[]>>qpat_abbrev_tac`frame = (a,b,c,d)`>>
      `¬(handler < LENGTH (frame::x))` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE,Abbr`frame`,handler_val_def]>>
      imp_res_tac read_bitmap_split>>
      first_x_assum (qspec_then`handler` mp_tac)>>
      `¬(handler < LENGTH x)` by (fs[]>>DECIDE_TAC)>>
      fs[LASTN_MORE]>>rw[]>>
      fs[LENGTH_TAKE_EQ]>>IF_CASES_TAC>>
      DECIDE_TAC)

val EL_REVERSE_REWRITE = prove(``
  ∀l n k. n < LENGTH l ∧ k < n ⇒
  EL (LENGTH l - n + k) l = EL (n-k -1) (REVERSE l)``,
  rw[]>>
  `n-k-1 < LENGTH l` by DECIDE_TAC>>
  fs[EL_REVERSE]>>
  `LENGTH l - (n- k-1) = LENGTH l -n +k +1` by DECIDE_TAC>>
  fs[GSYM ADD1])

(*Strengthened version of LASTN_DROP after change to make it total*)
val LASTN_DROP2 = prove(``
  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l``,
  Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]
  >-
    `¬ (n ≤ LENGTH l)` by DECIDE_TAC
  >-
    (fs[ADD1]>>
    `LENGTH l +1 - n -1 = LENGTH l -n` by DECIDE_TAC>>
    fs[])
  >-
    (`LENGTH l -n = 0` by DECIDE_TAC >>
    pop_assum SUBST_ALL_TAC>>fs[DROP])
  >>
    `n = LENGTH l` by DECIDE_TAC>>
    simp[])

val LASTN_LESS = prove(``
  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs``,
  Induct>>rw[]>>
  Cases_on`n+1 ≤ LENGTH ls`>>fs[]
  >-
    (fs[LASTN_CONS]>>
    res_tac>>fs[]>>
    `n ≤ LENGTH ls` by (fs[]>>decide_tac)>>
    fs[LASTN_CONS])
  >>
  `n = LENGTH ls` by DECIDE_TAC>>
  `n+1 = LENGTH (h::ls)` by (fs[]>>DECIDE_TAC)>>
  imp_res_tac LASTN_LENGTH_ID2>>
  fs[LASTN_CONS])

val ALOOKUP_IFF_MEM = prove(
  ``ALL_DISTINCT (MAP FST l) ==>
    (ALOOKUP l q = SOME r <=> MEM (q,r) l)``,
  Induct_on `l` \\ fs [FORALL_PROD,MEM_MAP] \\ rw [] \\ metis_tac []);

val SORTED_CONS_IMP = prove(
  ``SORTED (\x y. FST x > (FST y):num) (h::t) ==>
    ~(MEM h t) /\ SORTED (\x y. FST x > FST y) t /\
    !x. MEM x t ==> FST h > FST x``,
  Induct_on `t` \\ fs [SORTED_DEF] \\ rw []
  \\ `SORTED (\x y. FST x > FST y) (h::t)` by
    (Cases_on `t` \\ fs [SORTED_DEF] \\ decide_tac)
  \\ fs [] \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ disj1_tac \\ decide_tac);

val SORTED_IMP_ALL_DISTINCT_LEMMA = prove(
  ``!l. SORTED (\x y. FST x > (FST y):num) l ==> ALL_DISTINCT (MAP FST l)``,
  Induct \\ fs [] \\ rw [MEM_MAP]
  \\ metis_tac [DECIDE ``m>n ==> m<>n:num``,SORTED_CONS_IMP]);

val MEM_toAList_fromAList = prove(
  ``SORTED (\x y. FST x > (FST y):num) l ==>
    MEM a (toAList (fromAList l)) = MEM a l``,
  Cases_on `a` \\ fs [MEM_toAList,lookup_fromAList] \\ rw []
  \\ imp_res_tac SORTED_IMP_ALL_DISTINCT_LEMMA \\ fs [ALOOKUP_IFF_MEM]);

val SORTED_FST_PERM_IMP_ALIST_EQ = prove(
  ``SORTED (\x y. FST x > FST y) l /\
    SORTED (\x y. FST x > FST y) q /\
    PERM (toAList (fromAList l)) q ==>
    q = l``,
  rw [] \\ drule MEM_PERM \\ fs [MEM_toAList_fromAList]
  \\ pop_assum kall_tac \\ rpt (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`l`,`l`) \\ Induct_on `q` \\ fs [MEM]
  THEN1 (Cases \\ fs[] \\ metis_tac [])
  \\ Cases_on `l` THEN1 (fs [] \\ metis_tac [])
  \\ fs [] \\ rw []
  \\ imp_res_tac SORTED_CONS_IMP
  \\ `!m n:num. m > n /\ n > m ==> F` by decide_tac
  \\ metis_tac []);

val stack_rel_raise = prove(``
    n ≤ LENGTH sstack /\
    handler+1 ≤ LENGTH wstack /\ SORTED (\x y. FST x > FST y) l /\
    LASTN (handler + 1) wstack = StackFrame l (SOME (h1,l3,l4))::rest /\
    abs_stack wstack (DROP n sstack) = SOME stack /\
    stack_rel_aux k (LENGTH sstack) wstack stack ==>
    ?ex payload.
      LASTN (handler+1) stack = (SOME ex,payload) :: LASTN handler stack /\
      3 <= LENGTH sstack /\ 3 <= handler_val (LASTN (handler+1) stack) /\
      h1 < LENGTH rest ∧
      EL (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 1)
            sstack = Loc l3 l4 /\
      EL (LENGTH sstack − handler_val (LASTN (handler+1) stack) + 2) sstack =
          Word (n2w
            (LENGTH sstack - handler_val (LASTN (h1+1) (LASTN (handler+1) stack)))) /\
      stack_rel_aux k (LENGTH sstack)
        (StackFrame (FST (env_to_list (fromAList l) (K I))) NONE::rest)
            ((NONE,payload) :: LASTN handler stack) /\
      abs_stack (StackFrame (FST (env_to_list (fromAList l) (K I))) NONE::rest)
        (DROP (LENGTH sstack - handler_val (LASTN (handler+1) stack) + 3)
           sstack) = SOME ((NONE,payload) :: LASTN handler stack)``,
  rw[]>>
  imp_res_tac abs_stack_prefix_drop>>
  fs[LET_THM]>>
  Cases_on`LASTN (handler+1) stack`>>fs[stack_rel_aux_def]>>
  PairCases_on`h`>>Cases_on`h0`>>fs[stack_rel_aux_def]>>
  PairCases_on`x`>>fs[stack_rel_aux_def]>>
  `FST (env_to_list (fromAList l) (K I)) = l` by
   (Cases_on `env_to_list (fromAList l) (K I)` \\ fs []
    \\ imp_res_tac env_to_list_K_I_IMP \\ rw []
    \\ metis_tac [SORTED_FST_PERM_IMP_ALIST_EQ]) >>
  imp_res_tac abs_stack_IMP_LENGTH>>fs[]>>
  CONJ_TAC>- fs[LASTN_LESS]>>
  imp_res_tac abs_stack_len>>
  fs[handler_val_def]>>CONJ_ASM1_TAC>-
    (rator_x_assum `abs_stack` mp_tac>>
    (*The DROP must have length ≥ 3*)
    Cases_on`DROP n sstack`>>simp[abs_stack_def,LASTN_def]>>
    Cases_on`t'`>>simp[abs_stack_def]>>
    Cases_on`t''`>>simp[abs_stack_def]>>
    `3 ≤ LENGTH (DROP n sstack)` by
      (pop_assum SUBST_ALL_TAC>>
      simp[])>>
    Q.ISPECL_THEN [`n`,`sstack`] assume_tac LENGTH_DROP >>
    `LENGTH (DROP n sstack) ≤ LENGTH sstack` by DECIDE_TAC>>
    simp[])>>
  CONJ_ASM1_TAC>-
    DECIDE_TAC>>
  rator_x_assum `abs_stack` mp_tac>>
  qpat_abbrev_tac`ls = LASTN A B`>>
  strip_tac>>
  simp[LASTN_CONS]>>
  qpat_abbrev_tac`w = Word A`>>
  `EL 1 ls = Loc l3 l4 ∧ EL 2 ls = w` by
    (rator_x_assum`abs_stack` mp_tac>>
    Cases_on`ls`>-simp[abs_stack_def]>>
    Cases_on`h`>>simp[abs_stack_def,LET_THM]>>
    ntac 8 TOP_CASE_TAC>>fs[])>>
  fs[Abbr`ls`,LASTN_DROP2]>>
  qabbrev_tac`offset = (3+LENGTH h2 +LENGTH h3 +handler_val t)`>>
  (*Using DROP_DROP and more assumptions on the lengths*)
  `n + offset ≤ LENGTH sstack` by
    (first_x_assum(qspec_then`handler+1` mp_tac)>>
    simp[handler_val_def,Abbr`offset`])>>
  `DROP (LENGTH sstack - n - offset) (DROP n sstack) =
   DROP (LENGTH sstack - offset) sstack` by
     simp[DROP_DROP]>>
  `EL 1 (DROP (LENGTH sstack - offset) sstack) = Loc l3 l4 ∧
   EL 2 (DROP (LENGTH sstack - offset) sstack) = w` by fs[]>>
  `EL (1+(LENGTH sstack - offset)) sstack = Loc l3 l4 ∧
   EL (2+(LENGTH sstack - offset)) sstack = w` by
     (ntac 2 (pop_assum sym_sub_tac)>>
     rw[]>>match_mp_tac (GSYM EL_DROP)>>
     unabbrev_all_tac>>
     DECIDE_TAC)>>
  CONJ_TAC>-
    (ntac 2 (pop_assum sym_sub_tac)>>
    simp[Abbr`offset`])>>
  CONJ_TAC>-
    (ntac 2 (pop_assum sym_sub_tac)>>
    simp[Abbr`offset`])>>
  qpat_assum`DROP A stack = C` mp_tac>>
  qpat_assum`LENGTH stack =A` sym_sub_tac>>
  simp[GSYM LASTN_DROP2]>>
  strip_tac >> imp_res_tac LASTN_LESS>>
  simp[]>>
  qpat_assum`abs_stack A B = C` mp_tac>>
  simp[]>>
  qpat_abbrev_tac`ls = DROP A B`>>
  qpat_abbrev_tac`ls' = DROP A B`>>
  `ls' = DROP 3 ls` by
    (unabbrev_all_tac>>
    simp[DROP_DROP])>>
  Cases_on`ls`>>simp[abs_stack_def]>>
  Cases_on`t'`>>simp[]>>
  Cases_on`t''`>>simp[]>>
  ntac 6 TOP_CASE_TAC>>simp[])

val EVERY_IMP_EVERY_LASTN = prove(
  ``!xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys``,
  fs [EVERY_MEM] \\ rw [] \\ imp_res_tac MEM_LASTN_ALT \\ res_tac \\ fs []);

val is_tail_call_def = Define `
  (is_tail_call (Call NONE _ [0] NONE) = T) /\
  (is_tail_call _ = F)`

val comp_correct = store_thm("comp_correct",
  ``!(prog:'a wordLang$prog) (s:('a,'ffi) wordSem$state) k f f' res s1 t.
      (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
      state_rel k f f' s t /\ post_alloc_conventions k prog /\
      max_var prog <= 2 * f' + 2 * k /\
      (~(is_tail_call prog) ==> 1 <= f) ==>
      ?ck t1 res1.
        (stackSem$evaluate (comp prog (k,f,f'),t with clock := t.clock + ck) = (res1,t1)) /\
        if OPTION_MAP compile_result res <> res1
        then res1 = SOME (Halt (Word 2w)) /\
             t1.ffi.io_events ≼ s1.ffi.io_events /\
             (IS_SOME t1.ffi.final_event ==> t1.ffi = s1.ffi)
        else
          case res of
          | NONE => state_rel k f f' s1 t1
          | SOME (Result _ _) => state_rel k 0 0 s1 t1
          | SOME (Exception _ _) => state_rel k 0 0 (push_locals s1) t1
          | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [is_tail_call_def]
  THEN1 (* Skip *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw [])
  THEN1 (* Alloc *)
   (qexists_tac `0`
    \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `n = 2` by (fs [convs_def]) \\ rw []
    \\ Cases_on `get_var 2 s` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ `t.use_alloc /\ (get_var 1 t = SOME (Word c))` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
    \\ Cases_on `cut_env names s.locals`
    THEN1 fs [wordSemTheory.alloc_def]
    \\ Q.MATCH_ASSUM_RENAME_TAC `cut_env names s.locals = SOME env`
    \\ mp_tac evaluate_wLive \\ fs []>>
    discharge_hyps_keep>-
      (fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
      fs[GSYM toAList_domain,EVERY_MEM]>>
      fs[X_LE_DIV,reg_allocTheory.is_phy_var_def]>>
      rw[]>>res_tac>>DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ `1 < k` by fs [state_rel_def] \\ res_tac
    \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
    \\ drule alloc_IMP_alloc \\ discharge_hyps
    >-
      (fs[]>>cheat)
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [] \\ Cases_on `res = NONE` \\ fs [])
  THEN1 (* Move *) cheat
  THEN1 (* Inst *) cheat
  THEN1 (* Assign *) cheat
  THEN1 (* Get *) cheat
  THEN1 (* Set *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [state_rel_def,wordSemTheory.dec_clock_def,stackSemTheory.dec_clock_def])
  THEN1 (* Seq *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
    \\ split_pair_tac \\ fs []
    \\ `max_var c1 <= 2 * f' + 2 * k /\ max_var c2 <= 2 * f' + 2 * k` by
      (fs [word_allocTheory.max_var_def] \\ decide_tac)
    \\ `post_alloc_conventions k c1 /\
        post_alloc_conventions k c2` by fs [convs_def]
    \\ reverse (Cases_on `res' = NONE`) \\ fs [] \\ rpt var_eq_tac
    THEN1
     (first_x_assum drule \\ fs [] \\ rw [] \\ fs []
      \\ qexists_tac `ck` \\ fs [] \\ Cases_on `res` \\ fs []
      \\ Cases_on `res1 = NONE` \\ fs [])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ reverse (Cases_on `res1 = NONE`) \\ fs [] THEN1
     (qexists_tac `ck`
      \\ `good_dimindex (:'a)` by fs [state_rel_def]
      \\ fs [Halt_EQ_compile_result]
      \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
      \\ `s.ffi = t.ffi` by fs [state_rel_def]
      \\ imp_res_tac evaluate_io_events_mono \\ fs []
      \\ imp_res_tac wordPropsTheory.evaluate_io_events_mono \\ fs []
      \\ rfs [] \\ fs [] \\ metis_tac [IS_PREFIX_TRANS])
    \\ first_x_assum drule \\ fs [] \\ rw [] \\ fs []
    \\ imp_res_tac stack_evaluate_add_clock_NONE \\ fs []
    \\ pop_assum (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,wReg1_def]
    \\ Cases_on `get_var n s` \\ fs []
    \\ Cases_on `get_var m s` \\ fs [] \\ rw []
    \\ Cases_on `x` \\ fs []
    \\ qcase_tac `get_var n s = SOME (Loc l1 l2)`
    \\ fs [wStackLoad_def] \\ fs [convs_def] \\ rw []
    \\ fs [reg_allocTheory.is_phy_var_def,word_allocTheory.max_var_def]
    \\ `t.use_stack /\ ~(LENGTH t.stack < t.stack_space + f) /\
        t.stack_space <= LENGTH t.stack` by
     (fs [state_rel_def] \\ decide_tac) \\ fs [LET_DEF]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    THEN1
     (`(get_var (n DIV 2) t = SOME (Loc l1 l2)) /\ (get_var 1 t = SOME x')` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
      \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF]
      \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
             fromList2_def,lookup_def]
      \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ imp_res_tac DROP_DROP \\ fs [])
    \\ `~(LENGTH t.stack < t.stack_space + (f -1 - (n DIV 2 - k))) /\
        (EL (t.stack_space + (f -1 - (n DIV 2 - k))) t.stack = Loc l1 l2) /\
        (get_var 1 t = SOME x')` by
     (fs [state_rel_def,get_var_def,LET_DEF]
      \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
      \\ fs [stackSemTheory.get_var_def]
      \\ imp_res_tac el_opt_TAKE_IMP
      \\ fs [el_opt_DROP] \\ fs [el_opt_THM] \\
      qpat_abbrev_tac `A=f-1-B`>>
      rw[]>>DECIDE_TAC)
    \\ fs [LET_DEF]
    \\ `(set_var k (Loc l1 l2) t).use_stack /\
        (set_var k (Loc l1 l2) t).stack_space <=
         LENGTH (set_var k (Loc l1 l2) t).stack` by
      fs [stackSemTheory.set_var_def]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    \\ fs [stackSemTheory.set_var_def,LET_DEF]
    \\ `k <> 1` by (fs [state_rel_def] \\ decide_tac)
    \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF,FLOOKUP_UPDATE]
    \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
           fromList2_def,lookup_def]
    \\ fs [AC ADD_ASSOC ADD_COMM]
    \\ imp_res_tac DROP_DROP \\ fs [])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def]
    \\ qpat_assum `xxx = (aa,bb)` mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ pop_assum mp_tac
    \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
    \\ qexists_tac `1`
    \\ qcase_tac `LASTN (s.handler + 1) s.stack =
          StackFrame l (SOME (h1,l3,l4))::rest`
    \\ fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,jump_exc_def,
        stackSemTheory.find_code_def]
    \\ `lookup 5 t.code = SOME (raise_stub k)` by fs [state_rel_def] \\ fs []
    \\ pop_assum kall_tac
    \\ fs [stackSemTheory.dec_clock_def,raise_stub_def,word_allocTheory.max_var_def]
    \\ fs [stackSemTheory.evaluate_def,state_rel_def,LET_DEF]
    \\ fs [DROP_DROP_EQ] \\ fs [stack_rel_def,LET_DEF,get_var_set_var]
    \\ fs [stackSemTheory.set_var_def]
    \\ `(LENGTH t.stack - handler_val (LASTN (s.handler+1) stack)) < dimword (:'a)`
         by decide_tac \\ fs []
    \\ `SORTED (\x y. FST x > FST y) l` by
      (imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [sorted_env_def])
    \\ `LENGTH t.stack - handler_val (LASTN (s.handler+1) stack) + 3 <= LENGTH t.stack` by
         (imp_res_tac stack_rel_raise \\
         pop_assum mp_tac >>
         ntac 16 (pop_assum kall_tac)>>
         discharge_hyps>-
           DECIDE_TAC>>
         discharge_hyps>-
            simp[]>>
         rw[]>>
         decide_tac)
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,stackSemTheory.set_store_def]
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ IF_CASES_TAC \\ fs [] THEN1 decide_tac
    \\ fs [stackSemTheory.get_var_def,FLOOKUP_UPDATE,push_locals_def,lookup_def]
    \\ imp_res_tac stack_rel_raise \\
    pop_assum mp_tac >>
    ntac 32 (pop_assum kall_tac)>>
    discharge_hyps>- DECIDE_TAC>>
    discharge_hyps >- simp[]>>
    rw[] >>
    fs [FLOOKUP_UPDATE]>>
    rfs[]
    \\ `h1 < SUC (LENGTH rest)` by decide_tac \\ fs []
    \\ conj_tac THEN1
     (fs [sorted_env_def] \\ Cases_on `env_to_list (fromAList l) (K I)`
      \\ imp_res_tac env_to_list_K_I_IMP \\ fs [])
    \\ rfs[]
    \\ `h1 <= LENGTH (LAST_N (s.handler+1) stack)` by all_tac
    \\ fs [LASTN_CONS]
    \\ imp_res_tac LASTN_LENGTH_BOUNDS
    \\ imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
    \\ imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs []
    >-
      DECIDE_TAC
    >>
      simp[LASTN_CONS])
  THEN1 (* If *) cheat
  THEN1 (* FFI *) cheat
  \\ (* Call *) cheat);

val make_init_def = Define `
  make_init (t:('a,'ffi)stackSem$state) code =
    <| locals  := LN
     ; store   := t.store \\ Handler
     ; stack   := []
     ; memory  := t.memory
     ; mdomain := t.mdomain
     ; permute := K I
     ; gc_fun  := t.gc_fun
     ; handler := 0
     ; clock   := t.clock
     ; code    := code
     ; be      := t.be
     ; ffi     := t.ffi |> `;

val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,CallAny_def]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       word_allocTheory.list_max_def,is_tail_call_def,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0] NONE)``,
       word_allocTheory.max_var_def,LET_DEF,word_allocTheory.max2_def] |> GEN_ALL

val comp_Call = prove(
  ``∀start (s:('a,'ffi) wordSem$state) k res s1 t.
      evaluate (Call NONE (SOME start) [0] NONE,s) = (res,s1) /\
      res ≠ SOME Error /\ state_rel k 0 0 s t ⇒
      ∃ck t1 res1.
        evaluate (Call NONE (INL start) NONE,t with clock := t.clock + ck) =
        (res1,t1) /\ 1w <> (0w:'a word) /\ 2w <> (0w:'a word) /\
        if lift compile_result res = res1 then
          s1.ffi = t1.ffi /\ s1.clock = t1.clock
        else
          res1 = SOME (Halt (Word 2w)) /\
          t1.ffi.io_events ≼ s1.ffi.io_events /\
          (IS_SOME t1.ffi.final_event ⇒ t1.ffi = s1.ffi)``,
  rw [] \\ drule comp_Call_lemma \\ fs []
  \\ disch_then drule \\ fs [] \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ conj_tac THEN1 (fs [state_rel_def,good_dimindex_def,dimword_def])
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs [state_rel_def,push_locals_def,LET_DEF]);

val state_rel_IMP_semantics = store_thm("state_rel_IMP_semantics",
  ``state_rel k 0 0 s t /\ semantics s start <> Fail ==>
    semantics start t IN extend_with_resource_limit { semantics s start }``,
  cheat); (* TODO Ramana, use comp_Call, see bvp_to_word for a similar proof *)

val init_state_ok_def = Define `
  init_state_ok k (t:('a,'ffi)stackSem$state) <=>
    1n < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
    t.stack_space <= LENGTH t.stack /\
    t.use_stack ∧ t.use_store ∧ t.use_alloc ∧ gc_fun_ok t.gc_fun /\
    t.stack_space ≤ LENGTH t.stack ∧
    LENGTH t.stack < dimword (:'a)`

val init_state_ok_IMP_state_rel = prove(
  ``lookup 5 t.code = SOME (raise_stub k) /\
    (∀n word_prog arg_count.
        lookup n code = SOME (arg_count,word_prog) ==>
        lookup n t.code = SOME (compile_prog word_prog arg_count k)) /\
    init_state_ok k t ==>
    state_rel k 0 0 (make_init t code) (t:('a,'ffi)stackSem$state)``,
  fs [state_rel_def,make_init_def,LET_DEF,lookup_def,init_state_ok_def] \\ rw []
  \\ cheat); (* stack_rel_def needs tweaking *)

val init_state_ok_semantics =
  state_rel_IMP_semantics |> Q.INST [`s`|->`make_init t code`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

val compile_word_to_stack_semantics = prove(
  ``t.code = fromAList (compile_word_to_stack k code) /\
    init_state_ok k t /\ (ALOOKUP code 5 = NONE) /\
    semantics (make_init t (fromAList code)) start <> Fail ==>
    semantics start t IN
    extend_with_resource_limit {semantics (make_init t (fromAList code)) start}``,
  rw [] \\ match_mp_tac init_state_ok_semantics \\ fs []
  \\ fs [compile_word_to_stack_def,lookup_fromAList] \\ rw [] \\ fs []
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac)
  \\ Induct_on `code` \\ fs [ALOOKUP_def,FORALL_PROD] \\ rw []);

val _ = export_theory();
