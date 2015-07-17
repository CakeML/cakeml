open preamble
     stackSemTheory wordSemTheory
     word_to_stackTheory;

val _ = new_theory "word_to_stackProof";

(* TODO: move? *)

val ANY_EL_def = Define `
  (ANY_EL n [] = NONE) /\
  (ANY_EL n (x::xs) = if n = 0n then SOME x else ANY_EL (n-1) xs)`

val ANY_EL_THM = prove(
  ``!xs n. ANY_EL n xs = if n < LENGTH xs then SOME (EL n xs) else NONE``,
  Induct \\ fs [ANY_EL_def] \\ rw [] THEN1 decide_tac
  \\ Cases_on `xs` \\ fs [] \\ Cases_on `n` \\ fs [] \\ decide_tac);

val LENGTH_TAKE_EQ = prove(
  ``!n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)``,
  Induct \\ fs [TAKE_def] \\ Cases \\ fs [TAKE_def]
  \\ fs [MIN_DEF] \\ decide_tac);

val EL_TAKE_EQ = prove(
  ``!n xs i. i < n ==> EL i (TAKE n xs) = EL i xs``,
  Induct \\ fs [] \\ Cases \\ fs [TAKE_def] \\ Cases \\ fs []);

val ANY_EL_TAKE_IMP = prove(
  ``(ANY_EL n (TAKE f xs) = SOME x) ==>
    (ANY_EL n xs = SOME x)``,
  fs [ANY_EL_THM] \\ rw []
  \\ fs [LENGTH_TAKE_EQ]
  \\ match_mp_tac (GSYM EL_TAKE_EQ) \\ fs []);

val ANY_EL_DROP = prove(
  ``(ANY_EL n (DROP f xs) = ANY_EL (f + n) xs)``,
  Cases_on `DROP f xs = []` \\ fs [] \\ fs [DROP_NIL]
  \\ fs [ANY_EL_THM] THEN1 decide_tac
  \\ `f + n < LENGTH xs <=> n < LENGTH xs - f` by decide_tac \\ fs []
  \\ rw [] \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ match_mp_tac (GSYM EL_DROP) \\ decide_tac);

(* move to props? *)

val LENGTH_word_list_lemma = prove(
  ``!xs d. 0 < d ==> (LENGTH (word_list xs d) = LENGTH xs DIV d + 1)``,
  recInduct word_list_ind
  \\ rpt strip_tac \\ fs []
  \\ once_rewrite_tac [word_list_def] \\ fs [] \\ rw []
  \\ imp_res_tac ZERO_DIV \\ fs [] \\ res_tac
  \\ imp_res_tac LESS_DIV_EQ_ZERO \\ fs []
  \\ fs [ADD1] \\ fs [NOT_LESS]
  \\ imp_res_tac (ONCE_REWRITE_RULE [ADD_COMM] LESS_EQ_EXISTS)
  \\ ASSUME_TAC (ADD_DIV_ADD_DIV |> Q.SPECL [`d`] |> UNDISCH
      |> Q.SPECL [`1`,`p`] |> ONCE_REWRITE_RULE [ADD_COMM]) \\ fs []);

val LENGTH_word_list = store_thm("LENGTH_word_list",
  ``!xs d. LENGTH (word_list xs d) = if d = 0 then 1 else LENGTH xs DIV d + 1``,
  rw [] THEN1 (once_rewrite_tac [word_list_def] \\ fs [])
  \\ match_mp_tac LENGTH_word_list_lemma \\ decide_tac);

(* state relation *)

val stack_names_def = Define `
  stack_names = { Handler }`;

val abs_stack_def = tDefine "abs_stack" `
  (abs_stack [] = NONE) /\
  (abs_stack xs =
    if xs = [Word 0w] then SOME [] else
    case read_bitmap xs of
    | NONE => NONE
    | SOME (bs,rs1,rs) =>
        if LENGTH rs < LENGTH bs then NONE else
          let xs1 = TAKE (LENGTH bs) rs in
          let xs2 = DROP (LENGTH bs) rs in
            case abs_stack xs2 of
            | NONE => NONE
            | SOME ys => SOME ((bs,rs1,xs1)::ys))`
 (WF_REL_TAC `measure LENGTH`
  \\ REPEAT STRIP_TAC
  \\ imp_res_tac read_bitmap_LENGTH
  \\ fs [LENGTH_DROP]
  \\ decide_tac)

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
  (index_list [] n = ([],n)) /\
  (index_list (x::xs) n =
     let (ys,k) = index_list xs n in ((k:num,x)::ys,k+1))`

val alist_eq_def = Define `
  alist_eq l1 l2 <=>
    !x. lookup x (fromAList l1) = lookup x (fromAList l2)`;

val joined_ok_def = Define `
  (joined_ok k [] len <=> T) /\
  (joined_ok k ((StackFrame l1 NONE,[(bs1,rs1,xs1)])::rest) len <=>
     joined_ok k rest len /\
     ?l2.
       (filter_bitmap bs1 (FST (index_list xs1 k)) = SOME (l2,[])) /\
       alist_eq l1 l2) /\
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

val state_rel_def = Define `
  state_rel k f f' (s:'a wordSem$state) (t:'a stackSem$state) <=>
    (s.clock = t.clock) /\ (s.gc_fun = t.gc_fun) /\ (s.permute = K I) /\
    (t.io = s.io) /\ t.use_stack /\ t.use_store /\ t.use_alloc /\
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\ 1 < k /\
    s.store SUBMAP t.store /\ DISJOINT (FDOM s.store) stack_names /\
    (!n ignore word_prog arg_count.
       (lookup n s.code = SOME (ignore,word_prog,arg_count)) ==>
       (lookup n t.code = SOME (word_to_stack$compile word_prog arg_count k))) /\
    (lookup 0 t.code = SOME (raise_stub k)) /\ 8 <= dimindex (:'a) /\
    t.stack_space + f <= LENGTH t.stack /\
    (if f = 0 then f' = 0 else (f = f' + (f' + 1) DIV (dimindex (:'a) - 1) + 1)) /\
    let stack = DROP t.stack_space t.stack in
    let current_frame = TAKE f stack in
    let rest_of_stack = DROP f stack in
      stack_rel k s.handler s.stack (FLOOKUP s.store Handler)
        rest_of_stack (LENGTH t.stack) /\
      (!n v.
        (lookup n s.locals = SOME v) ==>
        EVEN n /\
        if n DIV 2 < k then (lookup (n DIV 2) t.regs = SOME v)
        else (ANY_EL (f+k-(n DIV 2)) current_frame = SOME v) /\ n DIV 2 < k + f')`

(* correctness proof *)

val evaluate_SeqStackFree = prove(
  ``t.use_stack /\ t.stack_space <= LENGTH t.stack ==>
    evaluate (SeqStackFree f p,t) =
    evaluate (Seq (StackFree f) p,t)``,
  fs [SeqStackFree_def] \\ rw [stackSemTheory.evaluate_def]
  THEN1 (`F` by decide_tac) \\ AP_TERM_TAC
  \\ fs [stackSemTheory.state_component_equality]);

val convs_def = LIST_CONJ
  [word_allocProofTheory.post_alloc_conventions_def,
   word_allocProofTheory.call_arg_convention_def,
   wordPropsTheory.every_var_def,
   wordPropsTheory.every_stack_var_def]

val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``

val LENGTH_write_bitmap = prove(
  ``state_rel k f f' (s:'a wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap names k f f'):'a word list) + f' = f)``,
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac);

val evaluate_wLive = prove(
  ``state_rel k f f' (s:'a wordSem$state) t /\ 1 <= f /\
    (cut_env names s.locals = SOME env) ==>
    ?t5. (evaluate (wLive names (k,f,f'),t) = (NONE,t5)) /\
         state_rel k 0 0 (push_env env ^nn s) t5 /\
         state_rel k f f' s t5 /\
         (get_var 1 t5 = get_var 1 t)``,
  fs [wLive_def]
  \\ cheat);

val push_env_set_store = prove(
  ``push_env env ^nn (set_store AllocSize (Word c) s) =
    set_store AllocSize (Word c) (push_env env ^nn s)``,
  fs [push_env_def,set_store_def,env_to_list_def,LET_DEF]);

val state_rel_set_store = prove(
  ``state_rel k 0 0 s5 t5 ==>
    state_rel k 0 0 (set_store AllocSize w s5) (set_store AllocSize w t5)``,
  fs [state_rel_def,set_store_def,stackSemTheory.set_store_def,LET_DEF,
      FLOOKUP_DEF,stack_names_def] \\ REPEAT STRIP_TAC \\ rfs[]
  \\ fs [SUBMAP_DEF] \\ rw [FAPPLY_FUPDATE_THM]);

val gc_state_rel = prove(
  ``(gc s1 = SOME s2) /\ state_rel k 0 0 s1 t1 ==>
    ?t2. gc t1 = SOME t2 /\ state_rel k 0 0 s2 t2``,
  cheat);

val FLOOKUP_SUBMAP = prove(
  ``(FLOOKUP f n = SOME x) /\ f SUBMAP g ==> (FLOOKUP g n = SOME x)``,
  fs [FLOOKUP_DEF,SUBMAP_DEF] \\ metis_tac []);

val alloc_IMP_alloc = prove(
  ``(alloc c names (s:'a wordSem$state) = (res:'a result option,s1)) /\
    state_rel k f f' s t5 /\
    state_rel k 0 0 (push_env env ^nn s) t5 /\
    (cut_env names s.locals = SOME env) /\
    res <> SOME Error ==>
    ?t1 res1.
      (alloc c t5 = (res1,t1)) /\
      if res = NONE then
        res1 = NONE /\ state_rel k f f' s1 t1
      else
        res = SOME NotEnoughSpace /\ res1 = res``,
  fs [wordSemTheory.alloc_def,stackSemTheory.alloc_def]
  \\ REPEAT STRIP_TAC \\ fs [push_env_set_store]
  \\ imp_res_tac state_rel_set_store
  \\ pop_assum (mp_tac o Q.SPEC `Word c`) \\ REPEAT STRIP_TAC
  \\ Cases_on `gc (set_store AllocSize (Word c) (push_env env ^nn s))`
  \\ fs [] \\ imp_res_tac gc_state_rel \\ NTAC 3 (POP_ASSUM (K ALL_TAC)) \\ fs []
  \\ Cases_on `pop_env x` \\ fs []
  \\ Q.MATCH_ASSUM_RENAME_TAC `pop_env s2 = SOME s3`
  \\ `state_rel k f f' s3 t2` by cheat
  \\ Cases_on `FLOOKUP s3.store AllocSize` \\ fs []
  \\ Cases_on `has_space x s3` \\ fs []
  \\ `s3.store SUBMAP t2.store` by fs [state_rel_def]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs []
  \\ fs [has_space_def,stackSemTheory.has_space_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs [] \\ rw [] \\ fs []);

val compile_correct = prove(
  ``!(prog:'a wordLang$prog) s k f f' res s1 t.
      (evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
      state_rel k f f' s t /\ post_alloc_conventions k prog /\
      max_var prog <= 2 * f' + 2 * k /\ 1 <= f ==>
      ?t1 res1. (evaluate (comp prog (k,f,f'),t) = (res1,t1)) /\
                if res <> res1 then (res1 = SOME NotEnoughSpace) else
                  case res of
                  | NONE => state_rel k f f' s1 t1
                  | SOME (Result v1 v2) => state_rel k 0 0 s1 t1
                  | SOME (Exception v1 v2) => state_rel k 0 0 s1 t1
                  | SOME _ => T``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs []
  THEN1 (* Skip *)
   (fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw [])
  THEN1 (* Alloc *)
   (fs [wordSemTheory.evaluate_def,
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
    \\ mp_tac evaluate_wLive \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
    \\ mp_tac alloc_IMP_alloc \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [] \\ Cases_on `res = NONE` \\ fs [])
  THEN1 (* Move *) cheat
  THEN1 (* Inst *) cheat
  THEN1 (* Assign *) cheat
  THEN1 (* Get *) cheat
  THEN1 (* Set *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* Tick *)
   (fs [wordSemTheory.evaluate_def,
        stackSemTheory.evaluate_def,comp_def] \\ rw []
    \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [state_rel_def,wordSemTheory.dec_clock_def,stackSemTheory.dec_clock_def])
  THEN1 (* Seq *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs []
    \\ `max_var c1 <= 2 * f' + 2 * k /\ max_var c2 <= 2 * f' + 2 * k` by
      (fs [word_allocTheory.max_var_def] \\ decide_tac)
    \\ `post_alloc_conventions k c1 /\
        post_alloc_conventions k c2` by fs [convs_def]
    \\ first_x_assum (mp_tac o Q.SPECL [`k`,`f`,`f'`,`t`])
    \\ Cases_on `q = SOME Error` \\ fs []
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `res1` \\ fs [] \\ rw [])
  THEN1 (* Return *)
   (fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def,wReg1_def]
    \\ Cases_on `get_var n s` \\ fs []
    \\ Cases_on `get_var m s` \\ fs [] \\ rw []
    \\ fs [wStackLoad_def] \\ fs [convs_def] \\ rw []
    \\ fs [reg_allocTheory.is_phy_var_def,word_allocTheory.max_var_def]
    \\ `t.use_stack /\ ~(LENGTH t.stack < t.stack_space + f) /\
        t.stack_space <= LENGTH t.stack` by
     (fs [state_rel_def] \\ decide_tac) \\ fs [LET_DEF]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    THEN1
     (`(get_var (n DIV 2) t = SOME x) /\ (get_var 1 t = SOME x')` by
       (fs [state_rel_def,get_var_def,LET_DEF]
        \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
        \\ fs [stackSemTheory.get_var_def])
      \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF]
      \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
             fromList2_def,lookup_def]
      \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ imp_res_tac DROP_DROP \\ fs [] \\ rfs [] \\ fs [])
    \\ `~(LENGTH t.stack < t.stack_space + (f + k - n DIV 2)) /\
        (EL (t.stack_space + (f + k - n DIV 2)) t.stack = x) /\
        (get_var 1 t = SOME x')` by
     (fs [state_rel_def,get_var_def,LET_DEF]
      \\ res_tac \\ qpat_assum `!x.bbb` (K ALL_TAC) \\ rfs []
      \\ fs [stackSemTheory.get_var_def]
      \\ imp_res_tac ANY_EL_TAKE_IMP
      \\ fs [ANY_EL_DROP] \\ fs [ANY_EL_THM] \\ decide_tac)
    \\ fs [LET_DEF]
    \\ `(set_var k x t).use_stack /\
        (set_var k x t).stack_space <= LENGTH (set_var k x t).stack` by
      fs [stackSemTheory.set_var_def]
    \\ fs [evaluate_SeqStackFree,stackSemTheory.evaluate_def]
    \\ fs [stackSemTheory.set_var_def,LET_DEF]
    \\ `k <> 1` by (fs [state_rel_def] \\ decide_tac)
    \\ fs [get_var_def,stackSemTheory.get_var_def,LET_DEF,
           lookup_insert]
    \\ fs [state_rel_def,empty_env_def,call_env_def,LET_DEF,
           fromList2_def,lookup_def]
    \\ fs [AC ADD_ASSOC ADD_COMM]
    \\ imp_res_tac DROP_DROP \\ fs [])
  THEN1 (* Raise *) cheat
  THEN1 (* If *) cheat
  \\ (* Call *) cheat);

val _ = save_thm("compile_correct",compile_correct);

(*
   TODO:
    - also assume absence of Assign and Store, and only simple form of Set
    - prove cases in order that should set correct state_rel_def
      sooner rather than later:
       - Alloc
       - Raise
       - Call
*)

val _ = export_theory();
