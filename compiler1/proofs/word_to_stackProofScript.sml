open preamble
     stackSemTheory wordSemTheory
     word_to_stackTheory;

val _ = new_theory "word_to_stackProof";

(* state relation *)

val ANY_EL_def = Define `
  ANY_EL n xs = if n < LENGTH xs then SOME (EL n xs) else NONE`;

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
    (t.memory = s.memory) /\ (t.mdomain = s.mdomain) /\
    s.store SUBMAP t.store /\ DISJOINT (FDOM s.store) stack_names /\
    (!n ignore word_prog arg_count.
       (lookup n s.code = SOME (ignore,word_prog,arg_count)) ==>
       (lookup n t.code = SOME (word_to_stack$compile word_prog arg_count k))) /\
    (lookup 0 t.code = SOME (raise_stub k)) /\
    t.stack_space + f <= LENGTH t.stack /\
    (if f = 0 then f' = 0 else (f = f' + (f' DIV (dimindex (:'a) - 1)) + 1)) /\
    let stack = DROP t.stack_space t.stack in
    let current_frame = TAKE f stack in
    let rest_of_stack = DROP f stack in
      stack_rel k s.handler s.stack (FLOOKUP s.store Handler)
        rest_of_stack (LENGTH t.stack) /\
      (!n v.
        (lookup n s.locals = SOME v) ==>
        if n < k then (lookup n t.regs = SOME v)
        else (ANY_EL (f+k-n) current_frame = SOME v) /\ n < k + f')`

(* correctness proof *)

val compile_correct = prove(
  ``!(prog:'a wordLang$prog) s k f f' res s1 t.
      (evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
      state_rel k f f' s t /\
      max_var prog <= 2 * f' ==>
      ?t1 res1. (evaluate (comp prog (k,f),t) = (res1,t1)) /\
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
  THEN1 (* Alloc *) cheat
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
    \\ Cases_on `evaluate (c1,s)` \\ fs [max_var_def,MAX_LE]
    \\ Cases_on `q` \\ fs []
    \\ cheat (* easy? *))
  THEN1 (* Return *) cheat
  THEN1 (* Raise *) cheat
  THEN1 (* If *) cheat
  \\ (* Call *) cheat);

val _ = save_thm("compile_correct",compile_correct);

(*
   TODO:
    - assume syntax restrictions on word progs (based on reg alloc)
    - also assume absence of Assign and Store, and only simple form of Set
    - add DIV 2 in appropriate places
    - prove cases in order that should set correct state_rel_def
      sooner rather than later:
       - Alloc
       - Raise
       - Call
*)

val _ = export_theory();
