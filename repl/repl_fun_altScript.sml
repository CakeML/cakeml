
open HolKernel Parse boolLib bossLib;

val _ = new_theory "repl_fun_alt";

open listTheory arithmeticTheory relationTheory;
open repl_funTheory bytecodeLabelsTheory BytecodeTheory;

(*

   This file rephrases repl_fun (as repl_fun_alt) so that it fits
   better with the machine-code implementation. In particular:

    - all functions that are to be bootstrapped are collected into
      one function called repl_step, and

    - all labels are expanded away before code installation.

*)

val bc_num_def = Define `
  bc_num s =
     case s of
       Stack Pop => (0:num,0:num,0:num)
     | Stack (Pops n) => (1,n,0)
     | Stack (PushInt i) => (3,Num (ABS i),if i < 0 then 1 else 0)
     | Stack (Cons n m) => (4,n,m)
     | Stack (Load n) => (5,n,0)
     | Stack (Store n) => (6,n,0)
     | Stack (LoadRev n) => (7,n,0)
     | Stack (El n) => (8,n,0)
     | Stack (TagEq n) => (9,n,0)
     | Stack IsBlock => (10,0,0)
     | Stack Equal => (11,0,0)
     | Stack Add => (12,0,0)
     | Stack Sub => (13,0,0)
     | Stack Mult => (14,0,0)
     | Stack Div => (15,0,0)
     | Stack Mod => (16,0,0)
     | Stack Less => (17,0,0)
     | Label n => (20,n,0)
     | Jump (Addr n) => (21,n,0)
     | JumpIf (Addr n) => (22,n,0)
     | Call (Addr n) => (23,n,0)
     | PushPtr (Addr n) => (24,n,0)
     | Jump (Lab n) => (41,n,0)
     | JumpIf (Lab n) => (42,n,0)
     | Call (Lab n) => (43,n,0)
     | PushPtr (Lab n) => (44,n,0)
     | CallPtr => (26,0,0)
     | Return => (27,0,0)
     | PushExc => (28,0,0)
     | PopExc => (29,0,0)
     | Ref => (30,0,0)
     | Deref => (31,0,0)
     | Update => (32,0,0)
     | Stop => (33,0,0)
     | Tick => (34,0,0)
     | Print => (35,0,0)
     | PrintC c => (36,ORD c,0)
     | Stop => (37,0,0)`;

val num_bc_def = Define `
  num_bc (n,x1,x2) =
    if n = 0 then Stack Pop else
    if n = 1 then Stack (Pops x1) else
    if n = 3 then Stack (PushInt (if x2 = 1 then 0 - & x1 else & x1)) else
    if n = 4 then Stack (Cons x1 x2) else
    if n = 5 then Stack (Load x1) else
    if n = 6 then Stack (Store x1) else
    if n = 7 then Stack (LoadRev x1) else
    if n = 8 then Stack (El x1) else
    if n = 9 then Stack (TagEq x1) else
    if n = 10 then Stack (IsBlock) else
    if n = 11 then Stack (Equal) else
    if n = 12 then Stack (Add) else
    if n = 13 then Stack (Sub) else
    if n = 14 then Stack (Mult) else
    if n = 15 then Stack (Div) else
    if n = 16 then Stack (Mod) else
    if n = 17 then Stack (Less) else
    if n = 20 then Label x1 else
    if n = 21 then Jump (Addr x1) else
    if n = 22 then JumpIf (Addr x1) else
    if n = 23 then Call (Addr x1) else
    if n = 24 then PushPtr (Addr x1) else
    if n = 41 then Jump (Lab x1) else
    if n = 42 then JumpIf (Lab x1) else
    if n = 43 then Call (Lab x1) else
    if n = 44 then PushPtr (Lab x1) else
    if n = 26 then CallPtr else
    if n = 27 then Return else
    if n = 28 then PushExc else
    if n = 29 then PopExc else
    if n = 30 then Ref else
    if n = 31 then Deref else
    if n = 32 then Update else
    if n = 33 then Stop else
    if n = 34 then Tick else
    if n = 35:num then Print else
      PrintC (CHR x1)`

val num_bc_bc_num = store_thm("num_bc_bc_num",
  ``!x. num_bc (bc_num x) = x``,
  Cases THEN TRY (Cases_on `b`) THEN TRY (Cases_on `l`) THEN EVAL_TAC
  THEN SIMP_TAC std_ss [stringTheory.ORD_BOUND]
  THEN Cases_on `i < 0` THEN FULL_SIMP_TAC std_ss []
  THEN intLib.COOPER_TAC);

val bc_num_lists_def = Define `
  bc_num_lists xs ys = MAP bc_num xs ++ [(18,0,0)] ++ MAP bc_num ys`;

val empty_bc_state_def = Define `
  empty_bc_state = <| stack := []; code := []; pc := 0; refs := FEMPTY;
                      handler := 0; clock := NONE; output := "";
                      cons_names := []; inst_length := real_inst_length |>`;

val repl_step_def = Define `
  repl_step state =
    case state of
    | NONE => (* first time around *)
       let len = 0 in
       let code = PrintE ++ [Stop] in
       let labs = collect_labels code len real_inst_length in
       let len = code_length real_inst_length code in
       let code1 = inst_labels labs code in
       let code = SND (SND compile_primitives) in
       let code = REVERSE code in
       let labs = FUNION labs (collect_labels code len real_inst_length) in
       let len = len + code_length real_inst_length code in
       let code = inst_labels labs code in
         INL ([],bc_num_lists code1 code,len,labs,
                 initial_repl_fun_state,initial_repl_fun_state)
    | SOME (tokens,new_s,len,labs,s',s_exc) => (* received some input *)
        let s = if new_s then s' else s_exc in
        case parse_elaborate_infertype_compile (MAP token_of_sym tokens) s of
        | Success (code,s',s_exc) =>
            let code = REVERSE code in
            let labs = FUNION labs (collect_labels code len real_inst_length) in
            let len = len + code_length real_inst_length code in
            let code = inst_labels labs code in
              INL (cpam s'.rcompiler_state,bc_num_lists [] code,len,labs,s_exc,s')
        | Failure error_msg => INR (error_msg,(F,len,labs,s,s))`

val set_cons_names_def = Define `
  set_cons_names m bs =
    bs with <| cons_names := m; output := "" |>`;

val install_bc_lists_def = Define `
  (install_bc_lists [] bs = bs) /\
  (install_bc_lists (x::xs) bs =
     if FST x = 18 then
       install_bc_lists xs (bs with
         pc := next_addr bs.inst_length bs.code)
     else
       install_bc_lists xs (bs with
         code := bs.code ++ [num_bc x]))`;

val tac = (WF_REL_TAC `measure (LENGTH o FST o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lexer_implTheory.lex_until_top_semicolon_alt_LESS);

val main_loop_alt_def = tDefine "main_loop_alt" `
  main_loop_alt bs input state init =
    case repl_step state of
      | INR (error_msg,x) =>
            Result error_msg
             (case lex_until_top_semicolon_alt input of
              | NONE => Terminate
              | SOME (ts,rest) =>
                  (main_loop_alt bs rest (SOME (ts,x)) F))
      | INL (m,code,new_state) =>
        case bc_eval (set_cons_names m (install_bc_lists code bs)) of
        | NONE => Diverge
        | SOME new_bs =>
            let new_bs = (if init then new_bs with stack := TL new_bs.stack
                                  else new_bs) in
            let new_s = (bc_fetch new_bs = SOME Stop) in
              (if init then I else Result (REVERSE new_bs.output))
                (case lex_until_top_semicolon_alt input of
                 | NONE => Terminate
                 | SOME (ts,rest) =>
                     (main_loop_alt new_bs rest (SOME (ts,new_s,new_state)) F)) ` tac

val repl_fun_alt_def = Define `
  repl_fun_alt input = main_loop_alt empty_bc_state input NONE T`;

val _ = export_theory();
