(*
  Kommentar som beskriver filen
*)

open preamble stackLangTheory stackSemTheory stack_callTheory;

val _ = new_theory("stack_callProof");

Theorem dest_StackFree_SOME[simp]:
  dest_StackFree x = SOME m <=> x = StackFree m
Proof
  Cases_on `x`
  \\ fs[dest_StackFree_def]
QED;

Theorem dest_StackFree_NONE[simp]:
  dest_StackFree x = NONE <=> !m. x <> StackFree m
Proof
  Cases_on `x`
  \\ fs[dest_StackFree_def]
QED;

val state_rel_def = Define `
  state_rel s t <=>
    t.clock = s.clock /\
    t.regs = s.regs /\
    t.stack = s.stack /\
    t.stack_space = s.stack_space /\
    ARB (* TODO: complete this *)`;

val tree_accurate_def = Define `
  tree_accurate tree (s_code:('a stackLang$prog) num_map) <=>
    T (* TODO: for every entry in tree,
                 there is code in s_code such that get_alloc for that
                 code returns what is stored in the tree (in other words,
                 tree is accurate w.r.t. s_code and get_alloc) *)`;

(*
  <| regs := dfgdg ; clock := 676 |> with clock := 3
=
  <| regs := dfgdg ; clock := 3 |>
*)

Theorem opt_code_correct:
  !prog s res s1 t tree.
    evaluate (prog,s) = (res,s1) /\ state_rel s t /\
    tree_accurate tree s.code /\ res <> SOME Error ==>
    ?ck t1. evaluate (opt_code prog tree,t with clock := t.clock + ck) =
              (res,t1) /\ state_rel s1 t1 /\ tree_accurate tree s1.code
Proof

  recInduct evaluate_ind \\ rpt strip_tac
  THEN1
   (rename [`Skip`]
    \\ fs [opt_code_def,evaluate_def] \\ rveq
    \\ qexists_tac `0` \\ fs [state_rel_def])
  THEN1
   (rename [`Halt`]
    \\ fs [opt_code_def,evaluate_def] \\ rveq
    \\ fs [get_var_def,state_rel_def]
    \\ TOP_CASE_TAC \\ fs []
    \\ rveq \\ fs [empty_env_def])
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1

   (rename [`Seq p1 p2`]
    \\ once_rewrite_tac [opt_code_def] \\ simp []
    \\ TOP_CASE_TAC
    THEN1
     (fs [evaluate_def]
      \\ Cases_on `evaluate (p1,s)` \\ fs []
      \\ rename [`evaluate (p1,s) = (res0,s0)`]
      \\ reverse (Cases_on `res0`)
      THEN1
       (fs [] \\ rveq \\ fs []
        \\ first_x_assum (qspecl_then [`t`,`tree`] mp_tac)
        \\ fs [] \\ strip_tac
        \\ qexists_tac `ck` \\ fs [])
      \\ fs []
      \\ first_x_assum (qspecl_then [`t`,`tree`] mp_tac)
      \\ fs [] \\ strip_tac
      \\ first_x_assum (qspecl_then [`t1`,`tree`] mp_tac)
      \\ fs [] \\ strip_tac
      \\ qexists_tac `ck+ck'`
      \\ qpat_x_assum `_ = (NONE,t1)` assume_tac
      \\ drule (GEN_ALL stackPropsTheory.evaluate_add_clock)
      \\ fs [])
    \\ cheat)

  \\ cheat
QED;

val _ = export_theory();
