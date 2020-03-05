(*
  Correctness proof for loop_to_word
*)

open preamble loopLangTheory loopSemTheory loopPropsTheory wordSemTheory

val _ = new_theory"loop_to_wordProof";

val _ = set_grammar_ancestry ["loopSem","loopProps","wordSem"];

Definition find_var_def:
  find_var ctxt v =
    case lookup v ctxt of
    | NONE => 0
    | SOME n => (n:num)
End

Definition mk_new_cutset_def:
  mk_new_cutset ctxt (l:num_set) =
    insert 0 () (fromAList (MAP (λ(n,x). (find_var ctxt n,x)) (toAList l)))
End

Definition comp_def:
  (comp ctxt (Seq p1 p2) l =
    let (p1,l) = comp ctxt p1 l in
    let (p2,l) = comp ctxt p2 l in
      (wordLang$Seq p1 p2,l)) /\
  (comp ctxt Break l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt Continue l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt (Loop l1 body l2) l = (Skip,l)) /\ (* not present in input *)
  (comp ctxt (If x1 x2 x3 p1 p2 l1) l =
    let (p1,l) = comp ctxt p1 l in
    let (p2,l) = comp ctxt p2 l in
      (Seq (If x1 x2 x3 p1 p2) Tick,l)) /\
  (comp ctxt (Mark p1) l = comp ctxt p1 l) /\
  (comp ctxt Tick l = (Tick,l)) /\
  (comp ctxt Skip l = (Skip,l)) /\
  (comp ctxt Fail l = (Skip,l)) /\
  (comp ctxt (Raise v) l = (Raise (find_var ctxt v),l)) /\
  (comp ctxt (Return v) l = (Return 0 (find_var ctxt v),l)) /\
  (comp ctxt (Call ret dest args handler) l =
     let args = MAP (find_var ctxt) args in
       case ret of
       | NONE (* tail-call *) => (wordLang$Call NONE dest args NONE,l)
       | SOME (v,live) =>
         let v = find_var ctxt v in
         let live = mk_new_cutset ctxt live in
         let new_l = (FST l, SND l+1) in
           case handler of
           | NONE => (wordLang$Call (SOME (v,live,Skip,l)) dest args NONE, new_l)
           | SOME (n,p1,p2,_) =>
              let (p1,l1) = comp ctxt p1 new_l in
              let (p2,l1) = comp ctxt p2 l1 in
              let new_l = (FST l1, SND l1+1) in
                (Seq (Call (SOME (v,live,p1,l)) dest args
                   (SOME (find_var ctxt n,p1,l1))) Tick, new_l)) /\
  (comp ctxt prog l = (Skip,l)) (* TODO *)
End

Definition locals_rel_def:
  locals_rel ctxt l1 l2 =
    ∀n v. lookup n l1 = SOME v ⇒
          ∃m. lookup n ctxt = SOME m ∧ lookup m l2 = SOME v ∧ m ≠ 0
End

Definition globals_rel_def:
  globals_rel g1 g2 =
    ∀n v. FLOOKUP g1 n = SOME v ⇒ FLOOKUP g2 (Temp n) = SOME v
End

Definition state_rel_def:
  state_rel ctxt s t <=>
    locals_rel ctxt s.locals t.locals ∧
    t.memory = s.memory ∧
    t.mdomain = s.mdomain ∧
    t.clock = s.clock ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    globals_rel s.globals t.store (* TODO: code *)
End

val goal =
  ``λ(prog, s). ∀res s1 t ctxt retv l.
      evaluate (prog,s) = (res,s1) ∧ state_rel ctxt s t ∧ res ≠ SOME Error ∧
      lookup 0 t.locals = SOME retv ∧ no_Loops prog ⇒
      ∃t1 res1.
         evaluate (FST (comp ctxt prog l),t) = (res1,t1) ∧
         state_rel ctxt s1 t1 ∧
         case res of
         | NONE => res1 = NONE ∧ lookup 0 t1.locals = SOME retv
         | SOME (Result v) => res1 = SOME (Result retv v)
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | SOME (Exception v) =>
            ∀r l1 l2. jump_exc t = SOME (r,l1,l2) ⇒
                      res1 = SOME (Exception (Loc l1 l2) v)
         | _ => F``

local
  val ind_thm = loopSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_Skip:
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ loopLang$Tick")
Proof
  cheat
QED

Theorem compile_Loop:
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  cheat
QED

Theorem compile_Mark:
  ^(get_goal "comp _ (Mark _)")
Proof
  cheat
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return")
Proof
  cheat
QED

Theorem compile_Raise:
  ^(get_goal "loopLang$Raise")
Proof
  cheat
QED

Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  cheat
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  cheat
QED

Theorem compile_Seq:
  ^(get_goal "comp _ (loopLang$Seq _ _)")
Proof
  cheat
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  cheat
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
  ^(get_goal "loopLang$LoadByte")
Proof
  cheat
QED

Theorem compile_StoreGlob:
  ^(get_goal "loopLang$StoreGlob") ∧
  ^(get_goal "loopLang$LoadGlob")
Proof
  cheat
QED

Theorem compile_FFI:
  ^(get_goal "loopLang$FFI")
Proof
  cheat
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  \\ EVERY (map strip_assume_tac [compile_Skip, compile_Raise,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_StoreGlob, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop])
  \\ asm_rewrite_tac [] \\ rw [] \\ rpt (pop_assum kall_tac)
QED

val _ = export_theory();
