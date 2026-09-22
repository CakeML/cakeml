(*
  Translates xaig_to_cnf (and its dependencies on xaig).
*)
Theory aig_to_cnfProg
Ancestors
  ml_translator  (* MEMBER_INTRO *)
  ml_monad_translator aig_cert_encodeProg xaig_to_cnf aig_to_cnf
Libs
  preamble ml_translatorLib ml_monad_translator_interfaceLib

val _ = translation_extends "aig_cert_encodeProg";

(* The xaig definitions name the gate, input and latch type variables
   'a, 'i and 'l. *)
val to_num =
  INST_TYPE [alpha |-> “:num”, mk_vartype "'i" |-> “:num”,
             mk_vartype "'l" |-> “:num”];

(*----------------------------------------------------------------------*
   the parsed circuit: xor/ite detection
 *----------------------------------------------------------------------*)

val r = translate (xaig_to_cnfTheory.match_xor_def |> to_num);
val r = translate (xaig_to_cnfTheory.match_ite_def |> to_num);

(*----------------------------------------------------------------------*
   the lowering to CNF
 *----------------------------------------------------------------------*)

val r = translate cnfTheory.negate_def;

val r = translate xaig_to_cnfTheory.xvar_to_num_def;
val r = translate xaig_to_cnfTheory.xvar_to_lit_def;
val r = translate xaig_to_cnfTheory.eq_every_pos_def;
val r = translate xaig_to_cnfTheory.eq_every_neg_def;
val r = translate xaig_to_cnfTheory.or_every_pos_def;
val r = translate xaig_to_cnfTheory.or_every_neg_def;
val r = translate xaig_to_cnfTheory.xor_pos_def;
val r = translate xaig_to_cnfTheory.xor_neg_def;
val r = translate xaig_to_cnfTheory.ite_pos_def;
val r = translate xaig_to_cnfTheory.ite_neg_def;
val r = translate xaig_to_cnfTheory.gty_pos_def;
val r = translate xaig_to_cnfTheory.gty_neg_def;
val r = translate xaig_to_cnfTheory.xgty_to_cnf_def;

val r = translate xaig_to_cnfTheory.flip_pol_def;
val r = translate xaig_to_cnfTheory.gty_pols_def;

val r = translate (xaig_to_cnfTheory.gty_lits_def |> to_num);

(*----------------------------------------------------------------------*
   the monadic state: arrays standing in for the finite maps of the
   lowering, one field per map, indexed by the names the map is keyed by
 *----------------------------------------------------------------------*)

val _ = set_up_monadic_translator ();

Datatype:
  state_refs = <|
    seen_array : bool list;
    nm_array   : num option list;
    im_array   : num option list;
    lm_array   : num option list;
    next_ref   : num;
    gm_array   : (num,num,num) aig$lit list option list;
    pm_array   : (bool # bool) option list
  |>
End

Datatype:
  state_exn = Subscript
End

val _ = local_state_config
        |> with_state “:state_refs”
        |> with_exception “:state_exn”
        |> with_refs [("next_ref", “2:num”)]
        |> with_fixed_arrays
             [("seen_array", “F”, 0, “Subscript”, “Subscript”),
              ("nm_array", “NONE:num option”, 0, “Subscript”, “Subscript”),
              ("im_array", “NONE:num option”, 0, “Subscript”, “Subscript”),
              ("lm_array", “NONE:num option”, 0, “Subscript”, “Subscript”),
              ("gm_array", “NONE:(num,num,num) aig$lit list option”, 0,
               “Subscript”, “Subscript”),
              ("pm_array", “NONE:(bool # bool) option”, 0,
               “Subscript”, “Subscript”)]
        |> start_translation;

val run_init_state_def =
  define_run “:state_refs”
    ["seen_array", "nm_array", "im_array", "lm_array", "gm_array", "pm_array"]
    "init_state";

Theorem run_eq_M_success:
  (run f x = M_success r) ⇔ ∃s1. f x = (M_success r, s1)
Proof
  simp [ml_monadBaseTheory.run_def]
  \\ Cases_on ‘f x’ \\ gvs []
QED

Theorem IMP_Mupdate_M_success:
  (y = LUPDATE x n l) ∧ n < LENGTH l ⇒
  (Mupdate e x n l = M_success y)
Proof
  simp [ml_monadBaseTheory.Mupdate_eq]
QED

(*----------------------------------------------------------------------*
   sizing the arrays: the largest names a circuit mentions
 *----------------------------------------------------------------------*)

(* The largest gate name a circuit mentions; the pruning's state relation
   measures its array against it. *)

Definition max_each_def:
  (max_each ([]:(num,num,num) aig$lit list) acc = acc) ∧
  (max_each ((x,b)::xs) acc =
    case x of
    | Gate n => max_each xs (MAX n acc)
    | _      => max_each xs acc)
End

Definition max_gt_def:
  (max_gt ([]:(num,num,num) xaig) acc = acc) ∧
  (max_gt ((m,gt)::xs) acc = max_gt xs (MAX m (max_each (gty_lits gt) acc)))
End

Theorem max_each_acc:
  ∀xs m. max_each xs m = MAX (max_each xs 0) m
Proof
  Induct \\ simp [max_each_def]
  \\ Cases
  \\ Cases_on ‘q’
  \\ simp_tac (srw_ss()) [max_each_def]
  \\ pop_assum (fn th => once_rewrite_tac [th] \\ assume_tac th)
  \\ rewrite_tac [GSYM MAX_ASSOC, MAX_0] \\ rw []
QED

Theorem max_gt_acc:
  ∀xs m. max_gt xs m = MAX (max_gt xs 0) m
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ once_rewrite_tac [max_gt_def] >- rw [MAX_DEF]
  \\ PairCases \\ rewrite_tac [max_gt_def]
  \\ pop_assum (fn th => simp [Once (GSYM th)] \\ assume_tac th)
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ pop_assum (fn th => simp [Once (GSYM th)] \\ assume_tac th)
  \\ rewrite_tac [GSYM MAX_ASSOC] \\ rw []
  \\ rpt AP_TERM_TAC
  \\ simp [Once max_each_acc]
QED

(* Every gate name a literal, or a circuit, mentions is below the bound. *)

Definition lit_below_def:
  lit_below L ((v,b):(num,num,num) aig$lit) ⇔ ∀k. (v = Gate k) ⇒ k < L
End

Definition gate_below_def:
  gate_below L ((m,gt):(num,num,num) gate) ⇔
    m < L ∧ EVERY (lit_below L) (gty_lits gt)
End

(* Every input or latch index a literal mentions, by a selector on its
   variable, is below the bound. *)

Definition inp_key_def:
  inp_key (v:(num,num,num) var) =
    case v of Base (Input i) => SOME i | _ => NONE
End

Definition lat_key_def:
  lat_key (v:(num,num,num) var) =
    case v of Base (Latch l) => SOME l | _ => NONE
End

Definition key_below_def:
  key_below f L ((v,b):(num,num,num) aig$lit) ⇔
    ∀k. (f v = SOME (k:num)) ⇒ k < L
End

(* The sizing pass proper: the largest gate name, input index and latch
   index a circuit mentions, each folded through its own accumulator. *)

Definition lit_g_def:
  lit_g ((v,b):(num,num,num) aig$lit) a =
    case v of Gate n => if a < n then n else a | _ => a
End

Definition lit_i_def:
  lit_i ((v,b):(num,num,num) aig$lit) a =
    case v of Base (Input k) => if a < k then k else a | _ => a
End

Definition lit_l_def:
  lit_l ((v,b):(num,num,num) aig$lit) a =
    case v of Base (Latch k) => if a < k then k else a | _ => a
End

(* One walk over the circuit.  The second argument holds the literals of the
   current gate that are still to be folded: And and Or gates hand over
   their input list, Xor and Ite gates fold their inputs in place. *)

Definition max_names_def:
  (max_names ([]:(num,num,num) xaig) ([]:(num,num,num) aig$lit list)
     mg mi ml = (mg,mi,ml)) ∧
  (max_names xs (t::ts) mg mi ml =
     max_names xs ts (lit_g t mg) (lit_i t mi) (lit_l t ml)) ∧
  (max_names ((m,gt)::xs) [] mg mi ml =
     let mg1 = if mg < m then m else mg in
       case gt of
       | And ts => max_names xs ts mg1 mi ml
       | Or ts => max_names xs ts mg1 mi ml
       | Xor t1 t2 =>
           max_names xs [] (lit_g t2 (lit_g t1 mg1)) (lit_i t2 (lit_i t1 mi))
             (lit_l t2 (lit_l t1 ml))
       | Ite t1 t2 t3 =>
           max_names xs [] (lit_g t3 (lit_g t2 (lit_g t1 mg1)))
             (lit_i t3 (lit_i t2 (lit_i t1 mi)))
             (lit_l t3 (lit_l t2 (lit_l t1 ml))))
Termination
  WF_REL_TAC ‘measure (λ(xs,ts,mg,mi,ml).
    LENGTH ts + list_size (λ(m,g). LENGTH (gty_lits g) + 1) xs)’
  \\ rw [list_size_def]
End

val _ = translate lit_g_def;
val _ = translate lit_i_def;
val _ = translate lit_l_def;
val _ = translate max_names_def;

(* Each fold is monotone in its accumulator. *)

Theorem lit_g_ge:
  k ≤ a ⇒ k ≤ lit_g t a
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"] \\ rw [lit_g_def]
QED

Theorem lit_i_ge:
  k ≤ a ⇒ k ≤ lit_i t a
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"] \\ rw [lit_i_def]
  \\ namedCases_on ‘bv’ ["", "k", "k"] \\ rw []
QED

Theorem lit_l_ge:
  k ≤ a ⇒ k ≤ lit_l t a
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"] \\ rw [lit_l_def]
  \\ namedCases_on ‘bv’ ["", "k", "k"] \\ rw []
QED

Theorem max_names_ge:
  ∀xs ts mg mi ml g1 i1 l1.
    (max_names xs ts mg mi ml = (g1,i1,l1)) ⇒ mg ≤ g1 ∧ mi ≤ i1 ∧ ml ≤ l1
Proof
  ho_match_mp_tac max_names_ind \\ rpt conj_tac
  >- simp [max_names_def]
  >- (
    simp [max_names_def] \\ rpt strip_tac
    \\ first_x_assum drule \\ strip_tac
    \\ irule LESS_EQ_TRANS \\ first_x_assum $ irule_at (Pos last)
    \\ simp [lit_g_ge, lit_i_ge, lit_l_ge])
  \\ rpt gen_tac \\ rename1 ‘(m,g)::xs’ \\ simp [max_names_def]
  \\ rpt strip_tac \\ Cases_on ‘g’ \\ gvs []
  \\ irule LESS_EQ_TRANS \\ first_x_assum $ irule_at (Pos last)
  \\ simp [lit_g_ge, lit_i_ge, lit_l_ge] \\ rw []
QED

(* A bound on a fold's result bounds everything folded into it. *)

Theorem lit_g_below:
  lit_g t a < L ⇒ a < L ∧ lit_below L t
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  \\ rw [lit_g_def, lit_below_def] \\ gvs []
QED

Theorem lit_i_below:
  lit_i t a < L ⇒ a < L ∧ key_below inp_key L t
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  >- rw [lit_i_def, key_below_def, inp_key_def]
  \\ namedCases_on ‘bv’ ["", "k", "k"]
  \\ rw [lit_i_def, key_below_def, inp_key_def] \\ gvs []
QED

Theorem lit_l_below:
  lit_l t a < L ⇒ a < L ∧ key_below lat_key L t
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  >- rw [lit_l_def, key_below_def, lat_key_def]
  \\ namedCases_on ‘bv’ ["", "k", "k"]
  \\ rw [lit_l_def, key_below_def, lat_key_def] \\ gvs []
QED

(* The gate component of the pass is the maximum the pruning proofs use. *)

Theorem max_each_lit_g:
  max_each (t::ts) a = max_each ts (lit_g t a)
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  \\ simp [max_each_def, lit_g_def]
  \\ ‘(if a < n then n else a) = MAX n a’ by (rw [MAX_DEF] \\ decide_tac)
  \\ simp []
QED

Theorem max_each_MAX:
  max_each ts (MAX m a) = MAX m (max_each ts a)
Proof
  once_rewrite_tac [max_each_acc] \\ simp [AC MAX_ASSOC MAX_COMM]
QED

Theorem lit_g_MAX:
  lit_g t (MAX m a) = MAX m (lit_g t a)
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  \\ rw [lit_g_def, MAX_DEF] \\ decide_tac
QED

Theorem max_names_gt:
  ∀xs ts mg mi ml. FST (max_names xs ts mg mi ml) = max_gt xs (max_each ts mg)
Proof
  ho_match_mp_tac max_names_ind \\ rpt conj_tac
  >- simp [max_names_def, max_gt_def, max_each_def]
  >- simp [max_names_def, max_each_lit_g]
  \\ rpt gen_tac \\ rename1 ‘(m,g)::xs’
  \\ simp [max_names_def, max_gt_def, max_each_def]
  \\ ‘(if mg < m then m else mg) = MAX m mg’ by (rw [MAX_DEF] \\ decide_tac)
  \\ Cases_on ‘g’
  \\ gvs [max_each_def, max_each_lit_g, max_each_MAX, lit_g_MAX]
QED

(*----------------------------------------------------------------------*
   pruning a circuit
 *----------------------------------------------------------------------*)

Definition mark_each_gate_def:
  (mark_each_gate ([]:(num,num,num) aig$lit list) = return ()) ∧
  (mark_each_gate ((x,b)::xs) =
    case x of
    | Gate n => do u <- update_seen_array n T; mark_each_gate xs od
    | _      => mark_each_gate xs)
End

val _ = m_translate mark_each_gate_def;

Definition xprune_loop_def:
  (xprune_loop ([]:(num,num,num) xaig) acc = return acc) ∧
  (xprune_loop ((m,gt)::xs) acc =
     do
       b <- seen_array_sub m;
       if b then
         do
           u <- update_seen_array m F;
           u <- mark_each_gate (gty_lits gt);
           xprune_loop xs ((m,gt)::acc)
         od
       else
         xprune_loop xs acc
     od)
End

val _ = m_translate xprune_loop_def;

Definition xprune_for_array_def:
  xprune_for_array root aig =
    do
      u <- update_seen_array root T;
      xprune_loop aig []
    od
End

val _ = m_translate xprune_for_array_def;

Definition run_xprune_def:
  run_xprune root aig l =
    run_init_state (xprune_for_array root aig)
      <| seen_array := (l,F); nm_array := (0,NONE); im_array := (0,NONE);
         lm_array := (0,NONE); next_ref := 0; gm_array := (0,NONE);
         pm_array := (0,NONE) |>
End

val run_xprune_v_thm = m_translate_run run_xprune_def;

Definition state_rel_def:
  state_rel s seen aig ⇔
    max_gt aig 0 < LENGTH s.seen_array ∧
    ∀i. i < LENGTH s.seen_array ⇒
        (EL i s.seen_array = i ∈ FDOM seen)
End

Theorem new_live_update:
  ∀xs m n. new_live xs (m |+ (n,())) = new_live xs m |+ (n,())
Proof
  Induct \\ simp [aig_to_cnfTheory.new_live_def]
  \\ PairCases \\ namedCases_on ‘h0’ ["k", "v"]
  \\ rw [aig_to_cnfTheory.new_live_def]
  \\ Cases_on ‘k = n’ \\ gvs []
  \\ irule FUPDATE_COMMUTES \\ simp []
QED

Theorem mark_each_gate_thm:
  ∀xs s seen aig.
    state_rel s seen aig ∧
    max_each xs 0 < LENGTH s.seen_array ⇒
    ∃s1. (mark_each_gate xs s = (M_success (),s1)) ∧
         state_rel s1 (new_live xs seen) aig
Proof
  Induct
  \\ gvs [aig_to_cnfTheory.new_live_def, mark_each_gate_def,
          ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases
  \\ gvs [aig_to_cnfTheory.new_live_def, mark_each_gate_def,
          ml_monadBaseTheory.st_ex_return_def]
  \\ CASE_TAC \\ fs [max_each_def]
  \\ simp [ml_monadBaseTheory.st_ex_bind_def]
  \\ rw [Once state_rel_def, AllCaseEqs(), PULL_EXISTS]
  \\ simp [fetch "-" "update_seen_array_def"]
  \\ simp [ml_monadBaseTheory.Marray_update_def]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ conj_tac >- fs [Once max_each_acc]
  \\ simp [GSYM new_live_update]
  \\ first_x_assum irule
  \\ fs [state_rel_def, EL_LUPDATE, Once max_each_acc]
  \\ rw []
QED

Theorem xprune_loop_thm:
  ∀aig seen acc s.
    state_rel s seen aig ⇒
    ∃s1. xprune_loop aig acc s =
         (M_success (xprune_rev aig seen acc),s1)
Proof
  Induct
  >- simp [xprune_loop_def, ml_monadBaseTheory.st_ex_return_def, xprune_rev_def]
  \\ PairCases \\ rw []
  \\ simp [xprune_loop_def, ml_monadBaseTheory.st_ex_bind_def]
  \\ gvs [fetch "-" "seen_array_sub_def"]
  \\ simp [ml_monadBaseTheory.Marray_sub_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq] \\ simp []
  \\ have ‘oEL h0 s.seen_array = SOME (h0 ∈ FDOM seen)’
  >- (gvs [state_rel_def, max_gt_def]
      \\ pop_assum $ qspec_then ‘h0’ mp_tac
      \\ fs [Once max_gt_def]
      \\ fs [Once max_gt_acc]
      \\ simp [oEL_THM])
  \\ gvs [oEL_THM]
  \\ simp [xprune_rev_def, FLOOKUP_DEF]
  \\ have ‘state_rel s seen aig’
  >- (gvs [state_rel_def, max_gt_def] \\ rw []
      \\ fs [Once max_gt_def]
      \\ fs [Once max_gt_acc])
  \\ reverse IF_CASES_TAC >- simp []
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ simp [fetch "-" "update_seen_array_def"]
  \\ simp [ml_monadBaseTheory.Marray_update_def]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ qabbrev_tac ‘s0 = s with seen_array := s.seen_array❲h0 ↦ F❳’
  \\ have ‘state_rel s0 (seen \\ h0) aig’
  >- (gvs [state_rel_def, Abbr‘s0’] \\ rw [EL_LUPDATE]
      \\ eq_tac \\ simp [])
  \\ have ‘max_each (gty_lits h1) 0 < LENGTH s0.seen_array’
  >-
   (gvs [state_rel_def, max_gt_def]
    \\ fs [Once max_gt_acc] \\ gvs [Abbr ‘s0’])
  \\ drule_all mark_each_gate_thm
  \\ strip_tac \\ gvs []
QED

(* The pruning, given the size of its array: every gate name in the circuit,
   and the root, must be below it. *)

Definition xprune_for_sz_def:
  xprune_for_sz L root aig =
    case run_xprune root aig L of
    | M_success x => x
    | _           => []
End

Theorem xprune_for_sz_eq:
  max_gt aig root < L ⇒ (xprune_for_sz L root aig = xprune_for root aig)
Proof
  strip_tac
  \\ ‘root < L ∧ max_gt aig 0 < L’ by (
    qpat_x_assum ‘max_gt _ _ < L’ mp_tac \\ simp [Once max_gt_acc, MAX_LT])
  \\ suff ‘run_xprune root aig L = M_success $ xprune_for root aig’
  >- simp [xprune_for_sz_def]
  \\ gvs [run_xprune_def, run_init_state_def, run_eq_M_success]
  \\ gvs [xprune_for_array_def, ml_monadBaseTheory.st_ex_bind_def]
  \\ gvs [definition "update_seen_array_def"]
  \\ simp [AllCaseEqs(), ml_monadBaseTheory.Marray_update_def]
  \\ simp [PULL_EXISTS]
  \\ irule_at Any IMP_Mupdate_M_success \\ simp []
  \\ gvs [xprune_for_def, GSYM PULL_EXISTS]
  \\ irule xprune_loop_thm
  \\ simp [state_rel_def, oEL_THM]
  \\ rw []
  \\ simp [listTheory.EL_LUPDATE]
  \\ Cases_on ‘i = root’ \\ gvs []
  \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ simp []
QED

val _ = translate xprune_for_sz_def;

(* Pruning only drops gates, so any bound on the input bounds the output. *)

Theorem xprune_rev_MEM:
  ∀xs live acc x.
    MEM x (xprune_rev (xs:(num,num,num) xaig) live acc) ⇒ MEM x xs ∨ MEM x acc
Proof
  Induct \\ simp [xprune_rev_def]
  \\ PairCases \\ rename [‘(m,g)::xs’]
  \\ rw [xprune_rev_def] \\ Cases_on ‘FLOOKUP live m’ \\ gvs []
  \\ res_tac \\ gvs []
QED

Theorem xprune_for_EVERY:
  EVERY P (aig:(num,num,num) xaig) ⇒ EVERY P (xprune_for root aig)
Proof
  rw [xprune_for_def, EVERY_MEM] \\ drule xprune_rev_MEM \\ simp []
QED

(*----------------------------------------------------------------------*
   renaming a circuit
 *----------------------------------------------------------------------*)

Definition xrename_lit_M_def:
  xrename_lit_M ((x,b):(num,num,num) aig$lit) =
    case x of
    | Gate n =>
        do
          t <- nm_array_sub n;
          return (case t of NONE => (Base Ff,b) | SOME t => (Gate t,b))
        od
    | Base (Input i) =>
        do
          t <- im_array_sub i;
          case t of
          | NONE =>
              do
                nxt <- get_next_ref;
                u <- update_im_array i (SOME nxt);
                u <- set_next_ref (nxt + 1);
                return (Base (Input nxt),b)
              od
          | SOME t => return (Base (Input t),b)
        od
    | Base (Latch l) =>
        do
          t <- lm_array_sub l;
          case t of
          | NONE =>
              do
                nxt <- get_next_ref;
                u <- update_lm_array l (SOME nxt);
                u <- set_next_ref (nxt + 1);
                return (Base (Latch nxt),b)
              od
          | SOME t => return (Base (Latch t),b)
        od
    | Base Ff => return (Base Ff,b)
End

val _ = m_translate xrename_lit_M_def;

Definition xrename_lits_M_def:
  (xrename_lits_M ([]:(num,num,num) aig$lit list) acc = return acc) ∧
  (xrename_lits_M (t::ts) acc =
    do t1 <- xrename_lit_M t; xrename_lits_M ts (t1::acc) od)
End

val _ = m_translate xrename_lits_M_def;

Definition xrename_gty_M_def:
  (xrename_gty_M (And ts : (num,num,num) gty) =
    do ts1 <- xrename_lits_M ts []; return (And ts1) od) ∧
  (xrename_gty_M (Xor t1 t2) =
    do u1 <- xrename_lit_M t1; u2 <- xrename_lit_M t2; return (Xor u1 u2) od) ∧
  (xrename_gty_M (Ite t1 t2 t3) =
    do
      u1 <- xrename_lit_M t1;
      u2 <- xrename_lit_M t2;
      u3 <- xrename_lit_M t3;
      return (Ite u1 u2 u3)
    od) ∧
  (xrename_gty_M (Or ts) =
    do ts1 <- xrename_lits_M ts []; return (Or ts1) od)
End

val _ = m_translate xrename_gty_M_def;

Definition xaig_rename_loop_def:
  (xaig_rename_loop ([]:(num,num,num) xaig) acc = return acc) ∧
  (xaig_rename_loop ((m,g)::xs) acc =
    do
      g1 <- xrename_gty_M g;
      nxt <- get_next_ref;
      u <- update_nm_array m (SOME nxt);
      u <- set_next_ref (nxt + 1);
      xaig_rename_loop xs ((nxt,g1)::acc)
    od)
End

val _ = m_translate xaig_rename_loop_def;

Definition xaig_rename_M_def:
  xaig_rename_M xs =
    do
      acc <- xaig_rename_loop xs [];
      nxt <- get_next_ref;
      return (acc,nxt)
    od
End

val _ = m_translate xaig_rename_M_def;

Definition run_rename_def:
  run_rename xs lg li ll =
    run_init_state (xaig_rename_M xs)
      <| seen_array := (0,F); nm_array := (lg,NONE); im_array := (li,NONE);
         lm_array := (ll,NONE); next_ref := 2; gm_array := (0,NONE);
         pm_array := (0,NONE) |>
End

val run_rename_v_thm = m_translate_run run_rename_def;

Definition ren_rel_def:
  ren_rel s next im lm nm ⇔
    (s.next_ref = next) ∧
    (∀i. i < LENGTH s.im_array ⇒ (EL i s.im_array = FLOOKUP im i)) ∧
    (∀i. i < LENGTH s.lm_array ⇒ (EL i s.lm_array = FLOOKUP lm i)) ∧
    (∀i. i < LENGTH s.nm_array ⇒ (EL i s.nm_array = FLOOKUP nm i))
End

Definition lens_def:
  lens s = (LENGTH s.nm_array, LENGTH s.im_array, LENGTH s.lm_array)
End

(* Every name a literal mentions is within the array it is looked up in. *)

Definition ren_below_def:
  ren_below L (t:(num,num,num) aig$lit) ⇔
    lit_below (FST L) t ∧ key_below inp_key (FST (SND L)) t ∧
    key_below lat_key (SND (SND L)) t
End

Definition ren_gate_below_def:
  ren_gate_below L ((m,g):(num,num,num) gate) ⇔
    m < FST L ∧ EVERY (ren_below L) (gty_lits g)
End

Theorem max_names_below:
  ∀xs ts mg mi ml g1 i1 l1.
    (max_names xs ts mg mi ml = (g1,i1,l1)) ⇒
    EVERY (ren_below (g1+1,i1+1,l1+1)) ts ∧
    EVERY (ren_gate_below (g1+1,i1+1,l1+1)) xs
Proof
  ho_match_mp_tac max_names_ind \\ rpt conj_tac
  >- simp [max_names_def]
  >- (
    simp [max_names_def] \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ drule max_names_ge \\ strip_tac
    \\ first_x_assum drule \\ strip_tac \\ simp []
    \\ ‘lit_g t mg < g1 + 1 ∧ lit_i t mi < i1 + 1 ∧ lit_l t ml < l1 + 1’ by
         decide_tac
    \\ imp_res_tac lit_g_below \\ imp_res_tac lit_i_below
    \\ imp_res_tac lit_l_below
    \\ simp [ren_below_def])
  \\ rpt gen_tac \\ rename1 ‘(m,g)::xs’ \\ simp [max_names_def]
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘g’ \\ gvs []
  \\ drule max_names_ge \\ strip_tac
  \\ simp [ren_gate_below_def]
  \\ fs [LESS_EQ_IFF_LESS_SUC, GSYM ADD1]
  \\ rpt (dxrule_then strip_assume_tac lit_g_below)
  \\ rpt (dxrule_then strip_assume_tac lit_i_below)
  \\ rpt (dxrule_then strip_assume_tac lit_l_below)
  \\ gvs [ren_below_def]
QED

Theorem xrename_lit_M_thm:
  ren_rel s next im lm nm ∧ ren_below (lens s) t ∧
  (xrename_lit t next im lm nm = (t1,next1,im1,lm1)) ⇒
  ∃s1. (xrename_lit_M t s = (M_success t1, s1)) ∧
       ren_rel s1 next1 im1 lm1 nm ∧ (lens s1 = lens s)
Proof
  PairCases_on ‘t’ \\ rename [‘xrename_lit (v,b)’]
  \\ namedCases_on ‘v’ ["n", "bv"]
  >- (
    rw [xrename_lit_M_def, xrename_lit_def, ren_below_def, lit_below_def,
        lens_def, ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def, fetch "-" "nm_array_sub_def",
        ml_monadBaseTheory.Marray_sub_def]
    \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq] \\ gvs [ren_rel_def]
    \\ Cases_on ‘FLOOKUP nm n’ \\ gvs [])
  \\ namedCases_on ‘bv’ ["", "i", "l"]
  >- (
    rw [xrename_lit_M_def, xrename_lit_def, lens_def,
        ml_monadBaseTheory.st_ex_return_def]
    \\ gvs [ren_rel_def])
  >- (
    rw [xrename_lit_M_def, xrename_lit_def, ren_below_def, key_below_def,
        inp_key_def, lens_def, ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def, fetch "-" "im_array_sub_def",
        ml_monadBaseTheory.Marray_sub_def]
    \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq] \\ gvs [ren_rel_def]
    \\ Cases_on ‘FLOOKUP im i’ \\ gvs []
    \\ simp [fetch "-" "get_next_ref_def", fetch "-" "update_im_array_def",
             fetch "-" "set_next_ref_def", ml_monadBaseTheory.Marray_update_def]
    \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq]
    \\ simp [EL_LUPDATE, FLOOKUP_UPDATE]
    \\ rpt strip_tac \\ IF_CASES_TAC \\ gvs [])
  \\ rw [xrename_lit_M_def, xrename_lit_def, ren_below_def, key_below_def,
         lat_key_def, lens_def, ml_monadBaseTheory.st_ex_bind_def,
         ml_monadBaseTheory.st_ex_return_def, fetch "-" "lm_array_sub_def",
         ml_monadBaseTheory.Marray_sub_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq] \\ gvs [ren_rel_def]
  \\ Cases_on ‘FLOOKUP lm l’ \\ gvs []
  \\ simp [fetch "-" "get_next_ref_def", fetch "-" "update_lm_array_def",
           fetch "-" "set_next_ref_def", ml_monadBaseTheory.Marray_update_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq]
  \\ simp [EL_LUPDATE, FLOOKUP_UPDATE]
  \\ rpt strip_tac \\ IF_CASES_TAC \\ gvs []
QED

Theorem xrename_lits_M_thm:
  ∀ts s next im lm nm acc ts1 next1 im1 lm1.
    ren_rel s next im lm nm ∧ EVERY (ren_below (lens s)) ts ∧
    (xrename_lits ts next im lm nm acc = (ts1,next1,im1,lm1)) ⇒
    ∃s1. (xrename_lits_M ts acc s = (M_success ts1, s1)) ∧
         ren_rel s1 next1 im1 lm1 nm ∧ (lens s1 = lens s)
Proof
  Induct
  >- simp [xrename_lits_def, xrename_lits_M_def,
           ml_monadBaseTheory.st_ex_return_def]
  \\ rw [xrename_lits_def, xrename_lits_M_def,
         ml_monadBaseTheory.st_ex_bind_def]
  \\ pairarg_tac \\ gvs []
  \\ drule_all xrename_lit_M_thm \\ strip_tac \\ simp []
  \\ qpat_x_assum ‘lens _ = lens _’ (SUBST_ALL_TAC o GSYM)
  \\ first_x_assum irule \\ simp []
  \\ first_assum $ irule_at Any \\ simp []
QED

Theorem xrename_gty_M_thm:
  ren_rel s next im lm nm ∧ EVERY (ren_below (lens s)) (gty_lits g) ∧
  (xrename_gty g next im lm nm = (g1,next1,im1,lm1)) ⇒
  ∃s1. (xrename_gty_M g s = (M_success g1, s1)) ∧
       ren_rel s1 next1 im1 lm1 nm ∧ (lens s1 = lens s)
Proof
  Cases_on ‘g’
  \\ rw [xrename_gty_M_def, xrename_gty_def,
         ml_monadBaseTheory.st_ex_bind_def,
         ml_monadBaseTheory.st_ex_return_def]
  \\ rpt (pairarg_tac \\ gvs [])
  >- (drule_all xrename_lits_M_thm \\ strip_tac \\ gvs [])
  >- (
    drule_all xrename_lit_M_thm \\ strip_tac \\ simp []
    \\ qpat_x_assum ‘lens _ = lens _’ (SUBST_ALL_TAC o GSYM)
    \\ drule_all xrename_lit_M_thm \\ strip_tac \\ gvs [])
  >- (
    drule_all xrename_lit_M_thm \\ strip_tac \\ simp []
    \\ qpat_x_assum ‘lens _ = lens _’ (SUBST_ALL_TAC o GSYM)
    \\ drule_all xrename_lit_M_thm \\ strip_tac \\ simp []
    \\ qpat_x_assum ‘lens _ = lens _’ (SUBST_ALL_TAC o GSYM)
    \\ drule_all xrename_lit_M_thm \\ strip_tac \\ gvs [])
  \\ drule_all xrename_lits_M_thm \\ strip_tac \\ gvs []
QED

Theorem xaig_rename_loop_thm:
  ∀xs s next im lm nm acc acc1 next1 im1 lm1 nm1.
    ren_rel s next im lm nm ∧ EVERY (ren_gate_below (lens s)) xs ∧
    (xaig_rename_rev xs acc next im lm nm = (acc1,next1,im1,lm1,nm1)) ⇒
    ∃s1. (xaig_rename_loop xs acc s = (M_success acc1, s1)) ∧
         ren_rel s1 next1 im1 lm1 nm1 ∧ (lens s1 = lens s)
Proof
  Induct
  >- simp [xaig_rename_rev_def, xaig_rename_loop_def,
           ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases \\ rename [‘(m,g)::xs’]
  \\ rw [xaig_rename_rev_def, xaig_rename_loop_def,
         ml_monadBaseTheory.st_ex_bind_def, ren_gate_below_def]
  \\ pairarg_tac \\ gvs []
  \\ rename1 ‘xrename_gty g next im lm nm = (g1,nxt,im2,lm2)’
  \\ drule_all xrename_gty_M_thm \\ strip_tac \\ simp []
  \\ rename1 ‘xrename_gty_M g s = (M_success _, sg)’
  \\ gvs [lens_def]
  \\ simp [fetch "-" "get_next_ref_def", fetch "-" "update_nm_array_def",
           fetch "-" "set_next_ref_def", ml_monadBaseTheory.Marray_update_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ ‘sg.next_ref = nxt’ by fs [ren_rel_def] \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘xaig_rename_loop _ _ s2’
  \\ first_x_assum (drule_at (Pos last))
  \\ disch_then (qspec_then ‘s2’ mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (
      qpat_x_assum ‘ren_rel sg _ _ _ _’ mp_tac
      \\ simp [ren_rel_def, Abbr ‘s2’, EL_LUPDATE, FLOOKUP_UPDATE]
      \\ rpt strip_tac \\ IF_CASES_TAC \\ gvs [])
    \\ simp [Abbr ‘s2’])
  \\ strip_tac \\ gvs [Abbr ‘s2’]
QED

Definition xaig_rename_top_def:
  xaig_rename_top (xs:(num,num,num) xaig) =
    let (acc,next,im,lm,nm) = xaig_rename_rev xs [] 2 FEMPTY FEMPTY FEMPTY in
      (acc,next)
End

(* The renaming, given the sizes of its three arrays. *)

Definition xaig_rename_sz_def:
  xaig_rename_sz lg li ll xs =
    case run_rename xs lg li ll of
    | M_success r => r
    | _           => ([],2)
End

Theorem xaig_rename_sz_eq:
  EVERY (ren_gate_below (lg,li,ll)) xs ⇒
  (xaig_rename_sz lg li ll xs = xaig_rename_top xs)
Proof
  strip_tac
  \\ suff ‘run_rename xs lg li ll = M_success $ xaig_rename_top xs’
  >- simp [xaig_rename_sz_def]
  \\ simp [run_rename_def, run_init_state_def, run_eq_M_success,
           xaig_rename_top_def, xaig_rename_M_def,
           ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def]
  \\ pairarg_tac \\ gvs []
  \\ qmatch_goalsub_abbrev_tac ‘xaig_rename_loop _ _ s0’
  \\ drule_at (Pos last) xaig_rename_loop_thm
  \\ disch_then (qspec_then ‘s0’ mp_tac)
  \\ impl_tac
  >- (
    conj_tac >- simp [ren_rel_def, Abbr ‘s0’, EL_REPLICATE]
    \\ simp [Abbr ‘s0’, lens_def])
  \\ strip_tac \\ simp [fetch "-" "get_next_ref_def"]
  \\ gvs [ren_rel_def]
QED

val _ = translate xaig_rename_sz_def;

(* Every name the renaming hands out is a value of its counter, which only
   grows, so the renamed circuit is bounded by the final counter. *)

Definition maps_below_def:
  maps_below next (im:num |-> num) (lm:num |-> num) (nm:num |-> num) ⇔
    (∀k v. (FLOOKUP im k = SOME v) ⇒ v < next) ∧
    (∀k v. (FLOOKUP lm k = SOME v) ⇒ v < next) ∧
    (∀k v. (FLOOKUP nm k = SOME v) ⇒ v < next)
End

Theorem lit_below_mono:
  L ≤ L' ∧ lit_below L t ⇒ lit_below L' t
Proof
  PairCases_on ‘t’ \\ simp [lit_below_def] \\ rpt strip_tac
  \\ res_tac \\ decide_tac
QED

Theorem gate_below_mono:
  L ≤ L' ∧ gate_below L x ⇒ gate_below L' x
Proof
  PairCases_on ‘x’ \\ simp [gate_below_def, EVERY_MEM] \\ rpt strip_tac
  \\ res_tac \\ irule lit_below_mono
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Theorem EVERY_lit_below_mono:
  L ≤ L' ∧ EVERY (lit_below L) ts ⇒ EVERY (lit_below L') ts
Proof
  rw [EVERY_MEM] \\ res_tac \\ irule lit_below_mono
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Theorem EVERY_gate_below_mono:
  L ≤ L' ∧ EVERY (gate_below L) xs ⇒ EVERY (gate_below L') xs
Proof
  rw [EVERY_MEM] \\ res_tac \\ irule gate_below_mono
  \\ first_assum $ irule_at (Pos last) \\ simp []
QED

Theorem xrename_lit_bound:
  (xrename_lit (t:(num,num,num) aig$lit) next im lm nm = (t1,next1,im1,lm1)) ∧
  maps_below next im lm nm ⇒
  next ≤ next1 ∧ lit_below next1 t1 ∧ maps_below next1 im1 lm1 nm
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["n", "bv"]
  \\ rw [xrename_lit_def, AllCaseEqs()]
  \\ gvs [lit_below_def]
  >- (fs [maps_below_def] \\ res_tac \\ simp [])
  \\ gvs [maps_below_def, FLOOKUP_UPDATE] \\ rw [] \\ res_tac \\ simp []
QED

Theorem xrename_lits_bound:
  ∀ts next im lm nm acc ts1 next1 im1 lm1.
    (xrename_lits (ts:(num,num,num) aig$lit list) next im lm nm acc =
       (ts1,next1,im1,lm1)) ∧
    maps_below next im lm nm ∧ EVERY (lit_below next) acc ⇒
    next ≤ next1 ∧ EVERY (lit_below next1) ts1 ∧ maps_below next1 im1 lm1 nm
Proof
  Induct \\ simp [xrename_lits_def] \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ drule_all xrename_lit_bound \\ strip_tac
  \\ first_x_assum drule
  \\ impl_tac
  >- (
    simp [] \\ irule EVERY_lit_below_mono
    \\ first_assum $ irule_at (Pos last) \\ simp [])
  \\ strip_tac \\ simp []
QED

Theorem xrename_gty_bound:
  (xrename_gty (g:(num,num,num) gty) next im lm nm = (g1,next1,im1,lm1)) ∧
  maps_below next im lm nm ⇒
  next ≤ next1 ∧ EVERY (lit_below next1) (gty_lits g1) ∧
  maps_below next1 im1 lm1 nm
Proof
  Cases_on ‘g’ \\ simp [xrename_gty_def] \\ strip_tac
  >- (pairarg_tac \\ gvs [] \\ drule xrename_lits_bound \\ simp [])
  >- (
    pairarg_tac \\ gvs [] \\ dxrule_all xrename_lit_bound \\ strip_tac
    \\ pairarg_tac \\ gvs [] \\ dxrule_all xrename_lit_bound \\ strip_tac
    \\ simp [] \\ irule lit_below_mono
    \\ first_assum $ irule_at (Pos last) \\ simp [])
  >- (
    pairarg_tac \\ gvs [] \\ dxrule_all xrename_lit_bound \\ strip_tac
    \\ pairarg_tac \\ gvs [] \\ dxrule_all xrename_lit_bound \\ strip_tac
    \\ pairarg_tac \\ gvs [] \\ dxrule_all xrename_lit_bound \\ strip_tac
    \\ simp [] \\ conj_tac \\ irule lit_below_mono
    \\ first_assum $ irule_at (Pos last) \\ simp [])
  \\ pairarg_tac \\ gvs [] \\ drule xrename_lits_bound \\ simp []
QED

Theorem xaig_rename_rev_bound:
  ∀xs acc next im lm nm acc1 next1 im1 lm1 nm1.
    (xaig_rename_rev (xs:(num,num,num) xaig) acc next im lm nm =
       (acc1,next1,im1,lm1,nm1)) ∧
    maps_below next im lm nm ∧ EVERY (gate_below next) acc ⇒
    next ≤ next1 ∧ EVERY (gate_below next1) acc1
Proof
  Induct \\ simp [xaig_rename_rev_def]
  \\ PairCases \\ rename [‘(m,g)::xs’]
  \\ simp [xaig_rename_rev_def] \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ gvs []
  \\ drule_all xrename_gty_bound \\ strip_tac
  \\ first_x_assum drule
  \\ impl_tac
  >- (
    conj_tac
    >- (gvs [maps_below_def, FLOOKUP_UPDATE] \\ rw [] \\ res_tac \\ simp [])
    \\ simp [gate_below_def]
    \\ conj_tac
    >- (
      irule EVERY_lit_below_mono
      \\ first_assum $ irule_at (Pos last) \\ simp [])
    \\ irule EVERY_gate_below_mono
    \\ first_assum $ irule_at (Pos last) \\ simp [])
  \\ strip_tac \\ simp []
QED

(*----------------------------------------------------------------------*
   xor/ite detection
 *----------------------------------------------------------------------*)

(* The two gate inputs of a binary And gate with positive inputs, which is
   the only shape the detection reads the map at. *)

Definition and2_gates_def:
  and2_gates (g:(num,num,num) gty) =
    case g of
    | And [(Gate l,T);(Gate r,T)] => SOME (l,r)
    | _ => NONE
End

Definition opt_pair_def:
  opt_pair (x:(num,num,num) aig$lit list option) y =
    case (x,y) of
    | (SOME [l0;l1], SOME [r0;r1]) =>
        if match_xor l0 l1 r0 r1 then SOME (Xor l0 l1)
        else (case match_ite l0 l1 r0 r1 of
              | SOME (c,t,e) => SOME (Ite c t e)
              | NONE => NONE)
    | _ => NONE
End

val _ = translate and2_gates_def;
val _ = translate opt_pair_def;

Theorem optimize_gate_and2:
  optimize_gate g gm =
    case and2_gates g of
    | NONE => NONE
    | SOME (l,r) => opt_pair (FLOOKUP gm l) (FLOOKUP gm r)
Proof
  rw [optimize_gate_def, and2_gates_def, opt_pair_def]
  \\ every_case_tac \\ gvs []
QED

Theorem and2_gates_below:
  (and2_gates g = SOME (l,r)) ∧ EVERY (lit_below L) (gty_lits g) ⇒
  l < L ∧ r < L
Proof
  rw [and2_gates_def] \\ every_case_tac \\ gvs [lit_below_def]
QED

Definition optimize_gate_M_def:
  optimize_gate_M (g:(num,num,num) gty) =
    case and2_gates g of
    | NONE => return NONE
    | SOME (l,r) =>
        do
          x <- gm_array_sub l;
          y <- gm_array_sub r;
          return (opt_pair x y)
        od
End

val _ = m_translate optimize_gate_M_def;

Definition add_and_M_def:
  add_and_M n (g:(num,num,num) gty) =
    case g of
    | And [a;b] => update_gm_array n (SOME [a;b])
    | _ => return ()
End

val _ = m_translate add_and_M_def;

Definition xaig_opt_loop_def:
  (xaig_opt_loop ([]:(num,num,num) xaig) acc = return acc) ∧
  (xaig_opt_loop ((n,g)::xs) acc =
    do
      og <- optimize_gate_M g;
      u <- add_and_M n g;
      xaig_opt_loop xs ((n, case og of SOME g1 => g1 | NONE => g)::acc)
    od)
End

val _ = m_translate xaig_opt_loop_def;

Definition xaig_opt_M_def:
  xaig_opt_M xs = xaig_opt_loop xs []
End

val _ = m_translate xaig_opt_M_def;

Definition run_opt_def:
  run_opt xs l =
    run_init_state (xaig_opt_M xs)
      <| seen_array := (0,F); nm_array := (0,NONE); im_array := (0,NONE);
         lm_array := (0,NONE); next_ref := 0; gm_array := (l,NONE);
         pm_array := (0,NONE) |>
End

val run_opt_v_thm = m_translate_run run_opt_def;

Definition gm_rel_def:
  gm_rel s gm ⇔
    ∀i. i < LENGTH s.gm_array ⇒ (EL i s.gm_array = FLOOKUP gm i)
End

Theorem optimize_gate_M_thm:
  gm_rel s gm ∧ EVERY (lit_below (LENGTH s.gm_array)) (gty_lits g) ⇒
  (optimize_gate_M g s = (M_success (optimize_gate g gm), s))
Proof
  rw [optimize_gate_M_def, optimize_gate_and2]
  \\ Cases_on ‘and2_gates g’ >- simp [ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases_on ‘x’ \\ rename [‘SOME (l,r)’]
  \\ drule_all and2_gates_below \\ strip_tac
  \\ simp [ml_monadBaseTheory.st_ex_bind_def,
           ml_monadBaseTheory.st_ex_return_def,
           fetch "-" "gm_array_sub_def", ml_monadBaseTheory.Marray_sub_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq]
  \\ gvs [gm_rel_def]
QED

Theorem add_and_M_thm:
  gm_rel s gm ∧ n < LENGTH s.gm_array ⇒
  ∃s1. (add_and_M n g s = (M_success (), s1)) ∧
       gm_rel s1 (add_and gm n g) ∧
       (LENGTH s1.gm_array = LENGTH s.gm_array)
Proof
  rw [add_and_M_def, add_and_def]
  \\ every_case_tac \\ gvs [ml_monadBaseTheory.st_ex_return_def]
  \\ simp [fetch "-" "update_gm_array_def",
           ml_monadBaseTheory.Marray_update_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ fs [gm_rel_def] \\ simp [EL_LUPDATE, FLOOKUP_UPDATE]
  \\ rpt strip_tac \\ Cases_on ‘i = n’ \\ gvs []
QED

Theorem xaig_opt_loop_thm:
  ∀xs s gm acc.
    gm_rel s gm ∧ EVERY (gate_below (LENGTH s.gm_array)) xs ⇒
    ∃s1. xaig_opt_loop xs acc s =
         (M_success (FST (xaig_opt_rev xs gm acc)), s1)
Proof
  Induct
  >- simp [xaig_opt_loop_def, xaig_opt_rev_def,
           ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases \\ rename [‘(n,g)::xs’]
  \\ rw [xaig_opt_loop_def, xaig_opt_rev_def, ml_monadBaseTheory.st_ex_bind_def,
         gate_below_def]
  \\ drule_all optimize_gate_M_thm \\ rw []
  \\ drule_all add_and_M_thm
  \\ disch_then (qspec_then ‘g’ strip_assume_tac) \\ simp []
  \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ (SUBST_ALL_TAC o GSYM)
  \\ first_x_assum irule \\ simp []
QED

Definition xaig_opt_top_def:
  xaig_opt_top xs = FST (xaig_opt_rev xs FEMPTY [])
End

(* The detection, given the size of its array. *)

Definition xaig_opt_sz_def:
  xaig_opt_sz L xs =
    case run_opt xs L of
    | M_success r => r
    | _           => []
End

Theorem xaig_opt_sz_eq:
  EVERY (gate_below L) xs ⇒ (xaig_opt_sz L xs = xaig_opt_top xs)
Proof
  strip_tac
  \\ suff ‘run_opt xs L = M_success $ xaig_opt_top xs’
  >- simp [xaig_opt_sz_def]
  \\ simp [run_opt_def, run_init_state_def, run_eq_M_success, xaig_opt_top_def,
           xaig_opt_M_def]
  \\ irule xaig_opt_loop_thm
  \\ simp [gm_rel_def, EL_REPLICATE]
QED

val _ = translate xaig_opt_sz_def;

(* The detection keeps the gate names and only builds gates from literals
   already in the circuit, so it preserves any bound. *)

Theorem lit_below_not:
  lit_below L (not t) ⇔ lit_below L t
Proof
  PairCases_on ‘t’ \\ simp [aigTheory.not_def, lit_below_def]
QED

Theorem optimize_gate_below:
  (optimize_gate g gm = SOME g1) ∧
  (∀k ts. (FLOOKUP gm k = SOME ts) ⇒ EVERY (lit_below L) ts) ⇒
  EVERY (lit_below L) (gty_lits g1)
Proof
  rw [optimize_gate_def] \\ gvs [AllCaseEqs(), match_ite_def]
  \\ res_tac \\ gvs [lit_below_not]
QED

Theorem xaig_opt_rev_below:
  ∀xs gm acc.
    EVERY (gate_below L) (xs:(num,num,num) xaig) ∧
    (∀k ts. (FLOOKUP gm k = SOME ts) ⇒ EVERY (lit_below L) ts) ∧
    EVERY (gate_below L) acc ⇒
    EVERY (gate_below L) (FST (xaig_opt_rev xs gm acc))
Proof
  Induct \\ simp [xaig_opt_rev_def]
  \\ PairCases \\ rename [‘(n,g)::xs’]
  \\ rw [xaig_opt_rev_def]
  \\ first_x_assum irule \\ simp []
  \\ conj_tac
  >- (
    rw [] \\ drule FLOOKUP_add_and \\ rw []
    >- gvs [gate_below_def]
    \\ res_tac \\ simp [])
  \\ gvs [gate_below_def] \\ CASE_TAC
  >- simp []
  \\ drule_all optimize_gate_below \\ simp []
QED

Theorem xaig_opt_top_below:
  EVERY (gate_below L) xs ⇒ EVERY (gate_below L) (xaig_opt_top xs)
Proof
  rw [xaig_opt_top_def] \\ irule xaig_opt_rev_below \\ simp []
QED

(*----------------------------------------------------------------------*
   lowering a renamed circuit to CNF
 *----------------------------------------------------------------------*)

Definition pol_of_M_def:
  pol_of_M n =
    do
      p <- pm_array_sub n;
      return (case p of NONE => (F,F) | SOME pl => pl)
    od
End

val _ = m_translate pol_of_M_def;

Definition add_pol_M_def:
  add_pol_M (p,n) m =
    do
      pl <- pol_of_M m;
      case pl of (p1,n1) => update_pm_array m (SOME (p ∨ p1, n ∨ n1))
    od
End

val _ = m_translate add_pol_M_def;

Definition add_lit_pol_M_def:
  add_lit_pol_M pl ((v,b):(num,num,num) aig$lit) =
    case v of
    | Gate m => add_pol_M (if b then flip_pol pl else pl) m
    | Base _ => return ()
End

val _ = m_translate add_lit_pol_M_def;

Definition add_lits_pol_M_def:
  (add_lits_pol_M [] = return ()) ∧
  (add_lits_pol_M ((pl,t)::rest) =
    do u <- add_lit_pol_M pl t; add_lits_pol_M rest od)
End

val _ = m_translate add_lits_pol_M_def;

Definition add_gty_pol_M_def:
  add_gty_pol_M pl gt = add_lits_pol_M (gty_pols pl gt)
End

val _ = m_translate add_gty_pol_M_def;

Definition xto_cnf_loop_def:
  (xto_cnf_loop ([]:(num,num,num) xaig) acc = return acc) ∧
  (xto_cnf_loop ((n,gt)::xs) acc =
    do
      pl <- pol_of_M n;
      u <- add_gty_pol_M pl gt;
      xto_cnf_loop xs (xgty_to_cnf pl n gt ++ acc)
    od)
End

val _ = m_translate xto_cnf_loop_def;

Definition direct_M_def:
  direct_M (xaig:(num,num,num) xaig) =
    case xaig of
    | [] => return [[]]
    | ((root,_)::_) =>
        do
          u <- update_pm_array root (SOME (T,F));
          c <- xto_cnf_loop xaig [];
          return ([Neg 1] :: [Pos root] :: c)
        od
End

val _ = m_translate direct_M_def;

Definition run_direct_def:
  run_direct xaig l =
    run_init_state (direct_M xaig)
      <| seen_array := (0,F); nm_array := (0,NONE); im_array := (0,NONE);
         lm_array := (0,NONE); next_ref := 0; gm_array := (0,NONE);
         pm_array := (l,NONE) |>
End

val run_direct_v_thm = m_translate_run run_direct_def;

Definition pm_rel_def:
  pm_rel s pm ⇔
    ∀i. i < LENGTH s.pm_array ⇒ (EL i s.pm_array = FLOOKUP pm i)
End

Theorem pol_of_M_thm:
  pm_rel s pm ∧ n < LENGTH s.pm_array ⇒
  (pol_of_M n s = (M_success (pol_of pm n), s))
Proof
  rw [pol_of_M_def, ml_monadBaseTheory.st_ex_bind_def,
      ml_monadBaseTheory.st_ex_return_def, fetch "-" "pm_array_sub_def",
      ml_monadBaseTheory.Marray_sub_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Msub_eq]
  \\ gvs [pm_rel_def, pol_of_def]
QED

Theorem add_pol_M_thm:
  pm_rel s pm ∧ m < LENGTH s.pm_array ⇒
  ∃s1. (add_pol_M pl m s = (M_success (), s1)) ∧
       pm_rel s1 (add_pol pl m pm) ∧
       (LENGTH s1.pm_array = LENGTH s.pm_array)
Proof
  PairCases_on ‘pl’ \\ strip_tac
  \\ simp [add_pol_M_def, ml_monadBaseTheory.st_ex_bind_def, add_pol_def]
  \\ drule_all pol_of_M_thm \\ rw []
  \\ Cases_on ‘pol_of pm m’ \\ rename1 ‘pol_of pm m = (p1,n1)’ \\ gvs []
  \\ simp [fetch "-" "update_pm_array_def",
           ml_monadBaseTheory.Marray_update_def]
  \\ DEP_REWRITE_TAC [ml_monadBaseTheory.Mupdate_eq] \\ simp []
  \\ fs [pm_rel_def] \\ simp [EL_LUPDATE, FLOOKUP_UPDATE]
  \\ rpt strip_tac \\ Cases_on ‘i = m’ \\ gvs []
QED

Theorem add_lit_pol_M_thm:
  pm_rel s pm ∧ lit_below (LENGTH s.pm_array) t ⇒
  ∃s1. (add_lit_pol_M pl t s = (M_success (), s1)) ∧
       pm_rel s1 (add_lit_pol pl t pm) ∧
       (LENGTH s1.pm_array = LENGTH s.pm_array)
Proof
  PairCases_on ‘t’ \\ namedCases_on ‘t0’ ["m", "v"]
  \\ rw [add_lit_pol_M_def, add_lit_pol_def, lit_below_def,
         ml_monadBaseTheory.st_ex_return_def]
  \\ irule add_pol_M_thm \\ simp []
QED

Theorem add_lits_pol_M_thm:
  ∀ls s pm.
    pm_rel s pm ∧ EVERY (λ(pl,t). lit_below (LENGTH s.pm_array) t) ls ⇒
    ∃s1. (add_lits_pol_M ls s = (M_success (), s1)) ∧
         pm_rel s1 (add_lits_pol ls pm) ∧
         (LENGTH s1.pm_array = LENGTH s.pm_array)
Proof
  Induct
  >- simp [add_lits_pol_M_def, add_lits_pol_def,
           ml_monadBaseTheory.st_ex_return_def]
  \\ Cases \\ rename [‘(pl,t)::ls’]
  \\ rw [add_lits_pol_M_def, add_lits_pol_def,
         ml_monadBaseTheory.st_ex_bind_def]
  \\ drule_all add_lit_pol_M_thm
  \\ disch_then (qspec_then ‘pl’ strip_assume_tac) \\ simp []
  \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ (SUBST_ALL_TAC o GSYM)
  \\ first_x_assum irule \\ simp []
QED

Theorem gty_pols_below:
  EVERY (lit_below L) (gty_lits g) ⇒
  EVERY (λ(pl,t). lit_below L t) (gty_pols pl g)
Proof
  rw [gty_pols_def] \\ Cases_on ‘g’
  \\ gvs [EVERY_MEM, MEM_MAP, PULL_EXISTS, ELIM_UNCURRY] \\ rw [] \\ gvs []
QED

Theorem add_gty_pol_M_thm:
  ∀pl g s pm.
    pm_rel s pm ∧ EVERY (lit_below (LENGTH s.pm_array)) (gty_lits g) ⇒
    ∃s1. (add_gty_pol_M pl g s = (M_success (), s1)) ∧
         pm_rel s1 (add_gty_pol pl g pm) ∧
         (LENGTH s1.pm_array = LENGTH s.pm_array)
Proof
  rw [add_gty_pol_M_def, add_gty_pol_def]
  \\ irule add_lits_pol_M_thm \\ simp [gty_pols_below]
QED

Theorem xto_cnf_loop_thm:
  ∀xs s pm acc.
    pm_rel s pm ∧ EVERY (gate_below (LENGTH s.pm_array)) xs ⇒
    ∃s1. xto_cnf_loop xs acc s = (M_success (xto_cnf xs pm acc), s1)
Proof
  Induct
  >- simp [xto_cnf_loop_def, xto_cnf_def, ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases \\ rename [‘(n,g)::xs’]
  \\ rw [xto_cnf_loop_def, xto_cnf_def, ml_monadBaseTheory.st_ex_bind_def,
         gate_below_def]
  \\ drule_all pol_of_M_thm \\ rw []
  \\ drule_all add_gty_pol_M_thm
  \\ disch_then (qspec_then ‘pol_of pm n’ strip_assume_tac) \\ simp []
  \\ qpat_x_assum ‘LENGTH _ = LENGTH _’ (SUBST_ALL_TAC o GSYM)
  \\ first_x_assum irule \\ simp []
QED

(* The lowering to CNF, given the size of its array. *)

Definition direct_sz_def:
  direct_sz L xaig =
    case run_direct xaig L of
    | M_success c => c
    | _           => [[]]
End

Theorem direct_sz_eq:
  EVERY (gate_below L) xaig ⇒ (direct_sz L xaig = direct_xaig_to_cnf xaig)
Proof
  strip_tac
  \\ Cases_on ‘xaig’
  >- simp [direct_sz_def, direct_xaig_to_cnf_def, run_direct_def,
           run_init_state_def, direct_M_def, ml_monadBaseTheory.run_def,
           ml_monadBaseTheory.st_ex_return_def]
  \\ PairCases_on ‘h’ \\ rename [‘(root,g)::xs’]
  \\ ‘root < L’ by gvs [gate_below_def]
  \\ suff ‘run_direct ((root,g)::xs) L =
           M_success $ direct_xaig_to_cnf ((root,g)::xs)’
  >- simp [direct_sz_def]
  \\ simp [run_direct_def, run_init_state_def, run_eq_M_success, direct_M_def,
           ml_monadBaseTheory.st_ex_bind_def,
           ml_monadBaseTheory.st_ex_return_def,
           fetch "-" "update_pm_array_def",
           ml_monadBaseTheory.Marray_update_def]
  \\ simp [AllCaseEqs(), PULL_EXISTS]
  \\ irule_at Any IMP_Mupdate_M_success \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘xto_cnf_loop _ _ s0’
  \\ qspecl_then [‘(root,g)::xs’, ‘s0’, ‘FEMPTY |+ (root,(T,F))’, ‘[]’]
       mp_tac xto_cnf_loop_thm
  \\ impl_tac
  >- (
    conj_tac
    >- (
      simp [Abbr ‘s0’, pm_rel_def, EL_LUPDATE, FLOOKUP_UPDATE]
      \\ rpt strip_tac \\ Cases_on ‘i = root’ \\ gvs [EL_REPLICATE])
    \\ fs [Abbr ‘s0’])
  \\ strip_tac \\ simp [direct_xaig_to_cnf_def]
QED

val _ = translate direct_sz_def;

(*----------------------------------------------------------------------*
   plugging everything together: the circuit is measured once, pruning
   and renaming are sized from that measurement, and the renamed circuit
   is bounded by the counter the renaming returns
 *----------------------------------------------------------------------*)

Theorem xaig_to_cnf_alt:
  xaig_to_cnf (xaig:(num,num,num) xaig) root =
    let (mg,mi,ml) = max_names xaig [] root 0 0 in
    let xaig_1 = xprune_for_sz (mg+1) root xaig in
    let (xaig_2, limit) = xaig_rename_sz (mg+1) (mi+1) (ml+1) xaig_1 in
    let xaig_3 = xaig_opt_sz limit (REVERSE xaig_2) in
      (direct_sz limit xaig_3, limit)
Proof
  simp [xaig_to_cnf_def]
  \\ qspecl_then [‘xaig’, ‘[]’, ‘root’, ‘0’, ‘0’] mp_tac max_names_gt
  \\ qspecl_then [‘xaig’, ‘[]’, ‘root’, ‘0’, ‘0’] mp_tac max_names_below
  \\ Cases_on ‘max_names xaig [] root 0 0’
  \\ rename [‘max_names _ _ _ _ _ = (mg,mil)’]
  \\ Cases_on ‘mil’ \\ rename [‘max_names _ _ _ _ _ = (mg,mi,ml)’]
  \\ simp [max_each_def] \\ rpt strip_tac \\ gvs []
  \\ simp [xprune_for_sz_eq]
  \\ ‘EVERY (ren_gate_below (max_gt xaig root + 1,mi+1,ml+1))
        (xprune_for root xaig)’ by simp [xprune_for_EVERY]
  \\ simp [xaig_rename_sz_eq, xaig_rename_top_def]
  \\ pairarg_tac \\ gvs []
  \\ rename1 ‘xaig_rename_rev _ _ _ _ _ _ = (ys,limit,_)’
  \\ PairCases_on ‘x’ \\ gvs []
  \\ drule xaig_rename_rev_bound \\ simp [maps_below_def] \\ strip_tac
  \\ simp [xaig_opt_sz_eq, xaig_opt_top_def]
  \\ pairarg_tac \\ gvs []
  \\ ‘EVERY (gate_below limit) xaig_3’ by (
    ‘xaig_3 = xaig_opt_top (REVERSE ys)’ by simp [xaig_opt_top_def]
    \\ simp [] \\ irule xaig_opt_top_below \\ simp [])
  \\ simp [direct_sz_eq]
QED

val r = translate xaig_to_cnf_alt;
