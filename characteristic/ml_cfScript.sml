open HolKernel Parse boolLib bossLib preamble;
open set_sepTheory ml_translatorTheory;

val _ = new_theory "ml_cf";

(*
STAR_def
bigStepTheory.evaluate_rules
bigStepTheory.evaluate_ind
*)

(*
  ``(one (2n, Litv (IntLit 5)) * anything) (fmap2set (s:v_map))``
*)

(* val _ = type_abbrev("v_map",``:num |-> v``); *)

(* val fmap2set_def = Define ` *)
(*   fmap2set (f:'a |-> 'b) = fun2set ((\a. f ' a), FDOM f)` *)

(* val storev2v_def = Define ` *)
(*   storev2v (Refv v) = v`; *)

(* val store2fmap_aux_def = Define ` *)
(*   store2fmap_aux n [] = FEMPTY /\ *)
(*   store2fmap_aux n (h::t) = (store2fmap_aux (n+1: num) t) |+ (n, storev2v h)`; *)

(* val store2fmap_def = Define `store2fmap l = store2fmap_aux (0: num) l`; *)

(* val state_disjoint_def = Define ` *)
(*   state_disjoint s1 s2 = DISJOINT (fmap2set s1) (fmap2set s2)`; *)

(* val state_disjoint_3_def = Define ` *)
(*   state_disjoint_3 s1 s2 s3 = *)
(*     (state_disjoint s1 s2 /\ state_disjoint s2 s3 /\ state_disjoint s1 s3)`; *)

(* val state_split_def = Define ` *)
(*   state_split s (u, v) = SPLIT (fmap2set s) (fmap2set u, fmap2set v)`; *)

(* val SPLIT_3_def = Define ` *)
(*   SPLIT_3 (s:'a set) (u,v,w) = *)
(*     ((u UNION v UNION w = s) /\ *)
(*      DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w)`; *)

(* val state_split_3_def = Define ` *)
(*   state_split_3 s (u, v, w) = *)
(*     SPLIT_3 (fmap2set s) (fmap2set u, fmap2set v, fmap2set w)`; *)

(* Heaps *)
val _ = type_abbrev("heap", ``:(num # v) -> bool``);

(* store2heap: v store -> heap *)
val storev2v_def = Define `
  storev2v (Refv v) = v`;

val store2heap_aux_def = Define `
  store2heap_aux n [] = ({}: heap) /\
  store2heap_aux n (h::t) = (n, storev2v h) INSERT (store2heap_aux (n+1: num) t)`;

val store2heap_def = Define `store2heap l = store2heap_aux (0: num) l`;

val store2heap_aux_append = Q.prove (
  `!s n x. store2heap_aux n (s ++ [Refv x]) = (LENGTH s + n, x) INSERT store2heap_aux n s`,
  Induct \\ fs [store2heap_aux_def, storev2v_def, INSERT_COMM]
  \\ `(LENGTH s + 1) = SUC (LENGTH s)` by RW_TAC arith_ss []
  \\ METIS_TAC []
);

val store2heap_append = Q.prove (
  `!s x. store2heap (s ++ [Refv x]) = (LENGTH s, x) INSERT store2heap s`,
  Induct \\ fs [store2heap_def, store2heap_aux_append]
);

(* st2heap: 'ffi state -> heap *)
val st2heap_def = Define `
  st2heap (:'ffi) (st: 'ffi state) = store2heap st.refs`;

(* Utils *)
val SPLIT3_def = Define `
  SPLIT3 (s:'a set) (u,v,w) =
    ((u UNION v UNION w = s) /\
     DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w)`;

(* Heap assertions *)
val _ = type_abbrev("hprop", ``:heap -> bool``);

val STARPOST_def = Define `
  STARPOST (Q: v -> hprop) (H: hprop) = \x. (Q x) * H`;

val SEP_IMPPOST_def = Define `
  SEP_IMPPOST (Q1: v -> hprop) (Q2: v -> hprop) =
    !x. SEP_IMP (Q1 x) (Q2 x)`;

val _ = overload_on ("*+", Term `STARPOST`);
val _ = add_infix ("*+", 480, HOLgrammars.LEFT);

(* Locality *)

(* local = frame rule + consequence rule + garbage collection *)

val local_def = Define `
  local cf env (H: hprop) (Q: v -> hprop) =
    !(h: heap). H h ==> ?H1 H2 H3 Q1.
      (H1 * H2) h /\
      cf env H1 Q1 /\
      SEP_IMPPOST (Q1 *+ H2) (Q *+ H3)`;

val is_local_def = Define `
  is_local cf = (cf = local cf)`;

(** App *)

val app_basic_def = Define `
  app_basic (:'ffi) (f: v) (x: v) env (H: hprop) (Q: v -> hprop) =
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap (:'ffi) st) (h, i) ==> H h ==>
      ?exp (v': v) (h': heap) (g: heap) (st': 'ffi state).
        SPLIT3 (st2heap (:'ffi) st') (h', g, i) /\
        Q v' h' /\
        (do_opapp [f;x] = SOME (env, exp)) /\
        evaluate F env st exp (st', Rval v')`;

val app_basic_local = Q.prove(
  `!f x. is_local (app_basic (:'ffi) f x)`,
  cheat);

val app_def = Define `
  app (:'ffi) (f: v) ([]: v list) env (H: hprop) (Q: v -> hprop) = F /\
  app (:'ffi) f [x] env H Q = app_basic (:'ffi) f x env H Q /\
  app (:'ffi) f (x::xs) env H Q =
    app_basic (:'ffi) f x env H
      (\g. SEP_EXISTS H'. H' * (cond (app (:'ffi) g xs env H' Q)))`;

val app_local = Q.prove(
  `!f xs. is_local (app (:'ffi) f xs)`,
  cheat);


val app_ref_def = Define `
  app_ref (:'ffi) (x: v) env H Q =
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap (:'ffi) st) (h, i) ==> H h ==>
      ?(s': v store) (r: num) h'.
        store_alloc (Refv x) st.refs = (s', r) /\
        h' = (r, x) INSERT h /\
        SPLIT3 (st2heap (:'ffi) (st with <| refs := s' |>)) (h', {}, i) /\
        Q (Loc r) h'`;

val app_assign_def = Define `
  app_assign (r: num) (x: v) env H Q =
    !h x'. (r, x') IN h ==> H h ==>
      Q (Conv NONE []) ((r, x) INSERT (h DELETE (r, x')))`;

val app_deref_def = Define `
  app_deref (r: num) env H Q =
    !h x. (r, x) IN h ==> H h ==> Q x h`;

(* CF *)

val cf_lit_def = Define `
  cf_lit l = local (\env H Q. SEP_IMP H (Q (Litv l)))`;

val cf_var_def = Define `
  cf_var name = local (\env H Q.
    !h. H h ==> ?v. lookup_var_id name env = SOME v /\ Q v h)`;

val cf_let_def = Define `
  cf_let F1 F2 = local (\env H Q.
    ?Q'. F1 env H Q' /\ !xv. F2 env (Q' xv) Q)`;

val exp2v_def = Define `
  exp2v _ (Lit l) = SOME (Litv l) /\
  exp2v env (Var name) = lookup_var_id name env /\
  exp2v _ _ = NONE`;

val exp2v_evaluate = Q.prove (
  `!e env st v. exp2v env e = SOME v ==>
   evaluate F env st e (st, Rval v)`,
  Induct \\ fs [exp2v_def] \\ prove_tac [bigStepTheory.evaluate_rules]
);

val cf_app2_def = Define `
  cf_app2 (:'ffi) f x = local (\env H Q.
    ?fv xv.
      exp2v env f = SOME fv /\
      exp2v env x = SOME xv /\
      app_basic (:'ffi) fv xv env H Q)`;

val cf_fundecl_def = Define `
  cf_fundecl (:'ffi) F1 F2 = local (\env H Q.
    !fv. (!xv H' Q'. F1 env H' Q' ==> app_basic (:'ffi) fv xv env H' Q') ==>
         F2 env H Q)`;

val cf_ref_def = Define `
  cf_ref (:'ffi) x = local (\env H Q.
    ?xv.
      exp2v env x = SOME xv /\
      app_ref (:'ffi) xv env H Q)`;

val cf_assign_def = Define `
  cf_assign r x = local (\env H Q.
    ?rv xv.
      exp2v env r = SOME (Loc rv) /\
      exp2v env x = SOME xv /\
      app_assign rv xv env H Q)`;

val cf_deref_def = Define `
  cf_deref r = local (\env H Q.
    ?rv.
      exp2v env r = SOME (Loc rv) /\
      app_deref rv env H Q)`;

val cf_def = Define `
  cf (:'ffi) (Lit l) = cf_lit l /\
  cf (:'ffi) (Var name) = cf_var name /\
  (* cf (:'ffi) (Let x e1 e2) = *)
  (*   (case (x, e1) of *)
  (*      | (SOME f, Fun _ body) => cf_fundecl (:'ffi) (cf (:'ffi) body) (cf (:'ffi) e2) *)
  (*      | (_, _) => cf_let (cf (:'ffi) e1) (cf (:'ffi) e2)) /\ *)

  cf (:'ffi) (Let (SOME f) (Fun _ body) e) =
    cf_fundecl (:'ffi) (cf (:'ffi) body) (cf (:'ffi) e) /\
  cf (:'ffi) (Let _ e1 e2) = cf_let (cf (:'ffi) e1) (cf (:'ffi) e2) /\
  cf (:'ffi) (App Opapp args) = 
    (case args of
      | [f; x] => cf_app2 (:'ffi) f x
      | _ => \env H Q. F) /\
  cf (:'ffi) (App Opref args) = 
    (case args of
       | [x] => cf_ref (:'ffi) x
       | _ => \env H Q. F) /\
  cf (:'ffi) (App Opassign args) = 
    (case args of
       | [r; x] => cf_assign r x
       | _ => \env H Q. F) /\
  cf (:'ffi) (App Opderef args) =
    (case args of
       | [r] => cf_deref r
       | _ => \env H Q. F) /\

  cf _ _ = \env H Q. F`;

val cf_defs = [cf_def, cf_lit_def, cf_var_def, cf_fundecl_def, cf_let_def,
               cf_app2_def, cf_ref_def, cf_assign_def, cf_deref_def];

val _ = export_theory();
