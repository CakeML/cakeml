(*

An example of a queue data structure implemented using CakeML arrays, verified
using CF.

*)
open preamble basis

val _ = new_theory "queueProg";

val _ = translation_extends"basisProg";

val _ = Datatype `exn_type = FullQueue | EmptyQueue`;
val _ = register_exn_type ``:exn_type``;

val queue_decls = process_topdecs
   ‘fun empty_queue sz err = Ref (Array.array sz err, 0, 0, 0)

    fun full q =
      case !q of (a,f,r,c) => c = Array.length a

    fun enqueue q e =
      if full q then raise Fullqueue
      else
        case !q of
          (a,f,r,c) =>
              (Array.update a r e;
               q := (a,f,(r + 1) mod Array.length a,c+1))

    fun dequeue q =
      case !q of
        (a,f,r,c) =>
           if c = 0 then raise Emptyqueue
           else let val e = Array.sub a f
                in
                  q := (a, (f + 1) mod Array.length a, r, c - 1);
                  e
                end’;

val _ = append_prog queue_decls;

val EmptyQueue_exn_def = Define`
  EmptyQueue_exn v = QUEUEPROG_EXN_TYPE_TYPE EmptyQueue v`;

val EmptyQueue_exn_def = EVAL ``EmptyQueue_exn v``;

val lqueue_def = Define‘
  lqueue qels f r els ⇔
    f < LENGTH qels ∧ r < LENGTH qels ∧
    (f ≤ r ∧
     (∃pj rj. qels = pj ++ els ++ rj ∧ LENGTH pj = f ∧
              r + LENGTH rj = LENGTH qels) ∨
     r ≤ f ∧ (∃p s mj. qels = s ++ mj ++ p ∧ els = p ++ s ∧
                       r = LENGTH s ∧ f = r + LENGTH mj))’;

Theorem lqueue_empty:
   i < LENGTH xs ⇒ lqueue xs i i []
Proof
  simp[lqueue_def] >> strip_tac >>
  map_every qexists_tac [‘TAKE i xs’, ‘DROP i xs’] >> simp[]
QED

Theorem lqueue_enqueue:
   ∀x f r vs aels n.
      LENGTH vs < LENGTH aels ∧ lqueue aels f r vs ∧ (n = LENGTH aels) ⇒
      lqueue (LUPDATE x r aels) f ((r + 1) MOD n) (vs ++ [x])
Proof
  rw[lqueue_def] >> fs[]
  >- (Cases_on ‘r + 1 = LENGTH pj + (LENGTH rj + LENGTH vs)’ >> simp[]
      >- ((* wrap around happened *)
          disj2_tac >> qexists_tac `pj` >> simp[] >>
          simp[rich_listTheory.LUPDATE_APPEND2] >>
          ‘LENGTH rj = 1’ by simp[] >>
          ‘r = LENGTH pj + LENGTH vs’ by simp[] >> simp[] >>
          Cases_on `rj` >> fs[] >> simp[LUPDATE_def]) >>
      map_every qexists_tac [`pj`, `TL rj`] >> simp[] >>
      Cases_on `rj` >> fs[] >> simp[LUPDATE_APPEND2, LUPDATE_APPEND1] >>
      `r = LENGTH pj + LENGTH vs` by simp[] >> simp[LUPDATE_def]) >>
  (* already wrapped around *) disj2_tac >>
  map_every qexists_tac [‘p’, ‘s ++ [x]’, ‘TL mj’] >> Cases_on ‘mj’ >> fs[] >>
  simp[LUPDATE_APPEND2, LUPDATE_APPEND1]
QED

Theorem lqueue_dequeue:
   lqueue aels f r (v::vs) ⇒ lqueue aels ((f + 1) MOD LENGTH aels) r vs
Proof
  rw[lqueue_def] >> fs[]
  >- (disj1_tac >> map_every qexists_tac [‘pj ++ [v]’, ‘rj’] >> simp[]) >>
  Cases_on ‘LENGTH p = 1’ >> simp[]
  >- ((* f wraps around *) disj1_tac >> Cases_on ‘p’ >> fs[]) >>
  map_every qexists_tac [‘TL p’, ‘s’, ‘mj ++ [v]’] >> simp[] >>
  Cases_on ‘p’ >> fs[]
QED


(* Heap predicate for queues:
     QUEUE A mx vs qv means qv is a reference to a queue of elements vs, with A
     the refinement invariant satsfied by the elements of the queue, and mx
     being the largest the queue can be allowed to get.

   There are two levels of representation from memory to value here:
     1. first there is an array/list of values (the qelvs) that actually appear
        in memory. This representation step is captured by LIST_REL below.
        This list is accompanied by values that encode the front
        index, rear index, and count of the number of things in the queue.
     2. then there is another step that extracts the queue elements (els) in the
        right order from the sequence of HOL values that were encoded in the
        array (qels).

   The QUEUE predicate mentions els so that the specifications of the
   operations can be expressed in terms of the abstract value
*)

val QUEUE_def = Define‘
  QUEUE A sz els qv ⇔
    SEP_EXISTS av fv rv cv qelvs.
      REF qv (Conv NONE [av;fv;rv;cv]) *
      ARRAY av qelvs *
      & (0 < sz ∧ NUM (LENGTH els) cv ∧
         ∃qels f r. LIST_REL A qels qelvs ∧ NUM f fv ∧ NUM r rv ∧
                    lqueue qels f r els ∧ LENGTH qels = sz)’;
(*
   type_of “QUEUE”;
*)

(* Some simple auto tactics *)
val xsimpl_tac = rpt(FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp]);
val xs_auto_tac = rpt (FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp, xlet_auto, xref]);

val st = get_ml_prog_state ();

Theorem empty_queue_spec:
     NUM n nv ∧ 0 < n ∧ A a errv ⇒
      app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [nv; errv]
          emp (POSTv qv. QUEUE A n [] qv)
Proof
    xcf "empty_queue" st \\
    xs_auto_tac >> simp[QUEUE_def] >> xsimpl >>
    qexists_tac `REPLICATE n a` >>
    simp[lqueue_def, LIST_REL_REPLICATE_same]
QED

val EqualityType_INT = prove(``EqualityType INT``, simp[EqualityType_NUM_BOOL])

val eq_int_thm = mlbasicsProgTheory.eq_v_thm
                   |> INST_TYPE [alpha |-> “:int”]
                   |> Q.INST [‘a’ |-> ‘INT’]
                   |> PROVE_HYP EqualityType_INT

Theorem full_spec:
   app (p:'ffi ffi_proj) ^(fetch_v "full" st) [qv]
       (QUEUE A mx vs qv)
       (POSTv bv. &(BOOL (LENGTH vs = mx) bv) * QUEUE A mx vs qv)
Proof
  xcf "full" st >> simp[QUEUE_def] >> xpull >> xs_auto_tac >>
  reverse (rw[]) >- EVAL_TAC (* validate_pat *) >>
  xlet_auto >- xsimpl >>
  xapp_spec (cf_spec “:'ffi” Translator_spec eq_int_thm) >> xsimpl >>
  fs[ml_translatorTheory.BOOL_def, ml_translatorTheory.NUM_def] >>
  rpt (goal_assum (first_assum o mp_then (Pos hd) mp_tac)) >>
  imp_res_tac LIST_REL_LENGTH >> simp[] >> metis_tac[]
QED

Theorem enqueue_spec:
     !qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "enqueue" st) [qv; xv]
          (QUEUE A mx vs qv * & (A x xv ∧ LENGTH vs < mx))
          (POSTv uv. QUEUE A mx (vs ++ [x]) qv)
Proof
    xcf "enqueue" st >>
    xpull >> xs_auto_tac >>
    xlet ‘POSTv bv. QUEUE A mx vs qv * &(BOOL (LENGTH vs = mx) bv)’
    >- (xapp >> xsimpl >> qexists_tac `emp` >> xsimpl >>
        map_every qexists_tac [`vs`, `mx`, `A`] >> xsimpl) >>
    xs_auto_tac >> qexists_tac `F` >> simp[] >>
    simp[QUEUE_def] >> xpull >> xs_auto_tac >> reverse (rw[])
    >- EVAL_TAC >>
    xs_auto_tac
    >- (imp_res_tac LIST_REL_LENGTH >> fs[lqueue_def])
    >- (imp_res_tac LIST_REL_LENGTH >> strip_tac >> fs[]) >>
    simp[ml_translatorTheory.UNIT_TYPE_def] >>
    qexists_tac ‘LUPDATE x r qels’ >> simp[EVERY2_LUPDATE_same] >>
    fs[ml_translatorTheory.NUM_def] >>
    qpat_x_assum `INT (_ % _) _` mp_tac >> imp_res_tac LIST_REL_LENGTH >>
    ‘qelvs ≠ []’ by (strip_tac >> fs[]) >> simp[integerTheory.INT_MOD] >>
    strip_tac >>
    rpt (goal_assum (first_assum o mp_then (Pos hd) mp_tac)) >>
    simp[lqueue_enqueue]
QED

Theorem LIST_REL_REL_lqueue_HD:
   LIST_REL A qels qelvs ∧ lqueue qels f r (h::t) ⇒ A h (EL f qelvs)
Proof
  simp[lqueue_def] >> rw[]
  >- (fs[LIST_REL_SPLIT1] >> rw[] >>
      imp_res_tac LIST_REL_LENGTH >>
      simp[EL_APPEND1, EL_APPEND2]) >>
  Cases_on `p` >> fs[] >> rw[] >>
  fs[LIST_REL_SPLIT1] >> rw[] >>
  imp_res_tac LIST_REL_LENGTH >> fs[] >>
  simp[EL_APPEND1, EL_APPEND2]
QED

val dequeue_spec_noexn = Q.prove(
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "dequeue" st) [qv]
          (QUEUE A mx vs qv * &(vs ≠ []))
          (POSTv v. &(A (HD vs) v) * QUEUE A mx (TL vs) qv)`,
    xcf "dequeue" st >> simp[QUEUE_def] >> xpull >> xs_auto_tac >>
    reverse(rw[]) >- EVAL_TAC >> xlet_auto >- xsimpl >> xif >>
    qexists_tac `F` >> simp[] >> xs_auto_tac
    >- (imp_res_tac LIST_REL_LENGTH >> fs[lqueue_def])
    >- (strip_tac >> fs[]) >>
    dsimp[] >> fs[ml_translatorTheory.NUM_def] >>
    rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
    qpat_x_assum ‘INT (_ % _) _’ mp_tac >> imp_res_tac LIST_REL_LENGTH >>
    ‘qelvs ≠ []’ by (strip_tac >> fs[]) >> simp[integerTheory.INT_MOD] >>
    strip_tac >>
    rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
    Cases_on `vs` >> fs[integerTheory.INT_SUB] >>
    metis_tac[lqueue_dequeue, LIST_REL_REL_lqueue_HD]);

Theorem dequeue_spec:
   ∀p qv xv vs x A mx.
      app (p:'ffi ffi_proj) ^(fetch_v "dequeue" st) [qv]
          (QUEUE A mx vs qv)
       (POSTve (λv. &(vs ≠ [] ∧ A (HD vs) v) * QUEUE A mx (TL vs) qv)
               (λe. &(vs = [] ∧ EmptyQueue_exn e) * QUEUE A mx vs qv))
Proof
  xcf "dequeue" st >> simp[QUEUE_def] >> xpull >> xs_auto_tac >>
  reverse(rw[]) >- EVAL_TAC >> xlet_auto >- xsimpl >> xif
  >- ((* throws exception *)
      xs_auto_tac >> rw[] >> xraise >> xsimpl >> dsimp[] >> fs[] >>
      simp[EmptyQueue_exn_def] >> metis_tac[]) >>
  (* as before *)
  xs_auto_tac
  >- (imp_res_tac LIST_REL_LENGTH >> fs[lqueue_def])
  >- (strip_tac >> fs[]) >>
  dsimp[] >> fs[ml_translatorTheory.NUM_def] >>
  rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
  qpat_x_assum ‘INT (_ % _) _’ mp_tac >> imp_res_tac LIST_REL_LENGTH >>
  ‘qelvs ≠ []’ by (strip_tac >> fs[]) >> simp[integerTheory.INT_MOD] >>
  strip_tac >>
  rpt (goal_assum (first_assum o mp_then Any mp_tac)) >>
  Cases_on `vs` >> fs[integerTheory.INT_SUB] >>
  metis_tac[lqueue_dequeue, LIST_REL_REL_lqueue_HD]
QED

val _ = export_theory ()
