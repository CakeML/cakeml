(*
An example of a stack data structure implemented using CakeML arrays, verified
using CF.
*)

open preamble basis

val _ = new_theory "stackProg";

val _ = translation_extends"basisProg";

val _ = Datatype `exn_type = EmptyStack`;
val _ = register_exn_type ``:exn_type``;

val stack_decls = process_topdecs
   ‘fun empty_stack u = Ref (Array.arrayEmpty (), 0)

    fun push q e =
        case !q of (a,i) =>
          let val l = Array.length a in
            if i >= l then
              let val a' = Array.array (2*l+1) e in
                (Array.copy a a' 0;
                 q := (a', i+1))
              end
                else
              (Array.update a i e;
               q := (a,i+1))
          end

    fun pop q =
      case !q of
        (a,i) => if i = 0 then raise Emptystack
                 else let val x = Array.sub a (i-1) in (q := (a, i-1); x) end’;

val _ = append_prog stack_decls;

val EmptyStack_exn_def = Define`
  EmptyStack_exn v = STACKPROG_EXN_TYPE_TYPE EmptyStack v`;

val EmptyStack_exn_def = EVAL ``EmptyStack_exn v``;

(* Heap predicate for stacks:
   STACK A vs qv means qv is a reference to a stack of
   elements vs, with A the refinement invariant satsfied by the elements of the stack *)
val STACK_def  = Define `
  STACK A vs qv =
  SEP_EXISTS av iv vvs junk.
    REF qv (Conv NONE [av;iv]) *
    & NUM (LENGTH vs) iv *
    ARRAY av (vvs ++ junk) *
    & LIST_REL A vs vvs`;

(* Some simple auto tactics *)
val xsimpl_tac = rpt(FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp]);
val xs_auto_tac = rpt (FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp, xlet_auto, xref]);

val st = get_ml_prog_state ();

Theorem empty_stack_spec:
     !uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_stack" st) [uv]
          emp (POSTv qv. STACK A [] qv)
Proof
    xcf "empty_stack" st \\
    xlet `POSTv v. &UNIT_TYPE () v` THEN1(xcon \\ xsimpl) \\
    xlet `POSTv av. ARRAY av []` THEN1(xapp \\ fs[]) \\
    xlet `POSTv pv. SEP_EXISTS av iv.
      &(pv = Conv NONE [av; iv]) * ARRAY av [] * &NUM 0 iv`
    THEN1(xcon \\ xsimpl) \\
    xref >> simp[STACK_def] >> xsimpl
QED

Theorem empty_stack_spec:
     !uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_stack" st) [uv]
          emp (POSTv qv. STACK A [] qv)
Proof
    xcf "empty_stack" st >> simp[STACK_def] >> xs_auto_tac
QED

Theorem push_spec:
     !qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (STACK A vs qv * & A x xv)
          (POSTv uv. STACK A (vs ++ [x]) qv)
Proof
    xcf "push" st >>
    simp[STACK_def] >>
    xpull >>
    xlet_auto >-(xsimpl)>>
    xmatch >> reverse(rw[]) >- EVAL_TAC >>
    xlet_auto >-(xsimpl) >>

    xlet_auto >-(xsimpl) >>
    xif
        >-(
            xlet_auto >-(xsimpl) >>
            xlet_auto >-(xsimpl) >>
            xlet_auto >-(xsimpl) >>
            xlet_auto >-(xsimpl >> fs[REPLICATE, REPLICATE_APPEND_DECOMPOSE_SYM, LENGTH_REPLICATE]) >>
            xlet_auto >-(xsimpl) >>
            xlet_auto >-(xcon >> xsimpl) >>
            xapp >>
            xsimpl >>
            fs[UNIT_TYPE_def] >>
            (* Should be partially automatized *)
            qexists_tac `vvs ++ [xv]` >>
     `LENGTH junk = 0` by (
                `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
                bossLib.DECIDE_TAC
            ) >>
            fs[LENGTH_NIL] >>
            fs[REPLICATE, REPLICATE_PLUS_ONE] >>
            fs (get_retract_thms())
            (*---------------------------------*)
        ) >>
        xlet_auto >-(xsimpl) >>
        xlet_auto >-(xsimpl) >>
        xlet_auto >-(xcon >> xsimpl) >>
        xapp >>
        xsimpl >>
        (* Should be partially automatized *)
        fs[UNIT_TYPE_def] >>
        qexists_tac `vvs ++ [xv]` >>
        qexists_tac `TL junk` >>
        fs (get_retract_thms()) >>
        `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
        Cases_on `junk:v list` >-(fs[LENGTH_NIL]) >>
        `vvs++[h]++t = vvs++h::t` by rw[] >>
        POP_ASSUM (fn x => fs[x, LUPDATE_LENGTH])
QED

Theorem push_spec:
     !qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (STACK A vs qv * & A x xv)
          (POSTv uv. STACK A (vs ++ [x]) qv)
Proof
    xcf "push" st >>
    simp[STACK_def] >>
    xpull >>
    xs_auto_tac >>
    reverse(rw[]) >- EVAL_TAC >>
    xs_auto_tac
        (* 3 subgoals *)
        >-(fs[REPLICATE, REPLICATE_APPEND_DECOMPOSE_SYM, LENGTH_REPLICATE])
        >-(
            fs[UNIT_TYPE_def] >>
            qexists_tac `vvs ++ [xv]` >>
      `LENGTH junk = 0` by (
          `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
                bossLib.DECIDE_TAC
            ) >>
            fs[LENGTH_NIL] >>
            fs[REPLICATE, REPLICATE_PLUS_ONE] >>
            fs (get_retract_thms())
        ) >>
        fs[UNIT_TYPE_def] >>
        qexists_tac `vvs ++ [xv]` >>
        qexists_tac `TL junk` >>
        fs (get_retract_thms()) >>
        `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
        Cases_on `junk:v list` >-(fs[LENGTH_NIL]) >>
        `vvs++[h]++t = vvs++h::t` by rw[] >>
        POP_ASSUM (fn x => fs[x, LUPDATE_LENGTH])
QED

val eq_num_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (EqualityType_NUM_BOOL |> CONJUNCT1);

Theorem pop_spec:
   !qv.
   EqualityType A ==>
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
   (STACK A vs qv)
   (POSTve (\v. &(not(NULL vs) /\ A (LAST vs) v) * STACK A (FRONT vs) qv)
           (\e. &(NULL vs /\ EmptyStack_exn e) * STACK A vs qv))
Proof
   xcf "pop" st >>
   simp[STACK_def] >>
   xpull >>
   xlet_auto >-(xsimpl)>>
   xmatch >>
   reverse(rw[]) >- EVAL_TAC >>
   xlet_auto >-(xsimpl) >>
   xif
   >-(
       xlet_auto >-(xcon >> xsimpl) >>
       xraise >>
       xsimpl >>
       fs[EmptyStack_exn_def] >>
       rw[] >>
       irule FALSITY >>
       fs[computeLib.EVAL_CONV ``not T``]
   ) >>
   xlet_auto >-(xsimpl) >>
   xlet_auto
   >-(
       xsimpl >>
       `vvs <> []` by metis_tac[LIST_REL_LENGTH, LENGTH_NIL] >>
       `LENGTH vs <> 0 /\ LENGTH vvs <> 0` by metis_tac[LENGTH_NIL] >>
       `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
       bossLib.DECIDE_TAC
   ) >>
   xlet_auto >-(xsimpl) >>
   xlet_auto >-(xcon >> xsimpl) >>
   xlet_auto >-(xsimpl) >>
   xvar
   >-(
      xsimpl >>
      qexists_tac `FRONT vvs` >>
      qexists_tac `[LAST vvs] ++ junk` >>
      fs[mlbasicsProgTheory.not_def, NULL_EQ] >>
      `vvs <> [] /\ LENGTH vs <> 0 /\ LENGTH vvs <> 0` by metis_tac[LIST_REL_LENGTH, LENGTH_NIL] >>
      `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
      FIRST_ASSUM (fn x => PURE_REWRITE_TAC[x]) >>
      `LENGTH vvs - 1 = PRE(LENGTH vvs)` by rw[] >>
      FIRST_ASSUM (fn x => fs[x]) >>
      fs[EL_APPEND_EQN, GSYM LAST_EL, LIST_REL_FRONT_LAST] >>
      fs[APPEND_FRONT_LAST] >>
      rw[LENGTH_FRONT] >>
      `PRE(LENGTH vvs) = LENGTH vvs - 1` by rw[] >>
      POP_ASSUM(fn x => fs[x]) >>
      fs[NUM_def, int_arithTheory.INT_NUM_SUB]
  ) >>
  xsimpl >>
  rw[] >>
  fs[NULL_EQ]
QED

val _ = export_theory ()
