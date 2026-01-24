(*
  A pretty printer producing mlstring app_lists.
  Based on the pretty printer from "ML from the working programmer".
*)
Theory pretty
Ancestors
  holSyntax holKernel mlstring
Libs
  preamble

Datatype:
  t = Block (t list) num num
    | String mlstring
    | Break num
End

(* Compute the distance until the next break token *)

Definition breakdist_def:
  breakdist after [] = after ∧
  breakdist after (h::t) =
    pmatch h of
      Block _ _ n => n + breakdist after t
    | String s => strlen s + breakdist after t
    | Break _ => 0
End

Definition blanks_def:
  blanks sp n = (sp - n, List (REPLICATE n « »))
End

Definition newline_def:
  newline = «\n»
End

Definition print_list_def:
  print_list bs af sp mr [] = (sp, Nil) ∧
  print_list bs af sp mr (h::t) =
    pmatch h of
      Block bes ind ln =>
        let (s1,r1) = print_list (sp-ind) (breakdist af t) sp mr bes;
            (s2,r2) = print_list bs af s1 mr t
        in (s2, SmartAppend r1 r2)
    | String s =>
        let (s1,r1) = print_list bs af (sp-strlen s) mr t
        in (s1, SmartAppend (List [s]) r1)
    | Break ln =>
        if ln + breakdist af t < sp then
          let (s1,r1) = blanks sp ln;
              (s2,r2) = print_list bs af s1 mr t
          in (s2, SmartAppend r1 r2)
        else
          let (s1,r1) = (mr, List [newline]);
              (s2,r2) = blanks s1 (mr-bs);
              (s3,r3) = print_list bs af s2 mr t
          in (s3, SmartAppend r1 (SmartAppend r2 r3))
End

Definition pr_def:
  pr e m = SND (print_list m 0 m m [e])
End

Definition tlength_def:
  tlength t =
    pmatch t of
      Block _ _ len => len
    | String s => strlen s
    | Break len => len
End

Definition mk_str_def:
  mk_str x = String x
End

Definition mk_brk_def:
  mk_brk x = Break x
End

Definition mk_blo_def:
  mk_blo indent es = Block es indent (SUM (MAP tlength es))
End

Definition pp_margin_def:
  pp_margin = 78n
End

Overload space[local] = “« »”;
Overload lpar[local] = “«(»”;
Overload rpar[local] = “«)»”;

(* ------------------------------------------------------------------------- *)
(* A pretty printer for HOL types.                                           *)
(* ------------------------------------------------------------------------- *)

Theorem type_size_MEM[local]:
  MEM t ts ==> type_size t < type1_size ts
Proof
  Induct_on ‘ts’
  \\ rw [type_size_def]
  \\ res_tac \\ fs []
QED

Definition pp_tyop_aux_def:
  pp_tyop_aux sep [] = [] ∧
  pp_tyop_aux sep (h::t) = mk_str sep :: h :: pp_tyop_aux sep t
End

Definition pp_with_sep_def:
  pp_with_sep sep p xs =
    let ts = pp_tyop_aux sep xs in
      if p then mk_blo 0 (mk_str lpar::ts ++ [mk_str rpar]) else mk_blo 0 ts
End

Definition pp_type_def:
  pp_type (prec:num) ty =
    pmatch ty of
      Tyvar nm => mk_str nm
    | Tyapp nm [t1; t2] =>
        if nm = «fun» then
          pp_with_sep «->» (prec > 0) [pp_type 1 t1; pp_type 0 t2]
        else if nm = «sum» then
          pp_with_sep «+» (prec > 2) [pp_type 3 t1; pp_type 2 t2]
        else if nm = «prod» then
          pp_with_sep «#» (prec > 4) [pp_type 5 t1; pp_type 4 t2]
        else
          mk_blo 0 [pp_with_sep «,» T [pp_type 0 t1; pp_type 0 t2]; mk_str nm]
    | Tyapp nm ts =>
          mk_blo 0 [pp_with_sep «,» T (MAP (pp_type 0) ts); mk_str nm]
Termination
  WF_REL_TAC ‘measure (type_size o SND)’
  \\ rw [] \\ simp[]
  \\ drule MEM_list_size
  \\ disch_then (qspec_then`type_size` mp_tac)
  \\ simp[]
End

(* ------------------------------------------------------------------------- *)
(* Some handy things for breaking apart terms.                               *)
(* ------------------------------------------------------------------------- *)

Datatype:
  fixity = right num
         | left num
End

Definition fixity_of_def:
  fixity_of nm =
    if nm = «Data.Bool.==>» then
      right 4
    else if nm = «Data.Bool.\\/» then
      right 6
    else if nm = «Data.Bool./\\» then
      right 8
    else if nm = «=» then
      right 12
    else if nm = «Data.Pair.,» then
      right 14
    else
      left 0
End

Definition name_of_def:
  name_of nm =
    if nm = «Data.Bool.==>» then
      «==>»
    else if nm = «Data.Bool.\\/» then
      «\\/»
    else if nm = «Data.Bool./\\» then
      «/\\»
    else if nm = «Data.Pair.,» then
      «,»
    else if nm = «Data.Bool.!» then
      «!»
    else if nm = «Data.Bool.?» then
      «?»
    else if nm = «Data.Bool.?!» then
      «?!»
    else if nm = «Data.Bool.~» then
      «~»
    else if nm = «Data.Bool.T» then
      «T»
    else if nm = «Data.Bool.F» then
      «F»
    else if nm = «Data.Bool.cond» then
      «cond»
    else
      nm
End

Definition is_binop_def:
  is_binop tm =
    pmatch tm of
      Comb (Comb (Const con _) _) _ =>
        (pmatch fixity_of con of
           right _ => T
         | _ => F)
    | _ => F
End

Definition is_binder_def:
  is_binder tm =
    pmatch tm of
      Comb (Const nm _) (Abs (Var _ _) _) =>
        nm = «Data.Bool.?» ∨
        nm = «Data.Bool.!» ∨
        nm = «Data.Bool.?!» ∨
        nm = «@»
    | _ => F
End

Definition is_cond_def:
  is_cond tm =
    pmatch tm of
      Comb (Comb (Comb (Const con _) _) _) _ =>
        con = «Data.Bool.cond»
    | _ => F
End

Definition is_neg_def:
  is_neg tm =
    pmatch tm of
      Comb (Const nm _) _ => nm = «Data.Bool.~»
    | _ => F
End

Definition collect_vars_def:
  collect_vars tm =
    pmatch tm of
      Abs (Var v ty) r =>
        let (vs, b) = collect_vars r in
          (v::vs, b)
    | _ => ([], tm)
End

Theorem collect_vars_term_size:
   term_size (SND (collect_vars tm)) ≤ term_size tm
Proof
  Induct_on ‘tm’
  \\ rw [Once collect_vars_def, term_size_def]
  \\ PURE_CASE_TAC \\ fs []
  \\ TRY pairarg_tac \\ fs []
  \\ rw [term_size_def]
QED

Definition dest_binary_def:
  dest_binary nm tm =
    pmatch tm of
      Comb (Comb (Const nm' _) l) r =>
        if nm ≠ nm' then
          ([], tm)
        else
          let (ls, r) = dest_binary nm r in
            (l::ls, r)
    | _ => ([], tm)
End

Theorem dest_binary_term_size:
   term_size (SND (dest_binary nm tm)) ≤ term_size tm
Proof
  Induct_on ‘tm’
  \\ rw [Once dest_binary_def, term_size_def]
  \\ PURE_CASE_TAC \\ fs [] \\ rw [term_size_def]
  \\ PURE_CASE_TAC \\ fs [] \\ rw [term_size_def]
  \\ fs [UNCURRY]
QED

Theorem dest_binary_MEM_term_size:
  ∀nm tm ts t q.
    MEM t ts ∧
    dest_binary nm tm = (ts, q) ⇒
      term_size t < term_size tm
Proof
  recInduct dest_binary_ind
  \\ rpt gen_tac \\ strip_tac
  \\ Induct
  \\ rw [Once dest_binary_def]
  \\ pop_assum mp_tac
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rw []
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ rw [term_size_def]
  \\ res_tac \\ fs []
QED

Definition dest_binder_def:
  dest_binder nm tm =
    pmatch tm of
      Comb (Const nm' _) (Abs (Var v _) b) =>
        if nm ≠ nm' then
          ([], tm)
        else
          let (vs, r) = dest_binder nm b in
            (v::vs, r)
    | _ => ([], tm)
End

Theorem dest_binder_term_size:
  ∀nm tm vs b.
    dest_binder nm tm = (vs, b) ⇒
      term_size b ≤ term_size tm
Proof
  recInduct dest_binder_ind
  \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once dest_binder_def]
  \\ strip_tac \\ gvs[AllCaseEqs()]
  \\ pairarg_tac
  \\ fs[]
QED

(* ------------------------------------------------------------------------- *)
(* A pretty printer for terms.                                               *)
(* ------------------------------------------------------------------------- *)

Definition pp_paren_blk_def:
  pp_paren_blk ind p xs =
    mk_blo ind
      ((if p then [mk_str lpar] else []) ++
       xs ++
       (if p then [mk_str rpar] else []))
End

Definition pp_seq_def:
  pp_seq pf brk sep ts =
    pmatch ts of
      []    => []
    | [t]   => [pf t]
    | t::ts =>
        pf t  ::
        mk_str sep ::
        if brk then [mk_brk 1] else [] ++
        pp_seq pf brk sep ts
End

Definition interleave_def:
  interleave sep ts =
    pmatch ts of
      []    => []
    | [t]   => [t]
    | t::ts => t::mk_str sep::mk_brk 1::interleave sep ts
End

Definition pp_term_def:
  (pp_term (prec: num) tm =
    pmatch tm of
      Comb l r =>
        if is_neg tm then
          pp_paren_blk 0 (prec = 1000) [pp_term 999 l; pp_term 1000 r]
        else if is_binop tm then
          (pmatch l of
             Comb (Const nm _) l =>
               (pmatch dest_binary nm tm of
                  ([], _) => mk_str «<pp_term: bogus BINOP>»
               | (tms, tmt) =>
                   let args = tms ++ [tmt] in
                   let sep  = space ^ name_of nm in
                     (pmatch fixity_of nm of
                        left _ => mk_str «<pp_term: bogus BINOP>»
                      | right nprec =>
                          let ts = MAP (pp_term nprec) args in
                            pp_paren_blk
                              (if nprec <= prec then 1 else 0)
                              (nprec <= prec)
                              (interleave sep ts))
           | _ =>
             pp_paren_blk 0
                 (prec = 1000)
                 [pp_term 999 l;
                  mk_brk 1;
                  pp_term 1000 r]))
        else if is_cond tm then
          (pmatch l of
            Comb (Comb c p) l =>
              pp_paren_blk 0 (0 < prec)
                [mk_str «if »;
                 pp_term 0 p;
                 mk_brk 1;
                 mk_str «then »;
                 pp_term 0 l;
                 mk_brk 1;
                 mk_str «else »;
                 pp_term 0 r]
          | _ =>
             pp_paren_blk 0
                 (prec = 1000)
                 [pp_term 999 l;
                  mk_brk 1;
                  pp_term 1000 r])
        else if is_binder tm then
          (pmatch tm of
            Comb (Const nm _) (Abs (Var v _) b) =>
              let (vs, b) = dest_binder nm tm in
              let ind = if prec = 0 then 4 else 5 in
                pp_paren_blk ind (0 < prec)
                  ((mk_str (name_of nm) :: pp_seq mk_str F space vs) ++
                   [mk_str «.»;
                    (if 1 < LENGTH vs then mk_brk 1 else mk_str space);
                    pp_term 0 b])
           | _ =>
               pp_paren_blk 0
                 (prec = 1000)
                 [pp_term 999 l;
                  mk_brk 1;
                  pp_term 1000 r])
        else
          pp_paren_blk 0
            (prec = 1000)
            [pp_term 999 l; mk_brk 1; pp_term 1000 r]
    | Abs (Var _ _) r =>
        let (vs, b) = collect_vars tm in
        let ind = if prec = 0 then 4 else 5 in
             pp_paren_blk ind (0 < prec)
               ((mk_str «\\» :: pp_seq mk_str F space vs) ++
                [mk_str «.»;
                 (if 1 < LENGTH vs then mk_brk 1 else mk_str space);
                 pp_term 0 b])
    | Abs _ _ => mk_str «<pp_term: bogus abstraction>»
    | Const n ty => mk_str (name_of n) (* Hide Data.Bool and Data.Pair *)
    | Var n ty => mk_str n)
Termination
  WF_REL_TAC ‘measure (term_size o SND)’
  \\ rw [Once collect_vars_def]
  \\ fs [Once dest_binary_def, Once dest_binder_def] \\ rw []
  \\ fs [is_binop_def, is_cond_def, is_binder_def, is_neg_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  >- (
    rename1 ‘collect_vars tm’ \\ fs []
    \\ ‘term_size (SND (collect_vars tm)) ≤ term_size tm’ suffices_by rw []
    \\ fs [collect_vars_term_size])
  \\ imp_res_tac dest_binary_MEM_term_size \\ fs []
  >- (
    rename1 ‘dest_binary nm tm’
    \\ ‘term_size (SND (dest_binary nm tm)) <= term_size tm’ suffices_by rw []
    \\ fs [dest_binary_term_size])
  \\ imp_res_tac dest_binder_term_size \\ fs []
End

(* ------------------------------------------------------------------------- *)
(* A pretty printer for theorems.                                            *)
(* ------------------------------------------------------------------------- *)

Definition pp_thm_def:
  pp_thm (Sequent asl c) =
    let ss = [mk_str «|- »; pp_term 0 c] in
      pmatch asl of
        [] => mk_blo 0 ss
      | _  => mk_blo 0 ((pp_seq (pp_term 0) T («,») asl) ++ ss)
End

Definition term2str_applist_def:
  term2str_applist tm = pr (pp_term 0 tm) pp_margin
End

Definition thm2str_applist_def:
  thm2str_applist thm = pr (pp_thm thm) pp_margin
End

(* ------------------------------------------------------------------------- *)
(* PMATCH definitions.                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = patternMatchesSyntax.temp_enable_pmatch();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem is_binop_PMATCH:
   !tm.
     is_binop tm =
       pmatch tm of
         Comb (Comb (Const con _) _) _ =>
           (pmatch fixity_of con of
              right _ => T
            | _ => F)
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_binop_def]
QED

Theorem is_binder_PMATCH:
   !tm.
     is_binder tm =
       pmatch tm of
         Comb (Const nm _) (Abs (Var _ _) _) =>
           nm = «Data.Bool.?» \/
           nm = «Data.Bool.!» \/
           nm = «Data.Bool.?!» \/
           nm = «@»
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_binder_def]
QED

Theorem is_cond_PMATCH:
   !tm.
     is_cond tm =
       pmatch tm of
         Comb (Comb (Comb (Const con _) _) _) _ =>
           con = «Data.Bool.cond»
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_cond_def]
QED

Theorem is_neg_PMATCH:
   !tm.
     is_neg tm =
       pmatch tm of
         Comb (Const nm _) _ => nm = «Data.Bool.~»
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_neg_def]
QED

Theorem collect_vars_PMATCH:
   !tm.
     collect_vars tm =
       pmatch tm of
         Abs (Var v ty) r =>
           let (vs, b) = collect_vars r in
             (v::vs, b)
       | _ => ([], tm)
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [Once collect_vars_def]
QED

Theorem dest_binary_PMATCH:
   !tm.
     dest_binary nm tm =
       pmatch tm of
         Comb (Comb (Const nm' _) l) r =>
           if nm <> nm' then
             ([], tm)
           else
             let (ls, r) = dest_binary nm r in
               (l::ls, r)
       | _ => ([], tm)
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [Once dest_binary_def]
QED

Theorem dest_binder_PMATCH:
   !tm.
     dest_binder nm tm =
       pmatch tm of
         Comb (Const nm' _) (Abs (Var v _) b) =>
           if nm <> nm' then
             ([], tm)
           else
             let (vs, r) = dest_binder nm b in
               (v::vs, r)
       | _ => ([], tm)
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [Once dest_binder_def]
QED

