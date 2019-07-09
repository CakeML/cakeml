(*
  A pretty printer producing strings.
  Based on the pretty printer from "ML from the working programmer".
*)
open preamble holSyntaxTheory holKernelTheory mlstringTheory

val _ = new_theory "pretty";

val _ = Datatype `
  t = Block (t list) num num
    | String mlstring
    | Break num`;

val breakdist_def = Define `
  breakdist tt after =
    case tt of
      []                => after
    | Block _ _ len::es => len + breakdist es after
    | String s::es      => strlen s + breakdist es after
    | Break _::es       => 0`;

val blanks_def = Define `
  blanks space n = (space-n, concat (REPLICATE n (strlit" ")))`;

val newline_def = Define `newline = strlit"\n"`;

val printing_def = tDefine "printing" `
  (printing bs af sp mr []                     = (sp, strlit"")) /\
  (printing bs af sp mr (Block bes ind ln::es) =
     let (s1, r1) = printing (sp-ind) (breakdist es af) sp mr bes in
     let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)) /\
  (printing bs af sp mr (String s::es) =
     let (s1, r1) = (sp - strlen s, s) in
     let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)) /\
  (printing bs af sp mr (Break ln::es) =
     if ln + breakdist es af < sp then
       let (s1, r1) = blanks sp ln in
       let (s2, r2) = printing bs af s1 mr es in (s2, r1 ^ r2)
     else
       let (s1, r1) = (mr, newline) in
       let (s2, r2) = blanks s1 (mr - bs) in
       let (s3, r3) = printing bs af s2 mr es in (s3, r1 ^ r2 ^ r3))`
  (WF_REL_TAC `measure (t1_size o SND o SND o SND o SND)`);

val pr_def = Define `pr e margin = SND (printing margin 0 margin margin [e])`

val tlength_def = Define `
  tlength t =
    case t of
      Block _ _ len => len
    | String s      => strlen s
    | Break len     => len`;

val mk_str_def = Define `mk_str x = String x`;
val mk_brk_def = Define `mk_brk x = Break x`;
val mk_blo_def = Define `
  mk_blo indent es = Block es indent (SUM (MAP tlength es))`

val pp_margin_def = Define `pp_margin = 78n`;

val _ = temp_overload_on ("space", ``(strlit" ")``);
val _ = temp_overload_on ("lpar", ``(strlit"(")``);
val _ = temp_overload_on ("rpar", ``(strlit")")``);

(* ------------------------------------------------------------------------- *)
(* A pretty printer for HOL types.                                           *)
(* ------------------------------------------------------------------------- *)

val type_size_MEM = Q.prove (
  `MEM t ts ==> type_size t < type1_size ts`,
  Induct_on `ts`
  \\ rw [type_size_def]
  \\ res_tac \\ fs []);

val pp_tyop_def = Define `
  pp_tyop sep p ts =
    case ts of
      [] => strlit""
    | t::ts =>
        let s = FOLDL (\x y. x ^ sep ^ y) t ts in
          if p then lpar ^ s ^ rpar else s`;

val pp_type_def = tDefine "pp_type" `
  pp_type (prec:num) ty =
    case ty of
      Tyvar nm => nm
    | Tyapp nm [t1; t2] =>
        if nm = strlit"fun" then
          pp_tyop (strlit"->") (prec > 0) [pp_type 1 t1; pp_type 0 t2]
        else if nm = strlit"sum" then
          pp_tyop (strlit"+") (prec > 2) [pp_type 3 t1; pp_type 2 t2]
        else if nm = strlit"prod" then
          pp_tyop (strlit"#") (prec > 4) [pp_type 5 t1; pp_type 4 t2]
        else
          (pp_tyop (strlit",") T [pp_type 0 t1; pp_type 0 t2]) ^ nm
    | Tyapp nm ts =>
          (pp_tyop (strlit",") T (MAP (pp_type 0) ts)) ^ nm`
  (WF_REL_TAC `measure (type_size o SND)`
   \\ rw [type_size_def]
   \\ imp_res_tac type_size_MEM \\ fs []);

(* ------------------------------------------------------------------------- *)
(* Some handy things for breaking apart terms.                               *)
(* ------------------------------------------------------------------------- *)

val _ = Datatype `
  fixity = right num
         | left num`;

val fixity_of_def = Define `
  fixity_of nm =
    if nm = strlit"Data.Bool.==>" then
      right 4
    else if nm = strlit"Data.Bool.\\/" then
      right 6
    else if nm = strlit"Data.Bool./\\" then
      right 8
    else if nm = strlit"=" then
      right 12
    else if nm = strlit"Data.Pair.," then
      right 14
    else
      left 0`;

val name_of_def = Define `
  name_of nm =
    if nm = strlit"Data.Bool.==>" then
      strlit"==>"
    else if nm = strlit"Data.Bool.\\/" then
      strlit"\\/"
    else if nm = strlit"Data.Bool./\\" then
      strlit"/\\"
    else if nm = strlit"Data.Pair.," then
      strlit","
    else if nm = strlit"Data.Bool.!" then
      strlit"!"
    else if nm = strlit"Data.Bool.?" then
      strlit"?"
    else if nm = strlit"Data.Bool.?!" then
      strlit"?!"
    else if nm = strlit"Data.Bool.~" then
      strlit"~"
    else if nm = strlit"Data.Bool.T" then
      strlit"T"
    else if nm = strlit"Data.Bool.F" then
      strlit"F"
    else if nm = strlit"Data.Bool.cond" then
      strlit"cond"
    else
      nm`;

val is_binop_def = Define `
  is_binop tm =
    case tm of
      Comb (Comb (Const con _) _) _ =>
        (case fixity_of con of
           right _ => T
         | _ => F)
    | _ => F`;

val is_binder_def = Define `
  is_binder tm =
    case tm of
      Comb (Const nm _) (Abs (Var _ _) _) =>
        nm = strlit"Data.Bool.?" \/
        nm = strlit"Data.Bool.!" \/
        nm = strlit"Data.Bool.?!" \/
        nm = strlit"@"
    | _ => F`;

val is_cond_def = Define `
  is_cond tm =
    case tm of
      Comb (Comb (Comb (Const con _) _) _) _ =>
        con = strlit"Data.Bool.cond"
    | _ => F`;

val is_neg_def = Define `
  is_neg tm =
    case tm of
      Comb (Const nm _) _ => nm = strlit"Data.Bool.~"
    | _ => F`;

val collect_vars_def = Define `
  collect_vars tm =
    case tm of
      Abs (Var v ty) r =>
        let (vs, b) = collect_vars r in
          (v::vs, b)
    | _ => ([], tm)`;

Theorem collect_vars_term_size:
   term_size (SND (collect_vars tm)) <= term_size tm
Proof
  Induct_on `tm`
  \\ rw [Once collect_vars_def, term_size_def]
  \\ PURE_CASE_TAC \\ fs []
  \\ TRY pairarg_tac \\ fs []
  \\ rw [term_size_def]
QED

val dest_binary_def = Define `
  dest_binary nm tm =
    case tm of
      Comb (Comb (Const nm' _) l) r =>
        if nm <> nm' then
          ([], tm)
        else
          let (ls, r) = dest_binary nm r in
            (l::ls, r)
    | _ => ([], tm)`;

Theorem dest_binary_term_size:
   term_size (SND (dest_binary nm tm)) <= term_size tm
Proof
  Induct_on `tm`
  \\ rw [Once dest_binary_def, term_size_def]
  \\ PURE_CASE_TAC \\ fs [] \\ rw [term_size_def]
  \\ PURE_CASE_TAC \\ fs [] \\ rw [term_size_def]
  \\ fs [UNCURRY]
QED

Theorem dest_binary_MEM_term_size:
   !nm tm ts t q.
     MEM t ts /\
     dest_binary nm tm = (ts, q)
     ==>
     term_size t < term_size tm
Proof
  recInduct (theorem "dest_binary_ind")
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

val dest_binder_def = Define `
  dest_binder nm tm =
    case tm of
      Comb (Const nm' _) (Abs (Var v _) b) =>
        if nm <> nm' then
          ([], tm)
        else
          let (vs, r) = dest_binder nm b in
            (v::vs, r)
    | _ => ([], tm)`;

Theorem dest_binder_term_size:
   !nm tm vs b. dest_binder nm tm = (vs, b) ==> term_size b <= term_size tm
Proof
  recInduct (theorem "dest_binder_ind")
  \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once dest_binder_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ pairarg_tac
  \\ rw [term_size_def]
  \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* A pretty printer for terms.                                               *)
(* ------------------------------------------------------------------------- *)

val pp_paren_blk_def = Define `
  pp_paren_blk ind p xs =
    mk_blo ind
      ((if p then [mk_str lpar] else []) ++
       xs ++
       (if p then [mk_str rpar] else []))`;

val pp_seq_def = Define `
  pp_seq pf brk sep ts =
    case ts of
      []    => []
    | [t]   => [pf t]
    | t::ts =>
        pf t  ::
        mk_str sep ::
        if brk then [mk_brk 1] else [] ++
        pp_seq pf brk sep ts`;

val interleave_def = Define `
  interleave sep ts =
    case ts of
      []    => []
    | [t]   => [t]
    | t::ts => t::mk_str sep::mk_brk 1::interleave sep ts`;

val pp_term_def = tDefine "pp_term" `
  (pp_term (prec: num) tm =
    case tm of
      Comb l r =>
        if is_neg tm then
          pp_paren_blk 0 (prec = 1000) [pp_term 999 l; pp_term 1000 r]
        else if is_binop tm then
          (case l of
             Comb (Const nm _) l =>
               (case dest_binary nm tm of
                  ([], _) => mk_str (strlit"<pp_term: bogus BINOP>")
               | (tms, tmt) =>
                   let args = tms ++ [tmt] in
                   let sep  = space ^ name_of nm in
                     (case fixity_of nm of
                        left _ => mk_str (strlit"<pp_term: bogus BINOP>")
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
          (case l of
            Comb (Comb c p) l =>
              pp_paren_blk 0 (0 < prec)
                [mk_str (strlit"if ");
                 pp_term 0 p;
                 mk_brk 1;
                 mk_str (strlit"then ");
                 pp_term 0 l;
                 mk_brk 1;
                 mk_str (strlit"else ");
                 pp_term 0 r]
          | _ =>
             pp_paren_blk 0
                 (prec = 1000)
                 [pp_term 999 l;
                  mk_brk 1;
                  pp_term 1000 r])
        else if is_binder tm then
          (case tm of
            Comb (Const nm _) (Abs (Var v _) b) =>
              let (vs, b) = dest_binder nm tm in
              let ind = if prec = 0 then 4 else 5 in
                pp_paren_blk ind (0 < prec)
                  ((mk_str (name_of nm) :: pp_seq mk_str F space vs) ++
                   [mk_str (strlit".");
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
               ((mk_str (strlit"\\") :: pp_seq mk_str F space vs) ++
                [mk_str (strlit".");
                 (if 1 < LENGTH vs then mk_brk 1 else mk_str space);
                 pp_term 0 b])
    | Abs _ _ => mk_str (strlit"<pp_term: bogus abstraction>")
    | Const n ty => mk_str (name_of n) (* Hide Data.Bool and Data.Pair *)
    | Var n ty => mk_str n)`
  (WF_REL_TAC `measure (term_size o SND)`
   \\ rw [Once collect_vars_def]
   \\ fs [Once dest_binary_def, Once dest_binder_def] \\ rw []
   \\ fs [is_binop_def, is_cond_def, is_binder_def, is_neg_def]
   \\ pairarg_tac \\ fs [] \\ rw []
   >-
    (rename1 `collect_vars tm` \\ fs []
     \\ `term_size (SND (collect_vars tm)) <= term_size tm` suffices_by rw []
     \\ fs [collect_vars_term_size])
   \\ imp_res_tac dest_binary_MEM_term_size \\ fs []
   >-
    (rename1 `dest_binary nm tm`
     \\ `term_size (SND (dest_binary nm tm)) <= term_size tm` suffices_by rw []
     \\ fs [dest_binary_term_size])
   \\ imp_res_tac dest_binder_term_size \\ fs []);

(* ------------------------------------------------------------------------- *)
(* A pretty printer for theorems.                                            *)
(* ------------------------------------------------------------------------- *)

val pp_thm_def = Define `
  pp_thm (Sequent asl c) =
    let ss = [mk_str (strlit"|- "); pp_term 0 c] in
      case asl of
        [] => mk_blo 0 ss
      | _  => mk_blo 0 ((pp_seq (pp_term 0) T (strlit",") asl) ++ ss)`

val term2str_def = Define `
  term2str tm = pr (pp_term 0 tm) pp_margin`;

val thm2str_def = Define `
  thm2str thm = pr (pp_thm thm) pp_margin`;

(* ------------------------------------------------------------------------- *)
(* PMATCH definitions.                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ();
val PMATCH_ELIM_CONV = patternMatchesLib.PMATCH_ELIM_CONV;

Theorem is_binop_PMATCH:
   !tm.
     is_binop tm =
       case tm of
         Comb (Comb (Const con _) _) _ =>
           (case fixity_of con of
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
       case tm of
         Comb (Const nm _) (Abs (Var _ _) _) =>
           nm = strlit"Data.Bool.?" \/
           nm = strlit"Data.Bool.!" \/
           nm = strlit"Data.Bool.?!" \/
           nm = strlit"@"
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_binder_def]
QED

Theorem is_cond_PMATCH:
   !tm.
     is_cond tm =
       case tm of
         Comb (Comb (Comb (Const con _) _) _) _ =>
           con = strlit"Data.Bool.cond"
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_cond_def]
QED

Theorem is_neg_PMATCH:
   !tm.
     is_neg tm =
       case tm of
         Comb (Const nm _) _ => nm = strlit"Data.Bool.~"
       | _ => F
Proof
  CONV_TAC (DEPTH_CONV PMATCH_ELIM_CONV)
  \\ simp [is_neg_def]
QED

Theorem collect_vars_PMATCH:
   !tm.
     collect_vars tm =
       case tm of
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
       case tm of
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
       case tm of
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

val _ = export_theory ();
