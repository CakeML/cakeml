(*
  Demonstration of using the translator on functions containing PMATCH-based
  pattern matching.
*)
open HolKernel Parse boolLib bossLib;
open patternMatchesLib ml_translatorLib patternMatchesSyntax patternMatchesTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "ml_pmatch_demo";

(* basic example *)

val foo_def = Define `
  foo f x k = case f x of ([t]::[y]::ys) => t + y + (3:num) + k | _ => 5`

val c = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV)

val def = CONV_RULE (TOP_DEPTH_CONV c) foo_def

val res = translate def;

(* red-black tree example *)

val _ = Datatype `
  tree = Empty
       | Red tree 'a tree
       | Black tree 'a tree`;

(* causes the normal case-of syntax to be parsed as PMATCH *)
val _ = patternMatchesSyntax.ENABLE_PMATCH_CASES();

val balance_black_def = Define `
  balance_black a n b =
    case (a,b) of
    | (Red (Red a x b) y c,d) => Red (Black a x b) y (Black c n d)
    | (Red a x (Red b y c),d) => Red (Black a x b) y (Black c n d)
    | (a,Red (Red b y c) z d) => Red (Black a n b) y (Black c z d)
    | (a,Red b y (Red c z d)) => Red (Black a n b) y (Black c z d)
    | other => Black a n b`

val res = translate balance_black_def;

(* tricky case from BVL *)

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (num option) (exp list)
      | Op num (exp list) `

val dest_Seq_def = PmatchHeuristics.with_classic_heuristic Define `
  (dest_Seq (Let [e1;e2] (Var 1)) = SOME (e1,e2)) /\
  (dest_Seq _ = NONE)`

Theorem dest_Seq_pmatch:
  ∀exp.
  dest_Seq exp =
    case exp of
      Let [e1;e2] (Var 1) => SOME (e1,e2)
     | _ => NONE
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
         BasicProvers.every_case_tac)
  >> fs[dest_Seq_def]
QED

val _ = translate dest_Seq_pmatch;

(* set up some examples from Candle *)

fun fix def name rwth =
  def |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(REWR_CONV rwth)))
      |> curry save_thm name

Datatype:
  type
  = Tyvar mlstring
  | Tyapp mlstring (type list)
End

Datatype:
  term
  = Var mlstring type
  | Const mlstring type
  | Comb term term
  | Abs term term
End

Definition TRANS_def:
  TRANS c1 c2 =
    case (c1,c2) of
    | (Comb (Comb (Const (strlit "=") _) l) m1,
       Comb (Comb (Const (strlit "=") _) m2) r) => "yes"
    | _ => "no"
End

val res = translate TRANS_def;

val PAIR_EQ_COLLAPSE = Q.prove (
`(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))`,
Cases_on `x` THEN SIMP_TAC std_ss [] THEN METIS_TAC[])

val pabs_elim_ss =
    simpLib.conv_ss
      {name  = "PABS_ELIM_CONV",
       trace = 2,
       key   = SOME ([],``UNCURRY (f:'a -> 'b -> bool)``),
       conv  = K (K pairTools.PABS_ELIM_CONV)}

val select_conj_ss =
    simpLib.conv_ss
      {name  = "SELECT_CONJ_SS_CONV",
       trace = 2,
       key   = SOME ([],``$@ (f:'a -> bool)``),
       conv  = K (K (SIMP_CONV (std_ss++boolSimps.CONJ_ss) []))};

val static_ss = simpLib.merge_ss
  [pabs_elim_ss,
   pairSimps.paired_forall_ss,
   pairSimps.paired_exists_ss,
   pairSimps.gen_beta_ss,
   select_conj_ss,
   elim_fst_snd_select_ss,
   boolSimps.EQUIV_EXTRACT_ss,
   simpLib.rewrites [
     some_var_bool_T, some_var_bool_F,
     GSYM boolTheory.F_DEF,
     pairTheory.EXISTS_PROD,
     pairTheory.FORALL_PROD,
     PMATCH_ROW_EQ_NONE,
     PMATCH_ROW_COND_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]];

fun rc_ss gl = srw_ss() ++ simpLib.merge_ss (static_ss :: gl)

val tac =
  BasicProvers.PURE_CASE_TAC >>
  FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def,
    PMATCH_INCOMPLETE_def]

val codomain_def = Define `
  codomain ty = dtcase ty of Tyapp n (y::x::xs) => x | _ => ty`;

val codomain_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL codomain_def))) =
    case ty of Tyapp n (y::x::xs) => x | _ => ty`,
  rpt tac)
val codomain_def = fix codomain_def "codomain_def" codomain_PMATCH

val rev_assocd_def = Define `
  rev_assocd a l d =
    dtcase l of
      [] => d
    | ((x,y)::l) => if y = a then x else rev_assocd a l d`;

val rev_assocd_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL rev_assocd_def))) =
    case l of
       (x,y)::l1 => if y = a then x else rev_assocd a l1 d
     | _ => d`,
  rpt tac)
val rev_assocd_def = fix rev_assocd_def "rev_assocd_def" rev_assocd_PMATCH

val alphavars_def = Define `
  alphavars env tm1 tm2 =
    dtcase env of
      [] => (tm1 = tm2)
    | (t1,t2)::oenv =>
         ((t1 = tm1) /\ (t2 = tm2)) \/
         ((t1 <> tm1) /\ (t2 <> tm2) /\ alphavars oenv tm1 tm2)`;

val raconv_def = Define `
  raconv env tm1 tm2 =
    dtcase (tm1,tm2) of
      (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2) => raconv env s1 s2 /\ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2) =>
       (dtcase (v1,v2) of
          (Var n1 ty1, Var n2 ty2) => (ty1 = ty2) /\
                                      raconv ((v1,v2)::env) t1 t2
        | _ => F)
    | _ => F`;

val raconv_PMATCH = Q.prove(
  `^(rhs(concl(SPEC_ALL raconv_def))) =
    case (tm1,tm2) of
    | (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2)
        => raconv env s1 s2 ∧ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2)
        => (case (v1,v2) of
            | (Var n1 ty1,Var n2 ty2)
                => (ty1 = ty2) ∧ raconv ((v1,v2)::env) t1 t2
            | _ => F)
    | _ => F`,
  rpt tac)

val raconv_def = fix raconv_def "raconv_def" raconv_PMATCH

(* do the sample translations *)

val res = translate codomain_def;
val res = translate rev_assocd_def
val res = translate alphavars_def;

val variant_def = Define `variant _ v = v`;

val res = translate variant_def

val vfree_in_def = Define `
  vfree_in v tm =
    dtcase tm of
      Abs bv bod => v <> bv /\ vfree_in v bod
    | Comb s t => vfree_in v s \/ vfree_in v t
    | _ => (tm = v)`;

val res = translate vfree_in_def

val is_var_def = Define `
  is_var tm =
    dtcase tm of
      Var bv bod => T
    | _ => F`

val res = translate is_var_def
val res = translate listTheory.FILTER
val res = translate listTheory.EXISTS_DEF

val vsubst_aux_def = Define `
  vsubst_aux ilist tm =
    dtcase tm of
      Var _ _ => rev_assocd tm ilist tm
    | Const _ _ => tm
    | Comb s t => let s' = vsubst_aux ilist s in
                  let t' = vsubst_aux ilist t in
                    Comb s' t'
    | Abs v s  => if ~is_var v then tm else
                  let ilist' = FILTER (\(t,x). x <> v) ilist in
                  if ilist' = [] then tm else
                  let s' = vsubst_aux ilist' s in
                  (* if s' = s then tm else --- commented out becuase it doesn't
                                             seem to fit Harrison's formalisation *)
                  if EXISTS (\(t,x). vfree_in v t /\ vfree_in x s) ilist'
                  then let v' = variant [s'] v in
                         Abs v' (vsubst_aux ((v',v)::ilist') s)
                  else Abs v s'`;

val res = translate vsubst_aux_def;

val foo1_def = Define `
  foo1 theta tm = vsubst_aux theta tm`

val res = translate foo1_def

val _ = export_theory();
