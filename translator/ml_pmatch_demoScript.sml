(*
  Demonstration of using the translator on functions containing PMATCH-based
  pattern matching.
*)
Theory ml_pmatch_demo
Ancestors
  patternMatches ml_pmatch ml_optimise
Libs
  patternMatchesLib ml_translatorLib patternMatchesSyntax

val _ = patternMatchesSyntax.temp_enable_pmatch();

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

(* basic example *)

Definition foo_def:
  foo f x k = pmatch f x of ([t]::[y]::ys) => t + y + (3:num) + k | _ => 5
End

val c = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV)

val def = CONV_RULE (TOP_DEPTH_CONV c) foo_def

val res = translate def;

(* red-black tree example *)

Datatype:
  tree = Empty
       | Red tree 'a tree
       | Black tree 'a tree
End

Definition balance_black_def:
  balance_black a n b =
    pmatch (a,b) of
    | (Red (Red a x b) y c,d) => Red (Black a x b) y (Black c n d)
    | (Red a x (Red b y c),d) => Red (Black a x b) y (Black c n d)
    | (a,Red (Red b y c) z d) => Red (Black a n b) y (Black c z d)
    | (a,Red b y (Red c z d)) => Red (Black a n b) y (Black c z d)
    | other => Black a n b
End

val res = translate balance_black_def;

(* tricky pmatch from BVL *)

Datatype:
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (num option) (exp list)
      | Op num (exp list)
End

val dest_Seq_def = PmatchHeuristics.with_classic_heuristic Define `
  (dest_Seq (Let [e1;e2] (Var 1)) = SOME (e1,e2)) /\
  (dest_Seq _ = NONE)`

Theorem dest_Seq_pmatch:
  ∀exp.
  dest_Seq exp =
    pmatch exp of
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
      |> curry save_thm (name ^ "[allow_rebind]")

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
    pmatch (c1,c2) of
    | (Comb (Comb (Const (strlit "=") _) l) m1,
       Comb (Comb (Const (strlit "=") _) m2) r) => "yes"
    | _ => "no"
End

val res = translate TRANS_def;

Theorem PAIR_EQ_COLLAPSE[local]:
  (((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))
Proof
  Cases_on `x` THEN SIMP_TAC std_ss [] THEN METIS_TAC[]
QED

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

Definition codomain_def:
  codomain ty = case ty of Tyapp n (y::x::xs) => x | _ => ty
End

Theorem codomain_PMATCH[local]:
   ^(rhs(concl(SPEC_ALL codomain_def))) =
    pmatch ty of Tyapp n (y::x::xs) => x | _ => ty
Proof
  rpt tac
QED
val codomain_def = fix codomain_def "codomain_def" codomain_PMATCH

Definition rev_assocd_def:
  rev_assocd a l d =
    case l of
      [] => d
    | ((x,y)::l) => if y = a then x else rev_assocd a l d
End

Theorem rev_assocd_PMATCH[local]:
   ^(rhs(concl(SPEC_ALL rev_assocd_def))) =
    pmatch l of
       (x,y)::l1 => if y = a then x else rev_assocd a l1 d
     | _ => d
Proof
  rpt tac
QED
val rev_assocd_def = fix rev_assocd_def "rev_assocd_def" rev_assocd_PMATCH

Definition alphavars_def:
  alphavars env tm1 tm2 =
    case env of
      [] => (tm1 = tm2)
    | (t1,t2)::oenv =>
         ((t1 = tm1) /\ (t2 = tm2)) \/
         ((t1 <> tm1) /\ (t2 <> tm2) /\ alphavars oenv tm1 tm2)
End

Definition raconv_def:
  raconv env tm1 tm2 =
    case (tm1,tm2) of
      (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2) => raconv env s1 s2 /\ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2) =>
       (case (v1,v2) of
          (Var n1 ty1, Var n2 ty2) => (ty1 = ty2) /\
                                      raconv ((v1,v2)::env) t1 t2
        | _ => F)
    | _ => F
End

Theorem raconv_PMATCH[local]:
  ^(rhs(concl(SPEC_ALL raconv_def))) =
    pmatch (tm1,tm2) of
    | (Var _ _, Var _ _) => alphavars env tm1 tm2
    | (Const _ _, Const _ _) => (tm1 = tm2)
    | (Comb s1 t1, Comb s2 t2)
        => raconv env s1 s2 ∧ raconv env t1 t2
    | (Abs v1 t1, Abs v2 t2)
        => (pmatch (v1,v2) of
            | (Var n1 ty1,Var n2 ty2)
                => (ty1 = ty2) ∧ raconv ((v1,v2)::env) t1 t2
            | _ => F)
    | _ => F
Proof
  rpt tac
QED

val raconv_def = fix raconv_def "raconv_def" raconv_PMATCH

(* do the sample translations *)

val res = translate codomain_def;
val res = translate rev_assocd_def
val res = translate alphavars_def;

Definition variant_def:
  variant _ v = v
End

val res = translate variant_def

Definition vfree_in_def:
  vfree_in v tm =
    case tm of
      Abs bv bod => v <> bv /\ vfree_in v bod
    | Comb s t => vfree_in v s \/ vfree_in v t
    | _ => (tm = v)
End

val res = translate vfree_in_def

Definition is_var_def:
  is_var tm =
    case tm of
      Var bv bod => T
    | _ => F
End

val res = translate is_var_def
val res = translate listTheory.FILTER
val res = translate listTheory.EXISTS_DEF

Definition vsubst_aux_def:
  vsubst_aux ilist tm =
    case tm of
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
                  else Abs v s'
End

val res = translate vsubst_aux_def;

Definition foo1_def:
  foo1 theta tm = vsubst_aux theta tm
End

val res = translate foo1_def
