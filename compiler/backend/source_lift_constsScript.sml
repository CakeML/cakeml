(*
  This is a source-to-source transformation that lifts constants
  from within function expressions to top-level local-declarations.

  This optimisation is implemented as two passes over the input.

    1. A bottom-up sweep prepares a tree with free-variable maps and
       pure-value flags, and collects a fresh-name bound from references
       and binders. It retains the original source nodes.

    2. A top-down sweep tracks local bindings and renamed hoisted
       bindings. It emits constants and closed-ish helpers in dependency
       order, keeping curried functions whole and constant data maximal.
       The emitted declarations are accumulated backwards and wrapped in
       one Dlocal at the declaration boundary.

 *)
Theory source_lift_consts
Ancestors
  ast mlstring finite_map source_dce[qualified] misc[qualified]
Libs
  preamble

(* --------------------------------------------------------- *
    Set up for handling variable sets and fresh names
 * --------------------------------------------------------- *)

Definition str_empty_def:
  str_empty = (FEMPTY : mlstring |-> unit)
End

Overload constant_prefix[local] = “strlit "constant_"”

Definition bump_def:
  bump new_name n =
    if isPrefix constant_prefix new_name then
      MAX n (strlen new_name + 1)
    else n
End

Definition bump_all_def:
  bump_all [] n = n ∧
  bump_all (x::xs) n = bump_all xs (bump x n)
End

Definition bump_pat_def:
  bump_pat n Pany = (n:num) ∧
  bump_pat n (Pvar vname) = bump vname n ∧
  bump_pat n (Plit l) = n ∧
  bump_pat n (Pref p) = bump_pat n p ∧
  bump_pat n (Pas p x) = bump_pat (bump x n) p ∧
  bump_pat n (Ptannot p y) = bump_pat n p ∧
  bump_pat n (Pcon _ ps) = bump_pats n ps ∧
  bump_pats n [] = n ∧
  bump_pats n (p::ps) = bump_pats (bump_pat n p) ps
End

Definition delete_all_def:
  delete_all [] s = s ∧
  delete_all (n::ns) s = fdomsub (delete_all ns s) (n:mlstring)
End

(* --------------------------------------------------------- *
    Pass 1
 * --------------------------------------------------------- *)

(* Keep the source node and its prepared children together. The map records
   free variables for values, and the group's free variables for Letrec.
   The flag identifies pure value constructions (literals, constructors whose
   children are values, and functions). No source type annotations are used. *)
Datatype:
  lift_tree = Lift exp (mlstring |-> unit) bool (lift_tree list)
End

Definition tree_exp_def:
  tree_exp (Lift e fvs value children) = e
End

Definition tree_fvs_def:
  tree_fvs (Lift e fvs value children) = fvs
End

Definition tree_value_def:
  tree_value (Lift e fvs value children) = value
End

Definition bind_all_def:
  bind_all [] bound = bound ∧
  bind_all (x::xs) bound = bind_all xs (bound |+ ((x:mlstring),()))
End

Definition maps_disjoint_def:
  maps_disjoint fvs bound ⇔ str_empty = DRESTRICT fvs (FDOM bound)
End

Definition max_list_def:
  (max_list [] = 0) ∧
  (max_list (x::xs) = MAX x (max_list xs))
End

Definition is_Fun_def:
  is_Fun (Fun _ _) = T ∧
  is_Fun _ = F
End

(* The first sweep computes free variables and a conservative fresh-name
   bound, including every binder even when it is unused. The t argument is
   retained for the existing annotation interface; closure eligibility is now
   decided by the second sweep after earlier helpers have been lifted. *)
Definition annotate_exp_def:
  (annotate_exp (t:mlstring list) (ast$Lit l) =
     (Lift (Lit l) str_empty T [],0,str_empty)) ∧
  (annotate_exp t (Con cn es) =
     let (es1,n,fvs) = annotate_exps t es in
       (Lift (Con cn es) fvs (EVERY tree_value es1) es1,n,fvs)) ∧
  (annotate_exp t (Fun x e) =
     let (e1,n,fvs1) = annotate_exp t e in
     let fvs = fdomsub fvs1 x in
       (Lift (Fun x e) fvs T [e1],bump x n,fvs)) ∧
  (annotate_exp t (ast$Letrec funs e) =
     let names = MAP FST funs in
     let (funs1,n,fvs1) = annotate_funs t funs in
     let group_fvs = delete_all names fvs1 in
     let (e1,n',fvs) = annotate_exp t e in
       (Lift (Letrec funs e) group_fvs F (e1::funs1),
        bump_all names (MAX n n'),
        delete_all names (FUNION fvs fvs1))) ∧
  (annotate_exp t (Var x) =
     let fvs = case x of
               | Short vname => str_empty |+ (vname,())
               | _ => str_empty in
     let n = case x of Short vname => bump vname 0 | _ => 0 in
       (Lift (Var x) fvs F [],n,fvs)) ∧
  (annotate_exp t (ast$App op es) =
     let (es1,n,fvs) = annotate_exps t es in
       (Lift (App op es) fvs F es1,n,fvs)) ∧
  (annotate_exp t (Log lop e1 e2) =
     let (a,n1,fvs1) = annotate_exp t e1 in
     let (b,n2,fvs2) = annotate_exp t e2 in
     let fvs = FUNION fvs1 fvs2 in
       (Lift (Log lop e1 e2) fvs F [a;b],MAX n1 n2,fvs)) ∧
  (annotate_exp t (If e1 e2 e3) =
     let (a,n1,fvs1) = annotate_exp t e1 in
     let (b,n2,fvs2) = annotate_exp t e2 in
     let (c,n3,fvs3) = annotate_exp t e3 in
     let fvs = FUNION fvs1 (FUNION fvs2 fvs3) in
       (Lift (If e1 e2 e3) fvs F [a;b;c],MAX n1 (MAX n2 n3),fvs)) ∧
  (annotate_exp t (Let name e1 e2) =
     let (a,n1,fvs1) = annotate_exp t e1 in
     let (b,n2,fvs2) = annotate_exp t e2 in
     let fvs = FUNION fvs1
       (case name of NONE => fvs2 | SOME x => fdomsub fvs2 x) in
     let n = case name of NONE => MAX n1 n2 | SOME x => bump x (MAX n1 n2) in
       (Lift (Let name e1 e2) fvs F [a;b],n,fvs)) ∧
  (annotate_exp t (Raise e) =
     let (a,n,fvs) = annotate_exp t e in
       (Lift (Raise e) fvs F [a],n,fvs)) ∧
  (annotate_exp t (Mat e pes) =
     let (a,n,fvs) = annotate_exp t e in
     let (bs,n',fvs1) = annotate_pes t pes in
     let fvs = FUNION fvs fvs1 in
       (Lift (Mat e pes) fvs F (a::bs),MAX n n',fvs)) ∧
  (annotate_exp t (Handle e pes) =
     let (a,n,fvs) = annotate_exp t e in
     let (bs,n',fvs1) = annotate_pes t pes in
     let fvs = FUNION fvs fvs1 in
       (Lift (Handle e pes) fvs F (a::bs),MAX n n',fvs)) ∧
  (annotate_exp t (Tannot e _) = annotate_exp t e) ∧
  (annotate_exp t (Lannot e _) = annotate_exp t e) ∧
  (annotate_exp t (Open path e) =
     (Lift (Open path e) str_empty F [],0,str_empty)) ∧
  (annotate_exps t [] = ([],0,str_empty)) ∧
  (annotate_exps t (e::es) =
     let (e,n,fvs) = annotate_exp t e in
       if NULL es then ([e],n,fvs) else
         let (es,n',fvs1) = annotate_exps t es in
           (e::es,MAX n n',FUNION fvs fvs1)) ∧
  (annotate_pes t [] = ([],0,str_empty)) ∧
  (annotate_pes t ((p,e)::pes) =
     let (a,n,fvs) = annotate_exp t e in
     let fvs' = delete_all (pat_bindings p) fvs in
     let (bs,n',fvs1) = annotate_pes t pes in
       (a::bs,MAX (bump_pat n p) n',FUNION fvs' fvs1)) ∧
  (annotate_funs t [] = ([],0,str_empty)) ∧
  (annotate_funs t ((f,x,e)::funs) =
     let (a,n,fvs) = annotate_exp t e in
     let fvs' = fdomsub fvs x in
     let (bs,n',fvs1) = annotate_funs t funs in
       (a::bs,MAX (bump f (bump x n)) n',FUNION fvs' fvs1))
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL (t,e) => exp_size e
   | INR (INL (t,es)) => list_size exp_size es
   | INR (INR (INL (t,pes))) =>
       list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR (t,funs))) =>
       list_size (pair_size mlstring_size
                  (pair_size mlstring_size exp_size)) funs’
End

(* --------------------------------------------------------- *
    Pass 2
 * --------------------------------------------------------- *)

Definition is_trivial_def:
  is_trivial (Con _ es) = NULL es ∧
  is_trivial (Lit l) =
    (case l of
     | IntLit i => -2**31 < i ∧ i < 2**31
     | Char c => T
     | Word8 b => T
     | _ => F) ∧
   is_trivial _ = F
End

Definition make_name_def:
  make_name n =
    constant_prefix ^ implode (REPLICATE n #"_")
End

Definition allow_lift_def:
  allow_lift op (es:exp list) ⇔
    op ≠ Equality
    (* TODO: make also flag Opapp of Var (Short "=") *)
End

(* State is (fresh counter, declarations in reverse order, reserved names).
   Named helpers retain their spelling when safe. If that spelling is a free
   declaration-level name, is bound locally, or was already emitted, allocate a
   fresh spelling and rename references within the original binding's scope. *)
Definition choose_name_def:
  choose_name (bound:mlstring |-> unit) x (n,ds,used) =
    if FLOOKUP used x = NONE ∧ FLOOKUP bound x = NONE then
      (x,(n,ds,used |+ (x,())))
    else
      let y = make_name n in
        (y,(n+1,ds,used |+ (x,()) |+ (y,())))
End

Definition choose_names_def:
  choose_names bound [] st = ([],st) ∧
  choose_names bound (x::xs) st =
    let (y,st) = choose_name bound x st in
    let (ys,st) = choose_names bound xs st in
      (y::ys,st)
End

Definition emit_dec_def:
  emit_dec d (n,ds,used) = (n,d::ds,used)
End

Definition emit_value_def:
  emit_value e (n,ds,used) =
    let x = make_name n in
      (Var (Short x),
       (n+1,Dlet NoLocs (Pvar x) e::ds,used |+ (x,())))
End

Definition rename_var_def:
  rename_var ren (Short (x:mlstring)) =
    (case FLOOKUP ren x of NONE => Short x | SOME y => Short y) ∧
  rename_var ren (Long (m:mlstring) x) = Long m x
End

Datatype:
  lift_mode = KeepValue | LiftValues | LiftFunctions
End

(* KeepValue retains the current value. LiftValues lifts expensive values.
   LiftFunctions keeps constant data together but lifts function-valued children.
   Entering a function starts LiftValues. Directly consecutive Fun nodes are
   lowered together, so a curried function is never split into closures.

   bound contains bindings still local to the expression; ren contains names
   of earlier hoisted bindings. Pushing a local binder shadows both maps. *)
Definition lift_exp_def:
  (lift_exp mode bound ren st (Lift e fvs value children) =
     if value ∧ (mode = LiftValues ∨ (mode = LiftFunctions ∧ is_Fun e)) ∧
        maps_disjoint fvs bound ∧ ¬is_trivial e then
       let (e,st) = lower_exp LiftFunctions bound ren st (Lift e fvs value children) in
         emit_value e st
     else lower_exp mode bound ren st (Lift e fvs value children)) ∧
  (lower_exp mode bound ren st (Lift (Con cn es) fvs value children) =
     let (es,st) = lift_exps mode bound ren st children in
       (Con cn es,st)) ∧
  (lower_exp mode bound ren st (Lift (Fun x e) fvs value [body]) =
     let bound = bound |+ (x,()) in
     let ren = fdomsub ren x in
     let (e,st) =
       if is_Fun (tree_exp body) then lower_exp LiftValues bound ren st body
       else lift_exp LiftValues bound ren st body in
       (Fun x e,st)) ∧
  (lower_exp mode bound ren st
     (Lift (ast$Letrec funs e) fvs value (body::children)) =
     let names = MAP FST funs in
       if mode ≠ KeepValue ∧ maps_disjoint fvs bound then
         let (names1,st) = choose_names bound names st in
         let ren = ren |++ ZIP (names,names1) in
         let bound = delete_all names bound in
         (* Recursive names become declaration-level only after the group is
            emitted. Keep them local while processing its bodies, so nested
            closures cannot become forward references to the group. *)
         let (funs1,st) = lift_funs (bind_all names bound) ren st
           (ZIP (names1,MAP (FST o SND) funs)) children in
         let st = emit_dec (Dletrec NoLocs funs1) st in
           lift_exp mode bound ren st body
       else
         let bound = bind_all names bound in
         let ren = delete_all names ren in
         let (funs1,st) = lift_funs bound ren st
           (MAP (λ(f,x,e). (f,x)) funs) children in
         let (e,st) = lift_exp mode bound ren st body in
           (Letrec funs1 e,st)) ∧
  (lower_exp mode bound ren st (Lift (Var v) fvs value children) =
     (Var (rename_var ren v),st)) ∧
  (lower_exp mode bound ren st (Lift (ast$App op es) fvs value children) =
     let mode = if allow_lift op es then mode else KeepValue in
     let (es,st) = lift_exps mode bound ren st children in
       (App op es,st)) ∧
  (lower_exp mode bound ren st (Lift (Log lop e1 e2) fvs value [a;b]) =
     let (e1,st) = lift_exp mode bound ren st a in
     let (e2,st) = lift_exp mode bound ren st b in
       (Log lop e1 e2,st)) ∧
  (lower_exp mode bound ren st (Lift (If e1 e2 e3) fvs value [a;b;c]) =
     let (e1,st) = lift_exp mode bound ren st a in
     let (e2,st) = lift_exp mode bound ren st b in
     let (e3,st) = lift_exp mode bound ren st c in
       (If e1 e2 e3,st)) ∧
  (lower_exp mode bound ren st (Lift (Let (SOME x) e1 e2) fvs value [a;b]) =
     let rhs = tree_exp a in
     let rhs_fvs = tree_fvs a in
       if mode ≠ KeepValue ∧ is_Fun rhs ∧ maps_disjoint rhs_fvs bound then
         let (e1,st) = lower_exp mode bound ren st a in
         let (y,st) = choose_name bound x st in
         let st = emit_dec (Dlet NoLocs (Pvar y) e1) st in
           lift_exp mode (fdomsub bound x) (ren |+ (x,y)) st b
       else
         let (e1,st) = lift_exp mode bound ren st a in
         let (e2,st) = lift_exp mode (bound |+ (x,())) (fdomsub ren x) st b in
           (Let (SOME x) e1 e2,st)) ∧
  (lower_exp mode bound ren st (Lift (Let NONE e1 e2) fvs value [a;b]) =
     let (e1,st) = lift_exp mode bound ren st a in
     let (e2,st) = lift_exp mode bound ren st b in
       (Let NONE e1 e2,st)) ∧
  (lower_exp mode bound ren st (Lift (Raise e) fvs value [a]) =
     let (e,st) = lift_exp mode bound ren st a in
       (Raise e,st)) ∧
  (lower_exp mode bound ren st (Lift (Mat e pes) fvs value (a::bs)) =
     let (e,st) = lift_exp mode bound ren st a in
     let (pes,st) = lift_pes mode bound ren st (MAP FST pes) bs in
       (Mat e pes,st)) ∧
  (lower_exp mode bound ren st (Lift (Handle e pes) fvs value (a::bs)) =
     let (e,st) = lift_exp mode bound ren st a in
     let (pes,st) = lift_pes mode bound ren st (MAP FST pes) bs in
       (Handle e pes,st)) ∧
  (lower_exp mode bound ren st (Lift e fvs value children) = (e,st)) ∧
  (lift_exps mode bound ren st [] = ([],st)) ∧
  (lift_exps mode bound ren st (a::bs) =
     let (e,st) = lift_exp mode bound ren st a in
     let (es,st) = lift_exps mode bound ren st bs in
       (e::es,st)) ∧
  (lift_pes mode bound ren st [] children = ([],st)) ∧
  (lift_pes mode bound ren st (p::ps) [] = ([],st)) ∧
  (lift_pes mode bound ren st (p::ps) (a::bs) =
     let names = pat_bindings p in
     let (e,st) = lift_exp mode (bind_all names bound) (delete_all names ren) st a in
     let (pes,st) = lift_pes mode bound ren st ps bs in
       ((p,e)::pes,st)) ∧
  (lift_funs bound ren st [] children = ([],st)) ∧
  (lift_funs bound ren st (f::fs) [] = ([],st)) ∧
  (lift_funs bound ren st ((f,x)::fs) (a::bs) =
     let bound1 = bound |+ (x,()) in
     let ren1 = fdomsub ren x in
     let (e,st) = if is_Fun (tree_exp a) then lower_exp LiftValues bound1 ren1 st a
                 else lift_exp LiftValues bound1 ren1 st a in
     let (funs,st) = lift_funs bound ren st fs bs in
       ((f,x,e)::funs,st))
Termination
  WF_REL_TAC ‘measure $ λinput. case input of
    | INL (mode,bound,ren,st,a) => 2 * lift_tree_size a + 1
    | INR (INL (mode,bound,ren,st,a)) => 2 * lift_tree_size a
    | INR (INR (INL (mode,bound,ren,st,bs))) =>
        2 * list_size lift_tree_size bs + 1
    | INR (INR (INR (INL (mode,bound,ren,st,ps,bs)))) =>
        2 * list_size lift_tree_size bs + 1
    | INR (INR (INR (INR (bound,ren,st,fs,bs)))) =>
        2 * list_size lift_tree_size bs + 1’
End

(* --------------------------------------------------------- *
    Putting it all together
 * --------------------------------------------------------- *)

Definition make_local_def:
  make_local ds d = if NULL ds then d else Dlocal (REVERSE ds) [d]
End

Definition compile_dec_def:
  compile_dec (Dlet l p e) =
    (if ¬source_dce$no_Open e then Dlet l p e else
     let (a,n,fvs) = annotate_exp [] e in
     let st = (bump_pat n p,[],bind_all (pat_bindings p) fvs) in
     let (e,n,ds,used) = lower_exp KeepValue str_empty FEMPTY st a in
       make_local ds (Dlet l p e)) ∧
  compile_dec (Dletrec l funs) =
    (if ¬EVERY (λ(f,x,e). source_dce$no_Open e) funs then Dletrec l funs else
     let names = MAP FST funs in
     let (trees,n,fvs) = annotate_funs [] funs in
     let st = (n,[],bind_all names fvs) in
     let (funs,n,ds,used) = lift_funs (bind_all names str_empty) FEMPTY st
       (MAP (λ(f,x,e). (f,x)) funs) trees in
       make_local ds (Dletrec l funs)) ∧
  compile_dec (Dtype l tds) = Dtype l tds ∧
  compile_dec (Dtabbrev l x y z) = Dtabbrev l x y z ∧
  compile_dec (Dexn l x y) = Dexn l x y ∧
  compile_dec (Denv v) = Denv v ∧
  compile_dec (Dopen l path) = Dopen l path ∧
  compile_dec (Dmod m ds) = Dmod m (compile_decs ds) ∧
  compile_dec (Dlocal xs ys) = Dlocal (compile_decs xs) (compile_decs ys) ∧
  compile_decs [] = [] ∧
  compile_decs (d::ds) = compile_dec d :: compile_decs ds
Termination
  WF_REL_TAC `measure $ λinput. case input of
                            | INL d => dec_size d
                            | INR ds => list_size dec_size ds`
End

Definition map_eq_def:
  map_eq (map1:'a |-> 'b) (map2:'a |-> 'b) ⇔ map1 = map2
End

Theorem annotate_exps_CONS:
  annotate_exp t x = (e,n,fv1) ∧
  annotate_exps t xs = (es,n',fv2) ⇒
  ∃fvs.
    annotate_exps t (x::xs) = (e::es, MAX n n', fvs) ∧
    map_eq fvs (FUNION fv1 fv2)
Proof
  Cases_on `xs`
  >> gvs [annotate_exp_def,map_eq_def,str_empty_def]
QED

Theorem map_eq_trans:
  map_eq a b ∧
  map_eq b c ⇒
  map_eq a c
Proof
  rw[map_eq_def]
QED

Theorem map_eq_cong:
  map_eq a a' ∧
  map_eq b b' ∧
  map_eq a' b' ⇒
  map_eq a b
Proof
  rw[map_eq_def]
QED

Theorem annotate_exps_APPEND:
  ∀xs' xn xfvs.
  annotate_exps t xs = (xs',xn,xfvs) ∧
  annotate_exps t ys = (ys',yn,yfvs) ⇒
  ∃fvs.
    annotate_exps t (xs ++ ys) = (xs'++ys', MAX xn yn, fvs) ∧
    map_eq fvs (FUNION xfvs yfvs)
Proof
  Induct_on `xs`
  >- simp [annotate_exp_def,str_empty_def,map_eq_def]
  >> rw []
  >> qpat_x_assum `_ _ (h::xs) = _` mp_tac
  >> simp [Once annotate_exp_def]
  >> rpt (pairarg_tac >> fs [])
  >> rw []
  >- (
    Cases_on `xs` >> fs []
    >> metis_tac [annotate_exps_CONS])
  >> drule annotate_exps_CONS
  >> last_x_assum assume_tac
  >> disch_then drule
  >> rw [] >> simp []
  >> gvs [map_eq_def,FUNION_ASSOC,MAX_ASSOC]
QED

Theorem FUNION_UNIT_COMM:
  FUNION (f1 : 'a |-> unit) (f2 : 'a |-> unit) =
  FUNION f2 f1
Proof
  Induct_on`f1`>>rw[]>>
  simp[FUNION_FUPDATE_1,FUNION_FUPDATE_2]>>
  rw[]
  >- (
    last_x_assum SUBST_ALL_TAC>>
    match_mp_tac FUPDATE_ELIM>>
    fs[])
  >- metis_tac[]
QED

Theorem annotate_exps_REVERSE:
  ∀es t es' n fvs.
  annotate_exps t es = (es',n,fvs) ⇒
  ∃fvs'.
    annotate_exps t (REVERSE es) = (REVERSE es', n, fvs') ∧
    map_eq fvs fvs'
Proof
  Induct
  >- simp [annotate_exp_def,str_empty_def,map_eq_def]
  >> rw []
  >> `∃e1 n1 fv1 es2 n2 fv2.
        annotate_exps t es = (es2,n2,fv2) ∧
        annotate_exps t [h] = (e1,n1,fv1)` by metis_tac [PAIR]
  >> drule annotate_exps_APPEND
  >> qpat_x_assum `_ _ es = _` assume_tac
  >> disch_then drule
  >> rw []
  >> last_x_assum drule >> rw []
  >> drule annotate_exps_APPEND
  >> qpat_x_assum `_ _ [h] = _` assume_tac
  >> disch_then drule
  >> rw [] >> simp []
  >> gvs [map_eq_def]
  >> fs [annotate_exp_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [MAX_DEF,FUNION_UNIT_COMM]
QED

(* Computation equations for the finite maps used by the executable tests. *)
val _ = computeLib.add_funs
  [finite_mapTheory.FUNION_FEMPTY_1, finite_mapTheory.FUNION_FUPDATE_1,
   finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.DRESTRICT_FUPDATE,
   finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_FUNION,
   finite_mapTheory.NOT_EQ_FEMPTY_FUPDATE,
   pred_setTheory.IN_COMPL, pred_setTheory.IN_SING];

(* --------------------------------------------------------- *
    Some simple sanity tests
 * --------------------------------------------------------- *)

Theorem test1[local]: (* no lift outside of closures *)
  compile_dec (Dlet NoLocs (Pvar «a») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)]))
  =
  Dlet NoLocs (Pvar «a») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])
Proof
  EVAL_TAC
QED

Theorem test2[local]: (* constants lifted from within closures *)
  compile_dec (Dlet NoLocs (Pvar «a»)
    (Fun «a» (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet NoLocs (Pvar «a») (Fun «a» (Var (Short «constant_»)))]
Proof
  EVAL_TAC
QED

Theorem test3[local]: (* constants are *not* lifted under Equality *)
  compile_dec
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App Equality [Var (Short «a»);
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App Equality [Var (Short «a»);
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
Proof
  EVAL_TAC
QED

Theorem test4[local]: (* constants are lifted under App *)
  compile_dec
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App ListAppend [Var (Short «a»);
                                Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_»)
        (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet NoLocs (Pvar «a»)
        (Fun «a» (App ListAppend [Var (Short «a»); Var (Short «constant_»)]))]
Proof
  EVAL_TAC
QED

Theorem test5[local]: (* curried functions are not taken apart *)
  compile_dec
    (Dlet NoLocs (Pvar «a») (Fun «a» (Fun «b» (Lit (IntLit 5)))))
  =
  Dlet NoLocs (Pvar «a») (Fun «a» (Fun «b» (Lit (IntLit 5))))
Proof
  EVAL_TAC
QED

Theorem test6[local]: (* functions inside constant data are lifted separately *)
  compile_dec
    (Dlet NoLocs (Pvar «a») (Fun «a» (Con NONE [Fun «b» (Lit (IntLit 5))])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_») (Fun «b» (Lit (IntLit 5)));
      Dlet NoLocs (Pvar «constant__») (Con NONE [Var (Short «constant_»)])]
     [Dlet NoLocs (Pvar «a») (Fun «a» (Var (Short «constant__»)))]
Proof
  EVAL_TAC
QED
