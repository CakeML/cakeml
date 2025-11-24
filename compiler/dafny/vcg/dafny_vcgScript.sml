(*
  Verification Condition Generator for Dafny.
*)
Theory dafny_vcg
Ancestors
  result_monad
  dafny_ast
  dafnyProps  (* For list_exp_size_snd *)
  dafny_wp_calc  (* For met_spec and met *)
  mlint (* For num_to_str *)
Libs
  preamble

Definition dest_VarLhs_def:
  dest_VarLhs (VarLhs var) = return var ∧
  dest_VarLhs _ = fail «dest_VarLhs: Not VarLhs»
End

Definition dest_ExpRhs_def:
  dest_ExpRhs (ExpRhs e) = return e ∧
  dest_ExpRhs _ = fail «dest_ExpRhs: Not ExpRhs»
End

Definition find_met_def:
  find_met name [] = fail «find_met: Could not find method» ∧
  find_met name (Method name' spec body::rest) =
    if name' = name
    then return (Method name' spec body)
    else find_met name rest
End

Definition dest_met_def[simp]:
  dest_met (Method name spec body) = (name, spec, body)
End

Definition freevars_aux_list_def:
  (freevars_aux_list (Var n) = ([n],[])) ∧
  (freevars_aux_list (Lit _) = ([],[])) ∧
  (freevars_aux_list (If grd thn els) =
    let (vg,sg) = freevars_aux_list grd in
    let (v0,s0) = freevars_aux_list thn in
    let (v1,s1) = freevars_aux_list els in
      (vg ++ v0 ++ v1, sg ++ s0 ++ s1)) ∧
  (freevars_aux_list (UnOp _ e) = freevars_aux_list e) ∧
  (freevars_aux_list (BinOp _ e0 e1) =
    let (v0,s0) = freevars_aux_list e0 in
    let (v1,s1) = freevars_aux_list e1 in
      (v0 ++ v1, s0 ++ s1)) ∧
  (freevars_aux_list (ArrLen arr) = freevars_aux_list arr) ∧
  (freevars_aux_list (ArrSel e0 e1) =
    let (v0,s0) = freevars_aux_list e0 in
    let (v1,s1) = freevars_aux_list e1 in
      (v0 ++ v1, s0 ++ s1)) ∧
  (freevars_aux_list (FunCall _ es) =
    let vs = MAP freevars_aux_list es in
      (FLAT (MAP FST vs), FLAT (MAP SND vs))) ∧
  (freevars_aux_list (Forall (vn,_) e) =
    let (v,s) = freevars_aux_list e in
      (FILTER (λx. x ≠ vn) v, s)) ∧
  (freevars_aux_list (Old e) = freevars_aux_list e) ∧
  (freevars_aux_list (OldHeap e) = freevars_aux_list e) ∧
  (freevars_aux_list (Prev e) =
    let (v,s) = freevars_aux_list e in
      ([], v ++ s)) ∧
  (freevars_aux_list (PrevHeap e) = freevars_aux_list e) ∧
  (freevars_aux_list (SetPrev e) =
    let (v,s) = freevars_aux_list e in
      (v ++ s, [])) ∧
  (freevars_aux_list (ForallHeap mods e) =
    let vs = MAP freevars_aux_list mods in
    let v0 = FLAT (MAP FST vs) in
    let s0 = FLAT (MAP SND vs) in
    let (v1,s1) = freevars_aux_list e in
     (v0 ++ v1, s0 ++ s1)) ∧
  (freevars_aux_list (Let binds body) =
    let vs = MAP freevars_aux_list (MAP SND binds) in
    let v0 = FLAT (MAP FST vs) in
    let s0 = FLAT (MAP SND vs) in
    let (v1,s1) = freevars_aux_list body in
     (v0 ++ (FILTER (λx. ¬MEM x (MAP FST binds)) v1),
     s0 ++ s1))
Termination
  wf_rel_tac ‘measure $ exp_size’
  \\ rpt strip_tac
  \\ gvs [list_size_pair_size_MAP_FST_SND]
  \\ rewrite_tac [list_exp_size_snd]
  \\ drule MEM_list_size
  \\ disch_then $ qspec_then ‘exp_size’ assume_tac
  \\ gvs []
End

Definition freevars_list_def:
  freevars_list e = FST (freevars_aux_list e)
End

(* TODO Move? *)
Definition list_disjoint_def:
  list_disjoint xs ys ⇔
    list_inter xs ys = []
End

(* TODO Move? *)
Definition list_subset_def:
  list_subset xs ys ⇔
    EVERY (λx. MEM x ys) xs
End

Definition gen_ds_vars_def:
  gen_ds_vars ds = GENLIST (λn. «ds» ^ (num_to_str n)) (LENGTH ds)
End

Definition get_VarLhss_def:
  get_VarLhss [] = [] ∧
  get_VarLhss (lhs::lhss) =
  case lhs of
  | VarLhs v => v::(get_VarLhss lhss)
  | _ => get_VarLhss lhss
End

Definition find_assigned_in_def:
  (find_assigned_in (Then stmt₁ stmt₂) =
     find_assigned_in stmt₁ ++ find_assigned_in stmt₂) ∧
  (find_assigned_in (If _ stmt₁ stmt₂) =
     find_assigned_in stmt₁ ++ find_assigned_in stmt₂) ∧
  (find_assigned_in (Dec n_ty stmt) =
     FILTER (λx. x ≠ FST n_ty) (find_assigned_in stmt)) ∧
  (find_assigned_in (Assign ass) = get_VarLhss (MAP FST ass)) ∧
  (find_assigned_in (While _ _ _ _ body) = find_assigned_in body) ∧
  (find_assigned_in (MetCall lhss _ _) = get_VarLhss lhss) ∧
  (find_assigned_in Skip = []) ∧
  (find_assigned_in (Assert _) = []) ∧
  (find_assigned_in (Print _ _) = []) ∧
  (find_assigned_in Return = [])
End

(* TODO Move to result_monad and use assert overload? *)
Definition assert_def:
  assert cond (err:mlstring) =
  if cond then return () else fail err
End

(* TODO Pattern matching should probably not be this deep *)
Definition is_AssignArray_def:
  is_AssignArray [(ArrSelLhs _ _, _)] = T ∧
  is_AssignArray _ = F
End

(* TODO Pattern matching should probably not be this deep *)
Definition dest_AssignArray_def:
  dest_AssignArray [(ArrSelLhs (Var arr_v) idx_e, ExpRhs rhs_e)] =
    return (arr_v, idx_e, rhs_e) ∧
  dest_AssignArray _ = fail «dest_AssignArray: Does not fit rule»
End

(* TODO Pattern matching should probably not be this deep *)
Definition dest_ArrayAlloc_def:
  dest_ArrayAlloc (Assign [(VarLhs arr_v, ArrAlloc len_e el_e el_ty)])
    = SOME (arr_v, len_e, el_e, el_ty) ∧
  dest_ArrayAlloc _ = NONE
End

Definition stmt_vcg_def:
  stmt_vcg _ Skip post ens decs mods ls = return post ∧
  stmt_vcg _ (Assert e) post ens decs mods ls = return (e::post) ∧
  stmt_vcg _ (Print e t) post ens decs mods ls =
  do
    e_t <- get_type ls e;
    assert (e_t = t) «stmt_vcg:Print: Type mismatch»;
    return (CanEval e::post)
  od ∧
  stmt_vcg _ (Return) _ ens decs mods ls = return ens ∧
  stmt_vcg m (Then s₁ s₂) post ens decs mods ls =
    (case dest_ArrayAlloc s₁ of
     | NONE =>
         do
           pre' <- stmt_vcg m s₂ post ens decs mods ls;
           stmt_vcg m s₁ pre' ens decs mods ls;
         od
     | SOME (arr_v, len_e, el_e, el_ty) =>
         do
           e <<- strlit " e";
           j <<- strlit " j";
           assert (~MEM arr_v mods)
             «stmt_vcg:ArrayAllocThen: name occurs in mods»;
           assert (e ≠ arr_v ∧ j ≠ arr_v)
             «stmt_vcg:ArrayAllocThen: cannot assign to mods var»;
           pre2 <- stmt_vcg m s₂ post ens decs (arr_v::mods) ls;
           assert (no_Prev F len_e ∧ no_Prev F el_e ∧ no_Prev F (conj pre2))
             «stmt_vcg:ArrayAllocThen: fails no_Prev checks»;
           assert (get_type ls (Var arr_v) = INR (ArrT el_ty))
             «stmt_vcg:ArrayAllocThen: array var not of correct type»;
           assert (get_type ls len_e = INR IntT)
             «stmt_vcg:ArrayAllocThen: length expression must be in typet»;
           assert (get_type ls el_e = INR el_ty)
             «stmt_vcg:ArrayAllocThen: initial array element not of correct type»;
           same_type <<- MAP FST (FILTER (λ(l,ty). MEM l mods ∧ ty = ArrT el_ty) ls);
           return
              [BinOp Le (Lit (IntL 0)) len_e;
               CanEval len_e; CanEval el_e;
               SetPrev $ ForallHeap [] $ Forall (arr_v, ArrT el_ty)
                 (imp (conj (MAP (λv. not (dfy_eq (Var arr_v) (Var v))) same_type ++
                             [dfy_eq (ArrLen (Var arr_v)) (Prev len_e);
                              Let [(e,Prev el_e)] $
                                Forall (j,IntT) $
                                  (imp (conj [BinOp Le (Lit (IntL 0)) (Var j);
                                              BinOp Lt (Var j) (ArrLen (Var arr_v))])
                                       (dfy_eq (ArrSel (Var arr_v) (Var j))
                                               (Var e)))]))
                      (conj pre2))]
         od) ∧
  stmt_vcg m (If grd thn els) post ens decs mods ls =
  do
    pre_thn <- stmt_vcg m thn post ens decs mods ls;
    pre_els <- stmt_vcg m els post ens decs mods ls;
    return [IsBool grd; imp grd (conj pre_thn); imp (not grd) (conj pre_els)]
  od ∧
  stmt_vcg m (Dec (n,ty) stmt) post ens decs mods ls =
  do
    wp <- stmt_vcg m stmt post ens decs mods ((n,ty)::ls);
    assert (EVERY (λe. ¬MEM n (freevars_list e)) wp) «stmt_vcg:Dec: Name occurs freely in wp»;
    assert (EVERY (λe. ¬MEM n (freevars_list e)) post) «stmt_vcg:Dec: Name occurs freely in post»;
    assert (EVERY (λe. ¬MEM n (freevars_list e)) ens) «stmt_vcg:Dec: Name occurs freely in ens»;
    assert (¬MEM n (MAP FST ls)) «stmt_vcg:Dec: Shadowing variables disallowed»;
    assert (¬MEM n mods) «stmt_vcg:Dec: Shadowing mod variables disallowed»;
    return wp
  od ∧
  stmt_vcg _ (Assign ass) post _ _ mods ls =
  (if is_AssignArray ass then
    do
      (arr_v, index_e, rhs_e) <- dest_AssignArray ass;
      assert (MEM arr_v mods) «stmt_vcg:Assign:Array: Trying to modify array not in mods»;
      index_ty <- get_type ls index_e;
      assert (index_ty = IntT) «stmt_vcg:Assign:Array: Index not an int»;
      el_ty <- get_type ls rhs_e;
      arr_ty <- get_type ls (Var arr_v);
      j <<- strlit " j";
      j' <<- strlit " j'";
      assert (j' ≠ arr_v ∧ j ≠ arr_v) «stmt_vcg:Assign:Array: Bad array var name»;
      assert (arr_ty = ArrT el_ty) «stmt_vcg:Assign:Array: Mismatch between lhs and rhs»;
      assert (no_Prev T index_e) «stmt_vcg_Assign:Array: no_Prev T violated in index»;
      assert (no_ticks index_e) «stmt_vcg_Assign:Array: no_ticks violated in index»;
      assert (no_Prev T rhs_e) «stmt_vcg_Assign:Array: no_Prev T violated in rhs»;
      assert (no_Prev T (conj post)) «stmt_vcg_Assign:Array: no_Prev T violated in postcondition»;
      return
        [int_le (int_lit 0) index_e; int_lt index_e (ArrLen (Var arr_v));
         CanEval rhs_e; CanEval (Var arr_v);
         SetPrev
         (ForallHeap [Var arr_v]
            (imp (conj [dfy_eq (ArrSel (Var arr_v) (Prev index_e)) (Prev rhs_e);
                        Let [(j',Prev index_e)]
                            (Forall (j,IntT)
                               (imp (conj [not (dfy_eq (Var j) (Var j'));
                                           BinOp Le (Lit (IntL 0)) (Var j);
                                           BinOp Lt (Var j) (ArrLen (Var arr_v))])
                                    (dfy_eq (ArrSel (Var arr_v) (Var j))
                                            (PrevHeap (ArrSel (Var arr_v) (Var j))))))])
                 (conj post)))]
    od
  else
    do
      (lhss, rhss) <<- UNZIP ass;
      vars <- result_mmap dest_VarLhs lhss;
      es <- result_mmap dest_ExpRhs rhss;
      assert (ALL_DISTINCT vars) «stmt_vcg:Assign: variables not distinct»;
      assert (list_disjoint vars mods) «stmt_vcg:Assign: assigning to mods»;
      assert (list_subset vars (MAP FST ls)) «stmt_vcg:Assign: Trying to assign to undeclared variables»;
      es_tys <- get_types ls es;
      vars_tys <- get_types ls (MAP Var vars);
      assert (es_tys = vars_tys) «stmt_vcg:Assign: lhs and rhs types do not match»;
      return [Let (ZIP (vars, es)) (conj post)]
    od) ∧
  stmt_vcg m (While guard invs ds ms body) post ens decs (mods:mlstring list) ls =
  do
    (* Inventing variables; after freshen, this should always succeed *)
    ds_vars <<- gen_ds_vars ds;
    assert
      (list_disjoint ds_vars
        (MAP FST ls ++ FLAT (MAP get_vars_exp ens) ++
          get_vars_stmt (While guard invs ds ms body)))
       «stmt_vcg:While: Invented variable not unique»;
    assert (list_disjoint ds_vars mods) «stmt_vcg:While: Invented variable overlaps mods»;
    assigned_in_body <<- find_assigned_in body;
    ms_vars <- dest_Vars ms;
    body_wp <- stmt_vcg m body
                 (invs ++ [CanEval guard] ++ MAP CanEval ds ++
                  decreases_check (0,ds) (0,MAP Var ds_vars))
                 ens decs (ms_vars: mlstring list) (MAP (λv. (v,IntT)) ds_vars ++ ls);
    body_cond <<-
      imp (conj (guard::invs ++ MAP2 dec_assum ds_vars ds)) (conj body_wp);
    assert (list_subset (freevars_list body_cond) (ds_vars ++ MAP FST ls))
      «stmt_vcg:While: Body condition has illegal free variables»;
    assert (list_subset (assigned_in_body) (MAP FST ls))
      «stmt_vcg:While: Body is assigning to undeclared variables»;
    assert (list_disjoint assigned_in_body mods)
      «stmt_vcg:While: Body is assigning to mods»;
    guard_ty <- get_type ls guard;
    assert (guard_ty = BoolT) «stmt_vcg:While: Guard is not a boolean»;
    assert (EVERY (λd. get_type ls d = INR IntT) ds)
      «stmt_vcg:While: Not all decreases are integers»;
    assert (list_subset ms_vars mods)
      «stmt_vcg:While: annotated mods not subset of mods»;
    assert (EVERY (no_Prev T) body_wp ∧ EVERY (no_Prev T) ds ∧
            EVERY (no_Prev T) invs ∧ EVERY (no_Prev T) post ∧
            EVERY (no_Prev T) (SND decs) ∧ no_Prev T guard)
      «stmt_vcg:While: Bad use of Prev»;
    ls1 <<- FILTER (λ(v,ty). assigned_in body v) ls;
    loop_cond <<-
      ForallHeap (MAP Var ms_vars)
        (Foralls (MAP (λv. (v,IntT)) ds_vars ++ ls) body_cond);
    return
      (invs ++ [CanEval guard] ++ MAP CanEval ds ++
       MAP (CanEval ∘ Var ∘ FST) ls ++
       [loop_cond;
        ForallHeap (MAP Var ms_vars)
          (Foralls ls1 (imp (conj (not guard::invs)) (conj post)))])
  od ∧
  stmt_vcg m (MetCall lhss name args) post ens decs mods ls =
  do
    method <- find_met name m;
    (name, spec, body) <<- dest_met method;
    assert (LENGTH spec.ins = LENGTH args)
      «stmt_vcg:MetCall: Bad number of arguments»;
    assert (LENGTH spec.outs = LENGTH lhss)
      «stmt_vcg:MetCall: Bad number of left-hand sides»;
    assert (ALL_DISTINCT (MAP FST spec.ins ++ MAP FST spec.outs))
      «stmt_vcg:MetCall: Method ins and outs not distinct»;
    vars <- result_mmap dest_VarLhs lhss;
    assert (ALL_DISTINCT vars)
      «stmt_vcg:MetCall: left-hand side names not distinct»;
    assert (EVERY (no_Prev T) args ∧ EVERY (no_Prev T) post)
      «stmt_vcg:MetCall: Cannot read and assign a variable in one statement»;
    assert (EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins) ∧
                       no_Old F e ∧ (no_Prev T) e) spec.reqs)
      «stmt_vcg:MetCall: Bad requires spec»;
    assert (EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins) ∧
                       no_Old F e ∧ (no_Prev T) e) spec.decreases)
      «stmt_vcg:MetCall: Bad decreases spec»;
    assert (EVERY (λe. list_subset (freevars_list e) (MAP FST spec.ins
                                                   ++ MAP FST spec.outs) ∧
                       no_Old T e ∧ no_Prev F e) spec.ens)
      «stmt_vcg:MetCall: Bad ensures spec»;
    assert (list_subset vars (MAP FST ls))
      «stmt_vcg:MetCall: Trying to assign to undeclared variables»;
    assert (list_disjoint vars mods)
      «stmt_vcg:MetCall: assigning to mods»;
    arg_tys <- get_types ls args;
    assert (arg_tys = MAP SND spec.ins)
      «stmt_vcg:MetCall: Argument and parameters types do not match»;
    var_tys <- get_types ls (MAP Var vars);
    assert (var_tys = MAP SND spec.outs)
      «stmt_vcg:MetCall: lhs variable types do not match»;
    callee_mod_params <- dest_Vars spec.mods;
    assert (list_subset callee_mod_params (MAP FST spec.ins))
      «stmt_vcg:MetCall: callee mod params outside of spec ins»;
    callee_mod_arg_vars <- dest_Vars
            (MAP SND
               (FILTER (λ(v,a). MEM v callee_mod_params)
                  (ZIP (MAP FST spec.ins,args))));
    assert (list_subset callee_mod_arg_vars mods)
      «stmt_vcg:MetCall: callee mod args outside of mods»;
    return
      (Let (ZIP (MAP FST spec.ins,args)) (conj spec.reqs)
       :: MAP CanEval args
       ++ decreases_check
          (spec.rank,
           MAP (Let (ZIP (MAP FST spec.ins,args))) spec.decreases)
          (wrap_old decs)
       ++ [SetPrev $ ForallHeap (MAP Var callee_mod_arg_vars) $
           Foralls (ZIP (vars, MAP SND spec.outs))
                   (imp (Let (ZIP(MAP FST spec.ins ++ MAP FST spec.outs,
                                  MAP Prev args    ++ MAP Var vars))
                             (conj (MAP replace_OldHeap spec.ens)))
                        (conj post))])
  od ∧
  stmt_vcg _ _ _ _ _ _ _ = fail «stmt_vcg: Unsupported statement»
End

Definition wrap_Old_list_def:
  wrap_Old_list vs (Var v) =
    (if MEM v vs then Old (Var v) else Var v) ∧
  wrap_Old_list _ (Lit l) = Lit l ∧
  wrap_Old_list vs (If grd thn els) =
    If (wrap_Old_list vs grd) (wrap_Old_list vs thn) (wrap_Old_list vs els) ∧
  wrap_Old_list vs (UnOp uop e) =
    UnOp uop (wrap_Old_list vs e) ∧
  wrap_Old_list vs (BinOp bop e₀ e₁) =
    BinOp bop (wrap_Old_list vs e₀) (wrap_Old_list vs e₁) ∧
  wrap_Old_list vs (ArrLen arr) =
    ArrLen (wrap_Old_list vs arr) ∧
  wrap_Old_list vs (ArrSel arr idx) =
    ArrSel (wrap_Old_list vs arr) (wrap_Old_list vs idx) ∧
  wrap_Old_list vs (FunCall name args) =
    FunCall name (MAP (wrap_Old_list vs) args) ∧
  wrap_Old_list vs (Forall (vn,vt) term) =
    Forall (vn,vt) (wrap_Old_list (FILTER (λx. x ≠ vn) vs) term) ∧
  wrap_Old_list vs (Old e) =
    Old (wrap_Old_list vs e) ∧
  wrap_Old_list vs (OldHeap e) =
    OldHeap (wrap_Old_list vs e) ∧
  wrap_Old_list vs (Prev e) = Prev e ∧ (* impossible *)
  wrap_Old_list vs (PrevHeap e) = PrevHeap e ∧ (* impossible *)
  wrap_Old_list vs (SetPrev e) = SetPrev e ∧ (* impossible *)
  wrap_Old_list vs (Let binds body) =
    Let (MAP (λ(n,e). (n, wrap_Old_list vs e)) binds)
        ((wrap_Old_list (FILTER (λx. ¬MEM x (MAP FST binds)) vs)) body) ∧
  wrap_Old_list vs (ForallHeap mods term) =
    ForallHeap (MAP (wrap_Old_list vs) mods) (wrap_Old_list vs term)
End

Definition met_vcg_def:
  met_vcg mets (Method name specs body) =
  do
    (* ensures should always refer to the locals as they were at the beginning
       of a method; in particular, it should ignore any updates/shadowing *)
    mod_vars <- dest_Vars specs.mods;
    ens <<- (MAP (wrap_Old_list (MAP FST specs.ins)) specs.ens ++
             MAP (CanEval ∘ Var ∘ FST) specs.outs);
    vcs <- stmt_vcg mets body [False] ens (specs.rank, specs.decreases) mod_vars
                    (specs.ins ++ specs.outs);
    return (specs.ins, imp (conj specs.reqs) (conj vcs))
  od
End

Definition mets_vcg_def:
  mets_vcg mets = result_mmap (met_vcg mets) mets
End

(* TODO Perhaps we should use this in the semantics? *)
Definition get_method_def:
  get_method name members =
  case get_member_aux name members of
  | NONE => fail «get_method: Method not found»
  | SOME member =>
    (case member of
     | Function _ _ _ _ _ _ _ => fail «get_method: Found function instead»
     | Method _ _ _ _ _ _ _ _ _ => return member)
End

Definition met_calls_def:
  met_calls members (MetCall _ name _) =
  do
    member <- get_method name members;
    return [member]
  od ∧
  met_calls members (Then s₁ s₂) =
  do
    mcs₁ <- met_calls members s₁;
    mcs₂ <- met_calls members s₂;
    return (mcs₁ ++ mcs₂)
  od ∧
  met_calls members (If _ thn els) =
  do
    mcs₁ <- met_calls members thn;
    mcs₂ <- met_calls members els;
    return (mcs₁ ++ mcs₂)
  od ∧
  met_calls members (Dec _ stmt) = met_calls members stmt ∧
  met_calls members (While _ _ _ _ body) = met_calls members body ∧
  met_calls members Skip = return [] ∧
  met_calls members (Assert _) = return [] ∧
  met_calls members (Assign _) = return [] ∧
  met_calls members (Print _ _) = return [] ∧
  met_calls members Return = return []
End

Definition dependencies_def:
  dependencies members member =
  case member of
  | (Method _ _ _ _ _ _ _ _ body) =>
      do
        deps <- met_calls members body;
        return (member, deps)
      od
  | _ => fail «dependencies: Functions unsupported»
End

Definition top_sorted_deps_def:
  top_sorted_deps members =
  do
    members <<- nub members;
    deps <- result_mmap (dependencies members) members;
    return $ top_sort_any deps
  od
End

Definition to_met_def:
  to_met rank (Method name ins reqs ens reads decreases outs mods body) =
  return (Method name
                 <| ins := ins;
                    reqs := reqs;
                    ens := ens;
                    reads := reads;
                    decreases := decreases;
                    outs := outs;
                    mods := mods;
                    rank := rank |>
                 body) ∧
  to_met _ _ = fail «to_met: Not a method»
End

Definition to_mets_aux_def:
  to_mets_aux _ [] = return [] ∧
  to_mets_aux rank (methods::rest) =
  do
    mets <- result_mmap (to_met rank) methods;
    rest <- to_mets_aux (rank + 1) rest;
    return $ mets ++ rest
  od
End

Definition to_mets_def:
  to_mets methods = to_mets_aux 0 methods
End

Definition rank_methods_def:
  rank_methods members =
  do
    top_sorted_methods <- top_sorted_deps members;
    to_mets top_sorted_methods
  od
End

Definition vcg_def:
  vcg (Program members) =
  do
    mets <- rank_methods members;
    mets_vcg mets
  od
End

(* In-logic testing *)
(* open dafny_compilerTheory; *)

(* val cwd = OS.FileSys.getDir (); *)
(* val fname = OS.Path.mkCanonical (cwd ^ "/../examples/mccarthy.sexp"); *)

(* val inStream = TextIO.openIn fname; *)
(* val dafny = TextIO.inputAll inStream; *)
(* val _ = TextIO.closeIn inStream; *)

(* val dafny_tm = stringSyntax.fromMLstring dafny; *)

(* val dafny_ast = EVAL “frontend ^dafny_tm” |> concl |> rhs |> rand; *)
(* val vcgs = EVAL “vcg ^dafny_ast” |> concl |> rhs |> rand; *)
