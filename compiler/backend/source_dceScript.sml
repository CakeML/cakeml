(*
  This is a source-to-source transformation that removes declarations
  that bind values that are never used and whose evaluation cannot have
  any externally observable effect on the state.
*)
Theory source_dce
Ancestors
  ast namespace finite_map misc[qualified]
Libs
  preamble


(* -------------------------------------------------------------------------
   Sets of used names
   ------------------------------------------------------------------------- *)

Datatype:
  long_names = Names ((mlstring, (mlstring |-> unit) # long_names) alist)
End

Type names[pp] = “:(mlstring |-> unit) # long_names”

Definition empty_names_def:
  empty_names = ((FEMPTY, Names []) : names)
End

Definition is_used_def:
  is_used ((shorts,longs):names) n ⇔ n ∈ FDOM shorts
End

Definition lookup_mod_def:
  lookup_mod (Names xs) mn =
    case ALOOKUP xs mn of
    | NONE => empty_names
    | SOME s => s
End

Definition upd_alist_def:
  upd_alist [] mn s = [(mn,s)] ∧
  upd_alist ((m,t)::xs) mn s =
    if m = mn then (mn,s)::xs else (m,t)::upd_alist xs mn s
End

Definition insert_mod_def:
  insert_mod (Names xs) mn s = Names (upd_alist xs mn s)
End

Definition add_name_def:
  add_name ((shorts,longs):names) (Short n) = (shorts |+ (n,()), longs) ∧
  add_name ((shorts,longs):names) (Long mn id) =
    (shorts, insert_mod longs mn (add_name (lookup_mod longs mn) id))
End

Definition delete_name_def:
  delete_name ((shorts,longs):names) n = (shorts \\ n, longs)
End

Definition delete_names_def:
  delete_names s [] = s ∧
  delete_names s (n::ns) = delete_names (delete_name s n) ns
End

Definition strip_mod_def:
  strip_mod mn ((shorts,longs):names) = lookup_mod longs mn
End

Definition union_names_def:
  union_names ((s1,l1):names) ((s2,l2):names) =
    (FUNION s1 s2, union_longs l1 l2) ∧
  union_longs (Names []) l = l ∧
  union_longs (Names ((mn,s)::xs)) l =
    union_longs (Names xs) (insert_mod l mn (union_names s (lookup_mod l mn)))
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL (s,t) => long_names_size (SND s) + 1
                           | INR (l1,l2) => long_names_size l1)’
  \\ simp [list_size_def, basicSizeTheory.pair_size_def]
End

Theorem IN_FDOM_thms[compute]:
  (x ∈ FDOM (FUNION f g) ⇔ x ∈ FDOM f ∨ x ∈ FDOM g) ∧
  (x ∈ FDOM (f \\ k) ⇔ x ≠ k ∧ x ∈ FDOM f)
Proof
  simp [FDOM_FUNION] \\ metis_tac []
QED

(* -------------------------------------------------------------------------
   Free variables
   ------------------------------------------------------------------------- *)

Definition free_vars_def:
  free_vars locals acc (Raise e) =
    free_vars locals acc e ∧
  free_vars locals acc (Handle e pes) =
    free_vars_pes locals (free_vars locals acc e) pes ∧
  free_vars locals acc (ast$Lit l) = acc ∧
  free_vars locals acc (Con cn es) =
    free_vars_list locals acc es ∧
  free_vars locals acc (Var (Short n)) =
    (if MEM n locals then acc else add_name acc (Short n)) ∧
  free_vars locals acc (Var (Long m id)) =
    add_name acc (Long m id) ∧
  free_vars locals acc (Fun x e) =
    free_vars (x::locals) acc e ∧
  free_vars locals acc (App op es) =
    free_vars_list locals acc es ∧
  free_vars locals acc (Log lop e1 e2) =
    free_vars locals (free_vars locals acc e1) e2 ∧
  free_vars locals acc (If e1 e2 e3) =
    free_vars locals (free_vars locals (free_vars locals acc e1) e2) e3 ∧
  free_vars locals acc (Mat e pes) =
    free_vars_pes locals (free_vars locals acc e) pes ∧
  free_vars locals acc (Let NONE e1 e2) =
    free_vars locals (free_vars locals acc e1) e2 ∧
  free_vars locals acc (Let (SOME x) e1 e2) =
    free_vars (x::locals) (free_vars locals acc e1) e2 ∧
  free_vars locals acc (Letrec funs e) =
    (let locals1 = MAP FST funs ++ locals in
       free_vars_funs locals1 (free_vars locals1 acc e) funs) ∧
  free_vars locals acc (Tannot e t) =
    free_vars locals acc e ∧
  free_vars locals acc (Lannot e l) =
    free_vars locals acc e ∧
  free_vars_list locals acc [] = acc ∧
  free_vars_list locals acc (e::es) =
    free_vars_list locals (free_vars locals acc e) es ∧
  free_vars_pes locals acc [] = acc ∧
  free_vars_pes locals acc ((p,e)::pes) =
    free_vars_pes locals (free_vars (pat_bindings p ++ locals) acc e) pes ∧
  free_vars_funs locals acc [] = acc ∧
  free_vars_funs locals acc ((f,x,e)::funs) =
    free_vars_funs locals (free_vars (x::locals) acc e) funs
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL (_,_,e) => exp_size e
                           | INR (INL (_,_,es)) => list_size exp_size es
                           | INR (INR (INL (_,_,pes))) =>
                               list_size (pair_size pat_size exp_size) pes
                           | INR (INR (INR (_,_,funs))) =>
                               list_size (pair_size mlstring_size
                                 (pair_size mlstring_size exp_size)) funs)’
End

Definition free_vars_dec_def:
  free_vars_dec acc (Dlet l p e) = free_vars [] acc e ∧
  free_vars_dec acc (Dletrec l funs) =
    free_vars_funs (MAP FST funs) acc funs ∧
  free_vars_dec acc _ = acc
End

Definition dec_binds_def:
  dec_binds (Dlet l p e) = pat_bindings p ∧
  dec_binds (Dletrec l funs) = MAP FST funs ∧
  dec_binds (Denv n) = [n] ∧
  dec_binds _ = []
End

Definition update_names_def:
  update_names used d = free_vars_dec (delete_names used (dec_binds d)) d
End

(* -------------------------------------------------------------------------
   Pure enough expressions
   ------------------------------------------------------------------------- *)

Definition pure_op_def:
  pure_op op ⇔
    case op of
    (* do_arith raises only when dividing an integer by zero *)
    | Arith a ty => (ty = IntT ⇒ a ≠ Div ∧ a ≠ Mod)
    (* do_conversion raises only in chr *)
    | FromTo ty1 ty2 => ¬(ty1 = IntT ∧ ty2 = CharT)
    | Shift ws sh n => T
    | Equality => T
    | Test t ty => T
    (* reads of the state, which do not change it *)
    | Opderef => T
    | Aw8length => T
    | Alength => T
    | Vlength => T
    | Strlen => T
    (* total operations on strings, vectors and lists *)
    | Implode => T
    | Explode => T
    | Strcat => T
    | VfromList => T
    | ListAppend => T
    | _ => F
End

Definition alloc_op_def:
  alloc_op op ⇔
    case op of
    | Opref => T
    | AallocEmpty => T
    | AallocFixed => T
    | ThunkOp (AllocThunk m) => T
    | _ => F
End

Definition dest_int_lit_def:
  dest_int_lit (ast$Lit (IntLit n)) = SOME n ∧
  dest_int_lit (Tannot e t) = dest_int_lit e ∧
  dest_int_lit (Lannot e l) = dest_int_lit e ∧
  dest_int_lit _ = NONE
End

Definition alloc_app_def:
  alloc_app op es ⇔
    alloc_op op ∨
    ((op = Aalloc ∨ op = Aw8alloc) ∧
     case es of
     | (e :: rest) => (case dest_int_lit e of
                       | SOME n => 0 ≤ n
                       | NONE => F)
     | _ => F)
End

Definition total_pat_def:
  total_pat Pany = T ∧
  total_pat (Pvar n) = T ∧
  total_pat (Pcon NONE ps) = total_pat_list ps ∧
  total_pat (Pas p n) = total_pat p ∧
  total_pat (Ptannot p t) = total_pat p ∧
  total_pat _ = F ∧
  total_pat_list [] = T ∧
  total_pat_list (p::ps) = (total_pat p ∧ total_pat_list ps)
End

Definition pure_exp_def:
  pure_exp (Raise e) = F ∧
  (* the handler is unreachable because e cannot raise *)
  pure_exp (Handle e pes) = pure_exp e ∧
  pure_exp (ast$Lit l) = T ∧
  pure_exp (Con cn es) = pure_exp_list es ∧
  pure_exp (Var id) = T ∧
  pure_exp (Fun x e) = T ∧
  pure_exp (App op es) = ((pure_op op ∨ alloc_app op es) ∧ pure_exp_list es) ∧
  pure_exp (Log lop e1 e2) = (pure_exp e1 ∧ pure_exp e2) ∧
  pure_exp (If e1 e2 e3) =
    (pure_exp e1 ∧ pure_exp e2 ∧ pure_exp e3) ∧
  (* one of the patterns must match, or the match raises *)
  pure_exp (Mat e pes) =
    (pure_exp e ∧ EXISTS total_pat (MAP FST pes) ∧ pure_exp_pes pes) ∧
  pure_exp (Let x e1 e2) = (pure_exp e1 ∧ pure_exp e2) ∧
  (* the function bodies are not evaluated *)
  pure_exp (Letrec funs e) = pure_exp e ∧
  pure_exp (Tannot e t) = pure_exp e ∧
  pure_exp (Lannot e l) = pure_exp e ∧
  pure_exp_list [] = T ∧
  pure_exp_list (e::es) = (pure_exp e ∧ pure_exp_list es) ∧
  pure_exp_pes [] = T ∧
  pure_exp_pes ((p,e)::pes) = (pure_exp e ∧ pure_exp_pes pes)
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL e => exp_size e
                           | INR (INL es) => list_size exp_size es
                           | INR (INR pes) =>
                               list_size (pair_size pat_size exp_size) pes)’
End

(* -------------------------------------------------------------------------
   Which declarations can be removed, and what is left of the others
   ------------------------------------------------------------------------- *)

Definition can_remove_def:
  (can_remove used (Dlet l p e) ⇔
     pure_exp e ∧ total_pat p ∧
     EVERY (λn. ¬ is_used used n) (pat_bindings p)) ∧
  (can_remove used (Dletrec l funs) ⇔
     EVERY (λ(f,x,e). ¬ is_used used f) funs) ∧
  (can_remove used (Denv n) ⇔ ¬ is_used used n) ∧
  (* a type abbreviation has no effect whatsoever: evaluating it changes
     nothing and binds nothing, and the type checker has already run *)
  (can_remove used (Dtabbrev l tvs tn t) ⇔ T) ∧
  (can_remove used _ ⇔ F)
End

Definition prune_pat_def:
  prune_pat used Pany = Pany ∧
  prune_pat used (Pvar n) = (if is_used used n then Pvar n else Pany) ∧
  prune_pat used (Plit l) = Plit l ∧
  prune_pat used (Pcon cn ps) = Pcon cn (prune_pat_list used ps) ∧
  prune_pat used (Pref p) = Pref (prune_pat used p) ∧
  prune_pat used (Pas p n) =
    (if is_used used n then Pas (prune_pat used p) n else prune_pat used p) ∧
  prune_pat used (Ptannot p t) = Ptannot (prune_pat used p) t ∧
  prune_pat_list used [] = [] ∧
  prune_pat_list used (p::ps) = prune_pat used p :: prune_pat_list used ps
End

Definition prune_dec_def:
  prune_dec used (Dlet l p e) = Dlet l (prune_pat used p) e ∧
  prune_dec used d = d
End

(* -------------------------------------------------------------------------
   The transformation
   ------------------------------------------------------------------------- *)

Definition dce_decs_def:
  dce_decs used [] = (Nil,used) ∧
  dce_decs used (d::ds) =
    (let (ds1,used1) = dce_decs used ds in
     let (ds2,used2) = dce_dec used1 d in
       (SmartAppend ds2 ds1, used2)) ∧
  (* an empty module is kept: dropping it would remove a name-shadowing
     barrier, i.e. later qualified names could resolve differently *)
  dce_dec used (Dmod mn ds) =
    (let (ds1,used1) = dce_decs (strip_mod mn used) ds in
     let ds2 = append ds1 in
       if NULL ds2 then (List [Dmod mn []],used)
       else (List [Dmod mn ds2], union_names used used1)) ∧
  dce_dec used (Dlocal lds ds) =
    (let (ds1,used1) = dce_decs used ds in
     let (lds1,used2) = dce_decs used1 lds in
     let lds2 = append lds1 in
       if NULL lds2 then (ds1,used1)
       else (List [Dlocal lds2 (append ds1)], union_names used used2)) ∧
  dce_dec used d =
    (if can_remove used d then (Nil,used)
     else (List [prune_dec used d], update_names used d))
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL (_,ds) => list_size dec_size ds
                           | INR (_,d) => dec_size d)’
End

(* -------------------------------------------------------------------------
   Top-level entry point
   ------------------------------------------------------------------------- *)

Definition has_Denv_dec_def:
  has_Denv_dec (Denv n) = T ∧
  has_Denv_dec (Dmod mn ds) = has_Denv_decs ds ∧
  has_Denv_dec (Dlocal lds ds) = (has_Denv_decs lds ∨ has_Denv_decs ds) ∧
  has_Denv_dec _ = F ∧
  has_Denv_decs [] = F ∧
  has_Denv_decs (d::ds) = (has_Denv_dec d ∨ has_Denv_decs ds)
Termination
  wf_rel_tac ‘measure (λx. case x of
                           | INL d => dec_size d
                           | INR ds => list_size dec_size ds)’
End

Definition compile_decs_def:
  compile_decs ds =
    let ds1 = append (FST (dce_decs empty_names ds)) in
      if has_Denv_decs ds1 then ds else ds1
End

(* -------------------------------------------------------------------------
   Tests
   ------------------------------------------------------------------------- *)

(* an unused function is removed, a used one is kept *)
Theorem test_unused[local]:
  compile_decs
    [Dlet l (Pvar «unused») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «used») (Fun «y» (Var (Short «y»)));
     Dlet l Pany (App Opapp [Var (Short «used»); Lit (IntLit 4)])] =
    [Dlet l (Pvar «used») (Fun «y» (Var (Short «y»)));
     Dlet l Pany (App Opapp [Var (Short «used»); Lit (IntLit 4)])]
Proof
  EVAL_TAC
QED

(* unused declarations that are not functions are removed when neither the
   expression nor the pattern can have an effect *)
Theorem test_pure[local]:
  compile_decs
    [Dlet l (Pvar «x») (App (Arith Add IntT) [Lit (IntLit 1); Lit (IntLit 2)]);
     Dlet l (Pcon NONE [Pvar «a»; Pvar «b»])
       (Con NONE [Var (Short «x»); App Opderef [Var (Short «r»)]]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* a declaration that only allocates something that nothing can reach is
   removed too *)
Theorem test_alloc[local]:
  compile_decs
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «a») (App AallocEmpty [Con NONE []]);
     Dlet l (Pvar «v») (App AallocFixed [Lit (IntLit 1); Lit (IntLit 2)]);
     Dlet l (Pvar «arr») (App Aalloc [Lit (IntLit 5); Lit (IntLit 0)]);
     Dlet l (Pvar «arr2»)
       (App Aalloc [Lannot (Tannot (Lit (IntLit 5)) (Atapp [] (Short «int»))) l;
                    Lit (IntLit 0)]);
     Dlet l (Pvar «bs») (App Aw8alloc [Lit (IntLit 5); Lit (Word8 0w)]);
     Dlet l (Pvar «t»)
       (App (ThunkOp (AllocThunk NotEvaluated)) [Fun «u» (Lit (IntLit 1))]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* declarations that can change the state, raise an exception or diverge are
   kept, and so are patterns that can fail to match. Note the two Aalloc:s:
   the length is not known to be non-negative in either. *)
Theorem test_impure[local]:
  compile_decs
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App (Arith Div IntT) [Lit (IntLit 1); Var (Short «n»)]);
     Dlet l Pany (App (FromTo IntT CharT) [Lit (IntLit 300)]);
     Dlet l Pany (App Asub [Var (Short «arr»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Var (Short «n»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Lit (IntLit (-1)); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Tannot (Lit (IntLit (-1)))
                                     (Atapp [] (Short «int»)); Lit (IntLit 0)]);
     Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l Pany (Raise (Con (SOME (Short «Bind»)) []));
     Dlet l (Plit (IntLit 3)) (Lit (IntLit 3))] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App (Arith Div IntT) [Lit (IntLit 1); Var (Short «n»)]);
     Dlet l Pany (App (FromTo IntT CharT) [Lit (IntLit 300)]);
     Dlet l Pany (App Asub [Var (Short «arr»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Var (Short «n»); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Lit (IntLit (-1)); Lit (IntLit 0)]);
     Dlet l Pany (App Aalloc [Tannot (Lit (IntLit (-1)))
                                     (Atapp [] (Short «int»)); Lit (IntLit 0)]);
     Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l Pany (Raise (Con (SOME (Short «Bind»)) []));
     Dlet l (Plit (IntLit 3)) (Lit (IntLit 3))]
Proof
  EVAL_TAC
QED

(* type abbreviations are always removed *)
Theorem test_dtabbrev[local]:
  compile_decs
    [Dtabbrev l [] «t» (Atapp [] (Short «int»));
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* in a declaration that is kept, the unused names of the pattern are
   replaced by wildcards *)
Theorem test_prune[local]:
  compile_decs
    [Dlet l (Pcon NONE [Pvar «a»; Pvar «b»])
       (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l (Pas (Pvar «d») «e»)
       (App Opassign [Var (Short «out»); Lit (IntLit 1)]);
     Dlet l (Pvar «c») (App Opassign [Var (Short «out»); Var (Short «b»)])] =
    [Dlet l (Pcon NONE [Pany; Pvar «b»])
       (App Opassign [Var (Short «out»); Lit (IntLit 0)]);
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)]);
     Dlet l Pany (App Opassign [Var (Short «out»); Var (Short «b»)])]
Proof
  EVAL_TAC
QED

(* a Dlocal of which nothing is left is dropped; a module is emptied but
   kept, since dropping it could change how later qualified names resolve *)
Theorem test_empty_mod[local]:
  compile_decs
    [Dmod «M» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))];
     Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))] [];
     Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] [];
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])] =
    [Dmod «M» [];
     Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] [];
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 0)])]
Proof
  EVAL_TAC
QED

(* a Dlocal whose local part is left empty is replaced by its visible part *)
Theorem test_empty_local[local]:
  compile_decs
    [Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)));
             Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
            [Dlet l (Pvar «h») (Fun «x» (Var (Short «x»)))];
     Dlocal [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]
            [Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 2)])]] =
    [Dlocal [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
            [Dlet l (Pvar «h») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 2)])]
Proof
  EVAL_TAC
QED

(* a case expression is pure only if one of its patterns always matches *)
Theorem test_pure_mat[local]:
  compile_decs
    [Dlet l (Pvar «x») (Mat (Var (Short «y»)) [(Pany, Lit (IntLit 2))]);
     Dlet l Pany (Mat (Var (Short «y»)) [(Plit (IntLit 1), Lit (IntLit 2))])] =
    [Dlet l Pany (Mat (Var (Short «y»)) [(Plit (IntLit 1), Lit (IntLit 2))])]
Proof
  EVAL_TAC
QED

(* whole chains of unused functions are removed, including Dletrec:s, and
   a Dlet with a wildcard pattern that binds a Fun is always removed *)
Theorem test_chain[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dletrec l [(«g»,«y»,App Opapp [Var (Short «f»); Var (Short «g»)])];
     Dlet l Pany (Fun «z» (App Opapp [Var (Short «g»); Var (Short «z»)]))] = []
Proof
  EVAL_TAC
QED

(* a Dletrec is kept if any of its names is used *)
Theorem test_letrec_used[local]:
  compile_decs
    [Dletrec l [(«f»,«x»,Var (Short «g»)); («g»,«y»,Var (Short «f»))];
     Dlet l Pany (App Opapp [Var (Short «g»); Lit (IntLit 1)])] =
    [Dletrec l [(«f»,«x»,Var (Short «g»)); («g»,«y»,Var (Short «f»))];
     Dlet l Pany (App Opapp [Var (Short «g»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a later declaration of the same name shadows an earlier one, which makes
   the earlier one dead *)
Theorem test_shadow_dletrec[local]:
  compile_decs
    [Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dletrec l [(«foo»,«x»,Var (Short «bar»))];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* but the shadowing declaration can itself refer to the shadowed one *)
Theorem test_shadow_dlet[local]:
  compile_decs
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «foo») (Fun «x» (App Opapp [Var (Short «foo»);
                                              Var (Short «x»)]));
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlet l (Pvar «foo») (Fun «x» (App Opapp [Var (Short «foo»);
                                              Var (Short «x»)]));
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the local part of a Dlocal is not visible after it, so it does not
   shadow anything *)
Theorem test_local_no_shadow[local]:
  compile_decs
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlocal [Dlet l (Pvar «foo») (Fun «x» (Lit (IntLit 1)))] [];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])] =
    [Dlet l (Pvar «foo») (Fun «x» (Var (Short «x»)));
     Dlocal [Dlet l (Pvar «foo») (Fun «x» (Lit (IntLit 1)))] [];
     Dlet l Pany (App Opapp [Var (Short «foo»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a local variable with the same name does not count as a use *)
Theorem test_shadow[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dlet l Pany
       (Let (SOME «f») (Fun «x» (Var (Short «x»)))
            (App Opapp [Var (Short «f»); Lit (IntLit 1)]))] =
    [Dlet l Pany
       (Let (SOME «f») (Fun «x» (Var (Short «x»)))
            (App Opapp [Var (Short «f»); Lit (IntLit 1)]))]
Proof
  EVAL_TAC
QED

(* an allocation is kept when the location it makes is used, and a name
   bound by a pattern of a case expression is not a use *)
Theorem test_effect[local]:
  compile_decs
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «f») (Fun «x» (App Opassign [Var (Short «r»); Var (Short «x»)]));
     Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)));
     Dlet l Pany
       (Mat (Lit (IntLit 1))
          [(Pvar «g», App Opapp [Var (Short «f»); Var (Short «g»)])])] =
    [Dlet l (Pvar «r») (App Opref [Lit (IntLit 0)]);
     Dlet l (Pvar «f») (Fun «x» (App Opassign [Var (Short «r»); Var (Short «x»)]));
     Dlet l Pany
       (Mat (Lit (IntLit 1))
          [(Pvar «g», App Opapp [Var (Short «f»); Var (Short «g»)])])]
Proof
  EVAL_TAC
QED

(* unused declarations inside modules are removed, and qualified names
   count as uses of the declarations they refer to *)
Theorem test_module[local]:
  compile_decs
    [Dmod «M» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
               Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany
       (App Opapp [Var (Long «M» (Short «g»)); Lit (IntLit 1)])] =
    [Dmod «M» [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))];
     Dlet l Pany
       (App Opapp [Var (Long «M» (Short «g»)); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* only uses in later declarations count *)
Theorem test_later_use_only[local]:
  compile_decs
    [Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)]);
     Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))] =
    [Dlet l Pany (App Opapp [Var (Short «f»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* nested modules *)
Theorem test_nested_module[local]:
  compile_decs
    [Dmod «A» [Dmod «B» [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
                         Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]];
     Dlet l Pany
       (App Opapp [Var (Long «A» (Long «B» (Short «g»))); Lit (IntLit 1)])] =
    [Dmod «A» [Dmod «B» [Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]];
     Dlet l Pany
       (App Opapp [Var (Long «A» (Long «B» (Short «g»))); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the local part of a Dlocal is only used by its visible part *)
Theorem test_local[local]:
  compile_decs
    [Dlocal [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
             Dlet l (Pvar «g») (Fun «x» (Var (Short «x»)))]
            [Dlet l (Pvar «h») (Fun «x» (App Opapp [Var (Short «f»);
                                                    Var (Short «x»)]))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 1)])] =
    [Dlocal [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)))]
            [Dlet l (Pvar «h») (Fun «x» (App Opapp [Var (Short «f»);
                                                    Var (Short «x»)]))];
     Dlet l Pany (App Opapp [Var (Short «h»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a Denv whose name is never used is dropped, and its presence does not
   stop the other declarations from being removed *)
Theorem test_denv_unused[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* the name of a Denv counts as used only in declarations that are kept *)
Theorem test_denv_used_by_dead[local]:
  compile_decs
    [Denv «e»;
     Dlet l (Pvar «f») (Fun «x» (Var (Short «e»)));
     Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])] =
    [Dlet l Pany (App Opassign [Var (Short «out»); Lit (IntLit 1)])]
Proof
  EVAL_TAC
QED

(* a program where a Denv survives is left alone *)
Theorem test_denv_used[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opapp [Var (Short «g»); Var (Short «e»)])] =
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Opapp [Var (Short «g»); Var (Short «e»)])]
Proof
  EVAL_TAC
QED

(* an Eval does not stop the pass by itself: it takes an Env value to
   evaluate anything, and only a Denv makes one. The Eval is kept, since
   it is not a pure expression, but the dead function next to it goes. *)
Theorem test_eval[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Dlet l Pany (App Eval [Var (Short «x»)])] =
    [Dlet l Pany (App Eval [Var (Short «x»)])]
Proof
  EVAL_TAC
QED

(* but a program that has both is left alone, because the Denv survives *)
Theorem test_eval_denv[local]:
  compile_decs
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Eval [Var (Short «e»)])] =
    [Dlet l (Pvar «f») (Fun «x» (Var (Short «x»)));
     Denv «e»;
     Dlet l Pany (App Eval [Var (Short «e»)])]
Proof
  EVAL_TAC
QED
