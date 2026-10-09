(*
  Defines a datatype for nested namespaces where names can be either
  short (e.g. foo) or long (e.g. ModuleA.InnerB.bar).
*)
Theory namespace
Ancestors[qualified]
  alist

val _ = numLib.temp_prefer_num();

Type alist = ``: ('k # 'v) list``

(* Identifiers *)
Datatype:
  id = Short 'n | Long 'm id
End

Definition mk_id_def:
  mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
End

Definition id_to_n_def:
 id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
End

Definition id_to_mods_def:
  id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
End

Datatype:
  namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
End

Definition nsLookup_def:
  nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
End

Definition nsLookupMod_def:
  nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
End

(* Resolve a source-level module-open path.  Unlike nsLookupMod, an empty
   path is not a valid open and must not select the entire current namespace. *)
Definition nsOpen_def:
  nsOpen path (env:('m,'n,'v)namespace) =
    if NULL path then NONE else nsLookupMod env path
End

Definition nsEmpty_def:
  nsEmpty = Bind [] []
End

Definition nsAppend_def:
  nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
End

Definition nsLift_def:
  nsLift mn env = Bind [] [(mn,env)]
End

Definition alist_to_ns_def:
  alist_to_ns a = Bind a []
End

Definition nsBind_def:
  nsBind k x (Bind v m) = Bind ((k,x)::v) m
End

Definition nsBindList_def:
  nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
End

Definition nsOptBind_def:
  nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
End

Definition nsSing_def:
  nsSing n x = Bind [(n,x)] []
End

Definition nsSub_def:
  nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
End

Definition nsAll_def:
  nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
End

Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End

Definition nsDom_def:
  nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
End

Definition nsDomMod_def:
  nsDomMod (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:(ν, ξ, φ) namespace) ∧ n ∈ 𝕌(:ν list) ∧
                  nsLookupMod env n = SOME v}
End

Definition nsMap_def:
  nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
End
