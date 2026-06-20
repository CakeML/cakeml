(*
  Setting up translator for the fmap instances that are used in aig_to_cnf.
*)
Theory aig_fmapsProg
Ancestors
  aig_cert_encodeProg aig_to_cnf
Libs
  preamble ml_translatorLib

val _ = translation_extends "aig_cert_encodeProg";

(*----------------------------------------------------------------------*
   general tooling for adding mlmap support for fmaps
 *----------------------------------------------------------------------*)

Definition FMAP_TYPE_def:
  FMAP_TYPE cmp a b f v =
    ∃m. mlmap$map_ok m ∧ mlmap$to_fmap m = f ∧ MAP_TYPE a b m v ∧
        mlmap$cmp_of m = cmp
End

Theorem MAP_TYPE_empty_IMP_FMAP_TYPE:
  MAP_TYPE a b (mlmap$empty cmp) v ∧ TotOrd cmp ⇒
  FMAP_TYPE cmp a b FEMPTY v
Proof
  rw [FMAP_TYPE_def]
  \\ last_x_assum $ irule_at Any
  \\ fs [mlmapTheory.empty_thm]
QED

Theorem IMP_FMAP_TYPE_FLOOKUP:
  (MAP_TYPE b a --> b --> OPTION_TYPE a) mlmap$lookup v ⇒
  (FMAP_TYPE cmp b a --> b --> OPTION_TYPE a) FLOOKUP v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def]
  \\ rw [] \\ simp [GSYM (mlmapTheory.lookup_thm)]
QED

Theorem IMP_FMAP_TYPE_FUPDATE:
  (MAP_TYPE b a --> (b:'a -> v -> bool) --> a --> MAP_TYPE b a) mlmap$insert v ⇒
  (FMAP_TYPE cmp b a --> b --> a --> FMAP_TYPE cmp b a) fmap_update v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ fs [fmap_update_def]
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.insert_thm]
QED

Theorem IMP_FMAP_TYPE_DOMSUB:
  (MAP_TYPE b a --> (b:'a -> v -> bool) --> MAP_TYPE b a) mlmap$delete v ⇒
  (FMAP_TYPE cmp b a --> b --> FMAP_TYPE cmp b a) $\\ v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.delete_thm]
QED

Theorem IMP_FMAP_TYPE_FUNION:
  (MAP_TYPE b a --> MAP_TYPE b a --> MAP_TYPE b a) mlmap$union v ⇒
  (FMAP_TYPE cmp b a --> FMAP_TYPE cmp b a --> FMAP_TYPE cmp b a) FUNION v
Proof
  fs [ml_translatorTheory.Arrow_def,FMAP_TYPE_def,
      ml_translatorTheory.AppReturns_def] \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum $ qspec_then ‘refs’ strip_assume_tac \\ fs []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ first_x_assum $ irule_at Any \\ rw []
  \\ metis_tac [mlmapTheory.union_thm]
QED

Theorem IMP_FMAP_TYPE_ops:
  MAP_TYPE (key:'k -> v -> bool) (a:'a -> v -> bool) (mlmap$empty cmp) v ∧ TotOrd cmp ⇒
  FMAP_TYPE cmp key a FEMPTY v ∧
  ((MAP_TYPE key a --> key --> OPTION_TYPE a) mlmap$lookup v1 ⇒
   (FMAP_TYPE cmp key a --> key --> OPTION_TYPE a) FLOOKUP v1) ∧
  ((MAP_TYPE key a --> key --> a --> MAP_TYPE key a) mlmap$insert v1 ⇒
   (FMAP_TYPE cmp key a --> key --> a --> FMAP_TYPE cmp key a) fmap_update v1) ∧
  ((MAP_TYPE key a --> key --> MAP_TYPE key a) mlmap$delete v1 ⇒
   (FMAP_TYPE cmp key a --> key --> FMAP_TYPE cmp key a) $\\ v1) ∧
  ((MAP_TYPE key a --> MAP_TYPE key a --> MAP_TYPE key a) mlmap$union v1 ⇒
   (FMAP_TYPE cmp key a --> FMAP_TYPE cmp key a --> FMAP_TYPE cmp key a) FUNION v1)
Proof
  rw []
  >- (irule MAP_TYPE_empty_IMP_FMAP_TYPE \\ simp [])
  >- (irule IMP_FMAP_TYPE_FLOOKUP \\ simp [])
  >- (irule IMP_FMAP_TYPE_FUPDATE \\ simp [])
  >- (irule IMP_FMAP_TYPE_DOMSUB \\ simp [])
  >- (irule IMP_FMAP_TYPE_FUNION \\ simp [])
QED

val mlmap_lookup_v_thm =
  match ["MapProg"] “(_ --> _) mlmap$lookup _” |> hd |> snd |> #1;
val mlmap_union_v_thm =
  match ["MapProg"] “(_ --> _) mlmap$union _” |> hd |> snd |> #1
val mlmap_delete_v_thm =
  match ["MapProg"] “(_ --> _) mlmap$delete _” |> hd |> snd |> #1;
val mlmap_insert_v_thm =
  match ["MapProg"] “(_ --> _) mlmap$insert _” |> hd |> snd |> #1;

fun add_fmap_for_cmp th = let
  val cmp_tm = th |> concl |> rand
  val _ = hol2deep cmp_tm handle UnableToTranslate _ =>
          failwith "Ordering must the translated first"
  fun find_name name i = let
    val s = if i < 0 then name else name ^ "_" ^ int_to_string i
    in
      (if (Parse.Term [QUOTE (s ^ " :'a ")] |> is_const) then
         find_name name (i+1)
       else s)
      handle HOL_ERR _ => find_name name (i+1)
    end
  val const_name = find_name "fempty" (0-1)
  val tm = mlmapTheory.empty_def |> ISPEC cmp_tm |> concl |> dest_eq |> fst
  val def_tm = mk_eq(mk_var(const_name,type_of tm), tm)
  val def = new_definition(const_name ^ "_def", def_tm)
  val empty_v_thm = translate def
  val lem = CONJ (empty_v_thm |> REWRITE_RULE [def]) th
  val ops_thm = MATCH_MP IMP_FMAP_TYPE_ops lem
  val fempty_thm = ops_thm |> cj 1
  (* empty + teach about type’*)
  val res = fempty_thm |> concl |> rator
  val fmap_ty = res |> rand |> type_of
  val fmap_inv = res |> rator
  val _ = add_type_inv fmap_inv fmap_ty
  val _ = add_user_proved_v_thm fempty_thm
  (* lookup *)
  val th1 = cj 2 ops_thm
  val th2 = mlmap_lookup_v_thm
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val flookup_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm flookup_thm
  (* delete *)
  val th1 = cj 4 ops_thm
  val th2 = mlmap_delete_v_thm
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val domsub_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm domsub_thm
  (* update *)
  val th1 = cj 3 ops_thm
  val th2 = mlmap_insert_v_thm
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val fmap_update_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm fmap_update_thm
  (* union *)
  val th1 = cj 5 ops_thm
  val th2 = mlmap_union_v_thm
  val tm1 = th1 |> concl |> dest_imp |> fst |> rator |> rator
  val tm2 = th2 |> concl |> rator |> rator
  val (i1,i2) = match_term tm2 tm1
  val th2a = INST i1 (INST_TYPE i2 th2)
  val funion_thm = MATCH_MP th1 th2a
  val _ = add_user_proved_v_thm funion_thm
  in () end;

(*----------------------------------------------------------------------*
   specific types to target
 *----------------------------------------------------------------------*)

Type ty1[local] = “:num”;
Type ty2[local] = “:num + num”;
Type ty3[local] = “:num iext”;
Type ty4[local] = “:(num + num) iext”;
Type ty5[local] = “:(num iext + num iext) iext”;
Type ty6[local] = “:((num + num) iext + (num + num) iext) iext”;

(*----------------------------------------------------------------------*
   ty1
 *----------------------------------------------------------------------*)

Definition num_cmp_def:
  num_cmp n1 (n2:num) =
    if n1 < n2 then LESS else
    if n2 < n1 then GREATER else EQUAL
End

val _ = translate num_cmp_def;

Theorem TotOrd_ty1:
  TotOrd (num_cmp : ty1 -> ty1 -> ordering)
Proof
  fs [totoTheory.TotOrd, num_cmp_def, CaseEq"bool"]
QED

(*----------------------------------------------------------------------*
   ty2
 *----------------------------------------------------------------------*)

Definition sum_cmp_def:
  sum_cmp c1 c2 x1 x2 =
    case x1 of
    | INL n1 =>
        (case x2 of
         | INL n2 => c1 n1 n2
         | INR _ => LESS)
    | INR n1 =>
        (case x2 of
         | INL _ => GREATER
         | INR n2 => c2 n1 n2)
End

Theorem sum_forall:
  (∀x. P x) ⇔ (∀y. P (INL y)) ∧ (∀y. P (INR y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem TotOrd_sum:
  TotOrd c1 ∧ TotOrd c2 ⇒
  TotOrd (sum_cmp c1 c2)
Proof
  fs [totoTheory.TotOrd, sum_cmp_def, AllCaseEqs(), sum_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

Definition num_sum_num_cmp_def:
  num_sum_num_cmp = sum_cmp num_cmp num_cmp
End

Theorem num_sum_num_cmp_eq[local] =
  num_sum_num_cmp_def |> SRULE [sum_cmp_def, num_cmp_def, FUN_EQ_THM];

val r = translate num_sum_num_cmp_eq;

Theorem TotOrd_ty2:
  TotOrd (num_sum_num_cmp : ty2 -> ty2 -> ordering)
Proof
  rewrite_tac [num_sum_num_cmp_def]
  \\ irule TotOrd_sum \\ simp [TotOrd_ty1]
QED

(*----------------------------------------------------------------------*
   ty3
 *----------------------------------------------------------------------*)

Definition ext_cmp_def:
  ext_cmp cmp (x1: 'a ext) (x2: 'a ext) =
    case x1 of
    | Orig n1 =>
        (case x2 of
         | Orig n2 => cmp n1 n2
         | Ext _ => LESS)
    | Ext n1 =>
        (case x2 of
         | Orig _ => GREATER
         | Ext n2 => mlstring$compare n1 n2)
End

Definition iext_cmp_def:
  iext_cmp cmp (x1: 'a iext) (x2: 'a iext) =
    case x1 of
    | Named n1 =>
        (case x2 of
         | Named n2 => ext_cmp cmp n1 n2
         | Anon _ => LESS)
    | Anon n1 =>
        (case x2 of
         | Named _ => GREATER
         | Anon n2 => num_cmp n1 n2)
End

Theorem ext_forall:
  (∀x. P x) ⇔ (∀y. P (Orig y)) ∧ (∀y. P (Ext y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem iext_forall:
  (∀x. P x) ⇔ (∀y. P (Named y)) ∧ (∀y. P (Anon y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem TotOrd_ext:
  TotOrd c1 ⇒ TotOrd (ext_cmp c1)
Proof
  mp_tac mlstringTheory.TotOrd_compare
  \\ fs [totoTheory.TotOrd, ext_cmp_def, AllCaseEqs(), ext_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

Theorem TotOrd_iext:
  TotOrd c1 ⇒ TotOrd (iext_cmp c1)
Proof
  strip_tac \\ dxrule TotOrd_ext
  \\ mp_tac TotOrd_ty1
  \\ fs [totoTheory.TotOrd, iext_cmp_def, AllCaseEqs(), iext_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

Definition num_iext_cmp_def:
  num_iext_cmp = iext_cmp num_cmp
End

Theorem num_iext_cmp_eq[local] =
  num_iext_cmp_def |> SRULE [iext_cmp_def, num_cmp_def, FUN_EQ_THM, ext_cmp_def];

val r = translate num_iext_cmp_eq;

Theorem TotOrd_ty3:
  TotOrd (num_iext_cmp : ty3 -> ty3 -> ordering)
Proof
  rewrite_tac [num_iext_cmp_def]
  \\ irule TotOrd_iext \\ simp [TotOrd_ty1]
QED

(*----------------------------------------------------------------------*
   ty4
 *----------------------------------------------------------------------*)

Definition ty4_cmp_def:
  ty4_cmp = iext_cmp num_sum_num_cmp
End

Theorem ty4_cmp_eq[local] =
  ty4_cmp_def
  |> SRULE [iext_cmp_def, num_sum_num_cmp_eq, FUN_EQ_THM, ext_cmp_def, num_cmp_def];

val r = translate ty4_cmp_eq;

Theorem TotOrd_ty4:
  TotOrd (ty4_cmp : ty4 -> ty4 -> ordering)
Proof
  rewrite_tac [ty4_cmp_def]
  \\ irule TotOrd_iext \\ simp [TotOrd_ty2]
QED

(*----------------------------------------------------------------------*
   ty5
 *----------------------------------------------------------------------*)

Definition ty5_cmp_def:
  ty5_cmp = iext_cmp (sum_cmp num_iext_cmp num_iext_cmp)
End

Theorem ty5_cmp_eq[local] =
  ty5_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty5_cmp_eq;

Theorem TotOrd_ty5:
  TotOrd (ty5_cmp : ty5 -> ty5 -> ordering)
Proof
  rewrite_tac [ty5_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty3]
QED

(*----------------------------------------------------------------------*
   ty6
 *----------------------------------------------------------------------*)

Definition ty6_cmp_def:
  ty6_cmp = iext_cmp (sum_cmp ty4_cmp ty4_cmp)
End

Theorem ty6_cmp_eq[local] =
  ty6_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty6_cmp_eq;

Theorem TotOrd_ty6:
  TotOrd (ty6_cmp : ty6 -> ty6 -> ordering)
Proof
  rewrite_tac [ty6_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty4]
QED

(*----------------------------------------------------------------------*
   translating them all
 *----------------------------------------------------------------------*)

val _ = add_fmap_for_cmp TotOrd_ty1;
val _ = add_fmap_for_cmp TotOrd_ty2;
val _ = add_fmap_for_cmp TotOrd_ty3;
val _ = add_fmap_for_cmp TotOrd_ty4;
val _ = add_fmap_for_cmp TotOrd_ty5;
val _ = add_fmap_for_cmp TotOrd_ty6;
