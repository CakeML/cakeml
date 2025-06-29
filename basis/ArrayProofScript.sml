(*
  Proofs about the Array module.
*)
open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory ArrayProgTheory

val _ = new_theory"ArrayProof";

val _ = translation_extends "ArrayProg";

val array_st = get_ml_prog_state();

fun prove_array_spec op_name =
  rpt strip_tac \\
  xcf op_name array_st \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_empty_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def, REPLICATE] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

Theorem array_alloc_spec:
   !n nv v.
     NUM n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.array" array_st) [nv; v]
       emp (POSTv av. ARRAY av (REPLICATE n v))
Proof
  prove_array_spec "Array.array"
QED

Theorem array_alloc_empty_spec:
   !v.
     UNIT_TYPE () v ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "Array.arrayEmpty" array_st) [v]
       emp (POSTv av. ARRAY av [])
Proof
  prove_array_spec "Array.arrayEmpty"
QED

Theorem array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.sub" array_st) [av; nv]
       (ARRAY av a) (POSTv v. cond (v = EL n a) * ARRAY av a)
Proof
  prove_array_spec "Array.sub"
QED

Theorem array_length_spec:
   !a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Array.length" array_st) [av]
       (ARRAY av a)
       (POSTv v. cond (NUM (LENGTH a) v) * ARRAY av a)
Proof
  prove_array_spec "Array.length"
QED

Theorem array_update_spec:
   !a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.update" array_st)
       [av; nv; v]
       (ARRAY av a)
       (POSTv uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))
Proof
  prove_array_spec "Array.update"
QED

Theorem array_fromList_spec:
   !l lv a A.
    LIST_TYPE A l lv /\ v_to_list lv = SOME a ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Array.fromList" array_st) [lv]
      emp (POSTv av. ARRAY av a)
Proof
  rpt strip_tac \\
  xcf "Array.fromList" array_st \\
  xfun_spec `f`
    `!ls lsv i iv a l_pre rest ar.
      NUM i iv /\ LENGTH l_pre = i /\
      LIST_TYPE A ls lsv /\ v_to_list lsv = SOME a /\ LENGTH ls = LENGTH rest
    ==>
    app p f [ar; lsv; iv]
    (ARRAY ar (l_pre ++ rest))
    (POSTv ret. & (ret = ar) * ARRAY ar (l_pre ++ a))` >- (
      Induct
        >- (rw[LIST_TYPE_def] \\
        first_x_assum match_mp_tac \\
        xmatch \\ xret \\
        fs [LENGTH_NIL_SYM] \\
        fs [semanticPrimitivesTheory.v_to_list_def] \\
        xsimpl) \\
      rw[LIST_TYPE_def] \\
      fs[semanticPrimitivesTheory.v_to_list_def] \\
      qpat_x_assum`_ = SOME _`mp_tac \\ CASE_TAC \\ rw[] \\
      last_x_assum match_mp_tac \\
      xmatch \\
      Cases_on `rest` \\ fs[] \\
      qmatch_assum_rename_tac`A h hv` \\
      xlet `POSTv u. ARRAY ar (l_pre ++ hv::t)` >- (
        xapp \\
        instantiate \\
        xsimpl ) \\
      xlet `POSTv iv. ARRAY ar (l_pre ++ hv::t) * & NUM (LENGTH l_pre + 1) iv`
      >- (
        xapp \\
        xsimpl \\
        qexists_tac `&(LENGTH l_pre)` \\
        fs [NUM_def, plus_def, integerTheory.INT_ADD]
        ) \\
      once_rewrite_tac[CONS_APPEND] \\
      rewrite_tac[APPEND_ASSOC] \\
      xapp \\ xsimpl ) \\
  Cases_on `l` >>
  fs [LIST_TYPE_def] >>
  rfs [] >>
  xmatch
  >- (
    fs [semanticPrimitivesTheory.v_to_list_def] >>
    rw [] >>
    xlet `POSTv uv. &UNIT_TYPE () uv`
    >- (
      xret >>
      xsimpl) >>
    xapp >>
    simp []) >>
  rw [] >>
  xlet `POSTv lv. &NUM (LENGTH t + 1) lv`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `h::t` >>
    qexists_tac `A` >>
    simp [LIST_TYPE_def, ADD1]) >>
  xlet `POSTv av. ARRAY av (REPLICATE (LENGTH t + 1) v2_1)`
  >- (
    xapp >>
    simp []) >>
  fs [semanticPrimitivesTheory.v_to_list_def] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  first_x_assum (qspecl_then [`t`, `v2_2`, `Litv (IntLit &1)`, `x`, `[v2_1]`,
                              `REPLICATE (LENGTH t) v2_1`] mp_tac) >>
  simp [LENGTH_REPLICATE] >>
  qpat_x_assum`_ = list_type_num`(assume_tac o SYM) \\ fs[GSYM ADD1] \\
  disch_then xapp_spec >>
  xsimpl >>
  rw [REPLICATE, GSYM ADD1]
QED

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1)

Triviality num_eq_thm:
  !n nv x xv. NUM n nv /\ NUM x xv ==> (n = x <=> nv = xv)
Proof
  metis_tac[EqualityType_NUM_BOOL, EqualityType_def]
QED

Theorem array_tabulate_spec:
   !n nv f fv (A: 'a -> v -> bool).
    NUM n nv /\ (NUM --> A) f fv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Array.tabulate" array_st) [nv; fv]
    emp (POSTv av. SEP_EXISTS vs. ARRAY av vs * cond (EVERY2 A (GENLIST f n) vs))
Proof
  rpt strip_tac
  \\ xcf "Array.tabulate" array_st
  \\ xfun_spec `u`
      `!x xv l_pre rest av.
        NUM x xv /\ LENGTH l_pre = x /\ LENGTH l_pre + LENGTH rest = n ==>
          app p u [av; xv]
        (ARRAY av (l_pre ++ rest))
        (POSTv ret. SEP_EXISTS vs. & (ret = av) * ARRAY av (l_pre ++ vs) * cond (EVERY2 A (GENLIST (\i. f (x + i)) (n - x)) vs))`
  >- (Induct_on `n - x`
    >- (rw []  \\ first_x_assum match_mp_tac
        \\ xlet `POSTv bv. & BOOL (xv=nv) bv * ARRAY av l_pre`
        >- (
          xapp_spec eq_num_v_thm \\ rw[BOOL_def] \\ xsimpl
          \\ `LENGTH rest = 0` by decide_tac
          \\ `xv = nv` by fs [NUM_def, INT_def]
          \\ instantiate \\ fs [])
      \\ xif >- (xret \\ xsimpl \\ `LENGTH rest = 0` by decide_tac \\ fs[] )
      \\ gvs [NUM_def, INT_def] \\ Cases_on ‘rest’ >> gvs[])
    \\ rw[] \\ first_assum match_mp_tac
    \\ xlet `POSTv bv. & BOOL (xv = nv) bv * ARRAY av (l_pre ++ rest)`
      >- (xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[BOOL_def, NUM_def, INT_def])
    \\ xif
      >- (xret \\ xsimpl \\ `LENGTH rest = 0` by fs [NUM_def, INT_def]
        \\ fs [GENLIST, LENGTH_NIL])
    \\ xlet `POSTv val. ARRAY av (l_pre ++ rest) * & A (f (LENGTH l_pre)) val`
      >- (xapp \\ xsimpl \\ instantiate)
    \\ xlet `POSTv u. ARRAY av (LUPDATE val (LENGTH l_pre) (l_pre ++ rest))`
      >- (xapp \\ xsimpl \\ instantiate \\ `LENGTH l_pre + LENGTH rest <> LENGTH l_pre` by metis_tac[num_eq_thm] \\ fs[])
    \\ xlet_auto
    \\ fs [plus_def]
    THEN1 xsimpl
    \\ xapp \\ xsimpl \\ cases_on `rest`
      >- (`xv = nv` by fs [NUM_def, INT_def])
    \\ qexists_tac `t` \\ qexists_tac `l_pre ++ [val]`
    \\ fs [LENGTH, ADD1, GSYM CONS_APPEND, lupdate_append2] \\ rw[GENLIST_CONS, GSYM ADD1, o_DEF] \\ fs [ADD1,NUM_def,GSYM integerTheory.INT_ADD]) >>
  Cases_on `n` >>
  fs [NUM_def, INT_def] >>
  rfs []
  >- (
    xlet `POSTv bv. &BOOL T bv`
    >- (
      xapp_spec eq_num_v_thm >>
      xsimpl) >>
    xif >>
    qexists_tac `T` >>
    simp [] >>
    xlet `POSTv uv. &UNIT_TYPE () uv`
    >- (
      xret >>
      xsimpl) >>
    xapp >>
    xsimpl) >>
  xlet `POSTv bv. &BOOL F bv`
  >- (
    xapp_spec eq_num_v_thm >>
    xsimpl) >>
  xif >>
  qexists_tac `F` >>
  simp [] >>
  xlet `POSTv xv. &A (f 0) xv`
  >- (
    xapp >>
    simp []) >>
  xlet `POSTv av. ARRAY av (REPLICATE (SUC n') xv)`
  >- (
    xapp >>
    simp [NUM_def] >>
    xsimpl) >>
  first_x_assum (qspecl_then [`[xv]`, `REPLICATE n' xv`, `av`] mp_tac) >>
  simp [LENGTH_REPLICATE] >>
  disch_then xapp_spec >>
  xsimpl >>
  rw [REPLICATE, GENLIST_CONS] >>
  simp [combinTheory.o_DEF, ADD1]
QED

(*
val _ = show_types := false
val _ = hide_environments true
val res = max_print_depth := 20


val _ = show_types := true
val _ = hide_environments false
val res = max_print_depth := 100
*)


Triviality less_than_length_thm:
  !xs n. (n < LENGTH xs) ==> (?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH ys = n))
Proof
  rw[] \\
  qexists_tac`TAKE n xs` \\
  rw[] \\
  qexists_tac`HD (DROP n xs)` \\
  qexists_tac`TL (DROP n xs)` \\
  Cases_on`DROP n xs` \\ fs[] \\
  metis_tac[TAKE_DROP,APPEND_ASSOC,CONS_APPEND]
QED


Triviality lupdate_breakdown_thm:
  !l val n. n < LENGTH l
    ==> LUPDATE val n l = TAKE n l ++ [val] ++ DROP (n + 1) l
Proof
  rw[] \\ drule less_than_length_thm
    \\ rw[] \\ simp_tac std_ss [TAKE_LENGTH_APPEND, GSYM APPEND_ASSOC, GSYM CONS_APPEND]
    \\simp_tac std_ss [DROP_APPEND2]
    \\ simp_tac std_ss [GSYM CONS_APPEND]
    \\ EVAL_TAC \\ rw[lupdate_append2]
QED

Theorem array_copy_aux_spec:
   !src n srcv dstv di div nv max maxv bfr mid afr.
      NUM di div /\ NUM n nv /\ NUM max maxv /\
      di = LENGTH bfr/\ LENGTH mid = max - n /\ n <= max /\
      max <= LENGTH src
      ==> app (p:'ffi ffi_proj) Array_copy_aux_v [srcv; dstv; div; maxv; nv]
      (ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr))
    (POSTv uv. ARRAY srcv src *
               ARRAY dstv (bfr ++ (TAKE (max -n) (DROP n src)) ++ afr))
Proof
  gen_tac \\ gen_tac \\ Induct_on `max - n` >>
  rpt strip_tac \\ xcf_with_def Array_copy_aux_v_def
  >-(xlet_auto >> (xsimpl >> xif) >>
     instantiate >> xcon >> xsimpl >> metis_tac[TAKE_0,LENGTH_NIL]) >>
  xlet_auto >- xsimpl >>
  xif >> instantiate >>
  NTAC 4 (xlet_auto >- xsimpl) >>
  xapp >> xsimpl >>
  cases_on`mid` >> fs[] >>
  qexists_tac`1 + n` >> qexists_tac`t` >>
  qexists_tac`max` >> qexists_tac`bfr ++ [EL n src]` >> fs[] >>
  qexists_tac`afr` >> rw[]
  >-(`LENGTH bfr <= LENGTH bfr` by fs[] >>
     imp_res_tac LUPDATE_APPEND2 >>
     first_x_assum (assume_tac o Q.SPECL[`EL n src`, `[h] ⧺ t ⧺ afr`]) >>
     fs[LUPDATE_def]) >>
 cases_on`DROP n src` >- fs[DROP_NIL] >>
 `EL (0 + n) src = EL 0 (DROP n src)` by fs[EL_DROP] >> fs[] >>
 `DROP 1 (DROP n src) = t'` by fs[GSYM DROP_DROP_T] >>
 fs[DROP_DROP_T]
QED


Theorem array_copy_spec:
   !src srcv bfr mid afr dstv di div.
      NUM di div /\ LENGTH src = LENGTH mid /\  di = LENGTH bfr
      ==> app (p:'ffi ffi_proj) ^(fetch_v "Array.copy" array_st) [srcv; dstv; div]
      (ARRAY srcv src * ARRAY dstv (bfr ++ mid ++ afr))
    (POSTv uv. ARRAY srcv src * ARRAY dstv (bfr ++ src ++ afr))
Proof
  rpt strip_tac \\
  xcf "Array.copy" array_st \\
  xlet_auto >- xsimpl >> xapp >> xsimpl >> instantiate >>
  fs[] >> instantiate >> metis_tac[TAKE_LENGTH_ID]
QED

Theorem array_app_aux_spec:
   ∀l idx len_v idx_v a_v f_v eff.
   NUM (LENGTH l) len_v ∧
   NUM idx idx_v ∧
   idx ≤ LENGTH l ∧
   (!n.
     n < LENGTH l ⇒
     app p f_v [EL n l] (eff l n) (POSTv v. &UNIT_TYPE () v * (eff l (n+1))))
   ⇒
   app (p:'ffi ffi_proj) Array_app_aux_v [f_v; a_v; len_v; idx_v]
     (eff l idx * ARRAY a_v l)
     (POSTv v. &UNIT_TYPE () v * (eff l (LENGTH l)) * ARRAY a_v l)
Proof
  ntac 2 gen_tac >>
  completeInduct_on `LENGTH l - idx` >>
  rpt strip_tac >>
  xcf_with_def Array_app_aux_v_def >>
  rw [] >>
  xlet `POSTv env_v. eff l idx * ARRAY a_v l * &BOOL (idx = LENGTH l) env_v`
  >- (
    xapp_spec eq_num_v_thm >>
    xsimpl >>
    fs [NUM_def, BOOL_def, INT_def]) >>
  xif
  >- (
    xret >>
    xsimpl) >>
  xlet `POSTv x_v. eff l idx * ARRAY a_v l * &(EL idx l = x_v)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `idx` >>
    rw []) >>
  xlet `POSTv u_v. eff l (idx + 1) * ARRAY a_v l`
  >- (
    first_x_assum (qspec_then `idx` mp_tac) >>
    simp [] >>
    disch_then xapp_spec >>
    xsimpl) >>
  xlet `POSTv next_idx_v. eff l (idx + 1) * ARRAY a_v l * & NUM (idx + 1) next_idx_v`
  >- (
    xapp >>
    xsimpl >>
    fs [NUM_def, INT_def] >>
    intLib.ARITH_TAC) >>
  first_x_assum xapp_spec >>
  simp []
QED

(* eff is the effect of executing the function on the first n elements of l *)
Theorem array_app_spec:
   ∀l a_v f_v eff.
   (!n.
     n < LENGTH l ⇒
     app p f_v [EL n l] (eff l n) (POSTv v. &UNIT_TYPE () v * (eff l (n+1))))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "Array.app" array_st) [f_v; a_v] (eff l 0 * ARRAY a_v l)
     (POSTv v. &UNIT_TYPE () v * (eff l (LENGTH l)) * ARRAY a_v l)
Proof
  rw [] >>
  xcf "Array.app" array_st  >>
  xlet `POSTv len_v. eff l 0 * ARRAY a_v l * &NUM (LENGTH l) len_v`
  >- (
    xapp >>
    xsimpl) >>
  xapp >>
  rw [NUM_def]
QED

Theorem array_appi_aux_spec:
   ∀l idx len_v idx_v a_v f_v eff.
   NUM (LENGTH l) len_v ∧
   NUM idx idx_v ∧
   idx ≤ LENGTH l ∧
   (!n n_v.
      n < LENGTH l ∧
      NUM n n_v ⇒
      app p f_v [n_v; EL n l] (eff l n)
                (POSTv v. &UNIT_TYPE () v * (eff l (n+1))))
   ⇒
   app (p:'ffi ffi_proj) Array_appi_aux_v [f_v; a_v; len_v; idx_v]
     (eff l idx * ARRAY a_v l)
     (POSTv v. &UNIT_TYPE () v * (eff l (LENGTH l)) * ARRAY a_v l)
Proof
  ntac 2 gen_tac >>
  completeInduct_on `LENGTH l - idx` >>
  rpt strip_tac >>
  xcf_with_def Array_appi_aux_v_def >>
  rw [] >>
  xlet `POSTv env_v. eff l idx * ARRAY a_v l * &BOOL (idx = LENGTH l) env_v`
  >- (
    xapp_spec eq_num_v_thm >>
    xsimpl >>
    fs [NUM_def, BOOL_def, INT_def]) >>
  xif
  >- (
    xret >>
    xsimpl) >>
  xlet `POSTv x_v. eff l idx * ARRAY a_v l * &(EL idx l = x_v)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `idx` >>
    rw []) >>
  xlet `POSTv u_v. eff l (idx + 1) * ARRAY a_v l`
  >- (
    first_x_assum (qspec_then `idx` mp_tac) >>
    simp [] >>
    disch_then xapp_spec >>
    xsimpl) >>
  xlet `POSTv next_idx_v. eff l (idx + 1) * ARRAY a_v l * & NUM (idx + 1) next_idx_v`
  >- (
    xapp >>
    xsimpl >>
    fs [NUM_def, INT_def] >>
    intLib.ARITH_TAC) >>
  first_x_assum xapp_spec >>
  simp []
QED

(* eff is the effect of executing the function on the first n elements of l *)
Theorem array_appi_spec:
   ∀l a_v f_v eff.
   (!n n_v.
     n < LENGTH l ∧
     NUM n n_v ⇒
     app p f_v [n_v; EL n l] (eff l n)
               (POSTv v. &UNIT_TYPE () v * (eff l (n+1))))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "Array.appi" array_st) [f_v; a_v]
     (eff l 0 * ARRAY a_v l)
     (POSTv v. &UNIT_TYPE () v * (eff l (LENGTH l)) * ARRAY a_v l)
Proof
  rw [] >>
  xcf "Array.appi" array_st  >>
  xlet `POSTv len_v. eff l 0 * ARRAY a_v l * &NUM (LENGTH l) len_v`
  >- (
    xapp >>
    xsimpl) >>
  xapp >>
  rw [NUM_def]
QED

Triviality list_rel_take_thm:
  !A xs ys n.
      LIST_REL A xs ys ==> LIST_REL A (TAKE n xs) (TAKE n ys)
Proof
  Induct_on `xs` \\ Induct_on `ys` \\ rw[LIST_REL_def, TAKE_def]
QED

Triviality drop_pre_length_thm:
  !l. l <> [] ==> (DROP (LENGTH l - 1) l) = [(EL (LENGTH l - 1) l)]
Proof
  rw[] \\ Induct_on `l` \\ rw[DROP, LENGTH, DROP_EL_CONS, DROP_LENGTH_NIL]
QED

(*
Definition ARRAY_TYPE_def:
  ARRAY_TYPE A a av = SEP_EXISTS vs. ARRAY av vs * & LIST_REL A a vs
End
*)

Theorem array_modify_aux_spec:
   !a n f fv vs av max maxv nv A.
    NUM max maxv /\ LENGTH a = max /\ NUM n nv /\ (A --> A) f fv /\ n <= max /\ LIST_REL A a vs
    ==> app (p:'ffi ffi_proj) Array_modify_aux_v [fv; av; maxv; nv]
    (ARRAY av vs) (POSTv uv. SEP_EXISTS vs1 vs2. ARRAY av (vs1 ++ vs2) * cond(EVERY2 A (TAKE n a) vs1) * cond(EVERY2 A (MAP f (DROP n a)) vs2))
Proof
  gen_tac \\ gen_tac \\ Induct_on `LENGTH a - n` \\ rpt strip_tac
    >-(xcf_with_def Array_modify_aux_v_def
    \\ rw[] \\ xlet `POSTv bool. & (BOOL (nv = maxv) bool) * ARRAY av vs`
      >- (xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def, BOOL_def])
    \\ xif
      >- (xcon \\ xsimpl \\ fs[NUM_def, INT_def, BOOL_def] \\ rw[DROP_LENGTH_NIL])
    \\ `LENGTH a = n` by DECIDE_TAC \\ fs[NUM_def, INT_def] \\ rfs[])
  \\ xcf_with_def Array_modify_aux_v_def
  \\ xlet `POSTv bool. & (BOOL (nv = maxv) bool) * ARRAY av vs`
    >- (xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def, BOOL_def])
  \\ xif
    >- (xcon \\ xsimpl \\ qexists_tac `vs` \\ fs[NUM_def, INT_def, BOOL_def] \\ rw[DROP_LENGTH_NIL])
  \\ xlet `POSTv vsub. &(vsub = EL n vs)* ARRAY av vs`
    >-(xapp \\ fs[NUM_def, INT_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[])
  \\ xlet `POSTv res. & (A (f (EL n a)) res) * ARRAY av vs`
      >-(xapp \\ xsimpl \\ instantiate \\ qexists_tac `(EL n a)` \\ fs[LIST_REL_EL_EQN])
  \\ xlet `POSTv u. ARRAY av (LUPDATE res n vs)`
    >-(xapp \\ xsimpl \\ instantiate \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def] \\ rfs[])
  \\ xlet `POSTv n1. & NUM (n + 1) n1 * ARRAY av (LUPDATE res n vs)`
    >-(xapp \\ xsimpl \\ qexists_tac `&n` \\ fs[NUM_def, INT_def, integerTheory.INT_ADD])
  \\ first_x_assum (qspecl_then [`LUPDATE (f (EL n a)) n a`, `n + 1`] mp_tac) \\ rw[]
  \\ xapp \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def] \\ rw[EVERY2_LUPDATE_same]
  \\ qexists_tac `TAKE n x`
  \\ simp[RIGHT_EXISTS_AND_THM]
  \\ conj_tac
    >-(`(TAKE n (TAKE (n + 1) (LUPDATE (f (EL n a)) n a))) = (TAKE n a)` by fs[lupdate_breakdown_thm, TAKE_APPEND1, TAKE_TAKE]
        \\ metis_tac[list_rel_take_thm])
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ qexists_tac`[EL n x] ++ x'`
  \\ reverse conj_tac
  >- (
    imp_res_tac LIST_REL_LENGTH
    \\ rfs[LENGTH_LUPDATE,LENGTH_TAKE]
    \\ fs[LIST_EQ_REWRITE]
    \\ qx_gen_tac`z`
    \\ Cases_on`z<n` \\ simp[EL_APPEND1,EL_APPEND2,EL_TAKE]
    \\ rw[] \\ `z = n` by decide_tac \\ simp[] )
  \\ rfs[LIST_REL_EL_EQN,EL_MAP,EL_DROP,EL_LUPDATE,EL_TAKE]
  \\ Cases \\ fs[]
  >- ( rpt(first_x_assum(qspec_then`n`mp_tac) \\ simp[]) )
  \\ qmatch_goalsub_rename_tac`A _ (EL z l2)`
  \\ strip_tac
  \\ first_x_assum(qspec_then`z`mp_tac)
  \\ simp[]
  \\ fs[ADD1]
  \\ qpat_x_assum`_ = LENGTH x`(SUBST_ALL_TAC o SYM)
  \\ fs[]
QED


Theorem array_modify_spec:
   !f fv a vs av A A'.
    (A --> A) f fv  /\ LIST_REL A a vs
    ==> app (p:'ffi ffi_proj) ^(fetch_v "Array.modify" array_st) [fv; av]
    (ARRAY av vs) (POSTv uv. SEP_EXISTS vs1. ARRAY av vs1 * cond(EVERY2 A (MAP f a) vs1))
Proof
    rpt strip_tac
    \\ xcf "Array.modify" array_st
    \\ xlet `POSTv len. & NUM (LENGTH a) len * ARRAY av vs`
      >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[INT_def, NUM_def])
    \\ xapp \\ xsimpl \\ instantiate
QED

Theorem array_modifyi_aux_spec:
   !a n f fv vs av max maxv nv A.
    NUM max maxv /\ max = LENGTH a /\ NUM n nv /\ (NUM --> A --> A) f fv /\ n <= max /\
    LIST_REL A a vs
    ==> app (p:'ffi ffi_proj) Array_modifyi_aux_v [fv; av; maxv; nv]
    (ARRAY av vs) (POSTv uv. SEP_EXISTS vs1 vs2. ARRAY av (vs1 ++ vs2) * cond(EVERY2 A (TAKE n a) vs1) *
      cond(EVERY2 A (MAPi (\i. f (n + i)) (DROP n a)) vs2))
Proof
    gen_tac \\ gen_tac \\ Induct_on `LENGTH a - n` \\ rpt strip_tac
      >-(xcf_with_def Array_modifyi_aux_v_def
        \\ xlet `POSTv bool. & BOOL (nv=maxv) bool * ARRAY av vs`
          >-(xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[INT_def, NUM_def, BOOL_def])
        \\ xif
          >-(xcon \\ xsimpl \\ fs[NUM_def, INT_def] \\ rw[DROP_LENGTH_NIL])
        \\ `LENGTH a = n` by DECIDE_TAC \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ xcf_with_def Array_modifyi_aux_v_def
    \\ xlet `POSTv bool. & BOOL (nv=maxv) bool * ARRAY av vs`
      >-(xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[INT_def, NUM_def, BOOL_def])
    \\ xif
      >-(xcon \\ xsimpl \\ qexists_tac `vs` \\ fs[NUM_def, INT_def] \\ rw[DROP_LENGTH_NIL])
    \\ xlet `POSTv val. &(val = EL n vs) * ARRAY av vs`
      >-(xapp \\ fs[NUM_def, INT_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs[])
    \\ xlet `POSTv res. & A (f n (EL n a)) res * ARRAY av vs`
      >-(xapp \\ xsimpl \\ instantiate \\ qexists_tac `EL n a` \\ fs[LIST_REL_EL_EQN])
    \\ xlet `POSTv u. ARRAY av (LUPDATE res n vs)`
      >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ xlet `POSTv n1. & NUM (n + 1) n1 * ARRAY av (LUPDATE res n vs)`
      >-(xapp \\ xsimpl \\ qexists_tac `&n` \\ fs[NUM_def, integerTheory.INT_ADD])
    \\ first_x_assum(qspecl_then [`LUPDATE (f n (EL n a)) n a`, `n + 1`] mp_tac) \\ rw[]
    \\ xapp \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def] \\ rw[EVERY2_LUPDATE_same]
    \\ qexists_tac `TAKE n x`
    \\ simp[RIGHT_EXISTS_AND_THM]
    \\ conj_tac
      >-(`(TAKE n (TAKE (n + 1) (LUPDATE (f n (EL n a)) n a))) = (TAKE n a)` by fs[lupdate_breakdown_thm, TAKE_APPEND1, TAKE_TAKE]
          \\ metis_tac[list_rel_take_thm])
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ qexists_tac `[EL n x] ++ x'`
    \\ reverse conj_tac
    >-(
      imp_res_tac LIST_REL_LENGTH
      \\ rfs[LENGTH_LUPDATE, LENGTH_TAKE]
      \\ fs [LIST_EQ_REWRITE]
      \\ qx_gen_tac`z`
      \\ Cases_on`z<n` \\ simp[EL_APPEND1, EL_APPEND2, EL_TAKE]
      \\ rw[] \\ `z = n` by DECIDE_TAC \\ simp[])
    \\ rfs[LIST_REL_EL_EQN, EL_MAP, EL_DROP, EL_LUPDATE, EL_TAKE]
    \\ Cases \\ fs[]
    >- ( rpt(first_x_assum(qspec_then`n`mp_tac) \\ simp[]))
    \\ qmatch_goalsub_rename_tac`A _ (EL z l2)`
    \\ strip_tac
    \\ first_x_assum(qspec_then`z`mp_tac)
    \\ simp[] \\ fs[ADD1] \\ qpat_x_assum`_ = LENGTH x`(SUBST_ALL_TAC o SYM)
    \\ fs[]
QED

Theorem array_modifyi_spec:
   !f fv a vs av A A'.
    (NUM --> A --> A) f fv  /\ LIST_REL A a vs
    ==> app (p:'ffi ffi_proj) ^(fetch_v "Array.modifyi" array_st) [fv; av]
    (ARRAY av vs) (POSTv uv. SEP_EXISTS vs1. ARRAY av vs1 * cond(EVERY2 A (MAPi f a) vs1))
Proof
    rpt strip_tac
    \\ xcf "Array.modifyi" array_st
    \\ xlet `POSTv len. & NUM (LENGTH a) len * ARRAY av vs`
      >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[INT_def, NUM_def])
    \\ xapp \\ xsimpl \\ metis_tac [BETA_THM]
QED


(*
Theorem array_foldli_aux_spec:
   !a n f fv init initv vs av max maxv nv (A:'a->v->bool) (B:'b->v->bool).
    (NUM-->B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv /\ NUM max maxv /\ NUM n nv
    /\ max = LENGTH a /\ n <= max
    ==> app (p:'ffi ffi_proj) Array_foldli_aux_v [fv; initv; av; maxv; nv]
    (ARRAY av vs) (POSTv val. & A (mllist$foldli (\i. f (i + n)) init (DROP n a)) val * ARRAY av vs)
Proof
    gen_tac \\ gen_tac \\ Induct_on `LENGTH a - n`
      >-(xcf_with_def "foldli_aux" Array_foldli_aux_v_def
      \\ xlet `POSTv bool. & BOOL (nv = maxv) bool * ARRAY av vs`
        >-(xapp \\ xsimpl \\ instantiate\\ fs[BOOL_def, INT_def, NUM_def])
      \\ xif
        >-(xvar \\ xsimpl \\ fs[NUM_def, INT_def, DROP_LENGTH_NIL, mllistTheory.foldli_def, mllistTheory.foldli_aux_def])
     \\ fs[NUM_def, INT_def, BOOL_def] \\ rfs[])
    \\ xcf_with_def "foldli_aux" Array_foldli_aux_v_def
    \\ xlet `POSTv bool. & BOOL (nv = maxv) bool * ARRAY av vs`
      >-(xapp \\ xsimpl \\ instantiate\\ fs[BOOL_def, INT_def, NUM_def])
    \\ xif
      >-(xvar \\ xsimpl \\ fs[NUM_def, INT_def, DROP_LENGTH_NIL, mllistTheory.foldli_def, mllistTheory.foldli_aux_def])
    \\ xlet `POSTv n1. & NUM (n + 1) n1 * ARRAY av vs`
      >-(xapp \\ xsimpl \\ qexists_tac `&n` \\ fs[NUM_def, integerTheory.INT_ADD])
    \\ xlet `POSTv val. & (val = EL n vs) * ARRAY av vs`
      >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ xlet `POSTv res. & A (f n (EL n a) init) res * ARRAY av vs`
      >-(xapp \\ xsimpl \\ instantiate \\ qexists_tac `EL n a` \\ fs[LIST_REL_EL_EQN])
    \\ first_x_assum(qspecl_then [`a`, `n + 1`] mp_tac) \\ rw[]
    \\ xapp \\ xsimpl \\ instantiate \\ rw[mllistTheory.foldli_def, mllistTheory.foldli_aux_def, DROP_EL_CONS]
    \\ ... (*How to deal with foldli_aux as it has nothing proved about it *)
QED

Theorem array_foldli_spec:
     !f fv init initv a vs av (A:'a->v->bool) (B:'b->v->bool).
      (NUM-->B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv
    ==> app (p:'ffi ffi_proj) ^(fetch_v "foldli" foldli_st) [fv; initv; av]
    (ARRAY av vs) (POSTv val. &A (mllist$foldli f init a) val * ARRAY av vs)
Proof
  xcf "foldli" foldli_st
  \\ xlet `POSTv len. & NUM (LENGTH a) len * ARRAY av vs`
    >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[])
  \\ xapp \\ xsimpl \\ instantiate \\ srw_tac[ETA_ss][]
QED

Theorem array_foldl_aux_spec:
   !f fv init initv a vs av max maxv n nv (A:'a->v->bool) (B:'b->v->bool).
    (B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv /\ NUM max maxv /\ NUM n nv
    /\ max = LENGTH a /\ n <= max
    ==> app (p:'ffi ffi_proj) Array_foldl_aux_v [fv; initv; av; maxv; nv]
    (ARRAY av vs) (POSTv val. & A (FOLDL (\i. f (i + n)) init (DROP n a)) val * ARRAY av vs)
Proof
    xcf_with_def "foldl_aux" Array_foldl_aux_v_def
    \\ xlet `POSTv bool. & BOOL (nv = maxv) bool * ARRAY av vs`
      >-(xapp \\ xsimpl \\ instantiate\\ fs[BOOL_def, INT_def, NUM_def])
    \\ xif
      >-(xvar \\ xsimpl \\ fs[NUM_def, INT_def, DROP_LENGTH_NIL, FOLDL])
    \\ xlet `POSTv n1. & NUM (n + 1) n1 * ARRAY av vs`
      >-(xapp \\ xsimpl \\ qexists_tac `&n` \\ fs[NUM_def, integerTheory.INT_ADD])
    \\ xlet `POSTv res. & A (f init b) res * ARRAY av vs`
      >-(... (*xapp*))
    \\ xlet `POSTv val. & (val = EL n vs) * ARRAY av vs`
      >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ Induct_on `LENGTH a - n`
      >-(rw[] \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ rw[] \\ ... (*xapp*)
QED

Theorem array_foldl_spec:
     !f fv init initv a vs av (A:'a->v->bool) (B:'b->v->bool).
      (B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv
    ==> app (p:'ffi ffi_proj) ^(fetch_v "foldl" foldl_st) [fv; initv; av]
    (ARRAY av vs) (POSTv val. &A (FOLDL f init a) val * ARRAY av vs)
Proof
  xcf "foldl" foldl_st
  \\ xlet `POSTv len. & NUM (LENGTH a) len * ARRAY av vs`
    >-(xapp \\ xsimpl \\ imp_res_tac LIST_REL_LENGTH \\ fs[])
  \\ xapp \\ xsimpl \\ instantiate
QED


Theorem array_foldri_aux_spec:
     !n f fv init initv a vs av nv (A:'a->v->bool) (B:'b->v->bool).
      (NUM-->B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv /\
      NUM n nv /\ n <= LENGTH a
      ==> app (p:'ffi ffi_proj) Array_foldri_aux_v [fv; initv; av; nv]
      (ARRAY av vs) (POSTv val. & A (FOLDRi f init (TAKE n a)) val * ARRAY av vs)
Proof
    gen_tac \\ Induct_on `n`
      >-(xcf_with_def "foldri_aux" Array_foldri_aux_v_def
      \\ xlet `POSTv bool. SEP_EXISTS ov. & BOOL (nv = ov) bool * ARRAY av vs * & NUM 0 ov`
        >-(xapp \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def])
      \\ xif
        >-(xvar \\ xsimpl)
      \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ xcf_with_def "foldri_aux" Array_foldri_aux_v_def
    \\ xlet `POSTv bool. SEP_EXISTS ov. & BOOL (nv = ov) bool * ARRAY av vs * & NUM 0 ov`
      >-(xapp \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def])
    \\ xif
      >-(fs[NUM_def, INT_def, numTheory.NOT_SUC])
    \\ xlet `POSTv n1. & NUM (SUC n - 1) n1 * ARRAY av vs`
        >-(xapp \\ xsimpl \\ qexists_tac `&(SUC n)` \\ fs[NUM_def, INT_def, ADD1, integerTheory.INT_SUB])
    \\ xlet `POSTv n2. & NUM (SUC n - 1) n2 * ARRAY av vs`
        >-(xapp \\ xsimpl \\ qexists_tac `&(SUC n)` \\ fs[NUM_def, INT_def, ADD1, integerTheory.INT_SUB])
    \\ xlet `POSTv val. &(val = EL n vs) * ARRAY av vs`
        >-(xapp \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def])
    \\ xlet `POSTv n3. & NUM (SUC n - 1) n3 * ARRAY av vs`
        >-(xapp \\ xsimpl \\ qexists_tac `&(SUC n)` \\ fs[NUM_def, INT_def, ADD1, integerTheory.INT_SUB])
    \\ xlet `POSTv res. & (A (f n (EL n a) init) res) * ARRAY av vs`
        >-(xapp \\ xsimpl \\ instantiate \\ qexists_tac`EL n a` \\ fs[LIST_REL_EL_EQN])
    \\ xapp \\ xsimpl \\ instantiate \\ fs[TAKE_EL_SNOC, ADD1] (*need something similar to FOLDR SNOC*)
    \\ ...
QED

Theorem array_foldri_spec:
   !f fv init initv a av vs (A:'a->v->bool) (B:'b->v->bool).
    (NUM-->B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv
    ==> app (p:'ffi ffi_proj) ^(fetch_v "foldri" foldri_st) [fv; initv; av]
      (ARRAY av vs) (POSTv val. & A (FOLDRi f init a) val * ARRAY av vs)
Proof
      xcf "foldri" foldri_st
      \\ xlet `POSTv len. & NUM (LENGTH vs) len * ARRAY av vs`
        >-(xapp \\ xsimpl)
      \\ xapp \\ xsimpl \\ instantiate \\ imp_res_tac LIST_REL_LENGTH
      \\ fs[] \\ metis_tac[TAKE_LENGTH_ID]
QED

*)

Theorem array_foldr_aux_spec:
     !n f fv init initv a vs av nv (A:'a->v->bool) (B:'b->v->bool).
      (B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv /\
      NUM n nv /\ n <= LENGTH a
      ==> app (p:'ffi ffi_proj) Array_foldr_aux_v [fv; initv; av; nv]
      (ARRAY av vs) (POSTv val. & A (FOLDR f init (TAKE n a)) val * ARRAY av vs)
Proof
    gen_tac \\ Induct_on `n` \\ rpt strip_tac
      >-(xcf_with_def Array_foldr_aux_v_def
      \\ xlet `POSTv bool. SEP_EXISTS ov. & BOOL (nv = ov) bool * ARRAY av vs * & NUM 0 ov`
        >-(xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def])
      \\ xif
        >-(xvar \\ xsimpl)
      \\ fs[NUM_def, INT_def] \\ rfs[])
    \\ xcf_with_def Array_foldr_aux_v_def
    \\ xlet `POSTv bool. SEP_EXISTS ov. & BOOL (nv = ov) bool * ARRAY av vs * & NUM 0 ov`
      >-(xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate \\ fs[NUM_def, INT_def])
    \\ xif
      >-(fs[NUM_def, INT_def, numTheory.NOT_SUC])
    \\ xlet `POSTv n1. & NUM (SUC n - 1) n1 * ARRAY av vs`
        >-(xapp \\ xsimpl \\ qexists_tac `&(SUC n)` \\ fs[NUM_def, INT_def, ADD1, integerTheory.INT_SUB])
    \\ xlet `POSTv n2. & NUM (SUC n - 1) n2 * ARRAY av vs`
        >-(xapp \\ xsimpl \\ qexists_tac `&(SUC n)` \\ fs[NUM_def, INT_def, ADD1, integerTheory.INT_SUB])
    \\ xlet `POSTv val. &(val = EL n vs) * ARRAY av vs`
        >-(xapp \\ imp_res_tac LIST_REL_LENGTH \\ fs[NUM_def, INT_def])
    \\ xlet `POSTv res. & (A (f (EL n a) init) res) * ARRAY av vs`
        >-(xapp \\ xsimpl \\ instantiate \\ qexists_tac`EL n a` \\ fs[LIST_REL_EL_EQN])
    \\ xapp \\ xsimpl \\ instantiate \\ fs[TAKE_EL_SNOC, ADD1, FOLDR_SNOC]
QED

Theorem array_foldr_spec:
   !f fv init initv a av vs (A:'a->v->bool) (B:'b->v->bool).
    (B-->A-->A) f fv /\ LIST_REL B a vs /\ A init initv
    ==> app (p:'ffi ffi_proj) ^(fetch_v "Array.foldr" array_st) [fv; initv; av]
      (ARRAY av vs) (POSTv val. & A (FOLDR f init a) val * ARRAY av vs)
Proof
      rpt strip_tac
      \\ xcf "Array.foldr" array_st
      \\ xlet `POSTv len. & NUM (LENGTH vs) len * ARRAY av vs`
        >-(xapp \\ xsimpl)
      \\ xapp \\ xsimpl \\ instantiate \\ imp_res_tac LIST_REL_LENGTH
      \\ fs[] \\metis_tac[TAKE_LENGTH_ID]
QED

Triviality IMP_app:
  f = Closure v1 env (Fun v2 x) ∧
  app p (Closure (v1 with v := nsBind env x1 v1.v) v2 x) (x2::xs) H Q ⇒
  app p f (x1::x2::xs) H Q
Proof
  simp [app_def]
  \\ rw [app_basic_def]
  \\ fs [semanticPrimitivesTheory.do_opapp_def,cfDivTheory.POSTv_eq,PULL_EXISTS]
  \\ ‘SPLIT3 (st2heap p st) (h_i,h_k,{})’ by fs [SPLIT_def,SPLIT3_def]
  \\ first_x_assum $ irule_at Any
  \\ rw [evaluate_to_heap_def,evaluate_ck_def,evaluateTheory.evaluate_def,PULL_EXISTS]
  \\ fs [cfStoreTheory.st2heap_def,SEP_EXISTS_THM,cond_STAR]
  \\ first_x_assum $ irule_at Any \\ fs []
QED

val eval_nsLookup_tac =
  rewrite_tac [ml_progTheory.nsLookup_merge_env]
  \\ CONV_TAC(DEPTH_CONV ml_progLib.nsLookup_conv)

Theorem array_lookup_spec:
  NUM n nv ⇒
  app (p : 'ffi ffi_proj)
    Array_lookup_v
    [arrv; defaultv; nv]
    (ARRAY arrv arrlsv)
    (POSTv v.
      ARRAY arrv arrlsv *
      &(v = any_el n arrlsv defaultv))
Proof
  (* this can unfortunately not be proved using CF since CF rules for
     Asub don't allow reasoning about out of bounds indexing *)
  rw [] \\ rpt (irule_at Any IMP_app) \\ fs []
  \\ fs [app_def,app_basic_def,cfDivTheory.POSTv_eq,PULL_EXISTS,SEP_EXISTS_THM]
  \\ fs [Array_lookup_v_def]
  \\ rw [semanticPrimitivesTheory.do_opapp_def,cond_STAR]
  \\ first_assum $ irule_at Any \\ fs []
  \\ ‘SPLIT3 (st2heap p st) (h_i,h_k,{})’ by fs [SPLIT_def,SPLIT3_def]
  \\ first_assum $ irule_at Any \\ fs []
  \\ rw [evaluate_to_heap_def,evaluate_ck_def]
  \\ qexists_tac ‘100’
  \\ fs [evaluateTheory.evaluate_def]
  \\ eval_nsLookup_tac \\ fs [evaluateTheory.dec_clock_def]
  \\ rw [semanticPrimitivesTheory.do_opapp_def,Array_sub_v_def]
  \\ fs [evaluateTheory.evaluate_def]
  \\ rw [semanticPrimitivesTheory.do_app_def]
  \\ gvs [ARRAY_def,SEP_EXISTS_THM,cond_STAR,NUM_def,INT_def]
  \\ gvs [cell_def,one_def,EVAL “pat_bindings Pany []”]
  \\ ‘store_lookup loc st.refs = SOME (Varray arrlsv)’ by
   (fs [semanticPrimitivesTheory.store_lookup_def]
    \\ ‘Mem loc (Varray arrlsv) IN st2heap p st’ by
         (fs [SPLIT_def,EXTENSION] \\ metis_tac [])
    \\ fs [cfStoreTheory.st2heap_def]
    \\ imp_res_tac cfStoreTheory.store2heap_IN_LENGTH \\ fs []
    \\ imp_res_tac cfStoreTheory.store2heap_IN_EL \\ fs []
    \\ fs [cfStoreTheory.Mem_NOT_IN_ffi2heap])
  \\ fs [GREATER_EQ]
  \\ Cases_on ‘n < LENGTH arrlsv’ \\ fs [any_el_ALT]
  >- fs [cfStoreTheory.st2heap_def]
  \\ fs [semanticPrimitivesTheory.can_pmatch_all_def]
  \\ fs [semanticPrimitivesTheory.pmatch_def]
  \\ eval_nsLookup_tac \\ fs [evaluateTheory.dec_clock_def]
  \\ fs [EVAL “nsLookup_Short nsEmpty n”]
  \\ eval_nsLookup_tac \\ fs [evaluateTheory.dec_clock_def]
  \\ fs [cfStoreTheory.st2heap_def]
QED

Theorem array_update_any_spec[local]:
   !a av i iv v.
     INT i iv ==>
     app (p:'ffi ffi_proj) Array_update_v
       [av; iv; v]
       (ARRAY av a)
       (POSTve (λuv. cond (UNIT_TYPE () uv ∧ 0i ≤ i ∧ Num i < LENGTH a) *
                     ARRAY av (LUPDATE v (Num i) a))
               (λev. cond (ev = sub_exn_v ∧ (0i ≤ i ⇒ LENGTH a ≤ Num i)) * ARRAY av a))
Proof
  rw []
  \\ Cases_on ‘0 ≤ i ⇒ LENGTH a ≤ Num i’ \\ fs []
  (* this can unfortunately not be proved using CF since CF rules for
     arrays don't allow reasoning about out of bounds indexing *)
  >-
   (rw [] \\ rpt (irule_at Any IMP_app) \\ fs []
    \\ fs [app_def,app_basic_def,PULL_EXISTS,SEP_EXISTS_THM]
    \\ rw [semanticPrimitivesTheory.do_opapp_def,cond_STAR,update_resize_def]
    \\ fs [Array_update_v_def] \\ rw []
    \\ qexists_tac ‘Exn sub_exn_v’
    \\ ‘SPLIT3 (st2heap p st) (h_i,h_k,{})’ by fs [SPLIT_def,SPLIT3_def]
    \\ first_assum $ irule_at Any \\ fs []
    \\ rw [evaluate_to_heap_def,evaluate_ck_def,SEP_CLAUSES]
    \\ fs [evaluateTheory.evaluate_def,semanticPrimitivesTheory.do_app_def]
    \\ gvs [ARRAY_def,SEP_CLAUSES,cond_STAR,SEP_EXISTS_THM,cell_def,one_def]
    \\ ‘store_lookup loc st.refs = SOME (Varray a)’ by
      (fs [semanticPrimitivesTheory.store_lookup_def]
       \\ ‘Mem loc (Varray a) IN st2heap p st’ by
         (fs [SPLIT_def,EXTENSION] \\ metis_tac [])
       \\ fs [cfStoreTheory.st2heap_def]
       \\ imp_res_tac cfStoreTheory.store2heap_IN_LENGTH \\ fs []
       \\ imp_res_tac cfStoreTheory.store2heap_IN_EL \\ fs []
       \\ fs [cfStoreTheory.Mem_NOT_IN_ffi2heap])
    \\ gvs [INT_def,AllCaseEqs(),PULL_EXISTS]
    \\ qexists_tac ‘0’ \\ qexists_tac ‘st.refs’ \\ fs []
    \\ qexists_tac ‘st.ffi’ \\ fs [cfStoreTheory.st2heap_def]
    \\ Cases_on ‘i’ \\ fs [])
  \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ gvs []
  \\ fs [GSYM NUM_def, GSYM NOT_LESS]
  \\ fs [SEP_CLAUSES]
  \\ rename [‘NUM n nv’]
  \\ mp_tac (array_update_spec |> SPEC_ALL)
  \\ fs []
  \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ (f x ⇒ f y)”)
  \\ fs [FUN_EQ_THM]
  \\ Cases \\ fs [cond_def,SEP_F_def]
QED

Theorem array_updateResize_spec:
  NUM n nv ⇒
  app (p : 'ffi ffi_proj)
    Array_updateResize_v
    [arrv; defaultv; nv; xv]
    (ARRAY arrv arrlsv)
    (POSTv v. ARRAY v (update_resize arrlsv defaultv xv n))
Proof
  rw []
  \\ xcf_with_def Array_updateResize_v_def
  \\ Cases_on ‘n < LENGTH arrlsv’
  >-
   (xhandle ‘(POSTv v. ARRAY v (update_resize arrlsv defaultv xv n))’
    \\ xsimpl
    \\ xlet ‘(POSTv v. ARRAY arrv (LUPDATE xv n arrlsv))’
    >-
     (xapp_spec array_update_spec
      \\ rpt (first_x_assum $ irule_at Any)
      \\ xsimpl)
    >- (xvar \\ xsimpl \\ fs [update_resize_def]))
  \\ xhandle ‘(POSTe ev. cond (ev = sub_exn_v) * ARRAY arrv arrlsv)’
  >-
   (xlet ‘(POSTe ev. cond (ev = sub_exn_v) * ARRAY arrv arrlsv)’
    \\ xsimpl
    \\ xapp_spec array_update_any_spec
    \\ gvs [NUM_def]
    \\ first_x_assum $ irule_at Any
    \\ xsimpl)
  \\ xcases
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet ‘POSTv av. ARRAY av (REPLICATE (2*n+1) defaultv) * ARRAY arrv arrlsv’
  >-
   (xapp_spec array_alloc_spec
    \\ first_x_assum $ irule_at Any
    \\ xsimpl)
  \\ fs [update_resize_def]
  \\ qabbrev_tac ‘k = (2 * n + 1 − LENGTH arrlsv)’
  \\ ‘∃ts. REPLICATE (2 * n + 1) defaultv = ts ++ REPLICATE k defaultv ∧
           LENGTH ts = LENGTH arrlsv’ by
   (qexists_tac ‘REPLICATE (LENGTH arrlsv) defaultv’
    \\ fs [rich_listTheory.REPLICATE_APPEND,Abbr‘k’])
  \\ fs []
  \\ xlet ‘POSTv v. ARRAY av (arrlsv ++ REPLICATE k defaultv)’
  >- (xapp_spec array_copy_spec \\ fs [PULL_EXISTS] \\ xsimpl)
  \\ xlet ‘(POSTv v. ARRAY av (LUPDATE xv n (arrlsv ++ REPLICATE k defaultv)))’
  >-
   (xapp_spec array_update_spec
    \\ first_x_assum $ irule_at Any
    \\ xsimpl \\ unabbrev_all_tac \\ fs [])
  \\ xvar \\ fs [] \\ xsimpl
QED

Theorem array_exists_aux_spec:
  ∀n nv.
  NUM max maxv ∧
  NUM n nv ∧
  LIST_REL R ls arr ∧
  (R --> BOOL) f fv ∧
  n ≤ max ∧
  max = LENGTH ls
  ⇒
  app (p:'ffi ffi_proj) Array_exists_aux_v [fv; arrv; maxv; nv]
    (ARRAY arrv arr)
    (POSTv v. ARRAY arrv arr * &BOOL (EXISTS f (DROP n ls)) v)
Proof
  Induct_on`max - n`>>rw[]
  \\ xcf_with_def Array_exists_aux_v_def
  >- (
    xlet_auto >> xsimpl>>
    xif >> instantiate>>
    xcon>>xsimpl>>
    DEP_REWRITE_TAC[DROP_LENGTH_NIL_rwt]>>
    simp[]>>EVAL_TAC)>>
  xlet_auto >- xsimpl >>
  xif >> instantiate >>
  gvs[LIST_REL_EL_EQN]>>
  xlet_auto >- xsimpl>>
  rename1`EL n arr`>>
  `DROP n ls = EL n ls :: DROP (n+1) ls` by
    (irule DROP_EL_CONS>>
    gvs[])>>
  first_x_assum (qspec_then`n` assume_tac)>>gvs[]>>
  xlet_auto >-xsimpl>>
  xif>- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xapp>>
  xsimpl
QED

Theorem array_exists_spec:
  LIST_REL R ls arr ∧
  (R --> BOOL) f fv
  ⇒
  app (p:'ffi ffi_proj) Array_exists_v [fv; arrv]
    (ARRAY arrv arr)
    (POSTv v. ARRAY arrv arr * &BOOL (EXISTS f ls) v)
Proof
  rw[]>>xcf_with_def Array_exists_v_def>>
  xlet_auto >- xsimpl>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp>> xsimpl>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem array_all_aux_spec:
  ∀n nv.
  NUM max maxv ∧
  NUM n nv ∧
  LIST_REL R ls arr ∧
  (R --> BOOL) f fv ∧
  n ≤ max ∧
  max = LENGTH ls
  ⇒
  app (p:'ffi ffi_proj) Array_all_aux_v [fv; arrv; maxv; nv]
    (ARRAY arrv arr)
    (POSTv v. ARRAY arrv arr * &BOOL (EVERY f (DROP n ls)) v)
Proof
  Induct_on`max - n`>>rw[]
  \\ xcf_with_def Array_all_aux_v_def
  >- (
    xlet_auto >> xsimpl>>
    xif >> instantiate>>
    xcon>>xsimpl>>
    DEP_REWRITE_TAC[DROP_LENGTH_NIL_rwt]>>
    simp[]>>EVAL_TAC)>>
  xlet_auto >- xsimpl >>
  xif >> instantiate >>
  gvs[LIST_REL_EL_EQN]>>
  xlet_auto >- xsimpl>>
  rename1`EL n arr`>>
  `DROP n ls = EL n ls :: DROP (n+1) ls` by
    (irule DROP_EL_CONS>>
    gvs[])>>
  first_x_assum (qspec_then`n` assume_tac)>>gvs[]>>
  xlet_auto >-xsimpl>>
  xif>- (
    xlet_auto >- xsimpl>>
    xapp>>
    xsimpl)>>
  xcon>>xsimpl
QED

Theorem array_all_spec:
  LIST_REL R ls arr ∧
  (R --> BOOL) f fv
  ⇒
  app (p:'ffi ffi_proj) Array_all_v [fv; arrv]
    (ARRAY arrv arr)
    (POSTv v. ARRAY arrv arr * &BOOL (EVERY f ls) v)
Proof
  rw[]>>xcf_with_def Array_all_v_def>>
  xlet_auto >- xsimpl>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp>> xsimpl>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

val _ = export_theory();
