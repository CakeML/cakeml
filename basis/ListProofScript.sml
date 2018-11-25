(*
  Proofs about the module about the list tyoe.
*)
open preamble ml_translatorTheory ml_translatorLib cfLib ListProgTheory

val _ = new_theory "ListProof";

val _ = translation_extends "ListProg";

val st = get_ml_prog_state();

val app_spec = Q.prove(
  `∀l start lv A.
   LIST_TYPE A l lv /\
   (!n xv. n < LENGTH l ∧ A (EL n l) xv ==>
     app p fv [xv] (eff (start+n)) (POSTv v. &UNIT_TYPE () v * (eff (start+n+1))))
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "List.app" st) [fv; lv] (eff start)
     (POSTv v. &UNIT_TYPE () v * (eff (start + (LENGTH l))))`,
  Induct \\ rw[LIST_TYPE_def]
  >- ( xcf "List.app" st \\ xmatch \\ xcon \\ xsimpl )
  \\ xcf "List.app" st
  \\ xmatch
  \\ xlet`POSTv v. &UNIT_TYPE () v * eff (start+1)`
  >- (
    xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"]))
    \\ qexists_tac`0` \\ xsimpl )
  \\ first_x_assum drule
  \\ disch_then(qspec_then`start+1`mp_tac)
  \\ simp[ADD1]
  \\ impl_tac
  >- (
    rw[]
    \\ first_x_assum(qspec_then`n+1`mp_tac)
    \\ simp[EL_CONS,PRE_SUB1] )
  \\ strip_tac \\ xapp)
|> CONV_RULE SWAP_FORALL_CONV
|> Q.SPEC`0` |> SIMP_RULE(srw_ss())[]
|> Q.GENL[`eff`,`fv`]
|> curry save_thm "app_spec";

(* TODO: using p:'b ffi_proj makes xapp fail in hard to trace ways
      - ultimately it's because app_of_Arrow_rule is not robust when ffi_ty is either 'a or 'b
*)
val tabulate_aux_inv_spec = Q.store_thm("tabulate_aux_inv_spec",
  `∀f fv A heap_inv n m nv mv acc accv ls.
    NUM n nv /\ NUM m mv /\ LIST_TYPE A acc accv /\
    ls = REVERSE acc ++ GENLIST (f o FUNPOW SUC n) (m - n) /\
    (!i iv. NUM i iv /\ n <= i /\ i < m ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "List.tabulate_aux" st) [nv;mv;fv;accv] heap_inv
      (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  ntac 6 gen_tac
  \\ Induct_on`m-n`
  >- (
    rw[]
    \\ xcf "List.tabulate_aux" st
    \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
      >-(xopb \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
    \\ xif \\ asm_exists_tac \\ simp[]
    \\ xapp
    \\ instantiate \\ xsimpl
    \\ `m - n = 0` by simp[] \\ simp[])
  \\ rw[]
  \\ xcf "List.tabulate_aux" st
  \\ xlet `POSTv boolv. &BOOL (n >= m) boolv * heap_inv`
    >-(xopb \\ xsimpl \\ fs[NUM_def, INT_def] \\ intLib.COOPER_TAC)
  \\ xif \\ asm_exists_tac \\ simp[]
  \\ Cases_on`m` \\ fs[]
  \\ rename1`SUC v = SUC m - n`
  \\ `v = m - n` by decide_tac
  \\ qpat_x_assum`SUC v = _`(assume_tac o SYM)
  \\ rw[] \\ fs[GENLIST_CONS,FUNPOW_SUC_PLUS]
  \\ xlet `POSTv v. &(A (f n) v) * heap_inv`
  >- ( xapp \\ xsimpl )
  \\ xlet `POSTv nv. &NUM (n+1) nv * heap_inv`
  >-( xopn \\  xsimpl \\ fs[NUM_def,INT_def] \\ intLib.COOPER_TAC)
  \\ xlet `POSTv av. &LIST_TYPE A (f n::acc) av * heap_inv`
  >-( xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp
  \\ xsimpl
  \\ map_every qexists_tac[`n+1`,`SUC m`]
  \\ instantiate
  \\ simp[o_DEF,ADD1]
  \\ once_rewrite_tac[CONS_APPEND]
  \\ simp[]);

val tabulate_inv_spec = Q.store_thm("tabulate_inv_spec",
  `!f fv A heap_inv n nv ls.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "List.tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
  xcf "List.tabulate" st \\
  xlet`POSTv v. &LIST_TYPE A [] v * heap_inv`
  >- (xcon \\ xsimpl \\ fs[LIST_TYPE_def] )
  \\ xapp_spec tabulate_aux_inv_spec
  \\ xsimpl
  \\ instantiate
  \\ simp[FUNPOW_SUC_PLUS,o_DEF,ETA_AX]);

val _ = export_theory();
