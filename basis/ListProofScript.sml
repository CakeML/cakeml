(*
  Proofs about the module about the list type.
*)
Theory ListProof
Ancestors
  ml_translator ListProg
Libs
  preamble ml_translatorLib cfLib

val _ = translation_extends "ListProg";

val st = get_ml_prog_state();

Theorem app_spec = Q.prove(
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

Theorem sort_is_heap_list_sort:
  ListProg$sort R xs = heap_list_sort R xs
Proof
  simp [sort_def, sort_via_sfx_trees_def]
  \\ Cases_on `xs` \\ simp [EVAL ``(heap_list_sort R [])``]
  \\ simp [sort_via_sfx_trees_run_worker_def,
        run_init_heap_list_state_def, ml_monadBaseTheory.run_def]
  \\ simp [heap_list_sort_monadicTheory.sort_via_sfx_trees_worker_eq]
QED

Theorem sort_sorted = heap_list_sortTheory.heap_list_sort_sorted
  |> REWRITE_RULE [GSYM sort_is_heap_list_sort]

Theorem sort_contents = heap_list_sortTheory.heap_list_sort_contents
  |> REWRITE_RULE [GSYM sort_is_heap_list_sort]

