open preamble ml_translatorLib cfLib
     PrinterProgTheory Word8ArrayProofTheory

val _ = new_theory "PrinterProof";

val _ = translation_extends "PrinterProg";

(* heap predicate *)
val PRINTER_def = Define`
  PRINTER ls = IOx print_ffi_part ls`;

fun xffi_gc q =
  xpull_check_not_needed
  \\ head_unfold cf_ffi_def
  \\ irule local_gc_post
  \\ conj_tac >- simp[local_is_local]
  \\ qexists_tac q
  \\ reverse conj_tac >- xsimpl
  \\ irule local_elim \\ hnf
  \\ simp[app_ffi_def] \\ reduce_tac
  \\ conj_tac \\ cleanup_exn_side_cond

val print_spec = Q.store_thm("print_spec",
  `STRING_TYPE s sv ==>
   app (p:'ffi ffi_proj) ^(fetch_v"Printer.print"(get_ml_prog_state()))
     [sv] (PRINTER out) (POSTv uv. &UNIT_TYPE () uv * PRINTER (out ++ explode s))`,
  map_every qid_spec_tac[`out`,`sv`,`s`]
  \\ completeInduct_on`strlen s`
  \\ rw[]
  \\ xcf "Printer.print" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ qmatch_goalsub_rename_tac`W8ARRAY loc []`
    \\ xffi_gc `POSTv uv. &UNIT_TYPE () uv * PRINTER (out ++ explode s) * W8ARRAY loc []`
    \\ Cases_on`s`
    \\ fs[ml_translatorTheory.STRING_TYPE_def]
    \\ simp[PRINTER_def, printFFITheory.print_ffi_part_def, IOx_def]
    \\ qmatch_goalsub_abbrev_tac`IO st u ns`
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["s''","u'","ns'"]))
    \\ map_every qexists_tac[`st`,`u`,`ns`]
    \\ xsimpl
    \\ simp[Abbr`ns`]
    \\ simp[Abbr`u`,Abbr`st`]
    \\ EVAL_TAC \\ simp[]
    \\ qmatch_assum_rename_tac`NUM (LENGTH st) _`
    \\ qexists_tac`MAP (n2w o ORD) st`
    \\ simp[MAP_MAP_o, CHR_w2n_n2w_ORD] )
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ Cases_on`s`
  \\ fs[mlstringTheory.substring_def] \\ rfs[]
  \\ rfs[GSYM TAKE_SEG]
  \\ qmatch_asmsub_rename_tac`TAKE 63 st`
  \\ xlet`POSTv uv. &UNIT_TYPE () uv * PRINTER (out ++ (TAKE 63 st))`
  >- (
    qmatch_goalsub_rename_tac`W8ARRAY loc []`
    \\ xffi_gc `POSTv uv. &UNIT_TYPE () uv * PRINTER (out ++ (TAKE 63 st)) * W8ARRAY loc []`
    \\ fs[ml_translatorTheory.STRING_TYPE_def]
    \\ simp[PRINTER_def, printFFITheory.print_ffi_part_def, IOx_def]
    \\ qmatch_goalsub_abbrev_tac`IO ot u ns`
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["s","u'","ns'"]))
    \\ map_every qexists_tac[`ot`,`u`,`ns`]
    \\ xsimpl
    \\ simp[Abbr`ns`]
    \\ simp[Abbr`u`,Abbr`ot`]
    \\ EVAL_TAC \\ simp[]
    \\ qexists_tac`MAP (n2w o ORD) (TAKE 63 st)`
    \\ simp[MAP_MAP_o, CHR_w2n_n2w_ORD]
    \\ simp[LENGTH_SEG])
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ qmatch_asmsub_rename_tac`ov = Conv _ _`
  \\ `OPTION_TYPE NUM NONE ov` by (EVAL_TAC \\ rw[])
  \\ rveq
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ instantiate
  \\ `extract (strlit st) 63 NONE = strlit (DROP 63 st)`
  by ( rw[mlstringTheory.extract_def, mlstringTheory.substring_def, DROP_SEG] )
  \\ rw[]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`out ++ TAKE 63 st`
  \\ xsimpl
  \\ rewrite_tac[GSYM APPEND_ASSOC]
  \\ rewrite_tac[TAKE_DROP]
  \\ xsimpl);

val _ = export_theory();
