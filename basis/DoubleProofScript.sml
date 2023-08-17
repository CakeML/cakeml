(*
  Proofs that the to-/fromString functions in the Double
  module correctly produce a string representation from a double,
  and vice versa assuming that the FFI is implemented correctly.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib cfLib mlstringTheory
     Word64ProgTheory
     Word8ArrayProgTheory
     Word8ArrayProofTheory
     OptionProgTheory
     DoubleFFITheory
     DoubleProgTheory;

val _ = new_theory "DoubleProof";

val _ = translation_extends "DoubleProg";

val basis_st = get_ml_prog_state;

val doubleFuns_ok_def = Define `
  doubleFuns_ok doubleFns =
    (! w.
      LENGTH (doubleFns.toString w) <= 256 /\
      ~ MEM (CHR 0) (doubleFns.toString w))`;

val DoubleIO_def = Define `
  DoubleIO doubleFns =
    IOx double_ffi_part doubleFns * (cond (doubleFuns_ok doubleFns))`;

Theorem one_one_eq[simp]:
  one x ==>> one y <=> x = y
Proof
  fs[SEP_IMP_def, one_def]
QED

Theorem MAP_CHR_w2n_n2w_ORD_id:
  MAP (CHR o (w2n:word8 -> num) o (n2w:num -> word8) o ORD) s = s
Proof
  rewrite_tac[miscTheory.CHR_w2n_n2w_ORD]
  \\ Induct_on `s`  \\ fs[MAP]
QED

Theorem into_bytes_len:
  ! w. LENGTH (into_bytes n w) = n
Proof
  Induct_on `n` \\ fs[into_bytes_def]
QED

Theorem concat_all_into_bytes_id:
  concat_all (HD (into_bytes 8 w)) (EL 1 (into_bytes 8 w))
    (EL 2 (into_bytes 8 w)) (EL 3 (into_bytes 8 w)) (EL 4 (into_bytes 8 w))
    (EL 5 (into_bytes 8 w)) (EL 6 (into_bytes 8 w)) (EL 7 (into_bytes 8 w)) = w
Proof
  fs[EVAL ``into_bytes 8 w``]
  \\ fs[concat_all_def]
  \\ blastLib.BBLAST_TAC
QED

Definition string2Double_def:
  string2Double (s:string) (df:doubleFuns) = (df.fromString (explode (prepareString (strlit s))))
End

Theorem double_fromWord_spec:
  WORD w v ⇒
  app (p:'ffi ffi_proj) Double_fromWord_v [v]
      (emp)
      (POSTv v. cond (v = FP_WordTree $ Fp_const w))
Proof
  xcf_with_def "fromWord" Double_fromWord_v_def
  \\ gs[cf_fpfromword_def, local_def, emp_def] \\ rpt strip_tac
  \\ qexists_tac ‘GC’ \\ qexists_tac ‘emp’
  \\ gs[emp_def, GC_def, set_sepTheory.SEP_EXISTS, set_sepTheory.STAR_def,
        SPLIT_def, WORD_def, app_fpfromword_def]
  \\ qexists_tac ‘(λ v. λ h. v = Val $ FP_WordTree $ Fp_const w) *+ GC’
  \\ rpt conj_tac
  >- (qexists_tac ‘λ x. T’ \\ gs[])
  >- (
    qexists_tac ‘w’ \\ gs[exp2v_def] \\ rpt conj_tac
    >- EVAL_TAC
    >- (
      gs[set_sepTheory.SEP_IMP_def, STARPOST_def, GC_def]
      \\ rpt strip_tac \\ gs[set_sepTheory.STAR_def]
      \\ qexists_tac ‘EMPTY’ \\ qexists_tac ‘s’ \\ gs[SPLIT_def, SEP_EXISTS]
      \\ asm_exists_tac \\ gs[])
    \\ gs[SEP_IMPPOSTv_inv_def, SEP_IMPPOSTe_def, SEP_IMPPOSTf_def,
          SEP_IMPPOSTd_def, SEP_IMP_def, STARPOST_def, set_sepTheory.STAR_def])
  >- (
    rw[SEP_IMPPOST_def, SEP_IMP_def, POSTv_def, STARPOST_def, POST_def,
       set_sepTheory.STAR_def]
    \\ gvs[cond_def, GC_def, SEP_EXISTS, SPLIT_def]
    \\ qexists_tac ‘λ x. y v'’ \\ gs[])
QED

Theorem double_fromString_spec:
  ! s sv.
  STRING_TYPE (strlit s) sv ==>
  app (p:'ffi ffi_proj) Double_fromString_v [sv]
    (DoubleIO df)
    (POSTv v. cond (v = FP_WordTree $ Fp_const $ string2Double s df) * DoubleIO df)
Proof
  xcf_with_def "Double.fromString" Double_fromString_v_def
  \\ reverse (Cases_on `doubleFuns_ok df`)
  >- (fs[DoubleIO_def] \\ xpull)
  \\ gs[string2Double_def]
  \\ ntac 3 (xlet_auto >- (fs[] \\ xsimpl))
  \\ rename [`W8ARRAY iobuff`]
  \\ xlet `POSTv v. W8ARRAY iobuff (into_bytes 8 (df.fromString (explode (prepareString (strlit s))))) * DoubleIO df`
  >- (
    fs[DoubleIO_def, IOx_def, double_ffi_part_def, IO_def, mk_ffi_next_def]
    \\ xpull \\ xffi \\ xsimpl
    \\ fs[STRING_TYPE_def] \\ rveq
    \\ qexists_tac `MAP (n2w o ORD) (explode (prepareString (strlit s)))` \\ fs[MAP_MAP_o]
    \\ qexists_tac `emp`
    \\ xsimpl
    \\ rewrite_tac [one_one_eq] \\ fs[]
    \\ conj_tac
    >- (
      fs[MAP_CHR_w2n_n2w_ORD_id, STRING_TYPE_def, prepareString_def]
      \\ gs[STRING_TYPE_def, translate_thm, implode_def])
    \\ fs[mk_ffi_next_def, ffi_fromString_def]
    \\ xsimpl
    \\ rewrite_tac [one_one_eq] \\ fs[MAP_MAP_o, MAP_CHR_w2n_n2w_ORD_id])
  \\ ntac 9
    (xlet_auto
    >- (xsimpl \\ TRY (qexists_tac `df`) \\ fs[into_bytes_len]))
  \\ xapp \\ xsimpl
  \\ Cases_on `df` \\ fs[doubleFuns_ok_def, WORD_def, concat_all_into_bytes_id]
QED

Theorem concat_all_bytes_i:
  concat_all (byte_0 w) (byte_1 w) (byte_2 w) (byte_3 w) (byte_4 w) (byte_5 w)
(byte_6 w) (byte_7 w) = w
Proof
  fs[concat_all_def, byte_0_def, byte_1_def, byte_2_def,
     byte_3_def, byte_4_def, byte_5_def, byte_6_def, byte_7_def,
     concat_word_list_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem findi_app:
  ! f s1 s2 n x.
    findi f s1 = NONE /\
    findi f s2 = SOME (n, x) ==>
    findi f (s1 ++ s2) = SOME (n + LENGTH s1, x)
Proof
  Induct_on `s1` \\ fs[findi_def] \\ rpt strip_tac \\ fs[]
  \\ Cases_on `f h` \\ fs[]
  \\ reverse (Cases_on `findi f s1`)
  >- (rename [`findi f s1 = SOME p`] \\ PairCases_on `p` \\ fs[])
  \\ res_tac \\ fs[]
QED

Theorem findi_app2:
  ! f s1 s2 n x.
    findi f s1 = SOME (n,x) ==>
    findi f (s1 ++ s2) = SOME (n,x)
Proof
  Induct_on `s1` \\ fs[findi_def] \\ rpt strip_tac
  \\ Cases_on `f h` \\ fs[]
  \\ Cases_on `findi f s1` \\ fs[]
  \\ rename [`findi f s1 = SOME p`] \\ PairCases_on `p` \\ fs[]
  \\ rveq
  \\ res_tac \\ rveq \\ fs[]
QED

Theorem findi_none:
  ~ MEM #"\^@" s ==>
  findi is_0_byte (MAP (n2w o ORD) s) = NONE
Proof
  Induct_on `s` \\ fs[findi_def, is_0_byte_def]
  \\ rpt strip_tac
  \\ `ORD h MOD 256 = ORD h`
    by (irule MOD_UNIQUE
        \\ qexists_tac `0` \\ fs[ORD_BOUND])
  \\ pop_assum (fn thm => fs[thm])
  \\ fs[ORD_eq_0]
QED

Theorem toString_has_0byte:
  ! w. doubleFuns_ok df /\
  s = df.toString w ==>
  findi is_0_byte (MAP (n2w ∘ ORD) s ++ [0w] ++ remStr) =
    SOME (LENGTH s, 0w)
Proof
  rpt strip_tac
  \\ Q.ISPECL_THEN [`is_0_byte`] assume_tac findi_app2
  \\ first_x_assum (qspecl_then [`MAP (n2w o ORD) s ++ [0w]`, `remStr`, `STRLEN s`] assume_tac)
  \\ first_x_assum irule
  \\ Q.ISPECL_THEN [`is_0_byte`] assume_tac findi_app
  \\ first_x_assum (qspecl_then [`MAP (n2w o ORD) s`, `[0w]`, `0`] assume_tac)
  \\ fs[doubleFuns_ok_def] \\ first_x_assum (qspec_then `w` assume_tac)
  \\ fs[]
  \\ IMP_RES_TAC findi_none
  \\ rveq \\ res_tac \\ fs[findi_def, is_0_byte_def]
QED

Theorem TAKE_STRLEN_id:
  TAKE (STRLEN s1) (MAP f s1 ++ s2) = MAP f s1
Proof
  Induct_on `s1` \\ fs[TAKE]
QED

Theorem TAKE_STRLEN_id2:
  TAKE (STRLEN s1) (MAP f s1 ++ s2 ++ s3) = MAP f s1
Proof
  Induct_on `s1` \\ fs[TAKE]
QED

Theorem double_toWord_spec:
  v = FP_WordTree fp ⇒
  app (p:'ffi ffi_proj) Double_toWord_v [v]
      (emp)
      (POSTv v. cond (WORD (compress_word fp) v))
Proof
  xcf_with_def "toWord" Double_toWord_v_def
  \\ gs[cf_fptoword_def, local_def, emp_def] \\ rpt strip_tac
  \\ qexists_tac ‘GC’ \\ qexists_tac ‘emp’
  \\ gs[emp_def, GC_def, set_sepTheory.SEP_EXISTS, set_sepTheory.STAR_def,
        SPLIT_def, WORD_def, app_fptoword_def]
  \\ qexists_tac ‘(λ v. λ h. v = Val $ Litv $ Word64 $ compress_word fp) *+ GC’
  \\ rpt conj_tac
  >- (qexists_tac ‘λ x. T’ \\ gs[])
  >- (
    qexists_tac ‘fp’ \\ gs[exp2v_def] \\ rpt conj_tac
    >- EVAL_TAC
    >- (
      gs[set_sepTheory.SEP_IMP_def, STARPOST_def, GC_def]
      \\ rpt strip_tac \\ gs[set_sepTheory.STAR_def]
      \\ qexists_tac ‘EMPTY’ \\ qexists_tac ‘s’ \\ gs[SPLIT_def, SEP_EXISTS]
      \\ asm_exists_tac \\ gs[])
    \\ gs[SEP_IMPPOSTv_inv_def, SEP_IMPPOSTe_def, SEP_IMPPOSTf_def,
          SEP_IMPPOSTd_def, SEP_IMP_def, STARPOST_def, set_sepTheory.STAR_def])
  >- (
    rw[SEP_IMPPOST_def, SEP_IMP_def, POSTv_def, STARPOST_def, POST_def,
       set_sepTheory.STAR_def]
    \\ gvs[cond_def, GC_def, SEP_EXISTS, SPLIT_def]
    \\ qexists_tac ‘λ x. y v'’ \\ gs[])
QED

Theorem double_toString_spec:
  ! (w:word64) fp.
    compress_word fp = w ⇒
    app (p:'ffi ffi_proj) Double_toString_v [FP_WordTree fp]
        (DoubleIO df)
        (POSTv v. cond (STRING_TYPE (implode (df.toString w)) v) * DoubleIO df)
Proof
  xcf_with_def "Double.toString" Double_toString_v_def
  \\ reverse (Cases_on `doubleFuns_ok df`)
  >- (fs[DoubleIO_def] \\ xpull)
  \\ ntac 19 (xlet_auto >- (fs[] \\ xsimpl))
  \\ rename [`W8ARRAY iobuff`]
  \\ fs[concat_all_bytes_i]
  \\ qabbrev_tac `res_str = df.toString w`
  \\ qabbrev_tac `updBuf = (LUPDATE (byte_7 w) 7
             (LUPDATE (byte_6 w) 6
                (LUPDATE (byte_5 w) 5
                   (LUPDATE (byte_4 w) 4
                      (LUPDATE (byte_3 w) 3
                         (LUPDATE (byte_2 w) 2
                            (LUPDATE (byte_1 w) 1
                               (LUPDATE (byte_0 w) 0 (REPLICATE 256 0w)))))))))`
  \\ qabbrev_tac `final_str = (MAP (n2w o ORD) (res_str ++ [CHR 0]) ++
                    DROP (LENGTH res_str + 1) updBuf):word8 list`
  \\ xlet `POSTv v. W8ARRAY iobuff final_str * DoubleIO df`
  >- (
    fs[DoubleIO_def, IOx_def, double_ffi_part_def, IO_def, mk_ffi_next_def]
    \\ xpull \\ xffi \\ xsimpl
    \\ qexists_tac `emp`
    \\ fs [SEP_CLAUSES, one_one_eq]
    \\ fs [mk_ffi_next_def, ffi_toString_def]
    \\ unabbrev_all_tac
    \\ fs [EVAL ``REPLICATE 256 x``]
    \\ fs [EL_LUPDATE, HD_LUPDATE]
    \\ fs[concat_all_bytes_i]
    \\ xsimpl \\ fs[one_one_eq])
  \\ xlet `POSTv v. W8ARRAY iobuff final_str *
          DoubleIO df *
          cond (OPTION_TYPE (PAIR_TYPE NUM WORD8) (findi is_0_byte final_str) v)`
    >- (
      xapp \\ xsimpl
      \\ qexists_tac `is_0_byte` \\ fs[is_0_byte_v_thm])
  \\ IMP_RES_TAC toString_has_0byte
  \\ first_x_assum (qspecl_then [`w`, `df.toString w`] assume_tac)
  \\ fs[]
  \\ xlet_auto \\ fs[]
  >- (
    xsimpl
    \\ unabbrev_all_tac
    \\ fs[concat_all_bytes_i])
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl
  \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ asm_exists_tac \\ fs[]
  \\ rpt conj_tac
  >- (
    rpt strip_tac
    \\ fs[STRING_TYPE_def, mlstringTheory.implode_def]
    \\ `findi is_0_byte final_str = SOME (STRLEN (df.toString w), 0w)`
      by (unabbrev_all_tac \\ fs[])
    \\ fs[]
    \\ `TAKE (STRLEN (df.toString w)) final_str = MAP (n2w o ORD) (df.toString w)`
      by (unabbrev_all_tac \\ fs[concat_all_bytes_i, TAKE_STRLEN_id2])
    \\ unabbrev_all_tac \\ fs[]
    \\ fs[MAP_MAP_o, MAP_CHR_w2n_n2w_ORD_id])
  \\ unabbrev_all_tac
  \\ fs[]
QED

val _ = export_theory ();
