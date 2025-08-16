(*
  Translate md5 function
*)
Theory md5Prog
Libs
  preamble basis cfLib basisFunctionsLib
Ancestors
  md5 UnsafeProg

val _ = translation_extends "UnsafeProg";

(* translate md5Theory *)

val res = translate w64_zero_def;
val res = translate packLittle_def;
val res = translate PADDING_def;
val init_v = translate init_def;
val res = translate DROP_def;
val res = translate subVec_def;

Triviality word_not_thm:
  ¬w = word_xor w (0xFFFFFFFFw:word32)
Proof
  fs []
QED

val res = translate word_not_thm;
val res = translate F'_def;
val res = translate G'_def;
val res = translate H'_def;
val res = translate I'_def;
val res = translate (transform_def |> SIMP_RULE std_ss [XX_def,ROTATE_LEFT_def]);

val res = translate genlist_rev_def;
val res = translate oEL_def;
val res = translate extract_def;
val res = translate take_rev_def;
val res = translate loop_def;

val mul8add_simp = mul8add_def |> Q.SPECL [‘w’,‘1’]
  |> SIMP_RULE std_ss [LET_THM,WORD_MUL_LSL,word_mul_n2w,
       EVAL “(1w ⋙ 29):word32”, WORD_ADD_0,WORD_LO,w2n_n2w,
       EVAL “dimword (:32)”];

val mul8add_thm = mul8add_def
  |> SIMP_RULE std_ss [LET_THM,WORD_MUL_LSL,word_mul_n2w,
       WORD_ADD_0,WORD_LO,w2n_n2w,EVAL “dimword (:32)”];

val res = translate (update1_def |> REWRITE_RULE [mul8add_simp, GSYM ml_translatorTheory.sub_check_def]);

val res = translate mul8add_thm;
val res = translate genlist_rev_def;
val res = translate (update_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val final_v = translate (final_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val res = translate hxd_def;
val res = translate EL;

Theorem el_side_thm:
  ∀n xs. el_side n xs ⇔ n < LENGTH xs
Proof
  Induct
  \\ once_rewrite_tac [fetch "-" "el_side_def"]
  \\ rw [] \\ Cases_on ‘xs’ \\ fs []
QED

val _ = update_precondition el_side_thm;

val res = translate byte2hex_def;

Theorem byte2hex_side_thm:
  ∀n acc. byte2hex_side n acc = T
Proof
  fs [fetch "-" "byte2hex_side_def", EVAL “LENGTH hxd”] \\ fs [DIV_LT_X]
  \\ assume_tac (wordsTheory.w2n_lt |> INST_TYPE [“:'a” |-> “:8”])
  \\ fs []
QED

val _ = update_precondition byte2hex_side_thm;

val res = translate toHexString_def;

Definition md5_update_def:
  md5_update y x = update1 x (n2w (ORD y))
End

val md5_update_v = translate md5_update_def;

Definition md5_final_def:
  md5_final s = SOME (implode (toHexString (final s)))
End

val md5_final_v = translate md5_final_def;

val md5_lem = md5_def
  |> SIMP_RULE std_ss [FOLDL_MAP,mllistTheory.foldl_intro,GSYM md5_update_def]
  |> CONV_RULE (DEPTH_CONV ETA_CONV);

val res = translate md5_lem;

val _ = (append_prog o process_topdecs) `
  fun md5_of stdin_or_fname =
    case TextIO.foldChars md5_update init stdin_or_fname of
      Some s => md5_final s
    | None => None`;

val md5_of_v_def = fetch "-" "md5_of_v_def";

Theorem md5_of_SOME:
  OPTION_TYPE FILENAME (SOME s) fnv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) md5_of_v [fnv]
    (STDIO fs)
    (POSTv retv. STDIO fs *
                 & (OPTION_TYPE STRING_TYPE
                      (OPTION_MAP (implode o md5) (file_content fs s))
                      retv))
Proof
  rpt strip_tac
  \\ xcf_with_def md5_of_v_def
  \\ assume_tac md5_update_v
  \\ assume_tac init_v
  \\ drule_all (foldChars_SOME |> GEN_ALL)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet ‘(POSTv retv.
             STDIO fs *
             &OPTION_TYPE MD5_MD5STATE_TYPE
               (OPTION_MAP (foldl md5_update init) (file_content fs s)) retv)’
  THEN1 xapp
  \\ Cases_on ‘file_content fs s’ \\ fs []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch THEN1 (xcon \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ first_x_assum $ irule_at (Pos hd) \\ rw []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,md5_final_def]
  \\ fs [md5_lem]
QED

Theorem md5_of_NONE:
  OPTION_TYPE FILENAME NONE fnv ∧
  stdin_content fs = SOME text
  ⇒
  app (p:'ffi ffi_proj) md5_of_v [fnv]
    (STDIO fs)
    (POSTv retv. STDIO (fastForwardFD fs 0) *
                 & (OPTION_TYPE STRING_TYPE (SOME (implode (md5 text))) retv))
Proof
  rpt strip_tac
  \\ xcf_with_def md5_of_v_def
  \\ assume_tac md5_update_v
  \\ assume_tac init_v
  \\ drule_all (foldChars_NONE |> GEN_ALL)
  \\ disch_then (assume_tac o SPEC_ALL)
  \\ xlet ‘(POSTv retv.
             STDIO (fastForwardFD fs 0) *
             &OPTION_TYPE MD5_MD5STATE_TYPE
               (SOME (foldl md5_update init text)) retv)’
  THEN1 xapp
  \\ gvs [std_preludeTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ xapp \\ xsimpl
  \\ first_x_assum $ irule_at (Pos hd) \\ rw []
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,md5_final_def]
  \\ fs [md5_lem]
QED
