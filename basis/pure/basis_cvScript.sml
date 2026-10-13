(*
  Translation of basis types and functions for use with cv_compute.
*)
Theory basis_cv[no_sig_docs]
Ancestors
  mlsexp cv_std cv_string_fmap
Libs
  preamble cv_transLib

val _ = cv_memLib.use_long_names := true;

Theorem list_mem[local,cv_inline] = listTheory.MEM;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.SmartAppend_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;

val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans mlstringTheory.strcat_thm;
val _ = cv_trans mlstringTheory.chr_to_str_def;
val _ = cv_auto_trans mlstringTheory.concat_def;

val res = cv_trans_pre "strsub_pre" mlstringTheory.strsub_def;

Theorem strsub_pre[cv_pre]:
  ∀v n. strsub_pre v n ⇔ n < strlen v
Proof
  Cases \\ simp [Once res, mlstringTheory.strlen_def]
QED

val _ = cv_trans rich_listTheory.MAX_LIST_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

val toChar_pre = cv_trans_pre "mlint_toChar_pre" mlintTheory.toChar_def
val num_to_chars_pre = cv_auto_trans_pre "mlint_num_to_chars_pre" mlintTheory.num_to_chars_def;

Theorem IMP_toChar_pre:
  n < 16 ⇒ mlint_toChar_pre n
Proof
  gvs [toChar_pre]
QED

Theorem num_to_chars_pre[cv_pre,local]:
  ∀a0 a1 a2 a3. mlint_num_to_chars_pre a0 a1 a2 a3
Proof
  ho_match_mp_tac mlintTheory.num_to_chars_ind \\ rw []
  \\ rw [] \\ simp [Once num_to_chars_pre]
  \\ once_rewrite_tac [toChar_pre] \\ gvs [] \\ rw []
  \\ ‘k MOD 10 < 10’ by gvs [] \\ simp []
QED

Theorem Num_ABS[local]:
  Num (ABS i) = Num i
Proof
  Cases_on ‘i’ \\ gvs []
QED

val _ = cv_trans (mlintTheory.toString_def |> SRULE [Num_ABS]);
val _ = cv_trans mlintTheory.num_to_str_def;

val _ = cv_auto_trans (mlsexpTheory.smart_remove_def |> SRULE [GSYM GREATER_DEF]);
val _ = cv_auto_trans mlsexpTheory.v2pretty_def;
val _ = cv_auto_trans mlsexpTheory.str_tree_to_strs_def;

(* -- finite maps with an mlstring domain --
   These are represented as HOL's string |-> 'a maps, see cv_string_fmap,
   by exploding the keys. *)

Theorem FLOOKUP_MAP_KEYS_explode[local]:
  FLOOKUP (MAP_KEYS explode m) s = FLOOKUP m (implode s)
Proof
  ‘s = explode (implode s)’ by simp [mlstringTheory.explode_implode]
  \\ pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ irule FLOOKUP_MAP_KEYS_MAPPED
  \\ simp [pred_setTheory.INJ_DEF, mlstringTheory.explode_11]
QED

Theorem FLOOKUP_MAP_KEYS_implode[local]:
  FLOOKUP (MAP_KEYS implode m) k = FLOOKUP m (explode k)
Proof
  ‘k = implode (explode k)’ by simp [mlstringTheory.implode_explode]
  \\ pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ irule FLOOKUP_MAP_KEYS_MAPPED
  \\ simp [pred_setTheory.INJ_DEF]
  \\ metis_tac [mlstringTheory.explode_implode]
QED

Definition from_mlstring_fmap_def:
  from_mlstring_fmap (f:'a -> cv) (m:mlstring |-> 'a) =
    from_string_fmap f (MAP_KEYS explode m)
End

Definition to_mlstring_fmap_def:
  to_mlstring_fmap (t:cv -> 'a) v : mlstring |-> 'a =
    MAP_KEYS implode (to_string_fmap t v)
End

Theorem from_to_mlstring_fmap[cv_from_to]:
  from_to (f:'a -> cv) t ⇒
  from_to (from_mlstring_fmap f) (to_mlstring_fmap t)
Proof
  strip_tac \\ drule from_to_string_fmap
  \\ rw [cv_typeTheory.from_to_def, from_mlstring_fmap_def,
         to_mlstring_fmap_def]
  \\ rw [fmap_eq_flookup, FLOOKUP_MAP_KEYS_implode, FLOOKUP_MAP_KEYS_explode,
         mlstringTheory.implode_explode]
QED

val cv_explode_thm = fetch "-" "cv_mlstring_explode_thm";

Theorem cv_rep_mlstring_FEMPTY[cv_rep]:
  from_mlstring_fmap f FEMPTY = cv$Num 0
Proof
  simp [from_mlstring_fmap_def, MAP_KEYS_FEMPTY, cv_rep_string_FEMPTY]
QED

Theorem cv_rep_mlstring_FLOOKUP[cv_rep]:
  from_option f (FLOOKUP m k) =
  cv_st_get (from_mlstring_fmap f m)
    (cv_mlstring_explode (from_mlstring_mlstring_mlstring k))
Proof
  simp [from_mlstring_fmap_def, GSYM cv_explode_thm,
        GSYM cv_rep_string_FLOOKUP, FLOOKUP_MAP_KEYS_explode,
        mlstringTheory.implode_explode]
QED

Theorem cv_rep_mlstring_IN_FDOM[cv_rep]:
  b2c (k ∈ FDOM m) =
  cv_ispair (cv_st_get (from_mlstring_fmap (f:'a -> cv) m)
               (cv_mlstring_explode (from_mlstring_mlstring_mlstring k)))
Proof
  simp [GSYM cv_rep_mlstring_FLOOKUP, FLOOKUP_DEF]
  \\ rw [cv_typeTheory.from_option_def]
QED

Theorem cv_rep_mlstring_FUPDATE[cv_rep]:
  from_mlstring_fmap f (m |+ (k,v)) =
  cv_st_set (from_mlstring_fmap f m)
    (cv_mlstring_explode (from_mlstring_mlstring_mlstring k)) (f v)
Proof
  simp [from_mlstring_fmap_def, GSYM cv_explode_thm,
        GSYM cv_rep_string_FUPDATE]
  \\ AP_TERM_TAC
  \\ rw [fmap_eq_flookup, FLOOKUP_MAP_KEYS_explode, FLOOKUP_UPDATE]
  \\ metis_tac [mlstringTheory.implode_explode, mlstringTheory.explode_implode]
QED

Theorem cv_rep_mlstring_DOMSUB[cv_rep]:
  from_mlstring_fmap f (m \\ k) =
  cv_st_del (from_mlstring_fmap f m)
    (cv_mlstring_explode (from_mlstring_mlstring_mlstring k))
Proof
  simp [from_mlstring_fmap_def, GSYM cv_explode_thm,
        GSYM cv_rep_string_DOMSUB]
  \\ AP_TERM_TAC
  \\ rw [fmap_eq_flookup, FLOOKUP_MAP_KEYS_explode, DOMSUB_FLOOKUP_THM]
  \\ metis_tac [mlstringTheory.implode_explode, mlstringTheory.explode_implode]
QED

Theorem cv_rep_mlstring_FUNION[cv_rep]:
  from_mlstring_fmap f (FUNION m1 m2) =
  cv_st_union (from_mlstring_fmap f m1) (from_mlstring_fmap f m2)
Proof
  simp [from_mlstring_fmap_def, GSYM cv_rep_string_FUNION]
  \\ AP_TERM_TAC
  \\ rw [fmap_eq_flookup, FLOOKUP_MAP_KEYS_explode, FLOOKUP_FUNION]
QED
