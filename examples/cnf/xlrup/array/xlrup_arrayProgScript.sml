(*
  This refines xlrup_list to use arrays
*)
Theory xlrup_arrayProg
Ancestors
  misc mllist UnsafeProof ccnf_arrayProg ccnf_parseProg cnf ccnf ccnf_list
  syntax_helper xor xor_list xlrup_cnf xlrup xlrup_list xlrup_parsing
  mlint mlvector sptree
Libs
  preamble basis blastLib

val _ = hide_environments true;

val _ = translation_extends "ccnf_parseProg";

val _ = register_type``:xlrup``;
val _ = register_type``:'a spt``;

Overload "strxor_TYPE" = ``STRING_TYPE``

val _ = translate insert_def;
val _ = translate lookup_def;

val bw0_v_thm = fetch "ccnf_arrayProg" "bw0_v_thm";

(*** Adding XORs into a byte array, in place ***)

val res = translate toByte_def;

Quote add_cakeml:
  fun strxor_aux_c_arr cs ds n =
  if n = 0 then cs
  else
  let
    val n1 = n - 1
    val c = Unsafe.w8sub cs n1
    val d = tobyte (String.sub ds n1)
    val x = Word8.xorb c d
    val u = Unsafe.w8update cs n1 x
  in
    strxor_aux_c_arr cs ds n1
  end
End

Theorem strxor_aux_c_arr_spec:
  ∀n nv cs csv ds dsv.
  NUM n nv ∧
  strxor_TYPE ds dsv ∧
  n ≤ strlen ds ∧ strlen ds ≤ LENGTH cs
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_aux_c_arr" (get_ml_prog_state()))
    [csv; dsv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(strxor_aux_c cs ds n = cs'))
Proof
  Induct>>rw[]>>
  xcf "strxor_aux_c_arr" (get_ml_prog_state ())>>
  simp[Once strxor_aux_c_def]>>
  xlet_autop
  >- (
    xif>>asm_exists_tac>>simp[]>>
    xvar>>xsimpl)>>
  xif>>asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  xapp>>xsimpl
QED

Quote add_cakeml:
  fun strxor_c_arr s t =
  let
    val lt = String.size t
    val ls = Word8Array.length s
  in
    if lt <= ls
    then (Unsafe.w8xor_str s t; s)
    else
      let
        val ss = Word8Array.array lt bw0
        val u = Word8Array.copy s 0 ls ss 0
      in
        (Unsafe.w8xor_str ss t; ss)
      end
  end
End

Theorem xor_bytes_eq[local]:
  ∀xs ys zs.
    LENGTH xs = LENGTH ys ⇒
    xor_bytes xs (ys ++ zs) = SOME (MAP2 word_xor xs ys ++ zs)
Proof
  Induct>>Cases_on ‘ys’>>gvs [semanticPrimitivesTheory.xor_bytes_def]
QED

Theorem xor_bytes_same[local]:
  LENGTH xs = LENGTH ys ⇒
  xor_bytes xs ys = SOME (MAP2 word_xor xs ys)
Proof
  strip_tac>>
  drule xor_bytes_eq>>
  disch_then $ qspec_then ‘[]’ mp_tac>>
  gvs []
QED

Theorem xor_bytes_rest[local]:
  ∀s ys1 ys2.
    LENGTH s = LENGTH ys1 ⇒
    THE (xor_bytes s (ys1 ++ ys2)) =
    THE (xor_bytes s ys1) ++ ys2
Proof
  rw [xor_bytes_eq]>>
  qspecl_then [‘s’,‘ys1’,‘[]’] mp_tac xor_bytes_eq>>
  gvs []
QED

Theorem xor_bytes_snoc[local]:
  ∀xs ys xs1 ys1.
    LENGTH xs = LENGTH ys ⇒
    xor_bytes (xs ++ xs1) (ys ++ ys1) =
    case xor_bytes xs ys of
    | NONE => NONE
    | SOME res =>
       case xor_bytes xs1 ys1 of
       | NONE => NONE
       | SOME res1 => SOME (res ++ res1)
Proof
  Induct>>Cases_on ‘ys’>>gvs []>>
  gvs [semanticPrimitivesTheory.xor_bytes_def]
  >- (rw []>>CASE_TAC>>gvs [])>>
  rw []>>
  CASE_TAC>>asm_simp_tac (srw_ss()) []>>
  CASE_TAC>>asm_simp_tac (srw_ss()) []>>
  CASE_TAC>>asm_simp_tac (srw_ss()) []
QED

Theorem xor_bytes_lemma[local]:
  ∀s r ys1 ys2.
    LENGTH ys1 = LENGTH s ⇒
    THE (xor_bytes (MAP (n2w ∘ ORD) s) ys1) ++ ys2 =
    strxor_aux_c (ys1 ++ ys2) (strlit (s ++ r)) (STRLEN s)
Proof
  Induct using SNOC_INDUCT>>
  gvs [semanticPrimitivesTheory.xor_bytes_def]
  >- (rw []>>EVAL_TAC)>>
  Cases_on ‘ys1’ using SNOC_CASES>>gvs []>>
  rw []>>
  simp [Once strxor_aux_c_def]>>
  simp_tac std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]>>
  pop_assum $ assume_tac o GSYM>>
  asm_simp_tac std_ss [EL_APPEND,EL,HD,LUPDATE_LENGTH]>>
  pop_assum $ assume_tac o GSYM>>asm_rewrite_tac []>>
  last_x_assum $ DEP_REWRITE_TAC o single o GSYM>>
  simp []>>
  DEP_REWRITE_TAC [xor_bytes_snoc]>>
  gvs [semanticPrimitivesTheory.xor_bytes_def,toByte_def]>>
  DEP_REWRITE_TAC [xor_bytes_same]>>gvs []
QED

Theorem xor_bytes_strxor_aux_c[local]:
  LENGTH s ≤ LENGTH cs ⇒
  THE (xor_bytes (MAP (n2w ∘ ORD) s) cs) =
  strxor_aux_c cs (strlit s) (STRLEN s)
Proof
  strip_tac>>
  dxrule LESS_EQ_LENGTH>>
  strip_tac>>gvs[]>>
  drule xor_bytes_lemma>>
  disch_then $ qspec_then ‘[]’ assume_tac o GSYM>>gvs []>>
  irule xor_bytes_rest>>gvs []
QED

Theorem strxor_c_arr_spec:
  strxor_TYPE ds dsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_c_arr" (get_ml_prog_state()))
    [csv; dsv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(strxor_c cs ds = cs'))
Proof
  rw[]>>
  xcf "strxor_c_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xif
  >- (
    simp[strxor_c_def]>>
    xlet_auto >- xsimpl >>
    xvar >> xsimpl >>
    Cases_on ‘ds’ >> gvs [] >>
    irule xor_bytes_strxor_aux_c >> simp []) >>
  assume_tac bw0_v_thm >>
  xlet_autop >>
  xlet_autop >>
  xlet_auto >- xsimpl >>
  xvar >> xsimpl >>
  simp[strxor_c_def]>>
  DEP_REWRITE_TAC [xor_bytes_strxor_aux_c] >>
  conj_tac >- gvs [] >>
  Cases_on ‘ds’ >> gvs []
QED

Quote add_cakeml:
  fun add_xors_aux_c_arr lno fml is s =
  case is of
    [] => s
  | i::is =>
    if Array.length fml <= i then
      raise Fail (format_failure lno ("no xor at index: " ^ Int.toString i))
    else
    case Unsafe.sub fml i of
      None => raise Fail (format_failure lno ("no xor at index (maybe deleted): " ^ Int.toString i))
    | Some x =>
      add_xors_aux_c_arr lno fml is (strxor_c_arr s x)
End

Theorem add_xors_aux_c_arr_spec:
  ∀ls lsv cs csv fmlv fmlls fmllsv lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "add_xors_aux_c_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; csv]
    (ARRAY fmlv fmllsv * W8ARRAY csv cs)
    (POSTve
      (λv. ARRAY fmlv fmllsv * SEP_EXISTS cs'.
        W8ARRAY v cs' *
        &(unwrap_TYPE $=
          (add_xors_aux_c_list fmlls ls cs) cs'))
       (λe.
        ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ add_xors_aux_c_list fmlls ls cs = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "add_xors_aux_c_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (
    xvar>>xsimpl>>
    simp[unwrap_TYPE_def,add_xors_aux_c_list_def])>>
  rpt xlet_autop>>
  simp[add_xors_aux_c_list_def,any_el_ALT]>>
  drule LIST_REL_LENGTH>> simp[]>>
  strip_tac>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  gvs[]>>
  xlet_autop>>
  `OPTION_TYPE strxor_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  xapp>>xsimpl>>
  metis_tac[]
QED

(*** Bit operations on byte arrays ***)

Definition eq_w8z_def:
  eq_w8z (v:word8) ⇔ v = 0w
End

val _ = translate eq_w8z_def;

(* Testing bit n by masking, as the translated definitions below do *)
Theorem word_and_lsl_eq_0[local]:
  n < 8 ⇒
  (((w:word8) && 1w ≪ n = 0w) ⇔ ¬ w ' n)
Proof
  strip_tac>>
  DEP_REWRITE_TAC[word_bit |> INST_TYPE[alpha |-> ``:8``] |> SIMP_RULE std_ss [word_bit_test] |> CONV_RULE (wordsLib.WORD_CONV)]>>
  fs[WORD_MUL_LSL |> Q.ISPEC`1w:word8` |> CONV_RULE (wordsLib.WORD_CONV) |> GSYM]
QED

Definition set_bit_word'_def:
  set_bit_word' (w:word8) n b =
  let nw = var_word_lsl 1w n in
  if b then w ‖ nw else w && ¬nw
End

val res = translate set_bit_word'_def;

Theorem set_bit_word'_eq:
  n < 8 ⇒
  (set_bit_word' (w:word8) n b = set_bit_word w n b)
Proof
  simp[set_bit_word_def,set_bit_word'_def]
QED

Definition get_bit_word'_def:
  get_bit_word' (w:word8) n =
  let nw = var_word_lsl 1w n in
  (w && nw <> 0w)
End

val res = translate get_bit_word'_def;

Theorem get_bit_word'_eq:
  n < 8 ⇒
  (get_bit_word' (w:word8) n = w ' n)
Proof
  simp[get_bit_word'_def]>>
  strip_tac>>
  simp[word_and_lsl_eq_0]
QED

Quote add_cakeml:
  fun get_bit_arr s n =
  let
    val q = n div 8
    val r = n mod 8 in
    get_bit_word' (Unsafe.w8sub s q) r
  end
End

Theorem get_bit_arr_spec:
  NUM n nv ∧ n DIV 8 < LENGTH cs ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_bit_arr" (get_ml_prog_state()))
    [csv; nv]
    (W8ARRAY csv cs)
    (POSTv v. W8ARRAY csv cs * & BOOL (get_bit_list cs n) v)
Proof
  rw[]>>
  xcf "get_bit_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  simp[get_bit_list_def]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  DEP_REWRITE_TAC[get_bit_word'_eq]>>
  simp[]
QED

Quote add_cakeml:
  fun set_bit_arr s n b =
  let
    val q = n div 8
    val r = n mod 8
    val b = set_bit_word' (Unsafe.w8sub s q) r b in
    Unsafe.w8update s q b
  end
End

Theorem set_bit_arr_spec:
  NUM n nv ∧ n DIV 8 < LENGTH cs ∧ BOOL b bv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "set_bit_arr" (get_ml_prog_state()))
    [csv; nv; bv]
    (W8ARRAY csv cs)
    (POSTv v.
      &UNIT_TYPE () v *
      W8ARRAY csv (set_bit_list cs n b))
Proof
  rw[]>>
  xcf "set_bit_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  simp[set_bit_list_def]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  DEP_REWRITE_TAC[set_bit_word'_eq]>>
  simp[]
QED

Definition nabs_def:
  nabs x = Num (ABS x)
End

val res = translate nabs_def;

Definition flip_bit_word'_def:
  flip_bit_word' (w:word8) n =
  let nw = var_word_lsl 1w n in
  let b = (w && nw = 0w) in
  if b then w ‖ nw else w && ¬nw
End

val res = translate flip_bit_word'_def;

Theorem flip_bit_word'_eq:
  n < 8 ⇒
  (flip_bit_word' (w:word8) n = flip_bit_word w n)
Proof
  simp[flip_bit_word_def,flip_bit_word'_def]>>
  strip_tac>>
  simp[word_and_lsl_eq_0]
QED

Quote add_cakeml:
  fun flip_bit_arr s n =
  let
    val q = n div 8
    val r = n mod 8
    val b = flip_bit_word' (Unsafe.w8sub s q) r in
    Unsafe.w8update s q b
  end
End

Theorem flip_bit_arr_spec:
  NUM n nv ∧ n DIV 8 < LENGTH cs ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "flip_bit_arr" (get_ml_prog_state()))
    [csv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      &UNIT_TYPE () v *
      W8ARRAY csv (flip_bit_list cs n))
Proof
  rw[]>>
  xcf "flip_bit_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  simp[flip_bit_list_def]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  DEP_REWRITE_TAC[flip_bit_word'_eq]>>
  simp[]
QED

(*** Unit propagation into an XOR ***)

Quote add_cakeml:
  fun unit_prop_xor_arr t s l =
  let
    val n = nabs l in
    case lookup_1 n t of None => ()
    | Some n =>
    if n < 8 * Word8Array.length s then
      if l > 0 then
        (if get_bit_arr s n then
          (set_bit_arr s n False ;flip_bit_arr s 0)
        else ())
      else set_bit_arr s n False
    else ()
  end
End

Theorem unit_prop_xor_arr_spec:
  INT l lv ∧
  SPTREE_SPT_TYPE NUM t tv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_xor_arr" (get_ml_prog_state()))
    [tv; csv; lv]
    (W8ARRAY csv cs)
    (POSTv v.
        &(UNIT_TYPE () v) *
        W8ARRAY csv (unit_prop_xor_list t cs l))
Proof
  rw[]>>
  xcf "unit_prop_xor_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  fs[unit_prop_xor_list_def,nabs_def,OPTION_TYPE_SPLIT]>>
  xmatch
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  reverse xif
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (
    xlet_auto
    >-
      (DEP_REWRITE_TAC[DIV_LT_X]>>fs[])>>
    reverse xif
    >-
      (xvar>>xsimpl)>>
    xlet_autop>>
    xlet`POSTv v.
      &UNIT_TYPE () v *
      W8ARRAY csv (set_bit_list cs y F)`
    >- (
      xapp>>simp[]>>
      (DEP_REWRITE_TAC[DIV_LT_X]>>fs[])>>
      EVAL_TAC)>>
    xapp>>xsimpl>>
    fs[set_bit_list_def])>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  (DEP_REWRITE_TAC[DIV_LT_X]>>fs[])>>
  EVAL_TAC
QED

Quote add_cakeml:
  fun get_units_arr lno fml is s =
  case is of
    [] => s
  | i::is =>
    if Array.length fml <= i then
      raise Fail (format_failure lno ("no clause at index: " ^ Int.toString i))
    else
    let
      val x = Unsafe.sub fml i
      val n = Vector.length x
    in
      if n = 1 andalso int_eq_0 (uvsub x 0) then
        raise Fail (format_failure lno ("no clause at index (maybe deleted): " ^ Int.toString i))
      else if n = 1 then
        get_units_arr lno fml is (Vector.sub x 0::s)
      else
        raise Fail (format_failure lno ("clause at index not unit: " ^ Int.toString i))
    end
End

Theorem get_units_arr_spec:
  ∀ls lsv cs csv fmlv fmlls fmllsv lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  (LIST_TYPE INT) cs csv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_units_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; csv]
    (ARRAY fmlv fmllsv)
    (POSTve
       (λv. ARRAY fmlv fmllsv *
        &(unwrap_TYPE (LIST_TYPE INT)
          (get_units_list fmlls ls cs) v))
       (λe.
        ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ get_units_list fmlls ls cs = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "get_units_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (
    xvar>>xsimpl>>
    simp[unwrap_TYPE_def,get_units_list_def])>>
  rpt xlet_autop>>
  simp[get_units_list_def,any_el_ALT]>>
  drule LIST_REL_LENGTH>> simp[]>>
  strip_tac>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  gvs[]>>
  `vcclause_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  rpt xlet_autop>>
  xlet`POSTv bb.
    ARRAY fmlv fmllsv *
    &BOOL (length (EL h fmlls) = 1 ∧ sub (EL h fmlls) 0 = 0) bb`
  >- (
    xlog>>
    reverse IF_CASES_TAC>>gvs[]
    >- xsimpl>>
    xlet_auto
    >- (xsimpl>>gvs[uvsub_side_def])>>
    xapp>>
    xsimpl>>
    qexists_tac`sub (EL h fmlls) 0`>>
    simp[int_eq_0_def])>>
  xif
  >- (
    `EL h fmlls = vcc_none` by metis_tac[is_vcc_none]>>
    simp[]>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  `EL h fmlls ≠ vcc_none` by metis_tac[is_vcc_none]>>
  simp[]>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def,unwrap_TYPE_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun fold_unit_prop_xor_arr t s ls =
  case ls of [] => s
  | (x::xs) =>
    (unit_prop_xor_arr t s x;
    fold_unit_prop_xor_arr t s xs)
End

Quote add_cakeml:
  fun unit_props_xor_arr lno fml t is s =
  fold_unit_prop_xor_arr t s
    (get_units_arr lno fml is [])
End

Theorem fold_unit_prop_xor_arr_spec:
  ∀ls lsv cs csv.
  NUM lno lnov ∧
  (LIST_TYPE INT) ls lsv ∧
  SPTREE_SPT_TYPE NUM t tv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fold_unit_prop_xor_arr" (get_ml_prog_state()))
    [tv; csv; lsv]
    (W8ARRAY csv cs)
    (POSTv v.
      W8ARRAY v (FOLDL (unit_prop_xor_list t) cs ls))
Proof
  Induct>>
  rw[]>>
  xcf "fold_unit_prop_xor_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (xvar>>xsimpl)>>
  xlet_autop>>
  xapp>>xsimpl
QED

Theorem unit_props_xor_arr_spec:
  ∀ls lsv cs csv fmlv fmlls fmllsv lno lnov.
  NUM lno lnov ∧
  SPTREE_SPT_TYPE NUM t tv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_props_xor_arr" (get_ml_prog_state()))
    [lnov; fmlv; tv; lsv; csv]
    (ARRAY fmlv fmllsv * W8ARRAY csv cs)
    (POSTve
      (λv. ARRAY fmlv fmllsv * SEP_EXISTS cs'.
        W8ARRAY v cs' *
        &(unwrap_TYPE $=
          (unit_props_xor_list fmlls t ls cs) cs'))
       (λe.
        ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ unit_props_xor_list fmlls t ls cs = NONE)))
Proof
  rw[]>>
  xcf "unit_props_xor_arr" (get_ml_prog_state ())>>
  simp[unit_props_xor_list_def]>>
  TOP_CASE_TAC
  >- (
    xlet `POSTv v. ARRAY fmlv fmllsv * &(LIST_TYPE INT) [] v`
    >- (
      xcon>>xsimpl>>
      simp[LIST_TYPE_def])>>
    xlet_auto >> xsimpl>>
    gvs[unwrap_TYPE_def])>>
  xlet `POSTv v. ARRAY fmlv fmllsv * W8ARRAY csv cs * &(LIST_TYPE INT) [] v`
  >- (
    xcon>>xsimpl>>
    simp[LIST_TYPE_def])>>
  xlet_auto >> xsimpl>>
  xapp>>xsimpl>>
  gvs[unwrap_TYPE_def]>>
  rpt(first_x_assum (irule_at Any))>>
  simp[]
QED

(*** Rendering an XOR and the variable renaming, for error messages ***)

(* The translatable form of xor$char_to_bits *)
Definition bits_of_char_def:
  bits_of_char c =
  let b = toByte c in [
  get_bit_word' b 0;
  get_bit_word' b 1;
  get_bit_word' b 2;
  get_bit_word' b 3;
  get_bit_word' b 4;
  get_bit_word' b 5;
  get_bit_word' b 6;
  get_bit_word' b 7]
End

val res = translate bits_of_char_def;

Definition print_bits_aux_def:
  (print_bits_aux [] n acc = REVERSE acc) ∧
  (print_bits_aux (b::bs) n acc =
  if b then
    print_bits_aux bs (n+1)
      ((«x» ^ toString n) :: acc)
  else
    print_bits_aux bs (n+1) acc)
End

Definition print_xor_string_def:
  print_xor_string s =
  let cs = FLAT (MAP bits_of_char (explode s)) in
  if LENGTH cs = 0 then «»
  else
    let h = HD cs in
    let bb = if h then « = 1» else « = 0» in
    let t = TL cs in
    (concatWith « + » (print_bits_aux t 1 []) ^ bb)
End

val res = translate print_bits_aux_def;
val res = translate print_xor_string_def;

Quote add_cakeml:
  fun xor_to_string r =
  print_xor_string
    (Word8Array.substring r 0 (Word8Array.length r))
End

Theorem xor_to_string_spec:
  app (p : 'ffi ffi_proj)
    ^(fetch_v "xor_to_string" (get_ml_prog_state()))
    [csv]
    (W8ARRAY csv cs)
    (POSTv v.
      W8ARRAY csv cs * &(∃s. STRING_TYPE s v))
Proof
  xcf "xor_to_string" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  asm_exists_tac>>rw[]>>
  metis_tac[]
QED

Definition tn_to_string_def:
  tn_to_string tn =
  let ls = toSortedAList (FST tn) in
  let ss = MAP (λ(k,v:num). toString k ^ « -> » ^ toString v) ls in
  concatWith « ; » ss
End

val res = translate spt_center_def;
val res = translate spt_right_def;
val res = translate spt_left_def;
val res = translate spts_to_alist_add_pause_def;
val res = translate spts_to_alist_aux_def;
val res = translate spts_to_alist_def;
val res = translate toSortedAList_def;
val res = translate tn_to_string_def;

(*** Checking that a derived XOR is trivial ***)

Quote add_cakeml:
  fun is_emp_xor_arr_aux lno tn arr n =
  if n > 0
  then
  let
  val n1 = n - 1 in
    if
      eq_w8z (Unsafe.w8sub arr n1)
    then
      is_emp_xor_arr_aux lno tn arr n1
    else
      let val s = xor_to_string arr
        val tns = tn_to_string tn in
      raise Fail (format_failure lno ("derived XOR not empty (=0), got (internal var): " ^ s ^ " variable map (input var -> internal var): " ^ tns))
      end
  end
  else ()
End

Theorem is_emp_xor_arr_aux_spec:
  ∀n nv.
  NUM lno lnov ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  NUM n nv ∧ n <= LENGTH cs ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_emp_xor_arr_aux" (get_ml_prog_state()))
    [lnov; tnv; csv; nv]
    (W8ARRAY csv cs)
    (POSTve
      (λv. W8ARRAY csv cs *
        &(is_emp_xor_list (TAKE n cs)))
      (λe.
          W8ARRAY csv cs *
         &(Fail_exn e ∧ ¬is_emp_xor_list (TAKE n cs))))
Proof
  Induct>>fs[is_emp_xor_list_def]>>rw[]>>
  xcf "is_emp_xor_arr_aux" (get_ml_prog_state ())
  >- (
    xlet_autop>>xif>>
    asm_exists_tac>>xsimpl>>
    xcon>>xsimpl)>>
  xlet_autop>>
  xif>>
  asm_exists_tac>>xsimpl>>
  rpt xlet_autop>>
  DEP_REWRITE_TAC[GSYM SNOC_EL_TAKE]>>
  fs[EXISTS_SNOC,EVERY_SNOC,eq_w8z_def]>>
  xif
  >-
    (xapp>>fs[]>>xsimpl)>>
  xlet_auto>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  fs[Fail_exn_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun is_xor_arr lno tn def fml is cfml cis s =
  let
    val r = Word8Array.array def bw0
    val r = strxor_c_arr r s
    val r = add_xors_aux_c_arr lno fml is r
    val r = unit_props_xor_arr lno cfml (fst tn) cis r
  in
    is_emp_xor_arr_aux lno tn r (Word8Array.length r)
  end
End

Theorem is_xor_arr_spec:
  NUM lno lnov ∧
  NUM def defv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE NUM) cls clsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) fmlls fmllsv ∧
  LIST_REL vcclause_TYPE cfmlls cfmllsv ∧
  strxor_TYPE s sv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_xor_arr" (get_ml_prog_state()))
    [lnov; tnv; defv; fmlv; lsv; cfmlv; clsv; sv]
    (ARRAY fmlv fmllsv * ARRAY cfmlv cfmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv * ARRAY cfmlv cfmllsv *
        &(is_xor_list def fmlls ls cfmlls cls (FST tn) s))
      (λe.
         ARRAY fmlv fmllsv * ARRAY cfmlv cfmllsv *
         &(Fail_exn e ∧ ¬is_xor_list def fmlls ls cfmlls cls (FST tn) s)))
Proof
  rw[]>>
  xcf "is_xor_arr" (get_ml_prog_state ())>>
  rw[is_xor_list_def]>>
  assume_tac bw0_v_thm>>
  rpt xlet_autop>>xsimpl>>
  gvs[unwrap_TYPE_def]>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>simp[]>>
  first_x_assum (irule_at Any)>>simp[]>>
  first_x_assum (irule_at Any)>>simp[]
QED

(*** Converting a raw XOR into a bitstring ***)

Quote add_cakeml:
  fun extend_s_arr s n =
  let val ls = Word8Array.length s in
  if n < ls
  then s
  else
  let
    val ss = Word8Array.array n bw0
    val u = Word8Array.copy s 0 ls ss 0
  in
    ss
  end
  end
End

Theorem extend_s_arr_spec:
  NUM n nv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extend_s_arr" (get_ml_prog_state()))
    [csv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(extend_s_list cs n = cs'))
Proof
  rw[]>>
  xcf "extend_s_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[extend_s_list_def]>>
  xif
  >-
    (xvar>>xsimpl)>>
  assume_tac bw0_v_thm>>
  rpt xlet_autop>>
  xvar>>xsimpl>>
  EVAL_TAC
QED

Quote add_cakeml:
  fun conv_xor_aux_arr s xs =
  case xs of [] => s
  | x::xs =>
  let
    val v = nabs x
    val s = extend_s_arr s (v div 8 + 1)
    val u = flip_bit_arr s v in
    if x > 0 then
      conv_xor_aux_arr s xs
    else
      (flip_bit_arr s 0;
      conv_xor_aux_arr s xs)
  end
End

Theorem conv_xor_aux_arr_spec:
  ∀xs xsv cs csv.
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_xor_aux_arr" (get_ml_prog_state()))
    [csv; xsv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(conv_xor_aux_list cs xs = cs'))
Proof
  Induct>>
  rw[]>>
  xcf "conv_xor_aux_arr" (get_ml_prog_state ())>>
  fs[conv_xor_aux_list_def,LIST_TYPE_def]>>xmatch
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  gvs[nabs_def]>>
  xlet_auto>>
  xlet_auto
  >- (
    qexists_tac`emp`>>xsimpl>>
    rw[extend_s_list_def])>>
  xlet_autop>>
  xif>>fs[]
  >- (xapp>>xsimpl)>>
  xlet_auto
  >- (
    qexists_tac`emp`>>xsimpl>>
    fs[flip_bit_list_def]>>
    rw[extend_s_list_def])>>
  xapp>>xsimpl
QED

Quote add_cakeml:
  fun conv_rawxor_arr mv x =
  let
    val r = Word8Array.array (max 1 mv) bw0
    val u = flip_bit_arr r 0
    val r = conv_xor_aux_arr r x
  in
    Word8Array.substring r 0 (Word8Array.length r)
  end
End

Theorem conv_rawxor_arr_spec:
  NUM n nv ∧
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_rawxor_arr" (get_ml_prog_state()))
    [nv; xsv]
    (emp)
    (POSTv v.
      &(strxor_TYPE (conv_rawxor_list n xs) v))
Proof
  rw[]>>
  xcf "conv_rawxor_arr" (get_ml_prog_state ())>>
  assume_tac bw0_v_thm>>
  xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  rpt xlet_auto>-
    xsimpl>>
  xapp>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  simp[conv_rawxor_list_def]>>
  rw[]>>
  `fromByte = (CHR o w2n)` by
    rw[FUN_EQ_THM,fromByte_def]>>
  simp[]
QED

Quote add_cakeml:
  fun strxor_imp_cclause_arr lno tn mv s c =
  let
    val t = conv_rawxor_arr mv c
    val res = strxor_c_arr s t
  in
    is_emp_xor_arr_aux lno tn res (Word8Array.length res)
  end
End

Theorem strxor_imp_cclause_arr_spec:
  NUM lno lnov ∧
  NUM n nv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_imp_cclause_arr" (get_ml_prog_state()))
    [lnov; tnv; nv; csv; xsv]
    (W8ARRAY csv cs)
    (POSTve
      (λv. &(strxor_imp_cclause_list n cs xs))
      (λe.
         &(Fail_exn e ∧ ¬strxor_imp_cclause_list n cs xs)))
Proof
  rw[]>>
  xcf "strxor_imp_cclause_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  xlet_autop>>
  xapp>>
  first_x_assum(irule_at Any)>>xsimpl>>
  gvs[strxor_imp_cclause_list_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun is_cfromx_arr lno tn def fml is c =
  let
    val r = Word8Array.array def bw0
    val res = add_xors_aux_c_arr lno fml is r
  in
    strxor_imp_cclause_arr lno tn def res c
  end
End

Theorem is_cfromx_arr_spec:
  NUM lno lnov ∧
  NUM def defv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) fmlls fmllsv ∧
  LIST_TYPE INT s sv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_cfromx_arr" (get_ml_prog_state()))
    [lnov; tnv; defv; fmlv; lsv; sv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(is_cfromx_list def fmlls ls s))
      (λe.
         ARRAY fmlv fmllsv *
         &(Fail_exn e ∧ ¬is_cfromx_list def fmlls ls s)))
Proof
  rw[]>>
  xcf "is_cfromx_arr" (get_ml_prog_state ())>>
  rw[is_cfromx_list_def]>>
  assume_tac bw0_v_thm>>
  rpt xlet_autop
  >-
    xsimpl>>
  TOP_CASE_TAC>>gvs[unwrap_TYPE_def]>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

(*** Deriving an XOR from clauses ***)

Quote add_cakeml:
  fun get_constrs_arr lno fml ls =
    case ls of
      [] => []
    | (i::is) =>
      if Array.length fml <= i then
        raise Fail (format_failure lno ("no clause/constraint at index: " ^ Int.toString i))
      else
        (let val ci = Unsafe.sub fml i in
          if Vector.length ci = 1 andalso int_eq_0 (uvsub ci 0) then
            raise Fail (format_failure lno ("no clause/constraint at index (maybe deleted): " ^ Int.toString i))
          else
            Vector.toList ci :: get_constrs_arr lno fml is
        end)
End

Theorem get_constrs_arr_spec:
  ∀ls lsv fmlv fmlls fml lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_constrs_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &unwrap_TYPE
          (LIST_TYPE (LIST_TYPE INT))
          (get_constrs_list fmlls ls) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ get_constrs_list fmlls ls = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "get_constrs_arr" (get_ml_prog_state ())>>
  simp[get_constrs_list_def]
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl>>
    simp[unwrap_TYPE_def,LIST_TYPE_def])>>
  fs[LIST_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  drule LIST_REL_LENGTH>> simp[]>>
  strip_tac>>
  xif
  >- (
    rpt (xlet_autop)>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def,any_el_ALT,unwrap_TYPE_def]>>
    metis_tac[])>>
  gvs[]>>
  `vcclause_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  gvs[any_el_ALT]>>
  rpt xlet_autop>>
  xlet`POSTv bb.
    ARRAY fmlv fmllsv *
    &BOOL (length (EL h fmlls) = 1 ∧ sub (EL h fmlls) 0 = 0) bb`
  >- (
    xlog>>
    reverse IF_CASES_TAC>>gvs[]
    >- xsimpl>>
    xlet_auto
    >- (xsimpl>>gvs[uvsub_side_def])>>
    xapp>>
    xsimpl>>
    qexists_tac`sub (EL h fmlls) 0`>>
    simp[int_eq_0_def])>>
  xif
  >- (
    `EL h fmlls = vcc_none` by metis_tac[is_vcc_none]>>
    gvs[]>>
    rpt(xlet_autop)>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  `EL h fmlls ≠ vcc_none` by metis_tac[is_vcc_none]>>
  gvs[]>>
  xlet_autop
  >- (
    xsimpl>>rw[]>>gvs[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  xlet_autop>>
  xcon>>xsimpl>>
  gvs[LIST_TYPE_def]
QED

val res = translate clauses_from_rawxor_def;
val res = translate (imp_cclause_def |> SIMP_RULE std_ss [MEMBER_INTRO]);
val res = translate check_rawxor_imp_def;

Quote add_cakeml:
  fun is_xfromc_arr lno fml is rx =
  let val ds = get_constrs_arr lno fml is in
    if check_rawxor_imp ds rx then ()
    else raise Fail
      (format_failure lno ("clauses do not imply XOR"))
  end
End

Theorem is_xfromc_arr_spec:
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_TYPE INT rx rxv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_xfromc_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; rxv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(is_xfromc_list fmlls ls rx))
      (λe.
         ARRAY fmlv fmllsv *
         &(Fail_exn e ∧ ¬is_xfromc_list fmlls ls rx)))
Proof
  rw[]>>
  xcf "is_xfromc_arr" (get_ml_prog_state ())>>
  simp[is_xfromc_list_def]>>
  xlet_autop
  >- xsimpl>>
  TOP_CASE_TAC>>fs[unwrap_TYPE_def]>>
  xlet_autop>>
  xif
  >-
    (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  fs[Fail_exn_def]>>
  metis_tac[]
QED

Definition map_to_ilit_def:
  map_to_ilit ls = MAP to_ilit ls
End

val r = translate to_ilit_def;
val r = translate map_to_ilit_def;

Quote add_cakeml:
  fun conv_xor_mv_arr mv x =
  conv_rawxor_arr mv (map_to_ilit x)
End

Theorem conv_xor_mv_arr_spec:
  NUM n nv ∧
  LIST_TYPE (CNF_LIT_TYPE NUM) xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_xor_mv_arr" (get_ml_prog_state()))
    [nv; xsv]
    (emp)
    (POSTv v.
      &(strxor_TYPE (conv_xor_mv_list n xs) v))
Proof
  rw[]>>
  xcf "conv_xor_mv_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  fs[conv_xor_mv_list_def,map_to_ilit_def]>>
  metis_tac[]
QED

Definition ren_lits_def:
  ren_lits tn rx = ren_lit_ls tn rx []
End

val res = translate get_name_def;
val res = translate ren_lit_ls_def;
val res = translate ren_lits_def;

Definition ren_ints_def:
  ren_ints tn rx = ren_int_ls tn rx []
End

val res = translate ren_int_ls_def;
val res = translate ren_ints_def;

(*** Deletion from the XOR store.

  The clause array marks a free slot with vcc_none, so cnf/array's
  delete_arr writes that sentinel; an XOR slot is an option, so it needs
  its own deletion writing None. ***)

Quote add_cakeml:
  fun xdelete_arr fml i =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i None)
End

Theorem xdelete_arr_spec:
  NUM i iv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "xdelete_arr" (get_ml_prog_state()))
    [fmlv; iv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE strxor_TYPE) (xdelete_list fmlls i) fmllsv') )
Proof
  rw[]>>
  xcf "xdelete_arr" (get_ml_prog_state ())>>
  simp[xdelete_list_def]>>
  rpt xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xif>-(xcon>>xsimpl)>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &OPTION_TYPE strxor_TYPE NONE v`
  >- (xcon>>xsimpl>>simp[OPTION_TYPE_def])>>
  simp[]>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[]
QED

Quote add_cakeml:
  fun xdelete_ids_arr fml ls =
    case ls of
      [] => ()
    | (i::is) =>
      (xdelete_arr fml i; xdelete_ids_arr fml is)
End

Theorem xdelete_ids_arr_spec:
  ∀ls lsv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "xdelete_ids_arr" (get_ml_prog_state()))
    [fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE strxor_TYPE) (xdelete_ids_list fmlls ls) fmllsv') )
Proof
  Induct>>
  rw[]>>fs[xdelete_ids_list_def]>>
  xcf "xdelete_ids_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl) >>
  xlet_autop>>
  xapp>>
  xsimpl
QED

(*** One checker step ***)

Quote add_cakeml:
  fun check_xlrup_arr lno xorig xlrup cfml xfml tn def carr b =
  case xlrup of
    Del cl =>
      (delete_ids_arr cfml cl; (cfml, xfml, tn, def, carr, b))
  | Rup n c i0 =>
      (case is_rup_arr lno cfml carr b c i0 of (carr,b) =>
        (insert_clause_arr cfml n c, xfml, tn, def, carr, b))
  | Xorig n rx =>
      if List.member rx xorig
      then
      (case ren_lits tn rx of (mx,tn) =>
      let
        val x = conv_xor_mv_arr def mx
      in
        (cfml, Array.updateResize xfml None n (Some x),
          tn, max def (String.size x), carr, b)
      end)
      else
        raise Fail (format_failure lno "unable to find original XOR")
  | Xadd n rx i0 i1 =>
      (case ren_ints tn rx of (mx,tn) =>
      let
        val x = conv_rawxor_arr def mx
        val u = is_xor_arr lno tn def xfml i0 cfml i1 x
      in
        (cfml, Array.updateResize xfml None n (Some x),
          tn, max def (String.size x), carr, b)
      end)
  | Xdel xl =>
      (xdelete_ids_arr xfml xl; (cfml, xfml, tn, def, carr, b))
  | Cfromx n c i0 =>
    (case ren_ints tn c of (mc,tn) =>
    let val u = is_cfromx_arr lno tn def xfml i0 mc
        val v = Vector.fromList c in
      case resize_dm carr b v of (carr,b) =>
        (insert_clause_arr cfml n v, xfml, tn, def, carr, b)
    end)
  | Xfromc n rx i0 =>
    let val u = is_xfromc_arr lno cfml i0 rx
    in
      case ren_ints tn rx of (mx,tn) =>
      let val x = conv_rawxor_arr def mx in
        (cfml, Array.updateResize xfml None n (Some x),
            tn, max def (String.size x), carr, b)
      end
    end
End

val XLRUP_XLRUP_TYPE_def = fetch "-" "XLRUP_XLRUP_TYPE_def";

Theorem check_xlrup_arr_spec:
  NUM lno lnov ∧
  XLRUP_XLRUP_TYPE xlrup xlrupv ∧
  LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM)) xorig xorigv ∧
  LIST_REL vcclause_TYPE cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls xfmllsv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  NUM def defv ∧
  WORD8 b bv ∧
  bnd_fml cfmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_xlrup_arr" (get_ml_prog_state()))
    [lnov; xorigv; xlrupv; cfmlv; xfmlv; tnv; defv; Carrv; bv]
    (ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3 v4 v5 v6.
          &(v = Conv NONE [v1; v2; v3; v4; v5; v6]) *
          (SEP_EXISTS cfmllsv' xfmllsv' clist'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            W8ARRAY v5 clist' *
            &(
            case check_xlrup_list xorig xlrup cfmlls xfmlls tn def Clist b of
              NONE => F
            | SOME (cfmlls', xfmlls', tn', def', Clist', b') =>
                bnd_fml cfmlls' (LENGTH Clist') ∧
                LIST_REL vcclause_TYPE cfmlls' cfmllsv' ∧
                LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls' xfmllsv' ∧
                PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn' v3 ∧
                NUM def' v4 ∧
                WORD8 b' v6 ∧
                Clist' = clist'
            ))
      )
      (λe. ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
        &(Fail_exn e ∧
        check_xlrup_list xorig xlrup cfmlls xfmlls tn def Clist b = NONE)))
Proof
  rw[check_xlrup_list_def]>>
  xcf "check_xlrup_arr" (get_ml_prog_state ())>>
  Cases_on`xlrup`>>fs[XLRUP_XLRUP_TYPE_def]
  >- suspend "Del"
  >- suspend "RUP"
  >- suspend "XOrig"
  >- suspend "XAdd"
  >- suspend "XDel"
  >- suspend "CFromX"
  >- suspend "XFromC"
QED

Resume check_xlrup_arr_spec[Del]:
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl>>
  metis_tac[bnd_fml_delete_ids_list]
QED

Resume check_xlrup_arr_spec[RUP]:
  xmatch>>
  xlet `
    POSTve
      (λres.
           (SEP_EXISTS b' Carrv' Clist'.
              W8ARRAY Carrv' Clist' *
              &(PAIR_TYPE $= WORD8 (Carrv',b') res ∧
               is_rup_list cfmlls Clist b v l = (T,Clist',b'))) *
           ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv)
      (λe.
          ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
          &(Fail_exn e ∧ ¬FST (is_rup_list cfmlls Clist b v l)))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[PAIR_TYPE_def]>>rw[]>>
    xsimpl)
  >- (
    xsimpl>>
    simp[AllCaseEqs()]>>
    Cases_on`is_rup_list cfmlls Clist b v l`>>simp[])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  irule bnd_fml_insert_vcc_list>>
  metis_tac[bnd_fml_is_rup_list]
QED

Resume check_xlrup_arr_spec[XOrig]:
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    match_mp_tac EqualityType_LIST_TYPE>>
    simp[EqualityType_CNF_LIT_TYPE])>>
  fs[MEMBER_INTRO]>>
  reverse xif
  >- (
    xsimpl>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    rw[]>>xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  fs[PAIR_TYPE_SPLIT]>> xmatch>>
  rpt xlet_autop>>
  gvs[ren_lits_def]>>
  xcon>>xsimpl>>
  irule LIST_REL_update_resize>>
  simp[OPTION_TYPE_def]
QED

Resume check_xlrup_arr_spec[XAdd]:
  xmatch>>
  xlet_autop>>
  fs[PAIR_TYPE_SPLIT]>> xmatch>>
  xlet_autop>>
  pairarg_tac>>gvs[ren_ints_def]>>
  qmatch_asmsub_rename_tac`ren_int_ls _ l [] = (mX,tn1,tn2)`>>
  (* xlet_auto picks the wrong frame here *)
  xlet`POSTve
  (λv.
       ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
       W8ARRAY Carrv Clist *
       &is_xor_list def xfmlls l0 cfmlls l1 tn1 (conv_rawxor_list def mX))
  (λe.
       ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
       &(Fail_exn e ∧
        ¬is_xor_list def xfmlls l0 cfmlls l1 tn1 (conv_rawxor_list def mX)))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[PAIR_TYPE_SPLIT,PULL_EXISTS]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[])
  >-
    xsimpl>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  irule LIST_REL_update_resize>>
  simp[OPTION_TYPE_def]
QED

Resume check_xlrup_arr_spec[XDel]:
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl
QED

Resume check_xlrup_arr_spec[CFromX]:
  xmatch>>
  xlet_autop>>
  fs[PAIR_TYPE_SPLIT]>> xmatch>>
  pairarg_tac>>gvs[ren_ints_def]>>
  qmatch_asmsub_rename_tac`ren_int_ls _ l [] = (mc,tn1,tn2)`>>
  xlet`POSTve
      (λv.
           ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
           W8ARRAY Carrv Clist *
           &is_cfromx_list def xfmlls l0 mc)
      (λe.
           ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
           &(Fail_exn e ∧ ¬is_cfromx_list def xfmlls l0 mc))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[]>>
    metis_tac[PAIR_TYPE_def])
  >- xsimpl>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    rw[]>>metis_tac[W8ARRAY_refl])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  metis_tac[bnd_fml_insert_vcc_list_resize_dm]
QED

Resume check_xlrup_arr_spec[XFromC]:
  xmatch>>
  xlet`POSTve
    (λv.
         ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
         W8ARRAY Carrv Clist *
         &is_xfromc_list cfmlls l0 l)
    (λe.
         ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
         &(Fail_exn e ∧ ¬is_xfromc_list cfmlls l0 l))`
  >- (
    xapp>>xsimpl>>
    metis_tac[])
  >- xsimpl>>
  xlet_autop>>
  gvs[PAIR_TYPE_SPLIT]>>
  pairarg_tac>>gvs[ren_ints_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  irule LIST_REL_update_resize>>
  simp[OPTION_TYPE_def]
QED

Finalise check_xlrup_arr_spec;

(*** Parsing.

  blanks, tokenize_fast, is_int, fromString_unsafe, parse_until_zero(_nn),
  starts_with and mk_lit are already translated in ccnf_parseProg. ***)

val _ = translate parse_rup_def;
val _ = translate parse_until_c_zero_nn_def;
val _ = translate parse_u_rest_def;
val _ = translate parse_id_rest_def;
val _ = translate parse_id_u_rest_def;
val _ = translate parse_rup_del_def;
val _ = translate parse_xadd_xdel_def;
val _ = translate parse_imply_def;
val _ = translate parse_xor_nomv_def;
val _ = translate parse_orig_def;
val _ = translate parse_xlrup_def;

Definition parse_and_run_list_def:
  parse_and_run_list xorig cfml xfml tn def Clist b l =
  case parse_xlrup l of
    NONE => NONE
  | SOME xlrup =>
    check_xlrup_list xorig xlrup cfml xfml tn def Clist b
End

Quote add_cakeml:
  fun parse_and_run_arr lno xorig cfml xfml tn def carr b l =
  case parse_xlrup l of
    None => raise Fail (format_failure lno "failed to parse line")
  | Some xlrup =>
    check_xlrup_arr lno xorig xlrup cfml xfml tn def carr b
End

Theorem parse_and_run_arr_spec:
  NUM lno lnov ∧
  LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM)) xorig xorigv ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) l lv ∧
  LIST_REL vcclause_TYPE cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls xfmllsv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  NUM def defv ∧
  WORD8 b bv ∧
  bnd_fml cfmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_and_run_arr" (get_ml_prog_state()))
    [lnov; xorigv; cfmlv; xfmlv; tnv; defv; Carrv; bv; lv]
    (ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3 v4 v5 v6.
          &(v = Conv NONE [v1; v2; v3; v4; v5; v6]) *
          (SEP_EXISTS cfmllsv' xfmllsv' clist'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            W8ARRAY v5 clist' *
            &(
            case parse_and_run_list xorig cfmlls xfmlls tn def Clist b l of
              NONE => F
            | SOME (cfmlls', xfmlls', tn', def', Clist', b') =>
                bnd_fml cfmlls' (LENGTH Clist') ∧
                LIST_REL vcclause_TYPE cfmlls' cfmllsv' ∧
                LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls' xfmllsv' ∧
                PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn' v3 ∧
                NUM def' v4 ∧
                WORD8 b' v6 ∧
                Clist' = clist'
            ))
      )
      (λe. ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
        &(Fail_exn e ∧
        parse_and_run_list xorig cfmlls xfmlls tn def Clist b l = NONE)))
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  fs[OPTION_TYPE_SPLIT]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[unwrap_TYPE_def,Fail_exn_def]>>
    metis_tac[])>>
  xapp>>fs[]>>
  metis_tac[]
QED

(*** Reading and checking a proof file, line by line ***)

Quote add_cakeml:
  fun check_unsat'' fd lno xorig cfml xfml tn def carr b =
    case TextIO.inputLineTokens #"\n" fd blanks tokenize_fast of
      None => (cfml, xfml)
    | Some l =>
    case parse_and_run_arr lno xorig cfml xfml tn def carr b l of
      (cfml',xfml',tn',def',carr',b') =>
      check_unsat'' fd (lno+1) xorig cfml' xfml' tn' def' carr' b'
End

Definition parse_and_run_file_list_def:
  (parse_and_run_file_list [] xorig cfml xfml tn def Clist b =
    SOME (cfml, xfml)) ∧
  (parse_and_run_file_list (x::xs) xorig cfml xfml tn def Clist b =
    case parse_and_run_list xorig cfml xfml tn def Clist b (toks_fast x) of
      NONE => NONE
    | SOME (cfml', xfml', tn', def', Clist', b') =>
    parse_and_run_file_list xs xorig cfml' xfml' tn' def' Clist' b')
End

Theorem parse_and_run_file_list_eq:
  ∀ls xorig cfml xfml tn def Clist b.
  parse_and_run_file_list ls xorig cfml xfml tn def Clist b =
  case parse_xlrups ls of
    NONE => NONE
  | SOME xlrups =>
    OPTION_MAP (λ(cfml,xfml,rest). (cfml,xfml))
      (check_xlrups_list xorig xlrups cfml xfml tn def Clist b)
Proof
  Induct>>
  fs[parse_and_run_list_def,parse_xlrups_def,parse_and_run_file_list_def,
    check_xlrups_list_def]>>
  rw[]>>
  every_case_tac>>fs[toks_fast_def]>>
  simp[check_xlrups_list_def]
QED

val blanks_v_thm = fetch "ccnf_parseProg" "blanks_v_thm";
val tokenize_fast_v_thm = fetch "ccnf_parseProg" "tokenize_fast_v_thm";

val inputLineTokens_fast_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Theorem check_unsat''_spec:
  !lines fs cfmlv cfmlls cfmllsv xfmlv xfmlls xfmllsv
    Clist Carrv lno lnov tn tnv def defv b bv
    xorig xorigv.
  NUM lno lnov ∧
  LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM)) xorig xorigv ∧
  LIST_REL vcclause_TYPE cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls xfmllsv ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  NUM def defv ∧
  WORD8 b bv ∧
  bnd_fml cfmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; xorigv; cfmlv; xfmlv; tnv; defv; Carrv; bv]
    (STDIO fs * ARRAY cfmlv cfmllsv *
      ARRAY xfmlv xfmllsv *
      W8ARRAY Carrv Clist * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k v1 v2.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
           &(v = Conv NONE [v1; v2]) *
           (SEP_EXISTS cfmllsv' xfmllsv'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            &(unwrap_TYPE
              (λv fv.
              LIST_REL vcclause_TYPE (FST v) fv)
                (parse_and_run_file_list lines xorig
                  cfmlls xfmlls tn def Clist b) cfmllsv' ∧
              unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE strxor_TYPE) (SND v) fv)
                 (parse_and_run_file_list lines xorig
                  cfmlls xfmlls tn def Clist b) xfmllsv'
              ))
      )
      (λe.
         SEP_EXISTS k cfmlv cfmllsv xfmlv xfmllsv lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           ARRAY cfmlv cfmllsv *
           ARRAY xfmlv xfmllsv *
           &(Fail_exn e ∧
             parse_and_run_file_list lines xorig
               cfmlls xfmlls tn def Clist b = NONE)))
Proof
  Induct>>rw []>>
  xcf "check_unsat''" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY cfmlv cfmllsv *
                ARRAY xfmlv xfmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec inputLineTokens_fast_specialize>>
      qexists_tac ‘ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist’>>
      qexists_tac ‘[]’>>
      qexists_tac ‘fs’>>
      qexists_tac ‘fd’>>xsimpl>>fs []>>
      rw []>>qexists_tac ‘x’>>xsimpl>>
      fs[OPTION_TYPE_def])>>
    fs [std_preludeTheory.OPTION_TYPE_def]>>rveq>>fs []>>
    xmatch>>fs []>>
    xcon>>xsimpl>>
    fs [parse_and_run_file_list_def]>>
    qexists_tac ‘k’>>xsimpl>>
    fs [unwrap_TYPE_def])>>
  xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY cfmlv cfmllsv *
                ARRAY xfmlv xfmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
    >- (
      xapp_spec inputLineTokens_fast_specialize>>
      qexists_tac ‘ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist’>>
      qexists_tac ‘h::lines’>>
      qexists_tac ‘fs’>>
      qexists_tac ‘fd’>>xsimpl>>fs []>>
      rw []>>qexists_tac ‘x’>>xsimpl>>
      simp[toks_fast_def])>>
  fs [std_preludeTheory.OPTION_TYPE_def]>>rveq>>fs []>>
  xmatch>>fs []>>
  xlet_auto >- (
    xsimpl>>simp[unwrap_TYPE_def]>>rw[]>>
    qexists_tac`x`>> qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[parse_and_run_file_list_def]>>
    xsimpl>>
    rw[]>>
    qexists_tac ‘k’>>
    qexists_tac`cfmlv`>>qexists_tac`cfmllsv`>>
    qexists_tac`xfmlv`>>qexists_tac`xfmllsv`>>
    xsimpl>>
    qexists_tac ‘lines’>>
    xsimpl>>
    metis_tac[])>>
  rveq>>fs [] >>
  every_case_tac>>gvs[]>>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  fs [unwrap_TYPE_def]>>
  rpt(first_x_assum (irule_at Any))>>
  xsimpl>>
  qexists_tac ‘(forwardFD fs fd k)’>> xsimpl>>
  simp[parse_and_run_file_list_def]>>
  every_case_tac>> gvs[]>>
  rw[]>>gvs[forwardFD_o]
  >-
    (qexists_tac`k+x`>>xsimpl>>metis_tac[])>>
  qexists_tac ‘k+x’>>xsimpl >>
  rename1`INSTREAM_LINES _ _ _ A _ * ARRAY a1 a2 * ARRAY b1 b2 `>>
  qexists_tac`a1`>>
  qexists_tac`a2`>>
  qexists_tac`b1`>>
  qexists_tac`b2`>>
  qexists_tac`A`>>
  xsimpl
QED

(*** The file-level entry point ***)

Quote add_cakeml:
  fun check_unsat' xorig cfml xfml tn def fname n =
  let
    val fd = TextIO.openIn fname
    val carr = Word8Array.array n bw0
    val chk = Inr (check_unsat'' fd 1 xorig cfml xfml tn def carr bw1)
      handle Fail s => Inl s
    val close = TextIO.closeIn fd;
  in
    case chk of
      Inl s => Inl s
    | Inr res =>
      (case res of (cfml', xfml') =>
      Inr (contains_emp_arr cfml'))
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

val bw1_v_thm = fetch "ccnf_arrayProg" "bw1_v_thm";

Theorem check_unsat'_spec:
  NUM n nv ∧
  LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM)) xorig xorigv ∧
  LIST_REL vcclause_TYPE cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls xfmllsv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  PAIR_TYPE (SPTREE_SPT_TYPE NUM) NUM tn tnv ∧
  NUM def defv ∧
  bnd_fml cfmlls n
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [xorigv; cfmlv; xfmlv; tnv; defv; fv; nv]
  (STDIO fs * ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE BOOL)
      (if inFS_fname fs f then
        (case parse_xlrups (all_lines_file fs f) of
         SOME xlrup =>
           (case check_xlrups_list xorig xlrup
             cfmlls xfmlls tn def (REPLICATE n 0w) 1w of
             NONE => INL err
           | SOME (cfml', xfml') =>
            INR (contains_emp_list cfml'))
        | NONE => INL err)
      else
        INL err
      ) v)
Proof
  rw[]>>
  xcf"check_unsat'"(get_ml_prog_state()) >>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs *
      ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec)>>xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>xsimpl >>
  assume_tac bw0_v_thm >>
  assume_tac bw1_v_thm >>
  xlet_autop >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qabbrev_tac`Clist = REPLICATE n (0w:word8)`>>
  xlet`POSTv resv.
   SEP_EXISTS v0 v1 v2 cfmllsv' cfmlv' xfmllsv' xfmlv' k rest.
    STDIO (forwardFD fss (nextFD fs) k) *
    INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
    ARRAY cfmlv' cfmllsv' *
    ARRAY xfmlv' xfmllsv' *
    &(
      case
        parse_and_run_file_list (all_lines_file fs f) xorig
          cfmlls xfmlls tn def (REPLICATE n 0w) 1w
      of
        NONE => resv =
          Conv (SOME (TypeStamp «Inl» 4)) [v0] ∧ ∃s. STRING_TYPE s v0
      | SOME(cfmlls',xfmlls') =>
        resv = Conv (SOME (TypeStamp «Inr» 4)) [Conv NONE [v1; v2]] ∧
        v1 = cfmlv' ∧
        v2 = xfmlv' ∧
        LIST_REL vcclause_TYPE cfmlls' cfmllsv' ∧
        LIST_REL (OPTION_TYPE strxor_TYPE) xfmlls' xfmllsv'
    )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS cfmlv cfmllsv xfmlv xfmllsv rest k.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY cfmlv cfmllsv *
          ARRAY xfmlv xfmllsv *
          &(Fail_exn e ∧ parse_and_run_file_list (all_lines_file fs f) xorig
            cfmlls xfmlls tn def Clist 1w = NONE)`
      >- (
        xlet `POSTe e.
         SEP_EXISTS k cfmlv cfmllsv xfmlv xfmllsv lines'.
           STDIO (forwardFD fss (nextFD fs) k) *
           INSTREAM_LINES #"\n" (nextFD fs) is lines' (forwardFD fss (nextFD fs) k) *
           ARRAY cfmlv cfmllsv *
           ARRAY xfmlv xfmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list (all_lines_file fs f) xorig
            cfmlls xfmlls tn def Clist 1w = NONE)`
        >-
         (xapp_spec check_unsat''_spec>>
          xsimpl>>
          rpt (first_x_assum (irule_at Any))>>
          xsimpl>>fs [Abbr`Clist`]>>
          qexists_tac `all_lines_file fs f`>>
          qexists_tac `fss`>>
          qexists_tac `nextFD fs`>>
          qexists_tac `emp`>>
          xsimpl>>fs [unwrap_TYPE_def]>>
          rw[]>>
          qexists_tac `x`>>
          rename [`_ * INSTREAM_LINES _ _ _ xxx _ * ARRAY a1 a2 * ARRAY b1 b2`]>>
          qexists_tac `a1`>>
          qexists_tac `a2`>>
          qexists_tac `b1`>>
          qexists_tac `b2`>>
          qexists_tac `xxx`>>
          xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`_ * INSTREAM_LINES _ _ _ xxx _ * ARRAY a1 a2 * ARRAY b1 b2`]>>
        qexists_tac `a1`>>
        qexists_tac `a2`>>
        qexists_tac `b1`>>
        qexists_tac `b2`>>
        qexists_tac `xxx`>>
        qexists_tac `x`>>
        xsimpl)>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`_ * _ * ARRAY a1 a2 * ARRAY b1 b2`]>>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      qexists_tac `b2` >>
      qexists_tac `b1` >>
      qexists_tac `k` >>
      qexists_tac `rest` >> xsimpl) >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fss (nextFD fs) k) *
         INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
         &(v = Conv (SOME (TypeStamp «Inr» 4)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS cfmllsv' xfmllsv'.
           ARRAY v1 cfmllsv' *
           ARRAY v2 xfmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL vcclause_TYPE (FST v) fv)
                (parse_and_run_file_list (all_lines_file fs f) xorig
                  cfmlls xfmlls tn def Clist 1w) cfmllsv' ∧
             unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE strxor_TYPE) (SND v) fv)
                (parse_and_run_file_list (all_lines_file fs f) xorig
                  cfmlls xfmlls tn def Clist 1w) xfmllsv'
            )))`
    >- (
      xlet `POSTv v.
         SEP_EXISTS k v1 v2.
             STDIO (forwardFD fss (nextFD fs) k) *
             INSTREAM_LINES #"\n" (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
             &(v = Conv NONE [v1; v2]) *
             (SEP_EXISTS cfmllsv' xfmllsv'.
                  ARRAY v1 cfmllsv' *
                  ARRAY v2 xfmllsv' *
                  &(unwrap_TYPE
                    (λv fv.
                         LIST_REL vcclause_TYPE
                           (FST v) fv)
                      (parse_and_run_file_list (all_lines_file fs f) xorig
                        cfmlls xfmlls tn def Clist 1w) cfmllsv' ∧
                    unwrap_TYPE
                    (λv fv.
                         LIST_REL (OPTION_TYPE strxor_TYPE)
                           (SND v) fv)
                      (parse_and_run_file_list (all_lines_file fs f) xorig
                        cfmlls xfmlls tn def Clist 1w) xfmllsv'
                    ))`
      >-
       (xapp_spec check_unsat''_spec>>
        xsimpl>>
        rpt (first_x_assum (irule_at Any))>>
        xsimpl>>fs [Abbr`Clist`]>>
        qexists_tac `all_lines_file fs f`>>
        qexists_tac `fss`>>
        qexists_tac `nextFD fs`>>
        qexists_tac `emp`>>
        xsimpl>>fs [unwrap_TYPE_def]>>
        rpt strip_tac>>
        qexists_tac `x'`>>
        xsimpl) >>
      fs[unwrap_TYPE_def]>>
      xcon >>
      xsimpl>>
      rename [`forwardFD _ _ k`]>>qexists_tac `k` >>
      rename [`INSTREAM_LINES _ _ _ rr`]>>qexists_tac `rr`>>
      xsimpl>>gvs []) >>
      xsimpl>>simp[unwrap_TYPE_def]>>
      PairCases_on`x`>>fs[]>>rw[]>>xsimpl >>
      rename [`forwardFD _ _ kk`]>>qexists_tac `kk` >>
      rename [`INSTREAM_LINES _ _ _ rr`]>>qexists_tac `rr`>>xsimpl)>>
  qspecl_then [`all_lines_file fs f`,`xorig`,`cfmlls`,`xfmlls`,`tn`,`def`,`Clist`,`1w`]
    strip_assume_tac parse_and_run_file_list_eq>>
  gs[]>>rw[]>>
  pop_assum kall_tac >>
  xlet `POSTv v. STDIO fs *
    ARRAY cfmlv' cfmllsv' * ARRAY xfmlv' xfmllsv'`
  >-
   (xapp_spec closeIn_spec_lines >>
    rename [`_ * _ * ARRAY a1 a2 * ARRAY b1 b2`] >>
    qexists_tac `ARRAY a1 a2 * ARRAY b1 b2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fss (nextFD fs) k` >>
    qexists_tac `nextFD fs` >>
    qexists_tac `#"\n"` >>
    conj_tac >-
     (fs [forwardFD_def,Abbr`fss`]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs []) >>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by
      (simp[validFileFD_forwardFD]>> simp[Abbr`fss`]>>
       imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
       match_mp_tac validFileFD_nextFD>>fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`]>>xsimpl) >>
  Cases_on`parse_xlrups (all_lines_file fs f)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon >> xsimpl >>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  TOP_CASE_TAC>> fs[]
  >- (
    xmatch >> xcon >>
    xsimpl>> simp[SUM_TYPE_def] >> metis_tac[])>>
  PairCases_on`x'`>>gvs[]>>
  xmatch >> fs[]>>
  xmatch >> fs[]>>
  xlet_autop>>
  xcon >> xsimpl>>
  simp[SUM_TYPE_def] >> gvs[]
QED

(*** The array-level soundness theorem ***)

