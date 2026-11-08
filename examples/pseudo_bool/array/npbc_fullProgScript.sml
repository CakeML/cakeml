(*
  Add PBF parsing and wrap around the PBP parser
*)
Theory npbc_fullProg
Ancestors
  basis_ffi pb_parse pbc_normalise name_table npbc_parseProg mlint
Libs
  preamble basis

val _ = translation_extends"npbc_parseProg";

(* Translation for parsing an OPB file *)
val r = translate (nocomment_line_def |> REWRITE_RULE [strlen_small]);

Theorem nocomment_line_side[local]:
  ∀l. nocomment_line_side l ⇔ T
Proof
  rw[fetch "-" "nocomment_line_side_def",smallnum_lt_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val _ = nocomment_line_side |> update_precondition;

val r = translate parse_constraint_def;
val r = translate parse_annot_def;
val r = translate parse_annot_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_obj_def;
val r = translate parse_obj_maybe_def;
val r = translate parse_var_raw_def;
val r = translate parse_vars_raw_def;
val r = translate parse_pres_def;
val r = translate parse_pres_maybe_def;
val r = translate parse_obj_pres_maybe_def;
val r = translate parse_pbf_toks_def;

Definition noparse_string_def:
  noparse_string f s = concat[«c Input file: »;f;« unable to parse in format: »; s;«\n»]
End

val r = translate noparse_string_def;

Quote add_cakeml:
  fun parse_pbf_full f =
  (case TextIO.inputAllTokensFile #"\n" f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some res => Inr res
  ))
End

val inputAllTokensFile_spec_specialize =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm] ;

Definition get_annot_fml_def:
  get_annot_fml fs f =
  if inFS_fname fs f then
    parse_pbf (all_lines_file fs f)
  else NONE
End

Theorem parse_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE annot_prob_TYPE)
    (case get_annot_fml fs f of
      NONE => INL err
    | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_pbf_full"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize o tokens blanks) (all_lines_file fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec inputAllTokensFile_spec_specialize >>
    xsimpl>>
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_annot_fml_def]>>
  IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      metis_tac[toks_def,ETA_AX,o_DEF]>>
    rw[parse_pbf_def]>>
    qmatch_goalsub_abbrev_tac`option_CASE AAA`>>
    Cases_on`AAA`>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
    xmatch>>
    xcon>>
    xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]>>metis_tac[]
QED

Definition int_inf_to_string_def:
  (int_inf_to_string NONE = «INF») ∧
  (int_inf_to_string (SOME (i:int)) =
    toString i)
End

Definition concl_to_string_def:
  (concl_to_string NoConcl = «s VERIFIED NO CONCLUSION\n») ∧
  (concl_to_string DSat = «s VERIFIED SATISFIABLE\n») ∧
  (concl_to_string DUnsat = «s VERIFIED UNSATISFIABLE\n») ∧
  (concl_to_string (OBounds lbi ubi) =
    let lbs = int_inf_to_string lbi in
    let ubs = int_inf_to_string ubi in
    «s VERIFIED BOUNDS » ^ lbs ^ « <= obj <= » ^ ubs ^ «\n») ∧
  (concl_to_string (EEnum n b) =
    if b
    then
      «s VERIFIED COMPLETE ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»
    else
      «s VERIFIED PARTIAL ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»)
End

Definition get_fml_def:
  get_fml fs f =
  OPTION_MAP strip_annot_prob (get_annot_fml fs f)
End

(* Parsing an OPB file one line at a time, numbering and normalising each
  constraint as it is read *)
val r = translate_no_ind (skip_annot_def |> REWRITE_RULE [strlen_small]);

Theorem skip_annot_ind_small[local]:
  skip_annot_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "skip_annot_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac pb_parseTheory.skip_annot_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[strlen_small]
QED

val _ = skip_annot_ind_small |> update_precondition;

Theorem skip_annot_side[local]:
  ∀line. skip_annot_side line ⇔ T
Proof
  ho_match_mp_tac skip_annot_ind>>
  rw[]>>
  simp[Once (fetch "-" "skip_annot_side_def")]>>
  rw[smallnum_lt_str_def,semanticPrimitivesTheory.index_in_bounds_def]>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

val _ = skip_annot_side |> update_precondition;

Definition noparse_line_string_def:
  noparse_line_string f (lno:num) =
  noparse_string f («OPB, line » ^ toString lno)
End

val r = translate noparse_line_string_def;

Overload "nprob_TYPE" = ``
  PAIR_TYPE pres_TYPE (PAIR_TYPE obj_TYPE
    (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM))``

(* The parsed problem with its constraints stored, and their largest
  variable *)
Definition enc_prob_def:
  enc_prob ((pres,obj,fml):
    num_set option # ((int # num) list # int) option # npbc list) =
  (pres,obj,enc_list fml,max_var_list fml 0)
End

(* Stores the new constraints in front of acc; also returns the largest of
  mx and their variables *)
Definition app_enc_mv_def:
  (app_enc_mv [] acc (mx:num) = (acc,mx)) ∧
  (app_enc_mv (c::cs) acc mx =
    let (s,m) = enc_mv c T in
    let (ss,mx') = app_enc_mv cs acc (if mx < m then m else mx) in
    (s::ss,mx'))
End

val r = translate app_enc_mv_def;

Theorem app_enc_mv_enc_list:
  ∀new mx.
  app_enc_mv new (enc_list acc) mx =
    (enc_list (new ++ acc), max_var_list new mx)
Proof
  Induct>>
  gvs[app_enc_mv_def,npbc_slotTheory.enc_mv_enc]>>
  simp[enc_list_def,max_var_list_def,MAX_DEF]
QED

(* The constraints stored in the slots ss *)
(* TMC *)
Definition dec_list_def:
  (dec_list [] = []) ∧
  (dec_list (s::ss) = let c = dec s in c :: dec_list ss)
End

val r = translate dec_list_def;

Theorem dec_list_side:
  ∀ss. EVERY wf_slot ss ⇒ dec_list_side ss
Proof
  Induct>>
  rw[Once (fetch "-" "dec_list_side_def"),npbc_arrayProgTheory.dec_side]
QED

Theorem dec_list_enc_list:
  ∀fml. dec_list (enc_list fml) = fml
Proof
  Induct>>fs[dec_list_def,enc_list_def]
QED

(* lno counts the lines read so far *)
Quote add_cakeml:
  fun next_nocomment_arr lno fd =
  case input_toks fd of
    None => (lno, None)
  | Some l =>
    if nocomment_line l then (lno+1, Some l)
    else next_nocomment_arr (lno+1) fd
End

Theorem next_nocomment_arr_spec:
  ∀lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "next_nocomment_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      SEP_EXISTS k lines' lno'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno',oHD (FILTER nocomment_line (MAP toks lines))) v ∧
          FILTER nocomment_line (MAP toks lines') =
          DROP 1 (FILTER nocomment_line (MAP toks lines))))
Proof
  Induct>>
  simp[]>>
  rpt strip_tac>>
  xcf "next_nocomment_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac [`emp`,‘[]’,‘fs’]>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac [‘k’,`[]`,`lno`]>>
    xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def])>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                  (SOME (toks h)) v)’
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[toks_def])>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    rw[]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xif>>asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac [`k`,`lines`,`lno+1`]>>
  xsimpl>>
  simp[PAIR_TYPE_def,OPTION_TYPE_def]
QED

(* The constraints of line l, numbered with the table, normalised and
  stored in front of acc; NONE if l is not a constraint *)
Quote add_cakeml:
  fun parse_norm_line_arr tv l acc mx =
    case parse_constraint_ns (skip_annot l) of
      None => None
    | Some c => Some (app_enc_mv (norm_pbc (nt_pbc tv 0 c)) acc mx)
End

Theorem parse_norm_line_arr_spec:
  line_TYPE l lv ∧
  LIST_TYPE fslot_TYPE (enc_list acc) accv ∧
  NUM (max_var_list acc mx) mxv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_line_arr" (get_ml_prog_state()))
    [tv; lv; accv; mxv]
    (NT_TABLE NONE s tv)
    (POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(OPTION_TYPE (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
          (case parse_norm_line l s acc of
            NONE => NONE
          | SOME (x,t) => SOME (enc_list x, max_var_list x mx)) v ∧
        ∀x t. parse_norm_line l s acc = SOME (x,t) ⇒ s' = t))
Proof
  rw[]>>
  xcf "parse_norm_line_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[parse_norm_line_def]>>
  namedCases_on`parse_constraint_ns (skip_annot l)`["","c"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl>>
    qexists_tac`s`>>
    xsimpl)>>
  xlet`POSTve
    (λv. SEP_EXISTS c1 s1. NT_TABLE NONE s1 tv *
      &(name_pbc NONE c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 v))
    (λe. SEP_EXISTS s1. NT_TABLE NONE s1 tv *
      &(Fail_exn e ∧ name_pbc NONE c s = NONE))`
  >- (
    xapp>>
    xsimpl)
  >- (
    xsimpl>>
    simp[name_pbc_NONE])>>
  gvs[npbc_arrayProgTheory.LIST_TYPE_fslot_TYPE]>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`s1`>>
  gvs[name_pbc_NONE,name_norm_pbc_norm_pbc,app_enc_mv_enc_list,
      GSYM max_var_list_APPEND,PAIR_TYPE_def,OPTION_TYPE_def,
      npbc_arrayProgTheory.LIST_TYPE_fslot_TYPE]>>
  xsimpl>>
  simp[enc_list_def,EVERY_MAP]
QED

Quote add_cakeml:
  fun parse_norm_body_arr lno fd tv acc mx =
  case input_toks fd of
    None => Inr (acc, mx)
  | Some l =>
    if nocomment_line l then
      (case parse_norm_line_arr tv l acc mx of
        None => Inl (lno+1)
      | Some (acc',mx') => parse_norm_body_arr (lno+1) fd tv acc' mx')
    else parse_norm_body_arr (lno+1) fd tv acc mx
End

Theorem parse_norm_body_arr_spec:
  ∀lines fd fdv fs s acc accv lno lnov mx mxv.
  NUM lno lnov ∧
  LIST_TYPE fslot_TYPE (enc_list acc) accv ∧
  NUM (max_var_list acc mx) mxv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_body_arr" (get_ml_prog_state()))
    [lnov; fdv; tv; accv; mxv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE NONE s tv)
    (POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(∃n.
        SUM_TYPE NUM (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
          (case parse_norm_lines (MAP toks lines) s acc of
            NONE => INL n
          | SOME (x,t) => INR (enc_list x, max_var_list x mx)) v ∧
        ∀x t. parse_norm_lines (MAP toks lines) s acc = SOME (x,t) ⇒ s' = t) *
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp[parse_norm_lines_def]>>
  rpt strip_tac>>
  xcf "parse_norm_body_arr" (get_ml_prog_state ())
  >- (
    xlet`POSTv v.
      SEP_EXISTS k.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
        NT_TABLE NONE s tv *
        &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v`
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac[`NT_TABLE NONE s tv`,`[]`,`fs`,`fd`]>>
      xsimpl>>
      rw[]>>
      qexists_tac`x`>>
      xsimpl)>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`[]`]>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
      NT_TABLE NONE s tv *
      &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v`
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac[`NT_TABLE NONE s tv`,`h::lines`,`fs`,`fd`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl)>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif>>
    asm_exists_tac>>
    xsimpl>>
    xlet_autop>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`s`,`mx`,`forwardFD fs fd k`,`fd`,`acc`,`lno + 1`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`x`,`k + x'`,`x''`,`n`]>>
    simp[forwardFD_o]>>
    xsimpl)>>
  xif>>
  asm_exists_tac>>
  simp[]>>
  xlet`POSTv v.
    SEP_EXISTS s1.
    NT_TABLE NONE s1 tv *
    &(OPTION_TYPE (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
        (case parse_norm_line (toks h) s acc of
          NONE => NONE
        | SOME (x,t) => SOME (enc_list x, max_var_list x mx)) v ∧
      ∀x t. parse_norm_line (toks h) s acc = SOME (x,t) ⇒ s1 = t) *
    STDIO (forwardFD fs fd k) *
    INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k)`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`STDIO (forwardFD fs fd k) *
                  INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k)`,
                 `s`,`mx`,`toks h`,`acc`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl)>>
  Cases_on`parse_norm_line (toks h) s acc`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`s1`,`k`,`lines`]>>
    simp[SUM_TYPE_def]>>
    xsimpl>>
    qexists_tac`lno + 1`>>
    simp[])>>
  rename1`parse_norm_line _ _ _ = SOME res`>>
  PairCases_on`res`>>
  fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`res1`,`mx`,`forwardFD fs fd k`,`fd`,`res0`,`lno + 1`]>>
  xsimpl>>
  rw[]>>
  qexistsl_tac[`x`,`k + x'`,`x''`,`n`]>>
  simp[forwardFD_o]>>
  xsimpl
QED

(* The constraints of the header lines that are neither the objective nor
  the preserved line *)
Quote add_cakeml:
  fun parse_norm_rest_arr tv ls acc mx =
    case ls of
      [] => Some (acc,mx)
    | (l::ls) =>
      case parse_norm_line_arr tv l acc mx of
        None => None
      | Some (acc',mx') => parse_norm_rest_arr tv ls acc' mx'
End

Theorem parse_norm_rest_arr_spec:
  ∀ls lsv s acc accv mx mxv.
  EVERY nocomment_line ls ∧
  LIST_TYPE line_TYPE ls lsv ∧
  LIST_TYPE fslot_TYPE (enc_list acc) accv ∧
  NUM (max_var_list acc mx) mxv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_rest_arr" (get_ml_prog_state()))
    [tv; lsv; accv; mxv]
    (NT_TABLE NONE s tv)
    (POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(OPTION_TYPE (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
          (case parse_norm_lines ls s acc of
            NONE => NONE
          | SOME (x,t) => SOME (enc_list x, max_var_list x mx)) v ∧
        ∀x t. parse_norm_lines ls s acc = SOME (x,t) ⇒ s' = t))
Proof
  Induct>>
  rw[]>>
  xcf "parse_norm_rest_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`s`>>
    simp[parse_norm_lines_def,OPTION_TYPE_def,PAIR_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v.
    SEP_EXISTS s1.
    NT_TABLE NONE s1 tv *
    &(OPTION_TYPE (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
        (case parse_norm_line h s acc of
          NONE => NONE
        | SOME (x,t) => SOME (enc_list x, max_var_list x mx)) v ∧
      ∀x t. parse_norm_line h s acc = SOME (x,t) ⇒ s1 = t)`
  >- (
    xapp>>
    xsimpl)>>
  simp[parse_norm_lines_def]>>
  namedCases_on`parse_norm_line h s acc`["","xt"]
  >- (
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`s1`>>
    xsimpl)>>
  PairCases_on`xt`>>
  gvs[OPTION_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  xsimpl
QED

val res = translate opt_list_def;
val res = translate split_header_def;

Quote add_cakeml:
  fun parse_norm_toks_arr fd tv =
  case next_nocomment_arr 0 fd of (lno1,l1) =>
  case next_nocomment_arr lno1 fd of (lno2,l2) =>
  case split_header l1 l2 of (obj,(pres,rest)) =>
  let
    val pres1 = nt_pres tv pres
    val obj1 = nt_obj tv obj
  in
    case parse_norm_rest_arr tv rest [] 0 of
      None => Inl lno2
    | Some (acc,mx) =>
      case parse_norm_body_arr lno2 fd tv acc mx of
        Inl n => Inl n
      | Inr (acc1,mx1) =>
        Inr (pres1,(normalise_obj obj1,(List.rev acc1,mx1)))
  end
End

Theorem parse_norm_toks_arr_spec:
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_toks_arr" (get_ml_prog_state()))
    [fdv; tv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE NONE s tv)
    (POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(∃n.
        SUM_TYPE NUM nprob_TYPE
          (case parse_norm_pbf_toks (MAP toks lines) s of
            NONE => INL n
          | SOME (prob,t) => INR (enc_prob prob)) v ∧
        ∀prob t. parse_norm_pbf_toks (MAP toks lines) s = SOME (prob,t) ⇒
          s' = t) *
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  rw[]>>
  xcf "parse_norm_toks_arr" (get_ml_prog_state ())>>
  qabbrev_tac`fl = FILTER nocomment_line (MAP toks lines)`>>
  xlet`(POSTv v.
      SEP_EXISTS k1 lines1 lno1.
        STDIO (forwardFD fs fd k1) *
        INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k1) *
        NT_TABLE NONE s tv *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno1,oHD fl) v ∧
          FILTER nocomment_line (MAP toks lines1) = DROP 1 fl))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`NT_TABLE NONE s tv`,`lines`,`fs`,`fd`]>>
    xsimpl>>
    rw[Abbr`fl`]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`(POSTv v.
      SEP_EXISTS k2 lines2 lno2.
        STDIO (forwardFD fs fd k2) *
        INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd k2) *
        NT_TABLE NONE s tv *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno2,oHD (DROP 1 fl)) v ∧
          FILTER nocomment_line (MAP toks lines2) = DROP 2 fl))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`NT_TABLE NONE s tv`,`lines1`,`forwardFD fs fd k1`,`fd`,
                  `lno1`]>>
    xsimpl>>
    rw[]>>
    fs[forwardFD_o,DROP_DROP_T]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  qmatch_goalsub_abbrev_tac`STDIO fs2`>>
  xlet_autop>>
  qabbrev_tac`iof = STDIO fs2 * INSTREAM_LINES #"\n" fd fdv lines2 fs2`>>
  `∃obj pres rest.
     split_header (oHD (FILTER nocomment_line (MAP toks lines)))
       (oHD (DROP 1 (FILTER nocomment_line (MAP toks lines)))) =
     (obj,pres,rest)` by
    metis_tac[PAIR]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    qexistsl_tac[`iof`,`s`]>>
    xsimpl)>>
  Cases_on`name_to_num_pres pres s`>>
  fs[]>>
  rename1`name_to_num_pres pres s = (pres1,s1)`>>
  xlet_autop>>
  Cases_on`name_to_num_obj obj s1`>>
  fs[]>>
  rename1`name_to_num_obj obj s1 = (obj1,s2)`>>
  xlet_autop>>
  xlet`POSTv v.
    SEP_EXISTS s3.
    iof * NT_TABLE NONE s3 tv *
    &(OPTION_TYPE (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
        (case parse_norm_lines rest s2 [] of
          NONE => NONE
        | SOME (x,t) => SOME (enc_list x, max_var_list x 0)) v ∧
      ∀x t. parse_norm_lines rest s2 [] = SOME (x,t) ⇒ s3 = t)`
  >- (
    sg`EVERY nocomment_line rest`
    >- (
      gvs[split_header_oHD]>>
      drule_then irule parse_obj_pres_maybe_EVERY>>
      `EVERY nocomment_line fl` by
        simp[Abbr`fl`,EVERY_FILTER]>>
      simp[rich_listTheory.EVERY_TAKE])>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`iof`,`s2`,`0`,`rest`,`[]`]>>
    xsimpl>>
    simp[max_var_list_def,enc_list_def,LIST_TYPE_def]>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl)>>
  sg`parse_norm_pbf_toks (MAP toks lines) s =
     case parse_norm_lines rest s2 [] of
       NONE => NONE
     | SOME (acc,t1) =>
       case parse_norm_lines (MAP toks lines2) t1 acc of
         NONE => NONE
       | SOME (acc1,t) =>
         SOME ((OPTION_MAP list_to_num_set pres1,normalise_obj obj1,
                REVERSE acc1),t)`
  >- (
    simp[parse_norm_pbf_toks_def,parse_norm_header_def]>>
    qunabbrev_tac`fl`>>
    qpat_x_assum`FILTER nocomment_line (MAP toks lines2) = _`
      (assume_tac o GSYM)>>
    simp[parse_norm_lines_FILTER]>>
    namedCases_on`parse_norm_lines rest s2 []`["","res"]>>
    simp[]>>
    PairCases_on`res`>>
    simp[])>>
  pop_assum SUBST1_TAC>>
  Cases_on`parse_norm_lines rest s2 []`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`s3`,`k2`,`lines2`]>>
    simp[SUM_TYPE_def,Abbr`iof`,Abbr`fs2`]>>
    conj_tac
    >- (
      qexists_tac`lno2`>>
      simp[])>>
    xsimpl)>>
  rename1`parse_norm_lines rest s2 [] = SOME res`>>
  PairCases_on`res`>>
  gvs[OPTION_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  qunabbrev_tac`iof`>>
  xlet`POSTv v.
    SEP_EXISTS s4.
    NT_TABLE NONE s4 tv *
    &(∃n.
      SUM_TYPE NUM (PAIR_TYPE (LIST_TYPE fslot_TYPE) NUM)
        (case parse_norm_lines (MAP toks lines2) res1 res0 of
          NONE => INL n
        | SOME (x,t) => INR (enc_list x, max_var_list x 0)) v ∧
      ∀x t. parse_norm_lines (MAP toks lines2) res1 res0 = SOME (x,t) ⇒
        s4 = t) *
    SEP_EXISTS k3 lines3.
      STDIO (forwardFD fs fd k3) *
      INSTREAM_LINES #"\n" fd fdv lines3 (forwardFD fs fd k3)`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`res1`,`0`,`lines2`,`fs2`,`fd`,`res0`,`lno2`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`x`,`k2 + x'`,`x''`]>>
    simp[Abbr`fs2`,forwardFD_o]>>
    xsimpl>>
    qexists_tac`n`>>
    simp[])>>
  namedCases_on`parse_norm_lines (MAP toks lines2) res1 res0`["","body"]>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`s4`,`k3`,`lines3`]>>
    conj_tac
    >- (
      qexists_tac`n`>>
      simp[])>>
    xsimpl)>>
  PairCases_on`body`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexistsl_tac[`k3`,`lines3`]>>
  gvs[enc_prob_def,enc_list_def,MAP_REVERSE,max_var_list_REVERSE,
      PAIR_TYPE_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun parse_norm_pbf_full f tv =
  let
    val fd = TextIO.openInSetBufferSize f 65531
    val res = parse_norm_toks_arr fd tv
    val close = TextIO.closeIn fd
  in
    case res of
      Inl n => Inl (noparse_line_string f n)
    | Inr x => Inr x
  end
  handle TextIO.BadFileName => Inl (notfound_string f)
End

Theorem parse_norm_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_norm_pbf_full"(get_ml_prog_state()))
    [fv; tv]
    (STDIO fs * NT_TABLE NONE s tv)
    (POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(∃err. SUM_TYPE STRING_TYPE nprob_TYPE
        (case get_fml fs f of
          NONE => INL err
        | SOME prob => INR (enc_prob (FST (name_norm_prob prob s)))) v ∧
        ∀prob. get_fml fs f = SOME prob ⇒ s' = SND (name_norm_prob prob s)) *
      STDIO fs)
Proof
  rw[]>>
  xcf"parse_norm_pbf_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[]) >>
  simp[get_fml_def,get_annot_fml_def]>>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs * NT_TABLE NONE s tv`
    >- (xlet_auto_spec (SOME openInSetBufferSize_STDIO_spec)>>xsimpl)>>
    fs[BadFileName_exn_def]>>
    xcases>>rw[]>>
    xlet_auto>>xsimpl>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    qexists_tac`s`>>
    conj_tac
    >- (
      qexists_tac`notfound_string f`>>
      simp[])>>
    xsimpl)>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openInSetBufferSize_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>xsimpl>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES _ fdd fddv lines fss`>>
  xlet`(POSTv v.
      SEP_EXISTS s'.
      NT_TABLE NONE s' tv *
      &(∃n.
        SUM_TYPE NUM nprob_TYPE
          (case parse_norm_pbf_toks (MAP toks lines) s of
            NONE => INL n
          | SOME (prob,t) => INR (enc_prob prob)) v ∧
        ∀prob t. parse_norm_pbf_toks (MAP toks lines) s = SOME (prob,t) ⇒
          s' = t) *
      SEP_EXISTS k lines'.
        STDIO (forwardFD fss fdd k) *
        INSTREAM_LINES #"\n" fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`s`,`lines`,`fss`,`fdd`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`x`,`x'`,`x''`,`n`]>>
    xsimpl)>>
  xlet `POSTv v. STDIO fs * NT_TABLE NONE s' tv`
  >- (
    xapp_spec closeIn_spec_lines >>
    qexistsl_tac [`NT_TABLE NONE s' tv`,`lines'`,`forwardFD fss fdd k`,`fdd`,
                  `#"\n"`]>>
    conj_tac >-
     (unabbrev_all_tac>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs []) >>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]>>
       imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
       match_mp_tac validFileFD_nextFD>>fs []) >>
    xsimpl >> rw [] >>
    unabbrev_all_tac>>xsimpl>>
    simp[forwardFD_ADELKEY_same]>>
    DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
    xsimpl>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs [])>>
  fs[parse_norm_pbf_toks_thm,parse_pbf_def]>>
  Cases_on`parse_pbf_toks (MAP toks lines)`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    simp[SUM_TYPE_def]>>
    qexists_tac`s'`>>
    conj_tac
    >- (
      qexists_tac`noparse_line_string f n`>>
      simp[])>>
    xsimpl)>>
  rename1`parse_pbf_toks _ = SOME aprob`>>
  Cases_on`name_norm_prob (strip_annot_prob aprob) s`>>
  fs[SUM_TYPE_def]>>
  xmatch>>
  xcon>>
  xsimpl
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
  ∃pres obj fml.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    ∃concl.
      out = concl_to_string concl ∧
      pbc$sem_concl (set fml) obj (pres_set_list pres) concl)
End

(* Ignoring output section for 2-arg version *)
Definition map_concl_to_string_def:
  (map_concl_to_string (INL s) = (INL s)) ∧
  (map_concl_to_string (INR (out,bnd,c)) = (INR (concl_to_string c)))
End

val res = translate int_inf_to_string_def;
val res = translate concl_to_string_def;
val res = translate map_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  let val tv = nt_new None 0 in
  case parse_norm_pbf_full f1 tv of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (pres,(obj,(fml,mx))) =>
    (case
      map_concl_to_string
        (check_unsat_top False tv fml mx pres obj [] None None f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)
  end
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (
    fs [TextIOProofTheory.STDIO_def]>>
    xpull)>>
  xlet_autop>>
  xlet`POSTv tv. STDIO fs * NT_TABLE NONE (nt_init 0) tv`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`NONE`>>
    simp[OPTION_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v.
    SEP_EXISTS s'.
    NT_TABLE NONE s' tv *
    &(∃err. SUM_TYPE STRING_TYPE nprob_TYPE
      (case get_fml fs f1 of
        NONE => INL err
      | SOME prob => INR (enc_prob (FST (name_norm_prob prob (nt_init 0))))) v ∧
      ∀prob. get_fml fs f1 = SOME prob ⇒
        s' = SND (name_norm_prob prob (nt_init 0))) *
    STDIO fs`
  >- (
    xapp>>
    xsimpl)>>
  Cases_on`get_fml fs f1`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE NONE s' tv`,`err`,`fs`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`err`>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  rename1`get_fml fs f1 = SOME prob`>>
  PairCases_on`prob`>>
  `∃pres obj fml t.
    name_norm_prob (prob0,prob1,prob2) (nt_init 0) = ((pres,obj,fml),t)` by
    metis_tac[PAIR]>>
  fs[SUM_TYPE_def,PAIR_TYPE_def,enc_prob_def]>>
  xmatch>>
  ntac 4 xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res st'.
    NT_TABLE NONE st' tv *
    &(SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE)) res v ∧
      case res of
        INR (output,bound,concl) =>
        npbc$sem_concl (set fml) obj (pres_set_spt pres) concl
      | INL l => T)`
  >- (
    assume_tac (Q.INST [`mx`|->`0`] npbc_parseProgTheory.max_var_list_bound)>>
    xapp_spec check_unsat_top_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`t`,`NONE`,`pres`,`NONE`,`obj`,`NONE`,`fs`,`[]`,`fml`,
                 `F`,`f2`,`max_var_list fml 0`]>>
    xsimpl>>
    fs[validArg_def,FILENAME_def,LIST_TYPE_def,OPTION_TYPE_def,enc_list_def]>>
    rw[]>>
    qexistsl_tac[`x`,`x'`]>>
    xsimpl>>
    rpt (TOP_CASE_TAC>>gvs[]))>>
  xlet_autop>>
  namedCases_on`res`["errs","outc"]>>
  fs[map_concl_to_string_def,SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE NONE st' tv`,`errs`,`fs`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`«»`,`errs`]>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  PairCases_on`outc`>>
  fs[SUM_TYPE_def,map_concl_to_string_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`NT_TABLE NONE st' tv`,`concl_to_string outc2`,`fs`]>>
  xsimpl>>
  rw[]>>
  qexistsl_tac[`concl_to_string outc2`,`«»`]>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  rw[]>>
  qexists_tac`outc2`>>
  drule name_norm_prob_sem_concl>>
  simp[nt_init_ok]
QED

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_annot_fml fs f1 of
    SOME prob => out = concat (print_annot_prob prob)
  | NONE => out = «»
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr prob =>
    TextIO.print_list (print_annot_prob prob)
End

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_1_sem fs f1 out))
Proof
  rw[check_unsat_1_sem_def]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`err`>>xsimpl)>>
  xmatch>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition output_to_string_def:
  (output_to_string bound NoOutput =
    «s VERIFIED NO OUTPUT GUARANTEE\n») ∧
  (output_to_string bound Derivable =
    «s VERIFIED OUTPUT DERIVABLE\n») ∧
  (output_to_string bound Equisatisfiable =
    «s VERIFIED OUTPUT EQUISATISFIABLE\n») ∧
  (output_to_string bound Equioptimal =
    «s VERIFIED OUTPUT EQUIOPTIMAL FOR obj < » ^ int_inf_to_string bound ^ «\n») ∧
  (output_to_string bound Equisolvable =
    «s VERIFIED OUTPUT EQUISOLVABLE FOR obj < » ^ int_inf_to_string bound ^ «\n»)
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f3 out ⇔
  (out ≠ «» ⇒
  ∃pres obj fml prest objt fmlt.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    get_fml fs f3 = SOME (prest,objt,fmlt) ∧
    ∃output bound concl.
      out =
        (concl_to_string concl ^
        output_to_string bound output) ∧
      pbc$sem_concl (set fml) obj (pres_set_list pres) concl ∧
      pbc$sem_output (set fml) obj (pres_set_list pres) bound
        (set fmlt) objt (pres_set_list prest) output
  )
End

(* Ignoring output section for 2-arg version *)
Definition map_out_concl_to_string_def:
  (map_out_concl_to_string (INL s) = (INL s)) ∧
  (map_out_concl_to_string (INR (out,bnd,c)) =
    (INR (concl_to_string c ^ output_to_string bnd out)))
End

val res = translate output_to_string_def;
val res = translate map_out_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_3 f1 f2 f3 =
  let val tv = nt_new None 0 in
  case parse_norm_pbf_full f1 tv of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (pres,(obj,(fml,mx))) =>
  (case parse_norm_pbf_full f3 tv of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (prest,(objt,(fmlt,mxt))) =>
    (case
      map_out_concl_to_string
        (check_unsat_top True tv
          fml mx pres obj (dec_list fmlt) prest objt f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s))
  end
End

Theorem check_unsat_3_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  STRING_TYPE f3 f3v ∧ validArg f3 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_3"(get_ml_prog_state()))
    [f1v; f2v; f3v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_3_sem fs f1 f3 out))
Proof
  rw[check_unsat_3_sem_def]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (
    fs [TextIOProofTheory.STDIO_def]>>
    xpull)>>
  xlet_autop>>
  xlet`POSTv tv. STDIO fs * NT_TABLE NONE (nt_init 0) tv`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`NONE`>>
    simp[OPTION_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v.
    SEP_EXISTS s'.
    NT_TABLE NONE s' tv *
    &(∃err. SUM_TYPE STRING_TYPE nprob_TYPE
      (case get_fml fs f1 of
        NONE => INL err
      | SOME prob => INR (enc_prob (FST (name_norm_prob prob (nt_init 0))))) v ∧
      ∀prob. get_fml fs f1 = SOME prob ⇒
        s' = SND (name_norm_prob prob (nt_init 0))) *
    STDIO fs`
  >- (
    xapp>>
    xsimpl)>>
  Cases_on`get_fml fs f1`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE NONE s' tv`,`err`,`fs`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`err`>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  rename1`get_fml fs f1 = SOME prob`>>
  PairCases_on`prob`>>
  `∃pres obj fml t.
    name_norm_prob (prob0,prob1,prob2) (nt_init 0) = ((pres,obj,fml),t)` by
    metis_tac[PAIR]>>
  fs[SUM_TYPE_def,PAIR_TYPE_def,enc_prob_def]>>
  xmatch>>
  xlet`POSTv v.
    SEP_EXISTS s2.
    NT_TABLE NONE s2 tv *
    &(∃err. SUM_TYPE STRING_TYPE nprob_TYPE
      (case get_fml fs f3 of
        NONE => INL err
      | SOME prob => INR (enc_prob (FST (name_norm_prob prob t)))) v ∧
      ∀prob. get_fml fs f3 = SOME prob ⇒
        s2 = SND (name_norm_prob prob t)) *
    STDIO fs`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`t`,`fs`,`f3`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`x`,`err`]>>
    xsimpl)>>
  Cases_on`get_fml fs f3`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE NONE s2 tv`,`err`,`fs`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`err`>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  rename1`get_fml fs f3 = SOME probt`>>
  PairCases_on`probt`>>
  `∃prest objt fmlt u.
    name_norm_prob (probt0,probt1,probt2) t = ((prest,objt,fmlt),u)` by
    metis_tac[PAIR]>>
  fs[SUM_TYPE_def,PAIR_TYPE_def,enc_prob_def]>>
  xmatch>>
  xlet`POSTv v.
    STDIO fs * NT_TABLE NONE u tv * &LIST_TYPE constraint_TYPE fmlt v`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`enc_list fmlt`>>
    gvs[npbc_arrayProgTheory.LIST_TYPE_fslot_TYPE,dec_list_side,
        dec_list_enc_list])>>
  xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res st'.
    NT_TABLE NONE st' tv *
    &(SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE)) res v ∧
      case res of
        INR (output,bound,concl) =>
        npbc$sem_concl (set fml) obj (pres_set_spt pres) concl ∧
        npbc$sem_output (set fml) obj (pres_set_spt pres) bound
          (set fmlt) objt (pres_set_spt prest) output
      | INL l => T)`
  >- (
    assume_tac (Q.INST [`mx`|->`0`] npbc_parseProgTheory.max_var_list_bound)>>
    xapp_spec check_unsat_top_spec>>
    xsimpl>>
    fs[enc_list_def]>>
    rw[]
    >- (
      qexists_tac`T`>>
      EVAL_TAC)
    >- (
      qexists_tac`f2`>>
      fs[FILENAME_def,validArg_def])>>
    qexists_tac`max_var_list fml 0`>>
    simp[])>>
  xlet_autop>>
  namedCases_on`res`["errs","outc"]>>
  fs[map_out_concl_to_string_def,SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE NONE st' tv`,`errs`,`fs`]>>
    xsimpl>>
    rw[]>>
    qexistsl_tac[`«»`,`errs`]>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  PairCases_on`outc`>>
  fs[SUM_TYPE_def,map_out_concl_to_string_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`NT_TABLE NONE st' tv`,
               `concl_to_string outc2 ^ output_to_string outc1 outc0`,`fs`]>>
  xsimpl>>
  rw[]>>
  qexistsl_tac[`concl_to_string outc2 ^ output_to_string outc1 outc0`,`«»`]>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  rw[]>>
  qexistsl_tac[`outc0`,`outc1`,`outc2`]>>
  assume_tac (Q.INST [`n`|->`0`] nt_init_ok)>>
  drule_all name_norm_prob_2_sem>>
  simp[]
QED

Definition usage_string_def:
  usage_string = «Usage: cake_pb <OPB file> <optional: PB proof file> <optional: output OPB file>\n»
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | [f1,f2,f3] => check_unsat_3 f1 f2 f3
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
  else if LENGTH cl = 4 then
    check_unsat_3_sem fs (EL 1 cl) (EL 3 cl) out
  else out = «»
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(main_sem fs cl out))
Proof
  rw[main_sem_def]>>
  xcf"main"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `mk_usage_string usage_string` >>
    simp [] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  xmatch>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `mk_usage_string usage_string` >>
  simp [] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        main_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`add_stdout (add_stderr fs x') x`
  \\ xsimpl
  \\ qexists_tac`x`
  \\ qexists_tac`x'`
  \\ xsimpl
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

Theorem main_semantics =
  prove_sem_thm "main"
                "main_prog"
                main_whole_prog_spec2;
