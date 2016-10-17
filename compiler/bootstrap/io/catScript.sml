open preamble

open ml_translatorTheory ml_translatorLib semanticPrimitivesTheory
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib

open catfileSystemTheory

val _ = new_theory "cat"

(* ----------------------------------------------------------------------

    Our operations require memory to be allocated in the heap for the
    passing of parameters:

    1. write requires write_loc for the storage of the character to be
       written
    2. open-file requires filenamae_loc for the storage of the name of the
       (probably zero-terminated) file
    3. read-char needs storage for a single byte for identifying the
       file-descripter to read through. This assumes that there can't
       be more than 256 file-descriptors.  Perhaps we can share write_loc.
    4. close-file also needs a file-descriptor.

    Memory of this sort can be pre-allocated by making calls to AST
    expressions like

      App Aw8alloc [Lit (IntLit sz); Lit (Word8 0w)]

    where sz is the number of bytes needed.

   ---------------------------------------------------------------------- *)

(* first copy the Word8Array and CHAR_IO set up from helloProg, adding an
   extra array for filenames, of length FILENAME_MAX
*)
(* setup *)

fun get_module_prefix () = let
  val mod_tm = ml_progLib.get_thm (get_ml_prog_state ())
               |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none mod_tm then "" else
       stringSyntax.fromHOLstring (mod_tm |> rand |> rator |> rand) ^ "_"
  end

fun trans ml_name q = let
  val rhs = Term q
  val prefix = get_module_prefix ()
  val tm = mk_eq(mk_var(prefix ^ pick_name ml_name,type_of rhs),rhs)
  val def = Define `^tm`
  val _ = (next_ml_names := [ml_name])
  val v_thm = translate (def |> SIMP_RULE std_ss [FUN_EQ_THM])
  val v_thm = v_thm |> REWRITE_RULE [def]
                    |> CONV_RULE (DEPTH_CONV ETA_CONV)
  val v_name = v_thm |> concl |> rand |> dest_const |> fst
  (* evaluate precondition *)
  val pat = PRECONDITION_def |> SPEC_ALL |> GSYM |> concl |> rand
  fun PRECOND_CONV c tm =
    if can (match_term pat) tm then RAND_CONV c tm else NO_CONV tm
  val v_thm = v_thm |> DISCH_ALL
                    |> CONV_RULE (ONCE_DEPTH_CONV (PRECOND_CONV EVAL))
                    |> UNDISCH_ALL
  val _ = save_thm(v_name ^ "_thm",v_thm)
  in v_thm end

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_prog tm pick_name) end

fun append_dec tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_dec tm pick_name) end

fun append_decs tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  val tms = fst (listSyntax.dest_list tm)
  in (map append_dec tms; ()) end

fun basis_st () = get_ml_prog_state ()

val _ = Define `
  mk_binop name prim = Dlet (Pvar name)
    (Fun "x" (Fun "y" (App prim [Var (Short "x"); Var (Short "y")])))`;

val _ = Define `
  mk_unop name prim = Dlet (Pvar name)
    (Fun "x" (App prim [Var (Short "x")]))`;

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`

val _ = ml_prog_update (close_module NONE);

(* Word8Array module -- CF verified *)

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs
   ``[mk_binop "array" Aw8alloc;
      mk_binop "sub" Aw8sub;
      mk_unop "length" Aw8length;
      Dlet (Pvar "update") (Fun "x" (Fun "y" (Fun "z"
        (App Aw8update [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``

val _ = ml_prog_update (close_module NONE);

fun prove_array_spec op_name =
  xcf op_name (basis_st()) \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

val w8array_alloc_spec = store_thm ("w8array_alloc_spec",
  ``!n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" (basis_st())) [nv; wv]
       emp (POSTv v. W8ARRAY v (REPLICATE n w))``,
  prove_array_spec "Word8Array.array");

val w8array_sub_spec = store_thm ("w8array_sub_spec",
  ``!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" (basis_st())) [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.sub");

val w8array_length_spec = store_thm ("w8array_length_spec",
  ``!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" (basis_st())) [av]
       (W8ARRAY av a) (POSTv v. cond (NUM (LENGTH a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.length");

val w8array_update_spec = store_thm ("w8array_update_spec",
  ``!a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" (basis_st()))
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))``,
  prove_array_spec "Word8Array.update");

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val _ = append_dec ``Dtabbrev [] "char" (Tapp [] TC_char)``;
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`
val _ = trans "<" `string$char_lt`
val _ = trans ">" `string$char_gt`
val _ = trans "<=" `string$char_le`
val _ = trans ">=" `string$char_ge`

val _ = ml_prog_update (close_module NONE);


(* String module -- translated *)

val _ = ml_prog_update (open_module "String");

val _ = append_dec ``Dtabbrev [] "string" (Tapp [] TC_string)``;
val _ = trans "explode" `explode`
val _ = trans "implode" `implode`
val _ = trans "size" `strlen`

val _ = ml_prog_update (close_module NONE);

(* toplevel "primitive" operations *)
val _ = trans "+" `(+):int->int->int`
val _ = trans "=" `\x1 x2. x1 = x2:'a`

(* CharIO -- CF verified *)

val _ = ml_prog_update (open_module "CharIO");

fun derive_eval_thm v_name e = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val lemma = goal
    |> (NCONV 50 (SIMP_CONV (srw_ss()) [Once bigStepTheory.evaluate_cases,
            PULL_EXISTS,do_app_def,store_alloc_def,LET_THM]) THENC EVAL)
  val v_thm = prove(mk_imp(lemma |> concl |> rand,goal),fs [lemma])
                 |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
  val v_tm = v_thm |> concl |> rand |> rand |> rand
  val v_def = define_abbrev true v_name v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val onechar_e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``
val filename_e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

(*
   - onechar_loc is the name of the HOL constant
   - onechar is the name of the binding in the module
*)
val _ = ml_prog_update
          (add_Dlet (derive_eval_thm "onechar_loc" onechar_e) "onechar" [])

(* similarly
   - filename_loc is the name of the HOL constant
   - filename_array is the name of the binding in the module
*)
val _ = ml_prog_update
          (add_Dlet
             (derive_eval_thm "filename_loc" filename_e)
             "filename_array"
             [])


(* TODO: these two can definitely move somewhere else *)
val Apps_def = tDefine "Apps" `
  (Apps [x;y] = App Opapp [x;y]) /\
  (Apps [] = ARB) /\
  (Apps xs = App Opapp [Apps (FRONT xs); LAST xs])`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_FRONT]);

val LetApps_def = Define `
  LetApps n f args = Let (SOME n) (Apps (Var f::args))`;

val parse_t =
  ``λs. case peg_exec cmlPEG (nt (mkNT nDecl) I) (lexer_fun s) [] done failed of
          Result (SOME(_,[x])) => ptree_Decl x``
fun ParseDecl [QUOTE s] =
  EVAL (mk_comb(parse_t, stringSyntax.fromMLstring s))
       |> concl |> rhs |> rand

val word_eq1_d =
  ``Dletrec [("word_eq1", "w",
              Mat (Var (Short "w"))
                  [(Plit (Word8 1w), Con (SOME (Short "true")) []);
                   (Pvar "_", Con (SOME (Short "false")) [])])]``
val _ = append_dec word_eq1_d

val word_eq1_spec = Q.store_thm(
  "word_eq1_spec",
  `∀w:word8 wv.
     WORD w wv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "word_eq1" (basis_st())) [wv]
       emp
       (POSTv bv. &BOOL (w = 1w) bv)`,
  rpt strip_tac >> xcf "word_eq1" (basis_st()) >> xmatch >> xsimpl >>
  rw[]
  >- (xret >> xsimpl >> fs[WORD_def])
  >- (xret >> xsimpl >> fs[WORD_def] >> rfs[wordsTheory.w2w_def])
  >- simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
          pat_without_Pref_def, terminationTheory.pmatch_def]
  >- (simp[validate_pat_def, pat_typechecks_def, astTheory.pat_bindings_def,
           pat_without_Pref_def] >>
      fs[WORD_def] >> simp[terminationTheory.pmatch_def] >>
      rw[semanticPrimitivesTheory.lit_same_type_def]))

val copyi_q =
  `fun copyi a i clist =
      case clist of
          [] => let val z = Word8.fromInt 0 in Word8Array.update a i z end
        | c::cs => let
            val ordc = Char.ord c
            val cw = Word8.fromInt ordc
            val unit = Word8Array.update a i cw
            val suci = i + 1
          in
            copyi a suci cs
          end`
val copyi_d = ParseDecl copyi_q
val _ = append_dec copyi_d

val copyi_spec = Q.store_thm(
  "copyi_spec",
  `∀n nv cs csv a av.
     NUM n nv /\ n + LENGTH cs < LENGTH a /\ LIST_TYPE CHAR cs csv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "copyi" (basis_st()))
       [av; nv; csv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
                 W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) cs) n a))`,
  Induct_on `cs` >> fs[LIST_TYPE_def, LENGTH_NIL]
  >- (xcf "copyi" (basis_st()) >> xmatch >>
      xlet `POSTv zv. & WORD (0w:word8) zv * W8ARRAY av a`
      >- (xapp >> xsimpl) >>
      xapp >> xsimpl >> simp[insertNTS_atI_NIL] >> xsimpl >>
      metis_tac[DECIDE ``(x:num) + 1 < y ⇒ x < y``]) >>

  xcf "copyi" (basis_st()) >> xmatch >>
  rename [`LIST_TYPE CHAR ctail ctailv`, `CHAR chd chdv`] >>
  xlet `POSTv oc. &(NUM (ORD chd)) oc * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet `POSTv cw. &(WORD (n2w (ORD chd) : word8) cw) * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * W8ARRAY av (LUPDATE (n2w (ORD chd)) n a)`
  >- (xapp >> simp[]) >>
  qabbrev_tac `a0 = LUPDATE (n2w (ORD chd)) n a` >>
  xlet `POSTv si. &(NUM (n + 1) si) * W8ARRAY av a0`
  >- (xapp >> xsimpl >> qexists_tac `&n` >>
      fs[ml_translatorTheory.NUM_def, integerTheory.INT_ADD]) >>
  xapp >> xsimpl >> qexists_tac `n + 1` >>
  simp[insertNTS_atI_CONS, Abbr`a0`, LUPDATE_insertNTS_commute]);

val str_to_w8array_q =
  `fun str_to_w8array a s = let
     val clist = String.explode s
   in
      copyi a 0 clist
   end`
val str_to_w8array_d = ParseDecl str_to_w8array_q
val _ = append_dec str_to_w8array_d

val str_to_w8array_spec = Q.store_thm(
  "str_to_w8array_spec",
  `∀s sv a av.
     LENGTH (explode s) < LENGTH a ∧ STRING_TYPE s sv ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "str_to_w8array" (basis_st()))
       [av; sv]
       (W8ARRAY av a)
       (POSTv v.
          cond (UNIT_TYPE () v) *
          W8ARRAY av (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 a))`,
  rpt strip_tac >> xcf "str_to_w8array" (basis_st()) >>
  xlet `POSTv csv. &(LIST_TYPE CHAR (explode s) csv) * W8ARRAY av a`
  >- (xapp >> xsimpl >> metis_tac[]) >>
  xapp >> simp[])

(* ML implementation of write function (0), with parameter "c" *)
val write_e =
  ``LetApps "c" (Long "Word8Array" "update")
                [Var (Short "onechar"); Lit (IntLit 0); Var (Short "c")]
        (Let (SOME "_") (App (FFI 0) [Var (Short "onechar")])
             (Var (Short "c")))``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"write"`` ``"c"`` write_e "write_v")

(* ML implementation of open function (1), with parameter name "fname" *)
val open_e =
  ``Let (SOME "_")
        (Apps [Var (Short "str_to_w8array");
               Var (Short "filename_array");
               Var (Short "fname")])
    (Let (SOME "_")
         (App (FFI 1) [Var (Short "filename_array")])
      (Apps [Var (Long "Word8Array" "sub"); Var (Short "filename_array");
             Lit (IntLit 0)]))``
    |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"open"`` ``"fname"`` open_e "open_v")
val open_v_def = definition "open_v_def"

(* ML implementation of fgetc function (2), with parameter name "fd" *)
val fgetc_e =
  ``Let (SOME "_")
        (Apps [Var (Long "Word8Array" "update");
               Var (Short "onechar");
               Lit (IntLit 0);
               Var (Short "fd")])
        (App (FFI 2) [Var (Short "onechar")])`` |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"fgetc"`` ``"fd"`` fgetc_e "fgetc_v")
val fgetc_v_def = definition "fgetc_v_def"

(* ML implementation of close function (3), with parameter "w8" *)
val close_e =
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" "update");
                          Var (Short "onechar");
                          Lit (IntLit 0);
                          Var (Short "w8")])
             (Let (SOME "_") (App (FFI 3) [Var (Short "onechar")])
                  (Con NONE []))`` |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"close"`` ``"w8"`` close_e "close_v")

(* ML implementation of eof function (4), with parameter w8 (a fd) *)
val eof_e =
  ``Let (SOME "_") (Apps [Var (Long "Word8Array" "update");
                          Var (Short "onechar"); Lit (IntLit 0);
                          Var (Short "w8")]) (
    Let (SOME "_") (App (FFI 4) [Var (Short "onechar")]) (
    Let (SOME "bw") (Apps [Var (Long "Word8Array" "sub");
                           Var (Short "onechar"); Lit (IntLit 0)]) (
      Apps [Var (Short "word_eq1"); Var (Short "bw")])))``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"eof"`` ``"w8"`` eof_e "eof_v")

val _ = ml_prog_update (close_module NONE);

val CATFS_def = Define `
  CATFS fs = IO (encode fs) fs_ffi_next [0;1;2;3;4] * &(wfFS fs)
`

val CHAR_IO_char1_def = Define `
  CHAR_IO_char1 = SEP_EXISTS w. W8ARRAY onechar_loc [w]`;

val CHAR_IO_fname_def = Define`
  CHAR_IO_fname =
    SEP_EXISTS v. W8ARRAY filename_loc v * cond (LENGTH v = 256)
`;

val CHAR_IO_def = Define`
  CHAR_IO = CHAR_IO_char1 * CHAR_IO_fname
`;

val write_spec = store_thm ("write_spec",
  ``!c cv.
     WORD (c:word8) cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.write" (basis_st()))
       [cv]
       (CHAR_IO * CATFS fs)
       (POSTv uv.
         cond (UNIT_TYPE () uv) * CHAR_IO *
         CATFS (fs with stdout := fs.stdout ++ [CHR (w2n c)]))``,
  xcf "CharIO.write" (basis_st())
  \\ fs [CHAR_IO_def, CHAR_IO_char1_def] \\ xpull
  \\ xlet `POSTv zv. CATFS fs * W8ARRAY onechar_loc [c] * CHAR_IO_fname *
                     & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [EVAL ``onechar_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC)
  \\ xlet `POSTv _. CATFS (fs with stdout := fs.stdout ++ [CHR (w2n c)]) * W8ARRAY onechar_loc [c] * CHAR_IO_fname`
  >- (xffi >> simp [EVAL ``onechar_loc``, CATFS_def] >>
      `MEM 0 [0n;1;2;3;4]` by simp[] \\ instantiate >>
      map_every qexists_tac [`[c]`, `CHAR_IO_fname * &wfFS fs`] >> xsimpl >>
      simp[write_lemma, wfFS_def]) >>
  xret \\ xsimpl);

val ORD_eq_0 = Q.store_thm(
  "ORD_eq_0[simp]",
  `ORD c = 0 ⇔ c = CHR 0`,
  metis_tac[char_BIJ, ORD_CHR, EVAL ``0n < 256``]);

val nextFD_lt_256 = Q.store_thm(
  "nextFD_lt_256",
  `CARD (set (MAP FST fs.infds)) < 256 ⇒ nextFD fs < 256`,
  simp[nextFD_def] >> strip_tac >> numLib.LEAST_ELIM_TAC >> simp[] >>
  qabbrev_tac `ns = MAP FST fs.infds` >> RM_ALL_ABBREVS_TAC >> conj_tac
  >- (qexists_tac `MAX_SET (set ns) + 1` >>
      pop_assum kall_tac >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp[] >>
      rpt strip_tac >> res_tac >> fs[]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `count 256 ⊆ set ns` by simp[SUBSET_DEF] >>
  `256 ≤ CARD (set ns)`
     by metis_tac[CARD_COUNT, CARD_SUBSET, FINITE_LIST_TO_SET] >>
  fs[]);

val HD_LUPDATE = Q.store_thm(
  "HD_LUPDATE",
  `0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l`,
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]);

val open_spec = Q.store_thm(
  "open_spec",
  `∀s sv fs.
     STRING_TYPE s sv ∧ explode s ∈ FDOM (alist_to_fmap fs.files) ∧
     EVERY (λc. c ≠ CHR 0) (explode s) ∧
     LENGTH (explode s) < 256 ∧ CARD (FDOM (alist_to_fmap fs.infds)) < 256 ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.open" (basis_st()))
       [sv]
       (CHAR_IO * CATFS fs)
       (POSTv wv. &(WORD (n2w (nextFD fs) :word8) wv) *
                  CATFS (openFileFS (explode s) fs) * CHAR_IO)`,
  rpt strip_tac >>
  xcf "CharIO.open" (basis_st()) >>
  fs[CHAR_IO_def, CHAR_IO_fname_def] >> xpull >>
  rename [`W8ARRAY filename_loc fnm0`] >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_char1 *
                 W8ARRAY filename_loc
                         (insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0) *
                 CATFS fs`
  >- (xapp >> xsimpl >> instantiate >>
      simp[definition "filename_loc_def"] >> xsimpl) >>
  qabbrev_tac `fnm = insertNTS_atI (MAP (n2w o ORD) (explode s)) 0 fnm0` >>
  xlet `POSTv u.
          &(UNIT_TYPE () u) * CHAR_IO_char1 *
          W8ARRAY filename_loc (LUPDATE (n2w (nextFD fs)) 0 fnm) *
          CATFS (openFileFS (explode s) fs)`
  >- (xffi >> simp[definition "filename_loc_def", CATFS_def] >>
      map_every qexists_tac [`fnm`, `CHAR_IO_char1 * &wfFS fs`] >>
      `MEM 1 [0;1;2;3;4n]` by simp[] >> instantiate >> xsimpl >>
      simp[fs_ffi_next_def, decode_encode_FS, EXISTS_PROD, Abbr`fnm`,
           getNullTermStr_insertNTS_atI, EVERY_MAP, ORD_BOUND,
           dimword_8, MAP_MAP_o, o_DEF, char_BIJ] >>
      csimp[PULL_EXISTS, wfFS_openFile] >>
      csimp[nextFD_lt_256, ALOOKUP_EXISTS_IFF, openFile_def, openFileFS_def,
            PULL_EXISTS] >>
      fs[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  xapp >> xsimpl >> simp[definition "filename_loc_def"] >> xsimpl >>
  csimp[HD_LUPDATE] >>
  simp[Abbr`fnm`, LENGTH_insertNTS_atI])

val eof_spec = Q.store_thm(
  "eof_spec",
  `∀(w:word8) wv fs.
     WORD w wv ∧ w2n w ∈ FDOM (alist_to_fmap fs.infds) ∧ wfFS fs ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.eof" (basis_st()))
       [wv]
       (CHAR_IO * CATFS fs)
       (POSTv bv.
          &(BOOL (THE (eof (w2n w) fs)) bv) * CHAR_IO * CATFS fs)`,
  xcf "CharIO.eof" (basis_st()) >>
  simp[CHAR_IO_def, CHAR_IO_char1_def] >> xpull >>
  rename [`W8ARRAY onechar_loc [byte]`] >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_fname * CATFS fs *
                 W8ARRAY onechar_loc [w]`
  >- (xapp >> xsimpl >> simp[definition "onechar_loc_def"] >> xsimpl >>
      simp[LUPDATE_def]) >>
  xlet `POSTv u. &(UNIT_TYPE () u) * CHAR_IO_fname * CATFS fs *
                 W8ARRAY onechar_loc [if THE (eof (w2n w) fs) then 1w else 0w]`
  >- (xffi >> simp[definition "onechar_loc_def", CATFS_def] >>
      `MEM 4n [0;1;2;3;4]` by simp[] >> instantiate >> xsimpl >>
      csimp[fs_ffi_next_def, LUPDATE_def] >>
      simp[eof_def, EXISTS_PROD, PULL_EXISTS] >>
      fs[wfFS_def] >> res_tac >> simp[ALOOKUP_EXISTS_IFF]>>
      fs[EXISTS_PROD, MEM_MAP] >> metis_tac[]) >>
  xlet `POSTv bw. &(WORD (if THE (eof (w2n w) fs) then 1w else 0w:word8) bw) *
                  CATFS fs * CHAR_IO_fname *
                  W8ARRAY onechar_loc [if THE (eof (w2n w) fs) then 1w else 0w]`
  >- (xapp >> simp[definition "onechar_loc_def"] >> xsimpl) >>
  xapp >> xsimpl >>
  qexists_tac `if THE (eof (w2n w) fs) then 1w else 0w` >> rw[]);

(*

val e =
  ``LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"H")))]
      (LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"i")))]
         (Var (Short "_")))`` |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"main"`` ``"c"`` e "main_v")

val main_spec = store_thm ("main",
  ``!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "main" (basis_st()))
        [cv]
        (CHAR_IO * STDOUT "")
        (POSTv uv. CHAR_IO * STDOUT "Hi")``,
  xcf "main" (basis_st())
  \\ xlet `POSTv v. CHAR_IO * STDOUT "H"` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `""` \\ qexists_tac `n2w (ORD #"H")`
    \\ xsimpl)
  \\ xlet `POSTv v. CHAR_IO * STDOUT "Hi"` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `"H"` \\ qexists_tac `n2w (ORD #"i")`
    \\ xsimpl)
  \\ xvar \\ fs [] \\ xsimpl);

val main_applied = let
  val e = ``Apps [Var (Short "main"); Lit (IntLit 0)] ``
          |> EVAL |> concl |> rand
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val th = goal |> NCONV 6 (SIMP_CONV (srw_ss())
                    [Once bigStepTheory.evaluate_cases,PULL_EXISTS])
  val p = find_term (can (match_term ``lookup_var_id _ _ = SOME _``)) (concl th)
  val th = th |> SIMP_RULE std_ss [EVAL p]
  val exists_lemma = METIS_PROVE []
    ``(?x1 x2 x3 x4 x5 x6. P x1 x2 x3 x4 x5 x6) <=>
      (?x3 x4 x5 x6 x1 x2. P x1 x2 x3 x4 x5 x6)``
  val st = goal |> rator |> rator |> rand
  val th =
    main_spec |> SPEC_ALL |> Q.INST_TYPE [`:'ffi`|->`:'a`]
     |> REWRITE_RULE [cfAppTheory.app_basic_rel,cfAppTheory.app_def]
     |> Q.SPEC `st2heap (p:'a ffi_proj) ^st`
     |> Q.SPEC `{}`
     |> Q.SPEC `^st`
     |> SIMP_RULE std_ss [PULL_EXISTS,
          cfHeapsBaseTheory.res_case_def,
          cfHeapsBaseTheory.POSTv_ignore,
          cfHeapsBaseTheory.SPLIT3_emp3,
          cfHeapsBaseTheory.SPLIT_emp2]
     |> Q.INST [`cv`|->`Litv (IntLit 0)`]
     |> SIMP_RULE std_ss [Once exists_lemma]
     |> SIMP_RULE std_ss [GSYM PULL_EXISTS,GSYM th]
  in th end

val raw_evaluate_prog = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
  val th = th |> SPEC_ALL |> UNDISCH |> Q.SPEC `"_"` |> DISCH_ALL |> GEN_ALL
  val th = ConseqConv.WEAKEN_CONSEQ_CONV_RULE
             (ConseqConv.CONSEQ_REWRITE_CONV ([],[],[th])) main_applied
  val tm = th |> concl |> find_term (listSyntax.is_snoc)
  val entire_program_def = Define `entire_program = ^tm`
  val th = th |> SIMP_RULE std_ss [GSYM entire_program_def,PULL_EXISTS,
                   ml_progTheory.ML_code_def,ml_progTheory.Prog_def]
  in th end

*)
val _ = export_theory();
