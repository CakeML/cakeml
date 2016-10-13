open preamble

open ml_translatorTheory ml_translatorLib semanticPrimitivesTheory
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib
open monadsyntax

val _ = new_theory "catfileSystem";

val _ = overload_on ("return", ``SOME``)
val _ = overload_on ("fail", ``NONE``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unit_bind", ``OPTION_IGNORE_BIND``)

val _ = Datatype`
  RO_fs = <| files : (string # string) list ;
             infds : (num # (string # num)) list ;
             stdout : string
  |>
`

val nextFD_def = Define`
  nextFD fsys = LEAST n. ~ MEM n (MAP FST fsys.infds)
`;

val writeStdOut_def = Define`
  writeStdOut c fsys =
    SOME (fsys with stdout := fsys.stdout ++ [c])
`;

val openFile_def = Define`
  openFile fnm fsys =
     let fd = nextFD fsys
     in
       do
          ALOOKUP fsys.files fnm ;
          return (fd, fsys with infds := (nextFD fsys, (fnm, 0)) :: fsys.infds)
       od
`;

val A_DELKEY_def = Define`
  A_DELKEY k alist = FILTER (λp. FST p <> k) alist
`;

val fgetc_def = Define`
  fgetc fd fsys =
    do
       (fnm, off) <- ALOOKUP fsys.infds fd ;
       content <- ALOOKUP fsys.files fnm ;
       if off < LENGTH content then
         return
           (SOME (EL off content),
            fsys with infds := (fd,(fnm,off+1)) :: A_DELKEY fd fsys.infds)
       else
         return (NONE, fsys)
    od
`;

val closeFD_def = Define`
  closeFD fd fsys =
    do
       ALOOKUP fsys.infds fd ;
       return ((), fsys with infds := A_DELKEY fd fsys.infds)
    od
`;

(* ----------------------------------------------------------------------
    Coding RO_fs values as ffi values
   ---------------------------------------------------------------------- *)

val destStr_def = Define`
  (destStr (Str s) = SOME s) ∧
  (destStr _ = NONE)
`
val _ = export_rewrites ["destStr_def"]

val destNum_def = Define`
  (destNum (Num n) = SOME n) ∧
  (destNum _ = NONE)
`;
val _ = export_rewrites ["destNum_def"]

val encode_pair_def = Define`
  encode_pair e1 e2 (x,y) = Cons (e1 x) (e2 y)
`;

val decode_pair_def = Define`
  (decode_pair d1 d2 (Cons f1 f2) =
      do
        x <- d1 f1;
        y <- d2 f2;
        return (x,y)
      od) ∧
  (decode_pair _ _ _ = fail)
`;

val decode_encode_pair = Q.store_thm(
  "decode_encode_pair",
  `(∀x. d1 (e1 x) = return x) ∧ (∀y. d2 (e2 y) = return y) ⇒
   ∀p. decode_pair d1 d2 (encode_pair e1 e2 p) = return p`,
  strip_tac >> Cases >> simp[encode_pair_def, decode_pair_def])

val encode_list_def = Define`
  encode_list e l = List (MAP e l)
`;

val OPT_MMAP_def = Define`
  (OPT_MMAP f [] = return []) ∧
  (OPT_MMAP f (h0::t0) = do h <- f h0 ; t <- OPT_MMAP f t0 ; return (h::t) od)
`;

val decode_list_def = Define`
  (decode_list d (List fs) = OPT_MMAP d fs) ∧
  (decode_list d _ = fail)
`;

val decode_encode_list = Q.store_thm(
  "decode_encode_list[simp]",
  `(∀x. d (e x) = return x) ⇒
   ∀l. decode_list d (encode_list e l) = return l`,
  strip_tac >> simp[decode_list_def, encode_list_def] >> Induct >>
  simp[OPT_MMAP_def]);

val encode_files_def = Define`
  encode_files fs = encode_list (encode_pair Str Str) fs
`;

val encode_fds_def = Define`
  encode_fds fds =
     encode_list (encode_pair Num (encode_pair Str Num)) fds
`;

val encode_def = Define`
  encode fs = cfHeapsBase$Cons
                         (encode_files fs.files)
                         (Cons (encode_fds fs.infds) (Str fs.stdout))
`


val decode_files_def = Define`
  decode_files f = decode_list (decode_pair destStr destStr) f
`

val decode_encode_files = store_thm(
  "decode_encode_files",
  “∀l. decode_files (encode_files l) = return l”,
  simp[encode_files_def, decode_files_def] >>
  simp[decode_encode_list, decode_encode_pair]);

val decode_fds_def = Define`
  decode_fds = decode_list (decode_pair destNum (decode_pair destStr destNum))
`;

val decode_encode_fds = Q.store_thm(
  "decode_encode_fds",
  `decode_fds (encode_fds fds) = return fds`,
  simp[decode_fds_def, encode_fds_def] >>
  simp[decode_encode_list, decode_encode_pair]);

val decode_def = Define`
  (decode (Cons files0 (Cons fds0 stdout0)) =
     do
        files <- decode_files files0 ;
        fds <- decode_fds fds0 ;
        stdout <- destStr stdout0 ;
        return <| files := files ; infds := fds ; stdout := stdout |>
     od) ∧
  (decode _ = fail)
`;

val decode_encode_FS = Q.store_thm(
  "decode_encode_FS",
  `decode (encode fs) = return fs`,
  simp[decode_def, encode_def, decode_encode_files, decode_encode_fds] >>
  simp[theorem "RO_fs_component_equality"]);

val encode_11 = Q.store_thm(
  "encode_11[simp]",
  `encode fs1 = encode fs2 ⇔ fs1 = fs2`,
  metis_tac[decode_encode_FS, SOME_11]);

(* ----------------------------------------------------------------------
    Making the above available in the ffi_next view of the world
   ----------------------------------------------------------------------

    There are four operations to be used in the example:

    1. write char to stdout
    2. open file
    3. read char from file descriptor
    4. close file

    The existing example that handles stdout and the write operation
    labels that operation with 0; we might as well keep that, and then
    number the others above 1, 2 and 3. There should probably be a
    better way of developing this numbering methodically (and
    compositionally?).

   ---------------------------------------------------------------------- *)

val getNullTermStr_def = Define`
  getNullTermStr (bytes : word8 list) =
     let sz = findi 0w bytes
     in
       if sz = LENGTH bytes then NONE
       else SOME(MAP (CHR o w2n) (TAKE sz bytes))
`

val fs_ffi_next_def = Define`
  fs_ffi_next (n:num) bytes fs_ffi =
    do
      fs <- decode fs_ffi ;
      case n of
        0 => do (* write *)
               assert(LENGTH bytes = 1);
               fs' <- writeStdOut (CHR (w2n (HD bytes))) fs;
               return (bytes, encode fs')
             od
      | 1 => do (* open file *)
               fname <- getNullTermStr bytes;
               (fd, fs') <- openFile fname fs;
               assert(fd < 256);
               return ([n2w fd], encode fs')
             od
      | 2 => do
               assert(LENGTH bytes = 1);
               (copt, fs') <- fgetc (w2n (HD bytes)) fs;
               case copt of
                   NONE => return ([255w], encode fs')
                 | SOME c => return ([n2w (ORD c)], encode fs')
             od
      | 3 => do
               assert(LENGTH bytes = 1);
               (_, fs') <- closeFD (w2n (HD bytes)) fs;
               return (bytes, encode fs')
             od
      | _ => fail
    od
`;

val ALOOKUP_EXISTS_IFF = Q.store_thm(
  "ALOOKUP_EXISTS_IFF",
  `(∃v. ALOOKUP alist k = SOME v) ⇔ (∃v. MEM (k,v) alist)`,
  Induct_on `alist` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]);

val closeFD_lemma = Q.store_thm(
  "closeFD_lemma",
  `fd ∈ FDOM (alist_to_fmap fs.infds) ∧ fd < 256
     ⇒
   fs_ffi_next 3 [n2w fd] (encode fs) =
     SOME ([n2w fd], encode (fs with infds updated_by A_DELKEY fd))`,
  simp[fs_ffi_next_def, decode_encode_FS, closeFD_def, PULL_EXISTS,
       theorem "RO_fs_component_equality", MEM_MAP, FORALL_PROD,
       ALOOKUP_EXISTS_IFF] >> metis_tac[]);

val write_lemma = Q.store_thm(
  "write_lemma",
  `fs_ffi_next 0 [c] (encode fs) =
     SOME ([c], encode (fs with stdout := fs.stdout ++ [CHR (w2n c)]))`,
  simp[fs_ffi_next_def, decode_encode_FS, writeStdOut_def]);

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
        (Apps [Var (Long "Word8Array" "copyVec");
               Var (Short "filename_array");
               Var (Short "fname")])
        (App (FFI 1) [Var (Short "filename_array")])`` |> EVAL |> concl |> rand
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

val _ = ml_prog_update (close_module NONE);

val CATFS_def = Define `
  CATFS fs = IO (encode fs) fs_ffi_next [0;1;2;3]`

val CHAR_IO_char1_def = Define `
  CHAR_IO_char1 = SEP_EXISTS w. W8ARRAY onechar_loc [w]`;

val CHAR_IO_fname_def = Define`
  CHAR_IO_fname = SEP_EXISTS v. W8ARRAY filename_loc v * cond (LENGTH v = 256)
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
       (POSTv uv. cond (UNIT_TYPE () uv) * CHAR_IO * CATFS (fs with stdout := fs.stdout ++ [CHR (w2n c)]))``,
  xcf "CharIO.write" (basis_st())
  \\ fs [CHAR_IO_def, CHAR_IO_char1_def] \\ xpull
  \\ xlet `POSTv zv. CATFS fs * W8ARRAY onechar_loc [c] * CHAR_IO_fname *
                     & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [EVAL ``onechar_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC)
  \\ xlet `POSTv _. CATFS (fs with stdout := fs.stdout ++ [CHR (w2n c)]) * W8ARRAY onechar_loc [c] * CHAR_IO_fname`
  THEN1
   (xffi
    \\ simp [EVAL ``onechar_loc``, CATFS_def]
    \\ `MEM 0 [0n;1;2;3]` by EVAL_TAC \\ instantiate \\ xsimpl
    \\ simp[write_lemma])
  \\ xret \\ xsimpl);

(*
val open_spec = Q.store_thm(
  "open_spec",
  ``∀fnm

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
