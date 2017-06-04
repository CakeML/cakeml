open preamble
     ml_translatorLib ml_progLib
     cfTheory cfHeapsTheory cfTacticsLib cfTacticsBaseLib basisFunctionsLib
     stdinFFITheory stdoutFFITheory stderrFFITheory mlcommandLineProgTheory
     cfLetAutoLib

val _ = new_theory "mlcharioProg";

val _ = translation_extends "mlcommandLineProg";

(* CharIO -- CF verified *)

val _ = ml_prog_update (open_module "CharIO");

(* TODO: does this occur more naturally somewhere else in the basis ? *)
val _ = trans "bool_of_byte" `\(w:word8). w <> 0w`
(* -- *)

val e = ``(App Aw8alloc [Lit (IntLit 2); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "read_state_loc" e) "read_state" [])

val e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "write_state_loc" e) "write_state" [])

val _ = ml_prog_update (add_Dlet (derive_eval_thm "write_err_state_loc" e) "write_err_state" [])

val e =
  ``Let NONE (App (FFI "getChar") [Var (Short "read_state")])
     (LetApps "b" (Long "Word8Array" (Short "sub")) [Var (Short "read_state");  Lit (IntLit 0)]
       (LetApps "i" (Long "Word8" (Short "toInt")) [Var (Short "b")]
         (Apps [Var (Long "Char" (Short "chr")); Var (Short "i")])))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"read"`` ``"u"`` e "read_v")

val e =
  ``LetApps "f" (Long "Word8Array" (Short "sub")) [Var (Short "read_state"); Lit (IntLit 1)]
      (Apps [Var (Short "bool_of_byte"); Var (Short "f")])``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"read_failed"`` ``"u"`` e "read_failed_v")

val e =
  ``Let (SOME "i") (Apps [Var (Long "Char" (Short "ord")); Var (Short "c")])
    (Let (SOME "b") (Apps [Var (Long "Word8" (Short "fromInt")); Var (Short "i")])
     (Let (SOME "u") (Apps [Var (Long "Word8Array" (Short "update"));
                          Var (Short "write_state");
                          Lit (IntLit 0); Var (Short "b")])
      (Let NONE (App (FFI "putChar") [Var (Short "write_state")]) (Var (Short "u")))))``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"write"`` ``"c"`` e "write_v")

val e =
  ``Let (SOME "i") (Apps [Var (Long "Char" (Short "ord")); Var (Short "c")])
    (Let (SOME "b") (Apps [Var (Long "Word8" (Short "fromInt")); Var (Short "i")])
     (Let (SOME "u") (Apps [Var (Long "Word8Array" (Short "update"));
                          Var (Short "write_err_state");
                          Lit (IntLit 0); Var (Short "b")])
      (Let NONE (App (FFI "putChar_err") [Var (Short "write_err_state")]) (Var (Short "u")))))``
  |> EVAL |> concl |> rand
val _ = ml_prog_update (add_Dlet_Fun ``"write_err"`` ``"c"`` e "write_err_v")

val _ = ml_prog_update (close_module NONE);

val STDOUT_def = Define `
  STDOUT output =
    IOx stdout_ffi_part output *
    SEP_EXISTS w. W8ARRAY write_state_loc [w]`;

val STDOUT_precond = Q.store_thm("STDOUT_precond",
  `(STDOUT out)
    {FFI_part (Str out) (mk_ffi_next (Str,destStr,[("putChar",ffi_putChar)])) ["putChar"] events;
     Mem 2 (W8array [w])}`,
  rw[STDOUT_def, cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
     stdout_ffi_part_def,set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ fs[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``write_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ fs [set_sepTheory.one_def]
  \\ qexists_tac `w`
  \\ rw[EXTENSION, EQ_IMP_THM]
);

val STDOUT_FFI_part_hprop = Q.store_thm("STDOUT_FFI_part_hprop",
  `FFI_part_hprop (STDOUT x)`,
  rw [STDOUT_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      stdoutFFITheory.stdout_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    EVAL ``read_state_loc``,
    EVAL ``write_state_loc``,
    cfHeapsBaseTheory.W8ARRAY_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ metis_tac[]);

val STDERR_def = Define `
  STDERR output =
    IOx stderr_ffi_part output *
    SEP_EXISTS w. W8ARRAY write_err_state_loc [w]`;

val STDERR_precond = Q.store_thm("STDERR_precond",
  `(STDERR out)
    {FFI_part (Str out) (mk_ffi_next
    (Str,destStr,[("putChar_err",ffi_putChar_err)])) ["putChar_err"] events; Mem 3 (W8array [w])}`,
  rw[STDERR_def, cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
     stderr_ffi_part_def,set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ fs[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``write_err_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ fs [set_sepTheory.one_def]
  \\ qexists_tac `w`
  \\ rw[EXTENSION, EQ_IMP_THM]
);

val STDERR_FFI_part_hprop = Q.store_thm("STDERR_FFI_part_hprop",
  `FFI_part_hprop (STDERR x)`,
  rw [STDERR_def,
      cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
      stderrFFITheory.stderr_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    EVAL ``write_err_state_loc``,
    cfHeapsBaseTheory.W8ARRAY_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ metis_tac[]);

val STDIN_def = Define `
  STDIN input read_failed =
    IOx stdin_ffi_part input *
    SEP_EXISTS w. W8ARRAY read_state_loc [w;if read_failed then 1w else 0w]`;

val STDIN_T_precond = Q.store_thm("STDIN_T_precond",
  `(STDIN inp T)
     {FFI_part (Str inp) (mk_ffi_next (Str,destStr,[("getChar",ffi_getChar)])) ["getChar"] events;
      Mem 1 (W8array [w; 1w])}`,
  rw[STDIN_def, cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
     stdin_ffi_part_def,set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ rw[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``read_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ simp [set_sepTheory.one_def]
  \\ qexists_tac`w`
  \\ rw[EXTENSION,EQ_IMP_THM]);

val STDIN_F_precond = Q.store_thm("STDIN_F_precond",
  `(STDIN inp F)
     {FFI_part (Str inp) (mk_ffi_next (Str,destStr,[("getChar",ffi_getChar)])) ["getChar"] events;
      Mem 1 (W8array [w; 0w])}`,
  rw[STDIN_def, cfHeapsBaseTheory.IO_def, cfHeapsBaseTheory.IOx_def,
     stdin_ffi_part_def,set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES]
  \\ simp[set_sepTheory.one_STAR,GSYM set_sepTheory.STAR_ASSOC]
  \\ rw[cfHeapsBaseTheory.W8ARRAY_def,
        cfHeapsBaseTheory.cell_def,
        EVAL``read_state_loc``,
        set_sepTheory.SEP_EXISTS_THM]
  \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
  \\ simp [set_sepTheory.one_def]
  \\ qexists_tac`w`
  \\ rw[EXTENSION,EQ_IMP_THM]);

val STDIN_FFI_part_hprop = Q.store_thm("STDIN_FFI_part_hprop",
  `FFI_part_hprop (STDIN b x)`,
  rw [STDIN_def,
      cfHeapsBaseTheory.IO_def,cfHeapsBaseTheory.IOx_def,
      stdinFFITheory.stdin_ffi_part_def, cfMainTheory.FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    EVAL ``read_state_loc``,
    EVAL ``write_state_loc``,
    cfHeapsBaseTheory.W8ARRAY_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ metis_tac[]);

val basis_st = get_ml_prog_state;

val read_spec = Q.store_thm ("read_spec",
  `UNIT_TYPE u uv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.read" (basis_st()))
       [uv]
       (STDIN input read_failed)
       (POSTv cv. if input = "" then STDIN input T else
                  cond (CHAR (HD input) cv) * STDIN (TL input) F)`,
  xcf "CharIO.read" (basis_st())
  \\ Cases_on`input = ""` \\ fs[]
  >- (
    fs[STDIN_def] \\ xpull
    \\ xlet `POSTv x. STDIN "" T * cond (UNIT_TYPE () x)`
    >- (
      xffi
      \\ fs[STDIN_def, EVAL ``read_state_loc``, cfHeapsBaseTheory.IOx_def, stdin_ffi_part_def]
      \\ qmatch_goalsub_abbrev_tac`IO s u ns`
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ map_every qexists_tac[`ns`,`u`] \\ rpt(qexists_tac`s`)
      \\ simp[cfHeapsBaseTheory.mk_ffi_next_def,Abbr`u`,Abbr`s`]
      \\ xsimpl \\ fs[ ffi_getChar_def,Abbr`ns`] )
    \\ fs[STDIN_def] \\ xpull
    \\ xlet `POSTv x. STDIN "" T * cond (WORD (w:word8) x)`
    >- (
      xapp \\ xsimpl \\ fs[STDIN_def]
      \\ fs[EVAL``read_state_loc``] \\ xsimpl)
    \\ xlet `POSTv x. STDIN "" T * cond (NUM (w2n w) x)`
    >- ( xapp \\ xsimpl \\ fs[] \\ metis_tac[] )
    \\ rw[STDIN_def] \\ xpull
    \\ xapp \\ xsimpl \\ instantiate
    \\ simp[w2n_lt_256] )
  \\ fs[STDIN_def] \\ xpull
  \\ qmatch_goalsub_abbrev_tac`IOxx input`
  \\ xlet `POSTv x. IOxx (TL input) *
                    W8ARRAY read_state_loc [n2w (ORD (HD input)); 0w]`
  >- (
    xffi
    \\ fs[Abbr`IOxx`,STDIN_def, EVAL ``read_state_loc``,cfHeapsBaseTheory.IOx_def,stdin_ffi_part_def]
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ map_every qexists_tac[`ns`,`u`]
    \\ xsimpl
    \\ simp[cfHeapsBaseTheory.mk_ffi_next_def,Abbr`u`,Abbr`s`]
    \\ fs[ffi_getChar_def] \\ Cases_on `input` \\ rw[Abbr`ns`])
  \\ xlet `POSTv x. STDIN (TL input) F * cond (WORD ((n2w(ORD(HD input))):word8) x)`
  >- (
    xapp \\ xsimpl \\ fs[STDIN_def]
    \\ fs[EVAL``read_state_loc``] \\ xsimpl)
  \\ xlet `POSTv x. STDIN (TL input) F * cond (NUM (ORD (HD input)) x)`
  >- (xapp \\ xsimpl \\ instantiate \\ simp[ORD_BOUND])
  \\ rw[STDIN_def] \\ xpull
  \\ xapp \\ xsimpl \\ instantiate
  \\ simp[CHR_ORD,ORD_BOUND])

val read_failed_spec = Q.store_thm("read_failed_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "CharIO.read_failed" (basis_st()))
      [uv]
      (STDIN input read_failed)
      (POSTv bv. STDIN input read_failed * cond (BOOL read_failed bv))`,
  xcf "CharIO.read_failed" (basis_st())
  \\ fs[STDIN_def] \\ xpull
  \\ xlet `POSTv x. STDIN input read_failed * cond (WORD (if read_failed then 1w else (0w:word8)) x)`
  >- (
    xapp
    \\ fs[STDIN_def]
    \\ fs[EVAL``read_state_loc``]
    \\ xsimpl)
  \\ fs[STDIN_def] \\ xpull
  \\ xapp
  \\ instantiate
  \\ xsimpl
  \\ rw[]);

val write_spec = Q.store_thm ("write_spec",
  `CHAR c cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.write" (basis_st()))
       [cv]
       (STDOUT output)
       (POSTv uv. cond (UNIT_TYPE () uv) * STDOUT (output ++ [c]))`,
  xcf "CharIO.write" (basis_st())
  \\ fs [STDOUT_def] \\ xpull
  \\ qmatch_goalsub_abbrev_tac`IOxx output`
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_state_loc [w] *
                     & (NUM (ORD c) zv)`
  >- (xapp \\ xsimpl \\ metis_tac[])
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_state_loc [w] *
                     & (WORD ((n2w (ORD c)):word8) zv)`
  >- (xapp \\ xsimpl \\ metis_tac[])
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_state_loc [n2w (ORD c)] *
                     & UNIT_TYPE () zv`
  THEN1
   (xapp \\ xsimpl \\ fs [EVAL ``write_state_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC)
  \\ xlet `POSTv _. IOxx (output ++ [c]) * W8ARRAY write_state_loc [n2w (ORD c)]`
  THEN1
   (xffi
    \\ fs [EVAL ``write_state_loc``, STDOUT_def, Abbr`IOxx`, cfHeapsBaseTheory.IOx_def,stdout_ffi_part_def]
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev) \\ map_every qexists_tac[`ns`,`u`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ EVAL_TAC
    \\ simp[ORD_BOUND,CHR_ORD])
  \\ xret \\ xsimpl);


val write_err_spec = Q.store_thm ("write_err_spec",
  `CHAR c cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.write_err" (basis_st()))
       [cv]
       (STDERR output)
       (POSTv uv. cond (UNIT_TYPE () uv) * STDERR (output ++ [c]))`,
  xcf "CharIO.write_err" (basis_st())
  \\ fs [STDERR_def] \\ xpull
  \\ qmatch_goalsub_abbrev_tac`IOxx output`
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_err_state_loc [w] *
                     & (NUM (ORD c) zv)`
  >- (xapp \\ xsimpl \\ metis_tac[])
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_err_state_loc [w] *
                     & (WORD ((n2w (ORD c)):word8) zv)`
  >- (xapp \\ xsimpl \\ metis_tac[])
  \\ xlet `POSTv zv. IOxx output * W8ARRAY write_err_state_loc [n2w (ORD c)] *
                     & UNIT_TYPE () zv`
  THEN1
   (xapp \\ xsimpl \\ fs [EVAL ``write_err_state_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC)
  \\ xlet `POSTv _. IOxx (output ++ [c]) * W8ARRAY write_err_state_loc [n2w (ORD c)]`
  THEN1
   (xffi
    \\ fs [EVAL ``write_err_state_loc``, STDOUT_def, Abbr`IOxx`,
            cfHeapsBaseTheory.IOx_def,stderr_ffi_part_def]
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev) \\ map_every qexists_tac[`ns`,`u`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ EVAL_TAC
    \\ simp[ORD_BOUND,CHR_ORD])
  \\ xret \\ xsimpl);

(* Theorems used by xlet_auto *)
(*val FRAME_UNIQUE_IO = Q.store_thm("FRAME_UNIQUE_IO",
`!s. VALID_HEAP s ==>
!s1 u1 ns1 s2 u2 ns2 H1 H2. (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
(IO s1 u1 ns1 * H1) s /\ (IO s2 u2 ns2 * H2) s ==> s2 = s1 /\ u2 = u1 /\ ns2 = ns1`,
rpt (FIRST[GEN_TAC, DISCH_TAC]) >>
fs[IO_def]

fun instantiate_valid_ffi_heap_assum th (g as (asl, w)) =
  let
      val filter = Term.match_term ``(IO s u ns * H) h``
      val [(tm_s1, ty_s1), (tm_s2, ty_s2)] = mapfilter filter asl
      fun inst_type ty_s = List.map (fn {redex = x, residue = y} => (Term.inst ty_s x |-> y))
      val tm_s1 = inst_type ty_s1 tm_s1
      val tm_s2 = inst_type ty_s2 tm_s2
      fun find_inst tm_s =
	let
	    val s = Term.subst tm_s ``s:ffi``
	    val u = Term.subst tm_s ``u:tvarN -> word8 list -> ffi -> (word8 list # ffi) option``
	    val ns = Term.subst tm_s ``ns:tvarN list``
	    val H = Term.subst tm_s ``H:hprop``
	in
	    (s, u, ns, H)
	end
      val (s1, u1, ns1, H1) = find_inst tm_s1
      val (s2, u2, ns2, H2) = find_inst tm_s2
  in
      ASSUME_TAC (SPECL [s1, u1, ns1, s2, u2, ns2, H1, H2] th) g
  end;

val UNIQUE_STDOUT = Q.store_thm("UNIQUE_STDOUT",
`!s. VALID_HEAP s ==> !out1 out2 H1 H2. (STDOUT out1 * H1) s /\ (STDOUT out2 * H2) s ==> out2 = out1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[STDOUT_def, IOx_def, stdout_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[]);

val UNIQUE_STDERR = Q.store_thm("UNIQUE_STDERR",
`!s. VALID_HEAP s ==> !err1 err2 H1 H2. (STDERR err1 * H1) s /\ (STDERR err2 * H2) s ==> err2 = err1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[STDERR_def, IOx_def, stderr_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[]);

val UNIQUE_STDIN = Q.store_thm("UNIQUE_STDIN",
`!s H1 H2 in1 in2 b1 b2.
VALID_HEAP s ==> (STDIN in1 b1 * H1) s /\ (STDIN in2 b2 * H2) s ==> in2 = in1 /\ b2 = b1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def]
>-(
    fs[STDIN_def, IOx_def, stdin_ffi_part_def] >>
    fs[GSYM STAR_ASSOC] >>
    LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
    fs[]
) >>
fs[STDIN_def] >>
fs[SEP_CLAUSES, SEP_EXISTS_THM] >>
`(W8ARRAY read_state_loc [w; if b1 then 1w else 0w] * (IOx stdin_ffi_part in1 * H1)) s` by metis_tac[STAR_ASSOC, STAR_COMM] >>
`(W8ARRAY read_state_loc [w'; if b2 then 1w else 0w] * (IOx stdin_ffi_part in2 * H2)) s` by metis_tac[STAR_ASSOC, STAR_COMM] >>
IMP_RES_TAC UNIQUE_W8ARRAYS >>
rw[] >>
Cases_on `b1` >> (Cases_on `b2` >> fs[]));

val UNIQUE_ROFS = Q.store_thm("UNIQUE_ROFS",
`!s fs1 fs2 H1 H2. VALID_HEAP s ==> (ROFS fs1 * H1) s /\ (ROFS fs2 * H2) s ==> fs2 = fs1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[ROFS_def, IOx_def, rofs_ffi_part_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV (list_ss) []) x |> ASSUME_TAC) >>
`(∃pn. pn = "open" ∨ pn = "fgetc" ∨ pn = "close" ∨ pn = "isEof") = T` by (rw[] >> metis_tac[]) >>
fs[]);

val UNIQUE_COMMANDLINE = Q.store_thm("UNIQUE_COMMANDLINE",
`!s cl1 cl2 H1 H2. VALID_HEAP s ==>
(COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1`,
rw[VALID_HEAP_def, VALID_FFI_HEAP_def] >>
fs[COMMANDLINE_def, IOx_def, commandLine_ffi_part_def, encode_def, encode_list_def] >>
fs[GSYM STAR_ASSOC] >>
LAST_X_ASSUM instantiate_valid_ffi_heap_assum >>
fs[] >>
POP_ASSUM IMP_RES_TAC >>
sg `!l1 l2. (MAP Str l1 = MAP Str l2) ==> l2 = l1`
>-(
    Induct_on `l2` >-(rw[])>>
    rw[] >> fs[] >>
    Cases_on `l1` >-(fs[])>>  fs[]
) >>
fs[]);

val _ = add_frame_thms [UNIQUE_STDIN,
		  UNIQUE_STDOUT,
		  UNIQUE_STDERR,
		  UNIQUE_COMMANDLINE,
		  UNIQUE_ROFS]
*)


val _ = export_theory()
