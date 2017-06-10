open preamble ml_translatorTheory ml_translatorLib ml_progLib;
open cfTacticsLib basisFunctionsLib;
open rofsFFITheory mlfileioProgTheory ioProgTheory;
open quicksortProgTheory ioProgLib;

val _ = new_theory "sortProg";

val _ = translation_extends"quicksortProg";

(* TODO: move *)
val perm_zip = Q.store_thm ("perm_zip",
  `!l1 l2 l3 l4.
    LENGTH l1 = LENGTH l2 ∧ LENGTH l3 = LENGTH l4 ∧ PERM (ZIP (l1,l2)) (ZIP (l3,l4))
    ⇒
    PERM l1 l3 ∧ PERM l2 l4`,
  rw [] >>
  metis_tac [MAP_ZIP, PERM_MAP]);

val list_type_v_to_list = Q.store_thm ("list_type_v_to_list",
  `!A l v.
    LIST_TYPE A l v ⇒
    ?l'. v_to_list v = SOME l' ∧ LIST_REL A l l'`,
  Induct_on `l` >>
  rw [LIST_TYPE_def, terminationTheory.v_to_list_def] >>
  rw [terminationTheory.v_to_list_def] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  rw []);

val string_list_uniq = Q.store_thm ("string_list_uniq",
  `!l1 l2.
    LIST_REL STRING_TYPE l1 l2 ⇒ l2 = MAP (λs. Litv (StrLit (explode s))) l1`,
  Induct_on `l1` >>
  rw [] >>
  `?s'. h = strlit s'` by metis_tac [mlstringTheory.mlstring_nchotomy] >>
  fs [STRING_TYPE_def]);

val char_lt_total = Q.store_thm ("char_lt_total",
  `!(c1:char) c2. ¬(c1 < c2) ∧ ¬(c2 < c1) ⇒ c1 = c2`,
  rw [char_lt_def, CHAR_EQ_THM]);

val string_lt_total = Q.store_thm ("string_lt_total",
  `!(s1:string) s2. ¬(s1 < s2) ∧ ¬(s2 < s1) ⇒ s1 = s2`,
  ho_match_mp_tac string_lt_ind >>
  rw [string_lt_def, char_lt_total]
  >- (
    Cases_on `s1` >>
    fs [string_lt_def]) >>
  metis_tac [char_lt_total]);

val strict_weak_order_string_cmp = Q.store_thm ("strict_weak_order_string_cmp",
  `strict_weak_order (λs1 s2. explode s1 < explode s2)`,
  rw [strict_weak_order_alt, transitive_def] >>
  metis_tac [string_lt_antisym, string_lt_trans, string_lt_total]);

val wfFS_bumpLineFD = Q.store_thm ("wfFS_bumpLineFD",
  `!fs fd.
    wfFS fs
    ⇒
    wfFS (bumpLineFD fd fs)`,
  rw [bumpLineFD_def] >>
  every_case_tac >>
  fs [wfFS_def] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw [ALIST_FUPDKEY_ALOOKUP]);

val validArg_filename = Q.store_thm ("validArg_filename",
  `validArg (explode x) ∧ STRING_TYPE x v ⇒ FILENAME x v`,
  rw [commandLineFFITheory.validArg_def, FILENAME_def, EVERY_MEM,
      mlstringTheory.LENGTH_explode]);

val validArg_filename_list = Q.store_thm ("validArg_filename_list",
  `!x v. EVERY validArg (MAP explode x) ∧ LIST_TYPE STRING_TYPE x v ⇒ LIST_TYPE FILENAME x v`,
  Induct_on `x` >>
  rw [LIST_TYPE_def, validArg_filename]);

val files_contents_def = Define `
  files_contents fs fnames =
    MAP (\str. str ++ "\n")
      (FLAT (MAP (\fname. splitlines (THE (ALOOKUP fs.files fname))) fnames))`;

val v_to_string_def = Define `
  v_to_string (Litv (StrLit s)) = s`;
(* -- *)

val usage_string_def = Define`
  usage_string = strlit"Usage: sort <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val get_file_contents = process_topdecs `
  fun get_file_contents fd acc =
    case FileIO.inputLine fd of
      NONE => acc
    | SOME l => get_file_contents fd (l::acc);

  fun get_files_contents files acc =
    case files of
      [] => acc
    | file::files =>
      let
        val fd = FileIO.openIn file
        val res = get_file_contents fd acc
      in
        (FileIO.close fd;
         get_files_contents files res)
      end;

  fun sort () =
    let val contents_list =
      case Commandline.arguments () of
        [] => get_file_contents FileIO.stdIn []
      | files => get_files_contents files []
    val contents_array = Array.fromList contents_list
    in
      (quicksort String.< contents_array;
       Array.app print contents_array)
    end
    handle FileIO.BadFileName => print_err "Cannot open file"`;

val _ = append_prog get_file_contents;

(* TODO: these functions are generic, and should probably be moved *)
val get_file_contents_spec = Q.store_thm ("get_file_contents_spec",
  `!fs fd fd_v acc_v acc.
    WORD (n2w fd : word8) fd_v ∧
    validFD fd fs ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_file_contents" (get_ml_prog_state()))
      [fd_v; acc_v]
      (ROFS fs)
      (POSTv strings_v.
        ROFS (bumpAllFD fd fs) *
        &(LIST_TYPE STRING_TYPE
            (MAP implode (REVERSE (MAP (\l. l++"\n") (linesFD fd fs)) ++ acc))
            strings_v))`,
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fd fs)` >>
  rw [] >>
  xcf "get_file_contents" (get_ml_prog_state ()) >>
  reverse(Cases_on`wfFS fs`) >- (fs[ROFS_def] \\ xpull) \\
  xlet
    `POSTv line_v.
      ROFS (bumpLineFD fd fs) *
      &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline fd fs)) line_v`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `emp` >>
    qexists_tac `fs` >>
    qexists_tac `n2w fd` >>
    simp [] >>
    xsimpl >>
    fs [wfFS_def, validFD_def] >>
    first_x_assum drule >>
    rw [] >>
    xsimpl) >>
  Cases_on `FDline fd fs` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xvar >>
    xsimpl >>
    drule FDline_NONE_bumpAll_bumpLine >>
    fs [FDline_NONE_linesFD] >>
    xsimpl)
  >- (
    xlet
      `POSTv new_acc_v.
        ROFS (bumpLineFD fd fs) *
        &LIST_TYPE STRING_TYPE (MAP implode (x::acc)) new_acc_v`
    >- (
      xret >>
      xsimpl >>
      simp [LIST_TYPE_def]) >>
    xapp >>
    xsimpl >>
    qexists_tac `emp` >>
    qexists_tac `bumpLineFD fd fs` >>
    qexists_tac `fd` >>
    qexists_tac `x::acc` >>
    xsimpl >>
    `?l1 lines. linesFD fd fs = l1::lines`
    by (
      Cases_on `linesFD fd fs` >>
      fs [GSYM FDline_NONE_linesFD]) >>
    drule linesFD_eq_cons_imp >>
    rw []
    \\ metis_tac [APPEND, APPEND_ASSOC]));

val get_files_contents_spec = Q.store_thm ("get_files_contents_spec",
  `!fnames_v fnames acc_v acc fs.
    hasFreeFD fs ∧
    LIST_TYPE FILENAME fnames fnames_v ∧
    LIST_TYPE STRING_TYPE (MAP implode acc) acc_v
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "get_files_contents" (get_ml_prog_state ()))
      [fnames_v; acc_v]
      (ROFS fs)
      (POST
        (\strings_v.
          ROFS fs *
          &(LIST_TYPE STRING_TYPE
             (MAP (\str. implode (str ++ "\n"))
               (REVERSE
                 (FLAT
                   (MAP (\fname. splitlines (THE (ALOOKUP fs.files fname))) fnames)))
              ++ (MAP implode acc))
             strings_v ∧
            EVERY (\fname. inFS_fname fs fname) fnames))
        (\e.
          ROFS fs *
          &(BadFileName_exn e ∧
            EXISTS (\fname. ~inFS_fname fs fname) fnames)))`,
  Induct_on `fnames` >>
  rw [] >>
  xcf "get_files_contents" (get_ml_prog_state ()) >>
  fs [LIST_TYPE_def] >>
  xmatch >>
  rw []
  >- (
    xvar >>
    xsimpl) >>
  qmatch_assum_rename_tac `FILENAME fname fname_v` >>
  xlet
    `(POST
       (\wv. &(WORD (n2w (nextFD fs) :word8) wv ∧
               validFD (nextFD fs) (openFileFS fname fs) ∧
               inFS_fname fs fname) *
             ROFS (openFileFS fname fs))
       (\e. &(BadFileName_exn e ∧ ~inFS_fname fs fname) * ROFS fs))`
  >- (
    xapp >>
    xsimpl)
  >- xsimpl >>
  qmatch_assum_abbrev_tac `validFD fd fs'` >>
  xlet
    `POSTv strings_v.
       ROFS (bumpAllFD fd fs') *
       &(LIST_TYPE STRING_TYPE
          (MAP implode (REVERSE (MAP (\l. l++"\n") (linesFD fd fs')) ++ acc))
          strings_v)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `emp` >>
    qexists_tac `fs'` >>
    qexists_tac `fd` >>
    qexists_tac `acc` >>
    xsimpl >>
    metis_tac [wfFS_openFile]) >>
  xlet `POSTv u. ROFS (bumpAllFD fd fs' with infds updated_by A_DELKEY fd)`
  >- (
    xapp >>
    xsimpl >>
    qexists_tac `emp` >>
    qexists_tac `bumpAllFD fd fs'` >>
    qexists_tac `n2w fd` >>
    xsimpl >>
    `fd < 255` by metis_tac [nextFD_ltX] >>
    rw [] >>
    xsimpl) >>
  xapp >>
  xsimpl >>
  qexists_tac `emp` >>
  qexists_tac `fs` >>
  qexists_tac `REVERSE (MAP (λl. STRCAT l "\n") (linesFD fd fs')) ++ acc` >>
  rw [] >>
  `bumpAllFD fd fs' with infds updated_by A_DELKEY fd = fs`
  by (
    rw [RO_fs_component_equality, Abbr`fs'`, Abbr `fd`] >>
    irule A_DELKEY_nextFD_openFileFS >>
    rw [nextFD_ltX]) >>
  xsimpl >>
  fs [REVERSE_APPEND, MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF] >>
  `splitlines (THE (ALOOKUP fs.files fname)) = linesFD fd fs'`
  by (
    simp [linesFD_def, Abbr `fd`, Abbr `fs'`] >>
    drule ALOOKUP_inFS_fname_openFileFS_nextFD >>
    simp [nextFD_ltX] >>
    drule inFS_fname_ALOOKUP_EXISTS >>
    rw [] >>
    rw [] >>
    Cases_on `0 < STRLEN content` >>
    simp [libTheory.the_def] >>
    Cases_on`content` \\ fs[]) >>
  simp []);
(* -- *)

val sort_spec = Q.store_thm ("sort_spec",
  `!cl fs out err.
    (* TODO: until we get STDIN unified with the file system *) LENGTH cl > 1 ∧
    hasFreeFD fs
    ⇒
    app (p : 'ffi ffi_proj)
      ^(fetch_v "sort" (get_ml_prog_state ()))
      [Conv NONE []]
      (ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err)
      (POSTv uv.
        &UNIT_TYPE () uv *
        (SEP_EXISTS out' error.
         &(∃output err_msg. out' = out ++ CONCAT output ∧ error = err ++ err_msg ∧
           if EVERY (\fname. inFS_fname fs fname) (TL (MAP implode cl)) then
             err_msg = "" ∧
             PERM output (files_contents fs (TL (MAP implode cl))) ∧
             SORTED $<= output
            else
             output = [] ∧ err_msg = "Cannot open file")
         * STDOUT out' * STDERR error) *
        (ROFS fs * COMMANDLINE cl))`,
  xcf "sort" (get_ml_prog_state ()) >>
  fs [UNIT_TYPE_def] >>
  xmatch >>
  rw [] >>
  qabbrev_tac `fnames = TL (MAP implode cl)` >>
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) >>
  fs[mlcommandLineProgTheory.wfcl_def] >>
  xhandle
    `POST
      (\unit_v2. SEP_EXISTS output.
        &(PERM output (files_contents fs (TL (MAP implode cl))) ∧ SORTED $<= output) *
       ROFS fs * COMMANDLINE cl * STDOUT (out ++ CONCAT output) * STDERR err *
       &(EVERY (\fname. inFS_fname fs fname) fnames ∧
         UNIT_TYPE () unit_v2))
      (\e. ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
           &(BadFileName_exn e ∧
             EXISTS (\fname. ~inFS_fname fs fname) fnames))` >>
  xsimpl
  >- (
    xlet
      `POSTv a_v.
         ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
         &UNIT_TYPE () a_v`
    >- (
      xret >>
      xsimpl) >>
    xlet
      `POSTv args_v.
        ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
        &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) args_v`
    >- (
      xapp >>
      xsimpl >>
      qexists_tac `ROFS fs * STDOUT out * STDERR err` >>
      qexists_tac `cl` >>
      xsimpl) >>
    xlet
      `POST
         (\strings_v.
            ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
            &(LIST_TYPE STRING_TYPE
               (MAP (\str. implode (str ++ "\n"))
                 (REVERSE
                   (FLAT
                     (MAP (\fname. splitlines (THE (ALOOKUP fs.files fname))) fnames))))
               strings_v ∧
              EVERY (\fname. inFS_fname fs fname) fnames))
         (\e.
            ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
            &(BadFileName_exn e ∧
              EXISTS (\fname. ~inFS_fname fs fname) fnames))` >>
    xsimpl
    >- (
      `?command arg1 args. MAP implode cl = command::arg1::args`
      by (
        Cases_on `cl` >>
        fs [] >>
        Cases_on `t` >>
        fs [] >>
        metis_tac []) >>
      fs [LIST_TYPE_def, Abbr `fnames`] >>
      xmatch >>
      xlet `POSTv nil_v. ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
             &LIST_TYPE STRING_TYPE [] nil_v`
      >- (
        xret >>
        xsimpl >>
        simp [LIST_TYPE_def]) >>
      xapp >>
      xsimpl >>
      qexists_tac `COMMANDLINE cl * STDOUT out * STDERR err` >>
      qexists_tac `fs` >>
      qexists_tac `arg1::args` >>
      qexists_tac `[]` >>
      xsimpl >>
      fs [LIST_TYPE_def] >>
      `MAP explode (MAP implode cl) = MAP explode (command::arg1::args)` by metis_tac [] >>
      fs [MAP_MAP_o, combinTheory.o_DEF, mlstringTheory.explode_implode] >>
      rw [validArg_filename] >>
      induct_on `args` >>
      rw [LIST_TYPE_def, validArg_filename, validArg_filename_list]) >>
    qmatch_assum_abbrev_tac `LIST_TYPE STRING_TYPE strings strings_v` >>
    xlet
      `POSTv array_v.
         ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
         ARRAY array_v (MAP (\s. Litv (StrLit (explode s))) strings)`
    >- (
      xapp_spec (INST_TYPE [``:'a`` |-> ``:mlstring``] mlarrayProgTheory.array_fromList_spec) >>
      xsimpl >>
      qexists_tac `STRING_TYPE` >>
      qexists_tac `strings` >>
      rw [] >>
      imp_res_tac list_type_v_to_list >>
      fs [] >>
      metis_tac [string_list_uniq]) >>
    xlet
      `POSTv u_v. SEP_EXISTS sorted.
         ROFS fs * COMMANDLINE cl * STDOUT out * STDERR err *
         ARRAY array_v (MAP (\s. Litv (StrLit (explode s))) sorted) *
         &(PERM sorted strings ∧ SORTED $<= (MAP explode sorted))`
    >- (
      xapp_spec (INST_TYPE [``:'a`` |-> ``:mlstring``] quicksort_spec) >>
      xsimpl >>
      qexists_tac `strings` >>
      qexists_tac `\s1 s2. explode s1 < explode s2` >>
      qexists_tac `STRING_TYPE` >>
      rw [strict_weak_order_string_cmp]
      >- (
        fs [LIST_REL_EL_EQN] >>
        rw [EL_MAP] >>
        metis_tac [mlstringTheory.implode_def, mlstringTheory.implode_explode])
      >- (
        assume_tac mlstringProgTheory.mlstring_lt_v_thm >>
        fs [mlstringTheory.mlstring_lt_inv_image, inv_image_def])
      >- (
        qexists_tac `elems'` >>
        rw []
        >- metis_tac [perm_zip, LIST_REL_LENGTH, LENGTH_MAP]
        >- (
          `transitive (($<=) : string -> string -> bool)`
          by metis_tac [string_lt_trans, transitive_def, string_le_def] >>
          simp [sorted_map, inv_image_def] >>
          irule SORTED_weaken >>
          qexists_tac `(λx y. ¬(explode y < explode x))` >>
          rw [string_le_def] >>
          metis_tac [string_lt_total])
        >- metis_tac [string_list_uniq])) >>
    fs [] >>
    xapp >>
    xsimpl >>
    qexists_tac `ROFS fs * COMMANDLINE cl * STDERR err` >>
    xsimpl >>
    qexists_tac `\l n. STDOUT (out ++ CONCAT (MAP v_to_string (TAKE n l)))` >>
    xsimpl >>
    rw []
    >- (
      xapp >>
      xsimpl >>
      simp [MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF, v_to_string_def] >>
      qexists_tac `emp` >>
      xsimpl >>
      qexists_tac `EL n sorted` >>
      qexists_tac `out ++ CONCAT (TAKE n (MAP explode sorted))` >>
      simp [ETA_THM, EL_MAP] >>
      xsimpl >>
      rw []
      >- metis_tac [mlstringTheory.implode_explode, mlstringTheory.implode_def] >>
      rw [TAKE_EL_SNOC, EL_MAP, SNOC_APPEND] >>
      xsimpl)
    >- (
      qexists_tac `MAP explode sorted` >>
      simp [MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF, v_to_string_def, ETA_THM] >>
      simp [GSYM MAP_TAKE] >>
      xsimpl >>
      rw [] >>
      drule (INST_TYPE [``:'b`` |-> ``:string``] PERM_MAP) >>
      disch_then (qspec_then `explode` mp_tac) >>
      `~NULL cl` by (Cases_on `cl` >> rw [NULL_DEF]) >>
      simp [Abbr `fnames`, Abbr `strings`, MAP_MAP_o, MAP_REVERSE, combinTheory.o_DEF,
            mlstringTheory.explode_implode, files_contents_def, GSYM MAP_TL]))
  >- (
    fs [UNIT_TYPE_def] >>
    xsimpl >>
    rw [] >>
    qexists_tac `x` >>
    rw [] >>
    xsimpl)
  >- (
    fs [BadFileName_exn_def] >>
    xcases >>
    xsimpl >>
    fs [] >>
    xapp >>
    xsimpl >>
    fs [UNIT_TYPE_def] >>
    qexists_tac `ROFS fs * COMMANDLINE cl * STDOUT out` >>
    xsimpl >>
    qexists_tac `err` >>
    xsimpl >>
    every_case_tac >>
    fs [] >>
    xsimpl >>
    metis_tac [NOT_EVERY]));

val spec = sort_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "sort"
val (sem_thm,prog_tm) = ioProgLib.call_thm (get_ml_prog_state ()) name spec
val sort_prog_def = Define `sort_prog = ^prog_tm`;

val length_gt_1_not_null =
  Q.prove(`LENGTH cls > 1 ⇒ ¬ NULL cls`, rw[NULL_EQ] \\ strip_tac \\ fs[]);

val sort_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM sort_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[wfFS_def,inFS_fname_def,PULL_EXISTS,
                         mlcommandLineProgTheory.wfcl_def,
                         length_gt_1_not_null]
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> curry save_thm "sort_semantics";

val _ = export_theory ();
