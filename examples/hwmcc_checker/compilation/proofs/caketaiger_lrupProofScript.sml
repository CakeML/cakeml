(*
  Compose the end-to-end correctness theorems of caketaiger and of the
  verified LRUP checker cake_lrup: if caketaiger prints SUCCESS and cake_lrup
  verifies each of the CNF files it wrote, then the input model is safe and
  live.
*)
Theory caketaiger_lrupProof
Ancestors
  semanticsProps mlstring fsFFI fsFFIProps TextIOProof syntax_helper dimacs
  aig_to_cnf lrup_arrayFullProg caketaigerProgProof caketaigerProof lrupProof
Libs
  preamble

(* TODO: move to semanticsProps *)
Theorem Terminate_Success_extend_with_resource_limit[local]:
  Terminate Success e ∈ extend_with_resource_limit {Terminate Success io} ⇒
  e = io
Proof
  simp[extend_with_resource_limit_def]
QED

Theorem stdout_add_stdout_output[local]:
  stdout fs init ∧ stdout (add_stdout fs out) (init ^ x) ⇒ out = x
Proof
  strip_tac
  \\ `stdout (add_stdout fs out) (init ^ out)` by simp[stdo_add_stdo]
  \\ `init ^ out = init ^ x` by metis_tac[stdo_UNICITY_R]
  \\ fs[]
QED

(* TODO: move to TextIOProof *)
Theorem file_content_add_stdo[local]:
  stdo fd nm fs init ⇒
  file_content (add_stdo fd nm fs out) f = file_content fs f
Proof
  rw[stdo_def,file_content_def,add_stdo_def,up_stdo_def,fsupdate_def]
  \\ CASE_TAC \\ simp[AFUPDKEY_ALOOKUP]
  \\ CASE_TAC
QED

(* TODO: move to TextIOProof *)
Theorem splitlines_line[local]:
  ¬MEM #"\n" l ⇒
  splitlines (l ++ "\n" ++ r) = l :: splitlines r
Proof
  strip_tac
  \\ mp_tac (Q.INST [`r` |-> `#"\n" :: r`]
               (Q.SPEC `l` splitlines_append_not_exists_l))
  \\ rw[EVERY_MEM, mllistTheory.takeUntil_def]
QED

(* TODO: move to TextIOProof *)
Theorem lines_of_concat[local]:
  ∀ls.
    EVERY (λl. ∃t. l = t ^ «\n» ∧ ¬MEM #"\n" (explode t)) ls ⇒
    lines_of (concat ls) = ls
Proof
  Induct \\ rw[lines_of_def]
  \\ gvs[lines_of_def, concat_cons, splitlines_line]
QED

(* TODO: move to fsFFIProps *)
Theorem all_lines_file_lines_of[local]:
  file_content fs f = SOME c ⇒
  all_lines_file fs f = lines_of (strlit c)
Proof
  fs[file_content_def]>>
  rw[all_lines_file_def,lines_of_def]>>
  every_case_tac>>fs[]
QED

Theorem file_content_get_cnf[local]:
  file_content fs f = SOME txt ⇒
  get_cnf fs f = parse_cnf (lines_of (implode txt))
Proof
  strip_tac
  \\ drule_then assume_tac all_lines_file_lines_of
  \\ gvs[get_cnf_def, inFS_fname_def, file_content_def, AllCaseEqs()]
QED

(* Some observed run of cake_lrup, on a file with contents txt, terminated
   normally and printed «s VERIFIED UNSAT\n» *)
Definition lrup_verified_def:
  lrup_verified txt ⇔
    ∃cl fs mc ms ext evs fs₁ init.
      cake_lrup_run cl fs mc ms ∧ LENGTH cl = 3 ∧
      file_content fs (EL 1 cl) = SOME txt ∧
      Terminate Success evs ∈ machine_sem mc (basis_ffi ext cl fs) ms ∧
      extract_fs ext (cl,fs) evs = SOME fs₁ ∧
      stdout fs init ∧ stdout fs₁ (init ^ «s VERIFIED UNSAT\n»)
End

Theorem lrup_verified_sound:
  lrup_verified txt ⇒
  ∃fml. parse_cnf (lines_of (implode txt)) = SOME fml ∧
        unsatisfiable_cnf (set fml)
Proof
  rw[lrup_verified_def]
  \\ drule_then (qspec_then`ext`strip_assume_tac) lrupProofTheory.machine_code_sound
  \\ `evs = cake_lrup_io_events ext cl fs` by
    metis_tac[SUBSET_DEF, Terminate_Success_extend_with_resource_limit]
  \\ gvs[]
  \\ `STD_streams fs` by fs[cake_lrup_run_def]
  \\ `stdout (add_stderr fs err) init` by simp[stdout_add_stderr]
  \\ `out = «s VERIFIED UNSAT\n»` by metis_tac[stdout_add_stdout_output]
  \\ drule_then assume_tac file_content_get_cnf
  \\ gvs[]
QED

(* The text caketaiger writes for a CNF reads back as that CNF *)
Theorem is_cnf_str_parse_cnf[local]:
  is_cnf_str cs txt ⇒ parse_cnf (lines_of (implode txt)) = SOME cs
Proof
  rw[is_cnf_str_def, lits_within_def]
  \\ `lines_of (concat (print_cnf limit cs)) = print_cnf limit cs` by (
    irule lines_of_concat
    \\ simp[print_cnf_def, EVERY_MAP, print_header_line_newline,
            print_lits_newline])
  \\ simp[]
  \\ irule parse_cnf_print_cnf
  \\ gvs[EVERY_MEM] \\ rw[] \\ res_tac \\ simp[]
QED

Theorem cnf_saved_lrup_verified[local]:
  cnf_saved fs f cs ∧ file_content fs f = SOME txt ∧ lrup_verified txt ⇒
  unsatisfiable_cnf (set cs)
Proof
  rw[cnf_saved_def]
  \\ drule is_cnf_str_parse_cnf \\ strip_tac
  \\ drule lrup_verified_sound \\ strip_tac
  \\ gvs[]
QED

Theorem LIST_REL_cnf_saved_unsat[local]:
  LIST_REL (cnf_saved fs) fnames cnfs ∧
  EVERY (λf. ∃txt. file_content fs f = SOME txt ∧ lrup_verified txt) fnames ⇒
  EVERY (λcs. unsatisfiable_cnf (set cs)) cnfs
Proof
  rw[LIST_REL_EL_EQN, EVERY_EL]
  \\ metis_tac[cnf_saved_lrup_verified]
QED

(* An observed run of caketaiger that printed SUCCESS satisfies main_sem on
   the file system before the print, which has the same file contents *)
Theorem caketaiger_success[local]:
  caketaiger_run cl fs mc ms ∧
  Terminate Success evs ∈ machine_sem mc (basis_ffi ext cl fs) ms ∧
  extract_fs ext (cl,fs) evs = SOME fs₁ ∧
  stdout fs init ∧ stdout fs₁ (init ^ «SUCCESS\n»)
  ⇒
  ∃fs'. main_sem cl fs fs' «SUCCESS\n» ∧
        ∀f. file_content fs₁ f = file_content fs' f
Proof
  strip_tac
  \\ drule_then (qspec_then`ext`strip_assume_tac)
       caketaigerProofTheory.machine_code_sound
  \\ `evs = caketaiger_io_events ext cl fs` by
    metis_tac[SUBSET_DEF, Terminate_Success_extend_with_resource_limit]
  \\ gvs[]
  \\ `out = «SUCCESS\n»` by metis_tac[stdout_add_stdout_output]
  \\ qexists `fs'` \\ gvs[]
  \\ metis_tac[file_content_add_stdo]
QED

Theorem caketaiger_lrup_sound:
  caketaiger_run cl fs mc ms ∧ cnf_files_fresh fs (cl_prefix cl) ∧
  (* caketaiger terminated normally and printed SUCCESS *)
  Terminate Success evs ∈ machine_sem mc (basis_ffi ext cl fs) ms ∧
  extract_fs ext (cl,fs) evs = SOME fs₁ ∧
  stdout fs init ∧ stdout fs₁ (init ^ «SUCCESS\n») ∧
  (* cake_lrup verified the text of each file caketaiger wrote *)
  EVERY (λf. ∃txt. file_content fs₁ f = SOME txt ∧ lrup_verified txt)
    (cnf_fnames (cl_prefix cl))
  ⇒
  ∃maig mreset mnext msafes mcnstrs mlive mlatches mlatch_start mmax_latch.
    get_model fs (EL 1 cl) =
      SOME (maig, mreset, mnext, msafes, mcnstrs, mlive, mlatches,
            mlatch_start, mmax_latch) ∧
    is_safe maig mreset mnext (set mcnstrs) (set mlatches) (set msafes) ∧
    is_live maig mreset mnext (set mcnstrs) (qleft maig)
      (IMAGE set (set (qleft_live mlive))) (set mlatches)
Proof
  rpt strip_tac
  \\ drule_all caketaiger_success \\ strip_tac
  \\ `make_cert_sem fs fs' (EL 1 cl) «SUCCESS\n» (cl_prefix cl)` by
    gvs[main_sem_def]
  \\ pop_assum mp_tac \\ rewrite_tac[make_cert_sem_def]
  \\ disch_then drule \\ strip_tac
  \\ `EVERY (λf. ∃txt. file_content fs' f = SOME txt ∧ lrup_verified txt)
        (cnf_fnames (cl_prefix cl))` by (
    qpat_x_assum `EVERY (λf. ∃txt. file_content fs₁ f = _ ∧ _) _` mp_tac
    \\ simp[])
  \\ drule_all LIST_REL_cnf_saved_unsat \\ strip_tac
  \\ metis_tac[]
QED
