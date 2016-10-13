open preamble
open configTheory
open backendProofTheory
open configTheory

open x64_targetProofTheory arm6_targetProofTheory arm8_targetProofTheory riscv_targetProofTheory mips_targetProofTheory

val _ = new_theory"configProof";

(* TODO: move *)

val BIJ_support = Q.store_thm("BIJ_support",
  `∀f s' s. BIJ f s' s' ∧ s' ⊆ s ∧ (∀x. x ∉ s' ⇒ f x = x) ⇒ BIJ f s s`,
  rw[BIJ_IFF_INV,SUBSET_DEF]
  >- metis_tac[]
  \\ qexists_tac`λx. if x ∈ s' then g x else x`
  \\ rw[] \\ metis_tac[]);

val FINITE_SURJ = Q.store_thm("FINITE_SURJ",
  `FINITE s ∧ SURJ f s t ⇒ FINITE t`,
  rw[]
  \\ imp_res_tac SURJ_INJ_INV
  \\ imp_res_tac FINITE_INJ);

val SURJ_CARD = Q.store_thm("SURJ_CARD",
  `∀f s t. SURJ f s t ∧ FINITE s ⇒ CARD t ≤ CARD s`,
  rw[]
  \\ imp_res_tac SURJ_INJ_INV
  \\ imp_res_tac INJ_CARD);

val FINITE_SURJ_BIJ = Q.store_thm("FINITE_SURJ_BIJ",
  `FINITE s ∧ SURJ f s t ∧ CARD t = CARD s ⇒ BIJ f s t`,
  rw[BIJ_DEF,INJ_DEF] >- fs[SURJ_DEF]
  \\ CCONTR_TAC
  \\ `SURJ f (s DELETE x) t` by (fs[SURJ_DEF] \\ metis_tac[])
  \\ `FINITE (s DELETE x)` by metis_tac[FINITE_DELETE]
  \\ imp_res_tac SURJ_CARD
  \\ rfs[CARD_DELETE]
  \\ Cases_on`CARD s` \\ rfs[CARD_EQ_0] \\ fs[]);

val CARD_IMAGE_ID_BIJ = Q.store_thm("CARD_IMAGE_ID_BIJ",
  `∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s`,
  rw[]
  \\ `SURJ f s s` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
  \\ `IMAGE f s ⊆ s` by metis_tac[SUBSET_DEF,IN_IMAGE]
  \\ metis_tac[SUBSET_EQ_CARD,IMAGE_FINITE]);

val CARD_IMAGE_EQ_BIJ = Q.store_thm("CARD_IMAGE_EQ_BIJ",
  `∀s. FINITE s ⇒ CARD (IMAGE f s) = CARD s ⇒ BIJ f s (IMAGE f s)`,
  rw[]
  \\ `SURJ f s (IMAGE f s)` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]);

(* -- *)

val find_name_id = Q.store_thm("find_name_id",
  `x ∉ domain names
   ⇒ find_name names x = x`,
  rw[stack_namesTheory.find_name_def]
  \\ fs[domain_lookup] \\ CASE_TAC \\ fs[]);

val find_name_bij_suff = Q.store_thm("find_name_bij_suff",
  `set (toList names) = domain names ⇒
   BIJ (find_name names) UNIV UNIV`,
  strip_tac
  \\ match_mp_tac BIJ_support
  \\ qexists_tac`domain names`
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[stack_namesTheory.find_name_def]
    \\ CASE_TAC \\ fs[domain_lookup])
  \\ `set (toList names) = IMAGE (find_name names) (domain names)`
  by (
    pop_assum kall_tac
    \\ simp[EXTENSION,stack_namesTheory.find_name_def,MEM_toList,domain_lookup]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (qexists_tac`k` \\ fs[])
    \\ metis_tac[] )
  \\ match_mp_tac (MP_CANON CARD_IMAGE_ID_BIJ)
  \\ fs[] \\ rw[] \\ fs[EXTENSION]
  \\ metis_tac[]);

val find_name_bij_iff = Q.store_thm("find_name_bij_iff",
  `BIJ (find_name names) UNIV UNIV ⇔
   set (toList names) = domain names`,
  rw[EQ_IMP_THM,find_name_bij_suff]
  \\ fs[BIJ_IFF_INV]
  \\ rw[EXTENSION,domain_lookup,MEM_toList]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`k=x` >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ `find_name names x = x`
    by (
      simp[stack_namesTheory.find_name_def]
      \\ CASE_TAC \\ fs[] )
    \\ `find_name names k = x`
    by ( simp[stack_namesTheory.find_name_def] )
    \\ metis_tac[] )
  \\ Cases_on`x=v` >- metis_tac[]
  \\ spose_not_then strip_assume_tac
  \\ `find_name names x = v`
  by ( simp[stack_namesTheory.find_name_def] )
  \\ `∀k. find_name names k ≠ x`
  by (
    rw[stack_namesTheory.find_name_def]
    \\ CASE_TAC \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[])
  \\ metis_tac[] )

val names_tac =
  simp[find_name_bij_iff]
  \\ EVAL_TAC
  \\ REWRITE_TAC[SUBSET_DEF] \\ EVAL_TAC
  \\ rpt strip_tac \\ rveq \\ EVAL_TAC

val x64_machine_config_def = Define`
  x64_machine_config = <|target:= x64_target; len_reg:=6 ; ptr_reg := 7 ; caller_saved_regs := [12;13;14]|>`

val x64_conf_ok = prove(``
  conf_ok x64_compiler_config x64_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[x64_machine_config_def,x64_backend_correct]
  >- names_tac
  >>
  fs[markerTheory.Abbrev_def]>>EVAL_TAC>>fs[]);

val arm6_machine_config_def = Define`
  arm6_machine_config = <|target:= arm6_target ; len_reg:=1  ; ptr_reg := 0 ; caller_saved_regs := [8;10;11]|>`

val arm6_conf_ok = prove(``
  conf_ok arm_compiler_config arm6_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm6_machine_config_def,arm6_backend_correct]
  >- names_tac
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>fs[]);

val arm8_machine_config_def = Define`
  arm8_machine_config = <|target:= arm8_target ; len_reg:=1  ; ptr_reg := 0 ; caller_saved_regs := [27;28;29]|>`

val arm8_conf_ok = prove(``
  conf_ok arm8_compiler_config arm8_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >- fs[arm8_machine_config_def,arm8_backend_correct]
  >- names_tac
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val riscv_machine_config_def = Define`
  riscv_machine_config = <|target:= riscv_target; len_reg:= 11 ; ptr_reg :=10 ; caller_saved_regs := [25;26;27]|>`

val riscv_conf_ok = prove(``
  conf_ok riscv_compiler_config riscv_machine_config``,
  simp[conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >- fs[riscv_machine_config_def,riscv_backend_correct]
  >- names_tac
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val mips_machine_config_def = Define`
  mips_machine_config = <|target:= mips_target; len_reg:=5  ; ptr_reg := 4 ; caller_saved_regs := [21;22;23]|>`

val mips_conf_ok = prove(``
  conf_ok mips_compiler_config mips_machine_config``,
  simp[conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >- fs[mips_machine_config_def,mips_backend_correct]
  >- names_tac
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val _ = export_theory();
