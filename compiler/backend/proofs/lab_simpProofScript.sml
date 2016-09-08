open preamble labSemTheory lab_simpTheory lab_to_targetTheory;

val _ = new_theory "lab_simpProof";


val state_rel_def = Define `
state_rel (s1:('a,'ffi) labSem$state) t1 ⇔
          (s1 = t1 with <| code := lab_simp t1.code |>) ∧
          ¬t1.failed`

val evaluate_ind = labSemTheory.evaluate_ind
val evaluate_def = labSemTheory.evaluate_def

infixr 1 $
fun (a $ b) = a b
val case_tac = CASE_TAC
val top_case_tac = BasicProvers.TOP_CASE_TAC

val () = bring_to_front_overload "evaluate" {Name = "evaluate", Thy = "labSem"};

val lab_simp_sec_length = Q.store_thm("lab_simp_sec_length[simp]",
`!s. LENGTH (lab_simp_sec s) = LENGTH s`,
ho_match_mp_tac lab_simp_sec_ind \\
rw [lab_simp_sec_def] \\
every_case_tac \\ fs []
);


val null_lab_simp_sec_cons = Q.store_thm("null_lab_simp_sec_cons[simp]",
`NULL (lab_simp_sec ls) = NULL ls`,
rw[NULL_EQ, GSYM LENGTH_NIL]
);

val last_lab_simp_sec = Q.store_thm("last_lab_simp_sec[simp]",
`!xs. LAST (lab_simp_sec xs) = LAST xs`,
ho_match_mp_tac lab_simp_sec_ind \\
rw[lab_simp_sec_def] \\
every_case_tac \\ fs[LAST_CONS_cond] \\ rw[GSYM NULL_EQ]
);

val pc_to_section_def = Define `
(pc_to_section pc [] = NONE) /\
(pc_to_section 0 ((Section k xs)::ys) = SOME k) /\
(pc_to_section pc ((Section k [])::ys) = pc_to_section pc ys) /\
(pc_to_section (SUC pc) ((Section k (x::xs))::ys) = pc_to_section pc ((Section k xs)::ys))`;

val sec_not_empty_def = Define `
sec_not_empty (Section v ls) = ~NULL ls
`;
val _ = export_rewrites ["sec_not_empty_def"];

val label_ok_def = Define `
(label_ok s (Label n1 n2 k) = (n2 <> 0 /\ n1 = s)) /\
(label_ok s _ = T)
`;
val _ = export_rewrites ["label_ok_def"];

val sec_labels_ok_def = Define `
sec_labels_ok (Section k ls) = EVERY (label_ok k) ls
`;
val _ = export_rewrites ["sec_labels_ok_def"];

val loc_to_pc_lines_def = Define`
(loc_to_pc_lines _ [] = NONE) /\
(loc_to_pc_lines n2 (Label n1 n2' k::xs) =
 if n2 = n2' then SOME 0 else loc_to_pc_lines n2 xs) /\
(loc_to_pc_lines n2 (x::xs) = OPTION_MAP SUC (loc_to_pc_lines n2 xs))
`;

val loc_to_pc_sec_def = Define `
(loc_to_pc_sec n1 n2 [] = NONE) /\
(loc_to_pc_sec n1 n2 ((Section k xs)::ys) =
 if n1 = k then if n2 = 0 then SOME 0 else loc_to_pc_lines n2 xs else
 OPTION_MAP (\x. x + LENGTH (FILTER ($~ o is_Label) xs)) (loc_to_pc_sec n1 n2 ys))
`;

val loc_to_pc_loc_to_pc_sec = Q.store_thm("asdfasdf",
`!n1 n2 sections. EVERY sec_labels_ok sections /\ EVERY sec_not_empty sections ==> loc_to_pc n1 n2 sections = loc_to_pc_sec n1 n2 sections`,
recInduct loc_to_pc_ind \\
rw[] >- (rw[loc_to_pc_sec_def, loc_to_pc_def]) \\
fs [loc_to_pc_sec_def] \\
simp[Once loc_to_pc_def] \\
EVERY_CASE_TAC \\ fs[] \\ rw[loc_to_pc_sec_def, loc_to_pc_lines_def] \\ fs[] \\
qhdtm_x_assum `loc_to_pc` mp_tac \\ simp[Once loc_to_pc_def]

IF_CASES_TAC \\ fs[] >-
(
  case_tac \\ fs [] \\
case_tac \\ fs [] \\

)

                                         )
val loc_to_pc_section_is_pc_to_section = Q.store_thm("loc_to_pc_section_is_pc_to_section",
`!n1 n2 sections pc. EVERY sec_labels_ok sections /\ EVERY sec_not_empty sections /\ loc_to_pc n1 n2 sections = SOME pc ==> pc_to_section pc sections = SOME n1`
recInduct loc_to_pc_ind \\
rw [pc_to_section_def] >-
rw [loc_to_pc_def] >-
(
  pop_assum mp_tac \\ rw[Once loc_to_pc_def] >-
  rw [pc_to_section_def] \\
  qmatch_assum_abbrev_tac `~xx` \\
  Cases_on `xs` \\ fs[] \\
  qpat_x_assum `_ = SOME pc` mp_tac \\
IF_CASES_TAC >-
(
  fs[] \\
  rw[] \\
fs [loc_to_pc_def] \\
rw[pc_to_section_def] \\
) \\
IF_CASES_TAC >-
(
  qmatch_assum_abbrev_tac `~xy` \\
fs[] \\
qpat_x_assum`_ ==> _`mp_tac \\
impl_tac >- (unabbrev_all_tac \\ fs []) \\

  )
           (
             Cases_on `k = n1 /\ n2 = 0` \\
rw[SYM (ASSUME ``0 = pc``)] \\
rw[pc_to_section_def] \\
fs [demorgan_thingy] \\
rw[pc_to_section_def] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\
fs [] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]
fs [] \\

POP_ASSUM (fn th => rw[SYM th]) \\
ASSUME ``0 = pc``] \\

  )

Cases_on `k` \\ Cases_on `pc` >-
fs[pc_to_section_def] \\
           (
rw[pc_to_section_def] \\
           )
  recInduct pc_to_section_ind
)

                                                    )
val pc_to_section_not_none_eq = Q.store_thm("pc_to_section_not_none_eq",
`!pc sections k n. pc_to_section pc sections = SOME n ==> pc_to_section pc sections = pc_to_section pc (Section k []::sections)`,
recInduct pc_to_section_ind \\
rw[pc_to_section_def] \\
                                           )

val pc_to_section_ind = theorem "pc_to_section_ind";
`!pc sections k. pc_to_section pc (Section k []::sections) = pc_to_section pc sections`,
recInduct pc_to_section_ind \\
rw [pc_to_section_def] \\

val asm_fetch_aux_simp_def = Define `
asm_fetch_aux_simp pc code =
 (case asm_fetch_aux pc code of
    | SOME (LabAsm (Jump (Lab n1 n2)) w bytes len) =>
      (case loc_to_pc n1 n2 code of
         | SOME pc' => SOME (if pc' = pc + 1 /\ SOME n1 = pc_to_section pc code /\ n2 <> 0 then Asm (Inst Skip) bytes len else LabAsm (Jump (Lab n1 n2)) w bytes len)
         | NONE => SOME (LabAsm (Jump (Lab n1 n2)) w bytes len)
      )
    | x => x
 )
`

val lab_simp_asm_fetch_aux_simp = Q.store_thm("lab_simp_asm_fetch_aux_simp",
`!s pc. asm_fetch_aux pc (lab_simp s) = asm_fetch_aux_simp pc s`,
recInduct lab_simp_ind \\
rw [lab_simp_def, NULL_EQ] >-
(
  rw[asm_fetch_aux_def, asm_fetch_aux_simp_def, loc_to_pc_def] \\
  every_case_tac \\ fs[] \\ rw []
) \\
rw [asm_fetch_aux_simp_def] \\
Cases_on `lines` \\


val lab_simp_asm_fetch_aux = Q.store_thm("state_rel_asm_fetch_aux",
`!s pc. asm_fetch_aux pc (lab_simp s) = asm_fetch_aux pc s \/
                             (?l w wl k k' n1 n2. asm_fetch_aux pc s = SOME (LabAsm (Jump (Lab n1 n2)) w wl k) /\
asm_fetch_aux (pc + 1) s = SOME (Label n1 n2 k') /\
asm_fetch_aux pc (lab_simp s) = SOME (Asm (Inst Skip) wl k))
  \/ s = []`

ho_match_mp_tac lab_simp_ind\\
rw [lab_simp_def] \\
fs [NULL_EQ] >- (rw [asm_fetch_aux_def] \\ first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]) \\
Cases_on `lines` \\ fs[asm_fetch_aux_def] \\
Cases_on `t` >-
(
  fs[lab_simp_sec_def, asm_fetch_aux_def] \\
    top_case_tac \\ fs [asm_fetch_aux_def] >-
    (
      first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]
    ) >-
    (
    rw[] \\ first_x_assum (qspec_then `pc - 1` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[]
    )
) \\
IF_CASES_TAC >-
(
  Cases_on `h` \\ fs[lab_simp_sec_def] \\
) \\

fs[lab_simp_sec_def, asm_fetch_aux_def] \\
first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def]


    (
      every_case_tac \\ fs [asm_fetch_aux_def, lab_simp_def] \\
                     TRY (first_x_assum (qspec_then `pc - 1` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[] \\ NO_TAC) \\
                     TRY (first_x_assum (qspec_then `pc` strip_assume_tac) \\ rw[lab_simp_def] \\ rfs[] \\ NO_TAC)
    )



                                        )
ho_match_mp_tac asm_fetch_aux_ind\\
simp[asm_fetch_aux_def] \\
conj_tac >-
(
  simp[lab_simp_def, lab_simp_sec_def] \\
  rw[]\\
  rw[lab_simp_def]
) \\
ntac 6 strip_tac\\
reverse IF_CASES_TAC \\
fs[] >-
(
  IF_CASES_TAC >-
  (
    fs[lab_simp_def] \\
Cases_on `ys` \\ fs[lab_simp_sec_def] \\
top_case_tac \\ fs[asm_fetch_aux_def] \\
every_case_tac \\ fs[asm_fetch_aux_def]\\
rw[lab_simp_def, lab_simp_sec_def, asm_fetch_aux_def]
  )
fs[lab_simp_def, lab_simp_sec_def, asm_fetch_aux_def] \\
)

(EVAL_TAC\\ rw[]) \\
EVAL_TAC
conj_tac >-
(
  rpt gen_tac \\
disch_then assume_tac \\
simp[Once lab_simp_def, lab_simp_sec_def] \\
fs []
                                     )
val state_rel_asm_fetch = Q.store_thm("state_rel_asm_fetch",
`state_rel s1 t1 ==>
   (asm_fetch s1 = asm_fetch t1 \/
                   (?wl k. asm_fetch t1 = SOME (Asm (Inst Skip) wl k) /\
?l w wl k. asm_fetch s1 = SOME (LabAsm (Jump l) w wl k)))`
rw [asm_fetch_def, state_rel_def] \\
                                      )

val lab_simp_correct = store_thm("lab_simp_correct",
``!(s1:('a,'ffi) labSem$state) t1 res s2.
  (evaluate s1 = (res,s2)) /\ state_rel s1 t1 ==>
                              ?t2. (evaluate t1 = (res,t2)) /\ state_rel s2 t2``,
ho_match_mp_tac evaluate_ind \\
rw [] \\
qhdtm_x_assum `evaluate` mp_tac \\
simp [Once evaluate_def] \\
IF_CASES_TAC >-
(rw[] \\
(* first_assum takes the first assumption where the continuation succeeds. here
   we take the first that matches the second conjunct, and concl extracts the
   conclusion of a thm (as a term)
  related to asm_exists_tac
  mp_then replaces these eventually? reimplemented in terms of.
  see also qexists_tac `t1`
 *)
first_assum (part_match_exists_tac (el 2 o strip_conj) o concl) \\
simp [] \\ simp [Once evaluate_def] \\ fs [state_rel_def] \\ rw [] \\ fs []
) \\
top_case_tac \\
fs [] \\
>-
(
  CONV_TAC (QUANT_CONV $ LAND_CONV $ LAND_CONV $ REWR_CONV $ evaluate_def)
           )

val _ = export_theory ();
