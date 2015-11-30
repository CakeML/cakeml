open preamble
     source_to_modTheory
     mod_to_conTheory
     con_to_decTheory
     dec_to_exhTheory
     exh_to_patTheory
     pat_to_closTheory
     clos_to_bvlTheory
     bvl_to_bviTheory
     bvi_to_bvpTheory
     bvp_to_wordTheory
     word_to_stackTheory
     stack_to_labTheory
     lab_to_targetTheory

val _ = new_theory"backend";

val _ = Datatype`config =
  <| source_conf : source_to_mod$config
   ; mod_conf : mod_to_con$config
   ; clos_conf : clos_to_bvl$config
   ; bvp_conf : bvp_to_word$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; asm_conf : 'a asm_config
   |>`;

val compile_def = Define`
  compile c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    let (c',p) = mod_to_con$compile c.mod_conf p in
    let c = c with mod_conf := c' in
    let (n,e) = con_to_dec$compile c.source_conf.next_global p in
    let c = c with source_conf updated_by (λc. c with next_global := n) in
    let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
    let e = exh_to_pat$compile e in
    let e = pat_to_clos$compile e in
    let (c',p) = clos_to_bvl$compile c.clos_conf e in
    let c = c with clos_conf := c' in
    let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc p in
    let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
    let p = bvi_to_bvp$compile_prog p in
    let p = bvp_to_word$compile c.bvp_conf p in
    let p = word_to_stack$compile c.clos_conf.start c.asm_conf p in
    let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
    let b = lab_to_target$compile c.asm_conf c.lab_conf p in
    OPTION_MAP (λb. (b,c)) b`;

val to_mod_def = Define`
  to_mod c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    (c,p)`;

val to_con_def = Define`
  to_con c p =
  let (c,p) = to_mod c p in
  let (c',p) = mod_to_con$compile c.mod_conf p in
  let c = c with mod_conf := c' in
  (c,p)`;

val to_dec_def = Define`
  to_dec c p =
  let (c,p) = to_con c p in
  let (n,e) = con_to_dec$compile c.source_conf.next_global p in
  let c = c with source_conf updated_by (λc. c with next_global := n) in
  (c,e)`;

val to_exh_def = Define`
  to_exh c p =
  let (c,e) = to_dec c p in
  let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
  (c,e)`;

val to_pat_def = Define`
  to_pat c p =
  let (c,e) = to_exh c p in
  let e = exh_to_pat$compile e in
  (c,e)`;

val to_clos_def = Define`
  to_clos c p =
  let (c,e) = to_pat c p in
  let e = pat_to_clos$compile e in
  (c,e)`;

val to_bvl_def = Define`
  to_bvl c p =
  let (c,e) = to_clos c p in
  let (c',p) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  (c,p)`;

val to_bvi_def = Define`
  to_bvi c p =
  let (c,p) = to_bvl c p in
  let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc p in
  let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
  (c,p)`;

val to_bvp_def = Define`
  to_bvp c p =
  let (c,p) = to_bvi c p in
  let p = bvi_to_bvp$compile_prog p in
  (c,p)`;

val to_word_def = Define`
  to_word c p =
  let (c,p) = to_bvp c p in
  let p = bvp_to_word$compile c.bvp_conf p in
  (c,p)`;

val to_stack_def = Define`
  to_stack c p =
  let (c,p) = to_word c p in
  let p = word_to_stack$compile c.clos_conf.start c.asm_conf p in
  (c,p)`;

val to_lab_def = Define`
  to_lab c p =
  let (c,p) = to_stack c p in
  let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
  (c,p)`;

val to_target_def = Define`
  to_target c p =
  let (c,p) = to_lab c p in
  let b = lab_to_target$compile c.asm_conf c.lab_conf p in
  OPTION_MAP (λb. (b,c)) b`;

val compile_eq_to_target = Q.store_thm("compile_eq_to_target",
  `compile = to_target`,
  rw[FUN_EQ_THM,compile_def,
     to_target_def,
     to_lab_def,
     to_stack_def,
     to_word_def,
     to_bvp_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_pat_def,
     to_exh_def,
     to_dec_def,
     to_con_def,
     to_mod_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (rw[] >> fs[] >> rw[] >> rfs[])));

val from_lab_def = Define`
  from_lab c p =
  let b = lab_to_target$compile c.asm_conf c.lab_conf p in
  OPTION_MAP (λb. (b,c)) b`;

val from_stack_def = Define`
  from_stack c p =
  let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
  from_lab c p`;

val from_word_def = Define`
  from_word c p =
  let p = word_to_stack$compile c.clos_conf.start c.asm_conf p in
  from_stack c p`;

val from_bvp_def = Define`
  from_bvp c p =
  let p = bvp_to_word$compile c.bvp_conf p in
  from_word c p`;

val from_bvi_def = Define`
  from_bvi c p =
  let p = bvi_to_bvp$compile_prog p in
  from_bvp c p`;

val from_bvl_def = Define`
  from_bvl c p =
  let (s,p,n) = bvl_to_bvi$compile c.clos_conf.start c.clos_conf.next_loc p in
  let c = c with clos_conf updated_by (λc. c with <| start := s; next_loc := n |>) in
  from_bvi c p`;

val from_clos_def = Define`
  from_clos c e =
  let (c',p) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  from_bvl c p`;

val from_pat_def = Define`
  from_pat c e =
  let e = pat_to_clos$compile e in
  from_clos c e`;

val from_exh_def = Define`
  from_exh c e =
  let e = exh_to_pat$compile e in
  from_pat c e`;

val from_dec_def = Define`
  from_dec c e =
  let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
  from_exh c e`;

val from_con_def = Define`
  from_con c p =
  let (n,e) = con_to_dec$compile c.source_conf.next_global p in
  let c = c with source_conf updated_by (λc. c with next_global := n) in
  from_dec c e`;

val from_mod_def = Define`
  from_mod c p =
  let (c',p) = mod_to_con$compile c.mod_conf p in
  let c = c with mod_conf := c' in
  from_con c p`;

val from_source_def = Define`
  from_source c p =
  let (c',p) = source_to_mod$compile c.source_conf p in
  let c = c with source_conf := c' in
  from_mod c p`;

val compile_eq_from_source = Q.store_thm("compile_eq_from_source",
  `compile = from_source`,
  rw[FUN_EQ_THM,compile_def,
     from_source_def,
     from_lab_def,
     from_stack_def,
     from_word_def,
     from_bvp_def,
     from_bvi_def,
     from_bvl_def,
     from_clos_def,
     from_pat_def,
     from_exh_def,
     from_dec_def,
     from_con_def,
     from_mod_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (rw[] >> fs[] >> rw[] >> rfs[])));

val _ = export_theory();
