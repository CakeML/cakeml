open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open libTheory;
open libPropsTheory;
open intLang1Theory;
open intLang2Theory;
open toIntLang1ProofTheory;
open evalPropsTheory;

val _ = new_theory "toIntLang2Proof";

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  wf_rel_tac `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  induct_on `ps` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" pat_to_i2_def pat_to_i2_ind;

val (exp_to_i2_def, exp_to_i2_ind) =
  tprove_no_defn ((exp_to_i2_def, exp_to_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,e) => exp_i1_size e
                                        | INR (INL (x,es)) => exp_i16_size es
                                        | INR (INR (INL (x,pes))) => exp_i13_size pes
                                        | INR (INR (INR (x,funs))) => exp_i11_size funs)` >>
  srw_tac [ARITH_ss] [exp_i1_size_def]);
val _ = register "exp_to_i2" exp_to_i2_def exp_to_i2_ind;

val (pmatch_i2_def, pmatch_i2_ind) =
  tprove_no_defn ((pmatch_i2_def, pmatch_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,p,y,z) => pat_i2_size p
                                        | INR (x,ps,y,z) => pat_i21_size ps)` >>
  srw_tac [ARITH_ss] [pat_i2_size_def]);
val _ = register "pmatch_i2" pmatch_i1_def pmatch_i2_ind;

val (do_eq_i2_def, do_eq_i2_ind) =
  tprove_no_defn ((do_eq_i2_def, do_eq_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y) => v_i2_size x
                                        | INR (xs,ys) => v_i23_size xs)`);
val _ = register "do_eq_i2" do_eq_i2_def do_eq_i2_ind;

val lookup_type_tag_def = Define `
(lookup_type_tag NONE cenv = SOME tuple_tag) ∧
(lookup_type_tag (SOME cn) (next,env,type_cenv,inv) = FLOOKUP type_cenv cn)`;

val v_to_i2_def = tDefine "v_to_i2" `
 (v_to_i2 cenv (Litv_i1 l) = SOME (Litv_i2 l)) ∧
 (v_to_i2 cenv (Conv_i1 cn vs) =
   case lookup_type_tag cn cenv of
        NONE => NONE
      | SOME tag => 
          case vs_to_i2 cenv vs of
               NONE => NONE
             | SOME vs' => SOME (Conv_i2 tag vs')) ∧
 (v_to_i2 cenv (Closure_i1 (cenv',env) x e) =
   case env_to_i2 cenv env of
        NONE => NONE
      | SOME env' => 
          SOME (Closure_i2 env' x (exp_to_i2 cenv e))) ∧
 (v_to_i2 cenv (Recclosure_i1 (cenv',env) funs x) =
   case env_to_i2 cenv env of
        NONE => NONE
      | SOME env' => 
          SOME (Recclosure_i2 env' (funs_to_i2 cenv funs) x)) ∧
 (v_to_i2 cenv (Loc_i1 l) = SOME (Loc_i2 l)) ∧
 (vs_to_i2 cenv [] = SOME []) ∧
 (vs_to_i2 cenv (v::vs) =
   case v_to_i2 cenv v of
      NONE => NONE
    | SOME v' =>
        case vs_to_i2 cenv vs of
             NONE => NONE
           | SOME vs' => SOME (v'::vs')) ∧
 (env_to_i2 cenv [] = SOME []) ∧
 (env_to_i2 cenv ((x,v)::env) =
   case v_to_i2 cenv v of
      NONE => NONE
    | SOME v' =>
        case env_to_i2 cenv env of
             NONE => NONE
           | SOME env' => SOME ((x,v')::env'))`
cheat;

val fmap_inverse_def = Define `
fmap_inverse m1 m2 =
  !k. k ∈ FDOM m1 ⇒ ?v. FLOOKUP m1 k = SOME v ∧ FLOOKUP m2 v = SOME k`;

val cenv_inv_def = Define `
cenv_inv cenv (next,lex_cenv,type_cenv,inverse_cenv) ⇔
  (!id n. FLOOKUP lex_cenv id = SOME n ⇒ 
          ?l t. lookup_con_id id cenv = SOME (l,t) ∧
                FLOOKUP type_cenv (id_to_n id,t) = SOME n) ∧
  (fmap_inverse type_cenv inverse_cenv) ∧
  (fmap_inverse inverse_cenv type_cenv)`;

val length_vs_to_i2 = Q.prove (
`!vs cenv vs'. 
  vs_to_i2 cenv vs = SOME vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i2_def] >>
 fs [] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 metis_tac []);

val match_result_to_i2_def = Define 
`(match_result_to_i2 cenv (Match env) (Match env_i2) ⇔ 
   env_to_i2 cenv env = SOME env_i2) ∧
 (match_result_to_i2 cenv No_match No_match = T) ∧
 (match_result_to_i2 cenv Match_type_error Match_type_error = T) ∧
 (match_result_to_i2 cenv _ _ = F)`;

val pmatch_to_i2_correct = Q.prove (
`(!cenv s p v env r env_i2 s_i2 v_i2 cenv'.
  r ≠ Match_type_error ∧
  cenv_inv cenv cenv' ∧
  pmatch_i1 cenv s p v env = r ∧
  s_to_i2' cenv' s s_i2 ∧
  v_to_i2 cenv' v = SOME v_i2 ∧
  env_to_i2 cenv' env = SOME env_i2
  ⇒
  ?r_i2.
    pmatch_i2 s_i2 (pat_to_i2 cenv' p) v_i2 env_i2 = r_i2 ∧
    match_result_to_i2 cenv' r r_i2) ∧
 (!cenv s ps vs env r env_i2 s_i2 vs_i2 cenv'.
  r ≠ Match_type_error ∧
  cenv_inv cenv cenv' ∧
  pmatch_list_i1 cenv s ps vs env = r ∧
  s_to_i2' cenv' s s_i2 ∧
  vs_to_i2 cenv' vs = SOME vs_i2 ∧
  env_to_i2 cenv' env = SOME env_i2
  ⇒
  ?r_i2.
    pmatch_list_i2 s_i2 (MAP (pat_to_i2 cenv') ps) vs_i2 env_i2 = r_i2 ∧
    match_result_to_i2 cenv' r r_i2)`,

 ho_match_mp_tac pmatch_i1_ind >>
 rw [pmatch_i1_def, pmatch_i2_def] >>
 fs [match_result_to_i2_def, bind_def, pmatch_i2_def, v_to_i2_def, pat_to_i2_def] >>
 rw [pmatch_i2_def, match_result_to_i2_def] >>
 >- (every_case_tac >>
     fs [match_result_to_i2_def, pmatch_i2_def] >>
     rw [match_result_to_i2_def, pmatch_i2_def]
     >- metis_tac []

val _ = export_theory ();
