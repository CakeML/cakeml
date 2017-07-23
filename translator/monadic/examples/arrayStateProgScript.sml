open ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib

val _ = new_theory "arrayStateProg"
val _ = ParseExtras.temp_loose_equality();
(* val _ = ParseExtras.temp_tight_equality(); *)
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``
val _ = register_type ``:'a option``

(* For the dynamic store initialisation *)
val _ = register_type ``:('a, 'b) exc``;

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| the_num : num ;
	          the_num_array : num list ;
                  the_int_array : int list |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | ReadError of unit | WriteError of unit`;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

(* Monadic functions to handle the exceptions *)
val failwith_def = Define `
  ((failwith msg) : (state_refs, 'a, state_exn) M) = \state. (Failure (Fail msg), state)`;

val raise_read_error_def = Define `
((raise_read_error ()) :(state_refs, unit, state_exn) M) = \state. (Failure (ReadError ()), state)`;

val raise_write_error_def = Define `
((raise_write_error ()) :(state_refs, unit, state_exn) M) = \state. (Failure (WriteError ()), state)`;

val handle_fail_def = Define `
  handle_fail x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (Fail t), state) => f t state
    | other => other`;

val handle_read_error_def = Define `
  handle_read_error x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (ReadError t), state) => f t state
    | other => other`;

val handle_write_error_def = Define `
  handle_write_error x f = \state.
    dtcase ((x : (state_refs, 'a, state_exn) M) state) of
    | (Failure (WriteError t), state) => f t state
    | other => other`;

(* Define the functions used to access the elements of the state_refs data_type *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_name, get_the_num_def, set_the_num_def),
     (the_num_array_name, get_the_num_array_def, set_the_num_array_def),
     (the_int_array_name, get_the_int_array_def, set_the_int_array_def)] = access_funs;

val sub_exn = ``ReadError ()``;
val update_exn = ``WriteError ()``;
val array_access_funs = (List.tl access_funs);
val array_manip_funs = define_Marray_manip_funs array_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)];

val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val arrays_init_values = [init_num_array_def, init_int_array_def];
val arrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip array_manip_funs arrays_init_values);

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val EXN_RI = ``STATE_EXN_TYPE``;
val exc_ri_def = STATE_EXN_TYPE_def;

val refs_manip_list = List.map (fn (x, _, y, z) => (x, y, z)) refs_init_list;
val arrays_manip_list = List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) arrays_init_list;

val translation_parameters = translate_dynamic_init_fixed_store refs_manip_list arrays_manip_list store_hprop_name state_type exc_ri_def;

(* Initialize the store *)
(* val (translation_parameters, store_trans_result) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type STATE_EXN_TYPE_def; *)

(* Initialize the translation *)
(* val store_pred_exists = #store_pred_exists_thm store_trans_result; *)
val store_pred_exists = NONE : thm option;
val _ = init_translation translation_parameters store_pred_exists EXN_RI [];

(* Prove the theorems necessary to handle the exceptions *)
val raise_functions = [failwith_def, raise_read_error_def, raise_write_error_def];
val handle_functions = [handle_fail_def, handle_read_error_def, handle_write_error_def];
val exn_thms = add_raise_handle_functions raise_functions handle_functions STATE_EXN_TYPE_def

(* Monadic translations *)
val test2_def = Define `test2 n = the_num_array_sub n`;
val def = test2_def |> m_translate;

val test3_def = Define `test3 n x = update_the_num_array n x`;
val def = test2_def |> m_translate;

val test4_def = Define `test4 n x = alloc_the_num_array n x`;
val def = test3_def |> m_translate;

val test5_def = Define `
test5 n z =
    do
	alloc_the_num_array n z;
        return ()
    od`;
val def = test5_def |> m_translate;
val test5_trans_th = m_translate test5_def;

val test6_def = Define `
test6 n z = test5 n z`;
val def = test6_def;
val test6_trans_th = m_translate test6_def;

val test7_def = Define `
(test7 [] = return 0) /\ ((test7 (x::l)) = (do x <- test7 l; return (x+1) od))`;
val def = test7_def;
val test7_v_th = m_translate test7_def;

val test8_def = Define `
test8 l = test7 l`;
val test8_v_th = m_translate test8_def;


(* New definitions for ml_monadBaseTheory *)
(* val insert_monad_def = Define `
insert_monad (x : ('a, 'b, 'c) M) init_state =
case (x init_state) of
(Success y, s) => Success y
| (Failure e, s) => Failure s`; *)

val _ = ParseExtras.temp_tight_equality();

val handle_one_def = Define `
handle_one vname cname exp1 exp2 =
(Handle exp1 [(Pcon (SOME (Short cname)) [Pvar vname], Let (SOME vname) (Con (SOME (Short cname)) [Var(Short vname)]) exp2)])`;

(* val handle_mult_def = Define `
handle_mult varname (cname::cons_names) exp1 exp2 =
(Handle (handle_mult varname cons_names exp1 exp2) [(Pcon (SOME (Short cname)) [Pvar varname], Let (SOME varname) (Con (SOME (Short cname)) [Var(Short varname)]) exp2)]) /\
handle_mult varname [] exp1 exp2 = exp1`; *)

val handle_mult_def = Define `
handle_mult varname (cname::cons_names) exp1 exp2 =
handle_one varname cname (handle_mult varname cons_names exp1 exp2) exp2 /\
handle_mult varname [] exp1 exp2 = exp1`;

val insert_monad_def = Define `
insert_monad (x : ('a, 'b, 'c) M) f state =
case x state of
    (Success y, s) => y
  | (Failure e, s) => f e`;

(* Proof for exceptions defined in the same module *)
val Eval_PreH_def = Define `
Eval_PreH env exp P H =
!(s:unit semanticPrimitives$state) p refs. REFS_PRED H refs p s ==>
!junk. ?s2 res refs2.
evaluate F env (s with refs := s.refs ++ junk) exp (s2, Rval res) /\
P res /\ REFS_PRED_FRAME H p (refs, s) (refs2, s2)`;

(* Target 1 *)
val handle_mult_append = Q.prove(
`!cons_names1 cons_names2 vname exp1 exp2.
handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2 =
handle_mult vname cons_names1 (handle_mult vname cons_names2 exp1 exp2) exp2`,
Induct >-(rw[handle_mult_def])
\\ rw[handle_mult_def]);

(* val evaluate_handle_mult_append_Rraise = Q.prove(
`!cons_names1 cons_names2 vname exp1 exp2 exp3 env s.
evaluate F env s (handle_mult vname cons_names2 exp1 exp2) (s2, Rerr (Rraise e)) ==>
evaluate F env s (handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2) =
evaluate F env s (handle_mult vname cons_names1 (Raise e) exp2)`,
Induct >-(rw[handle_mult_def])
\\ rw[handle_mult_def]
\\ rw[handle_one_def]
\\ irule EQ_EXT
\\ rw[]
\\ Cases_on `x`
\\ Cases_on `r`
\\ rw[Once evaluate_cases]
\\ CONV_TAC (RAND_CONV (REWRITE_CONV[Once evaluate_cases]))
val (asl, w) = top_goal()

rand w
; *)

(*
Q.prove(
`!cons_names1 cons_names2 vname exp1 exp2 exp3 env s.
evaluate F env s (handle_mult vname cons_names2 exp1 exp2) (s2, res)
evaluate F env s (handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2) =
evaluate F env s (handle_mult vname cons_names1 exp3 exp2)`,
Induct >-(rw[handle_mult_def])
\\ rw[handle_mult_def]
\\ rw[handle_one_def]
\\ irule EQ_EXT
\\ rw[]
\\ Cases_on `x`
\\ Cases_on `r`
\\ rw[Once evaluate_cases]
\\ CONV_TAC (RAND_CONV (REWRITE_CONV[Once evaluate_cases]))
val (asl, w) = top_goal()

rand w
;*)

val evaluate_handle_mult_Rval = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rval res) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rval res)`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_mult_Rabort = Q.prove(`!cons_names vname exp1 exp2 res s s2 env.
 evaluate F env s exp1 (s2, Rerr (Rabort res)) ==>
 evaluate F env s (handle_mult vname cons_names exp1 exp2) (s2, Rerr (Rabort res))`,
Induct
>-(rw[handle_mult_def, handle_one_def])
\\ rw[handle_mult_def, handle_one_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_THROUGH = Q.prove(`
!cons_names exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names ==>
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F env s exp1`,
Induct >-(rw[handle_mult_def])
\\ rw[]
\\ rw[handle_mult_def]
\\ irule EQ_EXT
\\ rw[]
\\ last_assum (fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
\\ Cases_on `x`
\\ fs[]
\\ rw[handle_one_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[ALL_DISTINCT, pat_bindings_def]
\\ rw[Once evaluate_cases]);

val evaluate_handle_compos_suffices = Q.prove(`evaluate F env s exp3 = evaluate F env s exp4 ==>
(evaluate F env s
  (Handle exp3
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]) =
evaluate F env s
  (Handle exp4
     [(Pcon (SOME (Short h)) [Pvar vname],
       Let (SOME vname) (Con (SOME (Short h)) [Var (Short vname)])
         exp2)]))`,
rw[]
\\ irule EQ_EXT
\\ rw[Once evaluate_cases]
\\ rw[Once EQ_SYM_EQ]
\\ rw[Once evaluate_cases]);

val evaluate_handle_EXN_PARTIAL_THROUGH = Q.prove(`!cons_names1 cons_names2 exp1 exp2 vname s s2 ev env.
evaluate F env s exp1 (s2, Rerr (Rraise ev)) ==>
EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2 ==>
evaluate F env s (handle_mult vname (cons_names1 ++ cons_names2) exp1 exp2) =
evaluate F env s (handle_mult vname cons_names1 exp1 exp2)`,
Induct
>-(
    rw[handle_mult_def]
    \\ IMP_RES_TAC evaluate_handle_EXN_THROUGH
    \\ fs[])
\\ rw[handle_mult_def, handle_one_def]
\\ irule evaluate_handle_compos_suffices
\\ last_assum IMP_RES_TAC
\\ fs[]);

val EVERY_CONJ_1 = GSYM EVERY_CONJ |> SPEC_ALL |> EQ_IMP_RULE |> fst |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO];

val evaluate_handle_mult_CASE_MODULE = Q.prove(`
!cons_names module_name EXN_TYPE TYPE vname a exp1 exp2 s s2 e ev env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
(∀e ev ev1 cname.
EXN_TYPE e ev ==>
ev = Conv (SOME (cname,TypeExn (Long module_name (Short cname)))) [ev1] ==>
Eval (write vname ev (write vname ev1 env)) exp2 a) ==>
evaluate F env s exp1 (s2, Rerr (Rraise ev))
/\ EXN_TYPE e ev ==>
?cname ev'. ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev'] /\
evaluate F env s (handle_mult vname cons_names exp1 exp2) =
evaluate F (write vname ev (write vname ev' env)) s2 exp2`,
rw[]
\\ last_x_assum IMP_RES_TAC
\\ qexists_tac `cname`
\\ qexists_tac `ev'`
\\ simp[]
\\ sg `?cons_names1 cons_names2. cons_names = cons_names1 ++ [cname] ++ cons_names2`
>-(
    fs[MEM_EL]
    \\ sg `?cons_names1 cons_names'. cons_names = cons_names1 ++ cons_names' /\ LENGTH cons_names1 = n`
    >-(
	qexists_tac `TAKE n cons_names`
        \\ qexists_tac `DROP n cons_names`
        \\ simp[TAKE_DROP, LENGTH_TAKE])
    \\ qexists_tac `cons_names1`
    \\ fs[]
    \\ qexists_tac `TL cons_names'`
    \\ Cases_on `cons_names'` >> fs[]
    \\ rw[]
    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
    \\ `~NULL ([h] ++ t)` by fs[]
    \\ IMP_RES_TAC EL_LENGTH_APPEND
    \\ fs[])
\\ sg `EVERY (\cname. pmatch env.c s2.refs (Pcon (SOME (Short cname)) [Pvar vname]) ev [] = No_match) cons_names2`
>-(
    fs[ALL_DISTINCT_APPEND]
    \\ fs[EVERY_MEM]
    \\ rw[]
    \\ fs[EL_APPEND1, EL_APPEND2]
    \\ rw[Once pmatch_def]
    \\ fs[lookup_cons_def]
    \\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
    \\ `cname' <> cname` by (first_assum(qspec_then `cname` ASSUME_TAC) \\ fs[] \\ metis_tac[])    \\ fs[])
\\ fs[EL_APPEND1, EL_APPEND2]
\\ rw[]
\\ IMP_RES_TAC evaluate_handle_EXN_PARTIAL_THROUGH
\\ fs[]
\\ rw[handle_mult_append, handle_mult_def]
\\ fs[Eval_def]
\\ qpat_x_assum `!e' ev1 cname'. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `s2.refs ++ []` STRIP_ASSUME_TAC)
\\ first_x_assum (fn x => MATCH_MP evaluate_empty_state_IMP_junk x |> STRIP_ASSUME_TAC)
\\ fs[with_same_refs]
\\ sg `evaluate F env s (handle_mult vname cons_names1 (handle_one vname cname exp1 exp2) exp2) =
    evaluate F env s (handle_one vname cname exp1 exp2)`
>-(
    sg `?s' res. evaluate F env s (handle_one vname cname exp1 exp2) (s', Rval res)`
    >-(
	rw[handle_one_def]
	\\ rw[Once evaluate_cases]
	\\ last_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
	\\ rw[Once evaluate_cases]
	\\ fs[pat_bindings_def]
	\\ fs[pmatch_def]
	\\ fs[EVERY_MEM, lookup_cons_def]
	\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
	\\ fs[write_def]
	\\ fs[with_same_refs]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ rw[Once evaluate_cases]
	\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
	\\ fs[namespaceTheory.id_to_n_def]
	\\ first_x_assum(fn x => simp[MATCH_MP evaluate_unique_result x]))
    \\ first_assum(fn x => MATCH_MP evaluate_handle_mult_Rval x |> ASSUME_TAC)
    \\ first_x_assum(qspecl_then [`cons_names1`, `vname`, `exp2`] ASSUME_TAC)
    \\ irule EQ_EXT
    \\ rw[]
    \\ Cases_on `x`
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ first_x_assum(fn x => MATCH_MP evaluate_unique_result x |> ASSUME_TAC)
    \\ fs[])
\\ rw[]
\\ rw[handle_one_def]
\\ irule EQ_EXT
\\ rw[]
\\ Cases_on `x`
\\ rw[Once evaluate_cases]
\\ qpat_assum `evaluate F env s exp1 R` (fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ fs[pat_bindings_def]
\\ fs[pmatch_def]
\\ fs[EVERY_MEM, lookup_cons_def]
\\ fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]
\\ fs[namespaceTheory.id_to_n_def]
\\ fs[write_def]
\\ fs[with_same_refs]
\\ pop_assum(fn x => ALL_TAC)
\\ first_assum(fn x => simp[MATCH_MP evaluate_unique_result x])
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ rw[Once evaluate_cases]
\\ fs[do_con_check_def, build_conv_def, namespaceTheory.nsOptBind_def]);

(* Target *)
``
!cons_names module_name vname TYPE EXN_TYPE x1 x2 exp1 exp2 H init_state env.
(!e ev. EXN_TYPE e ev ==> ?ev' e' cname.
MEM cname cons_names /\
ev = Conv (SOME (cname, TypeExn (Long module_name (Short cname)))) [ev']) ==>
EVERY (\cname. lookup_cons cname env = SOME (1,TypeExn (Long module_name (Short cname)))) cons_names ==>
(ALL_DISTINCT cons_names) ==>
EvalM env exp1 (MONAD TYPE EXN_TYPE x1) H ==>
Eval env exp2 ((EXN_TYPE --> TYPE) x2) ==>
Eval_PreH env (handle_mult vname cons_names exp1 exp2) (TYPE (insert_monad x1 x2 init_state)) H``

rw[]
\\ rw[Eval_PreH_def]
\\ fs[EvalM_def]
\\ IMP_RES_TAC REFS_PRED_APPEND
\\ qpat_x_assum `!s p refs. P` IMP_RES_TAC
\\ first_x_assum(qspec_then `junk` STRIP_ASSUME_TAC)
\\ fs[REFS_PRED_FRAME_def]

\\ `?res junk'. evaluate F env (s with refs := s.refs ++ junk) (s with refs := s.refs ++ junk ++ junk', res)
\\ 
DB.find "REFS_PRED_FRAME_append"

DB.apropos ``REFS_PRED H refs p (s with refs := s.refs ++ junk)``

evaluate F env s exp1 (s2, Rerr (Rraise ev))
DB.thy "list" 
  |> DB.find_in "EXISTS_UNIQUE"

val _ = export_theory ();
