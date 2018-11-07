(*
  Functions for constructing a CakeML program (a list of declarations) together
  with the semantic environment resulting from evaluation of the program.
*)
structure ml_progLib :> ml_progLib =
struct

open preamble;
open ml_progTheory astSyntax packLib alist_treeLib comparisonTheory;

(* state *)

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

(* converting nsLookups *)

fun pfun_eq_name const = "nsLookup_" ^ fst (dest_const const) ^ "_pfun_eqs"

val nsLookup_tm = prim_mk_const {Name = "nsLookup", Thy = "namespace"}
val nsLookup_pf_tms = [prim_mk_const {Name = "nsLookup_Mod1", Thy = "ml_prog"},
    prim_mk_const {Name = "nsLookup_Short", Thy = "ml_prog"}]

fun str_dest tm = stringSyntax.fromHOLstring tm |> explode |> map ord

val env_type = type_of (prim_mk_const {Name = "empty_env", Thy = "ml_prog"})

local

val nsLookup_repr_set = let
    val irrefl_thm = MATCH_MP good_cmp_Less_irrefl_trans string_cmp_good
  in alist_treeLib.mk_alist_reprs irrefl_thm EVAL
    str_dest (list_compare Int.compare)
  end

val empty = (Redblackmap.mkDict Term.compare : (term, unit) Redblackmap.dict)
val pfun_eqs_in_repr = ref empty

fun add thm = List.app (add_alist_repr nsLookup_repr_set) (BODY_CONJUNCTS thm)

fun get_pfun_thm c = let
    val c_details = dest_thy_const c
    val thm = DB.fetch (#Thy c_details) (pfun_eq_name c)
    (* ensure that a relevant term is present *)
    val _ = find_term (same_const (hd nsLookup_pf_tms)) (concl thm)
  in (c, thm) end

fun uniq [] = []
  | uniq [x] = [x]
  | uniq (x :: y :: zs) = if same_const x y then uniq (y :: zs)
    else x :: uniq (y :: zs)

fun mk_chain [] chain set = (chain, set)
  | mk_chain ((c, t) :: cs) chain set = if Redblackmap.peek (set, c) = SOME ()
  then mk_chain cs chain set
  else let
    val cs2 = t |> concl |> strip_conj |> map (find_terms is_const o rhs)
        |> List.concat
        |> filter (fn tm => type_of tm = env_type)
        |> Listsort.sort Term.compare |> uniq
        |> filter (fn c => Redblackmap.peek (set, c) = NONE)
        |> List.mapPartial (total get_pfun_thm)
  in if null cs2 then mk_chain cs ((c, t) :: chain)
    (Redblackmap.insert (set, c, ()))
  else mk_chain (cs2 @ (c, t) :: cs) chain set end

in

fun check_in_repr_set tms = let
    val consts = List.concat (map (find_terms is_const) tms)
        |> filter (fn tm => type_of tm = env_type)
        |> Listsort.sort Term.compare |> uniq
        |> List.mapPartial (total get_pfun_thm)
    val (chain, set) = mk_chain consts [] (! pfun_eqs_in_repr)
    val _ = if null chain then raise Empty else ()
    val msg = if length chain > 3
        then "Adding repr thms for " ^ Int.toString (length chain) ^ " consts."
        else "Adding repr thms for ["
            ^ concat (commafy (map (fst o dest_const o fst) chain)) ^ "]."
  in
    print (msg ^ "\n"); List.app (add o snd) (rev chain);
        pfun_eqs_in_repr := set
  end handle Empty => ()

fun pfun_conv tm = let
    val (f, xs) = strip_comb tm
    val _ = length xs = 2 orelse raise UNCHANGED
    val _ = exists (same_const f) (nsLookup_tm :: nsLookup_pf_tms)
        orelse raise UNCHANGED
    val _ = check_in_repr_set [hd xs]
  in reprs_conv nsLookup_repr_set tm end

end

val nsLookup_conv_arg1_xs = [``option_CASE``, ``COND``,
  ``OPTION_CHOICE``, ``(/\)``, ``(\/)``, ``(=)``]

fun nsLookup_arg1_conv conv tm = let
    val (f, xs) = strip_comb tm
    val _ = exists (same_const f) nsLookup_conv_arg1_xs orelse raise UNCHANGED
  in if length xs > 1 then RATOR_CONV (nsLookup_arg1_conv conv) tm
    else if length xs = 1 then RAND_CONV conv tm
    else raise UNCHANGED
  end

val nsLookup_rewrs = List.concat (map BODY_CONJUNCTS
    [nsLookup_eq, option_choice_f_apply, boolTheory.COND_CLAUSES,
        optionTheory.option_case_def, optionTheory.OPTION_CHOICE_def,
        boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES,
        boolTheory.REFL_CLAUSE,
        nsLookup_pf_nsBind, nsLookup_Short_nsAppend, nsLookup_Mod1_nsAppend,
        nsLookup_Short_Bind, nsLookup_Mod1_Bind, nsLookup_merge_env_eqs])

fun nsLookup_conv tm = REPEATC (BETA_CONV ORELSEC FIRST_CONV
  (map REWR_CONV nsLookup_rewrs
    @ map (RATOR_CONV o REWR_CONV) nsLookup_rewrs
    @ map QCHANGED_CONV [nsLookup_arg1_conv nsLookup_conv, pfun_conv])) tm

val () = computeLib.add_convs
    (map (fn t => (t, 2, QCHANGED_CONV nsLookup_conv)) nsLookup_pf_tms)
val () = computeLib.add_thms [nsLookup_eq] computeLib.the_compset

(* helper functions *)

val reduce_conv =
  (* this could be a custom compset, but it's easier to get the
     necessary state updates directly from EVAL
     TODO: Might need more custom rewrites for env-refactor updates
  *)
  EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC
  EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL;

fun prove_assum_by_eval th = let
  val (x,y) = dest_imp (concl th)
  val lemma = reduce_conv x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma)) th
  in MP lemma TRUTH
     handle HOL_ERR e => let
       val _ = print "Failed to reduce:\n\n"
       val _ = print_term x
       val _ = print "\n\nto T. It only reduced to:\n\n"
       val _ = print_term (lemma |> concl |> dest_eq |> snd)
       val _ = print "\n\n"
       in failwith "prove_assum_by_eval: unable to reduce term to T"
     end
  end;

fun is_const_str str = can prim_mk_const {Thy=current_theory(), Name=str};

fun find_name name = let
  val ns = map (#1 o dest_const) (constants (current_theory()))
  fun aux n = let
    val str = name ^ "_" ^ int_to_string n
    in if mem str ns then aux (n+1) else str end
  in aux 0 end

fun ok_char c =
  (#"0" <= c andalso c <= #"9") orelse
  (#"a" <= c andalso c <= #"z") orelse
  (#"A" <= c andalso c <= #"Z") orelse
  mem c [#"_",#"'"]

val ml_name = String.translate
  (fn c => if ok_char c then implode [c] else "c" ^ int_to_string (ord c))

fun define_abbrev for_eval name tm = let
  val name = ml_name name
  val name = (if is_const_str name then find_name name else name)
  val tm = if List.null (free_vars tm) then
             mk_eq(mk_var(name,type_of tm),tm)
           else let
             val vs = free_vars tm |> sort
               (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
             val vars = foldr mk_pair (last vs) (butlast vs)
             val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
             in mk_eq(mk_comb(n,vars),tm) end
  val def_name = name ^ "_def"
  val def = (*Definition.*)new_definition(def_name,tm)
  val _ = if for_eval then computeLib.add_persistent_funs [def_name] else ()
  in def end

val ML_code_tm = prim_mk_const {Name = "ML_code", Thy = "ml_prog"}

fun no_prog_conv conv tm = let
    (* avoid conv operating on the 3rd argument of ML_code, the program *)
    val (f, xs) = strip_comb tm
  in if not (same_const f ML_code_tm) orelse null xs
    then conv tm
    else if length xs = 3 then RATOR_CONV (no_prog_conv conv) tm
    else (RATOR_CONV (no_prog_conv conv) THENC RAND_CONV conv) tm
  end

fun cond_abbrev dest conv eval name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val th = CONV_RULE (conv eval) th
       val tm = dest th
       val def = define_abbrev true (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       in (th,[def]) end end

fun cond_env_abbrev dest conv name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val def = define_abbrev false (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       val env_const = def |> concl |> dest_eq |> fst
       (* derive nsLookup thms *)
       val xs = nsLookup_eq_format |> SPEC env_const |> concl
                   |> find_terms is_eq |> map (fst o dest_eq)
       val rewrs = [def, nsLookup_write_eqs, nsLookup_write_cons_eqs,
                         nsLookup_merge_env_eqs, nsLookup_write_mod_eqs,
                         nsLookup_empty_eqs]
       val pfun_eqs = LIST_CONJ (map (REWRITE_CONV rewrs) xs)
       val thm_name = "nsLookup_" ^ fst (dest_const env_const) ^ "_pfun_eqs"
       val _ = save_thm(thm_name, pfun_eqs)
       in (th,[def]) end end

(*
val (ML_code (ss,envs,vs,th)) = (ML_code (ss,envs,v_def :: vs,th))
*)

fun clean (ML_code (ss,envs,vs,th)) = let
  val (th,new_ss) = cond_abbrev (rand o concl)
                      RAND_CONV reduce_conv "auto_state" th
  val dest = (rand o rator o concl)
  val conv = (RATOR_CONV o RAND_CONV)
  val name = "auto_env"
  val (th,new_envs) = cond_env_abbrev dest conv name th
  in ML_code (new_ss @ ss, new_envs @ envs, vs,  th) end

(* --- *)

val unknown_loc = locationTheory.unknown_loc_def |> concl |> dest_eq |> fst;
val loc = unknown_loc;

val init_state =
  ML_code ([SPEC_ALL init_state_def],[init_env_def],[],ML_code_NIL);

fun open_module mn_str (ML_code (ss,envs,vs,th)) =
  ML_code
    (ss,envs,vs,
     MATCH_MP ML_code_new_module th
     |> SPEC (stringSyntax.fromMLstring mn_str))
  handle HOL_ERR _ => failwith("open_module failed for " ^ thm_to_string th)

fun close_module sig_opt (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_close_module th
(*val v = th |> concl |> dest_forall |> fst
  val sig_tm = (case sig_opt of
                  NONE => mk_const("NONE",type_of v)
                | SOME tm => optionSyntax.mk_some(tm))
  val th = SPEC sig_tm th *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype loc tds_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dtype th
  val th = SPECL [tds_tm,loc] th |> prove_assum_by_eval
  val tm = th |> concl |> rator |> rand |> rator |> rator |> rand
  val th = th |> CONV_RULE ((* (RATOR_CONV o RAND_CONV) *)
            (REWRITE_CONV [EVAL tm] THENC
             SIMP_CONV std_ss [write_tdefs_def,MAP,FLAT,FOLDR,REVERSE_DEF,
                               write_conses_def,ML_code_env_def,LENGTH,
                               semanticPrimitivesTheory.build_constrs_def,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

(*
val loc = unknown_loc
val n_tm = ``"bar"``
val l_tm = ``[]:ast_t list``
*)

fun add_Dexn loc n_tm l_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dexn th
  val th = SPECL [n_tm,l_tm,loc] th
  val tm = th |> concl |> rand |> rator |> rand |> rand |> rator |> rand
  val th = th |> CONV_RULE ((* (RATOR_CONV o RAND_CONV) *)
            (REWRITE_CONV [EVAL tm] THENC
             SIMP_CONV std_ss [MAP,ML_code_env_def,
                               FLAT,FOLDR,REVERSE_DEF,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dtabbrev loc l1_tm l2_tm l3_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dtabbrev th
  val th = SPECL [l1_tm,l2_tm,l3_tm,loc] th
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dlet eval_thm var_str v_thms (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_Dlet_var th
           |> CONV_RULE (no_prog_conv (REWRITE_CONV [ML_code_env_def]))
  val th = MATCH_MP th eval_thm
           handle HOL_ERR _ => failwith "add_Dlet eval_thm does not match"
  val th = th |> SPECL [stringSyntax.fromMLstring var_str,unknown_loc]
  in clean (ML_code (ss,envs,v_thms @ vs,th)) end

(*
val (ML_code (ss,envs,vs,th)) = s
val (n,v,exp) = (v_tm,w,body)
*)

fun add_Dlet_Fun loc n v exp v_name (ML_code (ss,envs,vs,th)) = let
  val let_th = ML_code_Dlet_Fun |> UNDISCH_ALL
    |> SPECL [n,v,exp,loc] |> DISCH_ALL
  val th = MATCH_MP let_th th
    |> CONV_RULE (no_prog_conv (REWRITE_CONV [ML_code_env_def]))
  val tm = th |> concl |> rator |> rand |> rator |> rand
  val v_def = define_abbrev false v_name tm
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                   (REWR_CONV (GSYM v_def)))
  in clean (ML_code (ss,envs,v_def :: vs,th)) end

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> SPEC_ALL |> concl |> rand |> rand |> rand |> rator |> rand
  |> dest_exists |> snd
  |> dest_exists |> snd
  |> dest_exists |> snd |> rand

fun add_Dletrec loc funs v_names (ML_code (ss,envs,vs,th)) = let
  val let_th = ML_code_Dletrec |> UNDISCH_ALL
    |> SPECL [funs,loc] |> DISCH_ALL
  val th = MATCH_MP let_th th
    |> CONV_RULE (no_prog_conv (REWRITE_CONV [ML_code_env_def]))
    |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                  (SIMP_CONV std_ss [write_rec_def,FOLDR,
                    semanticPrimitivesTheory.build_rec_env_def]))
  val tms = rev (find_terms (can (match_term Recclosure_pat)) (concl th))
  val xs = zip v_names tms
  val v_defs = map (fn (x,y) => define_abbrev false x y) xs
  val th = CONV_RULE (no_prog_conv (REWRITE_CONV (map GSYM v_defs))) th
  in clean (ML_code (ss,envs,v_defs @ vs,th)) end

fun get_mod_prefix (ML_code (ss,envs,vs,th)) = let
  val tm = th |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none tm then "" else
       (tm |> rand |> rator |> rand |> stringSyntax.fromHOLstring) ^ "_"
  end

(*
val dec_tm = dec1_tm
*)

fun add_dec dec_tm pick_name s =
  if is_Dexn dec_tm then let
    val (loc,x1,x2) = dest_Dexn dec_tm
    in add_Dexn loc x1 x2 s end
  else if is_Dtype dec_tm then let
    val (loc,x1) = dest_Dtype dec_tm
    in add_Dtype loc x1 s end
  else if is_Dtabbrev dec_tm then let
    val (loc,x1,x2,x3) = dest_Dtabbrev dec_tm
    in add_Dtabbrev loc x1 x2 x3 s end
  else if is_Dletrec dec_tm then let
    val (loc,x1) = dest_Dletrec dec_tm
    val prefix = get_mod_prefix s
    fun f str = prefix ^ pick_name str ^ "_v"
    val xs = listSyntax.dest_list x1 |> fst
               |> map (f o stringSyntax.fromHOLstring o rand o rator)
    in add_Dletrec loc x1 xs s end
  else if is_Dlet dec_tm
          andalso is_Fun (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val (w,body) = dest_Fun f
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (stringSyntax.fromHOLstring v_tm) ^ "_v"
    in add_Dlet_Fun loc v_tm w body v_name s end
  else if is_Dmod dec_tm then let
    val (name,(*spec,*)decs) = dest_Dmod dec_tm
    val ds = fst (listSyntax.dest_list decs)
    val name_str = stringSyntax.fromHOLstring name
    val s = open_module name_str s handle HOL_ERR _ =>
            failwith ("add_top: failed to open module " ^ name_str)
    fun each [] s = s
      | each (d::ds) s = let
           val s = add_dec d pick_name s handle HOL_ERR e =>
                   failwith ("add_top: in module " ^ name_str ^
                             "failed to add " ^ term_to_string d ^ "\n " ^
                             #message e)
           in each ds s end
    val s = each ds s
    val spec = (* SOME (optionSyntax.dest_some spec)
                  handle HOL_ERR _ => *) NONE
    val s = close_module spec s handle HOL_ERR e =>
            failwith ("add_top: failed to close module " ^ name_str ^ "\n " ^
                             #message e)
    in s end
  else failwith("add_dec does not support this shape: " ^ term_to_string dec_tm);

fun remove_snocs (ML_code (ss,envs,vs,th)) = let
  val th = th |> PURE_REWRITE_RULE [listTheory.SNOC_APPEND]
              |> PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC]
              |> PURE_REWRITE_RULE [listTheory.APPEND]
  in (ML_code (ss,envs,vs,th)) end

fun get_thm (ML_code (ss,envs,vs,th)) = th
fun get_v_defs (ML_code (ss,envs,vs,th)) = vs

val ML_code_env_tm = prim_mk_const {Name = "ML_code_env", Thy = "ml_prog"}

fun get_env s = let
  val th = get_thm s
  val code_env = case strip_comb (concl th) of
      (f, [env1, _, _, mn, env2, _])
        => list_mk_icomb (ML_code_env_tm, [env1, mn, env2])
    | _ => failwith("thm concl unexpected: " ^ term_to_string (concl th))
  val rewr_thm = QCONV (REWRITE_CONV [ML_code_env_def]) code_env
  in rhs (concl rewr_thm) end

fun get_state s = get_thm s |> concl |> rand

fun get_next_type_stamp s =
  semanticPrimitivesTheory.state_component_equality
  |> ISPEC (get_state s)
  |> SPEC (get_state s)
  |> concl |> rand |> rand |> rand |> rand |> rator |> rand |> rand
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun get_next_exn_stamp s =
  semanticPrimitivesTheory.state_component_equality
  |> ISPEC (get_state s)
  |> SPEC (get_state s)
  |> concl |> rand |> rand |> rand |> rand |> rand |> rand
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x,y) => add_dec x pick_name y) s ts) end

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) =
  pack_4tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (ss,envs,vs,th)

fun unpack_ml_prog_state th =
  ML_code (unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
    (unpack_list unpack_thm) unpack_thm th)

fun clean_state (ML_code (ss,envs,vs,th)) = let
  fun FIRST_CONJUNCT th = CONJUNCTS th |> hd handle HOL_ERR _ => th
  fun delete_def def = let
    val {Name,Thy,Ty} =
      def |> SPEC_ALL |> FIRST_CONJUNCT |> SPEC_ALL |> concl
          |> dest_eq |> fst |> repeat rator |> dest_thy_const
    in if not (Thy = Theory.current_theory()) then ()
       else Theory.delete_binding (Name ^ "_def") end
  fun split x = ([hd x], tl x) handle Empty => (x,x)
  fun dd ls = let val (ls,ds) = split ls in app delete_def ds; ls end
  val () = app delete_def vs
  in (ML_code (dd ss, dd envs, [], th)) end

fun pick_name str =
  if str = "<" then "lt" else
  if str = ">" then "gt" else
  if str = "<=" then "le" else
  if str = ">=" then "ge" else
  if str = "=" then "eq" else
  if str = "<>" then "neq" else
  if str = "~" then "uminus" else
  if str = "+" then "plus" else
  if str = "-" then "minus" else
  if str = "*" then "times" else
  if str = "/" then "div" else
  if str = "!" then "deref" else
  if str = ":=" then "assign" else
  if str = "@" then "append" else
  if str = "^" then "strcat" else
  if str = "<<" then "lsl" else
  if str = ">>" then "lsr" else
  if str = "~>>" then "asr" else str (* name is fine *)

(*

val s = init_state
val dec1_tm = ``Dlet (ARB 1) (Pvar "f") (Fun "x" (Var (Short "x")))``
val dec2_tm = ``Dlet (ARB 2) (Pvar "g") (Fun "x" (Var (Short "x")))``
val prog_tm = ``[^dec1_tm; ^dec2_tm]``

val s = (add_prog prog_tm pick_name init_state)

val th = get_env s

*)

end
