structure ml_progLib :> ml_progLib =
struct

open preamble;
open ml_progTheory astSyntax packLib;

(* state *)

datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                    (thm list) (* env const definitions *) *
                                    (thm list) (* v const definitions *) *
                                    thm (* ML_code thm *);

(* helper functions *)

val reduce_conv =
  (* this could be a custom compset, but it's easier to get the
     necessary state updates directly from EVAL *)
  EVAL THENC REWRITE_CONV [DISJOINT_set_simp] THENC
  EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL;

fun prove_assum_by_eval th = let
  val (x,y) = dest_imp (concl th)
  val lemma = reduce_conv x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma)) th
  in MP lemma TRUTH end

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
  val tm = if free_vars tm = [] then
             mk_eq(mk_var(name,type_of tm),tm)
           else let
             val vs = free_vars tm |> sort
               (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
             val vars = foldr mk_pair (last vs) (butlast vs)
             val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
             in mk_eq(mk_comb(n,vars),tm) end
  val def_name = name ^ "_def"
  val def = Definition.new_definition(def_name,tm)
  val _ = if for_eval then computeLib.add_persistent_funs [def_name] else ()
  in def end

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

fun clean (ML_code (ss,envs,vs,th)) = let
  val (th,new_ss) = cond_abbrev (rand o concl)
                      RAND_CONV reduce_conv "auto_state" th
  val (th,new_envs) = cond_abbrev (rand o rator o concl)
                        (RATOR_CONV o RAND_CONV) EVAL "auto_env" th
  in ML_code (new_ss @ ss, new_envs @ envs, vs,  th) end

(* --- *)

val init_state =
  ML_code ([SPEC_ALL init_state_def],[init_env_def],[],ML_code_NIL);

fun open_module mn_str (ML_code (ss,envs,vs,th)) =
  ML_code
    (ss,envs,vs,
     MATCH_MP ML_code_new_module th
     |> SPEC (stringSyntax.fromMLstring mn_str)
     |> prove_assum_by_eval)
  handle HOL_ERR _ => failwith("open_module failed for " ^ thm_to_string th)

fun close_module sig_opt (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_close_module th
  val v = th |> concl |> dest_forall |> fst
  val sig_tm = (case sig_opt of
                  NONE => mk_const("NONE",type_of v)
                | SOME tm => optionSyntax.mk_some(tm))
  val th = SPEC sig_tm th
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes BUTLASTN *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype tds_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtype th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtype th
  val th = SPEC tds_tm th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes write_tds *)
  in clean (ML_code (ss,envs,vs,th)) end

(*
val n_tm = ``"bar"``
val l_tm = ``[]:t list``
*)

fun add_Dexn n_tm l_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dexn th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dexn th
  val th = SPECL [n_tm,l_tm] th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) (* removes write_tds *)
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dtabbrev l1_tm l2_tm l3_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtabbrev th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtabbrev th
  val th = SPECL [l1_tm,l2_tm,l3_tm] th
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dlet eval_thm var_str v_thms (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_var th
  val th = MATCH_MP th eval_thm
           handle HOL_ERR _ => failwith "add_Dlet eval_thm does not match"
  val th = th |> SPEC (stringSyntax.fromMLstring var_str)
  in clean (ML_code (ss,envs,v_thms @ vs,th)) end

fun add_Dlet_Fun n v exp v_name (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dlet_Fun th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_Fun th
  val th = SPECL [n,v,exp] th
  val tm = th |> concl |> rator |> rand |> rator |> rand
  val v_def = define_abbrev false v_name tm
  val th = th |> PURE_REWRITE_RULE [GSYM v_def]
  in clean (ML_code (ss,envs,v_def :: vs,th)) end

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> SPEC_ALL |> concl |> rand |> rand |> rand |> rator |> rand
  |> dest_exists |> snd
  |> dest_exists |> snd
  |> dest_exists |> snd |> rand

fun add_Dletrec funs v_names (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dletrec th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dletrec th
  val th = SPEC funs th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                  (SIMP_CONV std_ss [write_rec_def,FOLDR,
                    semanticPrimitivesTheory.build_rec_env_def]))
  val tms = rev (find_terms (can (match_term Recclosure_pat)) (concl th))
  val xs = zip v_names tms
  val v_defs = map (fn (x,y) => define_abbrev false x y) xs
  val th = REWRITE_RULE (map GSYM v_defs) th
  in clean (ML_code (ss,envs,v_defs @ vs,th)) end

fun get_mod_prefix (ML_code (ss,envs,vs,th)) = let
  val tm = th |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none tm then "" else
       (tm |> rand |> rator |> rand |> stringSyntax.fromHOLstring) ^ "_"
  end

fun add_dec pick_name dec_tm s =
  if is_Dexn dec_tm then let
    val (x1,x2) = dest_Dexn dec_tm
    in add_Dexn x1 x2 s end
  else if is_Dtype dec_tm then let
    val x1 = dest_Dtype dec_tm
    in add_Dtype x1 s end
  else if is_Dtabbrev dec_tm then let
    val (x1,x2,x3) = dest_Dtabbrev dec_tm
    in add_Dtabbrev x1 x2 x3 s end
  else if is_Dletrec dec_tm then let
    val x1 = dest_Dletrec dec_tm
    val prefix = get_mod_prefix s
    fun f str = prefix ^ pick_name str ^ "_v"
    val xs = listSyntax.dest_list x1 |> fst
               |> map (f o stringSyntax.fromHOLstring o rand o rator)
    in add_Dletrec x1 xs s end
  else if is_Dlet dec_tm
          andalso is_Fun (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val (w,body) = dest_Fun f
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (stringSyntax.fromHOLstring v_tm) ^ "_v"
    in add_Dlet_Fun v_tm w body v_name s end
  else failwith("add_dec does not support this shape: " ^ term_to_string dec_tm);

fun add_top pick_name top_tm s =
  if is_Tdec top_tm then
    add_dec pick_name (dest_Tdec top_tm) s
    handle HOL_ERR e =>
    failwith ("add_top: failed to add " ^ term_to_string top_tm ^ "\n " ^
                             #message e)
  else let
    val (name,spec,decs) = dest_Tmod top_tm
    val ds = fst (listSyntax.dest_list decs)
    val name_str = stringSyntax.fromHOLstring name
    val s = open_module name_str s handle HOL_ERR _ =>
            failwith ("add_top: failed to open module " ^ name_str)
    fun each [] s = s
      | each (d::ds) s = let
           val s = add_dec pick_name d s handle HOL_ERR e =>
                   failwith ("add_top: in module " ^ name_str ^
                             "failed to add " ^ term_to_string d ^ "\n " ^
                             #message e)
           in each ds s end
    val s = each ds s
    val spec = SOME (optionSyntax.dest_some spec)
               handle HOL_ERR _ => NONE
    val s = close_module spec s handle HOL_ERR e =>
            failwith ("add_top: failed to close module " ^ name_str ^ "\n " ^
                             #message e)
    in s end

fun remove_snocs (ML_code (ss,envs,vs,th)) = let
  val th = th |> PURE_REWRITE_RULE [listTheory.SNOC_APPEND]
              |> PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC]
              |> PURE_REWRITE_RULE [listTheory.APPEND]
  in (ML_code (ss,envs,vs,th)) end

fun get_thm (ML_code (ss,envs,vs,th)) = th
fun get_v_defs (ML_code (ss,envs,vs,th)) = vs

fun get_env s = get_thm s |> concl |> rator |> rand

fun get_state s = get_thm s |> concl |> rand

fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x,y) => add_top pick_name x y) s ts) end

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) =
  pack_4tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (ss,envs,vs,th)

fun unpack_ml_prog_state th =
  ML_code (unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
    (unpack_list unpack_thm) unpack_thm th)

fun clean_state (ML_code (ss,envs,vs,th)) = let
  fun FIRST_CONJUNCT th = CONJUNCTS th |> hd handle HOL_ERR _ => th
  fun delete_def def = let
    val name = def |> SPEC_ALL |> FIRST_CONJUNCT |> SPEC_ALL |> concl
                   |> dest_eq |> fst |> repeat rator |> dest_const |> fst
    in Theory.delete_binding (name ^ "_def") end
  fun dd [] = []
    | dd [def] = [def]
    | dd (def::d::defs) = (delete_def d; dd (def::defs))
  in (ML_code (dd ss,dd envs,tl (dd (TRUTH::vs)),th)) end

(*

val s = init_state
val prog_tm = EVAL ``basis_program`` |> concl |> rand
fun pick_name str =
  if str = "<" then "lt" else
  if str = ">" then "gt" else
  if str = "<=" then "le" else
  if str = ">=" then "ge" else
  if str = "=" then "eq" else
  if str = "~" then "uminus" else
  if str = "+" then "plus" else
  if str = "-" then "minus" else
  if str = "*" then "times" else
  if str = "!" then "deref" else
  if str = ":=" then "update" else str

val th = get_thm (add_prog prog_tm pick_name init_state)
val th = REWRITE_RULE [GSYM (EVAL ``basis_program``)] th

val env = th |> concl |> rator |> rand |> EVAL

*)

end
