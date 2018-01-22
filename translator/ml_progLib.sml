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

local
  val fast_rewrites = ref ([]:thm list);
  fun has_fast_result lemma = let
    val rhs = lemma |> concl |> dest_eq |> snd
    val c = repeat (fst o dest_comb) rhs
    val cname = dest_const c |> fst
    in mem cname ["F","NONE","mod_defined","nsLookup"] end
    handle HOL_ERR _ => false
in
  fun get_fast_rewrites () = !fast_rewrites
  fun add_fast_rewrite lemma =
    if has_fast_result lemma then
      fast_rewrites := lemma::(!fast_rewrites)
    else ()
end;

fun cond_env_abbrev dest conv name th = let
  val tm = dest th
  val (x,vs) = strip_comb tm handle HOL_ERR _ => (tm,[])
  in if is_const x andalso all is_var vs then (th,[])
     else let
       val def = define_abbrev false (find_name name) tm |> SPEC_ALL
       val th = CONV_RULE (conv (REWR_CONV (GSYM def))) th
       val env_const = def |> concl |> dest_eq |> fst
       (* derive theorem for computeLib *)
       val xs = nsLookup_eq_format |> SPEC env_const |> concl
                   |> find_terms is_eq |> map (fst o dest_eq)
       fun derive_rewrite tm = let
         val lemma = (REWRITE_CONV
                      ([def,nsLookup_write_cons,nsLookup_write,
                        nsLookup_merge_env,nsLookup_write_mod,nsLookup_empty]
                       @ (get_fast_rewrites ())) THENC SIMP_CONV (srw_ss()) []) tm
         val _ = add_fast_rewrite lemma
         in lemma end
       val compute_th = LIST_CONJ (map derive_rewrite xs)
       val thm_name = "nsLookup_" ^ fst (dest_const env_const)
       val _ = save_thm(thm_name ^ "[compute]",compute_th)
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
  in clean (ML_code (ss,envs,vs,th)) end

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype tds_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtype th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtype th
  val th = SPECL [tds_tm,unknown_loc] th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
            (SIMP_CONV std_ss [write_tds_def,MAP,FLAT,FOLDR,REVERSE_DEF,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

(*
val n_tm = ``"bar"``
val l_tm = ``[]:t list``
*)

fun add_Dexn n_tm l_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dexn th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dexn th
  val th = SPECL [n_tm,l_tm,unknown_loc] th |> prove_assum_by_eval
  val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
            (SIMP_CONV std_ss [write_tds_def,MAP,FLAT,FOLDR,REVERSE_DEF,
                               APPEND,namespaceTheory.mk_id_def]))
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dtabbrev l1_tm l2_tm l3_tm (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dtabbrev th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dtabbrev th
  val th = SPECL [l1_tm,l2_tm,l3_tm,unknown_loc] th
  in clean (ML_code (ss,envs,vs,th)) end

fun add_Dlet eval_thm var_str v_thms (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_var th
  val th = MATCH_MP th eval_thm
           handle HOL_ERR _ => failwith "add_Dlet eval_thm does not match"
  val th = th |> SPECL [stringSyntax.fromMLstring var_str,unknown_loc]
  in clean (ML_code (ss,envs,v_thms @ vs,th)) end

(*
val (ML_code (ss,envs,vs,th)) = s
val (n,v,exp) = (v_tm,w,body)
*)

fun add_Dlet_Fun n v exp v_name (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dlet_Fun th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_Fun th
  val th = SPECL [n,v,exp,unknown_loc] th
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

fun add_Dletrec funs v_names (ML_code (ss,envs,vs,th)) = let
  val th = MATCH_MP ML_code_NONE_Dletrec th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dletrec th
  val th = SPECL [funs,unknown_loc] th |> prove_assum_by_eval
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

(*
val dec_tm = dec1_tm
*)

fun add_dec dec_tm pick_name s =
  if is_Dexn dec_tm then let
    val (_,x1,x2) = dest_Dexn dec_tm
    in add_Dexn x1 x2 s end
  else if is_Dtype dec_tm then let
    val (_,x1) = dest_Dtype dec_tm
    in add_Dtype x1 s end
  else if is_Dtabbrev dec_tm then let
    val (_,x1,x2,x3) = dest_Dtabbrev dec_tm
    in add_Dtabbrev x1 x2 x3 s end
  else if is_Dletrec dec_tm then let
    val (_,x1) = dest_Dletrec dec_tm
    val prefix = get_mod_prefix s
    fun f str = prefix ^ pick_name str ^ "_v"
    val xs = listSyntax.dest_list x1 |> fst
               |> map (f o stringSyntax.fromHOLstring o rand o rator)
    in add_Dletrec x1 xs s end
  else if is_Dlet dec_tm
          andalso is_Fun (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (_,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val (w,body) = dest_Fun f
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (stringSyntax.fromHOLstring v_tm) ^ "_v"
    in add_Dlet_Fun v_tm w body v_name s end
  else failwith("add_dec does not support this shape: " ^ term_to_string dec_tm);

fun add_top pick_name top_tm s =
  if is_Tdec top_tm then
    add_dec (dest_Tdec top_tm) pick_name s
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
           val s = add_dec d pick_name s handle HOL_ERR e =>
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

fun get_env s = let
  val th = get_thm s
  val th = MATCH_MP ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ML_code_SOME_Dlet_var th
  in th |> SPEC_ALL |> concl |> dest_imp |> fst
        |> rator |> rator |> rator |> rand end

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
  if str = "^" then "strcat" else str (* name is fine *)

(*
val s = init_state
val dec1_tm = ``Dlet (Pvar "f") (Fun "x" (Var (Short "x")))``
val dec2_tm = ``Dlet (Pvar "g") (Fun "x" (Var (Short "x")))``
val prog_tm = ``[Tdec ^dec1_tm; Tdec ^dec2_tm]``

val s = (add_prog prog_tm pick_name init_state)

val th = get_env s1

val env = th |> concl |> rator |> rand |> EVAL

*)

end
