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
    val chain_names = map (fst o dest_const o fst) chain
    val msg_names = if length chain > 3
        then List.take (chain_names, 2) @ ["..."] @ [List.last chain_names]
        else chain_names
    val msg = "Adding nsLookup representation thms for "
        ^ (if length chain > 3 then Int.toString (length chain) ^ " consts ["
            else "[") ^ concat (commafy msg_names) ^ "]\n"
  in
    print msg; List.app (add o snd) (rev chain);
        pfun_eqs_in_repr := set
  end handle Empty => ()

fun nsLookup_pf_conv tm = let
    val (f, xs) = strip_comb tm
    val _ = length xs = 2 orelse raise UNCHANGED
    val _ = exists (same_const f) (nsLookup_tm :: nsLookup_pf_tms)
        orelse raise UNCHANGED
    val _ = check_in_repr_set [hd xs]
  in reprs_conv nsLookup_repr_set tm end

end

val nsLookup_conv_arg1_xs = [boolSyntax.conjunction, boolSyntax.disjunction,
  boolSyntax.equality, boolSyntax.conditional, optionSyntax.option_case_tm,
  prim_mk_const {Name = "OPTION_CHOICE", Thy = "option"}]

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
        nsLookup_Short_Bind, nsLookup_Mod1_Bind, nsLookup_merge_env_eqs,
        nsLookup_empty_eqs, alistTheory.ALOOKUP_def])

fun nsLookup_conv tm = REPEATC (BETA_CONV ORELSEC FIRST_CONV
  (map REWR_CONV nsLookup_rewrs
    @ map (RATOR_CONV o REWR_CONV) nsLookup_rewrs
    @ map QCHANGED_CONV [nsLookup_arg1_conv nsLookup_conv,
        nsLookup_pf_conv])) tm

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

fun prove_assum_by_conv conv th = let
  val (x,y) = dest_imp (concl th)
  val lemma1 = conv x
  val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV lemma1)) th
  in MP lemma TRUTH
     handle HOL_ERR e => let
       val _ = print "Failed to convert:\n\n"
       val _ = print_term x
       val _ = print "\n\nto T. It only reduced to:\n\n"
       val _ = print_term (lemma1 |> concl |> dest_eq |> snd)
       val _ = print "\n\n"
       in failwith "prove_assum_by_conv: unable to reduce term to T"
     end
  end;

val prove_assum_by_eval = prove_assum_by_conv reduce_conv

val eval_every_exp_one_con_check =
  SIMP_CONV (srw_ss()) [semanticPrimitivesTheory.do_con_check_def,ML_code_env_def]
  THENC DEPTH_CONV nsLookup_conv
  THENC reduce_conv;

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
  val def = Definition.new_definition(def_name,tm)
  val _ = if for_eval then computeLib.add_persistent_funs [def_name] else ()
  in def end

val ML_code_tm = prim_mk_const {Name = "ML_code", Thy = "ml_prog"}

fun dest_ML_code_block tm = let
    (* mn might or might not be a syntactic tuple,
        so make sure the list length is fixed. *)
    val (mn, elts) = pairSyntax.dest_pair tm
  in mn :: pairSyntax.strip_pair elts end

fun ML_code_blocks tm = let
    val (f, xs) = strip_comb tm
    val _ = (same_const f ML_code_tm andalso length xs = 3)
        orelse (print_term tm; failwith "ML_code_blocks: not ML_code")
    val (block_tms, _) = listSyntax.dest_list (hd (tl xs))
  in map dest_ML_code_block block_tms end

val ML_code_open_env = List.last o hd o ML_code_blocks

val let_conv = REWR_CONV LET_THM THENC (TRY_CONV BETA_CONV)

fun let_conv_ML_upd conv nm (th, code) = let
    val msg = "let_conv_ML_upd: " ^ nm ^ ": not let"
    val _ = is_let (concl th) orelse (print (msg ^ ":\n\n");
        print_thm th; failwith msg)
    val th = CONV_RULE (RAND_CONV conv THENC let_conv) th
  in (th, code) end

fun cond_let_abbrev cond for_eval name conv op_nm th = let
    val msg = "cond_let_abbrev: " ^ op_nm ^ ": not let"
    val _ = is_let (concl th) orelse (print (msg ^ ":\n\n");
        print_thm th; failwith msg)
    val th = CONV_RULE (RAND_CONV conv) th
    val (_, tm) = dest_let (concl th)
    val (f, xs) = strip_comb tm
  in if cond andalso is_const f andalso all is_var xs
     then (CONV_RULE let_conv th, [])
     else let
       val def = define_abbrev for_eval name tm |> SPEC_ALL
       in (CONV_RULE (RAND_CONV (REWR_CONV (GSYM def))
           THENC let_conv) th, [def])
       end
  end

fun auto_name sfx = current_theory () ^ "_" ^ sfx

fun let_st_abbrev conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
    val (th, abbrev_defs) = cond_let_abbrev true true
        (auto_name "st") conv op_nm th
  in (th, ML_code (abbrev_defs @ ss, envs, vs, ml_th)) end

fun derive_nsLookup_thms def = let
    val env_const = def |> concl |> dest_eq |> fst
    (* derive nsLookup thms *)
    val xs = nsLookup_eq_format |> SPEC env_const |> concl
                |> find_terms is_eq |> map (fst o dest_eq)
    val rewrs = [def, nsLookup_write_eqs, nsLookup_write_cons_eqs,
                      nsLookup_merge_env_eqs, nsLookup_write_mod_eqs,
                      nsLookup_empty_eqs]
    val pfun_eqs = LIST_CONJ (map (REWRITE_CONV rewrs) xs)
    val thm_name = "nsLookup_" ^ fst (dest_const env_const) ^ "_pfun_eqs"
  in save_thm (thm_name, pfun_eqs) end

fun let_env_abbrev conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
    val (th, abbrev_defs) = cond_let_abbrev true false
        (auto_name "env") conv op_nm th
    val _ = map derive_nsLookup_thms abbrev_defs
  in (th, ML_code (ss, abbrev_defs @ envs, vs, ml_th)) end

fun let_v_abbrev nm conv op_nm (th, ML_code (ss, envs, vs, ml_th)) = let
    val (th, abbrev_defs) = cond_let_abbrev false false nm conv op_nm th
  in (th, ML_code (ss, envs, abbrev_defs @ vs, ml_th)) end

(*
val tm = ``!n. n = 5 ==> n < 8``
*)
fun unwind_forall_conv tm =
  let
    val (v,_) = dest_forall tm
  in
    (QUANT_CONV (RAND_CONV (UNBETA_CONV v))
     THENC (REWR_CONV UNWIND_FORALL_THM1 ORELSEC
            REWR_CONV UNWIND_FORALL_THM2)
     THENC BETA_CONV) tm
  end

fun forall_nsLookup_upd nm (th,x) =
  (CONV_RULE
    (QUANT_CONV
      ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV) (nsLookup_conv THENC EVAL)
       THENC (RATOR_CONV o RAND_CONV) (REWR_CONV SOME_11))
     THENC unwind_forall_conv) th,
   x) handle HOL_ERR _ =>
  failwith "forall_nsLookup_upd: nsLookup failed to produce SOME"

fun solve_ml_imp f nm (th, ML_code code) = let
    val msg = "solve_ml_imp: " ^ nm ^ ": not imp"
    val _ = is_imp (concl th) orelse (print (msg ^ "\n\n");
        print_term (concl th); failwith msg)
  in (f th, ML_code code) end
fun solve_ml_imp_mp lemma = solve_ml_imp (fn th => MATCH_MP th lemma)
fun solve_ml_imp_conv conv = solve_ml_imp (prove_assum_by_conv conv)

(*
val (ML_code (ss,envs,vs,th)) = (ML_code (ss,envs,v_def :: vs,th))
*)

fun list_upd i x xs = mapi (fn j => fn y => if j = i then x else y) xs

fun ML_code_upd nm mp_thm adjs (ML_code code) = let
    (* when updating an ML_code thm by forward reasoning, first
       abstract over all the program components (which can be large
       snoc-lists or cons-lists) and process on the smaller abstracted
       theorem, connecting to the original ML_code thm with a single
       final MATCH_MP step. *)
    val orig_th = #4 code
    val blocks = ML_code_blocks (concl orig_th)
    val (f, xs) = strip_comb (concl orig_th)
    val abs_blocks = mapi (fn i => pairSyntax.list_mk_pair o
        (mapi (fn j => if j = 2 then (fn _ =>
            mk_var ("prog_var_" ^ Int.toString i, decs_ty)) else I))) blocks
    val abs_blocks_tm = listSyntax.mk_list (abs_blocks, type_of (hd abs_blocks))
    val abs_concl = list_mk_comb (f,
        mapi (fn i => if i = 1 then K abs_blocks_tm else I) xs)
    val preproc_th = MATCH_MP mp_thm (ASSUME abs_concl)
    val (proc_th, ML_code (ss, envs, vs, _))
        = foldl (fn (adj, x) => adj nm x) (preproc_th, ML_code code) adjs
    val _ = same_const ML_code_tm (fst (strip_comb (concl proc_th)))
        orelse failwith ("ML_code_upd: " ^ nm ^ ": unfinished: "
            ^ Parse.thm_to_string proc_th)
    val th = MATCH_MP (DISCH abs_concl proc_th) orig_th
  in ML_code (ss, envs, vs, th) end

(* --- *)

val unknown_loc = locationTheory.unknown_loc_def |> concl |> dest_eq |> fst;
val loc = unknown_loc;

val init_state =
  ML_code ([SPEC_ALL init_state_def],[init_env_def],[],ML_code_NIL);

fun mk_comment (s1, s2) = pairSyntax.mk_pair (stringSyntax.fromMLstring s1,
    stringSyntax.fromMLstring s2)

fun dest_comment t = let
    val (s1, s2) = pairSyntax.dest_pair t
  in (stringSyntax.fromHOLstring s1, stringSyntax.fromHOLstring s2) end

fun dest_comment_name t = let
    val (s1, s2) = dest_comment t
  in "(" ^ s1 ^ ", " ^ s2 ^ ")" end handle HOL_ERR _ => "(?, ?)"

fun open_block nm comment = ML_code_upd nm (SPEC comment ML_code_new_block)
    [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def])]

fun open_module mn_str = open_block "open_module"
    (mk_comment ("Module", mn_str))

fun close_module sig_opt = ML_code_upd "close_module"
    ML_code_close_module [let_env_abbrev ALL_CONV]

val open_local_block = open_block "open_local_block"
    (mk_comment ("Local", "local"))

val open_local_in_block = open_block "open_local_in_block"
    (mk_comment ("Local", "in"))

val close_local_block = ML_code_upd "close_local_block"
    ML_code_close_local [let_env_abbrev ALL_CONV]

(*
val tds_tm = ``[]:type_def``
*)

fun add_Dtype loc tds_tm = ML_code_upd "add_Dtype"
    (SPECL [tds_tm, loc] ML_code_Dtype)
    [solve_ml_imp_conv EVAL, let_conv_ML_upd EVAL,
        let_st_abbrev reduce_conv,
        let_env_abbrev (SIMP_CONV std_ss
            [write_tdefs_def,MAP,FLAT,FOLDR,REVERSE_DEF,
                write_conses_def,LENGTH,
                semanticPrimitivesTheory.build_constrs_def,
                APPEND,namespaceTheory.mk_id_def])]

(*
val loc = unknown_loc
val n_tm = ``"bar"``
val l_tm = ``[]:ast_t list``
*)

fun add_Dexn loc n_tm l_tm = ML_code_upd "add_Dexn"
    (SPECL [n_tm, l_tm, loc] ML_code_Dexn)
    [let_conv_ML_upd EVAL, let_st_abbrev reduce_conv,
        let_env_abbrev (SIMP_CONV std_ss [MAP,
                               FLAT,FOLDR,REVERSE_DEF,
                               APPEND,namespaceTheory.mk_id_def])]

fun add_Dtabbrev loc l1_tm l2_tm l3_tm = ML_code_upd "add_Dtabbrev"
    (SPECL [l1_tm,l2_tm,l3_tm,loc] ML_code_Dtabbrev) []

fun add_Dlet eval_thm var_str = let
    val (_, eval_thm_xs) = strip_comb (concl eval_thm)
    val mp_thm = ML_code_Dlet_var |> SPECL (tl eval_thm_xs
        @ [stringSyntax.fromMLstring var_str,unknown_loc])
  in ML_code_upd "add_Dlet" mp_thm
    [solve_ml_imp_mp eval_thm,
     solve_ml_imp_conv (SIMP_CONV bool_ss []
                        THENC SIMP_CONV bool_ss [ML_code_env_def]),
     solve_ml_imp_conv eval_every_exp_one_con_check,
     let_env_abbrev ALL_CONV, let_st_abbrev reduce_conv]
  end

fun add_Dlet_lit loc n l =
  let
    val mp_thm = SPECL [loc,n,l] ML_code_Dlet_var_lit
  in
    ML_code_upd "add_Dlet_lit" mp_thm [let_env_abbrev ALL_CONV, let_env_abbrev ALL_CONV]
end

fun add_Denv eval_thm var_str = let
    val (_, eval_thm_xs) = strip_comb (concl eval_thm)
    val mp_thm = ML_code_Denv |> SPECL (
      stringSyntax.fromMLstring var_str :: tl eval_thm_xs)
  in ML_code_upd "add_Denv" mp_thm
    [solve_ml_imp_mp eval_thm,
        solve_ml_imp_conv (SIMP_CONV bool_ss []
            THENC SIMP_CONV bool_ss [ML_code_env_def]),
        let_env_abbrev ALL_CONV, let_st_abbrev reduce_conv]
  end

(*
val (ML_code (ss,envs,vs,th)) = s
val (n,v,exp) = (v_tm,w,body)
*)

fun add_Dlet_Fun loc n v exp v_name = ML_code_upd "add_Dlet_Fun"
    (SPECL [n, v, exp, loc] ML_code_Dlet_Fun)
    [solve_ml_imp_conv eval_every_exp_one_con_check,
     let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
     let_v_abbrev v_name ALL_CONV,
     let_env_abbrev ALL_CONV]

fun add_Dlet_Var_Var loc n var_name = ML_code_upd "add_Dlet_Var_Var"
    (SPECL [n, var_name, loc] ML_code_Dlet_Var_Var)
    [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
     forall_nsLookup_upd,
     let_env_abbrev ALL_CONV]

fun add_Dlet_Var_Ref_Var loc n var_name v_name = ML_code_upd "add_Dlet_Var_Ref_Var"
    (SPECL [n, var_name, loc] ML_code_Dlet_Var_Ref_Var)
    [let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
     forall_nsLookup_upd,
     let_conv_ML_upd EVAL,
     let_v_abbrev v_name ALL_CONV,
     let_env_abbrev ALL_CONV,
     let_st_abbrev reduce_conv]

val Recclosure_pat =
  semanticPrimitivesTheory.v_nchotomy
  |> concl |> find_term (fn tm => total (fst o dest_const o fst o strip_comb
        o snd o dest_eq) tm = SOME "Recclosure")
  |> dest_eq |> snd

fun add_Dletrec loc funs v_names = let
    fun proc nm (th, (ML_code (ss,envs,vs,mlth))) = let
        val th = CONV_RULE (RAND_CONV (SIMP_CONV std_ss [write_rec_def,FOLDR,
            semanticPrimitivesTheory.build_rec_env_def])) th
        val _ = is_let (concl th) orelse failwith "add_Dletrec: not let"
        val (_, tm) = dest_let (concl th)
        val tms = rev (find_terms (can (match_term Recclosure_pat)) tm)
        val xs = zip v_names tms
        val v_defs = map (fn (x,y) => define_abbrev false x y) xs
        val th = CONV_RULE (RAND_CONV (REWRITE_CONV (map GSYM v_defs))) th
      in let_env_abbrev ALL_CONV nm
        (th, ML_code (ss,envs,v_defs @ vs,mlth)) end
  in ML_code_upd "add_Dletrec"
    (SPECL [funs, loc] ML_code_Dletrec)
    [solve_ml_imp_conv EVAL,
     solve_ml_imp_conv eval_every_exp_one_con_check,
     let_conv_ML_upd (REWRITE_CONV [ML_code_env_def]),
     proc]
  end

fun get_block_names (ML_code (ss,envs,vs,th))
  = ML_code_blocks (concl th) |> map (dest_comment o hd)

fun get_open_modules code
  = get_block_names code
    |> filter (fn ("Module", _) => true | _ => false)
    |> map snd |> rev

fun get_mod_prefix code = case get_open_modules code of [] => ""
  | (m :: _) => m ^ "_"

fun close_local_blocks code = case get_block_names code of
    ("Local", "in") :: _ => close_local_blocks (close_local_block code)
  | ("Local", "local") :: _ => open_local_in_block code
    |> close_local_block |> close_local_blocks
  | _ => code


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
  else if is_Dlet dec_tm
          andalso is_Lit (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,lit) = dest_Dlet dec_tm
    val l = dest_Lit lit
    val n = dest_Pvar p
    in add_Dlet_lit loc n l s end
  else if is_Dlet dec_tm
          andalso is_Var (rand dec_tm)
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val v_tm = dest_Pvar p
    val var_name = dest_Var f
    in add_Dlet_Var_Var loc v_tm var_name s end
  else if is_Dlet dec_tm
          andalso is_App (rand dec_tm)
          andalso aconv Opref (rand (rator (rand dec_tm)))
          andalso length (fst (listSyntax.dest_list (rand (rand dec_tm)))) = 1
          andalso is_Var (rand (rator (rand (rand dec_tm))))
          andalso is_Pvar (rand (rator dec_tm)) then let
    val (loc,p,f) = dest_Dlet dec_tm
    val n = dest_Pvar p
    val (_,args) = dest_App f
    val var_name = dest_Var (listSyntax.dest_list args |> fst |> hd)
    val prefix = get_mod_prefix s
    val v_name = prefix ^ pick_name (stringSyntax.fromHOLstring n) ^ "_v"
    in add_Dlet_Var_Ref_Var loc n var_name v_name s end
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

fun get_prog (ML_code (ss,envs,vs,th)) = case ML_code_blocks (concl th) of
      [comm :: st :: prog :: _] => prog
    | _ => failwith ("get_prog: couldn't get toplevel declarations")
fun get_Decls_thm code = let
    val _ = get_prog code
  in MATCH_MP ML_code_Decls (get_thm code) end

val merge_env_tm = prim_mk_const {Name = "merge_env", Thy = "ml_prog"}
val ML_code_env_tm = prim_mk_const {Name = "ML_code_env", Thy = "ml_prog"}

fun get_env s = let
    val th = get_thm s
    val bls = ML_code_blocks (concl th)
    fun mk [] = hd (snd (strip_comb (concl th)))
      | mk (bl :: bls) = list_mk_icomb (merge_env_tm, [List.last bl, mk bls])
  in mk bls end

fun get_state s = get_thm s |> concl |> rand

fun mk_acc nm rec_tm = let
    val fields = TypeBase.fields_of (type_of rec_tm)
    val field = assoc nm fields
  in mk_icomb (#accessor field, rec_tm) end

fun get_next_type_stamp s =
  get_state s
  |> mk_acc "next_type_stamp"
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun get_next_exn_stamp s =
  get_state s
  |> mk_acc "next_exn_stamp"
  |> QCONV EVAL |> concl |> rand |> numSyntax.int_of_term;

fun add_prog prog_tm pick_name s = let
  val ts = fst (listSyntax.dest_list prog_tm)
  in remove_snocs (foldl (fn (x,y) => add_dec x pick_name y) s ts) end

fun pack_ml_prog_state (ML_code (ss,envs,vs,th)) =
  pack_4tuple (pack_list pack_thm) (pack_list pack_thm)
    (pack_list pack_thm) pack_thm (ss,envs,vs,th)

fun unpack_ml_prog_state t =
  ML_code (unpack_4tuple (unpack_list unpack_thm) (unpack_list unpack_thm)
    (unpack_list unpack_thm) unpack_thm t)

fun set_eval_state es (ML_code (ss,envs,vs,th)) = let
  val th1 = MATCH_MP ML_code_set_eval_state th
  val th2 = th1 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL)
  val th3 = MP th2 TRUTH handle HOL_ERR _ =>
            failwith "set_eval_state: unable to prove that eval_state was NONE"
  val th4 = SPEC es th3
  in ML_code (ss,envs,vs,th4) end

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
val dec1_tm = ``Dlet (ARB 1) (Pvar "f") (Lit (IntLit 5))``
val dec2_tm = ``Dlet (ARB 2) (Pvar "g") (Fun "x" (Var (Short "x")))``
val dec3_tm = ``Dletrec (ARB 3) [("foo","n",Con (SOME (Short "::"))
                  [Var (Short "n");Var (Short "n")])]``
val prog_tm = ``[^dec1_tm; ^dec2_tm; ^dec3_tm]``

val s = (add_prog prog_tm pick_name init_state)

val th = get_env s

*)

end
