(*
  Encoders and decoders to/from configuration types in backend.
*)
open integerTheory ml_progTheory
     astTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory mlvectorTheory mlstringTheory
     ml_translatorTheory miscTheory
     backendTheory backend_commonTheory
     num_list_enc_decTheory num_tree_enc_decTheory;
open preamble;

val _ = new_theory "backend_enc_dec";

(* automation *)

val enc_dec_mapping =
  ref ([(“:bool”, “bool_enc'”, “bool_dec'”),
        (“:num”,  “num_enc'”,  “num_dec'” ),
        (“:int”,  “int_enc'”,  “int_dec'” ),
        (“:char”, “chr_enc'”,  “chr_dec'” ),
        (“:word64”, “word64_enc'”, “word64_dec'” )]);

fun reg_enc_dec_only ty enc dec =
   (enc_dec_mapping := (ty,enc,dec) :: (!enc_dec_mapping));

fun reg_enc_dec enc_dec_lemma = let
  val enc_dec_lemma = SPEC_ALL enc_dec_lemma
  val enc = enc_dec_lemma |> concl |> dest_eq |> fst |> rand |> rator
  val dec = enc_dec_lemma |> concl |> dest_eq |> fst |> rator
  val ty = dest_type (type_of enc) |> snd |> hd
  val _ = reg_enc_dec_only ty enc dec
  val th = MATCH_MP imp_enc_dec_ok (GEN_ALL enc_dec_lemma)
  val e = th |> concl |> rator |> rand
  val d = th |> concl |> rand
  val e_name = enc |> dest_const |> fst |> explode |> butlast |> implode
  val d_name = dec |> dest_const |> fst |> explode |> butlast |> implode
  val e_def = mk_eq(mk_var(e_name,type_of e), e)
    |> ANTIQUOTE |> single |> Define
  val d_def = mk_eq(mk_var(d_name,type_of d), d)
    |> ANTIQUOTE |> single |> Define
  val th = th |> REWRITE_RULE [GSYM e_def,GSYM d_def]
  in save_thm(e_name ^ "_dec_ok",th) end

fun get_enc_dec_for ty =
  if can listSyntax.dest_list_type ty then
    let val ty1 = listSyntax.dest_list_type ty
        val (x,y) = get_enc_dec_for ty1
    in (“list_enc' ^x”,“list_dec' ^y”) end
  else if can (match_type “:'a option”) ty then
    let val ty1 = ty |> dest_type |> snd |> hd
        val (x,y) = get_enc_dec_for ty1
    in (“option_enc' ^x”,“option_dec' ^y”) end
  else if can (match_type “:'a # 'b”) ty then
    let val (e1,d1) = ty |> dest_type |> snd |> el 1 |> get_enc_dec_for
        val (e2,d2) = ty |> dest_type |> snd |> el 2 |> get_enc_dec_for
    in (“pair_enc' ^e1 ^e2”,“pair_dec' ^d1 ^d2”) end
  else
    let val (_,x,y) = first (fn (x,_,_) => x = ty) (!enc_dec_mapping)
    in (x,y) end handle HOL_ERR _ => failwith ("Missing type: " ^ type_to_string ty)

fun enc_dec_for ty = let
  val name = type_to_string ty |> explode |> tl |> implode
             |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val enc_name = name ^ "_enc'"
  val enc_tm = mk_var(enc_name,mk_type("fun",[ty,“:num_tree”]))
  val dec_name = name ^ "_dec'"
  val dec_tm = mk_var(dec_name,mk_type("fun",[“:num_tree”,ty]))
  val _ = reg_enc_dec_only ty enc_tm dec_tm
  val cs = TypeBase.constructors_of ty
  fun arg_types ty =
    let val (n,xs) = dest_type ty
    in if n = "fun" then hd xs :: arg_types (hd (tl xs)) else [] end
  fun build_enc_eq i c = let
    val tys = type_of c |> arg_types
    val vs = mapi (fn i => fn ty => mk_var("v" ^ int_to_string i,ty)) tys
    val l = mk_comb(enc_tm,list_mk_comb(c,vs))
    val r = mk_comb(“Tree”,numSyntax.term_of_int i)
    val ws = map (fn v => mk_comb(fst (get_enc_dec_for (type_of v)),v)) vs
    val r = mk_comb(r,listSyntax.mk_list(ws, “:num_tree”))
    in mk_eq(l,r) end
  val enc_def_tm = list_mk_conj (mapi build_enc_eq cs)
  val arg = “Tree n xs”
  val xs = arg |> rand
  val l = mk_comb(dec_tm,arg)
  val nth = nth_def |> CONJUNCT1 |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun get_nth i = mk_comb(mk_comb(nth,numSyntax.term_of_int i),xs)
  fun make_dec_ifs i [] = fail()
    | make_dec_ifs i [c] = let
        val tys = type_of c |> arg_types
        fun arg i ty = let
          val (_,dec) = get_enc_dec_for ty
          in mk_comb(dec, get_nth i) end
        val ws = mapi arg tys
        in list_mk_comb(c,ws) end
    | make_dec_ifs i (c::cs) =
        mk_cond(mk_eq(rand (rator arg), numSyntax.term_of_int i),
                make_dec_ifs i [c],
                make_dec_ifs (i+1) cs)
  val dec_def_tm = mk_eq(l,make_dec_ifs 0 cs)
  in (enc_def_tm, dec_def_tm) end

fun define_enc_dec ty = let
  val (enc_def_tm, dec_def_tm) = enc_dec_for ty
  val enc_def = Define [ANTIQUOTE enc_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val dec_def = Define [ANTIQUOTE dec_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val (e,x) = enc_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val (d,_) = dec_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val x = mk_var("x",type_of x)
  val goal = mk_forall(x,mk_eq(mk_comb(d,mk_comb(e,x)),x))
  val ty_n = type_to_string ty |> explode |> tl |> implode
             |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val lemma = prove(goal,Cases \\ fs [enc_def,dec_def])
  val _ = save_thm(ty_n ^ "_enc'_thm[simp]",lemma)
  val _ = reg_enc_dec lemma
  in (enc_def,dec_def,lemma) end;

(* tra *)

val (e,d) = enc_dec_for “:tra”

Definition tra_enc'_def:
  ^e
End

Definition tra_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
  \\ Cases_on ‘x’ \\ gvs [list_dec'_def]
  \\ fs [num_tree_size_def]
End

Theorem tra_enc'_thm[simp]:
  tra_dec' (tra_enc' x) = x
Proof
  Induct_on ‘x’ \\ fs [tra_enc'_def,Once tra_dec'_def]
QED

val _ = reg_enc_dec tra_enc'_thm;

(* some simple ones *)

val res = define_enc_dec “:var_name”
val res = define_enc_dec “:word_size”
val res = define_enc_dec “:mlstring”

(* const *)

val (e,d) = enc_dec_for “:const”

Definition const_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure const_size’
End

Definition const_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
End

Theorem const_enc'_thm[simp]:
  const_dec' (const_enc' x) = x
Proof
  qid_spec_tac ‘x’
  \\ ho_match_mp_tac const_enc'_ind \\ rw []
  \\ TRY (fs [const_enc'_def,Once const_dec'_def] \\ NO_TAC)
  \\ simp [const_enc'_def,Once const_dec'_def,SF ETA_ss]
  \\ irule list_enc'_mem
  \\ fs []
QED

val _ = reg_enc_dec const_enc'_thm;

val res = define_enc_dec “:opw”
val res = define_enc_dec “:ast$shift”
val res = define_enc_dec “:fp_cmp”
val res = define_enc_dec “:fp_uop”
val res = define_enc_dec “:fp_bop”
val res = define_enc_dec “:fp_top”
val res = define_enc_dec “:const_part”
val res = define_enc_dec “:closLang$op”
val res = define_enc_dec “:gc_kind”
val res = define_enc_dec “:tap_config”

(* closLang's exp *)

val (e,d) = enc_dec_for “:closLang$exp”

Triviality MEM_exp_size:
  (∀xs x. MEM x xs ⇒ exp_size x ≤ closLang$exp3_size xs) ∧
  (∀xs x y. MEM (x,y) xs ⇒ exp_size y ≤ closLang$exp1_size xs)
Proof
  rpt conj_tac
  \\ Induct \\ fs [] \\ rw [] \\ fs [closLangTheory.exp_size_def]
  \\ res_tac \\ fs []
QED

Definition closLang_exp_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure closLang$exp_size’ \\ rw []
  \\ imp_res_tac MEM_exp_size \\ gvs []
End

Definition closLang_exp_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
  \\ Cases_on ‘x’ \\ gvs [list_dec'_def]
  \\ fs [num_tree_size_def]
End

Triviality bvl_MEM_exp_size:
  (∀xs x. MEM x xs ⇒ exp_size x ≤ bvl$exp1_size xs)
Proof
  Induct \\ fs [] \\ rw [] \\ fs [bvlTheory.exp_size_def]
  \\ res_tac \\ fs []
QED

Theorem closLang_exp_enc'_thm[simp]:
  ∀x. closLang_exp_dec' (closLang_exp_enc' x) = x
Proof
  ho_match_mp_tac closLang_exp_enc'_ind \\ rw []
  \\ fs [closLang_exp_enc'_def]
  \\ once_rewrite_tac [closLang_exp_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs [] \\ rw []
  \\ match_mp_tac pair_enc'_fst_snd
  \\ rename [‘MEM y ys’] \\ PairCases_on ‘y’ \\ gvs []
QED

val _ = reg_enc_dec closLang_exp_enc'_thm;

(* BVL's exp *)

val (e,d) = enc_dec_for “:bvl$exp”

Definition bvl_exp_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure bvl$exp_size’ \\ rw []
  \\ imp_res_tac bvl_MEM_exp_size \\ gvs []
End

Definition bvl_exp_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
End

Theorem bvl_exp_enc'_thm[simp]:
  ∀x. bvl_exp_dec' (bvl_exp_enc' x) = x
Proof
  ho_match_mp_tac bvl_exp_enc'_ind \\ rw []
  \\ fs [bvl_exp_enc'_def]
  \\ once_rewrite_tac [bvl_exp_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs []
QED

val _ = reg_enc_dec bvl_exp_enc'_thm;

(* val_approx *)

val (e,d) = enc_dec_for “:val_approx”

Definition val_approx_enc'_def:
  ^e
Termination
  WF_REL_TAC ‘measure val_approx_size’ \\ rw []
  \\ qsuff_tac ‘val_approx_size a ≤ val_approx1_size v1’ \\ fs []
  \\ pop_assum mp_tac \\ rename [‘MEM a xs’]
  \\ Induct_on ‘xs’ \\ fs [] \\ rw [clos_knownTheory.val_approx_size_def]
  \\ gvs [clos_knownTheory.val_approx_size_def]
End

Definition val_approx_dec'_def:
  ^d
Termination
  WF_REL_TAC `measure num_tree_size`
  \\ reverse (rw [])
  \\ rpt (pop_assum mp_tac)
  \\ rpt (goal_term (fn tm =>
            tmCases_on (rand (find_term (can (match_term “nth _ _”)) tm)) []
            \\ fs [num_tree_size_def,list_dec'_def]))
  \\ rename [‘list_dec' I xs’] \\ Cases_on ‘xs’
  \\ fs [list_dec'_def] \\ rw []
  \\ imp_res_tac MEM_num_tree_size \\ fs [num_tree_size_def]
End

Theorem val_approx_enc'_thm[simp]:
  ∀x. val_approx_dec' (val_approx_enc' x) = x
Proof
  ho_match_mp_tac val_approx_enc'_ind \\ rw []
  \\ fs [val_approx_enc'_def]
  \\ once_rewrite_tac [val_approx_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs []
QED

val _ = reg_enc_dec val_approx_enc'_thm;

(* automation for producing enc/dec for record types *)

fun define_abbrev name tm = let
  val name = name |> String.tokens (fn c => c = #" ") |> last
    |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val thm_name = name ^ "_def"
  val vs = free_vars tm |> sort (fn x => fn y => fst (dest_var x) <= fst (dest_var y))
  val f = mk_var(name,type_of (list_mk_abs(vs,tm)))
  val l = list_mk_comb(f,vs)
  val def = new_definition(thm_name,mk_eq(l,tm)) |> SPEC_ALL
  val _ = save_thm(thm_name ^ "[compute]",def |> SIMP_RULE std_ss [FUN_EQ_THM,LAMBDA_PROD] |> SPEC_ALL)
  in def end

val builtin = [bool_enc_dec_ok, unit_enc_dec_ok, num_enc_dec_ok,
               int_enc_dec_ok, char_enc_dec_ok, list_enc_dec_ok,
               word_enc_dec_ok, prod_enc_dec_ok, option_enc_dec_ok,
               sum_enc_dec_ok, spt_enc_dec_ok, namespace_enc_dec_ok,
               mlstring_enc_dec_ok, namespace_enc_dec_ok] |> map UNDISCH_ALL;

val extra = DB.find "enc_dec_ok"
  |> filter (fn ((thy,_),(th,_)) => thy = current_theory()
       andalso not (can (find_term is_forall) (concl th)))
  |> map (fst o snd);

val get_enc_dec_ok_mem = ref (builtin @ extra);

val ty = “:val_approx + num”

fun get_enc_dec_ok_thm ty = let
  fun get_match th =
    match_type (th |> concl |> rator |> rand |> type_of |> dest_type |> snd |> hd) ty
  val th = first (can get_match) (!get_enc_dec_ok_mem)
  val m = get_match th
  val th1 = INST_TYPE m th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  fun match_all th1 = let
    val tm = th1 |> concl |> dest_imp |> fst
    val ty1 = tm |> rator |> rand |> type_of |> dest_type |> snd |> hd
    in match_all (MATCH_MP th1 (get_enc_dec_ok_thm ty1)) end
    handle HOL_ERR _ => th1
  in match_all th1 end

val mem_enc_dec' = ref ([]:thm list);

fun get_enc_dec_ok'_thm (name, ty) =
  if can (match_type “:'a -> 'b”) ty orelse
     can (match_type “:'a asm_config”) ty then
    ISPEC (mk_var(name,ty)) enc_dec_ok'_const
  else if can get_enc_dec_ok_thm ty then
    MATCH_MP IMP_enc_dec_ok (get_enc_dec_ok_thm ty)
  else let
    fun is_match th =
      (th |> concl |> rator |> rand |> type_of |> dest_type |> snd |> hd) = ty
    in first is_match (!mem_enc_dec') end
    handle HOL_ERR e => (print "\n\nERROR: get_enc_dec_ok'_thm fails for: ";
                         print_type ty; print "\n\n"; raise HOL_ERR e);

fun encode_for_rec ty = let
  val xs = TypeBase.fields_of ty |> map (fn (x,{ty = c, ...}) => (x,c))
  val ys = map get_enc_dec_ok'_thm xs
(*
  val (name,ty) = first (not o can get_enc_dec_ok'_thm) xs
*)
  fun prod_enc [th] = th
    | prod_enc (th::thms) =
        MATCH_MP prod_enc_dec_ok' (CONJ th (prod_enc thms))
    | prod_enc _ = TRUTH
  val thi = prod_enc ys
  val x = mk_var("x",ty)
  val cons = TypeBase.constructors_of ty |> hd
  val cs = TypeBase.fields_of ty |> map snd |> map (fn {accessor = c, ...} => c)
  val e = mk_abs(x,list_mk_pair(map (fn tm => mk_comb(tm,x)) cs))
  val tms = map (fn tm => mk_comb(tm,x)) cs
  val tm = list_mk_pair tms
  val enc = mk_abs(x,tm)
  val y = mk_var("y",type_of tm)
  fun parts [] x = [x]
    | parts [_] x = [x]
    | parts (y::ys) x = mk_fst x :: parts ys (mk_snd x)
  val ys = parts tms y
  val dec = mk_abs(y,list_mk_comb(cons,ys))
  val goal = mk_forall(x,mk_eq(mk_comb(dec,mk_comb(enc,x)),x))
  val lemma = prove(goal,Cases THEN EVAL_TAC)
  val th = MATCH_MP enc_dec_ok'_o (CONJ thi lemma)
            |> SIMP_RULE std_ss [o_DEF,prod_enc_def]
  val enc_tm = th |> concl |> rator |> rand
  val enc_name = type_to_string ty ^ "_enc" |> explode |> tl |> implode
  val enc_def = define_abbrev enc_name enc_tm
  val dec_tm = th |> concl |> rand
  val dec_name = type_to_string ty ^ "_dec" |> explode |> tl |> implode
  val dec_def = define_abbrev dec_name dec_tm
  val res = CONV_RULE (RAND_CONV (REWR_CONV (GSYM dec_def))
                       THENC (RATOR_CONV o RAND_CONV) (REWR_CONV (GSYM enc_def))) th
  val _ = (mem_enc_dec' := res :: (!mem_enc_dec'))
  val _ = (get_enc_dec_ok_mem := !get_enc_dec_ok_mem @ [MATCH_MP enc_dec_ok'_IMP res])
          handle HOL_ERR _ => ()
  in res end handle HOL_ERR e => failwith ("encode_for_rec failed for " ^ type_to_string ty);

val res = encode_for_rec “:next_indices”;
val res = encode_for_rec “:clos_known$config”;
val res = encode_for_rec “:word_to_word$config”;
val res = encode_for_rec “:bvl_to_bvi$config”;
val res = encode_for_rec “:stack_to_lab$config”;
val res = encode_for_rec “:flat_pattern$config”;
val res = encode_for_rec “:data_to_word$config”;
val res = encode_for_rec “:clos_to_bvl$config”;
val res = encode_for_rec “:environment”;
val res = encode_for_rec “:environment_store”;
val res = encode_for_rec “:source_to_flat$config”;
val res = encode_for_rec “:word_to_stack$config”;
val res = encode_for_rec “:lab_to_target$inc_config”;
val res = encode_for_rec “:backend$inc_config”;

Theorem inc_config_dec_thm =
  res |> SIMP_RULE std_ss [enc_dec_ok'_def]
      |> CONJUNCT2 |> Q.SPECL [‘c’,‘[]’]
      |> GEN_ALL |> SIMP_RULE std_ss [APPEND_NIL];

(* top level *)

Definition encode_backend_config_def:
  encode_backend_config c =
    rev_nums_to_chars (append_rev (inc_config_enc c) []) "" : char list
End

Definition decode_backend_config_def:
  decode_backend_config s = FST (inc_config_dec (chars_to_nums s))
End

Theorem encode_backend_config_thm:
  decode_backend_config (encode_backend_config c) = c
Proof
  fs [encode_backend_config_def,decode_backend_config_def,rev_nums_to_chars_thm,
      chars_to_nums_nums_to_chars,inc_config_dec_thm,append_rev_thm]
QED

val _ = export_theory();
