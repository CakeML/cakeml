(*
  Encoders and decoders to/from types configuration types in backend.
*)
open integerTheory ml_progTheory
     astTheory semanticPrimitivesTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory
     fpSemTheory mlvectorTheory mlstringTheory
     ml_translatorTheory miscTheory
     backendTheory backend_commonTheory num_list_enc_decTheory;
open preamble;

val _ = new_theory "backend_enc_dec";

Definition nth_def[simp]:
  nth n [] = Tree 0 [] ∧
  nth n (x::xs) = if n = 0 then x else nth (n-1n) xs
End

(* namespace -- instantiated to (string, string, 'a) *)

Definition namespace_enc_def:
  namespace_enc e (Bind xs ys) =
    (let ns1 = list_enc (prod_enc (list_enc char_enc) (list_enc char_enc)) xs in
     let ns2 = namespace_enc_list e ys in
       Append ns1 ns2) ∧
  namespace_enc_list e [] = List [0] ∧
  namespace_enc_list e ((m,x)::xs) =
    Append (Append (List [1]) (e m))
      (Append (namespace_enc e x) (namespace_enc_list e xs))
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (_,x) => namespace_size (K 0) (K 0) (K 0) x
                           | INR (_,x) => namespace1_size (K 0) (K 0) (K 0) x)’
End

Definition namespace_dec_def:
  namespace_dec d ns =
    (if PRECONDITION (dec_ok d) then
     if ns = [] then (Bind [] [],ns) else
       let (xs,ns1) = list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)) ns in
       let (ys,ns2) = namespace_dec_list d ns1 in
         (Bind xs ys,ns2)
     else (Bind [] [],ns)) ∧
  namespace_dec_list d ns =
    if PRECONDITION (dec_ok d) then
      case ns of
      | [] => ([],ns)
      | (n::rest) =>
        if n = 0n then ([],rest) else
          let (m,ns) = d rest in
          let (x,ns) = fix_res ns (namespace_dec d ns) in
          let (ys,ns) = namespace_dec_list d ns in
            ((m,x)::ys,ns)
    else ([],ns)
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL (_,ns) => LENGTH ns
                           | INR (_,ns) => LENGTH ns)’
  \\ reverse (rw [] \\ imp_res_tac fix_res_IMP \\ fs [])
  \\ TRY
   (fs [PRECONDITION_def,dec_ok_def]
    \\ rpt (qpat_x_assum ‘(_,_) = _’ (assume_tac o GSYM))
    \\ first_x_assum (qspec_then ‘rest’ mp_tac) \\ fs [] \\ NO_TAC)
  \\ Cases_on ‘ns’ \\ fs []
  \\ fs [list_dec_def]
  \\ pop_assum (assume_tac o GSYM)
  \\ imp_res_tac list_dec'_length
  \\ pop_assum mp_tac \\ impl_tac \\ fs []
  \\ qsuff_tac ‘enc_dec_ok
                (prod_enc (list_enc char_enc) (list_enc char_enc))
                (prod_dec (list_dec char_dec) (list_dec char_dec))’
  THEN1 (fs [enc_dec_ok_def])
  \\ match_mp_tac prod_enc_dec_ok \\ fs []
  \\ match_mp_tac list_enc_dec_ok \\ fs [char_enc_dec_ok]
End

Theorem dec_ok_namespace_dec:
  dec_ok d ⇒ dec_ok (namespace_dec d)
Proof
  rw [] \\ simp [dec_ok_def]
  \\ qsuff_tac ‘
    (∀(d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec d i)) ≤ LENGTH i) ∧
    (∀(d:num list -> α # num list) i.
      dec_ok d ⇒ LENGTH (SND (namespace_dec_list d i)) ≤ LENGTH i)’
  THEN1 metis_tac [] \\ pop_assum kall_tac
  \\ ho_match_mp_tac namespace_dec_ind \\ rw []
  \\ once_rewrite_tac [namespace_dec_def]
  \\ fs [ml_translatorTheory.PRECONDITION_def,UNCURRY]
  \\ rw [] \\ fs []
  THEN1
   (Cases_on ‘list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)) i’ \\ fs []
    \\ ‘dec_ok (list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)))’ by
      metis_tac [list_enc_dec_ok, prod_enc_dec_ok, char_enc_dec_ok, enc_dec_ok_def]
    \\ fs [dec_ok_def] \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ fs [])
  \\ Cases_on ‘i’ \\ fs []
  \\ Cases_on ‘h=0’ \\ fs []
  \\ Cases_on ‘d t’ \\ fs []
  \\ Cases_on ‘namespace_dec d r’ \\ fs []
  \\ Cases_on ‘fix_res r (q',r')’ \\ fs []
  \\ match_mp_tac LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
  \\ imp_res_tac (GSYM fix_res_IMP)
  \\ fs [dec_ok_def]
  \\ first_x_assum (qspec_then ‘t’ mp_tac) \\ fs []
QED

Triviality fix_res_namespace_dec:
  PRECONDITION (dec_ok d) ⇒
  fix_res ns (namespace_dec d ns) = namespace_dec d ns
Proof
  metis_tac [dec_ok_namespace_dec,dec_ok_fix_res,
             ml_translatorTheory.PRECONDITION_def]
QED

Theorem namespace_dec_def = namespace_dec_def
  |> SIMP_RULE std_ss [fix_res_namespace_dec];

Theorem namespace_dec_ind = namespace_dec_ind
  |> SIMP_RULE std_ss [fix_res_namespace_dec,GSYM AND_IMP_INTRO]
  |> SIMP_RULE bool_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC];

Theorem namespace_enc_dec_ok:
  enc_dec_ok e d ⇒
  enc_dec_ok (namespace_enc e) (namespace_dec d)
Proof
  fs [enc_dec_ok_def,dec_ok_namespace_dec]
  \\ strip_tac
  \\ strip_tac \\ pop_assum mp_tac
  \\ qid_spec_tac ‘x’
  \\ qid_spec_tac ‘e’
  \\ qsuff_tac ‘
        (∀e x.
            (∀x xs. d (append (e x) ++ xs) = (x,xs)) ⇒
            ∀xs. namespace_dec d (append (namespace_enc e x) ++ xs) = (x,xs)) ∧
        (∀e x.
            (∀x xs. d (append (e x) ++ xs) = (x,xs)) ⇒
            ∀xs. namespace_dec_list d (append (namespace_enc_list e x) ++ xs) = (x,xs))’
  THEN1 metis_tac []
  \\ ho_match_mp_tac namespace_enc_ind \\ rw [] \\ fs []
  \\ fs [namespace_enc_def]
  \\ once_rewrite_tac [namespace_dec_def] \\ fs []
  \\ fs [ml_translatorTheory.PRECONDITION_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ IF_CASES_TAC THEN1 fs [list_enc_def]
  \\ pop_assum kall_tac
  \\ ‘enc_dec_ok
      (list_enc (prod_enc (list_enc char_enc) (list_enc char_enc)))
      (list_dec (prod_dec (list_dec char_dec) (list_dec char_dec)))’ by
    metis_tac [list_enc_dec_ok, prod_enc_dec_ok, char_enc_dec_ok, enc_dec_ok_def]
  \\ fs [enc_dec_ok_def] \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
QED

(* num *)

Definition num_enc'_def:
  num_enc' n = Tree n []
End

Definition num_dec'_def[simp]:
  num_dec' (Tree n xs) = n
End

Theorem num_dec_enc'[simp]:
  num_dec' (num_enc' n) = n
Proof
  fs [num_dec'_def,num_enc'_def]
QED

(* int *)

Definition int_enc'_def:
  int_enc' n = if n < 0i then Tree (Num (0 - n)) [Tree 0 []] else Tree (Num n) []
End

Definition int_dec'_def:
  int_dec' (Tree n []) = & n ∧
  int_dec' (Tree n _) = - (& n):int
End

Theorem int_dec_enc'[simp]:
  int_dec' (int_enc' n) = n
Proof
  rw [int_dec'_def,int_enc'_def] \\ intLib.COOPER_TAC
QED

(* bool *)

Definition bool_enc'_def:
  bool_enc' F = Tree 0 [] ∧
  bool_enc' T = Tree 1 []
End

Definition bool_dec'_def:
  bool_dec' (Tree n xs) = (n = 1)
End

Theorem bool_dec_enc'[simp]:
  bool_dec' (bool_enc' b) = b
Proof
  Cases_on ‘b’ \\ fs [bool_dec'_def,bool_enc'_def]
QED

(* chr *)

Definition chr_enc'_def:
  chr_enc' c = Tree (ORD c) []
End

Definition chr_dec'_def:
  chr_dec' (Tree n xs) = if n < 256 then CHR n else CHR 32
End

Theorem chr_enc'_thm[simp]:
  chr_dec' (chr_enc' c) = c
Proof
  fs [chr_enc'_def,chr_dec'_def,ORD_BOUND,CHR_ORD]
QED


(* list *)

Definition list_enc'_def:
  list_enc' f xs = Tree 0 (MAP f xs)
End

Definition list_dec'_def:
  list_dec' f (Tree _ xs) = MAP f xs
End

Theorem list_enc'_mem:
  (∀x. MEM x xs ⇒ g (f x) = x) ⇒
  list_dec' g (list_enc' f xs) = xs
Proof
  fs [list_enc'_def,list_dec'_def,MAP_MAP_o,o_DEF]
  \\ Induct_on ‘xs’ \\ fs []
QED

Theorem list_enc'_thm[simp]:
  (∀x. g (f x) = x) ⇒
  list_dec' g (list_enc' f xs) = xs
Proof
  fs [list_enc'_def,list_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem list_enc'_cong:
  ∀l1 l2 f f'.
    (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒
    (list_enc' f l1 = list_enc' f' l2)
Proof
  fs [] \\ Induct \\ fs [list_enc'_def]
QED

Theorem list_dec'_cong:
  ∀l1 l2 f f'.
    (l1 = l2) ∧ (∀x. MEM x (list_dec' I l2) ⇒ (f x = f' x)) ⇒
    (list_dec' f l1 = list_dec' f' l2)
Proof
  fs [] \\ Induct \\ fs [list_dec'_def,MAP_EQ_f]
QED

val _ = app DefnBase.export_cong ["list_enc'_cong", "list_dec'_cong"];

(* pair *)

Definition pair_enc'_def:
  pair_enc' f f' (x,y) = Tree 0 [f x; f' y]
End

Definition pair_dec'_def:
  pair_dec' f f' (Tree _ xs) = (f (nth 0 xs), f' (nth 1 xs))
End

Theorem pair_enc'_fst_snd:
  g (f (FST x)) = FST x ∧ g' (f' (SND x)) = SND x ⇒
  pair_dec' g g' (pair_enc' f f' x) = x
Proof
  PairCases_on ‘x’ \\ fs [pair_enc'_def,pair_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem pair_enc'_thm[simp]:
  (∀x. g (f x) = x) ∧  (∀x. g' (f' x) = x) ⇒
  pair_dec' g g' (pair_enc' f f' x) = x
Proof
  PairCases_on ‘x’ \\ fs [pair_enc'_def,pair_dec'_def,MAP_MAP_o,o_DEF]
QED

Theorem pair_enc'_cong:
  ∀l1 l2 f f' g g'.
    (l1 = l2) ∧
    (∀x. x = FST l1 ⇒ (f x = f' x)) ∧
    (∀x. x = SND l1 ⇒ (g x = g' x)) ⇒
    (pair_enc' f g l1 = pair_enc' f' g' l2)
Proof
  fs [] \\ Cases \\ fs [pair_enc'_def]
QED

Theorem pair_dec'_cong:
  ∀l1 l2 f f' g g'.
    (l1 = l2) ∧
    (∀x. x = nth 0 (list_dec' I l1) ⇒ (f x = f' x)) ∧
    (∀x. x = nth 1 (list_dec' I l1) ⇒ (g x = g' x)) ⇒
    (pair_dec' f g l1 = pair_dec' f' g' l2)
Proof
  fs [] \\ Cases \\ fs [pair_dec'_def,list_dec'_def]
QED

val _ = app DefnBase.export_cong ["pair_enc'_cong", "pair_dec'_cong"];

(* option *)

Definition option_enc'_def:
  option_enc' f NONE = Tree 0 [] ∧
  option_enc' f (SOME x) = Tree 1 [f x]
End

Definition option_dec'_def:
  option_dec' f (Tree n xs) = if n = 0 then NONE else SOME (f (nth 0 xs))
End

Theorem option_enc'_thm[simp]:
  (∀x. g (f x) = x) ⇒
  option_dec' g (option_enc' f x) = x
Proof
  Cases_on ‘x’ \\ fs [option_enc'_def,option_dec'_def,MAP_MAP_o,o_DEF]
QED

(* tra *)

Definition tra_enc'_def:
  tra_enc' None = Tree 0 [] ∧
  tra_enc' (Union t1 t2) = Tree 1 [tra_enc' t1; tra_enc' t2] ∧
  tra_enc' (Cons t n) = Tree 2 [tra_enc' t; num_enc' n] ∧
  tra_enc' (SourceLoc n1 n2 n3 n4) =
    Tree 3 [num_enc' n1; num_enc' n2; num_enc' n3; num_enc' n4]
End

Definition tra_dec'_def:
  tra_dec' (Tree n xs) =
    if n = 0 then None
    else if n = 1 then
      case xs of
      | [x1;x2] => Union (tra_dec' x1) (tra_dec' x2)
      | _ => None
    else if n = 2 then
      case xs of
      | [x1;x2] => Cons (tra_dec' x1) (num_dec' x2)
      | _ => None
    else
      case xs of
      | [x1;x2;x3;x4] => SourceLoc (num_dec' x1) (num_dec' x2) (num_dec' x3) (num_dec' x4)
      | _ => None
End

Definition tra_enc_def:
  tra_enc = num_tree_enc o tra_enc'
End

Definition tra_dec_def:
  tra_dec = (tra_dec' ## I) o num_tree_dec
End

Theorem tra_enc'_thm[simp]:
  tra_dec' (tra_enc' x) = x
Proof
  Induct_on ‘x’ \\ fs [tra_enc'_def,tra_dec'_def]
QED

Theorem tra_enc_dec_ok:
  enc_dec_ok tra_enc tra_dec
Proof
  fs [tra_enc_def,tra_dec_def]
  \\ match_mp_tac enc_dec_ok_o
  \\ fs [num_tree_enc_dec_ok]
QED

(* automation *)

val enc_dec_mapping =
  ref ([(“:bool”, “bool_enc'”, “bool_dec'”),
        (“:num”, “num_enc'”, “num_dec'”),
        (“:int”, “int_enc'”, “int_dec'”),
        (“:char”, “chr_enc'”, “chr_dec'”)]);

fun reg_enc_dec ty enc dec =
   (enc_dec_mapping := (ty,enc,dec) :: (!enc_dec_mapping));

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
  val _ = reg_enc_dec ty enc_tm dec_tm
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

val _ = reg_enc_dec “:tra” “tra_enc'” “tra_dec'”;

fun define_enc_dec ty = let
  val (enc_def_tm, dec_def_tm) = enc_dec_for ty
  val enc_def = Define [ANTIQUOTE enc_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val dec_def = Define [ANTIQUOTE dec_def_tm] |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val (e,x) = enc_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val (d,_) = dec_def |> CONJUNCTS |> hd |> concl |> dest_eq |> fst |> dest_comb
  val _ = reg_enc_dec ty e d
  val x = mk_var("x",type_of x)
  val goal = mk_forall(x,mk_eq(mk_comb(d,mk_comb(e,x)),x))
  val ty_n = type_to_string ty |> explode |> tl |> implode
             |> String.translate (fn c => if c = #"$" then "_" else implode [c])
  val lemma = prove(goal,Cases \\ fs [enc_def,dec_def])
  val _ = save_thm(ty_n ^ "_enc'_thm[simp]",lemma)
  in (enc_def,dec_def,lemma) end;

val res = define_enc_dec “:var_name”
val res = define_enc_dec “:word_size”
val res = define_enc_dec “:opw”
val res = define_enc_dec “:ast$shift”
val res = define_enc_dec “:fp_cmp”
val res = define_enc_dec “:fp_uop”
val res = define_enc_dec “:fp_bop”
val res = define_enc_dec “:fp_top”
val res = define_enc_dec “:closLang$op”
val res = define_enc_dec “:mlstring”

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

Triviality MEM_num_tree_size:
  ∀xs x. MEM x xs ⇒ num_tree_size x ≤ num_tree1_size xs
Proof
  Induct \\ fs [num_tree_size_def] \\ rw [] \\ res_tac \\ fs []
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

val _ = reg_enc_dec “:closLang$exp” “closLang_exp_enc'” “closLang_exp_dec'”;

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

val _ = reg_enc_dec “:bvl$exp” “bvl_exp_enc'” “bvl_exp_dec'”;

Theorem bvl_exp_enc'_thm[simp]:
  ∀x. bvl_exp_dec' (bvl_exp_enc' x) = x
Proof
  ho_match_mp_tac bvl_exp_enc'_ind \\ rw []
  \\ fs [bvl_exp_enc'_def]
  \\ once_rewrite_tac [bvl_exp_dec'_def] \\ gvs []
  \\ fs [SF ETA_ss]
  \\ match_mp_tac list_enc'_mem \\ fs []
QED

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


(*

  <| source_conf : source_to_flat$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : bvl_to_bvi$config
   ; data_conf : data_to_word$config
   ; word_to_word_conf : word_to_word$config
   ; word_conf : 'a word_to_stack$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; tap_conf : tap_config

  source_to_flat$config =
           <| next : next_indices
            ; mod_env : environment
            ; pattern_cfg : flat_pattern$config

  where

  next_indices = <| vidx : num; tidx : num; eidx : num |>

  var_name = Glob tra num | Local tra string

  environment =
    <| c : (modN, conN, num # num option) namespace;
       v : (modN, varN, var_name) namespace; |>

  flat_pattern$config =
  <| pat_heuristic : (* pattern_matching$branch list *) unit -> num ;  (* problem! *)
    type_map : (num # num) list spt |>

  clos_to_bvl$config =
           <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; known_conf : clos_known$config option
            ; do_call : bool
            ; call_state : num_set # (num, num # closLang$exp) alist
            ; max_app : num
            |>

  clos_known$config =
           <| inline_max_body_size : num
            ; inline_factor : num
            ; initial_inline_factor : num
            ; val_approx_spt : val_approx spt
            |>`;

  bvl_to_bvi$config =
           <| inline_size_limit : num (* zero disables inlining *)
            ; exp_cut : num (* huge number effectively disables exp splitting *)
            ; split_main_at_seq : bool (* split main expression at Seqs *)
            ; next_name1 : num (* there should be as many of       *)
            ; next_name2 : num (* these as bvl_to_bvi_namespaces-1 *)
            ; inlines : (num # bvl$exp) spt
            |>

  data_to_word$config = <| tag_bits : num (* in each pointer *)
            ; len_bits : num (* in each pointer *)
            ; pad_bits : num (* in each pointer *)
            ; len_size : num (* size of length field in block header *)
            ; has_div : bool (* Div available in target *)
            ; has_longdiv : bool (* LongDiv available in target *)
            ; has_fp_ops : bool (* can compile floating-point ops *)
            ; has_fp_tern : bool (* can compile FMA *)
            ; call_empty_ffi : bool (* emit (T) / omit (F) calls to FFI "" *)
            ; gc_kind : gc_kind (* GC settings *) |>

  word_to_word$config =
  <| reg_alg : num
   ; col_oracle : num -> (num num_map) option |>

  word_to_stack$config = <| bitmaps : 'a word list ;
                            stack_frame_size : num spt |>

  stack_to_lab$config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>

  lab_to_target$config =
           <| labels : num num_map num_map
            ; pos : num
            ; asm_conf : 'a asm_config
            ; init_clock : num
            ; ffi_names : string list option
            ; hash_size : num
            |>

  asm_config =
    <| ISA            : architecture
     ; encode         : 'a asm -> word8 list
     ; big_endian     : bool
     ; code_alignment : num
     ; link_reg       : num option
     ; avoid_regs     : num list
     ; reg_count      : num
     ; fp_reg_count   : num  (* set to 0 if float not available *)
     ; two_reg_arith  : bool
     ; valid_imm      : (binop + cmp) -> 'a word -> bool
     ; addr_offset    : 'a word # 'a word
     ; byte_offset    : 'a word # 'a word
     ; jump_offset    : 'a word # 'a word
     ; cjump_offset   : 'a word # 'a word
     ; loc_offset     : 'a word # 'a word
     |>

  tap_config = Tap_Config
    (* save filename prefix *) mlstring
    (* bits which should be saved. the boolean indicates
       the presence of a '*' suffix, and matches all suffixes *)
    ((mlstring # bool) list)

*)

val _ = export_theory();
