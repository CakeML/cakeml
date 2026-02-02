(*
  Formalization of the min coloring problem
*)
Theory color
Ancestors
  pbc graph_basic pbc_normalise mlstring mlint spt_to_vec
Libs
  preamble

val _ = numLib.temp_prefer_num();

(* f is a k-coloring function on the vertices {0..<v}
  iff it uses at most k colors ({0..<k}) and
      no two adjacent vertices have the same color *)
Definition is_k_color_def:
  is_k_color k f (v,e) ⇔
  (∀x. x < v ⇒ f x < k) ∧
  (∀x y.
    x < v ∧ y < v ∧
    is_edge e x y ⇒ f x ≠ f y)
End

Definition min_color_size_def:
  min_color_size g =
  MIN_SET ({k | ∃f. is_k_color k f g})
End

(* Color witness:
  We are given a mapping from {0..<v} to color option
  And we need to ensure that every vertex is assigned a color
*)
Definition parse_col_header_def:
  (parse_col_header [INL p; _; INR k] =
    if p = strlit"p"
    then SOME k
    else NONE) ∧
  parse_col_header _ = NONE
End

(* To keep the internal representation with LAD,
  we use 0-indexing *)
Definition strip_num_def:
  (strip_num [] acc = SOME (REVERSE acc)) ∧
  (strip_num (INR n::ns) acc = strip_num ns (n::acc)) ∧
  (strip_num (INL _::ns) acc = NONE)
End

Definition parse_col_line_def:
  parse_col_line ls =
    case ls of (INL s::rest) =>
      if s = strlit"s"
      then
        strip_num rest []
      else NONE
    | _ => NONE
End

Definition parse_col_lines_def:
  (parse_col_lines c [] acc = SOME (c,acc)) ∧
  (parse_col_lines c (l::ls) acc =
    case parse_col_line l of
      NONE => NONE
    | SOME vs =>
      let acc' = FOLDL (λacc v. sptree$insert v c acc) acc vs in
      parse_col_lines (c+1) ls acc')
End

(* For simplicity, set a default lookup *)
Definition mk_col_def:
  mk_col vec x =
  case vec_lookup vec x of
    NONE => 0
  | SOME k => k
End

Definition parse_col_toks_def:
  parse_col_toks lines =
  case FILTER nocomment_line lines of
    [] => NONE
  | (h::xs) =>
    (case parse_col_header h of NONE => NONE
    | SOME k =>
      (case parse_col_lines 0 xs LN of
        NONE => NONE
      | SOME (c,es) =>
        if c = k
        then
          SOME (k,mk_col (spt_to_vec es))
        else NONE))
End

Definition parse_col_def:
  parse_col lines = parse_col_toks (MAP toks_num lines)
End

Definition check_k_color_aux_def:
  check_k_color_aux k f e v ⇔
  let c = f v in
  c < k ∧
  let vs = neighbours (e:edges) (v:num) in
  EVERY (λy. f y ≠ c) vs
End

Definition check_k_color_def:
  check_k_color k f (v,e) =
  EVERY (check_k_color_aux k f e) (COUNT_LIST v)
End

Theorem check_k_color_is_k_color:
  good_graph g ⇒
  (check_k_color k f g ⇔
  is_k_color k f g)
Proof
  `∃v e. g = (v,e)` by metis_tac[PAIR]>>
  rw[check_k_color_def,is_k_color_def,good_graph_eq,SUBSET_DEF]>>
  gvs[EVERY_MEM,MEM_COUNT_LIST,check_k_color_aux_def,MEM_neighbours]>>
  eq_tac>>rw[]>>
  gvs[is_edge_def,AllCasePreds()]>>
  metis_tac[]
QED

Datatype:
  annot = Edge num num num    (* v1,v2,c: vertices v1, v2 do not both have color c *)
        | AtLeastOneColor num (* v: vertex v has at-least-one color                *)
        | AtMostOneColor num  (* v: vertex v has at-most-one color                 *)
        | VC_Imp_CU num       (* c: vertex-has-color implies color-used            *)
        | CU_Imp_VC num       (* c: color-used implies vertex-has-color            *)
End

Datatype:
  var = VertexHasColor num num (* v,c: vertex v has color c   *)
      | ColorUsed num          (* c: some vertex uses color c *)
End

Definition gen_constraint_def:
  gen_constraint (n:num) ((v,e):graph) (Edge x y c) =
    (if c < n ∧ x < v ∧ y < v ∧ is_edge e x y then
       SOME (GreaterEqual, [(1i, Neg (VertexHasColor x c));
                            (1i, Neg (VertexHasColor y c))], 1i)
     else NONE) ∧
  (gen_constraint (n:num) ((v,e):graph) (AtLeastOneColor vertex) =
    if vertex < v then
      SOME (GreaterEqual,
            GENLIST (λcolor. (1i,Pos (VertexHasColor vertex color))) n, 1i)
    else NONE) ∧
  (gen_constraint (n:num) ((v,e):graph) (AtMostOneColor vertex) =
    if vertex < v then
      SOME (GreaterEqual,
            GENLIST (λcolor. (1i,Neg (VertexHasColor vertex color))) n, & (n - 1))
    else NONE) ∧
  (gen_constraint (n:num) ((v,e):graph) (VC_Imp_CU c) =
    if c < n then
      SOME (GreaterEqual,
            (& v, Pos (ColorUsed c)) :: GENLIST (λu. (1i,Neg (VertexHasColor u c))) v, & v)
    else NONE) ∧
  (gen_constraint (n:num) ((v,e):graph) (CU_Imp_VC c) =
    if c < n then
      SOME (GreaterEqual,
            (1i, Neg (ColorUsed c)) :: GENLIST (λu. (1i,Pos (VertexHasColor u c))) v, 1i)
    else NONE)
End

Definition gen_named_constraint_def:
  gen_named_constraint n (v,e) a =
    case gen_constraint n (v,e) a of
    | NONE => []
    | SOME c => [(a,c)]
End

Definition flat_genlist_def:
  flat_genlist n f = FLAT (GENLIST f n)
End

Definition encode_def:
  encode (n:num) ((v,e):graph) =
    (* every vertex has at least one color *)
    flat_genlist v (λvertex.
      gen_named_constraint n (v,e) (AtLeastOneColor vertex)) ++
    (* every vertex has at most one color *)
    flat_genlist v (λvertex.
      gen_named_constraint n (v,e) (AtMostOneColor vertex)) ++
    (* every color: VC_Imp_CU *)
    flat_genlist n (λc.
      gen_named_constraint n (v,e) (VC_Imp_CU c)) ++
    (* every color: CU_Imp_VC *)
    flat_genlist n (λc.
      gen_named_constraint n (v,e) (CU_Imp_VC c)) ++
    (* for each color: at least one end of each edge does not have that color *)
    flat_genlist n (λcolor.
      flat_genlist v (λx.
        flat_genlist v (λy.
          gen_named_constraint n (v,e) (Edge x y color))))
  :(annot # var pbc) list
End

Definition color_obj_def:
  color_obj (n:num) =
    SOME (GENLIST (λc. (1, Pos (ColorUsed c))) n,0): ((var lin_term # int) option)
End

Theorem iSUM_GE_1[local]:
  EVERY (λx. x = 0 ∨ x = 1) xs ⇒
  (iSUM xs >= 1 ⇔ ∃x. MEM x xs ∧ x >= 1)
Proof
  Induct_on ‘xs’ \\ gvs [iSUM_def]
  \\ rw [] \\ gvs [SF DNF_ss]
  \\ qsuff_tac ‘iSUM xs >= 0’ >- intLib.COOPER_TAC
  \\ pop_assum mp_tac \\ pop_assum kall_tac
  \\ Induct_on ‘xs’ \\ gvs [iSUM_def]
  \\ rw [] \\ res_tac \\ intLib.COOPER_TAC
QED

Theorem iSUM_append:
  ∀xs ys. iSUM (xs ++ ys) = iSUM xs + iSUM ys
Proof
  Induct \\ gvs [iSUM_def,integerTheory.INT_ADD_ASSOC]
QED

Theorem iSUM_EQ_LENGTH:
  ∀xs. EVERY (λx. x = 1) xs ⇒ iSUM xs = & LENGTH xs
Proof
  Induct \\ gvs [iSUM_def, ADD1, integerTheory.INT_ADD]
QED

Theorem iSUM_LEQ_LENGTH:
  ∀xs. EVERY (λx. x = 0 ∨ x = 1) xs ⇒ iSUM xs ≤ & LENGTH xs
Proof
  Induct \\ gvs [iSUM_def, ADD1, integerTheory.INT_ADD]
  \\ rw [] \\ res_tac \\ gvs [] \\ intLib.COOPER_TAC
QED

Theorem iSUM_GENLIST_LEQ:
  ∀xs. EVERY (λx. x = 0 ∨ x = 1) (GENLIST f n) ⇒ iSUM (GENLIST f n) ≤ & n
Proof
  rw [] \\ drule iSUM_LEQ_LENGTH \\ gvs []
QED

Theorem iSUM_NOT_GE_LENGTH:
  ∀xs. EVERY (λx. x = 0 ∨ x = 1) xs ∧ MEM 0 xs ∧ LENGTH xs = v ⇒
       ¬(iSUM xs ≥ &v)
Proof
  Induct \\ rw [] \\ gvs [iSUM_def,ADD1,GSYM integerTheory.INT_ADD]
  \\ gvs [MEM_SPLIT,iSUM_append,iSUM_def]
  \\ imp_res_tac iSUM_LEQ_LENGTH \\ intLib.COOPER_TAC
QED

Theorem iSUM_one_less:
  ∀n t f.
    f t = 0 ∧ t < n ∧ (∀k. k < n ∧ k ≠ t ⇒  f k = 1) ⇒
    iSUM (GENLIST f n) ≥ &(n − 1)
Proof
  Induct \\ gvs [] \\ rw []
  \\ Cases_on ‘n = t’ \\ gvs []
  \\ simp [GENLIST,SNOC_APPEND,iSUM_append,iSUM_def]
  >-
   (‘∀k. k < n ⇒ f k = 1’ by gvs []
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘n’ \\ Induct
    \\ gvs [iSUM_def] \\ rw []
    \\ simp [GENLIST,SNOC_APPEND,iSUM_append,iSUM_def]
    \\ gvs [GSYM integerTheory.INT_OF_NUM_ADD, integerTheory.int_ge, ADD1])
  \\ last_x_assum $ qspecl_then [‘t’,‘f’] mp_tac
  \\ impl_tac >- gvs []
  \\ qabbrev_tac ‘k = iSUM (GENLIST f n)’
  \\ Cases_on ‘n’ \\ gvs [ADD1]
  \\ simp [GSYM integerTheory.INT_OF_NUM_ADD, integerTheory.int_ge]
QED

Theorem MEM_option[local]:
  MEM x (case opt of NONE => [] | SOME y => [f y]) ⇔
  ∃y. opt = SOME y ∧ x = f y
Proof
  Cases_on ‘opt’ \\ gvs [] \\ eq_tac \\ simp []
QED

Theorem ZERO_LE_iSUM:
  ∀xs. EVERY (λx. 0 ≤ x) xs ⇒ 0 ≤ iSUM xs
Proof
  Induct \\ gvs [iSUM_def]
QED

Theorem GENLIST_SPLIT_LESS:
  ∀n m f. n < m ⇒
          GENLIST f m = GENLIST f n ++ [f n] ++ GENLIST (\k. f (n + k + 1)) (m - n - 1)
Proof
  rpt strip_tac
  \\ ‘n + 1 ≤ m’ by fs []
  \\ gvs [LESS_EQ_EXISTS]
  \\ ‘n + (p + 1) = p + (1 + n)’ by fs []
  \\ asm_rewrite_tac []
  \\ rewrite_tac [GENLIST_APPEND]
  \\ gvs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp [FUN_EQ_THM]
QED

Theorem CARD_INTER_count:
  CARD (s ∩ count (SUC k)) =
  if k ∈ s then 1 + CARD (s ∩ count k) else CARD (s ∩ count k)
Proof
  fs [COUNT_SUC]
  \\ once_rewrite_tac [INSERT_SING_UNION]
  \\ rewrite_tac [UNION_OVER_INTER]
  \\ DEP_REWRITE_TAC [CARD_UNION_DISJOINT]
  \\ conj_tac
  >-
   (rw [] \\ rpt (irule FINITE_INTER) \\ gvs []
    \\ gvs [IN_DISJOINT])
  \\ qsuff_tac ‘s ∩ {k} = if k ∈ s then {k} else {}’ >- rw []
  \\ rw []
  \\ gvs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw []
QED

Definition colors_used_def:
  colors_used (f:num -> num) v = { c | ∃x. f x = c ∧ x < v }
End

Theorem CARD_colors_used_lemma[local]:
  ∀k n v.
    is_k_color n f (v,e) ∧ k ≤ n ⇒
    iSUM (GENLIST (λc. b2i (c ∈ colors_used f v)) k) =
    & CARD (colors_used f v ∩ count k)
Proof
  Induct \\ gvs [iSUM_def,GENLIST,SNOC_APPEND,iSUM_append]
  \\ rw [CARD_INTER_count,GSYM integerTheory.INT_ADD]
  \\ last_x_assum irule
  \\ first_x_assum $ irule_at Any \\ gvs []
QED

Theorem CARD_colors_used:
  is_k_color n f (v,e) ⇒
  iSUM (GENLIST (λc. b2i (c ∈ colors_used f v)) n) =
  & CARD (colors_used f v)
Proof
  rw [] \\ ‘n ≤ n’ by fs []
  \\ drule_all CARD_colors_used_lemma \\ rw []
  \\ AP_TERM_TAC
  \\ gvs [EXTENSION]
  \\ rw [] \\ eq_tac \\ rw []
  \\ gvs [colors_used_def,is_k_color_def]
QED

Theorem is_k_color_IMP_CARD_colors_used_LEQ:
  is_k_color k f (v,e) ⇒
  CARD (colors_used f v) ≤ k
Proof
  strip_tac
  \\ qsuff_tac ‘& CARD (colors_used f v) ≤ & k : int’ >- fs []
  \\ drule CARD_colors_used
  \\ disch_then $ rewrite_tac o single o GSYM
  \\ irule iSUM_GENLIST_LEQ
  \\ gvs [EVERY_GENLIST]
  \\ gvs [oneline b2i_def] \\ rw []
QED

Theorem encode_correct:
  good_graph (v,e) ⇒
  ((∃f.
      is_k_color n f (v,e) ∧
      CARD (colors_used f v) = k)
   ⇔
   (∃w.
      satisfies w (set (MAP SND (encode n (v,e)))) ∧
      eval_obj (color_obj n) w = & k))
Proof
  simp [satisfiable_def] \\ rw []
  \\ irule EQ_TRANS
  \\ qexists_tac
     ‘(∃f. is_k_color n f (v,e) ∧ iSUM (GENLIST (λc. b2i (c ∈ colors_used f v)) n) = & k)’
  \\ conj_tac
  >-
   (AP_TERM_TAC \\ simp [FUN_EQ_THM] \\ rw [] \\ eq_tac \\ rw []
    \\ imp_res_tac CARD_colors_used \\ gvs [])
  \\ eq_tac \\ rw []
  >-
   (qexists_tac ‘λa. case a of
                     | VertexHasColor x c => (f x = c)
                     | ColorUsed c => c ∈ colors_used f v’
    \\ gvs [encode_def]
    \\ simp [satisfies_def,MEM_MAP,EXISTS_PROD,flat_genlist_def,
             MEM_FLAT,MEM_GENLIST,PULL_EXISTS,gen_named_constraint_def]
    \\ simp [gen_constraint_def]
    \\ rpt strip_tac
    >-
     (gvs[satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST]
      \\ DEP_REWRITE_TAC [iSUM_GE_1]
      \\ conj_tac
      >- simp [EVERY_GENLIST,oneline b2i_def,AllCaseEqs(),EVERY_MAP]
      \\ gvs [is_k_color_def,MEM_GENLIST,PULL_EXISTS]
      \\ qexists_tac ‘f vertex’ \\ gvs [])
    >-
     (gvs[satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST,o_DEF]
      \\ irule iSUM_one_less
      \\ gvs [is_k_color_def]
      \\ last_x_assum drule \\ rw []
      \\ qexists_tac ‘f vertex’ \\ gvs [])
    >-
     (gvs[satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST,o_DEF,iSUM_def]
      \\ rename [‘c ∈ colors_used f v’]
      \\ Cases_on ‘c ∈ colors_used f v’ \\ gvs [integerTheory.INT_GE]
      >-
       (irule ZERO_LE_iSUM
        \\ gvs [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ DEP_REWRITE_TAC [iSUM_EQ_LENGTH]
      \\ gvs [EVERY_GENLIST,colors_used_def,IN_DEF,oneline b2i_def] \\ rw [])
    >-
     (gvs[satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST,o_DEF,iSUM_def]
      \\ rename [‘c ∈ colors_used f v’]
      \\ reverse $ Cases_on ‘c ∈ colors_used f v’ \\ gvs [integerTheory.INT_GE]
      >-
       (DEP_REWRITE_TAC [ZERO_LE_iSUM]
        \\ gvs [EVERY_GENLIST,colors_used_def,oneline b2i_def,IN_DEF] \\ rw [])
      \\ gvs [GSYM integerTheory.INT_GE]
      \\ DEP_REWRITE_TAC [iSUM_GE_1]
      \\ gvs [MEM_GENLIST,EVERY_GENLIST, oneline b2i_def, AllCaseEqs()]
      \\ gvs [SF DNF_ss, colors_used_def, IN_DEF]
      \\ first_assum $ irule_at Any \\ gvs [])
    >-
     (Cases_on ‘is_edge e x y’ \\ gvs []
      \\ simp [satisfies_pbc_def,eval_lin_term_def]
      \\ gvs [is_k_color_def,MEM_GENLIST,PULL_EXISTS]
      \\ gvs []
      \\ first_x_assum drule_all
      \\ Cases_on ‘f x = color’ >- gvs [iSUM_def]
      \\ Cases_on ‘f y = color’ >- gvs [iSUM_def]
      \\ gvs [iSUM_def])
    \\ gvs [color_obj_def,eval_obj_def,eval_lin_term_def,MAP_GENLIST,o_DEF,iSUM_def])
  \\ qexists_tac ‘λx. @c. w (VertexHasColor x c) ∧ c < n’
  \\ gvs [encode_def,satisfies_def,MEM_MAP,EXISTS_PROD,flat_genlist_def,
          MEM_FLAT,MEM_GENLIST,PULL_EXISTS,gen_named_constraint_def,SF DNF_ss]
  \\ gvs [gen_constraint_def,MEM_option]
  \\ ‘∀x. x < v ⇒ ∃c. w (VertexHasColor x c) ∧ c < n’ by
   (rw [] \\ last_x_assum drule
    \\ simp [satisfies_pbc_def,eval_lin_term_def]
    \\ DEP_REWRITE_TAC [iSUM_GE_1]
    \\ conj_tac
    >- simp [EVERY_GENLIST,oneline b2i_def,AllCaseEqs(),EVERY_MAP]
    \\ gvs [MEM_MAP,PULL_EXISTS,MEM_GENLIST]
    \\ rw [] \\ qexists_tac ‘color’ \\ gvs []
    \\ Cases_on ‘w (VertexHasColor x color)’ \\ gvs [])
  \\ ‘∀x. x < v ⇒ (@c. w (VertexHasColor x c) ∧ c < n) < n ∧
                  w (VertexHasColor x (@c. w (VertexHasColor x c) ∧ c < n))’
    by metis_tac []
  \\ simp [is_k_color_def]
  \\ rpt strip_tac
  >-
   (rename [‘is_edge e x y’]
    \\ first_x_assum (fn th => qspec_then ‘x’ mp_tac th \\ qspec_then ‘y’ mp_tac th)
    \\ qabbrev_tac ‘c_x = (@c. w (VertexHasColor x c) ∧ c < n)’
    \\ qabbrev_tac ‘c_y = (@c. w (VertexHasColor y c) ∧ c < n)’
    \\ first_x_assum (fn th => qspec_then ‘x’ mp_tac th \\ qspec_then ‘y’ mp_tac th)
    \\ simp [] \\ rpt strip_tac \\ gvs []
    \\ first_x_assum $ qspecl_then [‘c_x’,‘x’,‘y’] mp_tac
    \\ simp [satisfies_pbc_def,eval_lin_term_def,iSUM_def])
  \\ gvs [color_obj_def,eval_obj_def]
  \\ rewrite_tac [GSYM integerTheory.INT_OF_NUM_EQ]
  \\ rewrite_tac [GSYM CARD_colors_used]
  \\ qpat_x_assum ‘_ = &k’ (assume_tac o GSYM)
  \\ asm_rewrite_tac []
  \\ simp [eval_lin_term_def,MAP_GENLIST,o_DEF]
  \\ AP_TERM_TAC
  \\ gvs [listTheory.GENLIST_FUN_EQ] \\ rw []
  \\ AP_TERM_TAC
  \\ simp [colors_used_def]
  \\ reverse eq_tac
  >-
   (strip_tac
    \\ gvs [satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST,o_DEF]
    \\ ntac 2 $ qpat_x_assum ‘∀d. d < n ⇒ _’ $ qspec_then ‘c’ mp_tac
    \\ rw [iSUM_def]
    \\ qpat_x_assum ‘iSUM _ >= 1i’ mp_tac
    \\ DEP_REWRITE_TAC [iSUM_GE_1]
    \\ conj_tac >- gvs [EVERY_GENLIST,oneline b2i_def,AllCaseEqs()]
    \\ gvs [MEM_GENLIST] \\ rw []
    \\ Cases_on ‘w (VertexHasColor u c)’ \\ gvs []
    \\ qexists_tac ‘u’ \\ simp []
    \\ qsuff_tac ‘∀d. w (VertexHasColor u d) ∧ d < n ⇔ d = c’ >- simp []
    \\ rw [] \\ eq_tac \\ rw []
    \\ CCONTR_TAC
    \\ last_x_assum $ qspec_then ‘u’ kall_tac
    \\ last_x_assum $ qspec_then ‘u’ mp_tac
    \\ gvs [integerTheory.INT_GE,integerTheory.int_le]
    \\ qabbrev_tac ‘ff = λcolor. 1 − b2i (w (VertexHasColor u color))’
    \\ ‘c < d ∨ d < c’ by decide_tac
    >-
     (qspecl_then [‘d’,‘n’,‘ff’] mp_tac GENLIST_SPLIT_LESS \\ simp []
      \\ qspecl_then [‘c’,‘d’,‘ff’] mp_tac GENLIST_SPLIT_LESS \\ simp []
      \\ rw [Abbr ‘ff’,iSUM_append,iSUM_def]
      \\ qmatch_goalsub_abbrev_tac
           ‘iSUM (GENLIST f1 _) + iSUM (GENLIST f2 _) + iSUM (GENLIST f3 _)’
      \\ ‘iSUM (GENLIST f1 c) ≤ & c’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ ‘iSUM (GENLIST f2 (d − (c + 1))) ≤ & (d − (c + 1))’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ ‘iSUM (GENLIST f3 (n − (d + 1))) ≤ & (n − (d + 1))’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ intLib.COOPER_TAC)
    >-
     (qspecl_then [‘c’,‘n’,‘ff’] mp_tac GENLIST_SPLIT_LESS \\ simp []
      \\ qspecl_then [‘d’,‘c’,‘ff’] mp_tac GENLIST_SPLIT_LESS \\ simp []
      \\ rw [Abbr ‘ff’,iSUM_append,iSUM_def]
      \\ qmatch_goalsub_abbrev_tac
           ‘iSUM (GENLIST f1 _) + iSUM (GENLIST f2 _) + iSUM (GENLIST f3 _)’
      \\ ‘iSUM (GENLIST f1 d) ≤ & d’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ ‘iSUM (GENLIST f2 (c − (d + 1))) ≤ & (c − (d + 1))’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ ‘iSUM (GENLIST f3 (n − (c + 1))) ≤ & (n − (c + 1))’ by
       (irule iSUM_GENLIST_LEQ
        \\ unabbrev_all_tac \\ rw [EVERY_GENLIST,oneline b2i_def] \\ rw [])
      \\ intLib.COOPER_TAC))
  \\ rpt strip_tac
  \\ qabbrev_tac ‘c1 = (@c. w (VertexHasColor x c) ∧ c < n)’
  \\ gvs []
  \\ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs []
  \\ qpat_x_assum ‘∀c. c < n ⇒ _’ kall_tac
  \\ qpat_x_assum ‘∀c. c < n ⇒ _’ $ qspec_then ‘c’ mp_tac
  \\ simp [satisfies_pbc_def,eval_lin_term_def,MAP_GENLIST]
  \\ gvs [iSUM_def,o_DEF]
  \\ Cases_on ‘w (ColorUsed c)’ \\ gvs []
  \\ irule iSUM_NOT_GE_LENGTH \\ gvs []
  \\ gvs [MEM_GENLIST,EVERY_GENLIST,oneline b2i_def,AllCaseEqs()]
  \\ rw []
  \\ first_x_assum $ irule_at Any \\ gvs []
QED

Theorem encode_correct_leq:
  good_graph (v,e) ⇒
  ((∃f.
      is_k_color n f (v,e) ∧
      CARD (colors_used f v) <= k)
   ⇔
   (∃w.
      satisfies w (set (MAP SND (encode n (v,e)))) ∧
      eval_obj (color_obj n) w <= & k))
Proof
  strip_tac
  \\ drule encode_correct
  \\ disch_then $ qspec_then ‘n’ assume_tac
  \\ gvs [EQ_IMP_THM]
  \\ gvs [SF DNF_ss] \\ rw []
  >-
   (last_x_assum drule
    \\ strip_tac
    \\ first_x_assum $ irule_at Any
    \\ intLib.COOPER_TAC)
  \\ ‘0 ≤ eval_obj (color_obj n) w’ by
   (gvs [color_obj_def,eval_obj_def,eval_lin_term_def,MAP_GENLIST,o_DEF]
    \\ irule ZERO_LE_iSUM
    \\ gvs [EVERY_GENLIST]
    \\ rw [oneline b2i_def])
  \\ last_x_assum drule
  \\ disch_then $ qspec_then ‘Num (eval_obj (color_obj n) w)’ mp_tac
  \\ impl_tac >- intLib.COOPER_TAC
  \\ strip_tac
  \\ first_x_assum $ irule_at Any
  \\ intLib.COOPER_TAC
QED

Definition enc_string_def:
  (enc_string (ColorUsed c) = concat [«cu_»; toString c]) ∧
  (enc_string (VertexHasColor v c) = concat [«vc_»; toString v; «_»; toString c])
End

Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  gvs [INJ_DEF] \\ reverse Cases \\ Cases \\ simp [enc_string_def]
  \\ gvs [concat_def]
  \\ Cases_on ‘toString n’
  \\ Cases_on ‘toString n'’
  \\ simp []
  >- metis_tac [num_to_str_11]
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ rpt disch_tac
  \\ drule num_to_str_APPEND_11
  \\ simp []
  \\ disch_then drule_all
  \\ Cases_on ‘toString n0’
  \\ Cases_on ‘toString n0'’
  \\ gvs []
  \\ rw [] \\ gvs []
  \\ metis_tac [num_to_str_11]
QED

Definition annot_string_def:
  annot_string a =
  case a of
  | Edge u v c => SOME (concat [«e_»; toString u; «_»; toString v; «_»; toString c])
  | AtLeastOneColor u => SOME (concat [«colgeq_»; toString u])
  | AtMostOneColor u  => SOME (concat [«colleq_»; toString u])
  | VC_Imp_CU c => SOME (concat [«vc_impl_cu_»; toString c])
  | CU_Imp_VC c => SOME (concat [«cu_impl_vc_»; toString c])
End

Definition full_encode_def:
  full_encode n g =
  (map_obj enc_string (color_obj n),
  MAP (annot_string ## map_pbc enc_string) (encode n g))
End

Definition mk_key_def:
  mk_key NONE = NONE ∧
  mk_key (SOME ann) =
    let ts = tokens (λc. ~ (#"0" ≤ c ∧ c ≤ #"9")) ann in
      if isPrefix (strlit "e_") ann then
        (case MAP fromNatString ts of
         | [SOME n1; SOME n2; SOME n3] => SOME (Edge n1 n2 n3)
         | _ => NONE)
      else if LENGTH ts = 1 then
        case fromNatString (HD ts) of
        | NONE => NONE
        | SOME n =>
            if isPrefix (strlit "colgeq_") ann then SOME $ AtLeastOneColor n else
            if isPrefix (strlit "colleq_") ann then SOME $ AtMostOneColor n else
            if isPrefix (strlit "vc") ann then SOME $ VC_Imp_CU n else
            if isPrefix (strlit "cu") ann then SOME $ CU_Imp_VC n else
              NONE
      else NONE
End

Theorem mk_key_test[local]:
  EVERY (λk. mk_key (annot_string k) = SOME k)
    [Edge 21 34 48;
     AtLeastOneColor 400;
     AtMostOneColor 2;
     VC_Imp_CU 34;
     CU_Imp_VC 45]
Proof
  EVAL_TAC
QED

(*
  TODO: for initial simplicity, we may wish to compare the
    input and lazy formulas by exact equality.

  However, for improved flexibility, we should perhaps
    allow for them to be equal up to normalization.
*)

Definition lazy_constraint_aux_def:
  lazy_constraint_aux n g (i:annot) (c: mlstring pbc) ⇔
    case gen_constraint n g i of NONE => F
    | SOME cc =>
      c = map_pbc enc_string cc
End

Definition lazy_constraint_def:
  lazy_constraint n g (c: mlstring option # mlstring pbc) ⇔
    case mk_key (FST c) of
      NONE => F
    | SOME i => lazy_constraint_aux n g i (SND c)
End

Definition lazy_encode_def:
  lazy_encode n g fml =
  let le = lazy_constraint n g in
    EVERY le fml
End

Theorem MEM_gen_named_constraint:
  MEM (x,y) (gen_named_constraint n g a) ⇔
  x = a ∧
  gen_constraint n g a = SOME y
Proof
  Cases_on`g`>>rw[gen_named_constraint_def]>>
  TOP_CASE_TAC>>simp[]>>
  metis_tac[]
QED

(* could prove a stronger theorem (annotations also equal), but not needed *)
Theorem lazy_encode_imp:
  lazy_encode n g fml ⇒
  set (MAP SND fml) ⊆
  set (MAP (map_pbc enc_string o SND) (encode n g))
Proof
  rw[lazy_encode_def,SUBSET_DEF,EVERY_MEM,MEM_MAP]>>
  first_x_assum drule>>rw[lazy_constraint_def]>>
  gvs[AllCasePreds(),lazy_constraint_aux_def]>>
  `∃ann c. y = (ann,c)` by metis_tac[PAIR]>>
  gvs[]>>
  Cases_on`g`>>
  simp[encode_def,flat_genlist_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
  qexists_tac`(i,cc)`>>
  simp[MEM_gen_named_constraint]>>
  Cases_on`i`>>
  simp[]>>
  gvs[gen_constraint_def]
QED

(* Check that the objective actually matches up,
  e.g.:
    map_obj enc_string (color_obj n) = SOME obj
*)
Definition lazy_color_obj_def:
  lazy_color_obj n (obj: mlstring lin_term # int) ⇔
    map_obj enc_string (color_obj n) = SOME obj
End

(* Attempt to guess the value of "n" based on the objective.
  The literals variables in the objective are all Pos literals *)
Definition parse_cu_def:
  parse_cu (c,l) =
  case l of
    Pos s =>
      if 3 ≤ strlen s then
        case mlint$fromNatString (substring s 3 (strlen s - 3)) of
          NONE => 0
        | SOME n => n
      else 0
  | _ => 0
End

Definition guess_n_def:
  guess_n (obj:mlstring lin_term # int) =
    MAX_LIST (MAP parse_cu (FST obj))
End

Definition lazy_full_encode_def:
  lazy_full_encode (g:graph) prob =
  case prob of
    (NONE:mlstring option,SOME obj, fml) =>
    let n = guess_n obj in
      if lazy_encode n g fml ∧ lazy_color_obj n obj
      then SOME n
      else NONE
  | _ => NONE
End

Theorem lazy_full_encode_thm:
  lazy_full_encode g prob = SOME n ⇒
  ∃obj fml fml'.
    prob = (NONE,SOME obj,fml) ∧
    full_encode n g = (SOME obj, fml') ∧
    set (MAP SND fml) ⊆ set (MAP SND fml')
Proof
  rw[lazy_full_encode_def]>>
  gvs[AllCaseEqs()]>>
  simp[full_encode_def]>>
  fs[lazy_color_obj_def]>>
  drule lazy_encode_imp>>
  simp[MAP_MAP_o]
QED

(* If the palette allowed is n, then we can claim a lower
  bound with at most n colors.
  No upper bound is to be used in the PB proof. *)
Definition conv_concl_def:
  (conv_concl n (OBounds (SOME lb) NONE) =
      if 0 ≤ lb ∧ Num lb ≤ n then SOME (Num lb)
      else NONE) ∧
  (conv_concl _ _ = NONE)
End

Theorem lazy_full_encode_sem_concl:
  good_graph g ∧
  lazy_full_encode g (vs,obj,fml) = SOME n ∧
  pbc$sem_concl (set (MAP SND fml)) obj concl ∧
  conv_concl n concl = SOME lb ⇒
  ∀f k.
    is_k_color k f g ⇒ lb ≤ k
Proof
  rw[]>>
  Cases_on`g`>>
  drule encode_correct>>
  simp[PULL_EXISTS, EQ_IMP_THM,SF DNF_ss]>>
  rw[]>>
  pop_assum kall_tac>>
  ‘~(n < k) ⇒ is_k_color n f (q,r)’ by
    (gvs [is_k_color_def] >> rw [] >> res_tac >> fs [])>>
  Cases_on ‘n < k’ >> gvs [] >>
  first_x_assum drule>>rw[]>>
  drule lazy_full_encode_thm >>rw[] >>
  gvs[oneline conv_concl_def,AllCaseEqs()]>>
  rename1`full_encode n (v,e) = (SOME obj,fmll)`>>
  rename1`OBounds (SOME lb) NONE`>>
  `sem_concl (set (MAP SND fmll)) (SOME obj) (OBounds (SOME lb) NONE)` by
    (fs[sem_concl_def]>>
    rw[]>>first_x_assum irule>>
    fs[satisfies_def,SUBSET_DEF])>>
  qpat_x_assum`sem_concl _ _ _` mp_tac>>
  gvs[full_encode_def]>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  simp[GSYM IMAGE_IMAGE, GSYM (Once LIST_TO_SET_MAP)]>>
  qpat_x_assum`_ = SOME obj` sym_sub_tac>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  rw[sem_concl_def]>>
  last_x_assum $ qspec_then ‘w’ mp_tac >>
  impl_tac >- simp [] >>
  simp [] >>
  ‘∃l. lb = & l’ by (Cases_on ‘lb’ >> gvs []) >>
  gvs [] >>
  rw [] >> irule LESS_EQ_TRANS >> pop_assum $ irule_at Any >>
  imp_res_tac is_k_color_IMP_CARD_colors_used_LEQ >> fs []
QED

Theorem full_encode_eq =
  full_encode_def
  |> SIMP_RULE (srw_ss()) [FORALL_PROD,encode_def,flat_genlist_def]
  |> SIMP_RULE (srw_ss()) [gen_named_constraint_def]
  |> SIMP_RULE (srw_ss()) [MAP_FLAT,MAP_GENLIST,MAP_APPEND,o_DEF,MAP_MAP_o,pbc_ge_def,
                           map_pbc_def,FLAT_FLAT,FLAT_MAP_SING,map_lit_def,MAP_if]
  |> SIMP_RULE (srw_ss()) [FLAT_GENLIST_FOLDN,FOLDN_APPEND_op]
  |> PURE_ONCE_REWRITE_RULE [APPEND_OP_DEF]
  |> SIMP_RULE (srw_ss()) [if_APPEND];
