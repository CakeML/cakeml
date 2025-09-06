(*
  The Floyd-Warshall algorithm - testing the monadic translator
*)
Theory floyd_warshallProg
Ancestors
  ml_monadBase ml_monad_translator
Libs
  preamble ml_monad_translator_interfaceLib

val _ = set_up_monadic_translator ();

(* An adjacency matrix represented as a 1D-array with a dimension var *)
Datatype:
  graph = <| adj_mat : (num option) list
           ; dim     : num
           |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

(* Translator configuration *)
val config =  global_state_config |>
              with_state ``:graph`` |>
              with_exception ``:state_exn`` |>
              with_refs [("dim", ``0 : num``)] |>
              with_resizeable_arrays
                [("adj_mat", ``[] : num option list``,
                  ``Subscript``, ``Subscript``)];

(* Begin the translation *)
val _ = start_translation config;

(* allocate an n x n matrix *)
Definition mk_graph_def:
  mk_graph n =
  do
    () <- set_dim n;
    alloc_adj_mat (n * n) NONE
  od
End

(* Because we are using a 1D array to represent 2D*)
Definition reind_def:
  reind (i:num) j =
  do
    d <- get_dim;
    return (i*d+j)
  od
End

(* Make (i,j) adjacent with weight w *)
Definition set_weight_def:
  set_weight i j w =
  do
    pij <- reind i j;
    update_adj_mat pij (SOME w)
  od
End

(* Returns the weight of (i,j) *)
Definition get_weight_def:
  get_weight i j =
  do
    pij <- reind i j;
    adj_mat_sub pij
  od
End

Definition st_ex_FOR_def:
  st_ex_FOR (i:num) j a =
  if i >= j then
    return ()
  else
    do
      () <- a i;
      st_ex_FOR (i+1) j a
    od
Termination
  WF_REL_TAC `measure (\(i, j:num, a).  j-i)`
End

Definition st_ex_FOREACH_def:
  (st_ex_FOREACH [] a = return ()) ∧
  (st_ex_FOREACH (x::xs) a =
  do
    () <- a x;
    st_ex_FOREACH xs a
  od)
End

(* Initialize the diagonal to zero *)
Definition init_diag_def:
  init_diag d =
  do
    st_ex_FOR 0n d (λi. set_weight i i 0n)
  od
End

(* TODO: defining it as :
  init_diag =
  do
    d <- get_dim
    ...
  od
  fails

  Similarly,
  init_diag () = ...
  fails too (I think this was fixed on master's translator..)
*)

(* Floyd-Warshall algorithm *)

Definition relax_def:
  relax i k j =
  do
    wik <- get_weight i k;
    wkj <- get_weight k j;
    wij <- get_weight i j;
    case (wik,wkj,wij) of
      (NONE,_,_) => return ()
    | (_,NONE,_) => return ()
    | (SOME wik,SOME wkj,NONE) => set_weight i j (wik+wkj) (* Infinity *)
    | (SOME wik,SOME wkj,SOME wij) =>
      if wik + wkj < wij
      then set_weight i j (wik+wkj)
      else return ()
 od
End

(* TODO: same as init_diag *)
Definition floyd_warshall_def:
  floyd_warshall d =
  do
    st_ex_FOR 0n d (λk.
    st_ex_FOR 0n d (λi.
    st_ex_FOR 0n d (λj.
      relax i k j
    )
    )
    )
  od
End

Definition init_g_def:
  init_g =  <|dim := ref_init_dim ; adj_mat := rarray_init_adj_mat |>
End

Definition init_from_ls_def:
  init_from_ls ls =
  do
    d <- get_dim;
    () <- init_diag d;
    st_ex_FOREACH ls (\(i,j,w). set_weight i j w)
  od
End

Definition do_floyd_def:
  do_floyd d ls =
  do
    () <- mk_graph d;
    () <- init_from_ls ls;
    () <- floyd_warshall d;
  od
End

val alloc_adj_mat_def = definition "alloc_adj_mat_def";
val get_dim_def = definition "get_dim_def";
val st_ex_FOR_ind = theorem "st_ex_FOR_ind";
val set_dim_def = definition "set_dim_def";

val msimps = [st_ex_bind_def,st_ex_FOR_def]

val _ = temp_tight_equality();

Theorem mk_graph_SUCCESS:
    ∃res.
    (mk_graph d s = (M_success ():(unit,state_exn) exc,res)) ∧
    d*d = LENGTH res.adj_mat ∧ res.dim = d
Proof
  fs[mk_graph_def]>>
  fs(msimps)>>
  fs [alloc_adj_mat_def,set_dim_def,Marray_alloc_def,LENGTH_REPLICATE]
QED

Theorem set_weight_SUCCESS:
   j + i * s.dim < LENGTH s.adj_mat ⇒
   ∃r. set_weight i j k s = (M_success (), r) ∧
       LENGTH r.adj_mat = LENGTH s.adj_mat ∧
       r.dim = s.dim
Proof
  rw[set_weight_def, reind_def, get_dim_def, st_ex_return_def]
  \\ rw msimps
  \\ rw[fetch"-""update_adj_mat_def"]
  \\ rw[ml_monadBaseTheory.Marray_update_def]
  \\ rw[ml_monadBaseTheory.Mupdate_eq]
QED

Theorem lemma:
   ∀i j d l. i < d ∧ j < d ∧ d * d ≤ l ⇒ (j:num) + i * d < l
Proof
  rw[]
  \\ qpat_x_assum`i < d` assume_tac
  \\ `∃m. 0 < m ∧ i + m = d` by (
        IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1
        \\ fs[] )
  \\ `i = d - m` by simp[]
  \\ `j + i * d < d * d` by (
    simp[LEFT_SUB_DISTRIB]
    \\ `m * d ≤ d * d` by simp[]
    \\ `m * d ≤ d ** 2` by metis_tac[TWO,EXP,ONE,MULT_CLAUSES]
    \\ simp[]
    \\ `0 < d` by simp[]
    \\ qpat_x_assum`j < d` assume_tac
    \\ IMP_RES_THEN (STRIP_THM_THEN SUBST1_TAC) LESS_ADD_1 THEN simp[] )
  \\ pop_assum mp_tac
  \\ simp[]
QED

Theorem init_diag_SUCCESS:
   ∀d s. d ≤ s.dim ∧ s.dim * s.dim ≤ LENGTH s.adj_mat ⇒
   ∃r. init_diag d s = (M_success (), r) ∧
       LENGTH r.adj_mat = LENGTH s.adj_mat ∧
       r.dim = s.dim
Proof
  simp[init_diag_def]
  \\ qmatch_goalsub_abbrev_tac`st_ex_FOR _ _ f`
  \\ Q.SPEC_TAC(`0n`,`n`)
  \\ qunabbrev_tac`f`
  \\ Induct_on`d-(n:num)`
  \\ rw[]
  >- rw[Once st_ex_FOR_def, st_ex_return_def]
  \\ rw[Once st_ex_FOR_def]
  \\ Cases_on`d` \\ fs[]
  \\ qmatch_assum_rename_tac`SUC d ≤ s.dim`
  \\ `v = d - n` by decide_tac \\ rveq
  \\ `n < s.dim` by decide_tac
  \\ qspecl_then[`n`,`n`,`s.dim`,`LENGTH s.adj_mat`]mp_tac lemma
  \\ impl_tac >- simp[] \\ strip_tac
  \\ drule (GEN_ALL set_weight_SUCCESS)
  \\ disch_then(qspec_then`0`strip_assume_tac)
  \\ simp[st_ex_bind_def]
  \\ first_x_assum(qspecl_then[`SUC d`,`n + 1`]mp_tac)
  \\ simp[]
  \\ disch_then(qspec_then`r`mp_tac)
  \\ simp[]
QED

val adj_mat_sub_def = fetch "-" "adj_mat_sub_def"

Theorem Msub_eqn[simp]:
    ∀e n ls v.
  Msub e n ls =
  if n < LENGTH ls then M_success (EL n ls)
                   else M_failure e
Proof
  ho_match_mp_tac Msub_ind>>rw[]>>
  simp[Once Msub_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`n`>>fs[]
QED

Triviality adj_mat_sub_SUCCESS:
  ∀s. i < s.dim ∧ j < s.dim ∧
  LENGTH s.adj_mat = s.dim * s.dim ⇒
  ∃v.
  adj_mat_sub (i + j *s.dim) s = (M_success v, s)
Proof
  rw[]>> drule lemma>>
  disch_then (qspec_then `i` assume_tac)>>rfs[]>>
  rw[adj_mat_sub_def,Marray_sub_def]
QED

val update_adj_mat_def = fetch "-" "update_adj_mat_def"

Theorem Mupdate_eqn[simp]:
    ∀e x n ls.
  Mupdate e x n ls =
  if n < LENGTH ls then
    M_success (LUPDATE x n ls)
  else
    M_failure e
Proof
  ho_match_mp_tac Mupdate_ind>>rw[]>>
  simp[Once Mupdate_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[LUPDATE_def]>>
  Cases_on`n`>>fs[LUPDATE_def]
QED

Triviality update_adj_mat_SUCCESS:
  ∀s.
    i < s.dim ∧ j < s.dim ∧
    LENGTH s.adj_mat = s.dim * s.dim ⇒
  ∃res.
  update_adj_mat (j + i *s.dim) v s = (M_success (), res) ∧
  res.dim = s.dim ∧
  LENGTH res.adj_mat = res.dim * res.dim
Proof
  rw[update_adj_mat_def]>>
  fs[Marray_update_def]>>
  qspecl_then [`i`,`j`] mp_tac lemma>>
  rpt (disch_then drule)>>fs[]
QED

Triviality relax_SUCCESS:
  i < s.dim ∧
  k < s.dim ∧
  j < s.dim ∧
  LENGTH s.adj_mat = s.dim * s.dim ⇒
  ∃res.
  relax i k j s = (M_success (),res) ∧
  res.dim = s.dim ∧
  LENGTH res.adj_mat = res.dim * res.dim
Proof
  rw[]>>
  fs[relax_def,st_ex_bind_def,get_weight_def,reind_def,get_dim_def,
     st_ex_return_def,set_weight_def]>>
  imp_res_tac adj_mat_sub_SUCCESS>>rfs[]>>
  every_case_tac>>fs[]>>
  imp_res_tac update_adj_mat_SUCCESS>>rfs[]
QED

Triviality floyd_warshall_SUCCESS_j:
  ∀j s.
  i < s.dim ∧
  k < s.dim ∧
  LENGTH s.adj_mat = s.dim * s.dim
  ⇒
  ∃res.
  st_ex_FOR j s.dim (\j. relax i k j) s = (M_success (),res) ∧
  res.dim = s.dim ∧
  LENGTH res.adj_mat = res.dim * s.dim
Proof
  Induct_on`s.dim-j`
  >-
    rw[Once st_ex_FOR_def,st_ex_return_def]
  >>
    rw[Once st_ex_FOR_def,st_ex_bind_def]>>
    `j < s.dim` by fs[]>>
    assume_tac relax_SUCCESS>>rfs[]>>
    first_x_assum(qspecl_then[`res`,`j+1`] assume_tac)>>rfs[]
QED

Triviality floyd_warshall_SUCCESS_i:
  ∀i s.
  k < s.dim ∧
  LENGTH s.adj_mat = s.dim * s.dim
  ⇒
  ∃res.
  st_ex_FOR i s.dim (\i. st_ex_FOR 0 s.dim (\j. relax i k j)) s =
    (M_success (),res) ∧
  res.dim = s.dim ∧
  LENGTH res.adj_mat = res.dim * s.dim
Proof
  Induct_on`s.dim-i`
  >-
    rw[Once st_ex_FOR_def,st_ex_return_def]
  >>
    rw[Once st_ex_FOR_def,st_ex_bind_def]>>
    `i < s.dim` by fs[]>>
    imp_res_tac (floyd_warshall_SUCCESS_j |> Q.SPEC `0n`) >>rfs[]>>
    first_x_assum(qspecl_then[`res''`,`i+1`] assume_tac)>>rfs[]
QED

Triviality floyd_warshall_SUCCESS_k:
  ∀k s.
  LENGTH s.adj_mat = s.dim * s.dim ⇒
  ∃res.
  st_ex_FOR k s.dim
  (λk. st_ex_FOR 0 s.dim (λi. st_ex_FOR 0 s.dim (λj. relax i k j))) s =
  (M_success (),res) ∧
  res.dim = s.dim ∧
  LENGTH res.adj_mat = res.dim * res.dim
Proof
  Induct_on`s.dim-k`>-
    rw[Once st_ex_FOR_def,st_ex_return_def]
  >>
    rw[Once st_ex_FOR_def,st_ex_bind_def]>>
    `k < s.dim` by fs[]>>
    imp_res_tac (floyd_warshall_SUCCESS_i |> Q.SPEC `0n`) >>rfs[]>>
    first_x_assum(qspecl_then[`res`,`k+1`] assume_tac)>>rfs[]
QED

(* Prove that the algorithm is always successful (?) *)
Theorem do_floyd_SUCCESS:
    EVERY (λ (i,j,w). i < d ∧ j < d) ls ⇒
    ∃res.
    do_floyd d ls init_g = (M_success (),res)
Proof
  rw[]>>
  simp[do_floyd_def,init_g_def]>>
  simp msimps>>
  TOP_CASE_TAC >>
  qmatch_asmsub_abbrev_tac`mk_graph d s`>>
  assume_tac mk_graph_SUCCESS>>
  fs[] \\ fs[]
  \\ rveq \\ fs[]
  \\ fs[init_from_ls_def]
  \\ fs[get_dim_def]
  \\ simp msimps
  \\ qspecl_then[`r.dim`,`r`]mp_tac init_diag_SUCCESS
  \\ simp[] \\ strip_tac
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`st_ex_FOREACH ls f s0`
  \\ `∃s1. st_ex_FOREACH ls f s0 = (M_success (), s1) ∧
           s1.dim = s0.dim ∧ LENGTH s1.adj_mat = LENGTH s0.adj_mat`
  by (
    qpat_x_assum`s0.dim = _`(assume_tac o SYM) \\ fs[]
    \\ qpat_x_assum`LENGTH s0.adj_mat = _`(assume_tac o SYM) \\ fs[]
    \\ qpat_x_assum`EVERY _ _`mp_tac
    \\ qpat_x_assum`s0.dim**2 = _`mp_tac
    \\ qid_spec_tac`s0`
    \\ qunabbrev_tac`f`
    \\ rpt(pop_assum kall_tac)
    \\ Induct_on`ls`
    \\ simp[st_ex_FOREACH_def]
    >- rw[st_ex_return_def]
    \\ simp msimps
    \\ rpt gen_tac \\ pairarg_tac
    \\ rw[]
    \\ qspecl_then[`i`,`j`,`s0.dim`,`LENGTH s0.adj_mat`]mp_tac lemma
    \\ impl_tac >- simp[] \\ strip_tac
    \\ drule (GEN_ALL set_weight_SUCCESS)
    \\ disch_then(qspec_then`w`strip_assume_tac)
    \\ simp[]
    \\ first_x_assum(qspec_then`r`mp_tac)
    \\ simp[] )
  \\ simp[]
  \\ simp[floyd_warshall_def]
  \\ `LENGTH s1.adj_mat = s1.dim * s1.dim` by fs[]
  \\ metis_tac[floyd_warshall_SUCCESS_k]
QED



val res = m_translate mk_graph_def;
val res = m_translate reind_def;
val res = m_translate set_weight_def;
val res = m_translate get_weight_def;
val res = m_translate st_ex_FOR_def;
val res = m_translate st_ex_FOREACH_def;
val res = m_translate init_diag_def;
val res = m_translate relax_def;
val res = m_translate floyd_warshall_def;
val res = m_translate init_from_ls_def;
val res = m_translate do_floyd_def;
