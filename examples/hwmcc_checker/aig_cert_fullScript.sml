(*
  Verified certificate checker for the Hardware Model Checking Competition.
*)
Theory aig_cert_full
Ancestors
  errorMonad (* for monad_thms *)
  listRange
  mlint (* for num_to_str *)
  syntax_helper (* for the DIMACS printer *)
  xaig aig_parse xaig_cert xaig_cert_encode xaig_to_cnf
Libs
  preamble

(** List <-> Set **************************************************************)

(* Intersects xs with the set of numbers from m to n. *)
Definition range_inter_def:
  range_inter m n xs = FILTER (λh. m ≤ h ∧ h ≤ n) xs
End

Theorem range_inter_thm:
  set (range_inter m n xs) = set [m .. n] ∩ set xs
Proof
  simp [range_inter_def, EXTENSION, LIST_TO_SET_FILTER]
QED

(* Returns whether xs is a subset of the set of numbers from m to n. *)
Definition range_is_subset_def:
  (range_is_subset [] m n ⇔ T) ∧
  (range_is_subset (x::xs) m n ⇔
     m ≤ x ∧ x ≤ n ∧ range_is_subset xs m n)
End

Theorem range_is_subset_thm:
  ∀xs m n. range_is_subset xs m n ⇔ set xs ⊆ set [m .. n]
Proof
  Induct >> rw [range_is_subset_def] >> metis_tac []
QED

Theorem LIST_TO_SET_mapPartial:
  ∀xs. set (list$mapPartial f xs) = IMAGE_PARTIAL f (set xs)
Proof
  Induct >> simp [mapPartial_def]
  >> rw [IMAGE_PARTIAL_INSERT]
  >> CASE_TAC >> simp []
QED


(* Convert cnf to string  *****************************************************)

(* DIMACS output; the header declares limit as the variable count, which
   is an upper bound on the variables actually occurring (see lits_within) *)
Definition cnf_to_string_def:
  cnf_to_string (cnf: num clause list, limit: num) =
  concat (print_header_line limit (LENGTH cnf) :: MAP (print_lits #"\n") cnf)
End

(* end-to-end processing of model and witness *********************************)

(* parse_model and preprocess_model constitute the trusted frontend.
   Note that this is only a concern for the model,
   since mangling of the witness can only compromise provability,
   not soundness. Thus, while the preprocessing of the witness is not entirely
   trivial, the preprocessing of the model is kept straightforward. *)

Definition parse_model_def:
  parse_model mstr =
  do
    (maiger, rest) <- parse_aiger mstr 0;
    return maiger
  od
End

Definition preprocess_model_def:
  preprocess_model maiger =
  let
    mcounts = maiger.counts;
    micnt = mcounts.inputs;
    mlcnt = mcounts.latches;
    mlatch_start = micnt + 1;
    mmax_latch = micnt + mlcnt;
    mlatches = [mlatch_start .. mmax_latch];
    maig = maiger.aig;
    mreset = fromAList maiger.reset;
    mreset = (λl. lookup l mreset);
    mnext = fromAList maiger.next;
    mnext  = (λl. case lookup l mnext of
                    | SOME lit => lit
                    | NONE => (Base Ff, F) (* should not happen *));
    msafes =
      MAP not
        (if mcounts.bad = 0 ∧ mcounts.justice = 0 then maiger.outputs
         else maiger.bad);
    mcnstrs = maiger.constraints;
    mfair = MAP not maiger.fairness;
    mjust = maiger.justice;
    mlive = MAP (λsignals. mfair ++ (MAP not signals)) mjust;
  in
    (* By returning the bounds of the mlatches range, we can implement some
       set operations such as intersection more efficiently; see
       check_model. *)
    (maig, mreset, mnext, msafes, mcnstrs, mlive, mlatches,
     mlatch_start, mmax_latch)
End

Theorem preprocess_model_mlatches:
  preprocess_model maiger =
    (maig, mreset, mnext, msafes, mcnstrs, mlive, mlatches,
     mlatch_start, mmax_latch) ⇒
  mlatches = [mlatch_start .. mmax_latch]
Proof
  rw [preprocess_model_def]
QED

Definition parse_witness_def:
  parse_witness wstr =
  do
    (waiger, maps, rest) <- parse_aiger_and_symbols wstr 0;
    return (waiger, maps)
  od
End

(* TODO Pad to short witness signals/justices; did this in the past *)

Definition preprocess_witness_def:
  preprocess_witness maiger waiger ms =
  let
    (* information about the model is used for the shared and intervention
       mapping *)
    micnt = maiger.counts.inputs;
    mlcnt = maiger.counts.latches;
    (* -- witness -- *)
    wcounts = waiger.counts;
    wicnt = wcounts.inputs;
    wlcnt = wcounts.latches;
    wlatch_start = wicnt + 1;
    wmax_latch = wicnt + wlcnt;
    iren = ms.shared_inputs;
    lren = ms.shared_latches;
    (iren, lren) =
      if isEmpty iren ∧ isEmpty lren then
        default_shared micnt mlcnt wicnt wlcnt
      else (iren, lren);
    waig = shared_aig micnt mlcnt iren lren waiger.aig;
    wreset = fromAList (shared_latches micnt mlcnt iren lren waiger.reset);
    wreset = (λl. lookup l wreset);
    wnext_alist = shared_latches micnt mlcnt iren lren waiger.next;
    wnext = fromAList wnext_alist;
    wnext  = (λl. case lookup l wnext of
                    | SOME lit => lit
                    | NONE => (Base Ff, F));
    wsafes =
      MAP (not ∘ shared_lit micnt mlcnt iren lren)
        (if wcounts.bad = 0 ∧ wcounts.justice = 0 then waiger.outputs
         else waiger.bad);
    wcnstrs = MAP (shared_lit micnt mlcnt iren lren) waiger.constraints;
    wlatches =
      GENLIST (λk. shared_latch_key micnt mlcnt iren lren (wlatch_start + k))
        wlcnt;
    wfair = MAP (not ∘ shared_lit micnt mlcnt iren lren) waiger.fairness;
    wjust = waiger.justice;
    wlive =
      MAP
        (λsignals.
           wfair ++
           (MAP (not ∘ shared_lit micnt mlcnt iren lren) signals)) wjust;
    interv =
      make_interv micnt mlcnt wicnt wmax_latch iren lren wnext_alist
        (ms.intervened_latches);
    interv = FLOOKUP interv;
  in
    (waig, wreset, wnext, wsafes, wcnstrs, wlive, wlatches, interv)
End

(* Checks that dependencies of the model AIG, model properties, etc., are
   contained in the range of model latches. *)
Definition check_model_def:
  check_model
    mxaig mreset mnext msafes mcnstrs (mlatches: num list)
    mlatch_start mmax_latch mlive
  =
  let
    mxaig_latches = xaig_latches mxaig;
    safe_latches = FLAT (MAP lit_latches msafes);
    cnstrs_latches = FLAT (MAP lit_latches mcnstrs);
    next_latches = FLAT (MAP (lit_latches ∘ mnext) mlatches);
    reset_lits = list$mapPartial mreset mlatches;
    reset_lit_latches = FLAT (MAP lit_latches reset_lits);
    live_latches = FLAT (MAP lit_latches (FLAT mlive));
  in
    do
      assert «circuit mentions latches outside of mlatches»
        (range_is_subset mxaig_latches mlatch_start mmax_latch);
      assert «safety signals mention latches outside of mlatches»
        (range_is_subset safe_latches mlatch_start mmax_latch);
      assert «constraints mention latches outside of mlatches»
        (range_is_subset cnstrs_latches mlatch_start mmax_latch);
      assert «next literals mention latches outside of mlatches»
        (range_is_subset next_latches mlatch_start mmax_latch);
      assert «reset literals mention latches outside of mlatches»
        (range_is_subset reset_lit_latches mlatch_start mmax_latch);
      assert «signals mention latches outside of mlatches»
        (range_is_subset live_latches mlatch_start mmax_latch);
    od
End

val monad_thms = [oneline bind_def, guard_def]

Theorem check_model_return:
  check_model
    mxaig mreset mnext msafes mcnstrs [mlatch_start .. mmax_latch]
    mlatch_start mmax_latch mlive
  = return ()
  ⇒
  dep_cond mxaig mreset mnext msafes mcnstrs mlive [mlatch_start .. mmax_latch]
Proof
  simp [check_model_def, dep_cond_def]
  >> rw monad_thms
  >> fs [range_is_subset_thm]
  >> fs [LIST_TO_SET_FLAT, LIST_TO_SET_MAP, IMAGE_o, LIST_TO_SET_mapPartial]
QED

Definition process_and_check_def:
  process_and_check
    maig mreset mnext msafes mcnstrs mlive mlatches mlatch_start mmax_latch
    waig wreset wlive wlatches
  =
  do
    mxaig <<- aig_to_xaig maig;
    wxaig <<- aig_to_xaig waig;
    klatches <<- range_inter mlatch_start mmax_latch wlatches;
    check_model
      mxaig mreset mnext msafes mcnstrs
      mlatches mlatch_start mmax_latch mlive;
    assert «length mismatch in number of liveness properties/signals»
    (LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive);
    assert «witness not stratified» (stratified_cond wxaig wreset wlatches);
    return (mxaig, wxaig, klatches)
  od
End

Theorem process_and_check_return:
  process_and_check
    maig mreset mnext msafes mcnstrs mlive
    [mlatch_start .. mmax_latch] mlatch_start mmax_latch
    waig wreset wlive wlatches
  = return (mxaig, wxaig, klatches)
  ∧
  encodings_unsat
    mxaig mreset mnext msafes mcnstrs mlive [mlatch_start .. mmax_latch]
    wxaig wreset wnext wsafes wcnstrs wlive wlatches
    interv klatches
  ⇒
  is_safe
    maig mreset mnext (set mcnstrs)
    (set [mlatch_start .. mmax_latch]) (set msafes) ∧
  is_live
    maig mreset mnext (set mcnstrs) (qleft maig)
    (IMAGE set (set (qleft_live mlive))) (set [mlatch_start .. mmax_latch])
Proof
  simp [process_and_check_def]
  >> strip_tac >> gvs (AllCaseEqs ()::monad_thms)
  >> dxrule_all_then assume_tac check_model_return
  >> qspec_then ‘maig’ assume_tac aig_xaig_rel_aig_to_xaig
  >> drule_then assume_tac $ GSYM xis_safe_is_safe
  >> drule_then assume_tac $ GSYM xis_live_is_live
  >> simp []
  >> irule $ INST_TYPE [“:δ” |-> “:γ”, “:γ” |-> “:num”] encoding_xis_safe_and_live
  >> qpat_assum ‘encodings_unsat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _’ $ irule_at Any
  >> simp [range_inter_thm]
QED

(* TODO Maybe the constant strings «» should be translated once? *)

Definition xaig_map_then_cnf_def:
  xaig_map_then_cnf f g h xaig name =
    xaig_to_cnf (xaig_map f g h xaig) (h name)
End

Theorem xaig_map_then_cnf_correct:
  xaig_map_then_cnf f g h xaig name = (cnf, limit) ∧
  INJ f 𝕌(:α) 𝕌(:β) ∧ INJ g 𝕌(:γ) 𝕌(:δ) ∧ INJ h 𝕌(:ε) 𝕌(:ζ)
  ⇒
  (satisfiable_cnf (set cnf) ⇔ ∃is ls. xeval_gate (is,ls) xaig name) ∧
  lits_within limit cnf
Proof
  simp [xaig_map_then_cnf_def]
  >> strip_tac
  >> dxrule_all $ GSYM exists_xeval_gate_xaig_map
  >> disch_then $ qspecl_then [‘xaig’, ‘name’] mp_tac
  >> simp [EXISTS_PROD] >> strip_tac
  >> irule xaig_to_cnf_correct
  >> simp []
QED

Definition make_reset_string_def:
  make_reset_string
    (mxaig: (num, num, num) xaig) mreset mcnstrs mlatches
    (wxaig: (num, num, num) xaig) wreset wcnstrs wlatches klatches
  =
  let
    name = «reset»;
    xaig  =
      encode_reset_cond
        mxaig mreset mcnstrs mlatches
        wxaig wreset wcnstrs wlatches klatches;
    cnf = xaig_map_then_cnf I I nsn_e2num xaig (Ext Reset)
  in
    (name, cnf_to_string cnf)
End

Definition make_transition_string_def:
  make_transition_string
    (mxaig: (num, num, num) xaig) mnext mcnstrs mlatches
    (wxaig: (num, num, num) xaig) wnext wcnstrs wlatches klatches
  =
  let
    name = «transition»;
    xaig  =
      encode_transition_cond
        mxaig mnext mcnstrs mlatches
        wxaig wnext wcnstrs wlatches klatches;
    cnf = xaig_to_cnf xaig (Ext Transition)
  in
    (name, cnf_to_string cnf)
End

Definition make_safety_string_def:
  make_safety_string
    (mxaig: (num, num, num) xaig) mcnstrs msafes
    (wxaig: (num, num, num) xaig) wcnstrs wsafes
  =
  let
    name = «safety»;
    xaig  =
      encode_safety_cond mxaig mcnstrs msafes wxaig wcnstrs wsafes;
    cnf = xaig_to_cnf xaig (Ext Safety)
  in
    (name, cnf_to_string cnf)
End

Definition make_base_string_def:
  make_base_string
    (wxaig: (num, num, num) xaig) wreset wcnstrs wsafes wlatches
  =
  let
    name = «base»;
    xaig  =
      encode_base_cond wxaig wreset wcnstrs wsafes wlatches;
    cnf = xaig_to_cnf xaig (Ext Base)
  in
    (name, cnf_to_string cnf)
End

Definition make_induction_string_def:
  make_induction_string
    (wxaig: (num, num, num) xaig) wnext wcnstrs wsafes wlatches
  =
  let
    name = «induction»;
    xaig  =
      encode_induction_cond wxaig wnext wcnstrs wsafes wlatches;
    cnf = xaig_to_cnf xaig (Ext Induction)
  in
    (name, cnf_to_string cnf)
End

Definition make_liveness_string_def:
  make_liveness_string
    (mxaig: (num, num, num) xaig) mcnstrs mlive
    (wxaig: (num, num, num) xaig) wnext wcnstrs wsafes wlive wlatches interv
  =
  let
    name = «liveness»;
    xaig  =
      encode_liveness_cond
        mxaig mcnstrs mlive
        wxaig wnext wcnstrs wsafes wlive wlatches interv;
    cnf = xaig_to_cnf xaig (Ext Liveness)
  in
    (name, cnf_to_string cnf)
End

Definition make_decrease_string_def:
  make_decrease_string
    (wxaig: (num, num, num) xaig) wnext wcnstrs wsafes wlive wlatches interv
  =
  let
    name = «decrease»;
    xaig  =
      encode_decrease_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv;
    cnf = xaig_to_cnf xaig (Ext Decrease)
  in
    (name, cnf_to_string cnf)
End

Definition make_closure_string_def:
  make_closure_string
    (wxaig: (num, num, num) xaig) wnext wcnstrs wsafes wlive wlatches interv
  =
  let
    name = «closure»;
    xaig  =
      encode_closure_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv;
    cnf = xaig_to_cnf xaig (Ext Closure)
  in
    (name, cnf_to_string cnf)
End

Definition make_stable_string_def:
  make_stable_string
    (wxaig: (num, num, num) xaig) wnext wcnstrs wsafes wlive wlatches interv
  =
  let
    name = «stable»;
    xaig  =
      encode_stable_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv;
    cnf = xaig_to_cnf xaig (Ext Stable)
  in
    (name, cnf_to_string cnf)
End
