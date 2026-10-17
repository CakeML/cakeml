(*
  Proofs about the Unsafe module.
*)
Theory UnsafeProof
Ancestors
  ml_translator mlbasicsProg UnsafeProg
Libs
  preamble ml_translatorLib cfLib

val _ = translation_extends "UnsafeProg";

(* Unsafe.Array *)

fun prove_array_spec v_def =
  rpt strip_tac \\
  xcf_with_def v_def \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_empty_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def, REPLICATE] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

Theorem unsafe_array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_sub_v [av; nv]
       (ARRAY av a) (POSTv v. cond (v = EL n a) * ARRAY av a)
Proof
  prove_array_spec Unsafe_sub_v_def
QED

Theorem unsafe_array_update_spec:
   !a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_update_v
       [av; nv; v]
       (ARRAY av a)
       (POSTv uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))
Proof
  prove_array_spec Unsafe_update_v_def
QED

(* Unsafe.Word8Array *)

fun prove_array_spec v_def =
  rpt strip_tac \\
  xcf_with_def v_def \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aw8subbit_def, cf_aw8updatebit_def, cf_copyaw8aw8_def, cf_aalloc_def, cf_asub_def, cf_alength_def,
      cf_aupdate_def, cf_copystraw8_def, cf_copyaw8str_def,
      cf_xoraw8str_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aw8subbit_def, app_aw8updatebit_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def,
      app_copyaw8aw8_def, app_copystraw8_def, app_copyaw8str_def,
      app_xoraw8str_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, BOOL_def, w2w_def, UNIT_TYPE_def,STRING_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\
  TRY (
    qmatch_assum_rename_tac`STRING_TYPE s sv`
    \\ Cases_on`s` \\ fs[STRING_TYPE_def]
    \\ fs[mlstringTheory.substring_def, SEG_TAKE_DROP] )

Theorem w8array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_w8sub_v [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)
Proof
  prove_array_spec Unsafe_w8sub_v_def
QED

Theorem w8array_update_spec:
   !a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) Unsafe_w8update_v
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))
Proof
  prove_array_spec Unsafe_w8update_v_def
QED

Theorem w8array_subBit_spec:
   !a av n nv.
     NUM n nv /\ n < 8 * LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_w8subBit_v [av; nv]
       (W8ARRAY av a)
       (POSTv v. cond (BOOL ((EL (n DIV 8) a) ' (n MOD 8)) v) * W8ARRAY av a)
Proof
  prove_array_spec Unsafe_w8subBit_v_def
QED

Theorem w8array_updateBit_spec:
   !a av n nv b bv.
     NUM n nv /\ n < 8 * LENGTH a /\ BOOL b bv ==>
     app (p:'ffi ffi_proj) Unsafe_w8updateBit_v
       [av; nv; bv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
                 W8ARRAY av (LUPDATE (((n MOD 8) :+ b) (EL (n DIV 8) a))
                                     (n DIV 8) a))
Proof
  prove_array_spec Unsafe_w8updateBit_v_def
QED

Theorem bitarray_subBit_spec:
   !bs av n nv.
     NUM n nv /\ n < LENGTH bs ==>
     app (p:'ffi ffi_proj) Unsafe_w8subBit_v [av; nv]
       (BITARRAY av bs) (POSTv v. cond (BOOL (EL n bs) v) * BITARRAY av bs)
Proof
  rw [BITARRAY_def, BITS_BYTES_def] \\ xpull
  \\ xapp_spec w8array_subBit_spec
  \\ gvs [LENGTH_bytes_to_bits] \\ xsimpl
  \\ rw [EL_bytes_to_bits]
  \\ qexists_tac `n` \\ simp []
QED

Theorem bitarray_updateBit_spec:
   !bs av n nv b bv.
     NUM n nv /\ n < LENGTH bs /\ BOOL b bv ==>
     app (p:'ffi ffi_proj) Unsafe_w8updateBit_v
       [av; nv; bv]
       (BITARRAY av bs)
       (POSTv v. cond (UNIT_TYPE () v) * BITARRAY av (LUPDATE b n bs))
Proof
  rw [BITARRAY_def, BITS_BYTES_def] \\ xpull
  \\ xapp_spec w8array_updateBit_spec
  \\ qexists_tac `emp` \\ qexists_tac `n` \\ qexists_tac `b`
  \\ gvs [LENGTH_bytes_to_bits] \\ xsimpl
  \\ rw [LUPDATE_bytes_to_bits]
QED

Theorem w8xor_str_spec:
   !s sv n nv xor_res a.
     STRING_TYPE s sv /\ LENGTH (explode s) ≤ LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_w8xor_str_v [av; sv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
         W8ARRAY av (THE (xor_bytes (MAP (n2w o ORD) (explode s)) a)))
Proof
  Cases \\ simp [] \\ prove_array_spec Unsafe_w8xor_str_v_def
QED

open semanticPrimitivesTheory evaluateTheory cfStoreTheory;

Theorem unsafe_arith_curry[local]:
  app (p:'ffi ffi_proj)
    (Closure (env with v := nsBind x xv env.v) y body) (yv::ys) H Q ==>
  app p (Closure env x (Fun y body)) (xv::yv::ys) H Q
Proof
  simp [app_def]
  \\ rw [app_basic_def]
  \\ fs [do_opapp_def,cfDivTheory.POSTv_eq,PULL_EXISTS]
  \\ `SPLIT3 (st2heap p st) (h_i,h_k,{})` by fs [SPLIT_def,SPLIT3_def]
  \\ first_x_assum $ irule_at Any
  \\ rw [evaluate_to_heap_def,evaluate_ck_def,evaluateTheory.evaluate_def,PULL_EXISTS]
  \\ fs [cfStoreTheory.st2heap_def,SEP_EXISTS_THM,cond_STAR]
  \\ first_x_assum $ irule_at Any \\ fs []
QED

Theorem unsafe_arith_apply[local]:
  (!st h_i h_k.
    SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
    evaluate (st with clock := 0)
      (env with v := nsBind parameter arg env.v) [body] =
      (st with clock := 0,Rval [result])) ==>
  app (p:'ffi ffi_proj) (Closure env parameter body) [arg]
    H (POSTv v. &(v = result) * H)
Proof
  rw [app_def,app_basic_def,do_opapp_def]
  \\ Q.LIST_EXISTS_TAC [`Val result`, `h_i`, `{}`, `st2heap p st`]
  \\ simp [cfDivTheory.POSTv_eq,cond_STAR,evaluate_to_heap_def,evaluate_ck_def]
  \\ conj_tac
  >- metis_tac [SPLIT3_of_SPLIT_emp3]
  \\ Q.LIST_EXISTS_TAC [`0`, `st with clock := 0`]
  \\ fs [st2heap_clock]
  \\ metis_tac []
QED

Theorem unsafe_arith_app2[local]:
  getOpClass oper = Simple /\
  (!st h_i h_k.
    SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
    do_app (st.refs,st.ffi) oper [x;y] =
      SOME ((st.refs,st.ffi),Rval result)) ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y»
      (App oper [Var (Short «x»); Var (Short «y»)]))) [x;y]
    H (POSTv v. &(v = result) * H)
Proof
  strip_tac
  \\ irule unsafe_arith_curry
  \\ irule unsafe_arith_apply
  \\ rpt strip_tac
  \\ simp [evaluate_def,ml_progTheory.nsLookup_nsBind_compute]
  \\ qpat_x_assum `!st h_i h_k. _` drule_all
  \\ strip_tac \\ simp [state_component_equality]
QED

Theorem unsafe_arith_app3[local]:
  getOpClass oper = Simple /\
  (!st h_i h_k.
    SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
    do_app (st.refs,st.ffi) oper [x;y;witness] =
      SOME ((st.refs,st.ffi),Rval result)) ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y» (Fun «witness»
      (App oper [Var (Short «x»); Var (Short «y»);
                 Var (Short «witness»)])))) [x;y;witness]
    H (POSTv v. &(v = result) * H)
Proof
  strip_tac
  \\ irule unsafe_arith_curry
  \\ irule unsafe_arith_curry
  \\ irule unsafe_arith_apply
  \\ rpt strip_tac
  \\ simp [evaluate_def,ml_progTheory.nsLookup_nsBind_compute]
  \\ qpat_x_assum `!st h_i h_k. _` drule_all
  \\ strip_tac \\ simp [state_component_equality]
QED

Definition index_witness_heap_def:
  index_witness_heap (p:'ffi ffi_proj) H witness len <=>
    !st h_i h_k.
      SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
      index_witness_length st.refs witness = SOME len
End

Theorem index_witness_vector:
  VECTOR_TYPE a xs witness ==>
  index_witness_heap p emp witness (256 * length xs)
Proof
  namedCases_on `xs` ["entries"]
  \\ rw [VECTOR_TYPE_def,mlvectorTheory.length_def,
          index_witness_heap_def,index_witness_length_def]
  \\ gvs [index_witness_length_def]
QED

Theorem witness_store_lookup[local]:
  SPLIT (st2heap p st) ({Mem location value},h) ==>
  store_lookup location st.refs = SOME value
Proof
  strip_tac
  \\ `Mem location value IN st2heap p st` by fs [SPLIT_EQ]
  \\ `Mem location value IN store2heap st.refs` by
    fs [st2heap_def,Mem_NOT_IN_ffi2heap]
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ imp_res_tac store2heap_IN_EL
  \\ simp [store_lookup_def]
QED

Theorem index_witness_array:
  index_witness_heap p (ARRAY witness xs) witness (256 * LENGTH xs)
Proof
  rw [index_witness_heap_def,ARRAY_def,SEP_EXISTS_THM,cond_STAR,cell_def,one_def]
  \\ drule witness_store_lookup
  \\ simp [index_witness_length_def]
QED

Theorem index_witness_w8array:
  index_witness_heap p (W8ARRAY witness xs) witness (32 * LENGTH xs)
Proof
  rw [index_witness_heap_def,W8ARRAY_def,SEP_EXISTS_THM,cond_STAR,cell_def,one_def]
  \\ drule witness_store_lookup
  \\ simp [index_witness_length_def]
QED

Theorem unsafe_index_arith_spec[local]:
  index_in_bounds NONE x /\ index_in_bounds NONE y /\
  index_in_bounds NONE result /\
  do_arith arith IntT [Litv (IntLit x); Litv (IntLit y)] =
    SOME (INR (Litv (IntLit result))) ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y» (App (UnsafeIndexArith arith)
      [Var (Short «x»); Var (Short «y»)])))
    [Litv (IntLit x); Litv (IntLit y)]
    emp (POSTv v. &INT result v * emp)
Proof
  rw [INT_def]
  \\ irule unsafe_arith_app2
  \\ simp [do_app_def,do_unsafe_index_arith_def,unsafe_index_bound_def]
QED

Theorem unsafe_index_test_spec[local]:
  index_in_bounds NONE x /\ index_in_bounds NONE y /\
  do_test test IntT (Litv (IntLit x)) (Litv (IntLit y)) = Eq_val result ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y» (App (UnsafeIndexTest test)
      [Var (Short «x»); Var (Short «y»)])))
    [Litv (IntLit x); Litv (IntLit y)]
    emp (POSTv v. &BOOL result v * emp)
Proof
  rw [BOOL_def]
  \\ irule unsafe_arith_app2
  \\ simp [do_app_def,do_unsafe_index_test_def,unsafe_index_bound_def]
QED

Theorem unsafe_index_arith_witness_spec[local]:
  index_witness_heap p H witness len ==>
  index_in_bounds (SOME len) x /\ index_in_bounds (SOME len) y /\
  index_in_bounds (SOME len) result /\
  do_arith arith IntT [Litv (IntLit x); Litv (IntLit y)] =
    SOME (INR (Litv (IntLit result))) ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y» (Fun «witness»
      (App (UnsafeIndexArith arith)
        [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))))
    [Litv (IntLit x); Litv (IntLit y); witness]
    H (POSTv v. &INT result v * H)
Proof
  rw [INT_def,index_witness_heap_def]
  \\ irule unsafe_arith_app3 \\ simp []
  \\ rpt strip_tac
  \\ qpat_x_assum `!st h_i h_k. _` drule_all
  \\ strip_tac
  \\ simp [do_app_def,do_unsafe_index_arith_def,unsafe_index_bound_def]
QED

Theorem unsafe_index_test_witness_spec[local]:
  index_witness_heap p H witness len ==>
  index_in_bounds (SOME len) x /\ index_in_bounds (SOME len) y /\
  do_test test IntT (Litv (IntLit x)) (Litv (IntLit y)) = Eq_val result ==>
  app (p:'ffi ffi_proj)
    (Closure env «x» (Fun «y» (Fun «witness»
      (App (UnsafeIndexTest test)
        [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))))
    [Litv (IntLit x); Litv (IntLit y); witness]
    H (POSTv v. &BOOL result v * H)
Proof
  rw [BOOL_def,index_witness_heap_def]
  \\ irule unsafe_arith_app3 \\ simp []
  \\ rpt strip_tac
  \\ qpat_x_assum `!st h_i h_k. _` drule_all
  \\ strip_tac
  \\ simp [do_app_def,do_unsafe_index_test_def,unsafe_index_bound_def]
QED

Theorem unsafe_arith_inputs[local]:
  INT x xv /\ INT y yv ==>
  app p f (Litv (IntLit x)::Litv (IntLit y)::args) H Q ==>
  app p f (xv::yv::args) H Q
Proof
  simp [INT_def]
QED

local
  val arith_state = get_ml_prog_state ();
  val operations =
    [("add", "+", ``ast$Add``, ``x + y:int``, false),
     ("sub", "-", ``ast$Sub``, ``x - y:int``, false),
     ("mul", "*", ``ast$Mul``, ``x * y:int``, false),
     ("div", "div", ``ast$Div``, ``x / y:int``, false),
     ("mod", "mod", ``ast$Mod``, ``x % y:int``, false),
     ("lt", "<", ``ast$Compare ast$Lt``, ``x < y:int``, true),
     ("le", "<=", ``ast$Compare ast$Leq``, ``x <= y:int``, true),
     ("gt", ">", ``ast$Compare ast$Gt``, ``x > y:int``, true),
     ("ge", ">=", ``ast$Compare ast$Geq``, ``x >= y:int``, true),
     ("eq", "=", ``ast$Equal``, ``x = y:int``, true)];
  fun app_value tm = List.nth (#2 (strip_comb (#2 (strip_imp tm))), 1);
  fun bind_value name th =
    let
      val def = fetch_def ("Unsafe.Arith." ^ name) arith_state
    in
      REWRITE_RULE [GSYM def]
        (PART_MATCH app_value th (rhs (concl def)))
    end;
  fun generalise_inputs th =
    MATCH_MP (UNDISCH unsafe_arith_inputs) (UNDISCH_ALL th)
    |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
    |> SIMP_RULE (srw_ss ()) [SEP_CLAUSES] |> GEN_ALL;
  fun specialise is_test oper result th =
    INST [mk_var (if is_test then "test" else "arith", type_of oper) |-> oper,
          mk_var ("result", type_of result) |-> result] th
    |> SIMP_RULE (srw_ss ())
         [do_arith_def, do_test_def, do_eq_def, lit_same_type_def,check_type_def,
          semanticPrimitivesTheory.int_cmp_def];
  fun save_specs (name, mlname, oper, result, is_test) =
    let
      val plain = specialise is_test oper result
        (if is_test then unsafe_index_test_spec else unsafe_index_arith_spec)
        |> bind_value mlname
      val witness = specialise is_test oper result
        (if is_test then unsafe_index_test_witness_spec
         else unsafe_index_arith_witness_spec)
        |> bind_value (name ^ "Witness")
      fun save suffix th = save_thm
        ("unsafe_arith_" ^ name ^ suffix ^ "_spec", generalise_inputs th)
    in
      save "" plain;
      save "_witness" witness;
      List.app (fn (suffix, lemma) =>
        ignore (save suffix (MATCH_MP witness (UNDISCH_ALL lemma))))
        [("_vector", index_witness_vector), ("_array", index_witness_array),
         ("_w8array", index_witness_w8array)]
    end;
in
  val _ = List.app save_specs operations;
end
